-- Prove2me | solution 1 for PolicyGradTheory.QNPG.transfer_term_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:58:26.492304+00:00
-- url     : https://prove2.me/submissions/57a03104-8164-4b79-9dbd-08e488dce80a

import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.QNPG

section LL
variable {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}

lemma qn_Z_pos (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) :
    0 < ∑ b, Real.exp (inner ℝ θ (φ s b)) :=
  Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty

lemma qn_ll_eq (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) :
    logLinearPolicy φ θ s a = Real.exp (inner ℝ θ (φ s a)) / ∑ b, Real.exp (inner ℝ θ (φ s b)) := rfl

lemma qn_ll_pos (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) :
    0 < logLinearPolicy φ θ s a := by
  rw [qn_ll_eq]; exact div_pos (Real.exp_pos _) (qn_Z_pos φ θ s)

lemma qn_ll_sum (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) :
    ∑ a, logLinearPolicy φ θ s a = 1 := by
  simp only [qn_ll_eq, ← Finset.sum_div]
  exact div_self (qn_Z_pos φ θ s).ne'

/-- mean feature -/
noncomputable def qnMean (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    (s : S) : EuclideanSpace ℝ (Fin d) :=
  ∑ b, logLinearPolicy φ θ s b • φ s b

lemma qn_inner_hasFDeriv (v θ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => inner ℝ x v) (innerSL ℝ v) θ := by
  have := (innerSL ℝ v).hasFDerivAt (x := θ)
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  simp [real_inner_comm]

lemma qn_ll_hasGrad (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    (s : S) (a : A) :
    HasGradientAt (fun x => Real.log (logLinearPolicy φ x s a)) (φ s a - qnMean φ θ s) θ := by
  have heq : (fun x => Real.log (logLinearPolicy φ x s a)) =
      fun x => inner ℝ x (φ s a) - Real.log (∑ b, Real.exp (inner ℝ x (φ s b))) := by
    funext x
    rw [qn_ll_eq, Real.log_div (Real.exp_pos _).ne' (qn_Z_pos φ x s).ne', Real.log_exp]
  rw [heq, hasGradientAt_iff_hasFDerivAt]
  have hZ := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun b _ => (qn_inner_hasFDeriv (φ s b) θ).exp)
  have h := HasFDerivAt.fun_sub (qn_inner_hasFDeriv (φ s a) θ) (hZ.log (qn_Z_pos φ θ s).ne')
  refine h.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, qnMean, inner_sub_left,
    sum_inner, inner_smul_left, qn_ll_eq]
  simp only [Finset.sum_fn, conj_trivial]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  field_simp

lemma qn_ll_grad (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d))
    (s : S) (a : A) :
    gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ = φ s a - qnMean φ θ s :=
  (qn_ll_hasGrad φ θ s a).gradient

lemma qn_cov_bound {A : Type} [Fintype A] (p e y : A → ℝ) (hp : ∀ b, 0 ≤ p b) (hs : ∑ b, p b = 1)
    (E0 Y0 : ℝ) (hE : 0 ≤ E0) (hY : 0 ≤ Y0) (he : ∀ b, |e b| ≤ E0) (hy : ∀ b, |y b| ≤ Y0) :
    ∑ b, p b * e b * y b - (∑ b, p b * e b) * (∑ b, p b * y b) ≤ E0 * Y0 := by
  set me := ∑ b, p b * e b with hme
  set my := ∑ b, p b * y b with hmy
  have hcov : ∑ b, p b * e b * y b - me * my =
      ∑ b, Real.sqrt (p b) * (e b - me) * (Real.sqrt (p b) * (y b - my)) := by
    have : ∀ b, Real.sqrt (p b) * (e b - me) * (Real.sqrt (p b) * (y b - my)) =
        p b * e b * y b - my * (p b * e b) - me * (p b * y b) + me * my * p b := by
      intro b
      have := Real.mul_self_sqrt (hp b)
      linear_combination (e b - me) * (y b - my) * this
    simp_rw [this]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, ← hme, ← hmy]
    ring
  have hvar : ∀ (u : A → ℝ) (U : ℝ), (∀ b, |u b| ≤ U) →
      ∑ b, (Real.sqrt (p b) * (u b - ∑ c, p c * u c)) ^ 2 ≤ U ^ 2 := by
    intro u U hu
    set m := ∑ c, p c * u c with hm
    have h1 : ∀ b, (Real.sqrt (p b) * (u b - m)) ^ 2 = p b * u b ^ 2 - 2 * m * (p b * u b) + m ^ 2 * p b := by
      intro b
      rw [mul_pow, Real.sq_sqrt (hp b)]; ring
    simp_rw [h1]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, ← hm]
    have h2 : ∑ b, p b * u b ^ 2 ≤ ∑ b, p b * U ^ 2 := by
      refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hp b)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hu b) 2
    rw [← Finset.sum_mul, hs] at h2
    nlinarith [sq_nonneg m]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun b => Real.sqrt (p b) * (e b - me)) (fun b => Real.sqrt (p b) * (y b - my))
  have hv1 := hvar e E0 he
  have hv2 := hvar y Y0 hy
  rw [← hcov] at hcs
  have hsq : (∑ b, p b * e b * y b - me * my) ^ 2 ≤ (E0 * Y0) ^ 2 := by
    calc _ ≤ _ := hcs
      _ ≤ E0 ^ 2 * Y0 ^ 2 := mul_le_mul hv1 hv2 (Finset.sum_nonneg fun b _ => sq_nonneg _)
          (sq_nonneg _)
      _ = _ := by ring
  have h0 : 0 ≤ E0 * Y0 := mul_nonneg hE hY
  by_contra hc
  push_neg at hc
  nlinarith

lemma qn_mvt_cov {A : Type} [Fintype A] [Nonempty A] (c e y : A → ℝ) (E0 Y0 : ℝ)
    (hE : 0 ≤ E0) (hY : 0 ≤ Y0) (he : ∀ b, |e b| ≤ E0) (hy : ∀ b, |y b| ≤ Y0) :
    (∑ b, Real.exp (c b + e b) * y b) / (∑ b, Real.exp (c b + e b)) -
      (∑ b, Real.exp (c b) * y b) / (∑ b, Real.exp (c b)) ≤ E0 * Y0 := by
  let N : ℝ → ℝ := fun t => ∑ b, Real.exp (c b + t * e b) * y b
  let Z : ℝ → ℝ := fun t => ∑ b, Real.exp (c b + t * e b)
  let N' : ℝ → ℝ := fun t => ∑ b, Real.exp (c b + t * e b) * e b * y b
  let Z' : ℝ → ℝ := fun t => ∑ b, Real.exp (c b + t * e b) * e b
  have hZpos : ∀ t, 0 < Z t := fun t =>
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hexp : ∀ b t, HasDerivAt (fun t => Real.exp (c b + t * e b))
      (Real.exp (c b + t * e b) * e b) t := by
    intro b t
    have h1 : HasDerivAt (fun t => c b + t * e b) (e b) t := by
      simpa using ((hasDerivAt_id t).mul_const (e b)).const_add (c b)
    exact h1.exp
  have hN : ∀ t, HasDerivAt N (N' t) t := by
    intro t
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hexp b t).mul_const (y b))
    simpa [N, N'] using this
  have hZ : ∀ t, HasDerivAt Z (Z' t) t := by
    intro t
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => hexp b t)
    simpa [Z, Z'] using this
  have hF : ∀ t, HasDerivAt (fun t => N t / Z t)
      ((N' t * Z t - N t * Z' t) / Z t ^ 2) t := fun t =>
    (hN t).div (hZ t) (hZpos t).ne'
  obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope (fun t => N t / Z t)
    (fun t => (N' t * Z t - N t * Z' t) / Z t ^ 2) (zero_lt_one' ℝ)
    (fun t _ => (hF t).continuousAt.continuousWithinAt) (fun t _ => hF t)
  have hgoal : (∑ b, Real.exp (c b + e b) * y b) / (∑ b, Real.exp (c b + e b)) -
      (∑ b, Real.exp (c b) * y b) / (∑ b, Real.exp (c b)) = N 1 / Z 1 - N 0 / Z 0 := by
    simp [N, Z]
  rw [hgoal, show N 1 / Z 1 - N 0 / Z 0 = (N 1 / Z 1 - N 0 / Z 0) / (1 - 0) by norm_num, ← hξ]
  set p : A → ℝ := fun b => Real.exp (c b + ξ * e b) / Z ξ with hpdef
  have hp : ∀ b, 0 ≤ p b := fun b => div_nonneg (Real.exp_pos _).le (hZpos ξ).le
  have hs : ∑ b, p b = 1 := by
    simp only [hpdef, ← Finset.sum_div]; exact div_self (hZpos ξ).ne'
  have key := qn_cov_bound p e y hp hs E0 Y0 hE hY he hy
  have hZne := (hZpos ξ).ne'
  have e1 : ∑ b, p b * e b * y b = N' ξ / Z ξ := by
    simp only [hpdef, N', Finset.sum_div]; congr 1; ext b; field_simp
  have e2 : ∑ b, p b * e b = Z' ξ / Z ξ := by
    simp only [hpdef, Z', Finset.sum_div]; congr 1; ext b; field_simp
  have e3 : ∑ b, p b * y b = N ξ / Z ξ := by
    simp only [hpdef, N, Finset.sum_div]; congr 1; ext b; field_simp
  rw [e1, e2, e3] at key
  have : (N' ξ * Z ξ - N ξ * Z' ξ) / Z ξ ^ 2 = N' ξ / Z ξ - Z' ξ / Z ξ * (N ξ / Z ξ) := by
    field_simp
  rw [this]; exact key

theorem log_linear_smooth_core {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (B : ℝ)
    (hφ : ∀ s a, ‖φ s a‖ ≤ B) (s : S) (a : A) :
    ∀ θ θ' : EuclideanSpace ℝ (Fin d),
      ‖gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ -
        gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ'‖ ≤
        B ^ 2 * ‖θ - θ'‖ := by
  intro θ θ'
  have hB : 0 ≤ B := (norm_nonneg _).trans (hφ s a)
  rw [qn_ll_grad, qn_ll_grad, sub_sub_sub_cancel_left]
  set x := qnMean φ θ' s - qnMean φ θ s with hx
  set v := θ' - θ with hv
  have hmean : ∀ ϑ : EuclideanSpace ℝ (Fin d), inner ℝ (qnMean φ ϑ s) x =
      (∑ b, Real.exp (inner ℝ ϑ (φ s b)) * inner ℝ (φ s b) x) /
        ∑ b, Real.exp (inner ℝ ϑ (φ s b)) := by
    intro ϑ
    simp only [qnMean, sum_inner, inner_smul_left, conj_trivial, qn_ll_eq, Finset.sum_div]
    congr 1; ext b; ring
  have hxx : ‖x‖ ^ 2 = inner ℝ (qnMean φ θ' s) x - inner ℝ (qnMean φ θ s) x := by
    rw [← inner_sub_left, ← hx, real_inner_self_eq_norm_sq]
  have h1 : ∀ b, inner ℝ θ' (φ s b) = inner ℝ θ (φ s b) + inner ℝ v (φ s b) := by
    intro b; rw [← inner_add_left, hv, add_sub_cancel]
  rw [hmean, hmean] at hxx
  simp_rw [h1] at hxx
  have key := qn_mvt_cov (fun b => inner ℝ θ (φ s b)) (fun b => inner ℝ v (φ s b))
    (fun b => inner ℝ (φ s b) x) (‖v‖ * B) (B * ‖x‖) (mul_nonneg (norm_nonneg _) hB)
    (mul_nonneg hB (norm_nonneg _))
    (fun b => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hφ s b) (norm_nonneg _)))
    (fun b => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hφ s b) (norm_nonneg _)))
  rw [← hxx] at key
  rw [norm_sub_rev θ θ', ← hv]
  rcases (norm_nonneg x).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

end LL

section MDP
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- induced transition matrix -/
noncomputable def qnM (π : S → A → ℝ) (P : S → A → S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun s s' => InducedTransition π P s s'

lemma qn_occ_eq_pow (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (s : S) :
    OccupationDist π P s0 t s = (qnM π P ^ t) s0 s := by
  induction t generalizing s with
  | zero => simp [OccupationDist, Matrix.one_apply, eq_comm]
  | succ t ih =>
    simp only [OccupationDist, pow_succ, Matrix.mul_apply, ih]
    rfl

variable {π : S → A → ℝ} {P : S → A → S → ℝ}

lemma qn_M_nonneg (hP : IsTransitionKernel P) (hπ : IsPolicy π) (s s' : S) :
    0 ≤ qnM π P s s' := by
  simp only [qnM, Matrix.of_apply, InducedTransition]
  exact Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s')

lemma qn_M_rowsum (hP : IsTransitionKernel P) (hπ : IsPolicy π) (s : S) :
    ∑ s', qnM π P s s' = 1 := by
  simp only [qnM, Matrix.of_apply, InducedTransition]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
  exact (hπ s).2

lemma qn_pow_nonneg (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s s' : S) :
    0 ≤ (qnM π P ^ t) s s' := by
  induction t generalizing s' with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (ih x) (qn_M_nonneg hP hπ x s')

lemma qn_pow_rowsum (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s : S) :
    ∑ s', (qnM π P ^ t) s s' = 1 := by
  induction t with
  | zero => simp [Matrix.one_apply]
  | succ t ih =>
    simp_rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, qn_M_rowsum hP hπ, mul_one]
    exact ih

lemma qn_pow_le_one (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s s' : S) :
    (qnM π P ^ t) s s' ≤ 1 := by
  rw [← qn_pow_rowsum hP hπ t s]
  exact Finset.single_le_sum (fun x _ => qn_pow_nonneg hP hπ t s x) (Finset.mem_univ _)

lemma qn_E_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s : S) (g : S → ℝ)
    (B : ℝ) (hg : ∀ x, |g x| ≤ B) : |∑ s', (qnM π P ^ t) s s' * g s'| ≤ B := by
  calc |∑ s', (qnM π P ^ t) s s' * g s'| ≤ ∑ s', |(qnM π P ^ t) s s' * g s'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', (qnM π P ^ t) s s' * B := by
        apply Finset.sum_le_sum; intro x _
        rw [abs_mul, abs_of_nonneg (qn_pow_nonneg hP hπ t s x)]
        exact mul_le_mul_of_nonneg_left (hg x) (qn_pow_nonneg hP hπ t s x)
    _ = B := by rw [← Finset.sum_mul, qn_pow_rowsum hP hπ, one_mul]

lemma qn_summable (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', (qnM π P ^ t) s s' * g s') := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ0 hγ1).mul_right B) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  exact mul_le_mul_of_nonneg_left (qn_E_bound hP hπ t s g B hg) (pow_nonneg hγ0 t)

lemma qn_tsum_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    |∑' t : ℕ, γ ^ t * ∑ s', (qnM π P ^ t) s s' * g s'| ≤ B / (1 - γ) := by
  have hs := qn_summable hP hπ hγ0 hγ1 s g B hg
  have hgeo := (summable_geometric_of_lt_one hγ0 hγ1).mul_right B
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  calc ∑' t : ℕ, ‖γ ^ t * ∑ s', (qnM π P ^ t) s s' * g s'‖ ≤ ∑' t : ℕ, γ ^ t * B := by
        refine hs.norm.tsum_le_tsum (fun t => ?_) hgeo
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
        exact mul_le_mul_of_nonneg_left (qn_E_bound hP hπ t s g B hg) (pow_nonneg hγ0 t)
    _ = B / (1 - γ) := by rw [tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1]; ring

lemma qn_value_eq (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) :
    PolicyValue π P r γ s =
      ∑' t : ℕ, γ ^ t * ∑ s', (qnM π P ^ t) s s' * InducedReward π r s' := by
  simp only [PolicyValue, qn_occ_eq_pow]

lemma qn_reward_bound (hπ : IsPolicy π) {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (s : S) : |InducedReward π r s| ≤ 1 := by
  have h0 : 0 ≤ InducedReward π r s :=
    Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) (hr s a).1
  have h1 : InducedReward π r s ≤ 1 := by
    calc InducedReward π r s ≤ ∑ a, π s a * 1 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hr s a).2 ((hπ s).1 a)
      _ = 1 := by simp [(hπ s).2]
  rw [abs_le]; constructor <;> linarith

lemma qn_value_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    |PolicyValue π P r γ s| ≤ 1 / (1 - γ) := by
  rw [qn_value_eq]
  exact qn_tsum_bound hP hπ hγ0 hγ1 s _ 1 (qn_reward_bound hπ hr)

/-- first-step identity for E -/
lemma qn_E_succ (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) (s : S) (g : S → ℝ) :
    ∑ s', (qnM π P ^ (t + 1)) s s' * g s' =
      ∑ x, qnM π P s x * ∑ s', (qnM π P ^ t) x s' * g s' := by
  simp_rw [pow_succ', Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring

lemma qn_E_succ' (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) (s : S) (g : S → ℝ) :
    ∑ s', (qnM π P ^ (t + 1)) s s' * g s' =
      ∑ x, (qnM π P ^ t) s x * ∑ s', qnM π P x s' * g s' := by
  simp_rw [pow_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring

/-- generic Bellman-type identity -/
lemma qn_tsum_bellman (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    ∑' t : ℕ, γ ^ t * ∑ s', (qnM π P ^ t) s s' * g s' =
      g s + γ * ∑ x, qnM π P s x * ∑' t : ℕ, γ ^ t * ∑ s', (qnM π P ^ t) x s' * g s' := by
  rw [(qn_summable hP hπ hγ0 hγ1 s g B hg).tsum_eq_zero_add]
  congr 1
  · simp [Matrix.one_apply]
  · simp_rw [qn_E_succ]
    have : ∀ t : ℕ, γ ^ (t + 1) * ∑ x, qnM π P s x * ∑ s', (qnM π P ^ t) x s' * g s' =
        ∑ x, (γ * qnM π P s x) * (γ ^ t * ∑ s', (qnM π P ^ t) x s' * g s') := by
      intro t; rw [Finset.mul_sum]; congr 1; ext x; ring
    simp_rw [this]
    rw [Summable.tsum_finsetSum (fun x _ =>
      (qn_summable hP hπ hγ0 hγ1 x g B hg).mul_left (γ * qnM π P s x))]
    rw [Finset.mul_sum]; congr 1; ext x
    rw [Summable.tsum_mul_left _ (qn_summable hP hπ hγ0 hγ1 x g B hg)]; ring

lemma qn_bellman (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P r γ s =
      InducedReward π r s + γ * ∑ x, qnM π P s x * PolicyValue π P r γ x := by
  simp_rw [qn_value_eq]
  exact qn_tsum_bellman hP hπ hγ0 hγ1 s _ 1 (qn_reward_bound hπ hr)

lemma qn_adv_sum (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π' : S → A → ℝ)
    (s : S) :
    ∑ a, π' s a * PolicyGradTheory.ProjGA.advantage π P r γ s a =
      InducedReward π' r s + γ * ∑ x, qnM π' P s x * PolicyValue π P r γ x
        - (∑ a, π' s a) * PolicyValue π P r γ s := by
  simp only [PolicyGradTheory.ProjGA.advantage, QFunction, InducedReward, qnM, Matrix.of_apply,
    InducedTransition, mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1; congr 1
  rw [Finset.sum_comm]; congr 1; ext a; congr 1; ext x; ring

lemma qn_adv_sum_self (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    ∑ a, π s a * PolicyGradTheory.ProjGA.advantage π P r γ s a = 0 := by
  rw [qn_adv_sum hP hπ hr hγ0 hγ1, (hπ s).2, ← qn_bellman hP hπ hr hγ0 hγ1]; ring


lemma qn_pdl_state (hP : IsTransitionKernel P) (hπ : IsPolicy π) {π' : S → A → ℝ}
    (hπ' : IsPolicy π') {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s0 : S) :
    PolicyValue π P r γ s0 - PolicyValue π' P r γ s0 =
      ∑' t : ℕ, γ ^ t * ∑ s', (qnM π P ^ t) s0 s' *
        (∑ a, π s' a * PolicyGradTheory.ProjGA.advantage π' P r γ s' a) := by
  have hVb : ∀ x, |PolicyValue π' P r γ x| ≤ 1 / (1 - γ) :=
    fun x => qn_value_bound hP hπ' hr hγ0 hγ1 x
  have hbs : Summable (fun t : ℕ => γ ^ t * ∑ s', (qnM π P ^ t) s0 s' * PolicyValue π' P r γ s') :=
    qn_summable hP hπ hγ0 hγ1 s0 _ _ hVb
  have has : Summable (fun t : ℕ => γ ^ t * ∑ s', (qnM π P ^ t) s0 s' * InducedReward π r s') :=
    qn_summable hP hπ hγ0 hγ1 s0 _ 1 (qn_reward_bound hπ hr)
  have hbs1 : Summable (fun t : ℕ => γ ^ (t + 1) * ∑ s', (qnM π P ^ (t + 1)) s0 s' *
      PolicyValue π' P r γ s') := hbs.comp_injective (add_left_injective 1)
  have hterm : ∀ t : ℕ, γ ^ t * ∑ s', (qnM π P ^ t) s0 s' *
        (∑ a, π s' a * PolicyGradTheory.ProjGA.advantage π' P r γ s' a) =
      (γ ^ t * ∑ s', (qnM π P ^ t) s0 s' * InducedReward π r s') +
        (γ ^ (t + 1) * ∑ s', (qnM π P ^ (t + 1)) s0 s' * PolicyValue π' P r γ s') -
        (γ ^ t * ∑ s', (qnM π P ^ t) s0 s' * PolicyValue π' P r γ s') := by
    intro t
    simp_rw [qn_adv_sum hP hπ' hr hγ0 hγ1 π, (hπ _).2, one_mul]
    rw [qn_E_succ']
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, pow_succ]
    simp_rw [Finset.mul_sum]
    ring_nf
  rw [tsum_congr hterm, Summable.tsum_sub (has.add hbs1) hbs, Summable.tsum_add has hbs1,
    hbs.tsum_eq_zero_add, qn_value_eq π P r γ s0]
  simp [Matrix.one_apply]

/-- sums against the visitation distribution -/
lemma qn_vis_sum (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ρ : S → ℝ) (f : S → ℝ) (B : ℝ) (hf : ∀ x, |f x| ≤ B) :
    ∑ s, PolicyGradTheory.ProjGA.visitation π P γ ρ s * f s =
      (1 - γ) * ∑ s0, ρ s0 * ∑' t : ℕ, γ ^ t * ∑ s', (qnM π P ^ t) s0 s' * f s' := by
  have hu : ∀ s, Summable (fun t : ℕ => γ ^ t * ∑ s0, ρ s0 * (qnM π P ^ t) s0 s) := by
    intro s
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s0, |ρ s0|)) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul, abs_of_nonneg (qn_pow_nonneg hP hπ t x s)]
    exact mul_le_of_le_one_right (abs_nonneg _) (qn_pow_le_one hP hπ t x s)
  simp only [PolicyGradTheory.ProjGA.visitation, qn_occ_eq_pow]
  have h1 : ∀ s, (1 - γ) * (∑' t : ℕ, γ ^ t * ∑ s0, ρ s0 * (qnM π P ^ t) s0 s) * f s =
      (1 - γ) * ∑' t : ℕ, γ ^ t * ∑ s0, ρ s0 * (qnM π P ^ t) s0 s * f s := by
    intro s
    rw [mul_assoc, ← (hu s).tsum_mul_right]
    congr 2; ext t; rw [mul_assoc, Finset.sum_mul]
  simp_rw [h1]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum]
  · congr 1
    have h2 : ∀ t : ℕ, ∑ s, γ ^ t * ∑ s0, ρ s0 * (qnM π P ^ t) s0 s * f s =
        ∑ s0, ρ s0 * (γ ^ t * ∑ s', (qnM π P ^ t) s0 s' * f s') := by
      intro t
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring
    simp_rw [h2]
    rw [Summable.tsum_finsetSum]
    · congr 1; ext s0
      exact Summable.tsum_mul_left _ (qn_summable hP hπ hγ0 hγ1 s0 f B hf)
    · intro s0 _
      exact (qn_summable hP hπ hγ0 hγ1 s0 f B hf).mul_left _
  · intro s _
    have := (hu s).mul_right (f s)
    refine this.congr fun t => ?_
    rw [mul_assoc, Finset.sum_mul]

lemma qn_adv_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) {π' : S → A → ℝ}
    (hπ' : IsPolicy π') {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    |∑ a, π s a * PolicyGradTheory.ProjGA.advantage π' P r γ s a| ≤ 1 + 2 / (1 - γ) := by
  rw [qn_adv_sum hP hπ' hr hγ0 hγ1 π, (hπ s).2, one_mul]
  have h1 := qn_reward_bound hπ hr s
  have h2 := qn_E_bound (t := 1) hP hπ s (fun x => PolicyValue π' P r γ x) _
    (fun x => qn_value_bound hP hπ' hr hγ0 hγ1 x)
  simp only [pow_one] at h2
  have h3 := qn_value_bound hP hπ' hr hγ0 hγ1 s
  have hg : 0 < 1 - γ := by linarith
  have h4 : |γ * ∑ x, qnM π P s x * PolicyValue π' P r γ x| ≤ 1 / (1 - γ) := by
    rw [abs_mul, abs_of_nonneg hγ0]
    calc γ * _ ≤ 1 * (1 / (1 - γ)) := mul_le_mul (by linarith) h2 (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  calc _ ≤ |InducedReward π r s + γ * ∑ x, qnM π P s x * PolicyValue π' P r γ x|
        + |PolicyValue π' P r γ s| := abs_sub _ _
    _ ≤ |InducedReward π r s| + |γ * ∑ x, qnM π P s x * PolicyValue π' P r γ x|
        + |PolicyValue π' P r γ s| := by gcongr; exact abs_add_le _ _
    _ ≤ 1 + 1 / (1 - γ) + 1 / (1 - γ) := by gcongr
    _ = _ := by ring

/-- performance difference lemma with a general start vector `ρ` -/
lemma qn_pdl (hP : IsTransitionKernel P) (hπ : IsPolicy π) {π' : S → A → ℝ}
    (hπ' : IsPolicy π') {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) :
    PolicyGradTheory.ProjGA.valueAt π P r γ ρ - PolicyGradTheory.ProjGA.valueAt π' P r γ ρ =
      1 / (1 - γ) * ∑ s, PolicyGradTheory.ProjGA.visitation π P γ ρ s *
        ∑ a, π s a * PolicyGradTheory.ProjGA.advantage π' P r γ s a := by
  rw [qn_vis_sum hP hπ hγ0 hγ1 ρ _ _ (qn_adv_bound hP hπ hπ' hr hγ0 hγ1)]
  have hg : (1 - γ) ≠ 0 := by linarith
  rw [← mul_assoc, one_div_mul_cancel hg, one_mul]
  simp only [PolicyGradTheory.ProjGA.valueAt, ← Finset.sum_sub_distrib, ← mul_sub]
  congr 1; ext s0
  rw [qn_pdl_state hP hπ hπ' hr hγ0 hγ1]

end MDP

section TR
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

lemma qn_vis_nonneg {π : S → A → ℝ} {P : S → A → S → ℝ} (hP : IsTransitionKernel P)
    (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {ρ : S → ℝ}
    (hρ : PolicyGradTheory.ProjGA.IsDist ρ) (s : S) :
    0 ≤ PolicyGradTheory.ProjGA.visitation π P γ ρ s := by
  unfold PolicyGradTheory.ProjGA.visitation
  refine mul_nonneg (by linarith) (tsum_nonneg fun t => mul_nonneg (pow_nonneg hγ0 t)
    (Finset.sum_nonneg fun s0 _ => mul_nonneg (hρ.1 s0) ?_))
  rw [qn_occ_eq_pow]; exact qn_pow_nonneg hP hπ t s0 s

lemma qn_vis_total {π : S → A → ℝ} {P : S → A → S → ℝ} (hP : IsTransitionKernel P)
    (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {ρ : S → ℝ}
    (hρ : PolicyGradTheory.ProjGA.IsDist ρ) :
    ∑ s, PolicyGradTheory.ProjGA.visitation π P γ ρ s = 1 := by
  have h := qn_vis_sum hP hπ hγ0 hγ1 ρ (fun _ => 1) 1 (fun _ => by norm_num)
  simp only [mul_one] at h
  rw [h]
  simp_rw [qn_pow_rowsum hP hπ, mul_one, tsum_geometric_of_lt_one hγ0 hγ1, ← Finset.sum_mul,
    hρ.2, one_mul]
  field_simp [show (1 - γ) ≠ 0 by linarith]

lemma qn_jensen (q e : S → A → ℝ) (hq : ∀ s a, 0 ≤ q s a) (hs : ∑ s, ∑ a, q s a = 1) :
    ∑ s, ∑ a, q s a * |e s a| ≤ Real.sqrt (∑ s, ∑ a, q s a * e s a ^ 2) := by
  set m := ∑ s, ∑ a, q s a * |e s a| with hm
  have h0 : 0 ≤ ∑ s, ∑ a, q s a * (|e s a| - m) ^ 2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => mul_nonneg (hq s a) (sq_nonneg _)
  have h1 : ∑ s, ∑ a, q s a * (|e s a| - m) ^ 2 =
      ∑ s, ∑ a, q s a * e s a ^ 2 - 2 * m * m + m ^ 2 * 1 := by
    have : ∀ s a, q s a * (|e s a| - m) ^ 2 =
        q s a * e s a ^ 2 - 2 * m * (q s a * |e s a|) + m ^ 2 * q s a := by
      intro s a; rw [sub_sq, sq_abs]; ring
    simp_rw [this]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hm, hs]
  have h2 : m ^ 2 ≤ ∑ s, ∑ a, q s a * e s a ^ 2 := by nlinarith
  exact (le_abs_self m).trans (Real.abs_le_sqrt h2)

lemma qn_pol_le_one {π : S → A → ℝ} (hπ : IsPolicy π) (s : S) (a : A) : π s a ≤ 1 := by
  rw [← (hπ s).2]
  exact Finset.single_le_sum (fun b _ => (hπ s).1 b) (Finset.mem_univ a)

lemma qn_two_policy_bound (dd : S → ℝ) (hd : ∀ s, 0 ≤ dd s) (hds : ∑ s, dd s = 1)
    {π1 π2 : S → A → ℝ} (h1 : IsPolicy π1) (h2 : IsPolicy π2) (e : S → A → ℝ) :
    ∑ s, dd s * (∑ a, π1 s a * e s a - ∑ b, π2 s b * e s b) ≤
      2 * Real.sqrt (∑ s, ∑ a, dd s * e s a ^ 2) := by
  have hJ : ∀ π : S → A → ℝ, IsPolicy π →
      ∑ s, ∑ a, dd s * π s a * |e s a| ≤ Real.sqrt (∑ s, ∑ a, dd s * e s a ^ 2) := by
    intro π hπ
    have hq : ∀ s a, 0 ≤ dd s * π s a := fun s a => mul_nonneg (hd s) ((hπ s).1 a)
    have hsum : ∑ s, ∑ a, dd s * π s a = 1 := by
      simp_rw [← Finset.mul_sum, (hπ _).2, mul_one, hds]
    refine (qn_jensen (fun s a => dd s * π s a) e hq hsum).trans (Real.sqrt_le_sqrt ?_)
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => ?_
    have := qn_pol_le_one hπ s a
    have := hd s
    have := sq_nonneg (e s a)
    nlinarith [mul_nonneg (hd s) (sq_nonneg (e s a))]
  calc _ = ∑ s, ∑ a, (dd s * π1 s a * e s a - dd s * π2 s a * e s a) := by
        simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]
    _ ≤ ∑ s, ∑ a, (dd s * π1 s a * |e s a| + dd s * π2 s a * |e s a|) := by
        refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => ?_
        have h1' := mul_nonneg (hd s) ((h1 s).1 a)
        have h2' := mul_nonneg (hd s) ((h2 s).1 a)
        have := le_abs_self (e s a)
        have := neg_abs_le (e s a)
        nlinarith
    _ = ∑ s, ∑ a, dd s * π1 s a * |e s a| + ∑ s, ∑ a, dd s * π2 s a * |e s a| := by
        simp only [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (hJ π1 h1) (hJ π2 h2)
    _ = _ := by ring

lemma qn_ll_policy [Nonempty A] {d : ℕ} (φ : S → A → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) : IsPolicy (logLinearPolicy φ θ) :=
  fun s => ⟨fun a => (qn_ll_pos φ θ s a).le, qn_ll_sum φ θ s⟩

lemma qn_adv_decomp [Nonempty A] {d : ℕ} {P : S → A → S → ℝ} (hP : IsTransitionKernel P)
    {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (θ w : EuclideanSpace ℝ (Fin d))
    {π' : S → A → ℝ} (hπ' : IsPolicy π') (s : S) :
    ∑ a, π' s a * (PolicyGradTheory.ProjGA.advantage (logLinearPolicy φ θ) P r γ s a -
        inner ℝ w (φ s a - qnMean φ θ s)) =
      ∑ a, π' s a * (QFunction (logLinearPolicy φ θ) P r γ s a - inner ℝ w (φ s a)) -
      ∑ b, logLinearPolicy φ θ s b *
        (QFunction (logLinearPolicy φ θ) P r γ s b - inner ℝ w (φ s b)) := by
  set π := logLinearPolicy φ θ with hπdef
  have hπ : IsPolicy π := qn_ll_policy φ θ
  have h0 := qn_adv_sum_self hP hπ hr hγ0 hγ1 s
  unfold PolicyGradTheory.ProjGA.advantage at h0
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hπ s).2, one_mul] at h0
  have hM : inner ℝ w (qnMean φ θ s) = ∑ b, π s b * inner ℝ w (φ s b) := by
    simp [qnMean, inner_sum, inner_smul_right, hπdef]
  unfold PolicyGradTheory.ProjGA.advantage
  have : ∀ a, π' s a * (QFunction π P r γ s a - PolicyValue π P r γ s - inner ℝ w (φ s a - qnMean φ θ s)) =
      π' s a * (QFunction π P r γ s a - inner ℝ w (φ s a)) -
        π' s a * (PolicyValue π P r γ s - inner ℝ w (qnMean φ θ s)) := by
    intro a; rw [inner_sub_right]; ring
  simp_rw [this]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (hπ' s).2, one_mul, hM]
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

theorem transfer_term_bound_core [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (θ w : EuclideanSpace ℝ (Fin d)) :
    (∑ s : S, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s *
      ∑ a : A, πstar s a *
        (PolicyGradTheory.ProjGA.advantage (logLinearPolicy φ θ) P r γ s a -
          inner ℝ w (gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ))) ≤
      2 * Real.sqrt ((Fintype.card A : ℝ) *
        qLoss P r γ φ w θ (dstar P γ ρ πstar)) := by
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  simp_rw [qn_ll_grad]
  simp_rw [qn_adv_decomp hP hr hγ0 hγ1 φ θ w hπstar]
  refine (qn_two_policy_bound _ (qn_vis_nonneg hP hπstar hγ0 hγ1 hρ)
    (qn_vis_total hP hπstar hγ0 hγ1 hρ) hπstar (qn_ll_policy φ θ) _).trans_eq ?_
  congr 2
  have hA : (Fintype.card A : ℝ) ≠ 0 := by positivity
  simp only [qLoss, dstar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
  field_simp

end TR

end PolicyGradTheory.QNPG

open PolicyGradTheory.QNPG


theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (θ w : EuclideanSpace ℝ (Fin d)) :
    (∑ s : S, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s *
      ∑ a : A, πstar s a *
        (PolicyGradTheory.ProjGA.advantage (logLinearPolicy φ θ) P r γ s a -
          inner ℝ w (gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ))) ≤
      2 * Real.sqrt ((Fintype.card A : ℝ) *
        qLoss P r γ φ w θ (dstar P γ ρ πstar)) := by
  exact transfer_term_bound_core P r γ hM ρ hρ πstar hπstar φ θ w
