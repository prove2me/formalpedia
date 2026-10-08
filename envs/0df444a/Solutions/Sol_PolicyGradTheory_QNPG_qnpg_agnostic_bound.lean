-- Prove2me | solution 1 for PolicyGradTheory.QNPG.qnpg_agnostic_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:27:39.523198+00:00
-- url     : https://prove2.me/submissions/7bbebd02-7981-40ed-8230-8118e452245b

import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

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

lemma qn_smooth_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (hf : Differentiable ℝ f) (β : ℝ)
    (hs : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖) (x v : E) :
    f x + inner ℝ (gradient f x) v - β / 2 * ‖v‖ ^ 2 ≤ f (x + v) := by
  let g : ℝ → ℝ := fun t => f (x + t • v) - t * inner ℝ (gradient f x) v + β / 2 * t ^ 2 * ‖v‖ ^ 2
  let g' : ℝ → ℝ := fun t => inner ℝ (gradient f (x + t • v)) v - inner ℝ (gradient f x) v +
    β * t * ‖v‖ ^ 2
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have hline : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hfd : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f (x + t • v))) (x + t • v) :=
      hasGradientAt_iff_hasFDerivAt.mp (hf _).hasGradientAt
    have h1 := hfd.comp_hasDerivAt t hline
    rw [InnerProductSpace.toDual_apply_apply] at h1
    have h2 := ((hasDerivAt_id t).mul_const (inner ℝ (gradient f x) v))
    have h3 := (((hasDerivAt_id t).pow 2).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
    have := (h1.sub h2).add h3
    refine this.congr_deriv ?_
    simp only [g', id, Nat.cast_ofNat, pow_one, one_mul, mul_one]
    norm_num only
    ring
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hnn : 0 ≤ g' ξ := by
    have h1 := hs (x + ξ • v) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hξ.1] at h1
    have h2 := real_inner_le_norm (gradient f (x + ξ • v) - gradient f x) v
    rw [inner_sub_left] at h2
    have h3 : ‖gradient f (x + ξ • v) - gradient f x‖ * ‖v‖ ≤ β * (ξ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h4 := abs_real_inner_le_norm (gradient f (x + ξ • v) - gradient f x) v
    rw [inner_sub_left] at h4
    have h5 := neg_abs_le (inner ℝ (gradient f (x + ξ • v)) v - inner ℝ (gradient f x) v)
    simp only [g']
    nlinarith
  rw [hξe] at hnn
  rw [sub_zero, div_one] at hnn
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, mul_one,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at hnn
  linarith

theorem npg_regret_core {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (πtilde : S → A → ℝ) (hπtilde : IsPolicy πtilde)
    (pol : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (hpol : ∀ x, IsPolicy (pol x))
    (hpos : ∀ x s a, 0 < pol x s a)
    (β : ℝ) (hβ : 0 ≤ β)
    (hdiff : ∀ s a, Differentiable ℝ (fun z => Real.log (pol z s a)))
    (hsmooth : ∀ s a x y,
      ‖gradient (fun z => Real.log (pol z s a)) x -
        gradient (fun z => Real.log (pol z s a)) y‖ ≤ β * ‖x - y‖)
    (η W : ℝ) (hη : 0 < η)
    (T : ℕ) (hT : 0 < T)
    (θ w : ℕ → EuclideanSpace ℝ (Fin d))
    (hupdate : ∀ t < T, θ (t + 1) = θ t + η • w t)
    (hinit : ∀ s a, pol (θ 0) s a = 1 / (Fintype.card A : ℝ))
    (hw : ∀ t ≤ T, ‖w t‖ ≤ W) :
    ∃ t : ℕ, t < T ∧
      PolicyGradTheory.ProjGA.valueAt πtilde P r γ ρ - PolicyGradTheory.ProjGA.valueAt (pol (θ t)) P r γ ρ ≤
        (1 / (1 - γ)) *
          (Real.log (Fintype.card A : ℝ) / (η * T) + η * β * W ^ 2 / 2 +
            (1 / (T : ℝ)) * ∑ i ∈ Finset.range T,
              ∑ s : S, PolicyGradTheory.ProjGA.visitation πtilde P γ ρ s *
                ∑ a : A, πtilde s a *
                  (PolicyGradTheory.ProjGA.advantage (pol (θ i)) P r γ s a -
                    inner ℝ (w i) (gradient (fun z => Real.log (pol z s a)) (θ i)))) := by
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  have hg : 0 < 1 - γ := by linarith
  set dt : S → ℝ := fun s => PolicyGradTheory.ProjGA.visitation πtilde P γ ρ s with hdt
  have hd0 : ∀ s, 0 ≤ dt s := qn_vis_nonneg hP hπtilde hγ0 hγ1 hρ
  have hd1 : ∑ s, dt s = 1 := qn_vis_total hP hπtilde hγ0 hγ1 hρ
  have hq1 : ∑ s, dt s * ∑ a, πtilde s a = 1 := by simp [(hπtilde _).2, hd1]
  set Φ : ℕ → ℝ := fun t => ∑ s, dt s * ∑ a, πtilde s a * (-Real.log (pol (θ t) s a)) with hΦ
  set err : ℕ → ℝ := fun i => ∑ s, dt s * ∑ a, πtilde s a *
    (PolicyGradTheory.ProjGA.advantage (pol (θ i)) P r γ s a -
      inner ℝ (w i) (gradient (fun z => Real.log (pol z s a)) (θ i))) with herr
  set G : ℕ → ℝ := fun i => ∑ s, dt s * ∑ a, πtilde s a *
      inner ℝ (w i) (gradient (fun z => Real.log (pol z s a)) (θ i)) with hG
  set c : ℝ := β * η ^ 2 * W ^ 2 / 2 with hc
  have hstep : ∀ t < T, η * G t ≤ Φ t - Φ (t + 1) + c := by
    intro t ht
    have hpt : ∀ s a, η * inner ℝ (w t) (gradient (fun z => Real.log (pol z s a)) (θ t)) ≤
        Real.log (pol (θ (t + 1)) s a) - Real.log (pol (θ t) s a) + c := by
      intro s a
      have h := qn_smooth_lower (fun z => Real.log (pol z s a)) (hdiff s a) β (hsmooth s a)
        (θ t) (η • w t)
      rw [hupdate t ht]
      have hn : ‖η • w t‖ ^ 2 = η ^ 2 * ‖w t‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hin : inner ℝ (gradient (fun z => Real.log (pol z s a)) (θ t)) (η • w t) =
          η * inner ℝ (w t) (gradient (fun z => Real.log (pol z s a)) (θ t)) := by
        rw [inner_smul_right, real_inner_comm]
      have hW : ‖w t‖ ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hw t ht.le) 2
      rw [hn, hin] at h
      have : β / 2 * (η ^ 2 * ‖w t‖ ^ 2) ≤ c := by
        rw [hc]; have := mul_le_mul_of_nonneg_left hW (mul_nonneg hβ (sq_nonneg η)); nlinarith
      linarith
    have e1 : η * G t = ∑ s, dt s * ∑ a, πtilde s a *
        (η * inner ℝ (w t) (gradient (fun z => Real.log (pol z s a)) (θ t))) := by
      simp only [hG, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    have e2 : ∑ s, dt s * ∑ a, πtilde s a *
        (Real.log (pol (θ (t + 1)) s a) - Real.log (pol (θ t) s a) + c) = Φ t - Φ (t + 1) + c := by
      have : ∀ s, dt s * ∑ a, πtilde s a *
          (Real.log (pol (θ (t + 1)) s a) - Real.log (pol (θ t) s a) + c) =
          dt s * ∑ a, πtilde s a * (-Real.log (pol (θ t) s a)) -
          dt s * ∑ a, πtilde s a * (-Real.log (pol (θ (t + 1)) s a)) + c * (dt s * ∑ a, πtilde s a) := by
        intro s
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hq1, mul_one]
    rw [e1, ← e2]
    refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt s a) ((hπtilde s).1 a)) (hd0 s)
  have hpdl : ∀ t, PolicyGradTheory.ProjGA.valueAt πtilde P r γ ρ -
      PolicyGradTheory.ProjGA.valueAt (pol (θ t)) P r γ ρ = 1 / (1 - γ) * (G t + err t) := by
    intro t
    rw [qn_pdl hP hπtilde (hpol (θ t)) hr hγ0 hγ1 ρ]
    congr 1
    simp only [hG, herr, ← Finset.sum_add_distrib, ← mul_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hbound : ∀ t < T, PolicyGradTheory.ProjGA.valueAt πtilde P r γ ρ -
      PolicyGradTheory.ProjGA.valueAt (pol (θ t)) P r γ ρ ≤
        1 / (1 - γ) * ((Φ t - Φ (t + 1)) / η + c / η + err t) := by
    intro t ht
    rw [hpdl t]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h := hstep t ht
    have : G t ≤ (Φ t - Φ (t + 1)) / η + c / η := by
      rw [← add_div, le_div_iff₀ hη]; linarith
    linarith
  have hΦ0 : Φ 0 = Real.log (Fintype.card A : ℝ) := by
    have h0 : ∀ s a, -Real.log (pol (θ 0) s a) = Real.log (Fintype.card A : ℝ) := by
      intro s a; rw [hinit, one_div, Real.log_inv, neg_neg]
    simp only [hΦ, h0, ← Finset.sum_mul]
    have hs : ∀ s, ∑ a, πtilde s a = 1 := fun s => (hπtilde s).2
    simp only [hs, one_mul, ← Finset.sum_mul, hd1]
  have hΦT : 0 ≤ Φ T := by
    refine Finset.sum_nonneg fun s _ => mul_nonneg (hd0 s) (Finset.sum_nonneg fun a _ =>
      mul_nonneg ((hπtilde s).1 a) ?_)
    rw [neg_nonneg]
    exact Real.log_nonpos (hpos _ s a).le (qn_pol_le_one (hpol _) s a)
  by_contra hcon
  push_neg at hcon
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hT.ne')
    (fun t ht => lt_of_lt_of_le (hcon t (Finset.mem_range.mp ht))
      (hbound t (Finset.mem_range.mp ht)))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hs1 : ∑ x ∈ Finset.range T, (Φ x - Φ (x + 1)) / η = (Φ 0 - Φ T) / η := by
    rw [← Finset.sum_div, Finset.sum_range_sub']
  have hs2 : ∑ x ∈ Finset.range T, c / η = T * (c / η) := by simp
  have hL : (T : ℝ) * (1 / (1 - γ) * (Real.log (Fintype.card A : ℝ) / (η * T) + η * β * W ^ 2 / 2 +
      1 / (T : ℝ) * ∑ i ∈ Finset.range T, err i)) =
      1 / (1 - γ) * (Real.log (Fintype.card A : ℝ) / η + T * (η * β * W ^ 2 / 2) +
        ∑ i ∈ Finset.range T, err i) := by
    field_simp
  have hc' : c / η = η * β * W ^ 2 / 2 := by rw [hc]; field_simp
  rw [hs1, hs2, hL, hc', hΦ0] at hsum
  have h3 : (Real.log (Fintype.card A : ℝ) - Φ T) / η ≤ Real.log (Fintype.card A : ℝ) / η :=
    div_le_div_of_nonneg_right (by linarith) hη.le
  have h1g : 0 < 1 / (1 - γ) := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add_right (add_le_add_right h3
    ((T : ℝ) * (η * β * W ^ 2 / 2))) (∑ i ∈ Finset.range T, err i)) h1g.le
  linarith


section EST
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

lemma qn_opt_quad {d : ℕ} (υ : S × A → ℝ) (Qf : S → A → ℝ) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (W : ℝ) (w ws : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ ≤ W) (hws : ‖ws‖ ≤ W)
    (hopt : ∀ v, ‖v‖ ≤ W → ∑ s, ∑ a, υ (s, a) * (Qf s a - inner ℝ ws (φ s a)) ^ 2 ≤
      ∑ s, ∑ a, υ (s, a) * (Qf s a - inner ℝ v (φ s a)) ^ 2) :
    quadForm φ υ (w - ws) ≤ ∑ s, ∑ a, υ (s, a) * (Qf s a - inner ℝ w (φ s a)) ^ 2 -
      ∑ s, ∑ a, υ (s, a) * (Qf s a - inner ℝ ws (φ s a)) ^ 2 := by
  set u := w - ws with hu
  set L : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun v => ∑ s, ∑ a, υ (s, a) * (Qf s a - inner ℝ v (φ s a)) ^ 2 with hL
  set c := ∑ s, ∑ a, υ (s, a) * (Qf s a - inner ℝ ws (φ s a)) * inner ℝ u (φ s a) with hc
  set q := quadForm φ υ u with hq
  have hexp : ∀ l : ℝ, L (ws + l • u) = L ws - 2 * l * c + l ^ 2 * q := by
    intro l
    simp only [hL, hc, hq, quadForm, inner_add_left, inner_smul_left, conj_trivial,
      Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hball : ∀ l : ℝ, 0 ≤ l → l ≤ 1 → ‖ws + l • u‖ ≤ W := by
    intro l h0 h1
    have : ws + l • u = (1 - l) • ws + l • w := by
      rw [hu, smul_sub, sub_smul, one_smul]; abel
    rw [this]
    calc ‖(1 - l) • ws + l • w‖ ≤ ‖(1 - l) • ws‖ + ‖l • w‖ := norm_add_le _ _
      _ = (1 - l) * ‖ws‖ + l * ‖w‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
      _ ≤ (1 - l) * W + l * W := by gcongr
      _ = W := by ring
  have hineq : ∀ l : ℝ, 0 < l → l ≤ 1 → 0 ≤ -2 * l * c + l ^ 2 * q := by
    intro l h0 h1
    have := hopt _ (hball l h0.le h1)
    have h2 := hexp l
    simp only [hL] at h2
    linarith
  have hc0 : c ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    rcases le_or_gt q 0 with hq0 | hq0
    · have := hineq 1 one_pos le_rfl
      nlinarith
    · set l := min 1 (c / q) with hl
      have hl0 : 0 < l := lt_min one_pos (div_pos hcon hq0)
      have hl1 : l ≤ 1 := min_le_left _ _
      have hlq : l * q ≤ c := by
        have := min_le_right 1 (c / q)
        rw [← hl] at this
        calc l * q ≤ c / q * q := mul_le_mul_of_nonneg_right this hq0.le
          _ = c := div_mul_cancel₀ c hq0.ne'
      have := hineq l hl0 hl1
      nlinarith
  have h1 := hexp 1
  rw [one_smul, hu, add_sub_cancel] at h1
  simp only [hL] at h1
  rw [h1]
  nlinarith

lemma qn_sav_ge {π : S → A → ℝ} {P : S → A → S → ℝ} (hP : IsTransitionKernel P)
    (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {ν : S × A → ℝ}
    (hν : PolicyGradTheory.ProjGA.IsDist ν) (s : S) (a : A) :
    (1 - γ) * ν (s, a) ≤ saVisitation π P γ ν s a := by
  unfold saVisitation
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine le_add_of_nonneg_right (tsum_nonneg fun t => mul_nonneg (pow_nonneg hγ0 _)
    (Finset.sum_nonneg fun s0 _ => Finset.sum_nonneg fun a0 _ => mul_nonneg (hν.1 _)
      (Finset.sum_nonneg fun s1 _ => mul_nonneg (mul_nonneg ((hP s0 a0).1 s1) ?_) ((hπ s).1 a))))
  rw [qn_occ_eq_pow]; exact qn_pow_nonneg hP hπ t s1 s

lemma qn_quad_neg {d : ℕ} (φ : S → A → EuclideanSpace ℝ (Fin d)) (υ : S × A → ℝ)
    (u : EuclideanSpace ℝ (Fin d)) : quadForm φ υ (-u) = quadForm φ υ u := by
  simp [quadForm, inner_neg_left]

theorem qn_est_bound [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (ν : S × A → ℝ) (hν : PolicyGradTheory.ProjGA.IsDist ν)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ v, quadForm φ (dstar P γ ρ πstar) v ≤ κ * quadForm φ ν v)
    (W : ℝ) (θ w ws : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ ≤ W) (hws : ‖ws‖ ≤ W)
    (hopt : ∀ v, ‖v‖ ≤ W →
      qLoss P r γ φ ws θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν) ≤
      qLoss P r γ φ v θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν)) :
    ∑ s, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s * ∑ a, πstar s a *
      inner ℝ (ws - w) (gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ) ≤
    2 * Real.sqrt ((Fintype.card A : ℝ) * κ / (1 - γ) *
      (qLoss P r γ φ w θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν) -
        qLoss P r γ φ ws θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν))) := by
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  have hg : 0 < 1 - γ := by linarith
  set u := ws - w with hu
  simp_rw [qn_ll_grad]
  have hdec : ∀ s, ∑ a, πstar s a * inner ℝ u (φ s a - qnMean φ θ s) =
      ∑ a, πstar s a * inner ℝ u (φ s a) - ∑ b, logLinearPolicy φ θ s b * inner ℝ u (φ s b) := by
    intro s
    simp only [inner_sub_right, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hπstar s).2,
      one_mul, qnMean, inner_sum, inner_smul_right]
  simp_rw [hdec]
  refine (qn_two_policy_bound _ (qn_vis_nonneg hP hπstar hγ0 hγ1 hρ)
    (qn_vis_total hP hπstar hγ0 hγ1 hρ) hπstar (qn_ll_policy φ θ)
    (fun s a => inner ℝ u (φ s a))).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  set dt := onPolicyMeasure (logLinearPolicy φ θ) P γ ν with hdt
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have h1 : ∑ s, ∑ a, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s * inner ℝ u (φ s a) ^ 2 =
      (Fintype.card A : ℝ) * quadForm φ (dstar P γ ρ πstar) u := by
    simp only [quadForm, dstar, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
    field_simp
  have h3 : quadForm φ ν u ≤ quadForm φ dt u / (1 - γ) := by
    rw [le_div_iff₀ hg]
    simp only [quadForm, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => ?_
    have := qn_sav_ge hP (qn_ll_policy φ θ) hγ0 hγ1 hν s a
    have h0 := sq_nonneg (inner ℝ u (φ s a))
    simp only [hdt, onPolicyMeasure]
    nlinarith
  have h4 : quadForm φ dt u ≤ qLoss P r γ φ w θ dt - qLoss P r γ φ ws θ dt := by
    have : u = -(w - ws) := by rw [hu]; abel
    rw [this, qn_quad_neg]
    exact qn_opt_quad dt _ φ W w ws hw hws hopt
  rw [h1]
  calc (Fintype.card A : ℝ) * quadForm φ (dstar P γ ρ πstar) u
      ≤ (Fintype.card A : ℝ) * (κ * quadForm φ ν u) := mul_le_mul_of_nonneg_left (hκ u) hA.le
    _ ≤ (Fintype.card A : ℝ) * (κ * (quadForm φ dt u / (1 - γ))) := by gcongr
    _ ≤ (Fintype.card A : ℝ) * (κ * ((qLoss P r γ φ w θ dt - qLoss P r γ φ ws θ dt) / (1 - γ))) := by
        gcongr
    _ = _ := by ring

end EST

section CONT
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] {d : ℕ}

lemma qn_ll_cont (φ : S → A → EuclideanSpace ℝ (Fin d)) (s : S) (a : A) :
    Continuous (fun θ : EuclideanSpace ℝ (Fin d) => logLinearPolicy φ θ s a) := by
  simp only [qn_ll_eq]
  exact (continuous_id.inner continuous_const).rexp.div
    (continuous_finset_sum _ fun b _ => (continuous_id.inner continuous_const).rexp)
    (fun θ => (qn_Z_pos φ θ s).ne')

lemma qn_occ_cont (φ : S → A → EuclideanSpace ℝ (Fin d)) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) :
    ∀ s, Continuous (fun θ : EuclideanSpace ℝ (Fin d) =>
      OccupationDist (logLinearPolicy φ θ) P s0 t s) := by
  induction t with
  | zero => intro s; simp only [OccupationDist]; exact continuous_const
  | succ t ih =>
    intro s
    simp only [OccupationDist, InducedTransition]
    exact continuous_finset_sum _ fun x _ => (ih x).mul
      (continuous_finset_sum _ fun a _ => (qn_ll_cont φ x a).mul continuous_const)

lemma qn_V_cont (φ : S → A → EuclideanSpace ℝ (Fin d)) {P : S → A → S → ℝ}
    (hP : IsTransitionKernel P) {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    Continuous (fun θ : EuclideanSpace ℝ (Fin d) => PolicyValue (logLinearPolicy φ θ) P r γ s) := by
  simp only [PolicyValue]
  refine continuous_tsum (u := fun t => γ ^ t * 1) (fun t => ?_)
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right 1) (fun t θ => ?_)
  · exact continuous_const.mul (continuous_finset_sum _ fun s' _ => (qn_occ_cont φ P s t s').mul
      (continuous_finset_sum _ fun a _ => (qn_ll_cont φ s' a).mul continuous_const))
  · simp only [qn_occ_eq_pow]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    exact mul_le_mul_of_nonneg_left (qn_E_bound hP (qn_ll_policy φ θ) t s _ 1
      (qn_reward_bound (qn_ll_policy φ θ) hr)) (pow_nonneg hγ0 t)

lemma qn_Q_cont (φ : S → A → EuclideanSpace ℝ (Fin d)) {P : S → A → S → ℝ}
    (hP : IsTransitionKernel P) {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    Continuous (fun θ : EuclideanSpace ℝ (Fin d) => QFunction (logLinearPolicy φ θ) P r γ s a) := by
  simp only [QFunction]
  exact continuous_const.add (continuous_const.mul (continuous_finset_sum _ fun s' _ =>
    continuous_const.mul (qn_V_cont φ hP hr hγ0 hγ1 s')))

lemma qn_sav_cont (φ : S → A → EuclideanSpace ℝ (Fin d)) {P : S → A → S → ℝ}
    (hP : IsTransitionKernel P) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {ν : S × A → ℝ}
    (hν : PolicyGradTheory.ProjGA.IsDist ν) (s : S) (a : A) :
    Continuous (fun θ : EuclideanSpace ℝ (Fin d) =>
      saVisitation (logLinearPolicy φ θ) P γ ν s a) := by
  simp only [saVisitation]
  refine continuous_const.mul (continuous_const.add ?_)
  refine continuous_tsum (u := fun t => γ ^ (t + 1) * 1) (fun t => ?_)
    (((summable_geometric_of_lt_one hγ0 hγ1).mul_left γ).mul_right 1 |>.congr
      (fun t => by ring)) (fun t θ => ?_)
  · exact continuous_const.mul (continuous_finset_sum _ fun s0 _ => continuous_finset_sum _
      fun a0 _ => continuous_const.mul (continuous_finset_sum _ fun s1 _ =>
        (continuous_const.mul (qn_occ_cont φ P s1 t s)).mul (qn_ll_cont φ s a)))
  · have hπ := qn_ll_policy φ θ
    have hb : ∀ s0 a0 s1, 0 ≤ P s0 a0 s1 * OccupationDist (logLinearPolicy φ θ) P s1 t s *
        logLinearPolicy φ θ s a ∧ P s0 a0 s1 * OccupationDist (logLinearPolicy φ θ) P s1 t s *
        logLinearPolicy φ θ s a ≤ P s0 a0 s1 := by
      intro s0 a0 s1
      rw [qn_occ_eq_pow]
      have ho0 := qn_pow_nonneg hP hπ t s1 s
      have ho1 := qn_pow_le_one hP hπ t s1 s
      have hp0 := (hπ s).1 a
      have hp1 := qn_pol_le_one hπ s a
      have hP0 := (hP s0 a0).1 s1
      refine ⟨mul_nonneg (mul_nonneg hP0 ho0) hp0, ?_⟩
      rw [mul_assoc]
      exact mul_le_of_le_one_right hP0 (mul_le_one₀ ho1 hp0 hp1)
    have hin : ∀ s0 a0, 0 ≤ ∑ s1, P s0 a0 s1 * OccupationDist (logLinearPolicy φ θ) P s1 t s *
        logLinearPolicy φ θ s a ∧ ∑ s1, P s0 a0 s1 * OccupationDist (logLinearPolicy φ θ) P s1 t s *
        logLinearPolicy φ θ s a ≤ 1 := by
      intro s0 a0
      refine ⟨Finset.sum_nonneg fun s1 _ => (hb s0 a0 s1).1, ?_⟩
      rw [← (hP s0 a0).2]
      exact Finset.sum_le_sum fun s1 _ => (hb s0 a0 s1).2
    have hout0 : 0 ≤ ∑ s0, ∑ a0, ν (s0, a0) * ∑ s1, P s0 a0 s1 *
        OccupationDist (logLinearPolicy φ θ) P s1 t s * logLinearPolicy φ θ s a :=
      Finset.sum_nonneg fun s0 _ => Finset.sum_nonneg fun a0 _ =>
        mul_nonneg (hν.1 _) (hin s0 a0).1
    have hout1 : ∑ s0, ∑ a0, ν (s0, a0) * ∑ s1, P s0 a0 s1 *
        OccupationDist (logLinearPolicy φ θ) P s1 t s * logLinearPolicy φ θ s a ≤ 1 := by
      calc _ ≤ ∑ s0, ∑ a0, ν (s0, a0) * 1 :=
            Finset.sum_le_sum fun s0 _ => Finset.sum_le_sum fun a0 _ =>
              mul_le_mul_of_nonneg_left (hin s0 a0).2 (hν.1 _)
        _ = 1 := by simp only [mul_one]; rw [← Fintype.sum_prod_type']; exact hν.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 _), abs_of_nonneg hout0]
    exact mul_le_mul_of_nonneg_left hout1 (pow_nonneg hγ0 _)

lemma qn_qLoss_cont (φ : S → A → EuclideanSpace ℝ (Fin d)) {P : S → A → S → ℝ}
    (hP : IsTransitionKernel P) {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (υ : S × A → ℝ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      qLoss P r γ φ p.1 p.2 υ) := by
  simp only [qLoss]
  exact continuous_finset_sum _ fun s _ => continuous_finset_sum _ fun a _ =>
    continuous_const.mul ((((qn_Q_cont φ hP hr hγ0 hγ1 s a).comp continuous_snd).sub
      (continuous_fst.inner continuous_const)).pow 2)

lemma qn_qLossOn_cont (φ : S → A → EuclideanSpace ℝ (Fin d)) {P : S → A → S → ℝ}
    (hP : IsTransitionKernel P) {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {ν : S × A → ℝ}
    (hν : PolicyGradTheory.ProjGA.IsDist ν) :
    Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      qLoss P r γ φ p.1 p.2 (onPolicyMeasure (logLinearPolicy φ p.2) P γ ν)) := by
  simp only [qLoss, onPolicyMeasure]
  exact continuous_finset_sum _ fun s _ => continuous_finset_sum _ fun a _ =>
    ((qn_sav_cont φ hP hγ0 hγ1 hν s a).comp continuous_snd).mul
      ((((qn_Q_cont φ hP hr hγ0 hγ1 s a).comp continuous_snd).sub
      (continuous_fst.inner continuous_const)).pow 2)

end CONT

section INT

lemma qn_final_alg (A : Type) [Fintype A] (B W κ γ : ℝ) (T : ℕ) (η εstat εbias : ℝ)
    (hB : 0 < B) (hW : 0 < W) (hκnonneg : 0 ≤ κ) (hg : 0 < 1 - γ) (hTpos : (0 : ℝ) < T)
    (hLpos : 0 < Real.log (Fintype.card A : ℝ))
    (hη : η = Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / (B ^ 2 * W ^ 2 * T))) :
    1 / (1 - γ) * ((Real.log (Fintype.card A : ℝ) / (η * T) + η * B ^ 2 * W ^ 2 / 2) +
      1 / (T : ℝ) * ∑ i ∈ Finset.range T,
      (2 * Real.sqrt ((Fintype.card A : ℝ) * εbias) +
        2 * Real.sqrt ((Fintype.card A : ℝ) * κ / (1 - γ) * εstat))) =
      B * W / (1 - γ) * Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / T) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * κ * εstat / (1 - γ) ^ 3) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * εbias) / (1 - γ) := by
  set K : ℝ := (Fintype.card A : ℝ) * κ / (1 - γ) with hK
  set C0 : ℝ := Real.log (Fintype.card A : ℝ) / (η * T) + η * B ^ 2 * W ^ 2 / 2 with hC0
  show 1 / (1 - γ) * (C0 + 1 / (T : ℝ) * ∑ i ∈ Finset.range T,
    (2 * Real.sqrt ((Fintype.card A : ℝ) * εbias) + 2 * Real.sqrt (K * εstat))) =
    B * W / (1 - γ) * Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / T) +
    Real.sqrt (4 * (Fintype.card A : ℝ) * κ * εstat / (1 - γ) ^ 3) +
    Real.sqrt (4 * (Fintype.card A : ℝ) * εbias) / (1 - γ) 
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h4b : Real.sqrt (4 * (Fintype.card A : ℝ) * εbias) =
      2 * Real.sqrt ((Fintype.card A : ℝ) * εbias) := by
    rw [show 4 * (Fintype.card A : ℝ) * εbias = 2 ^ 2 * ((Fintype.card A : ℝ) * εbias) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h4s : Real.sqrt (4 * (Fintype.card A : ℝ) * κ * εstat / (1 - γ) ^ 3) =
      2 / (1 - γ) * Real.sqrt (K * εstat) := by
    rw [show 4 * (Fintype.card A : ℝ) * κ * εstat / (1 - γ) ^ 3 =
        (2 / (1 - γ)) ^ 2 * (K * εstat) by rw [hK]; field_simp; ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg (by norm_num) hg.le)]
  have hC : C0 = B * W * Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / T) := by
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / T) := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (by positivity)
    have hs2 : s ^ 2 = 2 * Real.log (Fintype.card A : ℝ) / T := by
      rw [hs, Real.sq_sqrt (by positivity)]
    have hηs : η = s / (B * W) := by
      rw [hη, hs, show 2 * Real.log (Fintype.card A : ℝ) / (B ^ 2 * W ^ 2 * T) =
        (2 * Real.log (Fintype.card A : ℝ) / T) / (B * W) ^ 2 by field_simp,
        Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hLs : Real.log (Fintype.card A : ℝ) = s ^ 2 * T / 2 := by
      rw [hs2]; field_simp
    rw [← hs, hC0, hηs, hLs]
    field_simp
    ring
  rw [h4b, h4s, hC]
  field_simp
  ring


lemma qn_int_cont {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    {Z : Type*} [NormedAddCommGroup Z] [ProperSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (H : Z → ℝ) (hH : Continuous H) (z : Ω → Z) (hz : Measurable z) (R : ℝ)
    (hR : ∀ ω, ‖z ω‖ ≤ R) : Integrable (fun ω => H (z ω)) ℙ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Z) R).exists_bound_of_continuousOn hH.continuousOn
  refine Integrable.of_bound (hH.measurable.comp hz).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _ ?_)
  simpa using hR ω

lemma qn_sqrt_integral {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (X : Ω → ℝ) (hX0 : ∀ ω, 0 ≤ X ω) (hX : Integrable X ℙ)
    (hs : Integrable (fun ω => Real.sqrt (X ω)) ℙ) :
    ∫ ω, Real.sqrt (X ω) ∂ℙ ≤ Real.sqrt (∫ ω, X ω ∂ℙ) := by
  set m := ∫ ω, Real.sqrt (X ω) ∂ℙ with hm
  have h0 : 0 ≤ ∫ ω, (X ω - 2 * m * Real.sqrt (X ω) + m ^ 2) ∂ℙ := by
    refine integral_nonneg fun ω => ?_
    simp only [Pi.zero_apply]
    have := Real.sq_sqrt (hX0 ω)
    nlinarith [sq_nonneg (Real.sqrt (X ω) - m)]
  have hi1 : Integrable (fun ω => X ω - 2 * m * Real.sqrt (X ω)) ℙ := hX.sub (hs.const_mul _)
  have hi2 : Integrable (fun ω => 2 * m * Real.sqrt (X ω)) ℙ := hs.const_mul _
  rw [integral_add hi1 (integrable_const _), integral_sub hX hi2, integral_const_mul, ← hm] at h0
  simp only [integral_const, probReal_univ, one_smul] at h0
  have h2 : m ^ 2 ≤ ∫ ω, X ω ∂ℙ := by nlinarith
  exact (le_abs_self m).trans (Real.abs_le_sqrt h2)

lemma qn_params_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (η : ℝ)
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (T : ℕ) (hwm : ∀ t < T, Measurable (w t))
    (t : ℕ) (ht : t < T) : Measurable (qnpgParams η w t) := by
  unfold qnpgParams
  exact (Finset.measurable_sum _ fun i hi =>
    hwm i (lt_trans (Finset.mem_range.mp hi) ht)).const_smul η

lemma qn_params_norm {d : ℕ} {Ω : Type*} (η : ℝ) (hη : 0 ≤ η)
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (T : ℕ) (W : ℝ)
    (hwW : ∀ t < T, ∀ ω, ‖w t ω‖ ≤ W) (t : ℕ) (ht : t < T) (ω : Ω) :
    ‖qnpgParams η w t ω‖ ≤ η * (t * W) := by
  unfold qnpgParams
  rw [norm_smul, Real.norm_of_nonneg hη]
  refine mul_le_mul_of_nonneg_left ?_ hη
  refine (norm_sum_le _ _).trans ?_
  have := Finset.sum_le_sum (s := Finset.range t) (fun i hi =>
    hwW i (lt_trans (Finset.mem_range.mp hi) ht) ω)
  simpa using this

theorem qnpg_core {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] (d : ℕ)
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (ν : S × A → ℝ) (hν : PolicyGradTheory.ProjGA.IsDist ν)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (B : ℝ) (hB : 0 < B) (hφ : ∀ s a, ‖φ s a‖ ≤ B)
    (W : ℝ) (hW : 0 < W)
    (κ : ℝ) (hκnonneg : 0 ≤ κ)
    (hκ : ∀ v, quadForm φ (dstar P γ ρ πstar) v ≤ κ * quadForm φ ν v)
    (T : ℕ) (hT : 0 < T)
    (η : ℝ) (hη : η = Real.sqrt (2 * Real.log (Fintype.card A : ℝ) /
      (B ^ 2 * W ^ 2 * T)))
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (w wstar : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hwm : ∀ t < T, Measurable (w t))
    (hwstarm : ∀ t < T, Measurable (wstar t))
    (hwW : ∀ t < T, ∀ ω, ‖w t ω‖ ≤ W)
    (hwstar : ∀ t < T, ∀ ω,
      ‖wstar t ω‖ ≤ W ∧
        ∀ v, ‖v‖ ≤ W →
          qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
            (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν) ≤
          qLoss P r γ φ v (qnpgParams η w t ω)
            (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν))
    (εstat εbias : ℝ)
    (hstat : ∀ t < T,
      (∫ ω, (qLoss P r γ φ (w t ω) (qnpgParams η w t ω)
                (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν) -
              qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
                (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν)) ∂ ℙ) ≤ εstat)
    (hbias : ∀ t < T,
      (∫ ω, qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
        (dstar P γ ρ πstar) ∂ ℙ) ≤ εbias) :
    (∫ ω, (Finset.range T).inf' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT))
      (fun t => PolicyGradTheory.ProjGA.valueAt πstar P r γ ρ -
        PolicyGradTheory.ProjGA.valueAt (logLinearPolicy φ (qnpgParams η w t ω)) P r γ ρ) ∂ ℙ) ≤
      B * W / (1 - γ) * Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / T) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * κ * εstat / (1 - γ) ^ 3) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * εbias) / (1 - γ) := by
  have hM' := hM
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM'
  have hg : 0 < 1 - γ := by linarith
  have hRHS : 0 ≤ B * W / (1 - γ) * Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / T) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * κ * εstat / (1 - γ) ^ 3) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * εbias) / (1 - γ) :=
    add_nonneg (add_nonneg (mul_nonneg (div_nonneg (by positivity) hg.le) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (div_nonneg (Real.sqrt_nonneg _) hg.le)
  by_cases hf : Integrable (fun ω => (Finset.range T).inf' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT))
      (fun t => PolicyGradTheory.ProjGA.valueAt πstar P r γ ρ -
        PolicyGradTheory.ProjGA.valueAt (logLinearPolicy φ (qnpgParams η w t ω)) P r γ ρ)) ℙ
  swap
  · rw [integral_undef hf]; exact hRHS
  have hA1 : 1 ≤ Fintype.card A := Fintype.card_pos
  rcases eq_or_lt_of_le hA1 with hA | hA
  · -- a single action: every policy is the same
    have hone : ∀ π : S → A → ℝ, IsPolicy π → ∀ s a, π s a = 1 := by
      intro π hπ s a
      obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hA.symm
      have hall : ∀ b, b = a := fun b => (hx b).trans (hx a).symm
      have h := (hπ s).2
      rwa [Finset.sum_eq_single a (fun b _ hb => absurd (hall b) hb) (by simp)] at h
    refine le_trans (integral_nonpos fun ω => ?_) hRHS
    refine (Finset.inf'_le _ (Finset.mem_range.mpr hT)).trans_eq ?_
    have : logLinearPolicy φ (qnpgParams η w 0 ω) = πstar := by
      funext s a; rw [hone _ (qn_ll_policy φ _), hone _ hπstar]
    simp only [Pi.zero_apply]
    rw [this, sub_self]
  have hLpos : 0 < Real.log (Fintype.card A : ℝ) := Real.log_pos (by exact_mod_cast hA)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hAr : (0 : ℝ) < Fintype.card A := by positivity
  have hη0 : 0 < η := by rw [hη]; exact Real.sqrt_pos.mpr (by positivity)
  set K : ℝ := (Fintype.card A : ℝ) * κ / (1 - γ) with hK
  have hK0 : 0 ≤ K := div_nonneg (mul_nonneg hAr.le hκnonneg) hg.le
  set X : ℕ → Ω → ℝ := fun i ω => qLoss P r γ φ (wstar i ω) (qnpgParams η w i ω)
    (dstar P γ ρ πstar) with hX
  set Y : ℕ → Ω → ℝ := fun i ω => qLoss P r γ φ (w i ω) (qnpgParams η w i ω)
      (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w i ω)) P γ ν) -
    qLoss P r γ φ (wstar i ω) (qnpgParams η w i ω)
      (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w i ω)) P γ ν) with hY
  set C0 : ℝ := Real.log (Fintype.card A : ℝ) / (η * T) + η * B ^ 2 * W ^ 2 / 2 with hC0
  set gfun : Ω → ℝ := fun ω => 1 / (1 - γ) * (C0 + 1 / (T : ℝ) * ∑ i ∈ Finset.range T,
    (2 * Real.sqrt ((Fintype.card A : ℝ) * X i ω) + 2 * Real.sqrt (K * Y i ω))) with hgfun
  -- pointwise bound
  have hfg : ∀ ω, (Finset.range T).inf' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT))
      (fun t => PolicyGradTheory.ProjGA.valueAt πstar P r γ ρ -
        PolicyGradTheory.ProjGA.valueAt (logLinearPolicy φ (qnpgParams η w t ω)) P r γ ρ) ≤
      gfun ω := by
    intro ω
    set w' : ℕ → EuclideanSpace ℝ (Fin d) := fun t => if t < T then w t ω else 0 with hw'
    have hupd : ∀ t < T, qnpgParams η w (t + 1) ω = qnpgParams η w t ω + η • w' t := by
      intro t ht
      simp only [qnpgParams, Finset.sum_range_succ, smul_add, hw', if_pos ht]
    have hinit : ∀ s a, logLinearPolicy φ (qnpgParams η w 0 ω) s a = 1 / (Fintype.card A : ℝ) := by
      intro s a
      simp [qnpgParams, qn_ll_eq]
    have hwb : ∀ t ≤ T, ‖w' t‖ ≤ W := by
      intro t _
      simp only [hw']
      split_ifs with h
      · exact hwW t h ω
      · simpa using hW.le
    obtain ⟨t, ht, hbound⟩ := npg_regret_core P r γ hM ρ hρ πstar hπstar (logLinearPolicy φ)
      (qn_ll_policy φ) (qn_ll_pos φ) (B ^ 2) (sq_nonneg B)
      (fun s a x => (qn_ll_hasGrad φ x s a).differentiableAt)
      (fun s a x y => log_linear_smooth_core φ B hφ s a x y) η W hη0 T hT
      (fun t => qnpgParams η w t ω) w' hupd hinit hwb
    refine (Finset.inf'_le _ (Finset.mem_range.mpr ht)).trans (hbound.trans ?_)
    simp only [hgfun]
    refine mul_le_mul_of_nonneg_left (add_le_add (le_of_eq hC0.symm) (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi => ?_) (one_div_nonneg.mpr hTpos.le)))
      (one_div_nonneg.mpr hg.le)
    have hi := Finset.mem_range.mp hi
    simp only [hw', if_pos hi]
    have hsplit : ∑ s, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s * ∑ a, πstar s a *
        (PolicyGradTheory.ProjGA.advantage (logLinearPolicy φ (qnpgParams η w i ω)) P r γ s a -
          inner ℝ (w i ω) (gradient (fun z => Real.log (logLinearPolicy φ z s a))
            (qnpgParams η w i ω))) =
        ∑ s, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s * ∑ a, πstar s a *
        (PolicyGradTheory.ProjGA.advantage (logLinearPolicy φ (qnpgParams η w i ω)) P r γ s a -
          inner ℝ (wstar i ω) (gradient (fun z => Real.log (logLinearPolicy φ z s a))
            (qnpgParams η w i ω))) +
        ∑ s, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s * ∑ a, πstar s a *
          inner ℝ (wstar i ω - w i ω) (gradient (fun z => Real.log (logLinearPolicy φ z s a))
            (qnpgParams η w i ω)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_sub_left]; ring
    rw [hsplit]
    exact add_le_add (transfer_term_bound_core P r γ hM ρ hρ πstar hπstar φ _ _)
      (qn_est_bound P r γ hM ρ hρ ν hν πstar hπstar φ κ hκnonneg hκ W _ (w i ω) (wstar i ω)
        (hwW i hi ω) (hwstar i hi ω).1 (hwstar i hi ω).2)
  -- integrability
  have hX0 : ∀ i ω, 0 ≤ X i ω := by
    intro i ω
    simp only [hX, qLoss, dstar]
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => mul_nonneg
      (div_nonneg (qn_vis_nonneg hP hπstar hγ0 hγ1 hρ s) hAr.le) (sq_nonneg _)
  have hY0 : ∀ i < T, ∀ ω, 0 ≤ Y i ω := fun i hi ω =>
    sub_nonneg.mpr ((hwstar i hi ω).2 (w i ω) (hwW i hi ω))
  have hcontX := qn_qLoss_cont φ hP hr hγ0 hγ1 (dstar P γ ρ πstar)
  have hLon := qn_qLossOn_cont φ hP hr hγ0 hγ1 hν
  have hcontY : Continuous (fun p : EuclideanSpace ℝ (Fin d) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      qLoss P r γ φ p.1 p.2.2 (onPolicyMeasure (logLinearPolicy φ p.2.2) P γ ν) -
      qLoss P r γ φ p.2.1 p.2.2 (onPolicyMeasure (logLinearPolicy φ p.2.2) P γ ν)) :=
    (hLon.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).sub
      (hLon.comp ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))
  have hmX : ∀ i < T, Measurable (fun ω => (wstar i ω, qnpgParams η w i ω)) := fun i hi =>
    (hwstarm i hi).prodMk (qn_params_meas η w T hwm i hi)
  have hmY : ∀ i < T, Measurable (fun ω => (w i ω, (wstar i ω, qnpgParams η w i ω))) :=
    fun i hi => (hwm i hi).prodMk (hmX i hi)
  have hpn : ∀ i < T, ∀ ω, ‖qnpgParams η w i ω‖ ≤ W + η * (i * W) := fun i hi ω =>
    (qn_params_norm η hη0.le w T W hwW i hi ω).trans (le_add_of_nonneg_left hW.le)
  have hWle : ∀ i : ℕ, W ≤ W + η * (i * W) := fun i =>
    le_add_of_nonneg_right (by positivity)
  have hbX : ∀ i < T, ∀ ω, ‖(wstar i ω, qnpgParams η w i ω)‖ ≤ W + η * (i * W) := by
    intro i hi ω
    rw [Prod.norm_def]
    exact max_le ((hwstar i hi ω).1.trans (hWle i)) (hpn i hi ω)
  have hbY : ∀ i < T, ∀ ω, ‖(w i ω, (wstar i ω, qnpgParams η w i ω))‖ ≤ W + η * (i * W) := by
    intro i hi ω
    rw [Prod.norm_def]
    exact max_le ((hwW i hi ω).trans (hWle i)) (hbX i hi ω)
  have hIX : ∀ i < T, Integrable (X i) ℙ := fun i hi =>
    qn_int_cont ℙ (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => qLoss P r γ φ p.1 p.2 (dstar P γ ρ πstar)) hcontX (fun ω => (wstar i ω, qnpgParams η w i ω)) (hmX i hi) _ (hbX i hi)
  have hIsX : ∀ i < T, Integrable (fun ω => Real.sqrt ((Fintype.card A : ℝ) * X i ω)) ℙ :=
    fun i hi => qn_int_cont ℙ (fun p => Real.sqrt ((Fintype.card A : ℝ) * (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => qLoss P r γ φ p.1 p.2 (dstar P γ ρ πstar)) p))
      (Real.continuous_sqrt.comp (continuous_const.mul hcontX)) (fun ω => (wstar i ω, qnpgParams η w i ω))
      (hmX i hi) _ (hbX i hi)
  have hIY : ∀ i < T, Integrable (Y i) ℙ := fun i hi =>
    qn_int_cont ℙ (fun p : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      qLoss P r γ φ p.1 p.2.2 (onPolicyMeasure (logLinearPolicy φ p.2.2) P γ ν) -
      qLoss P r γ φ p.2.1 p.2.2 (onPolicyMeasure (logLinearPolicy φ p.2.2) P γ ν)) hcontY (fun ω => (w i ω, (wstar i ω, qnpgParams η w i ω))) (hmY i hi) _ (hbY i hi)
  have hIsY : ∀ i < T, Integrable (fun ω => Real.sqrt (K * Y i ω)) ℙ :=
    fun i hi => qn_int_cont ℙ (fun p => Real.sqrt (K * (fun p : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      qLoss P r γ φ p.1 p.2.2 (onPolicyMeasure (logLinearPolicy φ p.2.2) P γ ν) -
      qLoss P r γ φ p.2.1 p.2.2 (onPolicyMeasure (logLinearPolicy φ p.2.2) P γ ν)) p))
      (Real.continuous_sqrt.comp (continuous_const.mul hcontY)) (fun ω => (w i ω, (wstar i ω, qnpgParams η w i ω)))
      (hmY i hi) _ (hbY i hi)
  have hJX : ∀ i < T, ∫ ω, Real.sqrt ((Fintype.card A : ℝ) * X i ω) ∂ℙ ≤
      Real.sqrt ((Fintype.card A : ℝ) * εbias) := by
    intro i hi
    refine (qn_sqrt_integral ℙ (fun ω => (Fintype.card A : ℝ) * X i ω)
      (fun ω => mul_nonneg hAr.le (hX0 i ω)) ((hIX i hi).const_mul _) (hIsX i hi)).trans
      (Real.sqrt_le_sqrt ?_)
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hbias i hi) hAr.le
  have hJY : ∀ i < T, ∫ ω, Real.sqrt (K * Y i ω) ∂ℙ ≤ Real.sqrt (K * εstat) := by
    intro i hi
    refine (qn_sqrt_integral ℙ (fun ω => K * Y i ω)
      (fun ω => mul_nonneg hK0 (hY0 i hi ω)) ((hIY i hi).const_mul _) (hIsY i hi)).trans
      (Real.sqrt_le_sqrt ?_)
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hstat i hi) hK0
  have hIterm : ∀ i ∈ Finset.range T, Integrable (fun ω =>
      2 * Real.sqrt ((Fintype.card A : ℝ) * X i ω) + 2 * Real.sqrt (K * Y i ω)) ℙ :=
    fun i hi => ((hIsX i (Finset.mem_range.mp hi)).const_mul 2).add
      ((hIsY i (Finset.mem_range.mp hi)).const_mul 2)
  have hIg : Integrable gfun ℙ :=
    ((integrable_const C0).add ((integrable_finset_sum _ hIterm).const_mul _)).const_mul _
  have hint : ∫ ω, gfun ω ∂ℙ = 1 / (1 - γ) * (C0 + 1 / (T : ℝ) * ∑ i ∈ Finset.range T,
      (2 * ∫ ω, Real.sqrt ((Fintype.card A : ℝ) * X i ω) ∂ℙ +
        2 * ∫ ω, Real.sqrt (K * Y i ω) ∂ℙ)) := by
    simp only [hgfun]
    rw [integral_const_mul, integral_add (integrable_const _)
      ((integrable_finset_sum _ hIterm).const_mul _), integral_const, integral_const_mul,
      integral_finset_sum _ hIterm]
    simp only [probReal_univ, one_smul]
    congr 3
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_add ((hIsX i (Finset.mem_range.mp hi)).const_mul 2)
      ((hIsY i (Finset.mem_range.mp hi)).const_mul 2), integral_const_mul, integral_const_mul]
  have hfin := qn_final_alg A B W κ γ T η εstat εbias hB hW hκnonneg hg hTpos hLpos hη
  calc _ ≤ ∫ ω, gfun ω ∂ℙ := integral_mono hf hIg hfg
    _ = _ := hint
    _ ≤ 1 / (1 - γ) * (C0 + 1 / (T : ℝ) * ∑ i ∈ Finset.range T,
      (2 * Real.sqrt ((Fintype.card A : ℝ) * εbias) + 2 * Real.sqrt (K * εstat))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i hi => ?_) (one_div_nonneg.mpr hTpos.le)))
          (one_div_nonneg.mpr hg.le)
        have hi := Finset.mem_range.mp hi
        have := hJX i hi
        have := hJY i hi
        linarith
    _ = _ := hfin

end INT

end PolicyGradTheory.QNPG

open PolicyGradTheory.QNPG


theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] (d : ℕ)
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (ν : S × A → ℝ) (hν : PolicyGradTheory.ProjGA.IsDist ν)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (B : ℝ) (hB : 0 < B) (hφ : ∀ s a, ‖φ s a‖ ≤ B)
    (W : ℝ) (hW : 0 < W)
    (κ : ℝ) (hκnonneg : 0 ≤ κ)
    (hκ : ∀ v, quadForm φ (dstar P γ ρ πstar) v ≤ κ * quadForm φ ν v)
    (T : ℕ) (hT : 0 < T)
    (η : ℝ) (hη : η = Real.sqrt (2 * Real.log (Fintype.card A : ℝ) /
      (B ^ 2 * W ^ 2 * T)))
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (w wstar : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hwm : ∀ t < T, Measurable (w t))
    (hwstarm : ∀ t < T, Measurable (wstar t))
    (hwW : ∀ t < T, ∀ ω, ‖w t ω‖ ≤ W)
    (hwstar : ∀ t < T, ∀ ω,
      ‖wstar t ω‖ ≤ W ∧
        ∀ v, ‖v‖ ≤ W →
          qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
            (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν) ≤
          qLoss P r γ φ v (qnpgParams η w t ω)
            (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν))
    (εstat εbias : ℝ)
    (hstat : ∀ t < T,
      (∫ ω, (qLoss P r γ φ (w t ω) (qnpgParams η w t ω)
                (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν) -
              qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
                (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν)) ∂ℙ) ≤ εstat)
    (hbias : ∀ t < T,
      (∫ ω, qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
        (dstar P γ ρ πstar) ∂ℙ) ≤ εbias) :
    (∫ ω, (Finset.range T).inf' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT))
      (fun t => PolicyGradTheory.ProjGA.valueAt πstar P r γ ρ -
        PolicyGradTheory.ProjGA.valueAt (logLinearPolicy φ (qnpgParams η w t ω)) P r γ ρ) ∂ℙ) ≤
      B * W / (1 - γ) * Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / T) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * κ * εstat / (1 - γ) ^ 3) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * εbias) / (1 - γ) := by
  exact qnpg_core d P r γ hM ρ hρ ν hν πstar hπstar φ B hB hφ W hW κ hκnonneg hκ T hT η hη ℙ w wstar hwm hwstarm hwW hwstar εstat εbias hstat hbias
