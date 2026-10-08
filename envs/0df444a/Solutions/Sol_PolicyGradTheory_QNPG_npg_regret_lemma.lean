-- Prove2me | solution 1 for PolicyGradTheory.QNPG.npg_regret_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:02:34.391585+00:00
-- url     : https://prove2.me/submissions/ba2872c9-9267-46b9-86e1-e818f2e2da47

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.QNPG

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

lemma qn_pol_le_one {π : S → A → ℝ} (hπ : IsPolicy π) (s : S) (a : A) : π s a ≤ 1 := by
  rw [← (hπ s).2]
  exact Finset.single_le_sum (fun b _ => (hπ s).1 b) (Finset.mem_univ a)

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

end PolicyGradTheory.QNPG

open PolicyGradTheory.QNPG


theorem solution {S A : Type} [Fintype S] [DecidableEq S]
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
  exact npg_regret_core P r γ hM ρ hρ πtilde hπtilde pol hpol hpos β hβ hdiff hsmooth η W hη T hT θ w hupdate hinit hw
