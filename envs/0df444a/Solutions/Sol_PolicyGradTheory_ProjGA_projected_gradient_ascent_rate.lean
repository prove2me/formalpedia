-- Prove2me | solution 1 for PolicyGradTheory.ProjGA.projected_gradient_ascent_rate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:36:29.245977+00:00
-- url     : https://prove2.me/submissions/2cb7acaf-84e1-439a-9818-171aa46dd544

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Projection
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning


namespace PolicyGradTheory.ProjGA

section MDP
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- induced transition matrix -/
noncomputable def pgaM (π : S → A → ℝ) (P : S → A → S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun s s' => InducedTransition π P s s'

lemma pga_occ_eq_pow (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (s : S) :
    OccupationDist π P s0 t s = (pgaM π P ^ t) s0 s := by
  induction t generalizing s with
  | zero => simp [OccupationDist, Matrix.one_apply, eq_comm]
  | succ t ih =>
    simp only [OccupationDist, pow_succ, Matrix.mul_apply, ih]
    rfl

variable {π : S → A → ℝ} {P : S → A → S → ℝ}

lemma pga_M_nonneg (hP : IsTransitionKernel P) (hπ : IsPolicy π) (s s' : S) :
    0 ≤ pgaM π P s s' := by
  simp only [pgaM, Matrix.of_apply, InducedTransition]
  exact Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s')

lemma pga_M_rowsum (hP : IsTransitionKernel P) (hπ : IsPolicy π) (s : S) :
    ∑ s', pgaM π P s s' = 1 := by
  simp only [pgaM, Matrix.of_apply, InducedTransition]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
  exact (hπ s).2

lemma pga_pow_nonneg (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s s' : S) :
    0 ≤ (pgaM π P ^ t) s s' := by
  induction t generalizing s' with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (ih x) (pga_M_nonneg hP hπ x s')

lemma pga_pow_rowsum (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s : S) :
    ∑ s', (pgaM π P ^ t) s s' = 1 := by
  induction t with
  | zero => simp [Matrix.one_apply]
  | succ t ih =>
    simp_rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, pga_M_rowsum hP hπ, mul_one]
    exact ih

lemma pga_pow_le_one (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s s' : S) :
    (pgaM π P ^ t) s s' ≤ 1 := by
  rw [← pga_pow_rowsum hP hπ t s]
  exact Finset.single_le_sum (fun x _ => pga_pow_nonneg hP hπ t s x) (Finset.mem_univ _)

lemma pga_E_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s : S) (g : S → ℝ)
    (B : ℝ) (hg : ∀ x, |g x| ≤ B) : |∑ s', (pgaM π P ^ t) s s' * g s'| ≤ B := by
  calc |∑ s', (pgaM π P ^ t) s s' * g s'| ≤ ∑ s', |(pgaM π P ^ t) s s' * g s'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', (pgaM π P ^ t) s s' * B := by
        apply Finset.sum_le_sum; intro x _
        rw [abs_mul, abs_of_nonneg (pga_pow_nonneg hP hπ t s x)]
        exact mul_le_mul_of_nonneg_left (hg x) (pga_pow_nonneg hP hπ t s x)
    _ = B := by rw [← Finset.sum_mul, pga_pow_rowsum hP hπ, one_mul]

lemma pga_summable (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', (pgaM π P ^ t) s s' * g s') := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ0 hγ1).mul_right B) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  exact mul_le_mul_of_nonneg_left (pga_E_bound hP hπ t s g B hg) (pow_nonneg hγ0 t)

lemma pga_tsum_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    |∑' t : ℕ, γ ^ t * ∑ s', (pgaM π P ^ t) s s' * g s'| ≤ B / (1 - γ) := by
  have hs := pga_summable hP hπ hγ0 hγ1 s g B hg
  have hgeo := (summable_geometric_of_lt_one hγ0 hγ1).mul_right B
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  calc ∑' t : ℕ, ‖γ ^ t * ∑ s', (pgaM π P ^ t) s s' * g s'‖ ≤ ∑' t : ℕ, γ ^ t * B := by
        refine hs.norm.tsum_le_tsum (fun t => ?_) hgeo
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
        exact mul_le_mul_of_nonneg_left (pga_E_bound hP hπ t s g B hg) (pow_nonneg hγ0 t)
    _ = B / (1 - γ) := by rw [tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1]; ring

lemma pga_value_eq (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) :
    PolicyValue π P r γ s =
      ∑' t : ℕ, γ ^ t * ∑ s', (pgaM π P ^ t) s s' * InducedReward π r s' := by
  simp only [PolicyValue, pga_occ_eq_pow]

lemma pga_reward_bound (hπ : IsPolicy π) {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (s : S) : |InducedReward π r s| ≤ 1 := by
  have h0 : 0 ≤ InducedReward π r s :=
    Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) (hr s a).1
  have h1 : InducedReward π r s ≤ 1 := by
    calc InducedReward π r s ≤ ∑ a, π s a * 1 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hr s a).2 ((hπ s).1 a)
      _ = 1 := by simp [(hπ s).2]
  rw [abs_le]; constructor <;> linarith

lemma pga_value_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    |PolicyValue π P r γ s| ≤ 1 / (1 - γ) := by
  rw [pga_value_eq]
  exact pga_tsum_bound hP hπ hγ0 hγ1 s _ 1 (pga_reward_bound hπ hr)

/-- first-step identity for E -/
lemma pga_E_succ (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) (s : S) (g : S → ℝ) :
    ∑ s', (pgaM π P ^ (t + 1)) s s' * g s' =
      ∑ x, pgaM π P s x * ∑ s', (pgaM π P ^ t) x s' * g s' := by
  simp_rw [pow_succ', Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring

lemma pga_E_succ' (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) (s : S) (g : S → ℝ) :
    ∑ s', (pgaM π P ^ (t + 1)) s s' * g s' =
      ∑ x, (pgaM π P ^ t) s x * ∑ s', pgaM π P x s' * g s' := by
  simp_rw [pow_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring

/-- generic Bellman-type identity -/
lemma pga_tsum_bellman (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    ∑' t : ℕ, γ ^ t * ∑ s', (pgaM π P ^ t) s s' * g s' =
      g s + γ * ∑ x, pgaM π P s x * ∑' t : ℕ, γ ^ t * ∑ s', (pgaM π P ^ t) x s' * g s' := by
  rw [(pga_summable hP hπ hγ0 hγ1 s g B hg).tsum_eq_zero_add]
  congr 1
  · simp [Matrix.one_apply]
  · simp_rw [pga_E_succ]
    have : ∀ t : ℕ, γ ^ (t + 1) * ∑ x, pgaM π P s x * ∑ s', (pgaM π P ^ t) x s' * g s' =
        ∑ x, (γ * pgaM π P s x) * (γ ^ t * ∑ s', (pgaM π P ^ t) x s' * g s') := by
      intro t; rw [Finset.mul_sum]; congr 1; ext x; ring
    simp_rw [this]
    rw [Summable.tsum_finsetSum (fun x _ =>
      (pga_summable hP hπ hγ0 hγ1 x g B hg).mul_left (γ * pgaM π P s x))]
    rw [Finset.mul_sum]; congr 1; ext x
    rw [Summable.tsum_mul_left _ (pga_summable hP hπ hγ0 hγ1 x g B hg)]; ring

lemma pga_bellman (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P r γ s =
      InducedReward π r s + γ * ∑ x, pgaM π P s x * PolicyValue π P r γ x := by
  simp_rw [pga_value_eq]
  exact pga_tsum_bellman hP hπ hγ0 hγ1 s _ 1 (pga_reward_bound hπ hr)

lemma pga_adv_sum (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π' : S → A → ℝ)
    (s : S) :
    ∑ a, π' s a * advantage π P r γ s a =
      InducedReward π' r s + γ * ∑ x, pgaM π' P s x * PolicyValue π P r γ x
        - (∑ a, π' s a) * PolicyValue π P r γ s := by
  simp only [advantage, QFunction, InducedReward, pgaM, Matrix.of_apply,
    InducedTransition, mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1; congr 1
  rw [Finset.sum_comm]; congr 1; ext a; congr 1; ext x; ring

lemma pga_adv_sum_self (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    ∑ a, π s a * advantage π P r γ s a = 0 := by
  rw [pga_adv_sum hP hπ hr hγ0 hγ1, (hπ s).2, ← pga_bellman hP hπ hr hγ0 hγ1]; ring


lemma pga_pdl_state (hP : IsTransitionKernel P) (hπ : IsPolicy π) {π' : S → A → ℝ}
    (hπ' : IsPolicy π') {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s0 : S) :
    PolicyValue π P r γ s0 - PolicyValue π' P r γ s0 =
      ∑' t : ℕ, γ ^ t * ∑ s', (pgaM π P ^ t) s0 s' *
        (∑ a, π s' a * advantage π' P r γ s' a) := by
  have hVb : ∀ x, |PolicyValue π' P r γ x| ≤ 1 / (1 - γ) :=
    fun x => pga_value_bound hP hπ' hr hγ0 hγ1 x
  have hbs : Summable (fun t : ℕ => γ ^ t * ∑ s', (pgaM π P ^ t) s0 s' * PolicyValue π' P r γ s') :=
    pga_summable hP hπ hγ0 hγ1 s0 _ _ hVb
  have has : Summable (fun t : ℕ => γ ^ t * ∑ s', (pgaM π P ^ t) s0 s' * InducedReward π r s') :=
    pga_summable hP hπ hγ0 hγ1 s0 _ 1 (pga_reward_bound hπ hr)
  have hbs1 : Summable (fun t : ℕ => γ ^ (t + 1) * ∑ s', (pgaM π P ^ (t + 1)) s0 s' *
      PolicyValue π' P r γ s') := hbs.comp_injective (add_left_injective 1)
  have hterm : ∀ t : ℕ, γ ^ t * ∑ s', (pgaM π P ^ t) s0 s' *
        (∑ a, π s' a * advantage π' P r γ s' a) =
      (γ ^ t * ∑ s', (pgaM π P ^ t) s0 s' * InducedReward π r s') +
        (γ ^ (t + 1) * ∑ s', (pgaM π P ^ (t + 1)) s0 s' * PolicyValue π' P r γ s') -
        (γ ^ t * ∑ s', (pgaM π P ^ t) s0 s' * PolicyValue π' P r γ s') := by
    intro t
    simp_rw [pga_adv_sum hP hπ' hr hγ0 hγ1 π, (hπ _).2, one_mul]
    rw [pga_E_succ']
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, pow_succ]
    simp_rw [Finset.mul_sum]
    ring_nf
  rw [tsum_congr hterm, Summable.tsum_sub (has.add hbs1) hbs, Summable.tsum_add has hbs1,
    hbs.tsum_eq_zero_add, pga_value_eq π P r γ s0]
  simp [Matrix.one_apply]

/-- sums against the visitation distribution -/
lemma pga_vis_sum (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ρ : S → ℝ) (f : S → ℝ) (B : ℝ) (hf : ∀ x, |f x| ≤ B) :
    ∑ s, visitation π P γ ρ s * f s =
      (1 - γ) * ∑ s0, ρ s0 * ∑' t : ℕ, γ ^ t * ∑ s', (pgaM π P ^ t) s0 s' * f s' := by
  have hu : ∀ s, Summable (fun t : ℕ => γ ^ t * ∑ s0, ρ s0 * (pgaM π P ^ t) s0 s) := by
    intro s
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s0, |ρ s0|)) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul, abs_of_nonneg (pga_pow_nonneg hP hπ t x s)]
    exact mul_le_of_le_one_right (abs_nonneg _) (pga_pow_le_one hP hπ t x s)
  simp only [visitation, pga_occ_eq_pow]
  have h1 : ∀ s, (1 - γ) * (∑' t : ℕ, γ ^ t * ∑ s0, ρ s0 * (pgaM π P ^ t) s0 s) * f s =
      (1 - γ) * ∑' t : ℕ, γ ^ t * ∑ s0, ρ s0 * (pgaM π P ^ t) s0 s * f s := by
    intro s
    rw [mul_assoc, ← (hu s).tsum_mul_right]
    congr 2; ext t; rw [mul_assoc, Finset.sum_mul]
  simp_rw [h1]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum]
  · congr 1
    have h2 : ∀ t : ℕ, ∑ s, γ ^ t * ∑ s0, ρ s0 * (pgaM π P ^ t) s0 s * f s =
        ∑ s0, ρ s0 * (γ ^ t * ∑ s', (pgaM π P ^ t) s0 s' * f s') := by
      intro t
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring
    simp_rw [h2]
    rw [Summable.tsum_finsetSum]
    · congr 1; ext s0
      exact Summable.tsum_mul_left _ (pga_summable hP hπ hγ0 hγ1 s0 f B hf)
    · intro s0 _
      exact (pga_summable hP hπ hγ0 hγ1 s0 f B hf).mul_left _
  · intro s _
    have := (hu s).mul_right (f s)
    refine this.congr fun t => ?_
    rw [mul_assoc, Finset.sum_mul]

lemma pga_adv_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) {π' : S → A → ℝ}
    (hπ' : IsPolicy π') {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    |∑ a, π s a * advantage π' P r γ s a| ≤ 1 + 2 / (1 - γ) := by
  rw [pga_adv_sum hP hπ' hr hγ0 hγ1 π, (hπ s).2, one_mul]
  have h1 := pga_reward_bound hπ hr s
  have h2 := pga_E_bound (t := 1) hP hπ s (fun x => PolicyValue π' P r γ x) _
    (fun x => pga_value_bound hP hπ' hr hγ0 hγ1 x)
  simp only [pow_one] at h2
  have h3 := pga_value_bound hP hπ' hr hγ0 hγ1 s
  have hg : 0 < 1 - γ := by linarith
  have h4 : |γ * ∑ x, pgaM π P s x * PolicyValue π' P r γ x| ≤ 1 / (1 - γ) := by
    rw [abs_mul, abs_of_nonneg hγ0]
    calc γ * _ ≤ 1 * (1 / (1 - γ)) := mul_le_mul (by linarith) h2 (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  calc _ ≤ |InducedReward π r s + γ * ∑ x, pgaM π P s x * PolicyValue π' P r γ x|
        + |PolicyValue π' P r γ s| := abs_sub _ _
    _ ≤ |InducedReward π r s| + |γ * ∑ x, pgaM π P s x * PolicyValue π' P r γ x|
        + |PolicyValue π' P r γ s| := by gcongr; exact abs_add_le _ _
    _ ≤ 1 + 1 / (1 - γ) + 1 / (1 - γ) := by gcongr
    _ = _ := by ring

/-- performance difference lemma with a general start vector `ρ` -/
lemma pga_pdl (hP : IsTransitionKernel P) (hπ : IsPolicy π) {π' : S → A → ℝ}
    (hπ' : IsPolicy π') {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) :
    valueAt π P r γ ρ - valueAt π' P r γ ρ =
      1 / (1 - γ) * ∑ s, visitation π P γ ρ s *
        ∑ a, π s a * advantage π' P r γ s a := by
  rw [pga_vis_sum hP hπ hγ0 hγ1 ρ _ _ (pga_adv_bound hP hπ hπ' hr hγ0 hγ1)]
  have hg : (1 - γ) ≠ 0 := by linarith
  rw [← mul_assoc, one_div_mul_cancel hg, one_mul]
  simp only [valueAt, ← Finset.sum_sub_distrib, ← mul_sub]
  congr 1; ext s0
  rw [pga_pdl_state hP hπ hπ' hr hγ0 hγ1]


lemma pga_E_succ_gen (M : Matrix S S ℝ) (t : ℕ) (s : S) (g : S → ℝ) :
    ∑ s', (M ^ (t + 1)) s s' * g s' = ∑ x, M s x * ∑ s', (M ^ t) x s' * g s' := by
  simp_rw [pow_succ', Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring

lemma pga_gE_bound (M : Matrix S S ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hM : ∀ s, ∑ s', |M s s'| ≤ c)
    (t : ℕ) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    |∑ s', (M ^ t) s s' * g s'| ≤ c ^ t * B := by
  induction t generalizing s with
  | zero => simpa [Matrix.one_apply] using hg s
  | succ t ih =>
    rw [pga_E_succ_gen]
    have hB : 0 ≤ B := le_trans (abs_nonneg _) (hg s)
    calc _ ≤ ∑ x, |M s x * ∑ s', (M ^ t) x s' * g s'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |M s x| * (c ^ t * B) := Finset.sum_le_sum fun x _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ih x) (abs_nonneg _)
      _ = (∑ x, |M s x|) * (c ^ t * B) := by rw [Finset.sum_mul]
      _ ≤ c * (c ^ t * B) := mul_le_mul_of_nonneg_right (hM s) (by positivity)
      _ = c ^ (t + 1) * B := by ring

lemma pga_gsummable (M : Matrix S S ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hM : ∀ s, ∑ s', |M s s'| ≤ c)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγc : γ * c < 1) (s : S) (g : S → ℝ) (B : ℝ)
    (hg : ∀ x, |g x| ≤ B) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', (M ^ t) s s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (mul_nonneg hγ0 hc0) hγc).mul_right B) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t), mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (pga_gE_bound M c hc0 hM t s g B hg) (pow_nonneg hγ0 t)

lemma pga_gtsum_bellman (M : Matrix S S ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hM : ∀ s, ∑ s', |M s s'| ≤ c)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγc : γ * c < 1) (s : S) (g : S → ℝ) (B : ℝ)
    (hg : ∀ x, |g x| ≤ B) :
    ∑' t : ℕ, γ ^ t * ∑ s', (M ^ t) s s' * g s' =
      g s + γ * ∑ x, M s x * ∑' t : ℕ, γ ^ t * ∑ s', (M ^ t) x s' * g s' := by
  rw [(pga_gsummable M c hc0 hM hγ0 hγc s g B hg).tsum_eq_zero_add]
  congr 1
  · simp [Matrix.one_apply]
  · simp_rw [pga_E_succ_gen]
    have : ∀ t : ℕ, γ ^ (t + 1) * ∑ x, M s x * ∑ s', (M ^ t) x s' * g s' =
        ∑ x, (γ * M s x) * (γ ^ t * ∑ s', (M ^ t) x s' * g s') := by
      intro t; rw [Finset.mul_sum]; congr 1; ext x; ring
    simp_rw [this]
    rw [Summable.tsum_finsetSum (fun x _ =>
      (pga_gsummable M c hc0 hM hγ0 hγc x g B hg).mul_left (γ * M s x))]
    rw [Finset.mul_sum]; congr 1; ext x
    rw [Summable.tsum_mul_left _ (pga_gsummable M c hc0 hM hγ0 hγc x g B hg)]; ring

lemma pga_fix_bound (N : Matrix S S ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hN : ∀ s, ∑ s', |N s s'| ≤ c)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγc : γ * c < 1)
    (z f : S → ℝ) (hz : ∀ s, z s = f s + γ * ∑ x, N s x * z x) :
    ‖z‖ ≤ ‖f‖ / (1 - γ * c) := by
  have h1 : ‖z‖ ≤ ‖f‖ + γ * (c * ‖z‖) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
    rw [hz s]
    refine (norm_add_le _ _).trans (add_le_add (norm_le_pi_norm f s) ?_)
    rw [norm_mul, Real.norm_of_nonneg hγ0]
    refine mul_le_mul_of_nonneg_left ?_ hγ0
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x, ‖N s x * z x‖ ≤ ∑ x, |N s x| * ‖z‖ := Finset.sum_le_sum fun x _ => by
          rw [norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z x) (abs_nonneg _)
      _ = (∑ x, |N s x|) * ‖z‖ := by rw [Finset.sum_mul]
      _ ≤ c * ‖z‖ := mul_le_mul_of_nonneg_right (hN s) (norm_nonneg _)
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- row bound of the induced matrix of an arbitrary table -/
lemma pga_M_absrow (hP : IsTransitionKernel P) (x : S → A → ℝ) (s : S) :
    ∑ s', |pgaM x P s s'| ≤ ∑ a, |x s a| := by
  simp only [pgaM, Matrix.of_apply, InducedTransition]
  calc ∑ s', |∑ a, x s a * P s a s'| ≤ ∑ s', ∑ a, |x s a| * P s a s' :=
        Finset.sum_le_sum fun s' _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun a _ => by rw [abs_mul, abs_of_nonneg ((hP s a).1 s')])
    _ = ∑ a, |x s a| := by
        rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]

lemma pga_cs (x : EuclideanSpace ℝ (S × A)) (s : S) :
    ∑ a, |x (s, a)| ≤ Real.sqrt (Fintype.card A) * ‖x‖ := by
  have h1 : (∑ a, |x (s, a)|) ^ 2 ≤ (Fintype.card A : ℝ) * ∑ a, x (s, a) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : A => (1 : ℝ))
      (fun a => |x (s, a)|)
    simpa [sq_abs] using this
  have h2 : ∑ a, x (s, a) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f := fun s' => ∑ a, x (s', a) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ s)
  have h3 : (∑ a, |x (s, a)|) ^ 2 ≤ (Real.sqrt (Fintype.card A) * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    two_ne_zero).1 h3

end MDP

section DG
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

lemma pga_Q_bound {P : S → A → S → ℝ} {π : S → A → ℝ} (hP : IsTransitionKernel P)
    (hπ : IsPolicy π) {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    |QFunction π P r γ s a| ≤ 1 / (1 - γ) := by
  have hg : 0 < 1 - γ := by linarith
  have h1 : |∑ s', P s a s' * PolicyValue π P r γ s'| ≤ 1 / (1 - γ) := by
    calc _ ≤ ∑ s', |P s a s' * PolicyValue π P r γ s'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', P s a s' * (1 / (1 - γ)) := Finset.sum_le_sum fun s' _ => by
          rw [abs_mul, abs_of_nonneg ((hP s a).1 s')]
          exact mul_le_mul_of_nonneg_left (pga_value_bound hP hπ hr hγ0 hγ1 s') ((hP s a).1 s')
      _ = 1 / (1 - γ) := by rw [← Finset.sum_mul, (hP s a).2, one_mul]
  unfold QFunction
  have h2 := abs_le.1 h1
  have h3 := (hr s a)
  rw [abs_le]
  have e : 1 / (1 - γ) = 1 + γ * (1 / (1 - γ)) := by field_simp; ring
  constructor <;> nlinarith [h2.1, h2.2]

/-- the main second-order expansion -/
lemma pga_err {P : S → A → S → ℝ} (hP : IsTransitionKernel P) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : EuclideanSpace ℝ (S × A)) (hπ : IsPolicy (asPolicy π))
    (x : EuclideanSpace ℝ (S × A)) (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ s, ∑ a, |x (s, a)| ≤ c)
    (hγc : γ * c < 1) (μ : S → ℝ) :
    |directValue P r γ μ x - directValue P r γ μ π -
      ∑ s0, μ s0 * ∑' t : ℕ, γ ^ t * ∑ s', (pgaM (asPolicy π) P ^ t) s0 s' *
        (∑ a, (x (s', a) - π (s', a)) * QFunction (asPolicy π) P r γ s' a)| ≤
      (∑ s, |μ s|) * ((γ * (Real.sqrt (Fintype.card A) * ‖x - π‖) *
        ((Real.sqrt (Fintype.card A) * ‖x - π‖ * (1 / (1 - γ))) / (1 - γ * 1))) /
          (1 - γ * c)) := by
  have hg : 0 < 1 - γ := by linarith
  set Q := QFunction (asPolicy π) P r γ with hQ
  set w : S → ℝ := fun s => ∑ a, (x (s, a) - π (s, a)) * Q s a with hwdef
  set Mx := pgaM (asPolicy x) P with hMx
  set Mp := pgaM (asPolicy π) P with hMp
  set Vx : S → ℝ := fun s => PolicyValue (asPolicy x) P r γ s with hVxdef
  set Vp : S → ℝ := fun s => PolicyValue (asPolicy π) P r γ s with hVpdef
  set RW : S → ℝ := fun s => ∑' t : ℕ, γ ^ t * ∑ s', (Mp ^ t) s s' * w s' with hRWdef
  have hMxrow : ∀ s, ∑ s', |Mx s s'| ≤ c := fun s =>
    (pga_M_absrow hP (asPolicy x) s).trans (hc s)
  have hMprow : ∀ s, ∑ s', |Mp s s'| ≤ 1 := fun s => by
    refine (pga_M_absrow hP (asPolicy π) s).trans (le_of_eq ?_)
    rw [← (hπ s).2]; exact Finset.sum_congr rfl fun a _ => abs_of_nonneg ((hπ s).1 a)
  have hrx : ∀ s, |InducedReward (asPolicy x) r s| ≤ c := fun s => by
    unfold InducedReward
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun a _ => ?_).trans (hc s))
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.2 ⟨by linarith [(hr s a).1], (hr s a).2⟩)
  have hVx : ∀ s, Vx s = InducedReward (asPolicy x) r s + γ * ∑ y, Mx s y * Vx y := by
    intro s
    simp only [hVxdef, pga_value_eq]
    exact pga_gtsum_bellman Mx c hc0 hMxrow hγ0 hγc s _ c hrx
  have hVp : ∀ s, Vp s = InducedReward (asPolicy π) r s + γ * ∑ y, Mp s y * Vp y :=
    fun s => pga_bellman hP hπ hr hγ0 hγ1 s
  have hwb : ∀ s, |w s| ≤ ‖w‖ := fun s => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w s
  have hRW : ∀ s, RW s = w s + γ * ∑ y, Mp s y * RW y :=
    fun s => pga_tsum_bellman hP hπ hγ0 hγ1 s w _ hwb
  have e1 : ∀ (y : S → A → ℝ) (s : S), ∑ s', pgaM y P s s' * Vp s' =
      ∑ a, y s a * ∑ s', P s a s' * Vp s' := by
    intro y s
    simp only [pgaM, Matrix.of_apply, InducedTransition]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; congr 1; ext a; congr 1; ext s'; ring
  have hw : ∀ s, w s = (InducedReward (asPolicy x) r s - InducedReward (asPolicy π) r s) +
      γ * (∑ y, Mx s y * Vp y - ∑ y, Mp s y * Vp y) := by
    intro s
    rw [hMx, hMp, e1, e1]
    simp only [hwdef, hQ, QFunction, InducedReward, asPolicy]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  set z : S → ℝ := fun s => Vx s - Vp s - RW s with hzdef
  set f : S → ℝ := fun s => γ * ∑ y, (Mx s y - Mp s y) * RW y with hfdef
  have hz : ∀ s, z s = f s + γ * ∑ y, Mx s y * z y := by
    intro s
    simp only [hzdef, hfdef]
    rw [hVx s, hVp s, hRW s, hw s]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have hzb := pga_fix_bound Mx c hc0 hMxrow hγ0 hγc z f hz
  have hRWb := pga_fix_bound Mp 1 zero_le_one hMprow hγ0 (by linarith) RW w hRW
  have hD : ∀ s, ∑ y, |Mx s y - Mp s y| ≤ Real.sqrt (Fintype.card A) * ‖x - π‖ := by
    intro s
    have : ∀ y, Mx s y - Mp s y = pgaM (fun s a => x (s, a) - π (s, a)) P s y := by
      intro y
      simp only [hMx, hMp, pgaM, Matrix.of_apply, InducedTransition, asPolicy, sub_mul,
        Finset.sum_sub_distrib]
    simp_rw [this]
    refine (pga_M_absrow hP _ s).trans ?_
    have := pga_cs (x - π) s
    simpa using this
  have hwn : ‖w‖ ≤ Real.sqrt (Fintype.card A) * ‖x - π‖ * (1 / (1 - γ)) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
    rw [Real.norm_eq_abs]
    calc |w s| ≤ ∑ a, |(x (s, a) - π (s, a)) * Q s a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, |x (s, a) - π (s, a)| * (1 / (1 - γ)) := Finset.sum_le_sum fun a _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (pga_Q_bound hP hπ hr hγ0 hγ1 s a) (abs_nonneg _)
      _ = (∑ a, |(x - π) (s, a)|) * (1 / (1 - γ)) := by rw [Finset.sum_mul]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (pga_cs (x - π) s) (by positivity)
  have hfn : ‖f‖ ≤ γ * (Real.sqrt (Fintype.card A) * ‖x - π‖) *
      ((Real.sqrt (Fintype.card A) * ‖x - π‖ * (1 / (1 - γ))) / (1 - γ * 1)) := by
    have hg1 : 0 < 1 - γ * 1 := by linarith
    have hi : 0 ≤ 1 / (1 - γ) := by positivity
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hγ0 (by positivity))
      (div_nonneg (mul_nonneg (by positivity) hi) hg1.le))).2 fun s => ?_
    rw [Real.norm_eq_abs, hfdef, abs_mul, abs_of_nonneg hγ0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hγ0
    calc _ ≤ ∑ y, |(Mx s y - Mp s y) * RW y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |Mx s y - Mp s y| * ‖RW‖ := Finset.sum_le_sum fun y _ => by
          rw [abs_mul, ← Real.norm_eq_abs (RW y)]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm RW y) (abs_nonneg _)
      _ = (∑ y, |Mx s y - Mp s y|) * ‖RW‖ := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul (hD s) (hRWb.trans (div_le_div_of_nonneg_right hwn (by linarith)))
          (norm_nonneg _) (by positivity)
  have hfin : directValue P r γ μ x - directValue P r γ μ π - ∑ s0, μ s0 * RW s0 =
      ∑ s, μ s * z s := by
    simp only [directValue, valueAt, hzdef, hVxdef, hVpdef, mul_sub, Finset.sum_sub_distrib]
  rw [hfin]
  calc |∑ s, μ s * z s| ≤ ∑ s, |μ s| * ‖z‖ := (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun s _ => by
          rw [abs_mul, ← Real.norm_eq_abs (z s)]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z s) (abs_nonneg _))
    _ = (∑ s, |μ s|) * ‖z‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hzb.trans
          (div_le_div_of_nonneg_right hfn (by linarith))) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

end DG

section DG2
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

noncomputable def pgaGrad (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ)
    (π : EuclideanSpace ℝ (S × A)) : EuclideanSpace ℝ (S × A) :=
  WithLp.toLp 2 (fun p : S × A => 1 / (1 - γ) * visitation (asPolicy π) P γ μ p.1 *
    QFunction (asPolicy π) P r γ p.1 p.2)

lemma pga_inner_grad {P : S → A → S → ℝ} (hP : IsTransitionKernel P) {r : S → A → ℝ}
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : EuclideanSpace ℝ (S × A)) (hπ : IsPolicy (asPolicy π)) (μ : S → ℝ)
    (v : EuclideanSpace ℝ (S × A)) :
    inner ℝ (pgaGrad P r γ μ π) v =
      ∑ s0, μ s0 * ∑' t : ℕ, γ ^ t * ∑ s', (pgaM (asPolicy π) P ^ t) s0 s' *
        (∑ a, v (s', a) * QFunction (asPolicy π) P r γ s' a) := by
  have hg : (1 - γ) ≠ 0 := by linarith
  set w : S → ℝ := fun s => ∑ a, v (s, a) * QFunction (asPolicy π) P r γ s a with hw
  have hwb : ∀ s, |w s| ≤ ‖w‖ := fun s => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w s
  have h1 : inner ℝ (pgaGrad P r γ μ π) v =
      1 / (1 - γ) * ∑ s, visitation (asPolicy π) P γ μ s * w s := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hw, Finset.mul_sum, pgaGrad]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    ring
  rw [h1, pga_vis_sum hP hπ hγ0 hγ1 μ w _ hwb, ← mul_assoc, one_div_mul_cancel hg, one_mul]

theorem pga_hasGrad {P : S → A → S → ℝ} {r : S → A → ℝ} {γ : ℝ} (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (π : EuclideanSpace ℝ (S × A)) (hπ : π ∈ simplexSet S A) :
    HasGradientAt (directValue P r γ μ) (pgaGrad P r γ μ π) π := by
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  have hπp : IsPolicy (asPolicy π) := hπ
  have hg : 0 < 1 - γ := by linarith
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO]
  set K := Real.sqrt (Fintype.card A) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  set δ := (1 - γ) / (2 * (K + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  set N1 := γ * K * ((K * (1 / (1 - γ))) / (1 - γ * 1)) with hN1
  have hN10 : 0 ≤ N1 := by
    have : 0 < 1 - γ * 1 := by linarith
    have : 0 ≤ 1 / (1 - γ) := by positivity
    positivity
  set C := (∑ s, |μ s|) * (N1 / ((1 - γ) / 2)) with hC
  have hC0 : 0 ≤ C := mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (div_nonneg hN10 (by linarith))
  have key : ∀ x : EuclideanSpace ℝ (S × A), ‖x - π‖ < δ →
      |directValue P r γ μ x - directValue P r γ μ π - inner ℝ (pgaGrad P r γ μ π) (x - π)|
        ≤ C * ‖x - π‖ ^ 2 := by
    intro x hx
    set n := ‖x - π‖ with hn
    have hn0 : 0 ≤ n := norm_nonneg _
    set c := 1 + K * n with hcdef
    have hc0 : 0 ≤ c := by positivity
    have hc : ∀ s, ∑ a, |x (s, a)| ≤ c := by
      intro s
      have h1 : ∀ a, |x (s, a)| ≤ π (s, a) + |(x - π) (s, a)| := by
        intro a
        have : x (s, a) = π (s, a) + (x - π) (s, a) := by simp
        rw [this]
        refine (abs_add_le _ _).trans ?_
        have h0 : 0 ≤ π (s, a) := (hπp s).1 a
        rw [abs_of_nonneg h0]
      refine (Finset.sum_le_sum fun a _ => h1 a).trans ?_
      rw [Finset.sum_add_distrib]
      have h2 : ∑ a, π (s, a) = 1 := (hπp s).2
      rw [h2]
      linarith [pga_cs (x - π) s]
    have hKn : K * n ≤ (1 - γ) / 2 := by
      have : K * n ≤ K * δ := mul_le_mul_of_nonneg_left hx.le hK0
      have h3 : K * δ ≤ (1 - γ) / 2 := by
        rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have hγc1 : (1 - γ) / 2 ≤ 1 - γ * c := by
      rw [hcdef]; nlinarith
    have hγc : γ * c < 1 := by linarith
    have herr := pga_err hP hr hγ0 hγ1 π hπp x c hc0 hc hγc μ
    rw [pga_inner_grad hP hγ0 hγ1 π hπp μ (x - π)]
    have e : ∀ s' a, (x - π) (s', a) = x (s', a) - π (s', a) := fun s' a => by simp
    simp only [e]
    refine herr.trans ?_
    have eN : γ * (K * n) * ((K * n * (1 / (1 - γ))) / (1 - γ * 1)) = N1 * n ^ 2 := by
      rw [hN1]; ring
    rw [eN]
    have hS : 0 ≤ ∑ s, |μ s| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h4 : N1 * n ^ 2 / (1 - γ * c) ≤ N1 / ((1 - γ) / 2) * n ^ 2 := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) (by linarith) hγc1
    calc (∑ s, |μ s|) * (N1 * n ^ 2 / (1 - γ * c))
        ≤ (∑ s, |μ s|) * (N1 / ((1 - γ) / 2) * n ^ 2) := mul_le_mul_of_nonneg_left h4 hS
      _ = C * n ^ 2 := by rw [hC]; ring
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hm : 0 < min δ (ε / (C + 1)) := lt_min hδ0 (by positivity)
  filter_upwards [Metric.ball_mem_nhds π hm] with x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hx1 : ‖x - π‖ < δ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : ‖x - π‖ < ε / (C + 1) := lt_of_lt_of_le hx (min_le_right _ _)
  have hk := key x hx1
  rw [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs]
  refine hk.trans ?_
  have hn0 : 0 ≤ ‖x - π‖ := norm_nonneg _
  have : C * ‖x - π‖ ≤ ε := by
    have h1 : C * ‖x - π‖ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hx2.le hC0
    have h2 : C * (ε / (C + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    linarith
  calc C * ‖x - π‖ ^ 2 = (C * ‖x - π‖) * ‖x - π‖ := by ring
    _ ≤ ε * ‖x - π‖ := mul_le_mul_of_nonneg_right this hn0

theorem direct_gradient_core {P : S → A → S → ℝ} {r : S → A → ℝ} {γ : ℝ}
    (hM : IsFiniteMDP P r γ) (μ : S → ℝ) :
    ∀ π ∈ simplexSet S A, ∀ (s : S) (a : A),
      gradient (directValue P r γ μ) π (s, a) =
        1 / (1 - γ) * visitation (asPolicy π) P γ μ s * QFunction (asPolicy π) P r γ s a := by
  intro π hπ s a
  rw [(pga_hasGrad hM μ π hπ).gradient]
  rfl

end DG2

section GD
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

lemma pga_inner_grad0 {P : S → A → S → ℝ} {r : S → A → ℝ} {γ : ℝ}
    (π : EuclideanSpace ℝ (S × A)) (μ : S → ℝ) (v : EuclideanSpace ℝ (S × A)) :
    inner ℝ (pgaGrad P r γ μ π) v =
      1 / (1 - γ) * ∑ s, visitation (asPolicy π) P γ μ s *
        ∑ a, v (s, a) * QFunction (asPolicy π) P r γ s a := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Finset.mul_sum, pgaGrad]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
  ring

lemma pga_vis_basic {P : S → A → S → ℝ} (hP : IsTransitionKernel P) {π : S → A → ℝ}
    (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {μ : S → ℝ} (hμ : IsDist μ) :
    (∀ s, (1 - γ) * μ s ≤ visitation π P γ μ s) ∧ (∀ s, 0 ≤ visitation π P γ μ s) ∧
      ∑ s, visitation π P γ μ s = 1 := by
  have hg : 0 < 1 - γ := by linarith
  have hu : ∀ s, Summable (fun t : ℕ => γ ^ t * ∑ s0, μ s0 * (pgaM π P ^ t) s0 s) := by
    intro s
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s0, |μ s0|)) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul, abs_of_nonneg (pga_pow_nonneg hP hπ t x s)]
    exact mul_le_of_le_one_right (abs_nonneg _) (pga_pow_le_one hP hπ t x s)
  have hnn : ∀ s t, 0 ≤ γ ^ t * ∑ s0, μ s0 * (pgaM π P ^ t) s0 s := fun s t =>
    mul_nonneg (pow_nonneg hγ0 t) (Finset.sum_nonneg fun s0 _ =>
      mul_nonneg (hμ.1 s0) (pga_pow_nonneg hP hπ t s0 s))
  have hv : ∀ s, visitation π P γ μ s =
      (1 - γ) * ∑' t : ℕ, γ ^ t * ∑ s0, μ s0 * (pgaM π P ^ t) s0 s := by
    intro s; simp only [visitation, pga_occ_eq_pow]
  refine ⟨fun s => ?_, fun s => ?_, ?_⟩
  · rw [hv]
    refine mul_le_mul_of_nonneg_left ?_ hg.le
    have := (hu s).le_tsum 0 (fun j _ => hnn s j)
    refine le_trans (le_of_eq ?_) this
    simp [Matrix.one_apply]
  · rw [hv]; exact mul_nonneg hg.le (tsum_nonneg (hnn s))
  · have := pga_vis_sum hP hπ hγ0 hγ1 μ (fun _ => (1 : ℝ)) 1 (fun _ => by norm_num)
    simp only [mul_one] at this
    rw [this]
    simp_rw [pga_pow_rowsum hP hπ, mul_one, tsum_geometric_of_lt_one hγ0 hγ1, ← Finset.sum_mul,
      hμ.2]
    field_simp

theorem pga_dom1 [DecidableEq A] {P : S → A → S → ℝ} {r : S → A → ℝ} {γ : ℝ}
    (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : IsDist μ) (ρ : S → ℝ) (hρ : IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (π : EuclideanSpace ℝ (S × A)) (hπ : π ∈ simplexSet S A)
    (G : ℝ) (hG : ∀ πbar ∈ simplexSet S A,
      inner ℝ (πbar - π) (gradient (directValue P r γ μ) π) ≤ G)
    (D₁ : ℝ) (hD₁ : ∀ s, visitation πstar P γ ρ s ≤ D₁ * visitation (asPolicy π) P γ μ s) :
    valueAt πstar P r γ ρ - valueAt (asPolicy π) P r γ ρ ≤ D₁ * G := by
  have hM' := hM
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM'
  have hg : 0 < 1 - γ := by linarith
  have hπp : IsPolicy (asPolicy π) := hπ
  have hS : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hρ.2; simp at this
  obtain ⟨s00⟩ := hS
  have hA : Nonempty A := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := (hπp s00).2; simp at this
  set Ad := advantage (asPolicy π) P r γ with hAd
  choose astar hastar using fun s => Finset.exists_max_image Finset.univ (Ad s)
    Finset.univ_nonempty
  set m : S → ℝ := fun s => Ad s (astar s) with hm
  have hmax : ∀ s a, Ad s a ≤ m s := fun s a => (hastar s).2 a (Finset.mem_univ a)
  have hsum_le : ∀ (q : S → A → ℝ), IsPolicy q → ∀ s, ∑ a, q s a * Ad s a ≤ m s := by
    intro q hq s
    calc ∑ a, q s a * Ad s a ≤ ∑ a, q s a * m s :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmax s a) ((hq s).1 a)
      _ = m s := by rw [← Finset.sum_mul, (hq s).2, one_mul]
  have hm0 : ∀ s, 0 ≤ m s := fun s => by
    have := pga_adv_sum_self hP hπp hr hγ0 hγ1 s
    have h2 := hsum_le _ hπp s
    linarith
  set πbar : EuclideanSpace ℝ (S × A) :=
    WithLp.toLp 2 (fun p : S × A => if p.2 = astar p.1 then (1 : ℝ) else 0) with hπbar
  have hπbar_apply : ∀ s a, πbar (s, a) = if a = astar s then 1 else 0 := fun s a => rfl
  have hπbarS : πbar ∈ simplexSet S A := by
    intro s
    refine ⟨fun a => ?_, ?_⟩
    · show 0 ≤ πbar (s, a)
      rw [hπbar_apply]; split_ifs <;> norm_num
    · show ∑ a, πbar (s, a) = 1
      simp only [hπbar_apply]; simp
  have hVQ : ∀ s, ∑ a, asPolicy π s a * QFunction (asPolicy π) P r γ s a =
      PolicyValue (asPolicy π) P r γ s := by
    intro s
    have := pga_adv_sum_self hP hπp hr hγ0 hγ1 s
    simp only [advantage, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hπp s).2,
      one_mul] at this
    linarith
  have hinner : inner ℝ (πbar - π) (gradient (directValue P r γ μ) π) =
      1 / (1 - γ) * ∑ s, visitation (asPolicy π) P γ μ s * m s := by
    rw [(pga_hasGrad hM μ π hπ).gradient, real_inner_comm, pga_inner_grad0]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    have e : ∀ a, (πbar - π) (s, a) = πbar (s, a) - asPolicy π s a := fun a => by
      simp [asPolicy]
    simp_rw [e, sub_mul, Finset.sum_sub_distrib, hVQ, hπbar_apply, ite_mul, one_mul, zero_mul]
    simp [hm, hAd, advantage]
  have hpdl := pga_pdl hP hπstar hπp hr hγ0 hγ1 ρ
  have hvs := pga_vis_basic hP hπstar hγ0 hγ1 hρ
  have hvm := pga_vis_basic hP hπp hγ0 hγ1 hμ
  have hD0 : 0 ≤ D₁ := by
    by_contra hneg
    push_neg at hneg
    have : ∑ s, visitation πstar P γ ρ s ≤ 0 := Finset.sum_nonpos fun s _ =>
      (hD₁ s).trans (mul_nonpos_of_nonpos_of_nonneg hneg.le (hvm.2.1 s))
    linarith [hvs.2.2]
  rw [hpdl]
  calc 1 / (1 - γ) * ∑ s, visitation πstar P γ ρ s * ∑ a, πstar s a * Ad s a
      ≤ 1 / (1 - γ) * ∑ s, (D₁ * visitation (asPolicy π) P γ μ s) * m s := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => ?_) (by positivity)
        exact (mul_le_mul_of_nonneg_left (hsum_le _ hπstar s) (hvs.2.1 s)).trans
          (mul_le_mul_of_nonneg_right (hD₁ s) (hm0 s))
    _ = D₁ * inner ℝ (πbar - π) (gradient (directValue P r γ μ) π) := by
        rw [hinner, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => by ring
    _ ≤ D₁ * G := mul_le_mul_of_nonneg_left (hG πbar hπbarS) hD0

theorem gradient_domination_core [DecidableEq A] {P : S → A → S → ℝ} {r : S → A → ℝ} {γ : ℝ}
    (hM : IsFiniteMDP P r γ)
    (μ : S → ℝ) (hμ : IsDist μ) (ρ : S → ℝ) (hρ : IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (π : EuclideanSpace ℝ (S × A)) (hπ : π ∈ simplexSet S A)
    (G : ℝ) (hG : ∀ πbar ∈ simplexSet S A,
      inner ℝ (πbar - π) (gradient (directValue P r γ μ) π) ≤ G)
    (D₁ : ℝ) (hD₁ : ∀ s, visitation πstar P γ ρ s ≤ D₁ * visitation (asPolicy π) P γ μ s)
    (D : ℝ) (hD : ∀ s, visitation πstar P γ ρ s ≤ D * μ s) :
    valueAt πstar P r γ ρ - valueAt (asPolicy π) P r γ ρ ≤ D₁ * G ∧
      valueAt πstar P r γ ρ - valueAt (asPolicy π) P r γ ρ ≤ 1 / (1 - γ) * D * G := by
  refine ⟨pga_dom1 hM μ hμ ρ hρ πstar hπstar π hπ G hG D₁ hD₁, ?_⟩
  have hM' := hM
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM'
  have hg : 0 < 1 - γ := by linarith
  have hπp : IsPolicy (asPolicy π) := hπ
  have hvs := pga_vis_basic hP hπstar hγ0 hγ1 hρ
  have hvm := pga_vis_basic hP hπp hγ0 hγ1 hμ
  have hD0 : 0 ≤ D := by
    by_contra hneg
    push_neg at hneg
    have : ∑ s, visitation πstar P γ ρ s ≤ 0 := Finset.sum_nonpos fun s _ =>
      (hD s).trans (mul_nonpos_of_nonpos_of_nonneg hneg.le (hμ.1 s))
    linarith [hvs.2.2]
  have h := pga_dom1 hM μ hμ ρ hρ πstar hπstar π hπ G hG (1 / (1 - γ) * D) (fun s => by
    refine (hD s).trans ?_
    have h1 := hvm.1 s
    have : D * μ s = 1 / (1 - γ) * D * ((1 - γ) * μ s) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h1 (by positivity))
  exact h

end GD

section SM
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

noncomputable def pgaR (P : S → A → S → ℝ) (γ : ℝ) (π : S → A → ℝ) (w : S → ℝ) : S → ℝ :=
  fun s => ∑' t : ℕ, γ ^ t * ∑ s', (pgaM π P ^ t) s s' * w s'

noncomputable def pgaW (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (π v : EuclideanSpace ℝ (S × A)) : S → ℝ :=
  fun s => ∑ a, v (s, a) * QFunction (asPolicy π) P r γ s a

variable {P : S → A → S → ℝ} {r : S → A → ℝ} {γ : ℝ}

lemma pga_wbound (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : EuclideanSpace ℝ (S × A)) (hπ : IsPolicy (asPolicy π))
    (v : EuclideanSpace ℝ (S × A)) :
    ‖pgaW P r γ π v‖ ≤ Real.sqrt (Fintype.card A) * ‖v‖ * (1 / (1 - γ)) := by
  have hg : 0 < 1 - γ := by linarith
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
  rw [Real.norm_eq_abs]
  calc |pgaW P r γ π v s| ≤ ∑ a, |v (s, a) * QFunction (asPolicy π) P r γ s a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |v (s, a)| * (1 / (1 - γ)) := Finset.sum_le_sum fun a _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (pga_Q_bound hP hπ hr hγ0 hγ1 s a) (abs_nonneg _)
    _ = (∑ a, |v (s, a)|) * (1 / (1 - γ)) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pga_cs v s) (by positivity)

lemma pga_Mdiff (hP : IsTransitionKernel P) (x π : EuclideanSpace ℝ (S × A)) (s : S) :
    ∑ y, |pgaM (asPolicy x) P s y - pgaM (asPolicy π) P s y| ≤
      Real.sqrt (Fintype.card A) * ‖x - π‖ := by
  have : ∀ y, pgaM (asPolicy x) P s y - pgaM (asPolicy π) P s y =
      pgaM (fun s a => x (s, a) - π (s, a)) P s y := by
    intro y
    simp only [pgaM, Matrix.of_apply, InducedTransition, asPolicy, sub_mul,
      Finset.sum_sub_distrib]
  simp_rw [this]
  refine (pga_M_absrow hP _ s).trans ?_
  have := pga_cs (x - π) s
  simpa using this

lemma pga_wid (π x : EuclideanSpace ℝ (S × A)) (s : S) :
    pgaW P r γ π (x - π) s =
      (InducedReward (asPolicy x) r s - InducedReward (asPolicy π) r s) +
      γ * (∑ y, pgaM (asPolicy x) P s y * PolicyValue (asPolicy π) P r γ y -
        ∑ y, pgaM (asPolicy π) P s y * PolicyValue (asPolicy π) P r γ y) := by
  have e1 : ∀ (y : S → A → ℝ), ∑ s', pgaM y P s s' * PolicyValue (asPolicy π) P r γ s' =
      ∑ a, y s a * ∑ s', P s a s' * PolicyValue (asPolicy π) P r γ s' := by
    intro y
    simp only [pgaM, Matrix.of_apply, InducedTransition]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; congr 1; ext a; congr 1; ext s'; ring
  rw [e1, e1]
  simp only [pgaW, QFunction, InducedReward, asPolicy, PiLp.sub_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma pga_Mrow1 (hP : IsTransitionKernel P) (π : EuclideanSpace ℝ (S × A))
    (hπ : IsPolicy (asPolicy π)) (s : S) : ∑ s', |pgaM (asPolicy π) P s s'| ≤ 1 := by
  refine (pga_M_absrow hP (asPolicy π) s).trans (le_of_eq ?_)
  rw [← (hπ s).2]; exact Finset.sum_congr rfl fun a _ => abs_of_nonneg ((hπ s).1 a)

lemma pga_Vdiff (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : EuclideanSpace ℝ (S × A)) (hπ : IsPolicy (asPolicy π))
    (x : EuclideanSpace ℝ (S × A)) (hx : IsPolicy (asPolicy x)) :
    ‖fun s => PolicyValue (asPolicy x) P r γ s - PolicyValue (asPolicy π) P r γ s‖ ≤
      Real.sqrt (Fintype.card A) * ‖x - π‖ * (1 / (1 - γ)) / (1 - γ * 1) := by
  have hz : ∀ s, PolicyValue (asPolicy x) P r γ s - PolicyValue (asPolicy π) P r γ s =
      pgaW P r γ π (x - π) s + γ * ∑ y, pgaM (asPolicy x) P s y *
        (PolicyValue (asPolicy x) P r γ y - PolicyValue (asPolicy π) P r γ y) := by
    intro s
    rw [pga_wid, pga_bellman hP hx hr hγ0 hγ1 s, pga_bellman hP hπ hr hγ0 hγ1 s]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  refine (pga_fix_bound _ 1 zero_le_one (pga_Mrow1 hP x hx) hγ0 (by linarith) _ _ hz).trans ?_
  exact div_le_div_of_nonneg_right (pga_wbound hP hr hγ0 hγ1 π hπ (x - π)) (by linarith)

lemma pga_RW_diff (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : EuclideanSpace ℝ (S × A)) (hπ : IsPolicy (asPolicy π))
    (x : EuclideanSpace ℝ (S × A)) (hx : IsPolicy (asPolicy x)) (v : EuclideanSpace ℝ (S × A)) :
    ‖fun s => pgaR P γ (asPolicy x) (pgaW P r γ x v) s - pgaR P γ (asPolicy π) (pgaW P r γ π v) s‖
      ≤ (γ * (Real.sqrt (Fintype.card A) * ‖v‖) *
          (Real.sqrt (Fintype.card A) * ‖x - π‖ * (1 / (1 - γ)) / (1 - γ * 1)) +
        γ * (Real.sqrt (Fintype.card A) * ‖x - π‖) *
          (Real.sqrt (Fintype.card A) * ‖v‖ * (1 / (1 - γ)) / (1 - γ * 1))) / (1 - γ * 1) := by
  have hg : 0 < 1 - γ := by linarith
  have hg1 : 0 < 1 - γ * 1 := by linarith
  set Mx := pgaM (asPolicy x) P
  set Mp := pgaM (asPolicy π) P
  set W' := pgaW P r γ x v with hW'
  set W := pgaW P r γ π v with hW
  set R' := pgaR P γ (asPolicy x) W' with hR'
  set R := pgaR P γ (asPolicy π) W with hR
  have hb : ∀ (w : S → ℝ) s, |w s| ≤ ‖w‖ := fun w s => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w s
  have hR'e : ∀ s, R' s = W' s + γ * ∑ y, Mx s y * R' y :=
    fun s => pga_tsum_bellman hP hx hγ0 hγ1 s W' _ (hb W')
  have hRe : ∀ s, R s = W s + γ * ∑ y, Mp s y * R y :=
    fun s => pga_tsum_bellman hP hπ hγ0 hγ1 s W _ (hb W)
  set f : S → ℝ := fun s => (W' s - W s) + γ * ∑ y, (Mx s y - Mp s y) * R y with hf
  have hy : ∀ s, R' s - R s = f s + γ * ∑ y, Mx s y * (R' y - R y) := by
    intro s
    rw [hR'e s, hRe s]
    simp only [hf, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have hyb := pga_fix_bound Mx 1 zero_le_one (pga_Mrow1 hP x hx) hγ0 (by linarith) _ f hy
  refine hyb.trans (div_le_div_of_nonneg_right ?_ hg1.le)
  set z : S → ℝ := fun s => PolicyValue (asPolicy x) P r γ s - PolicyValue (asPolicy π) P r γ s
    with hz
  have hzb : ‖z‖ ≤ _ := pga_Vdiff hP hr hγ0 hγ1 π hπ x hx
  have hRb : ‖R‖ ≤ Real.sqrt (Fintype.card A) * ‖v‖ * (1 / (1 - γ)) / (1 - γ * 1) :=
    (pga_fix_bound Mp 1 zero_le_one (pga_Mrow1 hP π hπ) hγ0 (by linarith) R W hRe).trans
      (div_le_div_of_nonneg_right (pga_wbound hP hr hγ0 hγ1 π hπ v) hg1.le)
  have hK0 : 0 ≤ Real.sqrt (Fintype.card A) := Real.sqrt_nonneg _
  have hi : 0 ≤ 1 / (1 - γ) := by positivity
  refine (pi_norm_le_iff_of_nonneg ?_).2 fun s => ?_
  · refine add_nonneg (mul_nonneg (mul_nonneg hγ0 (by positivity)) ?_)
      (mul_nonneg (mul_nonneg hγ0 (by positivity)) ?_)
    · exact div_nonneg (mul_nonneg (by positivity) hi) hg1.le
    · exact div_nonneg (mul_nonneg (by positivity) hi) hg1.le
  rw [Real.norm_eq_abs]
  have h1 : |W' s - W s| ≤ γ * (Real.sqrt (Fintype.card A) * ‖v‖) * ‖z‖ := by
    have e : W' s - W s = ∑ a, v (s, a) * (γ * ∑ s', P s a s' * z s') := by
      simp only [hW', hW, pgaW, QFunction, hz, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e]
    have hPz : ∀ a, |∑ s', P s a s' * z s'| ≤ ‖z‖ := fun a => by
      calc _ ≤ ∑ s', |P s a s' * z s'| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s', P s a s' * ‖z‖ := Finset.sum_le_sum fun s' _ => by
            rw [abs_mul, abs_of_nonneg ((hP s a).1 s')]
            exact mul_le_mul_of_nonneg_left (hb z s') ((hP s a).1 s')
        _ = ‖z‖ := by rw [← Finset.sum_mul, (hP s a).2, one_mul]
    calc _ ≤ ∑ a, |v (s, a) * (γ * ∑ s', P s a s' * z s')| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, |v (s, a)| * (γ * ‖z‖) := Finset.sum_le_sum fun a _ => by
          rw [abs_mul, abs_mul, abs_of_nonneg hγ0]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hPz a) hγ0) (abs_nonneg _)
      _ = (∑ a, |v (s, a)|) * (γ * ‖z‖) := by rw [Finset.sum_mul]
      _ ≤ (Real.sqrt (Fintype.card A) * ‖v‖) * (γ * ‖z‖) :=
          mul_le_mul_of_nonneg_right (pga_cs v s) (mul_nonneg hγ0 (norm_nonneg _))
      _ = _ := by ring
  have h2 : |γ * ∑ y, (Mx s y - Mp s y) * R y| ≤
      γ * (Real.sqrt (Fintype.card A) * ‖x - π‖) * ‖R‖ := by
    rw [abs_mul, abs_of_nonneg hγ0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hγ0
    calc _ ≤ ∑ y, |(Mx s y - Mp s y) * R y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |Mx s y - Mp s y| * ‖R‖ := Finset.sum_le_sum fun y _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb R y) (abs_nonneg _)
      _ = (∑ y, |Mx s y - Mp s y|) * ‖R‖ := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pga_Mdiff hP x π s) (norm_nonneg _)
  calc |f s| ≤ |W' s - W s| + |γ * ∑ y, (Mx s y - Mp s y) * R y| := abs_add_le _ _
    _ ≤ _ := add_le_add (h1.trans (mul_le_mul_of_nonneg_left hzb
          (mul_nonneg hγ0 (by positivity))))
        (h2.trans (mul_le_mul_of_nonneg_left hRb (mul_nonneg hγ0 (by positivity))))

theorem direct_smoothness_core {P : S → A → S → ℝ} {r : S → A → ℝ} {γ : ℝ}
    (hM : IsFiniteMDP P r γ) :
    ∀ (s₀ : S), ∀ π ∈ simplexSet S A, ∀ π' ∈ simplexSet S A,
      ‖gradient (directValue P r γ (fun x => if x = s₀ then 1 else 0)) π -
          gradient (directValue P r γ (fun x => if x = s₀ then 1 else 0)) π'‖ ≤
        2 * γ * (Fintype.card A : ℝ) / (1 - γ) ^ 3 * ‖π - π'‖ := by
  intro s₀ π hπ π' hπ'
  have hM' := hM
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM'
  have hg : 0 < 1 - γ := by linarith
  set μ : S → ℝ := fun x => if x = s₀ then 1 else 0 with hμ
  rw [(pga_hasGrad hM μ π hπ).gradient, (pga_hasGrad hM μ π' hπ').gradient]
  set u := pgaGrad P r γ μ π - pgaGrad P r γ μ π' with hu
  set C := 2 * γ * (Fintype.card A : ℝ) / (1 - γ) ^ 3 with hC
  have hC0 : 0 ≤ C := by positivity
  have hinner : ∀ v, inner ℝ u v ≤ C * ‖π - π'‖ * ‖v‖ := by
    intro v
    rw [hu, inner_sub_left, pga_inner_grad hP hγ0 hγ1 π hπ μ v,
      pga_inner_grad hP hγ0 hγ1 π' hπ' μ v]
    have e : ∀ (p : EuclideanSpace ℝ (S × A)),
        ∑ s0, μ s0 * ∑' t : ℕ, γ ^ t * ∑ s', (pgaM (asPolicy p) P ^ t) s0 s' *
          (∑ a, v (s', a) * QFunction (asPolicy p) P r γ s' a) =
        pgaR P γ (asPolicy p) (pgaW P r γ p v) s₀ := by
      intro p; simp [hμ, pgaR, pgaW]
    rw [e, e]
    have hd := pga_RW_diff hP hr hγ0 hγ1 π' hπ' π hπ v
    have h1 := norm_le_pi_norm (fun s => pgaR P γ (asPolicy π) (pgaW P r γ π v) s -
      pgaR P γ (asPolicy π') (pgaW P r γ π' v) s) s₀
    rw [Real.norm_eq_abs] at h1
    refine (le_abs_self _).trans (h1.trans (hd.trans (le_of_eq ?_)))
    have hA : Real.sqrt (Fintype.card A) * Real.sqrt (Fintype.card A) = (Fintype.card A : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hg' : (1 - γ) ≠ 0 := hg.ne'
    rw [hC]
    field_simp
    rw [mul_one] at *
    linear_combination (2 * γ * ‖v‖ * ‖π - π'‖) * hA
  by_cases h0 : ‖u‖ = 0
  · rw [h0]; positivity
  have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have := hinner u
  rw [real_inner_self_eq_norm_sq] at this
  have h2 : ‖u‖ * ‖u‖ ≤ (C * ‖π - π'‖) * ‖u‖ := by nlinarith
  exact le_of_mul_le_mul_right h2 hpos

end SM

section GOAL
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

lemma pga_proj_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (C : Set E)
    (hC : ∀ x ∈ C, ∀ y ∈ C, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → x + t • (y - x) ∈ C)
    (Proj : E → E) (hProj : IsProjOnto C Proj) (z y : E) (hy : y ∈ C) :
    inner ℝ (z - Proj z) (y - Proj z) ≤ 0 := by
  set p := Proj z
  have hp : p ∈ C := (hProj z).1
  set a := inner ℝ (z - p) (y - p) with ha
  set b := ‖y - p‖ ^ 2 with hb
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 2 * a ≤ t * b := by
    intro t ht0 ht1
    have h := (hProj z).2 (p + t • (y - p)) (hC p hp y hy t ht0.le ht1)
    have h2 : ‖z - p‖ ^ 2 ≤ ‖z - (p + t • (y - p))‖ ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    have e : z - (p + t • (y - p)) = (z - p) - t • (y - p) := by abel
    rw [e, norm_sub_sq_real (z - p) (t • (y - p)), inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs] at h2
    nlinarith
  by_contra hneg
  push_neg at hneg
  have hb0 : 0 ≤ b := by positivity
  rcases eq_or_lt_of_le hb0 with hb0' | hbpos
  · have := key 1 one_pos le_rfl; rw [← hb0'] at this; linarith
  · set t := min 1 (a / b)
    have ht0 : 0 < t := lt_min one_pos (div_pos hneg hbpos)
    have h1 := key t ht0 (min_le_left _ _)
    have h2 : t * b ≤ a := by
      have : t ≤ a / b := min_le_right _ _
      calc t * b ≤ a / b * b := mul_le_mul_of_nonneg_right this hb0
        _ = a := div_mul_cancel₀ a hbpos.ne'
    linarith

lemma pga_seg_mem : ∀ x ∈ simplexSet S A, ∀ y ∈ simplexSet S A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    x + t • (y - x) ∈ simplexSet S A := by
  intro x hx y hy t ht0 ht1 s
  have hx' : IsPolicy (asPolicy x) := hx
  have hy' : IsPolicy (asPolicy y) := hy
  have e : ∀ a, asPolicy (x + t • (y - x)) s a = (1 - t) * x (s, a) + t * y (s, a) := by
    intro a; simp [asPolicy]; ring
  refine ⟨fun a => ?_, ?_⟩
  · rw [e]
    have := (hx' s).1 a; have := (hy' s).1 a
    have h1 : 0 ≤ 1 - t := by linarith
    exact add_nonneg (mul_nonneg h1 (by assumption)) (mul_nonneg ht0 (by assumption))
  · simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 : ∑ a, x (s, a) = 1 := (hx' s).2
    have h2 : ∑ a, y (s, a) = 1 := (hy' s).2
    rw [h1, h2]; ring

theorem pga_smooth_gen {P : S → A → S → ℝ} {r : S → A → ℝ} {γ : ℝ}
    (hM : IsFiniteMDP P r γ) (μ : S → ℝ) (hμ : IsDist μ) :
    ∀ π ∈ simplexSet S A, ∀ π' ∈ simplexSet S A,
      ‖gradient (directValue P r γ μ) π - gradient (directValue P r γ μ) π'‖ ≤
        2 * γ * (Fintype.card A : ℝ) / (1 - γ) ^ 3 * ‖π - π'‖ := by
  intro π hπ π' hπ'
  have hM' := hM
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM'
  have hg : 0 < 1 - γ := by linarith
  rw [(pga_hasGrad hM μ π hπ).gradient, (pga_hasGrad hM μ π' hπ').gradient]
  set u := pgaGrad P r γ μ π - pgaGrad P r γ μ π' with hu
  set C := 2 * γ * (Fintype.card A : ℝ) / (1 - γ) ^ 3 with hC
  have hC0 : 0 ≤ C := by positivity
  have hinner : ∀ v, inner ℝ u v ≤ C * ‖π - π'‖ * ‖v‖ := by
    intro v
    rw [hu, inner_sub_left, pga_inner_grad hP hγ0 hγ1 π hπ μ v,
      pga_inner_grad hP hγ0 hγ1 π' hπ' μ v]
    have e : ∀ (p : EuclideanSpace ℝ (S × A)),
        ∑ s0, μ s0 * ∑' t : ℕ, γ ^ t * ∑ s', (pgaM (asPolicy p) P ^ t) s0 s' *
          (∑ a, v (s', a) * QFunction (asPolicy p) P r γ s' a) =
        ∑ s0, μ s0 * pgaR P γ (asPolicy p) (pgaW P r γ p v) s0 := by
      intro p; rfl
    rw [e, e, ← Finset.sum_sub_distrib]
    have hd := pga_RW_diff hP hr hγ0 hγ1 π' hπ' π hπ v
    set yv : S → ℝ := fun s => pgaR P γ (asPolicy π) (pgaW P r γ π v) s -
      pgaR P γ (asPolicy π') (pgaW P r γ π' v) s with hyv
    have h1 : ∑ s0, (μ s0 * pgaR P γ (asPolicy π) (pgaW P r γ π v) s0 -
        μ s0 * pgaR P γ (asPolicy π') (pgaW P r γ π' v) s0) ≤ ‖yv‖ := by
      calc _ = ∑ s0, μ s0 * yv s0 := Finset.sum_congr rfl fun s0 _ => by rw [hyv]; ring
        _ ≤ ∑ s0, μ s0 * ‖yv‖ := Finset.sum_le_sum fun s0 _ =>
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans
              (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm yv s0)) (hμ.1 s0)
        _ = ‖yv‖ := by rw [← Finset.sum_mul, hμ.2, one_mul]
    refine h1.trans (hd.trans (le_of_eq ?_))
    have hA : Real.sqrt (Fintype.card A) * Real.sqrt (Fintype.card A) = (Fintype.card A : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hg' : (1 - γ) ≠ 0 := hg.ne'
    rw [hC]
    field_simp
    rw [mul_one] at *
    linear_combination (2 * γ * ‖v‖ * ‖π - π'‖) * hA
  by_cases h0 : ‖u‖ = 0
  · rw [h0]; positivity
  have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have := hinner u
  rw [real_inner_self_eq_norm_sq] at this
  have h2 : ‖u‖ * ‖u‖ ≤ (C * ‖π - π'‖) * ‖u‖ := by nlinarith
  exact le_of_mul_le_mul_right h2 hpos

lemma pga_ascent {f : EuclideanSpace ℝ (S × A) → ℝ}
    (hgr : ∀ x ∈ simplexSet S A, HasGradientAt f (gradient f x) x) (β : ℝ) (hβ : 0 ≤ β)
    (hs : ∀ x ∈ simplexSet S A, ∀ y ∈ simplexSet S A,
      ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (x : EuclideanSpace ℝ (S × A)) (hx : x ∈ simplexSet S A)
    (y : EuclideanSpace ℝ (S × A)) (hy : y ∈ simplexSet S A) :
    f x + inner ℝ (gradient f x) (y - x) - β / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  set d := y - x with hd
  have hz : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • d ∈ simplexSet S A :=
    fun t ht => pga_seg_mem x hx y hy t ht.1 ht.2
  set ψ : ℝ → ℝ := fun t => f (x + t • d) - t * inner ℝ (gradient f x) d +
    β / 2 * t ^ 2 * ‖d‖ ^ 2 with hψ
  set ψ' : ℝ → ℝ := fun t => inner ℝ (gradient f (x + t • d)) d - inner ℝ (gradient f x) d +
    β * t * ‖d‖ ^ 2 with hψ'
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ψ (ψ' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h2 := ((hgr _ (hz t ht)).hasFDerivAt).comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => f (x + t • d))
        (inner ℝ (gradient f (x + t • d)) d) t := by
      simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h2
    have h4 := ((h3.sub ((hasDerivAt_id t).mul_const (inner ℝ (gradient f x) d))).add
      (((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖d‖ ^ 2)))
    refine h4.congr_deriv ?_
    simp only [hψ', id]; ring
  have hmono : MonotoneOn ψ (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t (interior_subset ht)).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have hb := hs (x + t • d) (hz t ⟨ht.1.le, ht.2.le⟩) x hx
    have e : x + t • d - x = t • d := by abel
    rw [e, norm_smul, Real.norm_of_nonneg ht0] at hb
    have hc : inner ℝ (gradient f (x + t • d) - gradient f x) d ≥
        -(β * (t * ‖d‖) * ‖d‖) := by
      have := abs_real_inner_le_norm (gradient f (x + t • d) - gradient f x) d
      have h5 : ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ ≤ β * (t * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      linarith [neg_abs_le (inner ℝ (gradient f (x + t • d) - gradient f x) d)]
    rw [inner_sub_left] at hc
    simp only [hψ']
    nlinarith
  have h01 := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_pow, mul_one,
    one_mul] at h01
  have hy' : x + d = y := by rw [hd]; abel
  rw [hy'] at h01
  have : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [this] at h01
  simp only [mul_zero, zero_mul, add_zero] at h01
  linarith

end GOAL

section MAIN
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

lemma pga_dist_norm (x y : EuclideanSpace ℝ (S × A)) (hx : x ∈ simplexSet S A)
    (hy : y ∈ simplexSet S A) : ‖x - y‖ ≤ Real.sqrt (2 * Fintype.card S) := by
  have hx' : IsPolicy (asPolicy x) := hx
  have hy' : IsPolicy (asPolicy y) := hy
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_prod_type]
  have hle : ∀ (q : EuclideanSpace ℝ (S × A)), IsPolicy (asPolicy q) → ∀ s a,
      q (s, a) ^ 2 ≤ q (s, a) := by
    intro q hq s a
    have h0 : 0 ≤ q (s, a) := (hq s).1 a
    have h1 : q (s, a) ≤ 1 := by
      have : ∑ b, q (s, b) = 1 := (hq s).2
      rw [← this]
      exact Finset.single_le_sum (f := fun b => q (s, b)) (fun b _ => (hq s).1 b)
        (Finset.mem_univ a)
    nlinarith
  calc ∑ s, ∑ a, ‖(x - y) (s, a)‖ ^ 2 ≤ ∑ s : S, ∑ a, (x (s, a) + y (s, a)) := by
        refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => ?_
        rw [Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
        have h1 := hle x hx' s a
        have h2 := hle y hy' s a
        have h3 : 0 ≤ x (s, a) := (hx' s).1 a
        have h4 : 0 ≤ y (s, a) := (hy' s).1 a
        nlinarith
    _ = ∑ s : S, (2 : ℝ) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_add_distrib]
        have h1 : ∑ a, x (s, a) = 1 := (hx' s).2
        have h2 : ∑ a, y (s, a) = 1 := (hy' s).2
        rw [h1, h2]; norm_num
    _ = 2 * Fintype.card S := by simp [mul_comm]

theorem projected_gradient_ascent_rate_core [DecidableEq A] {P : S → A → S → ℝ}
    {r : S → A → ℝ} {γ : ℝ} (hM : IsFiniteMDP P r γ)
    (hγ : 0 < γ) (μ : S → ℝ) (hμ : IsDist μ) (ρ : S → ℝ) (hρ : IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (D : ℝ) (hD : ∀ s, visitation πstar P γ ρ s ≤ D * μ s)
    (Proj : EuclideanSpace ℝ (S × A) → EuclideanSpace ℝ (S × A))
    (hProj : IsProjOnto (simplexSet S A) Proj)
    (π : ℕ → EuclideanSpace ℝ (S × A)) (hπ0 : π 0 ∈ simplexSet S A)
    (hrun : IsProjGARun P r γ μ ((1 - γ) ^ 3 / (2 * γ * (Fintype.card A : ℝ))) Proj π)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ T : ℕ,
      64 * γ * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) / ((1 - γ) ^ 6 * ε ^ 2) * D ^ 2 <
          (T : ℝ) →
        ∃ t ≤ T, valueAt πstar P r γ ρ - valueAt (asPolicy (π t)) P r γ ρ ≤ ε := by
  intro T hT
  have hM' := hM
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM'
  have hg : 0 < 1 - γ := by linarith
  have hS : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hρ.2; simp at this
  obtain ⟨s00⟩ := hS
  have hπ0' : IsPolicy (asPolicy (π 0)) := hπ0
  have hA : 0 < (Fintype.card A : ℝ) := by
    have : Nonempty A := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := (hπ0' s00).2; simp at this
    exact_mod_cast Fintype.card_pos
  set η := (1 - γ) ^ 3 / (2 * γ * (Fintype.card A : ℝ)) with hη
  set β := 2 * γ * (Fintype.card A : ℝ) / (1 - γ) ^ 3 with hβ
  have hβ0 : 0 < β := by positivity
  have hη0 : 0 < η := by positivity
  have hηβ : η * β = 1 := by rw [hη, hβ]; field_simp
  set f := directValue P r γ μ with hf
  have hmem : ∀ t, π t ∈ simplexSet S A := by
    intro t; induction t with
    | zero => exact hπ0
    | succ t _ => rw [hrun t]; exact (hProj _).1
  have hgr : ∀ x ∈ simplexSet S A, HasGradientAt f (gradient f x) x := by
    intro x hx
    have h := pga_hasGrad hM μ x hx
    rw [h.gradient]; exact h
  have hsm := pga_smooth_gen hM μ hμ
  have hfb : ∀ x ∈ simplexSet S A, |f x| ≤ 1 / (1 - γ) := by
    intro x hx
    have hx' : IsPolicy (asPolicy x) := hx
    simp only [hf, directValue, valueAt]
    calc _ ≤ ∑ s, |μ s * PolicyValue (asPolicy x) P r γ s| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, μ s * (1 / (1 - γ)) := Finset.sum_le_sum fun s _ => by
          rw [abs_mul, abs_of_nonneg (hμ.1 s)]
          exact mul_le_mul_of_nonneg_left (pga_value_bound hP hx' hr hγ0 hγ1 s) (hμ.1 s)
      _ = 1 / (1 - γ) := by rw [← Finset.sum_mul, hμ.2, one_mul]
  -- projection inequality at step t
  have hpi : ∀ t, ∀ y ∈ simplexSet S A,
      inner ℝ (π t - π (t + 1)) (y - π (t + 1)) + η * inner ℝ (gradient f (π t)) (y - π (t + 1))
        ≤ 0 := by
    intro t y hy
    have h := pga_proj_ineq (simplexSet S A) pga_seg_mem Proj hProj
      (π t + η • gradient f (π t)) y hy
    rw [← hrun t] at h
    have e : π t + η • gradient f (π t) - π (t + 1) = (π t - π (t + 1)) + η • gradient f (π t) := by
      abel
    rw [e, inner_add_left, real_inner_smul_left] at h
    exact h
  -- ascent
  have hasc : ∀ t, f (π t) + β / 2 * ‖π (t + 1) - π t‖ ^ 2 ≤ f (π (t + 1)) := by
    intro t
    have h1 := pga_ascent hgr β hβ0.le hsm (π t) (hmem t) (π (t + 1)) (hmem (t + 1))
    have h2 := hpi t (π t) (hmem t)
    rw [real_inner_self_eq_norm_sq] at h2
    have e1 : inner ℝ (gradient f (π t)) (π t - π (t + 1)) =
        - inner ℝ (gradient f (π t)) (π (t + 1) - π t) := by
      rw [← inner_neg_right, neg_sub]
    rw [e1, norm_sub_rev] at h2
    have h3 : β * ‖π (t + 1) - π t‖ ^ 2 ≤ inner ℝ (gradient f (π t)) (π (t + 1) - π t) := by
      have : ‖π (t + 1) - π t‖ ^ 2 ≤ η * inner ℝ (gradient f (π t)) (π (t + 1) - π t) := by
        linarith
      calc β * ‖π (t + 1) - π t‖ ^ 2 ≤ β * (η * inner ℝ (gradient f (π t)) (π (t + 1) - π t)) :=
            mul_le_mul_of_nonneg_left this hβ0.le
        _ = _ := by rw [← mul_assoc, mul_comm β η, hηβ, one_mul]
    linarith
  have htel : ∀ n, f (π 0) + β / 2 * ∑ t ∈ Finset.range n, ‖π (t + 1) - π t‖ ^ 2 ≤ f (π n) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hasc n
      linarith
  have hT0 : 0 < T := by
    have : 0 ≤ 64 * γ * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) / ((1 - γ) ^ 6 * ε ^ 2) * D ^ 2 := by
      positivity
    have : (0 : ℝ) < T := lt_of_le_of_lt this hT
    exact_mod_cast this
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT0
  set c := 4 / (β * (1 - γ) * T) with hc
  have hex : ∃ t < T, ‖π (t + 1) - π t‖ ^ 2 ≤ c := by
    by_contra hne
    push_neg at hne
    have hlt : ∑ t ∈ Finset.range T, c < ∑ t ∈ Finset.range T, ‖π (t + 1) - π t‖ ^ 2 :=
      Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 hT0⟩
        fun t ht => hne t (Finset.mem_range.1 ht)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
    have h1 := htel T
    have h2 := abs_le.1 (hfb _ (hmem T))
    have h3 := abs_le.1 (hfb _ (hmem 0))
    have h4 : (T : ℝ) * c = 4 / (β * (1 - γ)) := by rw [hc]; field_simp
    rw [h4] at hlt
    have h5 : β / 2 * (4 / (β * (1 - γ))) = 2 / (1 - γ) := by field_simp; ring
    have h6 : β / 2 * (4 / (β * (1 - γ))) < β / 2 * ∑ t ∈ Finset.range T, ‖π (t + 1) - π t‖ ^ 2 :=
      mul_lt_mul_of_pos_left hlt (by positivity)
    have h7 : 1 / (1 - γ) + 1 / (1 - γ) = 2 / (1 - γ) := by ring
    linarith
  obtain ⟨t, htT, ht⟩ := hex
  refine ⟨t + 1, by omega, ?_⟩
  set e := ‖π (t + 1) - π t‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  set K := Real.sqrt (2 * Fintype.card S) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  -- gradient bound at π (t+1)
  have hG : ∀ πbar ∈ simplexSet S A,
      inner ℝ (πbar - π (t + 1)) (gradient f (π (t + 1))) ≤ 2 * β * e * K := by
    intro πbar hπbar
    set δ := πbar - π (t + 1) with hδ
    have hδn : ‖δ‖ ≤ K := pga_dist_norm _ _ hπbar (hmem (t + 1))
    have e1 : inner ℝ δ (gradient f (π (t + 1))) =
        inner ℝ δ (gradient f (π (t + 1)) - gradient f (π t)) + inner ℝ δ (gradient f (π t)) := by
      rw [inner_sub_right]; ring
    have h1 : inner ℝ δ (gradient f (π (t + 1)) - gradient f (π t)) ≤ ‖δ‖ * (β * e) := by
      refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact hsm _ (hmem (t + 1)) _ (hmem t)
    have h2 : inner ℝ δ (gradient f (π t)) ≤ ‖δ‖ * (β * e) := by
      have hp := hpi t πbar hπbar
      have h3 : inner ℝ (π t - π (t + 1)) δ ≥ -(e * ‖δ‖) := by
        have := real_inner_le_norm (π (t + 1) - π t) δ
        have e2 : inner ℝ (π t - π (t + 1)) δ = - inner ℝ (π (t + 1) - π t) δ := by
          rw [← inner_neg_left, neg_sub]
        rw [e2]; linarith
      have h4 : η * inner ℝ δ (gradient f (π t)) ≤ e * ‖δ‖ := by
        rw [real_inner_comm]; linarith
      calc inner ℝ δ (gradient f (π t)) = β * (η * inner ℝ δ (gradient f (π t))) := by
            rw [← mul_assoc, mul_comm β η, hηβ, one_mul]
        _ ≤ β * (e * ‖δ‖) := mul_le_mul_of_nonneg_left h4 hβ0.le
        _ = ‖δ‖ * (β * e) := by ring
    rw [e1]
    have hbe : 0 ≤ β * e := by positivity
    calc _ ≤ ‖δ‖ * (β * e) + ‖δ‖ * (β * e) := add_le_add h1 h2
      _ ≤ K * (β * e) + K * (β * e) := by gcongr
      _ = 2 * β * e * K := by ring
  -- domination
  have hvs := pga_vis_basic hP hπstar hγ0 hγ1 hρ
  have hπt : IsPolicy (asPolicy (π (t + 1))) := hmem (t + 1)
  have hvm := pga_vis_basic hP hπt hγ0 hγ1 hμ
  have hD0 : 0 ≤ D := by
    by_contra hneg
    push_neg at hneg
    have : ∑ s, visitation πstar P γ ρ s ≤ 0 := Finset.sum_nonpos fun s _ =>
      (hD s).trans (mul_nonpos_of_nonpos_of_nonneg hneg.le (hμ.1 s))
    linarith [hvs.2.2]
  have hdom := pga_dom1 hM μ hμ ρ hρ πstar hπstar (π (t + 1)) (hmem (t + 1)) _ hG
    (1 / (1 - γ) * D) (fun s => by
      refine (hD s).trans ?_
      have h1 := hvm.1 s
      have : D * μ s = 1 / (1 - γ) * D * ((1 - γ) * μ s) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left h1 (by positivity))
  refine hdom.trans ?_
  set X := 1 / (1 - γ) * D * (2 * β * e * K) with hX
  have hX0 : 0 ≤ X := by positivity
  have hK2 : K ^ 2 = 2 * Fintype.card S := Real.sq_sqrt (by positivity)
  have hX2 : X ^ 2 ≤ (1 / (1 - γ) * D) ^ 2 * (4 * β ^ 2) * (2 * Fintype.card S) * c := by
    have : X ^ 2 = (1 / (1 - γ) * D) ^ 2 * (4 * β ^ 2) * K ^ 2 * e ^ 2 := by rw [hX]; ring
    rw [this, hK2]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hY : (1 / (1 - γ) * D) ^ 2 * (4 * β ^ 2) * (2 * Fintype.card S) * c =
      64 * γ * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) / ((1 - γ) ^ 6 * ε ^ 2) * D ^ 2 *
        ε ^ 2 / T := by
    rw [hc, hβ]; field_simp; ring
  have hlt : X ^ 2 < ε ^ 2 := by
    refine lt_of_le_of_lt (hX2.trans (le_of_eq hY)) ?_
    rw [div_lt_iff₀ hTr]
    have := mul_lt_mul_of_pos_right hT (by positivity : (0 : ℝ) < ε ^ 2)
    linarith
  exact (pow_lt_pow_iff_left₀ hX0 hε.le two_ne_zero).1 hlt |>.le

end MAIN
end PolicyGradTheory.ProjGA

open PolicyGradTheory.ProjGA


theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ)
    (hγ : 0 < γ) (μ : S → ℝ) (hμ : IsDist μ) (ρ : S → ℝ) (hρ : IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) (hopt : IsOptimalPolicy πstar P r γ)
    (D : ℝ) (hD : ∀ s, visitation πstar P γ ρ s ≤ D * μ s)
    (Proj : EuclideanSpace ℝ (S × A) → EuclideanSpace ℝ (S × A))
    (hProj : IsProjOnto (simplexSet S A) Proj)
    (π : ℕ → EuclideanSpace ℝ (S × A)) (hπ0 : π 0 ∈ simplexSet S A)
    (hrun : IsProjGARun P r γ μ ((1 - γ) ^ 3 / (2 * γ * (Fintype.card A : ℝ))) Proj π)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ T : ℕ,
      64 * γ * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) / ((1 - γ) ^ 6 * ε ^ 2) * D ^ 2 <
          (T : ℝ) →
        ∃ t ≤ T, valueAt πstar P r γ ρ - valueAt (asPolicy (π t)) P r γ ρ ≤ ε := by
  exact projected_gradient_ascent_rate_core hM hγ μ hμ ρ hρ πstar hπstar D hD Proj hProj π hπ0 hrun ε hε
