-- Prove2me | solution 1 for PolicyGradTheory.NPG.performance_difference
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:39:57.974703+00:00
-- url     : https://prove2.me/submissions/fdb42fe9-b614-4484-8cd9-9ef42c3911f5

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

set_option autoImplicit false

open FoundationsML.ReinforcementLearning in
theorem rl_M_nonneg {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s s' : S) : 0 ≤ InducedTransition π P s s' := by
  unfold InducedTransition
  exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s'))

open FoundationsML.ReinforcementLearning in
theorem rl_M_sum {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s : S) : ∑ s', InducedTransition π P s s' = 1 := by
  unfold InducedTransition
  rw [Finset.sum_comm]
  have h1 : ∀ a, ∑ s', P s a s' = 1 := fun a => (hP s a).2
  simp_rw [← Finset.mul_sum, h1, mul_one]
  exact (hπ s).2

open FoundationsML.ReinforcementLearning in
theorem rl_D_zero {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 s : S) :
    OccupationDist π P s0 0 s = if s = s0 then 1 else 0 := rfl

open FoundationsML.ReinforcementLearning in
theorem rl_D_succ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (s' : S) :
    OccupationDist π P s0 (t + 1) s' =
      ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s' := rfl

open FoundationsML.ReinforcementLearning in
theorem rl_D_prob {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s0 : S) (t : ℕ) :
    (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · rw [rl_D_zero]
      split_ifs <;> norm_num
    · simp [rl_D_zero]
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · rw [rl_D_succ]
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (rl_M_nonneg π hπ P hP s s'))
    · simp only [rl_D_succ]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, rl_M_sum π hπ P hP, mul_one]
      exact ih.2

open FoundationsML.ReinforcementLearning in
theorem rl_summable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → ℝ) (s0 : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s0 t s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |g s'|)) (fun t => ?_)
  obtain ⟨hnn, hsum⟩ := rl_D_prob π hπ P hP s0 t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
  calc |∑ s', OccupationDist π P s0 t s' * g s'|
      ≤ ∑ s', |OccupationDist π P s0 t s' * g s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', |g s'| := by
      apply Finset.sum_le_sum
      intro s' _
      rw [abs_mul, abs_of_nonneg (hnn s')]
      have h1 : OccupationDist π P s0 t s' ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ s')
      calc OccupationDist π P s0 t s' * |g s'| ≤ 1 * |g s'| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |g s'| := one_mul _

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pd_g {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (s : S) :
    ∑ a, π s a * advantage π' P r γ s a =
      InducedReward π r s + γ * ∑ s', InducedTransition π P s s' * PolicyValue π' P r γ s'
        - PolicyValue π' P r γ s := by
  unfold advantage QFunction InducedReward InducedTransition
  have h1 : ∑ a, π s a * PolicyValue π' P r γ s = PolicyValue π' P r γ s := by
    rw [← Finset.sum_mul, (hπ s).2, one_mul]
  have h2 : ∑ a, π s a * (γ * ∑ s', P s a s' * PolicyValue π' P r γ s') =
      γ * ∑ s', (∑ a, π s a * P s a s') * PolicyValue π' P r γ s' := by
    calc ∑ a, π s a * (γ * ∑ s', P s a s' * PolicyValue π' P r γ s')
        = ∑ a, ∑ s', γ * (π s a * P s a s' * PolicyValue π' P r γ s') := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = ∑ s', ∑ a, γ * (π s a * P s a s' * PolicyValue π' P r γ s') := Finset.sum_comm
      _ = γ * ∑ s', (∑ a, π s a * P s a s') * PolicyValue π' P r γ s' := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]

open FoundationsML.ReinforcementLearning in
theorem pd_shift {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (V : S → ℝ) :
    ∑ s, OccupationDist π P s0 t s * ∑ s', InducedTransition π P s s' * V s' =
      ∑ u, OccupationDist π P s0 (t + 1) u * V u := by
  simp only [rl_D_succ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem pd_visit {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (γ : ℝ) (s₀ s : S) :
    visitation π P γ (fun x => if x = s₀ then 1 else 0) s =
      (1 - γ) * ∑' t : ℕ, γ ^ t * OccupationDist π P s₀ t s := by
  unfold visitation
  simp [ite_mul, Finset.sum_ite_eq']

open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (s₀ : S) :
    PolicyValue π P r γ s₀ - PolicyValue π' P r γ s₀ =
      1 / (1 - γ) * ∑ s, PolicyGradTheory.ProjGA.visitation π P γ (fun x => if x = s₀ then 1 else 0) s *
        ∑ a, π s a * PolicyGradTheory.ProjGA.advantage π' P r γ s a := by
  obtain ⟨hP, -, hγ0, hγ1⟩ := hM
  have hne : (1 - γ) ≠ 0 := by linarith
  set V' : S → ℝ := PolicyValue π' P r γ with hV'
  set R : S → ℝ := InducedReward π r with hR
  set D : ℕ → S → ℝ := OccupationDist π P s₀ with hD
  have hT : ∀ s, Summable (fun t : ℕ => γ ^ t * D t s) := by
    intro s
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hγ0 t)
      ((rl_D_prob π hπ P hP s₀ t).1 s)) (fun t => ?_) (summable_geometric_of_lt_one hγ0 hγ1)
    obtain ⟨hnn, hsum⟩ := rl_D_prob π hπ P hP s₀ t
    have h1 : D t s ≤ 1 := by
      rw [hD, ← hsum]
      exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ s)
    exact mul_le_of_le_one_right (pow_nonneg hγ0 t) h1
  have hb : Summable (fun t : ℕ => γ ^ t * ∑ u, D t u * V' u) :=
    rl_summable π hπ P hP γ hγ0 hγ1 V' s₀
  have hR' : Summable (fun t : ℕ => γ ^ t * ∑ u, D t u * R u) :=
    rl_summable π hπ P hP γ hγ0 hγ1 R s₀
  have hb1 : Summable (fun t : ℕ => γ ^ (t + 1) * ∑ u, D (t + 1) u * V' u) :=
    (summable_nat_add_iff 1).mpr hb
  simp_rw [pd_visit, pd_g P r γ π π' hπ]
  have step1 : 1 / (1 - γ) * ∑ s, (1 - γ) * (∑' t : ℕ, γ ^ t * D t s) *
        (R s + γ * ∑ s', InducedTransition π P s s' * V' s' - V' s) =
      ∑ s, ∑' t : ℕ, γ ^ t * D t s *
        (R s + γ * ∑ s', InducedTransition π P s s' * V' s' - V' s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [tsum_mul_right]
    field_simp
  rw [step1, ← Summable.tsum_finsetSum (fun s _ => (hT s).mul_right _)]
  have step2 : ∀ t : ℕ, ∑ s, γ ^ t * D t s *
        (R s + γ * ∑ s', InducedTransition π P s s' * V' s' - V' s) =
      γ ^ t * ∑ u, D t u * R u + γ ^ (t + 1) * ∑ u, D (t + 1) u * V' u
        - γ ^ t * ∑ u, D t u * V' u := by
    intro t
    have e : ∀ s, γ ^ t * D t s *
        (R s + γ * ∑ s', InducedTransition π P s s' * V' s' - V' s) =
        γ ^ t * (D t s * R s) + γ ^ (t + 1) * (D t s * ∑ s', InducedTransition π P s s' * V' s')
          - γ ^ t * (D t s * V' s) := by intro s; ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hD, pd_shift]
  rw [tsum_congr step2, (hR'.add hb1).tsum_sub hb, hR'.tsum_add hb1, hb.tsum_eq_zero_add]
  have h0 : γ ^ 0 * ∑ u, D 0 u * V' u = V' s₀ := by
    simp [hD, rl_D_zero]
  rw [h0]
  have hV : PolicyValue π P r γ s₀ = ∑' t : ℕ, γ ^ t * ∑ u, D t u * R u := rfl
  rw [hV]
  ring
