-- Prove2me | solution 1 for PGLandscape.Regularized.regularization_gap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T14:41:04.126966+00:00
-- url     : https://prove2.me/submissions/689d25a1-4edb-46ee-b35a-ec0baeedbdcb

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PGLandscape_Regularized_Model

set_option autoImplicit false

open scoped ENNReal

namespace P2Ma771

open FoundationsML.ReinforcementLearning PGLandscape.Regularized

theorem M_nonneg {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s s' : S) : 0 ≤ InducedTransition π P s s' := by
  unfold InducedTransition
  exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s'))

theorem M_sum {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s : S) : ∑ s', InducedTransition π P s s' = 1 := by
  unfold InducedTransition
  rw [Finset.sum_comm]
  have h1 : ∀ a, ∑ s', P s a s' = 1 := fun a => (hP s a).2
  simp_rw [← Finset.mul_sum, h1, mul_one]
  exact (hπ s).2

theorem D_succ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (s' : S) :
    OccupationDist π P s0 (t + 1) s' =
      ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s' := rfl

theorem D_prob {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s0 : S) (t : ℕ) :
    (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · show 0 ≤ (if s = s0 then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · show ∑ s, (if s = s0 then (1 : ℝ) else 0) = 1
      simp
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · rw [D_succ]
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (M_nonneg π hπ P hP s s'))
    · simp only [D_succ]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, M_sum π hπ P hP, mul_one]
      exact ih.2

theorem summ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → ℝ) (s0 : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s0 t s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |g s'|)) (fun t => ?_)
  obtain ⟨hnn, hsum⟩ := D_prob π hπ P hP s0 t
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

/-- The extended-real cost sum equals `ofReal` of the real cost sum for a nonnegative cost. -/
theorem ennr_eq {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ : ∀ s, 0 ≤ ρ s)
    (h : S → ℝ) (hh : ∀ s, 0 ≤ h s) :
    ENNReal.ofReal (1 - γ) * ∑ s, ENNReal.ofReal (ρ s) * ∑' t : ℕ, ENNReal.ofReal (γ ^ t) *
      ∑ s', ENNReal.ofReal (OccupationDist π P s t s') * ENNReal.ofReal (h s') =
    ENNReal.ofReal ((1 - γ) * ∑ s, ρ s * ∑' t : ℕ, γ ^ t *
      ∑ s', OccupationDist π P s t s' * h s') := by
  have hX : ∀ s t, 0 ≤ ∑ s', OccupationDist π P s t s' * h s' := fun s t =>
    Finset.sum_nonneg (fun s' _ => mul_nonneg ((D_prob π hπ P hP s t).1 s') (hh s'))
  have h1 : ∀ s t, ∑ s', ENNReal.ofReal (OccupationDist π P s t s') * ENNReal.ofReal (h s') =
      ENNReal.ofReal (∑ s', OccupationDist π P s t s' * h s') := by
    intro s t
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun s' _ => mul_nonneg ((D_prob π hπ P hP s t).1 s') (hh s'))]
    exact Finset.sum_congr rfl (fun s' _ => (ENNReal.ofReal_mul ((D_prob π hπ P hP s t).1 s')).symm)
  have hY : ∀ s, 0 ≤ ∑' t : ℕ, γ ^ t * ∑ s', OccupationDist π P s t s' * h s' := fun s =>
    tsum_nonneg (fun t => mul_nonneg (pow_nonneg hγ0 t) (hX s t))
  have h2 : ∀ s, ∑' t : ℕ, ENNReal.ofReal (γ ^ t) *
      ∑ s', ENNReal.ofReal (OccupationDist π P s t s') * ENNReal.ofReal (h s') =
      ENNReal.ofReal (∑' t : ℕ, γ ^ t * ∑ s', OccupationDist π P s t s' * h s') := by
    intro s
    rw [ENNReal.ofReal_tsum_of_nonneg (fun t => mul_nonneg (pow_nonneg hγ0 t) (hX s t))
      (summ π hπ P hP γ hγ0 hγ1 h s)]
    refine tsum_congr (fun t => ?_)
    rw [h1 s t, ENNReal.ofReal_mul (pow_nonneg hγ0 t)]
  simp_rw [h2]
  rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_sum_of_nonneg
    (fun s _ => mul_nonneg (hρ s) (hY s))]
  congr 1
  exact Finset.sum_congr rfl (fun s _ => (ENNReal.ofReal_mul (hρ s)).symm)

/-- Real identity: adding a constant `C` to the per-state cost adds `C` to the loss. -/
theorem real_shift {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (gs : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ1 : ∑ s, ρ s = 1)
    (C : ℝ) :
    (1 - γ) * ∑ s, ρ s * ∑' t : ℕ, γ ^ t *
      ∑ s', OccupationDist π P s t s' * ((∑ i, π s' i * gs s' i) + C) =
    loss0 P gs γ ρ π + C := by
  have hne : (1 - γ) ≠ 0 := by linarith
  have e1 : ∀ s t, ∑ s', OccupationDist π P s t s' * ((∑ i, π s' i * gs s' i) + C) =
      (∑ s', OccupationDist π P s t s' * InducedReward π gs s') + C := by
    intro s t
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, (D_prob π hπ P hP s t).2, one_mul]
    rfl
  have e2 : ∀ s, ∑' t : ℕ, γ ^ t *
      ∑ s', OccupationDist π P s t s' * ((∑ i, π s' i * gs s' i) + C) =
      PolicyValue π P gs γ s + C * (1 - γ)⁻¹ := by
    intro s
    simp_rw [e1, mul_add]
    rw [Summable.tsum_add (summ π hπ P hP γ hγ0 hγ1 _ s)
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right C), tsum_mul_right,
      tsum_geometric_of_lt_one hγ0 hγ1]
    unfold PolicyValue
    ring
  simp_rw [e2]
  unfold loss0
  rw [Finset.sum_congr rfl (fun x _ => mul_add (ρ x) _ _), Finset.sum_add_distrib,
    ← Finset.sum_mul, hρ1]
  field_simp

theorem loss0_nonneg {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (gs : S → A → ℝ) (hg : ∀ s i, 0 ≤ gs s i) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → ℝ) (hρ : ∀ s, 0 ≤ ρ s) : 0 ≤ loss0 P gs γ ρ π := by
  unfold loss0 PolicyValue
  refine mul_nonneg (by linarith) (Finset.sum_nonneg (fun s _ => mul_nonneg (hρ s)
    (tsum_nonneg (fun t => mul_nonneg (pow_nonneg hγ0 t) (Finset.sum_nonneg (fun s' _ =>
      mul_nonneg ((D_prob π hπ P hP s t).1 s') ?_))))))
  unfold InducedReward
  exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s').1 a) (hg s' a))

/-- `ℓ_0 ≤ ℓ_λ`. -/
theorem regLoss_ge {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (lam : ℝ)
    (hM : IsRegMDP P gs γ ρ) (π : S → I → ℝ) (hπ : IsPolicy π) :
    ENNReal.ofReal (loss0 P gs γ ρ π) ≤ regLoss P gs γ ρ lam π := by
  obtain ⟨hP, hg, hγ0, hγ1, hρ, hρ1⟩ := hM
  have key := ennr_eq π hπ P hP γ hγ0.le hγ1 ρ hρ (fun s' => (∑ i, π s' i * gs s' i) + 0)
    (fun s' => by simpa using Finset.sum_nonneg (fun i _ => mul_nonneg ((hπ s').1 i) (hg s' i)))
  rw [real_shift π hπ P hP gs γ hγ0.le hγ1 ρ hρ1 0, add_zero] at key
  rw [← key]
  unfold regLoss
  gcongr with s _ t s' _
  unfold regCost
  rw [add_zero]
  exact le_self_add

/-- `ℓ_λ(π) ≤ ℓ_0(π) + C` when every per-state regularized cost is at most `g_s^⊤ π(s) + C`. -/
theorem regLoss_le {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (lam : ℝ)
    (hM : IsRegMDP P gs γ ρ) (π : S → I → ℝ) (hπ : IsPolicy π) (C : ℝ) (hC : 0 ≤ C)
    (hcost : ∀ s, regCost gs lam (π s) s ≤ ENNReal.ofReal ((∑ i, π s i * gs s i) + C)) :
    regLoss P gs γ ρ lam π ≤ ENNReal.ofReal (loss0 P gs γ ρ π + C) := by
  obtain ⟨hP, hg, hγ0, hγ1, hρ, hρ1⟩ := hM
  have key := ennr_eq π hπ P hP γ hγ0.le hγ1 ρ hρ (fun s' => (∑ i, π s' i * gs s' i) + C)
    (fun s' => add_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg ((hπ s').1 i) (hg s' i))) hC)
  rw [real_shift π hπ P hP gs γ hγ0.le hγ1 ρ hρ1 C] at key
  rw [← key]
  unfold regLoss
  gcongr with s _ t s' _
  exact hcost s'

/-- The KL divergence from uniform of a vector bounded below by `ε/k`. -/
theorem kl_le {I : Type*} [Fintype I] [Nonempty I] (a : I → ℝ) (ε : ℝ) (hε : 0 < ε)
    (ha : ∀ i, ε / (Fintype.card I : ℝ) ≤ a i) :
    klUniform a ≤ ENNReal.ofReal (Real.log (1 / ε)) := by
  have hk : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpos : ∀ i, 0 < a i := fun i => lt_of_lt_of_le (div_pos hε hk) (ha i)
  unfold klUniform
  rw [if_pos hpos]
  apply ENNReal.ofReal_le_ofReal
  calc ∑ i, (1 / (Fintype.card I : ℝ)) * Real.log ((1 / (Fintype.card I : ℝ)) / a i)
      ≤ ∑ _i : I, (1 / (Fintype.card I : ℝ)) * Real.log (1 / ε) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.log_le_log (div_pos (by positivity) (hpos i))
        rw [div_le_div_iff₀ (hpos i) hε]
        have e : 1 / (Fintype.card I : ℝ) * ε = ε / Fintype.card I := by ring
        linarith [ha i]
    _ = Real.log (1 / ε) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- Crude performance-difference bound: occupation measures drift by at most `t η` in `ℓ¹`. -/
theorem occ_drift {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (P : S → A → S → ℝ)
    (hP : IsTransitionKernel P) (η : ℝ) (hη : ∀ s, ∑ a, |π' s a - π s a| ≤ η) (s0 : S) :
    ∀ t : ℕ, ∑ s, |OccupationDist π' P s0 t s - OccupationDist π P s0 t s| ≤ t * η := by
  have hT : ∀ s, ∑ s', |InducedTransition π' P s s' - InducedTransition π P s s'| ≤ η := by
    intro s
    calc ∑ s', |InducedTransition π' P s s' - InducedTransition π P s s'|
        = ∑ s', |∑ a, (π' s a - π s a) * P s a s'| := by
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          unfold InducedTransition
          rw [← Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_congr rfl (fun a _ => by ring)
      _ ≤ ∑ s', ∑ a, |π' s a - π s a| * P s a s' := by
          apply Finset.sum_le_sum
          intro s' _
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl (fun a _ => by rw [abs_mul, abs_of_nonneg ((hP s a).1 s')])
      _ = ∑ a, |π' s a - π s a| := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [← Finset.mul_sum, (hP s a).2, mul_one]
      _ ≤ η := hη s
  intro t
  induction t with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro s _
    show |(if s = s0 then (1 : ℝ) else 0) - (if s = s0 then (1 : ℝ) else 0)| = 0
    simp
  | succ t ih =>
    set D' := OccupationDist π' P s0 t
    set D := OccupationDist π P s0 t
    calc ∑ s', |OccupationDist π' P s0 (t + 1) s' - OccupationDist π P s0 (t + 1) s'|
        = ∑ s', |∑ s, ((D' s - D s) * InducedTransition π' P s s' +
            D s * (InducedTransition π' P s s' - InducedTransition π P s s'))| := by
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          rw [D_succ, D_succ, ← Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_congr rfl (fun s _ => by ring)
      _ ≤ ∑ s', ∑ s, (|D' s - D s| * InducedTransition π' P s s' +
            D s * |InducedTransition π' P s s' - InducedTransition π P s s'|) := by
          apply Finset.sum_le_sum
          intro s' _
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun s _ => ?_))
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (M_nonneg π' hπ' P hP s s'),
            abs_of_nonneg ((D_prob π hπ P hP s0 t).1 s)]
      _ = ∑ s, (|D' s - D s| * ∑ s', InducedTransition π' P s s' +
            D s * ∑ s', |InducedTransition π' P s s' - InducedTransition π P s s'|) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ s, (|D' s - D s| * 1 + D s * η) := by
          apply Finset.sum_le_sum
          intro s _
          rw [M_sum π' hπ' P hP s]
          gcongr
          · exact (D_prob π hπ P hP s0 t).1 s
          · exact hT s
      _ = ∑ s, |D' s - D s| + η := by
          have hDs : ∑ s, D s = 1 := (D_prob π hπ P hP s0 t).2
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hDs]
          ring
      _ ≤ t * η + η := by linarith
      _ = ((t + 1 : ℕ) : ℝ) * η := by push_cast; ring

/-- Crude performance-difference bound for the unregularized loss. -/
theorem loss_drift {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π') (P : S → A → S → ℝ)
    (hP : IsTransitionKernel P) (gs : S → A → ℝ) (G : ℝ) (hg : ∀ s a, 0 ≤ gs s a)
    (hG : ∀ s a, gs s a ≤ G) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → ℝ) (hρ : ∀ s, 0 ≤ ρ s) (hρ1 : ∑ s, ρ s = 1)
    (η : ℝ) (hη : ∀ s, ∑ a, |π' s a - π s a| ≤ η) :
    loss0 P gs γ ρ π' ≤ loss0 P gs γ ρ π + η * G / (1 - γ) := by
  have hγ1' : 0 < 1 - γ := by linarith
  have hG0 : 0 ≤ G := by
    obtain ⟨s⟩ : Nonempty S := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hρ1
    obtain ⟨a⟩ : Nonempty A := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := (hπ s).2
      simp at this
    exact (hg s a).trans (hG s a)
  have hη0 : 0 ≤ η := by
    obtain ⟨s⟩ : Nonempty S := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hρ1
    exact (Finset.sum_nonneg (fun a _ => abs_nonneg _)).trans (hη s)
  -- rewards
  have hR'le : ∀ s, InducedReward π' gs s ≤ G := by
    intro s
    unfold InducedReward
    calc ∑ a, π' s a * gs s a ≤ ∑ a, π' s a * G :=
          Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hG s a) ((hπ' s).1 a))
      _ = G := by rw [← Finset.sum_mul, (hπ' s).2, one_mul]
  have hR'0 : ∀ s, 0 ≤ InducedReward π' gs s := fun s =>
    Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ' s).1 a) (hg s a))
  have hRd : ∀ s, InducedReward π' gs s - InducedReward π gs s ≤ η * G := by
    intro s
    unfold InducedReward
    calc ∑ a, π' s a * gs s a - ∑ a, π s a * gs s a = ∑ a, (π' s a - π s a) * gs s a := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun a _ => by ring)
      _ ≤ ∑ a, |π' s a - π s a| * G := by
          apply Finset.sum_le_sum
          intro a _
          calc (π' s a - π s a) * gs s a ≤ |π' s a - π s a| * gs s a :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (hg s a)
            _ ≤ |π' s a - π s a| * G := mul_le_mul_of_nonneg_left (hG s a) (abs_nonneg _)
      _ = (∑ a, |π' s a - π s a|) * G := by rw [Finset.sum_mul]
      _ ≤ η * G := mul_le_mul_of_nonneg_right (hη s) hG0
  -- per-step
  have hstep : ∀ s0 (t : ℕ),
      ∑ s', OccupationDist π' P s0 t s' * InducedReward π' gs s' -
        ∑ s', OccupationDist π P s0 t s' * InducedReward π gs s' ≤ (η * G) * ((t : ℝ) + 1) := by
    intro s0 t
    have hd := occ_drift π π' hπ hπ' P hP η hη s0 t
    obtain ⟨hDn, hDs⟩ := D_prob π hπ P hP s0 t
    calc ∑ s', OccupationDist π' P s0 t s' * InducedReward π' gs s' -
          ∑ s', OccupationDist π P s0 t s' * InducedReward π gs s'
        = ∑ s', ((OccupationDist π' P s0 t s' - OccupationDist π P s0 t s') *
            InducedReward π' gs s' + OccupationDist π P s0 t s' *
            (InducedReward π' gs s' - InducedReward π gs s')) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun s _ => by ring)
      _ ≤ ∑ s', (|OccupationDist π' P s0 t s' - OccupationDist π P s0 t s'| * G +
            OccupationDist π P s0 t s' * (η * G)) := by
          apply Finset.sum_le_sum
          intro s _
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left (hRd s) (hDn s))
          calc (OccupationDist π' P s0 t s - OccupationDist π P s0 t s) * InducedReward π' gs s
              ≤ |OccupationDist π' P s0 t s - OccupationDist π P s0 t s| *
                  InducedReward π' gs s :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (hR'0 s)
            _ ≤ _ := mul_le_mul_of_nonneg_left (hR'le s) (abs_nonneg _)
      _ = (∑ s', |OccupationDist π' P s0 t s' - OccupationDist π P s0 t s'|) * G + η * G := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hDs, one_mul]
      _ ≤ (t * η) * G + η * G := by gcongr
      _ = (η * G) * ((t : ℝ) + 1) := by ring
  -- value difference
  have hV : ∀ s0, PolicyValue π' P gs γ s0 - PolicyValue π P gs γ s0 ≤
      (η * G) * (γ / (1 - γ) ^ 2 + (1 - γ)⁻¹) := by
    intro s0
    have hs1 := (summ π' hπ' P hP γ hγ0 hγ1 (InducedReward π' gs) s0).hasSum
    have hs2 := (summ π hπ P hP γ hγ0 hγ1 (InducedReward π gs) s0).hasSum
    have hn : ‖γ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hγ0]; exact hγ1
    have hA := hasSum_coe_mul_geometric_of_norm_lt_one hn
    have hB := hasSum_geometric_of_lt_one hγ0 hγ1
    have hC := (hA.add hB).mul_left (η * G)
    have hD := hs1.sub hs2
    unfold PolicyValue
    refine hasSum_le (fun t => ?_) hD hC
    have := hstep s0 t
    have hγt : 0 ≤ γ ^ t := pow_nonneg hγ0 t
    show γ ^ t * _ - γ ^ t * _ ≤ η * G * ((t : ℝ) * γ ^ t + γ ^ t)
    nlinarith
  unfold loss0
  have hsum : ∑ s, ρ s * PolicyValue π' P gs γ s ≤
      ∑ s, ρ s * PolicyValue π P gs γ s + (η * G) * (γ / (1 - γ) ^ 2 + (1 - γ)⁻¹) := by
    calc ∑ s, ρ s * PolicyValue π' P gs γ s
        ≤ ∑ s, (ρ s * PolicyValue π P gs γ s + ρ s * ((η * G) * (γ / (1 - γ) ^ 2 + (1 - γ)⁻¹))) := by
          apply Finset.sum_le_sum
          intro s _
          have := mul_le_mul_of_nonneg_left (hV s) (hρ s)
          nlinarith
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hρ1, one_mul]
  have hfin : (1 - γ) * ((η * G) * (γ / (1 - γ) ^ 2 + (1 - γ)⁻¹)) = η * G / (1 - γ) := by
    field_simp
    ring
  calc (1 - γ) * ∑ s, ρ s * PolicyValue π' P gs γ s
      ≤ (1 - γ) * (∑ s, ρ s * PolicyValue π P gs γ s +
          (η * G) * (γ / (1 - γ) ^ 2 + (1 - γ)⁻¹)) := mul_le_mul_of_nonneg_left hsum hγ1'.le
    _ = _ := by rw [mul_add, hfin]

end P2Ma771

open PGLandscape.Regularized FoundationsML.ReinforcementLearning in
theorem solution {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    [Nonempty S] [Nonempty I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (lam : ℝ)
    (hM : IsRegMDP P gs γ ρ) (hlam : 0 ≤ lam)
    (πlam : S → I → ℝ) (hπlam : IsPolicy πlam)
    (hmin : ∀ π : S → I → ℝ, IsPolicy π → regLoss P gs γ ρ lam πlam ≤ regLoss P gs γ ρ lam π) :
    ∀ π : S → I → ℝ, IsPolicy π →
      loss0 P gs γ ρ πlam ≤ loss0 P gs γ ρ π + lam * (1 + Real.log (1 + costConst gs γ / lam)) := by
  intro π hπ
  have hM' := hM
  obtain ⟨hP, hg, hγ0, hγ1, hρ, hρ1⟩ := hM'
  have hγ1' : 0 < 1 - γ := by linarith
  have hlow := P2Ma771.regLoss_ge P gs γ ρ lam hM πlam hπlam
  have hL0 := P2Ma771.loss0_nonneg π hπ P hP gs hg γ hγ0.le hγ1 ρ hρ
  rcases hlam.lt_or_eq with hpos | hzero
  swap
  · -- λ = 0
    subst hzero
    have hup := P2Ma771.regLoss_le P gs γ ρ 0 hM π hπ 0 le_rfl (fun s => by
      unfold regCost
      simp)
    have := (hlow.trans (hmin π hπ)).trans hup
    rw [add_zero, ENNReal.ofReal_le_ofReal_iff hL0] at this
    simpa using this
  -- λ > 0
  set G : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun p : S × I => |gs p.1 p.2|) with hGdef
  have hG : ∀ s i, gs s i ≤ G := by
    intro s i
    have : |gs (s, i).1 (s, i).2| ≤ G :=
      Finset.le_sup' (fun p : S × I => |gs p.1 p.2|) (Finset.mem_univ (s, i))
    exact (le_abs_self _).trans this
  have hG0 : 0 ≤ G := by
    obtain ⟨s⟩ := (inferInstance : Nonempty S)
    obtain ⟨i⟩ := (inferInstance : Nonempty I)
    exact (hg s i).trans (hG s i)
  have hc : costConst gs γ = 2 * G / (1 - γ) := rfl
  set c := costConst gs γ with hcdef
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set ε : ℝ := lam / (lam + c) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by positivity)]; linarith
  have hk : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  set πe : S → I → ℝ := fun s i => (1 - ε) * π s i + ε / (Fintype.card I : ℝ) with hπe
  have hπe_lb : ∀ s i, ε / (Fintype.card I : ℝ) ≤ πe s i := by
    intro s i
    have := mul_nonneg (sub_nonneg.mpr hε1) ((hπ s).1 i)
    simp only [hπe]
    linarith
  have hπe_pol : IsPolicy πe := by
    intro s
    refine ⟨fun i => (div_nonneg hε0.le hk.le).trans (hπe_lb s i), ?_⟩
    simp only [hπe]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, (hπ s).2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp
    ring
  have hη : ∀ s, ∑ i, |πe s i - π s i| ≤ 2 * ε := by
    intro s
    calc ∑ i, |πe s i - π s i| = ∑ i, ε * |1 / (Fintype.card I : ℝ) - π s i| := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show πe s i - π s i = ε * (1 / (Fintype.card I : ℝ) - π s i) by
            simp only [hπe]; ring, abs_mul, abs_of_nonneg hε0.le]
      _ ≤ ∑ i, ε * (1 / (Fintype.card I : ℝ) + π s i) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ hε0.le
          refine (abs_sub _ _).trans ?_
          rw [abs_of_nonneg (by positivity), abs_of_nonneg ((hπ s).1 i)]
      _ = 2 * ε := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, (hπ s).2, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          field_simp
          ring
  set L : ℝ := Real.log (1 / ε) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
  have hLeq : L = Real.log (1 + c / lam) := by
    rw [hL, hε]
    congr 1
    field_simp
  have hcost : ∀ s, regCost gs lam (πe s) s ≤
      ENNReal.ofReal ((∑ i, πe s i * gs s i) + lam * L) := by
    intro s
    unfold regCost
    rw [ENNReal.ofReal_add (Finset.sum_nonneg (fun i _ => mul_nonneg ((hπe_pol s).1 i) (hg s i)))
      (mul_nonneg hpos.le hL0), ENNReal.ofReal_mul hpos.le]
    gcongr
    exact P2Ma771.kl_le (πe s) ε hε0 (hπe_lb s)
  have hup := P2Ma771.regLoss_le P gs γ ρ lam hM πe hπe_pol (lam * L) (mul_nonneg hpos.le hL0) hcost
  have hchain := (hlow.trans (hmin πe hπe_pol)).trans hup
  have hLe0 := P2Ma771.loss0_nonneg πe hπe_pol P hP gs hg γ hγ0.le hγ1 ρ hρ
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have hdrift := P2Ma771.loss_drift π πe hπ hπe_pol P hP gs G hg hG γ hγ0.le hγ1 ρ hρ hρ1 (2 * ε) hη
  have hεc : 2 * ε * G / (1 - γ) ≤ lam := by
    have : 2 * ε * G / (1 - γ) = ε * c := by rw [hc]; ring
    rw [this, hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [← hLeq]
  nlinarith
