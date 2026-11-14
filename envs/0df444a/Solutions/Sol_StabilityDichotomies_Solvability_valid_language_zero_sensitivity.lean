-- Prove2me | solution 1 for StabilityDichotomies.Solvability.valid_language_zero_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:23:12.735824+00:00
-- url     : https://prove2.me/submissions/074396c0-9eac-4bdd-8ff0-2eb4be03f046

import Definitions.Def_StabilityDichotomies_Approximability_Core
import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
noncomputable section
open scoped Classical BigOperators ENNReal
open StabilityDichotomies.Solvability

private theorem wasserstein_self_zero {V : Type} [Fintype V] (μ : PMF (V → Bool)) :
    wasserstein μ μ = 0 := by
  let π : (V → Bool) → (V → Bool) → ℝ := fun x y => if x = y then (μ x).toReal else 0
  have hπ : π ∈ FairProxy.ClosedFormDD.couplingSet
      (fun x => (μ x).toReal) (fun y => (μ y).toReal) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; simp [π, eq_comm]
    · intro y; simp [π, eq_comm]
    · intro x y
      by_cases he : x = y
      · subst y
        have hle : (μ x).toReal ≤ 1 := by
          have := (ENNReal.toReal_le_toReal (μ.apply_ne_top x) ENNReal.one_ne_top).2 (μ.coe_le_one x)
          simpa using this
        simp [π, ENNReal.toReal_nonneg, hle]
      · simp [π, he]
  let S : Set ℝ := {t : ℝ | ∃ ρ ∈ FairProxy.ClosedFormDD.couplingSet
      (fun x => (μ x).toReal) (fun y => (μ y).toReal),
    t = ∑ x, ∑ y, ρ x y * hammingCost x y}
  have hzero : (0 : ℝ) ∈ S := by
    refine ⟨π,hπ,?_⟩
    simp [π, hammingCost]
  have hnonneg : ∀ t ∈ S, 0 ≤ t := by
    intro t ht
    obtain ⟨ρ,hρ,rfl⟩ := ht
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (hρ.2.2 x y).1 (by simp [hammingCost])
  change sInf S = 0
  exact le_antisymm (csInf_le ⟨0, hnonneg⟩ hzero) (le_csInf ⟨0,hzero⟩ hnonneg)

theorem solution (Γ : Language) (b : Bool) (hv : Valid Γ b)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ A : Solver Γ, Approximates A ε ∧
      ∀ (V : Type) [Fintype V] (I : Instance Γ V), averageSensitivity A I = 0 := by
  let A : Solver Γ := fun V _ _ => PMF.pure (fun _ : V => b)
  refine ⟨A, ?_, ?_⟩
  · intro V _ I hI
    have hs : Solution I (fun _ => b) := by
      intro c hc
      exact hv c.rel.val c.rel.property
    have hvzero : violationCount I (fun _ => b) = 0 := by
      unfold violationCount
      have hf : I.constraints.filter (fun c => ¬ c.Satisfied (fun _ => b)) = 0 := by
        apply Multiset.filter_eq_nil.mpr
        intro c hc
        exact not_not_intro (hs c hc)
      simp [hf]
    change (∑ x : V → Bool, (PMF.pure (fun _ : V => b) x).toReal *
      (violationCount I x : ℝ)) ≤ ε * I.constraints.card
    simp only [PMF.pure_apply, apply_ite, ENNReal.toReal_one, ENNReal.toReal_zero,
      ite_mul, one_mul, zero_mul]
    simpa [hvzero] using mul_nonneg hε (Nat.cast_nonneg I.constraints.card)
  · intro V _ I
    simp [averageSensitivity, A, wasserstein_self_zero]

