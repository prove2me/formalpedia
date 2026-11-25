-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cC_cost
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:39.567149+00:00
-- url     : https://prove2.me/submissions/bf284f77-2c9c-496a-812d-9a1ae4d59b05

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {Q o d : ℕ} {u v u₁ v₁ w : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) (hv : unitP k j ρ v)
    (hl : u.length + v.length ≤ Q) (hwo : w.length ≤ o) (hu₁ : u₁.Sublist u) (hv₁ : v₁.Sublist (v ++ w.map nrm)) :
    ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ) ≤ (j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) := by
  have hu0 : ∀ X ∈ u, costP k j ρ X = 0 := fun X hX => by simp [costP, (hu X hX).1]
  have hv0 : ∀ X ∈ v, costP k j ρ X = 0 := fun X hX => by simp [costP, (hv X hX).1]
  have hle : ∀ X, costP k j ρ X ≤ j := fun X => by
    unfold costP
    split_ifs <;> omega
  have hA : ((u₁ ++ v₁).map (costP k j ρ)).sum ≤ j * o := by
    rw [List.map_append, List.sum_append]
    have h1 : (u₁.map (costP k j ρ)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx
      exact hu0 X (hu₁.subset hX)
    have h2 : (v₁.map (costP k j ρ)).sum ≤ ((v ++ w.map nrm).map (costP k j ρ)).sum :=
      (hv₁.map _).sum_le_sum (fun _ _ => Nat.zero_le _)
    have h3 : ((v ++ w.map nrm).map (costP k j ρ)).sum ≤ j * w.length := by
      rw [List.map_append, List.sum_append]
      have h0 : (v.map (costP k j ρ)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx
        exact hv0 X hX
      rw [h0, zero_add, List.map_map]
      calc ((w.map (costP k j ρ ∘ nrm))).sum ≤ (w.map (fun _ => j)).sum :=
            List.sum_le_sum (fun X _ => hle _)
        _ = j * w.length := by simp [mul_comm]
    have h4 : j * w.length ≤ j * o := Nat.mul_le_mul_left _ hwo
    omega
  have hL : (u₁ ++ v₁).length ≤ Q + o := by
    have := hu₁.length_le
    have := hv₁.length_le
    simp only [List.length_append, List.length_map] at *
    omega
  have key : ((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum ≤ j * o + d * (Q + o) := by
    rw [List.sum_map_add]
    have hd : ((u₁ ++ v₁).map (fun _ => d)).sum = (u₁ ++ v₁).length * d := by simp
    rw [hd]
    have : (u₁ ++ v₁).length * d ≤ d * (Q + o) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ hL
    omega
  exact_mod_cast key
end PI.UnitaryCorollaryDerivatives
