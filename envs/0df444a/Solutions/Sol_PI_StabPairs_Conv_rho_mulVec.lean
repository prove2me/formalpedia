-- Prove2me | solution 1 for PI.StabPairs.Conv.rho_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:43.574542+00:00
-- url     : https://prove2.me/submissions/4da1061d-5d4e-41ab-a0a8-587af6ce1b51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec
import Theorems.Thm_PI_StabPairs_Conv_Wm_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    PI.StabPairsW.rhoOf k r z z' γ u u' *ᵥ v =
      v + Ff k r z *ᵥ ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) +
        (γ * Ff k r z') *ᵥ ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) := by
  have hF : ∀ (x y : Fin (r + 1) → ℂ), Fm k r z z' γ *ᵥ Sum.elim x y =
      Ff k r z *ᵥ x + (γ * Ff k r z') *ᵥ y := by
    intro x y
    rw [← Matrix.mulVec_mulVec]
    ext i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fm,
      Matrix.of_apply, gramVec, Ff, Pi.add_apply, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  unfold PI.StabPairsW.rhoOf
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Wm_sub_one, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  rw [hF, ← add_assoc]
end PI.StabPairs.Conv
