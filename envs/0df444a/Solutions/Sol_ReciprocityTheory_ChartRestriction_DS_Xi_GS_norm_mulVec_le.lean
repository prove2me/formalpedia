-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.norm_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:00.618122+00:00
-- url     : https://prove2.me/submissions/31a3f746-a447-46ca-996b-423f7b55b39d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {n m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution {k r : ℕ} (A : Mat k r) (y : Fin (2 * r + k + 1) → ℂ) :
    ‖(WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))‖ ≤
      gN A * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin (2 * r + k + 1)))‖ := by
  have hnn : (0 : ℝ) ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, gN, ← Real.sqrt_mul hnn]
  refine Real.sqrt_le_sqrt ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(A *ᵥ y) i‖ ≤ ∑ j, ‖A i j‖ * ‖y j‖ := by
    simp only [mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  calc ‖(A *ᵥ y) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖y j‖) ^ 2 := by gcongr
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖y j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = ∑ j, Complex.normSq (A i j) * ∑ j, ‖y j‖ ^ 2 := by
      rw [← Finset.sum_mul]; simp only [Complex.normSq_eq_norm_sq]
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
