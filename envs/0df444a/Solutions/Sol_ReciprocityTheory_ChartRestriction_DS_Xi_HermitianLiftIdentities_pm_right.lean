-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.pm_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:34.463862+00:00
-- url     : https://prove2.me/submissions/9b9ff225-e9a0-43cf-9356-13e50fc5972b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_herm_sum_l

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
theorem _root_.solution {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (g * y) = Pm k r (g * κ) * τ := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply]
  have e : (g * y) *ᵥ phiV' k r b = ∑ c, τ c b • ((g * κ) *ᵥ phiV' k r c) := by
    rw [← Matrix.mulVec_mulVec, hY b, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [e, herm_sum_l]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
