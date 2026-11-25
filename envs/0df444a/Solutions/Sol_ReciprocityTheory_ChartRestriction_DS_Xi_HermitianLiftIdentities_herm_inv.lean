-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.herm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:12.459191+00:00
-- url     : https://prove2.me/submissions/fa2a8150-35e5-4448-af89-73a6b6355330

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_herm_UH__244872423f2e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_uh_mul_inv

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
variable (k r : ℕ)
variable {k r}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
theorem _root_.solution {x : Mat k r} (hx : x ∈ GV k r) (g : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((x⁻¹ * g) *ᵥ v) w = herm (Hpk k r) (g *ᵥ v) (x *ᵥ w) := by
  rw [← herm_UH' (Hpk k r) hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, uh_mul_inv hx,
    Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
