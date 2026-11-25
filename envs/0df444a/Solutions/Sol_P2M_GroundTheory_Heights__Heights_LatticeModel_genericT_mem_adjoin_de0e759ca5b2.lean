-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_mem_adjoin_de0e759ca5b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:09:54.062844+00:00
-- url     : https://prove2.me/submissions/31be42b3-dc3c-43e4-a872-94882c9476b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_eq_8e6cdd01db8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_ne_zero_0edf84f2cbfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_div_mem_adjoin_bc6b541a5772
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_single_zero_55c62bc01ab6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {N r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)}
  {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hL : L.FG) (hφ : IsDualBasis L φ) (j : Fin r) :
    genericT K r j ∈ IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1))) := by
  have h := div_mem (dehom_div_mem_adjoin hL hφ (Pi.single j.succ 1))
    (dehom_div_mem_adjoin hL hφ (Pi.single 0 1))
  have hy := latticeCoord_ne_zero hφ 0
  rw [dehom_single_zero, ← genericT_eq] at h
  have e : genericT K r j / latticeCoord φ ⟨(), 0⟩ / (1 / latticeCoord φ ⟨(), 0⟩) = genericT K r j := by
    field_simp
  rwa [e] at h
end GroundTheory.Heights₂.Heights.LatticeModel
