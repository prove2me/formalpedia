-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_sum_41169ea91792
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:52.835941+00:00
-- url     : https://prove2.me/submissions/303fe1d8-8a31-4f8c-9ef6-ab304a07b1d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_eq_665c52b880b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_sum_776f66a088f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_zsmul_98c0401cc918


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
theorem _root_.solution (c : Fin (N + 1) → ℤ) :
    dehom K r (latticeForm (∑ b, c b • φ b)) = ∑ b, (c b : LatticeField K r) * latticeCoord φ ⟨(), b⟩ := by
  rw [latticeForm_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [latticeForm_zsmul, map_mul, latticeCoord_eq]
  simp [dehom]
end GroundTheory.Heights₂.Heights.LatticeModel
