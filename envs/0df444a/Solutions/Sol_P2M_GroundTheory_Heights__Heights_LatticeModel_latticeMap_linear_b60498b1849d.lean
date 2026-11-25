-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_linear_b60498b1849d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:48.855859+00:00
-- url     : https://prove2.me/submissions/ac43c21c-d231-47df-b7a2-99fe4bf4668f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_zsmul_98c0401cc918
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_sum_776f66a088f8

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
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (φ : Fin (N + 1) → Fin m → K) (c : Fin (N + 1) → ℤ) :
    latticeMap φ (∑ b, C (c b) * X ⟨(), b⟩) = latticeForm (∑ b, c b • φ b) := by
  rw [latticeForm_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [latticeForm_zsmul, map_mul]
  simp [latticeMap]
end GroundTheory.Heights₂.Heights.LatticeModel
