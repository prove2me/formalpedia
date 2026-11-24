-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_zsmul_98c0401cc918
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:58.097703+00:00
-- url     : https://prove2.me/submissions/0e6b8cbb-4855-4c96-8d42-cb33bef847a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_smul_09ba6711cb9c

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
theorem _root_.solution (c : ℤ) (u : Fin m → K) : latticeForm (c • u) = C (c : K) * latticeForm u := by
  rw [← latticeForm_smul]
  congr 1
  ext j
  simp
end GroundTheory.Heights₂.Heights.LatticeModel
