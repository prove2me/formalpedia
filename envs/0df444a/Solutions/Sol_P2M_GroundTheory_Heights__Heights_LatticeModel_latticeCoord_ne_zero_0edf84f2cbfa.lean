-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_ne_zero_0edf84f2cbfa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:11.542878+00:00
-- url     : https://prove2.me/submissions/b167e790-1ff3-429e-82bb-f7a72d666ce9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_ne_zero_d609092c2fe8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_eq_665c52b880b5


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
theorem _root_.solution (hφ : IsDualBasis L φ) (b : Fin (N + 1)) : latticeCoord φ ⟨(), b⟩ ≠ 0 := by
  rw [latticeCoord_eq]
  exact dehom_latticeForm_ne_zero (hφ.independent.ne_zero b)
end GroundTheory.Heights₂.Heights.LatticeModel
