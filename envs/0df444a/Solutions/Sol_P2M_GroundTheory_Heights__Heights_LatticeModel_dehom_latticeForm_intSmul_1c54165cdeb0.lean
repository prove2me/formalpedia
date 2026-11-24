-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_intSmul_1c54165cdeb0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:57.283034+00:00
-- url     : https://prove2.me/submissions/05bdf6c3-8ac3-476a-9e69-f65bd10f5c5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
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
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (k : ℤ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm ((k : K) • u)) = k * dehom K r (latticeForm u) := by
  rw [latticeForm_smul, map_mul]
  simp [dehom]
end GroundTheory.Heights₂.Heights.LatticeModel
