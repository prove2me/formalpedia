-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_eq_665c52b880b5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:48.494845+00:00
-- url     : https://prove2.me/submissions/1700d454-a295-4eb4-9418-221a31116417

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_882e60645eed

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
variable {r : ℕ}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (φ : Fin (N + 1) → Fin (r + 1) → K) (v : Coord fun _ : Unit ↦ N) :
    latticeCoord φ v = dehom K r (latticeForm (φ v.2)) :=
  (dehom_latticeForm _).symm
end GroundTheory.Heights₂.Heights.LatticeModel
