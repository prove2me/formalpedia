-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_single_zero_55c62bc01ab6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:57.635975+00:00
-- url     : https://prove2.me/submissions/2db12d09-22ce-4792-a4f8-d7e07fafb8f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB

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
theorem _root_.solution : dehom K r (latticeForm (Pi.single 0 1 : Fin (r + 1) → K)) = 1 := by
  simp [dehom, latticeForm, Pi.single_apply, genericVal]
end GroundTheory.Heights₂.Heights.LatticeModel
