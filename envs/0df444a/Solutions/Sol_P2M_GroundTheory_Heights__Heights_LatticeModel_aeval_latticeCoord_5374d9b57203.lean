-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_aeval_latticeCoord_5374d9b57203
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:41.988482+00:00
-- url     : https://prove2.me/submissions/cbc320ce-8a18-4451-a2e8-db5aa6344db9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
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
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (φ : Fin (N + 1) → Fin (r + 1) → K) (g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) :
    aeval (latticeCoord φ) g = dehom K r (latticeMap φ g) := by
  have h : (aeval (latticeCoord φ)).toRingHom = (dehom K r).comp (latticeMap φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [latticeMap]
    · intro v
      simp [latticeMap, latticeCoord_eq]
  exact RingHom.congr_fun h g
end GroundTheory.Heights₂.Heights.LatticeModel
