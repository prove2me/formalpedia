-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_yEval_eq_5a232bddc35c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:17.624797+00:00
-- url     : https://prove2.me/submissions/14d41ef7-d707-4548-9f6b-13a36cf7a64f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
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
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) : yEval φ g = dehom K r (latticeMap φ g) := by
  have h : yEval φ = (dehom K r).comp (latticeMap φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [yEval, latticeMap]
    · intro v
      simp [yEval, latticeMap, latticeCoord_eq]
  rw [h, RingHom.comp_apply]
end GroundTheory.Heights₂.Heights.LatticeModel
