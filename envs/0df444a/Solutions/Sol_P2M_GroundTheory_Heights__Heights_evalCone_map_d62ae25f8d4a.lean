-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:39.523329+00:00
-- url     : https://prove2.me/submissions/b189d108-683d-4a32-a8c0-8d8cf262d8c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight

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
open MvPolynomial NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type} {n : ι → ℕ} {F F' : Type*} [CommRing F] [CommRing F'] (φ : F →+* F')
    (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    evalCone (fun k i ↦ φ (z k i)) f = φ (evalCone z f) := by
  unfold evalCone
  rw [MvPolynomial.eval₂_comp_left φ]
  congr 1
  exact RingHom.ext_int _ _
end GroundTheory.Heights₂.Heights
