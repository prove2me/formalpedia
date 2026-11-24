-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_aeval_8800237edca7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:13.776215+00:00
-- url     : https://prove2.me/submissions/891344d8-7c7d-416a-bd81-23eabfe89392

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {σ : Type*} (z : Cone n ℂ) (g : σ → MvPolynomial (Coord n) ℤ)
    (F : MvPolynomial σ ℤ) :
    evalCone z (aeval g F) = eval₂ (Int.castRingHom ℂ) (fun j ↦ evalCone z (g j)) F := by
  change (eval₂Hom (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2)) (aeval g F) = _
  rw [aeval_def, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _
end GroundTheory.Heights₂.Heights.SmallSections
