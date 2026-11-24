-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_intQuad_cast_144727a14362
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:18.360899+00:00
-- url     : https://prove2.me/submissions/f36a73f9-8963-427c-8834-2d1b8de99cf4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {R : Type*} [CommRing R] {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    ((intQuad B v : ℤ) : R) = (fun k => (v k : R)) ⬝ᵥ B.map (Int.cast : ℤ → R) *ᵥ fun k => (v k : R) := by
  simp only [intQuad, dotProduct, mulVec, map_apply]
  push_cast
  rfl
end GroundTheory.Heights₂.Heights.Regular
