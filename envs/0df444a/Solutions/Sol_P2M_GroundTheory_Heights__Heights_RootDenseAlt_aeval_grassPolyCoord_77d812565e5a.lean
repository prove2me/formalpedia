-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_grassPolyCoord_77d812565e5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:11.555033+00:00
-- url     : https://prove2.me/submissions/e81d1e75-e7d9-474b-b7d7-265453f4e6d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDense

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootDenseAlt
namespace GroundTheory.Heights₂.Heights.RootDenseAlt
theorem _root_.solution {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval x (grassPolyCoord f j m p) = rootCoord (fun τ a b => x (τ, a, b)) p := by
  simp only [grassPolyCoord, rootCoord]
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp only [colsOf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
    onePipe, Matrix.of_apply]
  generalize (p.2.1.orderEmbOfFin p.2.2) b = c
  induction c using Fin.addCases with
  | left c => simp [Fin.append_left, Matrix.one_apply, apply_ite]
  | right c => simp [Fin.append_right]
end GroundTheory.Heights₂.Heights.RootDenseAlt
