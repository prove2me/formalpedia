-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_eval_grassPolyCoord_a7272b63b5bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:26.692088+00:00
-- url     : https://prove2.me/submissions/18b4edf5-5cbc-4dab-b074-148934da005f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot

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
open GroundTheory.Heights₂.Heights.GrassmannianRootBound
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.GrassmannianRootBound
theorem _root_.solution {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval (fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2) (grassPolyCoord f j m p) =
      rootCoord ζ p := by
  let φ : MvPolynomial (Fin f × Fin j × Fin m) ℚ →+* ℂ :=
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom
  show φ _ = _
  rw [grassPolyCoord, RingHom.map_det, rootCoord]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, colsOf, onePipe, submatrix_apply, of_apply, id]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) (p.2.1.orderEmbOfFin p.2.2 b)
  · simp [Fin.append_left, Matrix.one_apply, apply_ite φ]
  · simp [Fin.append_right, φ]
end GroundTheory.Heights₂.Heights.GrassmannianRootBound
