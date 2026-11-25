-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.logDetFlag_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:24.594901+00:00
-- url     : https://prove2.me/submissions/c9867151-8750-433f-ad95-d82f045c9310

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution : LogDetFlagEqStatement := by
  intro N hd m hm
  funext z
  have hs : star (fun k => (hd k : ℂ)) = fun k => (hd k : ℂ) :=
    funext fun k => Complex.conj_ofReal _
  have hH : (Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).conjTranspose =
      Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) *
        cellMat N z) (Fin.castLE hm) (Fin.castLE hm) := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]
  have him : (Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det.im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    change star _ = _
    rw [← Matrix.det_conjTranspose, hH]
  unfold logDetFlag detGram
  rw [(Complex.abs_re_eq_norm.2 him).symm]
end ReciprocityTheory.AnForm.P
