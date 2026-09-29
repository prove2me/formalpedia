-- Prove2me | solution 1 for TongEM.pd_comm
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T02:44:33.349989+00:00
-- url     : https://prove2.me/submissions/47b7a54a-11b5-4c3a-95bf-a45be1bcb6f7

import Definitions.Def_TongEM_wave_ops

namespace TongEM
open Larmor
end TongEM

open TongEM Larmor

theorem solution (f : Vec → ℝ) (hf : SmoothS f) (i j : Fin 3) (x : Vec) :
    pd i (pd j f) x = pd j (pd i f) x := by
  unfold pd
  have hf2 : ContDiff ℝ 2 f := contDiff_infty.mp hf 2
  have hC1 : ContDiff ℝ 1 (fderiv ℝ f) := hf2.fderiv_right (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ f) := hC1.differentiable (by norm_num)
  rw [fderiv_clm_apply (hD x) (differentiableAt_const _),
    fderiv_clm_apply (hD x) (differentiableAt_const _)]
  simp
  exact (hf2.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness])) _ _
