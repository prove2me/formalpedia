-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_complex_div_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/2e76232c-8059-4d48-a3c1-8697c33a2ebc

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f h : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hh : ContDiffAt ℝ 1 h x)
    (hne : h x ≠ 0) :
    ContDiffAt ℝ 1 (fun y => f y / h y) x := by
  have hfr : ContDiffAt ℝ 1 (fun y => (f y).re) x := by
    exact Complex.reCLM.contDiff.contDiffAt.comp x hf
  have hfi : ContDiffAt ℝ 1 (fun y => (f y).im) x := by
    exact Complex.imCLM.contDiff.contDiffAt.comp x hf
  have hhr : ContDiffAt ℝ 1 (fun y => (h y).re) x := by
    exact Complex.reCLM.contDiff.contDiffAt.comp x hh
  have hhi : ContDiffAt ℝ 1 (fun y => (h y).im) x := by
    exact Complex.imCLM.contDiff.contDiffAt.comp x hh
  have hnorm : ContDiffAt ℝ 1
      (fun y => Complex.normSq (h y)) x := by
    simpa only [Complex.normSq_apply] using
      (hhr.mul hhr).add (hhi.mul hhi)
  have hnorm_ne : Complex.normSq (h x) ≠ 0 :=
    (Complex.normSq_eq_zero.not).mpr hne
  have hreal : ContDiffAt ℝ 1
      (fun y =>
        (f y).re * (h y).re / Complex.normSq (h y) +
          (f y).im * (h y).im / Complex.normSq (h y)) x :=
    ((hfr.mul hhr).div hnorm hnorm_ne).add
      ((hfi.mul hhi).div hnorm hnorm_ne)
  have himag : ContDiffAt ℝ 1
      (fun y =>
        (f y).im * (h y).re / Complex.normSq (h y) -
          (f y).re * (h y).im / Complex.normSq (h y)) x :=
    ((hfi.mul hhr).div hnorm hnorm_ne).sub
      ((hfr.mul hhi).div hnorm hnorm_ne)
  convert Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp x
    (hreal.prodMk himag) using 1
  funext y
  apply Complex.ext
  · change
      (f y / h y).re =
        (f y).re * (h y).re / Complex.normSq (h y) +
          (f y).im * (h y).im / Complex.normSq (h y)
    exact Complex.div_re (f y) (h y)
  · change
      (f y / h y).im =
        (f y).im * (h y).re / Complex.normSq (h y) -
          (f y).re * (h y).im / Complex.normSq (h y)
    exact Complex.div_im (f y) (h y)
end PermanentRollout
