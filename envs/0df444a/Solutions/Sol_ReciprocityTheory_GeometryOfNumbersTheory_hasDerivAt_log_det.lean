-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_log_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:13.66263+00:00
-- url     : https://prove2.me/submissions/ebce6bc2-e114-4e4d-a82d-2f0822289874

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_hasDerivAt_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix MeasureTheory
open scoped ComplexOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hpos : (G t).PosDef) :
    HasDerivAt (fun s => Real.log (G s).det.re) ((G t)⁻¹ * G').trace.re t := by
  have hd := hasDerivAt_det G G' t hG
  have hre : HasDerivAt (fun s => (G s).det.re) ((G t).adjugate * G').trace.re t := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa [Function.comp_def] using this
  have hdpos : 0 < (G t).det := hpos.det_pos
  have hre0 : 0 < (G t).det.re ∧ (G t).det.im = 0 := by
    have := Complex.lt_def.1 hdpos
    simp only [Complex.zero_re, Complex.zero_im] at this
    exact ⟨this.1, this.2.symm⟩
  have hlog := hre.log hre0.1.ne'
  convert hlog using 1
  have hdet : (G t).det = (((G t).det.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre0.2])
  rw [Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul, Ring.inverse_eq_inv', smul_eq_mul, hdet,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  simp only [Complex.ofReal_re]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
