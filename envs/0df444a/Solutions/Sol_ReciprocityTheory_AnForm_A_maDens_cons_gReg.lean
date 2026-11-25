-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.maDens_cons_gReg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:40.974899+00:00
-- url     : https://prove2.me/submissions/7fee9f12-e6e7-4d4e-b36c-eff7607110a5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_gReg
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_cons
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (i : Fin (n + 1))
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons (fun y => gReg ε (y i)) φ) z =
      kDens n * cReg ε (z i) * (1 / ((n : ℝ) + 1)) * minorDens i φ z := by
  unfold maDens
  rw [hessC_cons, hessC_gReg hε, mdisc_cons_smul_single]
  have h1 : (1 / ((n : ℂ) + 1)) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  simp only [kDens, minorDens]
  ring
end ReciprocityTheory.AnForm.A
