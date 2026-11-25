-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.gradDensLeibniz_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:25.869099+00:00
-- url     : https://prove2.me/submissions/47de1d1d-6a0b-493b-8e10-616e4c00274a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_dzb_cplx
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_add
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_fst
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_cplx_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_sq_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : GradDensLeibnizStatement := by
  intro n φ f g w z hf hg
  constructor
  · have hM : gradMat (fun y => f y * g y) w z =
        (f z : ℂ) • gradMat g w z + (g z : ℂ) • gradMat f w z := by
      ext j k
      simp only [gradMat, dz_cplx_mul j f g z hf hg, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
      ring
    unfold gradDens
    rw [hM, mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · have hM : gradMat g (fun y => g y ^ 2 / 2) z = (g z : ℂ) • gradMat g g z := by
      ext j k
      simp only [gradMat, Matrix.smul_apply, smul_eq_mul, dzb_cplx, fderiv_sq_half g z hg,
        FunLike.coe_smul, Pi.smul_apply]
      push_cast
      ring
    unfold gradDens
    rw [hM, mdisc_cons_smul_fst]
    simp only [Complex.re_ofReal_mul]
    ring
end ReciprocityTheory.AnForm.A
