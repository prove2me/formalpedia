-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessCDz_thm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:20.013271+00:00
-- url     : https://prove2.me/submissions/1a58b4a4-1eb5-41b9-bb7e-5bc18c7578ee

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_dzb_cplx
import Theorems.Thm_ReciprocityTheory_AnForm_hessC_eq_leviC


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
theorem _root_.solution : HessCDzStatement := by
  intro D v U hU hv z hz j k
  have h2 : ContDiffAt ℝ 2 v z := hv.contDiffAt (hU.mem_nhds hz)
  have hL : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hc := fun c : Fin D → ℂ =>
    Complex.ofRealCLM.hasFDerivAt.comp z (hL.hasFDerivAt.clm_apply (hasFDerivAt_const c z))
  have hg := ((hc (Pi.single k 1)).add
    ((hc (Complex.I • Pi.single k 1)).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hd := hg.congr_of_eventuallyEq (f₁ := dzb k (cplx v))
    (Filter.Eventually.of_forall fun y => by
      rw [dzb_cplx]
      simp only [Pi.add_apply, Function.comp_apply, Complex.ofRealCLM_apply]
      ring)
  rw [dz, hd.fderiv]
  simp only [hessC_eq_leviC, leviC]
  simp
  apply Complex.ext <;> simp <;> ring
end ReciprocityTheory.AnForm.A
