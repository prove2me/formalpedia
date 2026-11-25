-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.monge_ampere_density_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:40.137018+00:00
-- url     : https://prove2.me/submissions/af162285-3ce0-4fd4-ab21-62af4fe21bdd

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_congr
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDisc_cons_eq_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : MaDensCofStatement := by
  intro n φ v U hU hv z hz
  have hs : ∀ j k : Fin (n + 1), hessC v z j k = dz j (dzb k (cplx v)) z := by
    intro j k
    have hv2 : ContDiffAt ℝ 2 v z := hv.contDiffAt (hU.mem_nhds hz)
    have hDv : DifferentiableAt ℝ (fderiv ℝ v) z :=
      (hv2.fderiv_right (m := 1) (by first | norm_num | simp | rfl)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)
    have hw : ∀ w : Fin (n + 1) → ℂ, HasFDerivAt (fun y => ((fderiv ℝ v y w : ℝ) : ℂ))
        (Complex.ofRealCLM.comp
          ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ v) z))) z :=
      fun w => Complex.ofRealCLM.hasFDerivAt.comp z
        ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp z hDv.hasFDerivAt)
    have hg : HasFDerivAt (fun y => (1 / 2 : ℂ) * (((fderiv ℝ v y (Pi.single k 1) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ v y (Complex.I • Pi.single k 1) : ℝ) : ℂ)))
        ((1 / 2 : ℂ) • (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ (Pi.single k 1)).comp
            (fderiv ℝ (fderiv ℝ v) z)) +
          Complex.I • Complex.ofRealCLM.comp
            ((ContinuousLinearMap.apply ℝ ℝ (Complex.I • Pi.single k 1)).comp
              (fderiv ℝ (fderiv ℝ v) z)))) z := by
      first
        | (exact ((hw _).add ((hw _).const_mul Complex.I)).const_mul (1 / 2 : ℂ))
        | (exact ((hw _).fun_add ((hw _).const_mul Complex.I)).const_mul (1 / 2 : ℂ))
        | (exact ((hw _).add ((hw _).fun_const_mul Complex.I)).fun_const_mul (1 / 2 : ℂ))
        | (exact ((hw _).fun_add ((hw _).fun_const_mul Complex.I)).fun_const_mul (1 / 2 : ℂ))
    have heq : dzb k (cplx v) =ᶠ[𝓝 z] fun y => (1 / 2 : ℂ) *
        (((fderiv ℝ v y (Pi.single k 1) : ℝ) : ℂ) +
          Complex.I * ((fderiv ℝ v y (Complex.I • Pi.single k 1) : ℝ) : ℂ)) := by
      filter_upwards [hU.mem_nhds hz] with y hy
      have hdy : DifferentiableAt ℝ v y :=
        (hv.contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)
      have hf : fderiv ℝ (cplx v) y = Complex.ofRealCLM.comp (fderiv ℝ v y) :=
        (Complex.ofRealCLM.hasFDerivAt.comp y hdy.hasFDerivAt).fderiv
      unfold dzb
      rw [hf]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Complex.ofRealCLM_apply]
      ring
    rw [dz_congr heq]
    unfold dz
    rw [hg.fderiv]
    simp only [hessC, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    push_cast
    linear_combination ((fderiv ℝ (fderiv ℝ v) z (Complex.I • Pi.single j 1)
      (Complex.I • Pi.single k 1) : ℝ) : ℂ) / 4 * Complex.I_sq
  rw [maDens_cons_eq, mixedDisc_cons_eq_sum]
  have hsum : (∑ j, ∑ k, hessC v z j k * mixedCof (fun i => hessC (φ i) z) j k) =
      ∑ j, ∑ k, hessCof φ z j k * dz j (dzb k (cplx v)) z := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hs j k]
    simp only [hessCof]
    ring
  rw [hsum]
end ReciprocityTheory.AnForm.A
