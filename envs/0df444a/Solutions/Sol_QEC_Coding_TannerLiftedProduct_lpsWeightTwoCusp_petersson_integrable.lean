-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_petersson_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:46.279394+00:00
-- url     : https://prove2.me/submissions/54ef8647-28ae-47fa-8cf2-eb3798c45794

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_fundamentalDomain_volume_finite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (petersson 2 f g) ModularGroup.fd := by
  obtain ⟨C,hC⟩ := CuspFormClass.petersson_bounded_left 2 _ f g
  have hi : IntegrableOn (fun _ : ℍ => C) ModularGroup.fd :=
    integrableOn_const (ne_of_lt lpsPetersson_fundamentalDomain_volume_finite)
  exact hi.mono' (petersson_continuous 2 (by fun_prop) (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall hC)
end QEC.Coding.TannerLiftedProduct
