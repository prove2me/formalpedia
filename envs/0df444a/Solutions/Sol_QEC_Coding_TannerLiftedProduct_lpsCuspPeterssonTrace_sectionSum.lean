-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_sectionSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:04:37.256859+00:00
-- url     : https://prove2.me/submissions/83dcfb19-ba1b-4535-9445-f3f871f517aa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0SectionPetersson
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Domain_finiteIndex


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) :
    lpsCuspPeterssonTrace N f g τ =
      ∑' c, petersson 2 f g ((lpsGamma0CosetSection N c)⁻¹ • τ) := by
  let : (lpsEffectiveGamma0 N).FiniteIndex := lpsGamma0Domain_finiteIndex N
  let : Fintype (lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Subgroup.fintypeQuotientOfFiniteIndex
  simp_rw [lpsGamma0SectionPetersson,tsum_fintype]
  unfold lpsCuspPeterssonTrace
  apply Fintype.sum_equiv (lpsEffectiveGamma0CosetEquiv N)
  intro c
  rw [Equiv.symm_apply_apply]
end QEC.Coding.TannerLiftedProduct
