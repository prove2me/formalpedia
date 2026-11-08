-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_aedisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:52:46.067295+00:00
-- url     : https://prove2.me/submissions/4837948f-5c45-4c8c-800e-7c38738e1c59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveCosets_countable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamentalDomain


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (h : H) (hh : h ≠ 1) :
    AEDisjoint volume (h • lpsCosetSectionDomain H r) (lpsCosetSectionDomain H r) := by
  letI : Countable (lpsEffectiveModularGroup ⧸ H) := lpsEffectiveCosets_countable H
  simp only [lpsCosetSectionDomain,smul_set_iUnion,AEDisjoint.iUnion_left_iff,AEDisjoint.iUnion_right_iff]
  intro d c
  change AEDisjoint volume ((h : lpsEffectiveModularGroup) •
    ((r c)⁻¹ • ModularGroup.fd)) ((r d)⁻¹ • ModularGroup.fd)
  rw [←mul_smul]
  apply lpsEffectiveFundamentalDomain.aedisjoint
  intro he
  have hm : (r d)⁻¹ * r c = (h : lpsEffectiveModularGroup) := by
    have := congrArg (fun x : lpsEffectiveModularGroup => x * r c) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using this.symm
  have hc : d = c := by
    rw [←hr d,←hr c,QuotientGroup.eq,hm]
    exact h.property
  subst c
  have hh' : (h : lpsEffectiveModularGroup) = 1 := by
    rw [hm.symm,inv_mul_cancel]
  exact hh (Subtype.ext hh')
end QEC.Coding.TannerLiftedProduct
