-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_aedisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:04:52.882004+00:00
-- url     : https://prove2.me/submissions/1a96ffc2-c157-43af-90e8-4566379f3cc9

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open MeasureTheory Set Filter
open scoped Pointwise ENNReal
noncomputable section
variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_countableQuotient
omit [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) (h : H) (hh : h ≠ 1) :
    AEDisjoint μ (h • lpsRelativeDomain H s r) (lpsRelativeDomain H s r) := by
  simp only [lpsRelativeDomain,smul_set_iUnion,AEDisjoint.iUnion_left_iff,AEDisjoint.iUnion_right_iff]
  intro d c
  change AEDisjoint μ ((h : G) •
    ((r c)⁻¹ • s)) ((r d)⁻¹ • s)
  rw [←mul_smul]
  apply hs.aedisjoint
  intro he
  have hm : (r d)⁻¹ * r c = (h : G) := by
    have := congrArg (fun x : G => x * r c) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using this.symm
  have hc : d = c := by
    rw [←hr d,←hr c,QuotientGroup.eq,hm]
    exact h.property
  subst c
  have hh' : (h : G) = 1 := by
    rw [hm.symm,inv_mul_cancel]
  exact hh (Subtype.ext hh')
end QEC.Coding.TannerLiftedProduct
