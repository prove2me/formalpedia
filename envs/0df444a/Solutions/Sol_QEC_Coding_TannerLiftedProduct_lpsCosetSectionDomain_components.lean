-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:52:24.438166+00:00
-- url     : https://prove2.me/submissions/6870b345-ea00-4afb-a535-a5058964f447

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamentalDomain


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) :
    Pairwise (fun c d => AEDisjoint volume ((r c)⁻¹ • ModularGroup.fd)
      ((r d)⁻¹ • ModularGroup.fd)) := by
  intro c d hcd
  apply lpsEffectiveFundamentalDomain.aedisjoint
  intro he
  apply hcd
  have he' : r c = r d := inv_injective he
  exact (hr c).symm.trans ((congrArg (QuotientGroup.mk : lpsEffectiveModularGroup →
    lpsEffectiveModularGroup ⧸ H) he').trans (hr d))
end QEC.Coding.TannerLiftedProduct
