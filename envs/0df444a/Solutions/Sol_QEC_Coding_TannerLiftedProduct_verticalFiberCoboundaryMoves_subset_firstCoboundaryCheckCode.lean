-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.verticalFiberCoboundaryMoves_subset_firstCoboundaryCheckCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:48:19.643076+00:00
-- url     : https://prove2.me/submissions/f462e268-b3a7-458b-a88f-14f04f4e9026

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (m : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hm : m ∈ verticalFiberCoboundaryMoves label h g') :
    m ∈ (chainComplex label h g').firstCoboundaryCheckCode.carrier := by
  classical
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
  exact ((chainComplex label h g').mem_firstCoboundaryCheckCode_iff _).2
    ⟨verticalFiberCochain p.1 p.2, rfl⟩
end QEC.Coding.TannerLiftedProduct
