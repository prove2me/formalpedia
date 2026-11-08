-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.semanticFamily_hasUniformLDPC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:20:45.212046+00:00
-- url     : https://prove2.me/submissions/d5419724-4bb2-406a-b5c0-a3dbe0b65ec1

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerFamily
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_semanticPresentation_boundedLocality


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {A F W R R' : Type u} {G : A → Type u}
variable [Field F] [Fintype F]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
variable [∀ a, Group (G a)] [∀ a, Fintype (G a)]
variable [∀ a, DecidableEq (G a)]
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_34
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_35
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a)) :
    QEC.QLDPC.HasUniformLDPC
      (semanticFamily label h h' hW hGroupCofinal) := by
  refine ⟨2 * (Fintype.card W + Fintype.card R + Fintype.card R') *
    Fintype.card F, ?_⟩
  intro a
  exact semanticPresentation_boundedLocality (label a) h h'
end QEC.Coding.TannerLiftedProduct
