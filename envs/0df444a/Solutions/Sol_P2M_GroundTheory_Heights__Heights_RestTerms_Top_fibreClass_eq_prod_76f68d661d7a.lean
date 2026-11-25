-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreClass_eq_prod_76f68d661d7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:48.201091+00:00
-- url     : https://prove2.me/submissions/8079bcda-8b96-4675-b3c0-857a09850438

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_yRoot_eq_blockEmb_3d7bdf650708
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_zRoot_eq_blockEmb_92857d617718
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_map_f1bef1dced82

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) :
    fibreClass f r a c = ∏ σ : Fin f, blockEmb f (r + a) σ (fib1 r a c) := by
  refine Finset.prod_congr rfl fun σ _ => ?_
  have h := vandermondeOf_map (blockEmb f (r + a) σ).toRingHom (yRoot 1 r a c 0)
  have h' := vandermondeOf_map (blockEmb f (r + a) σ).toRingHom (zRoot 1 r a c 0)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h h'
  rw [fib1, map_mul, h, h']
  simp only [← yRoot_eq_blockEmb, ← zRoot_eq_blockEmb]
end GroundTheory.Heights₂.Heights.RestTerms.Top
