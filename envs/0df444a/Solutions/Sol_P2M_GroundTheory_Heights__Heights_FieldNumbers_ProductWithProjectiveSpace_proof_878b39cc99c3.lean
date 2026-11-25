-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ProductWithProjectiveSpace_proof_878b39cc99c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:37.651013+00:00
-- url     : https://prove2.me/submissions/4bf47e2e-4204-4269-afeb-5e352538aac0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_prodFn_9c9c9edb0e49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_restrict_2aee757d54c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_eventually_none_ge_1e277cebb144
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_eventualValue_eq_f2e34bf02972
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_top_c3fbe0f74289
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_above_3565aa18c5f0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace ProductWithProjectiveSpace
theorem _root_.solution (h1 : MixedDiffConst.Statement.{u})
    (h2 : HilbAddBlock.Statement.{u}) : ProductWithProjectiveSpace.Statement.{u} := by
  intro F _ K _ _ ι _ P hP e N r m he hrm cs
  have hH : hilbFn (addBlockPrime N P) = prodFn (hilbFn P) (projSpaceHilb N) := by
    funext x
    exact h2 F K ι P N x
  unfold intNum
  rw [hH, mixedDiff_prodFn]
  have hlim := tendsto_restrict (K := K)
  rcases lt_trichotomy m N with hmN | hmN | hmN
  · rw [if_neg hmN.ne]
    apply eventualValue_eq
    have hz := (h1 F K ι P hP.multiHomog hP.relevant e he).2 r (by omega) cs
    filter_upwards [hlim.eventually hz] with x hx
    simp only [prodFn]
    rw [hx, zero_mul]
  · subst hmN
    rw [if_pos rfl]
    obtain rfl : r = e := by omega
    apply eventualValue_eq
    have hc := (h1 F K ι P hP.multiHomog hP.relevant r he).1 cs
    filter_upwards [hlim.eventually hc, eventually_none_ge (m : ℤ)] with x hx hn
    simp only [prodFn]
    rw [hx, iter_projSpaceHilb_top m _ hn, mul_one]
    rfl
  · rw [if_neg hmN.ne']
    apply eventualValue_eq
    filter_upwards [eventually_none_ge (m : ℤ)] with x hn
    simp only [prodFn]
    rw [iter_projSpaceHilb_above N m hmN _ hn, mul_zero]
end ProductWithProjectiveSpace
end GroundTheory.Heights₂.Heights.FieldNumbers
