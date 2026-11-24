-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:45.443392+00:00
-- url     : https://prove2.me/submissions/2af1071b-c05a-456c-847f-3781110421dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}
variable {β : Type*} [DecidableEq β]
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution (b : Module.Basis β K L) (T : Ideal (MvPolynomial Y K))
    {p : MvPolynomial Y L} (hp : p ∈ T.map (map (algebraMap K L))) (c : β) :
    coordPoly (b.coord c) p ∈ T := by
  have hp' : p ∈ Submodule.span (MvPolynomial Y L) ((map (algebraMap K L)) '' T) := hp
  clear hp
  revert c
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    intro c
    have e := coordPoly_C_mul_map (b.coord c) (1 : L) t
    rw [C_1, one_mul] at e
    rw [e]
    exact T.mul_mem_left _ ht
  | zero => intro c; rw [map_zero]; exact T.zero_mem
  | add x y _ _ hx hy => intro c; rw [map_add]; exact T.add_mem (hx c) (hy c)
  | smul r x _ hx =>
    intro c
    have e : r * x = ∑ c₁ ∈ coordSupport b r, ∑ c₂ ∈ coordSupport b x,
        C (b c₁ * b c₂) * map (algebraMap K L) (coordPoly (b.coord c₁) r * coordPoly (b.coord c₂) x) := by
      conv_lhs => rw [← sum_coordPoly b r, ← sum_coordPoly b x]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      rw [C_mul, map_mul]
      ring
    rw [smul_eq_mul, e, map_sum]
    refine T.sum_mem fun c₁ _ => ?_
    rw [map_sum]
    refine T.sum_mem fun c₂ _ => ?_
    rw [coordPoly_C_mul_map]
    exact T.mul_mem_left _ (T.mul_mem_left _ (hx c₂))
end GroundTheory.Heights₂.Heights.ChowFormExtend
