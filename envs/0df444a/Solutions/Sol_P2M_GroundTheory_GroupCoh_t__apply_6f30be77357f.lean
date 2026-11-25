-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_t__apply_6f30be77357f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:55.655031+00:00
-- url     : https://prove2.me/submissions/8320b153-34c5-49a9-88df-0bb56d9469aa

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.GroupCoh
theorem _root_.solution {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (i : ℤ)
    (x₃ : (tateComplex S.X₃).X i) (hx₃ : ((tateComplex S.X₃).d i (i + 1)).hom x₃ = 0)
    (x₂ : (tateComplex S.X₂).X i) (hx₂ : ((tateComplex.map S.g).f i).hom x₂ = x₃)
    (x₁ : (tateComplex S.X₁).X (i + 1))
    (hx₁ : ((tateComplex.map S.f).f (i + 1)).hom x₁ = ((tateComplex S.X₂).d i (i + 1)).hom x₂)
    (hd : ((tateComplex S.X₁).d (i + 1) (i + 1 + 1)).hom x₁ = 0) :
    (tδ hS i (i + 1) rfl).hom (((tateComplex S.X₃).homologyπ i).hom (tateCyclesMk _ i x₃ hx₃)) =
      ((tateComplex S.X₁).homologyπ (i + 1)).hom (tateCyclesMk _ (i + 1) x₁ hd) :=
  (TateCohomology.map_tateComplexFunctor_shortExact hS).δ_apply i (i + 1) rfl x₃ hx₃ x₂ hx₂ x₁ hx₁
    (i + 1 + 1) (by simp)
end GroundTheory.GroupCoh
