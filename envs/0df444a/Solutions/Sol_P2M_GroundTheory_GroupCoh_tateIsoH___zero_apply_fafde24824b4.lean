-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateIsoH___zero_apply_fafde24824b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:43.802543+00:00
-- url     : https://prove2.me/submissions/2cfdca1f-1255-4466-b222-86d08f57c5c1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateDeltaZero
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_iCycles_tateCyclesMk
import Theorems.Thm_GroundTheory_GroupCoh_tateCyclesMk_iCycles
import Theorems.Thm_GroundTheory_GroupCoh_tate_d_iCycles_int
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
import Theorems.Thm_P2M_GroundTheory_GroupCoh_t__apply_6f30be77357f
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateIsoH_homology__5a6abb47e55d
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
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {X : ShortComplex (Rep.{u} k G)}
  (hX : X.ShortExact)
namespace GroundTheory.GroupCoh
theorem _root_.solution (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) (c : (tateComplex X.X₃).cycles 0)
    (hc : ((tateComplex X.X₃).iCycles 0).hom c = (cochainsIso₀ X.X₃).inv.hom z) :
    (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom
      ((TateCohomology.δ hX 0).hom (((tateComplex X.X₃).homologyπ 0).hom c)) =
      H1π X.X₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ := by
  have hxc : x ∈ cocycles₁ X.X₁ := mem_cocycles₁_of_comp_eq_d₀₁ hX hx
  let x₁ : (tateComplex X.X₁).X (0 + 1) := (cochainsIso₁ X.X₁).inv.hom x
  let x₂ : (tateComplex X.X₂).X 0 := (cochainsIso₀ X.X₂).inv.hom y
  have hd : ((tateComplex X.X₁).d (0 + 1) (0 + 1 + 1)).hom x₁ = 0 := by
    have e := congr(($(eq_d₁₂_comp_inv X.X₁)).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    have h0 : d₁₂ X.X₁ x = 0 := LinearMap.mem_ker.1 hxc
    rw [h0, map_zero] at e
    exact e
  have hx₂ : ((tateComplex.map X.g).f 0).hom x₂ = ((tateComplex X.X₃).iCycles 0).hom c := by
    rw [hc]
    funext v
    exact hy
  have hx₁ : ((tateComplex.map X.f).f (0 + 1)).hom x₁ = ((tateComplex X.X₂).d 0 (0 + 1)).hom x₂ := by
    have e := congr(($(eq_d₀₁_comp_inv X.X₂)).hom y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    refine Eq.trans ?_ e.symm
    funext v
    exact congrFun hx (v 0)
  have h1 := tδ_apply hX 0 (((tateComplex X.X₃).iCycles 0).hom c)
    (tate_d_iCycles_int _ 0 c) x₂ hx₂ x₁ hx₁ hd
  rw [tateCyclesMk_iCycles] at h1
  have h2 := tateIsoH_homologyπ X.X₁ 1 (tateCyclesMk X.X₁ (0 + 1) x₁ hd)
  refine (congrArg (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom h1).trans (h2.trans ?_)
  have h3 := cocyclesMk₁_eq X.X₁ ⟨x, hxc⟩
  refine Eq.trans ?_ (congrArg (π X.X₁ 1).hom h3)
  congr 1
  apply cocycles_ext
  exact (iCocycles_mk _ _).trans ((iCycles_tateCyclesMk _ _ _ _).trans (iCocycles_mk _ _).symm)
end GroundTheory.GroupCoh
