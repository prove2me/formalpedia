-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_t__comp_tateIsoH_ed31795245a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:45:13.9798+00:00
-- url     : https://prove2.me/submissions/735f4364-b67e-46b2-a450-ac2a7cdfefba

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateIsoH_homology__5a6abb47e55d
import Theorems.Thm_GroundTheory_GroupCoh_iCycles_tateCyclesMk
import Theorems.Thm_GroundTheory_GroupCoh_tateCyclesMk_iCycles
import Theorems.Thm_GroundTheory_GroupCoh_tate_d_iCycles_int
import Theorems.Thm_P2M_GroundTheory_GroupCoh_t__apply_6f30be77357f
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_exists_lift_of_cocycle
import Theorems.Thm_P2M_GroundTheory_GroupCoh_____eq_9cd1eeda1d2f
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
theorem _root_.solution {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (n : ℕ) [NeZero n] :
    tδ hS n (n + 1) rfl ≫ (tateIsoH S.X₁ (n + 1) (n + 1) (Nat.cast_succ n).symm).hom =
      (tateIsoH S.X₃ n n rfl).hom ≫ δ hS n (n + 1) rfl := by
  apply (cancel_epi ((tateComplex S.X₃).homologyπ n)).1
  ext z
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hz := tate_d_iCycles_int _ _ z
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hS
    (cocyclesMk (((tateComplex S.X₃).iCycles n).hom z) (tate_d_iCycles _ n z))
  have hd : ((tateComplex S.X₁).d (↑n + 1) (↑n + 1 + 1)).hom (iCocycles S.X₁ (n + 1) x) = 0 := by
    have := d_iCocycles x
    rw [← inhomogeneousCochains.d_def] at this
    exact this
  have hy' : ((tateComplex.map S.g).f n).hom y = ((tateComplex S.X₃).iCycles n).hom z :=
    funext fun v => (hy v).trans (congrFun (iCocycles_mk _ _) v)
  have hx' : ((tateComplex.map S.f).f (↑n + 1)).hom (iCocycles S.X₁ (n + 1) x) =
      ((tateComplex S.X₂).d n (n + 1)).hom y := by
    rw [tateComplex_d_ofNat, inhomogeneousCochains.d_def]
    exact funext hx
  have h1 := tateIsoH_homologyπ S.X₃ n z
  have h2 := δ_π_eq hS _ y hy x hx
  have h3 : (tδ hS n (n + 1) rfl).hom (((tateComplex S.X₃).homologyπ n).hom z) =
      ((tateComplex S.X₁).homologyπ (n + 1)).hom (tateCyclesMk S.X₁ (n + 1) (iCocycles S.X₁ (n + 1) x) hd) := by
    have e := tδ_apply hS n _ hz y hy' (iCocycles S.X₁ (n + 1) x) hx' hd
    rw [tateCyclesMk_iCycles] at e
    exact e
  have h4 := tateIsoH_homologyπ S.X₁ (n + 1) (tateCyclesMk S.X₁ (n + 1) (iCocycles S.X₁ (n + 1) x) hd)
  refine ((congrArg (fun w => (tateIsoH S.X₁ (↑n + 1) (n + 1) (Nat.cast_succ n).symm).hom.hom w)
    h3).trans ?_).trans (congrArg (fun w => (δ hS n (n + 1) rfl).hom w) h1).symm
  refine (h4.trans ?_).trans h2.symm
  congr 1
  apply cocycles_ext
  exact (iCocycles_mk _ _).trans (iCycles_tateCyclesMk _ _ _ _)
end GroundTheory.GroupCoh
