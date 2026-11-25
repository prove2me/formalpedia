-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.height_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:42.493061+00:00
-- url     : https://prove2.me/submissions/9067ace6-8630-4c57-a380-62d7f3861f7a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_W_of
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_vanish
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_scalar
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_eval
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_prod_exact
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
import Theorems.Thm_PositivityTheory_Rg_Cz_tE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open HeightVanishing
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → Height := by
  intro _ n M _ _ E hE ℓ hW top htop
  obtain ⟨ψ, hψ1, hψ2, hψ⟩ := hW
  have hcast : ∀ {P : Type} [Fintype P] (I : P → Fin n),
      ((∑ p, ((top : ℕ) - I p) : ℕ) : ℤ) = H (fun _ => top) I := by
    intro P _ I
    simp only [H]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_sub (by omega)]
  refine ⟨fun P _ _ d g hg I => ⟨fun hd v => ?_, fun hd => ?_⟩, fun hl L hL => ?_, fun m => ?_⟩
  · obtain ⟨A, hA, hAv⟩ := eval E hg (fun _ => top) I
    rw [hAv, ← LinearMap.comp_apply, vanish E hE hψ2 hψ d _ A hA (by rw [← hcast]; exact_mod_cast hd)]
    rfl
  · obtain ⟨A, hA, hAv⟩ := eval E hg (fun _ => top) I
    obtain ⟨c, hc⟩ := scalar E hE hψ2 hψ d A (W_of E le_rfl (by rw [← hcast, hd]) hA)
    exact ⟨c, fun v => by rw [hAv, ← LinearMap.comp_apply, hc]; rfl⟩
  · have h0 : 0 < n := by omega
    obtain ⟨c, hc, hcv⟩ := prod_exact E hE hψ1 hψ2 hψ L ⟨0, h0⟩ top (by simp [hL])
    obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
      by_contra h; push_neg at h; exact hl (LinearMap.ext h)
    intro h
    have := LinearMap.congr_fun h (Pi.single (fun _ => ⟨0, h0⟩) v)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.zero_apply] at this
    rw [hcv] at this
    exact mul_ne_zero hc hv this
  · refine ⟨ψ, hψ1, hψ2, fun a b hab => ?_⟩
    have hab' := Fin.lt_def.1 hab
    have hta : top ≠ a := by
      intro h; subst h; have := b.2; omega
    ext f
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smul_apply]
    rw [tE_apply]
    simp only [hta, if_false, Finset.sum_const_zero, add_zero]
    rw [← LinearMap.comp_apply, hψ a b hab]
    rfl
end PositivityTheory.Rg.Cz
