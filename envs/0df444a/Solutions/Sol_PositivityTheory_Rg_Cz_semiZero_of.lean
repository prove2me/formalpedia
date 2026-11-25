-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.semiZero_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:44:05.718636+00:00
-- url     : https://prove2.me/submissions/74bc7608-74c8-4254-ad00-67780f25cf8f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSemiZero
import Theorems.Thm_PositivityTheory_Rg_Cz_SemiInvariantDeterminant_det_bar
import Theorems.Thm_PositivityTheory_Rg_Cz_SemiInvariantDeterminant_det_mul_star
import Theorems.Thm_PositivityTheory_Rg_Cz_actT_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
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
open SemiInvariantDeterminant
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (hQ : QdetFacts) (_hW : WallAlg) (hL : LieInv) (hWQ : WallQuot) : SemiZero := by
  intro n hn M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG s φ hφ hS
  obtain ⟨lab, c, ξ, -, hact, I, w, hw, hwξ⟩ := hS
  have hρ : ∀ γ, ρ γ (ξ I) = (∏ τ, (κ τ γ).det ^ c τ) • ξ I := by
    intro γ
    have h := congrFun (hact γ) I
    rw [actT_apply, Pi.smul_apply] at h
    rw [← h, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    rw [Subsingleton.elim (default : Fin 0 → Fin n) I]
  obtain ⟨N, F, hFgl, -, hFch, hFE, hN⟩ := hWQ n M ι E hG.gl hG.comm (fun _ _ => s) φ (by
    intro τ u
    rw [hφ τ u, Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  have hξN : N.mkQ (ξ I) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN]
    push Not
    exact ⟨w, hw, hwξ⟩
  have htr : ∀ τ', N.mkQ ((∑ a, E τ' a a) (ξ I)) = (∑ a, F τ' a a) (N.mkQ (ξ I)) := by
    intro τ'
    simp only [LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hFE τ' a a) (ξ I)
  have hc : ∀ τ, c τ = c (bar τ) := by
    intro τ
    have hl := hL n M ι Γ bar κ E ρ hK hG c (ξ I) hρ τ
    have h1 : N.mkQ ((∑ a, E τ a a) (ξ I)) = N.mkQ ((∑ a, E (bar τ) a a) (ξ I)) := by
      rw [htr, htr, (hQ n (M ⧸ N) (F τ) (hFgl τ)).2.2.1 _ (hFch τ),
        (hQ n (M ⧸ N) (F (bar τ)) (hFgl (bar τ))).2.2.1 _ (hFch (bar τ))]
    have h2 : (∑ a, E τ a a) (ξ I) - (∑ a, E (bar τ) a a) (ξ I) =
        ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • ξ I := by
      rw [LinearMap.sum_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
      simp only [hl, if_true]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have h3 : ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • N.mkQ (ξ I) = 0 := by
      rw [← map_smul, ← h2, map_sub, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (Nat.cast_eq_zero.mp h) (by omega)
      · exact sub_eq_zero.mp (Int.cast_eq_zero.mp h)
    · exact absurd h hξN
  have hχ : ∀ γ, (∏ τ, (κ τ γ).det ^ c τ) = 1 := by
    intro γ
    refine Finset.prod_involution (fun τ _ => bar τ) ?_ ?_ (fun _ _ => Finset.mem_univ _)
      (fun τ _ => hK.invol τ)
    · intro τ _
      rw [det_bar hK, ← hc τ, ← mul_zpow, det_mul_star hK, _root_.one_zpow]
    · intro τ _ _
      exact hK.ne τ
  exact ⟨ξ I, fun γ => by rw [hρ, hχ, one_smul], w, hw, hwξ⟩
end PositivityTheory.Rg.Cz
