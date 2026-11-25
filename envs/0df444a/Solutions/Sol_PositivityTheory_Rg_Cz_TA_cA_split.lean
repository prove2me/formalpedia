-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.cA_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:55.925954+00:00
-- url     : https://prove2.me/submissions/b66d28b0-ab55-4227-916b-2a7820473eaf

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_spl_apply
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


section
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]
private theorem subtypePerm_subtypeCongr_eq {q : P → Prop} [DecidablePred q] (σ : Equiv.Perm P)
    (h0 : ∀ x, q (σ x) ↔ q x) (h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x) :
    (σ.subtypePerm h0).subtypeCongr (σ.subtypePerm (p := fun x => ¬ q x) h1) = σ := by
  ext x
  by_cases hx : q x
  · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
    rfl
  · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
    rfl
end PositivityTheory.Rg.Cz.TA
end
end

set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution {C : Type} [DecidableEq C] (col : P → C) (hq : ∀ p p', col p = col p' → (q p ↔ q p'))
    (b : P → Fin n) (F : TV n M P) :
    cA col b F = cA (fun x : {p // ¬ q p} => col x.1) (fun x => b x.1)
      (cA (fun x : {p // q p} => col x.1) (fun x => b x.1) (spl q F)) := by
  simp only [cA, alt, colG, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, map_sum, map_smul, pm, LinearMap.pi_apply]
  simp_rw [Finset.smul_sum, smul_smul, spl_apply]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun τ _ => τ.1.subtypeCongr τ.2) ?_ ?_ ?_ ?_
  · rintro ⟨σ0, σ1⟩ hτ
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    intro x
    by_cases hx : q x
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      exact hτ.1 ⟨x, hx⟩
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
      exact hτ.2 ⟨x, hx⟩
  · rintro ⟨σ0, σ1⟩ _ ⟨σ0', σ1'⟩ _ he
    simp only at he
    have e0 : σ0 = σ0' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.left_apply _ _ x.2] at this
      exact this
    have e1 : σ1 = σ1' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.right_apply _ _ x.2] at this
      exact this
    rw [e0, e1]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have h0 : ∀ x, q (σ x) ↔ q x := fun x => hq _ _ (hσ x)
    have h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x := fun x => not_congr (h0 x)
    refine ⟨(σ.subtypePerm h0, σ.subtypePerm (p := fun x => ¬ q x) h1), ?_, subtypePerm_subtypeCongr_eq σ h0 h1⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun x => hσ x.1, fun x => hσ x.1⟩
  · rintro ⟨σ0, σ1⟩ _
    simp only
    rw [Equiv.Perm.sign_subtypeCongr]
    congr 1
    · push_cast
      ring
    · congr 1
      funext x
      by_cases hx : q x
      · simp [merge, hx, Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      · simp [merge, hx, Equiv.Perm.subtypeCongr.right_apply _ _ hx]
end PositivityTheory.Rg.Cz.TA
