-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:02.693786+00:00
-- url     : https://prove2.me/submissions/7912d5d7-a68b-4618-94ee-7f94922ce857

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_prodL_nat
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_xJ_nat
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_glrel_inj
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_ker_stable
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_comm_prod
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
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.SpecA
theorem _root_.solution {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Fin n → Fin n → Module.End ℂ V)
    (A : Module.End ℂ V) (hG : GlRel G) (hGA : ∀ a b, Commute A (G a b)) (l : Fin n → ℂ) (s : ℂ) (j : Fin k)
    (H : ∀ (W : Submodule ℂ V) (hW : ∀ a b, ∀ w ∈ W, G a b w ∈ W) (hA : ∀ w ∈ W, A w ∈ W) (c : Fin n)
      (N : Type) [AddCommGroup N] [Module ℂ N] (F : Fin n → Fin n → Module.End ℂ N) (q : W →ₗ[ℂ] N),
      GlRel F → Function.Surjective q → (∀ a b (w : W), q ⟨_, hW a b w w.2⟩ = F a b (q w)) →
      (∀ w : W, q ⟨_, hA w w.2⟩ = l c • q w) → Kl (xJ F j) s)
    (ks : List (Fin n)) : ∃ L : List ℕ, ∀ f : TV n V (Fin k),
      (∀ I, (ks.map fun c => A - algebraMap ℂ _ (l c)).prod (f I) = 0) →
      (L.map fun r : ℕ => xJ G j - algebraMap ℂ _ (s + r)).prod f = 0 := by
  induction ks with
  | nil =>
    refine ⟨[], fun f hf => ?_⟩
    have hf0 : f = 0 := funext fun I => by simpa using hf I
    simp [hf0]
  | cons c ks ih =>
    obtain ⟨L2, hL2⟩ := ih
    set Y : Module.End ℂ V := (ks.map fun c => A - algebraMap ℂ _ (l c)).prod with hYdef
    set Z : Module.End ℂ V := A - algebraMap ℂ _ (l c) with hZ
    have hZG : ∀ a b, Commute Z (G a b) := fun a b =>
      (hGA a b).sub_left (Algebra.commute_algebraMap_left _ _)
    have hZA : Commute Z A := (Commute.refl A).sub_left (Algebra.commute_algebraMap_left _ _)
    have hW : ∀ a b, ∀ w ∈ LinearMap.ker Z, G a b w ∈ LinearMap.ker Z :=
      fun a b => ker_stable Z (G a b) (hZG a b)
    have hWA : ∀ w ∈ LinearMap.ker Z, A w ∈ LinearMap.ker Z := ker_stable Z A hZA
    let F : Fin n → Fin n → Module.End ℂ (LinearMap.ker Z) := fun a b =>
      LinearMap.codRestrict (LinearMap.ker Z) ((G a b).comp (LinearMap.ker Z).subtype) (fun w => hW a b w w.2)
    have hsub : ∀ a b, (LinearMap.ker Z).subtype ∘ₗ F a b = G a b ∘ₗ (LinearMap.ker Z).subtype :=
      fun a b => LinearMap.ext fun w => rfl
    have hF : GlRel F := glrel_inj F G (LinearMap.ker Z).subtype (LinearMap.ker Z).injective_subtype hsub hG
    have hKl := H (LinearMap.ker Z) hW hWA c (LinearMap.ker Z) F LinearMap.id hF Function.surjective_id
      (fun a b w => rfl) (fun w => by
        apply Subtype.ext
        have hw : (A - algebraMap ℂ (Module.End ℂ V) (l c)) (w : V) = 0 := LinearMap.mem_ker.1 w.2
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at hw
        simpa using hw)
    obtain ⟨L1, hL1⟩ := hKl
    have hΦ := prodL_nat (LinearMap.compLeft (LinearMap.ker Z).subtype (Fin k → Fin n)) (xJ F j) (xJ G j)
      (xJ_nat F G (LinearMap.ker Z).subtype hsub j) (fun r : ℕ => s + (r : ℂ)) L1
    rw [hL1, LinearMap.comp_zero] at hΦ
    have hYG : ∀ a b, Y ∘ₗ G a b = G a b ∘ₗ Y := fun a b => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
      exact (comm_prod A (G a b) (hGA a b) l ks).eq
    have hΨ := prodL_nat (LinearMap.compLeft Y (Fin k → Fin n)) (xJ G j) (xJ G j) (xJ_nat G G Y hYG j)
      (fun r : ℕ => s + (r : ℂ)) L1
    refine ⟨L2 ++ L1, fun f hf => ?_⟩
    rw [List.map_append, List.prod_append, Module.End.mul_apply]
    apply hL2
    intro I
    have hf' : ∀ I, Y (f I) ∈ LinearMap.ker Z := fun I => by
      have hI := hf I
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply] at hI
      exact LinearMap.mem_ker.2 hI
    have h0 := LinearMap.congr_fun hΦ (fun I => (⟨Y (f I), hf' I⟩ : LinearMap.ker Z))
    have h1 := LinearMap.congr_fun hΨ f
    rw [LinearMap.comp_apply] at h0 h1
    rw [LinearMap.comp_apply] at h1
    have h2 : (LinearMap.compLeft (LinearMap.ker Z).subtype (Fin k → Fin n))
        (fun I => (⟨Y (f I), hf' I⟩ : LinearMap.ker Z)) = (LinearMap.compLeft Y (Fin k → Fin n)) f := rfl
    rw [h2, ← h1] at h0
    have h3 := congrFun h0.symm I
    simpa using h3
end PositivityTheory.Rg.Cz.SpecA
