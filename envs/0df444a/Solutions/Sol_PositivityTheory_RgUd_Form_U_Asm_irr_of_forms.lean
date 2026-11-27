-- Prove2me | solution 1 for PositivityTheory.RgUd.Form.U.Asm.irr_of_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:25.983786+00:00
-- url     : https://prove2.me/submissions/1e7fd8a7-fb90-49d4-af76-1f23a9f28dd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_HermitianForms_UnitaryLattices_UnitaryHypotheses_ExistsOrthOfFinset
import Theorems.Thm_PositivityTheory_RgUd_Form_U_Asm_exists_orth_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd.Form.U.Asm
namespace PositivityTheory.RgUd.Form.U.Asm
theorem _root_.solution {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D] [Module ℂ D]
    [Nontrivial D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBh : ∀ x y, B y x = starRingEnd ℂ (B x y)) (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y)
    (hC : ∀ C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ, (∀ x y, C y x = starRingEnd ℂ (C x y)) → (∀ x, 0 ≤ (C x x).re) →
      (∀ x, (C x x).re ≤ (B x x).re) → (∀ g x y, C (ρ g x) (ρ g y) = (χ g : ℂ) * C x y) →
      ∃ c : ℂ, ∀ x y, C x y = c * B x y) :
    ρ.IsIrreducible := by
  classical
  have key : ∀ W : Subrepresentation ρ, W ≠ ⊥ → W = ⊤ := by
    intro W hWb
    let Wm : Submodule ℂ D := W.toSubmodule
    have hWs : ∀ g, ∀ w ∈ Wm, ρ g w ∈ Wm := fun g w hw => W.apply_mem_toSubmodule g hw
    let Wp : Submodule ℂ D :=
      { carrier := {x | ∀ w ∈ Wm, B x w = 0}
        add_mem' := by
          intro a b ha hb w hw
          rw [map_add, LinearMap.add_apply, ha w hw, hb w hw, add_zero]
        zero_mem' := by intro w _; simp
        smul_mem' := by
          intro c x hx w hw
          rw [map_smul, LinearMap.smul_apply, hx w hw, smul_zero] }
    have hWp : ∀ x, x ∈ Wp ↔ ∀ w ∈ Wm, B x w = 0 := fun x => Iff.rfl
    have hWps : ∀ g, ∀ x ∈ Wp, ρ g x ∈ Wp := by
      intro g x hx
      rw [hWp]
      intro w hw
      have h1 : ρ g (ρ g⁻¹ w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [← h1, hBe, (hWp x).1 hx _ (hWs _ _ hw), mul_zero]
    have hdec := fun u => exists_orth_decomp ρ hA K₁ hK₁o hK₁c χ B hBp hBe Wm hWs u
    have hcompl : IsCompl Wm Wp := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx hxp
        by_contra hne
        have := hBp x hne
        rw [(hWp x).1 hxp x hx] at this
        simp at this
      · rw [codisjoint_iff, eq_top_iff]
        intro u _
        obtain ⟨w, hw, hw'⟩ := hdec u
        rw [show u = w + (u - w) by abel]
        exact Submodule.add_mem_sup hw ((hWp _).2 hw')
    let P : D →ₗ[ℂ] D := Wm.projection Wp hcompl
    have hPW : ∀ x, P x ∈ Wm := fun x => Submodule.projection_apply_mem hcompl x
    have hPw : ∀ w ∈ Wm, P w = w := fun w hw => Submodule.projection_apply_of_mem_left hcompl hw
    have hPq : ∀ x, x - P x ∈ Wp := fun x => Submodule.sub_projection_mem hcompl x
    have hP0 : ∀ q ∈ Wp, P q = 0 := fun q hq => Submodule.projection_apply_of_mem_right hcompl hq
    have hPρ : ∀ g x, P (ρ g x) = ρ g (P x) := by
      intro g x
      have hx : ρ g x = ρ g (P x) + ρ g (x - P x) := by
        rw [← map_add]; congr 1; abel
      rw [hx, map_add, hPw _ (hWs g _ (hPW x)), hP0 _ (hWps g _ (hPq x)), add_zero]
    let C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ := (B ∘ₗ P).compl₂ P
    have hCapp : ∀ x y, C x y = B (P x) (P y) := fun x y => rfl
    have hBsplit : ∀ x, B x x = B (P x) (P x) + B (x - P x) (x - P x) := by
      intro x
      have h1 : B (x - P x) (P x) = 0 := (hWp _).1 (hPq x) _ (hPW x)
      have h2 : B (P x) (x - P x) = 0 := by rw [hBh (x - P x) (P x), h1, map_zero]
      conv_lhs => rw [show x = P x + (x - P x) by abel]
      simp only [map_add, LinearMap.add_apply, h1, h2, add_zero, zero_add]
    have hnn : ∀ x, 0 ≤ (B x x).re := by
      intro x
      by_cases h : x = 0
      · rw [h]; simp
      · exact (hBp _ h).le
    obtain ⟨c, hc⟩ := hC C (fun x y => by rw [hCapp, hCapp, hBh]) (fun x => by rw [hCapp]; exact hnn _)
      (fun x => by
        rw [hCapp, hBsplit x, Complex.add_re]
        have := hnn (x - P x)
        linarith)
      (fun g x y => by rw [hCapp, hCapp, hPρ, hPρ, hBe])
    obtain ⟨w0, hw0, hw0ne⟩ : ∃ w ∈ Wm, w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hWb
      apply Subrepresentation.toSubmodule_injective
      show Wm = ⊥
      exact (Submodule.eq_bot_iff _).2 hcon
    have hc1 : c = 1 := by
      have h := hc w0 w0
      rw [hCapp, hPw w0 hw0] at h
      have hB0 : B w0 w0 ≠ 0 := by
        intro h0; have := hBp w0 hw0ne; rw [h0] at this; simp at this
      have h2 : (c - 1) * B w0 w0 = 0 := by rw [sub_mul, ← h]; ring
      rcases mul_eq_zero.1 h2 with h1 | h1
      · exact sub_eq_zero.1 h1
      · exact absurd h1 hB0
    apply Subrepresentation.toSubmodule_injective
    show Wm = ⊤
    rw [eq_top_iff]
    intro x _
    have hq : x - P x = 0 := by
      by_contra hne
      have h := hc (x - P x) (x - P x)
      rw [hCapp, hc1, one_mul, hP0 _ (hPq x), map_zero] at h
      have := hBp _ hne
      rw [← h] at this
      simp at this
    have hx : x = P x := sub_eq_zero.1 hq
    rw [hx]
    exact hPW x
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : D)
    have h1 : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ D))
    rw [← h] at h1
    exact hx ((Submodule.mem_bot ℂ).1 (h1 : x ∈ (⊥ : Submodule ℂ D)))
  exact { exists_pair_ne := ⟨⊥, ⊤, hne⟩
          eq_bot_or_eq_top := fun W => by
            by_cases h : W = ⊥
            · exact Or.inl h
            · exact Or.inr (key W h) }
end PositivityTheory.RgUd.Form.U.Asm
