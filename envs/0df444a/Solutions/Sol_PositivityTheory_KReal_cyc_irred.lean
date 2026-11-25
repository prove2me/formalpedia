-- Prove2me | solution 1 for PositivityTheory.KReal.cyc_irred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:46.272559+00:00
-- url     : https://prove2.me/submissions/3bd99e7a-4a0e-4691-ba17-c56e84bf0bce

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Theorems.Thm_PositivityTheory_KReal_words
import Theorems.Thm_PositivityTheory_KReal_sb_symm
import Theorems.Thm_PositivityTheory_KReal_sb_trans
import Theorems.Thm_PositivityTheory_KReal_sb_of_pos
import Theorems.Thm_PositivityTheory_KReal_sb_tri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] {ρ : Ix r s → Ix r s → Module.End ℂ A}
    (hadj : AdjK ρ) (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : A} (hf : HwK ρ μ f)
    (N : Submodule ℂ A) (hN : N ≤ cycK ρ f) (hK : KSt ρ N) : N = ⊥ ∨ N = cycK ρ f := by
  let S : Submodule ℂ (Module.End ℂ A) := Submodule.span ℂ {E | ∃ a b, sameBlock a b ∧ E = ρ a b}
  let L : Set (Module.End ℂ A) := {E | ∃ a b, posC a b ∧ E = ρ b a}
  have hmem : ∀ a b, sameBlock a b → ρ a b ∈ S := fun a b h => Submodule.subset_span ⟨a, b, h, rfl⟩
  have hS : ∀ E ∈ S, ∀ F ∈ S, E * F - F * E ∈ S := by
    intro E hE F hF
    induction hE using Submodule.span_induction with
    | mem E hE =>
      obtain ⟨a, b, hab, rfl⟩ := hE
      induction hF using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨c, d, hcd, rfl⟩ := hF
        rw [hρ a b c d hab hcd]
        refine S.sub_mem ?_ ?_
        · split_ifs with h
          · subst h; exact hmem _ _ (sb_trans hab hcd)
          · exact S.zero_mem
        · split_ifs with h
          · subst h; exact hmem _ _ (sb_trans hcd hab)
          · exact S.zero_mem
      | zero => simp
      | add F G _ _ h1 h2 =>
        have := S.add_mem h1 h2
        convert this using 1
        noncomm_ring
      | smul c F _ h1 =>
        have := S.smul_mem c h1
        convert this using 1
        simp [smul_sub]
    | zero => simp
    | add E G _ _ h1 h2 =>
      have := S.add_mem h1 h2
      convert this using 1
      noncomm_ring
    | smul c E _ h1 =>
      have := S.smul_mem c h1
      convert this using 1
      simp [smul_sub]
  have hL : L ⊆ S := by
    rintro _ ⟨a, b, hab, rfl⟩
    exact hmem _ _ (sb_symm (sb_of_pos hab))
  have hz : ∀ E ∈ S, ∃ F ∈ Submodule.span ℂ L, ∃ c : ℂ, E f = F f + c • f := by
    intro E hE
    induction hE using Submodule.span_induction with
    | mem E hE =>
      obtain ⟨a, b, hab, rfl⟩ := hE
      rcases sb_tri hab with h | h | h
      · subst h
        exact ⟨0, Submodule.zero_mem _, ((μ a : ℚ) : ℂ), by rw [hf.1 a]; simp⟩
      · exact ⟨0, Submodule.zero_mem _, 0, by rw [hf.2 a b h]; simp⟩
      · exact ⟨ρ a b, Submodule.subset_span ⟨b, a, h, rfl⟩, 0, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
    | add E G _ _ h1 h2 =>
      obtain ⟨F1, hF1, c1, e1⟩ := h1
      obtain ⟨F2, hF2, c2, e2⟩ := h2
      refine ⟨F1 + F2, Submodule.add_mem _ hF1 hF2, c1 + c2, ?_⟩
      simp only [LinearMap.add_apply, e1, e2, add_smul]
      abel
    | smul c E _ h1 =>
      obtain ⟨F1, hF1, c1, e1⟩ := h1
      refine ⟨c • F1, Submodule.smul_mem _ _ hF1, c * c1, ?_⟩
      simp only [LinearMap.smul_apply, e1, smul_add, smul_smul]
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ A, W = sInf {N | f ∈ N ∧ ∀ F ∈ L, ∀ x ∈ N, F x ∈ N} := ⟨_, rfl⟩
  obtain ⟨hfW, hSW, hWeq⟩ := words S hS L hL f hz W hW
  have hcW : cycK ρ f ≤ W := sInf_le ⟨hfW, fun a b hab x hx => hSW _ (hmem a b hab) x hx⟩
  have hKo : KSt ρ Nᗮ := by
    intro a b hab x hx
    rw [Submodule.mem_orthogonal'] at hx ⊢
    intro u hu
    rw [hadj a b hab]
    exact hx _ (hK b a (sb_symm hab) u hu)
  obtain ⟨y, hy, z, hz', hyz⟩ := Submodule.mem_sup.1
    (show f ∈ N ⊔ Nᗮ by rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; exact Submodule.mem_top)
  have hyk : ∀ a b, posC a b → ρ a b y = 0 := by
    intro a b hab
    have h1 : ρ a b y ∈ N := hK a b (sb_of_pos hab) y hy
    have h2 : ρ a b y ∈ Nᗮ := by
      have e : ρ a b y = - ρ a b z := by
        have := hf.2 a b hab
        rw [← hyz, map_add] at this
        exact eq_neg_of_add_eq_zero_left this
      rw [e]
      exact Nᗮ.neg_mem (hKo a b (sb_of_pos hab) z hz')
    exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 h2)
  have hw0 : ⟪f, f⟫_ℂ • y - ⟪f, y⟫_ℂ • f = 0 := by
    set w := ⟪f, f⟫_ℂ • y - ⟪f, y⟫_ℂ • f with hw
    have hwW : w ∈ W := W.sub_mem (W.smul_mem _ (hcW (hN hy))) (W.smul_mem _ hfW)
    have hle : W ≤ (Submodule.span ℂ {w})ᗮ := by
      rw [hWeq]
      refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 ?_) (iSup₂_le ?_)
      · rw [Submodule.mem_orthogonal_singleton_iff_inner_left, hw, inner_sub_right, inner_smul_right,
          inner_smul_right]
        ring
      · rintro _ ⟨a, b, hab, rfl⟩ _ ⟨x, _, rfl⟩
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left, hadj b a (sb_symm (sb_of_pos hab)), hw,
          map_sub, map_smul, map_smul, hyk a b hab, hf.2 a b hab]
        simp
    have := hle hwW
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    exact inner_self_eq_zero.1 this
  by_cases hfy : ⟪f, y⟫_ℂ = 0
  · left
    have hy0 : y = 0 := by
      rw [← hyz, inner_add_left, Submodule.inner_left_of_mem_orthogonal hy hz', add_zero] at hfy
      exact inner_self_eq_zero.1 hfy
    have hfo : f ∈ Nᗮ := by rw [← hyz, hy0, zero_add]; exact hz'
    have hle : cycK ρ f ≤ Nᗮ := sInf_le ⟨hfo, hKo⟩
    rw [eq_bot_iff]
    intro u hu
    exact (Submodule.mem_bot ℂ).2
      (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hu (hle (hN hu))))
  · right
    have hfN : f ∈ N := by
      have h1 : ⟪f, y⟫_ℂ • f ∈ N := by
        rw [← sub_eq_zero.1 hw0]
        exact N.smul_mem _ hy
      exact (N.smul_mem_iff hfy).1 h1
    exact le_antisymm hN (sInf_le ⟨hfN, hK⟩)
end PositivityTheory.KReal
