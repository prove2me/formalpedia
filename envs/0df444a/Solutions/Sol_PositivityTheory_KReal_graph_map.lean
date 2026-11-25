-- Prove2me | solution 1 for PositivityTheory.KReal.graph_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:39.952922+00:00
-- url     : https://prove2.me/submissions/5a932cf0-a4e2-4a86-8a14-4e50deec109c

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Theorems.Thm_PositivityTheory_KReal_graph_orth_stable
import Theorems.Thm_PositivityTheory_KReal_prodAct_apply
import Theorems.Thm_PositivityTheory_KReal_graph_sub

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
namespace PositivityTheory.KReal
theorem _root_.solution {p q : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B)
    (hA : IsLie ρA) (hB : IsLie ρB) (aA : AdjG ρA) (aB : AdjG ρB) (lam : Ix p q → ℂ) (x : A) (y : B)
    (hx0 : x ≠ 0)
    (hxK : ∀ a b, sameBlock a b → ρA (Eab a b) x = (if a = b then lam a else 0) • x)
    (hyK : ∀ a b, sameBlock a b → ρB (Eab a b) y = (if a = b then lam a else 0) • y)
    (hxP : ∀ i j, ρA (Eab (.inr j) (.inl i)) x = 0) (hyP : ∀ i j, ρB (Eab (.inr j) (.inl i)) y = 0)
    (hproj : genG ρA (Submodule.span ℂ {x}) ⊔ (genG ρA (Submodule.span ℂ {x}))ᗮ = ⊤) :
    ∃ Φ : A →ₗ[ℂ] B, (∀ Z u, Φ (ρA Z u) = ρB Z (Φ u)) ∧ Φ x = y := by
  classical
  obtain ⟨N, hxyN, hNinv, hN0⟩ := graph_sub ρA ρB hA hB aA aB lam x y hx0 hxK hyK hxP hyP
  have hg : ∀ (z : A × B), z ∈ N → z.1 = 0 → z.2 = 0 := by
    rintro ⟨a, b⟩ hz h0
    simp only at h0 ⊢
    subst h0
    exact hN0 b hz
  have huniq : ∀ (u : A) (b b' : B), (u, b) ∈ N → (u, b') ∈ N → b = b' := by
    intro u b b' h h'
    have hd : ((0 : A), b - b') ∈ N := by
      have h2 := N.sub_mem h h'
      simpa using h2
    exact sub_eq_zero.1 (hN0 _ hd)
  have hGinv : ∀ W, ∀ u ∈ genG ρA (Submodule.span ℂ {x}), ρA W u ∈ genG ρA (Submodule.span ℂ {x}) := by
    intro W u hu
    exact Submodule.mem_sInf.2 fun M hM => hM.2 W u (Submodule.mem_sInf.1 hu M hM)
  have hxG : x ∈ genG ρA (Submodule.span ℂ {x}) :=
    Submodule.mem_sInf.2 fun M hM => hM.1 (Submodule.mem_span_singleton_self x)
  have hGdom : genG ρA (Submodule.span ℂ {x}) ≤ N.map (LinearMap.fst ℂ A B) := by
    refine sInf_le (show N.map (LinearMap.fst ℂ A B) ∈ {M : Submodule ℂ A | Submodule.span ℂ {x} ≤ M ∧ ∀ W, ∀ u ∈ M, ρA W u ∈ M} from ⟨?_, ?_⟩)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨(x, y), hxyN, rfl⟩
    · rintro W u ⟨n, hn, rfl⟩
      refine ⟨prodAct ρA ρB W n, hNinv W n hn, ?_⟩
      simp [prodAct_apply]
  set G := genG ρA (Submodule.span ℂ {x}) with hGdef
  have hcompl : IsCompl G Gᗮ := ⟨Submodule.orthogonal_disjoint G, codisjoint_iff.2 hproj⟩
  let Φ : A →ₗ[ℂ] B := N.toLinearPMap.toFun ∘ₗ Submodule.inclusion hGdom ∘ₗ Submodule.linearProjOfIsCompl G Gᗮ hcompl
  have hΦG : ∀ u (hu : u ∈ G), (u, Φ u) ∈ N := by
    intro u hu
    have h := Submodule.mem_graph_toLinearPMap hg (Submodule.inclusion hGdom ⟨u, hu⟩)
    have hp : Submodule.linearProjOfIsCompl G Gᗮ hcompl u = ⟨u, hu⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hcompl ⟨u, hu⟩
    simp only [Φ, LinearMap.comp_apply, hp]
    exact h
  have hΦO : ∀ u ∈ Gᗮ, Φ u = 0 := by
    intro u hu
    have hp : Submodule.linearProjOfIsCompl G Gᗮ hcompl u = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hcompl ⟨u, hu⟩
    simp only [Φ, LinearMap.comp_apply, hp, map_zero]
  have hOinv := graph_orth_stable ρA aA G hGinv
  refine ⟨Φ, ?_, ?_⟩
  · intro Z u
    have hu : u ∈ G ⊔ Gᗮ := by
      rw [hproj]
      trivial
    obtain ⟨g, hgG, g', hgO, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add, map_add, map_add, hΦO g' hgO, hΦO _ (hOinv Z g' hgO), add_zero, add_zero]
    refine huniq (ρA Z g) _ _ (hΦG _ (hGinv Z g hgG)) ?_
    have h3 := hNinv Z _ (hΦG g hgG)
    rwa [prodAct_apply] at h3
  · exact huniq x _ _ (hΦG x hxG) hxyN
end PositivityTheory.KReal
