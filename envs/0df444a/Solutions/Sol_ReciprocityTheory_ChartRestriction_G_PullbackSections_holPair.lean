-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:47.433336+00:00
-- url     : https://prove2.me/submissions/a291c696-070e-4bd0-a6d2-3dc237ccd6d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPair
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__fromSpec_9b2f586a8f0b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolTo_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolTo_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolTo_pullbackSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor
private theorem pt_lemma_2 (a b : PrimeSpectrum ℂ) : a = b := by
  have h : ∀ c : PrimeSpectrum ℂ, c.asIdeal = ⊥ := fun c =>
    (Ideal.eq_bot_or_top c.asIdeal).resolve_right c.2.ne_top
  exact PrimeSpectrum.ext (by rw [h a, h b])
private theorem top_le_lemma_3 {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (W : Y.Opens) (q : Sp ℂ)
    (h : x q ∈ W) : ⊤ ≤ x ⁻¹ᵁ W := by
  intro q' _
  have hq : q' = q := pt_lemma_2 q' q
  rw [hq]
  exact h
end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (n : ℕ) (B : Set (Fin n → ℂ))
    (e₁ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₂)) (he : ∀ b, e₁ b ≫ p₁ = e₂ b ≫ p₂) :
    IsOpen B → IsHolTo B e₁ → IsHolTo B e₂ → IsHolTo B (fun b => pullback.lift (e₁ b) (e₂ b) (he b)) := by
  classical
  intro _ h₁ h₂
  apply isHolTo_of_local
  intro U f b₀ hb₀ hU
  let q : Sp ℂ := IsLocalRing.closedPoint ℂ

  obtain ⟨W, hW, hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X))
    (show (e₁ b₀ ≫ p₁) q ∈ (⊤ : X.Opens) from trivial)
  have hxW₂ : (e₂ b₀ ≫ p₂) q ∈ W := by rw [← he b₀]; exact hxW
  rw [Scheme.Hom.comp_apply] at hxW hxW₂
  obtain ⟨W₁, hW₁, hx₁, hW₁le⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y₁))
    (show e₁ b₀ q ∈ p₁ ⁻¹ᵁ W from hxW)
  obtain ⟨W₂, hW₂, hx₂, hW₂le⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y₂))
    (show e₂ b₀ q ∈ p₂ ⁻¹ᵁ W from hxW₂)
  have hW' : IsAffineOpen W := hW
  have hW₁' : IsAffineOpen W₁ := hW₁
  have hW₂' : IsAffineOpen W₂ := hW₂
  let N : Set (Fin n → ℂ) := {b ∈ B | ⊤ ≤ e₁ b ⁻¹ᵁ W₁} ∩ {b ∈ B | ⊤ ≤ e₂ b ⁻¹ᵁ W₂}
  have hN : IsOpen N := (h₁ W₁ 0).1.inter (h₂ W₂ 0).1
  have hb₀N : b₀ ∈ N := ⟨⟨hb₀, top_le_lemma_3 _ _ q hx₁⟩, ⟨hb₀, top_le_lemma_3 _ _ q hx₂⟩⟩

  have hr₁ : ∀ b ∈ N, Set.range (e₁ b) ⊆ Set.range hW₁'.fromSpec := by
    intro b hb
    rw [hW₁'.range_fromSpec]
    rintro _ ⟨q', rfl⟩
    exact hb.1.2 (show q' ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hr₂ : ∀ b ∈ N, Set.range (e₂ b) ⊆ Set.range hW₂'.fromSpec := by
    intro b hb
    rw [hW₂'.range_fromSpec]
    rintro _ ⟨q', rfl⟩
    exact hb.2.2 (show q' ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  let l₁ : ∀ b ∈ N, Sp ℂ ⟶ Spec Γ(Y₁, W₁) := fun b hb => IsOpenImmersion.lift hW₁'.fromSpec (e₁ b) (hr₁ b hb)
  let l₂ : ∀ b ∈ N, Sp ℂ ⟶ Spec Γ(Y₂, W₂) := fun b hb => IsOpenImmersion.lift hW₂'.fromSpec (e₂ b) (hr₂ b hb)
  have hl₁ : ∀ b (hb : b ∈ N), l₁ b hb ≫ hW₁'.fromSpec = e₁ b := fun b hb => IsOpenImmersion.lift_fac _ _ _
  have hl₂ : ∀ b (hb : b ∈ N), l₂ b hb ≫ hW₂'.fromSpec = e₂ b := fun b hb => IsOpenImmersion.lift_fac _ _ _
  letI : Algebra Γ(X, W) Γ(Y₁, W₁) := (p₁.appLE W W₁ hW₁le).hom.toAlgebra
  letI : Algebra Γ(X, W) Γ(Y₂, W₂) := (p₂.appLE W W₂ hW₂le).hom.toAlgebra
  have c₁ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₁, W₁))) ≫ hW'.fromSpec = hW₁'.fromSpec ≫ p₁ :=
    IsAffineOpen.SpecMap_appLE_fromSpec p₁ hW' hW₁' hW₁le
  have c₂ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₂, W₂))) ≫ hW'.fromSpec = hW₂'.fromSpec ≫ p₂ :=
    IsAffineOpen.SpecMap_appLE_fromSpec p₂ hW' hW₂' hW₂le
  have hc : ∀ b (hb : b ∈ N), l₁ b hb ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₁, W₁))) =
      l₂ b hb ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₂, W₂))) := by
    intro b hb
    rw [← cancel_mono hW'.fromSpec, Category.assoc, Category.assoc, c₁, c₂, ← Category.assoc, ← Category.assoc, hl₁ b hb, hl₂ b hb, he]
  let φ := pullback.map _ _ p₁ p₂ hW₁'.fromSpec hW₂'.fromSpec hW'.fromSpec c₁ c₂
  let wN : ∀ b ∈ N, Sp ℂ ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₁, W₁))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₂, W₂)))) :=
    fun b hb => pullback.lift (l₁ b hb) (l₂ b hb) (hc b hb)
  let w := fun b => if hb : b ∈ N then wN b hb else wN b₀ hb₀N
  have hw : ∀ b (hb : b ∈ N), w b = wN b hb := fun b hb => dif_pos hb
  have hwφ : ∀ b ∈ N, w b ≫ φ = pullback.lift (e₁ b) (e₂ b) (he b) := by
    intro b hb
    rw [hw b hb]
    apply pullback.hom_ext
    · simp only [φ, wN, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
      exact hl₁ b hb
    · simp only [φ, wN, Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc]
      exact hl₂ b hb
  have hwhol : IsHolTo N w := by
    refine isHolTo_pullbackSpec hN w (fun a => ?_) (fun c => ?_)
    · refine ((h₁ W₁ a).2.mono (fun b hb => hb.1)).congr (fun b hb => ?_)
      have h := valAt'_fromSpec hW₁' (l₁ b hb) a
      rw [hl₁ b hb] at h
      rw [hw b hb]
      simp only [wN, pullback.lift_fst]
      exact h.symm
    · refine ((h₂ W₂ c).2.mono (fun b hb => hb.2)).congr (fun b hb => ?_)
      have h := valAt'_fromSpec hW₂' (l₂ b hb) c
      rw [hl₂ b hb] at h
      rw [hw b hb]
      simp only [wN, pullback.lift_snd]
      exact h.symm
  obtain ⟨ho, hdf⟩ := isHolTo_comp hwhol φ U f
  refine ⟨{b ∈ N | ⊤ ≤ (w b ≫ φ) ⁻¹ᵁ U}, ho.mem_nhds ⟨hb₀N, by show ⊤ ≤ (w b₀ ≫ φ) ⁻¹ᵁ U; rw [hwφ b₀ hb₀N]; exact hU⟩,
    fun b hb => ⟨hb.1.1.1, by rw [← hwφ b hb.1]; exact hb.2⟩, hdf.congr fun b hb => ?_⟩
  simp only [hwφ b hb.1]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
