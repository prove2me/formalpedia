-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_comap_of_cartAt_d19af1b79604
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:00:16.842435+00:00
-- url     : https://prove2.me/submissions/b55cedaa-467b-48f6-8473-d3dedbd8bfd8

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierRestrictIffCartierAt
import Theorems.Thm_ReciprocityTheory_AnForm_R_algebraMap_mem_nonZeroDivisors_of_isLocalization
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringEquiv_mem_nonZeroDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
private theorem res_res_lemma {Y : Scheme.{0}} {A B : Y.Opens} (h1 : A ≤ B) (h2 : B ≤ A)
    (y : Γ(Y, A)) :
    (Y.presheaf.map (homOfLE h1).op).hom ((Y.presheaf.map (homOfLE h2).op).hom y) = y := by
  have e : (homOfLE h1 ≫ homOfLE h2 : A ⟶ A) = 𝟙 A := Subsingleton.elim _ _
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CategoryTheory.Functor.map_comp, ← op_comp, e, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution {X Y : Scheme.{0}} (J : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) (h : CartAt J (f x)) : CartAt (J.comap f) x := by
  obtain ⟨V, g, hfx, hg, hJ⟩ := h
  have hV : IsAffineOpen V.1 := V.2
  obtain ⟨h0, hle, hx0⟩ := hV.exists_basicOpen_le (V := f.opensRange) ⟨f x, x, rfl⟩ hfx
  have hU : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen h0) :=
    (hV.basicOpen h0).preimage_of_isOpenImmersion f hle
  have hW : IsAffineOpen (f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0) := hU.image_of_isOpenImmersion f
  have heq : f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0 = Y.basicOpen h0 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hle]
  have hWD : f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0 ≤ Y.basicOpen h0 := heq.le
  have hDW : Y.basicOpen h0 ≤ f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0 := heq.ge
  let r : Γ(Y, Y.basicOpen h0) := (Y.presheaf.map (homOfLE (Y.basicOpen_le h0)).op).hom g
  have hJD : J.ideal (Y.affineBasicOpen h0) = Ideal.span {r} := by
    rw [← J.map_ideal_basicOpen V h0, hJ, Ideal.map_span, Set.image_singleton]
  have hr : r ∈ nonZeroDivisors Γ(Y, Y.basicOpen h0) := by
    haveI := hV.isLocalization_basicOpen h0
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers h0) hg
  let s : Γ(Y, Y.basicOpen h0) →+* Γ(Y, f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0) :=
    (Y.presheaf.map (homOfLE hWD).op).hom
  let s' : Γ(Y, f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0) →+* Γ(Y, Y.basicOpen h0) :=
    (Y.presheaf.map (homOfLE hDW).op).hom
  have ss' : ∀ y, s (s' y) = y := fun y => res_res_lemma hWD hDW y
  have s's : ∀ y, s' (s y) = y := fun y => res_res_lemma hDW hWD y
  let σ : Γ(Y, Y.basicOpen h0) ≃+* Γ(Y, f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0) :=
    RingEquiv.ofRingHom s s' (RingHom.ext fun y => ss' y) (RingHom.ext fun y => s's y)
  have hJW : J.ideal ⟨f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0, hW⟩ = Ideal.span {σ r} := by
    apply le_antisymm
    · intro y hy
      have h3 : s' y ∈ J.ideal (Y.affineBasicOpen h0) :=
        J.ideal_le_comap_ideal (U := Y.affineBasicOpen h0) (V := ⟨_, hW⟩) hDW hy
      rw [hJD] at h3
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.1 h3
      rw [Ideal.mem_span_singleton, ← ss' y, ha, map_mul]
      exact dvd_mul_right _ _
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have h4 : r ∈ J.ideal (Y.affineBasicOpen h0) := by
        rw [hJD]
        exact Ideal.mem_span_singleton_self r
      exact J.ideal_le_comap_ideal (U := ⟨_, hW⟩) (V := Y.affineBasicOpen h0) hWD h4
  let ρ := (f.appIso (f ⁻¹ᵁ Y.basicOpen h0)).commRingCatIsoToRingEquiv
  refine ⟨⟨f ⁻¹ᵁ Y.basicOpen h0, hU⟩, ρ (σ r), hx0, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors ρ (ringEquiv_mem_nonZeroDivisors σ hr)
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    ext y
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    have key : (f.appIso (f ⁻¹ᵁ Y.basicOpen h0)).inv.hom y ∈
        J.ideal ⟨f ''ᵁ f ⁻¹ᵁ Y.basicOpen h0, hW⟩ ↔ σ r ∣ ρ.symm y := by
      rw [hJW, Ideal.mem_span_singleton]
      rfl
    refine key.trans ?_
    conv_rhs => rw [← ρ.apply_symm_apply y]
    rw [map_dvd_iff]
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
