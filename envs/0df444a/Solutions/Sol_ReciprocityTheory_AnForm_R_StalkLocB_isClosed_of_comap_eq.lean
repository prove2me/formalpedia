-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.StalkLocB.isClosed_of_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:54.846098+00:00
-- url     : https://prove2.me/submissions/18f63926-4f48-42fc-a131-8c6e0d7a5f6b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_secH_surjective
import Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_isUnit_germ_secH_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_germ_secH_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
open ReciprocityTheory.AnForm.R.StalkLocB
variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))
variable {K iso}
namespace ReciprocityTheory.AnForm.R.StalkLocB
theorem _root_.solution (s : W ⟶ Spec (.of ℂ))
    (hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
      V.ι ≫ s) (v : V) (p : Fin n → ℂ)
    (hp : (iso.hom.base v).asIdeal.comap (Ideal.Quotient.mk K) = ptIdeal p) :
    IsClosed ({v.1} : Set W) := by
  set x : W := v.1 with hxdef
  have hV : IsAffineOpen V := IsAffine.of_isIso iso.hom
  have hunit : ∀ f, IsUnit (W.presheaf.germ V x v.2 (secH V K iso f)) ↔ eval p f ≠ 0 := by
    intro f
    rw [isUnit_germ_secH_iff, ← Ideal.mem_comap, hp]
    simp [ptIdeal, RingHom.mem_ker]
  let γ : ℂ →+* W.presheaf.stalk x := (W.presheaf.germ ⊤ x trivial).hom.comp
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom)
  have hγ : ∀ c, γ c = W.presheaf.germ V x v.2 (secH V K iso (C c)) :=
    fun c => (germ_secH_C V s hover x v.2 c).symm
  have KC : ∀ t : W.presheaf.stalk x, ∃ c : ℂ, t - γ c ∈ IsLocalRing.maximalIdeal _ := by
    intro t
    let _ := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨x, v.2⟩
    have := hV.isLocalization_stalk ⟨x, v.2⟩
    set Q := (hV.primeIdealOf ⟨x, v.2⟩).asIdeal
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl t
    obtain ⟨f, rfl⟩ := secH_surjective V K iso a
    obtain ⟨g, hg⟩ := secH_surjective V K iso (b : Γ(W, V))
    have hb : algebraMap Γ(W, V) (W.presheaf.stalk x) b ∉ IsLocalRing.maximalIdeal _ := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (W.presheaf.stalk x) Q]
      exact b.2
    have hgb : W.presheaf.germ V x v.2 (secH V K iso g) = algebraMap Γ(W, V) _ b := by
      rw [hg]; rfl
    have hg0 : eval p g ≠ 0 := by
      rw [← hunit, hgb]
      by_contra h
      exact hb ((IsLocalRing.mem_maximalIdeal _).2 h)
    refine ⟨eval p f / eval p g, ?_⟩
    have hspec := IsLocalization.mk'_spec (W.presheaf.stalk x) (secH V K iso f) b
    have hfa : algebraMap Γ(W, V) (W.presheaf.stalk x) (secH V K iso f) =
        W.presheaf.germ V x v.2 (secH V K iso f) := rfl
    have hzero : W.presheaf.germ V x v.2 (secH V K iso (f - C (eval p f / eval p g) * g)) ∈
        IsLocalRing.maximalIdeal _ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
      simp [eval_sub, eval_mul, eval_C, div_mul_cancel₀ _ hg0]
    have hprod : (IsLocalization.mk' (W.presheaf.stalk x) (secH V K iso f) b -
        γ (eval p f / eval p g)) * algebraMap Γ(W, V) _ b =
        W.presheaf.germ V x v.2 (secH V K iso (f - C (eval p f / eval p g) * g)) := by
      rw [sub_mul, hspec, hfa, hγ, ← hgb, map_sub, map_sub, map_mul, map_mul]
    rw [← hprod] at hzero
    exact ((IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_or_mem hzero).resolve_right hb
  refine closure_subset_iff_isClosed.mp ?_
  intro y hy
  have hxy : x ⤳ y := specializes_iff_mem_closure.2 hy
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : W.Opens) from trivial)
  have hxU : x ∈ U := hxy.mem_open U.isOpen hyU
  let _ := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  set P := hU.primeIdealOf ⟨x, hxU⟩
  let β : ℂ →+* Γ(W, U) := (W.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom)
  have hβ : ∀ c, W.presheaf.germ U x hxU (β c) = γ c := fun c =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hmax : P.asIdeal.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, fun J b hPJ hb hbJ => ?_⟩
    obtain ⟨c, hc⟩ := KC (W.presheaf.germ U x hxU b)
    have hmem : b - β c ∈ P.asIdeal := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (W.presheaf.stalk x) P.asIdeal]
      show W.presheaf.germ U x hxU (b - β c) ∈ _
      rw [map_sub, hβ]
      exact hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hb
      simpa using hmem
    have hβJ : β c ∈ J := by
      have h1 := J.sub_mem hbJ (hPJ hmem)
      simpa using h1
    have hu : IsUnit (β c) := (isUnit_iff_ne_zero.2 hc0).map β
    rw [Ideal.eq_top_of_isUnit_mem J hβJ hu]
    exact Submodule.mem_top
  have hcl : IsClosed ({P} : Set (PrimeSpectrum Γ(W, U))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).2 hmax
  have hsp : (⟨x, hxU⟩ : U) ⤳ ⟨y, hyU⟩ := (subtype_specializes_iff _ _).2 hxy
  have hsp' : P ⤳ hU.primeIdealOf ⟨y, hyU⟩ := hsp.map hU.isoSpec.hom.continuous
  have heq : hU.primeIdealOf ⟨y, hyU⟩ = P := by
    have := specializes_iff_mem_closure.1 hsp'
    rwa [hcl.closure_eq] at this
  have hyx : (⟨y, hyU⟩ : U) = ⟨x, hxU⟩ := hU.isoSpec.hom.isOpenEmbedding.injective heq
  exact congrArg Subtype.val hyx
end ReciprocityTheory.AnForm.R.StalkLocB
