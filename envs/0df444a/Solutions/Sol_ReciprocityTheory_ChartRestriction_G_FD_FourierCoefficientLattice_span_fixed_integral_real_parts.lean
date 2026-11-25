-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.span_fixed_integral_real_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:56.917665+00:00
-- url     : https://prove2.me/submissions/73cefe6c-3299-41b6-8bb2-e1e64e358e20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
theorem _root_.solution : Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
    p = fun τ => (τ.1 a).re} = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hfS⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hf : ∀ p : X.Ψ → ℝ, f p = ∑ τ, p τ * f (fun j => if τ = j then 1 else 0) := by
    intro p
    rw [LinearMap.pi_apply_eq_sum_univ f p]
    simp only [smul_eq_mul]
  obtain ⟨lam, hlam⟩ : ∃ lam : X.Ψ → ℝ, ∀ p : X.Ψ → ℝ, f p = ∑ τ, p τ * lam τ := ⟨_, hf⟩
  have hinv : ∀ y : E, cc (cc y) = y := by
    intro y
    first
    | exact NumberField.IsCMField.complexConj_apply_apply E y
    | exact NumberField.IsCMField.complexConj_apply_apply y
    | simp [cc]
  have hvan : ∀ x : 𝓞 E, ∑ τ : X.Ψ, (τ.1 (x : E)).re * lam τ = 0 := by
    intro x
    have hx : IsIntegral ℤ (x : E) := by
      first
      | exact x.isIntegral_coe
      | exact NumberField.RingOfIntegers.isIntegral_coe x
      | exact x.2
    have hcx : IsIntegral ℤ (cc (x : E)) := by
      first
      | exact hx.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)
      | exact hx.map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)
    have hr : cc ((x : E) + cc (x : E)) = (x : E) + cc (x : E) := by
      rw [show cc ((x : E) + cc (x : E)) = cc (x : E) + cc (cc (x : E)) from map_add _ _ _, hinv,
        add_comm]
    have hmem : (fun τ : X.Ψ => (τ.1 ((x : E) + cc (x : E))).re) ∈ Submodule.span ℝ
        {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧ p = fun τ => (τ.1 a).re} :=
      Submodule.subset_span ⟨_, hr, hx.add hcx, rfl⟩
    have h := hfS hmem
    rw [LinearMap.mem_ker, hlam] at h
    have e : ∀ τ : X.Ψ, (τ.1 ((x : E) + cc (x : E))).re = 2 * (τ.1 (x : E)).re := by
      intro τ
      rw [map_add, show τ.1 (cc (x : E)) = conj (τ.1 (x : E)) from
        NumberField.IsCMField.complexEmbedding_complexConj E τ.1 (x : E), Complex.add_re, Complex.conj_re]
      ring
    simp only [e] at h
    have h2 : ∑ τ : X.Ψ, 2 * (τ.1 (x : E)).re * lam τ = 2 * ∑ τ : X.Ψ, (τ.1 (x : E)).re * lam τ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      ring
    linarith
  have hmh : ∀ φ ψ : 𝓞 E →+* ℂ, φ.toMonoidHom = ψ.toMonoidHom → φ = ψ := fun φ ψ h =>
    RingHom.ext fun x => DFunLike.congr_fun h x
  have hext : ∀ φ ψ : E →+* ℂ, φ.comp (algebraMap (𝓞 E) E) = ψ.comp (algebraMap (𝓞 E) E) → φ = ψ :=
    fun φ ψ h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  have hcc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
    intro φ
    first
    | exact ComplexEmbedding.conjugate_conjugate φ
    | exact star_star φ
    | (ext y; simp [ComplexEmbedding.conjugate_coe_eq])
  have hFinj : Function.Injective
      (Sum.elim (fun τ : X.Ψ => τ.1) (fun τ : X.Ψ => ComplexEmbedding.conjugate τ.1)) := by
    rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have h' : τ.1 = ComplexEmbedding.conjugate τ'.1 := h
      have h1 : ComplexEmbedding.conjugate τ'.1 ∈ X.Ψ := by
        rw [← h']
        exact τ.2
      exact ((X.cmType τ'.1).mp τ'.2) h1
    · exfalso
      have h' : ComplexEmbedding.conjugate τ.1 = τ'.1 := h
      have h1 : ComplexEmbedding.conjugate τ.1 ∈ X.Ψ := by
        rw [h']
        exact τ'.2
      exact ((X.cmType τ.1).mp τ.2) h1
    · have h' : ComplexEmbedding.conjugate τ.1 = ComplexEmbedding.conjugate τ'.1 := h
      have h1 : τ.1 = τ'.1 := by
        have h2 := congrArg ComplexEmbedding.conjugate h'
        rwa [hcc, hcc] at h2
      exact congrArg Sum.inr (Subtype.ext h1)
  have hGinj : Function.Injective (fun t : X.Ψ ⊕ X.Ψ =>
      ((Sum.elim (fun τ : X.Ψ => τ.1) (fun τ : X.Ψ => ComplexEmbedding.conjugate τ.1) t).comp
        (algebraMap (𝓞 E) E)).toMonoidHom) := by
    intro t t' h
    exact hFinj (hext _ _ (hmh _ _ h))
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ hGinj
  rw [Fintype.linearIndependent_iff] at hli
  have hzero := hli (Sum.elim (fun τ => (lam τ : ℂ)) (fun τ => (lam τ : ℂ))) (by
    funext x
    have key : ∑ τ : X.Ψ, (lam τ : ℂ) * (τ.1 (x : E) + conj (τ.1 (x : E))) = 0 := by
      have h := hvan x
      simp only [Complex.add_conj]
      have h3 : ∑ τ : X.Ψ, (lam τ : ℂ) * ((2 * (τ.1 (x : E)).re : ℝ) : ℂ) =
          ((2 * ∑ τ : X.Ψ, (τ.1 (x : E)).re * lam τ : ℝ) : ℂ) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        ring
      rw [h3, h, mul_zero, Complex.ofReal_zero]
    rw [Finset.sum_apply, Fintype.sum_sum_type]
    show ∑ τ : X.Ψ, (lam τ : ℂ) * τ.1 (x : E) +
      ∑ τ : X.Ψ, (lam τ : ℂ) * (ComplexEmbedding.conjugate τ.1) (x : E) = 0
    simp only [ComplexEmbedding.conjugate_coe_eq, ← Finset.sum_add_distrib, ← mul_add]
    exact key)
  have hl : ∀ τ, lam τ = 0 := fun τ => by
    have h := hzero (Sum.inl τ)
    simpa using h
  exact hf0 (LinearMap.ext fun p => by rw [hlam]; simp [hl])
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
