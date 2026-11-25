-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.exists_lift_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:23:18.434804+00:00
-- url     : https://prove2.me/submissions/9505e3bf-3569-4d84-b22d-8afcb1dd95ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_FiniteLocalLifts_SmLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
variable {R : Type} [CommRing R] {A W K : Type} [CommRing A] [CommRing W] [CommRing K]
  [Algebra R A] [Algebra R W] [Algebra R K]
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
theorem _root_.solution [Algebra.FormallySmooth R A] [Algebra.FinitePresentation R A]
    (ρ : W →ₐ[R] K) (hsurj : Function.Surjective ρ) (hnil : ∀ a ∈ RingHom.ker ρ, IsNilpotent a)
    (φ : A →ₐ[R] K) : ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by
  classical
  obtain ⟨n, f, hf, hfg⟩ : ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective f ∧
      (RingHom.ker f.toRingHom).FG := by
    first
    | exact Algebra.FinitePresentation.out
    | (obtain ⟨n, f, hf, hfg⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
       exact ⟨n, f, hf, hfg⟩)
  choose w hw using fun i : Fin n => hsurj (φ (f (MvPolynomial.X i)))
  let Φ : MvPolynomial (Fin n) R →ₐ[R] W := MvPolynomial.aeval w
  have hΦ : ρ.comp Φ = φ.comp f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Φ, hw]
  obtain ⟨s, hs⟩ := hfg
  let J : Ideal W := Ideal.span (Φ '' (s : Set (MvPolynomial (Fin n) R)))
  have hker : RingHom.ker f.toRingHom ≤ J.comap Φ := by
    rw [← hs, Ideal.span_le]
    intro p hp
    exact Ideal.mem_comap.mpr (Ideal.subset_span ⟨p, hp, rfl⟩)
  have hJker : J ≤ RingHom.ker ρ := by
    rw [Ideal.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have hpk : p ∈ RingHom.ker f.toRingHom := hs ▸ Ideal.subset_span hp
    rw [RingHom.mem_ker] at hpk
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h1 := congrArg (fun g => g p) hΦ
    simp only [AlgHom.comp_apply] at h1
    rw [h1]
    have h2 : f p = 0 := hpk
    rw [h2, map_zero]
  have hJnil : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical ⟨s.image Φ, by rw [Finset.coe_image]⟩]
    intro a ha
    exact mem_nilradical.mpr (hnil a (hJker ha))
  have hcond : ∀ a ∈ RingHom.ker f, ((Ideal.Quotient.mkₐ R J).comp Φ) a = 0 := by
    intro a ha
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hker ha
  let g : A →ₐ[R] W ⧸ J := (Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp Φ)
    hcond).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
  refine ⟨Algebra.FormallySmooth.lift J hJnil g, ?_⟩
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := hf a
  have hmk := Algebra.FormallySmooth.mk_lift J hJnil g (f p)
  have e2 : g (f p) = Ideal.Quotient.mk J (Φ p) := by
    have e0 : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f p) = Ideal.Quotient.mk (RingHom.ker f) p := by
      rw [AlgEquiv.symm_apply_eq]
      first
      | rfl
      | simp
    show (Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp Φ) hcond)
      ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f p)) = _
    rw [e0]
    rfl
  have e3 : ρ (Algebra.FormallySmooth.lift J hJnil g (f p)) = ρ (Φ p) := by
    have h4 : Ideal.Quotient.mk J (Algebra.FormallySmooth.lift J hJnil g (f p)) = Ideal.Quotient.mk J (Φ p) :=
      hmk.trans e2
    rw [Ideal.Quotient.eq] at h4
    have h5 := hJker h4
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h5
    exact h5
  rw [AlgHom.comp_apply, e3]
  exact congrArg (fun g' => g' p) hΦ
end ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
