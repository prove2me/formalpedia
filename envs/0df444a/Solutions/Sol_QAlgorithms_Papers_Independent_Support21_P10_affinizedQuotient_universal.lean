-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P10.affinizedQuotient_universal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:43:48.148371+00:00
-- url     : https://prove2.me/submissions/47e3cd1f-af1a-4712-842b-1d2cf691248c

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10
noncomputable section

open QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

theorem g66e_points_sep {k : Type u} {A : Type w} [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] (hft : Algebra.FiniteType k A) (hred : IsReduced A) (a : A)
    (h : ∀ x : A →ₐ[k] k, x a = 0) : a = 0 := by
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  obtain ⟨p, rfl⟩ := hπ a
  have hp : p ∈ (RingHom.ker π.toRingHom).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro v hv
    have := h (AlgHom.liftOfSurjective π hπ (MvPolynomial.aeval v)
      (fun q hq => RingHom.mem_ker.2 (hv q hq)))
    rwa [AlgHom.liftOfSurjective_apply] at this
  obtain ⟨m, hm⟩ := hp
  have : IsNilpotent (π p) := ⟨m, by rw [← map_pow]; exact hm⟩
  exact hred.eq_zero _ this

theorem solution
    {k : Type u} {H : Type v} {A : Type w} {B : Type z}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A] [CommRing B]
    [Algebra k H] [Algebra k A] [Algebra k B] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (hZ : IsAffineVariety k B) (rho : Point k H →* (A ≃ₐ[k] A))
    (hregular : IsRegularAction rho)
    (hfg : Algebra.FiniteType k (invariantSubalgebra rho))
    (f : B →ₐ[k] A) (hf : IsConstantOnOrbits rho f) :
    ∃! lift : B →ₐ[k] invariantSubalgebra rho,
      (invariantSubalgebra rho).val.comp lift = f := by
  have hinv : ∀ b, f b ∈ invariantSubalgebra rho := by
    intro b g
    have h0 : rho g (f b) - f b = 0 := by
      apply g66e_points_sep hX.1 hX.2
      intro x
      have := congrArg (fun φ => φ b) (hf g⁻¹ x)
      simp only [pointAction, inv_inv, AlgHom.comp_apply] at this
      rw [map_sub, sub_eq_zero]
      exact this
    exact sub_eq_zero.1 h0
  refine ⟨f.codRestrict _ hinv, AlgHom.ext fun b => rfl, ?_⟩
  intro l hl
  ext b
  have := congrArg (fun φ => φ b) hl
  simpa using this
