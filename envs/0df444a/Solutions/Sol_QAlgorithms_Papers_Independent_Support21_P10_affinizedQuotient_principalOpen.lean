-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P10.affinizedQuotient_principalOpen
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:42:17.396062+00:00
-- url     : https://prove2.me/submissions/15751ea7-98f0-477f-adb2-5e4958d6a3df

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10
noncomputable section

open QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

theorem g66e_L_mk' {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A] [Group (Point k H)]
    (rho : Point k H →* (A ≃ₐ[k] A)) (f : invariantSubalgebra rho)
    (a : invariantSubalgebra rho) (n : ℕ) :
    invariantLocalizationMap rho f
        (IsLocalization.mk' (Localization.Away f) a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)) =
      IsLocalization.mk' (Localization.Away (f : A)) (a : A)
        (⟨(f : A) ^ n, n, rfl⟩ : Submonoid.powers (f : A)) := by
  haveI : IsLocalization (Submonoid.powers ((invariantSubalgebra rho).val.toRingHom f))
      (Localization.Away (f : A)) := by
    change IsLocalization (Submonoid.powers (f : A)) _
    infer_instance
  unfold invariantLocalizationMap
  simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map]
  rw [IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]
  symm
  have := IsLocalization.mk'_spec (Localization.Away (f : A)) (a : A)
    (⟨(f : A) ^ n, n, rfl⟩ : Submonoid.powers (f : A))
  convert this using 2 <;> rfl

theorem g66e_P_mk' {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A] [Group (Point k H)]
    (rho : Point k H →* (A ≃ₐ[k] A)) (f : invariantSubalgebra rho) (g : Point k H)
    (a : A) (n : ℕ) :
    localizedPullback rho f g
        (IsLocalization.mk' (Localization.Away (f : A)) a
          (⟨(f : A) ^ n, n, rfl⟩ : Submonoid.powers (f : A))) =
      IsLocalization.mk' (Localization.Away (f : A)) (rho g a)
        (⟨(f : A) ^ n, n, rfl⟩ : Submonoid.powers (f : A)) := by
  have e : (↑(rho g) : A →ₐ[k] A).toRingHom (f : A) = (f : A) := f.property g
  haveI : IsLocalization (Submonoid.powers ((↑(rho g) : A →ₐ[k] A).toRingHom (f : A)))
      (Localization.Away (f : A)) := by
    rw [e]; infer_instance
  unfold localizedPullback
  simp only [IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map]
  rw [IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]
  symm
  have := IsLocalization.mk'_spec (Localization.Away (f : A)) (rho g a)
    (⟨(f : A) ^ n, n, rfl⟩ : Submonoid.powers (f : A))
  convert this using 2
  all_goals try rfl
  show algebraMap A (Localization.Away (f : A)) ((↑(rho g) : A →ₐ[k] A).toRingHom ((f : A) ^ n)) =
    algebraMap A _ ((f : A) ^ n)
  rw [map_pow, e]

theorem solution
    {k : Type u} {H : Type v} {A : Type w}
    [Field k] [IsAlgClosed k] [CommRing H] [CommRing A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (hG : IsAffineAlgebraicGroup k H) (hX : IsAffineVariety k A)
    (rho : Point k H →* (A ≃ₐ[k] A)) (hregular : IsRegularAction rho)
    (hfg : Algebra.FiniteType k (invariantSubalgebra rho))
    (f : invariantSubalgebra rho) :
    ∃ e : Localization.Away f ≃ₐ[k] localizedInvariantSubalgebra rho f,
      (localizedInvariantSubalgebra rho f).val.comp e.toAlgHom =
        invariantLocalizationMap rho f := by
  have hred : IsReduced A := hX.2
  have hinj : Function.Injective (invariantLocalizationMap rho f) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x
    obtain ⟨n, hn⟩ := s.2
    have hs : s = ⟨f ^ n, n, rfl⟩ := Subtype.ext hn.symm
    subst hs
    rw [g66e_L_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := hx
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨f ^ m, m, rfl⟩, Subtype.ext ?_⟩
    simpa using hm
  have hrange : (invariantLocalizationMap rho f).range = localizedInvariantSubalgebra rho f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x
      obtain ⟨n, hn⟩ := s.2
      have hs : s = ⟨f ^ n, n, rfl⟩ := Subtype.ext hn.symm
      subst hs
      intro g
      change localizedPullback rho f g (invariantLocalizationMap rho f _) = invariantLocalizationMap rho f _
      rw [g66e_L_mk', g66e_P_mk', a.property g]
    · intro hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (f : A)) y
      obtain ⟨n, hn⟩ := s.2
      have hs : s = ⟨(f : A) ^ n, n, rfl⟩ := Subtype.ext hn.symm
      subst hs
      have key : ∀ g, (f : A) * (rho g a) = (f : A) * a := by
        intro g
        have h1 := hy g
        rw [g66e_P_mk', IsLocalization.mk'_eq_iff_eq,
          IsLocalization.eq_iff_exists (Submonoid.powers (f : A))] at h1
        obtain ⟨⟨_, m, rfl⟩, hm⟩ := h1
        simp only at hm
        have h0 : (f : A) ^ (m + n) * (rho g a - a) = 0 := by
          rw [pow_add]; linear_combination hm
        have hnil : IsNilpotent ((f : A) * (rho g a - a)) :=
          ⟨m + n + 1, by
            rw [pow_succ, mul_pow]
            calc _ = ((f : A) ^ (m + n) * (rho g a - a)) * ((rho g a - a) ^ (m + n) * (f : A)) := by
                  ring
              _ = 0 := by rw [h0, zero_mul]⟩
        have := hred.eq_zero _ hnil
        linear_combination this
      have hb : (f : A) * a ∈ invariantSubalgebra rho := by
        intro g
        rw [map_mul, f.property g, key g]
      refine ⟨IsLocalization.mk' _ (⟨(f : A) * a, hb⟩ : invariantSubalgebra rho)
        (⟨f ^ (n + 1), n + 1, rfl⟩ : Submonoid.powers f), ?_⟩
      change invariantLocalizationMap rho f _ = _
      rw [g66e_L_mk', IsLocalization.mk'_eq_iff_eq]
      congr 1
      ring
  refine ⟨(AlgEquiv.ofInjective (invariantLocalizationMap rho f) hinj).trans (Subalgebra.equivOfEq _ _ hrange), ?_⟩
  ext x
  rfl
