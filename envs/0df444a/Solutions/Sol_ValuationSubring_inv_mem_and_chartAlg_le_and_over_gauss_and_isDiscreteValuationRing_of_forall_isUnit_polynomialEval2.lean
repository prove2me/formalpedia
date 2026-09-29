-- Prove2me | solution 1 for ValuationSubring.inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d4aa9db0-1ffe-55aa-915f-3f430be58fd2

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace GaussBranch

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})

include hϖ in
theorem exists_isUnit_coeff_of_not_C_dvd {P : Polynomial R} (h : ¬ Polynomial.C ϖ ∣ P) :
    ∃ i, IsUnit (P.coeff i) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff] at h
  simp only [not_forall] at h
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  by_contra hu
  apply hi
  have : P.coeff i ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hu
  rw [hϖ, Ideal.mem_span_singleton] at this
  exact this

include hϖ in
theorem not_C_dvd_of_map_residue_ne_zero {P : Polynomial R} (h : P.map (residue R) ≠ 0) :
    ¬ Polynomial.C ϖ ∣ P := by
  intro hd
  apply h
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hd
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton]
  exact hd i

include hϖ in
theorem map_residue_ne_zero_of_not_C_dvd {P : Polynomial R} (h : ¬ Polynomial.C ϖ ∣ P) :
    P.map (residue R) ≠ 0 := by
  intro h0
  apply h
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  have := congrArg (fun q => q.coeff i) h0
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, residue_eq_zero_iff] at this
  rw [hϖ, Ideal.mem_span_singleton] at this
  exact this

include hϖ in
theorem ϖ_ne_zero : ϖ ≠ 0 := by
  intro h
  apply IsDiscreteValuationRing.not_a_field R
  rw [hϖ, h, Ideal.span_singleton_eq_bot]

include hϖ in
theorem ϖ_not_isUnit : ¬ IsUnit ϖ := by
  intro h
  have : ϖ ∈ maximalIdeal R := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  exact (mem_maximalIdeal _).mp this h

end DVR

section Val

variable {F : Type u} [Field F] (O : ValuationSubring F)

theorem inv_mem_of_isUnit {x : F} (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : ↥O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have h1 : x * (((u⁻¹ : (↥O)ˣ) : ↥O) : F) = 1 := by
    have := congrArg (fun y : ↥O => (y : F)) u.mul_inv
    rw [hu] at this
    simpa using this
  rw [inv_eq_of_mul_eq_one_right h1]
  exact Subtype.coe_prop _

theorem ne_zero_of_isUnit {x : F} (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : ↥O)) : x ≠ 0 := by
  intro h0
  apply hu.ne_zero
  exact Subtype.ext h0

theorem not_mem_nonunits_of_isUnit {x : F} (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : ↥O)) : x ∉ O.nonunits := by
  intro hn
  have := ValuationSubring.coe_mem_nonunits_iff.mp (show ((⟨x, hx⟩ : ↥O) : F) ∈ O.nonunits from hn)
  exact (mem_maximalIdeal _).mp this hu

theorem mul_mem_nonunits {x y : F} (hx : x ∈ O) (hy : y ∈ O.nonunits) : x * y ∈ O.nonunits := by
  obtain ⟨hyO, hym⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hy
  have : (⟨x, hx⟩ : ↥O) * ⟨y, hyO⟩ ∈ maximalIdeal ↥O := Ideal.mul_mem_left _ _ hym
  exact ValuationSubring.coe_mem_nonunits_iff.mpr this

theorem mem_of_isIntegral_adjoin {R : Type u} [CommRing R] [Algebra R F]
    (hRO : ∀ a : R, algebraMap R F a ∈ O) {S : Set F} (hS : S ⊆ O) {x : F}
    (hx : IsIntegral ↥(Algebra.adjoin R S) x) : x ∈ O := by
  let O' : Subalgebra R F :=
    { toSubsemiring := O.toSubring.toSubsemiring
      algebraMap_mem' := hRO }
  have hle : Algebra.adjoin R S ≤ O' := Algebra.adjoin_le hS
  let φ : ↥(Algebra.adjoin R S) →+* ↥O :=
    (Algebra.adjoin R S).val.toRingHom.codRestrict O.toSubring (fun y => hle y.2)
  have hint : IsIntegral ↥O x :=
    hx.map_of_comp_eq φ (RingHom.id F) (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥O) (K := F)).mp hint
  rw [← hy]
  exact Subtype.coe_prop y

end Val

end GaussBranch

open GaussBranch in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (O : ValuationSubring F)
    (hRO : ∀ a : R, algebraMap R F a ∈ O) (hϖO : algebraMap R F ϖ ∈ O.nonunits)
    (f : F) (hfO : f ∈ O)
    (hgeo : ∀ p : Polynomial R, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ (algebraMap R F) f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)) :
    ∃ hf0 : f ≠ 0,
      letI : Fact (f ≠ 0) := ⟨hf0⟩
      f⁻¹ ∈ O ∧ Transcendental R f ∧

      (∀ x : ↥(chartAlgFin R F f), (x : F) ∈ O) ∧ (∀ x : ↥(chartAlgInf R F f), (x : F) ∈ O) ∧

      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval f P ∈ O ∧ (Polynomial.aeval f P)⁻¹ ∈ O) ∧

      (FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F →
        Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F →
        IsDiscreteValuationRing ↥O ∧
        ∃ 𝔭 : Ideal ↥(chartAlgFin R F f),
          𝔭 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes ∧ ¬ 𝔭.IsMaximal ∧
          (∀ x : ↥(chartAlgFin R F f), x ∈ 𝔭 ↔ (x : F) ∈ O.nonunits) ∧
          (∀ y : F, y ∈ O ↔ ∃ b c : ↥(chartAlgFin R F f), c ∉ 𝔭 ∧ y * (c : F) = (b : F))) := by
  classical
  have hinj : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hϖ0 : ϖ ≠ 0 := ϖ_ne_zero ϖ hϖ

  have haeval : ∀ P : Polynomial R, Polynomial.aeval f P = Polynomial.eval₂ (algebraMap R F) f P :=
    fun P => Polynomial.aeval_def f P
  have hunitP : ∀ P : Polynomial R, ¬ Polynomial.C ϖ ∣ P →
      ∃ hO : Polynomial.aeval f P ∈ O, IsUnit (⟨_, hO⟩ : ↥O) := by
    intro P hP
    rw [haeval P]
    exact hgeo P (exists_isUnit_coeff_of_not_C_dvd ϖ hϖ hP)

  have hfu : IsUnit (⟨f, hfO⟩ : ↥O) := by
    obtain ⟨hO, hu⟩ := hgeo Polynomial.X ⟨1, by simp⟩
    have : (⟨_, hO⟩ : ↥O) = ⟨f, hfO⟩ := Subtype.ext (by simp [Polynomial.eval₂_X])
    rwa [this] at hu
  have hf0 : f ≠ 0 := ne_zero_of_isUnit O hfO hfu
  have hfinv : f⁻¹ ∈ O := inv_mem_of_isUnit O hfO hfu

  have hgauss : ∀ P : Polynomial R, ¬ Polynomial.C ϖ ∣ P →
      Polynomial.aeval f P ∈ O ∧ (Polynomial.aeval f P)⁻¹ ∈ O := by
    intro P hP
    obtain ⟨hO, hu⟩ := hunitP P hP
    exact ⟨hO, inv_mem_of_isUnit O hO hu⟩

  have htr : Transcendental R f := by
    rintro ⟨p, hp0, hpf⟩
    have hCu : ¬ IsUnit (Polynomial.C ϖ) := by
      rw [Polynomial.isUnit_C]; exact ϖ_not_isUnit ϖ hϖ
    obtain ⟨n, P, hP, rfl⟩ := WfDvdMonoid.max_power_factor' hp0 hCu
    obtain ⟨hO, hu⟩ := hunitP P hP
    rw [map_mul, map_pow, Polynomial.aeval_C] at hpf
    rcases mul_eq_zero.mp hpf with h | h
    · exact pow_ne_zero n ((map_ne_zero_iff _ hinj).mpr hϖ0) h
    · exact ne_zero_of_isUnit O hO hu h
  refine ⟨hf0, hfinv, htr, ?_, ?_, hgauss, ?_⟩
  ·
    intro x
    exact mem_of_isIntegral_adjoin O hRO (Set.singleton_subset_iff.mpr hfO) ((mem_chartAlg_iff R F).mp x.2)
  ·
    intro x
    exact mem_of_isIntegral_adjoin O hRO (Set.singleton_subset_iff.mpr hfinv) ((mem_chartAlg_iff R F).mp x.2)
  ·
    intro hFD hsep
    haveI : Fact (f ≠ 0) := ⟨hf0⟩

    have hOm : ∀ a ∈ maximalIdeal R, algebraMap R F a ∈ O.nonunits := by
      intro a ha
      rw [hϖ, Ideal.mem_span_singleton'] at ha
      obtain ⟨r, rfl⟩ := ha
      rw [map_mul]
      exact mul_mem_nonunits O (hRO r) hϖO
    have hOj : ∀ P : Polynomial R, P.map (residue R) ≠ 0 →
        Polynomial.aeval f P ∈ O ∧ (Polynomial.aeval f P)⁻¹ ∈ O :=
      fun P hP => hgauss P (not_C_dvd_of_map_residue_ne_zero ϖ hϖ hP)
    obtain ⟨hchartO, ⟨𝔓, h𝔓prime, h𝔓ht, h𝔓mem, h𝔓R, h𝔓loc⟩, hdist⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
        R K₀ F f htr hFD hsep O hRO hOm hOj
    haveI := h𝔓prime

    have hϖ' : algebraMap R ↥(chartAlgFin R F f) ϖ ∈ 𝔓 := h𝔓R ϖ (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
    have hle : Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ} ≤ 𝔓 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hϖ'
    have hϖ'0 : algebraMap R ↥(chartAlgFin R F f) ϖ ≠ 0 := by
      intro h
      apply (map_ne_zero_iff _ hinj).mpr hϖ0
      have := congrArg (fun y : ↥(chartAlgFin R F f) => (y : F)) h
      simpa using this
    haveI : 𝔓.FiniteHeight := ⟨Or.inr (by rw [h𝔓ht]; exact ENat.one_ne_top)⟩
    have hmin : 𝔓 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F f) ϖ}).minimalPrimes := by
      refine Ideal.mem_minimalPrimes_of_height_eq hle ?_
      rw [h𝔓ht]
      exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ'0)

    have hprime : Prime ϖ :=
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ).prime
    obtain ⟨V, hVdvr, hchartV, hV𝔓, hϖV, hVgauss⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
        R K₀ F f htr hFD hsep ϖ hprime 𝔓 hmin
    have hRV : ∀ a : R, algebraMap R F a ∈ V := by
      intro a
      have := hchartV (algebraMap R ↥(chartAlgFin R F f) a)
      simpa using this
    have hVm : ∀ a ∈ maximalIdeal R, algebraMap R F a ∈ V.nonunits := by
      intro a ha
      rw [hϖ, Ideal.mem_span_singleton'] at ha
      obtain ⟨r, rfl⟩ := ha
      rw [map_mul]
      exact mul_mem_nonunits V (hRV r) hϖV
    have hVj : ∀ P : Polynomial R, P.map (residue R) ≠ 0 →
        Polynomial.aeval f P ∈ V ∧ (Polynomial.aeval f P)⁻¹ ∈ V :=
      fun P hP => hVgauss P (not_C_dvd_of_map_residue_ne_zero ϖ hϖ hP)
    have hOV : O = V := by
      by_contra hne
      obtain ⟨b, hbV, hbO⟩ := hdist V hRV hVm hVj hne
      exact hbO ((h𝔓mem b).mp ((hV𝔓 b).mpr hbV))
    refine ⟨by rw [hOV]; exact hVdvr, 𝔓, hmin, ?_, h𝔓mem, h𝔓loc⟩

    intro hmax

    let φ : Polynomial R →+* ↥(chartAlgFin R F f) := (polynomialToChartFin R F f).toRingHom
    have hφ : ∀ g : Polynomial R, ((φ g : ↥(chartAlgFin R F f)) : F) = Polynomial.aeval f g := by
      intro g
      exact (Polynomial.aeval_algHom_apply (chartAlgFin R F f).val (jChartFin R F f) g).symm
    have hφint : φ.IsIntegral := by
      intro x
      have hx : IsIntegral ↥(Algebra.adjoin R ({f} : Set F)) (x : F) := (mem_chartAlg_iff R F).mp x.2
      obtain ⟨p, hpm, hpx⟩ := hx

      let ψ : Polynomial R →+* ↥(Algebra.adjoin R ({f} : Set F)) :=
        (Polynomial.aeval f).toRingHom.codRestrict (Algebra.adjoin R ({f} : Set F)).toSubring
          (fun g => by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨g, rfl⟩)
      have hψs : Function.Surjective ψ := by
        rintro ⟨y, hy⟩
        rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
        obtain ⟨g, rfl⟩ := hy
        exact ⟨g, rfl⟩
      obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
        (show p ∈ Polynomial.lifts ψ from (Polynomial.lifts_iff_coeff_lifts p).mpr fun n => hψs _) hpm
      refine ⟨P, hPm, ?_⟩
      apply Subtype.ext
      have h1 : (((Polynomial.eval₂ φ x P) : ↥(chartAlgFin R F f)) : F) =
          Polynomial.eval₂ ((chartAlgFin R F f).val.toRingHom.comp φ) (x : F) P :=
        Polynomial.hom_eval₂ P φ (chartAlgFin R F f).val.toRingHom x
      rw [h1]
      have h2 : (chartAlgFin R F f).val.toRingHom.comp φ = (Algebra.adjoin R ({f} : Set F)).val.toRingHom.comp ψ :=
        Polynomial.ringHom_ext
          (fun a => by
            show ((φ (Polynomial.C a) : ↥(chartAlgFin R F f)) : F) =
              ((ψ (Polynomial.C a) : ↥(Algebra.adjoin R ({f} : Set F))) : F)
            rw [hφ]; rfl)
          (by
            show ((φ Polynomial.X : ↥(chartAlgFin R F f)) : F) =
              ((ψ Polynomial.X : ↥(Algebra.adjoin R ({f} : Set F))) : F)
            rw [hφ]; rfl)
      rw [h2, Polynomial.eval₂_eq_eval_map, ← Polynomial.map_map, hP, ← Polynomial.eval₂_eq_eval_map]
      simp at hpx ⊢
      exact hpx
    let 𝔮 : Ideal (Polynomial R) := 𝔓.comap φ
    haveI h𝔮 : 𝔮.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hφint 𝔓

    let π : Polynomial R →+* Polynomial (ResidueField R) := Polynomial.mapRingHom (residue R)
    have hπs : Function.Surjective π := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
    have hkerπ : ∀ g : Polynomial R, π g = 0 → g ∈ 𝔮 := by
      intro g hg
      have hdvd : Polynomial.C ϖ ∣ g := by
        by_contra h
        exact map_residue_ne_zero_of_not_C_dvd ϖ hϖ h hg
      obtain ⟨g', rfl⟩ := hdvd
      show φ (Polynomial.C ϖ * g') ∈ 𝔓
      rw [map_mul]
      refine Ideal.mul_mem_right _ _ ?_
      have : φ (Polynomial.C ϖ) = algebraMap R ↥(chartAlgFin R F f) ϖ := by
        show polynomialToChartFin R F f (Polynomial.C ϖ) = _
        simp [polynomialToChartFin]
      rw [this]; exact hϖ'
    have h𝔮ne : 𝔮.map π ≠ ⊤ := by
      intro htop
      have h1 : (1 : Polynomial (ResidueField R)) ∈ 𝔮.map π := htop.symm ▸ Submodule.mem_top
      obtain ⟨g, hg, hg1⟩ := (Ideal.mem_map_iff_of_surjective π hπs).mp h1
      have : g - 1 ∈ 𝔮 := hkerπ _ (by rw [map_sub, hg1, map_one, sub_self])
      have : (1 : Polynomial R) ∈ 𝔮 := by simpa using Ideal.sub_mem 𝔮 hg this
      exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have h𝔮max : (𝔮.map π).IsMaximal :=
      (Ideal.map_eq_top_or_isMaximal_of_surjective π hπs h𝔮).resolve_left h𝔮ne
    have h𝔮bot : 𝔮.map π ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔮max (Polynomial.not_isField (ResidueField R))
    obtain ⟨gbar, hgbar, hgbar0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮bot
    obtain ⟨g, hg𝔮, rfl⟩ := (Ideal.mem_map_iff_of_surjective π hπs).mp hgbar
    have hgC : ¬ Polynomial.C ϖ ∣ g := not_C_dvd_of_map_residue_ne_zero ϖ hϖ hgbar0
    obtain ⟨hO, hu⟩ := hunitP g hgC
    apply not_mem_nonunits_of_isUnit O hO hu
    rw [← hφ]
    exact (h𝔓mem (φ g)).mp hg𝔮

end S_ValuationSubring_inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2
end P2MW
export P2MW.S_ValuationSubring_inv_mem_and_chartAlg_le_and_over_gauss_and_isDiscreteValuationRing_of_forall_isUnit_polynomialEval2 (solution)
