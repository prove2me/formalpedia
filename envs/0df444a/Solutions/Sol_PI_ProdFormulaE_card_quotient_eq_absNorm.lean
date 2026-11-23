-- Prove2me | solution 1 for PI.ProdFormulaE.card_quotient_eq_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:10.860374+00:00
-- url     : https://prove2.me/submissions/d2d53488-51de-4ca6-bbe1-34f22d810c8e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_CardQuotientEqAbsNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open IsDedekindDomain NumberField ValuativeRel
namespace PI.ProdFormulaE
private theorem intValuation_le_iff_mem_maxPowDividing {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) (r s : R) (hs : s ≠ 0) :
    v.intValuation r ≤ v.intValuation s ↔ r ∈ v.maxPowDividing (Ideal.span {s}) := by
  rw [v.intValuation_if_neg hs, ← Ideal.dvd_span_singleton]
  exact v.intValuation_le_pow_iff_dvd r _
private theorem exists_valuation_sub_algebraMap_le {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) {f : K}
    (hf : v.valuation K f ≤ 1) {a : R} (ha : a ≠ 0) :
    ∃ x : R, v.valuation K (f - algebraMap R K x) ≤ v.valuation K (algebraMap R K a) := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap R K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hc0
  have hpos : 0 < v.valuation K (algebraMap R K c) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcK)
  have hbc : v.intValuation b ≤ v.intValuation c := by
    rw [map_div₀, div_le_one₀ hpos] at hf
    simpa only [HeightOneSpectrum.valuation_of_algebraMap] using hf
  have hca : c * a ≠ 0 := mul_ne_zero hc0 ha
  obtain ⟨N, hN⟩ : ∃ N : ℕ, v.maxPowDividing (Ideal.span {c * a}) = v.asIdeal ^ N := ⟨_, rfl⟩
  have hS : Ideal.span {c} ⊔ v.asIdeal ^ N ∣ v.asIdeal ^ N := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow v.prime N).1 hS
  rw [associated_iff_eq] at hk
  have hbk : b ∈ v.asIdeal ^ k := by
    rw [← Ideal.dvd_span_singleton]
    apply (v.intValuation_le_pow_iff_dvd b k).1
    refine hbc.trans ((v.intValuation_le_pow_iff_dvd c k).2 ?_)
    rw [← hk]
    exact Ideal.dvd_iff_le.2 le_sup_left
  rw [← hk] at hbk
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hbk
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  refine ⟨x, ?_⟩
  have hzle : v.intValuation z ≤ v.intValuation (c * a) := by
    rw [intValuation_le_iff_mem_maxPowDividing v z _ hca, hN]
    exact hz
  have hsub : algebraMap R K b / algebraMap R K c - algebraMap R K x =
      algebraMap R K z / algebraMap R K c := by
    rw [← hyz, map_add, map_mul, add_div, mul_div_assoc, div_self hcK, mul_one,
      add_sub_cancel_left]
  rw [hsub, map_div₀, div_le_iff₀ hpos]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  exact hzle.trans_eq (by rw [map_mul, mul_comm])
private theorem isOpen_setOf_valuation_le_of_ne_zero {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {r : K} (hr : r ≠ 0) :
    IsOpen {y : K | ValuativeRel.valuation K y ≤ ValuativeRel.valuation K r} := by
  have h := Valuation.isOpen_closedBall (v := ValuativeRel.valuation K)
    (r := (ValuativeRel.valuation K).restrict r) (by simpa using hr)
  simpa using h
end PI.ProdFormulaE
end
end

set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField ValuativeRel
open PI PI.ProdFormulaE
namespace PI.ProdFormulaE
theorem _root_.solution : CardStep := by
  unfold CardStep
  intro F _ _ p K _ _ _ _ ι hι hv a ha t ht
  have hcomp : ∀ x y : F, (ValuativeRel.valuation K) (ι x) ≤ (ValuativeRel.valuation K) (ι y) ↔ p.valuation F x ≤ p.valuation F y := by
    intro x y
    rw [← hv x y]
    exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) (ι x) (ι y)).symm
  have haF : (a : F) ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha
  have htK : (t : K) ≠ 0 := by
    rw [ht]
    exact (map_ne_zero ι).2 haF
  have hdvd : ∀ u w : 𝒪[K], u ∣ w ↔ (ValuativeRel.valuation K) (w : K) ≤ (ValuativeRel.valuation K) (u : K) := fun u w =>
    (Valuation.integer.integers (ValuativeRel.valuation K)).dvd_iff_le
  have hint_r : ∀ x : 𝓞 F, ι (algebraMap (𝓞 F) F x) ∈ 𝒪[K] := by
    intro x
    rw [Valuation.mem_integer_iff]
    have h := (hcomp (algebraMap (𝓞 F) F x) 1).2 (by
      rw [map_one]
      exact p.valuation_le_one x)
    simpa using h
  let ι₀ : 𝓞 F →+* 𝒪[K] := (ι.comp (algebraMap (𝓞 F) F)).codRestrict 𝒪[K] hint_r
  let φ : 𝓞 F →+* 𝒪[K] ⧸ Ideal.span {t} := (Ideal.Quotient.mk _).comp ι₀
  have hker : RingHom.ker φ = p.maxPowDividing (Ideal.span {a}) := by
    ext x
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk (Ideal.span {t}) (ι₀ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hdvd, ht]
    show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x)) ≤ (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F a)) ↔ _
    rw [hcomp, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact intValuation_le_iff_mem_maxPowDividing p x a ha
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hU : IsOpen {y : K | (ValuativeRel.valuation K) (y - s) ≤ (ValuativeRel.valuation K) t} := by
      have hB := isOpen_setOf_valuation_le_of_ne_zero htK
      exact hB.preimage (continuous_sub_right (s : K))
    obtain ⟨f, hf⟩ := hι.exists_mem_open hU ⟨(s : K), by simp⟩
    have hf' : (ValuativeRel.valuation K) (ι f - s) ≤ (ValuativeRel.valuation K) t := hf
    have hfK : (ValuativeRel.valuation K) (ι f) ≤ 1 := by
      have h1 : (ValuativeRel.valuation K) (ι f - s) ≤ 1 := hf'.trans ((Valuation.mem_integer_iff _ _).1 t.2)
      have h2 : (ValuativeRel.valuation K) (s : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 s.2
      simpa using (ValuativeRel.valuation K).map_add_le h1 h2
    have hf1 : p.valuation F f ≤ 1 := by
      have := (hcomp f 1).1 (by simpa using hfK)
      simpa using this
    obtain ⟨x, hx⟩ := exists_valuation_sub_algebraMap_le p hf1 ha
    refine ⟨x, ?_⟩
    show Ideal.Quotient.mk _ (ι₀ x) = Ideal.Quotient.mk _ s
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, hdvd]
    have h3 : (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x) - ι f) ≤ (ValuativeRel.valuation K) t := by
      rw [← map_sub, ht]
      show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x - f)) ≤ (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F a))
      rw [hcomp, ← neg_sub, Valuation.map_neg]
      exact hx
    have h4 : ι (algebraMap (𝓞 F) F x) - (s : K) =
        (ι (algebraMap (𝓞 F) F x) - ι f) + (ι f - s) := by ring
    show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x) - (s : K)) ≤ (ValuativeRel.valuation K) t
    rw [h4]
    exact (ValuativeRel.valuation K).map_add_le h3 hf'
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv.symm
end PI.ProdFormulaE
