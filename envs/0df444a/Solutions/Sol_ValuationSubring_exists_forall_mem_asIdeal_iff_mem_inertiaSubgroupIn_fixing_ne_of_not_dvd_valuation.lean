-- Prove2me | solution 1 for ValuationSubring.exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7d62a20a-b79f-5f21-b84d-8acf555ce410

import Definitions.Def_FLTPrelim_Ramification
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation

open NumberField IsDedekindDomain

set_option autoImplicit false

open NumberField IsDedekindDomain IntermediateField

open scoped Pointwise

namespace WtTF
namespace RB

local notation "ℚ̄" => AlgebraicClosure ℚ

private theorem isAlgebraic_rat_qbar : Algebra.IsAlgebraic ℚ ℚ̄ := by
  constructor
  intro x
  obtain ⟨p, hp0, hp⟩ := (AlgebraicClosure.isAlgebraic (k := ℚ)).isAlgebraic x
  refine ⟨p, hp0, ?_⟩
  rw [Polynomial.aeval_def] at hp ⊢
  have : (algebraMap ℚ ℚ̄) = (AlgebraicClosure.instAlgebra ℚ).algebraMap := by
    refine RingHom.ext fun q => ?_
    rw [eq_ratCast, eq_ratCast]
  rw [this]
  exact hp

private theorem isAlgebraic_over (F : Type*) [Field F] [Algebra ℚ F] [Algebra F ℚ̄]
    [IsScalarTower ℚ F ℚ̄] : Algebra.IsAlgebraic F ℚ̄ := by
  haveI := isAlgebraic_rat_qbar
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) F (A := ℚ̄)

private theorem isGalois_over (F : Type*) [Field F] [Algebra ℚ F] [Algebra F ℚ̄]
    [IsScalarTower ℚ F ℚ̄] : IsGalois F ℚ̄ := by
  haveI ha := isAlgebraic_over F
  haveI : IsAlgClosure F ℚ̄ := ⟨inferInstance, ha⟩
  haveI : Normal F ℚ̄ := IsAlgClosure.normal F ℚ̄
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  haveI : Algebra.IsIntegral F ℚ̄ := ha.isIntegral
  haveI : Algebra.IsSeparable F ℚ̄ := Algebra.IsSeparable.of_integral F ℚ̄
  constructor

private theorem coe_galSmul {F : Type*} [Field F] [Algebra F ℚ̄] (g : ℚ̄ ≃ₐ[F] ℚ̄) (b : 𝓞 ℚ̄) :
    ((g • b : 𝓞 ℚ̄) : ℚ̄) = g (b : ℚ̄) := rfl

private theorem coe_ringOfIntegersMap {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ F₂] (c : 𝓞 F₁) :
    ((algebraMap (𝓞 F₁) (𝓞 F₂) c : 𝓞 F₂) : F₂) = algebraMap F₁ F₂ (c : F₁) := by
  rw [show ((algebraMap (𝓞 F₁) (𝓞 F₂) c : 𝓞 F₂) : F₂) =
      algebraMap (𝓞 F₂) F₂ (algebraMap (𝓞 F₁) (𝓞 F₂) c) from rfl,
    ← IsScalarTower.algebraMap_apply (𝓞 F₁) (𝓞 F₂) F₂,
    IsScalarTower.algebraMap_apply (𝓞 F₁) F₁ F₂]

private theorem galSmul_ringOfIntegersMap {F : Type*} [Field F] [Algebra F ℚ̄] (g : ℚ̄ ≃ₐ[F] ℚ̄)
    (c : 𝓞 F) :
    g • algebraMap (𝓞 F) (𝓞 ℚ̄) c = algebraMap (𝓞 F) (𝓞 ℚ̄) c := by
  apply NumberField.RingOfIntegers.ext
  rw [coe_galSmul, coe_ringOfIntegersMap c]
  exact g.commutes (c : F)

private scoped instance smulCommClass_gal {F : Type*} [Field F] [Algebra F ℚ̄] :
    SMulCommClass (ℚ̄ ≃ₐ[F] ℚ̄) (𝓞 F) (𝓞 ℚ̄) := by
  constructor
  intro g a b
  apply NumberField.RingOfIntegers.ext
  have hcoe : ∀ z : 𝓞 ℚ̄, ∀ c : 𝓞 F,
      ((c • z : 𝓞 ℚ̄) : ℚ̄) = algebraMap F ℚ̄ (c : F) * (z : ℚ̄) := by
    intro z c
    rw [Algebra.smul_def,
      show ((algebraMap (𝓞 F) (𝓞 ℚ̄) c * z : 𝓞 ℚ̄) : ℚ̄) =
        algebraMap (𝓞 ℚ̄) ℚ̄ (algebraMap (𝓞 F) (𝓞 ℚ̄) c) * algebraMap (𝓞 ℚ̄) ℚ̄ z from
      map_mul (algebraMap (𝓞 ℚ̄) ℚ̄) _ _,
      show algebraMap (𝓞 ℚ̄) ℚ̄ (algebraMap (𝓞 F) (𝓞 ℚ̄) c) = algebraMap F ℚ̄ (c : F) from
      coe_ringOfIntegersMap c]
  rw [coe_galSmul, hcoe, hcoe, map_mul, coe_galSmul]
  congr 1
  exact g.commutes (a : F)

private theorem isInvariant_gal (F : Type*) [Field F] [Algebra ℚ F] [Algebra F ℚ̄]
    [IsScalarTower ℚ F ℚ̄] :
    Algebra.IsInvariant (𝓞 F) (𝓞 ℚ̄) (ℚ̄ ≃ₐ[F] ℚ̄) := by
  haveI := isGalois_over F
  constructor
  intro b hb
  have hmem : (b : ℚ̄) ∈ (⊥ : IntermediateField F ℚ̄) := by
    rw [InfiniteGalois.mem_bot_iff_fixed]
    intro f
    have := congrArg (fun z : 𝓞 ℚ̄ => (z : ℚ̄)) (hb f)
    simpa [coe_galSmul] using this
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  have hbint : IsIntegral ℤ (b : ℚ̄) := NumberField.RingOfIntegers.isIntegral_coe b
  have hcint : IsIntegral ℤ c := by
    obtain ⟨p, hmonic, hroot⟩ := hbint
    refine ⟨p, hmonic, ?_⟩
    apply (algebraMap F ℚ̄).injective
    have hcomp : (algebraMap F ℚ̄).comp (algebraMap ℤ F) = algebraMap ℤ ℚ̄ :=
      RingHom.ext fun n => by
        rw [RingHom.comp_apply, eq_intCast, eq_intCast, map_intCast]
    rw [map_zero, ← hroot, ← hc, Polynomial.hom_eval₂, hcomp]
  refine ⟨⟨c, hcint⟩, ?_⟩
  apply NumberField.RingOfIntegers.ext
  rw [coe_ringOfIntegersMap (⟨c, hcint⟩ : 𝓞 F)]
  exact hc

private theorem continuousSMul_gal (F : Type*) [Field F] [Algebra ℚ F] [Algebra F ℚ̄]
    [IsScalarTower ℚ F ℚ̄] :
    letI : TopologicalSpace (𝓞 ℚ̄) := ⊥
    ContinuousSMul (ℚ̄ ≃ₐ[F] ℚ̄) (𝓞 ℚ̄) := by
  letI : TopologicalSpace (𝓞 ℚ̄) := ⊥
  haveI : DiscreteTopology (𝓞 ℚ̄) := ⟨rfl⟩
  haveI := (isAlgebraic_over F).isIntegral
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro b
  have hstab : MulAction.stabilizer (ℚ̄ ≃ₐ[F] ℚ̄) b =
      MulAction.stabilizer (ℚ̄ ≃ₐ[F] ℚ̄) (b : ℚ̄) := by
    ext g
    simp only [MulAction.mem_stabilizer_iff]
    rw [NumberField.RingOfIntegers.ext_iff, coe_galSmul]
    rfl
  rw [hstab]
  exact stabilizer_isOpen_of_isIntegral (K := F) (L := ℚ̄) (b : ℚ̄)

private theorem exists_gal_smul_of_under_eq (F : Type*) [Field F] [Algebra ℚ F] [Algebra F ℚ̄]
    [IsScalarTower ℚ F ℚ̄] (𝔓 Q : Ideal (𝓞 ℚ̄)) [𝔓.IsPrime] [Q.IsPrime]
    (h : 𝔓.under (𝓞 F) = Q.under (𝓞 F)) : ∃ g : ℚ̄ ≃ₐ[F] ℚ̄, Q = g • 𝔓 := by
  haveI := isGalois_over F
  haveI := isInvariant_gal F
  letI : TopologicalSpace (𝓞 ℚ̄) := ⊥
  haveI : DiscreteTopology (𝓞 ℚ̄) := ⟨rfl⟩
  haveI := continuousSMul_gal F
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := 𝓞 F) (B := 𝓞 ℚ̄) (G := ℚ̄ ≃ₐ[F] ℚ̄) 𝔓 Q h

private theorem stabilizerHom_surjective_gal (F : Type*) [Field F] [Algebra ℚ F] [Algebra F ℚ̄]
    [IsScalarTower ℚ F ℚ̄] (w : Ideal (𝓞 F)) (𝔓 : Ideal (𝓞 ℚ̄)) [𝔓.IsPrime] [𝔓.LiesOver w] :
    Function.Surjective (Ideal.Quotient.stabilizerHom 𝔓 w (ℚ̄ ≃ₐ[F] ℚ̄)) := by
  haveI := isGalois_over F
  haveI := isInvariant_gal F
  letI : TopologicalSpace (𝓞 ℚ̄) := ⊥
  haveI : DiscreteTopology (𝓞 ℚ̄) := ⟨rfl⟩
  haveI := continuousSMul_gal F
  exact Ideal.Quotient.stabilizerHom_surjective_of_profinite w 𝔓

private theorem multiplicity_pow' {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    [UniqueFactorizationMonoid α] {p x : α} (hp : Prime p) (hx : x ≠ 0) (m : ℕ) :
    multiplicity p (x ^ m) = m * multiplicity p x := by
  induction m with
  | zero =>
      simp [multiplicity_eq_zero.mpr
        (fun h => hp.not_unit (isUnit_of_dvd_one (by simpa using h)))]
  | succ k ih =>
      rw [pow_succ, multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
        (mul_ne_zero (pow_ne_zero _ hx) hx)), ih]
      ring

private theorem multiplicity_map_span_eq {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] (hinj : Function.Injective (algebraMap R S))
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S)
    (hvw : w.asIdeal.under R = v.asIdeal) {a : R} (ha : a ≠ 0) :
    multiplicity w.asIdeal (Ideal.span {algebraMap R S a}) =
      multiplicity v.asIdeal (Ideal.span {a}) *
        multiplicity w.asIdeal (Ideal.map (algebraMap R S) v.asIdeal) := by
  set m := multiplicity v.asIdeal (Ideal.span {a}) with hm
  have hspan : Ideal.span {a} ≠ (⊥ : Ideal R) := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  obtain ⟨J, hJ⟩ := pow_multiplicity_dvd v.asIdeal (Ideal.span {a})
  have hJ0 : J ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hJ
    exact hspan hJ
  have hJv : ¬ v.asIdeal ∣ J := by
    intro hdvd
    have hpow : v.asIdeal ^ (m + 1) ∣ Ideal.span {a} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ hdvd
    exact (FiniteMultiplicity.of_prime_left v.prime hspan).not_pow_dvd_of_multiplicity_lt
      (Nat.lt_succ_self m) hpow
  have hmap : Ideal.span {algebraMap R S a} =
      (Ideal.map (algebraMap R S) v.asIdeal) ^ m * Ideal.map (algebraMap R S) J := by
    rw [← Ideal.map_pow, ← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton]
  have hmapv_ne : Ideal.map (algebraMap R S) v.asIdeal ≠ ⊥ := fun h =>
    v.ne_bot ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  have hmapJ_ne : Ideal.map (algebraMap R S) J ≠ ⊥ := fun h =>
    hJ0 ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  have hwJ : ¬ w.asIdeal ∣ Ideal.map (algebraMap R S) J := by
    intro hdvd
    apply hJv
    rw [Ideal.dvd_iff_le] at hdvd ⊢
    rw [← hvw]
    calc J ≤ (Ideal.map (algebraMap R S) J).comap (algebraMap R S) := Ideal.le_comap_map
    _ ≤ w.asIdeal.comap (algebraMap R S) := Ideal.comap_mono hdvd
  have hprod_ne : (Ideal.map (algebraMap R S) v.asIdeal) ^ m * Ideal.map (algebraMap R S) J ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hmapv_ne) hmapJ_ne
  rw [hmap, multiplicity_mul w.prime (FiniteMultiplicity.of_prime_left w.prime hprod_ne),
    multiplicity_pow' w.prime hmapv_ne m, multiplicity_eq_zero.mpr hwJ, add_zero, mul_comm]

private theorem ringOfIntegersMap_injective {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ F₂] :
    Function.Injective (algebraMap (𝓞 F₁) (𝓞 F₂)) := by
  intro u₁ u₂ h
  apply NumberField.RingOfIntegers.ext
  apply (algebraMap F₁ F₂).injective
  rw [← coe_ringOfIntegersMap (F₂ := F₂) u₁, ← coe_ringOfIntegersMap (F₂ := F₂) u₂, h]

private theorem valuation_map_integer {F₁ F₂ : Type*} [Field F₁] [NumberField F₁] [Field F₂]
    [NumberField F₂] [Algebra F₁ F₂] (v : HeightOneSpectrum (𝓞 F₁))
    (w : HeightOneSpectrum (𝓞 F₂)) (hvw : w.asIdeal.under (𝓞 F₁) = v.asIdeal)
    {r : 𝓞 F₁} (hr : r ≠ 0) :
    w.valuation F₂ (algebraMap F₁ F₂ (r : F₁)) =
      WithZero.exp (-((multiplicity v.asIdeal (Ideal.span {r}) *
        multiplicity w.asIdeal (Ideal.map (algebraMap (𝓞 F₁) (𝓞 F₂)) v.asIdeal) : ℕ) : ℤ)) := by
  have hinj : Function.Injective (algebraMap (𝓞 F₁) (𝓞 F₂)) := ringOfIntegersMap_injective
  have hmapr : algebraMap F₁ F₂ (r : F₁) = ((algebraMap (𝓞 F₁) (𝓞 F₂) r : 𝓞 F₂) : F₂) :=
    (coe_ringOfIntegersMap r).symm
  have hr₂ : algebraMap (𝓞 F₁) (𝓞 F₂) r ≠ 0 := fun h => hr (hinj (by rw [h, map_zero]))
  rw [hmapr, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hr₂,
    multiplicity_map_span_eq hinj v w hvw hr]

private theorem valuation_unit_eq_exp {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    v.valuation K (x : K) = WithZero.exp (Multiplicative.toAdd (v.valuationOfNeZero x)) := by
  rw [← IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
  rfl

private theorem p0_dvd_multiplicity_map {F₁ F₂ : Type*} [Field F₁] [NumberField F₁] [Field F₂]
    [NumberField F₂] [Algebra F₁ F₂] (p₀ : ℕ) (hp₀ : p₀.Prime) (x : F₁ˣ)
    (v : HeightOneSpectrum (𝓞 F₁))
    (hv : ¬ ((p₀ : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)))
    (yt : F₂) (hyt : yt ^ p₀ = algebraMap F₁ F₂ (x : F₁))
    (w : HeightOneSpectrum (𝓞 F₂)) (hvw : w.asIdeal.under (𝓞 F₁) = v.asIdeal) :
    p₀ ∣ multiplicity w.asIdeal (Ideal.map (algebraMap (𝓞 F₁) (𝓞 F₂)) v.asIdeal) := by
  set n : ℤ := Multiplicative.toAdd (v.valuationOfNeZero x) with hn
  set e : ℕ := multiplicity w.asIdeal (Ideal.map (algebraMap (𝓞 F₁) (𝓞 F₂)) v.asIdeal) with he

  obtain ⟨a, s, hs, hfrac⟩ := IsFractionRing.div_surjective (A := 𝓞 F₁) (x : F₁)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap (𝓞 F₁) F₁ s ≠ 0 := fun h => hs0 ((map_eq_zero_iff _
    (NumberField.RingOfIntegers.coe_injective)).mp h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hfrac
    exact x.ne_zero hfrac.symm
  set ma : ℕ := multiplicity v.asIdeal (Ideal.span {a}) with hma
  set ms : ℕ := multiplicity v.asIdeal (Ideal.span {s}) with hms

  have hE1 : WithZero.exp n = WithZero.exp ((ms : ℤ) - (ma : ℤ)) := by
    rw [← valuation_unit_eq_exp v x, ← hfrac, map_div₀,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ ha0,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hs0,
      ← WithZero.exp_sub]
    rw [hma, hms]
    congr 1
    ring
  have hnval : n = (ms : ℤ) - (ma : ℤ) := WithZero.exp_inj.mp hE1

  have hx2 : w.valuation F₂ (algebraMap F₁ F₂ (x : F₁)) = WithZero.exp (n * e) := by
    rw [← hfrac, map_div₀, map_div₀, valuation_map_integer v w hvw ha0,
      valuation_map_integer v w hvw hs0, ← WithZero.exp_sub]
    congr 1
    push_cast
    rw [hnval]
    ring

  have hy0 : yt ≠ 0 := by
    rintro rfl
    rw [zero_pow hp₀.ne_zero] at hyt
    exact x.ne_zero ((map_eq_zero_iff _ (algebraMap F₁ F₂).injective).mp hyt.symm)
  have hyval : w.valuation F₂ yt ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hyval
  have hy2 : w.valuation F₂ (algebraMap F₁ F₂ (x : F₁)) =
      WithZero.exp (p₀ * Multiplicative.toAdd u) := by
    have hupow : u ^ p₀ = Multiplicative.ofAdd ((p₀ : ℤ) * Multiplicative.toAdd u) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, nsmul_eq_mul, toAdd_ofAdd]
    rw [← hyt, map_pow, ← hu, ← WithZero.coe_pow, hupow]
    rfl

  have hkey : n * (e : ℤ) = (p₀ : ℤ) * Multiplicative.toAdd u :=
    WithZero.exp_inj.mp (hx2.symm.trans hy2)
  have hdvd : (p₀ : ℤ) ∣ n * (e : ℤ) := Dvd.intro _ hkey.symm
  rcases (Int.Prime.dvd_mul' (by exact_mod_cast hp₀) hdvd) with h | h
  · exact absurd h hv
  · exact_mod_cast h

private theorem multiplicity_map_eq_ramificationIdx {R S : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum S) :
    multiplicity w.asIdeal (Ideal.map (algebraMap R S) v.asIdeal) =
      Ideal.ramificationIdx' v.asIdeal w.asIdeal := by
  have hmapv_ne : Ideal.map (algebraMap R S) v.asIdeal ≠ ⊥ := fun h =>
    v.ne_bot ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_factors_count hmapv_ne w.isPrime w.ne_bot,
    UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
      w.prime.irreducible hmapv_ne,
    normalize_eq]

private theorem finset_sum_squeeze {ι : Type*} {W : Finset ι} {t : ι → ℕ} {p₀ : ℕ} (hp : 0 < p₀)
    (w₀ : ι) (hw₀ : w₀ ∈ W) (hsum : ∑ w ∈ W, t w = p₀) (hlow : ∀ w ∈ W, p₀ ≤ t w) :
    W = {w₀} ∧ t w₀ = p₀ := by
  have h1 : W.card • p₀ ≤ p₀ := by
    calc W.card • p₀ ≤ ∑ w ∈ W, t w := Finset.card_nsmul_le_sum W t p₀ hlow
    _ = p₀ := hsum
  rw [smul_eq_mul] at h1
  have hcard1 : W.card ≤ 1 := by
    by_contra h
    push Not at h
    have : 2 * p₀ ≤ W.card * p₀ := Nat.mul_le_mul_right p₀ h
    omega
  have hcard : W.card = 1 := le_antisymm hcard1 (Finset.card_pos.mpr ⟨w₀, hw₀⟩)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have haw : a = w₀ := by
    have := hw₀
    rw [ha, Finset.mem_singleton] at this
    exact this.symm
  subst haw
  refine ⟨ha, ?_⟩
  rw [ha, Finset.sum_singleton] at hsum
  exact hsum

private theorem residue_surjective_of_inertiaDeg_eq_one {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (p : Ideal A) (P : Ideal B) [p.IsMaximal] [P.IsPrime] [P.LiesOver p]
    (hf : Ideal.inertiaDeg' p P = 1) :
    Function.Surjective (algebraMap (A ⧸ p) (B ⧸ P)) := by
  rw [Ideal.inertiaDeg_algebraMap] at hf
  intro b
  letI F : Field (A ⧸ p) := Ideal.Quotient.field p
  haveI : Nontrivial (B ⧸ P) := Ideal.Quotient.nontrivial_of_liesOver_of_isPrime P p
  obtain ⟨c, hc⟩ := (@finrank_eq_one_iff_of_nonzero' (A ⧸ p) (B ⧸ P) F.toDivisionRing
      inferInstance Algebra.toModule (1 : B ⧸ P) one_ne_zero).mp hf b
  exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩

private theorem exists_second_root (M : IntermediateField ℚ ℚ̄) (y : ℚ̄) (hyi : IsIntegral (↥M) y)
    (hd : 1 < (minpoly (↥M) y).natDegree) :
    ∃ y₁ : ℚ̄, Polynomial.aeval y₁ (minpoly (↥M) y) = 0 ∧ y₁ ≠ y := by
  have hsep : (minpoly (↥M) y).Separable := (minpoly.irreducible hyi).separable
  have hnodup : ((minpoly (↥M) y).aroots ℚ̄).Nodup :=
    Polynomial.nodup_roots (Polynomial.Separable.map hsep)
  have hycard : 1 < ((minpoly (↥M) y).aroots ℚ̄).toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hnodup,
      IsAlgClosed.card_aroots_eq_natDegree (A := ↥M) (B := ℚ̄)]
    exact hd
  have hex : ∃ y₁ ∈ ((minpoly (↥M) y).aroots ℚ̄).toFinset, y₁ ≠ y := by
    by_contra h
    push Not at h
    have hle : ((minpoly (↥M) y).aroots ℚ̄).toFinset.card ≤ 1 :=
      Finset.card_le_one.mpr (fun a ha b hb => (h a ha).trans (h b hb).symm)
    omega
  obtain ⟨y₁, hy₁mem, hy₁ne⟩ := hex
  refine ⟨y₁, ?_, hy₁ne⟩
  exact (Polynomial.mem_aroots.mp (Multiset.mem_toFinset.mp hy₁mem)).2

private theorem exists_algEquiv_map_root (M : IntermediateField ℚ ℚ̄) (y y₁ : ℚ̄)
    (hy₁ : Polynomial.aeval y₁ (minpoly (↥M) y) = 0) : ∃ σ : ℚ̄ ≃ₐ[↥M] ℚ̄, σ y = y₁ := by
  have ha := isAlgebraic_over (↥M)
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_adjoin_splits_of_aeval
    (F := ↥M) (E := ℚ̄) (K := ℚ̄) (S := Set.univ)
    (fun s _ => ⟨(ha.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩)
    (IntermediateField.adjoin_univ (↥M) ℚ̄) hy₁
  exact ⟨(Algebra.IsAlgebraic.algEquivEquivAlgHom (↥M) ℚ̄).symm φ, hφ⟩

private scoped instance isFractionRing_ringOfIntegers_qbar : IsFractionRing (𝓞 ℚ̄) ℚ̄ := by
  haveI : Algebra.IsAlgebraic (𝓞 ℚ) ℚ̄ :=
    (IsFractionRing.comap_isAlgebraic_iff (A := 𝓞 ℚ) (K := ℚ) (C := ℚ̄)).mpr
      isAlgebraic_rat_qbar
  exact IsIntegralClosure.isFractionRing_of_algebraic (A := 𝓞 ℚ) (C := 𝓞 ℚ̄)
    (fun x hx => by
      rw [IsScalarTower.algebraMap_apply (𝓞 ℚ) ℚ ℚ̄] at hx
      have h2 : algebraMap (𝓞 ℚ) ℚ x = 0 :=
        (map_eq_zero_iff _ (algebraMap ℚ ℚ̄).injective).mp hx
      exact NumberField.RingOfIntegers.coe_injective (by rw [h2, map_zero]))

private theorem mem_or_inv_mem_loc (𝔓 : Ideal (𝓞 ℚ̄)) [hP : 𝔓.IsPrime] (hbot : 𝔓 ≠ ⊥) (α : ℚ̄) :
    (∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α = (a : ℚ̄) * (s : ℚ̄)⁻¹) ∨
    (∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α⁻¹ = (a : ℚ̄) * (s : ℚ̄)⁻¹) := by
  classical
  haveI := isAlgebraic_rat_qbar
  set K₀ : IntermediateField ℚ ℚ̄ := ℚ⟮α⟯ with hK₀
  have hαK : α ∈ K₀ := IntermediateField.mem_adjoin_simple_self ℚ α
  have hαint : IsIntegral ℚ α := (isAlgebraic_rat_qbar.isAlgebraic α).isIntegral
  haveI : FiniteDimensional ℚ (↥K₀) := IntermediateField.adjoin.finiteDimensional hαint
  haveI : NumberField (↥K₀) := NumberField.of_module_finite ℚ (↥K₀)
  set 𝔭 : Ideal (𝓞 K₀) := 𝔓.under (𝓞 K₀) with h𝔭
  haveI h𝔭p : 𝔭.IsPrime := Ideal.IsPrime.under (𝓞 K₀) 𝔓
  obtain ⟨b, hb𝔓, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have h𝔭bot : 𝔭 ≠ ⊥ := by
    apply Ideal.comap_ne_bot_of_algebraic_mem hb0 hb𝔓
    exact (Algebra.IsIntegral.isIntegral (R := 𝓞 K₀) b).isAlgebraic
  haveI h𝔭max : 𝔭.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔭bot h𝔭p
  set Loc : Subalgebra (𝓞 K₀) (↥K₀) :=
    Localization.subalgebra.ofField (↥K₀) 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors with hLoc
  haveI : IsLocalization.AtPrime ↥Loc 𝔭 :=
    Localization.subalgebra.isLocalization_ofField (↥K₀) 𝔭.primeCompl
      𝔭.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing ↥Loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₀) h𝔭bot ↥Loc
  haveI : ValuationRing ↥Loc := inferInstance
  haveI : IsFractionRing ↥Loc (↥K₀) :=
    Localization.subalgebra.isFractionRing_ofField (↥K₀) 𝔭.primeCompl
      𝔭.primeCompl_le_nonZeroDivisors
  set α' : ↥K₀ := ⟨α, hαK⟩ with hα'
  have transfer : ∀ β : ↥K₀, IsLocalization.IsInteger ↥Loc β →
      ∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ (β : ℚ̄) = (a : ℚ̄) * (s : ℚ̄)⁻¹ := by
    rintro β ⟨l, hl⟩
    obtain ⟨a, s, hs, hfrac⟩ := l.2
    refine ⟨algebraMap (𝓞 K₀) (𝓞 ℚ̄) a, algebraMap (𝓞 K₀) (𝓞 ℚ̄) s, ?_, ?_⟩
    · intro hmem
      exact hs (Ideal.mem_comap.mpr hmem)
    · have hβ : (β : ℚ̄) = algebraMap (↥K₀) ℚ̄ β := rfl
      have hlval : (l : ↥K₀) = β := hl
      rw [hβ, ← hlval, hfrac, map_mul, map_inv₀,
        coe_ringOfIntegersMap (F₂ := ℚ̄) a, coe_ringOfIntegersMap (F₂ := ℚ̄) s]
  rcases ValuationRing.isInteger_or_isInteger ↥Loc α' with h | h
  · exact Or.inl (transfer α' h)
  · obtain ⟨a, s, hs, heq⟩ := transfer α'⁻¹ h
    refine Or.inr ⟨a, s, hs, ?_⟩
    rw [← heq]
    rfl

private theorem coe_ne_zero_of_notMem {𝔓 : Ideal (𝓞 ℚ̄)} {s : 𝓞 ℚ̄} (hs : s ∉ 𝔓) : (s : ℚ̄) ≠ 0 := by
  intro h
  have hs0 : s = 0 := NumberField.RingOfIntegers.coe_injective (h.trans (map_zero _).symm)
  exact hs (hs0 ▸ 𝔓.zero_mem)

private def placeAt (𝔓 : Ideal (𝓞 ℚ̄)) [hP : 𝔓.IsPrime] (hbot : 𝔓 ≠ ⊥) : ValuationSubring ℚ̄ where
  carrier := {α : ℚ̄ | ∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α = (a : ℚ̄) * (s : ℚ̄)⁻¹}
  one_mem' := ⟨1, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one 𝔓).mpr h), by
    rw [show ((1 : 𝓞 ℚ̄) : ℚ̄) = 1 from map_one _, inv_one, mul_one]⟩
  zero_mem' := ⟨0, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one 𝔓).mpr h), by
    rw [show ((0 : 𝓞 ℚ̄) : ℚ̄) = 0 from map_zero _, zero_mul]⟩
  mul_mem' := by
    rintro x y ⟨a, s, hs, rfl⟩ ⟨b, t, ht, rfl⟩
    refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    rw [mul_inv]
    ring
  add_mem' := by
    rintro x y ⟨a, s, hs, rfl⟩ ⟨b, t, ht, rfl⟩
    have hsne := coe_ne_zero_of_notMem hs
    have htne := coe_ne_zero_of_notMem ht
    refine ⟨a * t + s * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, div_add_div _ _ hsne htne]
  neg_mem' := by
    rintro x ⟨a, s, hs, rfl⟩
    refine ⟨-a, s, hs, ?_⟩
    push_cast
    ring
  mem_or_inv_mem' := fun α => by
    rcases mem_or_inv_mem_loc 𝔓 hbot α with ⟨a, s, hs, heq⟩ | ⟨a, s, hs, heq⟩
    · exact Or.inl ⟨a, s, hs, heq⟩
    · exact Or.inr ⟨a, s, hs, heq⟩

private theorem mem_placeAt {𝔓 : Ideal (𝓞 ℚ̄)} [𝔓.IsPrime] {hbot : 𝔓 ≠ ⊥} {α : ℚ̄} :
    α ∈ placeAt 𝔓 hbot ↔ ∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α = (a : ℚ̄) * (s : ℚ̄)⁻¹ :=
  Iff.rfl

private theorem smul_ideal_congr {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    [MulSemiringAction G₁ (𝓞 ℚ̄)] [MulSemiringAction G₂ (𝓞 ℚ̄)] (g₁ : G₁) (g₂ : G₂)
    (h : ∀ b : 𝓞 ℚ̄, g₁⁻¹ • b = g₂⁻¹ • b) (I : Ideal (𝓞 ℚ̄)) : g₁ • I = g₂ • I := by
  have hsymm₁ : ∀ z : 𝓞 ℚ̄, (MulSemiringAction.toRingAut G₁ (𝓞 ℚ̄) g₁).symm z = g₁⁻¹ • z := by
    intro z
    rw [RingEquiv.symm_apply_eq]
    show z = g₁ • g₁⁻¹ • z
    rw [smul_inv_smul]
  have hsymm₂ : ∀ z : 𝓞 ℚ̄, (MulSemiringAction.toRingAut G₂ (𝓞 ℚ̄) g₂).symm z = g₂⁻¹ • z := by
    intro z
    rw [RingEquiv.symm_apply_eq]
    show z = g₂ • g₂⁻¹ • z
    rw [smul_inv_smul]
  ext z
  rw [Ideal.pointwise_smul_eq_comap, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap,
    Ideal.mem_comap]
  rw [show ((MulSemiringAction.toRingAut G₁ (𝓞 ℚ̄) g₁).symm : 𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) z = g₁⁻¹ • z from
      hsymm₁ z,
    show ((MulSemiringAction.toRingAut G₂ (𝓞 ℚ̄) g₂).symm : 𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) z = g₂⁻¹ • z from
      hsymm₂ z,
    h z]

private theorem gal_fix_of_mem_range {F : Type*} [Field F] [Algebra F ℚ̄] (g : ℚ̄ ≃ₐ[F] ℚ̄) {w : ℚ̄}
    (hw : w ∈ Set.range (algebraMap F ℚ̄)) : g w = w := by
  obtain ⟨w', rfl⟩ := hw
  exact g.commutes w'

private theorem mem_iff_valuation_lt_one (𝔓 : Ideal (𝓞 ℚ̄)) [𝔓.IsPrime] (P : ValuationSubring ℚ̄)
    (hPmem : ∀ α : ℚ̄, α ∈ P ↔ ∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α = (a : ℚ̄) * (s : ℚ̄)⁻¹)
    (w : 𝓞 ℚ̄) : w ∈ 𝔓 ↔ P.valuation (w : ℚ̄) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
  constructor
  · intro hw
    by_cases hw0 : (w : ℚ̄) = 0
    · exact Or.inl hw0
    · right
      intro hinv
      obtain ⟨a, s, hs, heq⟩ := (hPmem _).mp hinv
      have hsne : (s : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem hs
      have h2 : (s : ℚ̄) = (w : ℚ̄) * a := by
        calc (s : ℚ̄) = (w : ℚ̄) * ((w : ℚ̄)⁻¹ * s) := by rw [mul_inv_cancel_left₀ hw0]
          _ = (w : ℚ̄) * ((a : ℚ̄) * (s : ℚ̄)⁻¹ * s) := by rw [← heq]
          _ = (w : ℚ̄) * a := by rw [inv_mul_cancel_right₀ hsne]
      have h3 : s = w * a := by
        apply NumberField.RingOfIntegers.coe_injective
        rw [map_mul]
        exact h2
      exact hs (h3 ▸ Ideal.mul_mem_right a 𝔓 hw)
  · rintro (hw0 | hinv)
    · have hw : w = 0 := NumberField.RingOfIntegers.coe_injective (hw0.trans (map_zero _).symm)
      rw [hw]
      exact 𝔓.zero_mem
    · by_contra hw
      apply hinv
      exact (hPmem _).mpr ⟨1, w, hw, by
        rw [show ((1 : 𝓞 ℚ̄) : ℚ̄) = 1 from map_one _, one_mul]⟩

private theorem pin_of_under_eq (L' : IntermediateField ℚ ℚ̄) [NumberField L']
    (v : HeightOneSpectrum (𝓞 L')) (𝔓 : Ideal (𝓞 ℚ̄)) [𝔓.IsPrime]
    (h𝔓L' : 𝔓.under (𝓞 L') = v.asIdeal) (P : ValuationSubring ℚ̄)
    (hPmem : ∀ α : ℚ̄, α ∈ P ↔ ∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α = (a : ℚ̄) * (s : ℚ̄)⁻¹) :
    ∀ z : 𝓞 L', z ∈ v.asIdeal ↔ P.valuation (algebraMap L' ℚ̄ z) < 1 := by
  intro z
  rw [← h𝔓L', ← coe_ringOfIntegersMap (F₂ := ℚ̄) z]
  exact mem_iff_valuation_lt_one 𝔓 P hPmem (algebraMap (𝓞 L') (𝓞 ℚ̄) z)

end RB
p2m_reactivate "P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF.RB"

local notation "ℚ̄" => AlgebraicClosure ℚ

set_option maxHeartbeats 6400000 in
open RB in

private theorem exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd
    (L' : IntermediateField ℚ ℚ̄) [NumberField L']
    (p₀ : ℕ) (hp₀ : p₀.Prime) (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (hv : ¬ ((p₀ : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)))
    (y : ℚ̄) (hy : y ^ p₀ = ((x : L') : ℚ̄)) :
    ∃ P : ValuationSubring ℚ̄, P.LiesOverPrime q ∧
      (∀ z : 𝓞 L', z ∈ v.asIdeal ↔ P.valuation (algebraMap L' (AlgebraicClosure ℚ) z) < 1) ∧
      ∃ σ ∈ P.inertiaSubgroupIn ℚ, (∀ z : L', σ z = z) ∧ σ y ≠ y := by
  classical
  haveI := isAlgebraic_rat_qbar

  have hcoL : ∀ z : ↥L', (z : ℚ̄) = algebraMap (↥L') ℚ̄ z := fun z => rfl
  have hx0 : ((x : ↥L') : ℚ̄) ≠ 0 := by
    rw [hcoL]
    exact (map_ne_zero_iff _ (algebraMap (↥L') ℚ̄).injective).mpr x.ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hp₀.ne_zero] at hy
    exact hx0 hy.symm
  have haval : Polynomial.aeval y (Polynomial.X ^ p₀ - Polynomial.C (x : ↥L')) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hy, hcoL, sub_self]
  have hyint : IsIntegral (↥L') y := by
    refine ⟨Polynomial.X ^ p₀ - Polynomial.C (x : ↥L'),
      Polynomial.monic_X_pow_sub_C _ hp₀.ne_zero, ?_⟩
    rw [← Polynomial.aeval_def]
    exact haval
  set L'' : IntermediateField (↥L') ℚ̄ := (↥L')⟮y⟯ with hL''def
  haveI : FiniteDimensional (↥L') ↥L'' := IntermediateField.adjoin.finiteDimensional hyint
  haveI : NumberField ↥L'' := NumberField.of_module_finite (↥L') ↥L''
  have hyL'' : y ∈ L'' := IntermediateField.mem_adjoin_simple_self (↥L') y
  obtain ⟨yt, hytcoe⟩ : ∃ yt : ↥L'', (yt : ℚ̄) = y := ⟨⟨y, hyL''⟩, rfl⟩
  have hcoL'' : ∀ z : ↥L'', (z : ℚ̄) = algebraMap (↥L'') ℚ̄ z := fun z => rfl
  have hytpow : yt ^ p₀ = algebraMap (↥L') (↥L'') (x : ↥L') := by
    have h1 : ((yt ^ p₀ : ↥L'') : ℚ̄) = ((algebraMap (↥L') (↥L'') (x : ↥L') : ↥L'') : ℚ̄) := by
      rw [SubmonoidClass.coe_pow, hytcoe, hy, hcoL,
        IsScalarTower.algebraMap_apply (↥L') (↥L'') ℚ̄]
      rfl
    exact Subtype.coe_injective h1

  have hd_eq : Module.finrank (↥L') ↥L'' = (minpoly (↥L') y).natDegree :=
    IntermediateField.adjoin.finrank hyint
  have hd_le : Module.finrank (↥L') ↥L'' ≤ p₀ := by
    rw [hd_eq]
    have hdvd : minpoly (↥L') y ∣ Polynomial.X ^ p₀ - Polynomial.C (x : ↥L') :=
      minpoly.dvd _ _ haval
    calc (minpoly (↥L') y).natDegree
        ≤ (Polynomial.X ^ p₀ - Polynomial.C (x : ↥L')).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd (Polynomial.monic_X_pow_sub_C _ hp₀.ne_zero).ne_zero
      _ = p₀ := Polynomial.natDegree_X_pow_sub_C

  have hvbot : v.asIdeal ≠ ⊥ := v.ne_bot
  haveI : v.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hvbot v.isPrime
  haveI : Module.Finite (𝓞 L') (𝓞 ↥L'') :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 L') (𝓞 ↥L'')
  haveI : Algebra.IsIntegral (𝓞 L') (𝓞 ↥L'') := Algebra.IsIntegral.of_finite _ _

  obtain ⟨Q₁, -, hQ₁prime, hQ₁comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 ↥L''))
      (by rw [Ideal.comap_bot_of_injective _ ringOfIntegersMap_injective]; exact bot_le)
  haveI := hQ₁prime
  haveI hQ₁lies : Q₁.LiesOver v.asIdeal := ⟨hQ₁comap.symm⟩
  have hQ₁bot : Q₁ ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hvbot Q₁
  set w₁ : HeightOneSpectrum (𝓞 ↥L'') := ⟨Q₁, hQ₁prime, hQ₁bot⟩ with hw₁def

  set W : Finset (Ideal (𝓞 ↥L'')) := IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 ↥L'')
    with hWdef
  have hmemW : ∀ u : Ideal (𝓞 ↥L''), u ∈ W ↔ u.IsPrime ∧ u.LiesOver v.asIdeal := by
    intro u
    rw [hWdef, IsDedekindDomain.mem_primesOverFinset_iff hvbot]
    exact Iff.rfl
  have hw₁W : w₁.asIdeal ∈ W := (hmemW _).mpr ⟨hQ₁prime, hQ₁lies⟩
  have hinj : Function.Injective (algebraMap (𝓞 L') (𝓞 ↥L'')) := ringOfIntegersMap_injective

  have hlow : ∀ u ∈ W, p₀ ≤ Ideal.ramificationIdx' v.asIdeal u * Ideal.inertiaDeg' v.asIdeal u := by
    intro u huW
    obtain ⟨hup, hul⟩ := (hmemW u).mp huW
    haveI := hup
    haveI := hul
    have hubot : u ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hvbot u
    set wu : HeightOneSpectrum (𝓞 ↥L'') := ⟨u, hup, hubot⟩ with hwudef
    have hdvd_e : p₀ ∣ Ideal.ramificationIdx' v.asIdeal u := by
      rw [← multiplicity_map_eq_ramificationIdx hinj v wu]
      exact p0_dvd_multiplicity_map p₀ hp₀ x v hv yt hytpow wu hul.over.symm
    have he0 : Ideal.ramificationIdx' v.asIdeal u ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver u hvbot
    have hf0 : 0 < Ideal.inertiaDeg' v.asIdeal u := Ideal.inertiaDeg'_pos v.asIdeal u
    calc p₀ ≤ Ideal.ramificationIdx' v.asIdeal u := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hdvd_e
      _ ≤ Ideal.ramificationIdx' v.asIdeal u * Ideal.inertiaDeg' v.asIdeal u :=
          Nat.le_mul_of_pos_right _ hf0
  have hsum0 : ∑ u ∈ W, Ideal.ramificationIdx' v.asIdeal u * Ideal.inertiaDeg' v.asIdeal u =
      Module.finrank (↥L') ↥L'' :=
    Ideal.sum_ramification_inertia (𝓞 ↥L'') (↥L') (↥L'') hvbot

  have hd_ge : p₀ ≤ Module.finrank (↥L') ↥L'' := by
    rw [← hsum0]
    calc p₀ ≤ Ideal.ramificationIdx' v.asIdeal w₁.asIdeal * Ideal.inertiaDeg' v.asIdeal w₁.asIdeal :=
        hlow _ hw₁W
      _ ≤ _ := Finset.single_le_sum
          (f := fun u => Ideal.ramificationIdx' v.asIdeal u * Ideal.inertiaDeg' v.asIdeal u)
          (fun i _ => Nat.zero_le _) hw₁W
  have hd_p₀ : Module.finrank (↥L') ↥L'' = p₀ := le_antisymm hd_le hd_ge
  have hsum : ∑ u ∈ W, Ideal.ramificationIdx' v.asIdeal u * Ideal.inertiaDeg' v.asIdeal u = p₀ := by
    rw [hsum0, hd_p₀]
  obtain ⟨hWsingle, hef⟩ := finset_sum_squeeze hp₀.pos w₁.asIdeal hw₁W hsum hlow
  have huniq : ∀ u : Ideal (𝓞 ↥L''), u.IsPrime → u.LiesOver v.asIdeal → u = w₁.asIdeal := by
    intro u h1 h2
    have : u ∈ W := (hmemW u).mpr ⟨h1, h2⟩
    rw [hWsingle] at this
    exact Finset.mem_singleton.mp this

  have he_dvd : p₀ ∣ Ideal.ramificationIdx' v.asIdeal w₁.asIdeal := by
    rw [← multiplicity_map_eq_ramificationIdx hinj v w₁]
    exact p0_dvd_multiplicity_map p₀ hp₀ x v hv yt hytpow w₁ hQ₁lies.over.symm
  have he0 : Ideal.ramificationIdx' v.asIdeal w₁.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w₁.asIdeal hvbot
  have hf0 : 0 < Ideal.inertiaDeg' v.asIdeal w₁.asIdeal := Ideal.inertiaDeg'_pos _ _
  have he_p₀ : Ideal.ramificationIdx' v.asIdeal w₁.asIdeal = p₀ := by
    have h1 : p₀ ≤ Ideal.ramificationIdx' v.asIdeal w₁.asIdeal :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero he0) he_dvd
    have h2 : Ideal.ramificationIdx' v.asIdeal w₁.asIdeal ≤ p₀ := by
      calc Ideal.ramificationIdx' v.asIdeal w₁.asIdeal
          ≤ Ideal.ramificationIdx' v.asIdeal w₁.asIdeal * Ideal.inertiaDeg' v.asIdeal w₁.asIdeal :=
            Nat.le_mul_of_pos_right _ hf0
        _ = p₀ := hef
    exact le_antisymm h2 h1
  have hf_1 : Ideal.inertiaDeg' v.asIdeal w₁.asIdeal = 1 := by
    have := hef
    rw [he_p₀] at this
    exact Nat.eq_of_mul_eq_mul_left hp₀.pos (by rw [mul_one]; exact this)

  obtain ⟨𝔓, -, h𝔓prime, h𝔓comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral w₁.asIdeal (⊥ : Ideal (𝓞 ℚ̄))
      (by rw [Ideal.comap_bot_of_injective _ ringOfIntegersMap_injective]; exact bot_le)
  haveI := h𝔓prime
  haveI h𝔓lies : 𝔓.LiesOver w₁.asIdeal := ⟨h𝔓comap.symm⟩

  haveI htower𝓞 : IsScalarTower (𝓞 L') (𝓞 ↥L'') (𝓞 ℚ̄) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply NumberField.RingOfIntegers.ext
    rw [coe_ringOfIntegersMap, coe_ringOfIntegersMap, coe_ringOfIntegersMap,
      IsScalarTower.algebraMap_apply (↥L') (↥L'') ℚ̄]
  have htrans : ∀ I : Ideal (𝓞 ℚ̄), (I.under (𝓞 ↥L'')).under (𝓞 L') = I.under (𝓞 L') := by
    intro I
    rw [Ideal.under, Ideal.under, Ideal.under, Ideal.comap_comap,
      ← IsScalarTower.algebraMap_eq (𝓞 L') (𝓞 ↥L'') (𝓞 ℚ̄)]
  have h𝔓L'' : 𝔓.under (𝓞 ↥L'') = w₁.asIdeal := h𝔓comap
  have h𝔓L' : 𝔓.under (𝓞 L') = v.asIdeal := by
    rw [← htrans 𝔓, h𝔓L'']
    exact hQ₁comap

  have hdeg2 : 1 < (minpoly (↥L') y).natDegree := by
    rw [← hd_eq, hd_p₀]
    exact hp₀.one_lt
  obtain ⟨y₁, hy₁root, hy₁ne⟩ := exists_second_root L' y hyint hdeg2
  obtain ⟨σ₀, hσ₀⟩ := exists_algEquiv_map_root L' y y₁ hy₁root

  haveI hσ₀𝔓prime : (σ₀ • 𝔓).IsPrime := by
    rw [Ideal.pointwise_smul_eq_comap]
    infer_instance
  have hσ₀under : (σ₀ • 𝔓).under (𝓞 L') = v.asIdeal := by
    rw [Ideal.under_smul]
    exact h𝔓L'
  have hσ₀L'' : (σ₀ • 𝔓).under (𝓞 ↥L'') = w₁.asIdeal := by
    refine huniq _ (Ideal.IsPrime.under (𝓞 ↥L'') (σ₀ • 𝔓)) ⟨?_⟩
    rw [htrans (σ₀ • 𝔓), hσ₀under]
  have hunder_eq : 𝔓.under (𝓞 ↥L'') = (σ₀ • 𝔓).under (𝓞 ↥L'') := by
    rw [h𝔓L'', hσ₀L'']
  obtain ⟨ρ, hρ⟩ := exists_gal_smul_of_under_eq (↥L'') 𝔓 (σ₀ • 𝔓) hunder_eq

  have hresb : ∀ (g : ℚ̄ ≃ₐ[↥L''] ℚ̄) (b : 𝓞 ℚ̄),
      (AlgEquiv.restrictScalars (↥L') g) • b = g • b := fun g b =>
    NumberField.RingOfIntegers.ext rfl
  have hresbinv : ∀ (g : ℚ̄ ≃ₐ[↥L''] ℚ̄) (b : 𝓞 ℚ̄),
      (AlgEquiv.restrictScalars (↥L') g)⁻¹ • b = g⁻¹ • b := fun g b =>
    NumberField.RingOfIntegers.ext rfl
  have hresI : ∀ (g : ℚ̄ ≃ₐ[↥L''] ℚ̄) (I : Ideal (𝓞 ℚ̄)),
      (AlgEquiv.restrictScalars (↥L') g) • I = g • I := fun g I =>
    smul_ideal_congr _ _ (hresbinv g) I

  set σ₁ : ℚ̄ ≃ₐ[↥L'] ℚ̄ := (AlgEquiv.restrictScalars (↥L') ρ)⁻¹ * σ₀ with hσ₁def
  have hσ₁stab : σ₁ • 𝔓 = 𝔓 := by
    rw [hσ₁def, mul_smul, hρ, ← hresI ρ 𝔓, inv_smul_smul]
  have hσ₁mem : ∀ z ∈ 𝔓, σ₁ • z ∈ 𝔓 := by
    intro z hz
    have : σ₁ • z ∈ σ₁ • 𝔓 := by
      rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
      show σ₁⁻¹ • σ₁ • z ∈ 𝔓
      rwa [inv_smul_smul]
    rwa [hσ₁stab] at this

  have hsurj := residue_surjective_of_inertiaDeg_eq_one v.asIdeal w₁.asIdeal hf_1
  have hw₁to𝔓 : ∀ z : 𝓞 ↥L'', z ∈ w₁.asIdeal → algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) z ∈ 𝔓 := by
    intro z hz
    rw [← h𝔓L''] at hz
    exact Ideal.mem_comap.mp hz
  have hmaincong : ∀ c : 𝓞 ↥L'',
      σ₁ • algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c - algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c ∈ 𝔓 := by
    intro c
    obtain ⟨c'q, hc'⟩ := hsurj (Ideal.Quotient.mk w₁.asIdeal c)
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c'q
    have hc'' : Ideal.Quotient.mk w₁.asIdeal (algebraMap (𝓞 L') (𝓞 ↥L'') c') =
        Ideal.Quotient.mk w₁.asIdeal c := by
      rw [← hc']
      rfl
    have hw₁sub : c - algebraMap (𝓞 L') (𝓞 ↥L'') c' ∈ w₁.asIdeal :=
      Ideal.Quotient.eq.mp hc''.symm
    have hB : algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c - algebraMap (𝓞 L') (𝓞 ℚ̄) c' ∈ 𝔓 := by
      have := hw₁to𝔓 _ hw₁sub
      rwa [map_sub, ← IsScalarTower.algebraMap_apply (𝓞 L') (𝓞 ↥L'') (𝓞 ℚ̄)] at this
    have h1 : σ₁ • (algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c - algebraMap (𝓞 L') (𝓞 ℚ̄) c') ∈ 𝔓 :=
      hσ₁mem _ hB
    rw [smul_sub, galSmul_ringOfIntegersMap σ₁ c'] at h1
    have h2' : algebraMap (𝓞 L') (𝓞 ℚ̄) c' - algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c ∈ 𝔓 := by
      have := neg_mem hB
      rwa [neg_sub] at this
    have h2 := Ideal.add_mem 𝔓 h1 h2'
    rwa [sub_add_sub_cancel] at h2

  have hsmulmap : Ideal.map ((MulSemiringAction.toRingAut (ℚ̄ ≃ₐ[↥L'] ℚ̄) (𝓞 ℚ̄) σ₁) :
      𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) 𝔓 = σ₁ • 𝔓 := by
    rw [Ideal.pointwise_smul_eq_comap, Ideal.comap_symm]
  have hmapeq : 𝔓 = Ideal.map ((MulSemiringAction.toRingAut (ℚ̄ ≃ₐ[↥L'] ℚ̄) (𝓞 ℚ̄) σ₁) :
      𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) 𝔓 := by
    rw [hsmulmap, hσ₁stab]
  set φraw : (𝓞 ℚ̄ ⧸ 𝔓) ≃+* (𝓞 ℚ̄ ⧸ 𝔓) :=
    Ideal.quotientEquiv 𝔓 𝔓 ((MulSemiringAction.toRingAut (ℚ̄ ≃ₐ[↥L'] ℚ̄) (𝓞 ℚ̄) σ₁) :
      𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) hmapeq with hφrawdef
  have hφraw_mk : ∀ z : 𝓞 ℚ̄, φraw (Ideal.Quotient.mk 𝔓 z) = Ideal.Quotient.mk 𝔓 (σ₁ • z) := by
    intro z
    rfl
  set φ₁ : (𝓞 ℚ̄ ⧸ 𝔓) ≃ₐ[(𝓞 ↥L'') ⧸ w₁.asIdeal] (𝓞 ℚ̄ ⧸ 𝔓) :=
    AlgEquiv.ofRingEquiv (f := φraw) (by
      intro cq
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective cq
      have halg : algebraMap ((𝓞 ↥L'') ⧸ w₁.asIdeal) (𝓞 ℚ̄ ⧸ 𝔓)
          (Ideal.Quotient.mk w₁.asIdeal c) =
          Ideal.Quotient.mk 𝔓 (algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c) := rfl
      rw [halg, hφraw_mk]
      exact Ideal.Quotient.eq.mpr (hmaincong c)) with hφ₁def
  obtain ⟨δ, hδ⟩ := stabilizerHom_surjective_gal (↥L'') w₁.asIdeal 𝔓 φ₁⁻¹

  set σ₂ : ℚ̄ ≃ₐ[↥L'] ℚ̄ :=
    (AlgEquiv.restrictScalars (↥L') (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄)) * σ₁ with hσ₂def
  have hδstab : (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) • 𝔓 = 𝔓 := δ.2
  have hσ₂stab : σ₂ • 𝔓 = 𝔓 := by
    rw [hσ₂def, mul_smul, hσ₁stab, hresI, hδstab]
  have hσ₂mem : ∀ z ∈ 𝔓, σ₂ • z ∈ 𝔓 := by
    intro z hz
    have : σ₂ • z ∈ σ₂ • 𝔓 := by
      rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
      show σ₂⁻¹ • σ₂ • z ∈ 𝔓
      rwa [inv_smul_smul]
    rwa [hσ₂stab] at this
  have hσ₂meminv : ∀ z : 𝓞 ℚ̄, σ₂ • z ∈ 𝔓 → z ∈ 𝔓 := by
    intro z hz
    rw [← hσ₂stab, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap] at hz
    rwa [show ((MulSemiringAction.toRingAut (ℚ̄ ≃ₐ[↥L'] ℚ̄) (𝓞 ℚ̄) σ₂).symm :
        𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) (σ₂ • z) = z from by
      rw [RingEquiv.symm_apply_eq]
      rfl] at hz

  have hσ₂res : ∀ b : 𝓞 ℚ̄, σ₂ • b - b ∈ 𝔓 := by
    intro b
    rw [← Ideal.Quotient.eq]
    have h1 : σ₂ • b = (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) • (σ₁ • b) := by
      rw [hσ₂def, mul_smul, hresb]
    rw [h1, show Ideal.Quotient.mk 𝔓 ((δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) • (σ₁ • b)) =
        Ideal.Quotient.stabilizerHom 𝔓 w₁.asIdeal (ℚ̄ ≃ₐ[↥L''] ℚ̄) δ
          (Ideal.Quotient.mk 𝔓 (σ₁ • b)) from
      (Ideal.Quotient.stabilizerHom_apply 𝔓 w₁.asIdeal (ℚ̄ ≃ₐ[↥L''] ℚ̄) δ (σ₁ • b)).symm,
      hδ, show Ideal.Quotient.mk 𝔓 (σ₁ • b) = φ₁ (Ideal.Quotient.mk 𝔓 b) from
        (hφraw_mk b).symm,
      show (φ₁⁻¹ : (𝓞 ℚ̄ ⧸ 𝔓) ≃ₐ[(𝓞 ↥L'') ⧸ w₁.asIdeal] (𝓞 ℚ̄ ⧸ 𝔓)) = φ₁.symm from rfl,
      AlgEquiv.symm_apply_apply]

  have hfixgal : ∀ (g : ℚ̄ ≃ₐ[↥L''] ℚ̄) (w : ℚ̄), w ∈ L'' → g w = w := by
    intro g w hw
    exact gal_fix_of_mem_range g ⟨⟨w, hw⟩, rfl⟩
  have hyrange : y ∈ L'' := hyL''
  have hσ₂fix : ∀ z : ↥L', σ₂ (z : ℚ̄) = z := by
    intro z
    have hzL'' : (z : ℚ̄) ∈ L'' := by
      rw [hcoL]
      exact L''.algebraMap_mem z
    have h0 : σ₀ (z : ℚ̄) = z := by
      rw [hcoL]
      exact σ₀.commutes z
    have h1 : σ₁ (z : ℚ̄) = z := by
      rw [hσ₁def, AlgEquiv.mul_apply, h0]
      exact hfixgal ρ⁻¹ _ hzL''
    rw [hσ₂def, AlgEquiv.mul_apply, h1]
    exact hfixgal (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) _ hzL''
  have hσ₂y : σ₂ y ≠ y := by
    intro hcontra
    have h1 : σ₂ y = (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) (((AlgEquiv.restrictScalars (↥L') ρ)⁻¹ * σ₀) y) := by
      rw [hσ₂def, AlgEquiv.mul_apply]
      rfl
    have h2 : ((AlgEquiv.restrictScalars (↥L') ρ)⁻¹ * σ₀) y = ρ⁻¹ y₁ := by
      rw [AlgEquiv.mul_apply, hσ₀]
      rfl
    rw [h1, h2] at hcontra

    have h3 : ρ⁻¹ y₁ = (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄)⁻¹ y := by
      rw [← hcontra]
      show ρ⁻¹ y₁ = (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄).symm ((δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) (ρ⁻¹ y₁))
      rw [AlgEquiv.symm_apply_apply]
    have h4 : (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄)⁻¹ y = y := hfixgal _ y hyrange
    rw [h4] at h3
    have h5 : y₁ = ρ y := by
      rw [show ρ⁻¹ y₁ = ρ.symm y₁ from rfl] at h3
      rw [← h3, AlgEquiv.apply_symm_apply]
    have h6 : ρ y = y := hfixgal ρ y hyrange
    exact hy₁ne (by rw [h5, h6])

  have hq𝔓 : (q : 𝓞 ℚ̄) ∈ 𝔓 := by
    have h1 : (q : 𝓞 L') ∈ 𝔓.under (𝓞 L') := by
      rw [h𝔓L']
      exact hqv
    have h2 := Ideal.mem_comap.mp h1
    rwa [map_natCast] at h2
  have hq0 : (q : 𝓞 ℚ̄) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have h𝔓bot : 𝔓 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hq𝔓
    exact hq0 hq𝔓

  obtain ⟨P, hPmem⟩ : ∃ P : ValuationSubring ℚ̄,
      ∀ α : ℚ̄, α ∈ P ↔ ∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α = (a : ℚ̄) * (s : ℚ̄)⁻¹ :=
    ⟨placeAt 𝔓 h𝔓bot, fun α => mem_placeAt⟩
  have hcoe𝓞 : ∀ a : 𝓞 ℚ̄, (a : ℚ̄) = algebraMap (𝓞 ℚ̄) ℚ̄ a := fun a => rfl
  have hqQ0 : (q : ℚ̄) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero

  have hLies : P.LiesOverPrime q := by
    show (q : ℚ̄) ∈ P.nonunits
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hmem
    obtain ⟨a, s, hs, heq⟩ := (hPmem _).mp hmem
    have hsne : (s : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem hs
    have h2 : (s : ℚ̄) = (q : ℚ̄) * a := by
      calc (s : ℚ̄) = ((q : ℚ̄)⁻¹ * q) * s := by rw [inv_mul_cancel₀ hqQ0, one_mul]
      _ = ((a : ℚ̄) * (s : ℚ̄)⁻¹ * q) * s := by rw [← heq]
      _ = (q : ℚ̄) * a * ((s : ℚ̄)⁻¹ * s) := by ring
      _ = (q : ℚ̄) * a := by rw [inv_mul_cancel₀ hsne, mul_one]
    have h3 : s = (q : 𝓞 ℚ̄) * a := by
      apply NumberField.RingOfIntegers.coe_injective
      push_cast
      exact h2
    exact hs (h3 ▸ Ideal.mul_mem_right a _ hq𝔓)

  have hstabP : ∀ (g : ℚ̄ ≃ₐ[↥L'] ℚ̄), (∀ z ∈ 𝔓, g • z ∈ 𝔓) → (∀ z : 𝓞 ℚ̄, g • z ∈ 𝔓 → z ∈ 𝔓) →
      ∀ α ∈ P, g α ∈ P := by
    intro g hg hg' α hα
    obtain ⟨a, s, hs, rfl⟩ := (hPmem α).mp hα
    refine (hPmem _).mpr ⟨g • a, g • s, fun hmem => hs (hg' s hmem), ?_⟩
    rw [map_mul, map_inv₀, show g (a : ℚ̄) = ((g • a : 𝓞 ℚ̄) : ℚ̄) from (coe_galSmul g a).symm,
      show g (s : ℚ̄) = ((g • s : 𝓞 ℚ̄) : ℚ̄) from (coe_galSmul g s).symm]
  have hσ₂invmem : ∀ z ∈ 𝔓, σ₂⁻¹ • z ∈ 𝔓 := by
    intro z hz
    apply hσ₂meminv
    rwa [smul_inv_smul]
  have hσ₂invmem' : ∀ z : 𝓞 ℚ̄, σ₂⁻¹ • z ∈ 𝔓 → z ∈ 𝔓 := by
    intro z hz
    have := hσ₂mem _ hz
    rwa [smul_inv_smul] at this
  set σ : ℚ̄ ≃ₐ[ℚ] ℚ̄ := AlgEquiv.restrictScalars ℚ σ₂ with hσdef
  have hσapp : ∀ w : ℚ̄, σ w = σ₂ w := fun w => rfl
  have hσinvapp : ∀ w : ℚ̄, σ⁻¹ w = σ₂⁻¹ w := fun w => rfl
  have hdec : σ ∈ P.decompositionSubgroup ℚ := by
    show σ • P = P
    apply SetLike.ext
    intro α
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hmem
      have h1 : σ₂ (σ⁻¹ • α) ∈ P := hstabP σ₂ hσ₂mem hσ₂meminv _ hmem
      rwa [show σ⁻¹ • α = σ₂⁻¹ α from by rw [AlgEquiv.smul_def]; exact hσinvapp α,
        show σ₂ (σ₂⁻¹ α) = α from by
          rw [show σ₂⁻¹ α = σ₂.symm α from rfl, AlgEquiv.apply_symm_apply]] at h1
    · intro hmem
      rw [AlgEquiv.smul_def, hσinvapp]
      exact hstabP σ₂⁻¹ hσ₂invmem hσ₂invmem' α hmem

  have hinertia : σ ∈ P.inertiaSubgroupIn ℚ := by
    rw [ValuationSubring.inertiaSubgroupIn]
    refine Subgroup.mem_map.mpr ⟨⟨σ, hdec⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro ξ
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective (R := ↥P) ξ
    show (⟨σ, hdec⟩ : P.decompositionSubgroup ℚ) • IsLocalRing.residue ↥P z =
      IsLocalRing.residue ↥P z
    rw [← IsLocalRing.ResidueField.residue_smul]
    apply Ideal.Quotient.eq.mpr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨w'P, hw'P⟩ := hunit.exists_right_inv

    have hsmulcoe : (((⟨σ, hdec⟩ : P.decompositionSubgroup ℚ) • z : ↥P) : ℚ̄) = σ₂ (z : ℚ̄) :=
      rfl
    set d : ℚ̄ := σ₂ (z : ℚ̄) - (z : ℚ̄) with hddef
    have hdw' : d * (w'P : ℚ̄) = 1 := by
      have h0 := congrArg (fun t : ↥P => (t : ℚ̄)) hw'P
      push_cast at h0
      rwa [hsmulcoe, ← hddef] at h0
    have hd0 : d ≠ 0 := by
      intro h
      rw [h, zero_mul] at hdw'
      exact zero_ne_one hdw'
    have hw'inv : (w'P : ℚ̄) = d⁻¹ := eq_inv_of_mul_eq_one_right hdw'

    obtain ⟨a, s, hs, hzeq⟩ := (hPmem (z : ℚ̄)).mp (SetLike.coe_mem z)
    have hsne : (s : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem hs
    have hσ₂snot : σ₂ • s ∉ 𝔓 := fun h => hs (hσ₂meminv s h)
    have hσ₂sne : ((σ₂ • s : 𝓞 ℚ̄) : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem hσ₂snot

    set N : 𝓞 ℚ̄ := (σ₂ • a) * s - a * (σ₂ • s) with hNdef
    have hN𝔓 : N ∈ 𝔓 := by
      have hdecomp : N = (σ₂ • a - a) * s - a * (σ₂ • s - s) := by
        rw [hNdef]
        ring
      rw [hdecomp]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right s _ (hσ₂res a))
        (Ideal.mul_mem_left _ a (hσ₂res s))
    set D : 𝓞 ℚ̄ := (σ₂ • s) * s with hDdef
    have hD𝔓 : D ∉ 𝔓 := by
      intro h
      rcases h𝔓prime.mem_or_mem h with h | h
      · exact hσ₂snot h
      · exact hs h

    have hd_frac : d = (N : ℚ̄) / (D : ℚ̄) := by
      have hσ₂z : σ₂ (z : ℚ̄) = ((σ₂ • a : 𝓞 ℚ̄) : ℚ̄) / ((σ₂ • s : 𝓞 ℚ̄) : ℚ̄) := by
        rw [hzeq, map_mul, map_inv₀, ← div_eq_mul_inv,
          show σ₂ (a : ℚ̄) = ((σ₂ • a : 𝓞 ℚ̄) : ℚ̄) from (coe_galSmul σ₂ a).symm,
          show σ₂ (s : ℚ̄) = ((σ₂ • s : 𝓞 ℚ̄) : ℚ̄) from (coe_galSmul σ₂ s).symm]
      rw [hddef, hσ₂z, hzeq, ← div_eq_mul_inv,
        div_sub_div _ _ hσ₂sne hsne]
      rw [hNdef, hDdef]
      push_cast
      ring_nf

    have hNne : (N : ℚ̄) ≠ 0 := by
      intro h
      rw [hd_frac, h, zero_div] at hd0
      exact hd0 rfl
    obtain ⟨c, t, ht, hw'eq⟩ := (hPmem (w'P : ℚ̄)).mp (SetLike.coe_mem w'P)
    have htne : (t : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem ht
    have hdinv : (D : ℚ̄) / (N : ℚ̄) = (c : ℚ̄) / (t : ℚ̄) := by
      have h1 : d⁻¹ = (D : ℚ̄) / (N : ℚ̄) := by
        rw [hd_frac, inv_div]
      rw [← h1, ← hw'inv, hw'eq, div_eq_mul_inv]
    have hcross : D * t = N * c := by
      apply NumberField.RingOfIntegers.coe_injective
      push_cast
      have h4 := (div_eq_div_iff hNne htne).mp hdinv
      rw [mul_comm (c : ℚ̄) (N : ℚ̄)] at h4
      exact h4
    have hDt𝔓 : D * t ∈ 𝔓 := hcross ▸ Ideal.mul_mem_right c _ hN𝔓
    rcases h𝔓prime.mem_or_mem hDt𝔓 with h | h
    · exact hD𝔓 h
    · exact ht h

  exact ⟨P, hLies, pin_of_under_eq L' v 𝔓 h𝔓L' P hPmem, σ, hinertia, fun z => hσ₂fix z,
    fun h => hσ₂y ((hσapp y).symm.trans h)⟩

end WtTF
p2m_reactivate "P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF.RB P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF"

theorem solution
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L']
    (p₀ : ℕ) (hp₀ : p₀.Prime) (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (hv : ¬ ((p₀ : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)))
    (y : AlgebraicClosure ℚ) (hy : y ^ p₀ = ((x : L') : AlgebraicClosure ℚ)) :
    ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q ∧
      (∀ z : 𝓞 L', z ∈ v.asIdeal ↔ P.valuation (algebraMap L' (AlgebraicClosure ℚ) z) < 1) ∧
      ∃ σ ∈ P.inertiaSubgroupIn ℚ, (∀ z : L', σ z = z) ∧ σ y ≠ y :=
  WtTF.exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd L' p₀ hp₀ x v q hq hqv hv y hy

end S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
end P2MW
export P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation (solution)
