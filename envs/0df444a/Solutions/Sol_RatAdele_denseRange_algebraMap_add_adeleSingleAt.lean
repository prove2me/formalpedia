-- Prove2me | solution 1 for RatAdele.denseRange_algebraMap_add_adeleSingleAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1cdb4d27-990f-522a-a6a1-e306f2d5aa2f

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RatAdele_denseRange_algebraMap_add_adeleSingleAt

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped RestrictedProduct

namespace RatAdeleDensityAux

private theorem exists_pow_lt_of_lt_one (x γ : WithZero (Multiplicative ℤ)) (hx : x < 1) (hγ : γ ≠ 0) :
    ∃ n : ℕ, x ^ n < γ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨1, by rw [pow_one]; exact zero_lt_iff.mpr hγ⟩
  · have hl : WithZero.log x < 0 := by
      have h := (WithZero.log_lt_log hx0 one_ne_zero).mpr hx
      simpa using h
    refine ⟨(WithZero.log γ).natAbs + 1, ?_⟩
    rw [← WithZero.exp_log hγ]
    apply WithZero.lt_exp_of_log_lt
    rw [WithZero.log_pow, nsmul_eq_mul]
    have hn : (0 : ℤ) ≤ (((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) := by positivity
    have h1 : (((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) * WithZero.log x ≤
        -(((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) := by nlinarith
    have h2 : -(((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) < WithZero.log γ := by omega
    exact h1.trans_lt h2

private theorem exists_radius_of_mem_nhds (i : HeightOneSpectrum (RingOfIntegers ℚ)) (x : i.adicCompletion ℚ)
    (s : Set (i.adicCompletion ℚ)) (hs : s ∈ nhds x) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ y : i.adicCompletion ℚ, Valued.v (y - x) < γ → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1, (map_ne_zero _).mpr γ.ne_zero, fun y hy => hγ ?_⟩
  show Valued.v.restrict (y - x) < γ.1
  exact (Valuation.restrict_lt_iff_lt_embedding _).mpr hy

private theorem exists_pow_intValuation_lt (i : HeightOneSpectrum (RingOfIntegers ℚ)) (γ : WithZero (Multiplicative ℤ))
    (hγ : γ ≠ 0) : ∃ a : RingOfIntegers ℚ, a ≠ 0 ∧ i.intValuation a < γ := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot i.ne_bot
  have hlt : i.intValuation π < 1 := (i.intValuation_lt_one_iff_mem π).mpr hπ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one _ γ hlt hγ
  exact ⟨π ^ n, pow_ne_zero n hπ0, by rw [map_pow]; exact hn⟩

private theorem exists_ne_zero_forall_intValuation_lt (T : Finset (HeightOneSpectrum (RingOfIntegers ℚ)))
    (γ : HeightOneSpectrum (RingOfIntegers ℚ) → WithZero (Multiplicative ℤ)) (hγ : ∀ i, γ i ≠ 0) :
    ∃ N : RingOfIntegers ℚ, N ≠ 0 ∧ ∀ i ∈ T, i.intValuation N < γ i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun i hi => by simp at hi⟩
  | insert j T hj ih =>
    obtain ⟨N, hN0, hN⟩ := ih
    obtain ⟨a, ha0, ha⟩ := exists_pow_intValuation_lt j (γ j) (hγ j)
    refine ⟨N * a, mul_ne_zero hN0 ha0, fun i hi => ?_⟩
    rw [map_mul]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · calc i.intValuation N * i.intValuation a ≤ 1 * i.intValuation a :=
            mul_le_mul_left (i.intValuation_le_one N) _
        _ = i.intValuation a := one_mul _
        _ < γ i := ha
    · calc i.intValuation N * i.intValuation a ≤ i.intValuation N * 1 :=
            mul_le_mul_right (i.intValuation_le_one a) _
        _ = i.intValuation N := mul_one _
        _ < γ i := hN i hi

private theorem isPrincipalIdealRing_ringOfIntegers_rat : IsPrincipalIdealRing (RingOfIntegers ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective

private theorem exists_generator (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    ∃ π : RingOfIntegers ℚ, π ≠ 0 ∧ (∀ i : HeightOneSpectrum (RingOfIntegers ℚ), i ≠ v → i.intValuation π = 1) ∧
      ∀ w : InfinitePlace ℚ, 2 ≤ w (algebraMap (RingOfIntegers ℚ) ℚ π) := by
  haveI := isPrincipalIdealRing_ringOfIntegers_rat
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal v.asIdeal).principal
  rw [Ideal.submodule_span_eq] at hπ
  have hmem : π ∈ v.asIdeal := hπ ▸ Ideal.mem_span_singleton_self π
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by rw [hπ, Set.singleton_zero, Ideal.span_zero])
  refine ⟨π, hπ0, fun i hi => ?_, fun w => ?_⟩
  ·
    rw [i.intValuation_eq_one_iff_mem_primeCompl]
    intro hπi
    apply hi
    apply HeightOneSpectrum.asIdeal_injective
    have hle : v.asIdeal ≤ i.asIdeal := by rw [hπ]; exact (Ideal.span_singleton_le_iff_mem _).mpr hπi
    exact (v.isMaximal.eq_of_le i.isPrime.ne_top hle).symm
  ·
    set n : ℤ := Rat.ringOfIntegersEquiv π with hn
    have hcast : algebraMap (RingOfIntegers ℚ) ℚ π = (n : ℚ) := (Rat.ringOfIntegersEquiv_apply_coe π).symm
    have hn0 : n ≠ 0 := by
      intro h
      apply hπ0
      have : Rat.ringOfIntegersEquiv π = Rat.ringOfIntegersEquiv 0 := by rw [map_zero]; exact h
      exact Rat.ringOfIntegersEquiv.injective this
    have hunit : ∀ u : RingOfIntegers ℚ, IsUnit u → π ≠ u := by
      rintro u hu rfl
      exact v.isPrime.ne_top ((Ideal.eq_top_of_isUnit_mem _ hmem hu))
    have hn1 : n ≠ 1 := by
      intro h
      apply hunit 1 isUnit_one
      have : Rat.ringOfIntegersEquiv π = Rat.ringOfIntegersEquiv 1 := by rw [map_one]; exact h
      exact Rat.ringOfIntegersEquiv.injective this
    have hn1' : n ≠ -1 := by
      intro h
      apply hunit (-1) isUnit_one.neg
      have : Rat.ringOfIntegersEquiv π = Rat.ringOfIntegersEquiv (-1) := by rw [map_neg, map_one]; exact h
      exact Rat.ringOfIntegersEquiv.injective this
    have habs : (2 : ℝ) ≤ |(n : ℝ)| := by
      have h2 : (2 : ℤ) ≤ |n| := by
        rcases le_or_gt 0 n with h | h
        · rw [abs_of_nonneg h]; omega
        · rw [abs_of_neg h]; omega
      have := (Int.cast_le (R := ℝ)).mpr h2
      simpa using this
    rw [hcast, ← InfinitePlace.norm_embedding_eq, map_intCast, Complex.norm_intCast]
    exact habs

private theorem fst_algebraMap (q : ℚ) :
    (algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) q).1 = algebraMap ℚ (InfiniteAdeleRing ℚ) q := rfl

private theorem snd_algebraMap (q : ℚ) :
    (algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) q).2 = algebraMap ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ) q := rfl

private theorem finite_algebraMap_apply (q : ℚ) (i : HeightOneSpectrum (RingOfIntegers ℚ)) :
    algebraMap ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ) q i = algebraMap ℚ (i.adicCompletion ℚ) q := rfl

private theorem finite_mul_apply (y z : FiniteAdeleRing (RingOfIntegers ℚ) ℚ) (i : HeightOneSpectrum (RingOfIntegers ℚ)) :
    (y * z) i = y i * z i := rfl

private theorem finite_add_apply (y z : FiniteAdeleRing (RingOfIntegers ℚ) ℚ) (i : HeightOneSpectrum (RingOfIntegers ℚ)) :
    (y + z) i = y i + z i := rfl

private theorem finite_sub_apply (y z : FiniteAdeleRing (RingOfIntegers ℚ) ℚ) (i : HeightOneSpectrum (RingOfIntegers ℚ)) :
    (y - z) i = y i - z i := rfl

private theorem infinite_mul_apply (y z : InfiniteAdeleRing ℚ) (w : InfinitePlace ℚ) : (y * z) w = y w * z w := rfl

private theorem norm_infinite_algebraMap_apply (q : ℚ) (w : InfinitePlace ℚ) :
    ‖algebraMap ℚ (InfiniteAdeleRing ℚ) q w‖ = w q := by
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact InfinitePlace.Completion.norm_coe w q

private theorem valued_algebraMap_adicCompletion (i : HeightOneSpectrum (RingOfIntegers ℚ)) (q : ℚ) :
    Valued.v (algebraMap ℚ (i.adicCompletion ℚ) q) = i.valuation ℚ q := by
  first
    | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' i (algebraMap ℚ ℚ q)
    | (rw [HeightOneSpectrum.algebraMap_adicCompletion]
       exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' i (algebraMap ℚ ℚ q))

private theorem valuation_scalar (i : HeightOneSpectrum (RingOfIntegers ℚ)) (N π : RingOfIntegers ℚ)
    (hπ : i.intValuation π = 1) (k : ℕ) :
    i.valuation ℚ (algebraMap (RingOfIntegers ℚ) ℚ N / algebraMap (RingOfIntegers ℚ) ℚ π ^ k) =
      i.intValuation N := by
  rw [map_div₀, map_pow, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hπ,
    one_pow, div_one]

private theorem valued_correction_le (i : HeightOneSpectrum (RingOfIntegers ℚ)) (N π : RingOfIntegers ℚ)
    (hπ : i.intValuation π = 1) (k : ℕ) (y : FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
    (hy : y i ∈ i.adicCompletionIntegers ℚ) :
    Valued.v ((algebraMap ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ)
        (algebraMap (RingOfIntegers ℚ) ℚ N / algebraMap (RingOfIntegers ℚ) ℚ π ^ k) * y) i) ≤
      i.intValuation N := by
  rw [finite_mul_apply, finite_algebraMap_apply, Valuation.map_mul, valued_algebraMap_adicCompletion,
    valuation_scalar i N π hπ k]
  have hy1 : Valued.v (y i) ≤ 1 := by rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at hy
  calc i.intValuation N * Valued.v (y i) ≤ i.intValuation N * 1 := mul_le_mul_right hy1 _
    _ = i.intValuation N := mul_one _

private theorem tendsto_infinite_correction (N π : RingOfIntegers ℚ)
    (hπ : ∀ w : InfinitePlace ℚ, 2 ≤ w (algebraMap (RingOfIntegers ℚ) ℚ π)) (r : ℝ)
    (y : ℕ → InfiniteAdeleRing ℚ) (hy : ∀ k, ∀ w : InfinitePlace ℚ, ‖y k w‖ ≤ r) :
    Filter.Tendsto (fun k : ℕ => algebraMap ℚ (InfiniteAdeleRing ℚ)
      (algebraMap (RingOfIntegers ℚ) ℚ N / algebraMap (RingOfIntegers ℚ) ℚ π ^ k) * y k) Filter.atTop (nhds 0) := by
  refine tendsto_pi_nhds.mpr fun w => ?_
  have hπw : 1 < w (algebraMap (RingOfIntegers ℚ) ℚ π) := by linarith [hπ w]
  have hπ0 : 0 < w (algebraMap (RingOfIntegers ℚ) ℚ π) := by linarith
  have hgeom : Filter.Tendsto (fun k : ℕ => (w (algebraMap (RingOfIntegers ℚ) ℚ N) * r) *
      ((w (algebraMap (RingOfIntegers ℚ) ℚ π))⁻¹ ^ k)) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hπ0.le) (inv_lt_one_of_one_lt₀ hπw)).const_mul
      (w (algebraMap (RingOfIntegers ℚ) ℚ N) * r)
    simpa using h
  refine squeeze_zero_norm (fun k => ?_) hgeom
  rw [infinite_mul_apply, norm_mul, norm_infinite_algebraMap_apply, map_div₀, map_pow, div_eq_mul_inv, ← inv_pow]
  calc w (algebraMap (RingOfIntegers ℚ) ℚ N) * (w (algebraMap (RingOfIntegers ℚ) ℚ π))⁻¹ ^ k * ‖y k w‖ ≤
        w (algebraMap (RingOfIntegers ℚ) ℚ N) * (w (algebraMap (RingOfIntegers ℚ) ℚ π))⁻¹ ^ k * r :=
          mul_le_mul_of_nonneg_left (hy k w) (by positivity)
    _ = w (algebraMap (RingOfIntegers ℚ) ℚ N) * r * (w (algebraMap (RingOfIntegers ℚ) ℚ π))⁻¹ ^ k := by ring

private theorem exists_decomposition (x : AdeleRing (RingOfIntegers ℚ) ℚ) (s : ℚ) (hs : s ≠ 0) :
    ∃ q : ℚ, ∃ B : AdeleRing (RingOfIntegers ℚ) ℚ, B ∈ AdelicBox.adelicBox ℚ ∧
      x - algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) q = algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) s * B := by
  obtain ⟨κ, hκ, -⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox ℚ
    (algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) s⁻¹ * x)
  refine ⟨-(s * κ), _, hκ, ?_⟩
  rw [map_neg, sub_neg_eq_add, mul_add, ← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hs, map_one, one_mul,
    add_comm]

private theorem isOpen_adicCompletionIntegers (i : HeightOneSpectrum (RingOfIntegers ℚ)) :
    IsOpen (i.adicCompletionIntegers ℚ : Set (i.adicCompletion ℚ)) :=
  Valued.isOpen_valuationSubring _

end RatAdeleDensityAux

open RatAdeleDensityAux in
theorem solution
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    DenseRange fun qy : ℚ × v.adicCompletion ℚ =>
      algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2 := by
  classical

  obtain ⟨π, -, hπ_unit, hπ_arch⟩ := exists_generator v
  obtain ⟨r, hr⟩ := AdelicBox.exists_forall_norm_apply_le_of_mem_infiniteBox ℚ
  intro x
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨U₁, hU₁, U₂, hU₂, hUW⟩ := mem_nhds_prod_iff.mp hW

  obtain ⟨S, hS_nhds, hS_cof, hS_sub⟩ := (RestrictedProduct.mem_nhds_iff_of_cofinite isOpen_adicCompletionIntegers
    (x := x.2) (U := U₂)).mp hU₂
  have hT : {i : HeightOneSpectrum (RingOfIntegers ℚ) |
      ¬ S i = (i.adicCompletionIntegers ℚ : Set (i.adicCompletion ℚ))}.Finite := Filter.eventually_cofinite.mp hS_cof

  choose γ hγ0 hγ using fun i => exists_radius_of_mem_nhds i (x.2 i) (S i) (hS_nhds i)

  obtain ⟨N, hN0, hN⟩ := exists_ne_zero_forall_intValuation_lt hT.toFinset γ hγ0
  have hN' : algebraMap (RingOfIntegers ℚ) ℚ N ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  have hπ' : algebraMap (RingOfIntegers ℚ) ℚ π ≠ 0 := by
    intro h
    have := hπ_arch (Classical.arbitrary (InfinitePlace ℚ))
    rw [h, map_zero] at this
    norm_num at this
  set sc : ℕ → ℚ := fun k => algebraMap (RingOfIntegers ℚ) ℚ N / algebraMap (RingOfIntegers ℚ) ℚ π ^ k with hsc
  have hsc0 : ∀ k, sc k ≠ 0 := fun k => div_ne_zero hN' (pow_ne_zero k hπ')

  choose q B hB hxqB using fun k => exists_decomposition x (sc k) (hsc0 k)

  have hBbox : ∀ k, (B k).1 ∈ AdelicBox.infiniteBox ℚ ∧
      (B k).2 ∈ AdelicBox.integralFiniteAdeles (RingOfIntegers ℚ) ℚ := fun k => hB k
  have htend : Filter.Tendsto (fun k => (x - algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) (q k)).1)
      Filter.atTop (nhds 0) := by
    have h := tendsto_infinite_correction N π hπ_arch r (fun k => (B k).1) (fun k w => hr _ (hBbox k).1 w)
    refine h.congr fun k => ?_
    rw [hxqB k]
    rfl

  have hfst : Filter.Tendsto (fun k => (algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) (q k)).1)
      Filter.atTop (nhds x.1) := by
    have h := tendsto_const_nhds (x := x.1) |>.sub htend
    rw [sub_zero] at h
    refine h.congr fun k => ?_
    exact sub_sub_cancel x.1 (algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) (q k)).1
  obtain ⟨k, hk⟩ := (hfst.eventually_mem hU₁).exists

  refine ⟨_, ?_, (q k, (x - algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) (q k)).2 v), rfl⟩
  apply hUW
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  ·
    show (algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) (q k)).1 + (0 : InfiniteAdeleRing ℚ) ∈ U₁
    rw [add_zero]
    exact hk
  ·
    show algebraMap ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ) (q k) +
      StandardAddChar.finAdeleSingleAt ℚ v ((x - algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) (q k)).2 v) ∈ U₂
    set z : FiniteAdeleRing (RingOfIntegers ℚ) ℚ := algebraMap ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ) (q k) +
      StandardAddChar.finAdeleSingleAt ℚ v ((x - algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) (q k)).2 v) with hz

    have hD : ∀ i, (x - algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) (q k)).2 i = x.2 i -
        algebraMap ℚ (i.adicCompletion ℚ) (q k) := fun i => rfl
    have hD' : (x - algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) (q k)).2 =
        algebraMap ℚ (FiniteAdeleRing (RingOfIntegers ℚ) ℚ) (sc k) * (B k).2 := by
      rw [hxqB k]; rfl
    have hcorr : ∀ i, i ≠ v → Valued.v (x.2 i - algebraMap ℚ (i.adicCompletion ℚ) (q k)) ≤ i.intValuation N := by
      intro i hi
      rw [← hD i, hD']
      exact valued_correction_le i N π (hπ_unit i hi) k (B k).2 ((hBbox k).2 i)
    have hz_mem : ∀ i, z i ∈ S i := by
      intro i
      by_cases hiv : i = v
      · subst hiv
        rw [hz, finite_add_apply, finite_algebraMap_apply, StandardAddChar.finAdeleSingleAt_apply_self, hD,
          add_sub_cancel]
        exact mem_of_mem_nhds (hS_nhds i)
      · have hzi : z i = algebraMap ℚ (i.adicCompletion ℚ) (q k) := by
          rw [hz, finite_add_apply, finite_algebraMap_apply, StandardAddChar.finAdeleSingleAt_apply_of_ne _ _ _ hiv,
            add_zero]
        by_cases hiT : S i = (i.adicCompletionIntegers ℚ : Set (i.adicCompletion ℚ))
        ·
          rw [hiT, SetLike.mem_coe, hzi]
          have hx_int : x.2 i ∈ i.adicCompletionIntegers ℚ := by
            have := mem_of_mem_nhds (hS_nhds i)
            rwa [hiT, SetLike.mem_coe] at this
          have hc_int : x.2 i - algebraMap ℚ (i.adicCompletion ℚ) (q k) ∈ i.adicCompletionIntegers ℚ := by
            rw [HeightOneSpectrum.mem_adicCompletionIntegers]
            exact (hcorr i hiv).trans (i.intValuation_le_one N)
          have := sub_mem hx_int hc_int
          rwa [sub_sub_cancel] at this
        ·
          have hiT' : i ∈ hT.toFinset := hT.mem_toFinset.mpr hiT
          rw [hzi]
          apply hγ i
          rw [← Valuation.map_neg, neg_sub]
          exact (hcorr i hiv).trans_lt (hN i hiT')
    have hz_pi : (⇑z : ∀ i : HeightOneSpectrum (RingOfIntegers ℚ), i.adicCompletion ℚ) ∈ Set.univ.pi S :=
      Set.mem_univ_pi.mpr hz_mem
    obtain ⟨u, hu, huz⟩ := hS_sub hz_pi
    rwa [show u = z from DFunLike.coe_injective huz] at hu

end S_RatAdele_denseRange_algebraMap_add_adeleSingleAt
end P2MW
export P2MW.S_RatAdele_denseRange_algebraMap_add_adeleSingleAt (solution)
