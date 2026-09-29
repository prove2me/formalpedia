-- Prove2me | solution 1 for Submodule.finiteAdeleBox_ofFiniteIdele
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9c89499d-bc89-5e0e-9b87-5942d1f4df07

import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele

p2m_open "IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.mem_adicCompletionIntegers HeightOneSpectrum.valuedAdicCompletion_eq_valuation' HeightOneSpectrum.valuation_le_one HeightOneSpectrum.ext HeightOneSpectrum.mem_integers_of_valuation_le_one FiniteAdeleRing exists_forall_sub_mem_ideal HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "valuation_of_algebraMap intValuation_le_pow_iff_mem valuedAdicCompletion_eq_valuation adicCompletion_valueGroup_eq algebraMap_adicCompletion intValuation_lt_one_iff_mem asIdeal mem_adicCompletionIntegers comap isPrime valuedAdicCompletion_eq_valuation' valuation_le_one intValuation_ne_zero adicCompletion valuation coe_mem_adicCompletionIntegers ne_bot under intValuation_le_one adicCompletionIntegers valuedAdicCompletion_surjective mem_integers_of_valuation_le_one irreducible adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers intValuation_if_neg prime intValuation"
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"

section Multiplicative

open scoped WithZero
lemma s2_exists_ofAdd_natCast_of_le_one {x : ℤᵐ⁰} (hx : x ≠ 0) (hx' : x ≤ 1) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) = x := by
  lift x to Multiplicative ℤ using hx
  norm_cast at hx'
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos hx')
  use k
  rw [← hk, Int.neg_neg]
  rfl

lemma s2_exists_ofAdd_natCast_lt {x : ℤᵐ⁰} (hx : x ≠ 0) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) < x := by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  lift y to Multiplicative ℤ using hnz
  use y.natAbs
  apply lt_of_le_of_lt _ hyx
  norm_cast
  exact inv_mabs_le y

end Multiplicative

lemma s2_intValuation_eq_coe_neg_multiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {a : A} (hnz : a ≠ 0) :
    v.intValuation a = WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [intValuation_if_neg _ hnz, Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

lemma s2_ne_zero_of_some_le_intValuation {a : A} {m : Multiplicative ℤ} (h : m ≤ v.intValuation a)
    : a ≠ 0 := by
  rintro rfl
  simp at h

lemma s2_emultiplicity_eq_of_valuation_eq_ofAdd {a : A} {k : ℕ}
    (hv : v.intValuation a = (Multiplicative.ofAdd (-(k : ℤ)))) :
    emultiplicity v.asIdeal (Ideal.span {a}) = k := by
  classical
  have hnz : a ≠ 0 := s2_ne_zero_of_some_le_intValuation _ (le_of_eq hv.symm)
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  simp only [intValuation_if_neg _ hnz, WithZero.exp, ofAdd_neg, WithZero.coe_inv, inv_inj,
    WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq, Nat.cast_inj] at hv
  rw [← hv, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb,
    Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot, normalize_eq]

lemma s2_exists_adicValued_mul_sub_le {a b : A} {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0)
    (hle : γ ≤ v.intValuation a)
    (hle' : v.intValuation b ≤ v.intValuation a) :
    ∃ y, v.intValuation (y * a - b) ≤ γ := by

  have hγ' : γ ≤ 1 := by
    apply hle.trans
    apply intValuation_le_one
  obtain ⟨n, hn⟩ := s2_exists_ofAdd_natCast_of_le_one hγ hγ'
  rw [← hn, ← WithZero.exp] at hle ⊢
  have hnz : a ≠ 0 := s2_ne_zero_of_some_le_intValuation _ hle
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]

  rw [s2_intValuation_eq_coe_neg_multiplicity _ hnz, WithZero.exp_le_exp, neg_le_neg_iff,
    Int.ofNat_le] at hle
  have hm : emultiplicity v.asIdeal (Ideal.span {a}) ≤ n :=
    le_of_eq_of_le
      (s2_emultiplicity_eq_of_valuation_eq_ofAdd v <| s2_intValuation_eq_coe_neg_multiplicity v hnz)
      (ENat.coe_le_coe.mpr hle)
  have hb : b ∈ v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) := by
    rwa [← intValuation_le_pow_iff_mem, ← s2_intValuation_eq_coe_neg_multiplicity _ hnz]

  rw [← Ideal.irreducible_pow_sup_of_ge hnb (irreducible v) n hm] at hb

  obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.mp hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
  use y

  rwa [hy, ← hxz, sub_add_cancel_right, intValuation_le_pow_iff_mem, neg_mem_iff]

open MonoidWithZeroHom in
lemma s2_valued_coe_sub_coe (k : K) (x : WithVal (v.valuation K)) :
    Valued.v ((k : v.adicCompletion K) - (x : v.adicCompletion K)) =
      Valued.v ((k : (v.valuation K).Completion) - (x : (v.valuation K).Completion)) := rfl

lemma s2_exists_adicValued_sub_lt_of_adicValued_le_one {x : (WithVal (v.valuation K))}
    (γ : ((WithZero (Multiplicative ℤ)))ˣ) (hx : Valued.v x ≤ 1) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by

  obtain ⟨⟨n, d, hd⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors A) x
  dsimp only at hnd

  have hnd' := congr_arg Valued.v hnd
  simp only [map_mul] at hnd'
  have hge : Valued.v ((algebraMap A (WithVal (v.valuation K))) d) ≥
      Valued.v ((algebraMap A (WithVal (v.valuation K))) n) :=
    calc Valued.v ((algebraMap A (WithVal (v.valuation K))) d)
          ≥ (valuation K v) x.ofVal *
            (valuation K v) ((algebraMap A (WithVal (v.valuation K))) d).ofVal :=
                mul_le_of_le_one_left' hx
        _ = Valued.v ((algebraMap A (WithVal (v.valuation K))) n) := hnd'
  simp only [ge_iff_le, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hge
  simp only [valuation_of_algebraMap] at hge
  have hdz : (algebraMap A (WithVal (v.valuation K)) d) ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ (fun _ ↦ id) hd

  have hv : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hdz
  let hu : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) * γ.val ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact ⟨hv, γ.ne_zero⟩
  obtain ⟨γ', hγ, hγu, hγv⟩ := WithZero.exists_ne_zero_and_lt_and_lt hu hv
  simp only [WithVal.algebraMap_right_apply, WithVal.valued_toVal, valuation_of_algebraMap] at hγv

  obtain ⟨a, hval⟩ := s2_exists_adicValued_mul_sub_le v hγ hγv.le hge
  use a
  rw [← eq_div_iff_mul_eq hdz] at hnd
  rw [s2_valued_coe_sub_coe, ← UniformSpace.Completion.coe_sub, Valued.valuedCompletion_apply, hnd,
    sub_div' hdz, map_div₀]
  rw [← Valuation.pos_iff Valued.v, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hdz
  simp only [WithVal.algebraMap_right_apply, WithVal.equiv_symm_apply,
    ← WithVal.toVal_mul, ← WithVal.toVal_sub, WithVal.valued_toVal, ← map_mul, ← map_sub] at hγu ⊢
  rw [div_lt_iff₀' hdz, valuation_of_algebraMap]
  exact lt_of_le_of_lt hval hγu

open scoped WithZero

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

scoped instance s2_isRankOneDiscrete_valuedAdicCompletion : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

open Valuation.IsRankOneDiscrete in

theorem s2_closureAlgebraMapIntegers_eq_integers :
    closure (algebraMap A (v.adicCompletion K)).range =
    SetLike.coe (v.adicCompletionIntegers K) := by
  apply subset_antisymm

  · apply closure_minimal _ (Valued.isClosed_valuationSubring _)
    rintro b ⟨a, rfl⟩
    exact coe_mem_adicCompletionIntegers v a

  · let f := fun (k : WithVal (v.valuation K)) => (k : v.adicCompletion K)
    suffices h : closure (f '' (f ⁻¹' (adicCompletionIntegers K v))) ⊆
        closure (algebraMap A (adicCompletion K v)).range by
      apply Set.Subset.trans _ h
      exact DenseRange.subset_closure_image_preimage_of_isOpen
        ((adicCompletion.ofCompletion_surjective K v).denseRange.comp
          UniformSpace.Completion.denseRange_coe (adicCompletion.continuous_ofCompletion K v))
        (Valued.isOpen_valuationSubring _)

    apply closure_minimal _ isClosed_closure
    rintro k ⟨x, hx, rfl⟩
    unfold f at hx
    rw [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers,
        adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply] at hx
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Valued.mem_nhds] at hU
    obtain ⟨γ, hγ⟩ := hU
    let γ' := Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv γ
    obtain ⟨a, ha⟩ := s2_exists_adicValued_sub_lt_of_adicValued_le_one K v γ' hx
    use algebraMap A K a
    constructor
    · use a
      rfl
    · apply hγ
      simp only [sub_zero, WithVal.equiv_symm_apply, Set.mem_setOf_eq]
      rwa [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
        valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (valuedAdicCompletion_surjective K v)]

open Valuation.IsRankOneDiscrete in

theorem s2_exists_adicValued_sub_lt_of_adicCompletionInteger
    (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  have h := s2_closureAlgebraMapIntegers_eq_integers K v
  rw [Set.ext_iff] at h
  specialize h x
  simp_rw [RingHom.coe_range, Subtype.coe_prop, iff_true, mem_closure_iff_nhds] at h
  specialize h { y | Valued.v (y  - (x : v.adicCompletion K)) < γ.val }
  have hn : {y | Valued.v (y - (x : v.adicCompletion K)) < γ.val} ∈ nhds x.val := by
    rw [Valued.mem_nhds]
    use (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv).symm γ
    have hsurj := (valuedAdicCompletion_surjective K v)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono vK).lt_iff_lt,
      valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj] at hy
    simpa using hy
  obtain ⟨z, ⟨hz, a, ha⟩⟩ := h hn
  use a
  rw [algebraMap_adicCompletion, Function.comp_apply] at ha
  rwa [ha]

theorem s2_exists_forall_adicValued_sub_lt {ι : Type*} (s : Finset ι)
    (e : ι → (WithZero (Multiplicative ℤ))ˣ) (valuation : ι → HeightOneSpectrum A)
    (injective : Function.Injective valuation)
    (x : (i : ι) → (valuation i).adicCompletionIntegers K) :
    ∃ a, ∀ i ∈ s, Valued.v ((algebraMap A K a) - (x i).val) < (e i).val := by

  choose f hf using fun (i : s) =>
    s2_exists_adicValued_sub_lt_of_adicCompletionInteger K (valuation i) (x i) (e i)

  have hexists_e' : ∀ (i : ι), ∃ (e' : ℕ), (Multiplicative.ofAdd (-(e' : ℤ))) < (e i).val := by
    intro i
    apply s2_exists_ofAdd_natCast_lt (e i).ne_zero
  choose e' he' using hexists_e'
  have hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (fun i ↦ (valuation i).asIdeal) i ≠ (fun i ↦ (valuation i).asIdeal) j := by
    intro _ _ _ _
    exact mt <| fun hij ↦ injective (HeightOneSpectrum.ext hij)

  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun i => (valuation i).asIdeal) e' (fun i hi => (valuation i).prime) hinj f
  use a
  intro i hi
  specialize ha i hi
  specialize hf ⟨i, hi⟩
  rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := K),
    ← valuedAdicCompletion_eq_valuation, algebraMap.coe_sub] at ha
  refine lt_of_le_of_lt ?_ (Valuation.map_add_lt _ (ha.trans_lt (he' i)) hf)
  apply le_of_eq
  congr
  rw [add_sub, sub_eq_sub_iff_add_eq_add, add_right_cancel_iff,
    add_comm_sub, add_sub, eq_sub_iff_add_eq]
  rfl

open scoped algebraMap

theorem s2_exists_nonZeroDivisor_smul_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : HeightOneSpectrum A,
      (d : v.adicCompletion K) * a v ∈ v.adicCompletionIntegers K := by
  classical
  have hbad : {v : HeightOneSpectrum A | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose b hb hba using fun v : HeightOneSpectrum A ↦
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  refine ⟨∏ v ∈ hbad.toFinset, b v, prod_mem fun v _ ↦ hb v, fun v ↦ ?_⟩
  by_cases hv : a v ∈ v.adicCompletionIntegers K
  · exact mul_mem (coe_mem_adicCompletionIntegers v _) hv
  · have hvmem : v ∈ hbad.toFinset := hbad.mem_toFinset.mpr hv
    rw [← Finset.prod_erase_mul _ _ hvmem, algebraMap.coe_mul, mul_assoc]
    exact mul_mem (coe_mem_adicCompletionIntegers v _) (by rw [mul_comm]; exact hba v)

theorem s2_exists_sub_algebraMap_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  classical

  obtain ⟨d, hd, hda⟩ := s2_exists_nonZeroDivisor_smul_mem_adicCompletionIntegers K a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd

  have hsupp : {v : HeightOneSpectrum A | v.intValuation d < 1}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {d})
      (by simpa [Ideal.span_singleton_eq_bot] using hd0)
    refine h.subset fun v hv ↦ ?_
    rw [Set.mem_setOf_eq, intValuation_lt_one_iff_mem] at hv
    exact (Ideal.dvd_span_singleton).mpr hv

  obtain ⟨c, hc⟩ := s2_exists_forall_adicValued_sub_lt K hsupp.toFinset
    (fun v ↦ Units.mk0 (v.intValuation d) (v.intValuation_ne_zero d hd0))
    id Function.injective_id (fun v ↦ ⟨(d : v.adicCompletion K) * a v, hda v⟩)

  refine ⟨algebraMap A K c / algebraMap A K d, fun v ↦ ?_⟩
  have hdK : algebraMap A K d ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K (fun _ ↦ id) hd
  have hdv : Valued.v ((d : A) : v.adicCompletion K) ≠ 0 := by
    rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
    exact v.intValuation_ne_zero d hd0

  have key : ∀ v : HeightOneSpectrum A,
      Valued.v ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
        ≤ Valued.v (((d : A) : v.adicCompletion K)) := by
    intro v
    by_cases hv : v.intValuation d < 1
    ·
      have h := hc v (hsupp.mem_toFinset.mpr hv)
      simp only [id_eq, Units.val_mk0] at h
      rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
      calc Valued.v ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
          = Valued.v (((c : A) : v.adicCompletion K) - (d : v.adicCompletion K) * a v) := by
            rw [← Valuation.map_neg, neg_sub]
        _ ≤ v.intValuation d := le_of_lt h
    ·
      rw [not_lt] at hv
      have hd1 : Valued.v (((d : A) : v.adicCompletion K)) = 1 := by
        rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d) hv
      rw [hd1, ← mem_adicCompletionIntegers]
      exact sub_mem (hda v) (coe_mem_adicCompletionIntegers v c)

  rw [mem_adicCompletionIntegers]
  have hdne : ((d : A) : v.adicCompletion K) ≠ 0 := by
    intro h0
    exact hdv (by rw [h0, map_zero])
  have hmap : algebraMap K (v.adicCompletion K) (algebraMap A K c / algebraMap A K d)
      = ((c : A) : v.adicCompletion K) / ((d : A) : v.adicCompletion K) := by
    rw [map_div₀]
    rfl
  have hrw : a v - algebraMap K (v.adicCompletion K) (algebraMap A K c / algebraMap A K d)
      = ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
        / ((d : A) : v.adicCompletion K) := by
    rw [hmap, sub_div, mul_comm ((d : A) : v.adicCompletion K) (a v),
      mul_div_assoc, div_self hdne, mul_one]
  rw [hrw, map_div₀, div_le_one₀ (zero_lt_iff.mpr hdv)]
  exact key v

end IsDedekindDomain.HeightOneSpectrum
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain"

p2m_open "IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

open scoped algebraMap in

theorem s2_exists_nonZeroDivisor_coe_mul_mem_adicCompletionIntegers
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (a : FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : HeightOneSpectrum A,
      (d : v.adicCompletion K) * a v ∈ v.adicCompletionIntegers K := by
  classical

  have hbad : {v : HeightOneSpectrum A | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2

  choose b hb hba using fun v : HeightOneSpectrum A ↦
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)

  refine ⟨∏ v ∈ hbad.toFinset, b v, prod_mem fun v _ ↦ hb v, fun v ↦ ?_⟩
  by_cases hv : a v ∈ v.adicCompletionIntegers K
  ·
    exact mul_mem (coe_mem_adicCompletionIntegers v _) hv
  ·
    have hvmem : v ∈ hbad.toFinset := hbad.mem_toFinset.mpr hv
    rw [← Finset.prod_erase_mul _ _ hvmem, algebraMap.coe_mul, mul_assoc]
    exact mul_mem (coe_mem_adicCompletionIntegers v _) (by rw [mul_comm]; exact hba v)

theorem s2_algebraMap_adicCompletion_eq {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] (v : HeightOneSpectrum A) (d : A) :
    algebraMap A (v.adicCompletion K) d = algebraMap K (v.adicCompletion K) (algebraMap A K d) :=
  IsScalarTower.algebraMap_apply A K (v.adicCompletion K) d

namespace IsDedekindDomain p2m_export "IsDedekindDomain" "HeightOneSpectrum.mem_adicCompletionIntegers HeightOneSpectrum.valuedAdicCompletion_eq_valuation' HeightOneSpectrum.valuation_le_one HeightOneSpectrum.ext HeightOneSpectrum.mem_integers_of_valuation_le_one FiniteAdeleRing exists_forall_sub_mem_ideal HeightOneSpectrum" namespace FiniteAdeleRing p2m_export "IsDedekindDomain.FiniteAdeleRing" "algebraMap_apply ext" end IsDedekindDomain.FiniteAdeleRing
p2m_open_scoped "IsDedekindDomain IsDedekindDomain.FiniteAdeleRing" in
theorem IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K :=
  IsDedekindDomain.HeightOneSpectrum.s2_exists_sub_algebraMap_mem_adicCompletionIntegers K a

p2m_open_scoped "IsDedekindDomain IsDedekindDomain.FiniteAdeleRing" in
theorem IsDedekindDomain.FiniteAdeleRing.exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      algebraMap K (v.adicCompletion K) (algebraMap A K d) * a v ∈ v.adicCompletionIntegers K := by
  obtain ⟨d, hd, h⟩ := s2_exists_nonZeroDivisor_coe_mul_mem_adicCompletionIntegers K a
  exact ⟨d, hd, fun v => by rw [← s2_algebraMap_adicCompletion_eq K v d]; exact h v⟩

open scoped TensorProduct Pointwise nonZeroDivisors
p2m_open "IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain NumberField"

noncomputable section

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

def s1_Zhat : Subring 𝔸f where
  carrier := {a | ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => by
    show (a * b) v ∈ _
    have : (a * b) v = a v * b v := rfl
    rw [this]; exact mul_mem (ha v) (hb v)
  one_mem' := fun v => by
    have : (1 : 𝔸f) v = 1 := rfl
    rw [this]; exact one_mem _
  add_mem' := fun {a b} ha hb v => by
    have : (a + b) v = a v + b v := rfl
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := fun v => by
    have : (0 : 𝔸f) v = 0 := rfl
    rw [this]; exact zero_mem _
  neg_mem' := fun {a} ha v => by
    have : (-a) v = -(a v) := rfl
    rw [this]; exact neg_mem (ha v)

theorem s1_mem_Zhat_iff (a : 𝔸f) : a ∈ s1_Zhat ↔ ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

theorem s1_valued_algebraMap_apply (q : ℚ) (v : HOS) :
    Valued.v ((algebraMap ℚ 𝔸f q) v) = v.valuation ℚ q := by
  have h : (algebraMap ℚ 𝔸f q) v = ((WithVal.equiv (v.valuation ℚ)).symm q : v.adicCompletion ℚ) := rfl
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q

theorem s1_algebraMap_apply_mem_integers_iff (q : ℚ) (v : HOS) :
    (algebraMap ℚ 𝔸f q) v ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, s1_valued_algebraMap_apply]

theorem s1_valuation_intCast_le_one (v : HOS) (m : ℤ) : v.valuation ℚ (m : ℚ) ≤ 1 := by
  have h : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := ℚ) v (m : 𝓞 ℚ)
  rwa [map_intCast] at h

theorem s1_valuation_natCast_le_one (v : HOS) (n : ℕ) : v.valuation ℚ (n : ℚ) ≤ 1 := by
  have h := s1_valuation_intCast_le_one v (n : ℤ)
  rwa [Int.cast_natCast] at h

theorem s1_algebraMap_intCast_mem_Zhat (m : ℤ) : algebraMap ℚ 𝔸f (m : ℚ) ∈ s1_Zhat := fun v =>
  (s1_algebraMap_apply_mem_integers_iff _ v).mpr (s1_valuation_intCast_le_one v m)

theorem s1_exists_intCast_eq (r : 𝓞 ℚ) : ∃ m : ℤ, ((r : ℚ)) = (m : ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
  have h0 := Rat.ringOfIntegersEquiv.symm_apply_apply r
  rw [eq_intCast Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)] at h0
  calc (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r := rfl
    _ = algebraMap (𝓞 ℚ) ℚ ((Rat.ringOfIntegersEquiv r : ℤ) : 𝓞 ℚ) := by rw [h0]
    _ = ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) := map_intCast _ _

theorem s1_exists_intCast_of_forall_valuation_le_one (q : ℚ)
    (h : ∀ v : HOS, v.valuation ℚ q ≤ 1) : ∃ m : ℤ, q = (m : ℚ) := by
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q h
  obtain ⟨m, hm⟩ := s1_exists_intCast_eq r
  refine ⟨m, ?_⟩
  rw [← hm]
  exact hr.symm

section BoxGen

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_tmul_mem_finiteAdeleBox {Λ : Submodule ℤ K} {z : K} (hz : z ∈ Λ) {a : 𝔸f}
    (ha : a ∈ s1_Zhat) : z ⊗ₜ[ℚ] a ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, a, ha, rfl⟩

theorem s1_finiteAdeleBox_le_iff {Λ : Submodule ℤ K} {H : AddSubgroup (K ⊗[ℚ] 𝔸f)} :
    Submodule.finiteAdeleBox Λ ≤ H ↔ ∀ z ∈ Λ, ∀ a : 𝔸f, a ∈ s1_Zhat → z ⊗ₜ[ℚ] a ∈ H := by
  unfold Submodule.finiteAdeleBox
  rw [AddSubgroup.closure_le]
  constructor
  · intro h z hz a ha
    exact h ⟨z, hz, a, ha, rfl⟩
  · rintro h x ⟨z, hz, a, ha, rfl⟩
    exact h z hz a ha

end BoxGen
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

section Slice

variable {K : Type*} [Ring K] [Algebra ℚ K]

def s1_coord {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) : K ⊗[ℚ] 𝔸f →ₗ[ℚ] 𝔸f :=
  TensorProduct.lift ((LinearMap.lsmul ℚ 𝔸f).comp (b.coord i))

theorem s1_coord_tmul {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (z : K) (a : 𝔸f) :
    s1_coord b i (z ⊗ₜ[ℚ] a) = (b.repr z i) • a := by
  unfold s1_coord
  rw [TensorProduct.lift.tmul]
  rfl

theorem s1_coord_mem_Zhat_of_mem_finiteAdeleBox {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι)
    {t : K ⊗[ℚ] 𝔸f} (ht : t ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))) :
    s1_coord b i t ∈ s1_Zhat := by
  have hle : Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ≤ (s1_Zhat.toAddSubgroup).comap (s1_coord b i).toAddMonoidHom := by
    rw [s1_finiteAdeleBox_le_iff]
    intro z hz a ha
    rw [AddSubgroup.mem_comap]
    show s1_coord b i (z ⊗ₜ[ℚ] a) ∈ s1_Zhat
    rw [s1_coord_tmul]
    obtain ⟨m, hm⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ b z).mp hz i
    rw [← hm, Algebra.smul_def]
    refine mul_mem ?_ ha
    have : (algebraMap ℤ ℚ m) = ((m : ℤ) : ℚ) := by rw [algebraMap_int_eq, Int.coe_castRingHom]
    rw [this]
    exact s1_algebraMap_intCast_mem_Zhat m
  exact hle ht

theorem s1_tmul_one_mem_finiteAdeleBox_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (z : K) :
    z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ↔ z ∈ Submodule.span ℤ (Set.range b) := by
  constructor
  · intro hz
    rw [Module.Basis.mem_span_iff_repr_mem ℤ b z]
    intro i
    have hc := s1_coord_mem_Zhat_of_mem_finiteAdeleBox b i hz
    rw [s1_coord_tmul, Algebra.smul_def, mul_one] at hc
    have hval : ∀ v : HOS, v.valuation ℚ (b.repr z i) ≤ 1 := fun v =>
      (s1_algebraMap_apply_mem_integers_iff _ v).mp (hc v)
    obtain ⟨m, hm⟩ := s1_exists_intCast_of_forall_valuation_le_one _ hval
    refine ⟨m, ?_⟩
    rw [hm, algebraMap_int_eq, Int.coe_castRingHom]
  · intro hz
    exact s1_tmul_mem_finiteAdeleBox hz (one_mem _)

end Slice
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

section LatticeBasis

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_exists_basis_of_isLattice (M : Submodule ℤ K) [Submodule.IsLattice ℚ M] :
    ∃ (n : ℕ) (bM : Module.Basis (Fin n) ℚ K), Submodule.span ℤ (Set.range bM) = M := by
  classical
  haveI : Module.Finite ℤ ↥M := Submodule.IsLattice.finite ℚ _
  haveI : Module.Free ℤ ↥M := Submodule.IsLattice.free ℚ _
  let n := Module.finrank ℤ ↥M
  let bZ : Module.Basis (Fin n) ℤ ↥M := Module.finBasis ℤ ↥M
  refine ⟨n, bZ.extendOfIsLattice ℚ, ?_⟩
  have hrange : Set.range (bZ.extendOfIsLattice ℚ) = M.subtype '' Set.range bZ := by
    ext x
    simp only [Set.mem_range, Module.Basis.extendOfIsLattice_apply, Set.mem_image,
      Submodule.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨bZ k, ⟨k, rfl⟩, hk⟩, fun ⟨y, ⟨k, hk⟩, hy⟩ => ⟨k, by rw [hk]; exact hy⟩⟩
  rw [hrange, ← Submodule.map_span, bZ.span_eq, Submodule.map_top, Submodule.range_subtype]

end LatticeBasis
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

section Coord

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s3_sum_tmul_coord {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (t : K ⊗[ℚ] 𝔸f) :
    ∑ i, (b i) ⊗ₜ[ℚ] (s1_coord b i t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero, Finset.sum_const_zero]
  | tmul z a =>
      simp only [s1_coord_tmul]
      calc ∑ i, b i ⊗ₜ[ℚ] ((b.repr z) i • a)
          = ∑ i, ((b.repr z) i • b i) ⊗ₜ[ℚ] a := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [TensorProduct.smul_tmul]
        _ = (∑ i, (b.repr z) i • b i) ⊗ₜ[ℚ] a := by rw [TensorProduct.sum_tmul]
        _ = z ⊗ₜ[ℚ] a := by rw [b.sum_repr]
  | add s t hs ht =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hs, ht]

theorem s3_mem_finiteAdeleBox_span_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (t : K ⊗[ℚ] 𝔸f) :
    t ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b)) ↔ ∀ i, s1_coord b i t ∈ s1_Zhat := by
  constructor
  · intro ht i
    exact s1_coord_mem_Zhat_of_mem_finiteAdeleBox b i ht
  · intro h
    rw [← s3_sum_tmul_coord b t]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    exact s1_tmul_mem_finiteAdeleBox (Submodule.subset_span (Set.mem_range_self i)) (h i)

theorem s3_coord_tmul_one {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (x : K) :
    s1_coord b i (x ⊗ₜ[ℚ] (1 : 𝔸f)) = algebraMap ℚ 𝔸f (b.repr x i) := by
  rw [s1_coord_tmul, Algebra.smul_def, mul_one]

theorem s3_exists_sub_tmul_one_mem_finiteAdeleBox
    (hSA : ∀ a : 𝔸f, ∃ q : ℚ, a - algebraMap ℚ 𝔸f q ∈ s1_Zhat)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (t : K ⊗[ℚ] 𝔸f) :
    ∃ x : K, t - x ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b)) := by
  classical
  choose q hq using fun i => hSA (s1_coord b i t)
  refine ⟨∑ i, q i • b i, ?_⟩
  rw [s3_mem_finiteAdeleBox_span_iff]
  intro i
  rw [map_sub, s3_coord_tmul_one, b.repr_sum_self]
  exact hq i

end Coord
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

section FG
variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s3_fg_of_le {M N : Submodule ℤ K} [Submodule.IsLattice ℚ N] (hle : M ≤ N) : M.FG := by
  haveI : IsNoetherian ℤ ↥N := isNoetherian_of_fg_of_noetherian _ (Submodule.IsLattice.fg (A := ℚ))
  have hrw : M = Submodule.map N.subtype (Submodule.comap N.subtype M) := by
    rw [Submodule.map_comap_subtype]; exact (inf_of_le_right hle).symm
  rw [hrw]; exact (IsNoetherian.noetherian _).map _
end FG
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

theorem s3_algebraMap_apply (q : ℚ) (v : HOS) :
    (algebraMap ℚ 𝔸f q) v = algebraMap ℚ (v.adicCompletion ℚ) q := rfl

theorem s3_hSA : ∀ a : 𝔸f, ∃ q : ℚ, a - algebraMap ℚ 𝔸f q ∈ s1_Zhat := by
  intro a
  obtain ⟨q, hq⟩ := IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers ℚ a
  refine ⟨q, fun v => ?_⟩
  have : (a - algebraMap ℚ 𝔸f q) v = a v - algebraMap ℚ (v.adicCompletion ℚ) q := rfl
  rw [this]
  exact hq v

theorem s3_hDen : ∀ a : 𝔸f, ∃ m : ℕ, m ≠ 0 ∧ algebraMap ℚ 𝔸f (m : ℚ) * a ∈ s1_Zhat := by
  intro a
  obtain ⟨d, hd, h⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers ℚ a
  obtain ⟨m', hm'⟩ := s1_exists_intCast_eq d
  have hd0 : (d : ℚ) ≠ 0 := by
    have : d ≠ 0 := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero] at hm'
    exact hd0 hm'
  have hdm : algebraMap (𝓞 ℚ) ℚ d = (m' : ℚ) := hm'
  refine ⟨(m' ^ 2).toNat, ?_, fun v => ?_⟩
  · intro h0
    rw [Int.toNat_eq_zero] at h0
    exact absurd (lt_of_le_of_ne (sq_nonneg m') (Ne.symm (pow_ne_zero 2 hm'0))) (not_lt.mpr h0)
  have e : ((((m' ^ 2).toNat : ℕ)) : ℚ) = (m' : ℚ) * (m' : ℚ) := by
    have h1 : (((m' ^ 2).toNat : ℕ) : ℤ) = m' ^ 2 := Int.toNat_of_nonneg (sq_nonneg m')
    have h2 : (((m' ^ 2).toNat : ℕ) : ℚ) = (((((m' ^ 2).toNat : ℕ) : ℤ)) : ℚ) := by rw [Int.cast_natCast]
    rw [h2, h1, Int.cast_pow, sq]
  have : (algebraMap ℚ 𝔸f ((((m' ^ 2).toNat : ℕ)) : ℚ) * a) v
      = algebraMap ℚ (v.adicCompletion ℚ) (m' : ℚ) * (algebraMap ℚ (v.adicCompletion ℚ) (m' : ℚ) * a v) := by
    have h1 : (algebraMap ℚ 𝔸f ((((m' ^ 2).toNat : ℕ)) : ℚ) * a) v
        = (algebraMap ℚ 𝔸f ((((m' ^ 2).toNat : ℕ)) : ℚ)) v * a v := rfl
    rw [h1, s3_algebraMap_apply, e, map_mul, mul_assoc]
  rw [this]
  refine mul_mem ?_ ?_
  · rw [← s3_algebraMap_apply]
    exact (s1_algebraMap_apply_mem_integers_iff _ v).mpr (s1_valuation_intCast_le_one v m')
  · have h2 := h v
    rwa [hdm] at h2

section Multiplier

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s3_box_mul_one_tmul_mem (Λ : Submodule ℤ K) {t : K ⊗[ℚ] 𝔸f}
    (ht : t ∈ Submodule.finiteAdeleBox Λ) {c : 𝔸f} (hc : c ∈ s1_Zhat) :
    t * ((1 : K) ⊗ₜ[ℚ] c) ∈ Submodule.finiteAdeleBox Λ := by
  refine AddSubgroup.closure_induction (p := fun t _ => t * ((1 : K) ⊗ₜ[ℚ] c) ∈ Submodule.finiteAdeleBox Λ)
    ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨z, hz, a, ha, rfl⟩
    show z ⊗ₜ[ℚ] a * ((1 : K) ⊗ₜ[ℚ] c) ∈ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact s1_tmul_mem_finiteAdeleBox hz (mul_mem ha hc)
  · show (0 : K ⊗[ℚ] 𝔸f) * ((1 : K) ⊗ₜ[ℚ] c) ∈ _
    rw [zero_mul]; exact zero_mem _
  · intro x y _ _ hx hy
    show (x + y) * ((1 : K) ⊗ₜ[ℚ] c) ∈ _
    rw [add_mul]; exact add_mem hx hy
  · intro x _ hx
    convert neg_mem hx using 1
    exact neg_mul x _

theorem s3_natCast_smul_mem_box (Λ : Submodule ℤ K) {t : K ⊗[ℚ] 𝔸f}
    (ht : t ∈ Submodule.finiteAdeleBox Λ) (n : ℕ) : (n : ℚ) • t ∈ Submodule.finiteAdeleBox Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ ht n

theorem s3_exists_natCast_smul_mem (Λ : Submodule ℤ K) [Submodule.IsLattice ℚ Λ] (z : K) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • z ∈ Λ := by
  classical
  obtain ⟨m, b, hb⟩ := s1_exists_basis_of_isLattice Λ

  refine ⟨∏ i, (b.repr z i).den, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => (b.repr z i).den_nz
  · rw [← hb, Module.Basis.mem_span_iff_repr_mem ℤ b]
    intro i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hdvd : ((b.repr z i).den : ℤ) ∣ ((∏ j, (b.repr z j).den : ℕ) : ℤ) := by
      exact_mod_cast Finset.dvd_prod_of_mem (fun j => (b.repr z j).den) (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k * (b.repr z i).num, ?_⟩
    show ((k * (b.repr z i).num : ℤ) : ℚ) = ((∏ j, (b.repr z j).den : ℕ) : ℚ) * b.repr z i
    have hq : ((b.repr z i).den : ℚ) * (b.repr z i) = (b.repr z i).num := by
      rw [mul_comm]; exact Rat.mul_den_eq_num (b.repr z i)
    have hk' : ((∏ j, (b.repr z j).den : ℕ) : ℚ) = ((b.repr z i).den : ℚ) * (k : ℚ) := by
      exact_mod_cast hk
    rw [hk', mul_comm ((b.repr z i).den : ℚ) (k : ℚ), mul_assoc, hq, Int.cast_mul]

theorem s3_exists_natCast_smul_mul_mem_box
    (hDen : ∀ a : 𝔸f, ∃ m : ℕ, m ≠ 0 ∧ algebraMap ℚ 𝔸f (m : ℚ) * a ∈ s1_Zhat)
    (Λ : Submodule ℤ K) [Submodule.IsLattice ℚ Λ] (g : K ⊗[ℚ] 𝔸f) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ u ∈ Submodule.finiteAdeleBox Λ, (M : ℚ) • (g * u) ∈ Submodule.finiteAdeleBox Λ := by
  classical
  obtain ⟨n, b, hb⟩ := s1_exists_basis_of_isLattice Λ

  choose m hm0 hm using fun i => hDen (s1_coord b i g)
  choose nn hnn0 hnn using fun p : Fin n × Fin n => s3_exists_natCast_smul_mem Λ (b p.1 * b p.2)
  refine ⟨(∏ i, m i) * ∏ p, nn p, ?_, ?_⟩
  · exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hm0 i)
      (Finset.prod_ne_zero_iff.mpr fun p _ => hnn0 p)
  intro u hu

  have hu' := (s3_mem_finiteAdeleBox_span_iff b u).mp (hb.symm ▸ hu)
  rw [← s3_sum_tmul_coord b g, ← s3_sum_tmul_coord b u, Finset.sum_mul, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [Finset.mul_sum, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul]

  have hdvd : nn (i, j) * m i ∣ (∏ i, m i) * ∏ p, nn p := by
    rw [mul_comm ((∏ i, m i)) _]
    exact mul_dvd_mul (Finset.dvd_prod_of_mem nn (Finset.mem_univ (i, j)))
      (Finset.dvd_prod_of_mem m (Finset.mem_univ i))
  obtain ⟨r, hr⟩ := hdvd
  rw [hr, show (((nn (i, j) * m i * r : ℕ)) : ℚ) = (nn (i, j) : ℚ) * ((m i * r : ℕ) : ℚ) by push_cast; ring,
    mul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  refine s1_tmul_mem_finiteAdeleBox (hnn (i, j)) ?_
  rw [Algebra.smul_def, Nat.cast_mul, map_mul, mul_mul_mul_comm]
  refine mul_mem (hm i) (mul_mem ?_ (hu' j))
  exact_mod_cast s1_algebraMap_intCast_mem_Zhat (r : ℤ)

end Multiplier
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

section Dictionary

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s3_mem_ofFiniteIdele_iff_inv_mul_mem (Λ : Submodule ℤ K) (g : (K ⊗[ℚ] 𝔸f)ˣ) (z : K) :
    z ∈ Submodule.ofFiniteIdele Λ g ↔ ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f))
      ∈ Submodule.finiteAdeleBox Λ := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyz⟩
    rw [AddMonoidHom.coe_mulLeft] at hyz
    rw [← hyz, ← mul_assoc, Units.inv_mul, one_mul]
    exact hy
  · intro h
    exact ⟨_, h, by rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]⟩

theorem s3_isLattice_ofFiniteIdele
    (hDen : ∀ a : 𝔸f, ∃ m : ℕ, m ≠ 0 ∧ algebraMap ℚ 𝔸f (m : ℚ) * a ∈ s1_Zhat)
    (Λ : Submodule ℤ K) [Submodule.IsLattice ℚ Λ] (g : (K ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.IsLattice ℚ (Submodule.ofFiniteIdele Λ g) := by
  classical
  obtain ⟨M, hM0, hM⟩ := s3_exists_natCast_smul_mul_mem_box hDen Λ (g : K ⊗[ℚ] 𝔸f)
  obtain ⟨M', hM0', hM'⟩ := s3_exists_natCast_smul_mul_mem_box hDen Λ ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f)
  obtain ⟨n, b, hb⟩ := s1_exists_basis_of_isLattice Λ
  have hM0q : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM0
  have hM0q' : (M' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM0'

  have hsub : ∀ z ∈ Submodule.ofFiniteIdele Λ g, (M : ℚ) • z ∈ Λ := by
    intro z hz
    rw [s3_mem_ofFiniteIdele_iff_inv_mul_mem] at hz
    have h := hM _ hz
    rw [← mul_assoc, Units.mul_inv, one_mul, TensorProduct.smul_tmul'] at h
    rw [← hb] at h ⊢
    exact (s1_tmul_one_mem_finiteAdeleBox_iff b _).mp h

  have hsup : ∀ w ∈ Λ, (M' : ℚ) • w ∈ Submodule.ofFiniteIdele Λ g := by
    intro w hw
    rw [s3_mem_ofFiniteIdele_iff_inv_mul_mem, ← TensorProduct.smul_tmul', mul_smul_comm]
    exact hM' _ (s1_tmul_mem_finiteAdeleBox hw (one_mem _))
  refine ⟨?_, ?_⟩
  ·
    have hinj : Function.Injective ((((M : ℚ) • (LinearMap.id : K →ₗ[ℚ] K))).restrictScalars ℤ) := by
      intro x y hxy
      have hxy' : (M : ℚ) • x = (M : ℚ) • y := hxy
      exact smul_right_injective K hM0q hxy'
    refine Submodule.fg_of_fg_map_injective _ hinj (s3_fg_of_le (N := Λ) ?_)
    rintro _ ⟨z, hz, rfl⟩
    exact hsub z hz
  ·
    apply le_antisymm le_top
    have htop : Submodule.span ℚ ((Λ : Submodule ℤ K) : Set K) = ⊤ := Submodule.IsLattice.span_eq_top
    rw [← htop, Submodule.span_le]
    intro w hw
    have h := Submodule.subset_span (R := ℚ) (s := ((Submodule.ofFiniteIdele Λ g : Submodule ℤ K) : Set K))
      (hsup w hw)
    have : w = ((M' : ℚ))⁻¹ • ((M' : ℚ) • w) := by
      rw [smul_smul, inv_mul_cancel₀ hM0q', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ h

theorem s3_finiteAdeleBox_ofFiniteIdele
    (hDen : ∀ a : 𝔸f, ∃ m : ℕ, m ≠ 0 ∧ algebraMap ℚ 𝔸f (m : ℚ) * a ∈ s1_Zhat)
    (hSA : ∀ a : 𝔸f, ∃ q : ℚ, a - algebraMap ℚ 𝔸f q ∈ s1_Zhat)
    (Λ : Submodule ℤ K) [Submodule.IsLattice ℚ Λ] (g : (K ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ g)
      = (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) := by
  classical
  haveI := s3_isLattice_ofFiniteIdele hDen Λ g
  have hle : Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ g)
      ≤ (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) := by
    rw [s1_finiteAdeleBox_le_iff]
    intro w hw a ha
    rw [s3_mem_ofFiniteIdele_iff_inv_mul_mem] at hw
    refine ⟨((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) * (w ⊗ₜ[ℚ] (1 : 𝔸f)) * ((1 : K) ⊗ₜ[ℚ] a),
      s3_box_mul_one_tmul_mem Λ hw ha, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine le_antisymm hle ?_
  obtain ⟨n, bJ, hbJ⟩ := s1_exists_basis_of_isLattice (Submodule.ofFiniteIdele Λ g)
  rintro y ⟨u, hu, rfl⟩
  obtain ⟨x, hx⟩ := s3_exists_sub_tmul_one_mem_finiteAdeleBox hSA bJ ((AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) u)
  rw [hbJ] at hx
  have hgu : (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) u
      ∈ (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) :=
    AddSubgroup.mem_map_of_mem _ hu
  have hx1 : x ⊗ₜ[ℚ] (1 : 𝔸f) ∈ (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) := by
    have := sub_mem hgu (hle hx)
    rwa [sub_sub_cancel] at this
  have hxΦ : x ∈ Submodule.ofFiniteIdele Λ g := (Submodule.mem_ofFiniteIdele_iff Λ g x).mpr hx1
  have hx2 : x ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ g) :=
    s1_tmul_mem_finiteAdeleBox hxΦ (one_mem _)
  have := add_mem hx hx2
  rwa [sub_add_cancel] at this

theorem s3_smul_coe_finiteAdeleBox (Λ : Submodule ℤ K) (g : (K ⊗[ℚ] 𝔸f)ˣ) :
    (g • ((Submodule.finiteAdeleBox Λ : AddSubgroup (K ⊗[ℚ] 𝔸f)) : Set (K ⊗[ℚ] 𝔸f)))
      = (((Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) :
          AddSubgroup (K ⊗[ℚ] 𝔸f)) : Set (K ⊗[ℚ] 𝔸f)) := by
  rw [AddSubgroup.coe_map, ← Set.image_smul]
  rfl

theorem s3_ofFiniteIdele_eq_iff
    (hDen : ∀ a : 𝔸f, ∃ m : ℕ, m ≠ 0 ∧ algebraMap ℚ 𝔸f (m : ℚ) * a ∈ s1_Zhat)
    (hSA : ∀ a : 𝔸f, ∃ q : ℚ, a - algebraMap ℚ 𝔸f q ∈ s1_Zhat)
    (Λ : Submodule ℤ K) [Submodule.IsLattice ℚ Λ] (g g' : (K ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.ofFiniteIdele Λ g = Submodule.ofFiniteIdele Λ g' ↔
      g⁻¹ * g' ∈ Submodule.finiteIdeleStabilizer Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff, mul_smul, s3_smul_coe_finiteAdeleBox,
    ← s3_finiteAdeleBox_ofFiniteIdele hDen hSA Λ g', inv_smul_eq_iff, s3_smul_coe_finiteAdeleBox,
    ← s3_finiteAdeleBox_ofFiniteIdele hDen hSA Λ g, SetLike.coe_set_eq]
  constructor
  · intro h; rw [h]
  · intro h

    haveI := s3_isLattice_ofFiniteIdele hDen Λ g
    haveI := s3_isLattice_ofFiniteIdele hDen Λ g'
    obtain ⟨n, b, hb⟩ := s1_exists_basis_of_isLattice (Submodule.ofFiniteIdele Λ g)
    obtain ⟨n', b', hb'⟩ := s1_exists_basis_of_isLattice (Submodule.ofFiniteIdele Λ g')
    ext z
    rw [← hb, ← s1_tmul_one_mem_finiteAdeleBox_iff b, hb, ← h, ← hb', s1_tmul_one_mem_finiteAdeleBox_iff b', hb']

end Dictionary
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

theorem solution {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ g)
      = (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  haveI : Submodule.IsLattice ℚ Λ := ⟨hfg, hspan⟩
  exact s3_finiteAdeleBox_ofFiniteIdele s3_hDen s3_hSA Λ g

end
p2m_reactivate "P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele.IsDedekindDomain.HeightOneSpectrum"

end S_Submodule_finiteAdeleBox_ofFiniteIdele
end P2MW
export P2MW.S_Submodule_finiteAdeleBox_ofFiniteIdele (solution)
