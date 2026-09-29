-- Prove2me | solution 1 for ValuationSubring.finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e36e5f52-df50-5ba5-a2ec-dc9ca8e06a6b

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime

set_option autoImplicit false

noncomputable section

open IntermediateField

namespace LocalDegreeBound

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime]

section RingOfIntegers

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def toField : PadicAlgCl.ringOfIntegers p K →+* K where
  toFun x := ⟨x, PadicAlgCl.ringOfIntegers.coe_mem x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

scoped instance algebraField : Algebra (PadicAlgCl.ringOfIntegers p K) K := (toField p K).toAlgebra

theorem algebraMap_coe_coe (x : PadicAlgCl.ringOfIntegers p K) :
    ((algebraMap (PadicAlgCl.ringOfIntegers p K) K x : K) : PadicAlgCl p) = (x : PadicAlgCl p) := rfl

scoped instance isScalarTower_int : IsScalarTower ℤ_[p] (PadicAlgCl.ringOfIntegers p K) K :=
  IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (by
    rw [algebraMap_coe_coe]
    change (algebraMap ℤ_[p] (PadicAlgCl p) a) = ((algebraMap ℤ_[p] K a : K) : PadicAlgCl p)
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    rfl)

scoped instance isScalarTower_field : IsScalarTower (PadicAlgCl.ringOfIntegers p K) K (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem natCast_ne_zero : ((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ≠ 0 := by
  intro h
  have h' := congrArg (fun x : PadicAlgCl.ringOfIntegers p K => (x : PadicAlgCl p)) h
  simp only [SubringClass.coe_natCast, Subalgebra.coe_zero] at h'
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h'

scoped instance isFractionRing : IsFractionRing (PadicAlgCl.ringOfIntegers p K) K := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [isUnit_iff_ne_zero]
    intro h
    apply nonZeroDivisors.ne_zero hy
    exact Subtype.ext (congrArg (fun z : K => (z : PadicAlgCl p)) h)
  · intro z
    obtain ⟨m, y, hy⟩ := PadicAlgCl.ringOfIntegers.exists_pow_natCast_mul_mem p K z.2
    refine ⟨⟨y, ⟨((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ^ m,
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (natCast_ne_zero p K))⟩⟩, ?_⟩
    apply Subtype.ext
    change (z : PadicAlgCl p) * (((((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ^ m :
      PadicAlgCl.ringOfIntegers p K)) : PadicAlgCl p) = (y : PadicAlgCl p)
    rw [hy, Subalgebra.coe_pow, SubringClass.coe_natCast, mul_comm]
  · intro x y h
    refine ⟨1, ?_⟩
    have : (x : PadicAlgCl p) = y := congrArg (fun z : K => (z : PadicAlgCl p)) h
    rw [Subtype.ext this]

theorem mem_maximalIdeal_iff_norm_lt_one [IsDiscreteValuationRing (PadicAlgCl.ringOfIntegers p K)]
    (x : PadicAlgCl.ringOfIntegers p K) :
    x ∈ IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K) ↔ ‖(x : PadicAlgCl p)‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx
    by_contra hge
    push Not at hge
    have h1 : ‖(x : PadicAlgCl p)‖ = 1 := le_antisymm (PadicAlgCl.ringOfIntegers.norm_coe_le_one p K x) hge
    have hx0 : (x : PadicAlgCl p) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1

    have hinvK : (x : PadicAlgCl p)⁻¹ ∈ K := K.inv_mem (PadicAlgCl.ringOfIntegers.coe_mem x)
    have hinvI : IsIntegral ℤ_[p] (x : PadicAlgCl p)⁻¹ := by
      rw [PadicAlgCl.isIntegral_padicInt_iff_norm_le_one, norm_inv, h1, inv_one]
    apply hx
    refine ⟨⟨x, ⟨(x : PadicAlgCl p)⁻¹, hinvI, hinvK⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mul_inv_cancel₀ hx0)
    · exact Subtype.ext (inv_mul_cancel₀ hx0)
  · intro hlt hu
    obtain ⟨u, rfl⟩ := hu
    set a : PadicAlgCl p := ((u : PadicAlgCl.ringOfIntegers p K) : PadicAlgCl p) with ha
    set b : PadicAlgCl p := ((↑(u⁻¹) : PadicAlgCl.ringOfIntegers p K) : PadicAlgCl p) with hb
    have h1 : a * b = 1 := by
      rw [ha, hb, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have hbn : ‖b‖ ≤ 1 := PadicAlgCl.ringOfIntegers.norm_coe_le_one p K _
    have hab : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, h1, norm_one]
    nlinarith [norm_nonneg a, norm_nonneg b]

theorem ramificationIdx_mul_inertiaDeg [IsDiscreteValuationRing (PadicAlgCl.ringOfIntegers p K)]
    [Module.Finite ℤ_[p] (PadicAlgCl.ringOfIntegers p K)] :
    (IsLocalRing.maximalIdeal ℤ_[p]).ramificationIdx' (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K)) *
      (IsLocalRing.maximalIdeal ℤ_[p]).inertiaDeg' (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K)) =
        Module.finrank ℚ_[p] K :=
  Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (PadicAlgCl.ringOfIntegers p K) ℚ_[p] K
    (IsDiscreteValuationRing.not_a_field ℤ_[p])

end RingOfIntegers

section Place

variable (Pl : ValuationSubring (AlgebraicClosure ℚ))
  (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) (hιP : ∀ t : AlgebraicClosure ℚ, t ∈ Pl ↔ ‖ι t‖ ≤ 1)

include hιP in

theorem valuation_lt_one_iff_norm_lt_one (t : AlgebraicClosure ℚ) :
    Pl.valuation t < 1 ↔ ‖ι t‖ < 1 := by
  by_cases ht : t = 0
  · subst ht
    simp
  · have hιt : ι t ≠ 0 := (map_ne_zero ι).2 ht
    have hvt : 0 < Pl.valuation t := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht)
    have key : 1 ≤ Pl.valuation t ↔ 1 ≤ ‖ι t‖ := by
      rw [← inv_le_one₀ hvt, ← map_inv₀, ValuationSubring.valuation_le_one_iff, hιP, map_inv₀, norm_inv,
        inv_le_one₀ (norm_pos_iff.2 hιt)]
    rw [← not_le, key, not_le]

variable (Rh : Type) [CommRing Rh] [IsDomain Rh] [IsDiscreteValuationRing Rh]
  [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
  (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
  (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

include hRA hιP in
theorem norm_apply_algebraMap_le_one (x : Rh) : ‖ι (algebraMap Rh (AlgebraicClosure ℚ) x)‖ ≤ 1 :=
  (hιP _).1 (hRA x)

include hRloc hιP in
theorem mem_maximalIdeal_iff_norm_apply_lt_one (x : Rh) :
    x ∈ IsLocalRing.maximalIdeal Rh ↔ ‖ι (algebraMap Rh (AlgebraicClosure ℚ) x)‖ < 1 :=
  (hRloc x).trans (valuation_lt_one_iff_norm_lt_one p Pl ι hιP _)

include hRA hιP in
theorem norm_apply_algebraMap_unit (u : Rhˣ) : ‖ι (algebraMap Rh (AlgebraicClosure ℚ) (u : Rh))‖ = 1 := by
  have h1 := norm_apply_algebraMap_le_one p Pl ι hιP Rh hRA (u : Rh)
  have h2 := norm_apply_algebraMap_le_one p Pl ι hιP Rh hRA ((u⁻¹ : Rhˣ) : Rh)
  have h12 : ‖ι (algebraMap Rh (AlgebraicClosure ℚ) (u : Rh))‖ *
      ‖ι (algebraMap Rh (AlgebraicClosure ℚ) ((u⁻¹ : Rhˣ) : Rh))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  nlinarith [norm_nonneg (ι (algebraMap Rh (AlgebraicClosure ℚ) (u : Rh))),
    norm_nonneg (ι (algebraMap Rh (AlgebraicClosure ℚ) ((u⁻¹ : Rhˣ) : Rh)))]

include hRloc in

theorem exists_eq_algebraMap_of_mul_natCast_eq {a : AlgebraicClosure ℚ} {r : Rh} {N : ℕ} (hN : N ≠ 0)
    (h : a * N = algebraMap Rh (AlgebraicClosure ℚ) r) (ha : a ∈ Pl) :
    ∃ r' : Rh, a = algebraMap Rh (AlgebraicClosure ℚ) r' := by
  have hinj : Function.Injective (algebraMap Rh (AlgebraicClosure ℚ)) :=
    FaithfulSMul.algebraMap_injective Rh (AlgebraicClosure ℚ)
  have hNq : ((N : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond r (N : Rh)
  ·
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hc
      apply hNq
      rw [← map_natCast (algebraMap Rh (AlgebraicClosure ℚ)), ← hc, map_zero]
    have hac : a * algebraMap Rh (AlgebraicClosure ℚ) c = 1 := by
      have h' : (a * algebraMap Rh (AlgebraicClosure ℚ) c) * algebraMap Rh (AlgebraicClosure ℚ) r =
          1 * algebraMap Rh (AlgebraicClosure ℚ) r := by
        rw [one_mul, mul_assoc, ← map_mul, mul_comm c r, hc, map_natCast, h]
      exact mul_right_cancel₀ ((map_ne_zero_iff _ hinj).2 hr0) h'
    by_cases hu : IsUnit c
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨((u⁻¹ : Rhˣ) : Rh), ?_⟩
      calc a = a * (algebraMap Rh (AlgebraicClosure ℚ) (u : Rh) *
            algebraMap Rh (AlgebraicClosure ℚ) ((u⁻¹ : Rhˣ) : Rh)) := by
              rw [← map_mul, Units.mul_inv, map_one, mul_one]
        _ = algebraMap Rh (AlgebraicClosure ℚ) ((u⁻¹ : Rhˣ) : Rh) := by rw [← mul_assoc, hac, one_mul]
    · exfalso
      have hcm : c ∈ IsLocalRing.maximalIdeal Rh := (IsLocalRing.mem_maximalIdeal c).2 hu
      have hvc : Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) c) < 1 := (hRloc c).1 hcm
      have hva : Pl.valuation a ≤ 1 := (Pl.valuation_le_one_iff a).2 ha
      have hlt : Pl.valuation (a * algebraMap Rh (AlgebraicClosure ℚ) c) < 1 := by
        rw [map_mul]
        calc Pl.valuation a * Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) c)
            ≤ 1 * Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) c) := mul_le_mul_left hva _
          _ < 1 := by rw [one_mul]; exact hvc
      rw [hac, map_one] at hlt
      exact lt_irrefl _ hlt
  ·
    refine ⟨c, mul_left_cancel₀ hNq ?_⟩
    rw [mul_comm, h, ← hc, map_mul, map_natCast]

theorem exists_norm_sub_apply_lt (T : Set (PadicAlgCl p))
    (hT : T ⊆ Set.range (fun x : Rh => ι (algebraMap Rh (AlgebraicClosure ℚ) x)))
    {u : PadicAlgCl p} (hu : u ∈ IntermediateField.adjoin ℚ_[p] T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : AlgebraicClosure ℚ) (r : Rh) (N : ℕ),
      N ≠ 0 ∧ a * N = algebraMap Rh (AlgebraicClosure ℚ) r ∧ ‖u - ι a‖ < ε := by
  classical

  have halg : ∀ x ∈ T, IsAlgebraic ℚ_[p] x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  have hu' : u ∈ Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] T) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact hu
  rw [Algebra.adjoin_eq_span, Submodule.mem_span_set'] at hu'
  obtain ⟨n, c, m, hsum⟩ := hu'

  let φ : Rh →* PadicAlgCl p :=
    (ι : AlgebraicClosure ℚ →* PadicAlgCl p).comp (algebraMap Rh (AlgebraicClosure ℚ) : Rh →* AlgebraicClosure ℚ)
  have hcl : Submonoid.closure T ≤ MonoidHom.mrange φ :=
    Submonoid.closure_le.2 fun x hx => by obtain ⟨r, hr⟩ := hT hx; exact ⟨r, hr⟩
  have hm : ∀ i, ∃ r : Rh, ι (algebraMap Rh (AlgebraicClosure ℚ) r) = (m i : PadicAlgCl p) := fun i => by
    obtain ⟨r, hr⟩ := hcl (m i).2
    exact ⟨r, hr⟩
  choose r hr using hm

  set B : ℝ := ∑ i, ‖(m i : PadicAlgCl p)‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => norm_nonneg _
  set δ : ℝ := ε / (B + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hq : ∀ i, ∃ q : ℚ, ‖c i - (q : ℚ_[p])‖ < δ := fun i => Padic.rat_dense p (c i) hδ0
  choose q hq using hq

  set N : ℕ := ∏ i, (q i).den with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (q i).den_nz
  have hz : ∀ i, ∃ z : ℤ, (q i : ℚ) * N = z := fun i => by
    refine ⟨(q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ), ?_⟩
    rw [hN, ← Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ i)]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  choose z hz using hz
  refine ⟨∑ i, (q i : AlgebraicClosure ℚ) * algebraMap Rh (AlgebraicClosure ℚ) (r i), ∑ i, z i • r i, N, hN0,
    ?_, ?_⟩
  · rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hzi : ((q i : ℚ) : AlgebraicClosure ℚ) * (N : AlgebraicClosure ℚ) = ((z i : ℤ) : AlgebraicClosure ℚ) := by
      exact_mod_cast hz i
    rw [map_zsmul, zsmul_eq_mul, mul_right_comm, hzi]
  · have hιa : ι (∑ i, (q i : AlgebraicClosure ℚ) * algebraMap Rh (AlgebraicClosure ℚ) (r i)) =
        ∑ i, ((q i : ℚ) : ℚ_[p]) • (m i : PadicAlgCl p) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_ratCast, hr, Algebra.smul_def, map_ratCast]
    rw [hιa, ← hsum, ← Finset.sum_sub_distrib]
    calc ‖∑ i, (c i • (m i : PadicAlgCl p) - ((q i : ℚ) : ℚ_[p]) • (m i : PadicAlgCl p))‖
        ≤ ∑ i, ‖c i • (m i : PadicAlgCl p) - ((q i : ℚ) : ℚ_[p]) • (m i : PadicAlgCl p)‖ := norm_sum_le _ _
      _ ≤ ∑ i, δ * ‖(m i : PadicAlgCl p)‖ := Finset.sum_le_sum fun i _ => by
          rw [← sub_smul, norm_smul]
          exact mul_le_mul_of_nonneg_right (hq i).le (norm_nonneg _)
      _ = δ * B := by rw [← Finset.mul_sum]
      _ < ε := by
          rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith

end Place

section Bounds

theorem norm_sub_le_max' (x y : PadicAlgCl p) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max x (-y)

variable (Pl : ValuationSubring (AlgebraicClosure ℚ))
  (Rh : Type) [CommRing Rh] [IsDomain Rh] [IsDiscreteValuationRing Rh]
  [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
  (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
  (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
  (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) (hιP : ∀ t : AlgebraicClosure ℚ, t ∈ Pl ↔ ‖ι t‖ ≤ 1)
  (T : Set (PadicAlgCl p)) (hT : T ⊆ Set.range (fun x : Rh => ι (algebraMap Rh (AlgebraicClosure ℚ) x)))

include hRloc hιP hT in

theorem inertiaDeg_le_one [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] T)]
    [IsDiscreteValuationRing (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T))] :
    (IsLocalRing.maximalIdeal ℤ_[p]).inertiaDeg'
      (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T))) ≤ 1 := by
  classical
  unfold Ideal.inertiaDeg'
  split_ifs with hcomap
  · letI : Algebra (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
        (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T) ⧸
          IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T))) :=
      Ideal.Quotient.algebraQuotientOfLEComap hcomap.ge
    refine finrank_le_one (1 : PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T) ⧸
          IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T))) ?_
    intro w
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w

    obtain ⟨a, r, N, hN, hmul, hlt⟩ := exists_norm_sub_apply_lt p ι Rh T hT
      (u := (x : PadicAlgCl p)) (PadicAlgCl.ringOfIntegers.coe_mem x) one_pos
    have hιa : ‖ι a‖ ≤ 1 :=
      calc ‖ι a‖ = ‖(x : PadicAlgCl p) - ((x : PadicAlgCl p) - ι a)‖ := by rw [sub_sub_cancel]
        _ ≤ max ‖(x : PadicAlgCl p)‖ ‖(x : PadicAlgCl p) - ι a‖ := norm_sub_le_max' p _ _
        _ ≤ 1 := max_le (PadicAlgCl.ringOfIntegers.norm_coe_le_one p _ x) hlt.le
    obtain ⟨r', rfl⟩ := exists_eq_algebraMap_of_mul_natCast_eq Pl Rh hRloc hN hmul ((hιP a).2 hιa)

    set m : ℕ := (algebraMap Rh (ZMod p) r').val with hm
    have hrm : ‖ι (algebraMap Rh (AlgebraicClosure ℚ) r') - (m : PadicAlgCl p)‖ < 1 := by
      have h0 : algebraMap Rh (ZMod p) (r' - (m : Rh)) = 0 := by
        rw [map_sub, map_natCast, hm, ZMod.natCast_zmod_val, sub_self]
      have h1 := (hres _).1 h0
      rwa [valuation_lt_one_iff_norm_lt_one p Pl ι hιP, map_sub, map_sub, map_natCast, map_natCast] at h1
    have hxm : ‖(x : PadicAlgCl p) - (m : PadicAlgCl p)‖ < 1 :=
      calc ‖(x : PadicAlgCl p) - (m : PadicAlgCl p)‖
          = ‖((x : PadicAlgCl p) - ι (algebraMap Rh (AlgebraicClosure ℚ) r')) +
              (ι (algebraMap Rh (AlgebraicClosure ℚ) r') - (m : PadicAlgCl p))‖ := by rw [sub_add_sub_cancel]
        _ ≤ max ‖(x : PadicAlgCl p) - ι (algebraMap Rh (AlgebraicClosure ℚ) r')‖
              ‖ι (algebraMap Rh (AlgebraicClosure ℚ) r') - (m : PadicAlgCl p)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ < 1 := max_lt hlt hrm
    have hmem : x - (m : PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T)) ∈
        IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T)) := by
      rw [mem_maximalIdeal_iff_norm_lt_one, Subalgebra.coe_sub, SubringClass.coe_natCast]
      exact hxm
    refine ⟨Ideal.Quotient.mk _ (m : ℤ_[p]), ?_⟩
    rw [Algebra.smul_def, mul_one]
    change Ideal.Quotient.mk _ (algebraMap ℤ_[p] (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T))
      (m : ℤ_[p])) = Ideal.Quotient.mk _ x
    rw [map_natCast, eq_comm, Ideal.Quotient.eq]
    exact hmem
  · exact zero_le_one

include hRA hRloc hιP hT in

theorem ramificationIdx_le [FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] T)]
    [IsDiscreteValuationRing (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T))]
    {ϖ : Rh} (hϖ : Irreducible ϖ) {v : ℕ} {w : Rhˣ} (hpv : (p : Rh) = w * ϖ ^ v) :
    (IsLocalRing.maximalIdeal ℤ_[p]).ramificationIdx'
      (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T))) ≤ v := by
  classical
  have hinj : Function.Injective (algebraMap Rh (AlgebraicClosure ℚ)) :=
    FaithfulSMul.algebraMap_injective Rh (AlgebraicClosure ℚ)
  set ρ : ℝ := ‖ι (algebraMap Rh (AlgebraicClosure ℚ) ϖ)‖ with hρ
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal Rh := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have hρ1 : ρ < 1 := (mem_maximalIdeal_iff_norm_apply_lt_one p Pl ι hιP Rh hRloc ϖ).1 hϖm
  have hρ0 : 0 < ρ :=
    norm_pos_iff.2 ((map_ne_zero ι).2 ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero))

  have h1 : ∀ x ∈ IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T)),
      ‖(x : PadicAlgCl p)‖ ≤ ρ := by
    intro x hx
    have hx1 := (mem_maximalIdeal_iff_norm_lt_one p _ x).1 hx
    by_cases hx0 : (x : PadicAlgCl p) = 0
    · rw [hx0, norm_zero]; exact hρ0.le
    obtain ⟨a, r, N, hN, hmul, hlt⟩ := exists_norm_sub_apply_lt p ι Rh T hT
      (u := (x : PadicAlgCl p)) (PadicAlgCl.ringOfIntegers.coe_mem x) (norm_pos_iff.2 hx0)
    have hnorm : ‖ι a‖ = ‖(x : PadicAlgCl p)‖ := by
      apply le_antisymm
      · calc ‖ι a‖ = ‖(x : PadicAlgCl p) - ((x : PadicAlgCl p) - ι a)‖ := by rw [sub_sub_cancel]
          _ ≤ max ‖(x : PadicAlgCl p)‖ ‖(x : PadicAlgCl p) - ι a‖ := norm_sub_le_max' p _ _
          _ = ‖(x : PadicAlgCl p)‖ := max_eq_left hlt.le
      · have h := IsUltrametricDist.norm_add_le_max ((x : PadicAlgCl p) - ι a) (ι a)
        rw [sub_add_cancel] at h
        rcases le_max_iff.1 h with h | h
        · exact absurd h (not_le.2 hlt)
        · exact h
    obtain ⟨r', rfl⟩ := exists_eq_algebraMap_of_mul_natCast_eq Pl Rh hRloc hN hmul
      ((hιP a).2 (by rw [hnorm]; exact hx1.le))
    have hr'm : r' ∈ IsLocalRing.maximalIdeal Rh :=
      (mem_maximalIdeal_iff_norm_apply_lt_one p Pl ι hιP Rh hRloc r').2 (by rw [hnorm]; exact hx1)
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at hr'm
    obtain ⟨b, rfl⟩ := hr'm
    rw [← hnorm, map_mul, map_mul, norm_mul]
    calc ‖ι (algebraMap Rh (AlgebraicClosure ℚ) b)‖ * ρ ≤ 1 * ρ :=
          mul_le_mul_of_nonneg_right (norm_apply_algebraMap_le_one p Pl ι hιP Rh hRA b) hρ0.le
      _ = ρ := one_mul ρ

  have hk : ∀ k : ℕ, ∀ x ∈ IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T)) ^ k,
      ‖(x : PadicAlgCl p)‖ ≤ ρ ^ k := by
    intro k
    induction k with
    | zero =>
        intro x _
        rw [pow_zero]
        exact PadicAlgCl.ringOfIntegers.norm_coe_le_one p _ x
    | succ k ih =>
        intro x hx
        rw [pow_succ] at hx
        refine Submodule.mul_induction_on hx ?_ ?_
        · intro y hy z hz
          rw [Subalgebra.coe_mul, norm_mul, pow_succ]
          exact mul_le_mul (ih y hy) (h1 z hz) (norm_nonneg _) (pow_nonneg hρ0.le _)
        · intro y z hy hz
          rw [Subalgebra.coe_add]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hz)

  have hlt : (IsLocalRing.maximalIdeal ℤ_[p]).ramificationIdx'
      (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T))) < v + 1 := by
    apply Ideal.ramificationIdx_lt
    intro hle
    have hpmem : ((p : ℕ) : PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T)) ∈
        IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T)) ^ (v + 1) := by
      apply hle
      rw [← map_natCast (algebraMap ℤ_[p] (PadicAlgCl.ringOfIntegers p (IntermediateField.adjoin ℚ_[p] T)))]
      apply Ideal.mem_map_of_mem
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    have h2 := hk (v + 1) _ hpmem
    rw [SubringClass.coe_natCast] at h2
    have hpnorm : ‖((p : ℕ) : PadicAlgCl p)‖ = ρ ^ v := by
      have : ((p : ℕ) : PadicAlgCl p) = ι (algebraMap Rh (AlgebraicClosure ℚ) (p : Rh)) := by
        rw [map_natCast, map_natCast]
      rw [this, hpv, map_mul, map_mul, norm_mul, norm_apply_algebraMap_unit p Pl ι hιP Rh hRA w, one_mul,
        map_pow, map_pow, norm_pow]
    rw [hpnorm] at h2
    have h3 : ρ ^ (v + 1) < ρ ^ v := pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 (Nat.lt_succ_self v)
    linarith
  omega

include hRA hRloc hιP hT in

theorem main [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Finite T] :
    FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] T) ∧
      ((Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] T) : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal Rh (p : Rh) := by
  classical
  haveI hfd : FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  refine ⟨hfd, ?_⟩
  obtain ⟨hfin, hdvr, -⟩ :=
    PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p (IntermediateField.adjoin ℚ_[p] T)

  have hp0 : (p : Rh) ≠ 0 := by
    intro h
    have h' : ((p : ℕ) : AlgebraicClosure ℚ) = 0 := by
      rw [← map_natCast (algebraMap Rh (AlgebraicClosure ℚ)), h, map_zero]
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h')
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rh
  obtain ⟨v, w, hpv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  rw [IsDiscreteValuationRing.addVal_def (p : Rh) w hϖ v hpv, Nat.cast_le,
    ← ramificationIdx_mul_inertiaDeg p (IntermediateField.adjoin ℚ_[p] T)]
  calc _ ≤ v * 1 := Nat.mul_le_mul (ramificationIdx_le p Pl Rh hRA hRloc ι hιP T hT hϖ hpv)
        (inertiaDeg_le_one p Pl Rh hRloc ι hιP T hT hres)
    _ = v := mul_one v

end Bounds

end LocalDegreeBound
p2m_reactivate "P2MW.S_ValuationSubring_finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime.LocalDegreeBound"

theorem solution
    (p : ℕ) [Fact p.Prime]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh] [IsDiscreteValuationRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    (ι : AlgebraicClosure ℚ →+* PadicAlgCl p) (hιP : ∀ t : AlgebraicClosure ℚ, t ∈ Pl ↔ ‖ι t‖ ≤ 1)
    (s : Finset Rh) :
    FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p]
        ((fun x : Rh => ι (algebraMap Rh (AlgebraicClosure ℚ) x)) '' (↑s : Set Rh))) ∧
      ((Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p]
        ((fun x : Rh => ι (algebraMap Rh (AlgebraicClosure ℚ) x)) '' (↑s : Set Rh))) : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal Rh (p : Rh) :=
  LocalDegreeBound.main p Pl Rh hRA hRloc ι hιP _ (Set.image_subset_range _ _) hres

end
p2m_reactivate "P2MW.S_ValuationSubring_finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime.LocalDegreeBound"

end S_ValuationSubring_finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_finrank_adjoin_image_le_addVal_of_isDiscreteValuationRing_of_liesOverPrime (solution)
