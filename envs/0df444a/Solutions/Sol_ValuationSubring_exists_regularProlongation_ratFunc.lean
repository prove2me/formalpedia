-- Prove2me | solution 1 for ValuationSubring.exists_regularProlongation_ratFunc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/39924f49-cad3-5403-bb5d-50537223b877

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_regularProlongation_ratFunc

set_option autoImplicit false

namespace GaussVal

open Polynomial IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

local notation "k" => IsLocalRing.ResidueField A
local notation "ι" => (algebraMap A L : A →+* L)
local notation "red" => (IsLocalRing.residue A : A →+* k)

theorem residue_ne_zero_iff (a : A) : red a ≠ 0 ↔ IsUnit a := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem exists_isUnit_coeff {q : Polynomial A} (hq : q.map red ≠ 0) : ∃ i, IsUnit (q.coeff i) := by
  by_contra h
  push Not at h
  apply hq
  ext i
  rw [coeff_map, coeff_zero]
  exact not_not.mp fun hne => h i ((residue_ne_zero_iff A _).mp hne)

theorem map_ne_zero_of_isUnit_coeff {q : Polynomial A} {i : ℕ} (h : IsUnit (q.coeff i)) : q.map red ≠ 0 := by
  intro h0
  have := congrArg (fun p => p.coeff i) h0
  simp only [coeff_map, coeff_zero] at this
  exact (residue_ne_zero_iff A _).mpr h this

theorem map_algebraMap_ne_zero {q : Polynomial A} (hq : q.map red ≠ 0) : q.map ι ≠ 0 := by
  intro h0
  apply hq
  have : q = 0 := (Polynomial.map_injective ι (IsFractionRing.injective A L)) (by rw [h0, Polynomial.map_zero])
  rw [this, Polynomial.map_zero]

theorem exists_eq_C_mul_map {f : Polynomial L} (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ p : Polynomial A, p.map red ≠ 0 ∧ f = C c * p.map ι := by
  classical

  let v := A.valuation
  have hsupp : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image f.support (fun i => v (f.coeff i)) hsupp
  set c := f.coeff i₀ with hc
  have hc0 : c ≠ 0 := Polynomial.mem_support_iff.mp hi₀

  have hmem : ∀ i, c⁻¹ * f.coeff i ∈ A := by
    intro i
    by_cases hi : i ∈ f.support
    · rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
      have hvc : v c ≠ 0 := (map_ne_zero v).mpr hc0
      calc (v c)⁻¹ * v (f.coeff i) ≤ (v c)⁻¹ * v c := by
            gcongr
            exact hmax i hi
        _ = 1 := inv_mul_cancel₀ hvc
    · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]
      exact A.zero_mem

  have hlifts : (C c⁻¹ * f) ∈ Polynomial.lifts ι := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_C_mul]
    exact ⟨⟨_, hmem i⟩, rfl⟩
  obtain ⟨p, hp⟩ := hlifts
  rw [coe_mapRingHom] at hp
  refine ⟨c, hc0, p, ?_, ?_⟩
  · apply map_ne_zero_of_isUnit_coeff A (i := i₀)
    have hpi : ι (p.coeff i₀) = c⁻¹ * c := by
      have := congrArg (fun q => q.coeff i₀) hp
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
      rw [this, hc]
    rw [inv_mul_cancel₀ hc0] at hpi
    have : p.coeff i₀ = 1 := (IsFractionRing.injective A L) (by rw [hpi, map_one])
    rw [this]
    exact isUnit_one
  · rw [hp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]

theorem map_mul_ne_zero {p q : Polynomial A} (hp : p.map red ≠ 0) (hq : q.map red ≠ 0) :
    (p * q).map red ≠ 0 := by
  rw [Polynomial.map_mul]
  exact mul_ne_zero hp hq

end GaussVal

namespace GaussVal

open Polynomial IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

local notation "k" => IsLocalRing.ResidueField A
local notation "ι" => (algebraMap A L : A →+* L)
local notation "red" => (IsLocalRing.residue A : A →+* k)
local notation "π" => (algebraMap (Polynomial L) (RatFunc L) : Polynomial L →+* RatFunc L)
local notation "πk" => (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))

theorem π_injective : Function.Injective π := IsFractionRing.injective _ _

theorem π_map_ne_zero {q : Polynomial A} (hq : q.map red ≠ 0) : π (q.map ι) ≠ 0 :=
  (map_ne_zero_iff π (π_injective)).mpr (map_algebraMap_ne_zero A hq)

def carrier : Set (RatFunc L) :=
  {f | ∃ p q : Polynomial A, q.map red ≠ 0 ∧ f = π (p.map ι) / π (q.map ι)}

theorem mem_carrier_iff {f : RatFunc L} :
    f ∈ carrier A ↔ ∃ p q : Polynomial A, q.map red ≠ 0 ∧ f = π (p.map ι) / π (q.map ι) := Iff.rfl

theorem mk_mem (p q : Polynomial A) (hq : q.map red ≠ 0) : π (p.map ι) / π (q.map ι) ∈ carrier A :=
  ⟨p, q, hq, rfl⟩

def subring : Subring (RatFunc L) where
  carrier := carrier A
  mul_mem' := by
    rintro _ _ ⟨p, q, hq, rfl⟩ ⟨p', q', hq', rfl⟩
    refine ⟨p * p', q * q', map_mul_ne_zero A hq hq', ?_⟩
    rw [Polynomial.map_mul, Polynomial.map_mul, map_mul, map_mul, div_mul_div_comm]
  one_mem' := ⟨1, 1, by rw [Polynomial.map_one]; exact one_ne_zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨p, q, hq, rfl⟩ ⟨p', q', hq', rfl⟩
    refine ⟨p * q' + p' * q, q * q', map_mul_ne_zero A hq hq', ?_⟩
    rw [div_add_div _ _ (π_map_ne_zero A hq) (π_map_ne_zero A hq')]
    simp only [Polynomial.map_mul, Polynomial.map_add, map_mul, map_add]
    ring
  zero_mem' := ⟨0, 1, by rw [Polynomial.map_one]; exact one_ne_zero, by simp⟩
  neg_mem' := by
    rintro _ ⟨p, q, hq, rfl⟩
    exact ⟨-p, q, hq, by rw [Polynomial.map_neg, map_neg, neg_div]⟩

theorem mem_subring_iff {f : RatFunc L} : f ∈ subring A ↔ f ∈ carrier A := Iff.rfl

theorem algebraMap_eq_π_C (c : L) : algebraMap L (RatFunc L) c = π (C c) := by
  rw [IsScalarTower.algebraMap_apply L (Polynomial L) (RatFunc L), Polynomial.algebraMap_eq]

theorem π_C_mul_div (c d : L) (hd : d ≠ 0) (P Q : Polynomial L) :
    π (C c * P) / π (C d * Q) = algebraMap L (RatFunc L) (c / d) * (π P / π Q) := by
  have hπd : π (C d) ≠ 0 := (map_ne_zero_iff π (π_injective)).mpr (by simpa using hd)
  have hC : C c = C (c / d) * C d := by rw [← C_mul, div_mul_cancel₀ c hd]
  rw [hC, map_mul, map_mul, map_mul, algebraMap_eq_π_C, mul_comm (π (C d)) (π Q), mul_assoc,
    mul_comm (π (C d)) (π P), ← mul_assoc, mul_div_mul_right _ _ hπd, mul_div_assoc]

end GaussVal

namespace GaussVal

open Polynomial IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

local notation "k" => IsLocalRing.ResidueField A
local notation "ι" => (algebraMap A L : A →+* L)
local notation "red" => (IsLocalRing.residue A : A →+* k)
local notation "π" => (algebraMap (Polynomial L) (RatFunc L) : Polynomial L →+* RatFunc L)
local notation "πk" => (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))

theorem map_C_mul (a : A) (p : Polynomial A) : (C a * p).map ι = C (ι a) * p.map ι := by
  rw [Polynomial.map_mul, map_C]

theorem exists_decomp {f : RatFunc L} (hf : f ≠ 0) :
    ∃ c d : L, c ≠ 0 ∧ d ≠ 0 ∧ ∃ p₀ q₀ : Polynomial A, p₀.map red ≠ 0 ∧ q₀.map red ≠ 0 ∧
      f = algebraMap L (RatFunc L) (c / d) * (π (p₀.map ι) / π (q₀.map ι)) := by
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  obtain ⟨c, hc, p₀, hp₀, hnumeq⟩ := exists_eq_C_mul_map A hnum
  obtain ⟨d, hd, q₀, hq₀, hdeneq⟩ := exists_eq_C_mul_map A hden
  refine ⟨c, d, hc, hd, p₀, q₀, hp₀, hq₀, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom f, hnumeq, hdeneq]
  exact π_C_mul_div c d hd _ _

private theorem _root_.GaussVal.mem_or_inv_mem (f : RatFunc L) : f ∈ subring A ∨ f⁻¹ ∈ subring A := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact Or.inl (subring A).zero_mem
  obtain ⟨c, d, hc, hd, p₀, q₀, hp₀, hq₀, hfeq⟩ := exists_decomp A hf
  rcases A.mem_or_inv_mem (c / d) with h | h
  · left
    refine ⟨C ⟨c / d, h⟩ * p₀, q₀, hq₀, ?_⟩
    rw [hfeq, map_C_mul, map_mul, ← algebraMap_eq_π_C, mul_div_assoc]
    rfl
  · right
    refine ⟨C ⟨(c / d)⁻¹, h⟩ * q₀, p₀, hp₀, ?_⟩
    rw [hfeq, mul_inv, inv_div, map_C_mul, map_mul, ← algebraMap_eq_π_C, mul_div_assoc, ← map_inv₀]
    rfl

p2m_export "GaussVal" "mem_or_inv_mem"

def O : ValuationSubring (RatFunc L) :=
  { subring A with mem_or_inv_mem' := mem_or_inv_mem A }

theorem mem_O_iff {f : RatFunc L} :
    f ∈ O A ↔ ∃ p q : Polynomial A, q.map red ≠ 0 ∧ f = π (p.map ι) / π (q.map ι) := Iff.rfl

theorem mul_eq_mul_of_div_eq_div {p q p' q' : Polynomial A} (hq : q.map red ≠ 0) (hq' : q'.map red ≠ 0)
    (h : π (p.map ι) / π (q.map ι) = π (p'.map ι) / π (q'.map ι)) : p * q' = p' * q := by
  rw [div_eq_div_iff (π_map_ne_zero A hq) (π_map_ne_zero A hq'), ← map_mul, ← map_mul] at h
  have h2 := π_injective h
  rw [← Polynomial.map_mul, ← Polynomial.map_mul] at h2
  exact Polynomial.map_injective ι (IsFractionRing.injective A L) h2

theorem πk_map_ne_zero {q : Polynomial A} (hq : q.map red ≠ 0) : πk (q.map red) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq

theorem res_wd {p q p' q' : Polynomial A} (hq : q.map red ≠ 0) (hq' : q'.map red ≠ 0)
    (h : π (p.map ι) / π (q.map ι) = π (p'.map ι) / π (q'.map ι)) :
    πk (p.map red) / πk (q.map red) = πk (p'.map red) / πk (q'.map red) := by
  rw [div_eq_div_iff (πk_map_ne_zero A hq) (πk_map_ne_zero A hq'), ← map_mul, ← map_mul,
    ← Polynomial.map_mul, ← Polynomial.map_mul, mul_eq_mul_of_div_eq_div A hq hq' h]

private noncomputable def _root_.GaussVal.num (f : O A) : Polynomial A := Classical.choose f.2
p2m_export "GaussVal" "num"
noncomputable def den (f : O A) : Polynomial A := Classical.choose (Classical.choose_spec f.2)
theorem den_spec (f : O A) : (den A f).map red ≠ 0 := (Classical.choose_spec (Classical.choose_spec f.2)).1
theorem rep_spec (f : O A) : (f : RatFunc L) = π ((num A f).map ι) / π ((den A f).map ι) :=
  (Classical.choose_spec (Classical.choose_spec f.2)).2

noncomputable def resFun (f : O A) : RatFunc (IsLocalRing.ResidueField A) :=
  πk ((num A f).map red) / πk ((den A f).map red)

theorem resFun_eq (f : O A) {p q : Polynomial A} (hq : q.map red ≠ 0)
    (hf : (f : RatFunc L) = π (p.map ι) / π (q.map ι)) :
    resFun A f = πk (p.map red) / πk (q.map red) :=
  res_wd A (den_spec A f) hq ((rep_spec A f).symm.trans hf)

noncomputable def res : O A →+* RatFunc (IsLocalRing.ResidueField A) where
  toFun := resFun A
  map_one' := by
    rw [resFun_eq A 1 (p := 1) (q := 1) (by rw [Polynomial.map_one]; exact one_ne_zero) (by simp)]
    simp
  map_mul' f g := by
    obtain ⟨p, q, hq, hf⟩ := (mem_O_iff A).mp f.2
    obtain ⟨p', q', hq', hg⟩ := (mem_O_iff A).mp g.2
    rw [resFun_eq A f hq hf, resFun_eq A g hq' hg,
      resFun_eq A (f * g) (p := p * p') (q := q * q') (map_mul_ne_zero A hq hq') ?_]
    · simp only [Polynomial.map_mul, map_mul, div_mul_div_comm]
    · rw [MulMemClass.coe_mul, hf, hg, div_mul_div_comm, ← map_mul, ← map_mul, ← Polynomial.map_mul,
        ← Polynomial.map_mul]
  map_zero' := by
    rw [resFun_eq A 0 (p := 0) (q := 1) (by rw [Polynomial.map_one]; exact one_ne_zero) (by simp)]
    simp
  map_add' f g := by
    obtain ⟨p, q, hq, hf⟩ := (mem_O_iff A).mp f.2
    obtain ⟨p', q', hq', hg⟩ := (mem_O_iff A).mp g.2
    rw [resFun_eq A f hq hf, resFun_eq A g hq' hg,
      resFun_eq A (f + g) (p := p * q' + p' * q) (q := q * q') (map_mul_ne_zero A hq hq') ?_]
    · rw [div_add_div _ _ (πk_map_ne_zero A hq) (πk_map_ne_zero A hq')]
      simp only [Polynomial.map_mul, Polynomial.map_add, map_mul, map_add]
      ring
    · rw [AddMemClass.coe_add, hf, hg, div_add_div _ _ (π_map_ne_zero A hq) (π_map_ne_zero A hq')]
      simp only [Polynomial.map_mul, Polynomial.map_add, map_mul, map_add]
      ring

end GaussVal

namespace GaussVal

open Polynomial IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

local notation "k" => IsLocalRing.ResidueField A
local notation "ι" => (algebraMap A L : A →+* L)
local notation "red" => (IsLocalRing.residue A : A →+* k)
local notation "π" => (algebraMap (Polynomial L) (RatFunc L) : Polynomial L →+* RatFunc L)
local notation "πk" => (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))

theorem res_apply (f : O A) {p q : Polynomial A} (hq : q.map red ≠ 0)
    (hf : (f : RatFunc L) = π (p.map ι) / π (q.map ι)) :
    res A f = πk (p.map red) / πk (q.map red) := resFun_eq A f hq hf

theorem isUnit_iff (f : O A) {p q : Polynomial A} (hq : q.map red ≠ 0)
    (hf : (f : RatFunc L) = π (p.map ι) / π (q.map ι)) : IsUnit f ↔ p.map red ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ hp
    obtain ⟨p', q', hq', hg⟩ := (mem_O_iff A).mp ((u⁻¹ : (O A)ˣ) : O A).2
    have h2 : (((u : O A) * ((u⁻¹ : (O A)ˣ) : O A) : O A) : RatFunc L) = 1 := by
      rw [Units.mul_inv]; rfl
    rw [MulMemClass.coe_mul, hf, hg, div_mul_div_comm, ← map_mul, ← map_mul, ← Polynomial.map_mul,
      ← Polynomial.map_mul] at h2
    have h3 : π ((p * p').map ι) / π ((q * q').map ι) = π ((1 : Polynomial A).map ι) / π ((1 : Polynomial A).map ι) := by
      rw [h2]; simp
    have h4 := mul_eq_mul_of_div_eq_div A (map_mul_ne_zero A hq hq') (by simp) h3
    have h5 := congrArg (Polynomial.map red) h4
    simp only [mul_one, one_mul, Polynomial.map_mul] at h5
    have : (q * q').map red = 0 := by rw [Polynomial.map_mul, ← h5, hp, zero_mul]
    exact map_mul_ne_zero A hq hq' this
  · intro hp
    refine ⟨⟨f, ⟨π (q.map ι) / π (p.map ι), (mem_O_iff A).mpr ⟨q, p, hp, rfl⟩⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show (f : RatFunc L) * (π (q.map ι) / π (p.map ι)) = 1
      rw [hf, div_mul_div_comm, mul_comm, div_self]
      exact mul_ne_zero (π_map_ne_zero A hq) (π_map_ne_zero A hp)
    · apply Subtype.ext
      show (π (q.map ι) / π (p.map ι)) * (f : RatFunc L) = 1
      rw [hf, div_mul_div_comm, mul_comm, div_self]
      exact mul_ne_zero (π_map_ne_zero A hp) (π_map_ne_zero A hq)

theorem res_eq_zero_iff (f : O A) {p q : Polynomial A} (hq : q.map red ≠ 0)
    (hf : (f : RatFunc L) = π (p.map ι) / π (q.map ι)) : res A f = 0 ↔ p.map red = 0 := by
  rw [res_apply A f hq hf, div_eq_zero_iff, or_iff_left (πk_map_ne_zero A hq),
    map_eq_zero_iff _ (IsFractionRing.injective _ _)]

theorem ker_res : RingHom.ker (res A) = IsLocalRing.maximalIdeal (O A) := by
  ext f
  obtain ⟨p, q, hq, hf⟩ := (mem_O_iff A).mp f.2
  rw [RingHom.mem_ker, res_eq_zero_iff A f hq hf, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff A f hq hf, not_not]

theorem res_surjective : Function.Surjective (res A) := by
  intro g
  obtain ⟨p, hp⟩ := Polynomial.map_surjective red IsLocalRing.residue_surjective g.num
  obtain ⟨q, hq⟩ := Polynomial.map_surjective red IsLocalRing.residue_surjective g.denom
  have hq0 : q.map red ≠ 0 := by rw [hq]; exact RatFunc.denom_ne_zero g
  refine ⟨⟨π (p.map ι) / π (q.map ι), p, q, hq0, rfl⟩, ?_⟩
  rw [res_apply A _ hq0 rfl, hp, hq, RatFunc.num_div_denom]

theorem algebraMap_mem_iff (x : L) : algebraMap L (RatFunc L) x ∈ O A ↔ x ∈ A := by
  constructor
  · rintro ⟨p, q, hq, h⟩
    rw [algebraMap_eq_π_C, eq_div_iff (π_map_ne_zero A hq), ← map_mul] at h
    have h2 := π_injective h
    obtain ⟨i, hi⟩ := exists_isUnit_coeff A hq
    have h3 := congrArg (fun r => r.coeff i) h2
    simp only [coeff_C_mul, coeff_map] at h3

    obtain ⟨u, hu⟩ := hi
    have hu0 : ι (q.coeff i) ≠ 0 := by
      rw [← hu]
      exact (map_ne_zero_iff ι (IsFractionRing.injective A L)).mpr (Units.ne_zero u)
    have hx : x = ι (p.coeff i) * (ι (q.coeff i))⁻¹ := by
      rw [← h3, mul_inv_cancel_right₀ hu0]
    have hinv : (ι (q.coeff i))⁻¹ = ι ((u⁻¹ : Aˣ) : A) := by
      rw [← hu]
      exact (eq_inv_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])).symm
    rw [hx, hinv, ← map_mul]
    exact ((p.coeff i * ((u⁻¹ : Aˣ) : A) : A)).2
  · intro hx
    refine ⟨C ⟨x, hx⟩, 1, by simp, ?_⟩
    rw [algebraMap_eq_π_C, map_C, Polynomial.map_one, map_one, div_one]
    rfl

end GaussVal

namespace GaussVal

open Polynomial IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

local notation "k" => IsLocalRing.ResidueField A
local notation "ι" => (algebraMap A L : A →+* L)
local notation "red" => (IsLocalRing.residue A : A →+* k)
local notation "π" => (algebraMap (Polynomial L) (RatFunc L) : Polynomial L →+* RatFunc L)
local notation "πk" => (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))

theorem π_map_mem (p : Polynomial A) : π (p.map ι) ∈ O A :=
  ⟨p, 1, by simp, by rw [Polynomial.map_one, map_one, div_one]⟩

theorem res_π_map (p : Polynomial A) : res A ⟨π (p.map ι), π_map_mem A p⟩ = πk (p.map red) := by
  rw [res_apply A _ (p := p) (q := 1) (by simp) (by simp), Polynomial.map_one, map_one, div_one]

theorem residue_algebraMap (a : A) :
    res A ⟨algebraMap L (RatFunc L) a, (algebraMap_mem_iff A a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) (red a) := by
  have h : (⟨algebraMap L (RatFunc L) a, (algebraMap_mem_iff A a).mpr a.2⟩ : O A) =
      ⟨π ((C a).map ι), π_map_mem A (C a)⟩ := by
    apply Subtype.ext
    show algebraMap L (RatFunc L) a = π ((C a).map ι)
    rw [map_C, ← algebraMap_eq_π_C]
    rfl
  rw [h, res_π_map, map_C, IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k), Polynomial.algebraMap_eq]

theorem exists_smul_mem (f : RatFunc L) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ O A, res A ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, d, hc, hd, p₀, q₀, hp₀, hq₀, hfeq⟩ := exists_decomp A hf
  have hsmul : (d / c) • f = π (p₀.map ι) / π (q₀.map ι) := by
    rw [Algebra.smul_def, hfeq, ← mul_assoc, ← map_mul, div_mul_div_cancel₀ hc, div_self hd, map_one, one_mul]
  refine ⟨d / c, hsmul ▸ mk_mem A p₀ q₀ hq₀, ?_⟩
  rw [Ne, res_eq_zero_iff A _ hq₀ hsmul]
  exact hp₀

theorem X_mem : (RatFunc.X : RatFunc L) ∈ O A :=
  ⟨X, 1, by simp, by rw [Polynomial.map_X, Polynomial.map_one, map_one, div_one, RatFunc.algebraMap_X]⟩

theorem res_X : res A ⟨RatFunc.X, X_mem A⟩ = RatFunc.X := by
  rw [res_apply A _ (p := X) (q := 1) (by simp) (by rw [Polynomial.map_X, Polynomial.map_one, map_one, div_one, RatFunc.algebraMap_X]),
    Polynomial.map_X, Polynomial.map_one, map_one, div_one, RatFunc.algebraMap_X]

end GaussVal

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L) :
    ∃ R : AlgebraicCurve.RegularProlongation A (RatFunc L) (RatFunc (IsLocalRing.ResidueField A)),
      (∃ hX : (RatFunc.X : RatFunc L) ∈ R.integers,
        R.residue ⟨RatFunc.X, hX⟩ = RatFunc.X) ∧
      (∀ p : Polynomial A, ∃ hp : algebraMap (Polynomial L) (RatFunc L) (p.map A.subtype) ∈ R.integers,
        R.residue ⟨algebraMap (Polynomial L) (RatFunc L) (p.map A.subtype), hp⟩ =
          algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A))
            (p.map (IsLocalRing.residue A))) := by
  let R : AlgebraicCurve.RegularProlongation A (RatFunc L) (RatFunc (IsLocalRing.ResidueField A)) :=
    ⟨GaussVal.O A, GaussVal.res A, GaussVal.algebraMap_mem_iff A, GaussVal.res_surjective A,
      GaussVal.ker_res A, GaussVal.residue_algebraMap A, GaussVal.exists_smul_mem A⟩
  exact ⟨R, ⟨GaussVal.X_mem A, GaussVal.res_X A⟩, fun p => ⟨GaussVal.π_map_mem A p, GaussVal.res_π_map A p⟩⟩

end S_ValuationSubring_exists_regularProlongation_ratFunc
end P2MW
export P2MW.S_ValuationSubring_exists_regularProlongation_ratFunc (solution)
