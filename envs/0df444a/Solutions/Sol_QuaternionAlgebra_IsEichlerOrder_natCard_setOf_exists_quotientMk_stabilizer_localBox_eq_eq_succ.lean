-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.natCard_setOf_exists_quotientMk_stabilizer_localBox_eq_eq_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c51b985d-562a-5938-a7a1-905d28df422a

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_natCard_setOf_exists_quotientMk_stabilizer_localBox_eq_eq_succ
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace TqLoc

section Places

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

variable (q : ℕ) (hq : q.Prime)

local notation "𝔳" => place q hq
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)

theorem primesEquiv_place : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) 𝔳 = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place : Rat.HeightOneSpectrum.natGenerator 𝔳 = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem eq_place_of_mem (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : w = 𝔳 := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [primesEquiv_place]
  apply Subtype.ext
  change Rat.HeightOneSpectrum.natGenerator w = q
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).1
    ((natCast_mem_asIdeal_iff w q).1 hw)

theorem natCast_mem_asIdeal_place_iff (n : ℕ) : (n : 𝓞 ℚ) ∈ (𝔳).asIdeal ↔ q ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

theorem asIdeal_place_eq_span : (𝔳).asIdeal = Ideal.span {(q : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) 𝔳
  rw [natGenerator_place] at h
  have h2 : (𝔳).asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) (𝔳).asIdeal) := by
    rw [Ideal.map_map]
    have : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ).comp
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) = RingHom.id _ := by
      ext x; simp
    rw [this, Ideal.map_id]
  rw [h2]
  erw [← h]
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp

theorem valuation_q : (𝔳).valuation ℚ (q : ℚ) = WithZero.exp (-1) := by
  rw [show (q : ℚ) = algebraMap (𝓞 ℚ) ℚ q from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (by exact_mod_cast hq.ne_zero) (asIdeal_place_eq_span q hq)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem algebraMap_natCast (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) = (n : w.adicCompletion ℚ) := map_natCast _ n

theorem valued_q : Valued.v ((q : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_q]

theorem q_ne_zero' : ((q : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_q q hq
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap,
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one w _

theorem q_mem_integers : ((q : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers _ q

theorem q_inv_notMem_integers : ((q : ℕ) : 𝕂)⁻¹ ∉ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_q, ← WithZero.exp_neg, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  norm_num

def toPadicInt [Fact q.Prime] : 𝓞v ≃A[ℤ] ℤ_[q] :=
  (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨q, hq⟩).symm

def residue : 𝓞v →+* ZMod q :=
  haveI : Fact q.Prime := ⟨hq⟩
  (PadicInt.toZMod (p := q)).comp (toPadicInt q hq).toRingEquiv.toRingHom

theorem residue_natCast (n : ℕ) : residue q hq (n : 𝓞v) = n := by
  haveI : Fact q.Prime := ⟨hq⟩
  simp [residue]

theorem residue_eq_zero_iff (c : 𝓞v) :
    residue q hq c = 0 ↔ ∃ y : 𝓞v, c = ((q : ℕ) : 𝓞v) * y := by
  haveI : Fact q.Prime := ⟨hq⟩
  set e := toPadicInt q hq
  change PadicInt.toZMod (e c) = 0 ↔ _
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, e.injective ?_⟩
    change e c = e _
    rw [map_mul, map_natCast, ContinuousAlgEquiv.apply_symm_apply, mul_comm, hz]
  · rintro ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    change _ = e _
    rw [map_mul, map_natCast, mul_comm]

theorem q_inv_mul_mem_integers_iff (c : 𝕂) (hc : c ∈ 𝓞v) :
    ((q : ℕ) : 𝕂)⁻¹ * c ∈ 𝓞v ↔ residue q hq ⟨c, hc⟩ = 0 := by
  rw [residue_eq_zero_iff]
  constructor
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    change c = (q : 𝕂) * (((q : ℕ) : 𝕂)⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ (q_ne_zero' q hq), one_mul]
  · rintro ⟨y, hy⟩
    have : c = ((q : ℕ) : 𝕂) * (y : 𝕂) := by
      have := congrArg Subtype.val hy; simpa using this
    rw [this, ← mul_assoc, inv_mul_cancel₀ (q_ne_zero' q hq), one_mul]
    exact y.2

open Classical in

def red (c : 𝕂) : ZMod q := if hc : c ∈ 𝓞v then residue q hq ⟨c, hc⟩ else 0

theorem red_of_mem {c : 𝕂} (hc : c ∈ 𝓞v) : red q hq c = residue q hq ⟨c, hc⟩ := by
  rw [red, dif_pos hc]

theorem red_add {c d : 𝕂} (hc : c ∈ 𝓞v) (hd : d ∈ 𝓞v) : red q hq (c + d) = red q hq c + red q hq d := by
  rw [red_of_mem q hq hc, red_of_mem q hq hd, red_of_mem q hq (add_mem hc hd), ← map_add]; rfl

theorem red_mul {c d : 𝕂} (hc : c ∈ 𝓞v) (hd : d ∈ 𝓞v) : red q hq (c * d) = red q hq c * red q hq d := by
  rw [red_of_mem q hq hc, red_of_mem q hq hd, red_of_mem q hq (mul_mem hc hd), ← map_mul]; rfl

theorem red_neg {c : 𝕂} (hc : c ∈ 𝓞v) : red q hq (-c) = -red q hq c := by
  rw [red_of_mem q hq hc, red_of_mem q hq (neg_mem hc), ← map_neg]; rfl

theorem red_sub {c d : 𝕂} (hc : c ∈ 𝓞v) (hd : d ∈ 𝓞v) : red q hq (c - d) = red q hq c - red q hq d := by
  rw [sub_eq_add_neg, red_add q hq hc (neg_mem hd), red_neg q hq hd, sub_eq_add_neg]

theorem red_natCast (n : ℕ) : red q hq ((n : ℕ) : 𝕂) = n := by
  rw [red_of_mem q hq (natCast_mem_integers _ n)]
  exact residue_natCast q hq n

theorem red_q : red q hq ((q : ℕ) : 𝕂) = 0 := by
  rw [red_natCast, ZMod.natCast_self]

theorem q_inv_mul_mem_iff_red {c : 𝕂} (hc : c ∈ 𝓞v) : ((q : ℕ) : 𝕂)⁻¹ * c ∈ 𝓞v ↔ red q hq c = 0 := by
  rw [red_of_mem q hq hc]; exact q_inv_mul_mem_integers_iff q hq c hc

theorem red_natCast_val (t : ZMod q) : haveI : NeZero q := ⟨hq.ne_zero⟩; red q hq ((t.val : ℕ) : 𝕂) = t := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  rw [red_natCast, ZMod.natCast_zmod_val]

end Places

section Local

variable (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ (place q hq))

def intMat : Subring M₂ where
  carrier := {M | ∀ i j, M i j ∈ 𝓞v}
  mul_mem' {A B} hA hB i j := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => mul_mem (hA i k) (hB k j)
  one_mem' i j := by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  add_mem' {A B} hA hB i j := by rw [Matrix.add_apply]; exact add_mem (hA i j) (hB i j)
  zero_mem' i j := by rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' {A} hA i j := by rw [Matrix.neg_apply]; exact neg_mem (hA i j)

theorem mem_intMat_iff (M : M₂) : M ∈ intMat q hq ↔ ∀ i j, M i j ∈ 𝓞v := Iff.rfl

def rep : Option (Fin q) → M₂
  | some t => !![1, 0; ((t : ℕ) : 𝕂), ϖ]
  | none => !![ϖ, 0; 0, 1]

def repInv : Option (Fin q) → M₂
  | some t => !![1, 0; -(ϖ⁻¹ * ((t : ℕ) : 𝕂)), ϖ⁻¹]
  | none => !![ϖ⁻¹, 0; 0, 1]

theorem rep_mul_repInv (o : Option (Fin q)) : rep q hq o * repInv q hq o = 1 := by
  have hq0 := q_ne_zero' q hq
  cases o with
  | none =>
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;>
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hq0]
  | some t =>
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;>
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hq0]
    ring_nf
    rw [mul_inv_cancel_right₀ hq0, sub_self]

theorem repInv_mul_rep (o : Option (Fin q)) : repInv q hq o * rep q hq o = 1 := by
  have hq0 := q_ne_zero' q hq
  cases o with
  | none =>
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;>
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hq0]
  | some t =>
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;>
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hq0]

theorem rep_mem_intMat (o : Option (Fin q)) : rep q hq o ∈ intMat q hq := by
  cases o with
  | none => intro i j; fin_cases i <;> fin_cases j <;> simp [rep, one_mem, zero_mem, q_mem_integers q hq]
  | some t =>
    intro i j; fin_cases i <;> fin_cases j <;>
      simp [rep, one_mem, zero_mem, q_mem_integers q hq, natCast_mem_integers]

theorem smul_repInv_mem_intMat (o : Option (Fin q)) : ϖ • repInv q hq o ∈ intMat q hq := by
  have hq0 := q_ne_zero' q hq
  cases o with
  | none =>
    intro i j; fin_cases i <;> fin_cases j <;>
      simp [repInv, one_mem, zero_mem, q_mem_integers q hq, mul_inv_cancel₀ hq0]
  | some t =>
    intro i j; fin_cases i <;> fin_cases j
    · simp [repInv, q_mem_integers q hq]
    · simp [repInv, zero_mem]
    · simp only [repInv, Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.mk_one, Fin.zero_eta, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
      exact neg_mem (natCast_mem_integers _ _)
    · simp [repInv, mul_inv_cancel₀ hq0, one_mem]

theorem repInv_notMem_intMat (o : Option (Fin q)) : repInv q hq o ∉ intMat q hq := by
  intro h
  cases o with
  | none => have := h 0 0; simp [repInv] at this; exact q_inv_notMem_integers q hq this
  | some t => have := h 1 1; simp [repInv] at this; exact q_inv_notMem_integers q hq this

theorem smul_rep_notMem_intMat (o : Option (Fin q)) : ϖ⁻¹ • rep q hq o ∉ intMat q hq := by
  have hq0 := q_ne_zero' q hq
  intro h
  cases o with
  | none => have := h 1 1; simp [rep] at this; exact q_inv_notMem_integers q hq this
  | some t => have := h 0 0; simp [rep] at this; exact q_inv_notMem_integers q hq this

theorem eq_of_repInv_mul_rep_mem (o o' : Option (Fin q)) (h : repInv q hq o * rep q hq o' ∈ intMat q hq) :
    o = o' := by
  have hq0 := q_ne_zero' q hq
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some t' =>
      exfalso
      have := h 0 0
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two] at this
      exact q_inv_notMem_integers q hq this
  | some t =>
    cases o' with
    | none =>
      exfalso
      have := h 1 1
      simp [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two] at this
      exact q_inv_notMem_integers q hq this
    | some t' =>
      congr 1
      have h10 := h 1 0
      simp only [rep, repInv, Matrix.mul_apply, Fin.sum_univ_two] at h10
      simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
        Fin.mk_one, Fin.zero_eta] at h10

      have hmem : ((q : ℕ) : 𝕂)⁻¹ * (((t' : ℕ) : 𝕂) - ((t : ℕ) : 𝕂)) ∈ 𝓞v := by
        have : ((q : ℕ) : 𝕂)⁻¹ * (((t' : ℕ) : 𝕂) - ((t : ℕ) : 𝕂)) =
            -(((q : ℕ) : 𝕂)⁻¹ * ((t : ℕ) : 𝕂)) * 1 + ((q : ℕ) : 𝕂)⁻¹ * ((t' : ℕ) : 𝕂) := by ring
        rw [this]; exact h10
      rw [q_inv_mul_mem_iff_red q hq (sub_mem (natCast_mem_integers _ _) (natCast_mem_integers _ _)),
        red_sub q hq (natCast_mem_integers _ _) (natCast_mem_integers _ _), red_natCast, red_natCast,
        sub_eq_zero] at hmem

      apply Fin.ext
      have h1 := congrArg ZMod.val hmem
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt t'.2, Nat.mod_eq_of_lt t.2, eq_comm] at h1

theorem field_dichotomy {F : Type*} [Field F] (x y : Fin 2 → Fin 2 → F)
    (hE : ∀ i j, x i 0 * y 0 j + x i 1 * y 1 j = 0) (hF : ∀ i j, y i 0 * x 0 j + y i 1 * x 1 j = 0)
    (hy : ∃ i j, y i j ≠ 0) (hx : ∃ i j, x i j ≠ 0) :
    (∃ t : F, (∀ j, x 1 j = t * x 0 j) ∧ ∀ i, y i 0 + t * y i 1 = 0) ∨
    ((∀ j, x 0 j = 0) ∧ ∀ i, y i 1 = 0) := by
  by_cases hrow : x 0 0 = 0 ∧ x 0 1 = 0
  ·
    right
    refine ⟨fun j => by fin_cases j <;> simp [hrow.1, hrow.2], fun i => ?_⟩
    obtain ⟨c, d, hcd⟩ := hx
    have hx1 : ∃ j, x 1 j ≠ 0 := by
      fin_cases c
      · fin_cases d
        · exact absurd hrow.1 hcd
        · exact absurd hrow.2 hcd
      · exact ⟨d, hcd⟩
    obtain ⟨j, hj⟩ := hx1
    have h := hF i j
    have hx0j : x 0 j = 0 := by fin_cases j; exacts [hrow.1, hrow.2]
    rw [hx0j, mul_zero, zero_add] at h
    exact (mul_eq_zero.1 h).resolve_right hj
  ·
    left
    have hdet : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 0 := by
      by_contra hd
      apply absurd hy
      push Not
      have hy0 : ∀ j, y 0 j = 0 := fun j => by
        have h1 := hE 0 j
        have h2 := hE 1 j
        have : (x 0 0 * x 1 1 - x 0 1 * x 1 0) * y 0 j = 0 := by linear_combination (x 1 1) * h1 - (x 0 1) * h2
        exact (mul_eq_zero.1 this).resolve_left hd
      have hy1 : ∀ j, y 1 j = 0 := fun j => by
        have h1 := hE 0 j
        have h2 := hE 1 j
        have : (x 0 0 * x 1 1 - x 0 1 * x 1 0) * y 1 j = 0 := by linear_combination (x 0 0) * h2 - (x 1 0) * h1
        exact (mul_eq_zero.1 this).resolve_left hd
      intro i j
      fin_cases i
      · exact hy0 j
      · exact hy1 j

    obtain ⟨t, ht⟩ : ∃ t : F, ∀ j, x 1 j = t * x 0 j := by
      by_cases h00 : x 0 0 = 0
      · have h01 : x 0 1 ≠ 0 := fun h => hrow ⟨h00, h⟩
        refine ⟨x 1 1 * (x 0 1)⁻¹, fun j => ?_⟩
        fin_cases j
        · have : x 0 1 * x 1 0 = 0 := by rw [h00, zero_mul, zero_sub, neg_eq_zero] at hdet; exact hdet
          simp [h00, (mul_eq_zero.1 this).resolve_left h01]
        · simp [mul_assoc, inv_mul_cancel₀ h01]
      · refine ⟨x 1 0 * (x 0 0)⁻¹, fun j => ?_⟩
        fin_cases j
        · simp [mul_assoc, inv_mul_cancel₀ h00]
        · field_simp
          simp only [Fin.mk_one, Fin.isValue]
          linear_combination hdet
    refine ⟨t, ht, fun i => ?_⟩
    have key : ∀ j, (y i 0 + t * y i 1) * x 0 j = 0 := fun j => by
      have h := hF i j
      rw [ht j] at h
      linear_combination h
    by_cases h00 : x 0 0 = 0
    · have h01 : x 0 1 ≠ 0 := fun h => hrow ⟨h00, h⟩
      exact (mul_eq_zero.1 (key 1)).resolve_right h01
    · exact (mul_eq_zero.1 (key 0)).resolve_right h00

theorem red_mul_apply {A B : M₂} (hA : A ∈ intMat q hq) (hB : B ∈ intMat q hq) (i j : Fin 2) :
    red q hq ((A * B) i j) = red q hq (A i 0) * red q hq (B 0 j) + red q hq (A i 1) * red q hq (B 1 j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, red_add q hq (mul_mem (hA i 0) (hB 0 j)) (mul_mem (hA i 1) (hB 1 j)),
    red_mul q hq (hA i 0) (hB 0 j), red_mul q hq (hA i 1) (hB 1 j)]

theorem red_smul_one_apply (i j : Fin 2) : red q hq ((ϖ • (1 : M₂)) i j) = 0 := by
  rw [Matrix.smul_apply, smul_eq_mul, red_mul q hq (q_mem_integers q hq) ((intMat q hq).one_mem i j), red_q,
    zero_mul]

theorem exists_red_ne_zero {A : M₂} (hA : A ∈ intMat q hq) (hn : ϖ⁻¹ • A ∉ intMat q hq) :
    ∃ i j, red q hq (A i j) ≠ 0 := by
  by_contra h
  push Not at h
  apply hn
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, q_inv_mul_mem_iff_red q hq (hA i j)]
  exact h i j

theorem repInv_some_mul (t : Fin q) (X : M₂) : repInv q hq (some t) * X =
    !![X 0 0, X 0 1;
      ϖ⁻¹ * (X 1 0 - ((t : ℕ) : 𝕂) * X 0 0), ϖ⁻¹ * (X 1 1 - ((t : ℕ) : 𝕂) * X 0 1)] := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [repInv] <;> ring

theorem repInv_none_mul (X : M₂) : repInv q hq none * X =
    !![ϖ⁻¹ * X 0 0, ϖ⁻¹ * X 0 1; X 1 0, X 1 1] := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [repInv]

theorem smul_mul_rep_some (t : Fin q) (Y : M₂) : ϖ⁻¹ • (Y * rep q hq (some t)) =
    !![ϖ⁻¹ * (Y 0 0 + ((t : ℕ) : 𝕂) * Y 0 1), Y 0 1;
      ϖ⁻¹ * (Y 1 0 + ((t : ℕ) : 𝕂) * Y 1 1), Y 1 1] := by
  have hq0 := q_ne_zero' q hq
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simp [rep, hq0, mul_comm]
  · simp [rep]; rw [mul_comm (Y 0 1), inv_mul_cancel_left₀ hq0]
  · simp [rep, hq0, mul_comm]
  · simp [rep]; rw [mul_comm (Y 1 1), inv_mul_cancel_left₀ hq0]

theorem smul_mul_rep_none (Y : M₂) : ϖ⁻¹ • (Y * rep q hq none) =
    !![Y 0 0, ϖ⁻¹ * Y 0 1; Y 1 0, ϖ⁻¹ * Y 1 1] := by
  have hq0 := q_ne_zero' q hq
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simp [rep]; rw [mul_comm (Y 0 0), inv_mul_cancel_left₀ hq0]
  · simp [rep]
  · simp [rep]; rw [mul_comm (Y 1 0), inv_mul_cancel_left₀ hq0]
  · simp [rep]

theorem exists_rep (X Y : M₂) (hX : X ∈ intMat q hq) (hY : Y ∈ intMat q hq)
    (hXY : X * Y = ϖ • (1 : M₂)) (hYX : Y * X = ϖ • (1 : M₂))
    (hYn : ϖ⁻¹ • Y ∉ intMat q hq) (hXn : ϖ⁻¹ • X ∉ intMat q hq) :
    ∃ o : Option (Fin q), repInv q hq o * X ∈ intMat q hq ∧ ϖ⁻¹ • (Y * rep q hq o) ∈ intMat q hq := by
  haveI : Fact q.Prime := ⟨hq⟩

  set x : Fin 2 → Fin 2 → ZMod q := fun i j => red q hq (X i j) with hx
  set y : Fin 2 → Fin 2 → ZMod q := fun i j => red q hq (Y i j) with hy
  have hE : ∀ i j, x i 0 * y 0 j + x i 1 * y 1 j = 0 := fun i j => by
    have h := congrArg (fun M : M₂ => red q hq (M i j)) hXY
    rwa [red_mul_apply q hq hX hY, red_smul_one_apply] at h
  have hF : ∀ i j, y i 0 * x 0 j + y i 1 * x 1 j = 0 := fun i j => by
    have h := congrArg (fun M : M₂ => red q hq (M i j)) hYX
    rwa [red_mul_apply q hq hY hX, red_smul_one_apply] at h
  have hyne : ∃ i j, y i j ≠ 0 := exists_red_ne_zero q hq hY hYn
  have hxne : ∃ i j, x i j ≠ 0 := exists_red_ne_zero q hq hX hXn
  rcases field_dichotomy x y hE hF hyne hxne with ⟨t, ht, hty⟩ | ⟨hx0, hy1⟩
  ·
    refine ⟨some ⟨t.val, t.val_lt⟩, ?_, ?_⟩
    · rw [repInv_some_mul]
      have hT : red q hq ((t.val : ℕ) : 𝕂) = t := red_natCast_val q hq t
      have hrow : ∀ j, ϖ⁻¹ * (X 1 j - ((t.val : ℕ) : 𝕂) * X 0 j) ∈ 𝓞v := fun j => by
        rw [q_inv_mul_mem_iff_red q hq (sub_mem (hX 1 j) (mul_mem (natCast_mem_integers _ _) (hX 0 j))),
          red_sub q hq (hX 1 j) (mul_mem (natCast_mem_integers _ _) (hX 0 j)),
          red_mul q hq (natCast_mem_integers _ _) (hX 0 j), hT, sub_eq_zero]
        exact ht j
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using hX 0 0
      · simpa using hX 0 1
      · simpa using hrow 0
      · simpa using hrow 1
    · rw [smul_mul_rep_some]
      have hT : red q hq ((t.val : ℕ) : 𝕂) = t := red_natCast_val q hq t
      have hcol : ∀ i, ϖ⁻¹ * (Y i 0 + ((t.val : ℕ) : 𝕂) * Y i 1) ∈ 𝓞v := fun i => by
        rw [q_inv_mul_mem_iff_red q hq (add_mem (hY i 0) (mul_mem (natCast_mem_integers _ _) (hY i 1))),
          red_add q hq (hY i 0) (mul_mem (natCast_mem_integers _ _) (hY i 1)),
          red_mul q hq (natCast_mem_integers _ _) (hY i 1), hT]
        exact hty i
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using hcol 0
      · simpa using hY 0 1
      · simpa using hcol 1
      · simpa using hY 1 1
  ·
    refine ⟨none, ?_, ?_⟩
    · rw [repInv_none_mul]
      have hrow : ∀ j, ϖ⁻¹ * X 0 j ∈ 𝓞v := fun j => by
        rw [q_inv_mul_mem_iff_red q hq (hX 0 j)]; exact hx0 j
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using hrow 0
      · simpa using hrow 1
      · simpa using hX 1 0
      · simpa using hX 1 1
    · rw [smul_mul_rep_none]
      have hcol : ∀ i, ϖ⁻¹ * Y i 1 ∈ 𝓞v := fun i => by
        rw [q_inv_mul_mem_iff_red q hq (hY i 1)]; exact hy1 i
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using hY 0 0
      · simpa using hcol 0
      · simpa using hY 1 0
      · simpa using hcol 1

end Local

section Model

variable {a b : ℚ} (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ (place q hq))

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq) ≃+*
    Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))
  (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ (place q hq),
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))))
  (R : Submodule ℤ ℍ[ℚ, a, b])
  (hRv : ∀ z : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq),
    z ∈ Submodule.localBox R (place q hq) ↔ ∀ i j, φ z i j ∈ HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq))

omit hq φ R in

theorem ratCast_smul_eq_one_tmul_mul (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    r • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) r)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

include hφ in
omit R in
theorem map_one_tmul_mul (c : 𝕂) (x : ℍv) : φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • φ x := by
  rw [map_mul, hφ, smul_mul_assoc, one_mul]

include hφ in
omit R in

theorem map_natCast_smul (x : ℍv) : φ ((q : ℚ) • x) = ϖ • φ x := by
  rw [ratCast_smul_eq_one_tmul_mul, algebraMap_natCast, map_one_tmul_mul q hq φ hφ]

include hφ in
omit R in

theorem map_natCast_inv_smul (x : ℍv) : φ ((q : ℚ)⁻¹ • x) = ϖ⁻¹ • φ x := by
  rw [ratCast_smul_eq_one_tmul_mul, map_inv₀, algebraMap_natCast, map_one_tmul_mul q hq φ hφ]

def repUnit (o : Option (Fin q)) : (ℍv)ˣ where
  val := φ.symm (rep q hq o)
  inv := φ.symm (repInv q hq o)
  val_inv := by rw [← map_mul, rep_mul_repInv, map_one]
  inv_val := by rw [← map_mul, repInv_mul_rep, map_one]

omit R in
theorem coe_repUnit (o : Option (Fin q)) : ((repUnit q hq φ o : (ℍv)ˣ) : ℍv) = φ.symm (rep q hq o) := rfl

omit R in
theorem coe_repUnit_inv (o : Option (Fin q)) : (((repUnit q hq φ o)⁻¹ : (ℍv)ˣ) : ℍv) = φ.symm (repInv q hq o) := rfl

include hRv in

private theorem _root_.TqLoc.mem_stabilizer_iff (u : (ℍv)ˣ) :
    u ∈ MulAction.stabilizer (ℍv)ˣ
        ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) ↔
      φ (u : ℍv) ∈ intMat q hq ∧ φ ((u⁻¹ : (ℍv)ˣ) : ℍv) ∈ intMat q hq := by
  have h1 : (1 : ℍv) ∈ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
    rw [SetLike.mem_coe, hRv, map_one]; exact (intMat q hq).one_mem

  have hsub : ∀ w : (ℍv)ˣ, φ (w : ℍv) ∈ intMat q hq →
      w • ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) ⊆
        ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
    intro w hw x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
    rw [SetLike.mem_coe, hRv] at hy
    rw [Units.smul_def, smul_eq_mul, SetLike.mem_coe, hRv, map_mul]
    exact (intMat q hq).mul_mem hw hy
  constructor
  · intro hu
    rw [MulAction.mem_stabilizer_iff] at hu
    have hu' : u⁻¹ • ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) =
        ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
      conv_lhs => rw [← hu]
      rw [inv_smul_smul]
    constructor
    · have : (u : ℍv) ∈ u • ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) :=
        Set.mem_smul_set.2 ⟨1, h1, by rw [Units.smul_def, smul_eq_mul, mul_one]⟩
      rw [hu, SetLike.mem_coe, hRv] at this
      exact this
    · have : ((u⁻¹ : (ℍv)ˣ) : ℍv) ∈ u⁻¹ • ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) :=
        Set.mem_smul_set.2 ⟨1, h1, by rw [Units.smul_def, smul_eq_mul, mul_one]⟩
      rw [hu', SetLike.mem_coe, hRv] at this
      exact this
  · rintro ⟨hu, hui⟩
    rw [MulAction.mem_stabilizer_iff]
    refine Set.Subset.antisymm (hsub u hu) fun x hx => ?_
    have hx' : u⁻¹ • x ∈ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) :=
      hsub u⁻¹ hui (Set.smul_mem_smul_set hx)
    exact Set.mem_smul_set.2 ⟨u⁻¹ • x, hx', smul_inv_smul u x⟩

p2m_export "TqLoc" "mem_stabilizer_iff"
include hRv in

theorem inv_mul_mem_stabilizer (g h : (ℍv)ˣ)
    (h1 : φ (((g⁻¹ : (ℍv)ˣ) : ℍv) * (h : ℍv)) ∈ intMat q hq)
    (h2 : φ (((h⁻¹ : (ℍv)ˣ) : ℍv) * (g : ℍv)) ∈ intMat q hq) :
    g⁻¹ * h ∈ MulAction.stabilizer (ℍv)ˣ
        ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
  rw [mem_stabilizer_iff q hq φ R hRv, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  exact ⟨h1, h2⟩

def IsHecke (g : (ℍv)ˣ) : Prop :=
  (g : ℍv) ∈ Submodule.localBox R (place q hq) ∧
    (q : ℚ) • ((g⁻¹ : (ℍv)ˣ) : ℍv) ∈ Submodule.localBox R (place q hq) ∧
    ((g⁻¹ : (ℍv)ˣ) : ℍv) ∉ Submodule.localBox R (place q hq) ∧
    (q : ℚ)⁻¹ • (g : ℍv) ∉ Submodule.localBox R (place q hq)

include hφ hRv in

theorem local_of_isHecke (g : (ℍv)ˣ) (hg : IsHecke q hq R g) :
    φ (g : ℍv) ∈ intMat q hq ∧
    ϖ • φ (((g⁻¹ : (ℍv)ˣ) : ℍv)) ∈ intMat q hq ∧
    φ (((g⁻¹ : (ℍv)ˣ) : ℍv)) ∉ intMat q hq ∧
    ϖ⁻¹ • φ (g : ℍv) ∉ intMat q hq := by
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨(hRv _).1 hg1, ?_, fun hc => hg3 ((hRv _).2 hc), fun hc => hg4 ?_⟩
  · have := (hRv _).1 hg2
    rwa [map_natCast_smul q hq φ hφ] at this
  · rw [hRv, map_natCast_inv_smul q hq φ hφ]
    exact hc

include hφ hRv in

theorem isHecke_repUnit (o : Option (Fin q)) : IsHecke q hq R (repUnit q hq φ o) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hRv, coe_repUnit, RingEquiv.apply_symm_apply]
    exact rep_mem_intMat q hq o
  · rw [hRv, map_natCast_smul q hq φ hφ, coe_repUnit_inv, RingEquiv.apply_symm_apply]
    exact smul_repInv_mem_intMat q hq o
  · rw [hRv, coe_repUnit_inv, RingEquiv.apply_symm_apply]
    exact repInv_notMem_intMat q hq o
  · rw [hRv, map_natCast_inv_smul q hq φ hφ, coe_repUnit, RingEquiv.apply_symm_apply]
    exact smul_rep_notMem_intMat q hq o

include hRv in

theorem repUnit_injective (o o' : Option (Fin q))
    (h : (repUnit q hq φ o)⁻¹ * repUnit q hq φ o' ∈
      MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv)) :
    o = o' := by
  rw [mem_stabilizer_iff q hq φ R hRv] at h
  have h1 := h.1
  rw [Units.val_mul, coe_repUnit_inv, coe_repUnit, ← map_mul, RingEquiv.apply_symm_apply] at h1
  exact eq_of_repInv_mul_rep_mem q hq o o' h1

include hφ hRv in

theorem exists_repUnit_inv_mul_mem (g : (ℍv)ˣ) (hg : IsHecke q hq R g) :
    ∃ o, (repUnit q hq φ o)⁻¹ * g ∈
      MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) := by
  obtain ⟨hX, hY, hn1, hn2⟩ := local_of_isHecke q hq φ hφ R hRv g hg
  have hq0 := q_ne_zero' q hq
  set X : M₂ := φ (g : ℍv) with hXdef
  set Y : M₂ := ϖ • φ (((g⁻¹ : (ℍv)ˣ) : ℍv)) with hYdef
  have hXY : X * Y = ϖ • (1 : M₂) := by
    rw [hXdef, hYdef, Matrix.mul_smul, ← map_mul, Units.mul_inv, map_one]
  have hYX : Y * X = ϖ • (1 : M₂) := by
    rw [hXdef, hYdef, Matrix.smul_mul, ← map_mul, Units.inv_mul, map_one]
  have hYn : ϖ⁻¹ • Y ∉ intMat q hq := by
    rw [hYdef, smul_smul, inv_mul_cancel₀ hq0, one_smul]; exact hn1
  obtain ⟨o, ho1, ho2⟩ := exists_rep q hq X Y hX hY hXY hYX hYn hn2
  refine ⟨o, inv_mul_mem_stabilizer q hq φ R hRv (repUnit q hq φ o) g ?_ ?_⟩
  · rw [coe_repUnit_inv, map_mul, RingEquiv.apply_symm_apply]
    exact ho1
  · rw [coe_repUnit, map_mul, RingEquiv.apply_symm_apply]
    have : φ (((g⁻¹ : (ℍv)ˣ) : ℍv)) * rep q hq o = ϖ⁻¹ • (Y * rep q hq o) := by
      rw [hYdef, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hq0, one_smul]
    rw [this]; exact ho2

include hφ hRv in

theorem main :
    Nat.card {c : (ℍv)ˣ ⧸
        MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) //
      ∃ g : (ℍv)ˣ, IsHecke q hq R g ∧
        (QuotientGroup.mk g : (ℍv)ˣ ⧸
          MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv)) = c} =
      q + 1 := by
  classical
  let f : Option (Fin q) →
      {c : (ℍv)ˣ ⧸
          MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv) //
        ∃ g : (ℍv)ˣ, IsHecke q hq R g ∧
          (QuotientGroup.mk g : (ℍv)ˣ ⧸
            MulAction.stabilizer (ℍv)ˣ ((Submodule.localBox R (place q hq) : AddSubgroup ℍv) : Set ℍv)) = c} :=
    fun o => ⟨QuotientGroup.mk (repUnit q hq φ o), repUnit q hq φ o, isHecke_repUnit q hq φ hφ R hRv o, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro o o' heq
      have heq' := congrArg Subtype.val heq
      exact repUnit_injective q hq φ R hRv o o' (QuotientGroup.eq.1 heq')
    · rintro ⟨c, g, hg, rfl⟩
      obtain ⟨o, ho⟩ := exists_repUnit_inv_mul_mem q hq φ hφ R hRv g hg
      exact ⟨o, Subtype.ext (QuotientGroup.eq.2 ho)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_fin]

end Model

end TqLoc

end

open TqLoc in
theorem solution
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (hR : QuaternionAlgebra.IsEichlerOrder R N) (hqN : ¬ q ∣ N) {q' : ℕ} [Fact q'.Prime] (hqq' : q' ≠ q)
    (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    (v : HeightOneSpectrum (𝓞 ℚ)) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Nat.card {c : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸
        MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ
          ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) //
      ∃ g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
        ((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v ∧
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v ∧
          (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox R v) ∧
        (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸
          MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ
          ((Submodule.localBox R v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) = c} = q + 1 := by
  have hq : q.Prime := Fact.out
  have hq' : q'.Prime := Fact.out
  obtain rfl : v = place q hq := eq_place_of_mem q hq v hqv

  have hq'v : (q' : 𝓞 ℚ) ∉ (place q hq).asIdeal := by
    rw [natCast_mem_asIdeal_place_iff]
    exact fun h => hqq' ((Nat.prime_dvd_prime_iff_eq hq hq').1 h).symm
  have hNv : (N : 𝓞 ℚ) ∉ (place q hq).asIdeal := by
    rw [natCast_mem_asIdeal_place_iff]; exact hqN

  obtain ⟨φ, hφ, hRv⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef hR (place q hq) hq'v hNv
  exact main q hq φ hφ R hRv

end S_QuaternionAlgebra_IsEichlerOrder_natCard_setOf_exists_quotientMk_stabilizer_localBox_eq_eq_succ
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_natCard_setOf_exists_quotientMk_stabilizer_localBox_eq_eq_succ (solution)
