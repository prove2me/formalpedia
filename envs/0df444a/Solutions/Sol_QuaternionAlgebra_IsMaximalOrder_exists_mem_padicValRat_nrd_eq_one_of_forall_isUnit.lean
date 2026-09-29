-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/21d27420-ee52-5151-ab6d-89e090100b6d

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace RamUnifDiv

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

section Places

open Rat.HeightOneSpectrum

theorem natCast_mem_asIdeal_iff (w : HOS) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ natGenerator w ∣ n := by
  rw [natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_eq_of_mem {q : ℕ} (hq : q.Prime) (w : HOS) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) :
    natGenerator w = q :=
  (Nat.prime_dvd_prime_iff_eq (prime_natGenerator w) hq).mp ((natCast_mem_asIdeal_iff w q).mp hw)

theorem eq_of_natCast_mem {q : ℕ} (hq : q.Prime) {v w : HOS} (hv : (q : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  apply (primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  show natGenerator w = natGenerator v
  rw [natGenerator_eq_of_mem hq w hw, natGenerator_eq_of_mem hq v hv]

theorem natCast_notMem_of_ne {q : ℕ} (hq : q.Prime) {v : HOS} (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) {w : HOS}
    (hw : w ≠ v) : (q : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (eq_of_natCast_mem hq hv h)

theorem valued_natCast_eq_one {n : ℕ} (w : HOS) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (n : w.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem natCast_inv_mem_integers {n : ℕ} (w : HOS) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one w hn, inv_one]

theorem natCast_mem_integers (w : HOS) (n : ℕ) : (n : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = _ at h
  rw [map_natCast] at h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
  exact HeightOneSpectrum.valuation_le_one w _

variable (v : HOS)

theorem asIdeal_eq_span : v.asIdeal = Ideal.span {(natGenerator v : 𝓞 ℚ)} := by
  have h := span_natGenerator (R := 𝓞 ℚ) v
  have h2 : v.asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) v.asIdeal) := by
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

theorem valuation_natGenerator : v.valuation ℚ (natGenerator v : ℚ) = WithZero.exp (-1) := by
  rw [show (natGenerator v : ℚ) = algebraMap (𝓞 ℚ) ℚ (natGenerator v) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast (prime_natGenerator v).ne_zero)
    (asIdeal_eq_span v)

theorem valued_algebraMap (r : ℚ) : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) r) = v.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r

theorem valuation_eq_exp_neg_padicValRat {q : ℕ} [hq : Fact q.Prime] (hvq : natGenerator v = q) (r : ℚ) (hr : r ≠ 0) :
    v.valuation ℚ r = WithZero.exp (-padicValRat q r) := by

  have hpe : primesEquiv (R := 𝓞 ℚ) v = ⟨q, hq.out⟩ := Subtype.ext hvq
  have hiso : (v.valuation ℚ).IsEquiv (Rat.padicValuation q) := by
    have h := valuation_equiv_padicValuation (R := 𝓞 ℚ) v
    rw [hpe] at h
    exact h
  have hVq : v.valuation ℚ (q : ℚ) = WithZero.exp (-1) := by rw [← hvq]; exact valuation_natGenerator v
  have hPq : Rat.padicValuation q (q : ℚ) = WithZero.exp (-1) := Rat.padicValuation_self q
  have hP : Rat.padicValuation q r = WithZero.exp (-padicValRat q r) := by
    simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hr]
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
  have hVpow : ∀ j : ℤ, v.valuation ℚ ((q : ℚ) ^ j) = WithZero.exp (-j) := fun j => by
    rw [map_zpow₀, hVq, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]
  have hPpow : ∀ j : ℤ, Rat.padicValuation q ((q : ℚ) ^ j) = WithZero.exp (-j) := fun j => by
    rw [map_zpow₀, hPq, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]
  have hV0 : v.valuation ℚ r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  set m := WithZero.log (v.valuation ℚ r) with hm
  have hVr : v.valuation ℚ r = WithZero.exp m := (WithZero.exp_log hV0).symm
  set t := padicValRat q r

  have h1 : -t ≤ m := by
    have := (hiso.le_iff_le (x := r) (y := (q : ℚ) ^ (-m))).mp (by rw [hVr, hVpow, neg_neg])
    rw [hP, hPpow, neg_neg, WithZero.exp_le_exp] at this
    exact this
  have h2 : m ≤ -t := by
    have := (hiso.le_iff_le (x := r) (y := (q : ℚ) ^ t)).mpr (by rw [hP, hPpow])
    rw [hVr, hVpow, WithZero.exp_le_exp] at this
    exact this
  rw [hVr, le_antisymm h2 h1]

end Places

section PlaceDef

open Rat.HeightOneSpectrum

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

variable (q : ℕ) (hq : q.Prime)

local notation "𝔳" => place q hq

theorem primesEquiv_place : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) 𝔳 = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place : Rat.HeightOneSpectrum.natGenerator 𝔳 = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem q_mem_asIdeal_place : (q : 𝓞 ℚ) ∈ (𝔳).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

end PlaceDef

section Conic

open Polynomial

theorem hensel_simple {p : ℕ} [Fact p.Prime] (F : ℤ_[p][X]) (x : ℤ_[p])
    (h0 : PadicInt.toZMod (F.eval x) = 0) (h1 : PadicInt.toZMod (F.derivative.eval x) ≠ 0) :
    ∃ z : ℤ_[p], F.eval z = 0 := by
  have hn0 : ‖F.eval x‖ < 1 := by
    have : F.eval x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h0
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at this
    exact PadicInt.mem_nonunits.mp this
  have hn1 : ‖F.derivative.eval x‖ = 1 := by
    apply PadicInt.isUnit_iff.mp
    by_contra hu
    apply h1
    have : F.derivative.eval x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]; exact hu
    exact this
  have hnorm : ‖aeval x F‖ < ‖aeval x (derivative F)‖ ^ 2 := by
    rw [coe_aeval_eq_eval, hn1, one_pow]; exact hn0
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  exact ⟨z, by rwa [coe_aeval_eq_eval] at hz⟩

theorem conic_mod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (A B : ZMod p) (hA : A ≠ 0) :
    ∃ y₀ y₁ : ZMod p, y₀ ^ 2 - A * y₁ ^ 2 = B := by
  have hp : p.Prime := Fact.out
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hf : (X ^ 2 - C B : (ZMod p)[X]).degree = 2 := degree_X_pow_sub_C (by norm_num) B
  have hg : (C (-A) * X ^ 2 : (ZMod p)[X]).degree = 2 := by
    rw [degree_C_mul_X_pow 2 (neg_ne_zero.mpr hA)]; rfl
  obtain ⟨y₀, y₁, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  refine ⟨y₀, y₁, ?_⟩
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at h
  linear_combination h

theorem toZMod_ne_zero_iff {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) : PadicInt.toZMod x ≠ 0 ↔ ‖x‖ = 1 := by
  rw [← PadicInt.isUnit_iff]
  constructor
  · intro h
    by_contra hu
    apply h
    have : x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]; exact hu
    exact this
  · intro hu h0
    have : x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h0
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at this
    exact this hu

theorem conic_padic (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (A B : ℤ_[p]) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) :
    ∃ y₀ y₁ : ℤ_[p], y₀ ^ 2 - A * y₁ ^ 2 - B = 0 := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hAbar : PadicInt.toZMod A ≠ 0 := (toZMod_ne_zero_iff A).mpr hA
  have hBbar : PadicInt.toZMod B ≠ 0 := (toZMod_ne_zero_iff B).mpr hB
  obtain ⟨yb₀, yb₁, hyb⟩ := conic_mod p hp2 (PadicInt.toZMod A) (PadicInt.toZMod B) hAbar
  set Y₀ : ℤ_[p] := (yb₀.val : ℤ_[p]) with hY₀
  set Y₁ : ℤ_[p] := (yb₁.val : ℤ_[p]) with hY₁
  have hY₀r : PadicInt.toZMod Y₀ = yb₀ := by rw [hY₀, map_natCast, ZMod.natCast_zmod_val]
  have hY₁r : PadicInt.toZMod Y₁ = yb₁ := by rw [hY₁, map_natCast, ZMod.natCast_zmod_val]
  by_cases hy0 : yb₀ = 0
  · have hyb₁ : yb₁ ≠ 0 := by
      rintro rfl; apply hBbar; rw [← hyb, hy0]; ring
    have e0 : PadicInt.toZMod ((C A * X ^ 2 + C B : ℤ_[p][X]).eval Y₁) = 0 := by
      have : (C A * X ^ 2 + C B : ℤ_[p][X]).eval Y₁ = A * Y₁ ^ 2 + B := by
        simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      rw [this, map_add, map_mul, map_pow, hY₁r, ← hyb, hy0]; ring
    have e1 : PadicInt.toZMod ((C A * X ^ 2 + C B : ℤ_[p][X]).derivative.eval Y₁) ≠ 0 := by
      have : (C A * X ^ 2 + C B : ℤ_[p][X]).derivative.eval Y₁ = A * (2 * Y₁) := by
        simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow,
          Nat.cast_ofNat, add_zero, eval_mul, eval_C, eval_pow, eval_X]
        norm_num
      rw [this, map_mul, map_mul, map_ofNat, hY₁r]
      exact mul_ne_zero hAbar (mul_ne_zero h2 hyb₁)
    obtain ⟨z, hz⟩ := hensel_simple _ Y₁ e0 e1
    refine ⟨0, z, ?_⟩
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hz
    linear_combination -hz
  · have e0 : PadicInt.toZMod ((X ^ 2 - C (A * Y₁ ^ 2 + B) : ℤ_[p][X]).eval Y₀) = 0 := by
      have : (X ^ 2 - C (A * Y₁ ^ 2 + B) : ℤ_[p][X]).eval Y₀ = Y₀ ^ 2 - (A * Y₁ ^ 2 + B) := by
        simp only [eval_sub, eval_pow, eval_X, eval_C]
      rw [this, map_sub, map_pow, map_add, map_mul, map_pow, hY₀r, hY₁r, ← hyb]; ring
    have e1 : PadicInt.toZMod ((X ^ 2 - C (A * Y₁ ^ 2 + B) : ℤ_[p][X]).derivative.eval Y₀) ≠ 0 := by
      have : (X ^ 2 - C (A * Y₁ ^ 2 + B) : ℤ_[p][X]).derivative.eval Y₀ = 2 * Y₀ := by
        simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, Nat.cast_ofNat, eval_mul,
          eval_pow, eval_X, eval_C]
        norm_num
      rw [this, map_mul, map_ofNat, hY₀r]
      exact mul_ne_zero h2 hy0
    obtain ⟨z, hz⟩ := hensel_simple _ Y₀ e0 e1
    refine ⟨z, Y₁, ?_⟩
    simp only [eval_sub, eval_pow, eval_X, eval_C] at hz
    linear_combination hz

theorem padicValRat_zpow_self (q : ℕ) [hq : Fact q.Prime] (k : ℤ) : padicValRat q ((q : ℚ) ^ k) = k := by
  have hq1 : 1 < q := hq.out.one_lt
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, padicValRat.pow _, padicValRat.self hq1, mul_one]
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (le_of_lt hk)
    rw [hn, zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow _, padicValRat.self hq1, mul_one]

theorem padic_norm_eq_one_of_padicValRat_eq_zero (q : ℕ) [Fact q.Prime] (r : ℚ) (hr : r ≠ 0)
    (h : padicValRat q r = 0) : ‖(r : ℚ_[q])‖ = 1 := by
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hr, h, neg_zero, zpow_zero, Rat.cast_one]

theorem exists_normForm_eq_zero_of_even (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hea : Even (padicValRat q a)) (heb : Even (padicValRat q b)) :
    ∃ x₀ x₁ x₂ x₃ : (place q hq.out).adicCompletion ℚ,
      ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      x₀ ^ 2 - (a : _) * x₁ ^ 2 - (b : _) * x₂ ^ 2 + (a : _) * (b : _) * x₃ ^ 2 = 0 := by
  set v := place q hq.out with hv
  set K := v.adicCompletion ℚ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain ⟨m, hm⟩ := hea
  obtain ⟨n, hn⟩ := heb
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero

  set a₀ : ℚ := a * (q : ℚ) ^ (-(m + m)) with ha₀
  set b₀ : ℚ := b * (q : ℚ) ^ (-(n + n)) with hb₀
  have ha₀0 : a₀ ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hq0)
  have hb₀0 : b₀ ≠ 0 := mul_ne_zero hb (zpow_ne_zero _ hq0)
  have hva₀ : padicValRat q a₀ = 0 := by
    rw [ha₀, padicValRat.mul ha (zpow_ne_zero _ hq0), padicValRat_zpow_self, hm]; ring
  have hvb₀ : padicValRat q b₀ = 0 := by
    rw [hb₀, padicValRat.mul hb (zpow_ne_zero _ hq0), padicValRat_zpow_self, hn]; ring
  have haa₀ : a = a₀ * (q : ℚ) ^ (m + m) := by
    rw [ha₀, mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, mul_one]
  have hbb₀ : b = b₀ * (q : ℚ) ^ (n + n) := by
    rw [hb₀, mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, mul_one]

  have hAn : ‖(a₀ : ℚ_[q])‖ = 1 := padic_norm_eq_one_of_padicValRat_eq_zero q a₀ ha₀0 hva₀
  have hBn : ‖(b₀ : ℚ_[q])‖ = 1 := padic_norm_eq_one_of_padicValRat_eq_zero q b₀ hb₀0 hvb₀
  set A : ℤ_[q] := ⟨(a₀ : ℚ_[q]), hAn.le⟩
  set B : ℤ_[q] := ⟨(b₀ : ℚ_[q]), hBn.le⟩
  obtain ⟨y₀, y₁, hy⟩ := conic_padic q hq2 A B hAn hBn
  have hy' : (y₀ : ℚ_[q]) ^ 2 - (a₀ : ℚ_[q]) * (y₁ : ℚ_[q]) ^ 2 - (b₀ : ℚ_[q]) = 0 := by
    have := congrArg ((↑) : ℤ_[q] → ℚ_[q]) hy
    simpa [A, B] using this

  let e : ℚ_[q] ≃A[ℚ] K := Padic.adicCompletionEquiv (𝓞 ℚ) ⟨q, hq.out⟩
  have hK : (e y₀) ^ 2 - (a₀ : K) * (e y₁) ^ 2 - (b₀ : K) = 0 := by
    have := congrArg e hy'
    rwa [map_sub, map_sub, map_pow, map_mul, map_pow, map_ratCast, map_ratCast, map_zero] at this
  have hqK : (q : K) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
  refine ⟨e y₀, e y₁ * (q : K) ^ (-m), (q : K) ^ (-n), 0, ?_, ?_⟩
  · rintro ⟨-, -, h, -⟩
    exact zpow_ne_zero _ hqK h
  · rw [haa₀, hbb₀]
    push_cast
    have e1 : ((q : K) ^ (m + m)) * ((q : K) ^ (-m)) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hqK, show m + m + -m * ((2 : ℕ) : ℤ) = 0 by omega, zpow_zero]
    have e2 : ((q : K) ^ (n + n)) * ((q : K) ^ (-n)) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hqK, show n + n + -n * ((2 : ℕ) : ℤ) = 0 by omega, zpow_zero]
    linear_combination hK - (a₀ : K) * (e y₁) ^ 2 * e1 - (b₀ : K) * e2

end Conic

section LocalBox

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem tmul_one_mem_localBox {Λ : Submodule ℤ D} {z : D} (hz : z ∈ Λ) (w : HOS) :
    z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, 1, (w.adicCompletionIntegers ℚ).one_mem, rfl⟩

theorem gen_mul_mem_localBox (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (w : HOS)
    {z : D} (hz : z ∈ Λ) {c : w.adicCompletion ℚ} (hc : c ∈ w.adicCompletionIntegers ℚ)
    {y : D ⊗[ℚ] w.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ w) :
    (z ⊗ₜ[ℚ] c) * y ∈ Submodule.localBox Λ w := by
  unfold Submodule.localBox at hy ⊢
  refine AddSubgroup.closure_induction (p := fun y _ => (z ⊗ₜ[ℚ] c) * y ∈ _) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z', hz', c', hc', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hmul z z' hz hz', c * c', mul_mem hc hc', rfl⟩
  · show z ⊗ₜ[ℚ] c * 0 ∈ _
    rw [mul_zero]; exact AddSubgroup.zero_mem _
  · intro x y _ _ hx hy
    rw [mul_add]; exact AddSubgroup.add_mem _ hx hy
  · intro x _ hx
    convert AddSubgroup.neg_mem _ hx using 1
    exact mul_neg (z ⊗ₜ[ℚ] c) x

theorem rat_smul_eq_one_tmul_mul (w : HOS) (q : ℚ) (x : D ⊗[ℚ] w.adicCompletion ℚ) :
    q • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) q)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z s =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

variable (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : 𝕂} (hc : c ∈ 𝓞v) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_tmul_mul_mem_localBox {x : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) {c : 𝕂}
    (hc : c ∈ 𝓞v) : ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox Λ v hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx

theorem mul_mem_localBox (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {x y : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox Λ v (hmul _ _ hz' hz) (mul_mem hc' hc)
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | neg x _ hx => exact (neg_mul x _).symm ▸ neg_mem hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add x' y' _ _ hx' hy' => rw [mul_add]; exact add_mem hx' hy'
  | neg x' _ hx' => exact (mul_neg _ x').symm ▸ neg_mem hx'

omit [Algebra ℚ D] in

theorem one_tmul_comm' {S : Type*} [CommRing S] [Algebra ℚ S] [Algebra ℚ D] (c : S) (x : D ⊗[ℚ] S) :
    ((1 : D) ⊗ₜ[ℚ] c) * x = x * ((1 : D) ⊗ₜ[ℚ] c) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul z d => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end LocalBox

section Quaternion

variable {a b : ℚ}

theorem mem_iff_forall_tmul_one_mem_localBox (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (z : ℍ[ℚ, a, b]) : z ∈ Λ ↔ ∀ w : HOS, z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  have h1 := Submodule.ofFiniteIdele_one Λ hΛ.fg hΛ.spanTop
  constructor
  · intro hz w; exact tmul_one_mem_localBox hz w
  · intro hz
    rw [← h1, Submodule.mem_ofFiniteIdele_iff]
    refine ⟨z ⊗ₜ[ℚ] (1 : 𝔸f), ?_, by simp⟩
    rw [SetLike.mem_coe, Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop]
    intro w
    rw [Submodule.finiteAdeleEvalAt_tmul]
    exact hz w

theorem finiteAdeleEvalAt_tmul_one (w : HOS) (z : ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : 𝔸f)) = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]; rfl

theorem mem_finiteAdeleBox_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (t : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    t ∈ Submodule.finiteAdeleBox Λ ↔
      ∀ w : HOS, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w t ∈ Submodule.localBox Λ w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop t

theorem mem_ofFiniteIdele_iff_forall (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele Λ g ↔
      ∀ w : HOS, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) *
        (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox Λ w := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨t, ht, hgt⟩ w
    rw [AddMonoidHom.coe_mulLeft] at hgt
    have ht' : t = ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) := by
      rw [← hgt, Units.inv_mul_cancel_left]
    have := (mem_finiteAdeleBox_iff Λ hΛ t).mp ht w
    rwa [ht', map_mul, finiteAdeleEvalAt_tmul_one] at this
  · intro h
    refine ⟨((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f)), ?_, ?_⟩
    · rw [mem_finiteAdeleBox_iff Λ hΛ]
      intro w
      rw [map_mul, finiteAdeleEvalAt_tmul_one]
      exact h w
    · rw [AddMonoidHom.coe_mulLeft, Units.mul_inv_cancel_left]

section RamifiedPlace

open QuaternionAlgebra Rat.HeightOneSpectrum

theorem nrd_mul' {K : Type*} [CommRing K] {α β : K} (x y : ℍ[K, α, β]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring

theorem nrd_smul' {K : Type*} [CommRing K] {α β : K} (c : K) (x : ℍ[K, α, β]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, nrd_mk, smul_eq_mul]; ring

variable (v : HeightOneSpectrum (𝓞 ℚ))
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hφ : ∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re, algebraMap ℚ (v.adicCompletion ℚ) z.imI,
        algebraMap ℚ (v.adicCompletion ℚ) z.imJ, algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))

include hφ in
theorem nrd_φ_tmul (z : ℍ[ℚ, a, b]) (c : v.adicCompletion ℚ) :
    nrd (φ (z ⊗ₜ[ℚ] c)) = c ^ 2 * algebraMap ℚ (v.adicCompletion ℚ) (nrd z) := by
  rw [hφ, nrd_smul']
  congr 1
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [nrd_mk, map_add, map_sub, map_mul, map_pow]

include hφ in
theorem nrd_φ_one_tmul (c : v.adicCompletion ℚ) : nrd (φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)) = c ^ 2 := by
  rw [nrd_φ_tmul v φ hφ, nrd_one, map_one, mul_one]

theorem nrd_φ_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : nrd (φ (x * y)) = nrd (φ x) * nrd (φ y) := by
  rw [map_mul, nrd_mul']

abbrev VN (y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : WithZero (Multiplicative ℤ) := Valued.v (nrd (φ y))

theorem VN_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : VN v φ (x * y) = VN v φ x * VN v φ y := by
  rw [VN, nrd_φ_mul, map_mul]

theorem VN_one : VN v φ 1 = 1 := by
  rw [VN, map_one, nrd_one, map_one]

theorem VN_units_ne_zero (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : VN v φ (u : _) ≠ 0 := by
  have h : VN v φ (u : _) * VN v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = 1 := by
    rw [← VN_mul, Units.mul_inv, VN_one]
  exact left_ne_zero_of_mul_eq_one h

theorem VN_units_inv (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    VN v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = (VN v φ (u : _))⁻¹ := by
  have h : VN v φ (u : _) * VN v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = 1 := by
    rw [← VN_mul, Units.mul_inv, VN_one]
  exact (eq_inv_of_mul_eq_one_right h)

include hφ in
theorem VN_one_tmul (c : v.adicCompletion ℚ) : VN v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = (Valued.v c) ^ 2 := by
  rw [VN, nrd_φ_one_tmul v φ hφ, map_pow]

include hφ in

theorem VN_tmul_one {q : ℕ} [Fact q.Prime] (hvq : natGenerator v = q) (z : ℍ[ℚ, a, b]) (hz : nrd z ≠ 0) :
    VN v φ (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = WithZero.exp (-padicValRat q (nrd z)) := by
  rw [VN, nrd_φ_tmul v φ hφ, one_pow, one_mul, valued_algebraMap, valuation_eq_exp_neg_padicValRat v hvq _ hz]

include hφ in
theorem VN_one_tmul_algebraMap (r : ℚ) : VN v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) r) =
    (v.valuation ℚ r) ^ 2 := by
  rw [VN_one_tmul v φ hφ, valued_algebraMap]

end RamifiedPlace

def Aniso (a b : ℚ) : Prop :=
  ∀ x₀ x₁ x₂ x₃ : ℚ, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 → x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0

theorem aniso_of_forall_isUnit (v : HOS) (hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y) :
    Aniso a b := by
  intro x₀ x₁ x₂ x₃ h
  set K := v.adicCompletion ℚ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hK : (x₀ : K) ^ 2 - (a : K) * (x₁ : K) ^ 2 - (b : K) * (x₂ : K) ^ 2 + (a : K) * (b : K) * (x₃ : K) ^ 2 = 0 := by
    have := congrArg (fun r : ℚ => (r : K)) h
    simpa using this
  obtain ⟨h0, h1, h2, h3⟩ :=
    (QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero a b v).mp hdiv
      (x₀ : K) (x₁ : K) (x₂ : K) (x₃ : K) hK
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

theorem ne_zero_left_of_aniso (hA : Aniso a b) : a ≠ 0 := by
  intro ha
  have := (hA 0 1 0 0 (by rw [ha]; ring)).2.1
  exact one_ne_zero this

theorem ne_zero_right_of_aniso (hA : Aniso a b) : b ≠ 0 := by
  intro hb
  have := (hA 0 0 1 0 (by rw [hb]; ring)).2.2.1
  exact one_ne_zero this

theorem nrd_ne_zero_of_ne_zero (hA : Aniso a b) {h : ℍ[ℚ, a, b]} (h0 : h ≠ 0) :
    QuaternionAlgebra.nrd h ≠ 0 := by
  intro hn
  apply h0
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  simp only [QuaternionAlgebra.nrd_mk] at hn
  obtain ⟨f0, f1, f2, f3⟩ := hA h₀ h₁ h₂ h₃ hn
  subst f0; subst f1; subst f2; subst f3
  rfl

theorem natCast_tmul_one {S : Type*} [CommRing S] [Algebra ℚ S] (M : ℕ) :
    ((M : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : S)) = ((M : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] S) := by
  rw [Algebra.TensorProduct.natCast_def]

theorem star_mem_of_isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {t : ℍ[ℚ, a, b]}
    (ht : t ∈ Λ) : star t ∈ Λ := by
  obtain ⟨-, tt, htt⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ ht
  have h1 : star t = ((QuaternionAlgebra.trd t : ℚ) : ℍ[ℚ, a, b]) - t := by
    rw [← QuaternionAlgebra.add_star_eq_coe_trd t]; abel
  have h2 : ((tt : ℤ) : ℍ[ℚ, a, b]) = ((tt : ℚ) : ℍ[ℚ, a, b]) := by ext <;> simp
  rw [h1, ← htt, ← h2, ← zsmul_one]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hΛ.one_mem) ht

section OddElement

open QuaternionAlgebra

theorem two_mod_four_of_odd (n d n' d' : ℤ) (hn : Odd n) (hd : Odd d) (hn' : Odd n') (hd' : Odd d') :
    (d - n) % 4 = 2 ∨ (d' - n') % 4 = 2 ∨ (n * d' + n' * d) % 4 = 2 := by
  have key : ∀ x y x' y' : ZMod 4, (x = 1 ∨ x = 3) → (y = 1 ∨ y = 3) → (x' = 1 ∨ x' = 3) → (y' = 1 ∨ y' = 3) →
      (y - x = 2 ∨ y' - x' = 2 ∨ x * y' + x' * y = 2) := by decide
  have cast4 : ∀ z : ℤ, Odd z → ((z : ZMod 4) = 1 ∨ (z : ZMod 4) = 3) := by
    intro z hz
    obtain ⟨k, rfl⟩ := hz
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      have h1 : (2 * k + 1) % ((4 : ℕ) : ℤ) = 1 := by push_cast; omega
      rw [← ZMod.intCast_mod (2 * k + 1) 4, h1]; rfl
    · right
      have h1 : (2 * k + 1) % ((4 : ℕ) : ℤ) = 3 := by push_cast; omega
      rw [← ZMod.intCast_mod (2 * k + 1) 4, h1]; rfl
  have back : ∀ z : ℤ, (z : ZMod 4) = 2 → z % 4 = 2 := by
    intro z hz
    have h1 : ((z - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [hz]; decide
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    omega
  rcases key n d n' d' (cast4 n hn) (cast4 d hd) (cast4 n' hn') (cast4 d' hd') with h | h | h
  · left; apply back; push_cast; exact h
  · right; left; apply back; push_cast; exact h
  · right; right; apply back; push_cast; exact h

theorem padicValInt_two_eq_one {z : ℤ} (hz : z % 4 = 2) : padicValInt 2 z = 1 := by
  have hz0 : z ≠ 0 := by omega
  have h2 : (2 : ℤ) ^ 1 ∣ z := by rw [pow_one]; omega
  have h4 : ¬ (2 : ℤ) ^ 2 ∣ z := by norm_num; omega
  have h1 : 1 ≤ padicValInt 2 z := ((padicValInt_dvd_iff 1 z).mp h2).resolve_left hz0
  have h3 : ¬ 2 ≤ padicValInt 2 z := fun h => h4 ((padicValInt_dvd_iff 2 z).mpr (Or.inr h))
  omega

theorem odd_num_den_of_padicValRat_two {r : ℚ} (hr : r ≠ 0) (h : padicValRat 2 r = 0) :
    Odd r.num ∧ Odd (r.den : ℤ) := by
  have hcop : r.num.natAbs.Coprime r.den := r.reduced
  have hdef : padicValRat 2 r = padicValInt 2 r.num - padicValNat 2 r.den := rfl
  have hnum0 : r.num ≠ 0 := Rat.num_ne_zero.mpr hr
  have hnot : ¬ ((2 : ℤ) ∣ r.num ∧ 2 ∣ r.den) := by
    rintro ⟨h2n, h2d⟩
    have h2n' : 2 ∣ r.num.natAbs := Int.natCast_dvd.mp h2n
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2n' hcop) h2d
    norm_num at this
  by_cases h2n : (2 : ℤ) ∣ r.num
  · exfalso
    have hv : 1 ≤ padicValInt 2 r.num :=
      ((padicValInt_dvd_iff 1 r.num).mp (by rwa [pow_one])).resolve_left hnum0
    have hvd : 1 ≤ padicValNat 2 r.den := by
      have : (padicValNat 2 r.den : ℤ) = padicValInt 2 r.num := by rw [hdef] at h; omega
      omega
    have h2d : 2 ∣ r.den := by
      have := (padicValNat_dvd_iff_le (p := 2) (n := 1) r.den_nz).mpr hvd
      rwa [pow_one] at this
    exact hnot ⟨h2n, h2d⟩
  · have hv : padicValInt 2 r.num = 0 := by
      by_contra hne
      apply h2n
      have h1 : 1 ≤ padicValInt 2 r.num := Nat.one_le_iff_ne_zero.mpr hne
      have := (padicValInt_dvd_iff 1 r.num).mpr (Or.inr h1)
      rwa [pow_one] at this
    have hvd : padicValNat 2 r.den = 0 := by
      have : (padicValNat 2 r.den : ℤ) = padicValInt 2 r.num := by rw [hdef] at h; omega
      rw [hv] at this; exact_mod_cast this
    have h2d : ¬ 2 ∣ r.den := by
      intro hd
      have := (padicValNat_dvd_iff_le (p := 2) (n := 1) r.den_nz).mp (by rwa [pow_one])
      omega
    refine ⟨Int.not_even_iff_odd.mp (fun he => h2n (even_iff_two_dvd.mp he)),
      Int.not_even_iff_odd.mp (fun he => h2d ?_)⟩
    have := even_iff_two_dvd.mp he
    exact_mod_cast Int.natCast_dvd_natCast.mp this

end OddElement

section OddElement2

open QuaternionAlgebra

theorem padicValInt_eq_zero_of_odd {z : ℤ} (hz : Odd z) : padicValInt 2 z = 0 :=
  padicValInt.eq_zero_of_not_dvd (fun h => (Int.not_even_iff_odd.mpr hz) (even_iff_two_dvd.mpr h))

theorem padicValRat_intCast_div_of_odd {A B : ℤ} (hA : A ≠ 0) (hB : Odd B) :
    padicValRat 2 ((A : ℚ) / (B : ℚ)) = padicValInt 2 A := by
  have hB0 : B ≠ 0 := by rintro rfl; exact (Int.not_even_iff_odd.mpr hB) (by decide)
  rw [padicValRat.div (Int.cast_ne_zero.mpr hA) (Int.cast_ne_zero.mpr hB0), padicValRat.of_int, padicValRat.of_int,
    padicValInt_eq_zero_of_odd hB]
  simp

theorem exists_odd_padicValRat_nrd_two (a b : ℚ) (hA : Aniso a b)
    (hea : Even (padicValRat 2 a)) (heb : Even (padicValRat 2 b)) :
    ∃ g : ℍ[ℚ, a, b], g ≠ 0 ∧ Odd (padicValRat 2 (QuaternionAlgebra.nrd g)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hea
  obtain ⟨n, hn⟩ := heb
  have h20 : ((2 : ℕ) : ℚ) ≠ 0 := by norm_num
  have ha0 : a ≠ 0 := ne_zero_left_of_aniso hA
  have hb0 : b ≠ 0 := ne_zero_right_of_aniso hA
  set s : ℚ := ((2 : ℕ) : ℚ) ^ (-m) with hs
  set t : ℚ := ((2 : ℕ) : ℚ) ^ (-n) with ht
  have hs0 : s ≠ 0 := zpow_ne_zero _ h20
  have ht0 : t ≠ 0 := zpow_ne_zero _ h20
  set a₀ : ℚ := a * s ^ 2 with ha₀
  set b₀ : ℚ := b * t ^ 2 with hb₀
  have ha₀0 : a₀ ≠ 0 := mul_ne_zero ha0 (pow_ne_zero _ hs0)
  have hb₀0 : b₀ ≠ 0 := mul_ne_zero hb0 (pow_ne_zero _ ht0)

  have hA1 : (1 : ℚ) - a₀ ≠ 0 := by
    intro h0
    have := (hA 1 s 0 0 (by rw [ha₀] at h0; linear_combination h0)).1
    exact one_ne_zero this
  have hA2 : (1 : ℚ) - b₀ ≠ 0 := by
    intro h0
    have := (hA 1 0 t 0 (by rw [hb₀] at h0; linear_combination h0)).1
    exact one_ne_zero this
  have hA3 : a₀ + b₀ ≠ 0 := by
    intro h0
    have := (hA 0 s t 0 (by rw [ha₀, hb₀] at h0; linear_combination -h0)).2.1
    exact hs0 this
  have hva₀ : padicValRat 2 a₀ = 0 := by
    rw [ha₀, padicValRat.mul ha0 (pow_ne_zero _ hs0), padicValRat.pow _, hs, padicValRat_zpow_self, hm]; ring
  have hvb₀ : padicValRat 2 b₀ = 0 := by
    rw [hb₀, padicValRat.mul hb0 (pow_ne_zero _ ht0), padicValRat.pow _, ht, padicValRat_zpow_self, hn]; ring
  obtain ⟨hN₁, hD₁⟩ := odd_num_den_of_padicValRat_two ha₀0 hva₀
  obtain ⟨hN₂, hD₂⟩ := odd_num_den_of_padicValRat_two hb₀0 hvb₀
  set N₁ := a₀.num with hN₁def
  set D₁ : ℤ := (a₀.den : ℤ) with hD₁def
  set N₂ := b₀.num with hN₂def
  set D₂ : ℤ := (b₀.den : ℤ) with hD₂def
  have hD₁0 : (D₁ : ℚ) ≠ 0 := by rw [hD₁def, Int.cast_natCast]; exact Nat.cast_ne_zero.mpr a₀.den_nz
  have hD₂0 : (D₂ : ℚ) ≠ 0 := by rw [hD₂def, Int.cast_natCast]; exact Nat.cast_ne_zero.mpr b₀.den_nz
  have ha₀q : a₀ = (N₁ : ℚ) / (D₁ : ℚ) := by rw [hN₁def, hD₁def, Int.cast_natCast, Rat.num_div_den]
  have hb₀q : b₀ = (N₂ : ℚ) / (D₂ : ℚ) := by rw [hN₂def, hD₂def, Int.cast_natCast, Rat.num_div_den]

  have e1 : 1 - a₀ = ((D₁ - N₁ : ℤ) : ℚ) / (D₁ : ℚ) := by
    rw [ha₀q, Int.cast_sub, sub_div, div_self hD₁0]
  have e2 : 1 - b₀ = ((D₂ - N₂ : ℤ) : ℚ) / (D₂ : ℚ) := by
    rw [hb₀q, Int.cast_sub, sub_div, div_self hD₂0]
  have e3 : a₀ + b₀ = ((N₁ * D₂ + N₂ * D₁ : ℤ) : ℚ) / ((D₁ * D₂ : ℤ) : ℚ) := by
    rw [ha₀q, hb₀q, div_add_div _ _ hD₁0 hD₂0]; push_cast; ring
  have hne1 : D₁ - N₁ ≠ 0 := by
    intro h0; have : (1 : ℚ) - a₀ = 0 := by rw [e1, h0, Int.cast_zero, zero_div]
    exact hA1 this
  have hne2 : D₂ - N₂ ≠ 0 := by
    intro h0; have : (1 : ℚ) - b₀ = 0 := by rw [e2, h0, Int.cast_zero, zero_div]
    exact hA2 this
  have hne3 : N₁ * D₂ + N₂ * D₁ ≠ 0 := by
    intro h0; have : a₀ + b₀ = 0 := by rw [e3, h0, Int.cast_zero, zero_div]
    exact hA3 this

  have n1 : nrd (⟨1, s, 0, 0⟩ : ℍ[ℚ, a, b]) = 1 - a₀ := by simp only [nrd_mk, ha₀]; ring
  have n2 : nrd (⟨1, 0, t, 0⟩ : ℍ[ℚ, a, b]) = 1 - b₀ := by simp only [nrd_mk, hb₀]; ring
  have n3 : nrd (⟨0, s, t, 0⟩ : ℍ[ℚ, a, b]) = -(a₀ + b₀) := by simp only [nrd_mk, ha₀, hb₀]; ring
  rcases two_mod_four_of_odd N₁ D₁ N₂ D₂ hN₁ hD₁ hN₂ hD₂ with h | h | h
  · refine ⟨⟨1, s, 0, 0⟩, fun h0 => by have := congrArg QuaternionAlgebra.re h0; simp at this, ?_⟩
    rw [n1, e1, padicValRat_intCast_div_of_odd hne1 hD₁, padicValInt_two_eq_one h]
    exact odd_one
  · refine ⟨⟨1, 0, t, 0⟩, fun h0 => by have := congrArg QuaternionAlgebra.re h0; simp at this, ?_⟩
    rw [n2, e2, padicValRat_intCast_div_of_odd hne2 hD₂, padicValInt_two_eq_one h]
    exact odd_one
  · refine ⟨⟨0, s, t, 0⟩, fun h0 => by have := congrArg QuaternionAlgebra.imI h0; exact hs0 (by simpa using this), ?_⟩
    rw [n3, padicValRat.neg, e3, padicValRat_intCast_div_of_odd hne3 (hD₁.mul hD₂), padicValInt_two_eq_one h]
    exact odd_one

theorem exists_odd_padicValRat_nrd (q' : ℕ) [hq : Fact q'.Prime]
    (hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] (place q' hq.out).adicCompletion ℚ, y ≠ 0 → IsUnit y) :
    ∃ g : ℍ[ℚ, a, b], g ≠ 0 ∧ Odd (padicValRat q' (QuaternionAlgebra.nrd g)) := by
  have hqp : q'.Prime := hq.out
  have hA : Aniso a b := aniso_of_forall_isUnit (place q' hqp) hdiv
  have ha : a ≠ 0 := ne_zero_left_of_aniso hA
  have hb : b ≠ 0 := ne_zero_right_of_aniso hA
  have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := fun h0 => by
    have := congrArg QuaternionAlgebra.imI h0; simp at this
  have hj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := fun h0 => by
    have := congrArg QuaternionAlgebra.imJ h0; simp at this
  have ni : nrd (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) = -a := by simp only [nrd_mk]; ring
  have nj : nrd (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) = -b := by simp only [nrd_mk]; ring
  rcases Int.even_or_odd (padicValRat q' a) with hea | hoa
  · rcases Int.even_or_odd (padicValRat q' b) with heb | hob
    · by_cases hq2 : q' = 2
      · subst hq2
        exact exists_odd_padicValRat_nrd_two a b hA hea heb
      · exfalso
        obtain ⟨x₀, x₁, x₂, x₃, hne, h0⟩ := exists_normForm_eq_zero_of_even q' hq2 a b ha hb hea heb
        exact hne ((QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero a b
          (place q' hqp)).mp hdiv x₀ x₁ x₂ x₃ h0)
    · exact ⟨⟨0, 0, 1, 0⟩, hj, by rw [nj, padicValRat.neg]; exact hob⟩
  · exact ⟨⟨0, 1, 0, 0⟩, hi, by rw [ni, padicValRat.neg]; exact hoa⟩

end OddElement2

section Main

open QuaternionAlgebra Rat.HeightOneSpectrum

theorem smul_tmul_one {S : Type*} [CommRing S] [Algebra ℚ S] (r : ℚ) (z : ℍ[ℚ, a, b]) :
    ((r • z) ⊗ₜ[ℚ] (1 : S)) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ S r) * (z ⊗ₜ[ℚ] (1 : S)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul]

theorem main (q' : ℕ) [hq : Fact q'.Prime] (v : HOS) (hqv : (q' : 𝓞 ℚ) ∈ v.asIdeal)
    (hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ h ∈ Λ, h ≠ 0 ∧ padicValRat q' (QuaternionAlgebra.nrd h) = 1 := by
  classical
  have hqp : q'.Prime := hq.out
  have hq0 : (q' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqp.ne_zero
  have hq1 : 1 < q' := hqp.one_lt
  have hO : IsOrder Λ := hΛ.1

  have hvdef : v = place q' hqp := (eq_of_natCast_mem hqp (q_mem_asIdeal_place q' hqp) hqv)
  subst hvdef
  have hA : Aniso a b := aniso_of_forall_isUnit (place q' hqp) hdiv

  have hvq : natGenerator (place q' hqp) = q' := natGenerator_place q' hqp
  set v : HOS := place q' hqp with hvdef
  set K := v.adicCompletion ℚ with hK
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl AlgEquiv.refl
  have hφ' : ∀ (z : ℍ[ℚ, a, b]) (r : K),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ K z.re, algebraMap ℚ K z.imI, algebraMap ℚ K z.imJ, algebraMap ℚ K z.imK⟩ :
          ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b]) :=
    fun z r => by rw [hφ]; simp only [AlgEquiv.coe_refl, id_eq]
  have hVle : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] K, y ∈ Submodule.localBox Λ v ↔ VN v φ y ≤ 1 := fun y => by
    rw [hΛ.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit v hdiv φ hφ' y,
      HeightOneSpectrum.mem_adicCompletionIntegers]

  obtain ⟨g, hg0, hgodd⟩ := exists_odd_padicValRat_nrd q' hdiv
  have hnrdg : nrd g ≠ 0 := nrd_ne_zero_of_ne_zero hA hg0

  obtain ⟨N, hN0, hNg⟩ := QuaternionAlgebra.exists_natCast_smul_mem_of_mem_span (Λ := Λ) (y := g)
    (by rw [hO.spanTop]; trivial)
  set g' : ℍ[ℚ, a, b] := ((N : ℕ) : ℤ) • g with hg'
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have hg'q : g' = (N : ℚ) • g := by rw [hg', ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
  have hg'0 : g' ≠ 0 := by rw [hg'q]; exact smul_ne_zero hNq hg0
  have hnrdg' : nrd g' = (N : ℚ) ^ 2 * nrd g := by
    rw [hg'q, show (N : ℚ) • g = ((N : ℚ) : ℍ[ℚ, a, b]) * g from (QuaternionAlgebra.coe_mul_eq_smul _ _).symm,
      nrd_mul', nrd_coe]
  have hnrdg'0 : nrd g' ≠ 0 := nrd_ne_zero_of_ne_zero hA hg'0

  obtain ⟨m, hm⟩ := hgodd
  have hval' : padicValRat q' (nrd g') = 2 * (padicValRat q' (N : ℚ) + m) + 1 := by
    rw [hnrdg', padicValRat.mul (pow_ne_zero _ hNq) hnrdg, padicValRat.pow _, hm]; ring
  obtain ⟨⟨N₁, hN₁⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hNg
  have hnn : 0 ≤ padicValRat q' (nrd g') := by
    rw [← hN₁, padicValRat.of_int]; exact_mod_cast Nat.zero_le _
  obtain ⟨M, hM⟩ : ∃ M : ℕ, padicValRat q' (N : ℚ) + m = M :=
    ⟨(padicValRat q' (N : ℚ) + m).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩

  set c : ℚ := ((q' : ℚ) ^ M)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (pow_ne_zero _ hq0)
  set h : ℍ[ℚ, a, b] := c • g' with hh
  have hh0 : h ≠ 0 := smul_ne_zero hc0 hg'0
  have hnrdh : nrd h = c ^ 2 * nrd g' := by
    rw [hh, show c • g' = ((c : ℚ) : ℍ[ℚ, a, b]) * g' from (QuaternionAlgebra.coe_mul_eq_smul _ _).symm, nrd_mul', nrd_coe]
  have hvalh : padicValRat q' (nrd h) = 1 := by
    rw [hnrdh, padicValRat.mul (pow_ne_zero _ hc0) hnrdg'0, padicValRat.pow _, hc, padicValRat.inv, padicValRat.pow _,
      padicValRat.self hq1, hval', hM]; ring
  refine ⟨h, ?_, hh0, hvalh⟩

  rw [mem_iff_forall_tmul_one_mem_localBox Λ hO h]
  intro w
  rw [hh, smul_tmul_one]
  by_cases hw : w = v
  · subst hw
    rw [hVle, VN_mul, VN_one_tmul_algebraMap v φ hφ', VN_tmul_one v φ hφ' hvq g' hnrdg'0, valuation_eq_exp_neg_padicValRat v hvq c hc0,
      hc, padicValRat.inv, padicValRat.pow _, padicValRat.self hq1, hval', hM, pow_two, ← WithZero.exp_add, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp]
    push_cast; omega
  · have hn := natCast_notMem_of_ne hqp hqv hw
    have hcw : algebraMap ℚ (w.adicCompletion ℚ) c ∈ w.adicCompletionIntegers ℚ := by
      rw [hc, map_inv₀, map_pow, map_natCast, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_pow,
        valued_natCast_eq_one w hn, one_pow, inv_one]
    exact one_tmul_mul_mem_localBox Λ w (tmul_one_mem_localBox hNg w) hcw

end Main

end Quaternion

end RamUnifDiv

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField QuaternionAlgebra

theorem solution
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ h ∈ Λ, h ≠ 0 ∧ padicValRat p (QuaternionAlgebra.nrd h) = 1 :=
  RamUnifDiv.main p v hpv hdiv Λ hΛ

end
end S_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit (solution)
