-- Prove2me | solution 1 for QuaternionAlgebra.forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/be630b77-a8a7-5704-aa56-ce5c211aa265

import Mathlib
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_LocalLanglands_CartanDecomposition
import Theorems.Thm_LocalGL2_exists_cartanRel_cartanDiag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace QNLocNF

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

theorem eq_place_of_mem (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) : v = 𝔳 := by
  rw [natCast_mem_asIdeal_iff] at hv
  have hgen : Rat.HeightOneSpectrum.natGenerator v = q :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hq).mp hv
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [primesEquiv_place]
  exact Subtype.ext hgen

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

theorem valued_q_pow (n : ℕ) : Valued.v (((q : ℕ) : 𝕂) ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [map_pow, valued_q, ← WithZero.exp_nsmul]
  congr 1
  simp

theorem q_ne_zero' : ((q : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_q q hq
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem q_pow_ne_zero (n : ℕ) : ((q : ℕ) : 𝕂) ^ n ≠ 0 := pow_ne_zero n (q_ne_zero' q hq)

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

theorem exists_pow_mul_mem (x : 𝕂) : ∃ k : ℕ, ((q : ℕ) : 𝕂) ^ k * x ∈ 𝓞v := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, mul_zero]; exact zero_mem _⟩
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  set m : ℤ := WithZero.log (Valued.v x) with hm
  have hxm : Valued.v x = WithZero.exp m := (WithZero.exp_log hvx).symm
  refine ⟨m.toNat, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, valued_q_pow, hxm, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  have := Int.self_le_toNat m
  omega

theorem pow_mul_mem_of_le {x : 𝕂} {k K : ℕ} (hk : ((q : ℕ) : 𝕂) ^ k * x ∈ 𝓞v) (hkK : k ≤ K) :
    ((q : ℕ) : 𝕂) ^ K * x ∈ 𝓞v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkK
  rw [pow_add, mul_comm (((q : ℕ) : 𝕂) ^ k), mul_assoc]
  exact mul_mem (pow_mem (q_mem_integers q hq) d) hk

theorem irreducible_q : Irreducible ((q : ℕ) : 𝓞v) := by
  haveI : Fact q.Prime := ⟨hq⟩
  let e := PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨q, hq⟩
  have h1 : Irreducible (e (q : ℤ_[q])) := (PadicInt.irreducible_p (p := q)).map e
  rwa [map_natCast] at h1

theorem le_of_mul_pow_inv_mul_pow_mem {a b : ℕ}
    (h : ((q : ℕ) : 𝕂) * ((((q : ℕ) : 𝕂) ^ b)⁻¹ * ((q : ℕ) : 𝕂) ^ a) ∈ 𝓞v) : b ≤ a + 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_mul, map_inv₀, valued_q, valued_q_pow,
    valued_q_pow, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h
  omega

end Places

section Local

variable {a b : ℚ} (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq)

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq) ≃+*
    Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))
  (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ (place q hq),
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))))
  (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))

include hφ in
omit g in
theorem map_one_tmul_mul (c : 𝕂) (x : ℍv) : φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • φ x := by
  rw [map_mul, hφ, smul_mul_assoc, one_mul]

include hφ in
omit g in
theorem map_mul_one_tmul (c : 𝕂) (x : ℍv) : φ (x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)) = c • φ x := by
  rw [map_mul, hφ, mul_smul_comm, mul_one]

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

omit φ g in
theorem mem_intMat_iff (M : M₂) : M ∈ intMat q hq ↔ ∀ i j, M i j ∈ 𝓞v := Iff.rfl

omit φ g in
theorem smul_mem_intMat {M : M₂} (hM : M ∈ intMat q hq) {c : 𝕂} (hc : c ∈ 𝓞v) : c • M ∈ intMat q hq :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

abbrev coord (y : ℍv) : M₂ := ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * φ y * (g : M₂)

theorem coord_mul (x y : ℍv) : coord q hq φ g (x * y) = coord q hq φ g x * coord q hq φ g y := by
  have e : (g : M₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) = 1 := Units.mul_inv g
  simp only [coord, map_mul]
  calc ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * (φ x * φ y) * (g : M₂)
      = ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * φ x * ((g : M₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)) * φ y * (g : M₂) := by
        rw [e]; noncomm_ring
    _ = _ := by noncomm_ring

theorem coord_one : coord q hq φ g 1 = 1 := by
  simp only [coord, map_one, mul_one]; exact Units.inv_mul g

theorem map_eq_of_coord (y : ℍv) : φ y = (g : M₂) * coord q hq φ g y * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) := by
  have e : (g : M₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) = 1 := Units.mul_inv g
  calc φ y = ((g : M₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)) * φ y * ((g : M₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)) := by
        rw [e, one_mul, mul_one]
    _ = _ := by simp only [coord]; noncomm_ring

theorem coord_symm (M : M₂) : coord q hq φ g (φ.symm ((g : M₂) * M * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂))) = M := by
  simp only [coord, RingEquiv.apply_symm_apply]
  have e : ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * (g : M₂) = 1 := Units.inv_mul g
  calc ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * ((g : M₂) * M * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)) * (g : M₂)
      = (((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * (g : M₂)) * M * (((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * (g : M₂)) := by noncomm_ring
    _ = M := by rw [e, one_mul, mul_one]

include hφ in
theorem coord_one_tmul_mul (c : 𝕂) (y : ℍv) : coord q hq φ g (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * y) = c • coord q hq φ g y := by
  simp only [coord, map_one_tmul_mul q hq φ hφ, Matrix.mul_smul, Matrix.smul_mul]

omit φ g in

theorem smul_mul_smul_mul_smul (r s t : 𝕂) (X Y Z : M₂) :
    (r • X) * (s • Y) * (t • Z) = (r * s * t) • (X * Y * Z) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

omit φ g in

theorem smul_mul_smul₂ (r s : 𝕂) (X Y : M₂) : (r • X) * (s • Y) = (r * s) • (X * Y) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

abbrev ι : Matrix (Fin 2) (Fin 2) 𝓞v →+* M₂ :=
  (HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)).subtype.mapMatrix

omit φ g in
theorem ι_apply (M : Matrix (Fin 2) (Fin 2) 𝓞v) (i j : Fin 2) : ι q hq M i j = (M i j : 𝕂) := rfl

omit φ g in
theorem ι_mem_intMat (M : Matrix (Fin 2) (Fin 2) 𝓞v) : ι q hq M ∈ intMat q hq :=
  fun i j => by rw [ι_apply]; exact (M i j).2

omit φ g in
theorem exists_eq_ι_of_mem_intMat {G : M₂} (hG : G ∈ intMat q hq) :
    ∃ M : Matrix (Fin 2) (Fin 2) 𝓞v, ι q hq M = G :=
  ⟨Matrix.of fun i j => ⟨G i j, hG i j⟩, by ext i j; rfl⟩

omit φ g in
theorem ι_cartanDiag (m n : ℕ) :
    ι q hq (LocalGL2.cartanDiag ((q : ℕ) : 𝓞v) m n) = !![((q : ℕ) : 𝕂) ^ m, 0; 0, ((q : ℕ) : 𝕂) ^ n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ι_apply, LocalGL2.cartanDiag]

omit φ g in
theorem ι_units_mul_inv (k : (Matrix (Fin 2) (Fin 2) 𝓞v)ˣ) : ι q hq k.val * ι q hq (k⁻¹).val = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

omit φ g in
theorem ι_units_inv_mul (k : (Matrix (Fin 2) (Fin 2) 𝓞v)ˣ) : ι q hq (k⁻¹).val * ι q hq k.val = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

omit φ g in

theorem mem_intMat_iff_of_conj {K Ki : M₂} (hK : K ∈ intMat q hq) (hKi : Ki ∈ intMat q hq)
    (h1 : K * Ki = 1) (h2 : Ki * K = 1) (M : M₂) :
    Ki * M * K ∈ intMat q hq ↔ M ∈ intMat q hq := by
  constructor
  · intro h
    have : M = K * (Ki * M * K) * Ki := by
      calc M = (K * Ki) * M * (K * Ki) := by rw [h1, one_mul, mul_one]
        _ = _ := by noncomm_ring
    rw [this]
    exact (intMat q hq).mul_mem ((intMat q hq).mul_mem hK h) hKi
  · intro h
    exact (intMat q hq).mul_mem ((intMat q hq).mul_mem hKi h) hK

end Local

section Cartan

variable {a b : ℚ} (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq)

theorem cancel_left {A B : M₂} (h : A * B = 1) (X : M₂) : A * (B * X) = X := by
  rw [← mul_assoc, h, one_mul]

def Dg (m n : ℕ) : M₂ := !![((q : ℕ) : 𝕂) ^ m, 0; 0, ((q : ℕ) : 𝕂) ^ n]

def Dgi (m n : ℕ) : M₂ := !![(((q : ℕ) : 𝕂) ^ m)⁻¹, 0; 0, (((q : ℕ) : 𝕂) ^ n)⁻¹]

theorem Dg_mul_Dgi (m n : ℕ) : Dg q hq m n * Dgi q hq m n = 1 := by
  rw [Dg, Dgi, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [q_pow_ne_zero q hq]

theorem Dgi_mul_Dg (m n : ℕ) : Dgi q hq m n * Dg q hq m n = 1 := by
  rw [Dg, Dgi, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [q_pow_ne_zero q hq]

def E21 : M₂ := !![0, 0; 1, 0]

theorem E21_mem_intMat : E21 q hq ∈ intMat q hq := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E21, one_mem, zero_mem]

theorem Dgi_E21_Dg (m n : ℕ) :
    Dgi q hq m n * E21 q hq * Dg q hq m n = !![0, 0; (((q : ℕ) : 𝕂) ^ n)⁻¹ * ((q : ℕ) : 𝕂) ^ m, 0] := by
  rw [Dgi, E21, Dg, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

def D1 : M₂ := !![1, 0; 0, ((q : ℕ) : 𝕂)]

def D1i : M₂ := !![1, 0; 0, ((q : ℕ) : 𝕂)⁻¹]

theorem D1_mul_D1i : D1 q hq * D1i q hq = 1 := by
  rw [D1, D1i, Matrix.mul_fin_two, Matrix.one_fin_two]; simp [q_ne_zero' q hq]

theorem D1i_mul_D1 : D1i q hq * D1 q hq = 1 := by
  rw [D1, D1i, Matrix.mul_fin_two, Matrix.one_fin_two]; simp [q_ne_zero' q hq]

theorem D1_mem_intMat : D1 q hq ∈ intMat q hq := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [D1, one_mem, zero_mem, q_mem_integers q hq]

theorem q_smul_D1i_mem_intMat : ((q : ℕ) : 𝕂) • D1i q hq ∈ intMat q hq := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [D1i, one_mem, zero_mem, q_mem_integers q hq, q_ne_zero' q hq]

theorem D1i_notMem_intMat : D1i q hq ∉ intMat q hq := by
  intro h
  have := h 1 1
  simp only [D1i, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
  exact q_inv_notMem_integers q hq this

theorem q_inv_smul_D1_notMem_intMat : ((q : ℕ) : 𝕂)⁻¹ • D1 q hq ∉ intMat q hq := by
  intro h
  have := h 0 0
  simp only [D1, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, smul_eq_mul,
    mul_one] at this
  exact q_inv_notMem_integers q hq this

theorem Dg_succ (m : ℕ) : Dg q hq m (m + 1) = (((q : ℕ) : 𝕂) ^ m) • D1 q hq := by
  rw [Dg, D1]
  ext i j; fin_cases i <;> fin_cases j <;> simp [pow_succ]

theorem Dgi_succ (m : ℕ) : Dgi q hq m (m + 1) = ((((q : ℕ) : 𝕂) ^ m)⁻¹) • D1i q hq := by
  rw [Dgi, D1i]
  ext i j; fin_cases i <;> fin_cases j <;> simp [pow_succ, mul_inv, mul_comm]

theorem Dg_self (m : ℕ) : Dg q hq m m = (((q : ℕ) : 𝕂) ^ m) • (1 : M₂) := by
  rw [Dg, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem Dgi_self (m : ℕ) : Dgi q hq m m = ((((q : ℕ) : 𝕂) ^ m)⁻¹) • (1 : M₂) := by
  rw [Dgi, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq) ≃+*
    Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))
  (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ (place q hq),
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))))
  (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))
  (O : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq)))
  (hO' : ∀ x, x ∈ O ↔ coord q hq φ g x ∈ intMat q hq)
  (ν : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq))ˣ)
  (c : HeightOneSpectrum.adicCompletion ℚ (place q hq)) (hc0 : c ≠ 0)
  (K₁ K₁i K₂ K₂i : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))
  (hK₁K₁i : K₁ * K₁i = 1) (hK₁iK₁ : K₁i * K₁ = 1) (hK₂K₂i : K₂ * K₂i = 1) (hK₂iK₂ : K₂i * K₂ = 1)
  (hK₁int : K₁ ∈ intMat q hq) (hK₁iint : K₁i ∈ intMat q hq)
  (hK₂int : K₂ ∈ intMat q hq) (hK₂iint : K₂i ∈ intMat q hq)
  (m n : ℕ)
  (hGeq : coord q hq φ g (ν : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq)) =
    c⁻¹ • (K₁ * Dg q hq m n * K₂))
  (hGieq : coord q hq φ g ((ν⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq))ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq)) =
    c • (K₂i * Dgi q hq m n * K₁i))

include hGeq hGieq hc0 in

theorem coord_conj (y : ℍv) : coord q hq φ g (((ν⁻¹ : (ℍv)ˣ) : ℍv) * y * ν) =
    K₂i * (Dgi q hq m n * (K₁i * (coord q hq φ g y * (K₁ * (Dg q hq m n * K₂))))) := by
  rw [coord_mul, coord_mul, hGieq, hGeq, show coord q hq φ g y = (1 : 𝕂) • coord q hq φ g y by rw [one_smul],
    smul_mul_smul_mul_smul, mul_one, mul_inv_cancel₀ hc0, one_smul, one_smul]
  simp only [mul_assoc]

include hφ hO' hGeq hGieq hc0 hK₁K₁i hK₁iK₁ hK₂K₂i hK₂iK₂ hK₁int hK₁iint hK₂int hK₂iint in

theorem le_succ_of_test
    (hν : ∀ y ∈ O, ((ν⁻¹ : (ℍv)ˣ) : ℍv) * (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : 𝕂)) * y) * ν ∈ O) :
    n ≤ m + 1 := by
  set y₀ : ℍv := φ.symm ((g : M₂) * (K₁ * E21 q hq * K₁i) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)) with hy₀
  have hcy₀ : coord q hq φ g y₀ = K₁ * E21 q hq * K₁i := coord_symm q hq φ g _
  have hy₀O : y₀ ∈ O := by
    rw [hO', hcy₀]
    exact (intMat q hq).mul_mem ((intMat q hq).mul_mem hK₁int (E21_mem_intMat q hq)) hK₁iint
  have htest := hν y₀ hy₀O
  rw [hO', coord_conj q hq φ g ν c hc0 K₁ K₁i K₂ K₂i m n hGeq hGieq, coord_one_tmul_mul q hq φ hφ g, hcy₀] at htest
  have e1 : K₂i * (Dgi q hq m n * (K₁i * (((q : ℕ) : 𝕂) • (K₁ * E21 q hq * K₁i) * (K₁ * (Dg q hq m n * K₂))))) =
      K₂i * (((q : ℕ) : 𝕂) • (Dgi q hq m n * E21 q hq * Dg q hq m n)) * K₂ := by
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc, cancel_left q hq hK₁iK₁]
  rw [e1, mem_intMat_iff_of_conj q hq hK₂int hK₂iint hK₂K₂i hK₂iK₂, Dgi_E21_Dg] at htest
  have h10 := htest 1 0
  rw [Matrix.smul_apply, smul_eq_mul] at h10
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h10
  exact le_of_mul_pow_inv_mul_pow_mem q hq h10

include hO' hGeq hGieq hc0 hK₁K₁i hK₁iK₁ hK₂K₂i hK₂iK₂ hK₁int hK₁iint hK₂int hK₂iint in

theorem normalises_of_eq (hnm : n = m) (y : ℍv) : ((ν⁻¹ : (ℍv)ˣ) : ℍv) * y * ν ∈ O ↔ y ∈ O := by
  rw [hO', hO', coord_conj q hq φ g ν c hc0 K₁ K₁i K₂ K₂i m n hGeq hGieq, hnm, Dg_self, Dgi_self]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, inv_mul_cancel₀ (q_pow_ne_zero q hq m),
    mul_inv_cancel₀ (q_pow_ne_zero q hq m), one_smul]
  rw [show K₂i * (K₁i * (coord q hq φ g y * (K₁ * K₂))) = (K₂i * K₁i) * coord q hq φ g y * (K₁ * K₂) by
      simp only [mul_assoc]]
  refine mem_intMat_iff_of_conj q hq ((intMat q hq).mul_mem hK₁int hK₂int)
    ((intMat q hq).mul_mem hK₂iint hK₁iint) ?_ ?_ _
  · rw [mul_assoc, cancel_left q hq hK₂K₂i, hK₁K₁i]
  · rw [mul_assoc, cancel_left q hq hK₁iK₁, hK₂iK₂]

include hφ hO' hGeq hc0 hK₁K₁i hK₁iK₁ hK₂K₂i hK₂iK₂ hK₁int hK₁iint hK₂int hK₂iint in

theorem exists_of_succ (hn : n = m + 1) :
    ∃ (s : 𝕂) (ν₀ : (ℍv)ˣ),
      (ν : ℍv) = ν₀ * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) ∧
      (ν₀ : ℍv) ∈ O ∧
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : 𝕂)) * ((ν₀⁻¹ : (ℍv)ˣ) : ℍv) ∈ O ∧
      ((ν₀⁻¹ : (ℍv)ˣ) : ℍv) ∉ O ∧
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : 𝕂)⁻¹) * (ν₀ : ℍv) ∉ O := by
  have hgg : (g : M₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) = 1 := Units.mul_inv g
  have hgg' : ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) * (g : M₂) = 1 := Units.inv_mul g

  have hval : (g : M₂) * (K₁ * D1 q hq * K₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) *
      ((g : M₂) * (K₂i * D1i q hq * K₁i) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)) = 1 := by
    simp only [mul_assoc, cancel_left q hq hgg', cancel_left q hq hK₂K₂i, cancel_left q hq (D1_mul_D1i q hq),
      cancel_left q hq hK₁K₁i, hgg]
  have hinv : (g : M₂) * (K₂i * D1i q hq * K₁i) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂) *
      ((g : M₂) * (K₁ * D1 q hq * K₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)) = 1 := by
    simp only [mul_assoc, cancel_left q hq hgg', cancel_left q hq hK₁iK₁, cancel_left q hq (D1i_mul_D1 q hq),
      cancel_left q hq hK₂iK₂, hgg]
  let ν₀ : (ℍv)ˣ :=
    ⟨φ.symm ((g : M₂) * (K₁ * D1 q hq * K₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)),
     φ.symm ((g : M₂) * (K₂i * D1i q hq * K₁i) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)),
     by rw [← map_mul, hval, map_one], by rw [← map_mul, hinv, map_one]⟩
  have hν₀ : (ν₀ : ℍv) = φ.symm ((g : M₂) * (K₁ * D1 q hq * K₂) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)) := rfl
  have hν₀i : ((ν₀⁻¹ : (ℍv)ˣ) : ℍv) = φ.symm ((g : M₂) * (K₂i * D1i q hq * K₁i) * ((g⁻¹ : GL (Fin 2) 𝕂) : M₂)) := rfl
  have hcν₀ : coord q hq φ g (ν₀ : ℍv) = K₁ * D1 q hq * K₂ := by rw [hν₀]; exact coord_symm q hq φ g _
  have hcν₀i : coord q hq φ g ((ν₀⁻¹ : (ℍv)ˣ) : ℍv) = K₂i * D1i q hq * K₁i := by
    rw [hν₀i]; exact coord_symm q hq φ g _
  refine ⟨c⁻¹ * ((q : ℕ) : 𝕂) ^ m, ν₀, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply φ.injective
    rw [map_mul_one_tmul q hq φ hφ, map_eq_of_coord q hq φ g (ν : ℍv), map_eq_of_coord q hq φ g (ν₀ : ℍv), hcν₀,
      hGeq, hn, Dg_succ]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  ·
    rw [hO', hcν₀]
    exact (intMat q hq).mul_mem ((intMat q hq).mul_mem hK₁int (D1_mem_intMat q hq)) hK₂int
  ·
    rw [hO', coord_one_tmul_mul q hq φ hφ g, hcν₀i,
      show ((q : ℕ) : 𝕂) • (K₂i * D1i q hq * K₁i) = K₂i * (((q : ℕ) : 𝕂) • D1i q hq) * K₁i by
        simp only [smul_mul_assoc, mul_smul_comm]]
    exact (intMat q hq).mul_mem ((intMat q hq).mul_mem hK₂iint (q_smul_D1i_mem_intMat q hq)) hK₁iint
  ·
    rw [hO', hcν₀i]
    intro hmem
    apply D1i_notMem_intMat q hq
    have h2 := (intMat q hq).mul_mem ((intMat q hq).mul_mem hK₂int hmem) hK₁int
    have e : K₂ * (K₂i * D1i q hq * K₁i) * K₁ = D1i q hq := by
      simp only [mul_assoc, cancel_left q hq hK₂K₂i, hK₁iK₁, mul_one]
    rwa [e] at h2
  ·
    rw [hO', coord_one_tmul_mul q hq φ hφ g, hcν₀]
    intro hmem
    apply q_inv_smul_D1_notMem_intMat q hq
    have h2 := (intMat q hq).mul_mem ((intMat q hq).mul_mem hK₁iint hmem) hK₂iint
    have e : K₁i * (((q : ℕ) : 𝕂)⁻¹ • (K₁ * D1 q hq * K₂)) * K₂i = ((q : ℕ) : 𝕂)⁻¹ • D1 q hq := by
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      simp only [mul_assoc, cancel_left q hq hK₁iK₁, hK₂K₂i, mul_one]
    rwa [e] at h2

end Cartan

section Main

variable {a b : ℚ} (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq)

theorem main
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place q hq) ≃+*
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))
    (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ (place q hq),
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))))
    (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq)))
    (O : AddSubgroup ℍv)
    (hO : ∀ x, x ∈ O ↔ ∀ i j, (coord q hq φ g x) i j ∈ 𝓞v)
    (ν : (ℍv)ˣ)
    (hν : ∀ y ∈ O, ((ν⁻¹ : (ℍv)ˣ) : ℍv) * (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : 𝕂)) * y) * ν ∈ O) :
    (∀ y : ℍv, ((ν⁻¹ : (ℍv)ˣ) : ℍv) * y * ν ∈ O ↔ y ∈ O) ∨
      ∃ (s : 𝕂) (ν₀ : (ℍv)ˣ),
        (ν : ℍv) = ν₀ * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) ∧
        (ν₀ : ℍv) ∈ O ∧
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : 𝕂)) * ((ν₀⁻¹ : (ℍv)ˣ) : ℍv) ∈ O ∧
        ((ν₀⁻¹ : (ℍv)ˣ) : ℍv) ∉ O ∧
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : 𝕂)⁻¹) * (ν₀ : ℍv) ∉ O := by
  have hO' : ∀ x, x ∈ O ↔ coord q hq φ g x ∈ intMat q hq := hO
  have hq0 : ((q : ℕ) : 𝕂) ≠ 0 := q_ne_zero' q hq

  set G : M₂ := coord q hq φ g (ν : ℍv) with hG
  set Gi : M₂ := coord q hq φ g ((ν⁻¹ : (ℍv)ˣ) : ℍv) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← coord_mul, Units.mul_inv, coord_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← coord_mul, Units.inv_mul, coord_one]

  have hden : ∀ i j, ∃ k : ℕ, ((q : ℕ) : 𝕂) ^ k * G i j ∈ 𝓞v := fun i j => exists_pow_mul_mem q hq (G i j)
  choose k hk using hden
  set K : ℕ := ∑ i, ∑ j, k i j with hK
  have hkK : ∀ i j, k i j ≤ K := by
    intro i j
    calc k i j ≤ ∑ j', k i j' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', k i' j' :=
        Finset.single_le_sum (f := fun i' => ∑ j', k i' j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set c : 𝕂 := ((q : ℕ) : 𝕂) ^ K with hc
  have hc0 : c ≠ 0 := q_pow_ne_zero q hq K
  have hG₁ : c • G ∈ intMat q hq := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact pow_mul_mem_of_le q hq (hk i j) (hkK i j)

  obtain ⟨M₁, hM₁⟩ := exists_eq_ι_of_mem_intMat q hq hG₁
  have hdetG : G.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hGGi
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetM₁ : M₁.det ≠ 0 := by
    intro h0
    have h1 : (HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)).subtype M₁.det = (c • G).det := by
      rw [RingHom.map_det, hM₁]
    rw [h0, map_zero, Matrix.det_smul, Fintype.card_fin] at h1
    exact (mul_ne_zero (pow_ne_zero _ hc0) hdetG) h1.symm
  obtain ⟨m, n, hmn, k₁, k₂, hcartan⟩ := LocalGL2.exists_cartanRel_cartanDiag (irreducible_q q hq) M₁ hdetM₁
  set K₁ : M₂ := ι q hq k₁.val with hK₁
  set K₁i : M₂ := ι q hq (k₁⁻¹).val with hK₁i
  set K₂ : M₂ := ι q hq k₂.val with hK₂
  set K₂i : M₂ := ι q hq (k₂⁻¹).val with hK₂i
  have hK₁K₁i : K₁ * K₁i = 1 := ι_units_mul_inv q hq k₁
  have hK₁iK₁ : K₁i * K₁ = 1 := ι_units_inv_mul q hq k₁
  have hK₂K₂i : K₂ * K₂i = 1 := ι_units_mul_inv q hq k₂
  have hK₂iK₂ : K₂i * K₂ = 1 := ι_units_inv_mul q hq k₂
  have hK₁int : K₁ ∈ intMat q hq := ι_mem_intMat q hq _
  have hK₁iint : K₁i ∈ intMat q hq := ι_mem_intMat q hq _
  have hK₂int : K₂ ∈ intMat q hq := ι_mem_intMat q hq _
  have hK₂iint : K₂i ∈ intMat q hq := ι_mem_intMat q hq _

  have hEQ : c • G = K₁ * Dg q hq m n * K₂ := by
    rw [← hM₁, hcartan, map_mul, map_mul, ι_cartanDiag]; rfl
  have hGeq : G = c⁻¹ • (K₁ * Dg q hq m n * K₂) := by
    rw [← hEQ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hGieq : Gi = c • (K₂i * Dgi q hq m n * K₁i) := by
    have hX : G * (c • (K₂i * Dgi q hq m n * K₁i)) = 1 := by
      rw [hGeq, smul_mul_smul₂, inv_mul_cancel₀ hc0, one_smul]
      simp only [mul_assoc, cancel_left q hq hK₂K₂i, cancel_left q hq (Dg_mul_Dgi q hq m n), hK₁K₁i]
    calc Gi = Gi * (G * (c • (K₂i * Dgi q hq m n * K₁i))) := by rw [hX, mul_one]
      _ = (Gi * G) * (c • (K₂i * Dgi q hq m n * K₁i)) := (mul_assoc Gi G _).symm
      _ = _ := by rw [hGiG, one_mul]

  have hnm : n ≤ m + 1 :=
    le_succ_of_test q hq φ hφ g O hO' ν c hc0 K₁ K₁i K₂ K₂i hK₁K₁i hK₁iK₁ hK₂K₂i hK₂iK₂
      hK₁int hK₁iint hK₂int hK₂iint m n hGeq hGieq hν
  rcases Nat.eq_or_lt_of_le hnm with hn1 | hn1
  · exact Or.inr (exists_of_succ q hq φ hφ g O hO' ν c hc0 K₁ K₁i K₂ K₂i hK₁K₁i hK₁iK₁ hK₂K₂i hK₂iK₂
      hK₁int hK₁iint hK₂int hK₂iint m n hGeq hn1)
  · exact Or.inl (normalises_of_eq q hq φ g O hO' ν c hc0 K₁ K₁i K₂ K₂i hK₁K₁i hK₁iK₁ hK₂K₂i hK₂iK₂
      hK₁int hK₁iint hK₂int hK₂iint m n hGeq hGieq (le_antisymm (Nat.lt_succ_iff.mp hn1) hmn))

end Main

end QNLocNF

end

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem solution
    {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (h : GL (Fin 2) (v.adicCompletion ℚ))
    (O : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hO : ∀ x, x ∈ O ↔ ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (ν : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ)
    (hν : ∀ y ∈ O, ((ν⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) *
      (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)) * y) * ν ∈ O) :
    (∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        ((ν⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y * ν ∈ O ↔
          y ∈ O) ∨
      ∃ (s : v.adicCompletion ℚ) (ν₀ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ),
        (ν : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = ν₀ * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) ∧
        (ν₀ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ O ∧
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)) *
          ((ν₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ O ∧
        ((ν₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ O ∧
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)⁻¹) * (ν₀ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ O := by
  obtain rfl : v = QNLocNF.place ℓ hℓ := QNLocNF.eq_place_of_mem ℓ hℓ v hℓv
  exact QNLocNF.main ℓ hℓ φ hφ h O hO ν hν

end S_QuaternionAlgebra_forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem
end P2MW
export P2MW.S_QuaternionAlgebra_forall_conj_mem_iff_or_exists_eq_mul_one_tmul_of_forall_conj_natCast_mul_mem (solution)
