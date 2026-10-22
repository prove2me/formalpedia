-- Prove2me | solution 1 for QuantumWalkSearch.PhaseReflection.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T01:55:19.205347+00:00
-- url     : https://prove2.me/submissions/d72c6c18-9ffd-4270-84c5-c0d3ac0390a4

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_ReflectionCircuit
open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
noncomputable section
namespace QuantumReflectionProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def powerAverage (U : Matrix ι ι ℂ) (s : ℕ) : Matrix ι ι ℂ :=
  ((2 : ℂ) ^ s)⁻¹ • ∑ j : Fin (2 ^ s), U ^ (j : ℕ)

def circuit (U : Matrix ι ι ℂ) (s k : ℕ) :
    Matrix (ι × (Fin k → Fin (2 ^ s))) (ι × (Fin k → Fin (2 ^ s))) ℂ :=
  let V := repeatedPhaseEstimation U s k
  V.conjTranspose * flipNonzero s k * V

end QuantumReflectionProof

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
namespace QuantumReflectionProof

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem unitary_right (U : Matrix ι ι ℂ) (h : Uᴴ * U = 1) : U * Uᴴ = 1 := by
  exact (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr h))

theorem unitary_mul (U V : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (U * V)ᴴ * (U * V) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    Vᴴ * Uᴴ * (U * V) = Vᴴ * (Uᴴ * U) * V := by simp only [mul_assoc]
    _ = 1 := by rw [hU, mul_one, hV]

theorem unitary_pow (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (j : ℕ) :
    (U ^ j)ᴴ * (U ^ j) = 1 := by
  induction j with
  | zero => simp
  | succ j hj => simpa only [pow_succ] using unitary_mul (U ^ j) U hj hU

theorem matrix_inner_adjoint (U : Matrix ι κ ℂ) (x : EuclideanSpace ℂ κ)
    (y : EuclideanSpace ℂ ι) :
    inner ℂ (Matrix.toEuclideanLin U x) y =
      inner ℂ x (Matrix.toEuclideanLin Uᴴ y) := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_inner_right _ _ _).symm

theorem unitary_norm (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1)
    (x : EuclideanSpace ℂ ι) : ‖Matrix.toEuclideanLin U x‖ = ‖x‖ := by
  have hi := matrix_inner_adjoint U x (Matrix.toEuclideanLin U x)
  have hc : Matrix.toEuclideanLin Uᴴ (Matrix.toEuclideanLin U x) = x := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hU]
    simp
  rw [hc] at hi
  have hh : ‖Matrix.toEuclideanLin U x‖^2 = ‖x‖^2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, hi]
  nlinarith [norm_nonneg (Matrix.toEuclideanLin U x), norm_nonneg x]

omit [DecidableEq ι] in
theorem tensorZero_norm [Zero κ] (x : EuclideanSpace ℂ ι) :
    ‖(tensorZero x : EuclideanSpace ℂ (ι × κ))‖ = ‖x‖ := by
  have hs : ‖(tensorZero x : EuclideanSpace ℂ (ι × κ))‖ ^ 2 = ‖x‖ ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, tensorZero, Fintype.sum_prod_type, apply_ite]
  nlinarith [norm_nonneg (tensorZero x : EuclideanSpace ℂ (ι × κ)), norm_nonneg x]

theorem normalization_sq (s : ℕ) :
    ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ s) ^ 2) * (2 : ℂ)^s = 1 := by
  have h : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)^2 * (2 : ℂ) = 1 := by
    have hs : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
      exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [inv_pow, hs]
    norm_num
  calc
    (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ s)^2 * (2 : ℂ)^s =
        ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹)^2 * (2 : ℂ))^s := by ring
    _ = 1 := by rw [h, one_pow]

end QuantumReflectionProof

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
namespace QuantumReflectionProof

def bits (s : ℕ) (j : Fin (2 ^ s)) : Fin s → Bool := fun b => (j : ℕ).testBit b

theorem bits_injective (s : ℕ) : Function.Injective (bits s) := by
  intro j k h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < s
  · exact congrFun h ⟨b, hb⟩
  · have hj : (j : ℕ) < 2 ^ b := lt_of_lt_of_le j.isLt
      (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))
    have hk : (k : ℕ) < 2 ^ b := lt_of_lt_of_le k.isLt
      (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))
    rw [Nat.testBit_eq_false_of_lt hj, Nat.testBit_eq_false_of_lt hk]

def bitsEquiv (s : ℕ) : Fin (2 ^ s) ≃ (Fin s → Bool) :=
  Equiv.ofBijective (bits s) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨bits_injective s, by simp⟩)

def bitSign (a b : Bool) : ℂ := if a && b then -1 else 1

theorem bitSign_star (a b : Bool) : star (bitSign a b) = bitSign a b := by
  cases a <;> cases b <;> norm_num [bitSign]

theorem bitSign_sum (a b : Bool) :
    (∑ z : Bool, bitSign z a * bitSign z b) = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [bitSign, Fintype.sum_bool]

theorem bit_orthogonality (s : ℕ) (j k : Fin s → Bool) :
    (∑ a : Fin s → Bool, (∏ b, bitSign (a b) (j b)) * (∏ b, bitSign (a b) (k b))) =
      if j = k then (2 : ℂ)^s else 0 := by
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun b : Fin s => fun a : Bool => bitSign a (j b) * bitSign a (k b))]
  simp_rw [bitSign_sum]
  by_cases h : j = k
  · subst k
    simp
  · have hn : ∃ b, j b ≠ k b := by
      by_contra! hn
      exact h (funext hn)
    obtain ⟨b, hb⟩ := hn
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)

theorem hadamard_entry (s : ℕ) (j k : Fin (2 ^ s)) :
    hadamardMatrix s j k = ((Real.sqrt 2 : ℂ)⁻¹ ^ s) *
      ∏ b : Fin s, bitSign (bits s j b) (bits s k b) := by
  simp only [hadamardMatrix, bitSign, bits]
  rw [Finset.prod_range]
  rfl

theorem hadamard_unitary (s : ℕ) :
    (hadamardMatrix s)ᴴ * hadamardMatrix s = 1 := by
  have hstar : star (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by simp
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hadamard_entry,
    star_mul, star_pow, star_inv₀, hstar, star_prod, bitSign_star]
  have he : (∑ a : Fin (2 ^ s),
      (∏ b : Fin s, bitSign (bits s a b) (bits s j b)) *
      (∏ b : Fin s, bitSign (bits s a b) (bits s k b))) =
        if j = k then (2 : ℂ)^s else 0 := by
    calc
      _ = ∑ a : Fin s → Bool, (∏ b, bitSign (a b) (bits s j b)) *
          (∏ b, bitSign (a b) (bits s k b)) :=
        (bitsEquiv s).sum_comp _
      _ = _ := by rw [bit_orthogonality]; simp only [(bits_injective s).eq_iff]
  calc
    _ = (((Real.sqrt 2 : ℂ)⁻¹ ^ s)^2) *
      (∑ a : Fin (2 ^ s), (∏ b : Fin s, bitSign (bits s a b) (bits s j b)) *
        (∏ b : Fin s, bitSign (bits s a b) (bits s k b))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by
      rw [he]
      by_cases h : j = k
      · simp only [Matrix.one_apply, h, ite_true]
        exact normalization_sq s
      · simp [h]

theorem hadamard_zero_column (s : ℕ) (j : Fin (2 ^ s)) :
    hadamardMatrix s j 0 = (Real.sqrt 2 : ℂ)⁻¹ ^ s := by
  simp [hadamardMatrix]

end QuantumReflectionProof

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
namespace QuantumReflectionProof

def phaseEquiv (s : ℕ) : Fin (2^s) ≃ ZMod (2^s) := by
  let f : Fin (2^s) → ZMod (2^s) := fun j => (j : ℕ)
  refine Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨?_, by simp⟩)
  intro j k h
  apply Fin.ext
  have hh := congrArg ZMod.val h
  simpa only [f, ZMod.val_natCast, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt] using hh

theorem phaseEquiv_apply (s : ℕ) (j : Fin (2^s)) :
    phaseEquiv s j = (j : ℕ) := rfl

theorem qft_entry (s : ℕ) (j k : Fin (2^s)) :
    qftMatrix s j k = (Real.sqrt 2 : ℂ)⁻¹^s *
      ZMod.stdAddChar ((j : ZMod (2^s)) * (k : ZMod (2^s))) := by
  let : NeZero (2^s) := ⟨by positivity⟩
  simp only [qftMatrix]
  congr 1
  simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    (ZMod.stdAddChar_coe (N := 2^s) ((j : ℕ) * (k : ℕ))).symm

theorem qft_unitary (s : ℕ) : (qftMatrix s)ᴴ * qftMatrix s = 1 := by
  let : NeZero (2^s) := ⟨by positivity⟩
  have hs (j : ZMod (2^s)) : star (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
    change (starRingEnd ℂ) (ZMod.stdAddChar j) = _
    simpa only [AddChar.inv_apply] using AddChar.starComp_apply
      (φ := ZMod.stdAddChar) (by rw [ZMod.ringChar_zmod_n]; positivity) j
  have hstar : star (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by simp
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, qft_entry,
    star_mul, star_pow, star_inv₀, hstar, hs]
  have he : (∑ a : Fin (2^s), ZMod.stdAddChar (-((a : ZMod (2^s)) * (j : ZMod (2^s)))) *
      ZMod.stdAddChar ((a : ZMod (2^s)) * (k : ZMod (2^s)))) =
      if j = k then (2 : ℂ)^s else 0 := by
    simp_rw [← AddChar.map_add_eq_mul]
    have ht (a : Fin (2^s)) : -((a : ZMod (2^s)) * (j : ZMod (2^s))) +
        (a : ZMod (2^s)) * (k : ZMod (2^s)) =
        (a : ZMod (2^s)) * ((k : ZMod (2^s)) - (j : ZMod (2^s))) := by ring
    simp_rw [ht]
    calc
      _ = ∑ a : ZMod (2^s), ZMod.stdAddChar (a * ((k : ZMod (2^s)) - (j : ZMod (2^s)))) :=
        (phaseEquiv s).sum_comp _
      _ = _ := by
        rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (2^s))]
        have hi : ((k : ZMod (2^s)) - (j : ZMod (2^s)) = 0) ↔ j = k := by
          rw [sub_eq_zero]
          change phaseEquiv s k = phaseEquiv s j ↔ j = k
          rw [(phaseEquiv s).injective.eq_iff, eq_comm]
        simp only [hi, ZMod.card]
        split_ifs <;> simp
  calc
    _ = (((Real.sqrt 2 : ℂ)⁻¹ ^ s)^2) *
        (∑ a : Fin (2^s), ZMod.stdAddChar (-((a : ZMod (2^s)) * (j : ZMod (2^s)))) *
          ZMod.stdAddChar ((a : ZMod (2^s)) * (k : ZMod (2^s)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by
      rw [he]
      by_cases h : j = k
      · simp only [Matrix.one_apply, h, ite_true]
        exact normalization_sq s
      · simp [h]

theorem qft_zero_column (s : ℕ) (j : Fin (2^s)) :
    qftMatrix s j 0 = (Real.sqrt 2 : ℂ)⁻¹ ^ s := by simp [qftMatrix]

end QuantumReflectionProof

noncomputable section
open scoped BigOperators ComplexConjugate Kronecker
open Matrix QuantumWalkSearch.PhaseReflection
namespace QuantumReflectionProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem controlled_unitary (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (s : ℕ) :
    (controlledPowers U s)ᴴ * controlledPowers U s = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : a = b
  · subst b
    have hu := congrArg (fun M : Matrix ι ι ℂ => M i j) (unitary_pow U hU (a : ℕ))
    change (∑ x, star ((U ^ (a : ℕ)) x i) * (U ^ (a : ℕ)) x j) =
      (if i = j then 1 else 0) at hu
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, controlledPowers,
      Fintype.sum_prod_type, Matrix.one_apply] using hu
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, controlledPowers,
      Fintype.sum_prod_type, h, Ne.symm h]

theorem phase_unitary (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (s : ℕ) :
    (phaseEstimation U s)ᴴ * phaseEstimation U s = 1 := by
  have hH : hadamardMatrix s ∈ Matrix.unitaryGroup (Fin (2^s)) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr (hadamard_unitary s)
  have hF : (qftMatrix s)ᴴ ∈ Matrix.unitaryGroup (Fin (2^s)) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr (by
      change ((qftMatrix s)ᴴ)ᴴ * (qftMatrix s)ᴴ = 1
      rw [Matrix.conjTranspose_conjTranspose]
      exact unitary_right _ (qft_unitary s))
  have hI : (1 : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ := (Matrix.unitaryGroup ι ℂ).one_mem
  exact unitary_mul _ _ (unitary_mul _ _
    (Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary hI hF))
    (controlled_unitary U hU s))
    (Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary hI hH))

theorem phase_entry (U : Matrix ι ι ℂ) (s : ℕ) (i j : ι) (a b : Fin (2^s)) :
    phaseEstimation U s (i, a) (j, b) =
      ∑ z : Fin (2^s), star (qftMatrix s z a) * (U ^ (z : ℕ)) i j * hadamardMatrix s z b := by
  simp [phaseEstimation, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, controlledPowers, Matrix.one_apply]

theorem phase_zero_block (U : Matrix ι ι ℂ) (s : ℕ) (i j : ι) :
    phaseEstimation U s (i, 0) (j, 0) = powerAverage U s i j := by
  rw [phase_entry]
  have hstar : star (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by simp
  simp only [qft_zero_column, hadamard_zero_column, star_pow, star_inv₀, hstar]
  have hc : ((Real.sqrt 2 : ℂ)⁻¹ ^ s)^2 = ((2 : ℂ)^s)⁻¹ := by
    have hn : (2 : ℂ)^s ≠ 0 := pow_ne_zero s (by norm_num)
    apply mul_right_cancel₀ hn
    rw [normalization_sq, inv_mul_cancel₀ hn]
  calc
    _ = ((Real.sqrt 2 : ℂ)⁻¹ ^ s)^2 * ∑ z : Fin (2^s), (U ^ (z : ℕ)) i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = _ := by
      rw [hc]
      simp only [powerAverage, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]

end QuantumReflectionProof

noncomputable section
open scoped BigOperators ComplexConjugate Kronecker
open Matrix QuantumWalkSearch.PhaseReflection
namespace QuantumReflectionProof

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem unitary_submatrix (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (e : κ ≃ ι) :
    (U.submatrix e e)ᴴ * U.submatrix e e = 1 := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU,
    Matrix.submatrix_one_equiv]

def registerEquiv {s k : ℕ} (r : Fin k) :
    (ι × (Fin k → Fin (2^s))) ≃ ((ι × Fin (2^s)) × ({j : Fin k // j ≠ r} → Fin (2^s))) :=
  (Equiv.prodCongr (Equiv.refl ι) (Equiv.funSplitAt r (Fin (2^s)))).trans
    (Equiv.prodAssoc ι (Fin (2^s)) _).symm

omit [Fintype ι] [DecidableEq ι] in
theorem onRegister_kronecker {s k : ℕ}
    (C : Matrix (ι × Fin (2^s)) (ι × Fin (2^s)) ℂ) (r : Fin k) :
    onRegister C r = (C ⊗ₖ (1 : Matrix ({j : Fin k // j ≠ r} → Fin (2^s))
      ({j : Fin k // j ≠ r} → Fin (2^s)) ℂ)).submatrix (registerEquiv r) (registerEquiv r) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  have hh : (∀ r', r' ≠ r → a r' = b r') ↔
      (fun t : {j : Fin k // j ≠ r} => a t) = (fun t : {j : Fin k // j ≠ r} => b t) := by
    constructor
    · intro h
      funext t
      exact h t t.property
    · intro h t ht
      exact congrFun h ⟨t,ht⟩
  simp [onRegister, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.submatrix,
    registerEquiv, Equiv.funSplitAt, Equiv.piSplitAt, hh, mul_ite]

theorem onRegister_unitary {s k : ℕ}
    (C : Matrix (ι × Fin (2^s)) (ι × Fin (2^s)) ℂ) (hC : Cᴴ * C = 1) (r : Fin k) :
    (onRegister C r)ᴴ * onRegister C r = 1 := by
  rw [onRegister_kronecker]
  apply unitary_submatrix
  exact Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary
    (Matrix.mem_unitaryGroup_iff'.mpr hC) (show (1 : Matrix _ _ ℂ) ∈ Matrix.unitaryGroup _ ℂ from (Matrix.unitaryGroup _ ℂ).one_mem))

theorem list_prod_unitary (l : List (Matrix ι ι ℂ))
    (h : ∀ U ∈ l, Uᴴ * U = 1) : l.prodᴴ * l.prod = 1 := by
  induction l with
  | nil => simp
  | cons U l ih =>
    simp only [List.prod_cons]
    exact unitary_mul _ _ (h U (by simp)) (ih (fun V hV => h V (by simp [hV])))

theorem repeated_unitary (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (s k : ℕ) :
    (repeatedPhaseEstimation U s k)ᴴ * repeatedPhaseEstimation U s k = 1 := by
  apply list_prod_unitary
  intro V hV
  simp only [List.mem_reverse, List.mem_map] at hV
  obtain ⟨r, _, rfl⟩ := hV
  exact onRegister_unitary _ (phase_unitary U hU s) r

end QuantumReflectionProof

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
namespace QuantumReflectionProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def registerProduct {s k : ℕ}
    (C : Matrix (ι × Fin (2^s)) (ι × Fin (2^s)) ℂ) (l : List (Fin k)) :
    Matrix (ι × (Fin k → Fin (2^s))) (ι × (Fin k → Fin (2^s))) ℂ :=
  (l.map (onRegister C)).reverse.prod

def phaseBlock {s : ℕ}
    (C : Matrix (ι × Fin (2^s)) (ι × Fin (2^s)) ℂ) (a b : Fin (2^s)) : Matrix ι ι ℂ :=
  fun i j => C (i,a) (j,b)

theorem registerProduct_entry {s k : ℕ}
    (C : Matrix (ι × Fin (2^s)) (ι × Fin (2^s)) ℂ)
    (l : List (Fin k)) (hl : l.Nodup) (i j : ι) (b a : Fin k → Fin (2^s)) :
    registerProduct C l (i,b) (j,a) =
      if ∀ r, r ∉ l → b r = a r then
        ((l.map (fun r => phaseBlock C (b r) (a r))).reverse.prod) i j else 0 := by
  induction l generalizing i j b a with
  | nil =>
    have hh : (∀ r, b r = a r) ↔ b = a := funext_iff.symm
    by_cases hi : i = j <;> by_cases hb : b = a <;>
      simp [registerProduct, hh, Prod.ext_iff, hi, hb]
  | cons r l ih =>
    obtain ⟨hr, hl⟩ := List.nodup_cons.mp hl
    let c0 := Function.update a r (b r)
    have hiff (c : Fin k → Fin (2^s)) :
        ((∀ t, t ∉ l → b t = c t) ∧ (∀ t, t ≠ r → c t = a t)) ↔
        (c = c0 ∧ ∀ t, t ∉ r :: l → b t = a t) := by
      constructor
      · rintro ⟨h₁,h₂⟩
        constructor
        · funext t
          by_cases ht : t = r
          · subst t
            simpa [c0] using (h₁ r hr).symm
          · simpa [c0, ht] using h₂ t ht
        · intro t ht
          have htr : t ≠ r := fun he => ht (by simp [he])
          have htl : t ∉ l := fun he => ht (by simp [he])
          exact (h₁ t htl).trans (h₂ t htr)
      · rintro ⟨rfl,h⟩
        constructor
        · intro t ht
          by_cases htr : t = r
          · subst t
            simp [c0]
          · simpa [c0, htr] using h t (by simp [htr, ht])
        · intro t ht
          simp [c0, ht]
    have hm : l.map (fun t => phaseBlock C (b t) (c0 t)) =
        l.map (fun t => phaseBlock C (b t) (a t)) := by
      apply List.map_congr_left
      intro t ht
      have htr : t ≠ r := fun he => hr (he ▸ ht)
      simp [c0, htr]
    have hp (x : ι) (c : Fin k → Fin (2^s)) :
        registerProduct C l (i,b) (x,c) * onRegister C r (x,c) (j,a) =
          if c = c0 then
            if ∀ t, t ∉ r :: l → b t = a t then
              ((l.map (fun t => phaseBlock C (b t) (a t))).reverse.prod) i x *
                C (x,b r) (j,a r) else 0 else 0 := by
      rw [ih hl i x b c]
      unfold onRegister
      by_cases h₁ : ∀ t, t ∉ l → b t = c t
      · by_cases h₂ : ∀ t, t ≠ r → c t = a t
        · obtain ⟨hc,ho⟩ := (hiff c).mp ⟨h₁,h₂⟩
          subst c
          rw [if_pos h₁, if_pos h₂, if_pos rfl, if_pos ho, hm]
          simp [c0]
        · rw [if_neg h₂, mul_zero]
          by_cases hc : c = c0
          · rw [if_pos hc, if_neg (show ¬ (∀ t, t ∉ r :: l → b t = a t) from
              fun h => h₂ ((hiff c).mpr ⟨hc,h⟩).2)]
          · rw [if_neg hc]
      · rw [if_neg h₁, zero_mul]
        by_cases hc : c = c0
        · rw [if_pos hc, if_neg (show ¬ (∀ t, t ∉ r :: l → b t = a t) from
            fun h => h₁ ((hiff c).mpr ⟨hc,h⟩).1)]
        · rw [if_neg hc]
    simp only [registerProduct, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
    change (registerProduct C l * onRegister C r) (i,b) (j,a) = _
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp_rw [hp]
    simp [Matrix.mul_apply, phaseBlock]

end QuantumReflectionProof

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
namespace QuantumReflectionProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem repeated_zero_block (U : Matrix ι ι ℂ) (s k : ℕ) (i j : ι) :
    repeatedPhaseEstimation U s k (i,0) (j,0) = ((powerAverage U s)^k) i j := by
  have hb : phaseBlock (phaseEstimation U s) 0 0 = powerAverage U s := by
    ext a b
    exact phase_zero_block U s a b
  have hh := registerProduct_entry (phaseEstimation U s) (List.finRange k)
    (List.nodup_finRange k) i j 0 0
  simpa [registerProduct, repeatedPhaseEstimation, hb] using hh

theorem zero_projection_apply (s k : ℕ)
    (z : EuclideanSpace ℂ (ι × (Fin k → Fin (2^s)))) (p : ι × (Fin k → Fin (2^s))) :
    Matrix.toEuclideanLin (zeroAncillaProj s k) z p = if p.2 = 0 then z p else 0 := by
  change (∑ q, zeroAncillaProj s k p q * z q) = _
  simp [zeroAncillaProj, Matrix.diagonal_apply, ite_mul]

theorem repeated_zero_projection (U : Matrix ι ι ℂ) (s k : ℕ) (ψ : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (zeroAncillaProj s k)
      (Matrix.toEuclideanLin (repeatedPhaseEstimation U s k) (tensorZero ψ)) =
      tensorZero (Matrix.toEuclideanLin ((powerAverage U s)^k) ψ) := by
  ext ⟨i,b⟩
  rw [zero_projection_apply]
  by_cases hb : b = 0
  · subst b
    simp only [ite_true]
    change (∑ q, repeatedPhaseEstimation U s k (i,0) q *
      (if q.2 = 0 then ψ q.1 else 0)) =
      (if (0 : Fin k → Fin (2^s)) = 0 then
        (Matrix.toEuclideanLin ((powerAverage U s)^k) ψ) i else 0)
    rw [if_pos rfl]
    change (∑ q, repeatedPhaseEstimation U s k (i,0) q *
      (if q.2 = 0 then ψ q.1 else 0)) = ∑ j, ((powerAverage U s)^k) i j * ψ j
    simp [Fintype.sum_prod_type, mul_ite, repeated_zero_block]
  · simp [hb, tensorZero]

theorem zero_projection_pythagoras (s k : ℕ)
    (z : EuclideanSpace ℂ (ι × (Fin k → Fin (2^s)))) :
    ‖z‖^2 = ‖Matrix.toEuclideanLin (zeroAncillaProj s k) z‖^2 +
      ‖z - Matrix.toEuclideanLin (zeroAncillaProj s k) z‖^2 := by
  simp only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply, zero_projection_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p.2 = 0 <;> simp [h]

theorem zero_projection_eq_of_norm (s k : ℕ)
    (z : EuclideanSpace ℂ (ι × (Fin k → Fin (2^s))))
    (h : ‖Matrix.toEuclideanLin (zeroAncillaProj s k) z‖ = ‖z‖) :
    Matrix.toEuclideanLin (zeroAncillaProj s k) z = z := by
  have hp := zero_projection_pythagoras s k z
  rw [h] at hp
  have hn : ‖z - Matrix.toEuclideanLin (zeroAncillaProj s k) z‖ = 0 := by nlinarith [norm_nonneg (z - Matrix.toEuclideanLin (zeroAncillaProj s k) z)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

end QuantumReflectionProof

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
namespace QuantumReflectionProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem flip_add_one (s k : ℕ) :
    (flipNonzero s k : Matrix (ι × (Fin k → Fin (2^s))) _ ℂ) + 1 =
      (2 : ℂ) • zeroAncillaProj s k := by
  ext p q
  by_cases hpq : p = q
  · subst q
    by_cases h : p.2 = 0 <;>
      norm_num [flipNonzero, zeroAncillaProj, h]
  · simp [flipNonzero, zeroAncillaProj, hpq]

theorem powerAverage_fixed (U : Matrix ι ι ℂ) (s : ℕ) (ψ : EuclideanSpace ℂ ι)
    (hψ : Matrix.toEuclideanLin U ψ = ψ) :
    Matrix.toEuclideanLin (powerAverage U s) ψ = ψ := by
  have hp (j : ℕ) : Matrix.toEuclideanLin (U^j) ψ = ψ := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Matrix.toLpLin_mul_same, LinearMap.comp_apply, ih, hψ]
  simp only [powerAverage, map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, hp]
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ (2^s) ψ]
  simp only [Nat.cast_pow, Nat.cast_ofNat, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero s (by norm_num : (2 : ℂ) ≠ 0)), one_smul]

theorem powerAverage_pow_fixed (U : Matrix ι ι ℂ) (s k : ℕ) (ψ : EuclideanSpace ℂ ι)
    (hψ : Matrix.toEuclideanLin U ψ = ψ) :
    Matrix.toEuclideanLin ((powerAverage U s)^k) ψ = ψ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.toLpLin_mul_same, LinearMap.comp_apply, ih]
    exact powerAverage_fixed U s ψ hψ

theorem circuit_error (U : Matrix ι ι ℂ) (hUleft : Uᴴ * U = 1)
    (_hUright : U * Uᴴ = 1) (s k : ℕ) (ψ : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanLin (circuit U s k + 1) (tensorZero ψ)‖ =
      2 * ‖Matrix.toEuclideanLin ((powerAverage U s)^k) ψ‖ := by
  clear _hUright
  let V := repeatedPhaseEstimation U s k
  have hV : Vᴴ * V = 1 := repeated_unitary U hUleft s k
  have hV' : (Vᴴ)ᴴ * Vᴴ = 1 := by simpa using unitary_right V hV
  have heq : circuit U s k + 1 = Vᴴ * (flipNonzero s k + 1) * V := by
    simp [circuit, V, mul_add, add_mul, Matrix.mul_assoc, repeated_unitary U hUleft s k]
  rw [heq, flip_add_one, Matrix.mul_smul, Matrix.smul_mul]
  rw [map_smul, LinearMap.smul_apply, norm_smul]
  norm_num only [Complex.norm_ofNat]
  congr 1
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply, unitary_norm Vᴴ hV']
  rw [show Matrix.toEuclideanLin (zeroAncillaProj s k)
    (Matrix.toEuclideanLin V (tensorZero ψ)) =
      tensorZero (Matrix.toEuclideanLin ((powerAverage U s)^k) ψ) from
        repeated_zero_projection U s k ψ, tensorZero_norm]

theorem circuit_fixed (U : Matrix ι ι ℂ) (hUleft : Uᴴ * U = 1)
    (_hUright : U * Uᴴ = 1) (s k : ℕ) (ψ : EuclideanSpace ℂ ι)
    (hψ : Matrix.toEuclideanLin U ψ = ψ) :
    Matrix.toEuclideanLin (circuit U s k) (tensorZero ψ) = tensorZero ψ := by
  clear _hUright
  let V := repeatedPhaseEstimation U s k
  have hV : Vᴴ * V = 1 := repeated_unitary U hUleft s k
  have hp : Matrix.toEuclideanLin (zeroAncillaProj s k)
      (Matrix.toEuclideanLin V (tensorZero ψ)) = tensorZero ψ := by
    rw [show Matrix.toEuclideanLin (zeroAncillaProj s k)
      (Matrix.toEuclideanLin V (tensorZero ψ)) =
      tensorZero (Matrix.toEuclideanLin ((powerAverage U s)^k) ψ) from
        repeated_zero_projection U s k ψ, powerAverage_pow_fixed U s k ψ hψ]
  have hn : ‖Matrix.toEuclideanLin (zeroAncillaProj s k)
      (Matrix.toEuclideanLin V (tensorZero ψ))‖ = ‖Matrix.toEuclideanLin V (tensorZero ψ)‖ := by
    rw [hp, unitary_norm V hV]
  have hz : Matrix.toEuclideanLin V (tensorZero ψ) = tensorZero ψ :=
    (zero_projection_eq_of_norm s k _ hn).symm.trans hp
  have hb : Matrix.toEuclideanLin Vᴴ (tensorZero ψ) = tensorZero ψ := by
    have hh := congrArg (Matrix.toEuclideanLin Vᴴ) hz
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hV] at hh
    simpa using hh.symm
  have hf : Matrix.toEuclideanLin (flipNonzero s k) (tensorZero ψ) =
      (tensorZero ψ : EuclideanSpace ℂ (ι × (Fin k → Fin (2^s)))) := by
    ext p
    change (Matrix.diagonal (fun q : ι × (Fin k → Fin (2^s)) =>
      if q.2 = 0 then (1 : ℂ) else -1)).mulVec (tensorZero ψ).ofLp p = _
    rw [Matrix.mulVec_diagonal]
    by_cases h : p.2 = 0 <;> simp [tensorZero, h]
  change Matrix.toEuclideanLin (Vᴴ * flipNonzero s k * V) (tensorZero ψ) = _
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, hz,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply, hf, hb]

end QuantumReflectionProof

open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
noncomputable section
namespace QuantumReflectionProof
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
lemma reverse_eq {P : Matrix X X ℝ} {πd : X → ℝ}
    (hπ : IsStationaryDist P πd) (hr : IsReversible P πd) :
    timeReversal P πd = P := by
  ext y x
  dsimp [timeReversal]
  rw [hr x y, mul_div_cancel_left₀ _ (ne_of_gt (hπ.pos y))]

omit [DecidableEq X] in
lemma discriminant_symmetric {P : Matrix X X ℝ} {πd : X → ℝ}
    (hπ : IsStationaryDist P πd) (hr : IsReversible P πd) :
    (discriminant P πd).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial]
  simp [discriminant, reverse_eq hπ hr, mul_comm]

lemma discriminant_entry {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (x y : X) :
    discriminant P πd x y = Real.sqrt (πd x) * P x y / Real.sqrt (πd y) := by
  have hpx := Matrix.nonneg_of_mem_rowStochastic hp (i := x) (j := y)
  dsimp only [discriminant, timeReversal]
  rw [show P x y * (πd x * P x y / πd y) = πd x * (P x y) ^ 2 / πd y by ring]
  rw [Real.sqrt_div (mul_nonneg (le_of_lt (hπ.pos x)) (sq_nonneg _)),
    Real.sqrt_mul (le_of_lt (hπ.pos x)), Real.sqrt_sq_eq_abs, abs_of_nonneg hpx]

lemma discriminant_mul_mass {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) :
    discriminant P πd *ᵥ (fun x => Real.sqrt (πd x)) = fun x => Real.sqrt (πd x) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, discriminant_entry hp hπ]
  simp_rw [div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr (hπ.pos _)))]
  rw [← Finset.mul_sum, Matrix.sum_row_of_mem_rowStochastic hp, mul_one]

lemma stochastic_eigen_abs_le {P : Matrix X X ℝ} (hp : P ∈ Matrix.rowStochastic ℝ X)
    {f : X → ℝ} (hf : f ≠ 0) {d : ℝ} (he : P *ᵥ f = d • f) : |d| ≤ 1 := by
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by simpa [funext_iff] using hf
  let : Nonempty X := ⟨j⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun x => |f x|) Finset.univ_nonempty
  have hm : 0 < |f i| := lt_of_lt_of_le (abs_pos.mpr hj) (hi j (Finset.mem_univ _))
  have hb : |d| * |f i| ≤ |f i| := calc
    _ = |∑ j, P i j * f j| := by
      rw [← abs_mul]
      exact congrArg abs (congrFun he i).symm
    _ ≤ ∑ j, |P i j * f j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, P i j * |f j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hp)]
    _ ≤ ∑ j, P i j * |f i| := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (Matrix.nonneg_of_mem_rowStochastic hp)
    _ = |f i| := by rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hp, one_mul]
  nlinarith

lemma stochastic_eigen_pow {P : Matrix X X ℝ} {f : X → ℝ} {d : ℝ}
    (he : P *ᵥ f = d • f) (q : ℕ) : P ^ q *ᵥ f = d ^ q • f := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, he, smul_smul, pow_succ]

lemma stochastic_peripheral {P : Matrix X X ℝ} (hp : P ∈ Matrix.rowStochastic ℝ X)
    (hprim : P.IsPrimitive) {f : X → ℝ} (hf : f ≠ 0) {d : ℝ}
    (he : P *ᵥ f = d • f) (hd : |d| = 1) : d = 1 ∧ ∃ c : ℝ, f = fun _ => c := by
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by simpa [funext_iff] using hf
  let : Nonempty X := ⟨j⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun x => |f x|) Finset.univ_nonempty
  obtain ⟨q, _, hq⟩ := hprim.exists_pos_pow
  have hpq : P ^ q ∈ Matrix.rowStochastic ℝ X := (Matrix.rowStochastic ℝ X).pow_mem hp q
  have heq := congrFun (stochastic_eigen_pow he q) i
  have hab : |d ^ q * f i| = |f i| := by rw [abs_mul, abs_pow, hd, one_pow, one_mul]
  have hlo (x : X) : -|f i| ≤ f x := le_trans (neg_le_neg (hi x (Finset.mem_univ _))) (neg_abs_le _)
  have hhi (x : X) : f x ≤ |f i| := le_trans (le_abs_self _) (hi x (Finset.mem_univ _))
  have hc : ∃ c : ℝ, f = fun _ => c := by
    rcases le_total 0 (d ^ q * f i) with hg | hg
    · rw [abs_of_nonneg hg] at hab
      have hz : ∑ x, (P ^ q) i x * (|f i| - f x) = 0 := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hpq]
        change 1 * |f i| - (P ^ q *ᵥ f) i = 0
        rw [heq]
        simpa using sub_eq_zero.mpr hab.symm
      refine ⟨|f i|, funext fun x => ?_⟩
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
        mul_nonneg (le_of_lt (hq i x)) (sub_nonneg.mpr (hhi x)))).mp hz x (Finset.mem_univ _)
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt (hq i x)))).symm
    · rw [abs_of_nonpos hg] at hab
      have hz : ∑ x, (P ^ q) i x * (|f i| + f x) = 0 := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hpq]
        change 1 * |f i| + (P ^ q *ᵥ f) i = 0
        rw [heq]
        dsimp only [Pi.smul_apply, smul_eq_mul]
        linarith
      refine ⟨-|f i|, funext fun x => ?_⟩
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
        mul_nonneg (le_of_lt (hq i x)) (by linarith [hlo x]))).mp hz x (Finset.mem_univ _)
      have hh' := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hq i x))
      linarith
  obtain ⟨c, hc⟩ := hc
  refine ⟨?_, c, hc⟩
  have hc0 : c ≠ 0 := by simpa [hc] using hj
  have hh := congrFun he j
  simp only [hc, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hh
  rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hp] at hh
  exact (mul_eq_left₀ hc0).mp (by simpa [mul_comm] using hh.symm)

end QuantumReflectionProof

open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
noncomputable section
namespace QuantumReflectionProof
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
lemma rescaled_nonzero {P : Matrix X X ℝ} {πd : X → ℝ}
    (hπ : IsStationaryDist P πd) {u : X → ℝ} (hu : u ≠ 0) :
    (fun x => u x / Real.sqrt (πd x)) ≠ 0 := by
  intro h
  apply hu
  funext x
  have hx := congrFun h x
  exact (div_eq_zero_iff).mp hx |>.resolve_right (ne_of_gt (Real.sqrt_pos.mpr (hπ.pos x)))

lemma rescaled_eigen {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd)
    {u : X → ℝ} {d : ℝ} (he : discriminant P πd *ᵥ u = d • u) :
    P *ᵥ (fun x => u x / Real.sqrt (πd x)) = d • (fun x => u x / Real.sqrt (πd x)) := by
  funext x
  have hs (y : X) : P x y * (u y / Real.sqrt (πd y)) =
      (discriminant P πd x y * u y) / Real.sqrt (πd x) := by
    rw [discriminant_entry hp hπ]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hπ.pos x)), ne_of_gt (Real.sqrt_pos.mpr (hπ.pos y))]
  simp only [Matrix.mulVec, dotProduct, hs, ← Finset.sum_div, Pi.smul_apply, smul_eq_mul]
  change (discriminant P πd *ᵥ u) x / Real.sqrt (πd x) = _
  rw [he]
  dsimp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma discriminant_eigen_abs_le {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd)
    {u : X → ℝ} (hu : u ≠ 0) {d : ℝ} (he : discriminant P πd *ᵥ u = d • u) : |d| ≤ 1 :=
  stochastic_eigen_abs_le hp (rescaled_nonzero hπ hu) (rescaled_eigen hp hπ he)

lemma discriminant_peripheral {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hprim : P.IsPrimitive)
    {u : X → ℝ} (hu : u ≠ 0) {d : ℝ} (he : discriminant P πd *ᵥ u = d • u) (hd : |d| = 1) :
    d = 1 ∧ ∃ c : ℝ, u = fun x => c * Real.sqrt (πd x) := by
  obtain ⟨hd1, c, hc⟩ := stochastic_peripheral hp hprim (rescaled_nonzero hπ hu)
    (rescaled_eigen hp hπ he) hd
  refine ⟨hd1, c, funext fun x => ?_⟩
  exact (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (hπ.pos x)))).mp (congrFun hc x)

lemma eigen_abs_singular {P : Matrix X X ℝ} {πd : X → ℝ}
    (hπ : IsStationaryDist P πd) (hr : IsReversible P πd)
    {u : EuclideanSpace ℝ X} (hu : u ≠ 0) {d : ℝ}
    (he : Matrix.toEuclideanLin (discriminant P πd) u = d • u) : IsSingularValue P πd |d| := by
  let T := Matrix.toEuclideanLin (discriminant P πd)
  have hs : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (discriminant_symmetric hπ hr)
  have ha : T.adjoint = T := hs.adjoint_eq
  have hev : Module.End.HasEigenvector (T.adjoint ∘ₗ T) (d ^ 2) u := by
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      simp only [LinearMap.comp_apply, ha]
      change T (T u) = _
      rw [he, map_smul, he, smul_smul, ← sq]
    · exact hu
  obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq
    finrank_euclideanSpace (Module.End.hasEigenvalue_of_hasEigenvector hev)
  change T.isSymmetric_adjoint_comp_self.eigenvalues finrank_euclideanSpace i = d ^ 2 at hi
  refine ⟨i, i.isLt, ?_⟩
  change T.singularValues i = |d|
  rw [T.singularValues_fin finrank_euclideanSpace i, hi, Real.sqrt_sq_eq_abs]

end QuantumReflectionProof

open scoped BigOperators
open Matrix QuantumWalkSearch.PhaseReflection
noncomputable section
namespace QuantumReflectionProof
variable {X : Type*} [Fintype X] [DecidableEq X]

def angleSet (P : Matrix X X ℝ) (πd : X → ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Ioo 0 (Real.pi / 2) ∧ IsSingularValue P πd (Real.cos θ)}

lemma angleSet_finite (P : Matrix X X ℝ) (πd : X → ℝ) : (angleSet P πd).Finite := by
  apply (Set.finite_range (fun i : Fin (Fintype.card X) =>
    Real.arccos ((Matrix.toEuclideanLin (discriminant P πd)).singularValues i))).subset
  rintro θ ⟨hθ, i, hi, he⟩
  refine ⟨⟨i, hi⟩, ?_⟩
  change Real.arccos ((Matrix.toEuclideanLin (discriminant P πd)).singularValues i) = θ
  rw [he, Real.arccos_cos (le_of_lt hθ.1) (by linarith [hθ.2, Real.pi_pos])]

lemma phaseGap_pos_le (P : Matrix X X ℝ) (πd : X → ℝ) :
    0 < phaseGap P πd ∧ phaseGap P πd ≤ Real.pi := by
  classical
  change 0 < (if (angleSet P πd).Nonempty then 2 * sInf (angleSet P πd) else Real.pi) ∧
    (if (angleSet P πd).Nonempty then 2 * sInf (angleSet P πd) else Real.pi) ≤ Real.pi
  by_cases h : (angleSet P πd).Nonempty
  · have hm := h.csInf_mem (angleSet_finite P πd)
    change sInf (angleSet P πd) ∈ Set.Ioo 0 (Real.pi / 2) ∧ _ at hm
    rw [if_pos h]
    constructor <;> linarith [hm.1.1, hm.1.2]
  · simp only [h, ↓reduceIte]
    exact ⟨Real.pi_pos, le_rfl⟩

lemma phaseGap_le_angle {P : Matrix X X ℝ} {πd : X → ℝ} {θ : ℝ}
    (hθ : θ ∈ angleSet P πd) : phaseGap P πd ≤ 2 * θ := by
  classical
  have hn : (angleSet P πd).Nonempty := ⟨θ, hθ⟩
  change (if (angleSet P πd).Nonempty then _ else _) ≤ _
  rw [if_pos hn]
  exact mul_le_mul_of_nonneg_left (csInf_le (angleSet_finite P πd).bddBelow hθ) (by norm_num)

lemma phase_sin_bound {P : Matrix X X ℝ} {πd : X → ℝ} {d : ℝ}
    (hd : |d| ≤ 1) (hs : IsSingularValue P πd |d|) (hlt : |d| < 1) :
    phaseGap P πd / Real.pi ≤ Real.sqrt (1 - d ^ 2) := by
  by_cases hz : d = 0
  · subst d
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_one]
    exact (div_le_one Real.pi_pos).mpr (phaseGap_pos_le P πd).2
  have hab : 0 < |d| := abs_pos.mpr hz
  have ht0 : 0 < Real.arccos |d| := Real.arccos_pos.mpr hlt
  have htpi : Real.arccos |d| < Real.pi / 2 := by
    rw [← Real.arccos_zero]
    exact Real.strictAntiOn_arccos (by constructor <;> linarith) (by constructor <;> linarith) hab
  have hc : Real.cos (Real.arccos |d|) = |d| := Real.cos_arccos (by linarith) hd
  have hθ : Real.arccos |d| ∈ angleSet P πd := ⟨⟨ht0, htpi⟩, by simpa only [hc] using hs⟩
  have hg := phaseGap_le_angle hθ
  have hj := Real.mul_le_sin (le_of_lt ht0) (le_of_lt htpi)
  have hsin : Real.sin (Real.arccos |d|) = Real.sqrt (1 - d ^ 2) := by
    rw [Real.sin_arccos, sq_abs]
  rw [hsin] at hj
  apply (div_le_iff₀ Real.pi_pos).mpr
  have : 2 * Real.arccos |d| ≤ Real.sqrt (1 - d ^ 2) * Real.pi := by
    apply (div_le_iff₀ Real.pi_pos).mp
    simpa only [div_mul_eq_mul_div] using hj
  linarith

lemma precision_bound (Δ : ℝ) (hΔ : 0 < Δ) :
    2 * Real.pi / Δ ≤ (2 : ℝ) ^ precision Δ := by
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (div_pos (mul_pos (by norm_num) Real.pi_pos) hΔ)).mp (Nat.le_ceil (Real.logb 2 (2 * Real.pi / Δ)))
  simpa only [Real.rpow_natCast, precision] using h

end QuantumReflectionProof

open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
noncomputable section
namespace QuantumReflectionProof
variable {X : Type*} [Fintype X] [DecidableEq X]

def cvec (u : X → ℝ) : EuclideanSpace ℂ X := WithLp.toLp 2 fun x => (u x : ℂ)
def cDiscriminant (P : Matrix X X ℝ) (πd : X → ℝ) : Matrix X X ℂ :=
  (discriminant P πd).map (fun r => (r : ℂ))
def aMap (P : Matrix X X ℝ) := Matrix.toEuclideanLin (embedAMatrix P)
def bMap (P : Matrix X X ℝ) (πd : X → ℝ) := Matrix.toEuclideanLin (embedBMatrix P πd)

lemma embedA_gram {P : Matrix X X ℝ} (hp : P ∈ Matrix.rowStochastic ℝ X) :
    (embedAMatrix P)ᴴ * embedAMatrix P = 1 := by
  have hs (x y : X) : (Real.sqrt (P x y) : ℂ) * (Real.sqrt (P x y) : ℂ) = (P x y : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Matrix.nonneg_of_mem_rowStochastic hp (i := x) (j := y))
  ext x y
  by_cases h : x = y
  · subst y
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedAMatrix, Fintype.sum_prod_type,
      hs, ← Complex.ofReal_sum, Matrix.sum_row_of_mem_rowStochastic hp]
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedAMatrix, Fintype.sum_prod_type, h, Ne.symm h]

lemma embedB_gram {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd) :
    (embedBMatrix P πd)ᴴ * embedBMatrix P πd = 1 := by
  have hs (x y : X) : (Real.sqrt (P x y) : ℂ) * (Real.sqrt (P x y) : ℂ) = (P x y : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Matrix.nonneg_of_mem_rowStochastic hp (i := x) (j := y))
  ext x y
  by_cases h : x = y
  · subst y
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedBMatrix, Fintype.sum_prod_type,
      reverse_eq hπ hr, hs, ← Complex.ofReal_sum, Matrix.sum_row_of_mem_rowStochastic hp]
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedBMatrix, Fintype.sum_prod_type, h, Ne.symm h]

lemma embed_cross {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) :
    (embedAMatrix P)ᴴ * embedBMatrix P πd = cDiscriminant P πd := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, embedAMatrix, embedBMatrix,
    Fintype.sum_prod_type, cDiscriminant, Matrix.map_apply, discriminant]
  simp [apply_ite, Real.sqrt_mul (Matrix.nonneg_of_mem_rowStochastic hp)]

omit [DecidableEq X] in

lemma cDiscriminant_hermitian {P : Matrix X X ℝ} {πd : X → ℝ}
    (hπ : IsStationaryDist P πd) (hr : IsReversible P πd) :
    (cDiscriminant P πd)ᴴ = cDiscriminant P πd := by
  ext x y
  have h := congrFun (congrFun (discriminant_symmetric hπ hr) x) y
  simpa [cDiscriminant, Matrix.conjTranspose_apply] using congrArg Complex.ofReal h

lemma embed_cross_reverse {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd) :
    (embedBMatrix P πd)ᴴ * embedAMatrix P = cDiscriminant P πd := by
  have h := congrArg Matrix.conjTranspose (embed_cross (πd := πd) hp)
  simpa [Matrix.conjTranspose_mul, cDiscriminant_hermitian hπ hr] using h

lemma aMap_apply (P : Matrix X X ℝ) (u : EuclideanSpace ℂ X) :
    aMap P u = ∑ x, u x • vecA P x := by
  ext q
  simp [aMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, embedAMatrix, vecA, mul_comm]

lemma bMap_apply (P : Matrix X X ℝ) (πd : X → ℝ) (u : EuclideanSpace ℂ X) :
    bMap P πd u = ∑ x, u x • vecB P πd x := by
  ext q
  simp [bMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, embedBMatrix, vecB, mul_comm]

lemma range_aMap (P : Matrix X X ℝ) : LinearMap.range (aMap P) = spaceA P := by
  ext z
  simp only [LinearMap.mem_range, spaceA, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨fun x => u x, (aMap_apply P u).symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨WithLp.toLp 2 u, (aMap_apply P _).trans hu⟩

lemma range_bMap (P : Matrix X X ℝ) (πd : X → ℝ) : LinearMap.range (bMap P πd) = spaceB P πd := by
  ext z
  simp only [LinearMap.mem_range, spaceB, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨fun x => u x, (bMap_apply P πd u).symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨WithLp.toLp 2 u, (bMap_apply P πd _).trans hu⟩

lemma rectangular_inner {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : Matrix ι κ ℂ) (hT : Tᴴ * T = 1) (u v : EuclideanSpace ℂ κ) :
    inner ℂ (Matrix.toEuclideanLin T u) (Matrix.toEuclideanLin T v) = inner ℂ u v := by
  rw [matrix_inner_adjoint, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hT]
  simp

lemma rectangular_projection {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : Matrix ι κ ℂ) (hT : Tᴴ * T = 1) (v : EuclideanSpace ℂ ι) :
    (LinearMap.range (Matrix.toEuclideanLin T)).starProjection v =
      Matrix.toEuclideanLin T (Matrix.toEuclideanLin Tᴴ v) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨_, rfl⟩
  · rintro w ⟨z, rfl⟩
    rw [← LinearMap.adjoint_inner_left, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      map_sub, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hT]
    simp

lemma projection_a (P : Matrix X X ℝ) (hp : P ∈ Matrix.rowStochastic ℝ X) (v : H X) :
    (spaceA P).starProjection v = aMap P (Matrix.toEuclideanLin (embedAMatrix P)ᴴ v) := by
  rw [← range_aMap]
  exact rectangular_projection _ (embedA_gram hp) v

lemma projection_b (P : Matrix X X ℝ) (πd : X → ℝ)
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd) (v : H X) :
    (spaceB P πd).starProjection v = bMap P πd (Matrix.toEuclideanLin (embedBMatrix P πd)ᴴ v) := by
  rw [← range_bMap]
  exact rectangular_projection _ (embedB_gram hp hπ hr) v

lemma aMap_inner {P : Matrix X X ℝ} (hp : P ∈ Matrix.rowStochastic ℝ X) (u v : EuclideanSpace ℂ X) :
    inner ℂ (aMap P u) (aMap P v) = inner ℂ u v := rectangular_inner _ (embedA_gram hp) u v

lemma bMap_inner {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd)
    (u v : EuclideanSpace ℂ X) :
    inner ℂ (bMap P πd u) (bMap P πd v) = inner ℂ u v := rectangular_inner _ (embedB_gram hp hπ hr) u v

lemma aMap_bMap_inner {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (u v : EuclideanSpace ℂ X) :
    inner ℂ (aMap P u) (bMap P πd v) = inner ℂ u (Matrix.toEuclideanLin (cDiscriminant P πd) v) := by
  change inner ℂ (Matrix.toEuclideanLin _ u) (Matrix.toEuclideanLin _ v) = _
  rw [matrix_inner_adjoint, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, embed_cross hp]

lemma pi_aMap (P : Matrix X X ℝ) (πd : X → ℝ) :
    piState P πd = aMap P (cvec fun x => Real.sqrt (πd x)) := by
  rw [aMap_apply]
  rfl

lemma pi_bMap {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) :
    piState P πd = bMap P πd (cvec fun x => Real.sqrt (πd x)) := by
  rw [pi_aMap, aMap_apply, bMap_apply]
  ext q
  simp [vecA, vecB, cvec]
  have hx := hπ.pos q.1
  have hy := hπ.pos q.2
  have hpx := Matrix.nonneg_of_mem_rowStochastic hp (i := q.1) (j := q.2)
  norm_cast
  rw [← Real.sqrt_mul (le_of_lt hx), ← Real.sqrt_mul (le_of_lt hy)]
  congr 1
  dsimp [timeReversal]
  field_simp

lemma walk_pi {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) :
    walk P πd (piState P πd) = piState P πd := by
  have ha : piState P πd ∈ spaceA P := by rw [pi_aMap, ← range_aMap]; exact ⟨_, rfl⟩
  have hb : piState P πd ∈ spaceB P πd := by rw [pi_bMap hp hπ, ← range_bMap]; exact ⟨_, rfl⟩
  simp [walk, Submodule.reflection_mem_subspace_eq_self ha, Submodule.reflection_mem_subspace_eq_self hb]

end QuantumReflectionProof

open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
noncomputable section
namespace QuantumReflectionProof
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
lemma cvec_inner (u v : EuclideanSpace ℝ X) :
    inner ℂ (cvec u) (cvec v) = ((inner ℝ u v : ℝ) : ℂ) := by
  simp [cvec, PiLp.inner_apply, RCLike.inner_apply, ← Complex.ofReal_mul, ← Complex.ofReal_sum]

lemma cvec_orthonormal (b : OrthonormalBasis X ℝ (EuclideanSpace ℝ X)) :
    Orthonormal ℂ (fun i => cvec (b i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [cvec_inner, orthonormal_iff_ite.mp b.orthonormal i j]
  split_ifs <;> simp

variable [Nonempty X]
def complexBasis (b : OrthonormalBasis X ℝ (EuclideanSpace ℝ X)) :
    OrthonormalBasis X ℂ (EuclideanSpace ℂ X) :=
  (basisOfOrthonormalOfCardEqFinrank (cvec_orthonormal b) finrank_euclideanSpace.symm).toOrthonormalBasis
    (by simpa using cvec_orthonormal b)

@[simp] lemma complexBasis_apply (b : OrthonormalBasis X ℝ (EuclideanSpace ℝ X)) (i : X) :
    complexBasis b i = cvec (b i) := by simp [complexBasis]

omit [Nonempty X] in
lemma cDiscriminant_eigen {P : Matrix X X ℝ} {πd : X → ℝ} {u : EuclideanSpace ℝ X} {d : ℝ}
    (he : discriminant P πd *ᵥ (fun x => u x) = d • (fun x => u x)) :
    Matrix.toEuclideanLin (cDiscriminant P πd) (cvec u) = (d : ℂ) • cvec u := by
  ext x
  have hx := congrFun he x
  change ∑ y, ((discriminant P πd x y : ℝ) : ℂ) * (u y : ℂ) = (d : ℂ) * (u x : ℂ)
  exact_mod_cast hx

omit [Fintype X] [DecidableEq X] [Nonempty X] in
lemma cvec_mass_multiple {πd : X → ℝ} {u : EuclideanSpace ℝ X} {c : ℝ}
    (hu : (fun x => u x) = fun x => c * Real.sqrt (πd x)) :
    cvec u = (c : ℂ) • cvec (fun x => Real.sqrt (πd x)) := by
  ext x
  simp [cvec, congrFun hu x]

end QuantumReflectionProof

open scoped BigOperators ComplexConjugate
noncomputable section
namespace QuantumReflectionProof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma plane_inner {a b : E} {d : ℝ}
    (haa : inner ℂ a a = 1) (hbb : inner ℂ b b = 1) (hab : inner ℂ a b = (d : ℂ))
    (α β ζ ξ : ℂ) :
    inner ℂ (α • a + β • b) (ζ • a + ξ • b) =
      star α * ζ + star β * ξ + (d : ℂ) * (star α * ξ + star β * ζ) := by
  have hba : inner ℂ b a = (d : ℂ) := by rw [← inner_conj_symm, hab]; simp
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, haa, hbb, hab, hba,
    mul_one, Complex.star_def]
  ring

lemma plane_difference_sq {a b : E} {d : ℝ}
    (haa : inner ℂ a a = 1) (hbb : inner ℂ b b = 1) (hab : inner ℂ a b = (d : ℂ))
    (α β : ℂ) :
    ‖(-2 * α - 2 * (d : ℂ) * β) • a + (2 * (d : ℂ) * α + (4 * (d : ℂ)^2 - 2) * β) • b‖ ^ 2 =
      4 * (1 - d ^ 2) * ‖α • a + β • b‖ ^ 2 := by
  have hc : inner ℂ ((-2 * α - 2 * (d : ℂ) * β) • a +
        (2 * (d : ℂ) * α + (4 * (d : ℂ)^2 - 2) * β) • b)
      ((-2 * α - 2 * (d : ℂ) * β) • a +
        (2 * (d : ℂ) * α + (4 * (d : ℂ)^2 - 2) * β) • b) =
        (4 * (1 - (d : ℂ)^2)) * inner ℂ (α • a + β • b) (α • a + β • b) := by
    simp only [plane_inner haa hbb hab, star_sub, star_mul, star_add, star_neg,
      star_ofNat, star_pow, Complex.star_def, Complex.conj_ofReal]
    ring
  have hcoeff : (4 * (1 - (d : ℂ)^2)) = ((4 * (1 - d^2) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcoeff] at hc
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
  change Complex.re _ = _ * Complex.re _
  rw [hc]
  exact Complex.re_ofReal_mul _ _

lemma orthogonal_sum_norm_sq {I : Type*} [Fintype I] (v : I → E)
    (hv : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  have hh : inner ℂ (∑ i, v i) (∑ i, v i) = ∑ i, inner ℂ (v i) (v i) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    exact Finset.sum_eq_single i (fun j _ hji => hv i j (Ne.symm hji)) (by simp)
  simp_rw [@norm_sq_eq_re_inner ℂ]
  change Complex.re _ = ∑ i, Complex.re _
  rw [hh, Complex.re_sum]

end QuantumReflectionProof

open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
noncomputable section
namespace QuantumReflectionProof
variable {X : Type*} [Fintype X] [DecidableEq X]

lemma reflection_a_b {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (u : EuclideanSpace ℂ X) :
    (spaceA P).reflection (bMap P πd u) =
      2 • aMap P (Matrix.toEuclideanLin (cDiscriminant P πd) u) - bMap P πd u := by
  rw [Submodule.reflection_apply, projection_a P hp]
  congr 2
  congr 1
  change Matrix.toEuclideanLin (embedAMatrix P)ᴴ (Matrix.toEuclideanLin (embedBMatrix P πd) u) = _
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, embed_cross hp]

lemma reflection_b_a {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd)
    (u : EuclideanSpace ℂ X) :
    (spaceB P πd).reflection (aMap P u) =
      2 • bMap P πd (Matrix.toEuclideanLin (cDiscriminant P πd) u) - aMap P u := by
  rw [Submodule.reflection_apply, projection_b P πd hp hπ hr]
  congr 2
  congr 1
  change Matrix.toEuclideanLin (embedBMatrix P πd)ᴴ (Matrix.toEuclideanLin (embedAMatrix P) u) = _
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, embed_cross_reverse hp hπ hr]

lemma walk_a_eigen {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd)
    {u : EuclideanSpace ℂ X} {d : ℂ}
    (he : Matrix.toEuclideanLin (cDiscriminant P πd) u = d • u) :
    walk P πd (aMap P u) = (2 * d) • bMap P πd u - aMap P u := by
  have hm : aMap P u ∈ spaceA P := by rw [← range_aMap]; exact ⟨u, rfl⟩
  change (spaceB P πd).reflection ((spaceA P).reflection (aMap P u)) = _
  rw [Submodule.reflection_mem_subspace_eq_self hm]
  rw [reflection_b_a hp hπ hr, he, map_smul]
  module

lemma walk_b_eigen {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd)
    {u : EuclideanSpace ℂ X} {d : ℂ}
    (he : Matrix.toEuclideanLin (cDiscriminant P πd) u = d • u) :
    walk P πd (bMap P πd u) = (4 * d ^ 2 - 1) • bMap P πd u - (2 * d) • aMap P u := by
  have hm : bMap P πd u ∈ spaceB P πd := by rw [← range_bMap]; exact ⟨u, rfl⟩
  change (spaceB P πd).reflection ((spaceA P).reflection (bMap P πd u)) = _
  rw [reflection_a_b hp, he, map_smul, map_sub, map_nsmul, map_smul,
    reflection_b_a hp hπ hr, he, map_smul, Submodule.reflection_mem_subspace_eq_self hm]
  module

lemma walk_plane_difference {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd)
    {u : EuclideanSpace ℂ X} {d : ℂ}
    (he : Matrix.toEuclideanLin (cDiscriminant P πd) u = d • u) (α β : ℂ) :
    walk P πd (α • aMap P u + β • bMap P πd u) - (α • aMap P u + β • bMap P πd u) =
      (-2 * α - 2 * d * β) • aMap P u + (2 * d * α + (4 * d ^ 2 - 2) * β) • bMap P πd u := by
  rw [map_add, map_smul, map_smul, walk_a_eigen hp hπ hr he, walk_b_eigen hp hπ hr he]
  module

lemma walkMatrix_unitary (P : Matrix X X ℝ) (πd : X → ℝ) :
    (walkMatrix P πd)ᴴ * walkMatrix P πd = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  apply LinearMap.ext
  intro u
  apply ext_inner_left ℂ
  intro v
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  simp [walkMatrix, walk]

end QuantumReflectionProof

open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
noncomputable section
namespace QuantumReflectionProof
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

lemma native_gap {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd)
    (hprim : P.IsPrimitive) {ψ : H X} (hψ : ψ ∈ spaceA P ⊔ spaceB P πd)
    (hperp : inner ℂ (piState P πd) ψ = 0) :
    (2 * phaseGap P πd / Real.pi) * ‖ψ‖ ≤ ‖walk P πd ψ - ψ‖ := by
  let hD := discriminant_symmetric hπ hr
  let b := hD.eigenvectorBasis
  let e := complexBasis b
  let d := hD.eigenvalues
  let a (i : X) := aMap P (e i)
  let bb (i : X) := bMap P πd (e i)
  have he (i : X) : Matrix.toEuclideanLin (cDiscriminant P πd) (e i) = (d i : ℂ) • e i := by
    simpa only [e, complexBasis_apply] using cDiscriminant_eigen (hD.mulVec_eigenvectorBasis i)
  have hd (i : X) : |d i| ≤ 1 := discriminant_eigen_abs_le hp hπ
    (by simpa using b.orthonormal.ne_zero i) (hD.mulVec_eigenvectorBasis i)
  have hsing (i : X) : IsSingularValue P πd |d i| := by
    apply eigen_abs_singular hπ hr (b.orthonormal.ne_zero i)
    ext x
    exact congrFun (hD.mulVec_eigenvectorBasis i) x
  have haa (i j : X) : inner ℂ (a i) (a j) = if i = j then 1 else 0 := by
    rw [aMap_inner hp]
    exact orthonormal_iff_ite.mp e.orthonormal i j
  have hbb (i j : X) : inner ℂ (bb i) (bb j) = if i = j then 1 else 0 := by
    rw [bMap_inner hp hπ hr]
    exact orthonormal_iff_ite.mp e.orthonormal i j
  have hab (i j : X) : inner ℂ (a i) (bb j) = if i = j then (d j : ℂ) else 0 := by
    rw [aMap_bMap_inner hp, he, inner_smul_right, orthonormal_iff_ite.mp e.orthonormal]
    split_ifs <;> simp
  have hba (i j : X) : inner ℂ (bb i) (a j) = if i = j then (d i : ℂ) else 0 := by
    rw [← inner_conj_symm, hab]
    by_cases h : i = j <;> simp [h, Ne.symm]
  have horth (i j : X) (hij : i ≠ j) (α β ζ ξ : ℂ) :
      inner ℂ (α • a i + β • bb i) (ζ • a j + ξ • bb j) = 0 := by
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      haa, hbb, hab, hba, if_neg hij, mul_zero, add_zero]
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hψ
  obtain ⟨u, rfl⟩ : ∃ u, aMap P u = y := by rwa [← range_aMap, LinearMap.mem_range] at hy
  obtain ⟨v, rfl⟩ : ∃ v, bMap P πd v = z := by rwa [← range_bMap, LinearMap.mem_range] at hz
  let α := e.repr u
  let β := e.repr v
  let w (i : X) := α i • a i + β i • bb i
  have hw : ψ = ∑ i, w i := by
    rw [← hyz]
    change aMap P u + bMap P πd v = ∑ i, (α i • aMap P (e i) + β i • bMap P πd (e i))
    rw [Finset.sum_add_distrib]
    simp only [← map_smul, ← map_sum, α, β, e.sum_repr]
  have hw0 (i j : X) (hij : i ≠ j) : inner ℂ (w i) (w j) = 0 := horth i j hij _ _ _ _
  let dw (i : X) := walk P πd (w i) - w i
  have hdw (i : X) : dw i =
      (-2 * α i - 2 * (d i : ℂ) * β i) • a i +
      (2 * (d i : ℂ) * α i + (4 * (d i : ℂ)^2 - 2) * β i) • bb i :=
    walk_plane_difference hp hπ hr (he i) _ _
  have hdw0 (i j : X) (hij : i ≠ j) : inner ℂ (dw i) (dw j) = 0 := by
    rw [hdw, hdw]
    exact horth i j hij _ _ _ _
  have hnorm (i : X) : ‖dw i‖ ^ 2 = 4 * (1 - d i ^ 2) * ‖w i‖ ^ 2 := by
    rw [hdw]
    exact plane_difference_sq (by simpa using haa i i) (by simpa using hbb i i)
      (by simpa using hab i i) _ _
  have hper (i : X) (hi : |d i| = 1) : w i = 0 := by
    obtain ⟨_, c, hc⟩ := discriminant_peripheral hp hπ hprim
      (by simpa using b.orthonormal.ne_zero i) (hD.mulVec_eigenvectorBasis i) hi
    have ha : a i = (c : ℂ) • piState P πd := by
      change aMap P (complexBasis b i) = _
      rw [complexBasis_apply, cvec_mass_multiple hc, map_smul, ← pi_aMap]
    have hb : bb i = (c : ℂ) • piState P πd := by
      change bMap P πd (complexBasis b i) = _
      rw [complexBasis_apply, cvec_mass_multiple hc, map_smul, ← pi_bMap hp hπ]
    have hiψ : inner ℂ (w i) ψ = inner ℂ (w i) (w i) := by
      rw [hw, inner_sum]
      exact Finset.sum_eq_single i (fun j _ hji => hw0 i j (Ne.symm hji)) (by simp)
    have hi0 : inner ℂ (w i) ψ = 0 := by
      simp [w, ha, hb, hperp]
    exact inner_self_eq_zero.mp (hiψ.symm.trans hi0)
  have hfactor (i : X) : (2 * phaseGap P πd / Real.pi)^2 * ‖w i‖^2 ≤ ‖dw i‖^2 := by
    rw [hnorm]
    by_cases hi : |d i| = 1
    · rw [hper i hi]; simp
    have hstrict : |d i| < 1 := lt_of_le_of_ne (hd i) hi
    have hsin := phase_sin_bound (hd i) (hsing i) hstrict
    have hsq : 0 ≤ 1 - d i ^ 2 := by
      nlinarith [sq_abs (d i), mul_self_le_mul_self (abs_nonneg (d i)) (hd i)]
    have hg : 0 ≤ phaseGap P πd / Real.pi := le_of_lt (div_pos (phaseGap_pos_le P πd).1 Real.pi_pos)
    have hbnd : (phaseGap P πd / Real.pi)^2 ≤ 1 - d i^2 := by
      have := Real.sq_sqrt hsq
      nlinarith [Real.sqrt_nonneg (1 - d i^2), sq_nonneg (Real.sqrt (1 - d i^2) - phaseGap P πd / Real.pi)]
    have hmul := mul_le_mul_of_nonneg_right hbnd (sq_nonneg ‖w i‖)
    have heq : (2 * phaseGap P πd / Real.pi)^2 = 4 * (phaseGap P πd / Real.pi)^2 := by ring
    rw [heq]
    nlinarith only [hmul]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfactor i)
  have hsumdw : walk P πd ψ - ψ = ∑ i, dw i := by
    rw [hw, map_sum, ← Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← orthogonal_sum_norm_sq w hw0, ← hw,
    ← orthogonal_sum_norm_sq dw hdw0, ← hsumdw] at hsum
  have hΔ := (phaseGap_pos_le P πd).1
  have hnon : 0 ≤ (2 * phaseGap P πd / Real.pi) * ‖ψ‖ := by positivity
  nlinarith [norm_nonneg (walk P πd ψ - ψ)]

end QuantumReflectionProof

open scoped BigOperators ComplexConjugate
open Matrix QuantumWalkSearch.PhaseReflection
noncomputable section
namespace QuantumReflectionProof
variable {X : Type*} [Fintype X] [DecidableEq X]

lemma walk_mem {P : Matrix X X ℝ} {πd : X → ℝ} {ψ : H X}
    (hψ : ψ ∈ spaceA P ⊔ spaceB P πd) : walk P πd ψ ∈ spaceA P ⊔ spaceB P πd := by
  have ha : (spaceA P).reflection ψ ∈ spaceA P ⊔ spaceB P πd := by
    rw [Submodule.reflection_apply, two_smul]
    have hm : (spaceA P).starProjection ψ ∈ spaceA P ⊔ spaceB P πd :=
      (show spaceA P ≤ spaceA P ⊔ spaceB P πd from le_sup_left) ((spaceA P).starProjection_apply_mem ψ)
    exact (spaceA P ⊔ spaceB P πd).sub_mem ((spaceA P ⊔ spaceB P πd).add_mem hm hm) hψ
  change (spaceB P πd).reflection ((spaceA P).reflection ψ) ∈ _
  rw [Submodule.reflection_apply, two_smul]
  have hm : (spaceB P πd).starProjection ((spaceA P).reflection ψ) ∈ spaceA P ⊔ spaceB P πd :=
    (show spaceB P πd ≤ spaceA P ⊔ spaceB P πd from le_sup_right) ((spaceB P πd).starProjection_apply_mem _)
  exact (spaceA P ⊔ spaceB P πd).sub_mem ((spaceA P ⊔ spaceB P πd).add_mem hm hm) ha

lemma walk_perp {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd)
    {ψ : H X} (hψ : inner ℂ (piState P πd) ψ = 0) :
    inner ℂ (piState P πd) (walk P πd ψ) = 0 := by
  have hh := rectangular_inner (walkMatrix P πd) (walkMatrix_unitary P πd) (piState P πd) ψ
  simp only [walkMatrix, LinearEquiv.apply_symm_apply] at hh
  rwa [walk_pi hp hπ, hψ] at hh

lemma walk_pow_mem_perp {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd)
    {ψ : H X} (hψ : ψ ∈ spaceA P ⊔ spaceB P πd) (hperp : inner ℂ (piState P πd) ψ = 0) (j : ℕ) :
    Matrix.toEuclideanLin ((walkMatrix P πd)^j) ψ ∈ spaceA P ⊔ spaceB P πd ∧
    inner ℂ (piState P πd) (Matrix.toEuclideanLin ((walkMatrix P πd)^j) ψ) = 0 := by
  induction j with
  | zero => simpa using And.intro hψ hperp
  | succ j hj =>
    rw [pow_succ', Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    simpa only [walkMatrix, LinearEquiv.apply_symm_apply] using And.intro (walk_mem hj.1) (walk_perp hp hπ hj.2)

lemma average_mem_perp {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd)
    {ψ : H X} (hψ : ψ ∈ spaceA P ⊔ spaceB P πd) (hperp : inner ℂ (piState P πd) ψ = 0) (s : ℕ) :
    Matrix.toEuclideanLin (powerAverage (walkMatrix P πd) s) ψ ∈ spaceA P ⊔ spaceB P πd ∧
    inner ℂ (piState P πd) (Matrix.toEuclideanLin (powerAverage (walkMatrix P πd) s) ψ) = 0 := by
  simp only [powerAverage, map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply]
  constructor
  · apply Submodule.smul_mem
    exact Submodule.sum_mem _ (fun j _ => (walk_pow_mem_perp hp hπ hψ hperp j).1)
  · simp only [inner_smul_right, inner_sum, (walk_pow_mem_perp hp hπ hψ hperp _).2,
      Finset.sum_const_zero, mul_zero]

lemma average_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (s : ℕ) :
    (U - 1) * powerAverage U s = ((2 : ℂ)^s)⁻¹ • (U^(2^s) - 1) := by
  rw [powerAverage, Matrix.mul_smul]
  congr 1
  rw [Fin.sum_univ_eq_sum_range, mul_geom_sum]

lemma average_contraction [Nonempty X] {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd)
    (hprim : P.IsPrimitive) {ψ : H X} (hψ : ψ ∈ spaceA P ⊔ spaceB P πd)
    (hperp : inner ℂ (piState P πd) ψ = 0) :
    ‖Matrix.toEuclideanLin (powerAverage (walkMatrix P πd) (precision (phaseGap P πd))) ψ‖ ≤
      (1 / 2 : ℝ) * ‖ψ‖ := by
  let Δ := phaseGap P πd
  let s := precision Δ
  let m : ℝ := 2^s
  let z := Matrix.toEuclideanLin (powerAverage (walkMatrix P πd) s) ψ
  have hΔ : 0 < Δ := (phaseGap_pos_le P πd).1
  have hm : 0 < m := by dsimp [m]; positivity
  have hprec : 2 * Real.pi ≤ m * Δ := (div_le_iff₀ hΔ).mp (precision_bound Δ hΔ)
  have hz := average_mem_perp hp hπ hψ hperp s
  have hgap := native_gap hp hπ hr hprim hz.1 hz.2
  have heq : walk P πd z - z = ((2 : ℂ)^s)⁻¹ •
      (Matrix.toEuclideanLin ((walkMatrix P πd)^(2^s)) ψ - ψ) := by
    have hh := congrArg (fun M => Matrix.toEuclideanLin M ψ) (average_difference (walkMatrix P πd) s)
    simpa only [z, map_sub, map_smul, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Matrix.toLpLin_one, LinearMap.id_apply,
      walkMatrix, LinearEquiv.apply_symm_apply] using hh
  have hupper : ‖walk P πd z - z‖ ≤ (2 * ‖ψ‖) / m := by
    rw [heq, norm_smul]
    have hn : ‖((2 : ℂ)^s)⁻¹‖ = m⁻¹ := by simp [m]
    rw [hn]
    calc
      m⁻¹ * ‖Matrix.toEuclideanLin ((walkMatrix P πd)^(2^s)) ψ - ψ‖ ≤
          m⁻¹ * (‖Matrix.toEuclideanLin ((walkMatrix P πd)^(2^s)) ψ‖ + ‖ψ‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (le_of_lt (inv_pos.mpr hm))
      _ = _ := by rw [unitary_norm _ (unitary_pow _ (walkMatrix_unitary P πd) _)]; ring
  have hbase : (2 * Δ / Real.pi) * ‖z‖ ≤ (2 * ‖ψ‖) / m := hgap.trans hupper
  have hx : 2 * Δ * ‖z‖ * m ≤ 2 * ‖ψ‖ * Real.pi := by
    apply (le_div_iff₀ hm).mp at hbase
    apply (div_le_iff₀ Real.pi_pos).mp
    convert hbase using 1
    ring
  have hmul := mul_le_mul_of_nonneg_right hprec (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z))
  change ‖z‖ ≤ (1 / 2 : ℝ) * ‖ψ‖
  nlinarith [Real.pi_pos]

lemma average_power_bound [Nonempty X] {P : Matrix X X ℝ} {πd : X → ℝ}
    (hp : P ∈ Matrix.rowStochastic ℝ X) (hπ : IsStationaryDist P πd) (hr : IsReversible P πd)
    (hprim : P.IsPrimitive) {ψ : H X} (hψ : ψ ∈ spaceA P ⊔ spaceB P πd)
    (hperp : inner ℂ (piState P πd) ψ = 0) (k : ℕ) :
    ‖Matrix.toEuclideanLin ((powerAverage (walkMatrix P πd) (precision (phaseGap P πd)))^k) ψ‖ ≤
      (1 / 2 : ℝ)^k * ‖ψ‖ := by
  let A := powerAverage (walkMatrix P πd) (precision (phaseGap P πd))
  have hinv (j : ℕ) : Matrix.toEuclideanLin (A^j) ψ ∈ spaceA P ⊔ spaceB P πd ∧
      inner ℂ (piState P πd) (Matrix.toEuclideanLin (A^j) ψ) = 0 := by
    induction j with
    | zero => simpa using And.intro hψ hperp
    | succ j hj =>
      rw [pow_succ', Matrix.toLpLin_mul_same, LinearMap.comp_apply]
      exact average_mem_perp hp hπ hj.1 hj.2 _
  change ‖Matrix.toEuclideanLin (A^k) ψ‖ ≤ _
  induction k with
  | zero => simp
  | succ k hk =>
    rw [pow_succ', Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    calc
      ‖Matrix.toEuclideanLin A (Matrix.toEuclideanLin (A^k) ψ)‖ ≤
          (1 / 2 : ℝ) * ‖Matrix.toEuclideanLin (A^k) ψ‖ :=
        average_contraction hp hπ hr hprim (hinv k).1 (hinv k).2
      _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ)^k * ‖ψ‖) := mul_le_mul_of_nonneg_left hk (by norm_num)
      _ = _ := by rw [pow_succ]; ring

end QuantumReflectionProof

open scoped BigOperators ComplexConjugate
open Matrix
noncomputable section

namespace QuantumWalkSearch.PhaseReflection

/-- Theorem 6 (p. 9), properties 2 and 3, for the circuit `R(P)` of its proof, under the standing
assumption of §3.2 (p. 8) that `P` is ergodic and reversible. -/
theorem theorem_6 {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) (πd : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (herg : P.IsPrimitive)
    (hπ : IsStationaryDist P πd) (hrev : IsReversible P πd)
    (hn : 2 ≤ Fintype.card X) (k : ℕ) :
    Matrix.toEuclideanLin (reflectionCircuit P πd k) (tensorZero (piState P πd)) =
      tensorZero (piState P πd) ∧
    ∀ ψ ∈ spaceA P ⊔ spaceB P πd, inner ℂ (piState P πd) ψ = 0 →
      ‖Matrix.toEuclideanLin (reflectionCircuit P πd k + 1) (tensorZero ψ)‖ ≤
        (2 : ℝ) ^ (1 - (k : ℤ)) * ‖ψ‖ := by
  let : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hU := QuantumReflectionProof.walkMatrix_unitary P πd
  have hU' := QuantumReflectionProof.unitary_right (walkMatrix P πd) hU
  constructor
  · change Matrix.toEuclideanLin (QuantumReflectionProof.circuit (walkMatrix P πd)
      (precision (phaseGap P πd)) k) (tensorZero (piState P πd)) = _
    apply QuantumReflectionProof.circuit_fixed _ hU hU'
    simpa only [walkMatrix, LinearEquiv.apply_symm_apply] using QuantumReflectionProof.walk_pi hP hπ
  · intro ψ hψ hperp
    change ‖Matrix.toEuclideanLin (QuantumReflectionProof.circuit (walkMatrix P πd)
      (precision (phaseGap P πd)) k + 1) (tensorZero ψ)‖ ≤ _
    rw [QuantumReflectionProof.circuit_error _ hU hU']
    calc
      2 * ‖Matrix.toEuclideanLin ((QuantumReflectionProof.powerAverage (walkMatrix P πd)
          (precision (phaseGap P πd)))^k) ψ‖ ≤ 2 * ((1 / 2 : ℝ)^k * ‖ψ‖) :=
        mul_le_mul_of_nonneg_left (QuantumReflectionProof.average_power_bound hP hπ hrev herg hψ hperp k)
          (by norm_num)
      _ = (2 : ℝ)^(1 - (k : ℤ)) * ‖ψ‖ := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast]
        simp only [div_pow, one_pow]
        ring


end QuantumWalkSearch.PhaseReflection

open QuantumWalkSearch.PhaseReflection

theorem solution {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X X ℝ) (πd : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (herg : P.IsPrimitive)
    (hπ : IsStationaryDist P πd) (hrev : IsReversible P πd)
    (hn : 2 ≤ Fintype.card X) (k : ℕ) :
    Matrix.toEuclideanLin (reflectionCircuit P πd k) (tensorZero (piState P πd)) =
      tensorZero (piState P πd) ∧
    ∀ ψ ∈ spaceA P ⊔ spaceB P πd, inner ℂ (piState P πd) ψ = 0 →
      ‖Matrix.toEuclideanLin (reflectionCircuit P πd k + 1) (tensorZero ψ)‖ ≤
        (2 : ℝ) ^ (1 - (k : ℤ)) * ‖ψ‖ := by
  exact QuantumWalkSearch.PhaseReflection.theorem_6 P πd hP herg hπ hrev hn k
