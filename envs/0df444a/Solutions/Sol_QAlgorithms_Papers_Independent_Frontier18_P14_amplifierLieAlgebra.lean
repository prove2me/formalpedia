-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P14.amplifierLieAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:41:35.938911+00:00
-- url     : https://prove2.me/submissions/9b92c3ef-0899-429a-91fd-ec55cc05d65f

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
noncomputable section
open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P14

lemma x8_ann_single {n : ℕ} (j : Fin n) (m : Fin n → ℕ) (r : ℂ) :
    annihilate n j (Finsupp.single m r) =
      if m j = 0 then 0 else
        Finsupp.single (Function.update m j (m j - 1)) (r * (Real.sqrt (m j : ℝ) : ℂ)) := by
  unfold annihilate
  rw [Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
  split_ifs with h
  · simp
  · simp [coreKet, Finsupp.smul_single, mul_comm]

lemma x8_cre_single {n : ℕ} (j : Fin n) (m : Fin n → ℕ) (r : ℂ) :
    create n j (Finsupp.single m r) =
      Finsupp.single (Function.update m j (m j + 1)) (r * (Real.sqrt ((m j : ℝ) + 1) : ℂ)) := by
  unfold create
  rw [Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
  simp [coreKet, Finsupp.smul_single, mul_comm]


private lemma x8_sq (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = (x : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]

lemma x8_ccr_same {n : ℕ} (j : Fin n) :
    annihilate n j * create n j = create n j * annihilate n j + 1 := by
  apply Finsupp.lhom_ext
  intro m r
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, x8_cre_single,
    x8_ann_single, Function.update_self, Function.update_idem, Nat.add_sub_cancel,
    Function.update_eq_self, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
  by_cases h : m j = 0
  · simp [h]
  · rw [if_neg h, x8_cre_single, Function.update_self, Function.update_idem,
      Nat.sub_add_cancel (Nat.pos_of_ne_zero h), Function.update_eq_self,
      ← Finsupp.single_add]
    congr 1
    have e1 : ((m j + 1 : ℕ) : ℝ) = (m j : ℝ) + 1 := by push_cast; ring
    have e2 : (((m j - 1 : ℕ) : ℝ) + 1) = (m j : ℝ) := by
      rw [Nat.cast_sub (Nat.pos_of_ne_zero h)]; push_cast; ring
    rw [e1, e2, mul_assoc, x8_sq _ (by positivity), mul_assoc, x8_sq _ (by positivity)]
    push_cast; ring

lemma x8_ccr_ne {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    annihilate n j * create n k = create n k * annihilate n j := by
  apply Finsupp.lhom_ext
  intro m r
  simp only [Module.End.mul_apply, x8_cre_single, x8_ann_single,
    Function.update_of_ne hjk]
  by_cases h : m j = 0
  · simp [h]
  · rw [if_neg h, if_neg h, x8_cre_single, Function.update_of_ne (Ne.symm hjk),
      Function.update_comm hjk]
    congr 1; ring

lemma x8_aa {n : ℕ} (j k : Fin n) :
    annihilate n j * annihilate n k = annihilate n k * annihilate n j := by
  by_cases hjk : j = k
  · subst hjk; rfl
  apply Finsupp.lhom_ext
  intro m r
  simp only [Module.End.mul_apply, x8_ann_single]
  by_cases hk : m k = 0 <;> by_cases hj : m j = 0
  · simp [hk, hj]
  · simp only [hk, hj, if_true, if_false, map_zero, x8_ann_single,
      Function.update_of_ne (Ne.symm hjk)]
  · simp only [hk, hj, if_true, if_false, map_zero, x8_ann_single,
      Function.update_of_ne hjk]
  · simp only [hk, hj, if_false, x8_ann_single, Function.update_of_ne hjk,
      Function.update_of_ne (Ne.symm hjk)]
    rw [Function.update_comm hjk]
    congr 1; ring

lemma x8_cc {n : ℕ} (j k : Fin n) :
    create n j * create n k = create n k * create n j := by
  by_cases hjk : j = k
  · subst hjk; rfl
  apply Finsupp.lhom_ext
  intro m r
  simp only [Module.End.mul_apply, x8_cre_single, Function.update_of_ne hjk,
    Function.update_of_ne (Ne.symm hjk)]
  rw [Function.update_comm hjk]
  congr 1; ring

section X8alg
variable {R : Type*} [Ring R] [Algebra ℂ R]

private lemma x8_generic2 (a0 a1 c0 c1 : R)
    (h00 : a0 * c0 = c0 * a0 + 1) (h11 : a1 * c1 = c1 * a1 + 1)
    (h01 : a0 * c1 = c1 * a0) (h10 : a1 * c0 = c0 * a1)
    (haa : a1 * a0 = a0 * a1) (hcc : c1 * c0 = c0 * c1) :
    let KT : R := (1 / 2 : ℂ) • (c0 * a0 + a1 * c1)
    let KX : R := (1 / 2 : ℂ) • (a0 * a1 + c0 * c1)
    let KY : R := (Complex.I / 2) • (a0 * a1 - c0 * c1)
    let KZ : R := (1 / 2 : ℂ) • (c0 * a0 - a1 * c1)
    let T : R := (1 / 2 : ℂ) • (c0 * a0 + c1 * a1)
    let Z : R := (1 / 2 : ℂ) • (c0 * a0 - c1 * a1)
    KX * KY - KY * KX = -Complex.I • KT ∧
    KY * KT - KT * KY = Complex.I • KX ∧
    KT * KX - KX * KT = Complex.I • KY ∧
    KZ * KT - KT * KZ = 0 ∧
    KZ * KX - KX * KZ = 0 ∧
    KZ * KY - KY * KZ = 0 ∧
    KT = T + (1 / 2 : ℂ) • (1 : R) ∧
    KZ = Z - (1 / 2 : ℂ) • (1 : R) ∧
    KT ^ 2 - KX ^ 2 - KY ^ 2 = KZ * (KZ + 1) := by
  have h00' : ∀ x : R, a0 * (c0 * x) = c0 * (a0 * x) + x := fun x => by
    rw [← mul_assoc, h00, add_mul, one_mul, mul_assoc]
  have h11' : ∀ x : R, a1 * (c1 * x) = c1 * (a1 * x) + x := fun x => by
    rw [← mul_assoc, h11, add_mul, one_mul, mul_assoc]
  have h01' : ∀ x : R, a0 * (c1 * x) = c1 * (a0 * x) := fun x => by
    rw [← mul_assoc, h01, mul_assoc]
  have h10' : ∀ x : R, a1 * (c0 * x) = c0 * (a1 * x) := fun x => by
    rw [← mul_assoc, h10, mul_assoc]
  have haa' : ∀ x : R, a1 * (a0 * x) = a0 * (a1 * x) := fun x => by
    rw [← mul_assoc, haa, mul_assoc]
  have hcc' : ∀ x : R, c1 * (c0 * x) = c0 * (c1 * x) := fun x => by
    rw [← mul_assoc, hcc, mul_assoc]
  intro KT KX KY KZ T Z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [KT, KX, KY, KZ, T, Z, sq, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_sub, mul_assoc, smul_smul,
      h00', h11', h01', h10', haa', hcc', h00, h11, h01, h10, haa, hcc, mul_one, one_mul]
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf

end X8alg

theorem x8_main2 :
    commutator lorentzX lorentzY = -Complex.I • lorentzT ∧
    commutator lorentzY lorentzT = Complex.I • lorentzX ∧
    commutator lorentzT lorentzX = Complex.I • lorentzY ∧
    commutator lorentzZ lorentzT = 0 ∧
    commutator lorentzZ lorentzX = 0 ∧
    commutator lorentzZ lorentzY = 0 ∧
    lorentzT = stokesT + (1 / 2 : ℂ) • (1 : Module.End ℂ (Core 2)) ∧
    lorentzZ = stokesZ - (1 / 2 : ℂ) • (1 : Module.End ℂ (Core 2)) ∧
    lorentzT ^ 2 - lorentzX ^ 2 - lorentzY ^ 2 = lorentzZ * (lorentzZ + 1) :=
  x8_generic2 (annihilate 2 0) (annihilate 2 1) (create 2 0) (create 2 1)
    (x8_ccr_same 0) (x8_ccr_same 1) (x8_ccr_ne 0 1 (by decide)) (x8_ccr_ne 1 0 (by decide))
    (x8_aa 1 0) (x8_cc 1 0)

end QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Frontier18.P14 in
theorem solution :
    commutator lorentzX lorentzY = -Complex.I • lorentzT ∧
    commutator lorentzY lorentzT = Complex.I • lorentzX ∧
    commutator lorentzT lorentzX = Complex.I • lorentzY ∧
    commutator lorentzZ lorentzT = 0 ∧
    commutator lorentzZ lorentzX = 0 ∧
    commutator lorentzZ lorentzY = 0 ∧
    lorentzT = stokesT + (1 / 2 : ℂ) • (1 : Module.End ℂ (Core 2)) ∧
    lorentzZ = stokesZ - (1 / 2 : ℂ) • (1 : Module.End ℂ (Core 2)) ∧
    lorentzT ^ 2 - lorentzX ^ 2 - lorentzY ^ 2 = lorentzZ * (lorentzZ + 1) := x8_main2
