-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P17.bell_check_identities
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T23:49:39.578527+00:00
-- url     : https://prove2.me/submissions/ea4c0195-7d25-4b4f-ad6f-5bca01bb5741

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P17

set_option autoImplicit false

open scoped ComplexConjugate Matrix Kronecker
open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Intakenext100.P17
open QAlgorithms.DopedTomography (bellVector)

noncomputable section

namespace BB84Goal

lemma pauliOps_one (P : Stabilizer.Pauli) (y z : Qubits 1) :
    pauliOps (fun _ : Fin 1 => P) y z = P.mat (y 0) (z 0) := by
  simp [pauliOps, Stabilizer.PauliString.toMatrix]

/-- The amplitude `2^{-1/2}`. -/
def c : ℂ := ((Real.sqrt ((2 : ℝ) ^ 1))⁻¹ : ℂ)

lemma c_sq : c ^ 2 = 1 / 2 := by
  unfold c
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma conj_c : conj c = c := by
  unfold c
  rw [map_inv₀, Complex.conj_ofReal]

lemma bellVec_apply (P : Stabilizer.Pauli) (p : Qubits 1 × Qubits 1) :
    bellVector (fun _ : Fin 1 => P) p = P.mat (p.2 0) (p.1 0) * c := by
  obtain ⟨p1, p2⟩ := p
  unfold bellVector act
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, maxEntangled,
    ite_mul, one_mul, zero_mul, pauliOps_one]
  rw [Finset.sum_eq_single p1 (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [if_true, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
  rfl

lemma q1_ext (x y : Qubits 1) : x = y ↔ x 0 = y 0 := by
  constructor
  · rintro rfl; rfl
  · intro h
    funext i
    fin_cases i
    exact h

lemma ket_apply {ι : Type} [DecidableEq ι] (i j : ι) : (ket i : EuclideanSpace ℂ ι) j =
    if j = i then 1 else 0 := by
  simp [ket]

end BB84Goal

open BB84Goal in
theorem solution :
    (pureDensity (bellVector (fun _ : Fin 1 => Stabilizer.Pauli.X)) + pureDensity (bellVector (fun _ : Fin 1 => Stabilizer.Pauli.Y)) =
      pureDensity (ket (((fun _ => false), (fun _ => true)) : Qubits 1 × Qubits 1)) +
        pureDensity (ket (((fun _ => true), (fun _ => false)) : Qubits 1 × Qubits 1))) ∧
    (pureDensity (bellVector (fun _ : Fin 1 => Stabilizer.Pauli.Z)) + pureDensity (bellVector (fun _ : Fin 1 => Stabilizer.Pauli.Y)) =
      pureDensity (xPair false true) + pureDensity (xPair true false)) := by
  have hc := c_sq
  constructor
  · ext ⟨a1, a2⟩ ⟨b1, b2⟩
    obtain ⟨u1, rfl⟩ : ∃ u : Bool, a1 = fun _ => u := ⟨a1 0, (q1_ext _ _).mpr rfl⟩
    obtain ⟨u2, rfl⟩ : ∃ u : Bool, a2 = fun _ => u := ⟨a2 0, (q1_ext _ _).mpr rfl⟩
    obtain ⟨u3, rfl⟩ : ∃ u : Bool, b1 = fun _ => u := ⟨b1 0, (q1_ext _ _).mpr rfl⟩
    obtain ⟨u4, rfl⟩ : ∃ u : Bool, b2 = fun _ => u := ⟨b2 0, (q1_ext _ _).mpr rfl⟩
    simp only [Matrix.add_apply, pureDensity, Matrix.of_apply, bellVec_apply, ket_apply,
      Prod.mk.injEq, q1_ext, map_mul, conj_c]
    cases u1 <;> cases u2 <;> cases u3 <;> cases u4 <;>
      simp [Stabilizer.Pauli.mat, pauliX, pauliY, Complex.conj_I] <;> ring_nf <;>
      simp only [hc, Complex.I_sq] <;> ring_nf
  · ext ⟨a1, a2⟩ ⟨b1, b2⟩
    obtain ⟨u1, rfl⟩ : ∃ u : Bool, a1 = fun _ => u := ⟨a1 0, (q1_ext _ _).mpr rfl⟩
    obtain ⟨u2, rfl⟩ : ∃ u : Bool, a2 = fun _ => u := ⟨a2 0, (q1_ext _ _).mpr rfl⟩
    obtain ⟨u3, rfl⟩ : ∃ u : Bool, b1 = fun _ => u := ⟨b1 0, (q1_ext _ _).mpr rfl⟩
    obtain ⟨u4, rfl⟩ : ∃ u : Bool, b2 = fun _ => u := ⟨b2 0, (q1_ext _ _).mpr rfl⟩
    simp only [Matrix.add_apply, pureDensity, Matrix.of_apply, bellVec_apply, xPair,
      PiLp.toLp_apply, map_mul, conj_c]
    cases u1 <;> cases u2 <;> cases u3 <;> cases u4 <;>
      simp [Stabilizer.Pauli.mat, pauliY, pauliZ, Complex.conj_I, map_ofNat] <;> ring_nf <;>
      simp only [hc, Complex.I_sq] <;> ring_nf
