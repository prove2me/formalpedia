-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.exists_pauli_of_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:14:33.746857+00:00
-- url     : https://prove2.me/submissions/5f2a1f18-cf2c-40a3-9269-ce19e0dc8b9e

import Theorems.Thm_QAlgorithms_GottesmanIntro_independent_binary_generators
import Mathlib.LinearAlgebra.Dual.Lemmas

open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

private def xb : Pauli → ZMod 2
  | .X | .Y => 1
  | _ => 0

private def zb : Pauli → ZMod 2
  | .Z | .Y => 1
  | _ => 0

private def eps (x : ZMod 2) : ℂ := if x = 0 then 1 else -1

private lemma eps_add (x y : ZMod 2) : eps (x+y) = eps x * eps y := by
  have hx : x = 0 ∨ x = 1 := by fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hy : y = 0 ∨ y = 1 := by fin_cases y <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [eps, show (1 : ZMod 2) + 1 = 0 from rfl]

private lemma eps_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    eps (∑ i ∈ s, f i) = ∏ i ∈ s, eps (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eps]
  | @insert i s hi ih => simp [Finset.sum_insert hi, Finset.prod_insert hi, eps_add, ih]

private def tens {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ := fun y z => ∏ q, A q (y q) (z q)

private lemma tens_mul {n : ℕ} (A B : Fin n → Matrix Bool Bool ℂ) :
    tens A * tens B = tens (fun q => A q * B q) := by
  ext y z
  simp only [Matrix.mul_apply, tens, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun q b => A q (y q) b * B q b (z q)).symm

private lemma tens_one (n : ℕ) : tens (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y z
  simp only [tens, Matrix.one_apply]
  by_cases h : y = z
  · subst z; simp
  · rw [if_neg h]
    obtain ⟨q,hq⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

private lemma tens_star {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) :
    star (tens A) = tens (fun q => star (A q)) := by
  ext y z
  simp [tens, Matrix.star_apply]

private lemma mat_star (p : Pauli) : star p.mat = p.mat := by
  cases p <;> ext a b <;> cases a <;> cases b <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.star_apply]

private lemma mat_sq (p : Pauli) : p.mat * p.mat = 1 := by
  cases p <;> ext a b <;> cases a <;> cases b <;>
    norm_num [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool]

private lemma mat_comm (p q : Pauli) :
    p.mat * q.mat = eps (xb p * zb q + zb p * xb q) • (q.mat * p.mat) := by
  cases p <;> cases q <;> ext a b <;> cases a <;> cases b <;>
    norm_num [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply,
      Fintype.sum_bool, xb, zb, eps, show (1 : ZMod 2) + 1 = 0 from rfl]

private lemma tens_comm {n : ℕ} (p q : Fin n → Pauli) :
    tens (fun i => (p i).mat) * tens (fun i => (q i).mat) =
      eps (∑ i, (xb (p i) * zb (q i) + zb (p i) * xb (q i))) •
        (tens (fun i => (q i).mat) * tens (fun i => (p i).mat)) := by
  rw [tens_mul, tens_mul, eps_sum]
  ext y z
  change (∏ i, ((p i).mat * (q i).mat) (y i) (z i)) = _
  calc
    _ = ∏ i, eps (xb (p i) * zb (q i) + zb (p i) * xb (q i)) *
        ((q i).mat * (p i).mat) (y i) (z i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [mat_comm]
      rfl
    _ = _ := by simp only [tens, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

private lemma realize {n : ℕ} (p : Fin n → Pauli) :
    ∃ E ∈ pauliGroup n,
      (E : Matrix (Qubits n) (Qubits n) ℂ) = tens (fun q => (p q).mat) := by
  have hu : tens (fun q => (p q).mat) ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, tens_star, tens_mul]
    simpa only [mat_star, mat_sq] using tens_one n
  let E : Matrix.unitaryGroup (Qubits n) ℂ := ⟨_, hu⟩
  refine ⟨E, Subgroup.subset_closure ?_, rfl⟩
  refine ⟨⟨0,p⟩, ?_⟩
  ext y z
  simp [E, PauliString.toMatrix, tens]

private lemma linear_equations {n a : ℕ} (p : Fin a → Fin n → Pauli)
    (hli : LinearIndependent (ZMod 2) (fun i => Sum.elim (fun q => xb (p i q))
      (fun q => zb (p i q)))) (v : Fin a → ZMod 2) :
    ∃ x z : Fin n → ZMod 2, ∀ i,
      ∑ q, (xb (p i q) * z q + zb (p i q) * x q) = v i := by
  classical
  let r : Fin a → (Fin n ⊕ Fin n → ZMod 2) :=
    fun i => Sum.elim (fun q => xb (p i q)) (fun q => zb (p i q))
  let L := Fintype.linearCombination (ZMod 2) r
  have hL : Function.Injective L := linearIndependent_iff_injective_fintypeLinearCombination.mp hli
  let w : (Fin a → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun c => ∑ i, c i * v i
      map_add' := fun c d => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c d => by simp [Finset.mul_sum, mul_assoc] }
  obtain ⟨φ,hφ⟩ := LinearMap.dualMap_surjective_of_injective hL w
  have hval (i : Fin a) : φ (r i) = v i := by
    have h := congrArg (fun f : Module.Dual (ZMod 2) (Fin a → ZMod 2) =>
      f (Pi.single i 1)) hφ
    simpa [L, Fintype.linearCombination_apply, w, Pi.single_apply] using h
  refine ⟨(fun q => φ (Pi.single (Sum.inr q) 1)),
    (fun q => φ (Pi.single (Sum.inl q) 1)), fun i => ?_⟩
  have hr : (∑ j, r i j • Pi.single j (1 : ZMod 2)) = r i := by
    ext j
    simp [Pi.single_apply]
  have he := congrArg φ hr
  simp only [Fintype.sum_sum_type, map_add, map_sum, map_smul, smul_eq_mul] at he
  rw [← hval i, ← he]
  simp only [r, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]

private def op (x z : ZMod 2) : Pauli :=
  if x = 0 then (if z = 0 then .I else .Z) else (if z = 0 then .X else .Y)

private lemma op_x (x z : ZMod 2) : xb (op x z) = x := by
  have hx : x = 0 ∨ x = 1 := by fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hz : z = 0 ∨ z = 1 := by fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases hx with rfl | rfl <;> rcases hz with rfl | rfl <;> norm_num [op, xb]

private lemma op_z (x z : ZMod 2) : zb (op x z) = z := by
  have hx : x = 0 ∨ x = 1 := by fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hz : z = 0 ∨ z = 1 := by fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases hx with rfl | rfl <;> rcases hz with rfl | rfl <;> norm_num [op, zb]

private lemma string_eq {n : ℕ} (P : PauliString n) :
    P.toMatrix = Complex.I ^ P.phase.val • tens (fun q => (P.ops q).mat) := by
  rfl

theorem solution (n a : ℕ) (g : Fin a → Matrix.unitaryGroup (Qubits n) ℂ)
    (hS : IsStabilizerGroup (Subgroup.closure (Set.range g)))
    (hcard : Nat.card (Subgroup.closure (Set.range g)) = 2 ^ a) (v : Fin a → ZMod 2) :
    ∃ E ∈ pauliGroup n, ∀ i : Fin a,
      (v i = 0 → (g i : Matrix (Qubits n) (Qubits n) ℂ) * E = E * g i) ∧
      (v i = 1 → (g i : Matrix (Qubits n) (Qubits n) ℂ) * E =
        -((E : Matrix (Qubits n) (Qubits n) ℂ) * g i)) := by
  classical
  obtain ⟨P,hP,hli⟩ := QAlgorithms.GottesmanIntro.independent_binary_generators n a g hS hcard
  have hbits (p : Pauli) :
      (if p = Pauli.X ∨ p = Pauli.Y then 1 else 0 : ZMod 2) = xb p ∧
      (if p = Pauli.Z ∨ p = Pauli.Y then 1 else 0 : ZMod 2) = zb p := by
    cases p <;> simp [xb,zb]
  simp only [(hbits _).1, (hbits _).2] at hli
  obtain ⟨x,z,hxz⟩ := linear_equations (fun i => (P i).ops) hli v
  let p : Fin n → Pauli := fun q => op (x q) (z q)
  obtain ⟨E,hE,hmat⟩ := realize p
  refine ⟨E,hE,fun i => ?_⟩
  have hc : (g i : Matrix (Qubits n) (Qubits n) ℂ) * E =
      eps (v i) • ((E : Matrix (Qubits n) (Qubits n) ℂ) * g i) := by
    rw [hP, hmat, string_eq, Matrix.smul_mul, Matrix.mul_smul, tens_comm]
    simp only [p, op_x, op_z, hxz]
    exact smul_comm _ _ _
  constructor
  · intro hv; simpa [hv,eps] using hc
  · intro hv; simpa [hv,eps] using hc
