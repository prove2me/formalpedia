-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.independent_binary_generators
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:28:26.524273+00:00
-- url     : https://prove2.me/submissions/419bff69-3525-4288-b4e6-c9f1fa9fb09c

import Definitions.Def_QAlgorithms_Defs_QECC
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.SetTheory.Cardinal.Finite

open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

private def ph (c : ZMod 4) : ℂ := Complex.I ^ c.val

private lemma ph0 : ph 0 = 1 := by change Complex.I ^ 0 = 1; norm_num
private lemma ph1 : ph 1 = Complex.I := by change Complex.I ^ 1 = Complex.I; norm_num
private lemma ph2 : ph 2 = -1 := by change Complex.I ^ 2 = -1; norm_num
private lemma ph3 : ph 3 = -Complex.I := by change Complex.I ^ 3 = -Complex.I; norm_num

private lemma phase_cases (c : ZMod 4) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private lemma ph_add (c d : ZMod 4) : ph (c+d) = ph c * ph d := by
  simp only [ph, ZMod.val_add]
  rw [← Complex.I_pow_eq_pow_mod, pow_add]

private lemma ph_sum {ι : Type*} (s : Finset ι) (c : ι → ZMod 4) :
    ph (∑ i ∈ s, c i) = ∏ i ∈ s, ph (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ph]
  | @insert i s hi ih => simp [Finset.sum_insert hi, Finset.prod_insert hi, ph_add, ih]

private lemma zcases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

private def xb : Pauli → ZMod 2
  | .X | .Y => 1
  | _ => 0

private def zb : Pauli → ZMod 2
  | .Z | .Y => 1
  | _ => 0

private def bits {n : ℕ} (P : PauliString n) : Fin n ⊕ Fin n → ZMod 2 :=
  Sum.elim (fun q => xb (P.ops q)) (fun q => zb (P.ops q))

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

private lemma mat_mul (p q : Pauli) :
    p.mat * q.mat = ph (Pauli.mul p q).1 • (Pauli.mul p q).2.mat := by
  cases p <;> cases q <;> ext a b <;> cases a <;> cases b <;>
    norm_num [Pauli.mat, Pauli.mul, ph0, ph1, ph2, ph3, pauliX, pauliY, pauliZ, Matrix.mul_apply,
      Fintype.sum_bool]

private lemma bits_mul {n : ℕ} (P Q : PauliString n) : bits (P.mul Q) = bits P + bits Q := by
  funext j
  cases j with
  | inl j =>
    change xb (Pauli.mul (P.ops j) (Q.ops j)).2 = xb (P.ops j) + xb (Q.ops j)
    cases P.ops j <;> cases Q.ops j <;> norm_num [Pauli.mul, xb, show (1 : ZMod 2) + 1 = 0 from rfl]
  | inr j =>
    change zb (Pauli.mul (P.ops j) (Q.ops j)).2 = zb (P.ops j) + zb (Q.ops j)
    cases P.ops j <;> cases Q.ops j <;> norm_num [Pauli.mul, zb, show (1 : ZMod 2) + 1 = 0 from rfl]

private lemma string_eq {n : ℕ} (P : PauliString n) :
    P.toMatrix = ph P.phase • tens (fun q => (P.ops q).mat) := rfl

private lemma string_mul {n : ℕ} (P Q : PauliString n) :
    P.toMatrix * Q.toMatrix = (P.mul Q).toMatrix := by
  rw [string_eq, string_eq, Matrix.smul_mul, Matrix.mul_smul, tens_mul, string_eq]
  simp only [PauliString.mul, ph_add, ph_sum]
  ext y z
  simp only [Matrix.smul_apply, smul_eq_mul, tens]
  simp_rw [mat_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  ring

private def emptyString (n : ℕ) : PauliString n := ⟨0,fun _ => .I⟩

private lemma empty_matrix (n : ℕ) : (emptyString n).toMatrix = 1 := by
  rw [string_eq]
  simpa [emptyString, ph, Pauli.mat] using tens_one n

private lemma empty_bits (n : ℕ) : bits (emptyString n) = 0 := by
  funext j
  cases j <;> rfl

private lemma string_star {n : ℕ} (P : PauliString n) :
    star P.toMatrix = (⟨-P.phase, P.ops⟩ : PauliString n).toMatrix := by
  rw [string_eq, star_smul, tens_star, string_eq]
  simp only [mat_star]
  have hp : star (ph P.phase) = ph (-P.phase) := by
    generalize P.phase = c
    fin_cases c
    · change star (Complex.I ^ 0) = Complex.I ^ 0; norm_num
    · change star (Complex.I ^ 1) = Complex.I ^ 3; norm_num
    · change star (Complex.I ^ 2) = Complex.I ^ 2; norm_num
    · change star (Complex.I ^ 3) = Complex.I ^ 1; norm_num
  rw [hp]

private lemma pauli_repr {n : ℕ} (U : Matrix.unitaryGroup (Qubits n) ℂ)
    (hU : U ∈ pauliGroup n) : ∃ P : PauliString n, (U : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix := by
  induction hU using Subgroup.closure_induction with
  | mem U hU => exact hU
  | one => exact ⟨emptyString n, (empty_matrix n).symm⟩
  | mul U V _ _ hU hV =>
    obtain ⟨P,hP⟩ := hU
    obtain ⟨Q,hQ⟩ := hV
    exact ⟨P.mul Q, by simpa only [Submonoid.coe_mul, hP, hQ] using string_mul P Q⟩
  | inv U _ hU =>
    obtain ⟨P,hP⟩ := hU
    exact ⟨⟨-P.phase,P.ops⟩, by change star (U : Matrix (Qubits n) (Qubits n) ℂ) = _; rw [hP, string_star]⟩

private lemma mat_sq (p : Pauli) : p.mat * p.mat = 1 := by
  cases p <;> ext a b <;> cases a <;> cases b <;>
    norm_num [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool]

private lemma string_sq {n : ℕ} (P : PauliString n) :
    P.toMatrix * P.toMatrix = 1 ∨ P.toMatrix * P.toMatrix = -1 := by
  rw [string_eq, Matrix.smul_mul, Matrix.mul_smul, tens_mul]
  simp only [mat_sq, tens_one, smul_smul]
  rcases phase_cases P.phase with hc | hc | hc | hc <;> rw [hc] <;> norm_num [ph0,ph1,ph2,ph3]

private lemma stabilizer_sq {n : ℕ} (S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (hS : IsStabilizerGroup S) (U : S) : U * U = 1 := by
  obtain ⟨P,hP⟩ := pauli_repr U.val (hS.1 U.property)
  apply Subtype.ext
  apply Subtype.ext
  change (U.val : Matrix (Qubits n) (Qubits n) ℂ) * (U.val : Matrix (Qubits n) (Qubits n) ℂ) = 1
  rcases string_sq P with h | h
  · simpa [← hP] using h
  · exact False.elim (hS.2.2 (U.val * U.val) (S.mul_mem U.property U.property) (by simpa [← hP] using h))

private lemma zero_bits_identity {n : ℕ} (S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (hS : IsStabilizerGroup S) (U : S) (P : PauliString n)
    (hP : (U.val : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix) (hz : bits P = 0) : U = 1 := by
  have ho (q : Fin n) : P.ops q = .I := by
    have hx := congrFun hz (Sum.inl q)
    have hz := congrFun hz (Sum.inr q)
    cases h : P.ops q <;> simp_all [bits, xb, zb]
  have hm : P.toMatrix = ph P.phase • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
    rw [string_eq]
    simp only [ho, Pauli.mat, tens_one]
  have hu : (U.val : Matrix (Qubits n) (Qubits n) ℂ) = ph P.phase • 1 := hP.trans hm
  have hs := stabilizer_sq S hS U
  have hs' := congrArg (fun x : S => (x.val : Matrix (Qubits n) (Qubits n) ℂ)) hs
  have hn := hS.2.2 U.val U.property
  have he : (U.val : Matrix (Qubits n) (Qubits n) ℂ) = 1 := by
    rcases phase_cases P.phase with hc | hc | hc | hc <;> rw [hc] at hu
    · simpa [ph0,ph1,ph2,ph3] using hu
    · have h := congrFun (congrFun hs' (fun _ => false)) (fun _ => false)
      norm_num [hu,ph0,ph1,ph2,ph3] at h
    · exact False.elim (hn (by simpa [ph0,ph1,ph2,ph3] using hu))
    · have h := congrFun (congrFun hs' (fun _ => false)) (fun _ => false)
      norm_num [hu,ph0,ph1,ph2,ph3] at h
  exact Subtype.ext (Subtype.ext he)

private lemma product_repr {n : ℕ} {ι H : Type*} [CommMonoid H]
    (m : H →* Matrix (Qubits n) (Qubits n) ℂ) (u : ι → H) (P : ι → PauliString n)
    (hP : ∀ i, m (u i) = (P i).toMatrix) (s : Finset ι) :
    ∃ Q : PauliString n, m (∏ i ∈ s, u i) = Q.toMatrix ∧ bits Q = ∑ i ∈ s, bits (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨emptyString n, by simp [empty_matrix], by simp [empty_bits]⟩
  | @insert i s hi ih =>
    obtain ⟨Q,hQ,hb⟩ := ih
    refine ⟨(P i).mul Q, ?_, ?_⟩
    · rw [Finset.prod_insert hi, map_mul, hP, hQ, string_mul]
    · rw [Finset.sum_insert hi, bits_mul, hb]

theorem solution (n a : ℕ)
    (g : Fin a → Matrix.unitaryGroup (Qubits n) ℂ)
    (hS : IsStabilizerGroup (Subgroup.closure (Set.range g)))
    (hcard : Nat.card (Subgroup.closure (Set.range g)) = 2 ^ a) :
    ∃ P : Fin a → PauliString n,
      (∀ i, (g i : Matrix (Qubits n) (Qubits n) ℂ) = (P i).toMatrix) ∧
      LinearIndependent (ZMod 2) (fun i =>
        Sum.elim
          (fun q => (if (P i).ops q = Pauli.X ∨ (P i).ops q = Pauli.Y then 1 else 0 : ZMod 2))
          (fun q => (if (P i).ops q = Pauli.Z ∨ (P i).ops q = Pauli.Y then 1 else 0 : ZMod 2))) := by
  classical
  let S := Subgroup.closure (Set.range g)
  let : CommGroup S := { (inferInstance : Group S) with
    mul_comm := fun x y => Subtype.ext (hS.2.1 x.val x.property y.val y.property) }
  let u : Fin a → S := fun i => ⟨g i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  have hu2 (i : Fin a) : u i * u i = 1 := stabilizer_sq S hS (u i)
  let f : (Fin a → Bool) → S := fun c => ∏ i, if c i then u i else 1
  have hf0 : f (fun _ => false) = 1 := by simp [f]
  have hfm (c d : Fin a → Bool) : f c * f d = f (fun i => xor (c i) (d i)) := by
    simp only [f, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hc : c i = true <;> by_cases hd : d i = true <;> simp_all
  have hfi (c : Fin a → Bool) : (f c)⁻¹ = f c := by
    apply inv_eq_of_mul_eq_one_right
    rw [hfm]
    simpa using hf0
  have hall (x : Matrix.unitaryGroup (Qubits n) ℂ) (hx : x ∈ S) :
      ∃ c, (f c).val = x := by
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      refine ⟨fun j => decide (j = i), ?_⟩
      have he : f (fun j => decide (j = i)) = u i := by simp [f]
      exact congrArg Subtype.val he
    | one => exact ⟨fun _ => false, congrArg Subtype.val hf0⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c,hc⟩ := hx
      obtain ⟨d,hd⟩ := hy
      refine ⟨fun i => xor (c i) (d i), ?_⟩
      rw [← hfm, Subgroup.coe_mul, hc, hd]
    | inv x _ hx =>
      obtain ⟨c,hc⟩ := hx
      refine ⟨c, ?_⟩
      rw [← hfi c, Subgroup.coe_inv, hc]
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨c,hc⟩ := hall x.val x.property
    exact ⟨c,Subtype.ext hc⟩
  have hinj : Function.Injective f :=
    (hsurj.bijective_of_nat_card_le (by simpa [Nat.card_eq_fintype_card] using hcard.ge)).1
  have hp (i : Fin a) : ∃ P : PauliString n,
      (g i : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix :=
    pauli_repr (g i) (hS.1 (Subgroup.subset_closure (Set.mem_range_self i)))
  choose P hP using hp
  refine ⟨P,hP,?_⟩
  have hbits (p : Pauli) :
      (if p = Pauli.X ∨ p = Pauli.Y then 1 else 0 : ZMod 2) = xb p ∧
      (if p = Pauli.Z ∨ p = Pauli.Y then 1 else 0 : ZMod 2) = zb p := by
    cases p <;> simp [xb,zb]
  simp only [(hbits _).1, (hbits _).2]
  change LinearIndependent (ZMod 2) (fun i => bits (P i))
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let b : Fin a → Bool := fun i => decide (c i = 1)
  let Q : Fin a → PauliString n := fun i => if b i then P i else emptyString n
  let m : S →* Matrix (Qubits n) (Qubits n) ℂ :=
    (Matrix.unitaryGroup (Qubits n) ℂ).subtype.comp S.subtype
  have hm (i : Fin a) : m (if b i then u i else 1) = (Q i).toMatrix := by
    dsimp [Q]
    split <;> simp_all [m,u,empty_matrix]
  obtain ⟨R,hR,hb⟩ := product_repr m (fun i => if b i then u i else 1) Q hm Finset.univ
  have hz : bits R = 0 := by
    rw [hb, ← hc]
    apply Finset.sum_congr rfl
    intro i _
    have he : c i = 0 ∨ c i = 1 := by
      exact zcases (c i)
    rcases he with he | he <;> simp [Q,b,he,empty_bits]
  have hf : f b = 1 := zero_bits_identity S hS (f b) R hR hz
  have hbb := hinj (hf.trans hf0.symm)
  intro i
  have hi := congrFun hbb i
  have he : c i = 0 ∨ c i = 1 := by
    exact zcases (c i)
  rcases he with he | he
  · exact he
  · simp [b,he] at hi
