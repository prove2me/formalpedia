-- Prove2me | solution 1 for QAlgorithms.DeWolf.tableau_machine_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:31:46.38712+00:00
-- url     : https://prove2.me/submissions/58ce877d-191a-4c56-a8be-8db801797e50

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer
set_option autoImplicit false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace E261
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- Tensor product of one-qubit matrices, one per wire. -/
def tens {n : ℕ} (a : Fin n → Matrix Bool Bool ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => ∏ q, a q (y q) (z q)

lemma tens_mul {n : ℕ} (a b : Fin n → Matrix Bool Bool ℂ) :
    tens a * tens b = tens (fun q => a q * b q) := by
  ext y z
  simp only [tens, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun w _ => Finset.prod_mul_distrib.symm

lemma tens_one {n : ℕ} : tens (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y z
  by_cases hyz : y = z
  · subst hyz; simp [tens, Matrix.one_apply]
  · obtain ⟨q, hq⟩ := Function.ne_iff.mp hyz
    rw [Matrix.one_apply_ne hyz]
    simp only [tens, Matrix.of_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ q) (Matrix.one_apply_ne hq)

lemma tens_conjTranspose {n : ℕ} (a : Fin n → Matrix Bool Bool ℂ) :
    (tens a).conjTranspose = tens (fun q => (a q).conjTranspose) := by
  ext y z
  simp only [tens, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]

lemma tens_update_apply {n : ℕ} (a : Fin n → Matrix Bool Bool ℂ) (q : Fin n)
    (M : Matrix Bool Bool ℂ) (y z : Qubits n) :
    tens (Function.update a q M) y z =
      M (y q) (z q) * ∏ a' ∈ Finset.univ.erase q, a a' (y a') (z a') := by
  simp only [tens, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun a' ha' => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ha')]

lemma tens_update_smul {n : ℕ} (a : Fin n → Matrix Bool Bool ℂ) (q : Fin n) (c : ℂ)
    (M : Matrix Bool Bool ℂ) :
    tens (Function.update a q (c • M)) = c • tens (Function.update a q M) := by
  ext y z
  rw [Matrix.smul_apply, tens_update_apply, tens_update_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul, mul_assoc]

lemma toMatrix_eq_tens {n : ℕ} (P : PauliString n) :
    P.toMatrix = (Complex.I ^ P.phase.val) • tens (fun q => (P.ops q).mat) := by
  ext y z
  simp [PauliString.toMatrix, tens]

lemma embed1_eq {n : ℕ} (U : Matrix Bool Bool ℂ) (q : Fin n) :
    embedOp (Gate.ofMatrix1 U).mat (wire1 q) =
      tens (Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) q U) := by
  ext y z
  rw [tens_update_apply]
  simp only [embedOp, Matrix.of_apply]
  by_cases h : ∀ a : Fin n, a ≠ q → y a = z a
  · rw [if_pos (fun a ha => h a (fun hq => ha ⟨(0 : Fin 1), hq.symm⟩))]
    show U (y q) (z q) = _
    rw [Finset.prod_eq_one, mul_one]
    intro a ha
    rw [h a (Finset.ne_of_mem_erase ha), Matrix.one_apply_eq]
  · rw [if_neg (fun H => h (fun a ha => H a (by rintro ⟨i, hi⟩; exact ha hi.symm)))]
    push Not at h
    obtain ⟨a, haq, hya⟩ := h
    have hz : ∏ a' ∈ Finset.univ.erase q, (1 : Matrix Bool Bool ℂ) (y a') (z a') = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨haq, Finset.mem_univ a⟩) (Matrix.one_apply_ne hya)
    rw [hz, mul_zero]

lemma conj_tens {n : ℕ} (b a : Fin n → Matrix Bool Bool ℂ) :
    tens b * tens a * (tens b).conjTranspose =
      tens (fun q => b q * a q * (b q).conjTranspose) := by
  rw [tens_conjTranspose, tens_mul, tens_mul]

/-- Conjugating a Pauli string by a one-wire gate `U` on wire `q`, when
`U (P_q) U† = c • R` for a one-qubit Pauli `R`. -/
lemma conj1_toMatrix {n : ℕ} (U : Matrix Bool Bool ℂ) (hU : U * U.conjTranspose = 1)
    (q : Fin n) (P : PauliString n) (c : ℂ) (R : Pauli)
    (hR : U * (P.ops q).mat * U.conjTranspose = c • R.mat) :
    embedOp (Gate.ofMatrix1 U).mat (wire1 q) * P.toMatrix *
        (embedOp (Gate.ofMatrix1 U).mat (wire1 q)).conjTranspose =
      (Complex.I ^ P.phase.val * c) •
        tens (Function.update (fun q' => (P.ops q').mat) q R.mat) := by
  rw [embed1_eq, toMatrix_eq_tens, Matrix.mul_smul, Matrix.smul_mul, conj_tens]
  have h : (fun q' => Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) q U q' * (P.ops q').mat *
      (Function.update (fun _ => (1 : Matrix Bool Bool ℂ)) q U q').conjTranspose) =
      Function.update (fun q' => (P.ops q').mat) q (c • R.mat) := by
    funext q'
    by_cases hq : q' = q
    · subst hq; simp [hR]
    · simp [Function.update_of_ne hq]
  rw [h, tens_update_smul, smul_smul]

lemma conj_list_prod {m : Type*} [Fintype m] [DecidableEq m] (U : Matrix m m ℂ)
    (hU : U.conjTranspose * U = 1) (l : List (Matrix m m ℂ)) :
    U * l.prod * U.conjTranspose = (l.map (fun A => U * A * U.conjTranspose)).prod := by
  induction l with
  | nil => simpa using mul_eq_one_comm.mp hU
  | cons A l ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [← ih]
    calc U * (A * l.prod) * U.conjTranspose
        = U * A * (U.conjTranspose * U) * l.prod * U.conjTranspose := by
          rw [hU]; simp [Matrix.mul_assoc]
      _ = U * A * U.conjTranspose * (U * l.prod * U.conjTranspose) := by
          simp [Matrix.mul_assoc]

/-- A unitary conjugation acts generator by generator on `tableauProjector`. -/
lemma conj_tableauProjector {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U.conjTranspose * U = 1) (T T' : Tableau n)
    (h : ∀ j, U * (T j).toMatrix * U.conjTranspose = (T' j).toMatrix) :
    U * tableauProjector T * U.conjTranspose = tableauProjector T' := by
  unfold tableauProjector
  rw [conj_list_prod U hU, List.map_ofFn]
  congr 2
  funext j
  simp only [Function.comp_apply]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    mul_eq_one_comm.mp hU, h j]


/-- `H Q H† = i^c R`. -/
def conjH : Pauli → ZMod 4 × Pauli
  | .I => (0, .I) | .X => (0, .Z) | .Y => (2, .Y) | .Z => (0, .X)

/-- `S Q S† = i^c R`. -/
def conjS : Pauli → ZMod 4 × Pauli
  | .I => (0, .I) | .X => (0, .Y) | .Y => (2, .X) | .Z => (0, .Z)

/-- `P Q P† = ±Q` (minus iff both are non-identity and different). -/
def conjP (P Q : Pauli) : ZMod 4 × Pauli :=
  (if P = .I ∨ Q = .I ∨ P = Q then 0 else 2, Q)

/-- The unnormalised Hadamard. -/
def H0 : Matrix Bool Bool ℂ := Matrix.of fun a b => if a && b then -1 else 1

lemma hadamard_eq : hadamard = ((Real.sqrt 2 : ℂ))⁻¹ • H0 := by
  ext a b
  cases a <;> cases b <;> simp [hadamard, H0]

lemma sqrt2_inv_sq : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma hadamard_conj (M : Matrix Bool Bool ℂ) :
    hadamard * M * hadamard.conjTranspose = (2⁻¹ : ℂ) • (H0 * M * H0.conjTranspose) := by
  rw [hadamard_eq, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  congr 1
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, sqrt2_inv_sq]

lemma conjH_spec (Q : Pauli) :
    hadamard * Q.mat * hadamard.conjTranspose =
      (Complex.I ^ (conjH Q).1.val) • (conjH Q).2.mat := by
  have h2 : ((2 : ZMod 4)).val = 2 := rfl
  rw [hadamard_conj]
  cases Q <;> ext a b <;> cases a <;> cases b <;>
    simp [conjH, H0, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.conjTranspose_apply, Matrix.one_apply, h2] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma conjS_spec (Q : Pauli) :
    phaseS * Q.mat * phaseS.conjTranspose =
      (Complex.I ^ (conjS Q).1.val) • (conjS Q).2.mat := by
  have h2 : ((2 : ZMod 4)).val = 2 := rfl
  cases Q <;> ext a b <;> cases a <;> cases b <;>
    simp [conjS, phaseS, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.conjTranspose_apply, Matrix.one_apply, h2] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma conjP_spec (P Q : Pauli) :
    P.mat * Q.mat * P.mat.conjTranspose =
      (Complex.I ^ (conjP P Q).1.val) • (conjP P Q).2.mat := by
  have h2 : ((2 : ZMod 4)).val = 2 := rfl
  cases P <;> cases Q <;> ext a b <;> cases a <;> cases b <;>
    simp [conjP, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.conjTranspose_apply, Matrix.one_apply, h2] <;> ring_nf <;> simp [Complex.I_sq] <;> ring


/-! ## Session 3: gate step (validity + projector conjugation) for all Clifford gates -/

lemma I_pow_val_add (a b : ZMod 4) :
    Complex.I ^ a.val * Complex.I ^ b.val = Complex.I ^ (a + b).val := by
  rw [← pow_add, ZMod.val_add]
  conv_lhs => rw [← Nat.mod_add_div (a.val + b.val) 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

lemma conj_cancel {m : Type*} [Fintype m] [DecidableEq m] (U : Matrix m m ℂ)
    (hU : U.conjTranspose * U = 1) (A : Matrix m m ℂ) :
    U.conjTranspose * (U * A * U.conjTranspose) * U = A := by
  simp only [← Matrix.mul_assoc]
  rw [hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]

lemma subProd_conj {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (hU : U.conjTranspose * U = 1)
    (T T' : Tableau n) (h : ∀ j, U * (T j).toMatrix * U.conjTranspose = (T' j).toMatrix)
    (s : Finset (Fin n)) :
    U * subProd T s * U.conjTranspose = subProd T' s := by
  unfold subProd
  rw [conj_list_prod U hU, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply]
  split_ifs
  · exact h i
  · rw [Matrix.mul_one, mul_eq_one_comm.mp hU]

/-- Validity transfers along a unitary conjugation that maps generators to generators. -/
lemma valid_conj {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (hU : U.conjTranspose * U = 1)
    (T T' : Tableau n) (h : ∀ j, U * (T j).toMatrix * U.conjTranspose = (T' j).toMatrix)
    (hph : ∀ j, ((T j).phase = 0 ∨ (T j).phase = 2) → ((T' j).phase = 0 ∨ (T' j).phase = 2))
    (hT : IsValidTableau T) : IsValidTableau T' := by
  obtain ⟨h1, h2, h3, h4⟩ := hT
  have hU' : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  have hmul : ∀ A B : Matrix (Qubits n) (Qubits n) ℂ, U * (A * B) * U.conjTranspose =
      (U * A * U.conjTranspose) * (U * B * U.conjTranspose) := by
    intro A B
    calc U * (A * B) * U.conjTranspose
        = U * A * (U.conjTranspose * U) * B * U.conjTranspose := by rw [hU]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  have hinj : ∀ A B : Matrix (Qubits n) (Qubits n) ℂ,
      U * A * U.conjTranspose = U * B * U.conjTranspose → A = B := by
    intro A B hAB
    rw [← conj_cancel U hU A, hAB, conj_cancel U hU B]
  refine ⟨fun j => hph j (h1 j), fun i j => ?_, fun j s hj c hc => ?_, fun s hs => ?_⟩
  · have hc := h2 i j
    unfold PauliString.Commute at hc ⊢
    rw [← h i, ← h j, ← hmul, ← hmul, hc]
  · apply h3 j s hj c
    apply hinj
    rw [h j, hc, ← subProd_conj U hU T T' h s, Matrix.mul_smul, Matrix.smul_mul]
  · apply h4 s
    apply hinj
    rw [subProd_conj U hU T T' h s, hs, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hU']

/-- Conjugating one wire of a Pauli string by a table `f`. -/
def conjPS {n : ℕ} (f : Pauli → ZMod 4 × Pauli) (q : Fin n) (P : PauliString n) : PauliString n :=
  ⟨P.phase + (f (P.ops q)).1, Function.update P.ops q (f (P.ops q)).2⟩

lemma tens_update_mat {n : ℕ} (P : PauliString n) (q : Fin n) (R : Pauli) :
    tens (Function.update (fun q' => (P.ops q').mat) q R.mat) =
      tens (fun q' => (Function.update P.ops q R q').mat) := by
  congr 1
  funext q'
  by_cases h : q' = q
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma embed1_unitary {n : ℕ} (U : Matrix Bool Bool ℂ) (hU : U.conjTranspose * U = 1) (q : Fin n) :
    (embedOp (Gate.ofMatrix1 U).mat (wire1 q)).conjTranspose *
      embedOp (Gate.ofMatrix1 U).mat (wire1 q) = 1 := by
  rw [embed1_eq, tens_conjTranspose, tens_mul, ← tens_one]
  congr 1
  funext q'
  by_cases h : q' = q
  · subst h; simp [hU]
  · simp [Function.update_of_ne h]

lemma conj1_ps {n : ℕ} (U : Matrix Bool Bool ℂ) (hU : U * U.conjTranspose = 1)
    (f : Pauli → ZMod 4 × Pauli)
    (hf : ∀ Q, U * Q.mat * U.conjTranspose = Complex.I ^ (f Q).1.val • (f Q).2.mat)
    (q : Fin n) (P : PauliString n) :
    embedOp (Gate.ofMatrix1 U).mat (wire1 q) * P.toMatrix *
        (embedOp (Gate.ofMatrix1 U).mat (wire1 q)).conjTranspose = (conjPS f q P).toMatrix := by
  rw [conj1_toMatrix U hU q P _ _ (hf (P.ops q)), tens_update_mat, toMatrix_eq_tens (conjPS f q P),
    I_pow_val_add]
  rfl

lemma gate1_step {n : ℕ} (U : Matrix Bool Bool ℂ) (hU : U * U.conjTranspose = 1)
    (f : Pauli → ZMod 4 × Pauli)
    (hf : ∀ Q, U * Q.mat * U.conjTranspose = Complex.I ^ (f Q).1.val • (f Q).2.mat)
    (hfe : ∀ Q, (f Q).1 = 0 ∨ (f Q).1 = 2) (q : Fin n) (T : Tableau n) (hT : IsValidTableau T) :
    IsValidTableau (fun j => conjPS f q (T j)) ∧
    tableauProjector (fun j => conjPS f q (T j)) =
      embedOp (Gate.ofMatrix1 U).mat (wire1 q) * tableauProjector T *
        (embedOp (Gate.ofMatrix1 U).mat (wire1 q)).conjTranspose := by
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  have hE := embed1_unitary U hU' q
  have hj : ∀ j, embedOp (Gate.ofMatrix1 U).mat (wire1 q) * (T j).toMatrix *
      (embedOp (Gate.ofMatrix1 U).mat (wire1 q)).conjTranspose = (conjPS f q (T j)).toMatrix :=
    fun j => conj1_ps U hU f hf q (T j)
  refine ⟨valid_conj _ hE T _ hj (fun j hp => ?_) hT, (conj_tableauProjector _ hE T _ hj).symm⟩
  show (T j).phase + (f ((T j).ops q)).1 = 0 ∨ (T j).phase + (f ((T j).ops q)).1 = 2
  rcases hp with h | h <;> rcases hfe ((T j).ops q) with h' | h' <;> rw [h, h'] <;> decide

lemma H0_mul : H0 * H0.conjTranspose = (2 : ℂ) • 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [H0, Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, Matrix.one_apply] <;>
    norm_num

lemma hadamard_unitary : hadamard * hadamard.conjTranspose = 1 := by
  have h := hadamard_conj 1
  rw [Matrix.mul_one, Matrix.mul_one, H0_mul, smul_smul] at h
  rw [h]
  norm_num

lemma phaseS_unitary : phaseS * phaseS.conjTranspose = 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [phaseS, Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, Matrix.one_apply]

lemma pauli_unitary (P : Pauli) : P.mat * P.mat.conjTranspose = 1 := by
  cases P <;> ext a b <;> cases a <;> cases b <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.conjTranspose_apply, Matrix.one_apply]

lemma conjH_even (Q : Pauli) : (conjH Q).1 = 0 ∨ (conjH Q).1 = 2 := by
  cases Q <;> simp [conjH]
lemma conjS_even (Q : Pauli) : (conjS Q).1 = 0 ∨ (conjS Q).1 = 2 := by
  cases Q <;> simp [conjS]
lemma conjP_even (P Q : Pauli) : (conjP P Q).1 = 0 ∨ (conjP P Q).1 = 2 := by
  unfold conjP; split_ifs <;> simp

/-! ### CNOT as a permutation matrix -/

def px : Pauli → Bool | .I => false | .X => true | .Y => true | .Z => false
def pz : Pauli → Bool | .I => false | .X => false | .Y => true | .Z => true

/-- CNOT conjugation table on (control, target) Paulis: phase, new control, new target. -/
def cnotTab (Pc Pt : Pauli) : ZMod 4 × Pauli × Pauli :=
  (if px Pc && pz Pt && (px Pt == pz Pc) then 2 else 0,
    pauliOfBits (px Pc) (xor (pz Pc) (pz Pt)), pauliOfBits (xor (px Pt) (px Pc)) (pz Pt))

lemma cnotTab_even (Pc Pt : Pauli) : (cnotTab Pc Pt).1 = 0 ∨ (cnotTab Pc Pt).1 = 2 := by
  unfold cnotTab; split_ifs <;> simp

lemma cnotTab_spec (Pc Pt : Pauli) (a b a' b' : Bool) :
    Pc.mat a a' * Pt.mat (xor b a) (xor b' a') =
      Complex.I ^ (cnotTab Pc Pt).1.val *
        ((cnotTab Pc Pt).2.1.mat a a' * (cnotTab Pc Pt).2.2.mat b b') := by
  have h2 : ((2 : ZMod 4)).val = 2 := rfl
  cases Pc <;> cases Pt <;> cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [cnotTab, px, pz, pauliOfBits, Pauli.mat, pauliX, pauliY, pauliZ, h2, Matrix.one_apply] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq])

def cnotPerm {n : ℕ} (c t : Fin n) (z : Qubits n) : Qubits n :=
  Function.update z t (xor (z t) (z c))

lemma cnotPerm_invol {n : ℕ} {c t : Fin n} (hct : c ≠ t) : Function.Involutive (cnotPerm c t) := by
  intro z
  funext q
  by_cases hq : q = t
  · subst hq; simp [cnotPerm, Function.update_of_ne hct]
  · simp [cnotPerm, Function.update_of_ne hq]

lemma embed_cnot {n : ℕ} (c t : Fin n) (hct : c ≠ t) :
    embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (wire2 c t hct) =
      Matrix.of fun y z => if y = cnotPerm c t z then (1 : ℂ) else 0 := by
  have hw0 : (wire2 c t hct) 0 = c := rfl
  have hw1 : (wire2 c t hct) 1 = t := rfl
  have hr : ∀ a, a ∈ Set.range (wire2 c t hct) ↔ a = c ∨ a = t := by
    intro a
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      exacts [⟨0, hw0⟩, ⟨1, hw1⟩]
  ext y z
  have key : ((∀ a : Fin n, a ∉ Set.range (wire2 c t hct) → y a = z a) ∧
      (y c = z c ∧ y t = xor (z t) (z c))) ↔ y = cnotPerm c t z := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      funext a
      by_cases hat : a = t
      · subst hat; simp [cnotPerm, h3]
      · rw [cnotPerm, Function.update_of_ne hat]
        by_cases hac : a = c
        · subst hac; exact h2
        · exact h1 a (by rw [hr]; tauto)
    · rintro rfl
      refine ⟨fun a ha => ?_, ?_, ?_⟩
      · rw [hr] at ha
        push Not at ha
        simp [cnotPerm, Function.update_of_ne ha.2]
      · simp [cnotPerm, Function.update_of_ne hct]
      · simp [cnotPerm, Function.update_of_ne hct]
  simp only [Matrix.of_apply]
  by_cases hk : y = cnotPerm c t z
  · rw [if_pos hk]
    have hk' := key.mpr hk
    simp only [embedOp, Matrix.of_apply]
    rw [if_pos]
    · show QAlgorithms.cnot (y c, y t) (z c, z t) = 1
      simp [QAlgorithms.cnot, hk'.2]
    · exact fun a ha => hk'.1 a ha
  · rw [if_neg hk]
    simp only [embedOp, Matrix.of_apply]
    split_ifs with hA
    · show QAlgorithms.cnot (y c, y t) (z c, z t) = 0
      simp only [QAlgorithms.cnot, Matrix.of_apply]
      rw [if_neg]
      exact fun h => hk (key.mp ⟨fun a ha => hA a ha, h⟩)
    · rfl

lemma perm_conj {n : ℕ} (σ : Qubits n → Qubits n) (hσ : Function.Involutive σ)
    (A : Matrix (Qubits n) (Qubits n) ℂ) :
    (Matrix.of fun y z => if y = σ z then (1 : ℂ) else 0) * A *
      (Matrix.of fun y z => if y = σ z then (1 : ℂ) else 0).conjTranspose = A.submatrix σ σ := by
  have hs : ∀ y w : Qubits n, (y = σ w) ↔ (w = σ y) :=
    fun y w => ⟨fun h => by rw [h, hσ], fun h => by rw [h, hσ]⟩
  have hst : ∀ (p : Prop) [Decidable p], star (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
    intro p _; split_ifs <;> simp
  ext y z
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    hst]
  rw [Finset.sum_eq_single (σ z)]
  · rw [if_pos (hσ z).symm, mul_one, Finset.sum_eq_single (σ y)]
    · rw [if_pos (hσ y).symm, one_mul]
    · intro b _ hb
      rw [if_neg (fun h => hb (by rw [h, hσ])), zero_mul]
    · simp
  · intro b _ hb
    rw [if_neg (fun h => hb (by rw [h, hσ])), mul_zero]
  · simp

/-- CNOT conjugation of a Pauli string. -/
def cnotPS {n : ℕ} (c t : Fin n) (P : PauliString n) : PauliString n :=
  ⟨P.phase + (cnotTab (P.ops c) (P.ops t)).1,
    Function.update (Function.update P.ops c (cnotTab (P.ops c) (P.ops t)).2.1) t
      (cnotTab (P.ops c) (P.ops t)).2.2⟩

lemma prod_two {n : ℕ} {c t : Fin n} (hct : c ≠ t) (g : Fin n → ℂ) :
    ∏ q, g q = g c * (g t * ∏ q ∈ (Finset.univ.erase c).erase t, g q) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hct.symm, Finset.mem_univ t⟩)]

lemma cnot_toMatrix {n : ℕ} (c t : Fin n) (hct : c ≠ t) (P : PauliString n) :
    P.toMatrix.submatrix (cnotPerm c t) (cnotPerm c t) = (cnotPS c t P).toMatrix := by
  have hrest : ∀ y z : Qubits n,
      ∏ q ∈ (Finset.univ.erase c).erase t, (P.ops q).mat (cnotPerm c t y q) (cnotPerm c t z q) =
      ∏ q ∈ (Finset.univ.erase c).erase t, ((cnotPS c t P).ops q).mat (y q) (z q) := by
    intro y z
    refine Finset.prod_congr rfl fun q hq => ?_
    have h1 : q ≠ c := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hq)
    have h2 : q ≠ t := Finset.ne_of_mem_erase hq
    simp [cnotPerm, cnotPS, Function.update_of_ne h1, Function.update_of_ne h2]
  have hco : (cnotPS c t P).ops c = (cnotTab (P.ops c) (P.ops t)).2.1 := by
    simp [cnotPS, Function.update_of_ne hct]
  have hto : (cnotPS c t P).ops t = (cnotTab (P.ops c) (P.ops t)).2.2 := by
    simp [cnotPS]
  have hph : (cnotPS c t P).phase = P.phase + (cnotTab (P.ops c) (P.ops t)).1 := rfl
  have hyc : ∀ y : Qubits n, cnotPerm c t y c = y c := fun y => by
    simp [cnotPerm, Function.update_of_ne hct]
  have hyt : ∀ y : Qubits n, cnotPerm c t y t = xor (y t) (y c) := fun y => by
    simp [cnotPerm]
  ext y z
  simp only [Matrix.submatrix_apply, PauliString.toMatrix, Matrix.of_apply]
  rw [prod_two hct, prod_two hct, hrest, hco, hto, hph, ← I_pow_val_add, hyc, hyc, hyt, hyt]
  have hs := cnotTab_spec (P.ops c) (P.ops t) (y c) (y t) (z c) (z t)
  linear_combination (Complex.I ^ P.phase.val *
    ∏ q ∈ (Finset.univ.erase c).erase t, ((cnotPS c t P).ops q).mat (y q) (z q)) * hs

lemma cnot_step {n : ℕ} (c t : Fin n) (hct : c ≠ t) (T : Tableau n) (hT : IsValidTableau T) :
    IsValidTableau (fun j => cnotPS c t (T j)) ∧
    tableauProjector (fun j => cnotPS c t (T j)) =
      embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (wire2 c t hct) * tableauProjector T *
        (embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (wire2 c t hct)).conjTranspose := by
  have hinv := cnotPerm_invol hct
  have hE1 : embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (wire2 c t hct) *
      (embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (wire2 c t hct)).conjTranspose = 1 := by
    have h1 := perm_conj _ hinv 1
    rw [Matrix.mul_one] at h1
    rw [embed_cnot, h1]
    ext y z
    simp [Matrix.one_apply, hinv.injective.eq_iff]
  have hE := mul_eq_one_comm.mp hE1
  have hj : ∀ j, embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (wire2 c t hct) * (T j).toMatrix *
      (embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (wire2 c t hct)).conjTranspose =
        (cnotPS c t (T j)).toMatrix := fun j => by
    rw [embed_cnot, perm_conj _ hinv, cnot_toMatrix c t hct]
  refine ⟨valid_conj _ hE T _ hj (fun j hp => ?_) hT, (conj_tableauProjector _ hE T _ hj).symm⟩
  show (T j).phase + (cnotTab ((T j).ops c) ((T j).ops t)).1 = 0 ∨
    (T j).phase + (cnotTab ((T j).ops c) ((T j).ops t)).1 = 2
  rcases hp with h | h <;> rcases cnotTab_even ((T j).ops c) ((T j).ops t) with h' | h' <;>
    rw [h, h'] <;> decide

/-- The tableau update for a gate (measurements are handled separately). -/
def updG {n : ℕ} : CliffordOp n → Tableau n → Tableau n
  | .pauli q P, T => fun j => conjPS (conjP P) q (T j)
  | .h q, T => fun j => conjPS conjH q (T j)
  | .s q, T => fun j => conjPS conjS q (T j)
  | .cnot c t _, T => fun j => cnotPS c t (T j)
  | .measure _, T => T

/-- GATE HALF of ChildStepQ: every Clifford gate preserves validity and conjugates the projector. -/
theorem gate_step {n : ℕ} (op : CliffordOp n) (T : Tableau n) (hT : IsValidTableau T)
    (hop : ∀ M, op ≠ .measure M) :
    IsValidTableau (updG op T) ∧
      tableauProjector (updG op T) = op.mat * tableauProjector T * op.mat.conjTranspose := by
  cases op with
  | pauli q P => exact gate1_step P.mat (pauli_unitary P) (conjP P) (conjP_spec P) (conjP_even P) q T hT
  | h q => exact gate1_step hadamard hadamard_unitary conjH conjH_spec conjH_even q T hT
  | s q => exact gate1_step phaseS phaseS_unitary conjS conjS_spec conjS_even q T hT
  | cnot c t hct => exact cnot_step c t hct T hT
  | measure M => exact absurd rfl (hop M)


/-! ## Session 3: foundations for the measurement half (Pauli products, traces, expansion) -/

lemma pmul_spec (P Q : Pauli) :
    P.mat * Q.mat = Complex.I ^ (Pauli.mul P Q).1.val • (Pauli.mul P Q).2.mat := by
  have h1 : ((1 : ZMod 4)).val = 1 := rfl
  have h3 : ((3 : ZMod 4)).val = 3 := rfl
  cases P <;> cases Q <;> ext a b <;> cases a <;> cases b <;>
    simp [Pauli.mul, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.one_apply, h1, h3] <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf)

lemma tens_smul {n : ℕ} (c : Fin n → ℂ) (a : Fin n → Matrix Bool Bool ℂ) :
    tens (fun q => c q • a q) = (∏ q, c q) • tens a := by
  ext y z
  simp [tens, Finset.prod_mul_distrib]

lemma I_pow_sum {ι : Type*} (s : Finset ι) (k : ι → ZMod 4) :
    ∏ q ∈ s, Complex.I ^ (k q).val = Complex.I ^ (∑ q ∈ s, k q).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, I_pow_val_add]

lemma toMatrix_mul {n : ℕ} (P Q : PauliString n) :
    (P.mul Q).toMatrix = P.toMatrix * Q.toMatrix := by
  rw [toMatrix_eq_tens P, toMatrix_eq_tens Q, toMatrix_eq_tens (P.mul Q), Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, tens_mul]
  have h : (fun q => (P.ops q).mat * (Q.ops q).mat) =
      fun q => Complex.I ^ (Pauli.mul (P.ops q) (Q.ops q)).1.val •
        (Pauli.mul (P.ops q) (Q.ops q)).2.mat := funext fun q => pmul_spec _ _
  rw [h, tens_smul, smul_smul, I_pow_sum, I_pow_val_add, I_pow_val_add]
  rfl

lemma trace_tens {n : ℕ} (a : Fin n → Matrix Bool Bool ℂ) :
    (tens a).trace = ∏ q, (a q).trace := by
  simp only [Matrix.trace, Matrix.diag, tens, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma pauli_trace (P : Pauli) : P.mat.trace = if P = .I then 2 else 0 := by
  cases P <;> simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.trace, Fintype.sum_bool] <;> norm_num

lemma trace_toMatrix_of_ne {n : ℕ} (P : PauliString n) (q : Fin n) (hq : P.ops q ≠ .I) :
    P.toMatrix.trace = 0 := by
  rw [toMatrix_eq_tens, Matrix.trace_smul, trace_tens,
    Finset.prod_eq_zero (Finset.mem_univ q) (by rw [pauli_trace, if_neg hq]), smul_zero]

lemma toMatrix_of_allI {n : ℕ} (P : PauliString n) (h : ∀ q, P.ops q = .I) :
    P.toMatrix = Complex.I ^ P.phase.val • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  rw [toMatrix_eq_tens, ← tens_one]
  congr 2
  funext q
  rw [h q]
  rfl

/-- Noncommutative expansion of an ordered product of `1 + A j`. -/
lemma ofFn_prod_one_add {R : Type*} [Ring R] : ∀ (n : ℕ) (A : Fin n → R),
    (List.ofFn fun j => 1 + A j).prod =
      ∑ b : Fin n → Bool, (List.ofFn fun i => if b i then A i else 1).prod
  | 0, A => by simp
  | n + 1, A => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_one_add n (fun j => A j.succ),
      ← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
      add_mul, one_mul, Finset.mul_sum, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun b _ => ?_ <;>
      simp [Fin.consEquiv, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]


/-! ## Session 3: trace of the tableau projector is 1 -/

def oneP (n : ℕ) : PauliString n := ⟨0, fun _ => .I⟩

lemma oneP_toMatrix (n : ℕ) : (oneP n).toMatrix = 1 := by
  rw [toMatrix_of_allI _ (fun _ => rfl)]
  simp [oneP]

lemma list_prod_toMatrix {n : ℕ} : ∀ L : List (PauliString n),
    (L.map PauliString.toMatrix).prod = (L.foldr PauliString.mul (oneP n)).toMatrix
  | [] => by simp [oneP_toMatrix]
  | P :: L => by simp [list_prod_toMatrix L, toMatrix_mul]

lemma subProd_eq_toMatrix {n : ℕ} (T : Tableau n) (s : Finset (Fin n)) :
    ∃ P : PauliString n, subProd T s = P.toMatrix := by
  refine ⟨(List.ofFn fun i => if i ∈ s then T i else oneP n).foldr PauliString.mul (oneP n), ?_⟩
  rw [← list_prod_toMatrix, List.map_ofFn]
  unfold subProd
  congr 2
  funext i
  simp only [Function.comp_apply]
  split_ifs <;> simp [oneP_toMatrix]

lemma toMatrix_sq {n : ℕ} (P : PauliString n) (hP : P.phase = 0 ∨ P.phase = 2) :
    P.toMatrix * P.toMatrix = 1 := by
  have hs : ∀ q, (Pauli.mul (P.ops q) (P.ops q)).1 = 0 := fun q => by cases P.ops q <;> rfl
  have hI : ∀ q, (P.mul P).ops q = .I := fun q => by
    show (Pauli.mul (P.ops q) (P.ops q)).2 = .I
    cases P.ops q <;> rfl
  have hph : (P.mul P).phase = 0 := by
    show P.phase + P.phase + ∑ q, (Pauli.mul (P.ops q) (P.ops q)).1 = 0
    simp only [hs, Finset.sum_const_zero, add_zero]
    rcases hP with h | h <;> rw [h] <;> decide
  rw [← toMatrix_mul, toMatrix_of_allI _ hI, hph]
  simp

lemma ofFn_prod_move {R : Type*} [Monoid R] : ∀ (n : ℕ) (f : Fin n → R) (j : Fin n),
    (∀ i, Commute (f j) (f i)) →
      (List.ofFn f).prod = f j * (List.ofFn (Function.update f j 1)).prod
  | 0, _, j, _ => j.elim0
  | n + 1, f, j, hc => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    cases j using Fin.cases with
    | zero =>
      simp [Function.update_of_ne (Fin.succ_ne_zero _)]
    | succ j' =>
      have ih := ofFn_prod_move n (fun i => f i.succ) j' (fun i => hc i.succ)
      have h0 : Function.update f j'.succ 1 0 = f 0 :=
        Function.update_of_ne (Fin.succ_ne_zero j').symm _ _
      have hs : (fun i => Function.update f j'.succ 1 i.succ) =
          Function.update (fun i => f i.succ) j' 1 :=
        Function.update_comp_eq_of_injective f (Fin.succ_injective n) j' 1
      rw [h0, hs, ih, ← mul_assoc, ← mul_assoc, (hc 0).eq]

lemma subProd_erase {n : ℕ} (T : Tableau n) (hc : ∀ i j, (T i).Commute (T j))
    (s : Finset (Fin n)) (j : Fin n) (hj : j ∈ s) :
    subProd T s = (T j).toMatrix * subProd T (s.erase j) := by
  unfold subProd
  have hf : Function.update (fun i => if i ∈ s then (T i).toMatrix else 1) j 1 =
      fun i => if i ∈ s.erase j then (T i).toMatrix else 1 := by
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi, Finset.mem_erase, hi]
  rw [ofFn_prod_move n _ j, hf, if_pos hj]
  intro i
  simp only [if_pos hj]
  split_ifs
  · exact hc j i
  · exact Commute.one_right _

lemma trace_subProd {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (s : Finset (Fin n))
    (hs : s.Nonempty) : (subProd T s).trace = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hT
  obtain ⟨P, hP⟩ := subProd_eq_toMatrix T s
  by_cases hI : ∀ q, P.ops q = .I
  · exfalso
    obtain ⟨j, hj⟩ := hs
    have hR := subProd_erase T h2 s j hj
    rw [hP, toMatrix_of_allI P hI] at hR
    have hsq := toMatrix_sq (T j) (h1 j)
    have hR' : subProd T (s.erase j) = Complex.I ^ P.phase.val • (T j).toMatrix := by
      have := congrArg (fun X => (T j).toMatrix * X) hR
      simp only [Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hsq, Matrix.one_mul] at this
      exact this.symm
    apply h3 j (s.erase j) (Finset.notMem_erase j s) (-P.phase)
    rw [hR', smul_smul, I_pow_val_add, neg_add_cancel]
    simp
  · push Not at hI
    obtain ⟨q, hq⟩ := hI
    rw [hP, trace_toMatrix_of_ne P q hq]

lemma ofFn_prod_smul {m : Type*} [Fintype m] [DecidableEq m] (c : ℂ) :
    ∀ (n : ℕ) (B : Fin n → Matrix m m ℂ),
      (List.ofFn fun j => c • B j).prod = c ^ n • (List.ofFn B).prod
  | 0, B => by simp
  | n + 1, B => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_smul c n, List.ofFn_succ, List.prod_cons,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ, mul_comm]

/-- For a valid tableau, `tr Π_j (I + T_j)/2 = 1`. -/
theorem trace_tableauProjector {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) :
    (tableauProjector T).trace = 1 := by
  unfold tableauProjector
  rw [ofFn_prod_smul, ofFn_prod_one_add, Matrix.trace_smul, Matrix.trace_sum,
    Finset.sum_eq_single (fun _ => false)]
  · simp [Matrix.trace_one, Fintype.card_fun]
  · intro b _ hb
    obtain ⟨i, hi⟩ : ∃ i, b i = true := by
      by_contra h
      push Not at h
      exact hb (funext fun i => by simpa using h i)
    have := trace_subProd T hT (Finset.univ.filter fun i => b i = true) ⟨i, by simp [hi]⟩
    unfold subProd at this
    simpa using this
  · simp


/-! ## Session 3: projector algebra for a valid tableau -/

end E261

set_option autoImplicit false
set_option linter.all false

namespace E261P
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-! Part A of ChildP (tableau_machine_coupling): the deterministic rho-level coupling.
The sigma-level loop of the simulator, read through `tableauProjector ∘ tab`, is the iterate of a
rho-level map `gR` on (rho, transcript, coins). -/

noncomputable def Pr {n : ℕ} (M : Fin n → Pauli) (β : Bool) : Matrix (Qubits n) (Qubits n) ℂ :=
  (2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩)

open scoped Classical in
noncomputable def bet {n : ℕ} (ρ : Matrix (Qubits n) (Qubits n) ℂ) (M : Fin n → Pauli) (c : Bool) :
    Bool :=
  if (Pr M false * ρ).trace = 1 then false else if (Pr M true * ρ).trace = 1 then true else c

noncomputable def gR (F : MCCFamily) (n : ℕ) (r : List Bool) :
    Matrix (Qubits n) (Qubits n) ℂ × List (Option Bool) × List Bool →
    Matrix (Qubits n) (Qubits n) ℂ × List (Option Bool) × List Bool := fun st =>
  match F.ctrl n r st.2.1 with
  | none => st
  | some (.measure M) =>
      ((Pr M (bet st.1 M (st.2.2.headD false)) * st.1).trace⁻¹ •
        (Pr M (bet st.1 M (st.2.2.headD false)) * st.1 * Pr M (bet st.1 M (st.2.2.headD false))),
       st.2.1 ++ [some (bet st.1 M (st.2.2.headD false))], st.2.2.tail)
  | some o => (o.mat * st.1 * o.mat.conjTranspose, st.2.1 ++ [none], st.2.2)

def stepS {σ : Type} (F : MCCFamily) (n : ℕ) (r : List Bool)
    (upd : CliffordOp n → σ → Bool → σ × Option Bool) :
    σ × List (Option Bool) × List Bool → σ × List (Option Bool) × List Bool := fun st =>
  match F.ctrl n r st.2.1 with
  | none => st
  | some o => ((upd o st.1 (st.2.2.headD false)).1, st.2.1 ++ [(upd o st.1 (st.2.2.headD false)).2],
      match o with
      | .measure _ => st.2.2.tail
      | _ => st.2.2)

lemma Pr_add {n : ℕ} (M : Fin n → Pauli) : Pr M false + Pr M true = 1 := by
  ext i j
  simp only [Pr, Matrix.add_apply, Matrix.smul_apply, Bool.false_eq_true, if_false, if_true,
    one_smul, neg_smul, smul_eq_mul]
  simp only [Matrix.add_apply, Matrix.neg_apply]
  ring

lemma trace_Pr_add {n : ℕ} (M : Fin n → Pauli) (ρ : Matrix (Qubits n) (Qubits n) ℂ)
    (hρ : ρ.trace = 1) : (Pr M false * ρ).trace + (Pr M true * ρ).trace = 1 := by
  rw [← Matrix.trace_add, ← add_mul, Pr_add, one_mul, hρ]

lemma bet_eq {n : ℕ} (M : Fin n → Pauli) (ρ : Matrix (Qubits n) (Qubits n) ℂ)
    (hρ : ρ.trace = 1) (b β : Bool)
    (hcase : ((Pr M β * ρ).trace = 1) ∨ ((Pr M true * ρ).trace = 2⁻¹ ∧ β = b)) :
    bet ρ M b = β := by
  have hs := trace_Pr_add M ρ hρ
  rcases hcase with h1 | ⟨h2, rfl⟩
  · cases β
    · simp [bet, h1]
    · have h0 : (Pr M false * ρ).trace = 0 := by rw [h1] at hs; linear_combination hs
      simp [bet, h1, h0]
  · have h0 : (Pr M false * ρ).trace = 2⁻¹ := by rw [h2] at hs; linear_combination hs
    have hne : (2⁻¹ : ℂ) ≠ 1 := by norm_num
    simp [bet, h0, h2, hne]

theorem step_couple {σ : Type} (F : MCCFamily) (n : ℕ) (r : List Bool)
    (upd : CliffordOp n → σ → Bool → σ × Option Bool) (tab : σ → Tableau n) (Inv : σ → Prop)
    (hinv : ∀ op s b, Inv s → Inv (upd op s b).1)
    (htr : ∀ s, Inv s → (tableauProjector (tab s)).trace = 1)
    (hgate : ∀ (op : CliffordOp n) s b, Inv s → (∀ M, op ≠ .measure M) →
      (upd op s b).2 = none ∧
      tableauProjector (tab (upd op s b).1) = op.mat * tableauProjector (tab s) * op.mat.conjTranspose)
    (hmeas : ∀ (M : Fin n → Pauli) s b, Inv s →
      ∃ β, (upd (.measure M) s b).2 = some β ∧
        ((Pr M β * tableauProjector (tab s)).trace = 1 ∨
          ((Pr M true * tableauProjector (tab s)).trace = 2⁻¹ ∧ β = b)) ∧
        tableauProjector (tab (upd (.measure M) s b).1) =
          (Pr M β * tableauProjector (tab s)).trace⁻¹ •
            (Pr M β * tableauProjector (tab s) * Pr M β))
    (s : σ) (h : List (Option Bool)) (c : List Bool) (hs : Inv s) :
    Inv (stepS F n r upd (s, h, c)).1 ∧
      (tableauProjector (tab (stepS F n r upd (s, h, c)).1), (stepS F n r upd (s, h, c)).2.1,
        (stepS F n r upd (s, h, c)).2.2) = gR F n r (tableauProjector (tab s), h, c) := by
  rcases hc : F.ctrl n r h with _ | o
  · simp only [stepS, gR, hc, and_true]
    exact hs
  · rcases o with ⟨q, P⟩ | q | q | ⟨c1, t, hct⟩ | M
    · obtain ⟨h1, h2⟩ := hgate (.pauli q P) s (c.headD false) hs (by intro M hh; cases hh)
      refine ⟨by simp only [stepS, hc]; exact hinv _ _ _ hs, ?_⟩
      simp only [stepS, gR, hc, h1, h2]
    · obtain ⟨h1, h2⟩ := hgate (.h q) s (c.headD false) hs (by intro M hh; cases hh)
      refine ⟨by simp only [stepS, hc]; exact hinv _ _ _ hs, ?_⟩
      simp only [stepS, gR, hc, h1, h2]
    · obtain ⟨h1, h2⟩ := hgate (.s q) s (c.headD false) hs (by intro M hh; cases hh)
      refine ⟨by simp only [stepS, hc]; exact hinv _ _ _ hs, ?_⟩
      simp only [stepS, gR, hc, h1, h2]
    · obtain ⟨h1, h2⟩ := hgate (.cnot c1 t hct) s (c.headD false) hs (by intro M hh; cases hh)
      refine ⟨by simp only [stepS, hc]; exact hinv _ _ _ hs, ?_⟩
      simp only [stepS, gR, hc, h1, h2]
    · obtain ⟨β, h1, hcase, h2⟩ := hmeas M s (c.headD false) hs
      have hb := bet_eq M _ (htr s hs) (c.headD false) β hcase
      refine ⟨by simp only [stepS, hc]; exact hinv _ _ _ hs, ?_⟩
      simp only [stepS, gR, hc, h1, h2, hb]

theorem iter_couple {σ : Type} (F : MCCFamily) (n : ℕ) (r : List Bool)
    (upd : CliffordOp n → σ → Bool → σ × Option Bool) (tab : σ → Tableau n) (Inv : σ → Prop)
    (hinv : ∀ op s b, Inv s → Inv (upd op s b).1)
    (htr : ∀ s, Inv s → (tableauProjector (tab s)).trace = 1)
    (hgate : ∀ (op : CliffordOp n) s b, Inv s → (∀ M, op ≠ .measure M) →
      (upd op s b).2 = none ∧
      tableauProjector (tab (upd op s b).1) = op.mat * tableauProjector (tab s) * op.mat.conjTranspose)
    (hmeas : ∀ (M : Fin n → Pauli) s b, Inv s →
      ∃ β, (upd (.measure M) s b).2 = some β ∧
        ((Pr M β * tableauProjector (tab s)).trace = 1 ∨
          ((Pr M true * tableauProjector (tab s)).trace = 2⁻¹ ∧ β = b)) ∧
        tableauProjector (tab (upd (.measure M) s b).1) =
          (Pr M β * tableauProjector (tab s)).trace⁻¹ •
            (Pr M β * tableauProjector (tab s) * Pr M β))
    (k : ℕ) : ∀ (s : σ) (h : List (Option Bool)) (c : List Bool), Inv s →
    Inv ((stepS F n r upd)^[k] (s, h, c)).1 ∧
      (tableauProjector (tab ((stepS F n r upd)^[k] (s, h, c)).1),
        ((stepS F n r upd)^[k] (s, h, c)).2.1, ((stepS F n r upd)^[k] (s, h, c)).2.2) =
        (gR F n r)^[k] (tableauProjector (tab s), h, c) := by
  induction k with
  | zero => intro s h c hs; exact ⟨hs, rfl⟩
  | succ k ih =>
    intro s h c hs
    obtain ⟨hi, he⟩ := step_couple F n r upd tab Inv hinv htr hgate hmeas s h c hs
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← he]
    exact ih _ _ _ hi

end E261P

namespace E261P
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-! Part B0: Born-rule identities for pure densities. -/

lemma pureDensity_act {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    pureDensity (act A ψ) = A * pureDensity ψ * A.conjTranspose := by
  ext a b
  simp only [pureDensity, act, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, PiLp.toLp_apply, map_sum, map_mul]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [RCLike.star_def]
  ring

lemma trace_pureDensity {ι : Type} [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    (pureDensity ψ).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

lemma pureDensity_real_smul {ι : Type} (t : ℝ) (ψ : EuclideanSpace ℂ ι) :
    pureDensity (t • ψ) = ((t ^ 2 : ℝ) : ℂ) • pureDensity ψ := by
  ext a b
  simp only [pureDensity, Matrix.of_apply, Matrix.smul_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.real_smul, map_mul, Complex.conj_ofReal]
  push_cast; ring

/-- Born rule: for `P` with `Pᴴ P = P`, `‖Pψ‖² = tr(P ρ)`. -/
lemma born {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ)
    (hP : P.conjTranspose * P = P) (ψ : EuclideanSpace ℂ ι) :
    ((‖act P ψ‖ ^ 2 : ℝ) : ℂ) = (P * pureDensity ψ).trace := by
  rw [← trace_pureDensity, pureDensity_act, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP]

/-- Post-measurement state: `|ψ'⟩⟨ψ'| = tr(Pρ)⁻¹ P ρ P` for `P` Hermitian idempotent. -/
lemma pureDensity_post {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ)
    (hH : P.conjTranspose = P) (hI : P * P = P) (ψ : EuclideanSpace ℂ ι) :
    pureDensity ((‖act P ψ‖⁻¹ : ℝ) • act P ψ) =
      (P * pureDensity ψ).trace⁻¹ • (P * pureDensity ψ * P) := by
  have hP : P.conjTranspose * P = P := by rw [hH, hI]
  rw [pureDensity_real_smul, pureDensity_act, hH, ← born P hP ψ]
  congr 1
  push_cast
  rw [inv_pow]

end E261P

namespace E261P
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-! Part B1: the measurement projectors and the coin law. -/

def tensP {n : ℕ} (a : Fin n → Matrix Bool Bool ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => ∏ q, a q (y q) (z q)

lemma tensP_mul {n : ℕ} (a b : Fin n → Matrix Bool Bool ℂ) :
    tensP a * tensP b = tensP (fun q => a q * b q) := by
  ext y z
  simp only [tensP, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun w _ => Finset.prod_mul_distrib.symm

lemma tensP_one {n : ℕ} : tensP (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y z
  by_cases hyz : y = z
  · subst hyz; simp [tensP, Matrix.one_apply]
  · obtain ⟨q, hq⟩ := Function.ne_iff.mp hyz
    rw [Matrix.one_apply_ne hyz]
    simp only [tensP, Matrix.of_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ q) (Matrix.one_apply_ne hq)

lemma tensP_conjTranspose {n : ℕ} (a : Fin n → Matrix Bool Bool ℂ) :
    (tensP a).conjTranspose = tensP (fun q => (a q).conjTranspose) := by
  ext y z
  simp only [tensP, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]

lemma pauli_herm (P : Pauli) : P.mat.conjTranspose = P.mat := by
  cases P <;> ext a b <;> cases a <;> cases b <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

lemma pauli_sq (P : Pauli) : P.mat * P.mat = 1 := by
  cases P <;> ext a b <;> cases a <;> cases b <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply]

lemma X_eq {n : ℕ} (M : Fin n → Pauli) :
    PauliString.toMatrix (⟨0, M⟩ : PauliString n) = tensP (fun q => (M q).mat) := by
  ext y z
  simp [PauliString.toMatrix, tensP]

lemma X_herm {n : ℕ} (M : Fin n → Pauli) :
    (PauliString.toMatrix (⟨0, M⟩ : PauliString n)).conjTranspose =
      PauliString.toMatrix (⟨0, M⟩ : PauliString n) := by
  rw [X_eq, tensP_conjTranspose]
  simp only [pauli_herm]

lemma X_sq {n : ℕ} (M : Fin n → Pauli) :
    PauliString.toMatrix (⟨0, M⟩ : PauliString n) * PauliString.toMatrix (⟨0, M⟩ : PauliString n) = 1 := by
  rw [X_eq, tensP_mul]
  simp only [pauli_sq]
  exact tensP_one

lemma Pr_herm {n : ℕ} (M : Fin n → Pauli) (β : Bool) : (Pr M β).conjTranspose = Pr M β := by
  cases β <;> simp [Pr, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, X_herm]

lemma Pr_idem {n : ℕ} (M : Fin n → Pauli) (β : Bool) : Pr M β * Pr M β = Pr M β := by
  have key : ∀ c : ℤ, c * c = 1 →
      ((2⁻¹ : ℂ) • (1 + c • PauliString.toMatrix (⟨0, M⟩ : PauliString n))) *
        ((2⁻¹ : ℂ) • (1 + c • PauliString.toMatrix (⟨0, M⟩ : PauliString n))) =
        (2⁻¹ : ℂ) • (1 + c • PauliString.toMatrix (⟨0, M⟩ : PauliString n)) := by
    intro c hc2
    have hQ : (c • PauliString.toMatrix (⟨0, M⟩ : PauliString n)) *
        (c • PauliString.toMatrix (⟨0, M⟩ : PauliString n)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, X_sq, hc2, one_smul]
    have h2 : (1 + c • PauliString.toMatrix (⟨0, M⟩ : PauliString n)) *
        (1 + c • PauliString.toMatrix (⟨0, M⟩ : PauliString n)) =
        (2 : ℂ) • (1 + c • PauliString.toMatrix (⟨0, M⟩ : PauliString n)) := by
      simp only [add_mul, mul_add, hQ, one_mul, mul_one]
      rw [two_smul]
      abel
    rw [Matrix.smul_mul, Matrix.mul_smul, h2, smul_smul, smul_smul]
    norm_num
  unfold Pr
  cases β
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact key 1 (by norm_num)
  · simp only [↓reduceIte]
    exact key (-1) (by norm_num)

/-- The coin law: on reachable states, the simulator's coin-driven outcome has the Born law. -/
lemma coin {n : ℕ} (M : Fin n → Pauli) (ψ : EuclideanSpace ℂ (Qubits n))
    (htr : (pureDensity ψ).trace = 1)
    (hcase : (Pr M false * pureDensity ψ).trace = 1 ∨ (Pr M true * pureDensity ψ).trace = 1 ∨
      (Pr M true * pureDensity ψ).trace = 2⁻¹) :
    (PMF.uniformOfFintype Bool).map (bet (pureDensity ψ) M) =
      PMF.bernoulli (min 1 (Real.toNNReal (‖act (Pr M true) ψ‖ ^ 2))) (min_le_left _ _) := by
  have hs := trace_Pr_add M _ htr
  have hb := born (Pr M true) (by rw [Pr_herm, Pr_idem]) ψ
  have hne : (2⁻¹ : ℂ) ≠ 1 := by norm_num
  rcases hcase with h0 | h1 | h2
  · have h1 : (Pr M true * pureDensity ψ).trace = 0 := by linear_combination hs - h0
    have ht : ‖act (Pr M true) ψ‖ ^ 2 = 0 := by rw [h1] at hb; exact_mod_cast hb
    have hbet : bet (pureDensity ψ) M = fun _ => false := funext fun c => by simp [bet, h0]
    rw [hbet, show (fun _ : Bool => false) = Function.const Bool false from rfl, PMF.map_const, ht]
    ext b; cases b <;> simp [PMF.bernoulli_apply]
  · have h0 : (Pr M false * pureDensity ψ).trace = 0 := by linear_combination hs - h1
    have ht : ‖act (Pr M true) ψ‖ ^ 2 = 1 := by rw [h1] at hb; exact_mod_cast hb
    have hbet : bet (pureDensity ψ) M = fun _ => true := funext fun c => by simp [bet, h0, h1]
    rw [hbet, show (fun _ : Bool => true) = Function.const Bool true from rfl, PMF.map_const, ht]
    ext b; cases b <;> simp [PMF.bernoulli_apply]
  · have h0 : (Pr M false * pureDensity ψ).trace = 2⁻¹ := by linear_combination hs - h2
    have ht : ‖act (Pr M true) ψ‖ ^ 2 = 2⁻¹ := by
      apply Complex.ofReal_injective; rw [hb, h2]; push_cast; ring
    have hbet : bet (pureDensity ψ) M = id := funext fun c => by simp [bet, h0, h2, hne]
    rw [hbet, PMF.map_id, ht]
    have hm : min 1 (Real.toNNReal 2⁻¹) = 2⁻¹ := by
      rw [Real.toNNReal_inv, Real.toNNReal_ofNat]
      exact min_eq_right (by norm_num)
    ext b
    cases b <;> simp [PMF.bernoulli_apply, PMF.uniformOfFintype_apply, hm]
    all_goals norm_num
end E261P

namespace E261P
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-! Part B2: uniform splitting, the front-recursive run, and the run coupling. -/

lemma unif_map_bij {γ δ : Type} [Fintype γ] [Nonempty γ] [Fintype δ] [Nonempty δ]
    (p : γ → δ) (hp : Function.Bijective p) :
    (PMF.uniformOfFintype γ).map p = PMF.uniformOfFintype δ := by
  ext d
  obtain ⟨c, rfl⟩ := hp.2 d
  rw [PMF.map_apply, tsum_eq_single c]
  · rw [if_pos rfl]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_of_bijective hp]
  · intro x hx
    exact if_neg (fun h => hx (hp.1 h.symm))

lemma unif_prod {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).map (Prod.mk a) := by
  ext ⟨a, b⟩
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply, tsum_eq_single b]
    · rw [if_pos rfl]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
      rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
    · intro b' hb
      exact if_neg (fun h => hb (Prod.mk.inj h).2.symm)
  · intro a' ha
    rw [PMF.map_apply]
    simp [Ne.symm ha]

lemma unif_split {γ α β ε : Type} [Fintype γ] [Nonempty γ] [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (p : γ → α × β) (hp : Function.Bijective p) (g : α × β → ε) :
    (PMF.uniformOfFintype γ).map (fun c => g (p c)) =
      (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).map fun b => g (a, b) := by
  rw [show (fun c => g (p c)) = g ∘ p from rfl, ← PMF.map_comp, unif_map_bij p hp, unif_prod,
    PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp]
  rfl

lemma cons_bij (L : ℕ) :
    Function.Bijective (fun c : Fin (L + 1) → Bool => (c 0, fun i : Fin L => c i.succ)) := by
  constructor
  · intro c c' h
    simp only [Prod.mk.injEq] at h
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact h.1
    · exact congrFun h.2 i
  · rintro ⟨a, b⟩
    exact ⟨Fin.cons a b, by simp⟩

lemma app_bij (R L : ℕ) : Function.Bijective (fun c : Fin (R + L) → Bool =>
    ((fun i : Fin R => c (i.castLE (Nat.le_add_right R L))), (fun i : Fin L => c (i.natAdd R)))) := by
  constructor
  · intro c c' h
    simp only [Prod.mk.injEq] at h
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  · rintro ⟨a, b⟩
    refine ⟨Fin.append a b, ?_⟩
    simp only [Prod.mk.injEq]
    exact ⟨funext fun i => Fin.append_left a b i, funext fun i => Fin.append_right a b i⟩

noncomputable def runFrom (F : MCCFamily) (n : ℕ) (r : List Bool) :
    ℕ → EuclideanSpace ℂ (Qubits n) × List (Option Bool) →
      PMF (EuclideanSpace ℂ (Qubits n) × List (Option Bool))
  | 0, st => PMF.pure st
  | k + 1, st => (F.step n r st).bind (runFrom F n r k)

lemma runFrom_succ' (F : MCCFamily) (n : ℕ) (r : List Bool) :
    ∀ k st, runFrom F n r (k + 1) st = (runFrom F n r k st).bind (F.step n r) := by
  intro k
  induction k with
  | zero =>
    intro st
    have h0 : runFrom F n r 0 = PMF.pure := funext fun _ => rfl
    show (F.step n r st).bind (runFrom F n r 0) = (PMF.pure st).bind (F.step n r)
    rw [h0, PMF.bind_pure, PMF.pure_bind]
  | succ k ih =>
    intro st
    have ih' : runFrom F n r (k + 1) = fun s => (runFrom F n r k s).bind (F.step n r) := funext ih
    show (F.step n r st).bind (runFrom F n r (k + 1)) =
      ((F.step n r st).bind (runFrom F n r k)).bind (F.step n r)
    rw [ih', PMF.bind_bind]

lemma run_eq (F : MCCFamily) (n : ℕ) (r : List Bool) (x : Qubits n) :
    ∀ k, F.run n r x k = runFrom F n r k (ket x, []) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (F.run n r x k).bind (F.step n r) = _
    rw [ih, runFrom_succ']

lemma runFrom_none (F : MCCFamily) (n : ℕ) (r : List Bool)
    (st : EuclideanSpace ℂ (Qubits n) × List (Option Bool)) (hc : F.ctrl n r st.2 = none) :
    ∀ k, runFrom F n r k st = PMF.pure st := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (F.step n r st).bind (runFrom F n r k) = _
    have hs : F.step n r st = PMF.pure st := by simp only [MCCFamily.step, hc]
    rw [hs, PMF.pure_bind, ih]

noncomputable def post {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (M : Fin n → Pauli) (β : Bool) :
    EuclideanSpace ℂ (Qubits n) :=
  ((‖act (Pr M β) ψ‖⁻¹ : ℝ) • act (Pr M β) ψ)

lemma step_gate (F : MCCFamily) (n : ℕ) (r : List Bool) (o : CliffordOp n)
    (ho : ∀ M, o ≠ .measure M) (ψ : EuclideanSpace ℂ (Qubits n)) (h : List (Option Bool))
    (hc : F.ctrl n r h = some o) :
    F.step n r (ψ, h) = PMF.pure (act o.mat ψ, h ++ [none]) := by
  rcases o with ⟨q, P⟩ | q | q | ⟨c1, t, hct⟩ | M
  · simp only [MCCFamily.step, hc]
  · simp only [MCCFamily.step, hc]
  · simp only [MCCFamily.step, hc]
  · simp only [MCCFamily.step, hc]
  · exact absurd rfl (ho M)

lemma gR_gate (F : MCCFamily) (n : ℕ) (r : List Bool) (o : CliffordOp n)
    (ho : ∀ M, o ≠ .measure M) (ρ : Matrix (Qubits n) (Qubits n) ℂ) (h : List (Option Bool))
    (c : List Bool) (hc : F.ctrl n r h = some o) :
    gR F n r (ρ, h, c) = (o.mat * ρ * o.mat.conjTranspose, h ++ [none], c) := by
  rcases o with ⟨q, P⟩ | q | q | ⟨c1, t, hct⟩ | M
  · simp only [gR, hc]
  · simp only [gR, hc]
  · simp only [gR, hc]
  · simp only [gR, hc]
  · exact absurd rfl (ho M)

lemma step_meas (F : MCCFamily) (n : ℕ) (r : List Bool) (M : Fin n → Pauli)
    (ψ : EuclideanSpace ℂ (Qubits n)) (h : List (Option Bool))
    (hc : F.ctrl n r h = some (.measure M)) :
    F.step n r (ψ, h) =
      (PMF.bernoulli (min 1 (Real.toNNReal (‖act (Pr M true) ψ‖ ^ 2))) (min_le_left _ _)).map
        (fun β => (post ψ M β, h ++ [some β])) := by
  simp only [MCCFamily.step, hc]
  rfl

lemma gR_meas (F : MCCFamily) (n : ℕ) (r : List Bool) (M : Fin n → Pauli)
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) (h : List (Option Bool)) (a : Bool) (c : List Bool)
    (hc : F.ctrl n r h = some (.measure M)) :
    gR F n r (ρ, h, a :: c) =
      ((Pr M (bet ρ M a) * ρ).trace⁻¹ • (Pr M (bet ρ M a) * ρ * Pr M (bet ρ M a)),
        h ++ [some (bet ρ M a)], c) := by
  simp only [gR, hc, List.headD_cons, List.tail_cons]

lemma pd_post {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (M : Fin n → Pauli) (β : Bool) :
    pureDensity (post ψ M β) =
      (Pr M β * pureDensity ψ).trace⁻¹ • (Pr M β * pureDensity ψ * Pr M β) :=
  pureDensity_post _ (Pr_herm M β) (Pr_idem M β) ψ

theorem run_couple {σ : Type} (F : MCCFamily) (n : ℕ) (r : List Bool)
    (upd : CliffordOp n → σ → Bool → σ × Option Bool) (tab : σ → Tableau n) (Inv : σ → Prop)
    (hinv : ∀ op s b, Inv s → Inv (upd op s b).1)
    (htr : ∀ s, Inv s → (tableauProjector (tab s)).trace = 1)
    (hgate : ∀ (op : CliffordOp n) s b, Inv s → (∀ M, op ≠ .measure M) →
      (upd op s b).2 = none ∧
      tableauProjector (tab (upd op s b).1) = op.mat * tableauProjector (tab s) * op.mat.conjTranspose)
    (hmeas : ∀ (M : Fin n → Pauli) s b, Inv s →
      ∃ β, (upd (.measure M) s b).2 = some β ∧
        ((Pr M β * tableauProjector (tab s)).trace = 1 ∨
          ((Pr M true * tableauProjector (tab s)).trace = 2⁻¹ ∧ β = b)) ∧
        tableauProjector (tab (upd (.measure M) s b).1) =
          (Pr M β * tableauProjector (tab s)).trace⁻¹ •
            (Pr M β * tableauProjector (tab s) * Pr M β))
    (k : ℕ) : ∀ (L : ℕ), k ≤ L → ∀ (ψ : EuclideanSpace ℂ (Qubits n)) (h : List (Option Bool)) (s : σ),
      Inv s → tableauProjector (tab s) = pureDensity ψ →
      (PMF.uniformOfFintype (Fin L → Bool)).map (fun c =>
        (((gR F n r)^[k] (pureDensity ψ, h, List.ofFn c)).1,
          ((gR F n r)^[k] (pureDensity ψ, h, List.ofFn c)).2.1)) =
      (runFrom F n r k (ψ, h)).map (fun st => (pureDensity st.1, st.2)) := by
  induction k with
  | zero =>
    intro L _ ψ h s _ _
    simp only [Function.iterate_zero, id]
    rw [show runFrom F n r 0 (ψ, h) = PMF.pure (ψ, h) from rfl, PMF.pure_map]
    exact PMF.map_const _ _
  | succ k ih =>
    intro L hL ψ h s hs hsψ
    have hρtr : (pureDensity ψ).trace = 1 := hsψ ▸ htr s hs
    rcases hc : F.ctrl n r h with _ | o
    · have hfix : ∀ c : List Bool, (gR F n r)^[k + 1] (pureDensity ψ, h, c) = (pureDensity ψ, h, c) :=
        fun c => Function.iterate_fixed (by simp only [gR, hc]) _
      simp only [hfix]
      rw [runFrom_none F n r (ψ, h) hc, PMF.pure_map]
      exact PMF.map_const _ _
    · by_cases hom : ∃ M, o = .measure M
      · obtain ⟨M, rfl⟩ := hom
        obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
        have e1 : (fun c : Fin (L' + 1) → Bool =>
            (((gR F n r)^[k + 1] (pureDensity ψ, h, List.ofFn c)).1,
              ((gR F n r)^[k + 1] (pureDensity ψ, h, List.ofFn c)).2.1)) =
            fun c => (fun bt : Bool × (Fin L' → Bool) =>
              (((gR F n r)^[k + 1] (pureDensity ψ, h, bt.1 :: List.ofFn bt.2)).1,
                ((gR F n r)^[k + 1] (pureDensity ψ, h, bt.1 :: List.ofFn bt.2)).2.1))
              (c 0, fun i : Fin L' => c i.succ) := by
          funext c
          rw [List.ofFn_succ]
        rw [e1]
        refine (unif_split (fun c : Fin (L' + 1) → Bool => (c 0, fun i : Fin L' => c i.succ))
          (cons_bij L') (fun bt : Bool × (Fin L' → Bool) =>
            (((gR F n r)^[k + 1] (pureDensity ψ, h, bt.1 :: List.ofFn bt.2)).1,
              ((gR F n r)^[k + 1] (pureDensity ψ, h, bt.1 :: List.ofFn bt.2)).2.1))).trans ?_
        have hstep : ∀ a : Bool, (PMF.uniformOfFintype (Fin L' → Bool)).map (fun b =>
            (((gR F n r)^[k + 1] (pureDensity ψ, h, a :: List.ofFn b)).1,
              ((gR F n r)^[k + 1] (pureDensity ψ, h, a :: List.ofFn b)).2.1)) =
            (runFrom F n r k (post ψ M (bet (pureDensity ψ) M a), h ++ [some (bet (pureDensity ψ) M a)])).map
              (fun st => (pureDensity st.1, st.2)) := by
          intro a
          obtain ⟨β0, -, hcase, hpost⟩ := hmeas M s a hs
          rw [hsψ] at hcase hpost
          have hb := bet_eq M _ hρtr a β0 hcase
          have hpd : tableauProjector (tab (upd (.measure M) s a).1) = pureDensity (post ψ M β0) := by
            rw [hpost, pd_post]
          rw [hb, ← ih L' (by omega) (post ψ M β0) (h ++ [some β0]) _ (hinv _ _ _ hs) hpd]
          congr 1
          funext b
          rw [Function.iterate_succ_apply, gR_meas F n r M _ h a _ hc, hb, ← pd_post]
        simp only [hstep]
        obtain ⟨β1, -, hcase1, -⟩ := hmeas M s false hs
        rw [hsψ] at hcase1
        have h3 : (Pr M false * pureDensity ψ).trace = 1 ∨ (Pr M true * pureDensity ψ).trace = 1 ∨
            (Pr M true * pureDensity ψ).trace = 2⁻¹ := by
          rcases hcase1 with h1 | ⟨h2, -⟩
          · cases β1
            · exact Or.inl h1
            · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr h2)
        have hco := coin M ψ hρtr h3
        calc (PMF.uniformOfFintype Bool).bind (fun a =>
              (runFrom F n r k (post ψ M (bet (pureDensity ψ) M a),
                h ++ [some (bet (pureDensity ψ) M a)])).map (fun st => (pureDensity st.1, st.2)))
            = ((PMF.uniformOfFintype Bool).map (bet (pureDensity ψ) M)).bind (fun β =>
              (runFrom F n r k (post ψ M β, h ++ [some β])).map
                (fun st => (pureDensity st.1, st.2))) := by
              rw [PMF.bind_map]; rfl
          _ = _ := by
              rw [hco]
              show _ = ((F.step n r (ψ, h)).bind (runFrom F n r k)).map _
              rw [step_meas F n r M ψ h hc, PMF.bind_map, PMF.map_bind]
              rfl
      · have ho : ∀ M, o ≠ .measure M := fun M hM => hom ⟨M, hM⟩
        obtain ⟨-, hpj⟩ := hgate o s false hs ho
        rw [hsψ, ← pureDensity_act] at hpj
        have hih := ih L (by omega) (act o.mat ψ) (h ++ [none]) _ (hinv _ _ _ hs) hpj
        have e : ∀ c : List Bool, (gR F n r)^[k + 1] (pureDensity ψ, h, c) =
            (gR F n r)^[k] (pureDensity (act o.mat ψ), h ++ [none], c) := by
          intro c
          rw [Function.iterate_succ_apply, gR_gate F n r o ho _ h c hc, pureDensity_act]
        simp only [e]
        rw [hih]
        show _ = ((F.step n r (ψ, h)).bind (runFrom F n r k)).map _
        rw [step_gate F n r o ho ψ h hc, PMF.pure_bind]

end E261P

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity in
theorem solution (F : MCCFamily) (n : ℕ) (x : Qubits n) (σ : Type)
    (upd : CliffordOp n → σ → Bool → σ × Option Bool) (tab : σ → Tableau n) (Inv : σ → Prop) (s0 : σ)
    (h0 : Inv s0) (hx : tableauProjector (tab s0) = pureDensity (ket x))
    (hinv : ∀ op s b, Inv s → Inv (upd op s b).1)
    (hval : ∀ s, Inv s → IsValidTableau (tab s))
    (hgate : ∀ (op : CliffordOp n) s b, Inv s → (∀ M, op ≠ .measure M) →
      (upd op s b).2 = none ∧
      tableauProjector (tab (upd op s b).1) = op.mat * tableauProjector (tab s) * op.mat.conjTranspose)
    (hmeas : ∀ (M : Fin n → Pauli) s b, Inv s →
      ∃ β, (upd (.measure M) s b).2 = some β ∧
        (((((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector (tab s)).trace = 1 ∧
            ∀ b', upd (.measure M) s b' = upd (.measure M) s b) ∨
          ((((2⁻¹ : ℂ) • (1 + (if true then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector (tab s)).trace = 2⁻¹ ∧ β = b)) ∧
        tableauProjector (tab (upd (.measure M) s b).1) =
          (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector (tab s)).trace⁻¹ • (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector (tab s) * ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ)))
    (m : ℕ) (hm : F.rbits.eval n + F.steps.eval n ≤ m) :
    let simLoop : List Bool → σ × List (Option Bool) × List Bool := fun bits =>
      (fun st : σ × List (Option Bool) × List Bool =>
        match F.ctrl n (bits.take (F.rbits.eval n)) st.2.1 with
        | none => st
        | some o => ((upd o st.1 (st.2.2.headD false)).1, st.2.1 ++ [(upd o st.1 (st.2.2.headD false)).2],
            match o with
            | .measure _ => st.2.2.tail
            | _ => st.2.2))^[F.steps.eval n] (s0, [], bits.drop (F.rbits.eval n))
    (∀ bits : List Bool, Inv (simLoop bits).1) ∧
      (PMF.uniformOfFintype (Fin m → Bool)).map
          (fun bits => tableauProjector (tab (simLoop (List.ofFn bits)).1)) =
        F.finalDist n x := by
  intro simLoop
  have htr : ∀ s, Inv s → (tableauProjector (tab s)).trace = 1 :=
    fun s hs => E261.trace_tableauProjector _ (hval s hs)
  have hmeas' : ∀ (M : Fin n → Pauli) s b, Inv s →
      ∃ β, (upd (.measure M) s b).2 = some β ∧
        ((E261P.Pr M β * tableauProjector (tab s)).trace = 1 ∨
          ((E261P.Pr M true * tableauProjector (tab s)).trace = 2⁻¹ ∧ β = b)) ∧
        tableauProjector (tab (upd (.measure M) s b).1) =
          (E261P.Pr M β * tableauProjector (tab s)).trace⁻¹ •
            (E261P.Pr M β * tableauProjector (tab s) * E261P.Pr M β) := fun M s b hs => by
    obtain ⟨β, h1, hc, h2⟩ := hmeas M s b hs
    exact ⟨β, h1, hc.imp (fun h => h.1) id, h2⟩
  have hIC : ∀ bits : List Bool, Inv (simLoop bits).1 ∧
      tableauProjector (tab (simLoop bits).1) =
        ((E261P.gR F n (bits.take (F.rbits.eval n)))^[F.steps.eval n]
          (pureDensity (ket x), [], bits.drop (F.rbits.eval n))).1 := by
    intro bits
    have H := E261P.iter_couple F n (bits.take (F.rbits.eval n)) upd tab Inv hinv htr hgate hmeas'
      (F.steps.eval n) s0 [] (bits.drop (F.rbits.eval n)) h0
    rw [hx] at H
    exact ⟨H.1, congrArg Prod.fst H.2⟩
  refine ⟨fun bits => (hIC bits).1, ?_⟩
  simp only [fun bits => (hIC bits).2]
  obtain ⟨L, rfl⟩ : ∃ L, m = F.rbits.eval n + L := ⟨m - F.rbits.eval n, by omega⟩
  have e1 : (fun bits : Fin (F.rbits.eval n + L) → Bool =>
      ((E261P.gR F n ((List.ofFn bits).take (F.rbits.eval n)))^[F.steps.eval n]
        (pureDensity (ket x), [], (List.ofFn bits).drop (F.rbits.eval n))).1) =
      fun bits => (fun ab : (Fin (F.rbits.eval n) → Bool) × (Fin L → Bool) =>
        ((E261P.gR F n (List.ofFn ab.1))^[F.steps.eval n]
          (pureDensity (ket x), [], List.ofFn ab.2)).1)
        ((fun i : Fin (F.rbits.eval n) => bits (i.castLE (Nat.le_add_right (F.rbits.eval n) L))),
          (fun i : Fin L => bits (i.natAdd (F.rbits.eval n)))) := by
    funext bits
    rw [List.ofFn_add, List.take_left' (List.length_ofFn), List.drop_left' (List.length_ofFn)]
  rw [e1]
  refine (E261P.unif_split _ (E261P.app_bij (F.rbits.eval n) L) (fun ab : (Fin (F.rbits.eval n) → Bool) × (Fin L → Bool) =>
        ((E261P.gR F n (List.ofFn ab.1))^[F.steps.eval n]
          (pureDensity (ket x), [], List.ofFn ab.2)).1)).trans ?_
  unfold MCCFamily.finalDist
  congr 1
  funext a
  have hc := congrArg (PMF.map Prod.fst) (E261P.run_couple F n (List.ofFn a) upd tab Inv hinv htr
    hgate hmeas' (F.steps.eval n) L (by omega) (ket x) [] s0 h0 hx)
  rw [PMF.map_comp, PMF.map_comp] at hc
  rw [E261P.run_eq]
  exact hc
