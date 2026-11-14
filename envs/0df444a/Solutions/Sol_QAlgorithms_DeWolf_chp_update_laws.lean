-- Prove2me | solution 1 for QAlgorithms.DeWolf.chp_update_laws
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:25:15.176909+00:00
-- url     : https://prove2.me/submissions/35270730-d831-400f-be82-71c031ea23e6

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

lemma gen_mul_Q {n : ℕ} (P : PauliString n) (hP : P.phase = 0 ∨ P.phase = 2) :
    P.toMatrix * ((2⁻¹ : ℂ) • (1 + P.toMatrix)) = (2⁻¹ : ℂ) • (1 + P.toMatrix) := by
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, toMatrix_sq P hP, add_comm]

lemma commute_Q {n : ℕ} (A B : Matrix (Qubits n) (Qubits n) ℂ) (h : Commute A B) :
    Commute A ((2⁻¹ : ℂ) • (1 + B)) :=
  ((Commute.one_right A).add_right h).smul_right _

lemma commute_QQ {n : ℕ} (A B : Matrix (Qubits n) (Qubits n) ℂ) (h : Commute A B) :
    Commute ((2⁻¹ : ℂ) • (1 + A)) ((2⁻¹ : ℂ) • (1 + B)) :=
  ((Commute.one_left _).add_left (commute_Q A B h)).smul_left _

lemma commute_proj {n : ℕ} (T : Tableau n) (A : Matrix (Qubits n) (Qubits n) ℂ)
    (h : ∀ j, Commute A (T j).toMatrix) : Commute A (tableauProjector T) := by
  unfold tableauProjector
  apply Commute.list_prod_right
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  exact commute_Q _ _ (h j)

lemma gen_mul_proj {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (j : Fin n) :
    (T j).toMatrix * tableauProjector T = tableauProjector T := by
  unfold tableauProjector
  rw [ofFn_prod_move n _ j (fun i => commute_QQ _ _
      (hT.2.1 j i : Commute (T j).toMatrix (T i).toMatrix)), ← Matrix.mul_assoc,
    gen_mul_Q _ (hT.1 j)]

lemma proj_mul_gen {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (j : Fin n) :
    tableauProjector T * (T j).toMatrix = tableauProjector T := by
  rw [← (commute_proj T _ (fun i => (hT.2.1 j i : Commute (T j).toMatrix (T i).toMatrix))).eq,
    gen_mul_proj T hT j]

lemma mul_list_prod_fix {m : Type*} [Fintype m] [DecidableEq m] (ρ : Matrix m m ℂ) :
    ∀ l : List (Matrix m m ℂ), (∀ x ∈ l, ρ * x = ρ) → ρ * l.prod = ρ
  | [], _ => by simp
  | x :: l, h => by
    rw [List.prod_cons, ← Matrix.mul_assoc, h x List.mem_cons_self,
      mul_list_prod_fix ρ l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem proj_idem {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) :
    tableauProjector T * tableauProjector T = tableauProjector T := by
  have h := mul_list_prod_fix (tableauProjector T)
    (List.ofFn fun j : Fin n => (2⁻¹ : ℂ) • (1 + (T j).toMatrix)) ?_
  · exact h
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, proj_mul_gen T hT j, ← two_smul ℂ,
    smul_smul]
  norm_num


/-! ## Session 3: random-outcome measurement: each outcome has probability 1/2 -/

lemma trace_meas_anti {n : ℕ} (T : Tableau n) (hT : IsValidTableau T)
    (A : Matrix (Qubits n) (Qubits n) ℂ) (p : Fin n)
    (hp : A * (T p).toMatrix = -((T p).toMatrix * A)) (c : ℂ) :
    (((2⁻¹ : ℂ) • (1 + c • A)) * tableauProjector T).trace = 2⁻¹ := by
  have h0 : (A * tableauProjector T).trace = 0 := by
    have h1 : (A * tableauProjector T).trace = -(A * tableauProjector T).trace := by
      calc (A * tableauProjector T).trace
          = (A * ((T p).toMatrix * tableauProjector T)).trace := by rw [gen_mul_proj T hT p]
        _ = (-((T p).toMatrix * (A * tableauProjector T))).trace := by
            rw [← Matrix.mul_assoc, hp, Matrix.neg_mul, Matrix.mul_assoc]
        _ = -((A * tableauProjector T) * (T p).toMatrix).trace := by
            rw [Matrix.trace_neg, Matrix.trace_mul_comm]
        _ = -(A * tableauProjector T).trace := by
            rw [Matrix.mul_assoc, proj_mul_gen T hT p]
    linear_combination h1 / 2
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, Matrix.one_mul,
    Matrix.smul_mul, Matrix.trace_smul, h0, trace_tableauProjector T hT]
  simp

/-! ## Session 4: abstract measurement lemmas (from e261f9b1_meas.lean) -/

section MeasAbs
variable {m : Type*} [Fintype m] [DecidableEq m]

lemma idem_toLin' (Q : Matrix m m ℂ) (h : Q * Q = Q) : IsIdempotentElem (Matrix.toLin' Q) := by
  show (Matrix.toLin' Q).comp (Matrix.toLin' Q) = Matrix.toLin' Q
  rw [← Matrix.toLin'_mul, h]

lemma idem_trace_nat (Q : Matrix m m ℂ) (h : Q * Q = Q) : ∃ k : ℕ, Q.trace = k := by
  have he := idem_toLin' Q h
  refine ⟨Module.finrank ℂ (LinearMap.range (Matrix.toLin' Q)), ?_⟩
  rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ he).trace]

lemma idem_zero (Q : Matrix m m ℂ) (h : Q * Q = Q) (h0 : Q.trace = 0) : Q = 0 := by
  have he := idem_toLin' Q h
  have h1 : Matrix.toLin' Q = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff he).1 (by rw [Matrix.trace_toLin'_eq, h0])
  exact Matrix.toLin'.injective (by rw [h1, map_zero])

lemma idem_prod (A ρ : Matrix m m ℂ) (hA : A * A = A) (hρ : ρ * ρ = ρ) (hc : Commute A ρ) :
    (A * ρ) * (A * ρ) = A * ρ := by
  calc (A * ρ) * (A * ρ) = A * (ρ * A) * ρ := by simp only [Matrix.mul_assoc]
    _ = A * (A * ρ) * ρ := by rw [hc.eq]
    _ = A * ρ := by rw [← Matrix.mul_assoc A A, hA, Matrix.mul_assoc, hρ]

lemma split_det (ρ P : Matrix m m ℂ) (hρ : ρ * ρ = ρ) (htr : ρ.trace = 1) (hP : P * P = P)
    (hc : Commute P ρ) : P * ρ = ρ ∨ P * ρ = 0 := by
  have hc2 : Commute (1 - P) ρ := (Commute.one_left ρ).sub_left hc
  have hP2 : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, hP]; simp
  have h1 := idem_prod P ρ hP hρ hc
  have h2 := idem_prod (1 - P) ρ hP2 hρ hc2
  obtain ⟨k1, hk1⟩ := idem_trace_nat _ h1
  obtain ⟨k2, hk2⟩ := idem_trace_nat _ h2
  have hsum : (P * ρ).trace + ((1 - P) * ρ).trace = 1 := by
    rw [← Matrix.trace_add, ← add_mul, add_sub_cancel, one_mul, htr]
  rw [hk1, hk2] at hsum
  have hk : k1 + k2 = 1 := by exact_mod_cast hsum
  rcases Nat.add_eq_one_iff.1 hk with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · right; exact idem_zero _ h1 (by rw [hk1, ha]; simp)
  · left
    have := idem_zero _ h2 (by rw [hk2, hb]; simp)
    rw [sub_mul, one_mul, sub_eq_zero] at this
    exact this.symm

lemma proj_sq (M : Matrix m m ℂ) (hM : M * M = 1) (c : ℂ) (hc : c * c = 1) :
    ((2⁻¹ : ℂ) • (1 + c • M)) * ((2⁻¹ : ℂ) • (1 + c • M)) = (2⁻¹ : ℂ) • (1 + c • M) := by
  have h : (1 + c • M) * (1 + c • M) = (2 : ℂ) • (1 + c • M) := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hM, hc, one_smul, two_smul]
    abel
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul]
  congr 1
  norm_num

lemma fix_of (A ρ : Matrix m m ℂ) (h : A * ρ = ρ) (hc : Commute A ρ) : A * ρ * A = ρ := by
  rw [h, ← hc.eq, h]

/-- Deterministic measurement: `M` commutes with the rank-one projector `ρ`. -/
theorem meas_det (ρ M : Matrix m m ℂ) (hρ : ρ * ρ = ρ) (htr : ρ.trace = 1) (hM : M * M = 1)
    (hc : Commute M ρ) :
    ∃ β : Bool, (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1 : ℂ) • M)) * ρ).trace = 1 ∧
      ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1 : ℂ) • M)) * ρ *
        ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1 : ℂ) • M)) = ρ := by
  have hcP : ∀ c : ℂ, Commute ((2⁻¹ : ℂ) • (1 + c • M)) ρ := fun c =>
    ((Commute.one_left ρ).add_left (hc.smul_left c)).smul_left _
  rcases split_det ρ ((2⁻¹ : ℂ) • (1 + (1 : ℂ) • M)) hρ htr (proj_sq M hM 1 (by norm_num))
      (hcP 1) with h | h
  · refine ⟨false, ?_, ?_⟩
    · simp only [Bool.false_eq_true, if_false]; rw [h, htr]
    · simp only [Bool.false_eq_true, if_false]; exact fix_of _ _ h (hcP 1)
  · have e : (2⁻¹ : ℂ) • (1 + (-1 : ℂ) • M) = 1 - (2⁻¹ : ℂ) • (1 + (1 : ℂ) • M) := by module
    have h' : ((2⁻¹ : ℂ) • (1 + (-1 : ℂ) • M)) * ρ = ρ := by
      rw [e, sub_mul, one_mul, h, sub_zero]
    refine ⟨true, ?_, ?_⟩
    · simp only [if_true]; rw [h', htr]
    · simp only [if_true]; exact fix_of _ _ h' (hcP (-1))

/-- In a list of matrices commuting with an idempotent `R` that contains `R`, right
multiplication by `R` is absorbed. -/
lemma list_prod_mul_R (R : Matrix m m ℂ) (hR : R * R = R) :
    ∀ l : List (Matrix m m ℂ), (∀ x ∈ l, Commute R x) → R ∈ l → l.prod * R = l.prod
  | [], _, hm => absurd hm List.not_mem_nil
  | x :: l, hc, hm => by
    rw [List.prod_cons]
    rcases List.mem_cons.1 hm with h | h
    · subst h
      have hl : Commute R l.prod := Commute.list_prod_right _ _ (fun y hy => hc y (List.mem_cons_of_mem _ hy))
      rw [Matrix.mul_assoc, ← hl.eq, ← Matrix.mul_assoc, hR]
    · rw [Matrix.mul_assoc, list_prod_mul_R R hR l (fun y hy => hc y (List.mem_cons_of_mem _ hy)) h]

lemma ofFn_mul_R (R : Matrix m m ℂ) (hR : R * R = R) :
    ∀ (n : ℕ) (f : Fin n → Matrix m m ℂ), (∀ i, Commute R (f i)) →
      (List.ofFn f).prod * R = (List.ofFn fun i => f i * R).prod * R
  | 0, _, _ => by simp
  | n + 1, f, hc => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, Matrix.mul_assoc,
      ofFn_mul_R R hR n (fun i => f i.succ) (fun i => hc i.succ)]
    have hY : Commute R (List.ofFn fun i : Fin n => f i.succ * R).prod :=
      Commute.list_prod_right _ _ (fun y hy => by
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
        exact (hc i.succ).mul_right (Commute.refl R))
    have hYR : (List.ofFn fun i : Fin n => f i.succ * R).prod * R =
        R * (List.ofFn fun i : Fin n => f i.succ * R).prod * R := by
      rw [hY.eq, Matrix.mul_assoc, hR]
    rw [hYR]
    simp only [Matrix.mul_assoc]

/-- Replacing factors `f i` by `g i` with `f i R = g i R` (for an idempotent factor `R`
present in both) does not change the ordered product. -/
lemma ofFn_swap (R : Matrix m m ℂ) (hR : R * R = R) (n : ℕ) (f g : Fin n → Matrix m m ℂ)
    (p : Fin n) (hfp : f p = R) (hgp : g p = R) (hf : ∀ i, Commute R (f i))
    (hg : ∀ i, Commute R (g i)) (hfg : ∀ i, f i * R = g i * R) :
    (List.ofFn f).prod = (List.ofFn g).prod := by
  have hmf : R ∈ List.ofFn f := (List.mem_ofFn' _ _).2 ⟨p, hfp⟩
  have hmg : R ∈ List.ofFn g := (List.mem_ofFn' _ _).2 ⟨p, hgp⟩
  have af : ∀ x ∈ List.ofFn f, Commute R x := fun x hx => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx; exact hf i
  have ag : ∀ x ∈ List.ofFn g, Commute R x := fun x hx => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx; exact hg i
  rw [← list_prod_mul_R R hR _ af hmf, ← list_prod_mul_R R hR _ ag hmg, ofFn_mul_R R hR n f hf,
    ofFn_mul_R R hR n g hg]
  simp only [hfg]

/-- `P T P = 0` when `P = (1+S)/2` and `S` anticommutes with `T`. -/
lemma proj_anti_zero (S T : Matrix m m ℂ) (hS : S * S = 1) (hST : S * T = -(T * S)) :
    ((2⁻¹ : ℂ) • (1 + S)) * T * ((2⁻¹ : ℂ) • (1 + S)) = 0 := by
  have e1 : S * T * S = -T := by rw [hST, neg_mul, Matrix.mul_assoc, hS, mul_one]
  have e2 : (1 + S) * T * (1 + S) = 0 := by
    calc (1 + S) * T * (1 + S) = T + S * T + T * S + S * T * S := by noncomm_ring
      _ = 0 := by rw [e1, hST]; abel
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, e2]
  simp

lemma PQP_aux (P T : Matrix m m ℂ) (hP : P * P = P) (hz : P * T * P = 0) :
    P * ((2⁻¹ : ℂ) • (1 + T)) * P = (2⁻¹ : ℂ) • P := by
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_one, hP, hz, add_zero]

lemma proj_Q_proj (S T : Matrix m m ℂ) (hS : S * S = 1) (hST : S * T = -(T * S)) :
    ((2⁻¹ : ℂ) • (1 + S)) * ((2⁻¹ : ℂ) • (1 + T)) * ((2⁻¹ : ℂ) • (1 + S)) =
      (2⁻¹ : ℂ) • ((2⁻¹ : ℂ) • (1 + S)) := by
  have hP0 := proj_sq S hS 1 (by norm_num)
  simp only [one_smul] at hP0
  exact PQP_aux _ _ hP0 (proj_anti_zero S T hS hST)

/-- Random measurement, post-state: with `P = (1+S)/2`, `S` anticommuting with `T`, and the
factor `g p = (1+T)/2` commuting with every factor, `2 P (Π g) P` is the product with the
`p`-th factor replaced by `P` (provided `P` commutes with the other factors). -/
theorem rand_post (S T : Matrix m m ℂ) (hS : S * S = 1) (hST : S * T = -(T * S)) (n : ℕ)
    (g : Fin n → Matrix m m ℂ) (p : Fin n) (hgp : g p = (2⁻¹ : ℂ) • (1 + T))
    (hcT : ∀ i, Commute (g p) (g i))
    (hcS : ∀ i, i ≠ p → Commute ((2⁻¹ : ℂ) • (1 + S)) (g i)) :
    (2 : ℂ) • (((2⁻¹ : ℂ) • (1 + S)) * (List.ofFn g).prod * ((2⁻¹ : ℂ) • (1 + S))) =
      (List.ofFn (Function.update g p ((2⁻¹ : ℂ) • (1 + S)))).prod := by
  have hPQP := proj_Q_proj S T hS hST
  set P := (2⁻¹ : ℂ) • (1 + S) with hPdef
  have h1 := ofFn_prod_move n g p hcT
  have h2 := ofFn_prod_move n (Function.update g p P) p (fun i => by
    rw [Function.update_self]
    by_cases hi : i = p
    · subst hi; rw [Function.update_self]; exact Commute.refl P
    · rw [Function.update_of_ne hi]; exact hcS i hi)
  rw [Function.update_self, Function.update_idem] at h2
  have hR : Commute P (List.ofFn (Function.update g p 1)).prod :=
    Commute.list_prod_right _ _ (fun y hy => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
      by_cases hi : i = p
      · subst hi; rw [Function.update_self]; exact Commute.one_right P
      · rw [Function.update_of_ne hi]; exact hcS i hi)
  rw [h2, h1, hgp, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ P, ← hR.eq, ← Matrix.mul_assoc, hPQP,
    Matrix.smul_mul, smul_smul]
  norm_num

end MeasAbs

/-! ## Session 4: symbolic anticommutation test, phases of products -/

def antiPair (a b : Pauli) : Bool := decide (a ≠ .I ∧ b ≠ .I ∧ a ≠ b)

lemma pauli_comm_sign (a b : Pauli) :
    a.mat * b.mat = (if antiPair a b then (-1 : ℂ) else 1) • (b.mat * a.mat) := by
  cases a <;> cases b <;> ext i j <;> cases i <;> cases j <;>
    simp [antiPair, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.one_apply] <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf)

/-- Symbolic test: the Pauli strings anticommute (odd number of anticommuting wires). -/
def antiB {n : ℕ} (P Q : PauliString n) : Bool :=
  decide (Odd (Finset.univ.filter fun q => antiPair (P.ops q) (Q.ops q) = true).card)

lemma prod_sign {n : ℕ} (f : Fin n → Bool) :
    ∏ q, (if f q = true then (-1 : ℂ) else 1) =
      if decide (Odd (Finset.univ.filter fun q => f q = true).card) = true then -1 else 1 := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  split_ifs with h'
  · exact (by simpa using h' : Odd _).neg_one_pow
  · exact (Nat.not_odd_iff_even.1 (by simpa using h')).neg_one_pow

lemma toMatrix_comm_sign {n : ℕ} (P Q : PauliString n) :
    P.toMatrix * Q.toMatrix = (if antiB P Q then (-1 : ℂ) else 1) • (Q.toMatrix * P.toMatrix) := by
  simp only [toMatrix_eq_tens, Matrix.smul_mul, Matrix.mul_smul, smul_smul, tens_mul]
  have h : (fun q => (P.ops q).mat * (Q.ops q).mat) = fun q =>
      (if antiPair (P.ops q) (Q.ops q) = true then (-1 : ℂ) else 1) • ((Q.ops q).mat * (P.ops q).mat) :=
    funext fun q => pauli_comm_sign _ _
  rw [h, tens_smul, smul_smul, prod_sign (fun q => antiPair (P.ops q) (Q.ops q))]
  unfold antiB
  congr 1
  ring

lemma phase_even_of_sq {n : ℕ} (R : PauliString n) (h : R.toMatrix * R.toMatrix = 1) :
    R.phase = 0 ∨ R.phase = 2 := by
  have hs : ∀ q, (Pauli.mul (R.ops q) (R.ops q)).1 = 0 := fun q => by cases R.ops q <;> rfl
  have hI : ∀ q, (R.mul R).ops q = .I := fun q => by
    show (Pauli.mul (R.ops q) (R.ops q)).2 = .I
    cases R.ops q <;> rfl
  have hph : (R.mul R).phase = R.phase + R.phase := by
    show R.phase + R.phase + ∑ q, (Pauli.mul (R.ops q) (R.ops q)).1 = _
    simp [hs]
  rw [← toMatrix_mul, toMatrix_of_allI _ hI, hph] at h
  have h00 := congrFun (congrFun h (fun _ => false)) (fun _ => false)
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  rcases (show ∀ c : ZMod 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by decide) R.phase with hc | hc | hc | hc
  · left; exact hc
  · exfalso; rw [hc, show ((1 : ZMod 4) + 1).val = 2 from rfl, Complex.I_sq] at h00; norm_num at h00
  · right; exact hc
  · exfalso; rw [hc, show ((3 : ZMod 4) + 3).val = 2 from rfl, Complex.I_sq] at h00; norm_num at h00

lemma mul_phase_even {n : ℕ} (P Q : PauliString n) (hP : P.phase = 0 ∨ P.phase = 2)
    (hQ : Q.phase = 0 ∨ Q.phase = 2) (hc : P.Commute Q) :
    (P.mul Q).phase = 0 ∨ (P.mul Q).phase = 2 := by
  apply phase_even_of_sq
  rw [toMatrix_mul]
  have hc' : P.toMatrix * Q.toMatrix = Q.toMatrix * P.toMatrix := hc
  calc P.toMatrix * Q.toMatrix * (P.toMatrix * Q.toMatrix)
      = P.toMatrix * (Q.toMatrix * P.toMatrix) * Q.toMatrix := by simp only [Matrix.mul_assoc]
    _ = P.toMatrix * (P.toMatrix * Q.toMatrix) * Q.toMatrix := by rw [← hc']
    _ = 1 := by rw [← Matrix.mul_assoc P.toMatrix P.toMatrix, toMatrix_sq P hP, Matrix.one_mul,
                  toMatrix_sq Q hQ]


/-! ## Session 4: tableau-level measurement (deterministic outcome; random post-state) -/

lemma antiPair_symm (a b : Pauli) : antiPair a b = antiPair b a := by
  cases a <;> cases b <;> rfl

lemma antiB_symm {n : ℕ} (P Q : PauliString n) : antiB P Q = antiB Q P := by
  unfold antiB
  simp only [show ∀ q, antiPair (P.ops q) (Q.ops q) = antiPair (Q.ops q) (P.ops q) from
    fun q => antiPair_symm _ _]

lemma comm_of_antiB_false {n : ℕ} (P Q : PauliString n) (h : antiB P Q = false) :
    P.toMatrix * Q.toMatrix = Q.toMatrix * P.toMatrix := by
  rw [toMatrix_comm_sign, h]; simp

lemma anti_of_antiB_true {n : ℕ} (P Q : PauliString n) (h : antiB P Q = true) :
    P.toMatrix * Q.toMatrix = -(Q.toMatrix * P.toMatrix) := by
  rw [toMatrix_comm_sign, h]; simp

lemma signed_toMatrix {n : ℕ} (M : Fin n → Pauli) (b : Bool) :
    (⟨if b then 2 else 0, M⟩ : PauliString n).toMatrix =
      (if b then (-1 : ℂ) else 1) • (⟨0, M⟩ : PauliString n).toMatrix := by
  cases b
  · simp
  · show (⟨2, M⟩ : PauliString n).toMatrix = (-1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix
    rw [toMatrix_eq_tens, toMatrix_eq_tens, smul_smul]
    congr 1
    rw [show ((2 : ZMod 4)).val = 2 from rfl, show ((0 : ZMod 4)).val = 0 from rfl, Complex.I_sq]
    ring

lemma QQ_swap {m : Type*} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ) (hB : B * B = 1) :
    ((2⁻¹ : ℂ) • (1 + A)) * ((2⁻¹ : ℂ) • (1 + B)) =
      ((2⁻¹ : ℂ) • (1 + A * B)) * ((2⁻¹ : ℂ) • (1 + B)) := by
  have h : (1 + A) * (1 + B) = (1 + A * B) * (1 + B) := by
    have e : (1 + A * B) * (1 + B) = 1 + B + A * B + A * (B * B) := by noncomm_ring
    rw [e, hB, mul_one]; noncomm_ring
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, h]

/-- Deterministic measurement at the tableau level: `M` commutes with every generator. -/
theorem det_meas {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli)
    (hcm : ∀ j, antiB (T j) ⟨0, M⟩ = false) :
    ∃ β : Bool, (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix)) *
        tableauProjector T).trace = 1 ∧
      ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix)) *
        tableauProjector T *
        ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix)) =
        tableauProjector T :=
  meas_det (tableauProjector T) _ (proj_idem T hT) (trace_tableauProjector T hT)
    (toMatrix_sq _ (Or.inl rfl))
    (commute_proj T _ (fun j =>
      (show Commute (T j).toMatrix (⟨0, M⟩ : PauliString n).toMatrix from
        comm_of_antiB_false _ _ (hcm j)).symm))

/-- The measurement update for a random outcome `b` (`p` = an anticommuting generator):
`T'_p = (-1)^b M`, `T'_j = T_j T_p` for the other anticommuting generators. -/
def updM {n : ℕ} (T : Tableau n) (M : Fin n → Pauli) (p : Fin n) (b : Bool) : Tableau n :=
  fun j => if j = p then ⟨if b then 2 else 0, M⟩
    else if antiB (T j) ⟨0, M⟩ then (T j).mul (T p) else T j

theorem rand_proj {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli) (p : Fin n)
    (hp : antiB (T p) ⟨0, M⟩ = true) (b : Bool) :
    tableauProjector (updM T M p b) =
      (2 : ℂ) • (((2⁻¹ : ℂ) • (1 + (if b then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix)) *
        tableauProjector T *
        ((2⁻¹ : ℂ) • (1 + (if b then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix))) := by
  have hsgn : (if b then -1 else 1 : ℂ) * (if b then -1 else 1 : ℂ) = 1 := by cases b <;> simp
  have hMM : (⟨0, M⟩ : PauliString n).toMatrix * (⟨0, M⟩ : PauliString n).toMatrix = 1 :=
    toMatrix_sq _ (Or.inl rfl)
  have hTT : ∀ j, (T j).toMatrix * (T j).toMatrix = 1 := fun j => toMatrix_sq _ (hT.1 j)
  have hc : ∀ i j, (T i).toMatrix * (T j).toMatrix = (T j).toMatrix * (T i).toMatrix :=
    fun i j => hT.2.1 i j
  set Mm := (⟨0, M⟩ : PauliString n).toMatrix with hMm
  set S := (if b then -1 else 1 : ℂ) • Mm with hSdef
  have hS : S * S = 1 := by
    rw [hSdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMM, hsgn, one_smul]
  have hMT : ∀ j, antiB (T j) ⟨0, M⟩ = false → Commute S (T j).toMatrix := fun j h =>
    (show Commute (T j).toMatrix Mm from comm_of_antiB_false _ _ h).symm.smul_left _
  have hAT : ∀ j, antiB (T j) ⟨0, M⟩ = true → S * (T j).toMatrix = -((T j).toMatrix * S) :=
    fun j h => by
      have e := anti_of_antiB_true _ _ h
      rw [hSdef, Matrix.smul_mul, Matrix.mul_smul, e, smul_neg, neg_neg]
  have hT'S : ∀ j, j ≠ p → Commute S (updM T M p b j).toMatrix := fun j hj => by
    simp only [updM, if_neg hj]
    split_ifs with ha
    · rw [toMatrix_mul]
      show S * ((T j).toMatrix * (T p).toMatrix) = (T j).toMatrix * (T p).toMatrix * S
      rw [← Matrix.mul_assoc, hAT j ha, neg_mul, Matrix.mul_assoc, hAT p hp, mul_neg, neg_neg,
        Matrix.mul_assoc]
    · exact hMT j (by simpa using ha)
  have hT'p : ∀ j, j ≠ p → Commute (T p).toMatrix (updM T M p b j).toMatrix := fun j hj => by
    simp only [updM, if_neg hj]
    split_ifs with ha
    · rw [toMatrix_mul]
      exact (show Commute (T p).toMatrix (T j).toMatrix from hc p j).mul_right (Commute.refl _)
    · exact hc p j
  have hR : ((2⁻¹ : ℂ) • (1 + (T p).toMatrix)) * ((2⁻¹ : ℂ) • (1 + (T p).toMatrix)) =
      (2⁻¹ : ℂ) • (1 + (T p).toMatrix) := by
    have := proj_sq _ (hTT p) 1 (by norm_num)
    simp only [one_smul] at this
    exact this
  let g : Fin n → Matrix (Qubits n) (Qubits n) ℂ := fun j =>
    if j = p then (2⁻¹ : ℂ) • (1 + (T p).toMatrix) else (2⁻¹ : ℂ) • (1 + (updM T M p b j).toMatrix)
  have hgp : g p = (2⁻¹ : ℂ) • (1 + (T p).toMatrix) := if_pos rfl
  have hg : ∀ i, Commute ((2⁻¹ : ℂ) • (1 + (T p).toMatrix)) (g i) := fun i => by
    by_cases hi : i = p
    · subst hi; rw [hgp]
    · simp only [g, if_neg hi]; exact commute_QQ _ _ (hT'p i hi)
  have hswap : tableauProjector T = (List.ofFn g).prod :=
    ofFn_swap _ hR n (fun j => (2⁻¹ : ℂ) • (1 + (T j).toMatrix)) g p rfl hgp
      (fun i => commute_QQ _ _ (hc p i)) hg (fun i => by
        by_cases hi : i = p
        · subst hi; rw [hgp]
        · simp only [g, if_neg hi, updM]
          split_ifs
          · rw [toMatrix_mul]; exact QQ_swap _ _ (hTT p)
          · rfl)
  have hpost := rand_post S (T p).toMatrix hS (hAT p hp) n g p hgp (fun i => by rw [hgp]; exact hg i)
    (fun i hi => by simp only [g, if_neg hi]; exact commute_QQ _ _ (hT'S i hi))
  rw [hswap, hpost]
  unfold tableauProjector
  congr 2
  funext j
  by_cases hj : j = p
  · subst hj
    rw [Function.update_self]
    rw [show updM T M j b j = (⟨if b then 2 else 0, M⟩ : PauliString n) from if_pos rfl,
      signed_toMatrix]
  · rw [Function.update_of_ne hj]
    simp only [g, if_neg hj]

/-! ## Session 5: validity of the random-outcome update `updM` -/

lemma gen_mul_proj' {n : ℕ} (T : Tableau n) (h1 : ∀ j, (T j).phase = 0 ∨ (T j).phase = 2)
    (h2 : ∀ i j, (T i).Commute (T j)) (j : Fin n) :
    (T j).toMatrix * tableauProjector T = tableauProjector T := by
  unfold tableauProjector
  rw [ofFn_prod_move n _ j (fun i => commute_QQ _ _
      (h2 j i : Commute (T j).toMatrix (T i).toMatrix)), ← Matrix.mul_assoc,
    gen_mul_Q _ (h1 j)]

lemma proj_mul_gen' {n : ℕ} (T : Tableau n) (h1 : ∀ j, (T j).phase = 0 ∨ (T j).phase = 2)
    (h2 : ∀ i j, (T i).Commute (T j)) (j : Fin n) :
    tableauProjector T * (T j).toMatrix = tableauProjector T := by
  rw [← (commute_proj T _ (fun i => (h2 j i : Commute (T j).toMatrix (T i).toMatrix))).eq,
    gen_mul_proj' T h1 h2 j]

lemma comm_subProd {n : ℕ} (T : Tableau n) (A : Matrix (Qubits n) (Qubits n) ℂ)
    (s : Finset (Fin n)) (h : ∀ i ∈ s, Commute A (T i).toMatrix) : Commute A (subProd T s) := by
  unfold subProd
  apply Commute.list_prod_right
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split_ifs with hi
  · exact h i hi
  · exact Commute.one_right _

lemma anti_comm_zero {m : Type*} [Fintype m] [DecidableEq m] (A Z : Matrix m m ℂ)
    (hA : A * A = 1) (h1 : A * Z = Z * A) (h2 : A * Z = -(Z * A)) : Z = 0 := by
  have h3 : (2 : ℂ) • (Z * A) = 0 := by
    rw [two_smul]
    calc Z * A + Z * A = A * Z + Z * A := by rw [h1]
      _ = 0 := by rw [h2, neg_add_cancel]
  have h4 : Z * A = 0 := (smul_eq_zero.mp h3).resolve_left two_ne_zero
  calc Z = Z * A * A := by rw [Matrix.mul_assoc, hA, Matrix.mul_one]
    _ = 0 := by rw [h4, Matrix.zero_mul]

lemma anti_mul {m : Type*} [Fintype m] [DecidableEq m] (A X Y : Matrix m m ℂ)
    (hX : A * X = -(X * A)) (hY : A * Y = Y * A) (r : ℂ) :
    A * (r • (X * Y)) = -((r • (X * Y)) * A) := by
  calc A * (r • (X * Y)) = r • (A * X * Y) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
    _ = r • (-(X * (A * Y))) := by rw [hX, neg_mul, Matrix.mul_assoc]
    _ = r • (-(X * (Y * A))) := by rw [hY]
    _ = -((r • (X * Y)) * A) := by rw [Matrix.smul_mul, Matrix.mul_assoc, smul_neg]

def pw {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (k : Bool) : Matrix m m ℂ :=
  if k then A else 1

lemma pw_mul {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (hA : A * A = 1)
    (a k : Bool) : pw A a * pw A k = pw A (xor a k) := by
  cases a <;> cases k <;> simp [pw, hA]

lemma comm_pw {m : Type*} [Fintype m] [DecidableEq m] (B A : Matrix m m ℂ) (h : Commute B A)
    (k : Bool) : Commute B (pw A k) := by
  cases k <;> simp [pw, h]

lemma subProd_insert {n : ℕ} (T : Tableau n) (hc : ∀ i j, (T i).Commute (T j))
    (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) :
    subProd T (insert i s) = (T i).toMatrix * subProd T s := by
  rw [subProd_erase T hc (insert i s) i (Finset.mem_insert_self i s), Finset.erase_insert hi]

lemma updM_ne {n : ℕ} (T : Tableau n) (M : Fin n → Pauli) (p : Fin n) (b : Bool) (j : Fin n)
    (hj : j ≠ p) :
    (updM T M p b j).toMatrix = (T j).toMatrix * pw (T p).toMatrix (antiB (T j) ⟨0, M⟩) := by
  simp only [updM, if_neg hj]
  split_ifs with ha
  · rw [toMatrix_mul]; simp [pw, ha]
  · simp [pw, ha]

lemma updM_phase {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli) (p : Fin n)
    (b : Bool) : ∀ j, (updM T M p b j).phase = 0 ∨ (updM T M p b j).phase = 2 := by
  intro j
  by_cases hj : j = p
  · rw [hj, show updM T M p b p = (⟨if b then 2 else 0, M⟩ : PauliString n) from if_pos rfl]
    cases b <;> simp
  · simp only [updM, if_neg hj]
    split_ifs
    · exact mul_phase_even _ _ (hT.1 j) (hT.1 p) (hT.2.1 j p)
    · exact hT.1 j

lemma updM_commT {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli) (p : Fin n)
    (b : Bool) (j : Fin n) (hj : j ≠ p) (k : Fin n) :
    Commute (T k).toMatrix (updM T M p b j).toMatrix := by
  rw [updM_ne T M p b j hj]
  exact (show Commute (T k).toMatrix (T j).toMatrix from hT.2.1 k j).mul_right
    (comm_pw _ _ (show Commute (T k).toMatrix (T p).toMatrix from hT.2.1 k p) _)

lemma updM_commM {n : ℕ} (T : Tableau n) (M : Fin n → Pauli) (p : Fin n)
    (hp : antiB (T p) ⟨0, M⟩ = true) (b : Bool) (j : Fin n) (hj : j ≠ p) :
    Commute (⟨0, M⟩ : PauliString n).toMatrix (updM T M p b j).toMatrix := by
  rw [updM_ne T M p b j hj]
  cases ha : antiB (T j) ⟨0, M⟩
  · simp only [pw, Bool.false_eq_true, ↓reduceIte, Matrix.mul_one]
    exact (show Commute (T j).toMatrix _ from comm_of_antiB_false _ _ ha).symm
  · simp only [pw, ↓reduceIte]
    have e1 : (⟨0, M⟩ : PauliString n).toMatrix * (T j).toMatrix =
        -((T j).toMatrix * (⟨0, M⟩ : PauliString n).toMatrix) := by
      rw [anti_of_antiB_true _ _ ha, neg_neg]
    have e2 : (⟨0, M⟩ : PauliString n).toMatrix * (T p).toMatrix =
        -((T p).toMatrix * (⟨0, M⟩ : PauliString n).toMatrix) := by
      rw [anti_of_antiB_true _ _ hp, neg_neg]
    show _ * (_ * _) = (_ * _) * _
    rw [← Matrix.mul_assoc, e1, neg_mul, Matrix.mul_assoc, e2, mul_neg, neg_neg,
      Matrix.mul_assoc]

lemma updM_comm {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli) (p : Fin n)
    (hp : antiB (T p) ⟨0, M⟩ = true) (b : Bool) (i j : Fin n) :
    (updM T M p b i).Commute (updM T M p b j) := by
  show Commute _ _
  have hpM : ∀ j, j ≠ p → Commute (updM T M p b p).toMatrix (updM T M p b j).toMatrix :=
    fun j hj => by
      rw [show updM T M p b p = (⟨if b then 2 else 0, M⟩ : PauliString n) from if_pos rfl,
        signed_toMatrix]
      exact (updM_commM T M p hp b j hj).smul_left _
  by_cases hi : i = p <;> by_cases hj : j = p
  · have e : i = j := hi.trans hj.symm
    subst e; exact Commute.refl _
  · rw [hi]; exact hpM j hj
  · rw [hj]; exact (hpM i hi).symm
  · rw [updM_ne T M p b i hi]
    exact (updM_commT T hT M p b j hj i).mul_left
      (comm_pw _ _ (updM_commT T hT M p b j hj p).symm _).symm

lemma updM_trace {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli) (p : Fin n)
    (hp : antiB (T p) ⟨0, M⟩ = true) (b : Bool) :
    (tableauProjector (updM T M p b)).trace = 1 := by
  rw [rand_proj T hT M p hp b]
  have hQQ := proj_sq _ (toMatrix_sq (⟨0, M⟩ : PauliString n) (Or.inl rfl))
    (if b then -1 else 1 : ℂ) (by cases b <;> simp)
  have htr := trace_meas_anti T hT (⟨0, M⟩ : PauliString n).toMatrix p
    (by rw [anti_of_antiB_true _ _ hp, neg_neg]) (if b then -1 else 1 : ℂ)
  rw [Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQQ, htr]
  norm_num

lemma updM_cond4 {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli) (p : Fin n)
    (hp : antiB (T p) ⟨0, M⟩ = true) (b : Bool) (s : Finset (Fin n)) :
    subProd (updM T M p b) s ≠ -1 := by
  intro h
  have h1 := updM_phase T hT M p b
  have h2 := updM_comm T hT M p hp b
  have hfix : tableauProjector (updM T M p b) * subProd (updM T M p b) s =
      tableauProjector (updM T M p b) := by
    unfold subProd
    apply mul_list_prod_fix
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    split_ifs
    · exact proj_mul_gen' _ h1 h2 i
    · exact mul_one _
  rw [h, mul_neg, mul_one] at hfix
  have ht := congrArg Matrix.trace hfix
  rw [Matrix.trace_neg, updM_trace T hT M p hp b] at ht
  norm_num at ht

lemma updM_subProd {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli)
    (p : Fin n) (hp : antiB (T p) ⟨0, M⟩ = true) (b : Bool) (s : Finset (Fin n)) (hs : p ∉ s) :
    ∃ k : Bool, subProd (updM T M p b) s = subProd T s * pw (T p).toMatrix k := by
  have hTp := toMatrix_sq _ (hT.1 p)
  revert hs
  induction s using Finset.induction_on with
  | empty => intro _; exact ⟨false, by simp [subProd, pw]⟩
  | @insert i s hi ih =>
    intro hs
    have hip : i ≠ p := fun e => hs (e ▸ Finset.mem_insert_self i s)
    obtain ⟨k, hk⟩ := ih (fun h => hs (Finset.mem_insert_of_mem h))
    refine ⟨xor (antiB (T i) ⟨0, M⟩) k, ?_⟩
    have hcS : Commute (pw (T p).toMatrix (antiB (T i) ⟨0, M⟩)) (subProd T s) :=
      (comm_pw _ _ (comm_subProd T (T p).toMatrix s (fun l _ => hT.2.1 p l)).symm _).symm
    rw [subProd_insert _ (updM_comm T hT M p hp b) s i hi, subProd_insert _ hT.2.1 s i hi, hk,
      updM_ne T M p b i hip]
    simp only [Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc, hcS.eq, Matrix.mul_assoc, pw_mul _ hTp]

lemma updM_cond3 {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli) (p : Fin n)
    (hp : antiB (T p) ⟨0, M⟩ = true) (b : Bool) (j : Fin n) (s : Finset (Fin n)) (hj : j ∉ s)
    (c : ZMod 4) :
    (updM T M p b j).toMatrix ≠ Complex.I ^ c.val • subProd (updM T M p b) s := by
  intro h
  have hTp := toMatrix_sq _ (hT.1 p)
  have hU1 := updM_phase T hT M p b
  have hUc := updM_comm T hT M p hp b
  have hne : ∀ k, (updM T M p b k).toMatrix ≠ 0 := fun k h0 => by
    have h' := toMatrix_sq _ (hU1 k)
    rw [h0, Matrix.zero_mul] at h'
    haveI : Nonempty (Qubits n) := ⟨fun _ => false⟩
    exact zero_ne_one h'
  have hpp : (T p).toMatrix * (updM T M p b p).toMatrix =
      -((updM T M p b p).toMatrix * (T p).toMatrix) := by
    rw [show updM T M p b p = (⟨if b then 2 else 0, M⟩ : PauliString n) from if_pos rfl,
      signed_toMatrix, Matrix.mul_smul, Matrix.smul_mul, anti_of_antiB_true _ _ hp, smul_neg]
  by_cases hjp : j = p
  · rw [hjp] at h hj
    apply hne p
    refine anti_comm_zero (T p).toMatrix _ hTp ?_ hpp
    rw [h]
    exact ((comm_subProd (updM T M p b) (T p).toMatrix s
      (fun i hi => updM_commT T hT M p b i (fun e => hj (e ▸ hi)) p)).smul_right _).eq
  by_cases hps : p ∈ s
  · apply hne j
    rw [subProd_erase _ hUc s p hps] at h
    refine anti_comm_zero (T p).toMatrix _ hTp (updM_commT T hT M p b j hjp p).eq ?_
    rw [h]
    exact anti_mul _ _ _ hpp (comm_subProd (updM T M p b) (T p).toMatrix _
      (fun i hi => updM_commT T hT M p b i (Finset.ne_of_mem_erase hi) p)).eq _
  · obtain ⟨k, hk⟩ := updM_subProd T hT M p hp b s hps
    rw [hk, updM_ne T M p b j hjp] at h
    have hS := comm_subProd T (T p).toMatrix s (fun i _ => hT.2.1 p i)
    have key : (T j).toMatrix = Complex.I ^ c.val •
        (subProd T s * pw (T p).toMatrix (xor k (antiB (T j) ⟨0, M⟩))) := by
      have h' := congrArg (· * pw (T p).toMatrix (antiB (T j) ⟨0, M⟩)) h
      rw [Matrix.mul_assoc, pw_mul _ hTp, Bool.xor_self, Matrix.smul_mul, Matrix.mul_assoc,
        pw_mul _ hTp] at h'
      rw [← h']; simp [pw]
    cases hx : xor k (antiB (T j) ⟨0, M⟩)
    · rw [hx] at key
      simp only [pw, Bool.false_eq_true, ↓reduceIte, mul_one] at key
      exact hT.2.2.1 j s hj c key
    · rw [hx] at key
      simp only [pw, ↓reduceIte] at key
      rw [← hS.eq, ← subProd_insert T hT.2.1 s p hps] at key
      exact hT.2.2.1 j (insert p s) (by simp [hjp, hj]) c key

theorem valid_updM {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli)
    (p : Fin n) (hp : antiB (T p) ⟨0, M⟩ = true) (b : Bool) : IsValidTableau (updM T M p b) :=
  ⟨updM_phase T hT M p b, updM_comm T hT M p hp b,
    fun j s hj c => updM_cond3 T hT M p hp b j s hj c, updM_cond4 T hT M p hp b⟩

/-! ## Session 5: the explicit update `updQ` and ChildStepQ (Q half of ChildStep) -/

/-- First generator anticommuting with `M` (symbolic test). -/
def firstAnti {n : ℕ} (T : Tableau n) (M : Fin n → Pauli) : Option (Fin n) :=
  (List.finRange n).reverse.find? (fun j => antiB (T j) ⟨0, M⟩)

lemma firstAnti_some {n : ℕ} {T : Tableau n} {M : Fin n → Pauli} {p : Fin n}
    (h : firstAnti T M = some p) : antiB (T p) ⟨0, M⟩ = true := by
  have := List.find?_some h
  simpa using this

lemma firstAnti_none {n : ℕ} {T : Tableau n} {M : Fin n → Pauli}
    (h : firstAnti T M = none) : ∀ j, antiB (T j) ⟨0, M⟩ = false := by
  intro j
  have := List.find?_eq_none.mp h j (List.mem_reverse.mpr (List.mem_finRange j))
  simpa using this

def DetOK {n : ℕ} (T : Tableau n) (M : Fin n → Pauli) (β : Bool) : Prop :=
  (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix)) *
        tableauProjector T).trace = 1 ∧
      ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix)) *
        tableauProjector T *
        ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix)) =
        tableauProjector T

/-- The deterministic outcome (classically chosen; unique since the two traces sum to 1). -/
noncomputable def betaDet {n : ℕ} (T : Tableau n) (M : Fin n → Pauli) : Bool := by
  classical
  exact if h : ∃ β, DetOK T M β then h.choose else false

lemma betaDet_spec {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli)
    (hcm : ∀ j, antiB (T j) ⟨0, M⟩ = false) : DetOK T M (betaDet T M) := by
  have hex : ∃ β, DetOK T M β := det_meas T hT M hcm
  unfold betaDet
  rw [dif_pos hex]
  exact hex.choose_spec

lemma zsign {m : Type*} [Fintype m] [DecidableEq m] (β : Bool) (X : Matrix m m ℂ) :
    (if β then (-1 : ℤ) else 1) • X = (if β then (-1 : ℂ) else 1) • X := by
  cases β <;> simp

noncomputable def measUpd {n : ℕ} (T : Tableau n) (M : Fin n → Pauli) (b : Bool) :
    Tableau n × Option Bool :=
  match firstAnti T M with
  | some p => (updM T M p b, some b)
  | none => (T, some (betaDet T M))

noncomputable def updQ (n : ℕ) (op : CliffordOp n) (T : Tableau n) (b : Bool) :
    Tableau n × Option Bool :=
  match op with
  | .measure M => measUpd T M b
  | _ => (updG op T, none)

lemma updQ_gate {n : ℕ} (op : CliffordOp n) (T : Tableau n) (b : Bool)
    (hop : ∀ M, op ≠ .measure M) : updQ n op T b = (updG op T, none) := by
  cases op <;> first | rfl | exact absurd rfl (hop _)

theorem stepQ_valid (n : ℕ) (op : CliffordOp n) (T : Tableau n) (b : Bool)
    (hT : IsValidTableau T) : IsValidTableau (updQ n op T b).1 := by
  by_cases hm : ∃ M, op = .measure M
  · obtain ⟨M, rfl⟩ := hm
    show IsValidTableau (measUpd T M b).1
    unfold measUpd
    cases h : firstAnti T M with
    | some p => exact valid_updM T hT M p (firstAnti_some h) b
    | none => exact hT
  · simp only [not_exists] at hm
    rw [updQ_gate op T b hm]
    exact (gate_step op T hT hm).1

theorem childStepQ :
    (∀ n op T b, IsValidTableau T → IsValidTableau (updQ n op T b).1) ∧
    (∀ n (op : CliffordOp n) T b, IsValidTableau T → (∀ M, op ≠ .measure M) →
        (updQ n op T b).2 = none ∧
        tableauProjector (updQ n op T b).1 = op.mat * tableauProjector T * op.mat.conjTranspose) ∧
    (∀ n (M : Fin n → Pauli) T b, IsValidTableau T →
      ∃ β, (updQ n (.measure M) T b).2 = some β ∧
        (((((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))) *
              tableauProjector T).trace = 1 ∧
            ∀ b', updQ n (.measure M) T b' = updQ n (.measure M) T b) ∨
          ((((2⁻¹ : ℂ) • (1 + (-1 : ℂ) • (PauliString.toMatrix ⟨0, M⟩))) *
              tableauProjector T).trace = 2⁻¹ ∧ β = b)) ∧
        tableauProjector (updQ n (.measure M) T b).1 =
          (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))) *
              tableauProjector T).trace⁻¹ •
            (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))) *
              tableauProjector T *
              ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))))) := by
  refine ⟨fun n op T b hT => stepQ_valid n op T b hT, fun n op T b hT hop => ?_,
    fun n M T b hT => ?_⟩
  · rw [updQ_gate op T b hop]
    exact ⟨rfl, (gate_step op T hT hop).2⟩
  · have e : ∀ b', updQ n (.measure M) T b' = measUpd T M b' := fun _ => rfl
    simp only [e, zsign]
    unfold measUpd
    cases h : firstAnti T M with
    | some p =>
      have hp := firstAnti_some h
      have hMT : (⟨0, M⟩ : PauliString n).toMatrix * (T p).toMatrix =
          -((T p).toMatrix * (⟨0, M⟩ : PauliString n).toMatrix) := by
        rw [anti_of_antiB_true _ _ hp, neg_neg]
      refine ⟨b, rfl, Or.inr ⟨trace_meas_anti T hT _ p hMT (-1), rfl⟩, ?_⟩
      show tableauProjector (updM T M p b) = _
      rw [rand_proj T hT M p hp b, trace_meas_anti T hT _ p hMT _, inv_inv]
    | none =>
      obtain ⟨htr, hfix⟩ := betaDet_spec T hT M (firstAnti_none h)
      refine ⟨betaDet T M, rfl, Or.inl ⟨htr, fun b' => rfl⟩, ?_⟩
      show tableauProjector T = _
      rw [htr, inv_one, one_smul, hfix]

/-! ## Session 5: bridge for a symbolic deterministic outcome (K side): if some subproduct of
generators equals `±M`, that sign is `betaDet`. -/

lemma rho_fix_subProd {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (s : Finset (Fin n)) :
    tableauProjector T * subProd T s = tableauProjector T := by
  unfold subProd
  apply mul_list_prod_fix
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split_ifs
  · exact proj_mul_gen T hT i
  · exact mul_one _

lemma trace_Q_of_subProd {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli)
    (s : Finset (Fin n)) (σ : Bool)
    (h : subProd T s = (if σ then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix) (c : ℂ) :
    (((2⁻¹ : ℂ) • (1 + c • (⟨0, M⟩ : PauliString n).toMatrix)) * tableauProjector T).trace =
      2⁻¹ * (1 + c * (if σ then -1 else 1 : ℂ)) := by
  have hfix := rho_fix_subProd T hT s
  rw [h, Matrix.mul_smul] at hfix
  have hs2 : (if σ then -1 else 1 : ℂ) * (if σ then -1 else 1 : ℂ) = 1 := by cases σ <;> simp
  have hρM : tableauProjector T * (⟨0, M⟩ : PauliString n).toMatrix =
      (if σ then -1 else 1 : ℂ) • tableauProjector T := by
    calc tableauProjector T * (⟨0, M⟩ : PauliString n).toMatrix
        = ((if σ then -1 else 1 : ℂ) * (if σ then -1 else 1 : ℂ)) •
            (tableauProjector T * (⟨0, M⟩ : PauliString n).toMatrix) := by rw [hs2, one_smul]
      _ = (if σ then -1 else 1 : ℂ) • ((if σ then -1 else 1 : ℂ) •
            (tableauProjector T * (⟨0, M⟩ : PauliString n).toMatrix)) := by rw [smul_smul]
      _ = (if σ then -1 else 1 : ℂ) • tableauProjector T := by rw [hfix]
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_mul_comm (⟨0, M⟩ : PauliString n).toMatrix,
    hρM, Matrix.trace_smul, trace_tableauProjector T hT]
  simp only [smul_eq_mul]
  ring

theorem betaDet_of_subProd {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli)
    (hcm : ∀ j, antiB (T j) ⟨0, M⟩ = false) (s : Finset (Fin n)) (σ : Bool)
    (h : subProd T s = (if σ then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix) :
    betaDet T M = σ := by
  have hd := (betaDet_spec T hT M hcm).1
  rw [trace_Q_of_subProd T hT M s σ h] at hd
  cases hb : betaDet T M <;> rw [hb] at hd <;> cases σ <;> first | rfl | (norm_num at hd)

/-- Completeness of the stabilizer group: in the deterministic case `c_β M` (β = betaDet) is a
subproduct of the generators (so a symbolic search/elimination finds the outcome). -/
theorem det_in_group {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (M : Fin n → Pauli)
    (hcm : ∀ j, antiB (T j) ⟨0, M⟩ = false) :
    ∃ s : Finset (Fin n), subProd T s =
      (if betaDet T M then -1 else 1 : ℂ) • (⟨0, M⟩ : PauliString n).toMatrix := by
  obtain ⟨htr, -⟩ := betaDet_spec T hT M hcm
  have hMM := toMatrix_sq (⟨0, M⟩ : PauliString n) (Or.inl rfl)
  set c : ℂ := (if betaDet T M then -1 else 1 : ℂ) with hc
  have hc2 : c * c = 1 := by rw [hc]; cases betaDet T M <;> simp
  have hMρ : ((⟨0, M⟩ : PauliString n).toMatrix * tableauProjector T).trace = c := by
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.trace_add, Matrix.trace_smul, trace_tableauProjector T hT] at htr
    simp only [smul_eq_mul] at htr
    have h1 : c * ((⟨0, M⟩ : PauliString n).toMatrix * tableauProjector T).trace = 1 := by
      linear_combination 2 * htr
    calc ((⟨0, M⟩ : PauliString n).toMatrix * tableauProjector T).trace
        = (c * c) * ((⟨0, M⟩ : PauliString n).toMatrix * tableauProjector T).trace := by
          rw [hc2, one_mul]
      _ = c * (c * ((⟨0, M⟩ : PauliString n).toMatrix * tableauProjector T).trace) := by ring
      _ = c := by rw [h1, mul_one]
  by_contra hne
  push Not at hne
  have hzero : ∀ s, ((⟨0, M⟩ : PauliString n).toMatrix * subProd T s).trace = 0 := by
    intro s
    obtain ⟨P, hP⟩ := subProd_eq_toMatrix T s
    rw [hP, ← toMatrix_mul]
    by_cases hI : ∀ q, ((⟨0, M⟩ : PauliString n).mul P).ops q = .I
    · exfalso
      have e := toMatrix_of_allI _ hI
      generalize ((⟨0, M⟩ : PauliString n).mul P).phase.val = k at e
      rw [toMatrix_mul, ← hP] at e
      have e2 : subProd T s = Complex.I ^ k • (⟨0, M⟩ : PauliString n).toMatrix := by
        have := congrArg (fun X => (⟨0, M⟩ : PauliString n).toMatrix * X) e
        simp only [Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hMM,
          Matrix.one_mul] at this
        exact this
      have hfix := rho_fix_subProd T hT s
      rw [e2, Matrix.mul_smul] at hfix
      have ht := congrArg Matrix.trace hfix
      rw [Matrix.trace_smul, Matrix.trace_mul_comm, hMρ, trace_tableauProjector T hT,
        smul_eq_mul] at ht
      have hk : Complex.I ^ k = c := by
        calc Complex.I ^ k = Complex.I ^ k * (c * c) := by rw [hc2, mul_one]
          _ = (Complex.I ^ k * c) * c := by ring
          _ = c := by rw [ht, one_mul]
      exact hne s (by rw [e2, hk])
    · push Not at hI
      obtain ⟨q, hq⟩ := hI
      exact trace_toMatrix_of_ne _ q hq
  have h0 : ((⟨0, M⟩ : PauliString n).toMatrix * tableauProjector T).trace = 0 := by
    unfold tableauProjector
    rw [ofFn_prod_smul, ofFn_prod_one_add, Matrix.mul_smul, Matrix.trace_smul, Finset.mul_sum,
      Matrix.trace_sum]
    apply smul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro b _
    have := hzero (Finset.univ.filter fun i => b i = true)
    unfold subProd at this
    simpa using this
  rw [hMρ] at h0
  rw [h0] at hc2
  norm_num at hc2


/-! ## Session 6: K-side CHP destabilizer route (from e261f9b1_det.lean) -/

def bx : Pauli → ZMod 2 | .I => 0 | .X => 1 | .Y => 1 | .Z => 0
def bz : Pauli → ZMod 2 | .I => 0 | .X => 0 | .Y => 1 | .Z => 1

abbrev SV (n : ℕ) := Fin n ⊕ Fin n → ZMod 2

def sv {n : ℕ} (P : PauliString n) : SV n
  | .inl q => bx (P.ops q)
  | .inr q => bz (P.ops q)

def om {n : ℕ} (u v : SV n) : ZMod 2 :=
  ∑ q : Fin n, (u (.inl q) * v (.inr q) + u (.inr q) * v (.inl q))

lemma om_comm {n : ℕ} (u v : SV n) : om u v = om v u := by
  unfold om
  exact Finset.sum_congr rfl fun q _ => by ring

lemma om_add_right {n : ℕ} (u v w : SV n) : om u (v + w) = om u v + om u w := by
  unfold om
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by simp only [Pi.add_apply]; ring

lemma om_smul_right {n : ℕ} (u v : SV n) (c : ZMod 2) : om u (c • v) = c * om u v := by
  unfold om
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma om_zero_right {n : ℕ} (u : SV n) : om u 0 = 0 := by
  simp [om]

lemma om_sum_right {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : SV n)
    (c : ι → ZMod 2) (f : ι → SV n) :
    om u (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * om u (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [om_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, om_add_right,
      om_smul_right, ih]

lemma antiPair_eq (a b : Pauli) :
    (if antiPair a b = true then (1 : ZMod 2) else 0) = bx a * bz b + bz a * bx b := by
  cases a <;> cases b <;> decide

lemma om_sv_eq {n : ℕ} (P Q : PauliString n) :
    om (sv P) (sv Q) = if antiB P Q then 1 else 0 := by
  have hc : om (sv P) (sv Q) =
      ((Finset.univ.filter fun q => antiPair (P.ops q) (Q.ops q) = true).card : ZMod 2) := by
    rw [Finset.natCast_card_filter]
    exact Finset.sum_congr rfl fun q _ => (antiPair_eq _ _).symm
  rw [hc]
  unfold antiB
  generalize (Finset.univ.filter fun q => antiPair (P.ops q) (Q.ops q) = true).card = k
  split_ifs with h
  · obtain ⟨m, hm⟩ : Odd k := by simpa using h
    rw [hm]; push_cast
    rw [show (2 : ZMod 2) = 0 from rfl]; ring
  · exact ZMod.natCast_eq_zero_iff_even.2 (Nat.not_odd_iff_even.1 (by simpa using h))

lemma sv_mul {n : ℕ} (P Q : PauliString n) : sv (P.mul Q) = sv P + sv Q := by
  funext k
  cases k with
  | inl q =>
    show bx (Pauli.mul (P.ops q) (Q.ops q)).2 = bx (P.ops q) + bx (Q.ops q)
    generalize P.ops q = a; generalize Q.ops q = b
    cases a <;> cases b <;> decide
  | inr q =>
    show bz (Pauli.mul (P.ops q) (Q.ops q)).2 = bz (P.ops q) + bz (Q.ops q)
    generalize P.ops q = a; generalize Q.ops q = b
    cases a <;> cases b <;> decide

lemma sv_oneP (n : ℕ) : sv (oneP n) = 0 := by
  funext k; cases k <;> rfl

lemma sv_foldr {n : ℕ} : ∀ L : List (PauliString n),
    sv (L.foldr PauliString.mul (oneP n)) = (L.map sv).sum
  | [] => by simp [sv_oneP]
  | P :: L => by simp [sv_mul, sv_foldr L]

lemma ops_eq_of_sv {n : ℕ} (P Q : PauliString n) (h : sv P = sv Q) : P.ops = Q.ops := by
  funext q
  have h1 : bx (P.ops q) = bx (Q.ops q) := congrFun h (.inl q)
  have h2 : bz (P.ops q) = bz (Q.ops q) := congrFun h (.inr q)
  revert h1 h2
  generalize P.ops q = a; generalize Q.ops q = b
  cases a <;> cases b <;> decide

/-! ### The symplectic-basis argument over GF(2) -/

section Span
variable {n : ℕ} (g d : Fin n → SV n)

lemma pair_g (hgg : ∀ i j, om (g i) (g j) = 0)
    (hgd : ∀ i j, om (g i) (d j) = if j = i then 1 else 0) (c : Fin n ⊕ Fin n → ZMod 2) (k : Fin n) :
    om (g k) (∑ x, c x • Sum.elim g d x) = c (.inr k) := by
  rw [om_sum_right, Fintype.sum_sum_type]
  simp [hgg, hgd]

lemma pair_d (hdg : ∀ i j, om (d i) (g j) = if i = j then 1 else 0)
    (c : Fin n ⊕ Fin n → ZMod 2) (k : Fin n) :
    om (d k) (∑ x, c x • Sum.elim g d x) = c (.inl k) + ∑ j, c (.inr j) * om (d k) (d j) := by
  rw [om_sum_right, Fintype.sum_sum_type]
  simp [hdg]

theorem span_coeffs (hgg : ∀ i j, om (g i) (g j) = 0)
    (hdg : ∀ i j, om (d i) (g j) = if i = j then 1 else 0) (v : SV n)
    (hv : ∀ k, om (g k) v = 0) : v = ∑ j, om (d j) v • g j := by
  have hgd : ∀ i j, om (g i) (d j) = if j = i then 1 else 0 := by
    intro i j; rw [om_comm]; exact hdg j i
  have hli : LinearIndependent (ZMod 2) (Sum.elim g d) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hr : ∀ k, c (.inr k) = 0 := by
      intro k
      have := pair_g g d hgg hgd c k
      rw [hc, om_zero_right] at this
      exact this.symm
    have hl : ∀ k, c (.inl k) = 0 := by
      intro k
      have := pair_d g d hdg c k
      rw [hc, om_zero_right] at this
      simpa [hr] using this.symm
    intro x
    cases x with
    | inl k => exact hl k
    | inr k => exact hr k
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card])
  have hvm : v ∈ Submodule.span (ZMod 2) (Set.range (Sum.elim g d)) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hvm
  have hr : ∀ k, c (.inr k) = 0 := by
    intro k
    have := pair_g g d hgg hgd c k
    rw [hc, hv k] at this
    exact this.symm
  have hl : ∀ k, c (.inl k) = om (d k) v := by
    intro k
    have := pair_d g d hdg c k
    rw [hc] at this
    simpa [hr] using this.symm
  conv_lhs => rw [← hc]
  rw [Fintype.sum_sum_type]
  simp [hr, hl]

end Span

/-- The ordered symbolic product of the generators `T j` with `j ∈ s` (as in subProd_eq_toMatrix). -/
def prodSel {n : ℕ} (T : Fin n → PauliString n) (s : Finset (Fin n)) : PauliString n :=
  (List.ofFn fun i => if i ∈ s then T i else oneP n).foldr PauliString.mul (oneP n)

lemma sv_prodSel {n : ℕ} (T : Fin n → PauliString n) (s : Finset (Fin n)) :
    sv (prodSel T s) = ∑ i, (if i ∈ s then (1 : ZMod 2) else 0) • sv (T i) := by
  unfold prodSel
  rw [sv_foldr, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  split_ifs <;> simp [sv_oneP]

/-- Deterministic measurement, symbolically (Aaronson-Gottesman with destabilizers). -/
def detSel {n : ℕ} (D : Fin n → PauliString n) (M : Fin n → Pauli) : Finset (Fin n) :=
  Finset.univ.filter fun j => antiB (D j) ⟨0, M⟩ = true

theorem det_ops {n : ℕ} (T D : Fin n → PauliString n)
    (hTT : ∀ i j, antiB (T i) (T j) = false)
    (hDT : ∀ i j, antiB (D i) (T j) = decide (i = j))
    (M : Fin n → Pauli) (hM : ∀ j, antiB (T j) ⟨0, M⟩ = false) :
    (prodSel T (detSel D M)).ops = M := by
  apply ops_eq_of_sv (prodSel T (detSel D M)) ⟨0, M⟩
  rw [sv_prodSel]
  have key := span_coeffs (fun j => sv (T j)) (fun j => sv (D j))
    (fun i j => by rw [om_sv_eq, hTT]; rfl)
    (fun i j => by rw [om_sv_eq, hDT]; by_cases h : i = j <;> simp [h])
    (sv (⟨0, M⟩ : PauliString n)) (fun k => by rw [om_sv_eq, hM]; rfl)
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [om_sv_eq]
  simp [detSel]

/-! ### Session 6b: destabilizer invariant preserved by gates and random measurements -/

def wt (a b : Pauli) : ZMod 2 := bx a * bz b + bz a * bx b

lemma om_sv_w {n : ℕ} (P Q : PauliString n) :
    om (sv P) (sv Q) = ∑ q, wt (P.ops q) (Q.ops q) := rfl

lemma antiB_of_om {n : ℕ} {P Q : PauliString n} {c : Bool}
    (h : om (sv P) (sv Q) = if c then 1 else 0) : antiB P Q = c := by
  rw [om_sv_eq] at h
  cases h1 : antiB P Q <;> cases c <;> simp_all

lemma antiB_eq_of_om {n : ℕ} {P Q P' Q' : PauliString n}
    (h : om (sv P') (sv Q') = om (sv P) (sv Q)) : antiB P' Q' = antiB P Q :=
  antiB_of_om (h.trans (om_sv_eq P Q))

lemma om_conj {n : ℕ} (f : Pauli → ZMod 4 × Pauli) (hf : ∀ a b, wt (f a).2 (f b).2 = wt a b)
    (q : Fin n) (P Q : PauliString n) :
    om (sv (conjPS f q P)) (sv (conjPS f q Q)) = om (sv P) (sv Q) := by
  rw [om_sv_w, om_sv_w]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : r = q
  · subst h; simp [conjPS, hf]
  · simp [conjPS, Function.update_of_ne h]

lemma wt_cnot (a b c d : Pauli) :
    wt (cnotTab a b).2.1 (cnotTab c d).2.1 + wt (cnotTab a b).2.2 (cnotTab c d).2.2 =
      wt a c + wt b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma sum_two_split {n : ℕ} {c t : Fin n} (hct : c ≠ t) (G : Fin n → ZMod 2) :
    ∑ r, G r = G c + G t + ∑ r ∈ (Finset.univ.erase c).erase t, G r := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hct, Finset.mem_univ t⟩)]
  ring

lemma om_cnot {n : ℕ} (c t : Fin n) (hct : c ≠ t) (P Q : PauliString n) :
    om (sv (cnotPS c t P)) (sv (cnotPS c t Q)) = om (sv P) (sv Q) := by
  have ec : ∀ R : PauliString n, (cnotPS c t R).ops c = (cnotTab (R.ops c) (R.ops t)).2.1 := by
    intro R; simp [cnotPS, Function.update_of_ne hct]
  have et : ∀ R : PauliString n, (cnotPS c t R).ops t = (cnotTab (R.ops c) (R.ops t)).2.2 := by
    intro R; simp [cnotPS]
  have er : ∀ (R : PauliString n) r, r ∈ (Finset.univ.erase c).erase t →
      (cnotPS c t R).ops r = R.ops r := by
    intro R r hr
    have h1 : r ≠ t := (Finset.mem_erase.1 hr).1
    have h2 : r ≠ c := (Finset.mem_erase.1 (Finset.mem_erase.1 hr).2).1
    simp [cnotPS, Function.update_of_ne h1, Function.update_of_ne h2]
  rw [om_sv_w, om_sv_w, sum_two_split hct, sum_two_split hct (fun q => wt (P.ops q) (Q.ops q)),
    ec, et, ec, et, Finset.sum_congr rfl fun r hr => by rw [er P r hr, er Q r hr]]
  rw [wt_cnot]

theorem antiB_updG {n : ℕ} (op : CliffordOp n) (D T : Tableau n) (i j : Fin n) :
    antiB (updG op D i) (updG op T j) = antiB (D i) (T j) := by
  cases op with
  | pauli q P =>
    exact antiB_eq_of_om (om_conj _ (fun a b => by cases P <;> cases a <;> cases b <;> decide) q _ _)
  | h q => exact antiB_eq_of_om (om_conj _ (fun a b => by cases a <;> cases b <;> decide) q _ _)
  | s q => exact antiB_eq_of_om (om_conj _ (fun a b => by cases a <;> cases b <;> decide) q _ _)
  | cnot c t hct => exact antiB_eq_of_om (om_cnot c t hct _ _)
  | measure M => rfl

/-- Destabilizer update for a random measurement at the first anticommuting generator `p`. -/
def updDM {n : ℕ} (T D : Tableau n) (M : Fin n → Pauli) (p : Fin n) : Tableau n :=
  fun i => if i = p then T p else if antiB (D i) ⟨0, M⟩ then (D i).mul (T p) else D i

/-- The symbolic CHP invariant: stabilizers commute, destabilizer `i` anticommutes exactly with `T i`. -/
def SympOK {n : ℕ} (T D : Tableau n) : Prop :=
  (∀ i j, antiB (T i) (T j) = false) ∧ ∀ i j, antiB (D i) (T j) = decide (i = j)

theorem symp_updG {n : ℕ} (op : CliffordOp n) (T D : Tableau n) (h : SympOK T D) :
    SympOK (updG op T) (updG op D) :=
  ⟨fun i j => (antiB_updG op T T i j).trans (h.1 i j),
    fun i j => (antiB_updG op D T i j).trans (h.2 i j)⟩

lemma om_add_left {n : ℕ} (u v w : SV n) : om (u + v) w = om u w + om v w := by
  rw [om_comm, om_add_right, om_comm w, om_comm w]

lemma om_smul_left {n : ℕ} (u v : SV n) (c : ZMod 2) : om (c • u) v = c * om u v := by
  rw [om_comm, om_smul_right, om_comm]

lemma om_self {n : ℕ} (u : SV n) : om u u = 0 := by
  unfold om
  refine Finset.sum_eq_zero fun q _ => ?_
  generalize u (.inl q) = a; generalize u (.inr q) = b
  revert a b; decide

lemma ite_om {n : ℕ} (P Q : PauliString n) :
    (if antiB P Q = true then (1 : ZMod 2) else 0) = om (sv P) (sv Q) := by
  rw [om_sv_eq]

lemma sv_mk {n : ℕ} (ph : ZMod 4) (M : Fin n → Pauli) :
    sv (⟨ph, M⟩ : PauliString n) = sv (⟨0, M⟩ : PauliString n) := rfl

lemma sv_cond {n : ℕ} (P Q R : PauliString n) :
    sv (if antiB P R = true then P.mul Q else P) = sv P + om (sv P) (sv R) • sv Q := by
  rw [om_sv_eq]
  split_ifs <;> simp [sv_mul]

theorem symp_updM {n : ℕ} (T D : Tableau n) (h : SympOK T D) (M : Fin n → Pauli) (p : Fin n)
    (b : Bool) (hp : antiB (T p) ⟨0, M⟩ = true) :
    SympOK (updM T M p b) (updDM T D M p) := by
  set m := sv (⟨0, M⟩ : PauliString n) with hm
  have hgg : ∀ i j, om (sv (T i)) (sv (T j)) = 0 := fun i j => by rw [om_sv_eq, h.1 i j]; rfl
  have hdg : ∀ i j, om (sv (D i)) (sv (T j)) = if i = j then 1 else 0 := fun i j => by
    rw [om_sv_eq, h.2 i j]; by_cases e : i = j <;> simp [e]
  have hap : om (sv (T p)) m = 1 := by rw [om_sv_eq, hp]; rfl
  have hT : ∀ j, sv (updM T M p b j) = if j = p then m else
      sv (T j) + om (sv (T j)) m • sv (T p) := by
    intro j; unfold updM
    by_cases e : j = p
    · rw [if_pos e, if_pos e]; exact sv_mk _ _
    · rw [if_neg e, if_neg e]; exact sv_cond _ _ _
  have hD : ∀ i, sv (updDM T D M p i) = if i = p then sv (T p) else
      sv (D i) + om (sv (D i)) m • sv (T p) := by
    intro i; unfold updDM
    by_cases e : i = p
    · rw [if_pos e, if_pos e]
    · rw [if_neg e, if_neg e]; exact sv_cond _ _ _
  have two : ∀ x : ZMod 2, x + x = 0 := by decide
  refine ⟨fun i j => antiB_of_om ?_, fun i j => antiB_of_om ?_⟩
  · rw [hT, hT]
    by_cases ei : i = p <;> by_cases ej : j = p
    · simp [ei, ej, om_self]
    · simp only [ei, ej, if_true, if_false, om_comm m]
      rw [om_add_left, om_smul_left, hap, mul_one, two]
      rfl
    · simp only [ei, ej, if_true, if_false, om_add_left, om_smul_left, hap]
      simp [two]
    · simp [ei, ej, om_add_left, om_add_right, om_smul_left, om_smul_right, hgg]
  · rw [hD, hT]
    by_cases ei : i = p <;> by_cases ej : j = p
    · simp [ei, ej, hap]
    · simp [ei, ej, om_add_right, om_smul_right, hgg]
      exact fun e => ej e.symm
    · simp only [ei, ej, if_true, if_false, om_add_left, om_smul_left, hap]
      simp [two]
    · simp [ei, ej, om_add_left, om_add_right, om_smul_left, om_smul_right, hgg, hdg]


/-! ### Session 6c: the symbolic deterministic outcome equals betaDet -/

lemma toMatrix_phase {n : ℕ} (ph : ZMod 4) (M : Fin n → Pauli) :
    (⟨ph, M⟩ : PauliString n).toMatrix = Complex.I ^ ph.val • (⟨0, M⟩ : PauliString n).toMatrix := by
  ext y z; simp [PauliString.toMatrix]

lemma foldr_phase_even {n : ℕ} : ∀ L : List (PauliString n),
    (∀ P ∈ L, P.phase = 0 ∨ P.phase = 2) → (∀ P ∈ L, ∀ Q ∈ L, P.Commute Q) →
    (L.foldr PauliString.mul (oneP n)).phase = 0 ∨ (L.foldr PauliString.mul (oneP n)).phase = 2
  | [] => fun _ _ => Or.inl rfl
  | P :: L => fun h1 h2 => by
    simp only [List.foldr_cons]
    apply mul_phase_even P _ (h1 P (by simp))
      (foldr_phase_even L (fun Q hQ => h1 Q (by simp [hQ]))
        (fun Q hQ R hR => h2 Q (by simp [hQ]) R (by simp [hR])))
    show P.toMatrix * _ = _ * P.toMatrix
    rw [← list_prod_toMatrix]
    exact (Commute.list_prod_right _ _ (fun y hy => by
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hy
      exact h2 P (by simp) Q (by simp [hQ]))).eq

lemma prodSel_phase_even {n : ℕ} (T : Tableau n) (hT : IsValidTableau T) (s : Finset (Fin n)) :
    (prodSel T s).phase = 0 ∨ (prodSel T s).phase = 2 := by
  have hel : ∀ P ∈ List.ofFn (fun i => if i ∈ s then T i else oneP n),
      P = oneP n ∨ ∃ i, P = T i := by
    intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hP
    split_ifs
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inl rfl
  apply foldr_phase_even
  · intro P hP
    rcases hel P hP with rfl | ⟨i, rfl⟩
    · exact Or.inl rfl
    · exact hT.1 i
  · intro P hP Q hQ
    show P.toMatrix * Q.toMatrix = Q.toMatrix * P.toMatrix
    rcases hel P hP with rfl | ⟨i, rfl⟩ <;> rcases hel Q hQ with rfl | ⟨j, rfl⟩
    · simp [oneP_toMatrix]
    · simp [oneP_toMatrix]
    · simp [oneP_toMatrix]
    · exact hT.2.1 i j

theorem betaDet_sym {n : ℕ} (T D : Tableau n) (hT : IsValidTableau T) (hS : SympOK T D)
    (M : Fin n → Pauli) (hcm : ∀ j, antiB (T j) ⟨0, M⟩ = false) :
    betaDet T M = decide ((prodSel T (detSel D M)).phase = 2) := by
  have hops : (prodSel T (detSel D M)).ops = M := det_ops T D hS.1 hS.2 M hcm
  have hsub : subProd T (detSel D M) = (prodSel T (detSel D M)).toMatrix := by
    rw [prodSel, ← list_prod_toMatrix, List.map_ofFn]
    unfold subProd
    congr 2
    funext i
    simp only [Function.comp_apply]
    split_ifs <;> simp [oneP_toMatrix]
  have hPM : (prodSel T (detSel D M)).toMatrix =
      Complex.I ^ (prodSel T (detSel D M)).phase.val • (⟨0, M⟩ : PauliString n).toMatrix := by
    have key : ∀ P : PauliString n, P.ops = M →
        P.toMatrix = Complex.I ^ P.phase.val • (⟨0, M⟩ : PauliString n).toMatrix := by
      rintro ⟨ph, ops⟩ rfl; exact toMatrix_phase ph _
    exact key _ hops
  rcases prodSel_phase_even T hT (detSel D M) with h0 | h2
  · rw [h0, show decide ((0 : ZMod 4) = 2) = false by decide]
    apply betaDet_of_subProd T hT M hcm (detSel D M) false
    rw [hsub, hPM, h0]; simp
  · rw [h2, show decide ((2 : ZMod 4) = 2) = true by decide]
    apply betaDet_of_subProd T hT M hcm (detSel D M) true
    rw [hsub, hPM, h2, show (2 : ZMod 4).val = 2 from rfl, Complex.I_sq]; simp

/-! ## Session 7: CHP state (stabilizers, destabilizers), computable update. -/

/-- The computational-basis tableau `T_j = (-1)^{x_j} Z_j` (same as in ChildInit). -/
def initTab (n : ℕ) (x : Qubits n) : Tableau n :=
  fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩

/-- Initial destabilizers `D_j = X_j`. -/
def initD (n : ℕ) : Tableau n :=
  fun j => ⟨0, fun q => if q = j then .X else .I⟩

theorem symp_init (n : ℕ) (x : Qubits n) : SympOK (initTab n x) (initD n) := by
  constructor
  · intro i j
    have key : ∀ q, antiPair ((initTab n x i).ops q) ((initTab n x j).ops q) = false := by
      intro q
      simp only [initTab]
      split_ifs <;> rfl
    unfold antiB
    simp [key]
  · intro i j
    have key : ∀ q, antiPair ((initD n i).ops q) ((initTab n x j).ops q) = decide (q = i ∧ q = j) := by
      intro q
      simp only [initD, initTab]
      by_cases hi : q = i <;> by_cases hj : q = j
      · rw [if_pos hi, if_pos hj]
        exact (by decide : antiPair .X .Z = true).trans (decide_eq_true ⟨hi, hj⟩).symm
      · rw [if_pos hi, if_neg hj]
        exact (by decide : antiPair .X .I = false).trans (decide_eq_false fun h => hj h.2).symm
      · rw [if_neg hi, if_pos hj]
        exact (by decide : antiPair .I .Z = false).trans (decide_eq_false fun h => hi h.1).symm
      · rw [if_neg hi, if_neg hj]
        exact (by decide : antiPair .I .I = false).trans (decide_eq_false fun h => hi h.1).symm
    have hf : (Finset.univ.filter fun q =>
        antiPair ((initD n i).ops q) ((initTab n x j).ops q) = true) =
        Finset.univ.filter fun q => q = i ∧ q = j :=
      Finset.filter_congr fun q _ => by rw [key q, decide_eq_true_iff]
    unfold antiB
    rw [hf]
    by_cases hij : i = j
    · subst hij
      have h1 : (Finset.univ.filter fun q : Fin n => q = i ∧ q = i) = {i} := by
        ext q; simp
      rw [h1]; simp
    · have h0 : (Finset.univ.filter fun q : Fin n => q = i ∧ q = j) = ∅ :=
        Finset.filter_false_of_mem fun q _ h => hij (h.1.symm.trans h.2)
      rw [h0]; simp [hij]

/-- Computable CHP update on (stabilizers, destabilizers). -/
def updC (n : ℕ) (op : CliffordOp n) (TD : Tableau n × Tableau n) (b : Bool) :
    (Tableau n × Tableau n) × Option Bool :=
  match op with
  | .measure M =>
    match firstAnti TD.1 M with
    | some p => ((updM TD.1 M p b, updDM TD.1 TD.2 M p), some b)
    | none => (TD, some (decide ((prodSel TD.1 (detSel TD.2 M)).phase = 2)))
  | _ => ((updG op TD.1, updG op TD.2), none)

lemma updC_gate {n : ℕ} (op : CliffordOp n) (TD : Tableau n × Tableau n) (b : Bool)
    (hop : ∀ M, op ≠ .measure M) : updC n op TD b = ((updG op TD.1, updG op TD.2), none) := by
  cases op <;> first | rfl | exact absurd rfl (hop _)

/-- Under the invariant, the CHP update agrees with the matrix-level update `updQ`. -/
theorem updC_eq {n : ℕ} (op : CliffordOp n) (T D : Tableau n) (b : Bool)
    (hT : IsValidTableau T) (hS : SympOK T D) :
    (updC n op (T, D) b).1.1 = (updQ n op T b).1 ∧ (updC n op (T, D) b).2 = (updQ n op T b).2 := by
  by_cases hm : ∃ M, op = .measure M
  · obtain ⟨M, rfl⟩ := hm
    show (updC n (.measure M) (T, D) b).1.1 = (measUpd T M b).1 ∧
      (updC n (.measure M) (T, D) b).2 = (measUpd T M b).2
    unfold measUpd
    simp only [updC]
    cases h : firstAnti T M with
    | some p => exact ⟨rfl, rfl⟩
    | none => exact ⟨rfl, by rw [betaDet_sym T D hT hS M (firstAnti_none h)]⟩
  · simp only [not_exists] at hm
    rw [updC_gate op _ b hm, updQ_gate op T b hm]
    exact ⟨rfl, rfl⟩

/-- The CHP invariant (validity + symplectic destabilizers) is preserved. -/
theorem inv_updC {n : ℕ} (op : CliffordOp n) (T D : Tableau n) (b : Bool)
    (hT : IsValidTableau T) (hS : SympOK T D) :
    IsValidTableau (updC n op (T, D) b).1.1 ∧
      SympOK (updC n op (T, D) b).1.1 (updC n op (T, D) b).1.2 := by
  refine ⟨(updC_eq op T D b hT hS).1 ▸ stepQ_valid n op T b hT, ?_⟩
  by_cases hm : ∃ M, op = .measure M
  · obtain ⟨M, rfl⟩ := hm
    simp only [updC]
    cases h : firstAnti T M with
    | some p => exact symp_updM T D hS M p b (firstAnti_some h)
    | none => exact hS
  · simp only [not_exists] at hm
    rw [updC_gate op _ b hm]
    exact symp_updG op T D hS

/-- Coin independence in the deterministic case. -/
lemma updC_det_coin {n : ℕ} (M : Fin n → Pauli) (T D : Tableau n) (h : firstAnti T M = none)
    (b b' : Bool) : updC n (.measure M) (T, D) b' = updC n (.measure M) (T, D) b := by
  simp only [updC, h]

/-- The matrix-level (Q) half of the restated ChildStep over the CHP state `(T, D)`. -/
theorem childStepC_Q :
    (∀ n x, IsValidTableau (initTab n x) → SympOK (initTab n x) (initD n)) ∧
    (∀ n op (T D : Tableau n) b, IsValidTableau T → SympOK T D →
      IsValidTableau (updC n op (T, D) b).1.1 ∧
        SympOK (updC n op (T, D) b).1.1 (updC n op (T, D) b).1.2) ∧
    (∀ n (op : CliffordOp n) (T D : Tableau n) b, IsValidTableau T → SympOK T D →
        (∀ M, op ≠ .measure M) →
        (updC n op (T, D) b).2 = none ∧
        tableauProjector (updC n op (T, D) b).1.1 =
          op.mat * tableauProjector T * op.mat.conjTranspose) ∧
    (∀ n (M : Fin n → Pauli) (T D : Tableau n) b, IsValidTableau T → SympOK T D →
      ∃ β, (updC n (.measure M) (T, D) b).2 = some β ∧
        (((((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))) *
              tableauProjector T).trace = 1 ∧
            ∀ b', updC n (.measure M) (T, D) b' = updC n (.measure M) (T, D) b) ∨
          ((((2⁻¹ : ℂ) • (1 + (-1 : ℂ) • (PauliString.toMatrix ⟨0, M⟩))) *
              tableauProjector T).trace = 2⁻¹ ∧ β = b)) ∧
        tableauProjector (updC n (.measure M) (T, D) b).1.1 =
          (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))) *
              tableauProjector T).trace⁻¹ •
            (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))) *
              tableauProjector T *
              ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))))) := by
  obtain ⟨_, hG, hM⟩ := childStepQ
  refine ⟨fun n x _ => symp_init n x, fun n op T D b hT hS => inv_updC op T D b hT hS,
    fun n op T D b hT hS hop => ?_, fun n M T D b hT hS => ?_⟩
  · obtain ⟨e1, e2⟩ := updC_eq op T D b hT hS
    rw [e1, e2]; exact hG n op T b hT hop
  · obtain ⟨e1, e2⟩ := updC_eq (.measure M) T D b hT hS
    obtain ⟨β, hβ, hcase, hproj⟩ := hM n M T b hT
    refine ⟨β, e2 ▸ hβ, ?_, e1 ▸ hproj⟩
    rcases hcase with ⟨htr, _⟩ | hr
    · refine Or.inl ⟨htr, fun b' => ?_⟩
      cases h : firstAnti T M with
      | none => exact updC_det_coin M T D h b b'
      | some p =>
        exfalso
        have hp := firstAnti_some h
        have hMT : (⟨0, M⟩ : PauliString n).toMatrix * (T p).toMatrix =
            -((T p).toMatrix * (⟨0, M⟩ : PauliString n).toMatrix) := by
          rw [anti_of_antiB_true _ _ hp, neg_neg]
        have h2 := trace_meas_anti T hT _ p hMT (if β then -1 else 1)
        rw [← zsign, htr] at h2
        norm_num at h2
    · exact Or.inr hr

/-- The diagonal of `(-1)^{x_j} Z_j`. -/
def dsgn {n : ℕ} (x : Qubits n) (j : Fin n) (y : Qubits n) : ℂ :=
  if y j = x j then 1 else -1

lemma list_prod_diagonal {m : Type*} [Fintype m] [DecidableEq m] (l : List (m → ℂ)) :
    (l.map Matrix.diagonal).prod = Matrix.diagonal (fun y => (l.map (fun g => g y)).prod) := by
  induction l with
  | nil => simp
  | cons g l ih => simp [ih, Matrix.diagonal_mul_diagonal]

lemma ofFn_prod_diagonal {m : Type*} [Fintype m] [DecidableEq m] {k : ℕ} (f : Fin k → m → ℂ) :
    (List.ofFn fun i => Matrix.diagonal (f i)).prod = Matrix.diagonal (fun y => ∏ i, f i y) := by
  have h : (List.ofFn fun i => Matrix.diagonal (f i)) = (List.ofFn f).map Matrix.diagonal := by
    rw [List.map_ofFn]; rfl
  rw [h, list_prod_diagonal]
  congr 1; funext y
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

lemma initTab_toMatrix {n : ℕ} (x : Qubits n) (j : Fin n) :
    (initTab n x j).toMatrix = Matrix.diagonal (dsgn x j) := by
  have h2 : ((2 : ZMod 4)).val = 2 := rfl
  ext y z
  by_cases hyz : y = z
  · subst hyz
    simp only [PauliString.toMatrix, initTab, Matrix.of_apply, Matrix.diagonal_apply_eq, dsgn]
    rw [Finset.prod_eq_single j]
    · by_cases hx : x j <;> by_cases hy : y j <;>
        simp [hx, hy, h2, Pauli.mat, pauliZ, Complex.I_sq]
    · intro q _ hq; simp [hq, Pauli.mat]
    · simp
  · rw [Matrix.diagonal_apply_ne _ hyz]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hyz
    simp only [PauliString.toMatrix, initTab, Matrix.of_apply]
    rw [Finset.prod_eq_zero (Finset.mem_univ q), mul_zero]
    by_cases hqj : q = j
    · subst hqj
      simp [Pauli.mat, pauliZ, Matrix.diagonal_apply_ne _ hq]
    · simp [hqj, Pauli.mat, Matrix.one_apply_ne hq]

lemma half_diag {n : ℕ} (x : Qubits n) (j : Fin n) :
    (2⁻¹ : ℂ) • (1 + (initTab n x j).toMatrix) =
      Matrix.diagonal (fun y => if y j = x j then (1 : ℂ) else 0) := by
  rw [initTab_toMatrix, ← Matrix.diagonal_one, Matrix.diagonal_add, ← Matrix.diagonal_smul]
  congr 1; funext y
  simp only [Pi.smul_apply, dsgn, smul_eq_mul]
  split_ifs <;> norm_num

lemma initTab_proj {n : ℕ} (x : Qubits n) :
    tableauProjector (initTab n x) = pureDensity (ket x) := by
  unfold tableauProjector
  simp_rw [half_diag]
  rw [ofFn_prod_diagonal]
  ext a b
  simp only [Matrix.diagonal_apply, pureDensity, ket, Matrix.of_apply, PiLp.single_apply]
  rw [Finset.prod_boole]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = x
    · subst ha; simp
    · simpa [ha] using Function.ne_iff.mp ha
  · by_cases ha : a = x
    · subst ha
      have hb : b ≠ a := Ne.symm hab
      simp [hab, hb]
    · simp [hab, ha]

lemma subProd_initTab {n : ℕ} (x : Qubits n) (s : Finset (Fin n)) :
    subProd (initTab n x) s =
      Matrix.diagonal (fun y => ∏ i, if i ∈ s then dsgn x i y else 1) := by
  unfold subProd
  have h : ∀ i : Fin n, (if i ∈ s then (initTab n x i).toMatrix else 1) =
      Matrix.diagonal (fun y => if i ∈ s then dsgn x i y else 1) := by
    intro i; split_ifs
    · exact initTab_toMatrix x i
    · exact Matrix.diagonal_one.symm
  simp_rw [h]
  exact ofFn_prod_diagonal _

theorem childInit (n : ℕ) (x : Qubits n) : IsValidTableau (initTab n x) ∧
    tableauProjector (initTab n x) = pureDensity (ket x) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, initTab_proj x⟩
  · intro j
    by_cases hx : x j <;> simp [initTab, hx]
  · intro i j
    unfold PauliString.Commute
    rw [initTab_toMatrix, initTab_toMatrix, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1; funext y; ring
  · intro j s hj c h
    rw [initTab_toMatrix, subProd_initTab] at h
    obtain ⟨x', hx'j, hx'i⟩ : ∃ x' : Qubits n, x' j ≠ x j ∧ ∀ i, i ≠ j → x' i = x i :=
      ⟨Function.update x j (!x j), by simp, fun i hi => Function.update_of_ne hi _ _⟩
    have h1 := congrFun (congrFun h x) x
    have h2 := congrFun (congrFun h x') x'
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul] at h1 h2
    have d1 : dsgn x j x = 1 := by simp [dsgn]
    have d2 : dsgn x j x' = -1 := by simp [dsgn, hx'j]
    have e1 : (∏ i, if i ∈ s then dsgn x i x else 1) = 1 :=
      Finset.prod_eq_one fun i _ => by split_ifs <;> simp [dsgn]
    have e2 : (∏ i, if i ∈ s then dsgn x i x' else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      split_ifs with hi
      · have hij : i ≠ j := fun hh => hj (hh ▸ hi)
        simp [dsgn, hx'i i hij]
      · rfl
    rw [d1, e1] at h1
    rw [d2, e2] at h2
    have h3 : (1 : ℂ) = -1 := h1.trans h2.symm
    norm_num at h3
  · intro s h
    rw [subProd_initTab] at h
    have h1 := congrFun (congrFun h x) x
    have e1 : (∏ i, if i ∈ s then dsgn x i x else 1) = 1 :=
      Finset.prod_eq_one fun i _ => by split_ifs <;> simp [dsgn]
    simp only [Matrix.diagonal_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] at h1
    rw [e1] at h1
    norm_num at h1

end E261

namespace E261R
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- The CHP update on (stabilizers, destabilizers) with coin `b` (Aaronson-Gottesman 2004, Sec. III). -/
def chpUpd (n : ℕ) : CliffordOp n → Tableau n × Tableau n → Bool → (Tableau n × Tableau n) × Option Bool :=
  let px : Pauli → Bool := fun | .I => false | .X => true | .Y => true | .Z => false
  let pz : Pauli → Bool := fun | .I => false | .X => false | .Y => true | .Z => true
  let conjH : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Z) | .Y => (2, .Y) | .Z => (0, .X)
  let conjS : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Y) | .Y => (2, .X) | .Z => (0, .Z)
  let conjP : Pauli → Pauli → ZMod 4 × Pauli := fun P Q => (if P = .I ∨ Q = .I ∨ P = Q then 0 else 2, Q)
  let conjPS : (Pauli → ZMod 4 × Pauli) → Fin n → PauliString n → PauliString n := fun f q P =>
    ⟨P.phase + (f (P.ops q)).1, Function.update P.ops q (f (P.ops q)).2⟩
  let cnotTab : Pauli → Pauli → ZMod 4 × Pauli × Pauli := fun Pc Pt =>
    (if px Pc && pz Pt && (px Pt == pz Pc) then 2 else 0,
      pauliOfBits (px Pc) (xor (pz Pc) (pz Pt)), pauliOfBits (xor (px Pt) (px Pc)) (pz Pt))
  let cnotPS : Fin n → Fin n → PauliString n → PauliString n := fun c t P =>
    ⟨P.phase + (cnotTab (P.ops c) (P.ops t)).1,
      Function.update (Function.update P.ops c (cnotTab (P.ops c) (P.ops t)).2.1) t
        (cnotTab (P.ops c) (P.ops t)).2.2⟩
  let updG : CliffordOp n → Tableau n → Tableau n := fun op T =>
    match op with
    | .pauli q P => fun j => conjPS (conjP P) q (T j)
    | .h q => fun j => conjPS conjH q (T j)
    | .s q => fun j => conjPS conjS q (T j)
    | .cnot c t _ => fun j => cnotPS c t (T j)
    | .measure _ => T
  let antiPair : Pauli → Pauli → Bool := fun a b => decide (a ≠ .I ∧ b ≠ .I ∧ a ≠ b)
  let antiB : PauliString n → PauliString n → Bool := fun P Q =>
    decide (Odd (Finset.univ.filter fun q => antiPair (P.ops q) (Q.ops q) = true).card)
  let oneP : PauliString n := ⟨0, fun _ => .I⟩
  let prodSel : (Fin n → PauliString n) → Finset (Fin n) → PauliString n := fun T s =>
    (List.ofFn fun i => if i ∈ s then T i else oneP).foldr PauliString.mul oneP
  let firstAnti : Tableau n → (Fin n → Pauli) → Option (Fin n) := fun T M =>
    (List.finRange n).reverse.find? (fun j => antiB (T j) ⟨0, M⟩)
  let detSel : Tableau n → (Fin n → Pauli) → Finset (Fin n) := fun D M =>
    Finset.univ.filter fun j => antiB (D j) ⟨0, M⟩ = true
  let updM : Tableau n → (Fin n → Pauli) → Fin n → Bool → Tableau n := fun T M p b =>
    fun j => if j = p then ⟨if b then 2 else 0, M⟩
      else if antiB (T j) ⟨0, M⟩ then (T j).mul (T p) else T j
  let updDM : Tableau n → Tableau n → (Fin n → Pauli) → Fin n → Tableau n := fun T D M p =>
    fun i => if i = p then T p else if antiB (D i) ⟨0, M⟩ then (D i).mul (T p) else D i
  fun op TD b =>
    match op with
    | .measure M =>
      match firstAnti TD.1 M with
      | some p => ((updM TD.1 M p b, updDM TD.1 TD.2 M p), some b)
      | none => (TD, some (decide ((prodSel TD.1 (detSel TD.2 M)).phase = 2)))
    | _ => ((updG op TD.1, updG op TD.2), none)

/-- Run the controller of `F` for `steps(n)` rounds: random bits `r` = first `rbits(n)` bits,
measurement coins = the remaining bits, one fresh coin per measurement. -/
def simLoop {σ : Type} (F : MCCFamily) (n : ℕ) (upd : CliffordOp n → σ → Bool → σ × Option Bool)
    (s0 : σ) (bits : List Bool) : σ × List (Option Bool) × List Bool :=
  (fun st : σ × List (Option Bool) × List Bool =>
    match F.ctrl n (bits.take (F.rbits.eval n)) st.2.1 with
    | none => st
    | some o => ((upd o st.1 (st.2.2.headD false)).1, st.2.1 ++ [(upd o st.1 (st.2.2.headD false)).2],
        match o with
        | .measure _ => st.2.2.tail
        | _ => st.2.2))^[F.steps.eval n] (s0, [], bits.drop (F.rbits.eval n))

/-- The projector onto the `β` eigenspace of the Pauli string `M`. -/
noncomputable abbrev projM {n : ℕ} (M : Fin n → Pauli) (β : Bool) : Matrix (Qubits n) (Qubits n) ℂ :=
  (2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))

/-- Q laws of a state machine (`tab` reads the stabilizer tableau of a state). -/
def QLaws {n : ℕ} {σ : Type} (upd : CliffordOp n → σ → Bool → σ × Option Bool)
    (tab : σ → Tableau n) (Inv : σ → Prop) : Prop :=
  (∀ op s b, Inv s → Inv (upd op s b).1) ∧
  (∀ s, Inv s → IsValidTableau (tab s)) ∧
  (∀ (op : CliffordOp n) s b, Inv s → (∀ M, op ≠ .measure M) →
      (upd op s b).2 = none ∧
      tableauProjector (tab (upd op s b).1) = op.mat * tableauProjector (tab s) * op.mat.conjTranspose) ∧
  (∀ (M : Fin n → Pauli) s b, Inv s →
    ∃ β, (upd (.measure M) s b).2 = some β ∧
      (((projM M β * tableauProjector (tab s)).trace = 1 ∧
          ∀ b', upd (.measure M) s b' = upd (.measure M) s b) ∨
        ((projM M true * tableauProjector (tab s)).trace = 2⁻¹ ∧ β = b)) ∧
      tableauProjector (tab (upd (.measure M) s b).1) =
        (projM M β * tableauProjector (tab s)).trace⁻¹ •
          (projM M β * tableauProjector (tab s) * projM M β))

/-- ChildQ: CHP correctness at the matrix level, with an invariant (validity + symplectic destabilizers). -/
def ChildQ : Prop :=
  ∃ Inv : (n : ℕ) → Tableau n × Tableau n → Prop, ∀ n : ℕ,
    (∀ x : Qubits n,
      Inv n ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
        (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) ∧
      tableauProjector (fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n) =
        pureDensity (ket x)) ∧
    QLaws (chpUpd n) Prod.fst (Inv n)

theorem chpUpd_eq (n : ℕ) (op : CliffordOp n) (TD : Tableau n × Tableau n) (b : Bool) :
    chpUpd n op TD b = E261.updC n op TD b := by
  cases op with
  | measure M =>
    simp only [chpUpd]
    split
    · rename_i p heq
      have heq' : E261.firstAnti TD.1 M = some p := heq
      simp only [E261.updC, heq']; rfl
    · rename_i heq
      have heq' : E261.firstAnti TD.1 M = none := heq
      simp only [E261.updC, heq']; rfl
  | _ => rfl

set_option maxHeartbeats 1000000 in
theorem childQ : ChildQ := by
  obtain ⟨h0, h1, h2, h3⟩ := E261.childStepC_Q
  refine ⟨fun n s => IsValidTableau s.1 ∧ E261.SympOK s.1 s.2, fun n =>
    ⟨fun x => ⟨⟨(E261.childInit n x).1, h0 n x (E261.childInit n x).1⟩, (E261.childInit n x).2⟩,
      ?_, ?_, ?_, ?_⟩⟩
  · rintro op ⟨T, D⟩ b ⟨hT, hS⟩; rw [chpUpd_eq]; exact h1 n op T D b hT hS
  · rintro s ⟨hT, _⟩; exact hT
  · rintro op ⟨T, D⟩ b ⟨hT, hS⟩ hop; simp only [chpUpd_eq]; exact h2 n op T D b hT hS hop
  · rintro M ⟨T, D⟩ b ⟨hT, hS⟩
    obtain ⟨β, h1', h2', h3'⟩ := h3 n M T D b hT hS
    refine ⟨β, ?_, ?_, ?_⟩ <;> simp only [chpUpd_eq]
    · exact h1'
    · rcases h2' with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by simpa [projM] using h.1, h.2⟩
    · exact h3'

end E261R

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity in
theorem solution :
    let chpUpd : (n : ℕ) → CliffordOp n → Tableau n × Tableau n → Bool →
        (Tableau n × Tableau n) × Option Bool := fun n =>
      let px : Pauli → Bool := fun | .I => false | .X => true | .Y => true | .Z => false
      let pz : Pauli → Bool := fun | .I => false | .X => false | .Y => true | .Z => true
      let conjH : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Z) | .Y => (2, .Y) | .Z => (0, .X)
      let conjS : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Y) | .Y => (2, .X) | .Z => (0, .Z)
      let conjP : Pauli → Pauli → ZMod 4 × Pauli := fun P Q => (if P = .I ∨ Q = .I ∨ P = Q then 0 else 2, Q)
      let conjPS : (Pauli → ZMod 4 × Pauli) → Fin n → PauliString n → PauliString n := fun f q P =>
        ⟨P.phase + (f (P.ops q)).1, Function.update P.ops q (f (P.ops q)).2⟩
      let cnotTab : Pauli → Pauli → ZMod 4 × Pauli × Pauli := fun Pc Pt =>
        (if px Pc && pz Pt && (px Pt == pz Pc) then 2 else 0,
          pauliOfBits (px Pc) (xor (pz Pc) (pz Pt)), pauliOfBits (xor (px Pt) (px Pc)) (pz Pt))
      let cnotPS : Fin n → Fin n → PauliString n → PauliString n := fun c t P =>
        ⟨P.phase + (cnotTab (P.ops c) (P.ops t)).1,
          Function.update (Function.update P.ops c (cnotTab (P.ops c) (P.ops t)).2.1) t
            (cnotTab (P.ops c) (P.ops t)).2.2⟩
      let updG : CliffordOp n → Tableau n → Tableau n := fun op T =>
        match op with
        | .pauli q P => fun j => conjPS (conjP P) q (T j)
        | .h q => fun j => conjPS conjH q (T j)
        | .s q => fun j => conjPS conjS q (T j)
        | .cnot c t _ => fun j => cnotPS c t (T j)
        | .measure _ => T
      let antiPair : Pauli → Pauli → Bool := fun a b => decide (a ≠ .I ∧ b ≠ .I ∧ a ≠ b)
      let antiB : PauliString n → PauliString n → Bool := fun P Q =>
        decide (Odd (Finset.univ.filter fun q => antiPair (P.ops q) (Q.ops q) = true).card)
      let oneP : PauliString n := ⟨0, fun _ => .I⟩
      let prodSel : (Fin n → PauliString n) → Finset (Fin n) → PauliString n := fun T s =>
        (List.ofFn fun i => if i ∈ s then T i else oneP).foldr PauliString.mul oneP
      let firstAnti : Tableau n → (Fin n → Pauli) → Option (Fin n) := fun T M =>
        (List.finRange n).reverse.find? (fun j => antiB (T j) ⟨0, M⟩)
      let detSel : Tableau n → (Fin n → Pauli) → Finset (Fin n) := fun D M =>
        Finset.univ.filter fun j => antiB (D j) ⟨0, M⟩ = true
      let updM : Tableau n → (Fin n → Pauli) → Fin n → Bool → Tableau n := fun T M p b =>
        fun j => if j = p then ⟨if b then 2 else 0, M⟩
          else if antiB (T j) ⟨0, M⟩ then (T j).mul (T p) else T j
      let updDM : Tableau n → Tableau n → (Fin n → Pauli) → Fin n → Tableau n := fun T D M p =>
        fun i => if i = p then T p else if antiB (D i) ⟨0, M⟩ then (D i).mul (T p) else D i
      fun op TD b =>
        match op with
        | .measure M =>
          match firstAnti TD.1 M with
          | some p => ((updM TD.1 M p b, updDM TD.1 TD.2 M p), some b)
          | none => (TD, some (decide ((prodSel TD.1 (detSel TD.2 M)).phase = 2)))
        | _ => ((updG op TD.1, updG op TD.2), none)
    ∃ Inv : (n : ℕ) → Tableau n × Tableau n → Prop, ∀ n : ℕ,
      (∀ x : Qubits n,
        Inv n ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
          (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) ∧
        tableauProjector (fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n) =
          pureDensity (ket x)) ∧
      (∀ op s b, Inv n s → Inv n (chpUpd n op s b).1) ∧
      (∀ s, Inv n s → IsValidTableau s.1) ∧
      (∀ (op : CliffordOp n) s b, Inv n s → (∀ M, op ≠ .measure M) →
        (chpUpd n op s b).2 = none ∧
        tableauProjector (chpUpd n op s b).1.1 = op.mat * tableauProjector s.1 * op.mat.conjTranspose) ∧
      (∀ (M : Fin n → Pauli) s b, Inv n s →
        ∃ β, (chpUpd n (.measure M) s b).2 = some β ∧
          (((((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector s.1).trace = 1 ∧
              ∀ b', chpUpd n (.measure M) s b' = chpUpd n (.measure M) s b) ∨
            ((((2⁻¹ : ℂ) • (1 + (if true then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector s.1).trace = 2⁻¹ ∧ β = b)) ∧
          tableauProjector (chpUpd n (.measure M) s b).1.1 =
            (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector s.1).trace⁻¹ • (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector s.1 * ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ))) := by
  exact E261R.childQ
