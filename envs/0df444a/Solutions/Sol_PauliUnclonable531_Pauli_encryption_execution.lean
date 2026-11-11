-- Prove2me | solution 1 for PauliUnclonable531.Pauli.encryption_execution
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T09:56:48.262203+00:00
-- url     : https://prove2.me/submissions/eaf28b42-f88c-4f6b-b70e-db12db12ae83

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Ensemble
import Theorems.Thm_PauliUnclonable531_Pauli_resource_counts

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Kit


open PauliUnclonable531.Pauli

/-- The tensor product `⊗ᵢ fᵢ` of single-qubit matrices, on the computational basis. -/
def tens {n : ℕ} (f : Fin n → Op (Fin 2)) : Op (Bits n) := fun x y => ∏ i, f i (x i) (y i)

lemma tens_mul {n : ℕ} (f g : Fin n → Op (Fin 2)) :
    tens f * tens g = tens (fun i => f i * g i) := by
  ext x y
  simp only [tens, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

lemma tens_one {n : ℕ} : tens (fun _ : Fin n => (1 : Op (Fin 2))) = 1 := by
  ext x y
  simp only [tens, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma tens_smul {n : ℕ} (c : Fin n → ℂ) (f : Fin n → Op (Fin 2)) :
    tens (fun i => c i • f i) = (∏ i, c i) • tens f := by
  ext x y
  simp [tens, Finset.prod_mul_distrib]

lemma tens_conjTranspose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).conjTranspose = tens (fun i => (f i).conjTranspose) := by
  ext x y
  simp [tens, star_prod]

lemma tens_transpose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).transpose = tens (fun i => (f i).transpose) := by
  ext x y
  simp [tens]

lemma tens_trace {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).trace = ∏ i, (f i).trace := by
  simp only [Matrix.trace, Matrix.diag, tens]
  rw [Fintype.prod_sum]

lemma pauli_eq_tens {n : ℕ} (k : Label n) :
    pauli k = tens (fun j => QMaxCutSDP.Rounding.pauli (localLabel (k.1 j) (k.2 j))) := rfl

lemma sign_add (a b : Fin 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> simp [sign]

lemma sign_sum {ι : Type} (s : Finset ι) (f : ι → Fin 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sign_add, ih]


lemma onWire_eq_tens {n : ℕ} (j : Fin n) (M : Op (Fin 2)) :
    onWire j M = tens (fun i => if i = j then M else 1) := by
  ext x y
  simp only [onWire, tens]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp [Matrix.one_apply, *]

/-- The single-qubit computational projector `|a⟩⟨a|`. -/
def proj (a : Fin 2) : Op (Fin 2) := fun i j => if i = a ∧ j = a then 1 else 0

lemma basisDensity_eq_tens {n : ℕ} (r : Bits n) : basisDensity r = tens (fun j => proj (r j)) := by
  ext x y
  simp only [basisDensity, tens, proj]
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, true_implies, funext_iff]
  apply propext
  constructor
  · rintro ⟨h1, h2⟩ j; exact ⟨h1 j, h2 j⟩
  · intro h; exact ⟨fun j => (h j).1, fun j => (h j).2⟩

lemma basisUnitary_eq_tens {n : ℕ} (k : Key n) :
    basisUnitary k = tens (fun j => basisChange (k.val.1 j) (k.val.2 j)) := rfl

lemma conj_onWire_tens {n : ℕ} (j : Fin n) (g : Op (Fin 2)) (f : Fin n → Op (Fin 2)) :
    onWire j g * tens f * (onWire j g).conjTranspose =
      tens (fun i => if i = j then g * f i * g.conjTranspose else f i) := by
  rw [onWire_eq_tens, tens_conjTranspose, tens_mul, tens_mul]
  congr 1
  funext i
  split_ifs <;> simp

lemma foldl_conj {n : ℕ} (g : Fin n → Op (Fin 2)) (L : List (Fin n)) (hL : L.Nodup)
    (f : Fin n → Op (Fin 2)) :
    L.foldl (fun ρ j => onWire j (g j) * ρ * (onWire j (g j)).conjTranspose) (tens f) =
      tens (fun i => if i ∈ L then g i * f i * (g i).conjTranspose else f i) := by
  induction L generalizing f with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    rw [List.foldl_cons, conj_onWire_tens, ih hL.2]
    congr 1
    funext i
    by_cases hi : i = a
    · subst hi; simp [hL.1]
    · simp [hi]

/-! ## Executing the instruction phases -/

section Phases

variable {n : ℕ} (p : Option (Fin n)) (m : Fin 2) (t : Bits n)

/-- The conditional bit flip used by the preparation instruction. -/
noncomputable def flipGate (a : Fin 2) : Op (Fin 2) := if a = 0 then 1 else gateMatrix .X

lemma fold_fair (L : List (Fin n)) (s : EncState n) :
    (L.map EncInstruction.fair).foldl (encStep p m t) s =
      ⟨fun j => if j ∈ L then t j else s.bits j, s.parity, s.quantum⟩ := by
  induction L generalizing s with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.foldl_cons, ih]
    simp only [encStep]
    congr 1
    funext j
    by_cases hj : j = a
    · subst hj; simp
    · simp [hj, Function.update_of_ne hj]

lemma fold_xor (L : List (Fin n)) (s : EncState n) :
    (L.map EncInstruction.xorBit).foldl (encStep p m t) s =
      ⟨s.bits, s.parity + (L.map s.bits).sum, s.quantum⟩ := by
  induction L generalizing s with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.foldl_cons, ih]
    simp only [encStep, List.map_cons, List.sum_cons, add_assoc]

lemma fold_prepare (L : List (Fin n)) (s : EncState n) :
    (L.map EncInstruction.prepare).foldl (encStep p m t) s =
      ⟨s.bits, s.parity, L.foldl (fun ρ j => onWire j (flipGate (s.bits j)) * ρ *
        (onWire j (flipGate (s.bits j))).conjTranspose) s.quantum⟩ := by
  induction L generalizing s with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.foldl_cons, ih]
    simp only [encStep, List.foldl_cons, flipGate]
    rfl

/-- The gate block emitted for one wire. -/
def gateBlock (k : Key n) (j : Fin n) : List (EncInstruction n) :=
  if k.val.1 j = 0 then [] else
    [.gate j .H] ++ if k.val.2 j = 0 then [] else [.gate j .S]

lemma onWire_one {n : ℕ} (j : Fin n) : onWire j (1 : Op (Fin 2)) = 1 := by
  rw [onWire_eq_tens]
  simpa using tens_one

lemma onWire_mul {n : ℕ} (j : Fin n) (A B : Op (Fin 2)) :
    onWire j A * onWire j B = onWire j (A * B) := by
  rw [onWire_eq_tens, onWire_eq_tens, onWire_eq_tens, tens_mul]
  congr 1
  funext i
  split_ifs <;> simp

lemma fold_block (k : Key n) (j : Fin n) (s : EncState n) :
    (gateBlock k j).foldl (encStep p m t) s =
      ⟨s.bits, s.parity, onWire j (basisChange (k.val.1 j) (k.val.2 j)) * s.quantum *
        (onWire j (basisChange (k.val.1 j) (k.val.2 j))).conjTranspose⟩ := by
  unfold gateBlock basisChange
  by_cases hx : k.val.1 j = 0
  · simp [hx, onWire_one]
  · by_cases hz : k.val.2 j = 0
    · simp [hx, hz, encStep]
    · simp only [hx, hz, if_false, List.cons_append, List.nil_append, List.foldl_cons,
        List.foldl_nil, encStep]
      rw [← onWire_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]

lemma fold_gates (k : Key n) (L : List (Fin n)) (s : EncState n) :
    (L.flatMap (gateBlock k)).foldl (encStep p m t) s =
      ⟨s.bits, s.parity, L.foldl (fun ρ j => onWire j (basisChange (k.val.1 j) (k.val.2 j)) * ρ *
        (onWire j (basisChange (k.val.1 j) (k.val.2 j))).conjTranspose) s.quantum⟩ := by
  rw [List.foldl_flatMap]
  induction L generalizing s with
  | nil => simp
  | cons a L ih =>
    rw [List.foldl_cons, fold_block, ih, List.foldl_cons]

end Phases

lemma flip_proj (a : Fin 2) : flipGate a * proj 0 * (flipGate a).conjTranspose = proj a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [flipGate, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    simp [proj, gateMatrix, QMaxCutSDP.Rounding.pauli, Matrix.one_fin_two]

lemma list_sum_filter {n : ℕ} (q : Fin n → Bool) (f : Fin n → Fin 2) (l : List (Fin n)) :
    ((l.filter q).map f).sum = (l.map (fun j => if q j = true then f j else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : q a = true
    · simp [List.filter_cons, ha, ih]
    · simp [List.filter_cons, ha, ih]

/-! ## The bijection between tapes and constrained strings -/

section Bijection

variable {n : ℕ} (k : Key n) (m : Fin 2) (p0 : Fin n)

/-- Parity of the non-pivot active bits. -/
def restParity (r : Bits n) : Fin 2 := ∑ j, if j ≠ p0 ∧ active k.val j = true then r j else 0

/-- The string actually prepared from a tape. -/
def fixPivot (r : Bits n) : Bits n := Function.update r p0 (m + restParity k p0 r)

lemma restParity_update (r : Bits n) (a : Fin 2) :
    restParity k p0 (Function.update r p0 a) = restParity k p0 r := by
  unfold restParity
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = p0
  · simp [hj]
  · simp [hj, Function.update_of_ne hj]

lemma weightedParity_split (hpa : active k.val p0 = true) (r : Bits n) :
    weightedParity k r = r p0 + restParity k p0 r := by
  unfold weightedParity restParity
  rw [show (∑ j, if active k.val j = true then r j else 0) = ∑ j, ((if j = p0 then r j else 0) +
      (if j ≠ p0 ∧ active k.val j = true then r j else 0)) from
    Finset.sum_congr rfl fun j _ => by
      by_cases hj : j = p0
      · subst hj; simp [hpa]
      · simp [hj]]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma two_eq_zero (x : Fin 2) : x + x = 0 := by fin_cases x <;> decide

lemma weightedParity_fixPivot (hpa : active k.val p0 = true) (r : Bits n) :
    weightedParity k (fixPivot k m p0 r) = m := by
  rw [weightedParity_split k p0 hpa, fixPivot, restParity_update, Function.update_self, add_assoc,
    two_eq_zero, add_zero]

end Bijection

end PauliUnclonable531.Pauli.Kit

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Kit in
theorem solution (n : ℕ) (hn : 1 ≤ n) (k : Key n) (m : Fin 2) :
    operationalEnc k m = parityEnsemble k m := by
  obtain ⟨⟨p0, hp, hpa, -⟩, hcard, -⟩ := resource_counts n hn k
  -- Step 1: each run prepares `U |r'⟩⟨r'| U†` for `r' = fixPivot tape`.
  have hexec : ∀ tape : Tape k, executeEnc k m tape =
      basisUnitary k * basisDensity (fixPivot k m p0 tape.val) * (basisUnitary k).conjTranspose := by
    intro tape
    have htp : tape.val p0 = 0 := tape.property p0 hp
    have hprog : encProgram k =
        ((List.finRange n).filter (fun j => decide (some j ≠ some p0))).map EncInstruction.fair ++
        [.loadMessage] ++
        (((List.finRange n).filter (fun j => decide (some j ≠ some p0))).filter
          (active k.val)).map EncInstruction.xorBit ++ [.storePivot] ++
        (List.finRange n).map EncInstruction.prepare ++ (List.finRange n).flatMap (gateBlock k) := by
      simp only [encProgram, hp]
      rfl
    have hstep : encStep (pivot k) m tape.val = encStep (some p0) m tape.val :=
      congrArg (fun p => encStep p m tape.val) hp
    unfold executeEnc
    rw [hprog, hstep]
    simp only [List.foldl_append, fold_fair, List.foldl_cons, List.foldl_nil, fold_xor,
      fold_prepare, fold_gates]
    simp only [encStep]
    set b1 : Bits n := fun j => if j ∈ (List.finRange n).filter (fun j => decide (some j ≠ some p0))
      then tape.val j else (0 : Bits n) j with hb1
    have hb1t : b1 = tape.val := by
      funext j
      by_cases hj : j = p0
      · subst hj; simp [hb1, htp]
      · simp [hb1, hj]
    have hsum : List.sum ((((List.finRange n).filter (fun j => decide (some j ≠ some p0))).filter
        (active k.val)).map b1) = restParity k p0 tape.val := by
      rw [hb1t, List.filter_filter, list_sum_filter, restParity, Fin.sum_univ_def]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j = p0
      · subst hj; simp
      · by_cases ha : active k.val j = true <;> simp [hj, ha]
    rw [hsum, hb1t]
    rw [basisDensity_eq_tens, foldl_conj _ _ (List.nodup_finRange n),
      foldl_conj _ _ (List.nodup_finRange n)]
    simp only [List.mem_finRange, if_true, Pi.zero_apply, flip_proj]
    rw [basisDensity_eq_tens, basisUnitary_eq_tens, tens_conjTranspose, tens_mul, tens_mul]
    rfl
  -- Step 2: tapes are in bijection with strings of the right parity.
  let e : Tape k ≃ {r : Bits n // weightedParity k r = m} :=
    { toFun := fun tape => ⟨fixPivot k m p0 tape.val, weightedParity_fixPivot k m p0 hpa _⟩
      invFun := fun r => ⟨Function.update r.val p0 0, by
        intro j hj; rw [hp] at hj; cases hj; simp⟩
      left_inv := by
        intro tape
        apply Subtype.ext
        simp only [fixPivot, Function.update_idem]
        funext j
        by_cases hj : j = p0
        · subst hj; simp [tape.property j hp]
        · simp [Function.update_of_ne hj]
      right_inv := by
        rintro ⟨r, hr⟩
        apply Subtype.ext
        simp only [fixPivot, Function.update_idem, restParity_update]
        have h := hr
        rw [weightedParity_split k p0 hpa] at h
        have : m + restParity k p0 r = r p0 := by
          rw [← h, add_assoc, two_eq_zero, add_zero]
        rw [this, Function.update_eq_self] }
  unfold operationalEnc parityEnsemble
  rw [hcard]
  push_cast
  congr 1
  simp only [hexec]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun r => weightedParity k r = m) _ (by simp)]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)
