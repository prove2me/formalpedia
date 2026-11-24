-- Prove2me | solution 1 for QuantumLTF.Membership.theorem_3_3_single_run
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-23T23:59:40.47645+00:00
-- url     : https://prove2.me/submissions/6b9c9141-44cc-44cd-83fa-606c0c26da06

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_regBasis
import Definitions.Def_QuantumLTF_Membership_rho

section Mod_Basic

open QAlgorithms

namespace LTFB

/-! ### Phases -/

/-- `ph t = e^{2π i t}`. -/
noncomputable def ph (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * (t : ℂ) * Complex.I)

/-- A bit as a real number. -/
def bv (x : Bool) : ℝ := if x then 1 else 0

@[simp] lemma bv_true : bv true = 1 := rfl
@[simp] lemma bv_false : bv false = 0 := rfl

lemma bv_mul_self (x : Bool) : bv x * bv x = bv x := by cases x <;> simp

lemma ph_add (a b : ℝ) : ph (a + b) = ph a * ph b := by
  unfold ph; rw [← Complex.exp_add]; congr 1; push_cast; ring

@[simp] lemma ph_zero : ph 0 = 1 := by simp [ph]

lemma ph_int (m : ℤ) : ph m = 1 := by
  unfold ph
  have := Complex.exp_int_mul_two_pi_mul_I m
  rw [← this]; congr 1; push_cast; ring

lemma ph_nat (m : ℕ) : ph m = 1 := by
  have := ph_int m; simpa using this

lemma ph_add_int (a : ℝ) (m : ℤ) : ph (a + m) = ph a := by
  rw [ph_add, ph_int, mul_one]

lemma ph_eq_of_sub_int {a b : ℝ} (m : ℤ) (h : a - b = m) : ph a = ph b := by
  have : a = b + m := by linarith
  rw [this, ph_add_int]

lemma norm_ph (t : ℝ) : ‖ph t‖ = 1 := by
  unfold ph
  have : (2 * Real.pi * (t : ℂ) * Complex.I) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma star_ph (t : ℝ) : star (ph t) = ph (-t) := by
  unfold ph
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, map_ofNat]

lemma ph_neg_mul_ph (t : ℝ) : ph (-t) * ph t = 1 := by
  rw [← ph_add]; simp

lemma ph_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ph (∑ i ∈ s, f i) = ∏ i ∈ s, ph (f i) := by
  unfold ph
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

lemma norm_ph_sub_ph_le (a b : ℝ) : ‖ph a - ph b‖ ≤ 2 * Real.pi * |a - b| := by
  have h1 : ph a - ph b = ph b * (ph (a - b) - 1) := by
    rw [mul_sub, ← ph_add]; ring_nf
  rw [h1, norm_mul, norm_ph, one_mul]
  have : ph (a - b) = Complex.exp (Complex.I * ((2 * Real.pi * (a - b) : ℝ) : ℂ)) := by
    unfold ph; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  have := Real.abs_sin_le_abs (x := 2 * Real.pi * (a - b) / 2)
  rw [abs_div, abs_two] at this
  have hpi : |2 * Real.pi * (a - b)| = 2 * Real.pi * |a - b| := by
    rw [abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
  rw [hpi] at this
  linarith

lemma ph_half_bv (x y : Bool) : ph (bv x * bv y / 2) = if x && y then -1 else 1 := by
  have h : ph 2⁻¹ = -1 := by
    unfold ph
    have : (2 * Real.pi * ((2⁻¹ : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]
  cases x <;> cases y <;> simp [h]

/-! ### Gates -/

/-- Single wire embedding. -/
def oneWire {K : ℕ} (w : Fin K) : Fin 1 ↪ Fin K :=
  ⟨fun _ => w, fun a b _ => Subsingleton.elim a b⟩

@[simp] lemma oneWire_apply {K : ℕ} (w : Fin K) (i : Fin 1) : oneWire w i = w := rfl

/-- Two-wire embedding. -/
def twoWire {K : ℕ} (w1 w2 : Fin K) (h : w1 ≠ w2) : Fin 2 ↪ Fin K :=
  ⟨![w1, w2], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]⟩

/-- Hadamard on one qubit. -/
noncomputable def hmat : Matrix (Qubits 1) (Qubits 1) ℂ :=
  Matrix.of fun y z => ((Real.sqrt 2)⁻¹ : ℂ) * ph (bv (y 0) * bv (z 0) / 2)

lemma qubits1_ext {y z : Qubits 1} (h : y 0 = z 0) : y = z := by
  funext a; rw [Subsingleton.elim a 0]; exact h

lemma sum_qubits1 (f : Qubits 1 → ℂ) :
    ∑ u : Qubits 1, f u = f (fun _ => false) + f (fun _ => true) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp
  rw [add_comm]; rfl

lemma hmat_unitary : hmat ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  ext y z
  rw [Matrix.mul_apply, sum_qubits1]
  simp only [hmat, Matrix.star_apply, Matrix.of_apply, ph_half_bv, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz
    cases hy : y 0 <;> simp [hy] <;> field_simp <;> simp [h2] <;> ring_nf <;> simp [h2]
  · have : y 0 ≠ z 0 := fun h => hyz (qubits1_ext h)
    rw [if_neg hyz]
    cases hy : y 0 <;> cases hz : z 0 <;> simp_all <;> ring

/-- A diagonal phase gate on `k` qubits. -/
noncomputable def dmat (k : ℕ) (f : Qubits k → ℝ) : Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.diagonal fun y => ph (f y)

lemma dmat_unitary (k : ℕ) (f : Qubits k → ℝ) : dmat k f ∈ Matrix.unitaryGroup (Qubits k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, dmat, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1; funext y
  simp only [Pi.star_apply, star_ph, ← ph_add, add_neg_cancel, ph_zero]

noncomputable def hGate : Gate := ⟨1, hmat⟩
noncomputable def dGate (k : ℕ) (f : Qubits k → ℝ) : Gate := ⟨k, dmat k f⟩

lemma hGate_mem : hGate ∈ QuantumLTF.Membership.gates12 :=
  ⟨hmat_unitary, le_rfl, by norm_num [hGate]⟩

lemma dGate1_mem (f : Qubits 1 → ℝ) : dGate 1 f ∈ QuantumLTF.Membership.gates12 :=
  ⟨dmat_unitary 1 f, le_rfl, by norm_num [dGate]⟩

lemma dGate2_mem (f : Qubits 2 → ℝ) : dGate 2 f ∈ QuantumLTF.Membership.gates12 :=
  ⟨dmat_unitary 2 f, by norm_num [dGate], le_rfl⟩

/-! ### embedOp facts -/

lemma embedOp_diagonal {k K : ℕ} (d : Qubits k → ℂ) (w : Fin k ↪ Fin K) :
    embedOp (Matrix.diagonal d) w = Matrix.diagonal fun y => d (y ∘ w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso; apply hyz; funext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨b, rfl⟩ := ha; exact congrFun h2 b
      · exact h1 a ha
    · rfl
    · rfl

lemma embedOp_refl {K : ℕ} (M : Matrix (Qubits K) (Qubits K) ℂ) :
    embedOp M (Function.Embedding.refl (Fin K)) = M := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  rw [if_pos (fun a ha => absurd ⟨a, rfl⟩ ha)]
  rfl

end LTFB

end Mod_Basic

section Mod_PathSum

open QAlgorithms

namespace LTFB

/-! ### Oracle-circuit unitary of lists -/

section Circ

variable {S : Set Gate} {r : ℕ} {ar : Fin r → ℕ} {K : ℕ}
  (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ)

lemma unitary_nil : OracleCircuit.unitary ([] : OracleCircuit S ar K) orc = 1 := by
  simp [OracleCircuit.unitary]

lemma unitary_cons (s : OracleStep S ar K) (c : OracleCircuit S ar K) :
    OracleCircuit.unitary (s :: c) orc = OracleCircuit.unitary c orc * s.mat orc := by
  simp [OracleCircuit.unitary]

lemma unitary_append (c₁ c₂ : OracleCircuit S ar K) :
    OracleCircuit.unitary (c₁ ++ c₂) orc =
      OracleCircuit.unitary c₂ orc * OracleCircuit.unitary c₁ orc := by
  simp [OracleCircuit.unitary, List.prod_append]

lemma unitary_diag_list {α : Type*} (L : List α) (st : α → OracleStep S ar K)
    (f : α → Qubits K → ℝ)
    (hst : ∀ x ∈ L, (st x).mat orc = Matrix.diagonal fun y => ph (f x y)) :
    OracleCircuit.unitary (L.map st) orc =
      Matrix.diagonal fun y => ph ((L.map fun x => f x y).sum) := by
  induction L with
  | nil => simp [unitary_nil]
  | cons x L ih =>
    rw [List.map_cons, unitary_cons, ih (fun x hx => hst x (List.mem_cons_of_mem _ hx)),
      hst x List.mem_cons_self, Matrix.diagonal_mul_diagonal]
    congr 1; funext y
    simp only [List.map_cons, List.sum_cons, ph_add]
    ring

end Circ

/-! ### Steps -/

section Steps

variable {r : ℕ} {ar : Fin r → ℕ} {K : ℕ}

noncomputable def hStep (w : Fin K) : OracleStep QuantumLTF.Membership.gates12 ar K :=
  .gate ⟨hGate, hGate_mem, oneWire w⟩

noncomputable def d1Step (w : Fin K) (α : ℝ) : OracleStep QuantumLTF.Membership.gates12 ar K :=
  .gate ⟨dGate 1 (fun y => α * bv (y 0)), dGate1_mem _, oneWire w⟩

noncomputable def cpStep (w1 w2 : Fin K) (α : ℝ) : OracleStep QuantumLTF.Membership.gates12 ar K :=
  if h : w1 ≠ w2 then
    .gate ⟨dGate 2 (fun y => α * bv (y 0) * bv (y 1)), dGate2_mem _, twoWire w1 w2 h⟩
  else d1Step w1 0

variable (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ)

lemma hStep_mat (w : Fin K) : (hStep (ar := ar) w).mat orc = embedOp hmat (oneWire w) := rfl

lemma d1Step_mat (w : Fin K) (α : ℝ) :
    (d1Step (ar := ar) w α).mat orc = Matrix.diagonal fun y => ph (α * bv (y w)) := by
  simp only [d1Step, OracleStep.mat, dGate, dmat]
  rw [embedOp_diagonal]
  rfl

lemma cpStep_mat (w1 w2 : Fin K) (α : ℝ) (h : w1 ≠ w2 ∨ α = 0) :
    (cpStep (ar := ar) w1 w2 α).mat orc =
      Matrix.diagonal fun y => ph (α * bv (y w1) * bv (y w2)) := by
  unfold cpStep
  split_ifs with hne
  · simp only [OracleStep.mat, dGate, dmat]
    rw [embedOp_diagonal]
    rfl
  · rw [d1Step_mat]
    rcases h with h | h
    · exact absurd h hne
    · subst h; simp

end Steps

/-! ### Path-sum operators -/

/-- `PS P Φ` has entry `(1/√2)^{|P|} e^{2πiΦ(y,z)}` when `y, z` agree off `P`, and `0` otherwise. -/
noncomputable def PS {K : ℕ} (P : Finset (Fin K)) (Φ : Qubits K → Qubits K → ℝ) :
    Matrix (Qubits K) (Qubits K) ℂ :=
  Matrix.of fun y z =>
    if (∀ a, a ∉ P → y a = z a) then ((Real.sqrt 2)⁻¹ : ℂ) ^ P.card * ph (Φ y z) else 0

lemma PS_apply {K : ℕ} (P : Finset (Fin K)) (Φ : Qubits K → Qubits K → ℝ) (y z : Qubits K) :
    PS P Φ y z =
      if (∀ a, a ∉ P → y a = z a) then ((Real.sqrt 2)⁻¹ : ℂ) ^ P.card * ph (Φ y z) else 0 := rfl

lemma PS_congr {K : ℕ} {P Q : Finset (Fin K)} {Φ Ψ : Qubits K → Qubits K → ℝ} (hPQ : P = Q)
    (h : ∀ y z, (∀ a, a ∉ P → y a = z a) → ph (Φ y z) = ph (Ψ y z)) : PS P Φ = PS Q Ψ := by
  subst hPQ
  ext y z
  simp only [PS, Matrix.of_apply]
  split_ifs with hc
  · rw [h y z hc]
  · rfl

lemma PS_empty {K : ℕ} : PS (∅ : Finset (Fin K)) (fun _ _ => 0) = 1 := by
  ext y z
  simp only [PS, Matrix.of_apply, Finset.notMem_empty, not_false_eq_true, true_implies,
    Finset.card_empty, pow_zero, ph_zero, one_mul, Matrix.one_apply]
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg h, if_neg]; intro h'; exact h (funext h')

lemma diag_mul_PS {K : ℕ} (f : Qubits K → ℝ) (P : Finset (Fin K))
    (Φ : Qubits K → Qubits K → ℝ) :
    Matrix.diagonal (fun y => ph (f y)) * PS P Φ = PS P (fun y z => f y + Φ y z) := by
  ext y z
  rw [Matrix.diagonal_mul]
  simp only [PS, Matrix.of_apply]
  split_ifs
  · rw [ph_add]; ring
  · simp

lemma H_mul_PS {K : ℕ} (P : Finset (Fin K)) (Φ : Qubits K → Qubits K → ℝ) (w : Fin K)
    (hw : w ∉ P) (hΦ : ∀ y z β, Φ (Function.update y w β) z = Φ y z) :
    embedOp hmat (oneWire w) * PS P Φ =
      PS (insert w P) (fun y z => bv (y w) * bv (z w) / 2 + Φ y z) := by
  ext y z
  rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update y w (z w))]
  · simp only [embedOp, PS, Matrix.of_apply]
    have hE : ∀ a, a ∉ Set.range (oneWire w) → y a = Function.update y w (z w) a := by
      intro a ha
      have : a ≠ w := fun h => ha ⟨0, h.symm⟩
      rw [Function.update_of_ne this]
    rw [if_pos hE]
    have hcond : (∀ a, a ∉ P → Function.update y w (z w) a = z a) ↔
        (∀ a, a ∉ insert w P → y a = z a) := by
      constructor
      · intro h a ha
        have haw : a ≠ w := fun h' => ha (h' ▸ Finset.mem_insert_self _ _)
        have := h a (fun h' => ha (Finset.mem_insert_of_mem h'))
        rwa [Function.update_of_ne haw] at this
      · intro h a ha
        by_cases haw : a = w
        · subst haw; rw [Function.update_self]
        · rw [Function.update_of_ne haw]
          exact h a (by simp [haw, ha])
    by_cases hc : ∀ a, a ∉ insert w P → y a = z a
    · rw [if_pos (hcond.2 hc), if_pos hc, Finset.card_insert_of_notMem hw, hΦ]
      simp only [hmat, Matrix.of_apply, Function.comp_apply, oneWire_apply,
        Function.update_self, ph_add]
      ring
    · rw [if_neg (mt hcond.1 hc), if_neg hc, mul_zero]
  · intro y' _ hy'
    simp only [embedOp, PS, Matrix.of_apply]
    split_ifs with h1 h2
    · exfalso; apply hy'; funext a
      by_cases ha : a = w
      · subst ha; rw [Function.update_self]; exact h2 a hw
      · rw [Function.update_of_ne ha]
        exact (h1 a (fun ⟨i, hi⟩ => ha hi.symm)).symm
    · simp
    · simp
    · simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Hadamards on a list of distinct wires. -/
lemma hList_mul_PS {r : ℕ} {ar : Fin r → ℕ} {K : ℕ}
    (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ)
    (L : List (Fin K)) (hL : L.Nodup) :
    ∀ (P : Finset (Fin K)) (Φ : Qubits K → Qubits K → ℝ), (∀ w ∈ L, w ∉ P) →
      (∀ w ∈ L, ∀ y z β, Φ (Function.update y w β) z = Φ y z) →
      OracleCircuit.unitary (L.map (hStep (ar := ar))) orc * PS P Φ =
        PS (P ∪ L.toFinset) (fun y z => (L.map fun w => bv (y w) * bv (z w) / 2).sum + Φ y z) := by
  induction L with
  | nil =>
    intro P Φ _ _
    simp [unitary_nil]
  | cons w L ih =>
    intro P Φ hP hΦ
    rw [List.nodup_cons] at hL
    rw [List.map_cons, unitary_cons, Matrix.mul_assoc, hStep_mat,
      H_mul_PS P Φ w (hP w List.mem_cons_self) (hΦ w List.mem_cons_self)]
    rw [ih hL.2 (insert w P) _ ?_ ?_]
    · apply PS_congr
      · ext a; simp [or_comm, or_left_comm]
      · intro y z _
        congr 1
        simp only [List.map_cons, List.sum_cons]
        ring
    · intro v hv hvP
      rcases Finset.mem_insert.1 hvP with h | h
      · subst h; exact hL.1 hv
      · exact hP v (List.mem_cons_of_mem _ hv) h
    · intro v hv y z β
      have hvw : v ≠ w := fun h => hL.1 (h ▸ hv)
      simp only [Function.update_of_ne hvw.symm]
      rw [hΦ v (List.mem_cons_of_mem _ hv)]

end LTFB

end Mod_PathSum

section Mod_QFT

open QAlgorithms

namespace LTFB

/-- Controlled-phase angle for the pair `(t, s)` of wires of one register. -/
noncomputable def qa (b : ℕ) (t s : Fin b) : ℝ :=
  if t < s then -((2 : ℝ) ^ ((t : ℕ) + (b - 1 - (s : ℕ))) / (2 : ℝ) ^ b) else 0

/-- `Z` phase on the least significant input wire. -/
noncomputable def zph (b : ℕ) (t : Fin b) : ℝ := if (t : ℕ) + 1 = b then 1 / 2 else 0

/-- Phase of the register transform. -/
noncomputable def Qph (b : ℕ) (κ j : Qubits b) : ℝ :=
  ∑ t : Fin b, (zph b t * bv (j t) + bv (κ t) * bv (j t) / 2 +
    ∑ s : Fin b, qa b t s * bv (κ t) * bv (j s))

section Defs

variable {r : ℕ} {ar : Fin r → ℕ} {K : ℕ}

noncomputable def blk {b : ℕ} (e : Fin b → Fin K) (t : ℕ) :
    List (OracleStep QuantumLTF.Membership.gates12 ar K) :=
  if h : t < b then
    hStep (e ⟨t, h⟩) :: (List.finRange b).map (fun s => cpStep (e ⟨t, h⟩) (e s) (qa b ⟨t, h⟩ s))
  else []

noncomputable def zSteps {b : ℕ} (e : Fin b → Fin K) :
    List (OracleStep QuantumLTF.Membership.gates12 ar K) :=
  (List.finRange b).map (fun t => d1Step (e t) (zph b t))

noncomputable def qftSteps {b : ℕ} (e : Fin b → Fin K) :
    List (OracleStep QuantumLTF.Membership.gates12 ar K) :=
  zSteps e ++ (List.range b).flatMap (blk e)

end Defs

section Proofs

variable {r : ℕ} {ar : Fin r → ℕ} {K : ℕ}
  (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ)

/-- The phase contributed by block `t`. -/
noncomputable def Fblk {b : ℕ} (e : Fin b → Fin K) (t : Fin b) (y z : Qubits K) : ℝ :=
  bv (y (e t)) * bv (z (e t)) / 2 + ∑ s : Fin b, qa b t s * bv (y (e t)) * bv (z (e s))

lemma Fblk_update {b : ℕ} (e : Fin b → Fin K) (he : Function.Injective e) (t t' : Fin b)
    (htt : t ≠ t') (y z : Qubits K) (β : Bool) :
    Fblk e t (Function.update y (e t') β) z = Fblk e t y z := by
  have : e t ≠ e t' := fun h => htt (he h)
  simp only [Fblk, Function.update_of_ne this]

lemma blocks_mul_PS {b : ℕ} (e : Fin b → Fin K) (he : Function.Injective e)
    (P : Finset (Fin K)) (Φ : Qubits K → Qubits K → ℝ) (hP : ∀ t, e t ∉ P)
    (hΦ : ∀ t y z β, Φ (Function.update y (e t) β) z = Φ y z) :
    ∀ k, k ≤ b →
      OracleCircuit.unitary ((List.range k).flatMap (blk (ar := ar) e)) orc * PS P Φ =
        PS (P ∪ (Finset.univ.filter (fun t : Fin b => (t : ℕ) < k)).image e)
          (fun y z => (∑ t : Fin b, if (t : ℕ) < k then Fblk e t y z else 0) + Φ y z) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [List.range_zero, List.flatMap_nil, unitary_nil, Matrix.one_mul]
    apply PS_congr
    · ext a; simp
    · intro y z _; simp
  | succ k ih =>
    intro hk
    have hkb : k < b := by omega
    rw [List.range_succ, List.flatMap_append, unitary_append, Matrix.mul_assoc, ih (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [blk, dif_pos hkb, unitary_cons, Matrix.mul_assoc, hStep_mat]
    set kk : Fin b := ⟨k, hkb⟩ with hkk
    rw [H_mul_PS]
    · rw [unitary_diag_list orc (List.finRange b) _
        (fun s y => qa b kk s * bv (y (e kk)) * bv (y (e s)))]
      · rw [diag_mul_PS]
        apply PS_congr
        · ext a
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · rintro (h | h | ⟨t, ht, rfl⟩)
            · exact Or.inr ⟨kk, by simp [kk], h.symm⟩
            · exact Or.inl h
            · exact Or.inr ⟨t, by omega, rfl⟩
          · rintro (h | ⟨t, ht, rfl⟩)
            · exact Or.inr (Or.inl h)
            · by_cases htk : (t : ℕ) < k
              · exact Or.inr (Or.inr ⟨t, htk, rfl⟩)
              · left; congr 1; ext; simp [kk]; omega
        · intro y z hc
          congr 1
          have h1 : ((List.finRange b).map
              fun s => qa b kk s * bv (y (e kk)) * bv (y (e s))).sum =
              ∑ s : Fin b, qa b kk s * bv (y (e kk)) * bv (z (e s)) := by
            rw [← Fin.sum_univ_def]
            apply Finset.sum_congr rfl
            intro s _
            by_cases hks : kk < s
            · have : y (e s) = z (e s) := by
                apply hc
                simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image,
                  Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_exists, not_and]
                refine ⟨fun h => ?_, hP s, fun t ht h => ?_⟩
                · have := he h; rw [this] at hks; exact lt_irrefl _ hks
                · have := he h; subst this
                  have : (kk : ℕ) < t := hks
                  simp [kk] at this; omega
              rw [this]
            · simp [qa, hks]
          rw [h1]
          have h2 : (∑ t : Fin b, if (t : ℕ) < k + 1 then Fblk e t y z else 0) =
              (∑ t : Fin b, if (t : ℕ) < k then Fblk e t y z else 0) + Fblk e kk y z := by
            have : ∀ t : Fin b, (if (t : ℕ) < k + 1 then Fblk e t y z else 0) =
                (if (t : ℕ) < k then Fblk e t y z else 0) + (if kk = t then Fblk e t y z else 0) := by
              intro t
              by_cases h : (t : ℕ) < k
              · have : kk ≠ t := by intro h'; subst h'; simp [kk] at h
                simp [h, this, show (t : ℕ) < k + 1 by omega]
              · by_cases h' : (t : ℕ) = k
                · have : kk = t := by ext; simp [kk, h']
                  simp [h, this, show (t : ℕ) < k + 1 by omega]
                · have : kk ≠ t := by intro h''; subst h''; simp [kk] at h'
                  simp [h, this, show ¬ (t : ℕ) < k + 1 by omega]
            rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_add_distrib,
              Finset.sum_ite_eq]
            simp
          rw [h2]
          simp only [Fblk]
          ring
      · intro s _
        apply cpStep_mat
        by_cases hs : kk = s
        · right; simp [qa, hs]
        · left; exact fun h => hs (he h)
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, not_or, not_exists, not_and]
      refine ⟨hP kk, fun t ht h => ?_⟩
      have := he h; subst this; simp [kk] at ht
    · intro y z β
      rw [hΦ]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      split_ifs with ht
      · apply Fblk_update e he
        intro h; subst h; simp [kk] at ht
      · rfl

lemma qft_mul_PS {b : ℕ} (e : Fin b → Fin K) (he : Function.Injective e)
    (P : Finset (Fin K)) (Φ : Qubits K → Qubits K → ℝ) (hP : ∀ t, e t ∉ P)
    (hΦ : ∀ t y z β, Φ (Function.update y (e t) β) z = Φ y z) :
    OracleCircuit.unitary (qftSteps (ar := ar) e) orc * PS P Φ =
      PS (P ∪ Finset.univ.image e) (fun y z => Qph b (y ∘ e) (z ∘ e) + Φ y z) := by
  rw [qftSteps, unitary_append, Matrix.mul_assoc, zSteps,
    unitary_diag_list orc (List.finRange b) _ (fun t y => zph b t * bv (y (e t)))]
  · rw [diag_mul_PS]
    have hZ : PS P (fun y z => ((List.finRange b).map fun t => zph b t * bv (y (e t))).sum + Φ y z)
        = PS P (fun y z => (∑ t : Fin b, zph b t * bv (z (e t))) + Φ y z) := by
      apply PS_congr rfl
      intro y z hc
      congr 1
      rw [← Fin.sum_univ_def]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      rw [hc (e t) (hP t)]
    rw [hZ, blocks_mul_PS orc e he P _ hP _ b le_rfl]
    · apply PS_congr
      · ext a; simp
      · intro y z _
        congr 1
        simp only [Qph, Fblk, Function.comp_apply, Fin.is_lt, if_true, Finset.sum_add_distrib]
        ring
    · intro t y z β
      rw [hΦ]
  · intro t _
    exact d1Step_mat orc (e t) (zph b t)

end Proofs

end LTFB

end Mod_QFT

section Mod_Fejer

open QAlgorithms

namespace LTFB

/-! ### Lattice tail sums -/

lemma tail_one_side (c T : ℝ) (hT : 1 / 2 < T) (S : Finset ℤ)
    (hS : ∀ M ∈ S, T < (M : ℝ) - c) :
    ∑ M ∈ S, 1 / ((M : ℝ) - c) ^ 2 ≤ 1 / (T - 1 / 2) := by
  set L : ℤ := ⌊c + T⌋ + 1 with hLdef
  have hL : ∀ M ∈ S, L ≤ M := fun M hM => by
    have h1 := hS M hM
    have : ⌊c + T⌋ < M := by rw [Int.floor_lt]; linarith
    omega
  have hLc : T < (L : ℝ) - c := by
    have := Int.lt_floor_add_one (c + T)
    simp only [hLdef]; push_cast; linarith
  set g : ℤ → ℝ := fun M => 1 / ((M : ℝ) - c - 1 / 2) with hg
  have key : ∀ M : ℤ, L ≤ M → 1 / ((M : ℝ) - c) ^ 2 ≤ g M - g (M + 1) := by
    intro M hM
    have hM' : (L : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 / 2 < (M : ℝ) - c := by linarith
    simp only [hg]
    push_cast
    have ha : 0 < (M : ℝ) - c - 1 / 2 := by linarith
    have hb : 0 < (M : ℝ) + 1 - c - 1 / 2 := by linarith
    rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hnn : ∀ M : ℤ, L ≤ M → 0 ≤ g M - g (M + 1) :=
    fun M hM => le_trans (by positivity) (key M hM)
  set R : ℕ := (∑ M ∈ S, (M - L).toNat) + 1 with hR
  have hsub : S ⊆ (Finset.range R).image (fun i : ℕ => L + i) := by
    intro M hM
    rw [Finset.mem_image]
    refine ⟨(M - L).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      have := Finset.single_le_sum (f := fun M => (M - L).toNat) (fun _ _ => Nat.zero_le _) hM
      omega
    · have := hL M hM; omega
  have hgpos : ∀ M : ℤ, L ≤ M → 0 < g M := by
    intro M hM
    have hM' : (L : ℝ) ≤ M := by exact_mod_cast hM
    simp only [hg]
    apply div_pos one_pos; linarith
  calc ∑ M ∈ S, 1 / ((M : ℝ) - c) ^ 2 ≤ ∑ M ∈ S, (g M - g (M + 1)) :=
        Finset.sum_le_sum (fun M hM => key M (hL M hM))
    _ ≤ ∑ M ∈ (Finset.range R).image (fun i : ℕ => L + i), (g M - g (M + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun M hM _ => hnn M (by
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hM; omega))
    _ = ∑ i ∈ Finset.range R, (g (L + (i : ℕ)) - g (L + ((i + 1 : ℕ) : ℤ))) := by
        rw [Finset.sum_image (by intro i _ j _ h; simpa using h)]
        apply Finset.sum_congr rfl; intro i _; push_cast; ring_nf
    _ = g (L + ((0 : ℕ) : ℤ)) - g (L + (R : ℤ)) :=
        Finset.sum_range_sub' (fun i : ℕ => g (L + (i : ℤ))) R
    _ ≤ g L := by
        have := hgpos (L + R) (by omega)
        simp only [Nat.cast_zero, add_zero]; linarith
    _ ≤ 1 / (T - 1 / 2) := by
        simp only [hg]
        apply one_div_le_one_div_of_le (by linarith) (by linarith)

lemma tail_two_side (c T : ℝ) (hT : 1 / 2 < T) (S : Finset ℤ)
    (hS : ∀ M ∈ S, T < |c - M|) :
    ∑ M ∈ S, 1 / (c - (M : ℝ)) ^ 2 ≤ 2 / (T - 1 / 2) := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun M : ℤ => c < M)]
  have h1 : ∑ M ∈ S.filter (fun M : ℤ => c < (M : ℝ)), 1 / (c - (M : ℝ)) ^ 2 ≤ 1 / (T - 1 / 2) := by
    have := tail_one_side c T hT (S.filter fun M : ℤ => c < (M : ℝ)) (by
      intro M hM
      rw [Finset.mem_filter] at hM
      have := hS M hM.1
      rw [abs_of_neg (by linarith [hM.2])] at this
      linarith)
    calc _ = ∑ M ∈ S.filter (fun M : ℤ => c < (M : ℝ)), 1 / ((M : ℝ) - c) ^ 2 := by
          apply Finset.sum_congr rfl; intro M _; ring
      _ ≤ _ := this
  have h2 : ∑ M ∈ S.filter (fun M : ℤ => ¬ c < (M : ℝ)), 1 / (c - (M : ℝ)) ^ 2 ≤ 1 / (T - 1 / 2) := by
    have := tail_one_side (-c) T hT ((S.filter fun M : ℤ => ¬ c < (M : ℝ)).image Neg.neg) (by
      intro M hM
      obtain ⟨M', hM', rfl⟩ := Finset.mem_image.1 hM
      rw [Finset.mem_filter] at hM'
      have := hS M' hM'.1
      rw [abs_of_nonneg (by linarith [not_lt.1 hM'.2])] at this
      push_cast; linarith)
    rw [Finset.sum_image (by intro i _ j _ h; simpa using h)] at this
    calc _ = ∑ M ∈ S.filter (fun M : ℤ => ¬ c < (M : ℝ)), 1 / (((-M : ℤ) : ℝ) - -c) ^ 2 := by
          apply Finset.sum_congr rfl; intro M _; push_cast; ring
      _ ≤ _ := this
  have : 2 / (T - 1 / 2) = 1 / (T - 1 / 2) + 1 / (T - 1 / 2) := by ring
  linarith

/-! ### Geometric sums of phases -/

lemma ph_nat_mul (j : ℕ) (θ : ℝ) : ph (j * θ) = ph θ ^ j := by
  unfold ph
  rw [← Complex.exp_nat_mul]
  congr 1; push_cast; ring

lemma norm_ph_sub_one (θ : ℝ) : ‖ph θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
  have : ph θ = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
    unfold ph; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  congr 2; ring

lemma norm_geom_ph_le (N : ℕ) (θ : ℝ) (hs : Real.sin (Real.pi * θ) ≠ 0) :
    ‖∑ j ∈ Finset.range N, ph (j * θ)‖ ≤ 1 / |Real.sin (Real.pi * θ)| := by
  have hne : ph θ ≠ 1 := by
    intro h
    have := norm_ph_sub_one θ
    rw [h, sub_self, norm_zero] at this
    have : |Real.sin (Real.pi * θ)| = 0 := by linarith
    exact hs (abs_eq_zero.1 this)
  simp only [ph_nat_mul]
  rw [geom_sum_eq hne, norm_div, norm_ph_sub_one]
  have hpos : 0 < |Real.sin (Real.pi * θ)| := abs_pos.2 hs
  rw [div_le_div_iff₀ (by positivity) hpos]
  have : ‖ph θ ^ N - 1‖ ≤ 2 := by
    calc ‖ph θ ^ N - 1‖ ≤ ‖ph θ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_ph, one_pow, norm_one]; norm_num
  nlinarith

lemma abs_sin_pi_ge (x : ℝ) (hx : |x| ≤ 1 / 2) : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
  have hpi := Real.pi_pos
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx ⊢
    have h1 := Real.mul_le_sin (x := Real.pi * x) (by positivity) (by nlinarith)
    have h2 : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [h2] at h1
    rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg h] at hx ⊢
    have h1 := Real.mul_le_sin (x := Real.pi * (-x)) (by nlinarith) (by nlinarith)
    have h2 : 2 / Real.pi * (Real.pi * -x) = 2 * -x := by field_simp
    rw [h2] at h1
    simp only [mul_neg, Real.sin_neg] at h1
    rw [abs_of_nonpos (by linarith)]; linarith

lemma abs_sin_pi_sub_int (x : ℝ) (m : ℤ) :
    |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * (x - m))| := by
  have : Real.pi * x = Real.pi * (x - m) + m * Real.pi := by ring
  rw [this, Real.sin_add_int_mul_pi, abs_mul]
  have : |((-1 : ℝ) ^ m)| = 1 := by
    rcases Int.even_or_odd m with h | h
    · rw [h.neg_one_zpow]; simp
    · rw [h.neg_one_zpow]; simp
  rw [this, one_mul]

/-- The Fejér-type bound on one Fourier amplitude. -/
lemma amp_sq_le (N : ℕ) (hN : 0 < N) (θ : ℝ) (m : ℤ) (h1 : |θ - m| ≤ 1 / 2)
    (h2 : θ - m ≠ 0) :
    ‖(1 / (N : ℂ)) * ∑ j ∈ Finset.range N, ph (j * θ)‖ ^ 2 ≤
      1 / (4 * ((N : ℝ) * (θ - m)) ^ 2) := by
  have hs := abs_sin_pi_ge (θ - m) h1
  rw [← abs_sin_pi_sub_int] at hs
  have hpos : 0 < |θ - m| := abs_pos.2 h2
  have hsin : Real.sin (Real.pi * θ) ≠ 0 := by
    intro h; rw [h, abs_zero] at hs; linarith
  have hg := norm_geom_ph_le N θ hsin
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hb : ‖∑ j ∈ Finset.range N, ph (j * θ)‖ ≤ 1 / (2 * |θ - m|) := by
    calc _ ≤ 1 / |Real.sin (Real.pi * θ)| := hg
      _ ≤ 1 / (2 * |θ - m|) := one_div_le_one_div_of_le (by positivity) hs
  have hnn := norm_nonneg (∑ j ∈ Finset.range N, ph (j * θ))
  calc (1 / (N : ℝ) * ‖∑ j ∈ Finset.range N, ph (j * θ)‖) ^ 2
      ≤ (1 / (N : ℝ) * (1 / (2 * |θ - m|))) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 / (4 * ((N : ℝ) * (θ - m)) ^ 2) := by
        rw [mul_pow (N : ℝ), ← sq_abs (θ - m)]
        field_simp
        ring

/-- Total weight of the outcomes far from the peak. -/
lemma fail_bound (N : ℕ) (hN : 0 < N) (γ T : ℝ) (hγ : |γ| ≤ 1 / 5) (hT : 1 / 2 < T)
    (hTN : T ≤ N / 5) :
    ∑ K ∈ (Finset.range N).filter (fun K : ℕ => ¬ |(K : ℝ) - N * (γ + 1 / 2)| ≤ T),
      ‖(1 / (N : ℂ)) * ∑ j ∈ Finset.range N, ph (j * (γ - K / N - 1 / 2))‖ ^ 2 ≤
        1 / (2 * T - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := N * (γ + 1 / 2) with hc
  have hc1 : 3 / 10 * N ≤ c := by
    rw [hc]; have := (abs_le.1 hγ).1; nlinarith
  have hc2 : c ≤ 7 / 10 * N := by
    rw [hc]; have := (abs_le.1 hγ).2; nlinarith
  -- integer shift
  let rr : ℕ → ℤ := fun K => round ((c - K) / N)
  let MM : ℕ → ℤ := fun K => K + N * rr K
  have hθ : ∀ K : ℕ, (γ - K / N - 1 / 2) - ((rr K - 1 : ℤ) : ℝ) =
      ((c - K) / N - rr K) := by
    intro K; rw [hc]; push_cast; field_simp; ring
  have hd : ∀ K : ℕ, (N : ℝ) * ((c - K) / N - rr K) = c - MM K := by
    intro K; simp only [MM]; push_cast; field_simp; ring
  have hfar : ∀ K ∈ (Finset.range N).filter (fun K : ℕ => ¬ |(K : ℝ) - c| ≤ T),
      T < |c - MM K| := by
    intro K hK
    rw [Finset.mem_filter, Finset.mem_range] at hK
    have hK1 : T < |c - K| := by rw [abs_sub_comm]; exact lt_of_not_ge hK.2
    have hKN : (K : ℝ) + 1 ≤ N := by exact_mod_cast hK.1
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    by_cases hr : rr K = 0
    · simp only [MM, hr, mul_zero, add_zero]; exact hK1
    · have habs : |c - K| ≤ 7 / 10 * N := by
        rw [abs_le]; constructor <;> linarith
      have hrabs : (1 : ℝ) ≤ |(rr K : ℝ)| := by
        have : (1 : ℤ) ≤ |rr K| := Int.one_le_abs hr
        exact_mod_cast this
      have : c - MM K = (c - K) - N * rr K := by simp only [MM]; push_cast; ring
      rw [this]
      have h3 : (N : ℝ) * |(rr K : ℝ)| ≤ |c - MM K| + |c - K| := by
        rw [this]
        calc (N : ℝ) * |(rr K : ℝ)| = |(c - K) - ((c - K) - N * rr K)| := by
              rw [show (c - K) - ((c - K) - N * rr K) = (N : ℝ) * rr K by ring, abs_mul,
                abs_of_pos hNpos]
          _ ≤ |c - K| + |(c - K) - N * rr K| := abs_sub _ _
          _ = _ := by ring
      rw [← this]
      nlinarith
  have hinj : Set.InjOn MM ↑((Finset.range N).filter (fun K : ℕ => ¬ |(K : ℝ) - c| ≤ T)) := by
    intro K hK K' hK' h
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hK hK'
    have e1 : (MM K) % (N : ℤ) = K := by
      simp only [MM]; rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)
    have e2 : (MM K') % (N : ℤ) = K' := by
      simp only [MM]; rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)
    have : (K : ℤ) = K' := by rw [← e1, ← e2, h]
    exact_mod_cast this
  calc _ ≤ ∑ K ∈ (Finset.range N).filter (fun K : ℕ => ¬ |(K : ℝ) - c| ≤ T),
        (1 / 4) * (1 / (c - (MM K : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro K hK
        have hf := hfar K hK
        have hne : (γ - K / N - 1 / 2) - ((rr K - 1 : ℤ) : ℝ) ≠ 0 := by
          rw [hθ]; intro h0
          have := hd K; rw [h0, mul_zero] at this
          rw [← this, abs_zero] at hf; linarith
        have h1 : |(γ - K / N - 1 / 2) - ((rr K - 1 : ℤ) : ℝ)| ≤ 1 / 2 := by
          rw [hθ]; exact abs_sub_round _
        have := amp_sq_le N hN (γ - K / N - 1 / 2) (rr K - 1) h1 hne
        rw [hθ, hd] at this
        calc _ ≤ _ := this
          _ = _ := by field_simp
    _ = (1 / 4) * ∑ M ∈ ((Finset.range N).filter (fun K : ℕ => ¬ |(K : ℝ) - c| ≤ T)).image MM,
          1 / (c - (M : ℝ)) ^ 2 := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ (1 / 4) * (2 / (T - 1 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply tail_two_side c T hT
        intro M hM
        obtain ⟨K, hK, rfl⟩ := Finset.mem_image.1 hM
        exact hfar K hK
    _ = 1 / (2 * T - 1) := by
        have : T - 1 / 2 ≠ 0 := by linarith
        have : 2 * T - 1 ≠ 0 := by linarith
        field_simp; ring

/-- `∏ (1 - F_i) ≥ 1 - ∑ F_i`. -/
lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (F : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ F i)
    (h1 : ∀ i ∈ s, F i ≤ 1) : 1 - ∑ i ∈ s, F i ≤ ∏ i ∈ s, (1 - F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hp0 : 0 ≤ ∏ i ∈ s, (1 - F i) :=
      Finset.prod_nonneg (fun i hi => by linarith [h1 i (Finset.mem_insert_of_mem hi)])
    have hp1 : ∏ i ∈ s, (1 - F i) ≤ 1 :=
      Finset.prod_le_one (fun i hi => by linarith [h1 i (Finset.mem_insert_of_mem hi)])
        (fun i hi => by linarith [h0 i (Finset.mem_insert_of_mem hi)])
    have ha0 := h0 a (Finset.mem_insert_self a s)
    have ha1 := h1 a (Finset.mem_insert_self a s)
    nlinarith

end LTFB

end Mod_Fejer

section Mod_Phase

open QAlgorithms

namespace LTFB

def IsInt (x : ℝ) : Prop := ∃ m : ℤ, x = m

lemma IsInt.add {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by push_cast; ring⟩

lemma IsInt.mul {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, by push_cast; ring⟩

lemma isInt_nat (k : ℕ) : IsInt (k : ℝ) := ⟨k, by push_cast; ring⟩

lemma isInt_bv (x : Bool) : IsInt (bv x) := by
  cases x
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

lemma isInt_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, IsInt (f i)) :
    IsInt (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma bitsToNat_real {b : ℕ} (j : Qubits b) :
    (bitsToNat j : ℝ) = ∑ s : Fin b, bv (j s) * (2 : ℝ) ^ (b - 1 - (s : ℕ)) := by
  unfold bitsToNat
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  cases j s <;> simp

lemma bitsToNat_rev_real {b : ℕ} (κ : Qubits b) :
    (bitsToNat (κ ∘ Fin.rev) : ℝ) = ∑ t : Fin b, bv (κ t) * (2 : ℝ) ^ (t : ℕ) := by
  rw [bitsToNat_real]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun u => ?_)
  simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
  congr 2
  have := u.isLt
  omega

lemma Qph_ph (b : ℕ) (κ j : Qubits b) :
    ph (Qph b κ j) = ph (-((bitsToNat j : ℝ) * (bitsToNat (κ ∘ Fin.rev) : ℝ) / (2 : ℝ) ^ b +
      (bitsToNat j : ℝ) / 2)) := by
  -- coefficient functions
  set cc : Fin b → Fin b → ℝ := fun t s =>
    (if t = s then 1 / 2 else 0) + qa b t s + (2 : ℝ) ^ (t : ℕ) * (2 : ℝ) ^ (b - 1 - (s : ℕ)) /
      (2 : ℝ) ^ b with hcc
  set dd : Fin b → ℝ := fun t => zph b t + (2 : ℝ) ^ (b - 1 - (t : ℕ)) / 2 with hdd
  have hpow : ∀ k : ℕ, (2 : ℝ) ^ k ≠ 0 := fun k => pow_ne_zero _ (by norm_num)
  have hccI : ∀ t s, IsInt (cc t s) := by
    intro t s
    simp only [hcc]
    have ht := t.isLt; have hs := s.isLt
    rcases lt_trichotomy t s with h | h | h
    · have h' : ¬ t = s := ne_of_lt h
      refine ⟨0, ?_⟩
      simp only [h', if_false, qa, h, if_true, Int.cast_zero]
      rw [← pow_add]; ring
    · subst h
      refine ⟨1, ?_⟩
      simp only [if_true, qa, lt_irrefl, if_false, Int.cast_one]
      rw [← pow_add]
      have : (2 : ℝ) ^ b = 2 ^ ((t : ℕ) + (b - 1 - t)) * 2 := by
        rw [← pow_succ]; congr 1; omega
      rw [this]; field_simp; ring
    · have h' : ¬ t = s := ne_of_gt h
      have h'' : ¬ t < s := not_lt.2 (le_of_lt h)
      have hts : (s : ℕ) < t := h
      refine ⟨2 ^ ((t : ℕ) + (b - 1 - s) - b), ?_⟩
      simp only [h', if_false, qa, h'', zero_add]
      push_cast
      rw [← pow_add, div_eq_iff (hpow b), ← pow_add]
      congr 1; omega
  have hddI : ∀ t, IsInt (dd t) := by
    intro t
    simp only [hdd, zph]
    have ht := t.isLt
    by_cases h : (t : ℕ) + 1 = b
    · refine ⟨1, ?_⟩
      rw [if_pos h, show b - 1 - (t : ℕ) = 0 by omega]; norm_num
    · refine ⟨2 ^ (b - 2 - (t : ℕ)), ?_⟩
      rw [if_neg h]; push_cast
      rw [show b - 1 - (t : ℕ) = (b - 2 - t) + 1 by omega, pow_succ]; ring
  have hJK : (bitsToNat j : ℝ) * (bitsToNat (κ ∘ Fin.rev) : ℝ) =
      ∑ t : Fin b, ∑ s : Fin b, bv (κ t) * bv (j s) *
        ((2 : ℝ) ^ (t : ℕ) * (2 : ℝ) ^ (b - 1 - (s : ℕ))) := by
    rw [bitsToNat_real, bitsToNat_rev_real, Finset.sum_mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro s _
    ring
  have h1 : ∑ t : Fin b, bv (j t) * dd t =
      ∑ t : Fin b, zph b t * bv (j t) + (bitsToNat j : ℝ) / 2 := by
    rw [bitsToNat_real, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro t _
    simp only [hdd]; ring
  have h2 : ∑ t : Fin b, ∑ s : Fin b, bv (κ t) * bv (j s) * cc t s =
      ∑ t : Fin b, bv (κ t) * bv (j t) / 2 +
        ∑ t : Fin b, ∑ s : Fin b, qa b t s * bv (κ t) * bv (j s) +
        (bitsToNat j : ℝ) * (bitsToNat (κ ∘ Fin.rev) : ℝ) / (2 : ℝ) ^ b := by
    rw [hJK, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro t _
    have : bv (κ t) * bv (j t) / 2 =
        ∑ s : Fin b, if t = s then bv (κ t) * bv (j s) / 2 else 0 := by
      rw [Finset.sum_ite_eq]; simp
    rw [this, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s _
    simp only [hcc]
    split_ifs <;> ring
  have h3 : Qph b κ j = ∑ t : Fin b, zph b t * bv (j t) + ∑ t : Fin b, bv (κ t) * bv (j t) / 2 +
      ∑ t : Fin b, ∑ s : Fin b, qa b t s * bv (κ t) * bv (j s) := by
    simp only [Qph, Finset.sum_add_distrib]
  have hI : IsInt (Qph b κ j - -((bitsToNat j : ℝ) * (bitsToNat (κ ∘ Fin.rev) : ℝ) / (2 : ℝ) ^ b +
      (bitsToNat j : ℝ) / 2)) := by
    have : Qph b κ j - -((bitsToNat j : ℝ) * (bitsToNat (κ ∘ Fin.rev) : ℝ) / (2 : ℝ) ^ b +
      (bitsToNat j : ℝ) / 2) =
      ∑ t : Fin b, bv (j t) * dd t + ∑ t : Fin b, ∑ s : Fin b, bv (κ t) * bv (j s) * cc t s := by
      rw [h1, h2, h3]; ring
    rw [this]
    exact (isInt_sum _ _ (fun t _ => (isInt_bv _).mul (hddI t))).add
      (isInt_sum _ _ (fun t _ => isInt_sum _ _ (fun s _ =>
        ((isInt_bv _).mul (isInt_bv _)).mul (hccI t s))))
  obtain ⟨m, hm⟩ := hI
  exact ph_eq_of_sub_int m hm

end LTFB

end Mod_Phase

section Mod_Unit

open QAlgorithms

namespace LTFB

/-! ### embedOp is multiplicative, star-compatible, hence preserves unitarity -/

lemma embedOp_mul {k K : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin K) :
    embedOp A w * embedOp B w = embedOp (A * B) w := by
  classical
  ext y z
  rw [Matrix.mul_apply]
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    -- restrict to the strings agreeing with y off the range
    have hsplit : ∀ y' : Qubits K,
        ((if ∀ a, a ∉ Set.range w → y a = y' a then A (y ∘ w) (y' ∘ w) else 0) *
          (if ∀ a, a ∉ Set.range w → y' a = z a then B (y' ∘ w) (z ∘ w) else 0)) =
        if (∀ a, a ∉ Set.range w → y a = y' a) then A (y ∘ w) (y' ∘ w) * B (y' ∘ w) (z ∘ w)
          else 0 := by
      intro y'
      by_cases h1 : ∀ a, a ∉ Set.range w → y a = y' a
      · have h2 : ∀ a, a ∉ Set.range w → y' a = z a := fun a ha => (h1 a ha).symm.trans (hyz a ha)
        rw [if_pos h1, if_pos h2, if_pos h1]
      · rw [if_neg h1, if_neg h1, zero_mul]
    simp only [hsplit]
    rw [← Finset.sum_filter]
    apply Finset.sum_nbij' (fun y' => y' ∘ w) (fun u => Function.extend w u y)
    · intro _ _; exact Finset.mem_univ _
    · intro u _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun a ha => ?_⟩
      rw [Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => ha ⟨i, hi⟩)]
    · intro y' hy'
      have hy'' : ∀ a, a ∉ Set.range w → y a = y' a := by simpa using hy'
      funext a
      by_cases ha : ∃ i, w i = a
      · obtain ⟨i, rfl⟩ := ha
        rw [w.injective.extend_apply]; rfl
      · rw [Function.extend_apply' _ _ _ ha]
        exact hy'' a (fun ⟨i, hi⟩ => ha ⟨i, hi⟩)
    · intro u _
      funext i
      simp only [Function.comp_apply]
      rw [w.injective.extend_apply]
    · intro _ _; rfl
  · rw [if_neg hyz]
    apply Finset.sum_eq_zero
    intro y' _
    split_ifs with h1 h2
    · exfalso; exact hyz (fun a ha => (h1 a ha).trans (h2 a ha))
    · simp
    · simp
    · simp

lemma embedOp_star {k K : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin K) :
    star (embedOp M w) = embedOp (star M) w := by
  ext y z
  simp only [embedOp, Matrix.star_apply, Matrix.of_apply]
  have : (∀ a, a ∉ Set.range w → z a = y a) ↔ (∀ a, a ∉ Set.range w → y a = z a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a, a ∉ Set.range w → y a = z a
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (mt this.1 h), if_neg h, star_zero]

lemma embedOp_unitary {k K : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin K)
    (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits K) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  rw [embedOp_star, embedOp_mul, hM, embedOp_one]

section Circ

variable {r : ℕ} {ar : Fin r → ℕ} {K : ℕ}
  (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ)

lemma unitary_mem_of_steps (c : OracleCircuit QuantumLTF.Membership.gates12 ar K)
    (hc : ∀ s ∈ c, s.mat orc ∈ Matrix.unitaryGroup (Qubits K) ℂ) :
    OracleCircuit.unitary c orc ∈ Matrix.unitaryGroup (Qubits K) ℂ := by
  induction c with
  | nil => rw [unitary_nil]; exact one_mem _
  | cons s c ih =>
    rw [unitary_cons]
    exact mul_mem (ih (fun s' hs' => hc s' (List.mem_cons_of_mem _ hs'))) (hc s List.mem_cons_self)

lemma gate_mat_unitary (g : GateApp QuantumLTF.Membership.gates12 K) :
    (OracleStep.gate (a := ar) g).mat orc ∈ Matrix.unitaryGroup (Qubits K) ℂ :=
  embedOp_unitary _ _ g.mem.1

/-- A step is an elementary gate. -/
def IsGateStep (s : OracleStep QuantumLTF.Membership.gates12 ar K) : Prop :=
  ∃ g, s = OracleStep.gate g

lemma mat_unitary_of_isGate (s : OracleStep QuantumLTF.Membership.gates12 ar K)
    (hs : IsGateStep s) : s.mat orc ∈ Matrix.unitaryGroup (Qubits K) ℂ := by
  obtain ⟨g, rfl⟩ := hs
  exact gate_mat_unitary orc g

lemma hStep_isGate (w : Fin K) : IsGateStep (hStep (ar := ar) w) := ⟨_, rfl⟩
lemma d1Step_isGate (w : Fin K) (α : ℝ) : IsGateStep (d1Step (ar := ar) w α) := ⟨_, rfl⟩
lemma cpStep_isGate (w1 w2 : Fin K) (α : ℝ) : IsGateStep (cpStep (ar := ar) w1 w2 α) := by
  unfold cpStep; split_ifs
  · exact ⟨_, rfl⟩
  · exact d1Step_isGate _ _

end Circ

end LTFB

end Mod_Unit

section Mod_Circuit

open QAlgorithms QuantumLTF.Membership

namespace LTFB

/-! ### Register layout -/

section Layout

variable (n b Vb W : ℕ)

def xw (a : Fin (n * b)) : Fin (n * b + Vb + W) := Fin.castAdd W (Fin.castAdd Vb a)

def Ew (i : Fin n) (t : Fin b) : Fin (n * b + Vb + W) := xw n b Vb W (finProdFinEquiv (i, t))

def vw (j : Fin Vb) : Fin (n * b + Vb + W) := Fin.castAdd W (Fin.natAdd (n * b) j)

def Xset : Finset (Fin (n * b + Vb + W)) := Finset.univ.image (xw n b Vb W)

variable {n b Vb W}

lemma xw_val (a : Fin (n * b)) : (xw n b Vb W a : ℕ) = a := rfl

lemma xw_injective : Function.Injective (xw n b Vb W) := by
  intro a a' h; ext; have := congrArg Fin.val h; simpa [xw_val] using this

lemma mem_Xset (a : Fin (n * b + Vb + W)) : a ∈ Xset n b Vb W ↔ (a : ℕ) < n * b := by
  simp only [Xset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a', rfl⟩; rw [xw_val]; exact a'.isLt
  · intro h; exact ⟨⟨a, h⟩, Fin.ext rfl⟩

lemma Ew_val (i : Fin n) (t : Fin b) : (Ew n b Vb W i t : ℕ) = t + b * i := by
  simp [Ew, xw_val, finProdFinEquiv]

lemma Ew_injective2 {i i' : Fin n} {t t' : Fin b} (h : Ew n b Vb W i t = Ew n b Vb W i' t') :
    i = i' ∧ t = t' := by
  have h1 : finProdFinEquiv (i, t) = finProdFinEquiv (i', t') := xw_injective h
  have := finProdFinEquiv.injective h1
  simp only [Prod.mk.injEq] at this
  exact this

lemma Ew_injective (i : Fin n) : Function.Injective (Ew n b Vb W i) :=
  fun _ _ h => (Ew_injective2 h).2

lemma Ew_mem_Xset (i : Fin n) (t : Fin b) : Ew n b Vb W i t ∈ Xset n b Vb W := by
  simp [Xset, Ew]

lemma Xset_eq_image : Xset n b Vb W =
    (Finset.univ : Finset (Fin n × Fin b)).image (fun p => Ew n b Vb W p.1 p.2) := by
  ext a
  simp only [Xset, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨a', rfl⟩
    exact ⟨(finProdFinEquiv.symm a').1, (finProdFinEquiv.symm a').2, by
      rw [Ew, Prod.mk.eta, Equiv.apply_symm_apply]⟩
  · rintro ⟨i, t, rfl⟩; exact ⟨_, rfl⟩

lemma card_Xset : (Xset n b Vb W).card = n * b := by
  rw [Xset, Finset.card_image_of_injective _ xw_injective]; simp

lemma vw_notMem_Xset (j : Fin Vb) : vw n b Vb W j ∉ Xset n b Vb W := by
  rw [mem_Xset]; simp [vw]

lemma regBasis_xw (x : Fin n → Qubits b) (v : Qubits Vb) (a : Fin (n * b)) :
    regBasis n b Vb W x v (xw n b Vb W a) = flatReg n b x a := by
  simp [regBasis, xw, Fin.append_left]

lemma regBasis_Ew (x : Fin n → Qubits b) (v : Qubits Vb) (i : Fin n) (t : Fin b) :
    regBasis n b Vb W x v (Ew n b Vb W i t) = x i t := by
  rw [Ew, regBasis_xw]; simp [flatReg]

lemma regBasis_comp_Ew (x : Fin n → Qubits b) (v : Qubits Vb) (i : Fin n) :
    regBasis n b Vb W x v ∘ Ew n b Vb W i = x i := by
  funext t; exact regBasis_Ew x v i t

lemma regBasis_vw (x : Fin n → Qubits b) (v : Qubits Vb) (j : Fin Vb) :
    regBasis n b Vb W x v (vw n b Vb W j) = v j := by
  simp [regBasis, vw, Fin.append_left, Fin.append_right]

lemma regBasis_zero_off (x : Fin n → Qubits b) (a : Fin (n * b + Vb + W))
    (ha : a ∉ Xset n b Vb W) : regBasis n b Vb W x (fun _ => false) a = false := by
  rw [mem_Xset] at ha
  by_cases h2 : (a : ℕ) < n * b + Vb
  · have : a = Fin.castAdd W (Fin.natAdd (n * b) (⟨a - n * b, by omega⟩ : Fin Vb)) := by
      ext; simp; omega
    rw [this, regBasis, Fin.append_left, Fin.append_right]
  · have : a = Fin.natAdd (n * b + Vb) (⟨a - (n * b + Vb), by omega⟩ : Fin W) := by
      ext; simp; omega
    rw [this, regBasis, Fin.append_right]

/-- Decoding the `x` register. -/
def dec (y : Qubits (n * b + Vb + W)) : Fin n → Qubits b := fun i t => y (Ew n b Vb W i t)

lemma regBasis_dec (y : Qubits (n * b + Vb + W)) (hy : ∀ a, a ∉ Xset n b Vb W → y a = false) :
    regBasis n b Vb W (dec y) (fun _ => false) = y := by
  funext a
  by_cases ha : a ∈ Xset n b Vb W
  · obtain ⟨a', _, rfl⟩ := Finset.mem_image.1 ha
    rw [regBasis_xw]
    simp only [flatReg, dec, Ew, Prod.mk.eta, Equiv.apply_symm_apply]
  · rw [regBasis_zero_off _ _ ha, hy a ha]

lemma dec_regBasis (x : Fin n → Qubits b) (v : Qubits Vb) : dec (regBasis n b Vb W x v) = x := by
  funext i t; simp [dec, regBasis_Ew]

lemma regBasis_injective (v : Qubits Vb) : Function.Injective fun x => regBasis n b Vb W x v := by
  intro x x' h
  have := congrArg dec h
  simpa [dec_regBasis] using this

end Layout

/-! ### The circuit -/

section Circuit

variable (n b Vb W : ℕ)

abbrev AR : Fin 1 → ℕ := fun _ => n * b + Vb + W

abbrev OC := OracleCircuit gates12 (AR n b Vb W) (n * b + Vb + W)

noncomputable def preSteps : OC n b Vb W :=
  (List.finRange (n * b)).map (fun a => hStep (xw n b Vb W a))

noncomputable def phSteps (cv : Fin Vb → ℝ) : OC n b Vb W :=
  (List.finRange Vb).map (fun j => d1Step (vw n b Vb W j) (cv j))

noncomputable def postSteps : OC n b Vb W :=
  (List.range n).flatMap (fun i => if h : i < n then qftSteps (Ew n b Vb W ⟨i, h⟩) else [])

def qStep (adj : Bool) : OracleStep gates12 (AR n b Vb W) (n * b + Vb + W) :=
  .query 0 adj none (Function.Embedding.refl _) (by simp)

noncomputable def circ (cv : Fin Vb → ℝ) : OC n b Vb W :=
  preSteps n b Vb W ++ [qStep n b Vb W false] ++ phSteps n b Vb W cv ++ [qStep n b Vb W true] ++
    postSteps n b Vb W

variable {n b Vb W}

variable (orc : (k : Fin 1) → Matrix (Qubits (AR n b Vb W k)) (Qubits (AR n b Vb W k)) ℂ)

lemma unitary_pre :
    OracleCircuit.unitary (preSteps n b Vb W) orc =
      PS (Xset n b Vb W) (fun y z => ∑ a : Fin (n * b),
        bv (y (xw n b Vb W a)) * bv (z (xw n b Vb W a)) / 2) := by
  have h := hList_mul_PS orc ((List.finRange (n * b)).map (xw n b Vb W))
    ((List.nodup_finRange _).map xw_injective) ∅ (fun _ _ => 0) (by simp) (by simp)
  rw [PS_empty, Matrix.mul_one] at h
  rw [preSteps, show (List.finRange (n * b)).map (fun a => hStep (ar := AR n b Vb W) (xw n b Vb W a))
    = ((List.finRange (n * b)).map (xw n b Vb W)).map hStep from by rw [List.map_map]; rfl, h]
  apply PS_congr
  · ext a; simp [Xset]
  · intro y z _
    congr 1
    rw [Fin.sum_univ_def, List.map_map]
    simp [Function.comp_def]

lemma qStep_mat (adj : Bool) :
    (qStep n b Vb W adj).mat orc = if adj then star (orc 0) else orc 0 := by
  simp only [qStep, OracleStep.mat]
  exact embedOp_refl _

lemma unitary_ph (cv : Fin Vb → ℝ) :
    OracleCircuit.unitary (phSteps n b Vb W cv) orc =
      Matrix.diagonal fun y => ph (∑ j : Fin Vb, cv j * bv (y (vw n b Vb W j))) := by
  rw [phSteps, unitary_diag_list orc (List.finRange Vb) _ (fun j y => cv j * bv (y (vw n b Vb W j)))
    (fun j _ => d1Step_mat orc _ _)]
  congr 1

lemma unitary_post_aux : ∀ k, k ≤ n →
    OracleCircuit.unitary ((List.range k).flatMap
      (fun i => if h : i < n then qftSteps (ar := AR n b Vb W) (Ew n b Vb W ⟨i, h⟩) else [])) orc =
      PS ((Finset.univ.filter (fun p : Fin n × Fin b => (p.1 : ℕ) < k)).image
          (fun p => Ew n b Vb W p.1 p.2))
        (fun y z => ∑ i : Fin n, if (i : ℕ) < k then
          Qph b (y ∘ Ew n b Vb W i) (z ∘ Ew n b Vb W i) else 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [List.range_zero, List.flatMap_nil, unitary_nil]
    rw [← PS_empty]
    apply PS_congr
    · ext a; simp
    · intro y z _; simp
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    rw [List.range_succ, List.flatMap_append, unitary_append, ih (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, dif_pos hkn]
    set kk : Fin n := ⟨k, hkn⟩ with hkk
    rw [qft_mul_PS orc (Ew n b Vb W kk) (Ew_injective kk)]
    · apply PS_congr
      · ext a
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, Prod.exists]
        constructor
        · rintro (⟨i, t, hi, rfl⟩ | ⟨t, rfl⟩)
          · exact ⟨i, t, by omega, rfl⟩
          · exact ⟨kk, t, by simp [kk], rfl⟩
        · rintro ⟨i, t, hi, rfl⟩
          by_cases h : (i : ℕ) < k
          · exact Or.inl ⟨i, t, h, rfl⟩
          · right; refine ⟨t, ?_⟩
            have : i = kk := by ext; simp [kk]; omega
            rw [this]
      · intro y z _
        congr 1
        have : ∀ i : Fin n, (if (i : ℕ) < k + 1 then
            Qph b (y ∘ Ew n b Vb W i) (z ∘ Ew n b Vb W i) else 0) =
            (if (i : ℕ) < k then Qph b (y ∘ Ew n b Vb W i) (z ∘ Ew n b Vb W i) else 0) +
            (if kk = i then Qph b (y ∘ Ew n b Vb W i) (z ∘ Ew n b Vb W i) else 0) := by
          intro i
          by_cases h : (i : ℕ) < k
          · have : kk ≠ i := by intro h'; subst h'; simp [kk] at h
            simp [h, this, show (i : ℕ) < k + 1 by omega]
          · by_cases h' : (i : ℕ) = k
            · have : kk = i := by ext; simp [kk, h']
              simp [h, this, show (i : ℕ) < k + 1 by omega]
            · have : kk ≠ i := by intro h''; subst h''; simp [kk] at h'
              simp [h, this, show ¬ (i : ℕ) < k + 1 by omega]
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        ring
    · intro t h
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Prod.exists] at h
      obtain ⟨i, t', hi, he⟩ := h
      have := (Ew_injective2 he).1
      subst this; simp [kk] at hi
    · intro t y z β
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · congr 1
        funext t'
        simp only [Function.comp_apply]
        rw [Function.update_of_ne]
        intro he
        have := (Ew_injective2 he).1
        subst this; simp [kk] at hi
      · rfl

lemma unitary_post :
    OracleCircuit.unitary (postSteps n b Vb W) orc =
      PS (Xset n b Vb W) (fun y z => ∑ i : Fin n,
        Qph b (y ∘ Ew n b Vb W i) (z ∘ Ew n b Vb W i)) := by
  rw [postSteps, unitary_post_aux orc n le_rfl]
  apply PS_congr
  · rw [Xset_eq_image]; congr 1; ext p; simp
  · intro y z _; simp

lemma postSteps_isGate : ∀ s ∈ postSteps n b Vb W, IsGateStep s := by
  intro s hs
  simp only [postSteps, List.mem_flatMap, List.mem_range] at hs
  obtain ⟨i, hi, hs⟩ := hs
  rw [dif_pos hi] at hs
  simp only [qftSteps, zSteps, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_flatMap, List.mem_range] at hs
  rcases hs with ⟨t, rfl⟩ | ⟨t, ht, hs⟩
  · exact d1Step_isGate _ _
  · simp only [blk, dif_pos ht, List.mem_cons, List.mem_map, List.mem_finRange, true_and] at hs
    rcases hs with rfl | ⟨s', rfl⟩
    · exact hStep_isGate _
    · exact cpStep_isGate _ _ _

lemma unitary_post_mem :
    OracleCircuit.unitary (postSteps n b Vb W) orc ∈
      Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ :=
  unitary_mem_of_steps orc _ (fun s hs => mat_unitary_of_isGate orc s (postSteps_isGate s hs))

lemma unitary_circ (cv : Fin Vb → ℝ) :
    OracleCircuit.unitary (circ n b Vb W cv) orc =
      OracleCircuit.unitary (postSteps n b Vb W) orc * star (orc 0) *
        (Matrix.diagonal fun y => ph (∑ j : Fin Vb, cv j * bv (y (vw n b Vb W j)))) * orc 0 *
        OracleCircuit.unitary (preSteps n b Vb W) orc := by
  simp only [circ, unitary_append, unitary_cons, unitary_nil, Matrix.one_mul, qStep_mat,
    unitary_ph, if_true, Bool.false_eq_true, if_false]
  simp only [Matrix.mul_assoc]

/-! ### Resource counts -/

lemma count_gates (c : OC n b Vb W) (hc : ∀ s ∈ c, IsGateStep s) :
    c.gateCount = c.length ∧ c.queryCount 0 = 0 := by
  induction c with
  | nil => simp [OracleCircuit.gateCount, OracleCircuit.queryCount]
  | cons s c ih =>
    obtain ⟨g, rfl⟩ := hc s List.mem_cons_self
    have := ih (fun s hs => hc s (List.mem_cons_of_mem _ hs))
    simp only [OracleCircuit.gateCount, OracleCircuit.queryCount, List.countP_cons,
      List.length_cons, OracleStep.IsQueryTo] at this ⊢
    simp [this.1, this.2]

lemma length_qftSteps (e : Fin b → Fin (n * b + Vb + W)) :
    (qftSteps (ar := AR n b Vb W) e).length = b + b * (b + 1) := by
  simp only [qftSteps, zSteps, List.length_append, List.length_map, List.length_finRange,
    List.length_flatMap]
  congr 1
  have : ∀ t ∈ List.range b, (blk (ar := AR n b Vb W) e t).length = b + 1 := by
    intro t ht
    rw [List.mem_range] at ht
    simp [blk, dif_pos ht]
  rw [List.map_congr_left this, List.map_const', List.sum_replicate, List.length_range,
    smul_eq_mul]

lemma length_postSteps : (postSteps n b Vb W).length = n * (b + b * (b + 1)) := by
  simp only [postSteps, List.length_flatMap]
  have : ∀ i ∈ List.range n, ((fun i => if h : i < n then
      qftSteps (ar := AR n b Vb W) (Ew n b Vb W ⟨i, h⟩) else []) i).length = b + b * (b + 1) := by
    intro i hi
    rw [List.mem_range] at hi
    simp only [dif_pos hi, length_qftSteps]
  rw [List.map_congr_left this, List.map_const', List.sum_replicate, List.length_range,
    smul_eq_mul]

lemma circ_counts (cv : Fin Vb → ℝ) :
    (circ n b Vb W cv).gateCount = n * b + Vb + n * (b + b * (b + 1)) ∧
      (circ n b Vb W cv).queryCount 0 = 2 := by
  have hpre := count_gates (preSteps n b Vb W) (by
    intro s hs; simp only [preSteps, List.mem_map] at hs
    obtain ⟨a, _, rfl⟩ := hs; exact hStep_isGate _)
  have hph := count_gates (phSteps n b Vb W cv) (by
    intro s hs; simp only [phSteps, List.mem_map] at hs
    obtain ⟨a, _, rfl⟩ := hs; exact d1Step_isGate _ _)
  have hpost := count_gates (postSteps n b Vb W) postSteps_isGate
  simp only [OracleCircuit.gateCount, OracleCircuit.queryCount] at hpre hph hpost ⊢
  simp only [circ, List.countP_append, hpre.1, hpre.2, hph.1, hph.2, hpost.1, hpost.2,
    length_postSteps, List.countP_cons, List.countP_nil, qStep, OracleStep.IsQueryTo]
  simp [preSteps, phSteps]

lemma circ_uncontrolled (cv : Fin Vb → ℝ) : Uncontrolled (circ n b Vb W cv) := by
  intro st hst
  simp only [circ, List.mem_append, List.mem_singleton] at hst
  rcases hst with (((h | rfl) | h) | rfl) | h
  · simp only [preSteps, List.mem_map] at h
    obtain ⟨a, _, rfl⟩ := h; trivial
  · rfl
  · simp only [phSteps, List.mem_map] at h
    obtain ⟨a, _, rfl⟩ := h; trivial
  · rfl
  · obtain ⟨g, rfl⟩ := postSteps_isGate st h; trivial

end Circuit

end LTFB

end Mod_Circuit

section Mod_State

open QAlgorithms QuantumLTF.Membership

namespace LTFB

/-! ### Generic vector facts -/

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma act_apply_ket (A : Matrix ι ι ℂ) (z y : ι) : (act A (ket z)) y = A y z := by
  simp [act, ket, Matrix.mulVec_single]

lemma act_sum_smul {κ : Type} [Fintype κ] (A : Matrix ι ι ℂ) (a : κ → ℂ)
    (v : κ → EuclideanSpace ℂ ι) : act A (∑ x, a x • v x) = ∑ x, a x • act A (v x) := by
  have : ∀ ψ, act A ψ = Matrix.toEuclideanLin A ψ := fun ψ => rfl
  simp only [this, map_sum, map_smul]

lemma act_mul (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  simp [act, Matrix.mulVec_mulVec]

lemma act_sub (A : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act A (ψ - φ) = act A ψ - act A φ := by
  have : ∀ ψ, act A ψ = Matrix.toEuclideanLin A ψ := fun ψ => rfl
  simp only [this, map_sub]

lemma act_diagonal_ket (d : ι → ℂ) (z : ι) : act (Matrix.diagonal d) (ket z) = d z • ket z := by
  ext y
  simp only [act, ket, Matrix.mulVec_single, PiLp.smul_apply, smul_eq_mul]
  by_cases h : y = z
  · subst h; simp
  · simp [h, Matrix.diagonal_apply_ne _ h]

lemma prob_eq (ψ : EuclideanSpace ℂ ι) (z : ι) : prob ψ z = ‖ψ z‖ ^ 2 := by
  simp [prob, ket, EuclideanSpace.inner_single_left]

/-- Restriction of a vector to a set of outcomes. -/
noncomputable def restr (P : ι → Prop) [DecidablePred P] (ψ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι := WithLp.toLp 2 fun y => if P y then ψ y else 0

lemma norm_restr_sq (P : ι → Prop) [DecidablePred P] (ψ : EuclideanSpace ℂ ι) :
    ‖restr P ψ‖ ^ 2 = probEvent ψ P := by
  rw [EuclideanSpace.norm_sq_eq, probEvent, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  simp only [restr, prob_eq]
  split_ifs <;> simp

lemma norm_restr_le (P : ι → Prop) [DecidablePred P] (ψ : EuclideanSpace ℂ ι) :
    ‖restr P ψ‖ ≤ ‖ψ‖ := by
  have h1 := EuclideanSpace.norm_sq_eq (restr P ψ)
  have h2 := EuclideanSpace.norm_sq_eq ψ
  have : ‖restr P ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [h1, h2]
    apply Finset.sum_le_sum
    intro y _
    simp only [restr]
    split_ifs <;> simp
  exact le_of_sq_le_sq (by simpa using this) (norm_nonneg _) |>.trans (le_of_eq rfl)

lemma restr_sub (P : ι → Prop) [DecidablePred P] (ψ φ : EuclideanSpace ℂ ι) :
    restr P ψ = restr P φ + restr P (ψ - φ) := by
  ext y
  simp only [restr, PiLp.add_apply, PiLp.sub_apply]
  split_ifs <;> simp

lemma sqrt_probEvent_le (P : ι → Prop) [DecidablePred P] (ψ φ : EuclideanSpace ℂ ι) :
    Real.sqrt (probEvent ψ P) ≤ Real.sqrt (probEvent φ P) + ‖ψ - φ‖ := by
  rw [← norm_restr_sq, ← norm_restr_sq, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _), restr_sub P ψ φ]
  calc ‖restr P φ + restr P (ψ - φ)‖ ≤ ‖restr P φ‖ + ‖restr P (ψ - φ)‖ := norm_add_le _ _
    _ ≤ _ := by linarith [norm_restr_le P (ψ - φ)]

end Generic

/-! ### States on the register -/

section States

variable {n b Vb W : ℕ}

/-- `Σ_x a(x) |x⟩|0⟩|0⟩`. -/
noncomputable def st (a : (Fin n → Qubits b) → ℂ) : EuclideanSpace ℂ (Qubits (n * b + Vb + W)) :=
  ∑ x, a x • ket (regBasis n b Vb W x fun _ => false)

/-- The `x`-register condition. -/
def Cnd (y : Qubits (n * b + Vb + W)) : Prop := ∀ a, a ∉ Xset n b Vb W → y a = false

instance (y : Qubits (n * b + Vb + W)) : Decidable (Cnd y) := by unfold Cnd; infer_instance

lemma Cnd_regBasis (x : Fin n → Qubits b) : Cnd (regBasis n b Vb W x fun _ => false) :=
  fun a ha => regBasis_zero_off x a ha

lemma st_apply (a : (Fin n → Qubits b) → ℂ) (y : Qubits (n * b + Vb + W)) :
    (st (Vb := Vb) (W := W) a) y = if Cnd y then a (dec y) else 0 := by
  simp only [st, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, ket,
    smul_eq_mul]
  have : ∀ x, a x * (EuclideanSpace.single (regBasis n b Vb W x fun _ => false) (1 : ℂ)) y =
      if x = dec y ∧ Cnd y then a x else 0 := by
    intro x
    rw [EuclideanSpace.single_apply]
    by_cases h : y = regBasis n b Vb W x fun _ => false
    · subst h
      simp [dec_regBasis, Cnd_regBasis]
    · rw [if_neg h, mul_zero, if_neg]
      rintro ⟨rfl, hc⟩
      exact h (regBasis_dec y hc).symm
  simp only [this]
  by_cases hc : Cnd y
  · simp [hc]
  · simp [hc]

lemma sum_Cnd (g : Qubits (n * b + Vb + W) → ℝ) (hg : ∀ y, ¬ Cnd y → g y = 0) :
    ∑ y, g y = ∑ k : Fin n → Qubits b, g (regBasis n b Vb W k fun _ => false) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := fun k => regBasis n b Vb W k fun _ => false)
    (fun x _ x' _ h => regBasis_injective _ h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  apply hg
  intro hc
  apply hy
  rw [Finset.mem_image]
  exact ⟨dec y, Finset.mem_univ _, regBasis_dec y hc⟩

lemma norm_st_sq (a : (Fin n → Qubits b) → ℂ) :
    ‖st (Vb := Vb) (W := W) a‖ ^ 2 = ∑ x, ‖a x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have : ∀ y, ‖(st (Vb := Vb) (W := W) a).ofLp y‖ ^ 2 = if Cnd y then ‖a (dec y)‖ ^ 2 else 0 := by
    intro y
    have := st_apply (Vb := Vb) (W := W) a y
    change ‖(st (Vb := Vb) (W := W) a) y‖ ^ 2 = _
    rw [this]; split_ifs <;> simp
  simp only [this]
  rw [sum_Cnd]
  · apply Finset.sum_congr rfl; intro k _
    simp [Cnd_regBasis, dec_regBasis]
  · intro y hy; simp [hy]

lemma st_sub (a a' : (Fin n → Qubits b) → ℂ) :
    st (Vb := Vb) (W := W) a - st a' = st (fun x => a x - a' x) := by
  simp only [st, ← Finset.sum_sub_distrib, sub_smul]

variable (orc : (k : Fin 1) → Matrix (Qubits (AR n b Vb W k)) (Qubits (AR n b Vb W k)) ℂ)

/-- The common normalisation `2^{-nb/2}`. -/
noncomputable def c0 (n b : ℕ) : ℂ := ((Real.sqrt 2 : ℂ))⁻¹ ^ (n * b)

lemma act_pre_zero :
    act (OracleCircuit.unitary (preSteps n b Vb W) orc) (zeroKet _) =
      st (Vb := Vb) (W := W) (fun _ => c0 n b) := by
  ext y
  change (act _ (ket _)) y = (st (Vb := Vb) (W := W) (fun _ => c0 n b)) y
  rw [act_apply_ket, st_apply, unitary_pre, PS_apply, card_Xset]
  by_cases hc : Cnd y
  · rw [if_pos hc, if_pos (show ∀ a, a ∉ Xset n b Vb W → y a = (fun _ => false) a from hc)]
    simp [c0]
  · rw [if_neg hc, if_neg (show ¬ ∀ a, a ∉ Xset n b Vb W → y a = (fun _ => false) a from hc)]

lemma act_post_st (a : (Fin n → Qubits b) → ℂ) (y : Qubits (n * b + Vb + W)) :
    (act (OracleCircuit.unitary (postSteps n b Vb W) orc) (st (Vb := Vb) (W := W) a)) y =
      if Cnd y then c0 n b * ∑ x, a x * ph (∑ i : Fin n, Qph b (dec y i) (x i)) else 0 := by
  rw [st, act_sum_smul]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ x, (act (OracleCircuit.unitary (postSteps n b Vb W) orc)
      (ket (regBasis n b Vb W x fun _ => false))).ofLp y =
      if Cnd y then c0 n b * ph (∑ i : Fin n, Qph b (dec y i) (x i)) else 0 := by
    intro x
    change (act _ (ket _)) y = _
    rw [act_apply_ket, unitary_post, PS_apply, card_Xset]
    have hiff : (∀ w, w ∉ Xset n b Vb W → y w = regBasis n b Vb W x (fun _ => false) w) ↔
        Cnd y := by
      constructor
      · intro h w hw; rw [h w hw, regBasis_zero_off x w hw]
      · intro h w hw; rw [h w hw, regBasis_zero_off x w hw]
    by_cases hc : Cnd y
    · rw [if_pos (hiff.2 hc), if_pos hc]
      simp only [regBasis_comp_Ew, c0]
      rfl
    · rw [if_neg (mt hiff.1 hc), if_neg hc]
  simp only [this]
  by_cases hc : Cnd y
  · simp only [if_pos hc, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  · simp [hc]

lemma circ_state (cv : Fin Vb → ℝ) (Htil : (Fin n → Qubits b) → Qubits Vb)
    (hU : orc 0 ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ)
    (hO : ∀ x, act (orc 0) (ket (regBasis n b Vb W x fun _ => false)) =
      ket (regBasis n b Vb W x (Htil x))) :
    act (OracleCircuit.unitary (circ n b Vb W cv) orc) (zeroKet _) =
      act (OracleCircuit.unitary (postSteps n b Vb W) orc)
        (st (Vb := Vb) (W := W) fun x => c0 n b * ph (∑ j : Fin Vb, cv j * bv (Htil x j))) := by
  have hinv : ∀ x, act (star (orc 0)) (ket (regBasis n b Vb W x (Htil x))) =
      ket (regBasis n b Vb W x fun _ => false) := by
    intro x
    rw [← hO, ← act_mul, Matrix.mem_unitaryGroup_iff'.1 hU]
    simp [act]
  rw [unitary_circ]
  simp only [act_mul]
  rw [act_pre_zero, st, st]
  simp only [act_sum_smul, hO, act_diagonal_ket, regBasis_vw, smul_smul, hinv]

lemma probEvent_post (a : (Fin n → Qubits b) → ℂ) (P : Qubits (n * b + Vb + W) → Prop)
    [DecidablePred P] :
    probEvent (act (OracleCircuit.unitary (postSteps n b Vb W) orc) (st (Vb := Vb) (W := W) a)) P =
      ∑ k : Fin n → Qubits b, if P (regBasis n b Vb W k fun _ => false) then
        ‖c0 n b * ∑ x, a x * ph (∑ i : Fin n, Qph b (k i) (x i))‖ ^ 2 else 0 := by
  rw [probEvent, Finset.sum_filter, sum_Cnd]
  · apply Finset.sum_congr rfl; intro k _
    rw [prob_eq, act_post_st, if_pos (Cnd_regBasis k), dec_regBasis]
  · intro y hy
    rw [prob_eq, act_post_st, if_neg hy]
    simp

end States

end LTFB

end Mod_State

section Mod_Amp

open QAlgorithms QuantumLTF.Membership

namespace LTFB

/-- One register's output amplitude. -/
noncomputable def betaQ (b : ℕ) (γ : ℝ) (κ : Qubits b) : ℂ :=
  (1 / ((2 : ℂ) ^ b)) * ∑ j : Qubits b, ph (γ * (bitsToNat j : ℝ) + Qph b κ j)

/-- The same amplitude written as a geometric sum. -/
noncomputable def betaR (N : ℕ) (γ : ℝ) (K : ℕ) : ℂ :=
  (1 / (N : ℂ)) * ∑ m ∈ Finset.range N, ph (m * (γ - K / N - 1 / 2))

lemma sum_qubits_nat {M : Type*} [AddCommMonoid M] (b : ℕ) (f : ℕ → M) :
    ∑ j : Qubits b, f (bitsToNat j) = ∑ m ∈ Finset.range (2 ^ b), f m := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_equiv (bitsEquivFin b) _ _ (fun j => ?_)
  rw [bitsEquivFin_apply]

lemma sum_qubits_rev {M : Type*} [AddCommMonoid M] (b : ℕ) (f : ℕ → M) :
    ∑ κ : Qubits b, f (bitsToNat (κ ∘ Fin.rev)) = ∑ m ∈ Finset.range (2 ^ b), f m := by
  rw [← sum_qubits_nat]
  refine Fintype.sum_equiv (Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin b))
    (Equiv.refl Bool)).symm _ _ (fun κ => ?_)
  congr 2

lemma betaQ_eq (b : ℕ) (γ : ℝ) (κ : Qubits b) :
    betaQ b γ κ = betaR (2 ^ b) γ (bitsToNat (κ ∘ Fin.rev)) := by
  unfold betaQ betaR
  push_cast
  congr 1
  have : ∀ j : Qubits b, ph (γ * (bitsToNat j : ℝ) + Qph b κ j) =
      ph ((bitsToNat j : ℝ) * (γ - (bitsToNat (κ ∘ Fin.rev) : ℝ) / (2 : ℝ) ^ b - 1 / 2)) := by
    intro j
    rw [ph_add, Qph_ph, ← ph_add]
    congr 1; ring
  simp only [this]
  rw [sum_qubits_nat b (fun m : ℕ => ph ((m : ℝ) * (γ - (bitsToNat (κ ∘ Fin.rev) : ℝ) /
    (2 : ℝ) ^ b - 1 / 2)))]

lemma c0_sq (n b : ℕ) : c0 n b * c0 n b = ∏ _i : Fin n, (1 / ((2 : ℂ) ^ b)) := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, c0, ← mul_pow]
  have : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  rw [this, mul_comm n b, pow_mul, one_div_pow]

lemma amp_factor (n b : ℕ) (C : ℝ) (γ : Fin n → ℝ) (k : Fin n → Qubits b) :
    c0 n b * ∑ x : Fin n → Qubits b,
        (c0 n b * ph (C + ∑ i : Fin n, γ i * (bitsToNat (x i) : ℝ))) *
          ph (∑ i : Fin n, Qph b (k i) (x i)) =
      ph C * ∏ i : Fin n, betaQ b (γ i) (k i) := by
  have : ∀ x : Fin n → Qubits b,
      (c0 n b * ph (C + ∑ i : Fin n, γ i * (bitsToNat (x i) : ℝ))) *
        ph (∑ i : Fin n, Qph b (k i) (x i)) =
      c0 n b * ph C * ∏ i : Fin n, ph (γ i * (bitsToNat (x i) : ℝ) + Qph b (k i) (x i)) := by
    intro x
    rw [ph_add, ph_sum, ph_sum]
    simp only [ph_add, Finset.prod_mul_distrib]
    ring
  simp only [this, ← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun i j => ph (γ i * (bitsToNat j : ℝ) + Qph b (k i) j))]
  simp only [betaQ]
  rw [Finset.prod_mul_distrib, ← c0_sq]
  ring

lemma norm_c0_sq_sum (n b : ℕ) :
    ∑ _x : Fin n → Qubits b, ‖c0 n b‖ ^ 2 = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : (Fintype.card (Fin n → Qubits b) : ℝ) = (2 : ℝ) ^ (n * b) := by
    rw [Fintype.card_fun, Fintype.card_fun]; simp [pow_mul']
  have h2 : ‖c0 n b‖ ^ 2 = (1 / 2 : ℝ) ^ (n * b) := by
    rw [c0, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ← pow_mul, mul_comm, pow_mul, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [h1, h2, ← mul_pow]; norm_num

/-- Parseval for one register, from the unitarity of the circuit. -/
lemma sum_betaQ_sq (b : ℕ) (γ : ℝ) : ∑ κ : Qubits b, ‖betaQ b γ κ‖ ^ 2 = 1 := by
  let orc : (k : Fin 1) → Matrix (Qubits (AR 1 b 0 0 k)) (Qubits (AR 1 b 0 0 k)) ℂ := fun _ => 1
  let a : (Fin 1 → Qubits b) → ℂ := fun x =>
    c0 1 b * ph (0 + ∑ i : Fin 1, γ * (bitsToNat (x i) : ℝ))
  set ψ := act (OracleCircuit.unitary (postSteps 1 b 0 0) orc) (st (Vb := 0) (W := 0) a) with hψ
  have hnorm : ‖ψ‖ = 1 := by
    rw [hψ, act_norm_of_mem_unitaryGroup (unitary_post_mem orc)]
    have := norm_st_sq (Vb := 0) (W := 0) a
    have h2 : ∑ x, ‖a x‖ ^ 2 = 1 := by
      rw [← norm_c0_sq_sum 1 b]
      apply Finset.sum_congr rfl; intro x _
      simp only [a, norm_mul, norm_ph, mul_one]
    rw [h2] at this
    have h3 : 0 ≤ ‖st (Vb := 0) (W := 0) a‖ := norm_nonneg _
    nlinarith
  have hP : probEvent ψ (fun _ => True) = 1 := by
    rw [← norm_restr_sq]
    have : restr (fun _ => True) ψ = ψ := by ext y; simp [restr]
    rw [this, hnorm]; norm_num
  rw [hψ, probEvent_post] at hP
  have key : ∀ k : Fin 1 → Qubits b, c0 1 b * ∑ x : Fin 1 → Qubits b,
      a x * ph (∑ i : Fin 1, Qph b (k i) (x i)) = ph 0 * ∏ i : Fin 1, betaQ b γ (k i) :=
    fun k => amp_factor 1 b 0 (fun _ => γ) k
  simp only [if_true] at hP
  simp only [key] at hP
  simp only [ph_zero, one_mul, Finset.univ_unique, Finset.prod_singleton] at hP
  rw [← hP]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Qubits b)).symm _ _ (fun κ => ?_)
  simp [Equiv.funUnique]

end LTFB

end Mod_Amp

section Mod_Prob

open QAlgorithms QuantumLTF.Membership

namespace LTFB

/-- Phase-gate angles on the value register. -/
noncomputable def cvf (b Vb Vf : ℕ) (j : Fin Vb) : ℝ :=
  (2 : ℝ) ^ b * (2 : ℝ) ^ (Vb - 1 - (j : ℕ)) / (2 : ℝ) ^ Vf

/-- Output wires of register `i` (reversed order). -/
def oaE (n b Vb W : ℕ) (i : Fin n) : Fin b ↪ Fin (n * b + Vb + W) :=
  ⟨fun u => Ew n b Vb W i (Fin.rev u), fun _ _ h => Fin.rev_injective (Ew_injective i h)⟩

lemma phase_sum (b Vb Vf : ℕ) (v : Qubits Vb) :
    ∑ j : Fin Vb, cvf b Vb Vf j * bv (v j) =
      (2 : ℝ) ^ b * (fpVal Vb Vf v + (2 : ℝ) ^ Vb / 2 / (2 : ℝ) ^ Vf) := by
  have h : (2 : ℝ) ^ b * (fpVal Vb Vf v + (2 : ℝ) ^ Vb / 2 / (2 : ℝ) ^ Vf) =
      (2 : ℝ) ^ b / (2 : ℝ) ^ Vf * (bitsToNat v : ℝ) := by
    unfold fpVal; field_simp; ring
  rw [h, bitsToNat_real, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  unfold cvf; ring

lemma inner_rho_grid {n b : ℕ} (w : EuclideanSpace ℝ (Fin n)) (x : Fin n → Qubits b) (ρ : ℝ) :
    inner ℝ w (ρ • gridVec n b x) = ρ * ∑ i, w i * gridPoint b (x i) := by
  rw [real_inner_smul_right]
  simp [gridVec, PiLp.inner_apply, mul_comm]

lemma height_expand {n b : ℕ} (w p : EuclideanSpace ℝ (Fin n)) (θ ρ : ℝ) (x : Fin n → Qubits b)
    (hs : inner ℝ w p ≠ 0) :
    (2 : ℝ) ^ b * height w θ p (ρ • gridVec n b x) =
      (2 : ℝ) ^ b * θ / inner ℝ w p +
        ∑ i, (-ρ * w i / inner ℝ w p) * ((bitsToNat (x i) : ℝ) + 1 / 2 - (2 : ℝ) ^ b / 2) := by
  unfold height
  rw [inner_rho_grid]
  have hN : (2 : ℝ) ^ b ≠ 0 := pow_ne_zero _ (by norm_num)
  have : ∑ i, (-ρ * w i / inner ℝ w p) * ((bitsToNat (x i) : ℝ) + 1 / 2 - (2 : ℝ) ^ b / 2) =
      -((2 : ℝ) ^ b * (ρ * ∑ i, w i * gridPoint b (x i)) / inner ℝ w p) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    unfold gridPoint
    field_simp
    ring
  rw [this]
  field_simp
  ring

lemma numeric_tau (τ : ℝ) (h1 : 1 ≤ τ) (h2 : τ ≤ 2) :
    (Real.sqrt 3 / 2 + τ / 24) ^ 2 ≤ 1 - 1 / (6 * τ) := by
  have hs : Real.sqrt 3 ≤ 1.75 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hτ : 0 < τ := by linarith
  rw [show 1 - 1 / (6 * τ) = (6 * τ - 1) / (6 * τ) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) hτ.le,
    mul_le_mul_of_nonneg_right hs (sq_nonneg τ)]

lemma numeric_final (n T : ℝ) (hn : 1 ≤ n) (h1 : 3 * n + 1 ≤ T) (h2 : T ≤ 2 * (3 * n + 1)) :
    (Real.sqrt 3 / 2 + T / (24 * (3 * n + 1))) ^ 2 ≤ 1 - n / (2 * T - 1) := by
  have ha : 0 < 3 * n + 1 := by linarith
  set τ := T / (3 * n + 1) with hτ
  have hτ1 : 1 ≤ τ := by rw [hτ, le_div_iff₀ ha]; linarith
  have hτ2 : τ ≤ 2 := by rw [hτ, div_le_iff₀ ha]; linarith
  have e1 : T / (24 * (3 * n + 1)) = τ / 24 := by rw [hτ]; field_simp
  rw [e1]
  have e2 : n / (2 * T - 1) ≤ 1 / (6 * τ) := by
    have hT : T = τ * (3 * n + 1) := by rw [hτ]; field_simp
    rw [div_le_div_iff₀ (by nlinarith) (by positivity), hT]
    nlinarith
  linarith [numeric_tau τ hτ1 hτ2]

/-- The probability analysis of the circuit. -/
theorem prob_core (n b Vb Vf W r : ℕ) (hn : 1 ≤ n) (hrb : r ≤ b)
    (hρ : rho n = 1 / (2 : ℝ) ^ r) (hρ5 : 10 * rho n ≤ 1 / 5) (εg : ℝ) (hεg : 0 < εg)
    (hεg10 : εg ≤ 10)
    (hT1 : (3 * n + 1 : ℝ) ≤ (2 : ℝ) ^ b * rho n * εg)
    (hT2 : (2 : ℝ) ^ b * rho n * εg < 2 * (3 * n + 1))
    (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (hw : ‖w‖ = 1)
    (hwp : 1 / 10 ≤ |inner ℝ w p|)
    (Htil : (Fin n → Qubits b) → Qubits Vb)
    (hH : ∀ x, |fpVal Vb Vf (Htil x) - height w θ p (rho n • gridVec n b x)| ≤
      rho n * εg / (48 * Real.pi * (3 * n + 1)))
    (OH : Matrix (Qubits (n * b + Vb + W)) (Qubits (n * b + Vb + W)) ℂ)
    (hOH : OH ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ)
    (hspec : ∀ x, act OH (ket (regBasis n b Vb W x fun _ => false)) =
      ket (regBasis n b Vb W x (Htil x))) :
    open Classical in
    probEvent (act ((circ n b Vb W (cvf b Vb Vf)).unitary fun _ => OH) (zeroKet _))
      (fun z => ∀ i, |readFp (oaE n b Vb W i) (b - r) z - (-(w i) / inner ℝ w p)| ≤ εg) ≥
        3 / 4 := by
  classical
  set N : ℝ := (2 : ℝ) ^ b with hN
  set s : ℝ := inner ℝ w p with hs
  set ρ : ℝ := rho n with hρdef
  set T : ℝ := N * ρ * εg with hT
  set η : ℝ := ρ * εg / (48 * Real.pi * (3 * n + 1)) with hη
  have hNpos : 0 < N := by positivity
  have hs0 : s ≠ 0 := by intro h; rw [h, abs_zero] at hwp; norm_num at hwp
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set γ : Fin n → ℝ := fun i => -ρ * w i / s with hγ
  have hwi : ∀ i, |w i| ≤ 1 := by
    intro i; have := PiLp.norm_apply_le w i; simpa [hw] using this
  have hγ5 : ∀ i, |γ i| ≤ 1 / 5 := by
    intro i
    simp only [hγ]
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hρpos, div_le_iff₀ (by positivity)]
    have := hwi i
    nlinarith [abs_nonneg (w i)]
  -- the oracle
  let orc : (k : Fin 1) → Matrix (Qubits (AR n b Vb W k)) (Qubits (AR n b Vb W k)) ℂ :=
    fun _ => OH
  have hcs := circ_state orc (cvf b Vb Vf) Htil hOH hspec
  change probEvent (act ((circ n b Vb W (cvf b Vb Vf)).unitary orc) (zeroKet _)) _ ≥ 3 / 4
  rw [hcs]
  -- phases
  set U := OracleCircuit.unitary (postSteps n b Vb W) orc with hU
  set C0 : ℝ := N * θ / s + ∑ i, γ i * (1 / 2 - N / 2) + N * ((2 : ℝ) ^ Vb / 2 / (2 : ℝ) ^ Vf)
    with hC0
  set a : (Fin n → Qubits b) → ℂ := fun x => c0 n b * ph (∑ j : Fin Vb, cvf b Vb Vf j * bv (Htil x j))
    with ha
  set a' : (Fin n → Qubits b) → ℂ :=
    fun x => c0 n b * ph (C0 + ∑ i : Fin n, γ i * (bitsToNat (x i) : ℝ)) with ha'
  have hφ : ∀ x, |(∑ j : Fin Vb, cvf b Vb Vf j * bv (Htil x j)) -
      (C0 + ∑ i : Fin n, γ i * (bitsToNat (x i) : ℝ))| ≤ N * η := by
    intro x
    rw [phase_sum]
    have h2 := height_expand w p θ ρ x hs0
    have : C0 + ∑ i : Fin n, γ i * (bitsToNat (x i) : ℝ) =
        N * (height w θ p (ρ • gridVec n b x) + (2 : ℝ) ^ Vb / 2 / (2 : ℝ) ^ Vf) := by
      rw [mul_add, h2, hC0]
      have : ∑ i, γ i * (1 / 2 - N / 2) + ∑ i : Fin n, γ i * (bitsToNat (x i) : ℝ) =
          ∑ i, (-ρ * w i / s) * ((bitsToNat (x i) : ℝ) + 1 / 2 - N / 2) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        simp only [hγ]; ring
      linarith
    rw [this, ← mul_sub, abs_mul, abs_of_pos hNpos]
    have := hH x
    apply mul_le_mul_of_nonneg_left _ hNpos.le
    calc _ = |fpVal Vb Vf (Htil x) - height w θ p (rho n • gridVec n b x)| := by
          congr 1; ring
      _ ≤ η := this
  -- distance between actual and ideal states
  have hdist : ‖act U (st (Vb := Vb) (W := W) a) - act U (st (Vb := Vb) (W := W) a')‖ ≤
      2 * Real.pi * (N * η) := by
    rw [← act_sub, act_norm_of_mem_unitaryGroup (unitary_post_mem orc), st_sub]
    have h1 := norm_st_sq (Vb := Vb) (W := W) (fun x => a x - a' x)
    have h2 : ∑ x, ‖a x - a' x‖ ^ 2 ≤ (2 * Real.pi * (N * η)) ^ 2 := by
      calc ∑ x, ‖a x - a' x‖ ^ 2 ≤ ∑ x : Fin n → Qubits b, ‖c0 n b‖ ^ 2 *
            (2 * Real.pi * (N * η)) ^ 2 := by
            apply Finset.sum_le_sum; intro x _
            have e : ‖a x - a' x‖ ^ 2 = ‖c0 n b‖ ^ 2 *
                ‖ph (∑ j : Fin Vb, cvf b Vb Vf j * bv (Htil x j)) -
                  ph (C0 + ∑ i : Fin n, γ i * (bitsToNat (x i) : ℝ))‖ ^ 2 := by
              simp only [ha, ha']; rw [← mul_sub, norm_mul, mul_pow]
            rw [e]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply pow_le_pow_left₀ (norm_nonneg _)
            calc _ ≤ 2 * Real.pi * |(∑ j : Fin Vb, cvf b Vb Vf j * bv (Htil x j)) -
                  (C0 + ∑ i : Fin n, γ i * (bitsToNat (x i) : ℝ))| := norm_ph_sub_ph_le _ _
              _ ≤ _ := by
                apply mul_le_mul_of_nonneg_left (hφ x) (by positivity)
        _ = (2 * Real.pi * (N * η)) ^ 2 := by
            rw [← Finset.sum_mul, norm_c0_sq_sum, one_mul]
    rw [← h1] at h2
    have hpos : 0 ≤ 2 * Real.pi * (N * η) := by positivity
    nlinarith [norm_nonneg (st (Vb := Vb) (W := W) fun x => a x - a' x)]
  -- the ideal success probability
  set E : Qubits (n * b + Vb + W) → Prop :=
    fun z => ∀ i, |readFp (oaE n b Vb W i) (b - r) z - (-(w i) / s)| ≤ εg with hE
  set G : Fin n → Qubits b → Prop :=
    fun i κ => |(bitsToNat (κ ∘ Fin.rev) : ℝ) - N * (γ i + 1 / 2)| ≤ T with hG
  have hfo : (2 : ℝ) ^ (b - r) = N * ρ := by
    rw [hN, hρ, pow_sub₀ _ (by norm_num) hrb]; ring
  have hEG : ∀ k : Fin n → Qubits b,
      E (regBasis n b Vb W k fun _ => false) ↔ ∀ i, G i (k i) := by
    intro k
    apply forall_congr'
    intro i
    have hcomp : (regBasis n b Vb W k fun _ => false) ∘ (oaE n b Vb W i) = k i ∘ Fin.rev := by
      funext u; exact regBasis_Ew k _ i (Fin.rev u)
    simp only [readFp, hcomp, fpVal, hfo, hG]
    have hNρ : 0 < N * ρ := by positivity
    rw [show ((bitsToNat (k i ∘ Fin.rev) : ℝ) - (2 : ℝ) ^ b / 2) / (N * ρ) - -w i / s =
        ((bitsToNat (k i ∘ Fin.rev) : ℝ) - N * (γ i + 1 / 2)) / (N * ρ) by
      rw [hγ, hN]; field_simp; ring]
    rw [abs_div, abs_of_pos hNρ, div_le_iff₀ hNρ, hT]
    constructor <;> intro h <;> linarith
  have hT1' : 3 * (n : ℝ) + 1 ≤ T := by rw [hT]; linarith
  have hT2' : T < 2 * (3 * n + 1) := by rw [hT]; linarith
  have hTpos : 1 < T := by linarith
  have hTN : T ≤ ((2 ^ b : ℕ) : ℝ) / 5 := by
    rw [hT]; push_cast
    have : ρ * εg ≤ 1 / 5 := by nlinarith
    nlinarith
  -- failure weight of one coordinate
  set F : Fin n → ℝ := fun i =>
    ∑ κ : Qubits b, if G i κ then 0 else ‖betaQ b (γ i) κ‖ ^ 2 with hF
  have hF0 : ∀ i, 0 ≤ F i := fun i =>
    Finset.sum_nonneg (fun κ _ => by split_ifs <;> positivity)
  have hF1 : ∀ i, F i ≤ 1 / (2 * T - 1) := by
    intro i
    simp only [hF, hG]
    simp only [betaQ_eq]
    rw [sum_qubits_rev b (fun K => if |(K : ℝ) - N * (γ i + 1 / 2)| ≤ T then 0 else
      ‖betaR (2 ^ b) (γ i) K‖ ^ 2)]
    have := fail_bound (2 ^ b) (by positivity) (γ i) T (hγ5 i) (by linarith) hTN
    rw [Finset.sum_filter] at this
    convert this using 2 with K _
    · rw [betaR]; push_cast; rw [hN]
      split_ifs <;> rfl
  have hgood : ∀ i, (∑ κ : Qubits b, if G i κ then ‖betaQ b (γ i) κ‖ ^ 2 else 0) = 1 - F i := by
    intro i
    have h1 := sum_betaQ_sq b (γ i)
    have h2 : (∑ κ : Qubits b, if G i κ then ‖betaQ b (γ i) κ‖ ^ 2 else 0) + F i =
        ∑ κ : Qubits b, ‖betaQ b (γ i) κ‖ ^ 2 := by
      rw [hF, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro κ _
      split_ifs <;> ring
    linarith
  have hP' : 1 - n / (2 * T - 1) ≤ probEvent (act U (st (Vb := Vb) (W := W) a')) E := by
    rw [hU, probEvent_post]
    have key : ∀ k : Fin n → Qubits b, c0 n b * ∑ x : Fin n → Qubits b,
        a' x * ph (∑ i : Fin n, Qph b (k i) (x i)) = ph C0 * ∏ i : Fin n, betaQ b (γ i) (k i) :=
      fun k => amp_factor n b C0 γ k
    simp only [key]
    have : ∀ k : Fin n → Qubits b,
        (if E (regBasis n b Vb W k fun _ => false) then
          ‖ph C0 * ∏ i : Fin n, betaQ b (γ i) (k i)‖ ^ 2 else 0) =
        ∏ i : Fin n, (if G i (k i) then ‖betaQ b (γ i) (k i)‖ ^ 2 else 0) := by
      intro k
      rw [Finset.prod_ite_zero]
      by_cases h : ∀ i, G i (k i)
      · rw [if_pos ((hEG k).2 h), if_pos (fun i _ => h i), norm_mul, norm_ph, one_mul,
          norm_prod, Finset.prod_pow]
      · rw [if_neg (mt (hEG k).1 h), if_neg (fun h' => h (fun i => h' i (Finset.mem_univ _)))]
    simp only [this]
    rw [← Fintype.prod_sum (fun i κ => if G i κ then ‖betaQ b (γ i) κ‖ ^ 2 else 0)]
    simp only [hgood]
    calc 1 - n / (2 * T - 1) ≤ 1 - ∑ i : Fin n, F i := by
          have : ∑ i : Fin n, F i ≤ ∑ _i : Fin n, 1 / (2 * T - 1) :=
            Finset.sum_le_sum (fun i _ => hF1 i)
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
          rw [div_eq_mul_one_div (n : ℝ)]
          linarith
      _ ≤ _ := prod_one_sub_ge _ F (fun i _ => hF0 i) (fun i _ => by
          have := hF1 i
          have : 1 / (2 * T - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          linarith)
  -- combine
  have hsq := sqrt_probEvent_le E (act U (st (Vb := Vb) (W := W) a'))
    (act U (st (Vb := Vb) (W := W) a))
  rw [norm_sub_rev] at hsq
  have hnum := numeric_final n T hn' hT1' hT2'.le
  have hNη : 2 * Real.pi * (N * η) = T / (24 * (3 * n + 1)) := by
    rw [hη, hT]; field_simp; ring
  have hge : Real.sqrt 3 / 2 + T / (24 * (3 * n + 1)) ≤
      Real.sqrt (probEvent (act U (st (Vb := Vb) (W := W) a')) E) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hfinal : Real.sqrt 3 / 2 ≤ Real.sqrt (probEvent (act U (st (Vb := Vb) (W := W) a)) E) := by
    linarith
  have hP0 : 0 ≤ probEvent (act U (st (Vb := Vb) (W := W) a)) E :=
    Finset.sum_nonneg (fun _ _ => by rw [prob_eq]; positivity)
  have := Real.sq_sqrt hP0
  have h34 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  show 3 / 4 ≤ probEvent (act U (st (Vb := Vb) (W := W) a)) E
  nlinarith [Real.sqrt_nonneg 3]

end LTFB

end Mod_Prob

section Mod_Params

open QuantumLTF.Membership

namespace LTFB

lemma two_pow_ceil_logb (x : ℝ) (hx : 0 < x) : x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ := by
  calc x = (2 : ℝ) ^ (Real.logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ := Real.rpow_natCast _ _

lemma ceil_logb_lt (x : ℝ) (hx : 1 ≤ x) :
    ((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) < Real.logb 2 x + 1 :=
  Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hx)

lemma two_pow_ceil_logb_lt (x : ℝ) (hx : 1 ≤ x) : (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ < 2 * x := by
  calc (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ = (2 : ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
    _ < (2 : ℝ) ^ (Real.logb 2 x + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (ceil_logb_lt x hx)
    _ = 2 * x := by
        rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
          (by linarith), Real.rpow_one]; ring

lemma params (n : ℕ) (hn : 2 ≤ n) (εg : ℝ) (hεg : 0 < εg) (hεg10 : εg ≤ 10) :
    ∃ r : ℕ, r ≤ ⌈Real.logb 2 ((3 * n + 1) / (rho n * εg))⌉₊ ∧ rho n = 1 / (2 : ℝ) ^ r ∧
      10 * rho n ≤ 1 / 5 ∧
      (3 * n + 1 : ℝ) ≤ (2 : ℝ) ^ ⌈Real.logb 2 ((3 * n + 1) / (rho n * εg))⌉₊ * rho n * εg ∧
      (2 : ℝ) ^ ⌈Real.logb 2 ((3 * n + 1) / (rho n * εg))⌉₊ * rho n * εg < 2 * (3 * n + 1) ∧
      ((⌈Real.logb 2 ((3 * n + 1) / (rho n * εg))⌉₊ : ℕ) : ℝ) + 1 ≤
        478 + 3 * |Real.log (n / εg)| ∧
      Real.log (1 / (rho n * εg / (48 * Real.pi * (3 * n + 1)))) ≤
        479 + 2 * |Real.log (n / εg)| := by
  set r := ⌈Real.logb 2 (40 * Real.sqrt n)⌉₊ with hr
  set R : ℝ := (2 : ℝ) ^ r with hR
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt 2 ≤ Real.sqrt n := Real.sqrt_le_sqrt hn'
  have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hsn : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hR1 : 40 * Real.sqrt n ≤ R := two_pow_ceil_logb _ (by positivity)
  have hR2 : R < 2 * (40 * Real.sqrt n) := two_pow_ceil_logb_lt _ (by nlinarith)
  have hRpos : 0 < R := by positivity
  have hρ : rho n = 1 / R := by rw [rho, hR, inv_pow, one_div]
  have hR56 : 56 ≤ R := by nlinarith
  set X : ℝ := (3 * n + 1) / (rho n * εg) with hX
  have hXR : X = (3 * n + 1) * R / εg := by rw [hX, hρ]; field_simp
  have hX1 : 1 ≤ X := by
    rw [hXR, le_div_iff₀ hεg]; nlinarith
  set b := ⌈Real.logb 2 X⌉₊ with hb
  set N : ℝ := (2 : ℝ) ^ b with hN
  have hN1 : X ≤ N := two_pow_ceil_logb X (by linarith)
  have hN2 : N < 2 * X := two_pow_ceil_logb_lt X hX1
  refine ⟨r, ?_, hρ, ?_, ?_, ?_, ?_, ?_⟩
  · -- r ≤ b
    have h1 : R < (2 : ℝ) ^ (b + 1) := by
      rw [pow_succ, ← hN]
      have : R / 2 < X := by rw [hXR, lt_div_iff₀ hεg]; nlinarith
      linarith
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 (hR ▸ h1)
    omega
  · rw [hρ, mul_one_div, div_le_iff₀ hRpos]; linarith
  · have : (3 * n + 1 : ℝ) = X * (rho n * εg) := by
      rw [hX, div_mul_cancel₀ _ (show rho n * εg ≠ 0 by rw [hρ]; positivity)]
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_right hN1 (by rw [hρ]; positivity)
  · have : (3 * n + 1 : ℝ) = X * (rho n * εg) := by
      rw [hX, div_mul_cancel₀ _ (show rho n * εg ≠ 0 by rw [hρ]; positivity)]
    rw [this, mul_assoc]
    have hpos : 0 < rho n * εg := by rw [hρ]; positivity
    nlinarith
  · -- bound on b
    have hlogX : Real.log X ≤ 328 + 2 * Real.log (n / εg) := by
      have hXle : X ≤ 320 * n * (n / εg) := by
        rw [hXR, div_le_iff₀ hεg]
        have : (3 * n + 1 : ℝ) * R ≤ 320 * n * n := by nlinarith
        rw [mul_div_assoc', div_mul_cancel₀ _ hεg.ne']
        linarith
      have h1 := Real.log_le_log (by linarith) hXle
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity)] at h1
      have h320 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 320 by norm_num)
      have hlogn : Real.log n ≤ Real.log (n / εg) + 9 := by
        rw [Real.log_div (by positivity) hεg.ne']
        have := Real.log_le_log hεg hεg10
        have h10 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)
        linarith
      linarith
    have hb1 := ceil_logb_lt X hX1
    have hl2 := Real.log_two_gt_d9
    have hl2' : (0.69 : ℝ) < Real.log 2 := by linarith
    have hab := le_abs_self (Real.log (n / εg))
    have hab0 := abs_nonneg (Real.log (n / εg))
    have : Real.logb 2 X ≤ 476 + 3 * |Real.log (n / εg)| := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  · -- bound on log (1/η)
    have hpos : 0 < rho n * εg := by rw [hρ]; positivity
    have : 1 / (rho n * εg / (48 * Real.pi * (3 * n + 1))) = (48 * Real.pi) * X := by
      rw [hX]; field_simp
    rw [this, Real.log_mul (by positivity) (by linarith)]
    have h48 := Real.log_le_sub_one_of_pos (show 0 < 48 * Real.pi by positivity)
    have hpi := Real.pi_lt_d2
    have hlogX : Real.log X ≤ 328 + 2 * Real.log (n / εg) := by
      have hXle : X ≤ 320 * n * (n / εg) := by
        rw [hXR, div_le_iff₀ hεg]
        have : (3 * n + 1 : ℝ) * R ≤ 320 * n * n := by nlinarith
        rw [mul_div_assoc', div_mul_cancel₀ _ hεg.ne']
        linarith
      have h1 := Real.log_le_log (by linarith) hXle
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity)] at h1
      have h320 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 320 by norm_num)
      have hlogn : Real.log n ≤ Real.log (n / εg) + 9 := by
        rw [Real.log_div (by positivity) hεg.ne']
        have := Real.log_le_log hεg hεg10
        have h10 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)
        linarith
      linarith
    have hab := le_abs_self (Real.log (n / εg))
    nlinarith

/-- `n ≤ n L² + 50 log(1/ε)`. -/
lemma n_le (n : ℕ) (hn : 2 ≤ n) (ε εg : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hεg : 0 < εg)
    (hεg10 : εg ≤ 10) :
    (n : ℝ) ≤ n * Real.log (n / εg) ^ 2 + 50 * Real.log (1 / ε) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have hl2 := Real.log_two_gt_d9
  by_cases hL : 1 ≤ |Real.log (n / εg)|
  · have : 1 ≤ Real.log (n / εg) ^ 2 := by
      rw [← sq_abs]; nlinarith
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
  · push_neg at hL
    have h1 : Real.log (n / εg) < 1 := lt_of_le_of_lt (le_abs_self _) hL
    have h2 : (n : ℝ) / εg < Real.exp 1 := by
      rw [← Real.log_lt_iff_lt_exp (by positivity)]; exact h1
    have he := Real.exp_one_lt_d9
    have h3 : (n : ℝ) < 28 := by
      rw [div_lt_iff₀ hεg] at h2; nlinarith
    nlinarith [sq_nonneg (Real.log (n / εg))]

lemma cost_bound (n b Vb L lε lη C₁ : ℝ) (hn : 2 ≤ n) (hC₁ : 0 ≤ C₁) (hb0 : 0 ≤ b)
    (hb : b + 1 ≤ 478 + 3 * |L|) (hlη : lη ≤ 479 + 2 * |L|) (hlε : 0.69 ≤ lε)
    (hnL : n ≤ n * L ^ 2 + 50 * lε) (hVb : Vb ≤ C₁ * (lε + lη)) :
    Vb + 3 * n * (b + 1) ^ 2 ≤ (1000 * C₁ + 10 ^ 9) * (n * L ^ 2 + lε) ∧
      n * (b + 1) ^ 2 ≤ (1000 * C₁ + 10 ^ 9) * (n * L ^ 2 + lε + 1) := by
  have hA := abs_nonneg L
  have hA2 : |L| ^ 2 = L ^ 2 := sq_abs L
  have hAL : |L| ≤ 1 + L ^ 2 := by nlinarith [sq_nonneg (|L| - 1)]
  have hb1 : (b + 1) ^ 2 ≤ 456968 + 18 * L ^ 2 := by
    have : (b + 1) ^ 2 ≤ (478 + 3 * |L|) ^ 2 := pow_le_pow_left₀ (by linarith) hb 2
    nlinarith [sq_nonneg (478 - 3 * |L|)]
  have hnb : n * (b + 1) ^ 2 ≤ 456968 * n + 18 * (n * L ^ 2) := by
    have := mul_le_mul_of_nonneg_left hb1 (by linarith : (0 : ℝ) ≤ n)
    linarith
  have hnL2 : 0 ≤ n * L ^ 2 := by positivity
  have hQ : n * (b + 1) ^ 2 ≤ 23000000 * (n * L ^ 2 + lε) := by nlinarith
  have hV : Vb ≤ 700 * C₁ * (n * L ^ 2 + lε) := by
    have h1 : lε + lη ≤ 700 * (n * L ^ 2 + lε) := by
      have : L ^ 2 ≤ n * L ^ 2 := by nlinarith [sq_nonneg L]
      nlinarith
    have := mul_le_mul_of_nonneg_left h1 hC₁
    linarith
  constructor
  · nlinarith
  · nlinarith

end LTFB

end Mod_Params

section Mod_Main

open QAlgorithms

namespace LTFB

theorem main_thm (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε εg : ℝ, 0 < ε → ε ≤ 1 / 2 →
      0 < εg → εg ≤ 10 →
      let η : ℝ := QuantumLTF.Membership.rho n * εg / (48 * Real.pi * (3 * n + 1))
      let b : ℕ := ⌈Real.logb 2 ((3 * n + 1) / (QuantumLTF.Membership.rho n * εg))⌉₊
      ∀ Vb Vf W : ℕ, (Vb : ℝ) ≤ C₁ * (Real.log (1 / ε) + Real.log (1 / η)) →
        ∃ (m ℓo fo : ℕ) (c : OracleCircuit QuantumLTF.Membership.gates12
            (fun _ : Fin 1 => n * b + Vb + W) m)
          (oa : Fin n → (Fin ℓo ↪ Fin m)),
          QuantumLTF.Membership.Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C ∧
          (c.gateCount : ℝ) ≤ C * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε)) ∧
          (n * ℓo : ℝ) ≤ C * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε) + 1) ∧
          ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 →
            ∀ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) -
                QuantumLTF.Membership.height w θ p
                  (QuantumLTF.Membership.rho n • QuantumLTF.Membership.gridVec n b x)| ≤ η) →
            ∀ OH : Matrix (Qubits (n * b + Vb + W)) (Qubits (n * b + Vb + W)) ℂ,
              OH ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ →
              (∀ x, act OH (ket (QuantumLTF.Membership.regBasis n b Vb W x fun _ => false)) =
                ket (QuantumLTF.Membership.regBasis n b Vb W x (Htil x))) →
              open Classical in
              probEvent (act (c.unitary fun _ => OH) (zeroKet m))
                (fun z => ∀ i, |QuantumLTF.Membership.readFp (oa i) fo z -
                  (-(w i) / inner ℝ w p)| ≤ εg) ≥ 3 / 4 := by
  refine ⟨1000 * C₁ + 10 ^ 9, by positivity, ?_⟩
  intro n hn ε εg hε hε2 hεg hεg10 η b Vb Vf W hVb
  obtain ⟨r, hrb, hρ, hρ5, hT1, hT2, hbL, hlη⟩ := params n hn εg hεg hεg10
  have hcounts := circ_counts (n := n) (b := b) (Vb := Vb) (W := W) (cvf b Vb Vf)
  have hcost := cost_bound n b Vb (Real.log (n / εg)) (Real.log (1 / ε)) (Real.log (1 / η)) C₁
    (by exact_mod_cast hn) hC₁ (Nat.cast_nonneg _) hbL hlη
    (by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (show (2 : ℝ) ≤ 1 / ε by rw [le_div_iff₀ hε]; linarith)
      have := Real.log_two_gt_d9
      linarith)
    (n_le n hn ε εg hε hε2 hεg hεg10) hVb
  refine ⟨n * b + Vb + W, b, b - r, circ n b Vb W (cvf b Vb Vf), oaE n b Vb W,
    circ_uncontrolled _, ?_, ?_, ?_, ?_⟩
  · rw [hcounts.2]; norm_num
    nlinarith
  · rw [hcounts.1]
    push_cast
    have : ((n : ℝ) * b + Vb + n * (b + b * (b + 1))) ≤ Vb + 3 * n * (b + 1) ^ 2 := by
      have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
      nlinarith [mul_nonneg h0 (sq_nonneg (b : ℝ)), mul_nonneg h0 h1]
    linarith [hcost.1]
  · have : (n : ℝ) * b ≤ n * (b + 1) ^ 2 := by
      have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
      nlinarith [mul_nonneg h0 (sq_nonneg (b : ℝ)), mul_nonneg h0 h1]
    linarith [hcost.2]
  · intro w p θ hw hwp1 _ Htil hH OH hOH hspec
    exact prob_core n b Vb Vf W r (by omega) hrb hρ hρ5 εg hεg hεg10 hT1 hT2 w p θ hw hwp1
      Htil hH OH hOH hspec

end LTFB

end Mod_Main

open QAlgorithms QuantumLTF.Membership

theorem solution (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε εg : ℝ, 0 < ε → ε ≤ 1 / 2 →
      0 < εg → εg ≤ 10 →
      let η : ℝ := rho n * εg / (48 * Real.pi * (3 * n + 1))
      let b : ℕ := ⌈Real.logb 2 ((3 * n + 1) / (rho n * εg))⌉₊
      ∀ Vb Vf W : ℕ, (Vb : ℝ) ≤ C₁ * (Real.log (1 / ε) + Real.log (1 / η)) →
        ∃ (m ℓo fo : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n * b + Vb + W) m)
          (oa : Fin n → (Fin ℓo ↪ Fin m)),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C ∧
          (c.gateCount : ℝ) ≤ C * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε)) ∧
          (n * ℓo : ℝ) ≤ C * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε) + 1) ∧
          ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 →
            ∀ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, |fpVal Vb Vf (Htil x) - height w θ p (rho n • gridVec n b x)| ≤ η) →
            ∀ OH : Matrix (Qubits (n * b + Vb + W)) (Qubits (n * b + Vb + W)) ℂ,
              OH ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ →
              (∀ x, act OH (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) →
              open Classical in
              probEvent (act (c.unitary fun _ => OH) (zeroKet m))
                (fun z => ∀ i, |readFp (oa i) fo z - (-(w i) / inner ℝ w p)| ≤ εg) ≥ 3 / 4 := by
  exact LTFB.main_thm C₁ hC₁

