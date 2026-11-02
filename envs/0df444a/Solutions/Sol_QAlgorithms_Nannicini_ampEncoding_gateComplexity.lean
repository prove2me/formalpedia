-- Prove2me | solution 1 for QAlgorithms.Nannicini.ampEncoding_gateComplexity
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:03:19.682628+00:00
-- url     : https://prove2.me/submissions/30f79c87-47c3-48d2-b7f3-cb63beffca50

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05c_Model
set_option autoImplicit false

open scoped ComplexConjugate
open QAlgorithms
open QAlgorithms.Nannicini

noncomputable section

namespace AmpEncodingGateComplexityProof

/-! ### Section 1: Basic `act`, `ket`, and `embed1`/`embed2` Lemmas -/

@[simp] lemma toLp_ofLp_apply {ι : Type*} (f : ι → ℂ) (i : ι) :
    (WithLp.toLp 2 f).ofLp i = f i := rfl

@[simp] lemma add_ofLp_apply {ι : Type*} (ψ φ : EuclideanSpace ℂ ι) (i : ι) :
    (ψ + φ).ofLp i = ψ.ofLp i + φ.ofLp i := rfl

@[simp] lemma sub_ofLp_apply {ι : Type*} (ψ φ : EuclideanSpace ℂ ι) (i : ι) :
    (ψ - φ).ofLp i = ψ.ofLp i - φ.ofLp i := rfl

@[simp] lemma smul_ofLp_apply {ι : Type*} (c : ℂ) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    (c • ψ).ofLp i = c * ψ.ofLp i := rfl

@[simp] lemma zero_ofLp_apply {ι : Type*} (i : ι) :
    (0 : EuclideanSpace ℂ ι).ofLp i = 0 := rfl

@[simp] lemma sum_ofLp_apply {ι α : Type*} (s : Finset α) (f : α → EuclideanSpace ℂ ι) (i : ι) :
    (∑ x ∈ s, f x).ofLp i = ∑ x ∈ s, (f x).ofLp i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma act_apply {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    (act A ψ).ofLp i = (A.mulVec (WithLp.ofLp ψ)) i := rfl

lemma act_zero {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    act A 0 = 0 := by
  ext i; simp [act]

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  ext i; simp [act]

lemma act_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext i; simp [act, Matrix.mulVec_mulVec]

lemma act_add {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act A (ψ + φ) = act A ψ + act A φ := by
  ext i; simp [act, Matrix.mulVec_add]

lemma act_sub {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act A (ψ - φ) = act A ψ - act A φ := by
  ext i; simp [act, Matrix.mulVec_sub]

lemma act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act A (c • ψ) = c • act A ψ := by
  ext i; simp [act, Matrix.mulVec_smul]

lemma act_sum {ι α : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (s : Finset α)
    (f : α → EuclideanSpace ℂ ι) :
    act A (∑ x ∈ s, f x) = ∑ x ∈ s, act A (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i; simp [act]
  | @insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

@[simp] lemma ket_apply {ι : Type*} [DecidableEq ι] (i j : ι) :
    (ket i : EuclideanSpace ℂ ι).ofLp j = if j = i then 1 else 0 := by
  simp [ket]

lemma act_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (j : ι) :
    act A (ket j) = WithLp.toLp 2 (fun i => A i j) := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, ket_apply]

lemma decomp_euclidean {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    ψ = ∑ z : ι, ψ.ofLp z • ket z := by
  ext y
  simp [ket_apply]

lemma matrix_eq_of_act_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M1 M2 : Matrix ι ι ℂ} (h : ∀ z : ι, act M1 (ket z) = act M2 (ket z)) :
    M1 = M2 := by
  ext y z
  have hz := congrArg (fun ψ => ψ.ofLp y) (h z)
  simpa [act_ket] using hz

lemma act_star_ofLp_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (Ψ : EuclideanSpace ℂ ι) (z0 : ι) :
    (act (star U) Ψ).ofLp z0 =
      ∑ z : ι, star ((act U (ket z0)).ofLp z) * Ψ.ofLp z := by
  simp [act_ket, act_apply, Matrix.mulVec, dotProduct, Matrix.star_apply]

lemma qubits_zero_def (m : ℕ) : (0 : Qubits m) = fun _ => false := rfl

def singleEmb {N : ℕ} (w : Fin N) : Fin 1 ↪ Fin N where
  toFun _ := w
  inj' i j _ := Subsingleton.elim i j

@[simp] lemma singleEmb_zero {N : ℕ} (w : Fin N) : singleEmb w 0 = w := rfl

lemma range_singleEmb {N : ℕ} (w : Fin N) (a : Fin N) :
    a ∈ Set.range (singleEmb w) ↔ a = w := by
  constructor
  · rintro ⟨i, rfl⟩; rfl
  · rintro rfl; exact ⟨0, rfl⟩

def pairEmb {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) : Fin 2 ↪ Fin N where
  toFun := ![w0, w1]
  inj' i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact False.elim (h01 hij)
    · exact False.elim (h01 hij.symm)

@[simp] lemma pairEmb_zero {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    pairEmb w0 w1 h01 0 = w0 := rfl

@[simp] lemma pairEmb_one {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    pairEmb w0 w1 h01 1 = w1 := rfl

lemma range_pairEmb {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) (a : Fin N) :
    a ∈ Set.range (pairEmb w0 w1 h01) ↔ a = w0 ∨ a = w1 := by
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

lemma update_single_eq_iff {N : ℕ} (w : Fin N) (y z : Qubits N) (b : Bool) :
    y = Function.update z w b ↔
      (∀ a, a ∉ Set.range (singleEmb w) → y a = z a) ∧ b = y w := by
  constructor
  · intro hy
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [range_singleEmb] at ha
      rw [hy, Function.update_of_ne ha]
    · rw [hy, Function.update_self]
  · rintro ⟨hoff, rfl⟩
    funext a
    by_cases ha : a = w
    · subst ha; simp
    · rw [Function.update_of_ne ha]
      apply hoff
      rw [range_singleEmb]
      exact ha

lemma update_pair_eq_iff {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) (y z : Qubits N)
    (p : Bool × Bool) :
    y = Function.update (Function.update z w0 p.1) w1 p.2 ↔
      (∀ a, a ∉ Set.range (pairEmb w0 w1 h01) → y a = z a) ∧ p = (y w0, y w1) := by
  constructor
  · intro hy
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [range_pairEmb, not_or] at ha
      rw [hy, Function.update_of_ne ha.2, Function.update_of_ne ha.1]
    · have hw0 : y w0 = p.1 := by
        rw [hy, Function.update_of_ne h01, Function.update_self]
      have hw1 : y w1 = p.2 := by
        rw [hy, Function.update_self]
      ext <;> simp [hw0, hw1]
  · rintro ⟨hoff, rfl⟩
    funext a
    by_cases ha1 : a = w1
    · subst ha1; simp
    · rw [Function.update_of_ne ha1]
      by_cases ha0 : a = w0
      · subst ha0; simp
      · rw [Function.update_of_ne ha0]
        apply hoff
        rw [range_pairEmb, not_or]
        exact ⟨ha0, ha1⟩

abbrev embed1 {N : ℕ} (M : Matrix Bool Bool ℂ) (w : Fin N) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  embedOp (M.submatrix (fun b : Qubits 1 => b 0) (fun b => b 0)) (singleEmb w)

abbrev embed2 {N : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  embedOp (M.submatrix (fun b : Qubits 2 => (b 0, b 1)) (fun b => (b 0, b 1))) (pairEmb w0 w1 h01)

lemma act_embed1_ket {N : ℕ} (M : Matrix Bool Bool ℂ)
    (w : Fin N) (z : Qubits N) :
    act (embed1 M w) (ket z) =
      ∑ b : Bool, M b (z w) • ket (Function.update z w b) := by
  ext y
  rw [act_ket]
  dsimp [embed1, embedOp]
  simp only [sum_ofLp_apply, smul_ofLp_apply, ket_apply]
  by_cases hoff : ∀ a, a ∉ Set.range (singleEmb w) → y a = z a
  · rw [if_pos hoff]
    rw [Finset.sum_eq_single (y w)]
    · have hy : y = Function.update z w (y w) :=
        (update_single_eq_iff w y z (y w)).mpr ⟨hoff, rfl⟩
      rw [if_pos hy, mul_one]
    · intro b _ hb
      have hne : y ≠ Function.update z w b := by
        intro hy
        exact hb ((update_single_eq_iff w y z b).mp hy).2
      rw [if_neg hne, mul_zero]
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
  · rw [if_neg hoff]
    symm
    refine Finset.sum_eq_zero (fun b _ => ?_)
    have hne : y ≠ Function.update z w b := by
      intro hy
      exact hoff ((update_single_eq_iff w y z b).mp hy).1
    rw [if_neg hne, mul_zero]

lemma act_embed2_ket {N : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (w0 w1 : Fin N) (h01 : w0 ≠ w1) (z : Qubits N) :
    act (embed2 M w0 w1 h01) (ket z) =
      ∑ p : Bool × Bool, M p (z w0, z w1) •
        ket (Function.update (Function.update z w0 p.1) w1 p.2) := by
  ext y
  rw [act_ket]
  dsimp [embed2, embedOp]
  simp only [sum_ofLp_apply, smul_ofLp_apply, ket_apply]
  by_cases hoff : ∀ a, a ∉ Set.range (pairEmb w0 w1 h01) → y a = z a
  · rw [if_pos hoff]
    rw [Finset.sum_eq_single (y w0, y w1)]
    · have hy : y = Function.update (Function.update z w0 (y w0)) w1 (y w1) :=
        (update_pair_eq_iff w0 w1 h01 y z (y w0, y w1)).mpr ⟨hoff, rfl⟩
      rw [if_pos hy, mul_one]
    · intro p _ hp
      have hne : y ≠ Function.update (Function.update z w0 p.1) w1 p.2 := by
        intro hy
        exact hp ((update_pair_eq_iff w0 w1 h01 y z p).mp hy).2
      rw [if_neg hne, mul_zero]
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
  · rw [if_neg hoff]
    symm
    refine Finset.sum_eq_zero (fun p _ => ?_)
    have hne : y ≠ Function.update (Function.update z w0 p.1) w1 p.2 := by
      intro hy
      exact hoff ((update_pair_eq_iff w0 w1 h01 y z p).mp hy).1
    rw [if_neg hne, mul_zero]

lemma embed1_one {N : ℕ} (w : Fin N) :
    embed1 (1 : Matrix Bool Bool ℂ) w = 1 := by
  apply matrix_eq_of_act_ket
  intro z
  rw [act_embed1_ket, act_one]
  cases hzw : z w <;> {
    have hupd : Function.update z w (z w) = z := Function.update_eq_self w z
    rw [hzw] at hupd
    simp [hupd]
  }

lemma embed1_mul {N : ℕ} (A B : Matrix Bool Bool ℂ) (w : Fin N) :
    embed1 A w * embed1 B w = embed1 (A * B) w := by
  apply matrix_eq_of_act_ket
  intro z
  rw [act_mul, act_embed1_ket, act_embed1_ket, act_sum]
  simp_rw [act_smul, act_embed1_ket, Function.update_self, Function.update_idem]
  ext y
  simp only [Matrix.mul_apply, Fintype.sum_bool, add_ofLp_apply, smul_ofLp_apply]
  ring

lemma embed2_one {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    embed2 (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) w0 w1 h01 = 1 := by
  apply matrix_eq_of_act_ket
  intro z
  rw [act_embed2_ket, act_one, Fintype.sum_prod_type]
  have hupd : Function.update (Function.update z w0 (z w0)) w1 (z w1) = z := by
    rw [Function.update_eq_self, Function.update_eq_self]
  cases h0 : z w0 <;> cases h1 : z w1 <;> {
    rw [h0, h1] at hupd
    simp [Matrix.one_apply, hupd]
  }

lemma embed2_mul {N : ℕ} (A B : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    embed2 A w0 w1 h01 * embed2 B w0 w1 h01 = embed2 (A * B) w0 w1 h01 := by
  apply matrix_eq_of_act_ket
  intro z
  rw [act_mul, act_embed2_ket, act_embed2_ket, act_sum]
  have hupd_eq : ∀ p q : Bool × Bool,
      Function.update (Function.update (Function.update (Function.update z w0 q.1) w1 q.2) w0 p.1) w1 p.2 =
        Function.update (Function.update z w0 p.1) w1 p.2 := by
    intro p q
    funext a
    by_cases ha1 : a = w1
    · subst ha1; simp
    · by_cases ha0 : a = w0
      · subst ha0; simp [Function.update_of_ne ha1]
      · simp [Function.update_of_ne ha1, Function.update_of_ne ha0]
  have hw0 : ∀ q : Bool × Bool, (Function.update (Function.update z w0 q.1) w1 q.2) w0 = q.1 := by
    intro q; rw [Function.update_of_ne h01, Function.update_self]
  have hw1 : ∀ q : Bool × Bool, (Function.update (Function.update z w0 q.1) w1 q.2) w1 = q.2 := by
    intro q; rw [Function.update_self]
  simp_rw [act_smul, act_embed2_ket, hw0, hw1, hupd_eq]
  ext y
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    add_ofLp_apply, smul_ofLp_apply]
  ring

lemma star_embedOp {k N : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (wires : Fin k ↪ Fin N) :
    star (embedOp M wires) = embedOp (star M) wires := by
  ext y z
  simp only [embedOp, Matrix.star_apply, Matrix.of_apply]
  by_cases h : ∀ a : Fin N, a ∉ Set.range wires → y a = z a
  · have hsymm : ∀ a : Fin N, a ∉ Set.range wires → z a = y a :=
      fun a ha => (h a ha).symm
    rw [if_pos h, if_pos hsymm]
  · have hsymm : ¬ ∀ a : Fin N, a ∉ Set.range wires → z a = y a := by
      intro hs; exact h (fun a ha => (hs a ha).symm)
    rw [if_neg h, if_neg hsymm, star_zero]

lemma star_embed1 {N : ℕ} (M : Matrix Bool Bool ℂ) (w : Fin N) :
    star (embed1 M w) = embed1 (star M) w := by
  unfold embed1
  rw [star_embedOp]
  rfl

lemma star_embed2 {N : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    star (embed2 M w0 w1 h01) = embed2 (star M) w0 w1 h01 := by
  unfold embed2
  rw [star_embedOp]
  rfl

def blockDiag2 (U0 U1 : Matrix Bool Bool ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (if p.1 then U1 p.2 q.2 else U0 p.2 q.2) else 0

lemma blockDiag2_one : blockDiag2 1 1 = (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp [blockDiag2, Matrix.one_apply]

lemma blockDiag2_mul (A0 A1 B0 B1 : Matrix Bool Bool ℂ) :
    blockDiag2 A0 A1 * blockDiag2 B0 B1 = blockDiag2 (A0 * B0) (A1 * B1) := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  dsimp [blockDiag2]
  simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a1 <;> cases b1 <;> simp

lemma controlled_eq_blockDiag2 (U : Matrix Bool Bool ℂ) :
    controlled U = blockDiag2 1 U := rfl

lemma cnot_eq_blockDiag2 : cnot = blockDiag2 1 pauliX := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
    simp [cnot, blockDiag2, pauliX, Matrix.one_apply]

lemma embed1_eq_embed2_blockDiag2 {N : ℕ} (U : Matrix Bool Bool ℂ)
    (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    embed1 U w1 = embed2 (blockDiag2 U U) w0 w1 h01 := by
  apply matrix_eq_of_act_ket
  intro z
  rw [act_embed1_ket, act_embed2_ket, Fintype.sum_prod_type]
  have hupd : ∀ b1 : Bool,
      Function.update (Function.update z w0 (z w0)) w1 b1 = Function.update z w1 b1 := by
    intro b1
    rw [Function.update_eq_self]
  cases hzw0 : z w0 <;> {
    rw [hzw0] at hupd
    simp [blockDiag2, hupd]
  }

def cnotRev : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 ∧ p.1 = xor q.1 q.2 then 1 else 0

lemma embed2_cnot_swap {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    embed2 cnot w1 w0 h01.symm = embed2 cnotRev w0 w1 h01 := by
  apply matrix_eq_of_act_ket
  intro z
  rw [act_embed2_ket, act_embed2_ket, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hcomm : ∀ b0 b1 : Bool,
      Function.update (Function.update z w1 b1) w0 b0 =
        Function.update (Function.update z w0 b0) w1 b1 := by
    intro b0 b1
    exact Function.update_comm h01.symm b1 b0 z
  simp_rw [hcomm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b0 _ => Finset.sum_congr rfl (fun b1 _ => ?_))
  simp [cnot, cnotRev]

/-! ### Section 2: Elementary Gates and Composite Gates in `htcxGateSet` -/

def hGate {N : ℕ} (w : Fin N) : GateApp htcxGateSet N :=
  ⟨Gate.ofMatrix1 hadamard, Or.inl rfl, singleEmb w⟩

def tGate {N : ℕ} (w : Fin N) : GateApp htcxGateSet N :=
  ⟨Gate.ofMatrix1 gateT, Or.inr (Or.inl rfl), singleEmb w⟩

def cxGate {N : ℕ} (w_c w_t : Fin N) (h : w_c ≠ w_t) : GateApp htcxGateSet N :=
  ⟨Gate.ofMatrix2 cnot, Or.inr (Or.inr rfl), pairEmb w_c w_t h⟩

@[simp] lemma circuit_unitary_nil {S : Set Gate} {N : ℕ} :
    Circuit.unitary ([] : Circuit S N) = 1 := rfl

@[simp] lemma circuit_unitary_singleton {S : Set Gate} {N : ℕ} (g : GateApp S N) :
    Circuit.unitary ([g] : Circuit S N) = embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

lemma circuit_unitary_cons {S : Set Gate} {N : ℕ} (g : GateApp S N) (c : Circuit S N) :
    Circuit.unitary (g :: c) = c.unitary * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

lemma circuit_unitary_append {S : Set Gate} {N : ℕ} (c1 c2 : Circuit S N) :
    Circuit.unitary (c1 ++ c2) = c2.unitary * c1.unitary := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma act_circuit_unitary_append {S : Set Gate} {N : ℕ} (c1 c2 : Circuit S N)
    (ψ : EuclideanSpace ℂ (Qubits N)) :
    act (c1 ++ c2).unitary ψ = act c2.unitary (act c1.unitary ψ) := by
  rw [circuit_unitary_append, act_mul]

lemma circuit_size_append {S : Set Gate} {N : ℕ} (c1 c2 : Circuit S N) :
    (c1 ++ c2).size = c1.size + c2.size :=
  List.length_append

@[simp] lemma hGate_embedOp {N : ℕ} (w : Fin N) :
    embedOp (hGate w).gate.mat (hGate w).wires = embed1 hadamard w := rfl

@[simp] lemma tGate_embedOp {N : ℕ} (w : Fin N) :
    embedOp (tGate w).gate.mat (tGate w).wires = embed1 gateT w := rfl

@[simp] lemma cxGate_embedOp {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    embedOp (cxGate w0 w1 h01).gate.mat (cxGate w0 w1 h01).wires = embed2 cnot w0 w1 h01 := rfl

lemma sqrt2_inv_sq : ((Real.sqrt 2)⁻¹ : ℂ) ^ 2 = (2⁻¹ : ℂ) := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma sqrt2_div_two_eq_inv : (Real.sqrt 2 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  rw [div_eq_iff (by norm_num)]
  calc Real.sqrt 2 = ((Real.sqrt 2)⁻¹ * Real.sqrt 2) * Real.sqrt 2 := by
        rw [inv_mul_cancel₀ hne, one_mul]
    _ = (Real.sqrt 2)⁻¹ * (Real.sqrt 2 * Real.sqrt 2) := by ring
    _ = (Real.sqrt 2)⁻¹ * 2 := by rw [h]

lemma exp_I_pi_div_four :
    Complex.exp (Complex.I * Real.pi / 4) =
      ((Real.sqrt 2)⁻¹ : ℂ) * (1 + Complex.I) := by
  have h1 : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four, sqrt2_div_two_eq_inv, Complex.ofReal_inv]
  ring

def phaseSdag : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then -Complex.I else 1

noncomputable def gateTdag : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then ((Real.sqrt 2)⁻¹ : ℂ) * (1 - Complex.I) else 1

lemma gateT_eq_diag :
    gateT = Matrix.diagonal fun a => if a then ((Real.sqrt 2)⁻¹ : ℂ) * (1 + Complex.I) else 1 := by
  ext a b
  dsimp [gateT]
  rw [exp_I_pi_div_four]

lemma gateT_mul_gateT : gateT * gateT = phaseS := by
  rw [gateT_eq_diag]
  ext a b
  cases a <;> cases b <;> simp [phaseS]
  calc ((Real.sqrt 2)⁻¹ : ℂ) * (1 + Complex.I) * (((Real.sqrt 2)⁻¹ : ℂ) * (1 + Complex.I))
      = (((Real.sqrt 2)⁻¹ : ℂ) ^ 2) * (1 + 2 * Complex.I + Complex.I ^ 2) := by ring
    _ = Complex.I := by rw [sqrt2_inv_sq, Complex.I_sq]; ring

lemma phaseS_mul_phaseS : phaseS * phaseS = pauliZ := by
  ext a b
  cases a <;> cases b <;> simp [phaseS, pauliZ]

lemma pauliZ_mul_phaseS : pauliZ * phaseS = phaseSdag := by
  ext a b
  cases a <;> cases b <;> simp [pauliZ, phaseS, phaseSdag]

lemma phaseSdag_mul_gateT : phaseSdag * gateT = gateTdag := by
  rw [gateT_eq_diag]
  ext a b
  cases a <;> cases b <;> simp [phaseSdag, gateTdag]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma phaseSdag_mul_phaseS : phaseSdag * phaseS = 1 := by
  ext a b
  cases a <;> cases b <;> simp [phaseSdag, phaseS]

lemma phaseS_mul_phaseSdag : phaseS * phaseSdag = 1 := by
  ext a b
  cases a <;> cases b <;> simp [phaseS, phaseSdag]

lemma gateTdag_mul_gateT : gateTdag * gateT = 1 := by
  rw [gateT_eq_diag]
  ext a b
  cases a <;> cases b <;> simp [gateTdag]
  calc ((Real.sqrt 2)⁻¹ : ℂ) * (1 - Complex.I) * (((Real.sqrt 2)⁻¹ : ℂ) * (1 + Complex.I))
      = (((Real.sqrt 2)⁻¹ : ℂ) ^ 2) * (1 - Complex.I ^ 2) := by ring
    _ = 1 := by rw [sqrt2_inv_sq, Complex.I_sq]; ring

lemma gateT_mul_gateTdag : gateT * gateTdag = 1 := by
  rw [gateT_eq_diag]
  ext a b
  cases a <;> cases b <;> simp [gateTdag]
  calc ((Real.sqrt 2)⁻¹ : ℂ) * (1 + Complex.I) * (((Real.sqrt 2)⁻¹ : ℂ) * (1 - Complex.I))
      = (((Real.sqrt 2)⁻¹ : ℂ) ^ 2) * (1 - Complex.I ^ 2) := by ring
    _ = 1 := by rw [sqrt2_inv_sq, Complex.I_sq]; ring

lemma hadamard_pauliZ_hadamard : hadamard * (pauliZ * hadamard) = pauliX := by
  ext a b
  cases a <;> cases b <;>
    simp [hadamard, pauliZ, pauliX, Matrix.mul_apply] <;>
    linear_combination 2 * sqrt2_inv_sq

lemma hadamard_pauliX_hadamard : hadamard * (pauliX * hadamard) = pauliZ := by
  ext a b
  cases a <;> cases b <;>
    simp [hadamard, pauliZ, pauliX, Matrix.mul_apply]
  · linear_combination 2 * sqrt2_inv_sq
  · linear_combination -2 * sqrt2_inv_sq

noncomputable def matB : Matrix Bool Bool ℂ :=
  phaseS * (hadamard * (gateT * (hadamard * phaseSdag)))

noncomputable def matBdag : Matrix Bool Bool ℂ :=
  phaseS * (hadamard * (gateTdag * (hadamard * phaseSdag)))

lemma matBdag_mul_matB : matBdag * matB = 1 := by
  unfold matBdag matB
  calc phaseS * (hadamard * (gateTdag * (hadamard * phaseSdag))) *
        (phaseS * (hadamard * (gateT * (hadamard * phaseSdag))))
      = phaseS * (hadamard * (gateTdag * (hadamard * ((phaseSdag * phaseS) *
          (hadamard * (gateT * (hadamard * phaseSdag))))))) := by simp only [Matrix.mul_assoc]
    _ = phaseS * (hadamard * (gateTdag * ((hadamard * hadamard) *
          (gateT * (hadamard * phaseSdag))))) := by
        rw [phaseSdag_mul_phaseS, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
    _ = phaseS * (hadamard * ((gateTdag * gateT) * (hadamard * phaseSdag))) := by
        rw [hadamard_mul_self, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
    _ = phaseS * ((hadamard * hadamard) * phaseSdag) := by
        rw [gateTdag_mul_gateT, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hadamard_mul_self, Matrix.one_mul, phaseS_mul_phaseSdag]

lemma matBdag_pauliX_matB : matBdag * (pauliX * matB) = hadamard := by
  unfold matBdag matB
  have h1 : hadamard * (phaseSdag * (pauliX * (phaseS * hadamard))) =
      Matrix.of (fun a b : Bool => if a = b then 0 else if a then Complex.I else -Complex.I) := by
    ext a b
    cases a <;> cases b <;>
      simp [hadamard, phaseS, phaseSdag, pauliX, Matrix.mul_apply] <;> {
      ring_nf
      rw [sqrt2_inv_sq]
      ring
    }
  have h2 : gateTdag *
        (Matrix.of (fun a b : Bool => if a = b then 0 else if a then Complex.I else -Complex.I) *
        gateT) =
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliX +
        Matrix.of (fun a b : Bool => if a = b then 0 else if a then Complex.I else -Complex.I)) := by
    rw [gateT_eq_diag]
    ext a b
    cases a <;> cases b <;>
      simp [gateTdag, pauliX, Matrix.mul_apply] <;> {
      ring_nf
      rw [Complex.I_sq]
      ring
    }
  have h3 : hadamard *
        ((((Real.sqrt 2)⁻¹ : ℂ) • (pauliX +
          Matrix.of (fun a b : Bool => if a = b then 0 else if a then Complex.I else -Complex.I))) *
        hadamard) =
      ((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ +
        Matrix.of (fun a b : Bool => if a = b then 0 else if a then -Complex.I else Complex.I)) := by
    ext a b
    cases a <;> cases b <;>
      simp [hadamard, pauliX, pauliZ, Matrix.mul_apply]
    · linear_combination (2 * ((Real.sqrt 2)⁻¹ : ℂ)) * sqrt2_inv_sq
    · linear_combination (2 * Complex.I * ((Real.sqrt 2)⁻¹ : ℂ)) * sqrt2_inv_sq
    · linear_combination (-2 * Complex.I * ((Real.sqrt 2)⁻¹ : ℂ)) * sqrt2_inv_sq
    · linear_combination (-2 * ((Real.sqrt 2)⁻¹ : ℂ)) * sqrt2_inv_sq
  have h4 : phaseS *
        ((((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ +
          Matrix.of (fun a b : Bool => if a = b then 0 else if a then -Complex.I else Complex.I))) *
        phaseSdag) = hadamard := by
    ext a b
    cases a <;> cases b <;>
      simp [phaseS, phaseSdag, pauliZ, hadamard, Matrix.mul_apply] <;> {
      ring_nf
      rw [Complex.I_sq]
      ring
    }
  calc phaseS * (hadamard * (gateTdag * (hadamard * phaseSdag))) *
        (pauliX * (phaseS * (hadamard * (gateT * (hadamard * phaseSdag)))))
      = phaseS * (hadamard * ((gateTdag *
          ((hadamard * (phaseSdag * (pauliX * (phaseS * hadamard)))) *
          gateT)) * hadamard) * phaseSdag) := by simp only [Matrix.mul_assoc]
    _ = phaseS * (hadamard * ((gateTdag *
          (Matrix.of (fun a b : Bool => if a = b then 0 else if a then Complex.I else -Complex.I) *
          gateT)) * hadamard) * phaseSdag) := by rw [h1]
    _ = phaseS * ((hadamard *
          ((((Real.sqrt 2)⁻¹ : ℂ) • (pauliX +
            Matrix.of (fun a b : Bool => if a = b then 0 else if a then Complex.I else -Complex.I))) *
          hadamard)) * phaseSdag) := by rw [h2]
    _ = phaseS *
          ((((Real.sqrt 2)⁻¹ : ℂ) • (pauliZ +
            Matrix.of (fun a b : Bool => if a = b then 0 else if a then -Complex.I else Complex.I))) *
          phaseSdag) := by rw [h3]
    _ = hadamard := h4

lemma blockDiag2_BMul_cnot :
    blockDiag2 matBdag matBdag * (cnot * blockDiag2 matB matB) = controlled hadamard := by
  rw [cnot_eq_blockDiag2, blockDiag2_mul, blockDiag2_mul, Matrix.one_mul,
    matBdag_mul_matB, matBdag_pauliX_matB, controlled_eq_blockDiag2]

lemma blockDiag2_hadamard_cnot :
    blockDiag2 hadamard hadamard * (cnot * blockDiag2 hadamard hadamard) = controlled pauliZ := by
  rw [cnot_eq_blockDiag2, blockDiag2_mul, blockDiag2_mul, Matrix.one_mul,
    hadamard_mul_self, hadamard_pauliX_hadamard, controlled_eq_blockDiag2]

noncomputable def ohsMat : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  cnotRev * (controlled hadamard * cnotRev)

lemma ohsMat_apply (p q : Bool × Bool) :
    ohsMat p q = match p, q with
      | (false, false), (false, false) => 1
      | (false, true),  (false, true)  => -((Real.sqrt 2)⁻¹ : ℂ)
      | (false, true),  (true, false)  => ((Real.sqrt 2)⁻¹ : ℂ)
      | (true, false),  (false, true)  => ((Real.sqrt 2)⁻¹ : ℂ)
      | (true, false),  (true, false)  => ((Real.sqrt 2)⁻¹ : ℂ)
      | (true, true),   (true, true)   => 1
      | _, _ => 0 := by
  rcases p with ⟨a1, a2⟩
  rcases q with ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
    simp [ohsMat, cnotRev, controlled, hadamard, Matrix.mul_apply, Fintype.sum_prod_type]

lemma star_ohsMat : star ohsMat = ohsMat := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [Matrix.star_apply]
  rw [ohsMat_apply, ohsMat_apply]
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
    simp [Complex.conj_ofReal]

lemma cnotRev_mul_self : cnotRev * cnotRev = 1 := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
    simp [cnotRev, Matrix.mul_apply, Fintype.sum_prod_type]

lemma controlled_hadamard_mul_self : controlled hadamard * controlled hadamard = 1 := by
  rw [controlled_eq_blockDiag2, blockDiag2_mul, Matrix.mul_one, hadamard_mul_self, blockDiag2_one]

lemma ohsMat_mul_self : ohsMat * ohsMat = 1 := by
  unfold ohsMat
  calc cnotRev * (controlled hadamard * cnotRev) * (cnotRev * (controlled hadamard * cnotRev))
      = cnotRev * (controlled hadamard * ((cnotRev * cnotRev) * (controlled hadamard * cnotRev))) := by
        simp only [Matrix.mul_assoc]
    _ = cnotRev * ((controlled hadamard * controlled hadamard) * cnotRev) := by
        rw [cnotRev_mul_self, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [controlled_hadamard_mul_self, Matrix.one_mul, cnotRev_mul_self]

def gateS {N : ℕ} (w : Fin N) : Circuit htcxGateSet N :=
  [tGate w, tGate w]

def gateZ {N : ℕ} (w : Fin N) : Circuit htcxGateSet N :=
  gateS w ++ gateS w

def gateSdag {N : ℕ} (w : Fin N) : Circuit htcxGateSet N :=
  gateS w ++ gateZ w

def gateTdagCirc {N : ℕ} (w : Fin N) : Circuit htcxGateSet N :=
  [tGate w] ++ gateSdag w

def gateX {N : ℕ} (w : Fin N) : Circuit htcxGateSet N :=
  [hGate w] ++ gateZ w ++ [hGate w]

def gateB {N : ℕ} (w : Fin N) : Circuit htcxGateSet N :=
  gateSdag w ++ [hGate w, tGate w, hGate w] ++ gateS w

def gateBdag {N : ℕ} (w : Fin N) : Circuit htcxGateSet N :=
  gateSdag w ++ [hGate w] ++ gateTdagCirc w ++ [hGate w] ++ gateS w

def gateCH {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) : Circuit htcxGateSet N :=
  gateB w1 ++ [cxGate w0 w1 h01] ++ gateBdag w1

def oneHotSplit {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) : Circuit htcxGateSet N :=
  [cxGate w1 w0 h01.symm] ++ gateCH w0 w1 h01 ++ [cxGate w1 w0 h01.symm]

def gateCZ {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) : Circuit htcxGateSet N :=
  [hGate w1, cxGate w0 w1 h01, hGate w1]

lemma gateS_unitary {N : ℕ} (w : Fin N) :
    (gateS w).unitary = embed1 phaseS w := by
  dsimp [gateS]
  rw [circuit_unitary_cons, circuit_unitary_singleton, tGate_embedOp, embed1_mul, gateT_mul_gateT]

lemma gateZ_unitary {N : ℕ} (w : Fin N) :
    (gateZ w).unitary = embed1 pauliZ w := by
  dsimp [gateZ]
  rw [circuit_unitary_append, gateS_unitary, embed1_mul, phaseS_mul_phaseS]

lemma gateSdag_unitary {N : ℕ} (w : Fin N) :
    (gateSdag w).unitary = embed1 phaseSdag w := by
  dsimp [gateSdag]
  rw [circuit_unitary_append, gateZ_unitary, gateS_unitary, embed1_mul, pauliZ_mul_phaseS]

lemma gateTdagCirc_unitary {N : ℕ} (w : Fin N) :
    (gateTdagCirc w).unitary = embed1 gateTdag w := by
  unfold gateTdagCirc
  rw [circuit_unitary_append, gateSdag_unitary, circuit_unitary_singleton, tGate_embedOp,
    embed1_mul, phaseSdag_mul_gateT]

lemma gateX_unitary {N : ℕ} (w : Fin N) :
    (gateX w).unitary = embed1 pauliX w := by
  unfold gateX
  rw [circuit_unitary_append, circuit_unitary_append, circuit_unitary_singleton,
    hGate_embedOp, gateZ_unitary, embed1_mul, embed1_mul, hadamard_pauliZ_hadamard]

lemma gateB_unitary {N : ℕ} (w : Fin N) :
    (gateB w).unitary = embed1 matB w := by
  unfold gateB
  rw [circuit_unitary_append, circuit_unitary_append, gateS_unitary, gateSdag_unitary,
    circuit_unitary_cons, circuit_unitary_cons, circuit_unitary_singleton,
    hGate_embedOp, tGate_embedOp]
  simp only [embed1_mul, matB, Matrix.mul_assoc]

lemma gateBdag_unitary {N : ℕ} (w : Fin N) :
    (gateBdag w).unitary = embed1 matBdag w := by
  unfold gateBdag
  rw [circuit_unitary_append, circuit_unitary_append, circuit_unitary_append, circuit_unitary_append,
    gateS_unitary, gateTdagCirc_unitary, gateSdag_unitary, circuit_unitary_singleton, hGate_embedOp]
  simp only [embed1_mul, matBdag]

lemma gateCH_unitary {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    (gateCH w0 w1 h01).unitary = embed2 (controlled hadamard) w0 w1 h01 := by
  unfold gateCH
  rw [circuit_unitary_append, circuit_unitary_append, gateBdag_unitary, gateB_unitary,
    circuit_unitary_singleton, cxGate_embedOp,
    embed1_eq_embed2_blockDiag2 matBdag w0 w1 h01,
    embed1_eq_embed2_blockDiag2 matB w0 w1 h01,
    embed2_mul, embed2_mul, blockDiag2_BMul_cnot]

lemma oneHotSplit_unitary {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    (oneHotSplit w0 w1 h01).unitary = embed2 ohsMat w0 w1 h01 := by
  unfold oneHotSplit
  rw [circuit_unitary_append, circuit_unitary_append, gateCH_unitary,
    circuit_unitary_singleton, cxGate_embedOp, embed2_cnot_swap w0 w1 h01,
    embed2_mul, embed2_mul, ohsMat]

lemma star_oneHotSplit_unitary {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    star (oneHotSplit w0 w1 h01).unitary = (oneHotSplit w0 w1 h01).unitary := by
  rw [oneHotSplit_unitary, star_embed2, star_ohsMat]

lemma oneHotSplit_unitary_mul_self {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    (oneHotSplit w0 w1 h01).unitary * (oneHotSplit w0 w1 h01).unitary = 1 := by
  rw [oneHotSplit_unitary, embed2_mul, ohsMat_mul_self, embed2_one]

lemma gateCZ_unitary {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    (gateCZ w0 w1 h01).unitary = embed2 (controlled pauliZ) w0 w1 h01 := by
  dsimp [gateCZ]
  rw [circuit_unitary_cons, circuit_unitary_cons, circuit_unitary_singleton,
    hGate_embedOp, cxGate_embedOp,
    embed1_eq_embed2_blockDiag2 hadamard w0 w1 h01,
    embed2_mul, embed2_mul, Matrix.mul_assoc, blockDiag2_hadamard_cnot]

lemma star_hadamard : star hadamard = hadamard := by
  ext a b
  cases a <;> cases b <;> simp [hadamard, Complex.conj_ofReal]

lemma star_gateT : star gateT = gateTdag := by
  rw [gateT_eq_diag]
  ext a b
  cases a <;> cases b <;> simp [gateTdag, Complex.conj_ofReal]
  ring

lemma star_cnot : star cnot = cnot := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp [cnot]

lemma cnot_mul_self : cnot * cnot = 1 := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
    simp [cnot, Matrix.mul_apply, Fintype.sum_prod_type]

lemma emb1_eq_singleEmb {N : ℕ} (w : Fin 1 ↪ Fin N) :
    w = singleEmb (w 0) := by
  ext i
  fin_cases i
  rfl

lemma emb2_eq_pairEmb {N : ℕ} (w : Fin 2 ↪ Fin N) :
    w = pairEmb (w 0) (w 1) (fun h => by have := w.injective h; revert this; decide) := by
  ext i
  fin_cases i <;> rfl

lemma htcx_gateApp_mem_unitaryGroup {N : ℕ} (g : GateApp htcxGateSet N) :
    embedOp g.gate.mat g.wires ∈ Matrix.unitaryGroup (Qubits N) ℂ := by
  rcases g with ⟨⟨arity, mat⟩, hmem, wires⟩
  dsimp only [htcxGateSet, Gate.ofMatrix1, Gate.ofMatrix2, Set.mem_insert_iff,
    Set.mem_singleton_iff, Gate.mk.injEq] at hmem ⊢
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [emb1_eq_singleEmb wires]
    change embed1 hadamard (wires 0) ∈ Matrix.unitaryGroup (Qubits N) ℂ
    rw [Matrix.mem_unitaryGroup_iff', star_embed1, star_hadamard,
      embed1_mul, hadamard_mul_self, embed1_one]
  · rw [emb1_eq_singleEmb wires]
    change embed1 gateT (wires 0) ∈ Matrix.unitaryGroup (Qubits N) ℂ
    rw [Matrix.mem_unitaryGroup_iff', star_embed1, star_gateT,
      embed1_mul, gateTdag_mul_gateT, embed1_one]
  · rw [emb2_eq_pairEmb wires]
    set h01 : wires 0 ≠ wires 1 := fun h => by have := wires.injective h; revert this; decide
    change embed2 cnot (wires 0) (wires 1) h01 ∈ Matrix.unitaryGroup (Qubits N) ℂ
    rw [Matrix.mem_unitaryGroup_iff', star_embed2, star_cnot,
      embed2_mul, cnot_mul_self, embed2_one]

lemma htcx_unitary_mem_unitaryGroup {N : ℕ} (c : Circuit htcxGateSet N) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits N) ℂ := by
  induction c with
  | nil => exact Submonoid.one_mem _
  | cons g c ih =>
      rw [circuit_unitary_cons]
      exact Submonoid.mul_mem _ ih (htcx_gateApp_mem_unitaryGroup g)

lemma norm_act_htcx_unitary {N : ℕ} (c : Circuit htcxGateSet N)
    (ψ : EuclideanSpace ℂ (Qubits N)) :
    ‖act c.unitary ψ‖ = ‖ψ‖ :=
  act_norm_of_mem_unitaryGroup (htcx_unitary_mem_unitaryGroup c) ψ

/-! ### Section 3: Diagonal Circuits, Main + Workspace Decomposition, and `embedOH` -/

def IsDiagCircuit {N : ℕ} (c : Circuit htcxGateSet N) (ev : Qubits N → ℂ) : Prop :=
  ∀ z : Qubits N, act c.unitary (ket z) = ev z • ket z

lemma isDiagCircuit_nil {N : ℕ} :
    IsDiagCircuit ([] : Circuit htcxGateSet N) (fun _ => 1) := by
  intro z
  rw [circuit_unitary_nil, act_one, one_smul]

lemma IsDiagCircuit.append {N : ℕ} {c1 c2 : Circuit htcxGateSet N} {ev1 ev2 : Qubits N → ℂ}
    (h1 : IsDiagCircuit c1 ev1) (h2 : IsDiagCircuit c2 ev2) :
    IsDiagCircuit (c1 ++ c2) (fun z => ev1 z * ev2 z) := by
  intro z
  dsimp only
  rw [act_circuit_unitary_append, h1 z, act_smul, h2 z, smul_smul, mul_comm]

lemma isDiagCircuit_gateZ {N : ℕ} (w : Fin N) :
    IsDiagCircuit (gateZ w) (fun z => if z w then -1 else 1) := by
  intro z
  dsimp only
  rw [gateZ_unitary, act_embed1_ket]
  have hupd : Function.update z w (z w) = z := Function.update_eq_self w z
  cases hzw : z w <;> {
    rw [hzw] at hupd
    simp [pauliZ, hupd]
  }

lemma isDiagCircuit_gateS {N : ℕ} (w : Fin N) :
    IsDiagCircuit (gateS w) (fun z => if z w then Complex.I else 1) := by
  intro z
  dsimp only
  rw [gateS_unitary, act_embed1_ket]
  have hupd : Function.update z w (z w) = z := Function.update_eq_self w z
  cases hzw : z w <;> {
    rw [hzw] at hupd
    simp [phaseS, hupd]
  }

lemma isDiagCircuit_gateSdag {N : ℕ} (w : Fin N) :
    IsDiagCircuit (gateSdag w) (fun z => if z w then -Complex.I else 1) := by
  intro z
  dsimp only
  rw [gateSdag_unitary, act_embed1_ket]
  have hupd : Function.update z w (z w) = z := Function.update_eq_self w z
  cases hzw : z w <;> {
    rw [hzw] at hupd
    simp [phaseSdag, hupd]
  }

lemma isDiagCircuit_gateCZ {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) :
    IsDiagCircuit (gateCZ w0 w1 h01) (fun z => if z w0 && z w1 then -1 else 1) := by
  intro z
  dsimp only
  rw [gateCZ_unitary, act_embed2_ket, Fintype.sum_prod_type]
  have hupd : Function.update (Function.update z w0 (z w0)) w1 (z w1) = z := by
    rw [Function.update_eq_self, Function.update_eq_self]
  cases h0 : z w0 <;> cases h1 : z w1 <;> {
    rw [h0, h1] at hupd
    simp [controlled, pauliZ, hupd]
  }

def mainWire (n m : ℕ) (q : Fin (n + 1)) : Fin (n + (1 + 2 * m)) :=
  ⟨q.1, by omega⟩

def workWire (n m : ℕ) (k : Fin (2 * m)) : Fin (n + (1 + 2 * m)) :=
  ⟨n + 1 + k.1, by omega⟩

lemma mainWire_ne {n m : ℕ} {q1 q2 : Fin (n + 1)} (h : q1 ≠ q2) :
    mainWire n m q1 ≠ mainWire n m q2 := by
  intro heq
  apply h
  have := congrArg Fin.val heq
  dsimp [mainWire] at this
  ext
  exact this

lemma workWire_ne {n m : ℕ} {k1 k2 : Fin (2 * m)} (h : k1 ≠ k2) :
    workWire n m k1 ≠ workWire n m k2 := by
  intro heq
  apply h
  have := congrArg Fin.val heq
  dsimp [workWire] at this
  ext
  omega

lemma mainWire_ne_workWire {n m : ℕ} (q : Fin (n + 1)) (k : Fin (2 * m)) :
    mainWire n m q ≠ workWire n m k := by
  intro heq
  have := congrArg Fin.val heq
  dsimp [mainWire, workWire] at this
  omega

def vecMW {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m)) :
    Qubits (n + (1 + 2 * m)) :=
  fun w => if h : w.1 < n + 1 then y ⟨w.1, h⟩ else z_work ⟨w.1 - (n + 1), by omega⟩

def mainProj {n m : ℕ} (z : Qubits (n + (1 + 2 * m))) : Qubits (n + 1) :=
  fun q => z (mainWire n m q)

def workProj {n m : ℕ} (z : Qubits (n + (1 + 2 * m))) : Qubits (2 * m) :=
  fun k => z (workWire n m k)

@[simp] lemma vecMW_main {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m))
    (q : Fin (n + 1)) :
    vecMW y z_work (mainWire n m q) = y q := by
  dsimp [vecMW, mainWire]
  rw [dif_pos q.2]

@[simp] lemma vecMW_work {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m))
    (k : Fin (2 * m)) :
    vecMW y z_work (workWire n m k) = z_work k := by
  dsimp [vecMW, workWire]
  rw [dif_neg (by omega)]
  congr 1
  ext
  dsimp
  omega

@[simp] lemma mainProj_vecMW {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m)) :
    mainProj (vecMW y z_work) = y := by
  funext q
  exact vecMW_main y z_work q

@[simp] lemma workProj_vecMW {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m)) :
    workProj (vecMW y z_work) = z_work := by
  funext k
  exact vecMW_work y z_work k

lemma vecMW_mainProj_workProj {n m : ℕ} (z : Qubits (n + (1 + 2 * m))) :
    vecMW (mainProj z) (workProj z) = z := by
  funext w
  dsimp [vecMW, mainProj, workProj, mainWire, workWire]
  split_ifs with h
  · rfl
  · congr 1
    ext
    dsimp
    omega

lemma eq_vecMW_iff {n m : ℕ} (z : Qubits (n + (1 + 2 * m)))
    (y : Qubits (n + 1)) (z_work : Qubits (2 * m)) :
    z = vecMW y z_work ↔ mainProj z = y ∧ workProj z = z_work := by
  constructor
  · rintro rfl
    exact ⟨mainProj_vecMW y z_work, workProj_vecMW y z_work⟩
  · rintro ⟨rfl, rfl⟩
    exact (vecMW_mainProj_workProj z).symm

lemma update_vecMW_main {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m))
    (q : Fin (n + 1)) (b : Bool) :
    Function.update (vecMW y z_work) (mainWire n m q) b =
      vecMW (Function.update y q b) z_work := by
  rw [eq_vecMW_iff]
  refine ⟨?_, ?_⟩
  · funext q'
    dsimp [mainProj]
    by_cases h : q' = q
    · subst h; simp
    · rw [Function.update_of_ne (mainWire_ne h), vecMW_main, Function.update_of_ne h]
  · funext k
    dsimp [workProj]
    rw [Function.update_of_ne (mainWire_ne_workWire q k).symm, vecMW_work]

lemma update_vecMW_work {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m))
    (k : Fin (2 * m)) (b : Bool) :
    Function.update (vecMW y z_work) (workWire n m k) b =
      vecMW y (Function.update z_work k b) := by
  rw [eq_vecMW_iff]
  refine ⟨?_, ?_⟩
  · funext q
    dsimp [mainProj]
    rw [Function.update_of_ne (mainWire_ne_workWire q k), vecMW_main]
  · funext k'
    dsimp [workProj]
    by_cases h : k' = k
    · subst h; simp
    · rw [Function.update_of_ne (workWire_ne h), vecMW_work, Function.update_of_ne h]

def ketMW {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m)) :
    EuclideanSpace ℂ (Qubits (n + (1 + 2 * m))) :=
  ket (vecMW y z_work)

def ketZeroWork {n m : ℕ} (y : Qubits (n + 1)) :
    EuclideanSpace ℂ (Qubits (n + (1 + 2 * m))) :=
  ketMW y (0 : Qubits (2 * m))

def oneHotBits {M : ℕ} (k : Fin M) : Qubits M :=
  Function.update (0 : Qubits M) k true

@[simp] lemma oneHotBits_self {M : ℕ} (k : Fin M) :
    oneHotBits k k = true := by
  simp [oneHotBits]

lemma oneHotBits_of_ne {M : ℕ} {k j : Fin M} (h : j ≠ k) :
    oneHotBits k j = false := by
  simp [oneHotBits, Function.update_of_ne h, qubits_zero_def]

lemma oneHotBits_apply {M : ℕ} (k j : Fin M) :
    oneHotBits k j = decide (j = k) := by
  by_cases h : j = k
  · subst h; simp
  · simp [oneHotBits_of_ne h, h]

lemma oneHotBits_inj {M : ℕ} {k1 k2 : Fin M} :
    oneHotBits k1 = oneHotBits k2 ↔ k1 = k2 := by
  constructor
  · intro h
    have hk := congrFun h k1
    rw [oneHotBits_self, oneHotBits_apply] at hk
    exact of_decide_eq_true hk.symm
  · rintro rfl; rfl

lemma update_zero_true {M : ℕ} (k : Fin M) :
    Function.update (0 : Qubits M) k true = oneHotBits k := rfl

lemma update_oneHotBits_self_false {M : ℕ} (k : Fin M) :
    Function.update (oneHotBits k) k false = (0 : Qubits M) := by
  rw [qubits_zero_def]
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [Function.update_of_ne h, oneHotBits_of_ne h]

lemma update_oneHotBits_self_true {M : ℕ} (k : Fin M) :
    Function.update (oneHotBits k) k true = oneHotBits k := by
  simp [oneHotBits]

def ketOH {n m : ℕ} (y : Qubits (n + 1)) (k : Fin (2 * m)) :
    EuclideanSpace ℂ (Qubits (n + (1 + 2 * m))) :=
  ketMW y (oneHotBits k)

noncomputable def embedOH {n m : ℕ} (y : Qubits (n + 1)) (β : Fin (2 * m) → ℂ) :
    EuclideanSpace ℂ (Qubits (n + (1 + 2 * m))) :=
  ∑ k : Fin (2 * m), β k • ketOH y k

lemma embedOH_add {n m : ℕ} (y : Qubits (n + 1)) (α β : Fin (2 * m) → ℂ) :
    embedOH y (fun k => α k + β k) = embedOH y α + embedOH y β := by
  unfold embedOH
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => add_smul (α k) (β k) (ketOH y k))

lemma embedOH_sub {n m : ℕ} (y : Qubits (n + 1)) (α β : Fin (2 * m) → ℂ) :
    embedOH y (fun k => α k - β k) = embedOH y α - embedOH y β := by
  unfold embedOH
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => sub_smul (α k) (β k) (ketOH y k))

lemma embedOH_smul {n m : ℕ} (y : Qubits (n + 1)) (c : ℂ) (β : Fin (2 * m) → ℂ) :
    embedOH y (fun k => c * β k) = c • embedOH y β := by
  unfold embedOH
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => mul_smul c (β k) (ketOH y k))

lemma embedOH_single {n m : ℕ} (y : Qubits (n + 1)) (k0 : Fin (2 * m)) (c : ℂ) :
    embedOH y (fun k => if k = k0 then c else 0) = c • ketOH y k0 := by
  unfold embedOH
  rw [Finset.sum_eq_single k0]
  · simp
  · intro k _ hk; simp [hk]
  · intro habs; exact False.elim (habs (Finset.mem_univ _))

lemma embedOH_ofLp_vecMW_oneHotBits {n m : ℕ} (y : Qubits (n + 1))
    (β : Fin (2 * m) → ℂ) (k : Fin (2 * m)) :
    (embedOH y β).ofLp (vecMW y (oneHotBits k)) = β k := by
  unfold embedOH ketOH ketMW
  rw [sum_ofLp_apply, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    have hne : vecMW y (oneHotBits k) ≠ vecMW y (oneHotBits j) := by
      intro heq
      rw [eq_vecMW_iff, workProj_vecMW] at heq
      exact hj (oneHotBits_inj.mp heq.2).symm
    simp [hne]
  · intro habs; exact False.elim (habs (Finset.mem_univ _))

lemma embedOH_ofLp_of_not_oneHot {n m : ℕ} (y : Qubits (n + 1))
    (β : Fin (2 * m) → ℂ) (z : Qubits (n + (1 + 2 * m)))
    (hz : ∀ k : Fin (2 * m), z ≠ vecMW y (oneHotBits k)) :
    (embedOH y β).ofLp z = 0 := by
  unfold embedOH ketOH ketMW
  rw [sum_ofLp_apply]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  simp [hz k]

lemma norm_embedOH_sq {n m : ℕ} (y : Qubits (n + 1)) (β : Fin (2 * m) → ℂ) :
    ‖embedOH y β‖ ^ 2 = ∑ k : Fin (2 * m), ‖β k‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  let f : Fin (2 * m) → Qubits (n + (1 + 2 * m)) := fun k => vecMW y (oneHotBits k)
  have hinj : Function.Injective f := by
    intro k1 k2 h
    dsimp [f] at h
    rw [eq_vecMW_iff, workProj_vecMW] at h
    exact oneHotBits_inj.mp h.2
  have hsub : ∑ z : Qubits (n + (1 + 2 * m)), ‖(embedOH y β).ofLp z‖ ^ 2 =
      ∑ z ∈ Finset.univ.image f, ‖(embedOH y β).ofLp z‖ ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun z _ hz => ?_)
    rw [Finset.mem_image] at hz
    push Not at hz
    have h0 := embedOH_ofLp_of_not_oneHot y β z (fun k => (hz k (Finset.mem_univ k)).symm)
    simp [h0]
  rw [hsub, Finset.sum_image (fun k1 _ k2 _ h => hinj h)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [embedOH_ofLp_vecMW_oneHotBits]

def InFiber {n m : ℕ} (y : Qubits (n + 1))
    (Ψ : EuclideanSpace ℂ (Qubits (n + (1 + 2 * m)))) : Prop :=
  ∀ z : Qubits (n + (1 + 2 * m)), mainProj z ≠ y → Ψ.ofLp z = 0

lemma inFiber_ketMW {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m)) :
    InFiber y (ketMW y z_work) := by
  intro z hz
  dsimp [ketMW]
  rw [ket_apply, if_neg]
  intro heq
  rw [eq_vecMW_iff] at heq
  exact hz heq.1

lemma inFiber_ketZeroWork {n m : ℕ} (y : Qubits (n + 1)) :
    InFiber (m := m) y (ketZeroWork (m := m) y) :=
  inFiber_ketMW y 0

lemma inFiber_embedOH {n m : ℕ} (y : Qubits (n + 1)) (β : Fin (2 * m) → ℂ) :
    InFiber y (embedOH y β) := by
  intro z hz
  refine embedOH_ofLp_of_not_oneHot y β z (fun k heq => ?_)
  rw [eq_vecMW_iff] at heq
  exact hz heq.1

lemma InFiber.add {n m : ℕ} {y : Qubits (n + 1)}
    {Ψ Φ : EuclideanSpace ℂ (Qubits (n + (1 + 2 * m)))}
    (hΨ : InFiber y Ψ) (hΦ : InFiber y Φ) :
    InFiber y (Ψ + Φ) := by
  intro z hz
  rw [add_ofLp_apply, hΨ z hz, hΦ z hz, add_zero]

lemma InFiber.sub {n m : ℕ} {y : Qubits (n + 1)}
    {Ψ Φ : EuclideanSpace ℂ (Qubits (n + (1 + 2 * m)))}
    (hΨ : InFiber y Ψ) (hΦ : InFiber y Φ) :
    InFiber y (Ψ - Φ) := by
  intro z hz
  rw [sub_ofLp_apply, hΨ z hz, hΦ z hz, sub_zero]

lemma InFiber.smul {n m : ℕ} {y : Qubits (n + 1)} (c : ℂ)
    {Ψ : EuclideanSpace ℂ (Qubits (n + (1 + 2 * m)))}
    (hΨ : InFiber y Ψ) :
    InFiber y (c • Ψ) := by
  intro z hz
  rw [smul_ofLp_apply, hΨ z hz, mul_zero]

lemma norm_sum_inFiber_sq {n m : ℕ}
    (E : Qubits (n + 1) → EuclideanSpace ℂ (Qubits (n + (1 + 2 * m))))
    (hE : ∀ y, InFiber y (E y)) :
    ‖∑ y : Qubits (n + 1), E y‖ ^ 2 = ∑ y : Qubits (n + 1), ‖E y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have hz_eq : ∀ z : Qubits (n + (1 + 2 * m)),
      ‖(∑ y : Qubits (n + 1), E y).ofLp z‖ ^ 2 =
        ∑ y : Qubits (n + 1), ‖(E y).ofLp z‖ ^ 2 := by
    intro z
    rw [sum_ofLp_apply, Finset.sum_eq_single (mainProj z),
      Finset.sum_eq_single (mainProj z)]
    · intro y _ hy
      rw [hE y z (Ne.symm hy), norm_zero, sq, mul_zero]
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
    · intro y _ hy
      exact hE y z (Ne.symm hy)
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
  simp_rw [hz_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => (EuclideanSpace.norm_sq_eq (E y)).symm)

lemma norm_sum_inFiber_le {n m : ℕ}
    (E : Qubits (n + 1) → EuclideanSpace ℂ (Qubits (n + (1 + 2 * m))))
    (hE : ∀ y, InFiber y (E y))
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ y, ‖E y‖ ≤ δ * ‖Φ.ofLp y‖) :
    ‖∑ y : Qubits (n + 1), E y‖ ≤ δ * ‖Φ‖ := by
  have hsq : ‖∑ y : Qubits (n + 1), E y‖ ^ 2 ≤ (δ * ‖Φ‖) ^ 2 := by
    rw [norm_sum_inFiber_sq E hE, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun y _ => ?_)
    have hb := pow_le_pow_left₀ (norm_nonneg (E y)) (hbound y) 2
    rwa [mul_pow] at hb
  nlinarith [norm_nonneg (∑ y : Qubits (n + 1), E y), mul_nonneg hδ (norm_nonneg Φ)]

noncomputable def liftWork {n m : ℕ} (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    EuclideanSpace ℂ (Qubits (n + (1 + 2 * m))) :=
  WithLp.toLp 2 (fun z : Qubits (n + (1 + 2 * m)) =>
    if workProj z = 0 then Φ.ofLp (mainProj z) else 0)

lemma liftWork_eq_sum_ketZeroWork {n m : ℕ} (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    liftWork (m := m) Φ = ∑ y : Qubits (n + 1), Φ.ofLp y • ketZeroWork (m := m) y := by
  ext z
  simp only [liftWork, toLp_ofLp_apply, sum_ofLp_apply, smul_ofLp_apply, ketZeroWork, ketMW,
    ket_apply, eq_vecMW_iff]
  by_cases hw : workProj z = 0
  · rw [if_pos hw, Finset.sum_eq_single (mainProj z)]
    · simp [hw]
    · intro y _ hy
      simp [hy.symm]
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
  · rw [if_neg hw]
    symm
    refine Finset.sum_eq_zero (fun y _ => ?_)
    simp [hw]

lemma norm_ketMW {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m)) :
    ‖ketMW y z_work‖ = 1 := by
  change IsState (ket (vecMW y z_work))
  simp [IsState, ket]

lemma norm_ketZeroWork {n m : ℕ} (y : Qubits (n + 1)) :
    ‖ketZeroWork (m := m) y‖ = 1 :=
  norm_ketMW y 0

lemma norm_liftWork {n m : ℕ} (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    ‖liftWork (m := m) Φ‖ = ‖Φ‖ := by
  have hsq : ‖liftWork (m := m) Φ‖ ^ 2 = ‖Φ‖ ^ 2 := by
    rw [liftWork_eq_sum_ketZeroWork,
      norm_sum_inFiber_sq (fun y => Φ.ofLp y • ketZeroWork y)
        (fun y => (inFiber_ketZeroWork y).smul (Φ.ofLp y)),
      EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [norm_smul, norm_ketZeroWork, mul_one]
  nlinarith [norm_nonneg (liftWork (m := m) Φ), norm_nonneg Φ]

lemma liftWork_sub {n m : ℕ} (Φ1 Φ2 : EuclideanSpace ℂ (Qubits (n + 1))) :
    liftWork (m := m) Φ1 - liftWork (m := m) Φ2 = liftWork (m := m) (Φ1 - Φ2) := by
  ext z
  simp only [liftWork, toLp_ofLp_apply, sub_ofLp_apply]
  split_ifs <;> ring

lemma act_gateX_ketMW_work {n m : ℕ} (y : Qubits (n + 1)) (z_work : Qubits (2 * m))
    (k0 : Fin (2 * m)) :
    act (gateX (workWire n m k0)).unitary (ketMW y z_work) =
      ketMW y (Function.update z_work k0 (!z_work k0)) := by
  dsimp [ketMW]
  rw [gateX_unitary, act_embed1_ket, vecMW_work]
  cases hzk : z_work k0 <;>
    simp [pauliX, update_vecMW_work]

lemma act_gateX_ketZeroWork {n m : ℕ} (y : Qubits (n + 1)) (k0 : Fin (2 * m)) :
    act (gateX (workWire n m k0)).unitary (ketZeroWork y) = ketOH y k0 := by
  rw [ketZeroWork, act_gateX_ketMW_work]
  rfl

lemma act_gateX_ketOH_self {n m : ℕ} (y : Qubits (n + 1)) (k0 : Fin (2 * m)) :
    act (gateX (workWire n m k0)).unitary (ketOH y k0) = ketZeroWork y := by
  rw [ketOH, act_gateX_ketMW_work, oneHotBits_self, Bool.not_true,
    update_oneHotBits_self_false, ketZeroWork]

lemma inFiber_act_gateX_embedOH {n m : ℕ} (y : Qubits (n + 1)) (k0 : Fin (2 * m))
    (β : Fin (2 * m) → ℂ) :
    InFiber y (act (gateX (workWire n m k0)).unitary (embedOH y β)) := by
  unfold embedOH ketOH
  rw [act_sum]
  intro z hz
  rw [sum_ofLp_apply]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [act_smul, act_gateX_ketMW_work, smul_ofLp_apply,
    inFiber_ketMW y _ z hz, mul_zero]

lemma IsDiagCircuit.act_embedOH {n m : ℕ} {c : Circuit htcxGateSet (n + (1 + 2 * m))}
    {ev : Qubits (n + (1 + 2 * m)) → ℂ} (hc : IsDiagCircuit c ev)
    (y : Qubits (n + 1)) (β : Fin (2 * m) → ℂ) :
    act c.unitary (embedOH y β) =
      embedOH y (fun k => ev (vecMW y (oneHotBits k)) * β k) := by
  unfold embedOH ketOH ketMW
  rw [act_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  dsimp only
  rw [act_smul, hc, smul_smul, mul_comm (β k)]

lemma act_gateZ_embedOH {n m : ℕ} (y : Qubits (n + 1)) (k0 : Fin (2 * m))
    (β : Fin (2 * m) → ℂ) :
    act (gateZ (workWire n m k0)).unitary (embedOH y β) =
      embedOH y β - (2 * β k0) • ketOH y k0 := by
  rw [(isDiagCircuit_gateZ (workWire n m k0)).act_embedOH y β,
    ← embedOH_single y k0 (2 * β k0), ← embedOH_sub]
  congr 1
  funext k
  rw [vecMW_work, oneHotBits_apply]
  by_cases h : k = k0
  · subst h; simp; ring
  · have hne : k0 ≠ k := Ne.symm h
    simp [h, hne]

lemma act_oneHotSplit_ketOH {n m : ℕ} (y : Qubits (n + 1))
    (a b : Fin (2 * m)) (hab : a ≠ b) (k : Fin (2 * m)) :
    act (oneHotSplit (workWire n m a) (workWire n m b) (workWire_ne hab)).unitary (ketOH y k) =
      if k = a then
        ((Real.sqrt 2)⁻¹ : ℂ) • ketOH y a + ((Real.sqrt 2)⁻¹ : ℂ) • ketOH y b
      else if k = b then
        ((Real.sqrt 2)⁻¹ : ℂ) • ketOH y a - ((Real.sqrt 2)⁻¹ : ℂ) • ketOH y b
      else
        ketOH y k := by
  dsimp [ketOH, ketMW]
  rw [oneHotSplit_unitary, act_embed2_ket, Fintype.sum_prod_type]
  simp_rw [vecMW_work, update_vecMW_work]
  by_cases hka : k = a
  · subst hka
    rw [if_pos rfl, oneHotBits_self, oneHotBits_of_ne hab.symm]
    have h_ft : Function.update (Function.update (oneHotBits k) k false) b true = oneHotBits b := by
      rw [update_oneHotBits_self_false, update_zero_true]
    have h_tf : Function.update (Function.update (oneHotBits k) k true) b false = oneHotBits k := by
      rw [update_oneHotBits_self_true]
      funext j
      by_cases hjb : j = b
      · subst hjb; simp [oneHotBits_of_ne hab.symm]
      · simp [Function.update_of_ne hjb]
    simp only [Fintype.sum_bool, ohsMat_apply, h_ft, h_tf, zero_smul, add_zero, zero_add]
  · rw [if_neg hka]
    by_cases hkb : k = b
    · subst hkb
      rw [if_pos rfl, oneHotBits_of_ne hab, oneHotBits_self]
      have h_ft : Function.update (Function.update (oneHotBits k) a false) k true = oneHotBits k := by
        have h1 : Function.update (oneHotBits k) a false = oneHotBits k := by
          funext j
          by_cases hja : j = a
          · subst hja; simp [oneHotBits_of_ne hab]
          · simp [Function.update_of_ne hja]
        rw [h1, update_oneHotBits_self_true]
      have h_tf : Function.update (Function.update (oneHotBits k) a true) k false = oneHotBits a := by
        rw [Function.update_comm hab, update_oneHotBits_self_false, update_zero_true]
      simp only [Fintype.sum_bool, ohsMat_apply, h_ft, h_tf, zero_smul, add_zero, zero_add]
      ext z
      simp only [add_ofLp_apply, sub_ofLp_apply, smul_ofLp_apply]
      ring
    · rw [if_neg hkb, oneHotBits_of_ne (Ne.symm hka), oneHotBits_of_ne (Ne.symm hkb)]
      have h_ff : Function.update (Function.update (oneHotBits k) a false) b false = oneHotBits k := by
        funext j
        by_cases hjb : j = b
        · subst hjb; simp [oneHotBits_of_ne (Ne.symm hkb)]
        · rw [Function.update_of_ne hjb]
          by_cases hja : j = a
          · subst hja; simp [oneHotBits_of_ne (Ne.symm hka)]
          · simp [Function.update_of_ne hja]
      simp only [Fintype.sum_bool, ohsMat_apply, h_ff, one_smul, zero_smul, zero_add]

lemma sum_pair_split {α E : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid E]
    (a b : α) (hab : a ≠ b) (g : α → E) :
    ∑ k : α, g k = g a + g b + ∑ k ∈ (Finset.univ.erase a).erase b, g k := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
    add_assoc]

lemma act_oneHotSplit_embedOH {n m : ℕ} (y : Qubits (n + 1))
    (a b : Fin (2 * m)) (hab : a ≠ b) (β : Fin (2 * m) → ℂ) :
    act (oneHotSplit (workWire n m a) (workWire n m b) (workWire_ne hab)).unitary
        (embedOH y β) =
      embedOH y (fun k =>
        if k = a then ((Real.sqrt 2)⁻¹ : ℂ) * β a + ((Real.sqrt 2)⁻¹ : ℂ) * β b
        else if k = b then ((Real.sqrt 2)⁻¹ : ℂ) * β a - ((Real.sqrt 2)⁻¹ : ℂ) * β b
        else β k) := by
  unfold embedOH
  rw [act_sum, sum_pair_split a b hab, sum_pair_split a b hab]
  have hrest :
      ∑ k ∈ (Finset.univ.erase a).erase b,
        act (oneHotSplit (workWire n m a) (workWire n m b) (workWire_ne hab)).unitary (β k • ketOH y k) =
      ∑ k ∈ (Finset.univ.erase a).erase b,
        (if k = a then ((Real.sqrt 2)⁻¹ : ℂ) * β a + ((Real.sqrt 2)⁻¹ : ℂ) * β b
         else if k = b then ((Real.sqrt 2)⁻¹ : ℂ) * β a - ((Real.sqrt 2)⁻¹ : ℂ) * β b
         else β k) • ketOH y k := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkb : k ≠ b := (Finset.mem_erase.mp hk).1
    have hka : k ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    rw [act_smul, act_oneHotSplit_ketOH y a b hab k, if_neg hka, if_neg hkb, if_neg hka, if_neg hkb]
  rw [hrest]
  congr 1
  rw [act_smul, act_smul, act_oneHotSplit_ketOH y a b hab a, act_oneHotSplit_ketOH y a b hab b]
  simp only [↓reduceIte, hab.symm]
  ext z
  simp only [add_ofLp_apply, sub_ofLp_apply, smul_ofLp_apply]
  ring

/-! ### Section 4: One-Hot Dyadic LCU and 1-Step Oblivious Amplitude Amplification `approxRz` -/

def dyadicExp (m r : ℕ) : ℕ :=
  if r + 1 < m then r + 2 else m

lemma one_le_dyadicExp {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    1 ≤ dyadicExp m r := by
  unfold dyadicExp
  split_ifs <;> omega

noncomputable def dyadicWeight (m : ℕ) (r : Fin m) : ℝ :=
  ((2 : ℝ) ^ (dyadicExp m r.1))⁻¹

noncomputable def chiVec (m : ℕ) (k : Fin (2 * m)) : ℝ :=
  ((Real.sqrt 2)⁻¹) ^ (dyadicExp m (k.1 / 2))

lemma chiVec_nonneg (m : ℕ) (k : Fin (2 * m)) : 0 ≤ chiVec m k := by
  unfold chiVec
  positivity

lemma dyadicWeight_nonneg (m : ℕ) (r : Fin m) : 0 ≤ dyadicWeight m r := by
  unfold dyadicWeight
  positivity

lemma sqrt2_inv_pow_sq (p : ℕ) :
    (((Real.sqrt 2)⁻¹ : ℝ) ^ p) ^ 2 = ((2 : ℝ) ^ p)⁻¹ := by
  rw [← pow_mul, mul_comm p 2, pow_mul, inv_pow, Real.sq_sqrt (by norm_num), inv_pow]

lemma chiVec_sq_even {m : ℕ} (r : Fin m) :
    (chiVec m ⟨2 * r.1, by omega⟩) ^ 2 = dyadicWeight m r := by
  dsimp [chiVec, dyadicWeight]
  have hdiv : (2 * r.1) / 2 = r.1 := by omega
  rw [hdiv, sqrt2_inv_pow_sq]

lemma chiVec_sq_odd {m : ℕ} (r : Fin m) :
    (chiVec m ⟨2 * r.1 + 1, by omega⟩) ^ 2 = dyadicWeight m r := by
  dsimp [chiVec, dyadicWeight]
  have hdiv : (2 * r.1 + 1) / 2 = r.1 := by omega
  rw [hdiv, sqrt2_inv_pow_sq]

noncomputable def tailWeight (m r : ℕ) : ℝ :=
  if r < m then ((2 : ℝ) ^ (r + 1))⁻¹ else 0

lemma dyadicWeight_eq_sub_tailWeight {m : ℕ} (r : Fin m) :
    dyadicWeight m r = tailWeight m r.1 - tailWeight m (r.1 + 1) := by
  dsimp [dyadicWeight, dyadicExp, tailWeight]
  rw [if_pos r.2]
  by_cases h : r.1 + 1 < m
  · rw [if_pos h, if_pos h, pow_succ ((2 : ℝ)) (r.1 + 1), mul_inv]
    ring
  · rw [if_neg h, if_neg h]
    have hm : r.1 + 1 = m := by omega
    rw [hm, sub_zero]

lemma sum_dyadicWeight {m : ℕ} (hm : 1 ≤ m) :
    ∑ r : Fin m, dyadicWeight m r = 2⁻¹ := by
  simp_rw [dyadicWeight_eq_sub_tailWeight]
  rw [Fin.sum_univ_eq_sum_range (fun r => tailWeight m r - tailWeight m (r + 1)),
    Finset.sum_range_sub' (fun r => tailWeight m r) m]
  dsimp [tailWeight]
  rw [if_pos (by omega : 0 < m), if_neg (lt_irrefl m), pow_one, sub_zero]

lemma sum_range_two_mul {E : Type*} [AddCommMonoid E] (m : ℕ) (g : ℕ → E) :
    ∑ k ∈ Finset.range (2 * m), g k =
      ∑ r ∈ Finset.range m, (g (2 * r) + g (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

lemma sum_fin_two_mul {E : Type*} [AddCommMonoid E] (m : ℕ) (f : Fin (2 * m) → E) :
    ∑ k : Fin (2 * m), f k =
      ∑ r : Fin m, (f ⟨2 * r.1, by omega⟩ + f ⟨2 * r.1 + 1, by omega⟩) := by
  let g : ℕ → E := fun k => if h : k < 2 * m then f ⟨k, h⟩ else 0
  have hf : ∀ k : Fin (2 * m), f k = g k.1 := fun k => by
    simp [g, k.2]
  simp_rw [hf]
  rw [Fin.sum_univ_eq_sum_range g, sum_range_two_mul,
    ← Fin.sum_univ_eq_sum_range (fun r => g (2 * r) + g (2 * r + 1))]

lemma sum_chiVec_sq {m : ℕ} (hm : 1 ≤ m) :
    ∑ k : Fin (2 * m), (chiVec m k) ^ 2 = 1 := by
  rw [sum_fin_two_mul]
  simp_rw [chiVec_sq_even, chiVec_sq_odd, ← two_mul]
  rw [← Finset.mul_sum, sum_dyadicWeight hm]
  norm_num

lemma sum_chiVec_complex_sq {m : ℕ} (hm : 1 ≤ m) :
    ∑ k : Fin (2 * m), (chiVec m k : ℂ) * (chiVec m k : ℂ) = 1 := by
  have h : ∑ k : Fin (2 * m), (chiVec m k : ℂ) * (chiVec m k : ℂ) =
      ((∑ k : Fin (2 * m), (chiVec m k) ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [h, sum_chiVec_sq hm, Complex.ofReal_one]

noncomputable def greedyPartial (τ : ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 =>
    let prev := greedyPartial τ r
    prev + ((2 : ℝ) ^ (r + 2))⁻¹ * (if prev ≤ τ then 1 else -1)

noncomputable def greedyBit (τ : ℝ) (r : ℕ) : Bool :=
  decide (greedyPartial τ r ≤ τ)

def signOfBool (b : Bool) : ℝ :=
  if b then 1 else -1

lemma signOfBool_greedyBit (τ : ℝ) (r : ℕ) :
    signOfBool (greedyBit τ r) = if greedyPartial τ r ≤ τ then 1 else -1 := by
  dsimp [signOfBool, greedyBit]
  by_cases h : greedyPartial τ r ≤ τ <;> simp [h]

lemma abs_greedyPartial_sub_le {τ : ℝ} (hτ : |τ| ≤ 2⁻¹) :
    ∀ r : ℕ, |greedyPartial τ r - τ| ≤ ((2 : ℝ) ^ (r + 1))⁻¹
  | 0 => by simpa [greedyPartial] using hτ
  | r + 1 => by
    have ih := abs_le.mp (abs_greedyPartial_sub_le hτ r)
    have hpow : ((2 : ℝ) ^ (r + 1))⁻¹ = 2 * ((2 : ℝ) ^ (r + 2))⁻¹ := by
      rw [pow_succ ((2 : ℝ)) (r + 1), mul_inv]
      ring
    dsimp [greedyPartial]
    rw [abs_le]
    split_ifs with hle <;> constructor <;> linarith

lemma sum_range_dyadic_greedy (τ : ℝ) :
    ∀ j : ℕ,
      ∑ r ∈ Finset.range j, ((2 : ℝ) ^ (r + 2))⁻¹ * signOfBool (greedyBit τ r) =
        greedyPartial τ j
  | 0 => rfl
  | j + 1 => by
    rw [Finset.sum_range_succ, sum_range_dyadic_greedy τ j, signOfBool_greedyBit]
    rfl

lemma abs_sum_dyadicWeight_greedyBit_sub_le {m : ℕ} (hm : 1 ≤ m) {τ : ℝ} (hτ : |τ| ≤ 2⁻¹) :
    |(∑ r : Fin m, dyadicWeight m r * signOfBool (greedyBit τ r.1)) - τ| ≤ ((2 : ℝ) ^ m)⁻¹ := by
  dsimp only [dyadicWeight]
  rw [Fin.sum_univ_eq_sum_range (fun r =>
    ((2 : ℝ) ^ (dyadicExp m r))⁻¹ * signOfBool (greedyBit τ r))]
  have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
  conv_lhs =>
    arg 1; arg 1; arg 1; rw [hm_eq]
  rw [Finset.sum_range_succ]
  have hinit :
      ∑ r ∈ Finset.range (m - 1), ((2 : ℝ) ^ (dyadicExp m r))⁻¹ * signOfBool (greedyBit τ r) =
        greedyPartial τ (m - 1) := by
    rw [← sum_range_dyadic_greedy τ (m - 1)]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hlt : r + 1 < m := by
      rw [Finset.mem_range] at hr; omega
    dsimp [dyadicExp]
    rw [if_pos hlt]
  have hlast : dyadicExp m (m - 1) = m := by
    dsimp [dyadicExp]
    rw [if_neg (by omega)]
  rw [hinit, hlast, signOfBool_greedyBit]
  have hbound := abs_le.mp (abs_greedyPartial_sub_le hτ (m - 1))
  rw [← hm_eq] at hbound
  rw [abs_le]
  split_ifs with hle <;> constructor <;> linarith

lemma gateS_size {N : ℕ} (w : Fin N) : (gateS w).size = 2 := rfl
lemma gateZ_size {N : ℕ} (w : Fin N) : (gateZ w).size = 4 := rfl
lemma gateSdag_size {N : ℕ} (w : Fin N) : (gateSdag w).size = 6 := rfl
lemma gateX_size {N : ℕ} (w : Fin N) : (gateX w).size = 6 := rfl
lemma gateCZ_size {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) : (gateCZ w0 w1 h01).size = 3 := rfl
lemma oneHotSplit_size {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) : (oneHotSplit w0 w1 h01).size = 31 := rfl

abbrev OhsPair (m : ℕ) : Type :=
  { p : Fin (2 * m) × Fin (2 * m) // p.1 ≠ p.2 }

def ohsStep (n m : ℕ) (p : OhsPair m) : Circuit htcxGateSet (n + (1 + 2 * m)) :=
  oneHotSplit (workWire n m p.1.1) (workWire n m p.1.2) (workWire_ne p.2)

noncomputable def ohsVecStep {m : ℕ} (a b : Fin (2 * m)) (β : Fin (2 * m) → ℂ) :
    Fin (2 * m) → ℂ :=
  fun k =>
    if k = a then ((Real.sqrt 2)⁻¹ : ℂ) * β a + ((Real.sqrt 2)⁻¹ : ℂ) * β b
    else if k = b then ((Real.sqrt 2)⁻¹ : ℂ) * β a - ((Real.sqrt 2)⁻¹ : ℂ) * β b
    else β k

lemma act_ohsStep_embedOH {n m : ℕ} (y : Qubits (n + 1)) (p : OhsPair m)
    (β : Fin (2 * m) → ℂ) :
    act (ohsStep n m p).unitary (embedOH y β) =
      embedOH y (ohsVecStep p.1.1 p.1.2 β) :=
  act_oneHotSplit_embedOH y p.1.1 p.1.2 p.2 β

lemma star_ohsStep_unitary {n m : ℕ} (p : OhsPair m) :
    star (ohsStep n m p).unitary = (ohsStep n m p).unitary := by
  rw [ohsStep, oneHotSplit_unitary, star_embed2, star_ohsMat]

lemma ohsStep_unitary_mul_self {n m : ℕ} (p : OhsPair m) :
    (ohsStep n m p).unitary * (ohsStep n m p).unitary = 1 := by
  rw [ohsStep, oneHotSplit_unitary, embed2_mul, ohsMat_mul_self, embed2_one]

lemma ohsStep_size (n m : ℕ) (p : OhsPair m) :
    (ohsStep n m p).size = 31 :=
  oneHotSplit_size _ _ _

def ohsListCircuit (n m : ℕ) : List (OhsPair m) → Circuit htcxGateSet (n + (1 + 2 * m))
  | [] => []
  | p :: L => ohsStep n m p ++ ohsListCircuit n m L

lemma ohsListCircuit_append (n m : ℕ) (L1 L2 : List (OhsPair m)) :
    ohsListCircuit n m (L1 ++ L2) = ohsListCircuit n m L1 ++ ohsListCircuit n m L2 := by
  induction L1 with
  | nil => rfl
  | cons p L1 ih =>
    simp only [List.cons_append, ohsListCircuit, ih, List.append_assoc]

lemma ohsListCircuit_size (n m : ℕ) (L : List (OhsPair m)) :
    (ohsListCircuit n m L).size = 31 * L.length := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [ohsListCircuit, circuit_size_append, ohsStep_size, ih, List.length_cons]
    ring

lemma ohsListCircuit_reverse_unitary (n m : ℕ) (L : List (OhsPair m)) :
    (ohsListCircuit n m L.reverse).unitary = star (ohsListCircuit n m L).unitary := by
  induction L with
  | nil => simp [ohsListCircuit]
  | cons p L ih =>
    simp only [List.reverse_cons, ohsListCircuit_append, ohsListCircuit,
      circuit_unitary_append, circuit_unitary_nil, Matrix.one_mul,
      StarMul.star_mul, ih, star_ohsStep_unitary]

lemma ohsListCircuit_unitary_mul_reverse (n m : ℕ) (L : List (OhsPair m)) :
    (ohsListCircuit n m L).unitary * (ohsListCircuit n m L.reverse).unitary = 1 := by
  induction L with
  | nil => simp [ohsListCircuit]
  | cons p L ih =>
    simp only [List.reverse_cons, ohsListCircuit_append, ohsListCircuit,
      circuit_unitary_append, circuit_unitary_nil, Matrix.one_mul]
    calc ((ohsListCircuit n m L).unitary * (ohsStep n m p).unitary) *
          ((ohsStep n m p).unitary * (ohsListCircuit n m L.reverse).unitary)
        = (ohsListCircuit n m L).unitary *
            (((ohsStep n m p).unitary * (ohsStep n m p).unitary) *
            (ohsListCircuit n m L.reverse).unitary) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ohsStep_unitary_mul_self, Matrix.one_mul, ih]

lemma ohsListCircuit_reverse_mul_unitary (n m : ℕ) (L : List (OhsPair m)) :
    (ohsListCircuit n m L.reverse).unitary * (ohsListCircuit n m L).unitary = 1 := by
  have h := ohsListCircuit_unitary_mul_reverse n m L.reverse
  simpa [List.reverse_reverse] using h

noncomputable def ohsListVec {m : ℕ} :
    List (OhsPair m) → (Fin (2 * m) → ℂ) → (Fin (2 * m) → ℂ)
  | [], β => β
  | p :: L, β => ohsListVec L (ohsVecStep p.1.1 p.1.2 β)

lemma ohsListVec_append {m : ℕ} (L1 L2 : List (OhsPair m)) (β : Fin (2 * m) → ℂ) :
    ohsListVec (L1 ++ L2) β = ohsListVec L2 (ohsListVec L1 β) := by
  induction L1 generalizing β with
  | nil => rfl
  | cons p L1 ih => exact ih (ohsVecStep p.1.1 p.1.2 β)

lemma act_ohsListCircuit_embedOH {n m : ℕ} (y : Qubits (n + 1))
    (L : List (OhsPair m)) (β : Fin (2 * m) → ℂ) :
    act (ohsListCircuit n m L).unitary (embedOH y β) =
      embedOH y (ohsListVec L β) := by
  induction L generalizing β with
  | nil => simp [ohsListCircuit, ohsListVec, act_one]
  | cons p L ih =>
    rw [ohsListCircuit, act_circuit_unitary_append, act_ohsStep_embedOH, ih, ohsListVec]

lemma act_ket_ofLp {N : ℕ} (U : Matrix (Qubits N) (Qubits N) ℂ) (z w : Qubits N) :
    (act U (ket z)).ofLp w = U w z := by
  dsimp [act, ket]
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single z]
  · simp
  · intro x _ hx; simp [hx]
  · intro habs; exact False.elim (habs (Finset.mem_univ _))

lemma act_star_ket_ofLp {N : ℕ} (U : Matrix (Qubits N) (Qubits N) ℂ) (z w : Qubits N) :
    (act (star U) (ket z)).ofLp w = star ((act U (ket w)).ofLp z) := by
  rw [act_ket_ofLp, act_ket_ofLp, Matrix.star_apply]

lemma act_star_embedOH_ofLp {n m : ℕ}
    (U : Matrix (Qubits (n + (1 + 2 * m))) (Qubits (n + (1 + 2 * m))) ℂ)
    (y : Qubits (n + 1)) (k0 : Fin (2 * m)) (β : Fin (2 * m) → ℂ) :
    (act (star U) (embedOH y β)).ofLp (vecMW y (oneHotBits k0)) =
      ∑ j : Fin (2 * m),
        star ((act U (ketOH y k0)).ofLp (vecMW y (oneHotBits j))) * β j := by
  unfold embedOH ketOH ketMW
  rw [act_sum, sum_ofLp_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [act_smul, smul_ofLp_apply, act_star_ket_ofLp]
  ring

def reflOH (n m : ℕ) (L : List (OhsPair m)) (k0 : Fin (2 * m)) :
    Circuit htcxGateSet (n + (1 + 2 * m)) :=
  ohsListCircuit n m L.reverse ++ gateZ (workWire n m k0) ++ ohsListCircuit n m L

lemma reflOH_size (n m : ℕ) (L : List (OhsPair m)) (k0 : Fin (2 * m)) :
    (reflOH n m L k0).size = 62 * L.length + 4 := by
  dsimp [reflOH]
  rw [circuit_size_append, circuit_size_append, ohsListCircuit_size,
    ohsListCircuit_size, List.length_reverse, gateZ_size]
  ring

lemma act_reflOH_embedOH {n m : ℕ} (y : Qubits (n + 1))
    (L : List (OhsPair m)) (k0 : Fin (2 * m)) (γ : Fin (2 * m) → ℂ)
    (hγ : act (ohsListCircuit n m L).unitary (ketOH y k0) = embedOH y γ)
    (β : Fin (2 * m) → ℂ) :
    act (reflOH n m L k0).unitary (embedOH y β) =
      embedOH y (fun k => β k - (2 * ∑ j : Fin (2 * m), star (γ j) * β j) * γ k) := by
  dsimp [reflOH]
  set α := ohsListVec L.reverse β
  have hα : act (ohsListCircuit n m L.reverse).unitary (embedOH y β) = embedOH y α :=
    act_ohsListCircuit_embedOH y L.reverse β
  have hα0 : α k0 = ∑ j : Fin (2 * m), star (γ j) * β j := by
    rw [← embedOH_ofLp_vecMW_oneHotBits y α k0, ← hα, ohsListCircuit_reverse_unitary,
      act_star_embedOH_ofLp, hγ]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [embedOH_ofLp_vecMW_oneHotBits]
  have hrecover : act (ohsListCircuit n m L).unitary (embedOH y α) = embedOH y β := by
    rw [← hα, ← act_mul, ohsListCircuit_unitary_mul_reverse, act_one]
  rw [act_circuit_unitary_append, act_circuit_unitary_append, hα,
    act_gateZ_embedOH, act_sub, hrecover, act_smul, hγ, hα0,
    ← embedOH_smul, ← embedOH_sub]
  rfl

lemma act_grover5_embedOH {n m : ℕ} (y : Qubits (n + 1))
    (L : List (OhsPair m)) (k0 : Fin (2 * m)) (γ : Fin (2 * m) → ℂ)
    (hγ : act (ohsListCircuit n m L).unitary (ketOH y k0) = embedOH y γ)
    (hγ_star : ∀ k, star (γ k) = γ k)
    (hγ_norm : ∑ k : Fin (2 * m), γ k * γ k = 1)
    {cD cDinv : Circuit htcxGateSet (n + (1 + 2 * m))}
    {evD evDinv : Qubits (n + (1 + 2 * m)) → ℂ}
    (hcD : IsDiagCircuit cD evD) (hcDinv : IsDiagCircuit cDinv evDinv)
    (d : Fin (2 * m) → ℂ)
    (hd : ∀ k, evD (vecMW y (oneHotBits k)) = d k)
    (hdinv : ∀ k, evDinv (vecMW y (oneHotBits k)) = star (d k))
    (hd_unit : ∀ k, star (d k) * d k = 1) :
    let μ := ∑ j : Fin (2 * m), (γ j * γ j) * d j
    act (cD ++ reflOH n m L k0 ++ cDinv ++ reflOH n m L k0 ++ cD).unitary (embedOH y γ) =
      embedOH y (fun k => ((4 * μ * star μ - 1) * d k - 2 * μ) * γ k) := by
  intro μ
  have hstep1 : act cD.unitary (embedOH y γ) = embedOH y (fun k => d k * γ k) := by
    rw [hcD.act_embedOH]
    congr 1; funext k; rw [hd k]
  have hsum1 : ∑ j : Fin (2 * m), star (γ j) * (d j * γ j) = μ := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hγ_star j]; ring
  have hstep2 : act (reflOH n m L k0).unitary (embedOH y (fun k => d k * γ k)) =
      embedOH y (fun k => (d k - 2 * μ) * γ k) := by
    rw [act_reflOH_embedOH y L k0 γ hγ, hsum1]
    congr 1; funext k; ring
  have hstep3 : act cDinv.unitary (embedOH y (fun k => (d k - 2 * μ) * γ k)) =
      embedOH y (fun k => (1 - 2 * μ * star (d k)) * γ k) := by
    rw [hcDinv.act_embedOH]
    congr 1; funext k
    rw [hdinv k]
    calc star (d k) * ((d k - 2 * μ) * γ k)
        = (star (d k) * d k - 2 * μ * star (d k)) * γ k := by ring
      _ = (1 - 2 * μ * star (d k)) * γ k := by rw [hd_unit k]
  have hsum2 : ∑ j : Fin (2 * m), star (γ j) * ((1 - 2 * μ * star (d j)) * γ j) =
      1 - 2 * μ * star μ := by
    have hsplit : ∀ j : Fin (2 * m),
        star (γ j) * ((1 - 2 * μ * star (d j)) * γ j) =
          (γ j * γ j) - (2 * μ) * ((γ j * γ j) * star (d j)) := by
      intro j; rw [hγ_star j]; ring
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hγ_norm]
    congr 2
    rw [star_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [star_mul, star_mul, hγ_star j]
    ring
  have hstep4 : act (reflOH n m L k0).unitary
        (embedOH y (fun k => (1 - 2 * μ * star (d k)) * γ k)) =
      embedOH y (fun k => ((4 * μ * star μ - 1) - 2 * μ * star (d k)) * γ k) := by
    rw [act_reflOH_embedOH y L k0 γ hγ, hsum2]
    congr 1; funext k; ring
  have hstep5 : act cD.unitary
        (embedOH y (fun k => ((4 * μ * star μ - 1) - 2 * μ * star (d k)) * γ k)) =
      embedOH y (fun k => ((4 * μ * star μ - 1) * d k - 2 * μ) * γ k) := by
    rw [hcD.act_embedOH]
    congr 1; funext k
    rw [hd k]
    calc d k * (((4 * μ * star μ - 1) - 2 * μ * star (d k)) * γ k)
        = ((4 * μ * star μ - 1) * d k - 2 * μ * (star (d k) * d k)) * γ k := by ring
      _ = ((4 * μ * star μ - 1) * d k - 2 * μ) * γ k := by rw [hd_unit k]; ring
  rw [act_circuit_unitary_append, act_circuit_unitary_append, act_circuit_unitary_append,
    act_circuit_unitary_append, hstep1, hstep2, hstep3, hstep4, hstep5]

def chainPairs (m : ℕ) : ℕ → List (OhsPair m)
  | 0 => []
  | j + 1 =>
    if h : j + 1 < m then
      chainPairs m j ++
        [⟨(⟨2 * j, by omega⟩, ⟨2 * (j + 1), by omega⟩), by
          intro heq; have := congrArg Fin.val heq; dsimp at this; omega⟩]
    else []

def pairSplitPairs (m : ℕ) : ℕ → List (OhsPair m)
  | 0 => []
  | j + 1 =>
    if h : j < m then
      pairSplitPairs m j ++
        [⟨(⟨2 * j, by omega⟩, ⟨2 * j + 1, by omega⟩), by
          intro heq; have := congrArg Fin.val heq; dsimp at this; omega⟩]
    else []

def prepPairs (m : ℕ) : List (OhsPair m) :=
  chainPairs m (m - 1) ++ pairSplitPairs m m

lemma chainPairs_length (m : ℕ) : ∀ j : ℕ, j < m → (chainPairs m j).length = j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [chainPairs, dif_pos hj, List.length_append,
      chainPairs_length m j (Nat.lt_of_succ_lt hj), List.length_singleton]

lemma pairSplitPairs_length (m : ℕ) : ∀ j : ℕ, j ≤ m → (pairSplitPairs m j).length = j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [pairSplitPairs, dif_pos (by omega : j < m), List.length_append,
      pairSplitPairs_length m j (Nat.le_of_succ_le hj), List.length_singleton]

lemma prepPairs_length {m : ℕ} (hm : 1 ≤ m) :
    (prepPairs m).length = 2 * m - 1 := by
  dsimp [prepPairs]
  rw [List.length_append, chainPairs_length m (m - 1) (by omega),
    pairSplitPairs_length m m le_rfl]
  omega

noncomputable def chainVec (m j : ℕ) (k : Fin (2 * m)) : ℂ :=
  if k.1 % 2 = 0 then
    if k.1 / 2 < j then ((Real.sqrt 2)⁻¹ : ℂ) ^ (k.1 / 2 + 1)
    else if k.1 / 2 = j then ((Real.sqrt 2)⁻¹ : ℂ) ^ j
    else 0
  else 0

lemma embedOH_chainVec_zero {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1)) :
    embedOH y (chainVec m 0) = ketOH y ⟨0, by omega⟩ := by
  have h0 : chainVec m 0 = fun k : Fin (2 * m) => if k = ⟨0, by omega⟩ then (1 : ℂ) else 0 := by
    funext k
    dsimp [chainVec]
    by_cases hk : k = ⟨0, by omega⟩
    · subst hk; simp
    · have hne : k.1 ≠ 0 := fun h => hk (Fin.ext h)
      rw [if_neg hk]
      by_cases hmod : k.1 % 2 = 0
      · have hdiv : k.1 / 2 ≠ 0 := by omega
        simp [hmod, hdiv]
      · simp [hmod]
  rw [h0, embedOH_single, one_smul]

lemma ohsVecStep_chainVec {m j : ℕ} (hj : j + 1 < m) :
    ohsVecStep (⟨2 * j, by omega⟩ : Fin (2 * m)) (⟨2 * (j + 1), by omega⟩ : Fin (2 * m))
        (chainVec m j) =
      chainVec m (j + 1) := by
  funext k
  set a : Fin (2 * m) := ⟨2 * j, by omega⟩
  set b : Fin (2 * m) := ⟨2 * (j + 1), by omega⟩
  have ha : chainVec m j a = ((Real.sqrt 2)⁻¹ : ℂ) ^ j := by
    dsimp [chainVec, a]
    have h1 : (2 * j) % 2 = 0 := by omega
    have h2 : (2 * j) / 2 = j := by omega
    simp [h1, h2]
  have hb : chainVec m j b = 0 := by
    dsimp [chainVec, b]
    have h1 : (2 * (j + 1)) % 2 = 0 := by omega
    have h2 : (2 * (j + 1)) / 2 = j + 1 := by omega
    rw [if_pos h1, h2, if_neg (by omega), if_neg (by omega)]
  dsimp [ohsVecStep]
  by_cases hka : k = a
  · subst hka
    rw [if_pos rfl, ha, hb]
    dsimp [chainVec, a]
    have h1 : (2 * j) % 2 = 0 := by omega
    have h2 : (2 * j) / 2 = j := by omega
    rw [if_pos h1, h2, if_pos (Nat.lt_succ_self j), pow_succ']
    ring
  · rw [if_neg hka]
    by_cases hkb : k = b
    · subst hkb
      rw [if_pos rfl, ha, hb]
      dsimp [chainVec, b]
      have h1 : (2 * (j + 1)) % 2 = 0 := by omega
      have h2 : (2 * (j + 1)) / 2 = j + 1 := by omega
      rw [if_pos h1, h2, if_neg (lt_irrefl (j + 1)), if_pos rfl, pow_succ']
      ring
    · rw [if_neg hkb]
      dsimp [chainVec]
      by_cases hmod : k.1 % 2 = 0
      · rw [if_pos hmod, if_pos hmod]
        have hdiv_ne_j : k.1 / 2 ≠ j := by
          intro hd; apply hka; ext; dsimp [a]; omega
        have hdiv_ne_j1 : k.1 / 2 ≠ j + 1 := by
          intro hd; apply hkb; ext; dsimp [b]; omega
        by_cases hlt : k.1 / 2 < j
        · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
        · have hlt1 : ¬ (k.1 / 2 < j + 1) := by omega
          rw [if_neg hlt, if_neg hdiv_ne_j, if_neg hlt1, if_neg hdiv_ne_j1]
      · rw [if_neg hmod, if_neg hmod]

lemma ohsListVec_chainPairs (m : ℕ) :
    ∀ j : ℕ, j < m → ohsListVec (chainPairs m j) (chainVec m 0) = chainVec m j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [chainPairs, dif_pos hj, ohsListVec_append,
      ohsListVec_chainPairs m j (Nat.lt_of_succ_lt hj),
      ohsListVec, ohsListVec, ohsVecStep_chainVec hj]

lemma chainVec_pred_eq {m : ℕ} (hm : 1 ≤ m) (k : Fin (2 * m)) :
    chainVec m (m - 1) k =
      if k.1 % 2 = 0 then ((Real.sqrt 2)⁻¹ : ℂ) ^ (dyadicExp m (k.1 / 2) - 1) else 0 := by
  have hk : k.1 < 2 * m := k.2
  dsimp [chainVec, dyadicExp]
  split_ifs <;> first | rfl | (congr 1; omega) | omega

noncomputable def pairVec (m j : ℕ) (k : Fin (2 * m)) : ℂ :=
  if k.1 / 2 < j then (chiVec m k : ℂ) else chainVec m (m - 1) k

lemma ohsVecStep_pairVec {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) :
    ohsVecStep (⟨2 * j, by omega⟩ : Fin (2 * m)) (⟨2 * j + 1, by omega⟩ : Fin (2 * m))
        (pairVec m j) =
      pairVec m (j + 1) := by
  funext k
  set a : Fin (2 * m) := ⟨2 * j, by omega⟩
  set b : Fin (2 * m) := ⟨2 * j + 1, by omega⟩
  have ha : pairVec m j a = ((Real.sqrt 2)⁻¹ : ℂ) ^ (dyadicExp m j - 1) := by
    dsimp [pairVec, a]
    have hdiv : (2 * j) / 2 = j := by omega
    have hmod : (2 * j) % 2 = 0 := by omega
    rw [hdiv, if_neg (lt_irrefl j), chainVec_pred_eq hm a]
    dsimp [a]
    rw [if_pos hmod, hdiv]
  have hb : pairVec m j b = 0 := by
    dsimp [pairVec, b]
    have hdiv : (2 * j + 1) / 2 = j := by omega
    have hmod : (2 * j + 1) % 2 ≠ 0 := by omega
    rw [hdiv, if_neg (lt_irrefl j), chainVec_pred_eq hm b]
    dsimp [b]
    rw [if_neg hmod]
  have hpow : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) ^ (dyadicExp m j - 1) =
      ((Real.sqrt 2)⁻¹ : ℂ) ^ (dyadicExp m j) := by
    have h1 := one_le_dyadicExp hm j
    rw [← pow_succ', Nat.sub_add_cancel h1]
  dsimp [ohsVecStep]
  by_cases hka : k = a
  · subst hka
    rw [if_pos rfl, ha, hb, mul_zero, add_zero, hpow]
    dsimp [pairVec, chiVec, a]
    have hdiv : (2 * j) / 2 = j := by omega
    rw [hdiv, if_pos (Nat.lt_succ_self j)]
    push_cast
    rfl
  · rw [if_neg hka]
    by_cases hkb : k = b
    · subst hkb
      rw [if_pos rfl, ha, hb, mul_zero, sub_zero, hpow]
      dsimp [pairVec, chiVec, b]
      have hdiv : (2 * j + 1) / 2 = j := by omega
      rw [hdiv, if_pos (Nat.lt_succ_self j)]
      push_cast
      rfl
    · rw [if_neg hkb]
      dsimp [pairVec]
      have hdiv_ne : k.1 / 2 ≠ j := by
        intro hd
        by_cases hmod : k.1 % 2 = 0
        · apply hka; ext; dsimp [a]; omega
        · apply hkb; ext; dsimp [b]; omega
      by_cases hlt : k.1 / 2 < j
      · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
      · have hlt1 : ¬ (k.1 / 2 < j + 1) := by omega
        rw [if_neg hlt, if_neg hlt1]

lemma ohsListVec_pairSplitPairs {m : ℕ} (hm : 1 ≤ m) :
    ∀ j : ℕ, j ≤ m →
      ohsListVec (pairSplitPairs m j) (chainVec m (m - 1)) = pairVec m j
  | 0, _ => by
    funext k
    simp [ohsListVec, pairSplitPairs, pairVec]
  | j + 1, hj => by
    have hlt : j < m := hj
    rw [pairSplitPairs, dif_pos hlt, ohsListVec_append,
      ohsListVec_pairSplitPairs hm j (Nat.le_of_succ_le hj),
      ohsListVec, ohsListVec, ohsVecStep_pairVec hm hlt]

lemma act_prepPairs_ketOH {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1)) :
    act (ohsListCircuit n m (prepPairs m)).unitary (ketOH y ⟨0, by omega⟩) =
      embedOH y (fun k => (chiVec m k : ℂ)) := by
  rw [← embedOH_chainVec_zero hm y, act_ohsListCircuit_embedOH, prepPairs,
    ohsListVec_append, ohsListVec_chainPairs m (m - 1) (by omega),
    ohsListVec_pairSplitPairs hm m le_rfl]
  congr 1
  funext k
  dsimp [pairVec]
  rw [if_pos (by have := k.2; omega)]

noncomputable def diagPairStep (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) (r : ℕ) (hr : r < m) :
    Circuit htcxGateSet (n + (1 + 2 * m)) :=
  let w_even := workWire n m ⟨2 * r, by omega⟩
  let w_odd := workWire n m ⟨2 * r + 1, by omega⟩
  (if greedyBit (Real.cos (θ / 2) / 2) r then [] else gateZ w_even) ++
    (gateCZ (mainWire n m t) w_odd (mainWire_ne_workWire t _) ++
      (if greedyBit (Real.sin (θ / 2) / 2) r then gateSdag w_odd else gateS w_odd))

noncomputable def diagPairInvStep (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) (r : ℕ) (hr : r < m) :
    Circuit htcxGateSet (n + (1 + 2 * m)) :=
  let w_even := workWire n m ⟨2 * r, by omega⟩
  let w_odd := workWire n m ⟨2 * r + 1, by omega⟩
  (if greedyBit (Real.cos (θ / 2) / 2) r then [] else gateZ w_even) ++
    (gateCZ (mainWire n m t) w_odd (mainWire_ne_workWire t _) ++
      (if greedyBit (Real.sin (θ / 2) / 2) r then gateS w_odd else gateSdag w_odd))

lemma diagPairStep_size_le (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) (r : ℕ) (hr : r < m) :
    (diagPairStep n m t θ r hr).size ≤ 17 := by
  dsimp [diagPairStep]
  rw [circuit_size_append, circuit_size_append, gateCZ_size]
  have hnil : Circuit.size ([] : Circuit htcxGateSet (n + (1 + 2 * m))) = 0 := rfl
  split_ifs <;> simp only [hnil, gateZ_size, gateSdag_size, gateS_size] <;> omega

lemma diagPairInvStep_size_le (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) (r : ℕ) (hr : r < m) :
    (diagPairInvStep n m t θ r hr).size ≤ 17 := by
  dsimp [diagPairInvStep]
  rw [circuit_size_append, circuit_size_append, gateCZ_size]
  have hnil : Circuit.size ([] : Circuit htcxGateSet (n + (1 + 2 * m))) = 0 := rfl
  split_ifs <;> simp only [hnil, gateZ_size, gateSdag_size, gateS_size] <;> omega

noncomputable def evPair (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) (r : ℕ) (hr : r < m)
    (z : Qubits (n + (1 + 2 * m))) : ℂ :=
  let w_even := workWire n m ⟨2 * r, by omega⟩
  let w_odd := workWire n m ⟨2 * r + 1, by omega⟩
  (if greedyBit (Real.cos (θ / 2) / 2) r then 1 else (if z w_even then -1 else 1)) *
    ((if z (mainWire n m t) && z w_odd then -1 else 1) *
      (if greedyBit (Real.sin (θ / 2) / 2) r then (if z w_odd then -Complex.I else 1)
       else (if z w_odd then Complex.I else 1)))

noncomputable def evPairInv (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) (r : ℕ) (hr : r < m)
    (z : Qubits (n + (1 + 2 * m))) : ℂ :=
  let w_even := workWire n m ⟨2 * r, by omega⟩
  let w_odd := workWire n m ⟨2 * r + 1, by omega⟩
  (if greedyBit (Real.cos (θ / 2) / 2) r then 1 else (if z w_even then -1 else 1)) *
    ((if z (mainWire n m t) && z w_odd then -1 else 1) *
      (if greedyBit (Real.sin (θ / 2) / 2) r then (if z w_odd then Complex.I else 1)
       else (if z w_odd then -Complex.I else 1)))

lemma isDiagCircuit_diagPairStep (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) (r : ℕ) (hr : r < m) :
    IsDiagCircuit (diagPairStep n m t θ r hr) (evPair n m t θ r hr) := by
  dsimp [diagPairStep, evPair]
  refine IsDiagCircuit.append ?_ (IsDiagCircuit.append (isDiagCircuit_gateCZ _ _ _) ?_)
  · by_cases hc : greedyBit (Real.cos (θ / 2) / 2) r
    · simp only [hc, ↓reduceIte]; exact isDiagCircuit_nil
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact isDiagCircuit_gateZ _
  · by_cases hs : greedyBit (Real.sin (θ / 2) / 2) r
    · simp only [hs, ↓reduceIte]; exact isDiagCircuit_gateSdag _
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]; exact isDiagCircuit_gateS _

lemma isDiagCircuit_diagPairInvStep (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) (r : ℕ) (hr : r < m) :
    IsDiagCircuit (diagPairInvStep n m t θ r hr) (evPairInv n m t θ r hr) := by
  dsimp [diagPairInvStep, evPairInv]
  refine IsDiagCircuit.append ?_ (IsDiagCircuit.append (isDiagCircuit_gateCZ _ _ _) ?_)
  · by_cases hc : greedyBit (Real.cos (θ / 2) / 2) r
    · simp only [hc, ↓reduceIte]; exact isDiagCircuit_nil
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact isDiagCircuit_gateZ _
  · by_cases hs : greedyBit (Real.sin (θ / 2) / 2) r
    · simp only [hs, ↓reduceIte]; exact isDiagCircuit_gateS _
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]; exact isDiagCircuit_gateSdag _

noncomputable def targetEig {n m : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ)
    (k : Fin (2 * m)) : ℂ :=
  if k.1 % 2 = 0 then
    (signOfBool (greedyBit (Real.cos (θ / 2) / 2) (k.1 / 2)) : ℂ)
  else
    (if y t then Complex.I else -Complex.I) *
      (signOfBool (greedyBit (Real.sin (θ / 2) / 2) (k.1 / 2)) : ℂ)

lemma star_targetEig_mul_self {n m : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ)
    (k : Fin (2 * m)) :
    star (targetEig y t θ k) * targetEig y t θ k = 1 := by
  dsimp [targetEig]
  by_cases hmod : k.1 % 2 = 0
  · rw [if_pos hmod]
    cases greedyBit (Real.cos (θ / 2) / 2) (k.1 / 2) <;> simp [signOfBool]
  · rw [if_neg hmod]
    cases y t <;> cases greedyBit (Real.sin (θ / 2) / 2) (k.1 / 2) <;>
      simp [signOfBool] <;> { ring_nf; rw [Complex.I_sq]; ring }

lemma norm_targetEig {n m : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ)
    (k : Fin (2 * m)) :
    ‖targetEig y t θ k‖ = 1 := by
  dsimp [targetEig]
  by_cases hmod : k.1 % 2 = 0
  · rw [if_pos hmod]
    cases greedyBit (Real.cos (θ / 2) / 2) (k.1 / 2) <;> simp [signOfBool]
  · rw [if_neg hmod]
    cases y t <;> cases greedyBit (Real.sin (θ / 2) / 2) (k.1 / 2) <;> simp [signOfBool]

lemma evPair_vecMW_oneHotBits {n m : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ)
    (r : ℕ) (hr : r < m) (k : Fin (2 * m)) :
    evPair n m t θ r hr (vecMW y (oneHotBits k)) =
      if k.1 / 2 = r then targetEig y t θ k else 1 := by
  dsimp [evPair, targetEig]
  rw [vecMW_main, vecMW_work, vecMW_work]
  by_cases hdiv : k.1 / 2 = r
  · rw [if_pos hdiv, hdiv]
    by_cases hmod : k.1 % 2 = 0
    · have hk_even : (⟨2 * r, by omega⟩ : Fin (2 * m)) = k := by ext; dsimp; omega
      have hk_odd : (⟨2 * r + 1, by omega⟩ : Fin (2 * m)) ≠ k := by
        intro heq; have := congrArg Fin.val heq; dsimp at this; omega
      rw [if_pos hmod, hk_even, oneHotBits_self, oneHotBits_of_ne hk_odd, Bool.and_false]
      cases greedyBit (Real.cos (θ / 2) / 2) r <;> simp [signOfBool]
    · have hk_even : (⟨2 * r, by omega⟩ : Fin (2 * m)) ≠ k := by
        intro heq; have := congrArg Fin.val heq; dsimp at this; omega
      have hk_odd : (⟨2 * r + 1, by omega⟩ : Fin (2 * m)) = k := by ext; dsimp; omega
      rw [if_neg hmod, oneHotBits_of_ne hk_even, hk_odd, oneHotBits_self, Bool.and_true]
      cases y t <;> cases greedyBit (Real.sin (θ / 2) / 2) r <;> simp [signOfBool]
  · rw [if_neg hdiv]
    have hk_even : (⟨2 * r, by omega⟩ : Fin (2 * m)) ≠ k := by
      intro heq; have := congrArg Fin.val heq; dsimp at this; omega
    have hk_odd : (⟨2 * r + 1, by omega⟩ : Fin (2 * m)) ≠ k := by
      intro heq; have := congrArg Fin.val heq; dsimp at this; omega
    rw [oneHotBits_of_ne hk_even, oneHotBits_of_ne hk_odd, Bool.and_false]
    simp

lemma evPairInv_vecMW_oneHotBits {n m : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ)
    (r : ℕ) (hr : r < m) (k : Fin (2 * m)) :
    evPairInv n m t θ r hr (vecMW y (oneHotBits k)) =
      if k.1 / 2 = r then star (targetEig y t θ k) else 1 := by
  dsimp [evPairInv, targetEig]
  rw [vecMW_main, vecMW_work, vecMW_work]
  by_cases hdiv : k.1 / 2 = r
  · rw [if_pos hdiv, hdiv]
    by_cases hmod : k.1 % 2 = 0
    · have hk_even : (⟨2 * r, by omega⟩ : Fin (2 * m)) = k := by ext; dsimp; omega
      have hk_odd : (⟨2 * r + 1, by omega⟩ : Fin (2 * m)) ≠ k := by
        intro heq; have := congrArg Fin.val heq; dsimp at this; omega
      rw [if_pos hmod, hk_even, oneHotBits_self, oneHotBits_of_ne hk_odd, Bool.and_false]
      cases greedyBit (Real.cos (θ / 2) / 2) r <;> simp [signOfBool]
    · have hk_even : (⟨2 * r, by omega⟩ : Fin (2 * m)) ≠ k := by
        intro heq; have := congrArg Fin.val heq; dsimp at this; omega
      have hk_odd : (⟨2 * r + 1, by omega⟩ : Fin (2 * m)) = k := by ext; dsimp; omega
      rw [if_neg hmod, oneHotBits_of_ne hk_even, hk_odd, oneHotBits_self, Bool.and_true]
      cases y t <;> cases greedyBit (Real.sin (θ / 2) / 2) r <;> simp [signOfBool]
  · rw [if_neg hdiv]
    have hk_even : (⟨2 * r, by omega⟩ : Fin (2 * m)) ≠ k := by
      intro heq; have := congrArg Fin.val heq; dsimp at this; omega
    have hk_odd : (⟨2 * r + 1, by omega⟩ : Fin (2 * m)) ≠ k := by
      intro heq; have := congrArg Fin.val heq; dsimp at this; omega
    rw [oneHotBits_of_ne hk_even, oneHotBits_of_ne hk_odd, Bool.and_false]
    simp

noncomputable def diagChain (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    (j : ℕ) → j ≤ m → Circuit htcxGateSet (n + (1 + 2 * m))
  | 0, _ => []
  | j + 1, hj => diagChain n m t θ j (Nat.le_of_succ_le hj) ++ diagPairStep n m t θ j hj

noncomputable def diagInvChain (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    (j : ℕ) → j ≤ m → Circuit htcxGateSet (n + (1 + 2 * m))
  | 0, _ => []
  | j + 1, hj => diagInvChain n m t θ j (Nat.le_of_succ_le hj) ++ diagPairInvStep n m t θ j hj

noncomputable def evChain (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    (j : ℕ) → j ≤ m → Qubits (n + (1 + 2 * m)) → ℂ
  | 0, _, _ => 1
  | j + 1, hj, z => evChain n m t θ j (Nat.le_of_succ_le hj) z * evPair n m t θ j hj z

noncomputable def evInvChain (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    (j : ℕ) → j ≤ m → Qubits (n + (1 + 2 * m)) → ℂ
  | 0, _, _ => 1
  | j + 1, hj, z => evInvChain n m t θ j (Nat.le_of_succ_le hj) z * evPairInv n m t θ j hj z

lemma isDiagCircuit_diagChain (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    ∀ (j : ℕ) (hj : j ≤ m), IsDiagCircuit (diagChain n m t θ j hj) (evChain n m t θ j hj)
  | 0, _ => isDiagCircuit_nil
  | j + 1, hj =>
    (isDiagCircuit_diagChain n m t θ j (Nat.le_of_succ_le hj)).append
      (isDiagCircuit_diagPairStep n m t θ j hj)

lemma isDiagCircuit_diagInvChain (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    ∀ (j : ℕ) (hj : j ≤ m), IsDiagCircuit (diagInvChain n m t θ j hj) (evInvChain n m t θ j hj)
  | 0, _ => isDiagCircuit_nil
  | j + 1, hj =>
    (isDiagCircuit_diagInvChain n m t θ j (Nat.le_of_succ_le hj)).append
      (isDiagCircuit_diagPairInvStep n m t θ j hj)

lemma diagChain_size_le (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    ∀ (j : ℕ) (hj : j ≤ m), (diagChain n m t θ j hj).size ≤ 17 * j
  | 0, _ => by simp [diagChain, Circuit.size]
  | j + 1, hj => by
    rw [diagChain, circuit_size_append, Nat.mul_succ]
    exact Nat.add_le_add (diagChain_size_le n m t θ j (Nat.le_of_succ_le hj))
      (diagPairStep_size_le n m t θ j hj)

lemma diagInvChain_size_le (n m : ℕ) (t : Fin (n + 1)) (θ : ℝ) :
    ∀ (j : ℕ) (hj : j ≤ m), (diagInvChain n m t θ j hj).size ≤ 17 * j
  | 0, _ => by simp [diagInvChain, Circuit.size]
  | j + 1, hj => by
    rw [diagInvChain, circuit_size_append, Nat.mul_succ]
    exact Nat.add_le_add (diagInvChain_size_le n m t θ j (Nat.le_of_succ_le hj))
      (diagPairInvStep_size_le n m t θ j hj)

lemma evChain_vecMW_oneHotBits (n m : ℕ) (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ)
    (k : Fin (2 * m)) :
    ∀ (j : ℕ) (hj : j ≤ m),
      evChain n m t θ j hj (vecMW y (oneHotBits k)) =
        if k.1 / 2 < j then targetEig y t θ k else 1
  | 0, _ => by simp [evChain]
  | j + 1, hj => by
    rw [evChain, evChain_vecMW_oneHotBits n m y t θ k j (Nat.le_of_succ_le hj),
      evPair_vecMW_oneHotBits]
    by_cases hlt : k.1 / 2 < j
    · have hne : k.1 / 2 ≠ j := by omega
      rw [if_pos hlt, if_neg hne, mul_one, if_pos (Nat.lt_succ_of_lt hlt)]
    · rw [if_neg hlt, one_mul]
      by_cases heq : k.1 / 2 = j
      · rw [if_pos heq, if_pos (by omega)]
      · rw [if_neg heq, if_neg (by omega)]

lemma evInvChain_vecMW_oneHotBits (n m : ℕ) (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ)
    (k : Fin (2 * m)) :
    ∀ (j : ℕ) (hj : j ≤ m),
      evInvChain n m t θ j hj (vecMW y (oneHotBits k)) =
        if k.1 / 2 < j then star (targetEig y t θ k) else 1
  | 0, _ => by simp [evInvChain]
  | j + 1, hj => by
    rw [evInvChain, evInvChain_vecMW_oneHotBits n m y t θ k j (Nat.le_of_succ_le hj),
      evPairInv_vecMW_oneHotBits]
    by_cases hlt : k.1 / 2 < j
    · have hne : k.1 / 2 ≠ j := by omega
      rw [if_pos hlt, if_neg hne, mul_one, if_pos (Nat.lt_succ_of_lt hlt)]
    · rw [if_neg hlt, one_mul]
      by_cases heq : k.1 / 2 = j
      · rw [if_pos heq, if_pos (by omega)]
      · rw [if_neg heq, if_neg (by omega)]

lemma evChain_top_vecMW_oneHotBits {n m : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ)
    (k : Fin (2 * m)) :
    evChain n m t θ m le_rfl (vecMW y (oneHotBits k)) = targetEig y t θ k := by
  rw [evChain_vecMW_oneHotBits, if_pos (by have := k.2; omega)]

lemma evInvChain_top_vecMW_oneHotBits {n m : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ)
    (k : Fin (2 * m)) :
    evInvChain n m t θ m le_rfl (vecMW y (oneHotBits k)) = star (targetEig y t θ k) := by
  rw [evInvChain_vecMW_oneHotBits, if_pos (by have := k.2; omega)]

noncomputable def targetPhase {n : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ) : ℂ :=
  (Real.cos (θ / 2) : ℂ) + (if y t then Complex.I else -Complex.I) * (Real.sin (θ / 2) : ℂ)

lemma targetPhase_eq_exp {n : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ) :
    targetPhase y t θ =
      Complex.exp (((if y t then θ / 2 else -(θ / 2) : ℝ) : ℂ) * Complex.I) := by
  dsimp [targetPhase]
  cases y t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  · simp only [↓reduceIte]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring

lemma norm_targetPhase {n : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ) :
    ‖targetPhase y t θ‖ = 1 := by
  rw [targetPhase_eq_exp, Complex.norm_exp_ofReal_mul_I]

lemma targetPhase_add {n : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ1 θ2 : ℝ) :
    targetPhase y t θ1 * targetPhase y t θ2 = targetPhase y t (θ1 + θ2) := by
  dsimp [targetPhase]
  have hhalf : (θ1 + θ2) / 2 = θ1 / 2 + θ2 / 2 := by ring
  have hcos : (Real.cos ((θ1 + θ2) / 2) : ℂ) =
      (Real.cos (θ1 / 2) : ℂ) * (Real.cos (θ2 / 2) : ℂ) -
        (Real.sin (θ1 / 2) : ℂ) * (Real.sin (θ2 / 2) : ℂ) := by
    rw [hhalf]; exact_mod_cast Real.cos_add (θ1 / 2) (θ2 / 2)
  have hsin : (Real.sin ((θ1 + θ2) / 2) : ℂ) =
      (Real.sin (θ1 / 2) : ℂ) * (Real.cos (θ2 / 2) : ℂ) +
        (Real.cos (θ1 / 2) : ℂ) * (Real.sin (θ2 / 2) : ℂ) := by
    rw [hhalf]; exact_mod_cast Real.sin_add (θ1 / 2) (θ2 / 2)
  rw [hcos, hsin]
  cases y t <;> { simp; ring_nf; rw [Complex.I_sq]; ring }

lemma targetPhase_mul_star {n : ℕ} (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ) :
    targetPhase y t θ * star (targetPhase y t θ) = 1 := by
  have h : star (targetPhase y t θ) = targetPhase y t (-θ) := by
    dsimp [targetPhase]
    have hhalf : (-θ) / 2 = -(θ / 2) := by ring
    rw [hhalf, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    cases y t <;> {
      simp only [↓reduceIte, Bool.false_eq_true, Complex.star_def, map_add, map_sub, map_mul,
        map_neg, Complex.conj_ofReal, Complex.conj_I]
      ring
    }
  rw [h, targetPhase_add, add_neg_cancel]
  simp [targetPhase]

noncomputable def approxMean {n : ℕ} (m : ℕ) (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ) : ℂ :=
  ∑ k : Fin (2 * m), ((chiVec m k : ℂ) * (chiVec m k : ℂ)) * targetEig y t θ k

lemma norm_approxMean_le_one {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1))
    (t : Fin (n + 1)) (θ : ℝ) :
    ‖approxMean m y t θ‖ ≤ 1 := by
  calc ‖approxMean m y t θ‖
      ≤ ∑ k : Fin (2 * m), ‖((chiVec m k : ℂ) * (chiVec m k : ℂ)) * targetEig y t θ k‖ :=
        norm_sum_le _ _
    _ = ∑ k : Fin (2 * m), (chiVec m k) ^ 2 := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [norm_mul, norm_mul, norm_targetEig, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (chiVec_nonneg m k), sq]
    _ = 1 := sum_chiVec_sq hm

lemma approxMean_eq {n : ℕ} (m : ℕ) (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ) :
    approxMean m y t θ =
      ((∑ r : Fin m, dyadicWeight m r * signOfBool (greedyBit (Real.cos (θ / 2) / 2) r.1) : ℝ) : ℂ) +
      (if y t then Complex.I else -Complex.I) *
        ((∑ r : Fin m, dyadicWeight m r * signOfBool (greedyBit (Real.sin (θ / 2) / 2) r.1) : ℝ) : ℂ) := by
  unfold approxMean
  rw [sum_fin_two_mul]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hr : r.1 < m := r.2
  have heven : ((chiVec m ⟨2 * r.1, by omega⟩ : ℂ) * (chiVec m ⟨2 * r.1, by omega⟩ : ℂ)) =
      (dyadicWeight m r : ℂ) := by
    rw [← sq, ← Complex.ofReal_pow, chiVec_sq_even]
  have hodd : ((chiVec m ⟨2 * r.1 + 1, by omega⟩ : ℂ) * (chiVec m ⟨2 * r.1 + 1, by omega⟩ : ℂ)) =
      (dyadicWeight m r : ℂ) := by
    rw [← sq, ← Complex.ofReal_pow, chiVec_sq_odd]
  have hte_even : targetEig (m := m) y t θ ⟨2 * r.1, by omega⟩ =
      (signOfBool (greedyBit (Real.cos (θ / 2) / 2) r.1) : ℂ) := by
    dsimp [targetEig]
    have hmod : (2 * r.1) % 2 = 0 := by omega
    have hdiv : (2 * r.1) / 2 = r.1 := by omega
    rw [if_pos hmod, hdiv]
  have hte_odd : targetEig (m := m) y t θ ⟨2 * r.1 + 1, by omega⟩ =
      (if y t then Complex.I else -Complex.I) *
        (signOfBool (greedyBit (Real.sin (θ / 2) / 2) r.1) : ℂ) := by
    dsimp [targetEig]
    have hmod : (2 * r.1 + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * r.1 + 1) / 2 = r.1 := by omega
    rw [if_neg hmod, hdiv]
  rw [heven, hodd, hte_even, hte_odd]
  ring

lemma norm_two_mul_approxMean_sub_targetPhase {n m : ℕ} (hm : 1 ≤ m)
    (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ) :
    ‖(2 : ℂ) * approxMean m y t θ - targetPhase y t θ‖ ≤ 4 / (2 : ℝ) ^ m := by
  set Sc : ℝ := ∑ r : Fin m, dyadicWeight m r * signOfBool (greedyBit (Real.cos (θ / 2) / 2) r.1)
  set Ss : ℝ := ∑ r : Fin m, dyadicWeight m r * signOfBool (greedyBit (Real.sin (θ / 2) / 2) r.1)
  have hτc : |Real.cos (θ / 2) / 2| ≤ 2⁻¹ := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.abs_cos_le_one (θ / 2)]
  have hτs : |Real.sin (θ / 2) / 2| ≤ 2⁻¹ := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.abs_sin_le_one (θ / 2)]
  have hbc := abs_sum_dyadicWeight_greedyBit_sub_le hm hτc
  have hbs := abs_sum_dyadicWeight_greedyBit_sub_le hm hτs
  have hdiff : (2 : ℂ) * approxMean m y t θ - targetPhase y t θ =
      ((2 * (Sc - Real.cos (θ / 2) / 2) : ℝ) : ℂ) +
        (if y t then Complex.I else -Complex.I) *
          ((2 * (Ss - Real.sin (θ / 2) / 2) : ℝ) : ℂ) := by
    rw [approxMean_eq, targetPhase]
    change (2 : ℂ) * ((Sc : ℂ) + (if y t then Complex.I else -Complex.I) * (Ss : ℂ)) -
        ((Real.cos (θ / 2) : ℂ) + (if y t then Complex.I else -Complex.I) * (Real.sin (θ / 2) : ℂ)) = _
    push_cast
    ring
  have hI : ‖(if y t then Complex.I else -Complex.I : ℂ)‖ = 1 := by
    cases y t <;> simp
  rw [hdiff]
  calc ‖((2 * (Sc - Real.cos (θ / 2) / 2) : ℝ) : ℂ) +
          (if y t then Complex.I else -Complex.I) *
            ((2 * (Ss - Real.sin (θ / 2) / 2) : ℝ) : ℂ)‖
      ≤ ‖((2 * (Sc - Real.cos (θ / 2) / 2) : ℝ) : ℂ)‖ +
          ‖(if y t then Complex.I else -Complex.I) *
            ((2 * (Ss - Real.sin (θ / 2) / 2) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = 2 * |Sc - Real.cos (θ / 2) / 2| + 2 * |Ss - Real.sin (θ / 2) / 2| := by
        rw [norm_mul, hI, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ((2 : ℝ) ^ m)⁻¹ + 2 * ((2 : ℝ) ^ m)⁻¹ := by linarith
    _ = 4 / (2 : ℝ) ^ m := by ring

lemma norm_four_approxMean_star_sub_one {n m : ℕ} (hm : 1 ≤ m)
    (y : Qubits (n + 1)) (t : Fin (n + 1)) (θ : ℝ) :
    ‖4 * approxMean m y t θ * star (approxMean m y t θ) - 1‖ ≤ 12 / (2 : ℝ) ^ m := by
  set μ := approxMean m y t θ
  set u := (2 : ℂ) * μ
  set p := targetPhase y t θ
  have halg : 4 * μ * star μ - 1 = (u - p) * star u + p * star (u - p) := by
    have hp : p * star p = 1 := targetPhase_mul_star y t θ
    dsimp [u]
    calc 4 * μ * star μ - 1 = 4 * μ * star μ - p * star p := by rw [hp]
      _ = ((2 : ℂ) * μ - p) * star ((2 : ℂ) * μ) + p * star ((2 : ℂ) * μ - p) := by
          simp only [star_mul, star_sub, Complex.star_def, map_ofNat]
          ring
  have hu_le : ‖u‖ ≤ 2 := by
    dsimp [u]
    rw [norm_mul, Complex.norm_two]
    linarith [norm_approxMean_le_one hm y t θ]
  have hup : ‖u - p‖ ≤ 4 / (2 : ℝ) ^ m := norm_two_mul_approxMean_sub_targetPhase hm y t θ
  have hp_norm : ‖p‖ = 1 := norm_targetPhase y t θ
  rw [halg]
  calc ‖(u - p) * star u + p * star (u - p)‖
      ≤ ‖(u - p) * star u‖ + ‖p * star (u - p)‖ := norm_add_le _ _
    _ = ‖u - p‖ * ‖u‖ + ‖u - p‖ := by
        rw [norm_mul, norm_mul, norm_star, norm_star, hp_norm, one_mul]
    _ ≤ (4 / (2 : ℝ) ^ m) * 2 + 4 / (2 : ℝ) ^ m := by
        nlinarith [norm_nonneg (u - p)]
    _ = 12 / (2 : ℝ) ^ m := by ring

def prepCircuit (n m : ℕ) (hm : 1 ≤ m) : Circuit htcxGateSet (n + (1 + 2 * m)) :=
  gateX (workWire n m ⟨0, by omega⟩) ++ ohsListCircuit n m (prepPairs m)

def unprepCircuit (n m : ℕ) (hm : 1 ≤ m) : Circuit htcxGateSet (n + (1 + 2 * m)) :=
  ohsListCircuit n m (prepPairs m).reverse ++
    gateZ (workWire n m ⟨0, by omega⟩) ++
    gateX (workWire n m ⟨0, by omega⟩)

noncomputable def grover5Circuit (n m : ℕ) (hm : 1 ≤ m) (t : Fin (n + 1)) (θ : ℝ) :
    Circuit htcxGateSet (n + (1 + 2 * m)) :=
  let cD := diagChain n m t θ m le_rfl
  let cDinv := diagInvChain n m t θ m le_rfl
  let cRefl := reflOH n m (prepPairs m) ⟨0, by omega⟩
  cD ++ cRefl ++ cDinv ++ cRefl ++ cD

noncomputable def approxRz (n m : ℕ) (hm : 1 ≤ m) (t : Fin (n + 1)) (θ : ℝ) :
    Circuit htcxGateSet (n + (1 + 2 * m)) :=
  prepCircuit n m hm ++ grover5Circuit n m hm t θ ++ unprepCircuit n m hm

lemma approxRz_size_le (n m : ℕ) (hm : 1 ≤ m) (t : Fin (n + 1)) (θ : ℝ) :
    (approxRz n m hm t θ).size ≤ 447 * m := by
  have hp : (prepCircuit n m hm).size = 6 + 31 * (2 * m - 1) := by
    dsimp [prepCircuit]
    rw [circuit_size_append, gateX_size, ohsListCircuit_size, prepPairs_length hm]
  have hu : (unprepCircuit n m hm).size = 31 * (2 * m - 1) + 10 := by
    dsimp [unprepCircuit]
    rw [circuit_size_append, circuit_size_append, ohsListCircuit_size,
      List.length_reverse, prepPairs_length hm, gateZ_size, gateX_size]
  have hr : (reflOH n m (prepPairs m) ⟨0, by omega⟩).size = 62 * (2 * m - 1) + 4 := by
    rw [reflOH_size, prepPairs_length hm]
  have hd1 := diagChain_size_le n m t θ m le_rfl
  have hd2 := diagInvChain_size_le n m t θ m le_rfl
  have hg : (grover5Circuit n m hm t θ).size ≤ 51 * m + 2 * (62 * (2 * m - 1) + 4) := by
    dsimp [grover5Circuit]
    rw [circuit_size_append, circuit_size_append, circuit_size_append, circuit_size_append, hr]
    omega
  dsimp [approxRz]
  rw [circuit_size_append, circuit_size_append, hp, hu]
  omega

lemma act_prepCircuit_ketZeroWork {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1)) :
    act (prepCircuit n m hm).unitary (ketZeroWork y) =
      embedOH y (fun k => (chiVec m k : ℂ)) := by
  dsimp [prepCircuit]
  rw [act_circuit_unitary_append, act_gateX_ketZeroWork, act_prepPairs_ketOH hm y]

lemma act_unprepCircuit_embedOH_chiVec {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1)) :
    act (unprepCircuit n m hm).unitary (embedOH y (fun k => (chiVec m k : ℂ))) =
      (-1 : ℂ) • ketZeroWork y := by
  dsimp [unprepCircuit]
  set k0 : Fin (2 * m) := ⟨0, by omega⟩
  have h1 : act (ohsListCircuit n m (prepPairs m).reverse).unitary
        (embedOH y (fun k => (chiVec m k : ℂ))) = ketOH y k0 := by
    rw [← act_prepPairs_ketOH hm y, ← act_mul, ohsListCircuit_reverse_mul_unitary, act_one]
  have h2 : act (gateZ (workWire n m k0)).unitary (ketOH y k0) = (-1 : ℂ) • ketOH y k0 := by
    dsimp [ketOH, ketMW]
    rw [isDiagCircuit_gateZ (workWire n m k0) (vecMW y (oneHotBits k0))]
    dsimp only
    rw [vecMW_work, oneHotBits_self, if_pos rfl]
  rw [act_circuit_unitary_append, act_circuit_unitary_append, h1, h2,
    act_smul, act_gateX_ketOH_self]

lemma inFiber_act_unprepCircuit_embedOH {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1))
    (β : Fin (2 * m) → ℂ) :
    InFiber y (act (unprepCircuit n m hm).unitary (embedOH y β)) := by
  dsimp [unprepCircuit]
  rw [act_circuit_unitary_append, act_circuit_unitary_append,
    act_ohsListCircuit_embedOH,
    (isDiagCircuit_gateZ (workWire n m ⟨0, by omega⟩)).act_embedOH]
  exact inFiber_act_gateX_embedOH y ⟨0, by omega⟩ _

lemma act_grover5Circuit_embedOH_chiVec {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1))
    (t : Fin (n + 1)) (θ : ℝ) :
    let μ := approxMean m y t θ
    act (grover5Circuit n m hm t θ).unitary (embedOH y (fun k => (chiVec m k : ℂ))) =
      (- (2 * μ)) • embedOH y (fun k => (chiVec m k : ℂ)) +
        (4 * μ * star μ - 1) • embedOH y (fun k => targetEig y t θ k * (chiVec m k : ℂ)) := by
  intro μ
  have hg := act_grover5_embedOH y (prepPairs m) ⟨0, by omega⟩
    (fun k => (chiVec m k : ℂ)) (act_prepPairs_ketOH hm y)
    (fun k => Complex.conj_ofReal _) (sum_chiVec_complex_sq hm)
    (isDiagCircuit_diagChain n m t θ m le_rfl)
    (isDiagCircuit_diagInvChain n m t θ m le_rfl)
    (targetEig y t θ)
    (evChain_top_vecMW_oneHotBits y t θ)
    (evInvChain_top_vecMW_oneHotBits y t θ)
    (star_targetEig_mul_self y t θ)
  dsimp only [grover5Circuit]
  rw [hg, ← embedOH_smul, ← embedOH_smul, ← embedOH_add]
  congr 1
  funext k
  change ((4 * μ * star μ - 1) * targetEig y t θ k - 2 * μ) * (chiVec m k : ℂ) = _
  ring

lemma inFiber_act_approxRz_ketZeroWork {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1))
    (t : Fin (n + 1)) (θ : ℝ) :
    InFiber y (act (approxRz n m hm t θ).unitary (ketZeroWork y)) := by
  dsimp [approxRz]
  rw [act_circuit_unitary_append, act_circuit_unitary_append,
    act_prepCircuit_ketZeroWork hm y, act_grover5Circuit_embedOH_chiVec hm y t θ,
    ← embedOH_smul, ← embedOH_smul, ← embedOH_add]
  exact inFiber_act_unprepCircuit_embedOH hm y _

lemma norm_embedOH_targetEig_chiVec {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1))
    (t : Fin (n + 1)) (θ : ℝ) :
    ‖embedOH y (fun k => targetEig y t θ k * (chiVec m k : ℂ))‖ = 1 := by
  have hsq : ‖embedOH y (fun k => targetEig y t θ k * (chiVec m k : ℂ))‖ ^ 2 = 1 := by
    rw [norm_embedOH_sq]
    have hterm : ∀ k : Fin (2 * m),
        ‖targetEig y t θ k * (chiVec m k : ℂ)‖ ^ 2 = (chiVec m k) ^ 2 := by
      intro k
      rw [norm_mul, norm_targetEig, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (chiVec_nonneg m k)]
    simp_rw [hterm]
    exact sum_chiVec_sq hm
  nlinarith [norm_nonneg (embedOH y (fun k => targetEig y t θ k * (chiVec m k : ℂ)))]

lemma norm_act_approxRz_ketZeroWork_sub {n m : ℕ} (hm : 1 ≤ m) (y : Qubits (n + 1))
    (t : Fin (n + 1)) (θ : ℝ) :
    ‖act (approxRz n m hm t θ).unitary (ketZeroWork y) -
        targetPhase y t θ • ketZeroWork y‖ ≤ 16 / (2 : ℝ) ^ m := by
  set μ := approxMean m y t θ
  set errVec := embedOH y (fun k => targetEig y t θ k * (chiVec m k : ℂ))
  have hact : act (approxRz n m hm t θ).unitary (ketZeroWork y) =
      ((2 : ℂ) * μ) • ketZeroWork y +
        (4 * μ * star μ - 1) • act (unprepCircuit n m hm).unitary errVec := by
    dsimp [approxRz]
    rw [act_circuit_unitary_append, act_circuit_unitary_append,
      act_prepCircuit_ketZeroWork hm y, act_grover5Circuit_embedOH_chiVec hm y t θ,
      act_add, act_smul, act_smul, act_unprepCircuit_embedOH_chiVec hm y, smul_smul]
    congr 1
    congr 1
    change (-(2 * μ)) * (-1 : ℂ) = (2 : ℂ) * μ
    ring
  have hsub : act (approxRz n m hm t θ).unitary (ketZeroWork y) -
        targetPhase y t θ • ketZeroWork y =
      ((2 : ℂ) * μ - targetPhase y t θ) • ketZeroWork y +
        (4 * μ * star μ - 1) • act (unprepCircuit n m hm).unitary errVec := by
    ext z
    simp only [hact, sub_ofLp_apply, add_ofLp_apply, smul_ofLp_apply]
    ring
  rw [hsub]
  calc ‖((2 : ℂ) * μ - targetPhase y t θ) • ketZeroWork y +
          (4 * μ * star μ - 1) • act (unprepCircuit n m hm).unitary errVec‖
      ≤ ‖((2 : ℂ) * μ - targetPhase y t θ) • ketZeroWork y‖ +
          ‖(4 * μ * star μ - 1) • act (unprepCircuit n m hm).unitary errVec‖ := norm_add_le _ _
    _ = ‖(2 : ℂ) * μ - targetPhase y t θ‖ + ‖4 * μ * star μ - 1‖ := by
        rw [norm_smul, norm_ketZeroWork, mul_one, norm_smul,
          norm_act_htcx_unitary, norm_embedOH_targetEig_chiVec hm y t θ, mul_one]
    _ ≤ 4 / (2 : ℝ) ^ m + 12 / (2 : ℝ) ^ m :=
        add_le_add (norm_two_mul_approxMean_sub_targetPhase hm y t θ)
          (norm_four_approxMean_star_sub_one hm y t θ)
    _ = 16 / (2 : ℝ) ^ m := by ring

/-! ### Section 5: `ApproxLift`, Uniformly Controlled `ucRz`, and Stage Circuits -/

lemma liftWork_add {n m : ℕ} (Φ1 Φ2 : EuclideanSpace ℂ (Qubits (n + 1))) :
    liftWork (m := m) (Φ1 + Φ2) = liftWork (m := m) Φ1 + liftWork (m := m) Φ2 := by
  ext z
  simp only [liftWork, toLp_ofLp_apply, add_ofLp_apply]
  split_ifs <;> ring

lemma liftWork_smul {n m : ℕ} (c : ℂ) (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    liftWork (m := m) (c • Φ) = c • liftWork (m := m) Φ := by
  ext z
  simp only [liftWork, toLp_ofLp_apply, smul_ofLp_apply]
  split_ifs <;> ring

lemma liftWork_sum {n m : ℕ} {α : Type*} (s : Finset α)
    (f : α → EuclideanSpace ℂ (Qubits (n + 1))) :
    liftWork (m := m) (∑ x ∈ s, f x) = ∑ x ∈ s, liftWork (m := m) (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext z; simp [liftWork]
  | @insert a s ha ih => rw [Finset.sum_insert ha, liftWork_add, ih, Finset.sum_insert ha]

lemma liftWork_ket {n m : ℕ} (y : Qubits (n + 1)) :
    liftWork (m := m) (ket y) = ketZeroWork (m := m) y := by
  ext z
  simp only [liftWork, toLp_ofLp_apply, ketZeroWork, ketMW, ket_apply, eq_vecMW_iff]
  by_cases hw : workProj z = 0 <;> by_cases hm : mainProj z = y <;> simp [hw, hm]

lemma act_embed1_mainWire_liftWork {n m : ℕ} (U : Matrix Bool Bool ℂ)
    (t : Fin (n + 1)) (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    act (embed1 U (mainWire n m t)) (liftWork (m := m) Φ) =
      liftWork (m := m) (act (embed1 U t) Φ) := by
  rw [decomp_euclidean Φ, liftWork_sum, act_sum, act_sum, liftWork_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [liftWork_smul, act_smul, act_smul, liftWork_smul, liftWork_ket,
    ketZeroWork, ketMW, act_embed1_ket, act_embed1_ket, vecMW_main, liftWork_sum]
  congr 1
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [liftWork_smul, liftWork_ket, update_vecMW_main, ketZeroWork, ketMW]

lemma act_embed2_mainWire_liftWork {n m : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (w0 w1 : Fin (n + 1)) (h01 : w0 ≠ w1) (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    act (embed2 M (mainWire n m w0) (mainWire n m w1) (mainWire_ne h01))
        (liftWork (m := m) Φ) =
      liftWork (m := m) (act (embed2 M w0 w1 h01) Φ) := by
  rw [decomp_euclidean Φ, liftWork_sum, act_sum, act_sum, liftWork_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [liftWork_smul, act_smul, act_smul, liftWork_smul, liftWork_ket,
    ketZeroWork, ketMW, act_embed2_ket, act_embed2_ket, vecMW_main, vecMW_main, liftWork_sum]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [liftWork_smul, liftWork_ket, update_vecMW_main, update_vecMW_main, ketZeroWork, ketMW]

lemma act_embed1_ofLp {N : ℕ} (M : Matrix Bool Bool ℂ) (w : Fin N)
    (Φ : EuclideanSpace ℂ (Qubits N)) (y : Qubits N) :
    (act (embed1 M w) Φ).ofLp y =
      M (y w) false * Φ.ofLp (Function.update y w false) +
        M (y w) true * Φ.ofLp (Function.update y w true) := by
  rw [act_apply, Matrix.mulVec, dotProduct]
  have hterm : ∀ z : Qubits N,
      embed1 M w y z * Φ.ofLp z =
        if z = Function.update y w false ∨ z = Function.update y w true then
          M (y w) (z w) * Φ.ofLp z
        else 0 := by
    intro z
    dsimp [embed1, embedOp]
    by_cases hoff : ∀ a, a ∉ Set.range (singleEmb w) → y a = z a
    · have hz : z = Function.update y w false ∨ z = Function.update y w true := by
        cases hzw : z w
        · left
          exact (update_single_eq_iff w z y false).mpr
            ⟨fun a ha => (hoff a ha).symm, hzw.symm⟩
        · right
          exact (update_single_eq_iff w z y true).mpr
            ⟨fun a ha => (hoff a ha).symm, hzw.symm⟩
      rw [if_pos hoff, if_pos hz]
    · have hnot : ¬ (z = Function.update y w false ∨ z = Function.update y w true) := by
        rintro (hz | hz) <;>
          exact hoff (fun a ha => ((update_single_eq_iff w z y _).mp hz).1 a ha |>.symm)
      rw [if_neg hoff, if_neg hnot, zero_mul]
  simp_rw [hterm]
  have hne : Function.update y w false ≠ Function.update y w true := by
    intro h; have := congrFun h w; simp at this
  rw [← Finset.sum_filter,
    show Finset.univ.filter (fun z : Qubits N =>
        z = Function.update y w false ∨ z = Function.update y w true) =
      {Function.update y w false, Function.update y w true} by
      ext z; simp,
    Finset.sum_pair hne, Function.update_self, Function.update_self]

def ApproxLift {n : ℕ} (m : ℕ) (c : Circuit htcxGateSet (n + (1 + 2 * m)))
    (F : EuclideanSpace ℂ (Qubits (n + 1)) → EuclideanSpace ℂ (Qubits (n + 1)))
    (δ : ℝ) : Prop :=
  0 ≤ δ ∧ (∀ Φ, ‖F Φ‖ = ‖Φ‖) ∧
    ∀ Φ : EuclideanSpace ℂ (Qubits (n + 1)),
      ‖act c.unitary (liftWork (m := m) Φ) - liftWork (m := m) (F Φ)‖ ≤ δ * ‖Φ‖

lemma ApproxLift.append {n m : ℕ}
    {c1 c2 : Circuit htcxGateSet (n + (1 + 2 * m))}
    {F1 F2 : EuclideanSpace ℂ (Qubits (n + 1)) → EuclideanSpace ℂ (Qubits (n + 1))}
    {δ1 δ2 : ℝ}
    (h1 : ApproxLift m c1 F1 δ1) (h2 : ApproxLift m c2 F2 δ2) :
    ApproxLift m (c1 ++ c2) (fun Φ => F2 (F1 Φ)) (δ1 + δ2) := by
  refine ⟨add_nonneg h1.1 h2.1, fun Φ => by rw [h2.2.1, h1.2.1], fun Φ => ?_⟩
  rw [act_circuit_unitary_append]
  have htri :
      ‖act c2.unitary (act c1.unitary (liftWork (m := m) Φ)) -
          liftWork (m := m) (F2 (F1 Φ))‖ ≤
        ‖act c2.unitary (act c1.unitary (liftWork (m := m) Φ)) -
            act c2.unitary (liftWork (m := m) (F1 Φ))‖ +
          ‖act c2.unitary (liftWork (m := m) (F1 Φ)) -
            liftWork (m := m) (F2 (F1 Φ))‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hleft :
      ‖act c2.unitary (act c1.unitary (liftWork (m := m) Φ)) -
          act c2.unitary (liftWork (m := m) (F1 Φ))‖ ≤ δ1 * ‖Φ‖ := by
    rw [← act_sub, norm_act_htcx_unitary]
    exact h1.2.2 Φ
  have hright :
      ‖act c2.unitary (liftWork (m := m) (F1 Φ)) -
          liftWork (m := m) (F2 (F1 Φ))‖ ≤ δ2 * ‖Φ‖ := by
    have hb := h2.2.2 (F1 Φ)
    rwa [h1.2.1 Φ] at hb
  linarith

noncomputable def diagMain {n : ℕ} (t : Fin (n + 1)) (α : Qubits (n + 1) → ℝ)
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) : EuclideanSpace ℂ (Qubits (n + 1)) :=
  WithLp.toLp 2 (fun y => targetPhase y t (α y) * Φ.ofLp y)

lemma norm_diagMain {n : ℕ} (t : Fin (n + 1)) (α : Qubits (n + 1) → ℝ)
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    ‖diagMain t α Φ‖ = ‖Φ‖ := by
  have hsq : ‖diagMain t α Φ‖ ^ 2 = ‖Φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp [diagMain, norm_mul, norm_targetPhase]
  nlinarith [norm_nonneg (diagMain t α Φ), norm_nonneg Φ]

lemma approxLift_approxRz {n m : ℕ} (hm : 1 ≤ m) (t : Fin (n + 1)) (θ : ℝ) :
    ApproxLift m (approxRz n m hm t θ) (diagMain t (fun _ => θ)) (16 / (2 : ℝ) ^ m) := by
  refine ⟨by positivity, norm_diagMain t (fun _ => θ), fun Φ => ?_⟩
  have hrew :
      act (approxRz n m hm t θ).unitary (liftWork (m := m) Φ) -
          liftWork (m := m) (diagMain t (fun _ => θ) Φ) =
        ∑ y : Qubits (n + 1),
          Φ.ofLp y •
            (act (approxRz n m hm t θ).unitary (ketZeroWork (m := m) y) -
              targetPhase y t θ • ketZeroWork (m := m) y) := by
    rw [liftWork_eq_sum_ketZeroWork Φ,
      liftWork_eq_sum_ketZeroWork (diagMain t (fun _ => θ) Φ),
      act_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    dsimp [diagMain]
    rw [act_smul, smul_sub, smul_smul, mul_comm (Φ.ofLp y)]
  rw [hrew]
  refine norm_sum_inFiber_le
    (fun y => Φ.ofLp y •
      (act (approxRz n m hm t θ).unitary (ketZeroWork (m := m) y) -
        targetPhase y t θ • ketZeroWork (m := m) y))
    (fun y => ((inFiber_act_approxRz_ketZeroWork hm y t θ).sub
      ((inFiber_ketZeroWork (m := m) y).smul (targetPhase y t θ))).smul (Φ.ofLp y))
    Φ (16 / (2 : ℝ) ^ m) (by positivity) (fun y => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_act_approxRz_ketZeroWork_sub hm y t θ)
    (norm_nonneg (Φ.ofLp y))

def flipMain {n : ℕ} (c_wire t : Fin (n + 1)) (y : Qubits (n + 1)) : Qubits (n + 1) :=
  Function.update y t (xor (y t) (y c_wire))

lemma flipMain_invol {n : ℕ} (c_wire t : Fin (n + 1)) (hct : c_wire ≠ t)
    (y : Qubits (n + 1)) :
    flipMain c_wire t (flipMain c_wire t y) = y := by
  dsimp [flipMain]
  rw [Function.update_self, Function.update_of_ne hct, Function.update_idem]
  have hxor : xor (xor (y t) (y c_wire)) (y c_wire) = y t := by
    cases y t <;> cases y c_wire <;> rfl
  rw [hxor, Function.update_eq_self]

lemma targetPhase_flipMain {n : ℕ} (c_wire t : Fin (n + 1)) (y : Qubits (n + 1)) (θ : ℝ) :
    targetPhase (flipMain c_wire t y) t θ = targetPhase y t (if y c_wire then -θ else θ) := by
  dsimp [targetPhase, flipMain]
  rw [Function.update_self]
  have hhalf : (-θ) / 2 = -(θ / 2) := by ring
  cases y c_wire <;> cases y t <;>
    simp [hhalf, Real.cos_neg, Real.sin_neg] <;> ring

noncomputable def cnotMain {n : ℕ} (c_wire t : Fin (n + 1))
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) : EuclideanSpace ℂ (Qubits (n + 1)) :=
  WithLp.toLp 2 (fun y => Φ.ofLp (flipMain c_wire t y))

lemma act_embed2_cnot_eq_cnotMain {n : ℕ} (c_wire t : Fin (n + 1)) (hct : c_wire ≠ t)
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    act (embed2 cnot c_wire t hct) Φ = cnotMain c_wire t Φ := by
  have hket : ∀ z : Qubits (n + 1),
      act (embed2 cnot c_wire t hct) (ket z) = ket (flipMain c_wire t z) := by
    intro z
    rw [act_embed2_ket, Fintype.sum_prod_type]
    have hupd : ∀ b : Bool,
        Function.update (Function.update z c_wire (z c_wire)) t b =
          Function.update z t b := fun b => by rw [Function.update_eq_self]
    cases hzc : z c_wire <;> cases hzt : z t <;> {
      rw [hzc] at hupd
      simp [cnot, flipMain, hzc, hzt, hupd]
    }
  ext y
  conv_lhs => rw [decomp_euclidean Φ]
  rw [act_sum, sum_ofLp_apply]
  simp_rw [act_smul, hket, smul_ofLp_apply, ket_apply]
  dsimp [cnotMain]
  rw [Finset.sum_eq_single (flipMain c_wire t y)]
  · rw [flipMain_invol c_wire t hct y, if_pos rfl, mul_one]
  · intro z _ hz
    have hne : y ≠ flipMain c_wire t z := by
      intro heq
      apply hz
      rw [heq, flipMain_invol c_wire t hct z]
    rw [if_neg hne, mul_zero]
  · intro habs; exact False.elim (habs (Finset.mem_univ _))

lemma norm_cnotMain {n : ℕ} (c_wire t : Fin (n + 1)) (hct : c_wire ≠ t)
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    ‖cnotMain c_wire t Φ‖ = ‖Φ‖ := by
  let c : Circuit htcxGateSet (n + 1) := [cxGate c_wire t hct]
  have h : cnotMain c_wire t Φ = act c.unitary Φ := by
    dsimp [c]
    rw [circuit_unitary_singleton, cxGate_embedOp, act_embed2_cnot_eq_cnotMain]
  rw [h, norm_act_htcx_unitary]

lemma approxLift_cxGate {n m : ℕ} (c_wire t : Fin (n + 1)) (hct : c_wire ≠ t) :
    ApproxLift m [cxGate (mainWire n m c_wire) (mainWire n m t) (mainWire_ne hct)]
      (cnotMain c_wire t) 0 := by
  refine ⟨le_refl 0, norm_cnotMain c_wire t hct, fun Φ => ?_⟩
  rw [circuit_unitary_singleton, cxGate_embedOp,
    act_embed2_mainWire_liftWork cnot c_wire t hct Φ,
    act_embed2_cnot_eq_cnotMain, sub_self, norm_zero, zero_mul]

lemma diagMain_cnotMain_conj {n : ℕ} (c_wire t : Fin (n + 1)) (hct : c_wire ≠ t)
    (α β : Qubits (n + 1) → ℝ)
    (hα : ∀ y : Qubits (n + 1), α (flipMain c_wire t y) = α y)
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) :
    diagMain t β (cnotMain c_wire t (diagMain t α (cnotMain c_wire t Φ))) =
      diagMain t (fun y => β y + if y c_wire then -α y else α y) Φ := by
  ext y
  simp only [diagMain, cnotMain, toLp_ofLp_apply]
  rw [hα y, targetPhase_flipMain, flipMain_invol c_wire t hct y,
    ← mul_assoc, targetPhase_add]

def DependsOnPrefix {n : ℕ} (r : ℕ) (ang : Qubits (n + 1) → ℝ) : Prop :=
  ∀ y1 y2 : Qubits (n + 1), (∀ i : Fin (n + 1), i.1 < r → y1 i = y2 i) → ang y1 = ang y2

lemma dependsOnPrefix_zero_eq {n : ℕ} {ang : Qubits (n + 1) → ℝ}
    (h : DependsOnPrefix 0 ang) (y : Qubits (n + 1)) :
    ang y = ang 0 :=
  h y 0 (fun _ hi => by omega)

lemma dependsOnPrefix_update_ge {n r : ℕ} {ang : Qubits (n + 1) → ℝ}
    (h : DependsOnPrefix r ang) (t : Fin (n + 1)) (ht : r ≤ t.1)
    (y : Qubits (n + 1)) (b : Bool) :
    ang (Function.update y t b) = ang y := by
  refine h (Function.update y t b) y (fun i hi => ?_)
  have hne : i ≠ t := by
    intro heq; have := congrArg Fin.val heq; omega
  exact Function.update_of_ne hne b y

lemma dependsOnPrefix_flipMain {n r : ℕ} {ang : Qubits (n + 1) → ℝ}
    (h : DependsOnPrefix r ang) (c_wire t : Fin (n + 1)) (ht : r ≤ t.1)
    (y : Qubits (n + 1)) :
    ang (flipMain c_wire t y) = ang y :=
  dependsOnPrefix_update_ge h t ht y (xor (y t) (y c_wire))

noncomputable def halfDiff {n : ℕ} (c_wire : Fin (n + 1)) (ang : Qubits (n + 1) → ℝ)
    (y : Qubits (n + 1)) : ℝ :=
  (ang (Function.update y c_wire false) - ang (Function.update y c_wire true)) / 2

noncomputable def halfSum {n : ℕ} (c_wire : Fin (n + 1)) (ang : Qubits (n + 1) → ℝ)
    (y : Qubits (n + 1)) : ℝ :=
  (ang (Function.update y c_wire false) + ang (Function.update y c_wire true)) / 2

lemma dependsOnPrefix_halfDiff {n r : ℕ} (hr : r + 1 ≤ n + 1)
    {ang : Qubits (n + 1) → ℝ} (hang : DependsOnPrefix (r + 1) ang) :
    DependsOnPrefix r (halfDiff ⟨r, hr⟩ ang) := by
  intro y1 y2 hy
  dsimp [halfDiff]
  have h_upd : ∀ b : Bool,
      ang (Function.update y1 ⟨r, hr⟩ b) = ang (Function.update y2 ⟨r, hr⟩ b) := by
    intro b
    refine hang _ _ (fun i hi => ?_)
    by_cases hir : i = ⟨r, hr⟩
    · subst hir; simp
    · have hlt : i.1 < r := by
        have : i.1 ≠ r := fun h => hir (Fin.ext h)
        omega
      rw [Function.update_of_ne hir, Function.update_of_ne hir, hy i hlt]
  rw [h_upd false, h_upd true]

lemma dependsOnPrefix_halfSum {n r : ℕ} (hr : r + 1 ≤ n + 1)
    {ang : Qubits (n + 1) → ℝ} (hang : DependsOnPrefix (r + 1) ang) :
    DependsOnPrefix r (halfSum ⟨r, hr⟩ ang) := by
  intro y1 y2 hy
  dsimp [halfSum]
  have h_upd : ∀ b : Bool,
      ang (Function.update y1 ⟨r, hr⟩ b) = ang (Function.update y2 ⟨r, hr⟩ b) := by
    intro b
    refine hang _ _ (fun i hi => ?_)
    by_cases hir : i = ⟨r, hr⟩
    · subst hir; simp
    · have hlt : i.1 < r := by
        have : i.1 ≠ r := fun h => hir (Fin.ext h)
        omega
      rw [Function.update_of_ne hir, Function.update_of_ne hir, hy i hlt]
  rw [h_upd false, h_upd true]

lemma halfSum_add_halfDiff {n : ℕ} (c_wire : Fin (n + 1)) (ang : Qubits (n + 1) → ℝ)
    (y : Qubits (n + 1)) :
    halfSum c_wire ang y +
      (if y c_wire then -halfDiff c_wire ang y else halfDiff c_wire ang y) = ang y := by
  dsimp [halfSum, halfDiff]
  cases hy : y c_wire
  · have hupd : Function.update y c_wire false = y := by
      rw [← hy, Function.update_eq_self]
    simp [hupd]; ring
  · have hupd : Function.update y c_wire true = y := by
      rw [← hy, Function.update_eq_self]
    simp [hupd]; ring

noncomputable def ucRz (n m : ℕ) (hm : 1 ≤ m) :
    (r : ℕ) → r ≤ n → (t : Fin (n + 1)) → r ≤ t.1 → (Qubits (n + 1) → ℝ) →
      Circuit htcxGateSet (n + (1 + 2 * m))
  | 0, _, t, _, ang => approxRz n m hm t (ang 0)
  | r + 1, hr, t, ht, ang =>
      let c_wire : Fin (n + 1) := ⟨r, by omega⟩
      have hct : c_wire ≠ t := by
        intro heq; have := congrArg Fin.val heq; dsimp [c_wire] at this; omega
      [cxGate (mainWire n m c_wire) (mainWire n m t) (mainWire_ne hct)] ++
        ucRz n m hm r (Nat.le_of_succ_le hr) t (Nat.le_of_succ_le ht) (halfDiff c_wire ang) ++
        [cxGate (mainWire n m c_wire) (mainWire n m t) (mainWire_ne hct)] ++
        ucRz n m hm r (Nat.le_of_succ_le hr) t (Nat.le_of_succ_le ht) (halfSum c_wire ang)

lemma ucRz_size_add_two_le (n m : ℕ) (hm : 1 ≤ m) :
    ∀ (r : ℕ) (hr : r ≤ n) (t : Fin (n + 1)) (ht : r ≤ t.1) (ang : Qubits (n + 1) → ℝ),
      (ucRz n m hm r hr t ht ang).size + 2 ≤ 2 ^ r * (447 * m + 2)
  | 0, _, t, _, ang => by
      dsimp [ucRz]
      have h := approxRz_size_le n m hm t (ang 0)
      omega
  | r + 1, hr, t, ht, ang => by
      rw [ucRz, circuit_size_append, circuit_size_append, circuit_size_append]
      have h1 := ucRz_size_add_two_le n m hm r (Nat.le_of_succ_le hr) t
        (Nat.le_of_succ_le ht) (halfDiff ⟨r, by omega⟩ ang)
      have h2 := ucRz_size_add_two_le n m hm r (Nat.le_of_succ_le hr) t
        (Nat.le_of_succ_le ht) (halfSum ⟨r, by omega⟩ ang)
      have hcx : ∀ (w0 w1 : Fin (n + (1 + 2 * m))) (h01 : w0 ≠ w1),
          Circuit.size ([cxGate w0 w1 h01] : Circuit htcxGateSet (n + (1 + 2 * m))) = 1 :=
        fun _ _ _ => rfl
      rw [hcx, pow_succ', Nat.two_mul (2 ^ r), Nat.right_distrib]
      omega

lemma approxLift_ucRz (n m : ℕ) (hm : 1 ≤ m) :
    ∀ (r : ℕ) (hr : r ≤ n) (t : Fin (n + 1)) (ht : r ≤ t.1)
      (ang : Qubits (n + 1) → ℝ) (hang : DependsOnPrefix r ang),
      ApproxLift m (ucRz n m hm r hr t ht ang) (diagMain t ang)
        ((2 : ℝ) ^ r * (16 / (2 : ℝ) ^ m))
  | 0, _, t, _, ang, hang => by
      dsimp [ucRz]
      have heq : diagMain t ang = diagMain t (fun _ => ang 0) := by
        funext Φ; ext y; simp [diagMain, dependsOnPrefix_zero_eq hang y]
      rw [heq, pow_zero, one_mul]
      exact approxLift_approxRz hm t (ang 0)
  | r + 1, hr, t, ht, ang, hang => by
      dsimp [ucRz]
      set c_wire : Fin (n + 1) := ⟨r, by omega⟩
      have hct : c_wire ≠ t := by
        intro heq; have := congrArg Fin.val heq; dsimp [c_wire] at this; omega
      have hcx := approxLift_cxGate (m := m) c_wire t hct
      have h_diff := approxLift_ucRz n m hm r (Nat.le_of_succ_le hr) t (Nat.le_of_succ_le ht)
        (halfDiff c_wire ang) (dependsOnPrefix_halfDiff (by omega) hang)
      have h_sum := approxLift_ucRz n m hm r (Nat.le_of_succ_le hr) t (Nat.le_of_succ_le ht)
        (halfSum c_wire ang) (dependsOnPrefix_halfSum (by omega) hang)
      have happ := ((hcx.append h_diff).append hcx).append h_sum
      have hF : (fun Φ => diagMain t (halfSum c_wire ang)
          (cnotMain c_wire t (diagMain t (halfDiff c_wire ang) (cnotMain c_wire t Φ)))) =
          diagMain t ang := by
        funext Φ
        rw [diagMain_cnotMain_conj c_wire t hct _ _
          (dependsOnPrefix_flipMain (dependsOnPrefix_halfDiff (by omega) hang)
            c_wire t (Nat.le_of_succ_le ht))]
        ext y
        dsimp [diagMain]
        rw [halfSum_add_halfDiff c_wire ang y]
      have hδ : 0 + (2 : ℝ) ^ r * (16 / (2 : ℝ) ^ m) + 0 +
          (2 : ℝ) ^ r * (16 / (2 : ℝ) ^ m) =
          (2 : ℝ) ^ (r + 1) * (16 / (2 : ℝ) ^ m) := by
        rw [pow_succ']; ring
      rwa [hF, hδ] at happ

noncomputable def hsdagMain {n : ℕ} (t : Fin (n + 1))
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) : EuclideanSpace ℂ (Qubits (n + 1)) :=
  act (embed1 (hadamard * phaseSdag) t) Φ

noncomputable def shMain {n : ℕ} (t : Fin (n + 1))
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) : EuclideanSpace ℂ (Qubits (n + 1)) :=
  act (embed1 (phaseS * hadamard) t) Φ

lemma approxLift_hsdagMain {n m : ℕ} (t : Fin (n + 1)) :
    ApproxLift m (gateSdag (mainWire n m t) ++ [hGate (mainWire n m t)]) (hsdagMain t) 0 := by
  have hu : ∀ {N : ℕ} (w : Fin N),
      (gateSdag w ++ [hGate w] : Circuit htcxGateSet N).unitary =
        embed1 (hadamard * phaseSdag) w := by
    intro N w
    rw [circuit_unitary_append, circuit_unitary_singleton, hGate_embedOp,
      gateSdag_unitary, embed1_mul]
  refine ⟨le_refl 0, fun Φ => ?_, fun Φ => ?_⟩
  · dsimp [hsdagMain]
    rw [← hu t, norm_act_htcx_unitary]
  · dsimp [hsdagMain]
    rw [hu (mainWire n m t), act_embed1_mainWire_liftWork, sub_self, norm_zero, zero_mul]

lemma approxLift_shMain {n m : ℕ} (t : Fin (n + 1)) :
    ApproxLift m ([hGate (mainWire n m t)] ++ gateS (mainWire n m t)) (shMain t) 0 := by
  let c {N : ℕ} (w : Fin N) : Circuit htcxGateSet N := [hGate w] ++ gateS w
  have hu : ∀ {N : ℕ} (w : Fin N),
      (c w).unitary = embed1 (phaseS * hadamard) w := by
    intro N w
    dsimp [c]
    rw [circuit_unitary_cons, hGate_embedOp, gateS_unitary, embed1_mul]
  refine ⟨le_refl 0, fun Φ => ?_, fun Φ => ?_⟩
  · dsimp [shMain]
    rw [← hu t, norm_act_htcx_unitary]
  · dsimp [shMain]
    change ‖act (c (mainWire n m t)).unitary (liftWork (m := m) Φ) -
      liftWork (m := m) (act (embed1 (phaseS * hadamard) t) Φ)‖ ≤ 0 * ‖Φ‖
    rw [hu (mainWire n m t), act_embed1_mainWire_liftWork, sub_self, norm_zero, zero_mul]

lemma shMain_diagMain_hsdagMain_ofLp {n : ℕ} (t : Fin (n + 1)) (ang : Qubits (n + 1) → ℝ)
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) (y : Qubits (n + 1))
    (hang_f : ang (Function.update y t false) = ang y)
    (hang_t : ang (Function.update y t true) = ang y)
    (hsupp : Φ.ofLp (Function.update y t true) = 0) :
    (shMain t (diagMain t ang (hsdagMain t Φ))).ofLp y =
      (if y t then (Real.sin (ang y / 2) : ℂ) else (Real.cos (ang y / 2) : ℂ)) *
        Φ.ofLp (Function.update y t false) := by
  dsimp [shMain, hsdagMain]
  rw [act_embed1_ofLp]
  dsimp [diagMain]
  rw [act_embed1_ofLp, act_embed1_ofLp]
  simp only [Function.update_idem, hsupp, mul_zero, add_zero, hang_f, hang_t]
  dsimp [targetPhase]
  simp only [Function.update_self]
  cases y t <;> {
    simp [phaseS, phaseSdag, hadamard, Matrix.mul_apply, Fintype.sum_bool]
    ring_nf
    rw [sqrt2_inv_sq]
    try rw [Complex.I_sq]
    ring
  }

/-! ### Section 6: Ideal Amplitude Tree, Full Circuit, and Top-Level `solution` -/

lemma prefixVal_zero {n : ℕ} (z : Qubits n) : prefixVal z 0 = 0 := by
  simp [prefixVal]

lemma prefixVal_full {n : ℕ} (z : Qubits n) : prefixVal z n = bitsToNat z := by
  unfold prefixVal bitsToNat
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [i.isLt]

lemma prefixVal_congr {n : ℕ} {z1 z2 : Qubits n} {k : ℕ}
    (h : ∀ i : Fin n, (i : ℕ) < k → z1 i = z2 i) :
    prefixVal z1 k = prefixVal z2 k := by
  unfold prefixVal
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hik : (i : ℕ) < k
  · rw [h i hik]
  · simp [hik]

lemma prefixVal_update_ge {n : ℕ} (z : Qubits n) (k : ℕ) (i : Fin n) (hi : k ≤ (i : ℕ)) (b : Bool) :
    prefixVal (Function.update z i b) k = prefixVal z k := by
  refine prefixVal_congr (fun j hj => ?_)
  have hne : j ≠ i := by
    intro hji; subst hji; omega
  exact Function.update_of_ne hne b z

lemma prefixVal_succ {n : ℕ} (z : Qubits n) (k : ℕ) (hk : k < n) :
    prefixVal z (k + 1) = 2 * prefixVal z k + if z ⟨k, hk⟩ then 1 else 0 := by
  unfold prefixVal
  rw [Finset.mul_sum]
  have hsplit : ∀ i : Fin n,
      (if (i : ℕ) < k + 1 ∧ z i = true then 2 ^ (k + 1 - 1 - (i : ℕ)) else 0) =
        (2 * if (i : ℕ) < k ∧ z i = true then 2 ^ (k - 1 - (i : ℕ)) else 0) +
          if i = ⟨k, hk⟩ then (if z ⟨k, hk⟩ then 1 else 0) else 0 := by
    intro i
    by_cases hik : (i : ℕ) < k
    · have hne : i ≠ ⟨k, hk⟩ := by
        intro heq; have := congrArg Fin.val heq; dsimp at this; omega
      have hik1 : (i : ℕ) < k + 1 := by omega
      have hexp : k + 1 - 1 - (i : ℕ) = (k - 1 - (i : ℕ)) + 1 := by omega
      rw [if_neg hne, add_zero, hexp, pow_succ']
      cases z i <;> simp [hik, hik1]
    · by_cases heq : i = ⟨k, hk⟩
      · subst heq
        simp
      · have hgt : ¬ ((i : ℕ) < k + 1) := by
          intro hlt
          apply heq
          ext
          dsimp
          omega
        simp [hik, heq, hgt]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp

def flipAt {n : ℕ} (k : Fin n) : Qubits n ≃ Qubits n where
  toFun z := Function.update z k (!z k)
  invFun z := Function.update z k (!z k)
  left_inv z := by
    funext i
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  right_inv z := by
    funext i
    by_cases h : i = k
    · subst h; simp
    · simp [Function.update_of_ne h]

lemma sum_flipAt_pair {n : ℕ} (k : Fin n) (g : Qubits n → ℝ) :
    2 * ∑ z : Qubits n, g z = ∑ z : Qubits n, (g z + g (flipAt k z)) := by
  rw [Finset.sum_add_distrib, Equiv.sum_comp (flipAt k), two_mul]

noncomputable def rotStep {n : ℕ} (k : Fin n) (ang : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (Qubits n)) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun z =>
    let θ := ang (prefixVal z k.1)
    (if z k then (Real.sin (θ / 2) : ℂ) else (Real.cos (θ / 2) : ℂ)) *
      ψ.ofLp (Function.update z k false)

noncomputable def applyPhase {n : ℕ} (phi : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (Qubits n)) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun z =>
    Complex.exp ((phi (bitsToNat z) : ℂ) * Complex.I) * ψ.ofLp z

lemma norm_rotStep {n : ℕ} (k : Fin n) (ang : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (Qubits n)) (hsupp : ∀ z : Qubits n, z k = true → ψ.ofLp z = 0) :
    ‖rotStep k ang ψ‖ = ‖ψ‖ := by
  have hsq : ‖rotStep k ang ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hpair : ∀ z : Qubits n,
        ‖(rotStep k ang ψ).ofLp z‖ ^ 2 + ‖(rotStep k ang ψ).ofLp (flipAt k z)‖ ^ 2 =
          ‖ψ.ofLp z‖ ^ 2 + ‖ψ.ofLp (flipAt k z)‖ ^ 2 := by
      intro z
      dsimp [rotStep, flipAt]
      have hpref : prefixVal (Function.update z k (!z k)) k.1 = prefixVal z k.1 :=
        prefixVal_update_ge z k.1 k le_rfl (!z k)
      rw [hpref, Function.update_idem, Function.update_self]
      set θ := ang (prefixVal z k.1)
      have hcs : ‖(Real.cos (θ / 2) : ℂ)‖ ^ 2 + ‖(Real.sin (θ / 2) : ℂ)‖ ^ 2 = 1 := by
        rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          sq_abs, sq_abs]
        exact Real.cos_sq_add_sin_sq (θ / 2)
      cases hzk : z k
      · have hupd_f : Function.update z k false = z := by
          rw [← hzk, Function.update_eq_self]
        have hsupp_t : ψ.ofLp (Function.update z k true) = 0 :=
          hsupp (Function.update z k true) (Function.update_self k true z)
        simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, norm_mul, mul_pow,
          hupd_f, hsupp_t, norm_zero, sq, mul_zero, add_zero]
        linear_combination (‖ψ.ofLp z‖ * ‖ψ.ofLp z‖) * hcs
      · have hsupp_z : ψ.ofLp z = 0 := hsupp z hzk
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, norm_mul, mul_pow,
          hsupp_z, norm_zero, sq, mul_zero, zero_add]
        linear_combination (‖ψ.ofLp (Function.update z k false)‖ * ‖ψ.ofLp (Function.update z k false)‖) * hcs
    have h1 := sum_flipAt_pair k (fun z => ‖(rotStep k ang ψ).ofLp z‖ ^ 2)
    have h2 := sum_flipAt_pair k (fun z => ‖ψ.ofLp z‖ ^ 2)
    simp_rw [hpair] at h1
    linarith
  nlinarith [norm_nonneg (rotStep k ang ψ), norm_nonneg ψ]

noncomputable def xPad {d n : ℕ} (x : Fin d → ℂ) (j : Fin (2 ^ n)) : ℂ :=
  if h : (j : ℕ) < d then x ⟨j.1, h⟩ else 0

noncomputable def leafWeight {d : ℕ} (x : Fin d → ℂ) (j : ℕ) : ℝ :=
  if h : j < d then (x ⟨j, h⟩).re ^ 2 + (x ⟨j, h⟩).im ^ 2 else 0

lemma leafWeight_eq_norm_sq {d n : ℕ} (x : Fin d → ℂ) (j : Fin (2 ^ n)) :
    leafWeight x j.1 = ‖xPad (n := n) x j‖ ^ 2 := by
  dsimp [leafWeight, xPad]
  split_ifs with h
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  · simp

lemma leafWeight_nonneg {d : ℕ} (x : Fin d → ℂ) (j : ℕ) : 0 ≤ leafWeight x j := by
  dsimp [leafWeight]
  split_ifs with h
  · positivity
  · linarith

noncomputable def treeHeightSum {d : ℕ} (x : Fin d → ℂ) : ℕ → ℕ → ℝ
  | 0, j => leafWeight x j
  | m + 1, j => treeHeightSum x m (2 * j) + treeHeightSum x m (2 * j + 1)

lemma treeHeightSum_nonneg {d : ℕ} (x : Fin d → ℂ) : ∀ m j, 0 ≤ treeHeightSum x m j
  | 0, j => leafWeight_nonneg x j
  | m + 1, j => add_nonneg (treeHeightSum_nonneg x m (2 * j)) (treeHeightSum_nonneg x m (2 * j + 1))

noncomputable def exactTheta {d : ℕ} (x : Fin d → ℂ) (n k j : ℕ) : ℝ :=
  2 * Real.arccos (Real.sqrt (treeHeightSum x (n - (k + 1)) (2 * j) /
    treeHeightSum x (n - k) j))

noncomputable def exactPhi {d : ℕ} (x : Fin d → ℂ) (j : ℕ) : ℝ :=
  if h : j < d then Complex.arg (x ⟨j, h⟩) else 0

def UnusedFrom {n : ℕ} (m : ℕ) (ψ : EuclideanSpace ℂ (Qubits n)) : Prop :=
  ∀ z : Qubits n, ∀ i : Fin n, m ≤ (i : ℕ) → z i = true → ψ.ofLp z = 0

lemma cos_sin_arccos_sqrt {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    let θ := 2 * Real.arccos (Real.sqrt (A / (A + B)))
    Real.cos (θ / 2) * Real.sqrt (A + B) = Real.sqrt A ∧
    Real.sin (θ / 2) * Real.sqrt (A + B) = Real.sqrt B := by
  intro θ
  have hhalf : θ / 2 = Real.arccos (Real.sqrt (A / (A + B))) := by dsimp [θ]; ring
  rw [hhalf]
  by_cases hAB : A + B = 0
  · have hA0 : A = 0 := by linarith
    have hB0 : B = 0 := by linarith
    simp [hAB, hA0, hB0]
  · have hAB_pos : 0 < A + B := lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hAB)
    have hdiv_nonneg : 0 ≤ A / (A + B) := div_nonneg hA (le_of_lt hAB_pos)
    have hdiv_le_one : A / (A + B) ≤ 1 := (div_le_one hAB_pos).mpr (by linarith)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (A / (A + B)) := Real.sqrt_nonneg _
    have hsqrt_le_one : Real.sqrt (A / (A + B)) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hdiv_le_one
    constructor
    · rw [Real.cos_arccos (by linarith) hsqrt_le_one, ← Real.sqrt_mul hdiv_nonneg,
        div_mul_cancel₀ A (ne_of_gt hAB_pos)]
    · rw [Real.sin_arccos, Real.sq_sqrt hdiv_nonneg, ← Real.sqrt_mul (by linarith)]
      have heq : (1 - A / (A + B)) * (A + B) = B := by
        field_simp [ne_of_gt hAB_pos]
        ring
      rw [heq]

noncomputable def unnormIdealState {d n : ℕ} (x : Fin d → ℂ) (m : ℕ) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun z =>
    if ∀ i : Fin n, m ≤ (i : ℕ) → z i = false then
      (Real.sqrt (treeHeightSum x (n - m) (prefixVal z m)) : ℂ)
    else 0

lemma unusedFrom_unnormIdealState {d n : ℕ} (x : Fin d → ℂ) (m : ℕ) :
    UnusedFrom m (unnormIdealState (n := n) x m) := by
  intro z i hi hzi
  dsimp [unnormIdealState]
  rw [if_neg]
  intro hall
  exact Bool.false_ne_true ((hall i hi).symm.trans hzi)

lemma unnormIdealState_zero {d n : ℕ} (x : Fin d → ℂ) :
    unnormIdealState (n := n) x 0 =
      (Real.sqrt (treeHeightSum x n 0) : ℂ) • zeroKet n := by
  ext z
  simp only [unnormIdealState, toLp_ofLp_apply, Nat.sub_zero, prefixVal_zero, smul_ofLp_apply,
    zeroKet, ket_apply]
  by_cases hz : z = fun _ => false
  · subst hz; simp
  · have hnot : ¬ ∀ i : Fin n, z i = false := by
      intro hall; apply hz; funext i; exact hall i
    simp [hz, hnot]

lemma rotStep_unnormIdealState {d n : ℕ} (x : Fin d → ℂ) (m : ℕ) (hm : m < n) :
    rotStep ⟨m, hm⟩ (exactTheta x n m) (unnormIdealState (n := n) x m) =
      unnormIdealState (n := n) x (m + 1) := by
  ext z
  dsimp [rotStep, unnormIdealState]
  by_cases hall : ∀ i : Fin n, m + 1 ≤ (i : ℕ) → z i = false
  · have hall_upd : ∀ i : Fin n, m ≤ (i : ℕ) → (Function.update z ⟨m, hm⟩ false) i = false := by
      intro i hi
      by_cases him : i = ⟨m, hm⟩
      · subst him; simp
      · have hi1 : m + 1 ≤ (i : ℕ) := by
          have : (i : ℕ) ≠ m := fun h => him (Fin.ext h)
          omega
        rw [Function.update_of_ne him]
        exact hall i hi1
    rw [if_pos hall, if_pos hall_upd, prefixVal_update_ge z m ⟨m, hm⟩ le_rfl false]
    set j := prefixVal z m
    set A := treeHeightSum x (n - (m + 1)) (2 * j)
    set B := treeHeightSum x (n - (m + 1)) (2 * j + 1)
    have htree : treeHeightSum x (n - m) j = A + B := by
      have hsub : n - m = (n - (m + 1)) + 1 := by omega
      rw [hsub]
      rfl
    have hcs := cos_sin_arccos_sqrt (treeHeightSum_nonneg x (n - (m + 1)) (2 * j))
      (treeHeightSum_nonneg x (n - (m + 1)) (2 * j + 1))
    dsimp [exactTheta]
    rw [htree, prefixVal_succ z m hm]
    cases hzm : z ⟨m, hm⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      exact_mod_cast hcs.1
    · simp only [↓reduceIte]
      exact_mod_cast hcs.2
  · have hnot_upd : ¬ ∀ i : Fin n, m ≤ (i : ℕ) → (Function.update z ⟨m, hm⟩ false) i = false := by
      intro hall_upd
      apply hall
      intro i hi
      have him : i ≠ ⟨m, hm⟩ := by
        intro heq; have := congrArg Fin.val heq; dsimp at this; omega
      have h := hall_upd i (by omega)
      rwa [Function.update_of_ne him] at h
    rw [if_neg hall, if_neg hnot_upd, mul_zero]

lemma norm_unnormIdealState {d n : ℕ} (x : Fin d → ℂ) :
    ∀ (m : ℕ) (hm : m ≤ n),
      ‖unnormIdealState (n := n) x m‖ = Real.sqrt (treeHeightSum x n 0)
  | 0, _ => by
      rw [unnormIdealState_zero, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have hket : ‖zeroKet n‖ = 1 := by
        change IsState (zeroKet n)
        simp [IsState, zeroKet, ket]
      rw [hket, mul_one]
  | m + 1, hm => by
      rw [← rotStep_unnormIdealState x m hm,
        norm_rotStep ⟨m, hm⟩ (exactTheta x n m) (unnormIdealState x m)
          (fun z hz => unusedFrom_unnormIdealState x m z ⟨m, hm⟩ le_rfl hz),
        norm_unnormIdealState x m (Nat.le_of_lt hm)]

lemma unnormIdealState_full {d n : ℕ} (x : Fin d → ℂ) (z : Qubits n) :
    (unnormIdealState (n := n) x n).ofLp z = (‖xPad (n := n) x (bitsEquivFin n z)‖ : ℂ) := by
  dsimp [unnormIdealState]
  have hall : ∀ i : Fin n, n ≤ (i : ℕ) → z i = false := fun i hi => by omega
  rw [if_pos hall, Nat.sub_self, prefixVal_full, ← bitsEquivFin_apply]
  dsimp [treeHeightSum]
  rw [leafWeight_eq_norm_sq x (bitsEquivFin n z), Real.sqrt_sq (norm_nonneg _)]

lemma norm_unnormIdealState_full {d n : ℕ} (hd : d ≤ 2 ^ n) (x : Fin d → ℂ) :
    ‖unnormIdealState (n := n) x n‖ = ‖WithLp.toLp 2 x‖ := by
  have hsq : ‖unnormIdealState (n := n) x n‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp_rw [unnormIdealState_full, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    have hbij : ∑ z : Qubits n, ‖xPad (n := n) x (bitsEquivFin n z)‖ ^ 2 =
        ∑ j : Fin (2 ^ n), ‖xPad (n := n) x j‖ ^ 2 :=
      Fintype.sum_equiv (bitsEquivFin n) _ (fun j => ‖xPad (n := n) x j‖ ^ 2) (fun _ => rfl)
    rw [hbij]
    dsimp [xPad]
    have hsplit : ∑ j : Fin (2 ^ n), ‖if h : (j : ℕ) < d then x ⟨j.1, h⟩ else 0‖ ^ 2 =
        ∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ n) => (j : ℕ) < d),
          ‖if h : (j : ℕ) < d then x ⟨j.1, h⟩ else 0‖ ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
      rw [dif_neg (by omega)]
      simp
    rw [hsplit]
    refine Finset.sum_bij (fun (j : Fin (2 ^ n)) (hj : j ∈ Finset.univ.filter (fun j : Fin (2 ^ n) => (j : ℕ) < d)) =>
        (⟨j.1, (Finset.mem_filter.mp hj).2⟩ : Fin d))
      (fun _ _ => Finset.mem_univ _)
      (fun j1 hj1 j2 hj2 heq => by simpa [Fin.ext_iff] using heq)
      (fun i _ => ⟨⟨i.1, lt_of_lt_of_le i.2 hd⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩, rfl⟩)
      (fun j hj => ?_)
    have hlt := (Finset.mem_filter.mp hj).2
    rw [dif_pos hlt]
  nlinarith [norm_nonneg (unnormIdealState (n := n) x n), norm_nonneg (WithLp.toLp 2 x)]

lemma sqrt_treeHeightSum_root {d n : ℕ} (hd : d ≤ 2 ^ n) (x : Fin d → ℂ) :
    Real.sqrt (treeHeightSum x n 0) = ‖WithLp.toLp 2 x‖ := by
  rw [← norm_unnormIdealState x n le_rfl, norm_unnormIdealState_full hd x]

noncomputable def idealState {d n : ℕ} (x : Fin d → ℂ) (m : ℕ) :
    EuclideanSpace ℂ (Qubits n) :=
  ((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : ℂ) • unnormIdealState (n := n) x m

lemma idealState_zero {d n : ℕ} (hd : d ≤ 2 ^ n) (x : Fin d → ℂ) (hx : x ≠ 0) :
    idealState (n := n) x 0 = zeroKet n := by
  have hnorm_ne : ‖WithLp.toLp 2 x‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    apply hx
    funext i
    exact congrFun (congrArg WithLp.ofLp h0) i
  rw [idealState, unnormIdealState_zero, sqrt_treeHeightSum_root hd x, smul_smul,
    ← Complex.ofReal_mul, inv_mul_cancel₀ hnorm_ne, Complex.ofReal_one, one_smul]

lemma norm_idealState {d n : ℕ} (hd : d ≤ 2 ^ n) (x : Fin d → ℂ) (hx : x ≠ 0)
    (j : ℕ) (hj : j ≤ n) :
    ‖idealState (n := n) x j‖ = 1 := by
  have hnorm_pos : 0 < ‖WithLp.toLp 2 x‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hx
    funext i
    exact congrFun (congrArg WithLp.ofLp h0) i
  rw [idealState, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    norm_unnormIdealState x j hj, sqrt_treeHeightSum_root hd x,
    inv_mul_cancel₀ (ne_of_gt hnorm_pos)]

lemma rotStep_idealState {d n : ℕ} (x : Fin d → ℂ) (m : ℕ) (hm : m < n) :
    rotStep ⟨m, hm⟩ (exactTheta x n m) (idealState (n := n) x m) =
      idealState (n := n) x (m + 1) := by
  ext z
  simp only [idealState, rotStep, toLp_ofLp_apply, smul_ofLp_apply, ← rotStep_unnormIdealState x m hm]
  ring

lemma unusedFrom_idealState {d n : ℕ} (x : Fin d → ℂ) (m : ℕ) :
    UnusedFrom m (idealState (n := n) x m) := by
  intro z i hi hzi
  simp [idealState, unusedFrom_unnormIdealState x m z i hi hzi]

lemma applyPhase_idealState_full {d n : ℕ} (x : Fin d → ℂ) :
    applyPhase (exactPhi x) (idealState (n := n) x n) =
      padState n (normalizedVec (WithLp.toLp 2 x)) := by
  ext z
  simp only [applyPhase, idealState, toLp_ofLp_apply, smul_ofLp_apply,
    padState, normalizedVec]
  rw [unnormIdealState_full]
  by_cases hlt : bitsToNat z < d
  · have h1 : (bitsEquivFin n z : ℕ) = bitsToNat z := bitsEquivFin_apply z
    dsimp [exactPhi, xPad]
    rw [dif_pos hlt, dif_pos (by omega), dif_pos hlt]
    have hfin : (⟨(bitsEquivFin n z).1, by omega⟩ : Fin d) = ⟨bitsToNat z, hlt⟩ := by
      ext; exact h1
    rw [hfin]
    have hpolar := Complex.norm_mul_exp_arg_mul_I (x ⟨bitsToNat z, hlt⟩)
    rw [Complex.ofReal_inv]
    calc Complex.exp (↑(x ⟨bitsToNat z, hlt⟩).arg * Complex.I) *
          ((↑‖WithLp.toLp 2 x‖)⁻¹ * ↑‖x ⟨bitsToNat z, hlt⟩‖)
        = (↑‖x ⟨bitsToNat z, hlt⟩‖ * Complex.exp (↑(x ⟨bitsToNat z, hlt⟩).arg * Complex.I)) *
            (↑‖WithLp.toLp 2 x‖)⁻¹ := by ring
      _ = x ⟨bitsToNat z, hlt⟩ * (↑‖WithLp.toLp 2 x‖)⁻¹ := by rw [hpolar]
      _ = _ := by ring
  · have h1 : (bitsEquivFin n z : ℕ) = bitsToNat z := bitsEquivFin_apply z
    dsimp [xPad]
    rw [dif_neg (by omega), dif_neg hlt, norm_zero, Complex.ofReal_zero, mul_zero, mul_zero]

def projOut {n : ℕ} (y : Qubits (n + 1)) : Qubits n :=
  fun i => y ⟨i.1, Nat.lt_succ_of_lt i.2⟩

def vecMain1 {n : ℕ} (z : Qubits n) : Qubits (n + 1) :=
  fun q => if h : q.1 < n then z ⟨q.1, h⟩ else false

@[simp] lemma projOut_vecMain1 {n : ℕ} (z : Qubits n) :
    projOut (vecMain1 z) = z := by
  funext i
  dsimp [projOut, vecMain1]
  rw [if_pos i.2]

@[simp] lemma vecMain1_last {n : ℕ} (z : Qubits n) :
    vecMain1 z ⟨n, Nat.lt_succ_self n⟩ = false := by
  dsimp [vecMain1]
  rw [dif_neg (lt_irrefl n)]

lemma eq_vecMain1_iff {n : ℕ} (y : Qubits (n + 1)) (z : Qubits n) :
    y = vecMain1 z ↔ projOut y = z ∧ y ⟨n, Nat.lt_succ_self n⟩ = false := by
  constructor
  · rintro rfl
    exact ⟨projOut_vecMain1 z, vecMain1_last z⟩
  · rintro ⟨rfl, hlast⟩
    funext q
    dsimp [vecMain1, projOut]
    by_cases h : q.1 < n
    · rw [if_pos h]
    · rw [if_neg h]
      have hq : q = ⟨n, Nat.lt_succ_self n⟩ := by ext; dsimp; omega
      rw [hq, hlast]

noncomputable def liftMain1 {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Qubits (n + 1)) :=
  WithLp.toLp 2 (fun y : Qubits (n + 1) =>
    if y ⟨n, Nat.lt_succ_self n⟩ = false then ψ.ofLp (projOut y) else 0)

lemma norm_liftMain1 {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    ‖liftMain1 ψ‖ = ‖ψ‖ := by
  have hsq : ‖liftMain1 ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hinj : Function.Injective (vecMain1 (n := n)) := by
      intro z1 z2 h
      have := congrArg projOut h
      simpa using this
    have hsub : ∑ y : Qubits (n + 1), ‖(liftMain1 ψ).ofLp y‖ ^ 2 =
        ∑ y ∈ Finset.univ.image (vecMain1 (n := n)), ‖(liftMain1 ψ).ofLp y‖ ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => ?_)
      rw [Finset.mem_image] at hy
      push Not at hy
      have hne : y ⟨n, Nat.lt_succ_self n⟩ ≠ false := by
        intro hf
        exact hy (projOut y) (Finset.mem_univ _) ((eq_vecMain1_iff y (projOut y)).mpr ⟨rfl, hf⟩).symm
      dsimp [liftMain1]
      rw [if_neg hne, norm_zero, sq, mul_zero]
    rw [hsub, Finset.sum_image (fun z1 _ z2 _ h => hinj h)]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    dsimp [liftMain1]
    rw [vecMain1_last, if_pos rfl, projOut_vecMain1]
  nlinarith [norm_nonneg (liftMain1 ψ), norm_nonneg ψ]

lemma liftWork_liftMain1_zeroKet (n m : ℕ) :
    liftWork (m := m) (liftMain1 (zeroKet n)) = zeroKet (n + (1 + 2 * m)) := by
  ext z
  simp only [liftWork, liftMain1, toLp_ofLp_apply, zeroKet, ket_apply]
  by_cases hw : workProj z = 0
  · rw [if_pos hw]
    by_cases hn : mainProj z ⟨n, Nat.lt_succ_self n⟩ = false
    · rw [if_pos hn]
      by_cases hout : projOut (mainProj z) = fun _ => false
      · have hz : z = fun _ => false := by
          funext w
          by_cases hlt : w.1 < n
          · exact congrFun hout ⟨w.1, hlt⟩
          · by_cases heq : w.1 = n
            · have hw_eq : w = mainWire n m ⟨n, Nat.lt_succ_self n⟩ := by ext; exact heq
              rw [hw_eq]; exact hn
            · have hw_eq : w = workWire n m ⟨w.1 - (n + 1), by omega⟩ := by
                ext; dsimp [workWire]; omega
              rw [hw_eq]
              exact congrFun hw ⟨w.1 - (n + 1), by omega⟩
        rw [if_pos hout, if_pos hz]
      · have hz : z ≠ fun _ => false := by
          intro hz; apply hout; funext i; exact congrFun hz ⟨i.1, by omega⟩
        rw [if_neg hout, if_neg hz]
    · rw [if_neg hn]
      have hz : z ≠ fun _ => false := by
        intro hz; apply hn; exact congrFun hz (mainWire n m ⟨n, Nat.lt_succ_self n⟩)
      simp [hz]
  · rw [if_neg hw]
    have hz : z ≠ fun _ => false := by
      intro hz; apply hw; funext k; exact congrFun hz (workWire n m k)
    simp [hz]

lemma liftWork_liftMain1_eq_target {n m : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    liftWork (m := m) (liftMain1 ψ) =
      WithLp.toLp 2 (fun z : Qubits (n + (1 + 2 * m)) =>
        if ∀ k : Fin (1 + 2 * m), z (Fin.natAdd n k) = false then
          ψ.ofLp (fun i => z (Fin.castAdd (1 + 2 * m) i))
        else 0) := by
  ext z
  simp only [liftWork, liftMain1, toLp_ofLp_apply]
  have hcond : (workProj z = 0 ∧ mainProj z ⟨n, Nat.lt_succ_self n⟩ = false) ↔
      (∀ k : Fin (1 + 2 * m), z (Fin.natAdd n k) = false) := by
    constructor
    · rintro ⟨hw, hn⟩ k
      by_cases hk0 : k.1 = 0
      · have hkeq : Fin.natAdd n k = mainWire n m ⟨n, Nat.lt_succ_self n⟩ := by
          ext; dsimp [mainWire]; omega
        rw [hkeq]; exact hn
      · have hkeq : Fin.natAdd n k = workWire n m ⟨k.1 - 1, by omega⟩ := by
          ext; dsimp [workWire]; omega
        rw [hkeq]; exact congrFun hw ⟨k.1 - 1, by omega⟩
    · intro hall
      refine ⟨?_, ?_⟩
      · funext k
        have h := hall ⟨k.1 + 1, by omega⟩
        have hkeq : Fin.natAdd n (⟨k.1 + 1, by omega⟩ : Fin (1 + 2 * m)) = workWire n m k := by
          ext; dsimp [workWire]; omega
        rw [hkeq] at h
        exact h
      · have h := hall ⟨0, by omega⟩
        have h0eq : Fin.natAdd n (⟨0, by omega⟩ : Fin (1 + 2 * m)) =
            mainWire n m ⟨n, Nat.lt_succ_self n⟩ := rfl
        rw [h0eq] at h
        exact h
  have hproj : projOut (mainProj z) = fun i : Fin n => z (Fin.castAdd (1 + 2 * m) i) := rfl
  rw [hproj]
  by_cases hc : ∀ k : Fin (1 + 2 * m), z (Fin.natAdd n k) = false
  · obtain ⟨hw, hn⟩ := hcond.mpr hc
    simp [hw, hn, hc]
  · rw [if_neg hc]
    by_cases hw : workProj z = 0
    · have hn : ¬ (mainProj z ⟨n, Nat.lt_succ_self n⟩ = false) :=
        fun hn => hc (hcond.mp ⟨hw, hn⟩)
      rw [if_pos hw, if_neg hn]
    · rw [if_neg hw]

noncomputable def stageTheta {d n : ℕ} (x : Fin d → ℂ) (k : Fin n) (y : Qubits (n + 1)) : ℝ :=
  exactTheta x n k.1 (prefixVal (projOut y) k.1)

lemma dependsOnPrefix_stageTheta {d n : ℕ} (x : Fin d → ℂ) (k : Fin n) :
    DependsOnPrefix k.1 (stageTheta x k) := by
  intro y1 y2 hy
  dsimp [stageTheta]
  congr 1
  exact prefixVal_congr (fun i hi => hy ⟨i.1, Nat.lt_succ_of_lt i.2⟩ hi)

noncomputable def rotStageMain {d n : ℕ} (x : Fin d → ℂ) (k : Fin n)
    (Φ : EuclideanSpace ℂ (Qubits (n + 1))) : EuclideanSpace ℂ (Qubits (n + 1)) :=
  let t : Fin (n + 1) := ⟨k.1, Nat.lt_succ_of_lt k.2⟩
  shMain t (diagMain t (stageTheta x k) (hsdagMain t Φ))

lemma rotStageMain_liftMain1 {d n : ℕ} (x : Fin d → ℂ) (k : Fin n)
    (ψ : EuclideanSpace ℂ (Qubits n)) (hsupp : UnusedFrom k.1 ψ) :
    rotStageMain x k (liftMain1 ψ) = liftMain1 (rotStep k (exactTheta x n k.1) ψ) := by
  dsimp [rotStageMain]
  set t : Fin (n + 1) := ⟨k.1, Nat.lt_succ_of_lt k.2⟩
  ext y
  have hang_f : stageTheta x k (Function.update y t false) = stageTheta x k y :=
    dependsOnPrefix_update_ge (dependsOnPrefix_stageTheta x k) t le_rfl y false
  have hang_t : stageTheta x k (Function.update y t true) = stageTheta x k y :=
    dependsOnPrefix_update_ge (dependsOnPrefix_stageTheta x k) t le_rfl y true
  have hsupp_y : (liftMain1 ψ).ofLp (Function.update y t true) = 0 := by
    dsimp [liftMain1]
    split_ifs with hlast
    · refine hsupp (projOut (Function.update y t true)) k le_rfl ?_
      change (Function.update y t true) t = true
      exact Function.update_self t true y
    · rfl
  rw [shMain_diagMain_hsdagMain_ofLp t (stageTheta x k) (liftMain1 ψ) y hang_f hang_t hsupp_y]
  dsimp [liftMain1, rotStep, stageTheta]
  have hne_last : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠ t := by
    intro heq; have := congrArg Fin.val heq; dsimp [t] at this; omega
  rw [Function.update_of_ne hne_last]
  have hproj_upd : projOut (Function.update y t false) = Function.update (projOut y) k false := by
    funext i
    dsimp [projOut]
    by_cases hik : i = k
    · subst hik
      change (Function.update y t false) t = (Function.update (projOut y) i false) i
      simp
    · have hne : (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) ≠ t := by
        intro heq
        apply hik
        have hval : (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)).1 = t.1 := congrArg Fin.val heq
        exact Fin.ext hval
      rw [Function.update_of_ne hne, Function.update_of_ne hik]
      rfl
  rw [hproj_upd]
  have hyt : y t = projOut y k := rfl
  rw [hyt]
  split_ifs <;> ring

noncomputable def rotStageHtcx {d : ℕ} (x : Fin d → ℂ) (n m : ℕ) (hm : 1 ≤ m) (k : Fin n) :
    Circuit htcxGateSet (n + (1 + 2 * m)) :=
  let t : Fin (n + 1) := ⟨k.1, Nat.lt_succ_of_lt k.2⟩
  (gateSdag (mainWire n m t) ++ [hGate (mainWire n m t)]) ++
    ucRz n m hm k.1 (Nat.le_of_lt k.2) t le_rfl (stageTheta x k) ++
    ([hGate (mainWire n m t)] ++ gateS (mainWire n m t))

lemma rotStageHtcx_size_le {d : ℕ} (x : Fin d → ℂ) (n m : ℕ) (hm : 1 ≤ m) (k : Fin n) :
    (rotStageHtcx x n m hm k).size ≤ 2 ^ k.1 * (447 * m + 10) := by
  rw [rotStageHtcx, circuit_size_append, circuit_size_append, circuit_size_append,
    circuit_size_append, gateSdag_size, gateS_size]
  have h1 : Circuit.size ([hGate (mainWire n m ⟨k.1, Nat.lt_succ_of_lt k.2⟩)] :
      Circuit htcxGateSet (n + (1 + 2 * m))) = 1 := rfl
  have huc := ucRz_size_add_two_le n m hm k.1 (Nat.le_of_lt k.2)
    ⟨k.1, Nat.lt_succ_of_lt k.2⟩ le_rfl (stageTheta x k)
  have hpow : 1 ≤ 2 ^ k.1 := Nat.one_le_pow k.1 2 (by omega)
  rw [h1]
  calc 6 + 1 + (ucRz n m hm k.1 (Nat.le_of_lt k.2) ⟨k.1, Nat.lt_succ_of_lt k.2⟩
        le_rfl (stageTheta x k)).size + (1 + 2)
      = ((ucRz n m hm k.1 (Nat.le_of_lt k.2) ⟨k.1, Nat.lt_succ_of_lt k.2⟩
          le_rfl (stageTheta x k)).size + 2) + 8 := by omega
    _ ≤ 2 ^ k.1 * (447 * m + 2) + 2 ^ k.1 * 8 := by omega
    _ = 2 ^ k.1 * (447 * m + 10) := by ring

lemma approxLift_rotStageHtcx {d : ℕ} (x : Fin d → ℂ) (n m : ℕ) (hm : 1 ≤ m) (k : Fin n) :
    ApproxLift m (rotStageHtcx x n m hm k) (rotStageMain x k)
      ((2 : ℝ) ^ k.1 * (16 / (2 : ℝ) ^ m)) := by
  unfold rotStageHtcx rotStageMain
  set t : Fin (n + 1) := ⟨k.1, Nat.lt_succ_of_lt k.2⟩
  have h := ((approxLift_hsdagMain (m := m) t).append
    (approxLift_ucRz n m hm k.1 (Nat.le_of_lt k.2) t le_rfl (stageTheta x k)
      (dependsOnPrefix_stageTheta x k))).append (approxLift_shMain (m := m) t)
  rw [zero_add, add_zero] at h
  exact h

noncomputable def allRotStagesHtcx {d : ℕ} (x : Fin d → ℂ) (n m : ℕ) (hm : 1 ≤ m) :
    (j : ℕ) → j ≤ n → Circuit htcxGateSet (n + (1 + 2 * m))
  | 0, _ => []
  | j + 1, hj =>
      allRotStagesHtcx x n m hm j (Nat.le_of_succ_le hj) ++
        rotStageHtcx x n m hm ⟨j, hj⟩

lemma allRotStagesHtcx_size_le {d : ℕ} (x : Fin d → ℂ) (n m : ℕ) (hm : 1 ≤ m) :
    ∀ (j : ℕ) (hj : j ≤ n),
      (allRotStagesHtcx x n m hm j hj).size ≤ 2 ^ j * (447 * m + 10)
  | 0, _ => by simp [allRotStagesHtcx, Circuit.size]
  | j + 1, hj => by
      rw [allRotStagesHtcx, circuit_size_append, pow_succ', Nat.two_mul (2 ^ j), Nat.right_distrib]
      exact Nat.add_le_add (allRotStagesHtcx_size_le x n m hm j (Nat.le_of_succ_le hj))
        (rotStageHtcx_size_le x n m hm ⟨j, hj⟩)

lemma allRotStagesHtcx_error {d n : ℕ} (hd : d ≤ 2 ^ n) (x : Fin d → ℂ) (hx : x ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ (j : ℕ) (hj : j ≤ n),
      ‖act (allRotStagesHtcx x n m hm j hj).unitary (zeroKet (n + (1 + 2 * m))) -
          liftWork (m := m) (liftMain1 (idealState (n := n) x j))‖ ≤
        ((2 : ℝ) ^ j - 1) * (16 / (2 : ℝ) ^ m)
  | 0, _ => by
      rw [allRotStagesHtcx, circuit_unitary_nil, act_one, idealState_zero hd x hx,
        liftWork_liftMain1_zeroKet, sub_self, norm_zero, pow_zero, sub_self, zero_mul]
  | j + 1, hj => by
      rw [allRotStagesHtcx, act_circuit_unitary_append]
      set c_prev := allRotStagesHtcx x n m hm j (Nat.le_of_succ_le hj)
      set c_step := rotStageHtcx x n m hm ⟨j, hj⟩
      set Φ_j := liftMain1 (idealState (n := n) x j)
      have h_ideal : liftMain1 (idealState (n := n) x (j + 1)) = rotStageMain x ⟨j, hj⟩ Φ_j := by
        dsimp [Φ_j]
        rw [rotStageMain_liftMain1 x ⟨j, hj⟩ (idealState x j) (unusedFrom_idealState x j),
          rotStep_idealState x j hj]
      rw [h_ideal]
      have htri :
          ‖act c_step.unitary (act c_prev.unitary (zeroKet (n + (1 + 2 * m)))) -
              liftWork (m := m) (rotStageMain x ⟨j, hj⟩ Φ_j)‖ ≤
            ‖act c_step.unitary (act c_prev.unitary (zeroKet (n + (1 + 2 * m)))) -
                act c_step.unitary (liftWork (m := m) Φ_j)‖ +
              ‖act c_step.unitary (liftWork (m := m) Φ_j) -
                liftWork (m := m) (rotStageMain x ⟨j, hj⟩ Φ_j)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h1 :
          ‖act c_step.unitary (act c_prev.unitary (zeroKet (n + (1 + 2 * m)))) -
              act c_step.unitary (liftWork (m := m) Φ_j)‖ ≤
            ((2 : ℝ) ^ j - 1) * (16 / (2 : ℝ) ^ m) := by
        rw [← act_sub, norm_act_htcx_unitary]
        exact allRotStagesHtcx_error hd x hx m hm j (Nat.le_of_succ_le hj)
      have h2 :
          ‖act c_step.unitary (liftWork (m := m) Φ_j) -
              liftWork (m := m) (rotStageMain x ⟨j, hj⟩ Φ_j)‖ ≤
            (2 : ℝ) ^ j * (16 / (2 : ℝ) ^ m) := by
        have hb := (approxLift_rotStageHtcx x n m hm ⟨j, hj⟩).2.2 Φ_j
        have hnorm : ‖Φ_j‖ = 1 := by
          dsimp [Φ_j]
          rw [norm_liftMain1, norm_idealState hd x hx j (Nat.le_of_succ_le hj)]
        rwa [hnorm, mul_one] at hb
      have hpow : ((2 : ℝ) ^ j - 1) * (16 / (2 : ℝ) ^ m) +
          (2 : ℝ) ^ j * (16 / (2 : ℝ) ^ m) =
          ((2 : ℝ) ^ (j + 1) - 1) * (16 / (2 : ℝ) ^ m) := by
        rw [pow_succ']; ring
      linarith

noncomputable def stagePhi {d n : ℕ} (x : Fin d → ℂ) (y : Qubits (n + 1)) : ℝ :=
  -2 * exactPhi x (bitsToNat (projOut y))

lemma dependsOnPrefix_stagePhi {d n : ℕ} (x : Fin d → ℂ) :
    DependsOnPrefix n (stagePhi (n := n) x) := by
  intro y1 y2 hy
  dsimp [stagePhi]
  have hproj : projOut y1 = projOut y2 := by
    funext i
    exact hy ⟨i.1, Nat.lt_succ_of_lt i.2⟩ i.2
  rw [hproj]

lemma diagMain_stagePhi_liftMain1 {d n : ℕ} (x : Fin d → ℂ)
    (ψ : EuclideanSpace ℂ (Qubits n)) :
    diagMain ⟨n, Nat.lt_succ_self n⟩ (stagePhi x) (liftMain1 ψ) =
      liftMain1 (applyPhase (exactPhi x) ψ) := by
  ext y
  simp only [diagMain, liftMain1, applyPhase, toLp_ofLp_apply]
  by_cases hn : y ⟨n, Nat.lt_succ_self n⟩ = false
  · rw [if_pos hn, if_pos hn]
    congr 1
    dsimp [targetPhase, stagePhi]
    rw [hn, if_neg Bool.false_ne_true]
    set φ := exactPhi x (bitsToNat (projOut y))
    have hhalf : -2 * φ / 2 = -φ := by ring
    rw [hhalf, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  · rw [if_neg hn, if_neg hn, mul_zero]

noncomputable def phaseStageHtcx {d : ℕ} (x : Fin d → ℂ) (n m : ℕ) (hm : 1 ≤ m) :
    Circuit htcxGateSet (n + (1 + 2 * m)) :=
  ucRz n m hm n le_rfl ⟨n, Nat.lt_succ_self n⟩ le_rfl (stagePhi x)

noncomputable def fullHtcxCircuit {d : ℕ} (x : Fin d → ℂ) (n m : ℕ) (hm : 1 ≤ m) :
    Circuit htcxGateSet (n + (1 + 2 * m)) :=
  allRotStagesHtcx x n m hm n le_rfl ++ phaseStageHtcx x n m hm

lemma fullHtcxCircuit_size_le {d : ℕ} (x : Fin d → ℂ) (n m : ℕ) (hm : 1 ≤ m) :
    (fullHtcxCircuit x n m hm).size ≤ 914 * 2 ^ n * m := by
  dsimp [fullHtcxCircuit, phaseStageHtcx]
  rw [circuit_size_append]
  have h1 := allRotStagesHtcx_size_le x n m hm n le_rfl
  have h2 := ucRz_size_add_two_le n m hm n le_rfl ⟨n, Nat.lt_succ_self n⟩ le_rfl (stagePhi x)
  calc (allRotStagesHtcx x n m hm n le_rfl).size +
        (ucRz n m hm n le_rfl ⟨n, Nat.lt_succ_self n⟩ le_rfl (stagePhi x)).size
      ≤ 2 ^ n * (447 * m + 10) + 2 ^ n * (447 * m + 2) := by omega
    _ ≤ 2 ^ n * (457 * m) + 2 ^ n * (457 * m) := by
        refine Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
          (Nat.mul_le_mul_left _ (by omega))
    _ = 914 * 2 ^ n * m := by ring

lemma fullHtcxCircuit_error {d n : ℕ} (hd : d ≤ 2 ^ n) (x : Fin d → ℂ) (hx : x ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) :
    ‖act (fullHtcxCircuit x n m hm).unitary (zeroKet (n + (1 + 2 * m))) -
        liftWork (m := m) (liftMain1 (padState n (normalizedVec (WithLp.toLp 2 x))))‖ ≤
      32 * (2 : ℝ) ^ n / (2 : ℝ) ^ m := by
  dsimp [fullHtcxCircuit]
  rw [act_circuit_unitary_append, ← applyPhase_idealState_full x,
    ← diagMain_stagePhi_liftMain1 x (idealState (n := n) x n)]
  set c_rot := allRotStagesHtcx x n m hm n le_rfl
  set c_ph := phaseStageHtcx x n m hm
  set Φ_n := liftMain1 (idealState (n := n) x n)
  have htri :
      ‖act c_ph.unitary (act c_rot.unitary (zeroKet (n + (1 + 2 * m)))) -
          liftWork (m := m) (diagMain ⟨n, Nat.lt_succ_self n⟩ (stagePhi x) Φ_n)‖ ≤
        ‖act c_ph.unitary (act c_rot.unitary (zeroKet (n + (1 + 2 * m)))) -
            act c_ph.unitary (liftWork (m := m) Φ_n)‖ +
          ‖act c_ph.unitary (liftWork (m := m) Φ_n) -
            liftWork (m := m) (diagMain ⟨n, Nat.lt_succ_self n⟩ (stagePhi x) Φ_n)‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h1 :
      ‖act c_ph.unitary (act c_rot.unitary (zeroKet (n + (1 + 2 * m)))) -
          act c_ph.unitary (liftWork (m := m) Φ_n)‖ ≤
        ((2 : ℝ) ^ n - 1) * (16 / (2 : ℝ) ^ m) := by
    rw [← act_sub, norm_act_htcx_unitary]
    exact allRotStagesHtcx_error hd x hx m hm n le_rfl
  have h2 :
      ‖act c_ph.unitary (liftWork (m := m) Φ_n) -
          liftWork (m := m) (diagMain ⟨n, Nat.lt_succ_self n⟩ (stagePhi x) Φ_n)‖ ≤
        (2 : ℝ) ^ n * (16 / (2 : ℝ) ^ m) := by
    have hb := (approxLift_ucRz n m hm n le_rfl ⟨n, Nat.lt_succ_self n⟩ le_rfl
      (stagePhi x) (dependsOnPrefix_stagePhi x)).2.2 Φ_n
    have hnorm : ‖Φ_n‖ = 1 := by
      dsimp [Φ_n]
      rw [norm_liftMain1, norm_idealState hd x hx n le_rfl]
    rwa [hnorm, mul_one] at hb
  have hpos : (0 : ℝ) ≤ 16 / (2 : ℝ) ^ m := by positivity
  linarith [show ((2 : ℝ) ^ n - 1) * (16 / (2 : ℝ) ^ m) +
      (2 : ℝ) ^ n * (16 / (2 : ℝ) ^ m) =
      32 * (2 : ℝ) ^ n / (2 : ℝ) ^ m - 16 / (2 : ℝ) ^ m by ring]

lemma pow_clog_le_two_mul {d : ℕ} (hd : 1 ≤ d) :
    2 ^ Nat.clog 2 d ≤ 2 * d := by
  by_cases hd1 : d = 1
  · subst hd1; norm_num
  · have hd2 : 1 < d := by omega
    have hclog_pos : 0 < Nat.clog 2 d := Nat.clog_pos (by omega) hd2
    have hnot : ¬ (Nat.clog 2 d ≤ Nat.clog 2 d - 1) := by omega
    rw [Nat.clog_le_iff_le_pow (by omega)] at hnot
    push_neg at hnot
    have hpow : 2 ^ Nat.clog 2 d = 2 * 2 ^ (Nat.clog 2 d - 1) := by
      conv_lhs => rw [show Nat.clog 2 d = (Nat.clog 2 d - 1) + 1 by omega]
      rw [pow_succ']
    omega

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma log_two_le_log_two_add_d {d : ℕ} : Real.log 2 ≤ Real.log (2 + (d : ℝ)) := by
  apply Real.log_le_log (by norm_num)
  have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  linarith

lemma clog_real_le_log {d : ℕ} (hd : 1 ≤ d) :
    (Nat.clog 2 d : ℝ) ≤ (2 / Real.log 2) * Real.log (2 + (d : ℝ)) := by
  set n := Nat.clog 2 d
  have h1 : (2 : ℝ) ^ n ≤ 2 * (d : ℝ) := by
    exact_mod_cast pow_clog_le_two_mul hd
  have h2 : 2 * (d : ℝ) ≤ (2 + (d : ℝ)) ^ 2 := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have h3 : Real.log ((2 : ℝ) ^ n) ≤ Real.log ((2 + (d : ℝ)) ^ 2) :=
    Real.log_le_log (by positivity) (le_trans h1 h2)
  rw [Real.log_pow, Real.log_pow] at h3
  push_cast at h3
  have hlog2 := log_two_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
  linarith

noncomputable def chooseM (n : ℕ) (ε : ℝ) : ℕ :=
  n + ⌈Real.log (2 + 1 / ε) / Real.log 2⌉₊ + 5

lemma chooseM_ge_one (n : ℕ) (ε : ℝ) : 1 ≤ chooseM n ε := by
  dsimp [chooseM]; omega

lemma chooseM_error_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    32 * (2 : ℝ) ^ n / (2 : ℝ) ^ (chooseM n ε) ≤ ε := by
  set k := ⌈Real.log (2 + 1 / ε) / Real.log 2⌉₊
  have hlog2 := log_two_pos
  have hk_ge : Real.log (2 + 1 / ε) / Real.log 2 ≤ (k : ℝ) := Nat.le_ceil _
  have hlog_le : Real.log (2 + 1 / ε) ≤ Real.log ((2 : ℝ) ^ k) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ hlog2).mp hk_ge
  have h2e_pos : 0 < 2 + 1 / ε := by
    have : 0 < 1 / ε := one_div_pos.mpr hε
    linarith
  have hpow_k : 1 / ε ≤ (2 : ℝ) ^ k := by
    have h1 : 2 + 1 / ε ≤ (2 : ℝ) ^ k :=
      (Real.log_le_log_iff h2e_pos (by positivity)).mp hlog_le
    linarith
  have hpow_m : (2 : ℝ) ^ (chooseM n ε) = 32 * (2 : ℝ) ^ n * (2 : ℝ) ^ k := by
    change (2 : ℝ) ^ (n + k + 5) = 32 * (2 : ℝ) ^ n * (2 : ℝ) ^ k
    rw [pow_add, pow_add]
    ring
  have h32n : (0 : ℝ) < 32 * (2 : ℝ) ^ n := by positivity
  have hdiv : 32 * (2 : ℝ) ^ n / (2 : ℝ) ^ (chooseM n ε) = 1 / (2 : ℝ) ^ k := by
    rw [hpow_m]
    field_simp [ne_of_gt h32n]
  rw [hdiv, div_le_iff₀ (by positivity)]
  have h2 := (div_le_iff₀ hε).mp hpow_k
  linarith

lemma chooseM_real_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    (chooseM (Nat.clog 2 d) ε : ℝ) ≤
      (8 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by
  set n := Nat.clog 2 d
  set k := ⌈Real.log (2 + 1 / ε) / Real.log 2⌉₊
  have hlog2 := log_two_pos
  have h2e_gt1 : 1 < 2 + 1 / ε := by
    have : 0 < 1 / ε := one_div_pos.mpr hε
    linarith
  set L_d := Real.log (2 + (d : ℝ)) / Real.log 2
  set L_e := Real.log (2 + 1 / ε) / Real.log 2
  have hn : (n : ℝ) ≤ 2 * L_d := by
    have h := clog_real_le_log hd
    dsimp [L_d]
    linarith [show (2 / Real.log 2) * Real.log (2 + (d : ℝ)) =
      2 * (Real.log (2 + (d : ℝ)) / Real.log 2) by ring]
  have hLe_pos : 0 ≤ L_e :=
    div_nonneg (le_of_lt (Real.log_pos h2e_gt1)) (le_of_lt hlog2)
  have hk : (k : ℝ) ≤ L_e + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hLe_pos)
  have h1_le : 1 ≤ L_d := by
    dsimp [L_d]
    rw [one_le_div hlog2]
    exact log_two_le_log_two_add_d
  have hm_eq : (chooseM n ε : ℝ) = (n : ℝ) + (k : ℝ) + 5 := by
    dsimp [chooseM]; push_cast; ring
  have hgoal_eq : (8 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) =
      8 * L_d + 8 * L_e := by
    dsimp [L_d, L_e]; ring
  rw [hm_eq, hgoal_eq]
  linarith

end AmpEncodingGateComplexityProof

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (d : ℕ) (x : Fin d → ℂ), x ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ (w : ℕ) (circ : Circuit htcxGateSet (Nat.clog 2 d + w)),
        (circ.size : ℝ) ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        ‖act circ.unitary (zeroKet (Nat.clog 2 d + w)) -
            WithLp.toLp 2 (fun z : Qubits (Nat.clog 2 d + w) =>
              if ∀ k : Fin w, z (Fin.natAdd (Nat.clog 2 d) k) = false then
                padState (Nat.clog 2 d) (normalizedVec (WithLp.toLp 2 x))
                  (fun i => z (Fin.castAdd w i))
              else 0)‖ ≤ ε := by
  open AmpEncodingGateComplexityProof in
  refine ⟨14624 / Real.log 2, by have := log_two_pos; positivity, 1, ?_⟩
  intro d x hx ε hε
  have hd_pos : 1 ≤ d := by
    by_contra hd0
    have hd_eq : d = 0 := by omega
    subst hd_eq
    exact hx (funext fun i => Fin.elim0 i)
  set n := Nat.clog 2 d
  have hd_pow : d ≤ 2 ^ n := Nat.le_pow_clog (by omega) d
  set m := chooseM n ε
  have hm : 1 ≤ m := chooseM_ge_one n ε
  refine ⟨1 + 2 * m, fullHtcxCircuit x n m hm, ?_, ?_⟩
  · rw [pow_one]
    have hsize : ((fullHtcxCircuit x n m hm).size : ℝ) ≤ 914 * (2 : ℝ) ^ n * (m : ℝ) := by
      exact_mod_cast fullHtcxCircuit_size_le x n m hm
    have hpow : (2 : ℝ) ^ n ≤ 2 * (d : ℝ) := by
      exact_mod_cast pow_clog_le_two_mul hd_pos
    have hm_le := chooseM_real_le hd_pos hε
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    calc ((fullHtcxCircuit x n m hm).size : ℝ)
        ≤ 914 * (2 : ℝ) ^ n * (m : ℝ) := hsize
      _ ≤ 914 * (2 * (d : ℝ)) * (m : ℝ) := by nlinarith
      _ ≤ (1828 * (d : ℝ)) * ((8 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε))) := by
          nlinarith
      _ = 14624 / Real.log 2 * (d : ℝ) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by ring
  · rw [← liftWork_liftMain1_eq_target]
    exact le_trans (fullHtcxCircuit_error hd_pow x hx m hm) (chooseM_error_le n hε)

end
