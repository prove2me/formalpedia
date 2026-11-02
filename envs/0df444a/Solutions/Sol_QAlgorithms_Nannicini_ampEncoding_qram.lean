-- Prove2me | solution 1 for QAlgorithms.Nannicini.ampEncoding_qram
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:06:36.416309+00:00
-- url     : https://prove2.me/submissions/08efb5b8-f99a-46d2-812b-8338a6e0992a

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05c_Model
set_option autoImplicit false

open scoped ComplexConjugate
open QAlgorithms
open QAlgorithms.Nannicini

noncomputable section

namespace AmpEncodingQramProof

/-! ### Section 1: Basic `act`, `ket`, and `Qubits` Lemmas -/

@[simp] lemma toLp_ofLp_apply {ι : Type*} (f : ι → ℂ) (i : ι) :
    (WithLp.toLp 2 f).ofLp i = f i := rfl

@[simp] lemma add_ofLp_apply {ι : Type*} (ψ φ : EuclideanSpace ℂ ι) (i : ι) :
    (ψ + φ).ofLp i = ψ.ofLp i + φ.ofLp i := rfl

@[simp] lemma sub_ofLp_apply {ι : Type*} (ψ φ : EuclideanSpace ℂ ι) (i : ι) :
    (ψ - φ).ofLp i = ψ.ofLp i - φ.ofLp i := rfl

@[simp] lemma smul_ofLp_apply {ι : Type*} (c : ℂ) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    (c • ψ).ofLp i = c * ψ.ofLp i := rfl

@[simp] lemma real_smul_ofLp_apply {ι : Type*} (r : ℝ) (ψ : EuclideanSpace ℂ ι) (i : ι) :
    (r • ψ).ofLp i = (r : ℂ) * ψ.ofLp i := rfl

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

lemma act_smul_real {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (r : ℝ) (ψ : EuclideanSpace ℂ ι) :
    act A (r • ψ) = r • act A ψ := by
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

lemma bool_add_self (b : Bool) : b + b = false := by
  cases b <;> rfl

lemma bool_add_eq_xor (a b : Bool) : a + b = xor a b := by
  cases a <;> cases b <;> rfl

lemma bool_not_eq_add_true (b : Bool) : (!b) = b + true := by
  cases b <;> rfl

lemma qubits_zero_def (m : ℕ) : (0 : Qubits m) = fun _ => false := rfl

lemma qubits_add_self {m : ℕ} (z : Qubits m) : z + z = 0 := by
  funext i; exact bool_add_self (z i)

lemma qubits_add_cancel_right {m : ℕ} (y z : Qubits m) : y + z + z = y := by
  rw [add_assoc, qubits_add_self, add_zero]

/-! ### Section 2: Three-Register Decomposition `vec3` and `ket3` -/

def outWire (n a q : ℕ) (i : Fin n) : Fin (n + (a + q)) :=
  Fin.castAdd (a + q) i

def addrWire (n a q : ℕ) (j : Fin a) : Fin (n + (a + q)) :=
  Fin.natAdd n (Fin.castAdd q j)

def dataWire (n a q : ℕ) (r : Fin q) : Fin (n + (a + q)) :=
  Fin.natAdd n (Fin.natAdd a r)

def qramWires (n a q : ℕ) : Fin (a + q) ↪ Fin (n + (a + q)) :=
  ⟨Fin.natAdd n, Fin.natAdd_injective (a + q) n⟩

def vec3 {n a q : ℕ} (z_out : Qubits n) (z_addr : Qubits a) (z_data : Qubits q) :
    Qubits (n + (a + q)) :=
  Fin.append z_out (Fin.append z_addr z_data)

def ket3 {n a q : ℕ} (z_out : Qubits n) (z_addr : Qubits a) (z_data : Qubits q) :
    EuclideanSpace ℂ (Qubits (n + (a + q))) :=
  ket (vec3 z_out z_addr z_data)

@[simp]
lemma vec3_out {n a q : ℕ} (z_out : Qubits n) (z_addr : Qubits a) (z_data : Qubits q) (i : Fin n) :
    vec3 z_out z_addr z_data (outWire n a q i) = z_out i := by
  simp [vec3, outWire]

@[simp]
lemma vec3_addr {n a q : ℕ} (z_out : Qubits n) (z_addr : Qubits a) (z_data : Qubits q) (j : Fin a) :
    vec3 z_out z_addr z_data (addrWire n a q j) = z_addr j := by
  simp [vec3, addrWire]

@[simp]
lemma vec3_data {n a q : ℕ} (z_out : Qubits n) (z_addr : Qubits a) (z_data : Qubits q) (r : Fin q) :
    vec3 z_out z_addr z_data (dataWire n a q r) = z_data r := by
  simp [vec3, dataWire]

lemma vec3_zero (n a q : ℕ) :
    vec3 (0 : Qubits n) (0 : Qubits a) (0 : Qubits q) = (fun _ => false) := by
  funext w
  refine Fin.addCases (fun i => ?_) (fun k => Fin.addCases (fun j => ?_) (fun r => ?_) k) w <;>
    simp [vec3, qubits_zero_def]

lemma ket3_zero (n a q : ℕ) :
    ket3 (0 : Qubits n) (0 : Qubits a) (0 : Qubits q) = zeroKet (n + (a + q)) := by
  rw [ket3, vec3_zero, zeroKet]

lemma update_vec3_out {n a q : ℕ} (z_out : Qubits n) (z_addr : Qubits a) (z_data : Qubits q)
    (i : Fin n) (b : Bool) :
    Function.update (vec3 z_out z_addr z_data) (outWire n a q i) b =
      vec3 (Function.update z_out i b) z_addr z_data := by
  funext w
  refine Fin.addCases (fun i' => ?_) (fun k => ?_) w
  · by_cases h : i' = i
    · subst h; simp [vec3, outWire]
    · have hne : Fin.castAdd (a + q) i' ≠ outWire n a q i := by
        simp [outWire, h]
      rw [Function.update_of_ne hne]
      simp [vec3, Function.update_of_ne h]
  · have hne : Fin.natAdd n k ≠ outWire n a q i := by
      intro heq
      have := congrArg Fin.val heq
      simp [outWire] at this
      omega
    rw [Function.update_of_ne hne]
    simp [vec3]

lemma update_vec3_addr {n a q : ℕ} (z_out : Qubits n) (z_addr : Qubits a) (z_data : Qubits q)
    (j : Fin a) (b : Bool) :
    Function.update (vec3 z_out z_addr z_data) (addrWire n a q j) b =
      vec3 z_out (Function.update z_addr j b) z_data := by
  funext w
  refine Fin.addCases (fun i => ?_) (fun k => Fin.addCases (fun j' => ?_) (fun r => ?_) k) w
  · have hne : Fin.castAdd (a + q) i ≠ addrWire n a q j := by
      intro heq
      have := congrArg Fin.val heq
      simp [addrWire] at this
      omega
    rw [Function.update_of_ne hne]
    simp [vec3]
  · by_cases h : j' = j
    · subst h; simp [vec3, addrWire]
    · have hne : Fin.natAdd n (Fin.castAdd q j') ≠ addrWire n a q j := by
        simp [addrWire, h]
      rw [Function.update_of_ne hne]
      simp [vec3, Function.update_of_ne h]
  · have hne : Fin.natAdd n (Fin.natAdd a r) ≠ addrWire n a q j := by
      intro heq
      have := congrArg Fin.val heq
      simp [addrWire] at this
      omega
    rw [Function.update_of_ne hne]
    simp [vec3]

lemma update_vec3_data {n a q : ℕ} (z_out : Qubits n) (z_addr : Qubits a) (z_data : Qubits q)
    (r : Fin q) (b : Bool) :
    Function.update (vec3 z_out z_addr z_data) (dataWire n a q r) b =
      vec3 z_out z_addr (Function.update z_data r b) := by
  funext w
  refine Fin.addCases (fun i => ?_) (fun k => Fin.addCases (fun j => ?_) (fun r' => ?_) k) w
  · have hne : Fin.castAdd (a + q) i ≠ dataWire n a q r := by
      intro heq
      have := congrArg Fin.val heq
      simp [dataWire] at this
      omega
    rw [Function.update_of_ne hne]
    simp [vec3]
  · have hne : Fin.natAdd n (Fin.castAdd q j) ≠ dataWire n a q r := by
      intro heq
      have := congrArg Fin.val heq
      simp [dataWire] at this
      omega
    rw [Function.update_of_ne hne]
    simp [vec3]
  · by_cases h : r' = r
    · subst h; simp [vec3, dataWire]
    · have hne : Fin.natAdd n (Fin.natAdd a r') ≠ dataWire n a q r := by
        simp [dataWire, h]
      rw [Function.update_of_ne hne]
      simp [vec3, Function.update_of_ne h]

lemma outWire_ne_addrWire (n a q : ℕ) (i : Fin n) (j : Fin a) :
    outWire n a q i ≠ addrWire n a q j := by
  intro h; have := congrArg Fin.val h; simp [outWire, addrWire] at this; omega

lemma outWire_ne_dataWire (n a q : ℕ) (i : Fin n) (r : Fin q) :
    outWire n a q i ≠ dataWire n a q r := by
  intro h; have := congrArg Fin.val h; simp [outWire, dataWire] at this; omega

lemma addrWire_ne_dataWire (n a q : ℕ) (j : Fin a) (r : Fin q) :
    addrWire n a q j ≠ dataWire n a q r := by
  intro h; have := congrArg Fin.val h; simp [addrWire, dataWire] at this; omega

/-! ### Section 3: `liftAncilla` -/

noncomputable def liftAncilla {n w : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Qubits (n + w)) :=
  WithLp.toLp 2 (fun z : Qubits (n + w) =>
    if ∀ k : Fin w, z (Fin.natAdd n k) = false then
      ψ.ofLp (fun i => z (Fin.castAdd w i))
    else 0)

lemma liftAncilla_zeroKet (n w : ℕ) :
    liftAncilla (w := w) (zeroKet n) = zeroKet (n + w) := by
  ext z
  simp only [liftAncilla, toLp_ofLp_apply, zeroKet, ket_apply]
  by_cases h : ∀ k : Fin w, z (Fin.natAdd n k) = false
  · rw [if_pos h]
    by_cases h1 : (fun i : Fin n => z (Fin.castAdd w i)) = fun _ => false
    · have hz : z = fun _ => false := by
        funext m
        refine Fin.addCases (fun i => congrFun h1 i) (fun k => h k) m
      simp [h1, hz]
    · have hz : z ≠ fun _ => false := by
        intro hz; apply h1; funext i; exact congrFun hz (Fin.castAdd w i)
      simp [h1, hz]
  · rw [if_neg h]
    have hz : z ≠ fun _ => false := by
      intro hz; apply h; intro k; exact congrFun hz (Fin.natAdd n k)
    simp [hz]

lemma liftAncilla_eq_sum_ket3 {n a q : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    liftAncilla (w := a + q) ψ = ∑ z_out : Qubits n, ψ.ofLp z_out • ket3 z_out (0 : Qubits a) (0 : Qubits q) := by
  ext z
  simp only [liftAncilla, toLp_ofLp_apply, sum_ofLp_apply, smul_ofLp_apply, ket3, ket_apply]
  by_cases h : ∀ k : Fin (a + q), z (Fin.natAdd n k) = false
  · rw [if_pos h]
    have hz : z = vec3 (fun i => z (Fin.castAdd (a + q) i)) 0 0 := by
      funext m
      refine Fin.addCases (fun i => ?_) (fun k => ?_) m
      · simp [vec3]
      · rw [h k]
        refine Fin.addCases (fun j => ?_) (fun r => ?_) k <;> simp [vec3, qubits_zero_def]
    rw [Finset.sum_eq_single (fun i => z (Fin.castAdd (a + q) i))]
    · rw [if_pos hz, mul_one]
    · intro y _ hy
      rw [if_neg]
      · ring
      · intro hzy
        apply hy
        funext i
        have := congrFun hzy (Fin.castAdd (a + q) i)
        simpa [vec3] using this.symm
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [if_neg]
    · ring
    · intro hzy
      apply h
      intro k
      rw [hzy]
      refine Fin.addCases (fun j => ?_) (fun r => ?_) k <;> simp [vec3, qubits_zero_def]

lemma liftAncilla_sub {n w : ℕ} (ψ φ : EuclideanSpace ℂ (Qubits n)) :
    liftAncilla (w := w) ψ - liftAncilla (w := w) φ = liftAncilla (w := w) (ψ - φ) := by
  ext z
  simp only [liftAncilla, toLp_ofLp_apply, sub_ofLp_apply]
  split_ifs <;> ring

lemma norm_liftAncilla {n w : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    ‖liftAncilla (w := w) ψ‖ = ‖ψ‖ := by
  have hsq : ‖liftAncilla (w := w) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hbij : ∑ z : Qubits (n + w), ‖(liftAncilla (w := w) ψ).ofLp z‖ ^ 2 =
        ∑ p : Qubits n × Qubits w, ‖(liftAncilla (w := w) ψ).ofLp ((qubitsAppendEquiv n w).symm p)‖ ^ 2 :=
      Fintype.sum_equiv (qubitsAppendEquiv n w) _ _ (fun z => by
        rw [Equiv.symm_apply_apply])
    rw [hbij, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun z_out _ => ?_)
    rw [Finset.sum_eq_single (0 : Qubits w)]
    · have h0 : ∀ k : Fin w, ((qubitsAppendEquiv n w).symm (z_out, 0)) (Fin.natAdd n k) = false := by
        intro k; simp [qubitsAppendEquiv, qubits_zero_def]
      have h1 : (fun i : Fin n => ((qubitsAppendEquiv n w).symm (z_out, (0 : Qubits w))) (Fin.castAdd w i)) = z_out := by
        funext i; simp [qubitsAppendEquiv]
      change ‖(if ∀ k : Fin w, ((qubitsAppendEquiv n w).symm (z_out, 0)) (Fin.natAdd n k) = false then
        ψ.ofLp (fun i => ((qubitsAppendEquiv n w).symm (z_out, 0)) (Fin.castAdd w i)) else 0)‖ ^ 2 = ‖ψ.ofLp z_out‖ ^ 2
      rw [if_pos h0, h1]
    · intro z_anc _ hne
      have hnot : ¬ ∀ k : Fin w, ((qubitsAppendEquiv n w).symm (z_out, z_anc)) (Fin.natAdd n k) = false := by
        intro hall
        apply hne
        funext k
        have hk := hall k
        simp [qubitsAppendEquiv] at hk
        exact hk
      change ‖(if ∀ k : Fin w, ((qubitsAppendEquiv n w).symm (z_out, z_anc)) (Fin.natAdd n k) = false then
        ψ.ofLp (fun i => ((qubitsAppendEquiv n w).symm (z_out, z_anc)) (Fin.castAdd w i)) else 0)‖ ^ 2 = 0
      rw [if_neg hnot, norm_zero, sq, mul_zero]
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
  nlinarith [norm_nonneg (liftAncilla (w := w) ψ), norm_nonneg ψ]

/-! ### Section 4: Master 2-Qubit Gate Embedding & Elementary `OracleStep`s -/

def qubits2Equiv : Qubits 2 ≃ Bool × Bool where
  toFun b := (b 0, b 1)
  invFun p := ![p.1, p.2]
  left_inv b := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨b0, b1⟩
    rfl

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

lemma ofMatrix2_mem_twoQubitGateSet {M : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Gate.ofMatrix2 M ∈ twoQubitGateSet := by
  rw [twoQubitGateSet, Set.mem_setOf_eq]
  refine ⟨rfl, ?_⟩
  change (Gate.ofMatrix2 M).mat ∈ Matrix.unitaryGroup (Qubits 2) ℂ
  dsimp [Gate.ofMatrix2]
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  have hsub : M.submatrix (fun b : Qubits 2 => (b 0, b 1)) (fun b : Qubits 2 => (b 0, b 1)) =
      M.submatrix qubits2Equiv qubits2Equiv := rfl
  rw [hsub]
  have hstar : star (M.submatrix qubits2Equiv qubits2Equiv) =
      (star M).submatrix qubits2Equiv qubits2Equiv := by
    ext b c
    rfl
  rw [hstar, Matrix.submatrix_mul_equiv, hM, Matrix.submatrix_one_equiv]

lemma update_pair_eq_iff {N : ℕ} (w0 w1 : Fin N) (h01 : w0 ≠ w1) (y z : Qubits N)
    (p : Bool × Bool) :
    y = Function.update (Function.update z w0 p.1) w1 p.2 ↔
      (∀ a, a ∉ Set.range (pairEmb w0 w1 h01) → y a = z a) ∧ p = (y w0, y w1) := by
  constructor
  · intro hy
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [range_pairEmb] at ha
      push_neg at ha
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
        rw [range_pairEmb]
        push_neg
        exact ⟨ha0, ha1⟩

lemma act_embedOp_ofMatrix2_ket {N : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (w0 w1 : Fin N) (h01 : w0 ≠ w1) (z : Qubits N) :
    act (embedOp (Gate.ofMatrix2 M).mat (pairEmb w0 w1 h01)) (ket z) =
      ∑ p : Bool × Bool, M p (z w0, z w1) •
        ket (Function.update (Function.update z w0 p.1) w1 p.2) := by
  ext y
  rw [act_ket]
  dsimp [Gate.ofMatrix2, embedOp]
  simp only [toLp_ofLp_apply, sum_ofLp_apply, smul_ofLp_apply, ket_apply,
    Matrix.of_apply, Matrix.submatrix_apply, Function.comp_apply,
    pairEmb_zero, pairEmb_one]
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

def liftMat1 (U : Matrix Bool Bool ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then U p.1 q.1 else 0

lemma liftMat1_mem_unitaryGroup {U : Matrix Bool Bool ℂ}
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    liftMat1 U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  have hentry := congrFun (congrFun hU a1) b1
  cases a2 <;> cases b2 <;>
    simp [Matrix.mul_apply, Matrix.one_apply, liftMat1, Fintype.sum_prod_type] at hentry ⊢ <;>
    exact hentry

lemma act_embedOp_liftMat1_ket {N : ℕ} (U : Matrix Bool Bool ℂ)
    (w0 w1 : Fin N) (h01 : w0 ≠ w1) (z : Qubits N) :
    act (embedOp (Gate.ofMatrix2 (liftMat1 U)).mat (pairEmb w0 w1 h01)) (ket z) =
      ∑ b : Bool, U b (z w0) • ket (Function.update z w0 b) := by
  rw [act_embedOp_ofMatrix2_ket, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b0 _ => ?_)
  rw [Finset.sum_eq_single (z w1)]
  · have hupd : Function.update (Function.update z w0 b0) w1 (z w1) = Function.update z w0 b0 := by
      funext a
      by_cases ha : a = w1
      · subst ha; simp [Function.update_of_ne h01.symm]
      · simp [Function.update_of_ne ha]
    simp [liftMat1, hupd]
  · intro b1 _ hb1
    simp [liftMat1, hb1]
  · intro habs; exact False.elim (habs (Finset.mem_univ _))

lemma cnot_mem_unitaryGroup : cnot ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
    simp [cnot, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool]

lemma pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  cases a <;> cases b <;> simp [pauliX, Matrix.mul_apply, Fintype.sum_bool]

lemma rotY_mem_unitaryGroup (θ : ℝ) : rotY θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hcs : (Real.cos (θ / 2) : ℂ) ^ 2 + (Real.sin (θ / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (θ / 2)
  ext a b
  cases a <;> cases b <;>
    simp [rotY, Matrix.mul_apply, -Complex.ofReal_cos, -Complex.ofReal_sin,
      Complex.conj_ofReal]
  · linear_combination hcs
  · ring
  · ring
  · linear_combination hcs

lemma controlled_rotY_mem_unitaryGroup (θ : ℝ) :
    controlled (rotY θ) ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  have hU := rotY_mem_unitaryGroup θ
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  have hentry := congrFun (congrFun hU a2) b2
  cases a1 <;> cases b1 <;>
    simp [controlled, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type] at hentry ⊢
  · cases a2 <;> cases b2 <;> simp
  · exact hentry

def phaseMat1 (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then Complex.exp ((θ : ℂ) * Complex.I) else 1

lemma phaseMat1_mem_unitaryGroup (θ : ℝ) : phaseMat1 θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    exact Complex.exp_zero
  ext a b
  cases a <;> cases b <;>
    simp [phaseMat1, Matrix.mul_apply, Fintype.sum_bool, hexp]

def globalPhaseMat1 (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun _ => Complex.exp ((θ : ℂ) * Complex.I)

lemma globalPhaseMat1_mem_unitaryGroup (θ : ℝ) : globalPhaseMat1 θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    exact Complex.exp_zero
  ext a b
  cases a <;> cases b <;>
    simp [globalPhaseMat1, Matrix.mul_apply, Fintype.sum_bool, hexp]

/-! ### Section 5: The 6 Elementary `OracleStep`s and Circuit Composition -/

abbrev QramStep (a q N : ℕ) :=
  OracleStep twoQubitGateSet (fun _ : Fin 1 => a + q) N

abbrev QramCircuit (a q N : ℕ) :=
  OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + q) N

def mkGateStep {a q N : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ)
    (w0 w1 : Fin N) (h01 : w0 ≠ w1) : QramStep a q N :=
  .gate ⟨Gate.ofMatrix2 M, ofMatrix2_mem_twoQubitGateSet hM, pairEmb w0 w1 h01⟩

def cnotStep {a q N : ℕ} (w_c w_t : Fin N) (h : w_c ≠ w_t) : QramStep a q N :=
  mkGateStep cnot cnot_mem_unitaryGroup w_c w_t h

def notStep {a q N : ℕ} (w_t w_aux : Fin N) (h : w_t ≠ w_aux) : QramStep a q N :=
  mkGateStep (liftMat1 pauliX) (liftMat1_mem_unitaryGroup pauliX_mem_unitaryGroup) w_t w_aux h

def cRotYStep {a q N : ℕ} (θ : ℝ) (w_c w_t : Fin N) (h : w_c ≠ w_t) : QramStep a q N :=
  mkGateStep (controlled (rotY θ)) (controlled_rotY_mem_unitaryGroup θ) w_c w_t h

def phaseStep {a q N : ℕ} (θ : ℝ) (w_t w_aux : Fin N) (h : w_t ≠ w_aux) : QramStep a q N :=
  mkGateStep (liftMat1 (phaseMat1 θ)) (liftMat1_mem_unitaryGroup (phaseMat1_mem_unitaryGroup θ))
    w_t w_aux h

def globalPhaseStep {a q N : ℕ} (θ : ℝ) (w0 w1 : Fin N) (h : w0 ≠ w1) : QramStep a q N :=
  mkGateStep (liftMat1 (globalPhaseMat1 θ))
    (liftMat1_mem_unitaryGroup (globalPhaseMat1_mem_unitaryGroup θ)) w0 w1 h

def qramStep (n a q : ℕ) : QramStep a q (n + (a + q)) :=
  .query 0 false none (qramWires n a q) (by intro c hc; cases hc)

lemma act_cnotStep_ket {a q N : ℕ} (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
    (w_c w_t : Fin N) (h : w_c ≠ w_t) (z : Qubits N) :
    act (OracleStep.mat orc (cnotStep w_c w_t h)) (ket z) =
      ket (Function.update z w_t (z w_t + z w_c)) := by
  dsimp [cnotStep, mkGateStep, OracleStep.mat]
  rw [act_embedOp_ofMatrix2_ket, Fintype.sum_prod_type]
  have h0 : Function.update (Function.update z w_c (z w_c)) w_t (z w_t + z w_c) =
      Function.update z w_t (z w_t + z w_c) := by
    rw [Function.update_eq_self]
  rw [← h0]
  cases hzc : z w_c <;> cases hzt : z w_t <;>
    simp [cnot, Fintype.sum_bool, hzc, hzt, bool_add_eq_xor]

lemma act_notStep_ket {a q N : ℕ} (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
    (w_t w_aux : Fin N) (h : w_t ≠ w_aux) (z : Qubits N) :
    act (OracleStep.mat orc (notStep w_t w_aux h)) (ket z) =
      ket (Function.update z w_t (z w_t + true)) := by
  dsimp [notStep, mkGateStep, OracleStep.mat]
  rw [act_embedOp_liftMat1_ket]
  cases hzt : z w_t <;>
    simp [pauliX, Fintype.sum_bool, hzt, ← bool_not_eq_add_true]

def rotState {N : ℕ} (z : Qubits N) (w_t : Fin N) (α : ℝ) : EuclideanSpace ℂ (Qubits N) :=
  (Real.cos (α / 2) : ℂ) • ket (Function.update z w_t false) +
    (Real.sin (α / 2) : ℂ) • ket (Function.update z w_t true)

lemma rotState_zero {N : ℕ} (z : Qubits N) (w_t : Fin N) (hzt : z w_t = false) :
    rotState z w_t 0 = ket z := by
  have hupd : Function.update z w_t false = z := by
    rw [← hzt, Function.update_eq_self]
  simp [rotState, hupd]

lemma act_cRotYStep_ket {a q N : ℕ} (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
    (θ : ℝ) (w_c w_t : Fin N) (h : w_c ≠ w_t) (z : Qubits N) :
    act (OracleStep.mat orc (cRotYStep θ w_c w_t h)) (ket z) =
      let β := if z w_c then θ else 0
      (if z w_t then -(Real.sin (β / 2) : ℂ) else (Real.cos (β / 2) : ℂ)) •
        ket (Function.update z w_t false) +
      (if z w_t then (Real.cos (β / 2) : ℂ) else (Real.sin (β / 2) : ℂ)) •
        ket (Function.update z w_t true) := by
  dsimp [cRotYStep, mkGateStep, OracleStep.mat]
  rw [act_embedOp_ofMatrix2_ket, Fintype.sum_prod_type]
  cases hzc : z w_c <;> cases hzt : z w_t <;> {
    have hupd (b : Bool) : Function.update (Function.update z w_c (z w_c)) w_t b =
        Function.update z w_t b := by
      rw [Function.update_eq_self]
    rw [hzc] at hupd
    simp [controlled, rotY, Fintype.sum_bool, hupd, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    try abel
  }

lemma act_cRotYStep_rotState {a q N : ℕ}
    (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
    (θ : ℝ) (w_c w_t : Fin N) (h : w_c ≠ w_t) (z : Qubits N) (α : ℝ) :
    act (OracleStep.mat orc (cRotYStep θ w_c w_t h)) (rotState z w_t α) =
      rotState z w_t (α + if z w_c then θ else 0) := by
  unfold rotState
  rw [act_add, act_smul, act_smul, act_cRotYStep_ket, act_cRotYStep_ket]
  have hwc_f : (Function.update z w_t false) w_c = z w_c := Function.update_of_ne h false z
  have hwc_t : (Function.update z w_t true) w_c = z w_c := Function.update_of_ne h true z
  have hwt_f : (Function.update z w_t false) w_t = false := Function.update_self w_t false z
  have hwt_t : (Function.update z w_t true) w_t = true := Function.update_self w_t true z
  simp only [hwc_f, hwc_t, hwt_f, hwt_t, Function.update_idem, Bool.false_eq_true, ↓reduceIte]
  set β := if z w_c then θ else 0
  have hhalf : (α + β) / 2 = α / 2 + β / 2 := by ring
  have hcos : (Real.cos ((α + β) / 2) : ℂ) =
      (Real.cos (α / 2) : ℂ) * (Real.cos (β / 2) : ℂ) -
        (Real.sin (α / 2) : ℂ) * (Real.sin (β / 2) : ℂ) := by
    rw [hhalf]; exact_mod_cast Real.cos_add (α / 2) (β / 2)
  have hsin : (Real.sin ((α + β) / 2) : ℂ) =
      (Real.sin (α / 2) : ℂ) * (Real.cos (β / 2) : ℂ) +
        (Real.cos (α / 2) : ℂ) * (Real.sin (β / 2) : ℂ) := by
    rw [hhalf]; exact_mod_cast Real.sin_add (α / 2) (β / 2)
  rw [hcos, hsin]
  ext y
  simp only [add_ofLp_apply, smul_ofLp_apply]
  ring

lemma act_phaseStep_ket {a q N : ℕ} (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
    (θ : ℝ) (w_t w_aux : Fin N) (h : w_t ≠ w_aux) (z : Qubits N) :
    act (OracleStep.mat orc (phaseStep θ w_t w_aux h)) (ket z) =
      Complex.exp (((if z w_t then θ else 0 : ℝ) : ℂ) * Complex.I) • ket z := by
  dsimp [phaseStep, mkGateStep, OracleStep.mat]
  rw [act_embedOp_liftMat1_ket]
  cases hzt : z w_t <;> {
    have hupd : Function.update z w_t (z w_t) = z := Function.update_eq_self w_t z
    rw [hzt] at hupd
    simp [phaseMat1, Fintype.sum_bool, hupd]
  }

lemma act_globalPhaseStep_ket {a q N : ℕ}
    (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
    (θ : ℝ) (w0 w1 : Fin N) (h : w0 ≠ w1) (z : Qubits N) :
    act (OracleStep.mat orc (globalPhaseStep θ w0 w1 h)) (ket z) =
      Complex.exp ((θ : ℂ) * Complex.I) • ket z := by
  dsimp [globalPhaseStep, mkGateStep, OracleStep.mat]
  rw [act_embedOp_liftMat1_ket]
  cases hzw : z w0 <;> {
    have hupd : Function.update z w0 (z w0) = z := Function.update_eq_self w0 z
    rw [hzw] at hupd
    simp [globalPhaseMat1, Fintype.sum_bool, hupd]
  }

lemma act_qramStep_ket3 (n a q : ℕ) (M : Qubits a → Qubits q)
    (z_out : Qubits n) (z_addr : Qubits a) (z_data : Qubits q) :
    act (OracleStep.mat (fun _ => qramUnitary a q M) (qramStep n a q))
        (ket3 z_out z_addr z_data) =
      ket3 z_out z_addr (z_data + M z_addr) := by
  ext y
  rw [ket3, act_ket]
  dsimp [qramStep, OracleStep.mat, embedOp]
  simp only [toLp_ofLp_apply, Bool.false_eq_true, ↓reduceIte,
    qramUnitary, xorOracle, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply,
    Matrix.of_apply, ket3, ket_apply]
  change (if ∀ w, w ∉ Set.range (qramWires n a q) → y w = vec3 z_out z_addr z_data w then
      if (qubitsAppendEquiv a q (y ∘ qramWires n a q)).1 =
          (qubitsAppendEquiv a q (vec3 z_out z_addr z_data ∘ qramWires n a q)).1 ∧
        (qubitsAppendEquiv a q (y ∘ qramWires n a q)).2 =
          (qubitsAppendEquiv a q (vec3 z_out z_addr z_data ∘ qramWires n a q)).2 +
            M (qubitsAppendEquiv a q (vec3 z_out z_addr z_data ∘ qramWires n a q)).1
      then (1 : ℂ) else 0
    else 0) = if y = vec3 z_out z_addr (z_data + M z_addr) then 1 else 0
  have h1 : (qubitsAppendEquiv a q (vec3 z_out z_addr z_data ∘ qramWires n a q)).1 = z_addr := by
    funext j; simp [qubitsAppendEquiv, qramWires, vec3]
  have h2 : (qubitsAppendEquiv a q (vec3 z_out z_addr z_data ∘ qramWires n a q)).2 = z_data := by
    funext r; simp [qubitsAppendEquiv, qramWires, vec3]
  rw [h1, h2]
  by_cases hy : y = vec3 z_out z_addr (z_data + M z_addr)
  · rw [if_pos hy, if_pos, if_pos]
    · constructor
      · funext j; simp [hy, qubitsAppendEquiv, qramWires, vec3]
      · funext r; simp [hy, qubitsAppendEquiv, qramWires, vec3]
    · intro w hw
      refine Fin.addCases (fun i _ => ?_) (fun k hk => ?_) w hw
      · simp [hy, vec3]
      · exact False.elim (hk ⟨k, rfl⟩)
  · rw [if_neg hy]
    split_ifs with hoff hqram
    · exfalso
      apply hy
      funext w
      refine Fin.addCases (fun i => ?_) (fun k => Fin.addCases (fun j => ?_) (fun r => ?_) k) w
      · have hnot : Fin.castAdd (a + q) i ∉ Set.range (qramWires n a q) := by
          rintro ⟨k, hk⟩
          have := congrArg Fin.val hk
          simp [qramWires] at this
          omega
        simpa [vec3] using hoff (Fin.castAdd (a + q) i) hnot
      · have hj := congrFun hqram.1 j
        simpa [qubitsAppendEquiv, qramWires, vec3] using hj
      · have hr := congrFun hqram.2 r
        simpa [qubitsAppendEquiv, qramWires, vec3] using hr
    · rfl
    · rfl

@[simp] lemma unitary_nil {a q N : ℕ} (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ) :
    OracleCircuit.unitary ([] : QramCircuit a q N) orc = 1 := rfl

@[simp] lemma unitary_singleton {a q N : ℕ} (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
    (s : QramStep a q N) :
    OracleCircuit.unitary ([s] : QramCircuit a q N) orc = OracleStep.mat orc s := by
  simp [OracleCircuit.unitary]

lemma unitary_append {a q N : ℕ} (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
    (c1 c2 : QramCircuit a q N) :
    OracleCircuit.unitary (c1 ++ c2) orc = c2.unitary orc * c1.unitary orc := by
  simp [OracleCircuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma act_unitary_append {a q N : ℕ} (orc : Fin 1 → Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
    (c1 c2 : QramCircuit a q N) (ψ : EuclideanSpace ℂ (Qubits N)) :
    act ((c1 ++ c2).unitary orc) ψ = act (c2.unitary orc) (act (c1.unitary orc) ψ) := by
  rw [unitary_append, act_mul]

lemma queryCount_append {a q N : ℕ} (c1 c2 : QramCircuit a q N) :
    (c1 ++ c2).queryCount 0 = c1.queryCount 0 + c2.queryCount 0 :=
  List.countP_append

lemma gateCount_append {a q N : ℕ} (c1 c2 : QramCircuit a q N) :
    (c1 ++ c2).gateCount = c1.gateCount + c2.gateCount :=
  List.countP_append

/-! ### Section 6: Subcircuits and Stage Actions -/

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

lemma prefixVal_lt {n : ℕ} (z : Qubits n) (k : ℕ) (hk : k ≤ n) :
    prefixVal z k < 2 ^ k := by
  induction k with
  | zero => simp [prefixVal_zero]
  | succ k ih =>
    rw [prefixVal_succ z k hk]
    have ihk := ih (Nat.le_of_succ_le hk)
    rw [pow_succ']
    cases z ⟨k, hk⟩ <;> simp <;> omega

def prefixCopy (n k m : ℕ) (hk : k ≤ n) (hm : m ≤ k) (z_out : Qubits n) : Qubits (n + 1) :=
  fun j : Fin (n + 1) =>
    if h : (j : ℕ) < m then z_out ⟨j.1, lt_of_lt_of_le h (le_trans hm hk)⟩ else false

def stageAddr (n k : ℕ) (hk : k ≤ n) (z_out : Qubits n) : Qubits (n + 1) :=
  Function.update (prefixCopy n k k hk le_rfl z_out) ⟨k, Nat.lt_succ_of_le hk⟩ true

lemma prefixCopy_zero (n k : ℕ) (hk : k ≤ n) (z_out : Qubits n) :
    prefixCopy n k 0 hk (Nat.zero_le k) z_out = 0 := by
  funext j; simp [prefixCopy]; rfl

lemma prefixCopy_succ (n k m : ℕ) (hk : k ≤ n) (hm : m + 1 ≤ k) (z_out : Qubits n) :
    prefixCopy n k (m + 1) hk hm z_out =
      Function.update (prefixCopy n k m hk (Nat.le_of_succ_le hm) z_out)
        ⟨m, Nat.lt_succ_of_le (le_trans (Nat.le_of_succ_le hm) hk)⟩
        (z_out ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm hk)⟩) := by
  funext j
  by_cases hjm : (j : ℕ) = m
  · have hj_eq : j = ⟨m, Nat.lt_succ_of_le (le_trans (Nat.le_of_succ_le hm) hk)⟩ := by
      ext; exact hjm
    subst hj_eq
    simp [prefixCopy]
  · have hj_ne : j ≠ ⟨m, Nat.lt_succ_of_le (le_trans (Nat.le_of_succ_le hm) hk)⟩ := by
      intro heq; exact hjm (congrArg Fin.val heq)
    rw [Function.update_of_ne hj_ne]
    simp only [prefixCopy]
    by_cases hlt : (j : ℕ) < m
    · have hlt1 : (j : ℕ) < m + 1 := by omega
      simp [hlt, hlt1]
    · have hlt1 : ¬ (j : ℕ) < m + 1 := by omega
      simp [hlt, hlt1]

lemma stageAddr_congr (n k : ℕ) (hk : k ≤ n) {z1 z2 : Qubits n}
    (h : ∀ i : Fin n, (i : ℕ) < k → z1 i = z2 i) :
    stageAddr n k hk z1 = stageAddr n k hk z2 := by
  unfold stageAddr
  congr 1
  funext j
  simp only [prefixCopy]
  split_ifs with hj
  · exact h ⟨j.1, lt_of_lt_of_le hj hk⟩ hj
  · rfl

lemma stageAddr_update_ge (n k : ℕ) (hk : k ≤ n) (z_out : Qubits n) (i : Fin n)
    (hi : k ≤ (i : ℕ)) (b : Bool) :
    stageAddr n k hk (Function.update z_out i b) = stageAddr n k hk z_out := by
  refine stageAddr_congr n k hk (fun j hj => ?_)
  have hne : j ≠ i := by intro heq; subst heq; omega
  exact Function.update_of_ne hne b z_out

lemma stageAddr_apply_self (n k : ℕ) (hk : k ≤ n) (z_out : Qubits n) :
    stageAddr n k hk z_out ⟨k, Nat.lt_succ_of_le hk⟩ = true := by
  simp [stageAddr]

lemma stageAddr_apply_gt (n k : ℕ) (hk : k ≤ n) (z_out : Qubits n) (j : Fin (n + 1))
    (hj : k < (j : ℕ)) :
    stageAddr n k hk z_out j = false := by
  unfold stageAddr
  have hne : j ≠ ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro heq; have := congrArg Fin.val heq; dsimp at this; omega
  rw [Function.update_of_ne hne]
  simp only [prefixCopy]
  rw [dif_neg (by omega)]

lemma stageAddr_apply_lt (n k : ℕ) (hk : k ≤ n) (z_out : Qubits n) (i : Fin n) (hi : (i : ℕ) < k) :
    stageAddr n k hk z_out ⟨i.1, Nat.lt_succ_of_lt i.2⟩ = z_out i := by
  unfold stageAddr
  have hne : (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) ≠ ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro heq; have := congrArg Fin.val heq; dsimp at this; omega
  rw [Function.update_of_ne hne]
  simp [prefixCopy, hi]

lemma stageAddr_inj (n k1 k2 : ℕ) (hk1 : k1 ≤ n) (hk2 : k2 ≤ n) (z1 z2 : Qubits n)
    (heq : stageAddr n k1 hk1 z1 = stageAddr n k2 hk2 z2) :
    k1 = k2 ∧ prefixVal z1 k1 = prefixVal z2 k2 := by
  have hk : k1 = k2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := stageAddr_apply_gt n k1 hk1 z1 ⟨k2, Nat.lt_succ_of_le hk2⟩ hlt
      have h2 := stageAddr_apply_self n k2 hk2 z2
      rw [heq] at h1
      exact Bool.false_ne_true (h1.symm.trans h2)
    · have h1 := stageAddr_apply_self n k1 hk1 z1
      have h2 := stageAddr_apply_gt n k2 hk2 z2 ⟨k1, Nat.lt_succ_of_le hk1⟩ hgt
      rw [heq] at h1
      exact Bool.false_ne_true (h2.symm.trans h1)
  subst hk
  refine ⟨rfl, prefixVal_congr (fun i hi => ?_)⟩
  have h1 := stageAddr_apply_lt n k1 hk1 z1 i hi
  have h2 := stageAddr_apply_lt n k1 hk1 z2 i hi
  rw [heq] at h1
  exact h1.symm.trans h2

noncomputable def addrMap (n : ℕ) (table : ℕ → ℕ → ℕ) (u : Qubits (n + 1)) : ℕ :=
  open Classical in
  if h : ∃ (k : Fin (n + 1)) (z : Qubits n),
      stageAddr n k.1 (Nat.le_of_lt_succ k.2) z = u then
    let k := Classical.choose h
    let z := Classical.choose (Classical.choose_spec h)
    table k.1 (prefixVal z k.1)
  else 0

lemma addrMap_stageAddr (n : ℕ) (table : ℕ → ℕ → ℕ) (k : ℕ) (hk : k ≤ n) (z_out : Qubits n) :
    addrMap n table (stageAddr n k hk z_out) = table k (prefixVal z_out k) := by
  classical
  unfold addrMap
  have hex : ∃ (k' : Fin (n + 1)) (z' : Qubits n),
      stageAddr n k'.1 (Nat.le_of_lt_succ k'.2) z' = stageAddr n k hk z_out :=
    ⟨⟨k, Nat.lt_succ_of_le hk⟩, z_out, rfl⟩
  rw [dif_pos hex]
  have hspec := Classical.choose_spec (Classical.choose_spec hex)
  obtain ⟨hk_eq, hpref_eq⟩ :=
    stageAddr_inj n (Classical.choose hex).1 k
      (Nat.le_of_lt_succ (Classical.choose hex).2) hk
      (Classical.choose (Classical.choose_spec hex)) z_out hspec
  dsimp only
  rw [hpref_eq, hk_eq]

def cnotChain (n q k : ℕ) (hk : k ≤ n) :
    (m : ℕ) → m ≤ k → QramCircuit (n + 1) q (n + ((n + 1) + q))
  | 0, _ => []
  | m + 1, hm =>
      have hm_lt_n : m < n := lt_of_lt_of_le (Nat.lt_of_succ_le hm) hk
      have hm_lt_a : m < n + 1 := Nat.lt_succ_of_lt hm_lt_n
      cnotChain n q k hk m (Nat.le_of_succ_le hm) ++
        [cnotStep (outWire n (n + 1) q ⟨m, hm_lt_n⟩) (addrWire n (n + 1) q ⟨m, hm_lt_a⟩)
          (outWire_ne_addrWire n (n + 1) q _ _)]

def addrToggle (n q k : ℕ) (hk : k ≤ n) (hq : 1 ≤ q) :
    QramCircuit (n + 1) q (n + ((n + 1) + q)) :=
  cnotChain n q k hk k le_rfl ++
    [notStep (addrWire n (n + 1) q ⟨k, Nat.lt_succ_of_le hk⟩) (dataWire n (n + 1) q ⟨0, hq⟩)
      (addrWire_ne_dataWire n (n + 1) q _ _)]

lemma act_cnotChain_ket3 (n q k : ℕ) (hk : k ≤ n)
    (orc : Fin 1 → Matrix (Qubits ((n + 1) + q)) (Qubits ((n + 1) + q)) ℂ)
    (z_out : Qubits n) (z_addr : Qubits (n + 1)) (z_data : Qubits q) :
    ∀ (m : ℕ) (hm : m ≤ k),
      act ((cnotChain n q k hk m hm).unitary orc) (ket3 z_out z_addr z_data) =
        ket3 z_out (z_addr + prefixCopy n k m hk hm z_out) z_data
  | 0, hm => by
      simp [cnotChain, act_one, prefixCopy_zero]
  | m + 1, hm => by
      rw [cnotChain, act_unitary_append, act_cnotChain_ket3 n q k hk orc z_out z_addr z_data m,
        unitary_singleton, ket3, act_cnotStep_ket]
      simp only [vec3_out, vec3_addr, update_vec3_addr]
      rw [← ket3]
      congr 2
      funext j
      have hm_lt_a : m < n + 1 :=
        Nat.lt_succ_of_lt (lt_of_lt_of_le (Nat.lt_of_succ_le hm) hk)
      rw [prefixCopy_succ n k m hk hm z_out]
      by_cases hj : j = ⟨m, hm_lt_a⟩
      · subst hj
        have hfalse : prefixCopy n k m hk (Nat.le_of_succ_le hm) z_out ⟨m, hm_lt_a⟩ = false := by
          simp [prefixCopy]
        simp [Pi.add_apply, hfalse]
        rfl
      · simp [Function.update_of_ne hj, Pi.add_apply]

lemma act_addrToggle_ket3 (n q k : ℕ) (hk : k ≤ n) (hq : 1 ≤ q)
    (orc : Fin 1 → Matrix (Qubits ((n + 1) + q)) (Qubits ((n + 1) + q)) ℂ)
    (z_out : Qubits n) (z_addr : Qubits (n + 1)) (z_data : Qubits q) :
    act ((addrToggle n q k hk hq).unitary orc) (ket3 z_out z_addr z_data) =
      ket3 z_out (z_addr + stageAddr n k hk z_out) z_data := by
  rw [addrToggle, act_unitary_append, act_cnotChain_ket3, unitary_singleton, ket3, act_notStep_ket]
  simp only [vec3_addr, update_vec3_addr]
  rw [← ket3]
  congr 2
  funext j
  unfold stageAddr
  by_cases hj : j = ⟨k, Nat.lt_succ_of_le hk⟩
  · subst hj
    have hfalse : prefixCopy n k k hk le_rfl z_out ⟨k, Nat.lt_succ_of_le hk⟩ = false := by
      simp [prefixCopy]
    simp [Pi.add_apply, hfalse]
    rfl
  · simp [Function.update_of_ne hj, Pi.add_apply]

def partialBitsToNat {q : ℕ} (z_data : Qubits q) : (m : ℕ) → m ≤ q → ℕ
  | 0, _ => 0
  | m + 1, hm =>
      partialBitsToNat z_data m (Nat.le_of_succ_le hm) +
        if z_data ⟨m, hm⟩ then 2 ^ (q - 1 - m) else 0

lemma partialBitsToNat_full {q : ℕ} (z_data : Qubits q) :
    partialBitsToNat z_data q le_rfl = bitsToNat z_data := by
  unfold bitsToNat
  have h : ∀ (m : ℕ) (hm : m ≤ q),
      partialBitsToNat z_data m hm =
        ∑ r ∈ Finset.univ.filter (fun r : Fin q => (r : ℕ) < m),
          if z_data r then 2 ^ (q - 1 - (r : ℕ)) else 0 := by
    intro m hm
    induction m with
    | zero => simp [partialBitsToNat]
    | succ m ih =>
      rw [partialBitsToNat, ih (Nat.le_of_succ_le hm)]
      have hfilter : Finset.univ.filter (fun r : Fin q => (r : ℕ) < m + 1) =
          insert (⟨m, hm⟩ : Fin q) (Finset.univ.filter (fun r : Fin q => (r : ℕ) < m)) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotmem : (⟨m, hm⟩ : Fin q) ∉ Finset.univ.filter (fun r : Fin q => (r : ℕ) < m) := by
        simp
      rw [hfilter, Finset.sum_insert hnotmem, add_comm]
  rw [h q le_rfl]
  refine Finset.sum_subset (Finset.subset_univ _) (fun r _ hr => ?_)
  exfalso
  apply hr
  simp [r.isLt]

def rotYChain (n q : ℕ) (k : Fin n) :
    (m : ℕ) → m ≤ q → QramCircuit (n + 1) q (n + ((n + 1) + q))
  | 0, _ => []
  | m + 1, hm =>
      let θ := ((2 ^ (q - 1 - m) : ℕ) : ℝ) * (4 / (2 : ℝ) ^ q)
      rotYChain n q k m (Nat.le_of_succ_le hm) ++
        [cRotYStep θ (dataWire n (n + 1) q ⟨m, hm⟩) (outWire n (n + 1) q k)
          (outWire_ne_dataWire n (n + 1) q k ⟨m, hm⟩).symm]

def rotYCascade (n q : ℕ) (k : Fin n) : QramCircuit (n + 1) q (n + ((n + 1) + q)) :=
  rotYChain n q k q le_rfl

lemma act_rotYChain_ket3 (n q : ℕ) (k : Fin n)
    (orc : Fin 1 → Matrix (Qubits ((n + 1) + q)) (Qubits ((n + 1) + q)) ℂ)
    (z_out : Qubits n) (z_addr : Qubits (n + 1)) (z_data : Qubits q) (hzk : z_out k = false) :
    ∀ (m : ℕ) (hm : m ≤ q),
      act ((rotYChain n q k m hm).unitary orc) (ket3 z_out z_addr z_data) =
        rotState (vec3 z_out z_addr z_data) (outWire n (n + 1) q k)
          ((partialBitsToNat z_data m hm : ℝ) * (4 / (2 : ℝ) ^ q))
  | 0, hm => by
      simp only [rotYChain, unitary_nil, act_one, partialBitsToNat, Nat.cast_zero, zero_mul]
      rw [ket3]
      exact (rotState_zero (vec3 z_out z_addr z_data) (outWire n (n + 1) q k) (by simp [hzk])).symm
  | m + 1, hm => by
      rw [rotYChain, act_unitary_append, act_rotYChain_ket3 n q k orc z_out z_addr z_data hzk m,
        unitary_singleton, act_cRotYStep_rotState]
      congr 1
      simp only [vec3_data, partialBitsToNat, Nat.cast_add]
      cases z_data ⟨m, hm⟩ <;> simp [add_mul]

lemma act_rotYCascade_ket3 (n q : ℕ) (k : Fin n)
    (orc : Fin 1 → Matrix (Qubits ((n + 1) + q)) (Qubits ((n + 1) + q)) ℂ)
    (z_out : Qubits n) (z_addr : Qubits (n + 1)) (z_data : Qubits q) (hzk : z_out k = false) :
    let θ := (bitsToNat z_data : ℝ) * (4 / (2 : ℝ) ^ q)
    act ((rotYCascade n q k).unitary orc) (ket3 z_out z_addr z_data) =
      (Real.cos (θ / 2) : ℂ) • ket3 (Function.update z_out k false) z_addr z_data +
        (Real.sin (θ / 2) : ℂ) • ket3 (Function.update z_out k true) z_addr z_data := by
  dsimp [rotYCascade]
  rw [act_rotYChain_ket3 n q k orc z_out z_addr z_data hzk q le_rfl, partialBitsToNat_full]
  simp [rotState, update_vec3_out, ket3, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

def phaseChain (n q : ℕ) : (m : ℕ) → m ≤ q → QramCircuit (n + 1) q (n + ((n + 1) + q))
  | 0, _ => []
  | m + 1, hm =>
      let θ := ((2 ^ (q - 1 - m) : ℕ) : ℝ) * (8 / (2 : ℝ) ^ q)
      phaseChain n q m (Nat.le_of_succ_le hm) ++
        [phaseStep θ (dataWire n (n + 1) q ⟨m, hm⟩) (addrWire n (n + 1) q 0)
          (addrWire_ne_dataWire n (n + 1) q 0 ⟨m, hm⟩).symm]

def phaseCascade (n q : ℕ) (hq : 1 ≤ q) : QramCircuit (n + 1) q (n + ((n + 1) + q)) :=
  phaseChain n q q le_rfl ++
    [globalPhaseStep (-4) (addrWire n (n + 1) q 0) (dataWire n (n + 1) q ⟨0, hq⟩)
      (addrWire_ne_dataWire n (n + 1) q 0 ⟨0, hq⟩)]

lemma act_phaseChain_ket3 (n q : ℕ)
    (orc : Fin 1 → Matrix (Qubits ((n + 1) + q)) (Qubits ((n + 1) + q)) ℂ)
    (z_out : Qubits n) (z_addr : Qubits (n + 1)) (z_data : Qubits q) :
    ∀ (m : ℕ) (hm : m ≤ q),
      act ((phaseChain n q m hm).unitary orc) (ket3 z_out z_addr z_data) =
        Complex.exp ((((partialBitsToNat z_data m hm : ℝ) * (8 / (2 : ℝ) ^ q) : ℝ) : ℂ) * Complex.I) •
          ket3 z_out z_addr z_data
  | 0, hm => by
      simp [phaseChain, act_one, partialBitsToNat]
  | m + 1, hm => by
      rw [phaseChain, act_unitary_append, act_phaseChain_ket3 n q orc z_out z_addr z_data m,
        act_smul, unitary_singleton, ket3, act_phaseStep_ket, ← ket3, smul_smul, ← Complex.exp_add]
      congr 2
      simp only [vec3_data, partialBitsToNat, Nat.cast_add]
      cases z_data ⟨m, hm⟩ <;>
        { simp; try ring }

lemma act_phaseCascade_ket3 (n q : ℕ) (hq : 1 ≤ q)
    (orc : Fin 1 → Matrix (Qubits ((n + 1) + q)) (Qubits ((n + 1) + q)) ℂ)
    (z_out : Qubits n) (z_addr : Qubits (n + 1)) (z_data : Qubits q) :
    let φ := (bitsToNat z_data : ℝ) * (8 / (2 : ℝ) ^ q) - 4
    act ((phaseCascade n q hq).unitary orc) (ket3 z_out z_addr z_data) =
      Complex.exp ((φ : ℂ) * Complex.I) • ket3 z_out z_addr z_data := by
  dsimp [phaseCascade]
  rw [act_unitary_append, act_phaseChain_ket3 n q orc z_out z_addr z_data q le_rfl,
    partialBitsToNat_full, act_smul, unitary_singleton, ket3, act_globalPhaseStep_ket,
    ← ket3, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

def rotStageCircuit (n q : ℕ) (hq : 1 ≤ q) (k : Fin n) :
    QramCircuit (n + 1) q (n + ((n + 1) + q)) :=
  addrToggle n q k.1 (Nat.le_of_lt k.2) hq ++
    [qramStep n (n + 1) q] ++
    rotYCascade n q k ++
    [qramStep n (n + 1) q] ++
    addrToggle n q k.1 (Nat.le_of_lt k.2) hq

def phaseStageCircuit (n q : ℕ) (hq : 1 ≤ q) :
    QramCircuit (n + 1) q (n + ((n + 1) + q)) :=
  addrToggle n q n le_rfl hq ++
    [qramStep n (n + 1) q] ++
    phaseCascade n q hq ++
    [qramStep n (n + 1) q] ++
    addrToggle n q n le_rfl hq

lemma act_rotStageCircuit_ket3 (n q : ℕ) (hq : 1 ≤ q) (M : Qubits (n + 1) → Qubits q)
    (k : Fin n) (z_out : Qubits n) (hzk : z_out k = false) :
    let u := stageAddr n k.1 (Nat.le_of_lt k.2) z_out
    let θ := (bitsToNat (M u) : ℝ) * (4 / (2 : ℝ) ^ q)
    act ((rotStageCircuit n q hq k).unitary (fun _ => qramUnitary (n + 1) q M))
        (ket3 z_out 0 0) =
      (Real.cos (θ / 2) : ℂ) • ket3 (Function.update z_out k false) 0 0 +
        (Real.sin (θ / 2) : ℂ) • ket3 (Function.update z_out k true) 0 0 := by
  unfold rotStageCircuit
  set orc : Fin 1 → Matrix (Qubits ((n + 1) + q)) (Qubits ((n + 1) + q)) ℂ :=
    fun _ => qramUnitary (n + 1) q M
  set u := stageAddr n k.1 (Nat.le_of_lt k.2) z_out
  rw [act_unitary_append, act_unitary_append, act_unitary_append, act_unitary_append]
  rw [act_addrToggle_ket3, zero_add]
  rw [unitary_singleton, act_qramStep_ket3, zero_add]
  rw [act_rotYCascade_ket3 n q k orc z_out u (M u) hzk]
  rw [act_add, act_smul, act_smul, act_qramStep_ket3, act_qramStep_ket3,
    qubits_add_self]
  rw [act_add, act_smul, act_smul, act_addrToggle_ket3, act_addrToggle_ket3]
  have hu_f : stageAddr n k.1 (Nat.le_of_lt k.2) (Function.update z_out k false) = u :=
    stageAddr_update_ge n k.1 (Nat.le_of_lt k.2) z_out k le_rfl false
  have hu_t : stageAddr n k.1 (Nat.le_of_lt k.2) (Function.update z_out k true) = u :=
    stageAddr_update_ge n k.1 (Nat.le_of_lt k.2) z_out k le_rfl true
  rw [hu_f, hu_t, qubits_add_self]

lemma act_phaseStageCircuit_ket3 (n q : ℕ) (hq : 1 ≤ q) (M : Qubits (n + 1) → Qubits q)
    (z_out : Qubits n) :
    let u := stageAddr n n le_rfl z_out
    let φ := (bitsToNat (M u) : ℝ) * (8 / (2 : ℝ) ^ q) - 4
    act ((phaseStageCircuit n q hq).unitary (fun _ => qramUnitary (n + 1) q M))
        (ket3 z_out 0 0) =
      Complex.exp ((φ : ℂ) * Complex.I) • ket3 z_out 0 0 := by
  dsimp [phaseStageCircuit]
  set orc : Fin 1 → Matrix (Qubits ((n + 1) + q)) (Qubits ((n + 1) + q)) ℂ :=
    fun _ => qramUnitary (n + 1) q M
  set u := stageAddr n n le_rfl z_out
  rw [act_unitary_append, act_unitary_append, act_unitary_append, act_unitary_append]
  rw [act_addrToggle_ket3, zero_add]
  rw [unitary_singleton, act_qramStep_ket3, zero_add]
  rw [act_phaseCascade_ket3]
  rw [act_smul, act_qramStep_ket3, qubits_add_self]
  rw [act_smul, act_addrToggle_ket3, qubits_add_self]

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

lemma act_rotStageCircuit_liftAncilla (n q : ℕ) (hq : 1 ≤ q) (M : Qubits (n + 1) → Qubits q)
    (ang : ℕ → ℝ) (k : Fin n)
    (hang : ∀ z_out : Qubits n,
      (bitsToNat (M (stageAddr n k.1 (Nat.le_of_lt k.2) z_out)) : ℝ) * (4 / (2 : ℝ) ^ q) =
        ang (prefixVal z_out k.1))
    (ψ : EuclideanSpace ℂ (Qubits n)) (hsupp : ∀ z : Qubits n, z k = true → ψ.ofLp z = 0) :
    act ((rotStageCircuit n q hq k).unitary (fun _ => qramUnitary (n + 1) q M))
        (liftAncilla (w := (n + 1) + q) ψ) =
      liftAncilla (w := (n + 1) + q) (rotStep k ang ψ) := by
  rw [liftAncilla_eq_sum_ket3, act_sum]
  have hterm : ∀ z_out : Qubits n,
      act ((rotStageCircuit n q hq k).unitary (fun _ => qramUnitary (n + 1) q M))
          (ψ.ofLp z_out • ket3 z_out 0 0) =
        ψ.ofLp z_out •
          ((Real.cos (ang (prefixVal z_out k.1) / 2) : ℂ) •
              ket3 (Function.update z_out k false) (0 : Qubits (n + 1)) (0 : Qubits q) +
            (Real.sin (ang (prefixVal z_out k.1) / 2) : ℂ) •
              ket3 (Function.update z_out k true) (0 : Qubits (n + 1)) (0 : Qubits q)) := by
    intro z_out
    by_cases hzk : z_out k = false
    · rw [act_smul, act_rotStageCircuit_ket3 n q hq M k z_out hzk, hang z_out]
    · have hzt : z_out k = true := by cases h : z_out k <;> simp_all
      rw [hsupp z_out hzt, zero_smul, act_zero, zero_smul]
  simp_rw [hterm]
  rw [liftAncilla_eq_sum_ket3]
  ext w
  simp only [sum_ofLp_apply, smul_ofLp_apply, add_ofLp_apply]
  by_cases hw : ∀ m : Fin ((n + 1) + q), w (Fin.natAdd n m) = false
  · set y : Qubits n := fun i => w (Fin.castAdd ((n + 1) + q) i)
    have hw_eq : ∀ z : Qubits n, (ket3 z (0 : Qubits (n + 1)) (0 : Qubits q)).ofLp w =
        if y = z then 1 else 0 := by
      intro z
      rw [ket3, ket_apply]
      by_cases hyz : y = z
      · have hweq : w = vec3 z 0 0 := by
          funext idx
          refine Fin.addCases (fun i => ?_) (fun m => ?_) idx
          · simpa [vec3, y] using congrFun hyz i
          · rw [hw m]
            refine Fin.addCases (fun j => ?_) (fun r => ?_) m <;> simp [vec3, qubits_zero_def]
        simp [hyz, hweq]
      · have hwne : w ≠ vec3 z 0 0 := by
          intro hweq
          apply hyz
          funext i
          simpa [vec3, y] using congrFun hweq (Fin.castAdd ((n + 1) + q) i)
        simp [hyz, hwne]
    simp_rw [hw_eq]
    rw [Finset.sum_eq_single (Function.update y k false)]
    · rw [Finset.sum_eq_single y]
      · have hpref : prefixVal (Function.update y k false) k.1 = prefixVal y k.1 :=
          prefixVal_update_ge y k.1 k le_rfl false
        rw [Function.update_idem, Function.update_idem, hpref]
        dsimp [rotStep]
        cases hyk : y k
        · have hy_f : y = Function.update y k false := by
            rw [← hyk, Function.update_eq_self]
          have hy_t : y ≠ Function.update y k true := by
            intro h; have := congrFun h k; simp [hyk] at this
          rw [if_pos hy_f, if_neg hy_t]
          simp; try ring
        · have hy_t : y = Function.update y k true := by
            rw [← hyk, Function.update_eq_self]
          have hy_f : y ≠ Function.update y k false := by
            intro h; have := congrFun h k; simp [hyk] at this
          rw [if_neg hy_f, if_pos hy_t]
          simp; try ring
      · intro z _ hzy
        simp [Ne.symm hzy]
      · intro habs; exact False.elim (habs (Finset.mem_univ _))
    · intro z_out _ hz_ne
      by_cases hzk : z_out k = false
      · have h1 : y ≠ Function.update z_out k false := by
          intro hy
          apply hz_ne
          rw [hy, Function.update_idem, ← hzk, Function.update_eq_self]
        have h2 : y ≠ Function.update z_out k true := by
          intro hy
          apply hz_ne
          rw [hy, Function.update_idem, ← hzk, Function.update_eq_self]
        simp [h1, h2]
      · have hzt : z_out k = true := by cases h : z_out k <;> simp_all
        simp [hsupp z_out hzt]
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
  · have hw_zero : ∀ z : Qubits n, (ket3 z (0 : Qubits (n + 1)) (0 : Qubits q)).ofLp w = 0 := by
      intro z
      rw [ket3, ket_apply, if_neg]
      intro hweq
      apply hw
      intro m
      rw [hweq]
      refine Fin.addCases (fun j => ?_) (fun r => ?_) m <;> simp [vec3, qubits_zero_def]
    simp_rw [hw_zero]
    simp

lemma act_phaseStageCircuit_liftAncilla (n q : ℕ) (hq : 1 ≤ q) (M : Qubits (n + 1) → Qubits q)
    (phi : ℕ → ℝ)
    (hphi : ∀ z_out : Qubits n,
      (bitsToNat (M (stageAddr n n le_rfl z_out)) : ℝ) * (8 / (2 : ℝ) ^ q) - 4 =
        phi (bitsToNat z_out))
    (ψ : EuclideanSpace ℂ (Qubits n)) :
    act ((phaseStageCircuit n q hq).unitary (fun _ => qramUnitary (n + 1) q M))
        (liftAncilla (w := (n + 1) + q) ψ) =
      liftAncilla (w := (n + 1) + q) (applyPhase phi ψ) := by
  rw [liftAncilla_eq_sum_ket3, act_sum, liftAncilla_eq_sum_ket3]
  refine Finset.sum_congr rfl (fun z_out _ => ?_)
  rw [act_smul, act_phaseStageCircuit_ket3 n q hq M z_out, hphi z_out, smul_smul, mul_comm]
  rfl

def allRotStages (n q : ℕ) (hq : 1 ≤ q) :
    (m : ℕ) → m ≤ n → QramCircuit (n + 1) q (n + ((n + 1) + q))
  | 0, _ => []
  | m + 1, hm =>
      allRotStages n q hq m (Nat.le_of_succ_le hm) ++
        rotStageCircuit n q hq ⟨m, hm⟩

def fullCircuit (n q : ℕ) (hq : 1 ≤ q) : QramCircuit (n + 1) q (n + ((n + 1) + q)) :=
  allRotStages n q hq n le_rfl ++ phaseStageCircuit n q hq

lemma cnotChain_counts (n q k : ℕ) (hk : k ≤ n) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (cnotChain n q k hk m hm).queryCount 0 = 0 ∧
      (cnotChain n q k hk m hm).gateCount = m ∧
      (∀ s ∈ cnotChain n q k hk m hm, uncontrolledStep s)
  | 0, _ => ⟨rfl, rfl, by intro s hs; cases hs⟩
  | m + 1, hm => by
      obtain ⟨hq_m, hg_m, hu_m⟩ := cnotChain_counts n q k hk m (Nat.le_of_succ_le hm)
      refine ⟨?_, ?_, ?_⟩
      · rw [cnotChain, queryCount_append, hq_m]; rfl
      · rw [cnotChain, gateCount_append, hg_m]; rfl
      · intro s hs
        rw [cnotChain, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · exact hu_m s hs
        · trivial

lemma addrToggle_counts (n q k : ℕ) (hk : k ≤ n) (hq : 1 ≤ q) :
    (addrToggle n q k hk hq).queryCount 0 = 0 ∧
    (addrToggle n q k hk hq).gateCount = k + 1 ∧
    (∀ s ∈ addrToggle n q k hk hq, uncontrolledStep s) := by
  obtain ⟨hq_c, hg_c, hu_c⟩ := cnotChain_counts n q k hk k le_rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [addrToggle, queryCount_append, hq_c]; rfl
  · rw [addrToggle, gateCount_append, hg_c]; rfl
  · intro s hs
    rw [addrToggle, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact hu_c s hs
    · trivial

lemma rotYChain_counts (n q : ℕ) (k : Fin n) :
    ∀ (m : ℕ) (hm : m ≤ q),
      (rotYChain n q k m hm).queryCount 0 = 0 ∧
      (rotYChain n q k m hm).gateCount = m ∧
      (∀ s ∈ rotYChain n q k m hm, uncontrolledStep s)
  | 0, _ => ⟨rfl, rfl, by intro s hs; cases hs⟩
  | m + 1, hm => by
      obtain ⟨hq_m, hg_m, hu_m⟩ := rotYChain_counts n q k m (Nat.le_of_succ_le hm)
      refine ⟨?_, ?_, ?_⟩
      · rw [rotYChain, queryCount_append, hq_m]; rfl
      · rw [rotYChain, gateCount_append, hg_m]; rfl
      · intro s hs
        rw [rotYChain, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · exact hu_m s hs
        · trivial

lemma phaseChain_counts (n q : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ q),
      (phaseChain n q m hm).queryCount 0 = 0 ∧
      (phaseChain n q m hm).gateCount = m ∧
      (∀ s ∈ phaseChain n q m hm, uncontrolledStep s)
  | 0, _ => ⟨rfl, rfl, by intro s hs; cases hs⟩
  | m + 1, hm => by
      obtain ⟨hq_m, hg_m, hu_m⟩ := phaseChain_counts n q m (Nat.le_of_succ_le hm)
      refine ⟨?_, ?_, ?_⟩
      · rw [phaseChain, queryCount_append, hq_m]; rfl
      · rw [phaseChain, gateCount_append, hg_m]; rfl
      · intro s hs
        rw [phaseChain, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · exact hu_m s hs
        · trivial

lemma phaseCascade_counts (n q : ℕ) (hq : 1 ≤ q) :
    (phaseCascade n q hq).queryCount 0 = 0 ∧
    (phaseCascade n q hq).gateCount = q + 1 ∧
    (∀ s ∈ phaseCascade n q hq, uncontrolledStep s) := by
  obtain ⟨hq_c, hg_c, hu_c⟩ := phaseChain_counts n q q le_rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [phaseCascade, queryCount_append, hq_c]; rfl
  · rw [phaseCascade, gateCount_append, hg_c]; rfl
  · intro s hs
    rw [phaseCascade, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact hu_c s hs
    · trivial

lemma rotStageCircuit_counts (n q : ℕ) (hq : 1 ≤ q) (k : Fin n) :
    (rotStageCircuit n q hq k).queryCount 0 = 2 ∧
    (rotStageCircuit n q hq k).gateCount ≤ 2 * n + q + 3 ∧
    (∀ s ∈ rotStageCircuit n q hq k, uncontrolledStep s) := by
  obtain ⟨hq_a, hg_a, hu_a⟩ := addrToggle_counts n q k.1 (Nat.le_of_lt k.2) hq
  obtain ⟨hq_r, hg_r, hu_r⟩ := rotYChain_counts n q k q le_rfl
  have hq_q : OracleCircuit.queryCount ([qramStep n (n + 1) q] : QramCircuit (n + 1) q (n + ((n + 1) + q))) 0 = 1 := rfl
  have hg_q : OracleCircuit.gateCount ([qramStep n (n + 1) q] : QramCircuit (n + 1) q (n + ((n + 1) + q))) = 0 := rfl
  refine ⟨?_, ?_, ?_⟩
  · dsimp [rotStageCircuit, rotYCascade]
    rw [queryCount_append, queryCount_append, queryCount_append, queryCount_append,
      hq_a, hq_r, hq_q]
  · dsimp [rotStageCircuit, rotYCascade]
    rw [gateCount_append, gateCount_append, gateCount_append, gateCount_append,
      hg_a, hg_r, hg_q]
    have hk := k.isLt
    omega
  · intro s hs
    dsimp [rotStageCircuit, rotYCascade] at hs
    rcases List.mem_append.mp hs with hs | hs
    · rcases List.mem_append.mp hs with hs | hs
      · rcases List.mem_append.mp hs with hs | hs
        · rcases List.mem_append.mp hs with hs | hs
          · exact hu_a s hs
          · rcases List.mem_singleton.mp hs with rfl; rfl
        · exact hu_r s hs
      · rcases List.mem_singleton.mp hs with rfl; rfl
    · exact hu_a s hs

lemma phaseStageCircuit_counts (n q : ℕ) (hq : 1 ≤ q) :
    (phaseStageCircuit n q hq).queryCount 0 = 2 ∧
    (phaseStageCircuit n q hq).gateCount ≤ 2 * n + q + 3 ∧
    (∀ s ∈ phaseStageCircuit n q hq, uncontrolledStep s) := by
  obtain ⟨hq_a, hg_a, hu_a⟩ := addrToggle_counts n q n le_rfl hq
  obtain ⟨hq_p, hg_p, hu_p⟩ := phaseCascade_counts n q hq
  have hq_q : OracleCircuit.queryCount ([qramStep n (n + 1) q] : QramCircuit (n + 1) q (n + ((n + 1) + q))) 0 = 1 := rfl
  have hg_q : OracleCircuit.gateCount ([qramStep n (n + 1) q] : QramCircuit (n + 1) q (n + ((n + 1) + q))) = 0 := rfl
  refine ⟨?_, ?_, ?_⟩
  · dsimp [phaseStageCircuit]
    rw [queryCount_append, queryCount_append, queryCount_append, queryCount_append,
      hq_a, hq_p, hq_q]
  · dsimp [phaseStageCircuit]
    rw [gateCount_append, gateCount_append, gateCount_append, gateCount_append,
      hg_a, hg_p, hg_q]
    omega
  · intro s hs
    dsimp [phaseStageCircuit] at hs
    rcases List.mem_append.mp hs with hs | hs
    · rcases List.mem_append.mp hs with hs | hs
      · rcases List.mem_append.mp hs with hs | hs
        · rcases List.mem_append.mp hs with hs | hs
          · exact hu_a s hs
          · rcases List.mem_singleton.mp hs with rfl; rfl
        · exact hu_p s hs
      · rcases List.mem_singleton.mp hs with rfl; rfl
    · exact hu_a s hs

lemma allRotStages_counts (n q : ℕ) (hq : 1 ≤ q) :
    ∀ (m : ℕ) (hm : m ≤ n),
      (allRotStages n q hq m hm).queryCount 0 = 2 * m ∧
      (allRotStages n q hq m hm).gateCount ≤ m * (2 * n + q + 3) ∧
      (∀ s ∈ allRotStages n q hq m hm, uncontrolledStep s)
  | 0, _ => ⟨rfl, by simp [allRotStages, OracleCircuit.gateCount], by intro s hs; cases hs⟩
  | m + 1, hm => by
      obtain ⟨hq_m, hg_m, hu_m⟩ := allRotStages_counts n q hq m (Nat.le_of_succ_le hm)
      obtain ⟨hq_s, hg_s, hu_s⟩ := rotStageCircuit_counts n q hq ⟨m, hm⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [allRotStages, queryCount_append, hq_m, hq_s]; omega
      · rw [allRotStages, gateCount_append, Nat.succ_mul]
        exact Nat.add_le_add hg_m hg_s
      · intro s hs
        rw [allRotStages, List.mem_append] at hs
        rcases hs with hs | hs
        · exact hu_m s hs
        · exact hu_s s hs

lemma fullCircuit_counts (n q : ℕ) (hq : 1 ≤ q) :
    (fullCircuit n q hq).queryCount 0 = 2 * (n + 1) ∧
    (fullCircuit n q hq).gateCount ≤ (n + 1) * (2 * n + q + 3) ∧
    (∀ s ∈ fullCircuit n q hq, uncontrolledStep s) := by
  obtain ⟨hq_a, hg_a, hu_a⟩ := allRotStages_counts n q hq n le_rfl
  obtain ⟨hq_p, hg_p, hu_p⟩ := phaseStageCircuit_counts n q hq
  refine ⟨?_, ?_, ?_⟩
  · rw [fullCircuit, queryCount_append, hq_a, hq_p]; omega
  · rw [fullCircuit, gateCount_append, Nat.succ_mul]
    exact Nat.add_le_add hg_a hg_p
  · intro s hs
    rw [fullCircuit, List.mem_append] at hs
    rcases hs with hs | hs
    · exact hu_a s hs
    · exact hu_p s hs

/-! ### Section 7: Straight-Line Arithmetic Program `P` and `qramWords` -/

lemma arithRun_nil (input : List ℝ) : arithRun [] input = input := rfl

lemma arithRun_singleton (g : ArithInstr) (input : List ℝ) :
    arithRun [g] input = input ++ [g.value input] := rfl

lemma arithRun_append (P1 P2 : List ArithInstr) (input : List ℝ) :
    arithRun (P1 ++ P2) input = arithRun P2 (arithRun P1 input) :=
  List.foldl_append

lemma arithRun_length (P : List ArithInstr) (input : List ℝ) :
    (arithRun P input).length = input.length + P.length := by
  induction P generalizing input with
  | nil => simp [arithRun]
  | cons g P ih =>
    change (arithRun P (input ++ [g.value input])).length = _
    rw [ih (input ++ [g.value input])]
    simp
    omega

lemma getD_append_left (l1 l2 : List ℝ) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i 0 = l1.getD i 0 := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_append_right (l1 l2 : List ℝ) (i : ℕ) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i 0 = l2.getD (i - l1.length) 0 := by
  simp [List.getD, List.getElem?_append_right hi]

lemma getD_append_singleton_self (l : List ℝ) (v : ℝ) :
    (l ++ [v]).getD l.length 0 = v := by
  simp [List.getD]

lemma arithRun_getD_of_lt (P : List ArithInstr) (input : List ℝ) (i : ℕ)
    (hi : i < input.length) :
    (arithRun P input).getD i 0 = input.getD i 0 := by
  induction P generalizing input with
  | nil => rfl
  | cons g P ih =>
    change (arithRun P (input ++ [g.value input])).getD i 0 = _
    rw [ih (input ++ [g.value input]) (by simp; omega)]
    exact getD_append_left input [g.value input] i hi

lemma arithRun_eval_at (P0 : List ArithInstr) (g : ArithInstr) (P_rest : List ArithInstr)
    (input : List ℝ) :
    (arithRun (P0 ++ [g] ++ P_rest) input).getD (input.length + P0.length) 0 =
      g.value (arithRun P0 input) := by
  rw [arithRun_append, arithRun_append, arithRun_singleton]
  have hlen : (arithRun P0 input).length = input.length + P0.length :=
    arithRun_length P0 input
  rw [arithRun_getD_of_lt P_rest _ _ (by simp [hlen])]
  rw [← hlen, getD_append_singleton_self]

lemma flatMap_range_length (f : ℕ → List ArithInstr) (c : ℕ) (hc : ∀ j, (f j).length = c) (M : ℕ) :
    ((List.range M).flatMap f).length = c * M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton, hc]
    ring

lemma flatMap_range_split (f : ℕ → List ArithInstr) (c : ℕ) (hc : ∀ j, (f j).length = c)
    (M j : ℕ) (hj : j < M) :
    ∃ P_before P_after : List ArithInstr,
      (List.range M).flatMap f = P_before ++ f j ++ P_after ∧
      P_before.length = c * j := by
  induction M with
  | zero => omega
  | succ M ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · obtain ⟨P_b, P_a, heq, hlen⟩ := ih hlt
      exact ⟨P_b, P_a ++ f M, by rw [heq, List.append_assoc], hlen⟩
    · subst heq
      exact ⟨(List.range j).flatMap f, [], by simp, flatMap_range_length f c hc j⟩

lemma ofFn_pair_flatten_spec {d : ℕ} (a b : Fin d → ℝ) :
    ((List.ofFn fun j : Fin d => [a j, b j]).flatten).length = 2 * d ∧
    ∀ i : Fin d,
      ((List.ofFn fun j : Fin d => [a j, b j]).flatten).getD (2 * i.1) 0 = a i ∧
      ((List.ofFn fun j : Fin d => [a j, b j]).flatten).getD (2 * i.1 + 1) 0 = b i := by
  induction d with
  | zero =>
    refine ⟨rfl, fun i => Fin.elim0 i⟩
  | succ d ih =>
    obtain ⟨hlen, hget⟩ := ih (fun j => a j.succ) (fun j => b j.succ)
    have hcons : (List.ofFn fun j : Fin (d + 1) => [a j, b j]).flatten =
        [a 0, b 0] ++ (List.ofFn fun j : Fin d => [a j.succ, b j.succ]).flatten := by
      rw [List.ofFn_succ, List.flatten_cons]
    refine ⟨?_, fun i => ?_⟩
    · rw [hcons, List.length_append, hlen]
      simp; ring
    · rw [hcons]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [List.getD]
      · have hj := hget j
        have h1 : 2 ≤ 2 * (j.succ : ℕ) := by simp [Fin.val_succ]
        have h2 : 2 ≤ 2 * (j.succ : ℕ) + 1 := by simp [Fin.val_succ]; omega
        rw [getD_append_right [a 0, b 0] _ (2 * (j.succ : ℕ)) h1,
          getD_append_right [a 0, b 0] _ (2 * (j.succ : ℕ) + 1) h2]
        have e1 : 2 * (j.succ : ℕ) - 2 = 2 * j.1 := by simp [Fin.val_succ]; omega
        have e2 : 2 * (j.succ : ℕ) + 1 - 2 = 2 * j.1 + 1 := by simp [Fin.val_succ]; omega
        simp only [List.length_cons, List.length_nil, e1, e2]
        exact hj

lemma complexInput_length {d : ℕ} (x : Fin d → ℂ) :
    (complexInput x).length = 2 * d :=
  (ofFn_pair_flatten_spec (fun j => (x j).re) (fun j => (x j).im)).1

lemma complexInput_getD_re {d : ℕ} (x : Fin d → ℂ) (i : Fin d) :
    (complexInput x).getD (2 * i.1) 0 = (x i).re :=
  ((ofFn_pair_flatten_spec (fun j => (x j).re) (fun j => (x j).im)).2 i).1

lemma complexInput_getD_im {d : ℕ} (x : Fin d → ℂ) (i : Fin d) :
    (complexInput x).getD (2 * i.1 + 1) 0 = (x i).im :=
  ((ofFn_pair_flatten_spec (fun j => (x j).re) (fun j => (x j).im)).2 i).2

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

def idxZero (d : ℕ) : ℕ := 2 * d
def idxTwo (d : ℕ) : ℕ := 2 * d + 1
def idxFour (d : ℕ) : ℕ := 2 * d + 2
def idxScaleTheta (d : ℕ) : ℕ := 2 * d + 3
def idxScalePhi (d : ℕ) : ℕ := 2 * d + 4

def baseLeaves (d : ℕ) : ℕ := 2 * d + 5
def baseTree (d n : ℕ) : ℕ := baseLeaves d + 3 * 2 ^ n
def baseTheta (d n : ℕ) : ℕ := baseTree d n + n * 2 ^ n
def basePhi (d n : ℕ) : ℕ := baseTheta d n + 5 * (n * 2 ^ n)

def leafIdx (d j : ℕ) : ℕ := baseLeaves d + 3 * j + 2

def treeIdx (d n m j : ℕ) : ℕ :=
  match m with
  | 0 => leafIdx d j
  | p + 1 => baseTree d n + (p * 2 ^ n + j)

def thetaIdx (d n k j : ℕ) : ℕ :=
  baseTheta d n + 5 * (k * 2 ^ n + j) + 4

def phiIdx (d n j : ℕ) : ℕ :=
  basePhi d n + 3 * j + 2

def addrTable (d n k j : ℕ) : ℕ :=
  if k < n then thetaIdx d n k j else phiIdx d n j

def progConsts (q : ℕ) : List ArithInstr :=
  [.const 0, .const 2, .const 4, .const ((2 : ℚ) ^ (q - 2)), .const ((2 : ℚ) ^ (q - 3))]

def leafInstrs (d j : ℕ) : List ArithInstr :=
  let b := baseLeaves d + 3 * j
  if j < d then
    [.mul (2 * j) (2 * j), .mul (2 * j + 1) (2 * j + 1), .add b (b + 1)]
  else
    [.const 0, .const 0, .const 0]

def progLeaves (d n : ℕ) : List ArithInstr :=
  (List.range (2 ^ n)).flatMap (leafInstrs d)

def treeStepInstr (d n p j : ℕ) : List ArithInstr :=
  if 2 * j + 1 < 2 ^ n then
    [.add (treeIdx d n p (2 * j)) (treeIdx d n p (2 * j + 1))]
  else
    [.const 0]

def progTreeLevel (d n p : ℕ) : List ArithInstr :=
  (List.range (2 ^ n)).flatMap (treeStepInstr d n p)

def progTree (d n : ℕ) : List ArithInstr :=
  (List.range n).flatMap (progTreeLevel d n)

def thetaInstrs (d n k j : ℕ) : List ArithInstr :=
  let b := baseTheta d n + 5 * (k * 2 ^ n + j)
  [.div (treeIdx d n (n - (k + 1)) (2 * j)) (treeIdx d n (n - k) j),
   .sqrt b,
   .arccos (b + 1),
   .mul (idxTwo d) (b + 2),
   .mul (b + 3) (idxScaleTheta d)]

def progThetaLevel (d n k : ℕ) : List ArithInstr :=
  (List.range (2 ^ n)).flatMap (thetaInstrs d n k)

def progTheta (d n : ℕ) : List ArithInstr :=
  (List.range n).flatMap (progThetaLevel d n)

def phiInstrs (d n j : ℕ) : List ArithInstr :=
  let b := basePhi d n + 3 * j
  [if j < d then .arg (2 * j) (2 * j + 1) else .const 0,
   .add b (idxFour d),
   .mul (b + 1) (idxScalePhi d)]

def progPhi (d n : ℕ) : List ArithInstr :=
  (List.range (2 ^ n)).flatMap (phiInstrs d n)

def fullProg (d n q : ℕ) : List ArithInstr :=
  progConsts q ++ progLeaves d n ++ progTree d n ++ progTheta d n ++ progPhi d n

lemma progConsts_length (q : ℕ) : (progConsts q).length = 5 := rfl

lemma progLeaves_length (d n : ℕ) : (progLeaves d n).length = 3 * 2 ^ n :=
  flatMap_range_length (leafInstrs d) 3 (fun j => by dsimp [leafInstrs]; split_ifs <;> rfl) (2 ^ n)

lemma progTreeLevel_length (d n p : ℕ) : (progTreeLevel d n p).length = 2 ^ n := by
  have h := flatMap_range_length (treeStepInstr d n p) 1
    (fun j => by dsimp [treeStepInstr]; split_ifs <;> rfl) (2 ^ n)
  unfold progTreeLevel
  rw [h]
  ring

lemma progTree_length (d n : ℕ) : (progTree d n).length = n * 2 ^ n := by
  have h := flatMap_range_length (progTreeLevel d n) (2 ^ n) (progTreeLevel_length d n) n
  unfold progTree
  rw [h]
  ring

lemma progThetaLevel_length (d n k : ℕ) : (progThetaLevel d n k).length = 5 * 2 ^ n :=
  flatMap_range_length (thetaInstrs d n k) 5 (fun _ => rfl) (2 ^ n)

lemma progTheta_length (d n : ℕ) : (progTheta d n).length = 5 * (n * 2 ^ n) := by
  have h := flatMap_range_length (progThetaLevel d n) (5 * 2 ^ n) (progThetaLevel_length d n) n
  unfold progTheta
  rw [h]
  ring

lemma progPhi_length (d n : ℕ) : (progPhi d n).length = 3 * 2 ^ n :=
  flatMap_range_length (phiInstrs d n) 3 (fun _ => rfl) (2 ^ n)

lemma fullProg_length (d n q : ℕ) :
    (fullProg d n q).length = 5 + 3 * 2 ^ n + n * 2 ^ n + 5 * (n * 2 ^ n) + 3 * 2 ^ n := by
  simp only [fullProg, List.length_append, progConsts_length, progLeaves_length,
    progTree_length, progTheta_length, progPhi_length]

def ReadsBelow (L : ℕ) : ArithInstr → Prop
  | .const _ => True
  | .add i j | .sub i j | .mul i j | .div i j | .arg i j => i < L ∧ j < L
  | .sqrt i | .arccos i => i < L

lemma value_congr_of_readsBelow {vals1 vals2 : List ℝ} {L : ℕ} {g : ArithInstr}
    (hg : ReadsBelow L g) (heq : ∀ i < L, vals1.getD i 0 = vals2.getD i 0) :
    g.value vals1 = g.value vals2 := by
  cases g with
  | const c => rfl
  | add i j => dsimp [ArithInstr.value]; rw [heq i hg.1, heq j hg.2]
  | sub i j => dsimp [ArithInstr.value]; rw [heq i hg.1, heq j hg.2]
  | mul i j => dsimp [ArithInstr.value]; rw [heq i hg.1, heq j hg.2]
  | div i j => dsimp [ArithInstr.value]; rw [heq i hg.1, heq j hg.2]
  | sqrt i => dsimp [ArithInstr.value]; rw [heq i hg]
  | arccos i => dsimp [ArithInstr.value]; rw [heq i hg]
  | arg i j => dsimp [ArithInstr.value]; rw [heq i hg.1, heq j hg.2]

lemma arithRun_eval_final {P : List ArithInstr} (P0 : List ArithInstr) (g : ArithInstr)
    (P_rest : List ArithInstr) (hP : P = P0 ++ [g] ++ P_rest) (input : List ℝ)
    (hg : ReadsBelow (input.length + P0.length) g) :
    (arithRun P input).getD (input.length + P0.length) 0 = g.value (arithRun P input) := by
  subst hP
  rw [arithRun_eval_at P0 g P_rest input]
  refine value_congr_of_readsBelow hg (fun i hi => ?_)
  have hlen : (arithRun P0 input).length = input.length + P0.length :=
    arithRun_length P0 input
  rw [List.append_assoc, arithRun_append,
    arithRun_getD_of_lt ([g] ++ P_rest) (arithRun P0 input) i (by omega)]

lemma eval_block3 {P : List ArithInstr} (P0 : List ArithInstr) (g0 g1 g2 : ArithInstr)
    (P_rest : List ArithInstr) (hP : P = P0 ++ [g0, g1, g2] ++ P_rest) (input : List ℝ)
    (b : ℕ) (hb : b = input.length + P0.length)
    (hg0 : ReadsBelow b g0) (hg1 : ReadsBelow (b + 1) g1) (hg2 : ReadsBelow (b + 2) g2) :
    (arithRun P input).getD b 0 = g0.value (arithRun P input) ∧
    (arithRun P input).getD (b + 1) 0 = g1.value (arithRun P input) ∧
    (arithRun P input).getD (b + 2) 0 = g2.value (arithRun P input) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hb]
    exact arithRun_eval_final P0 g0 ([g1, g2] ++ P_rest)
      (by rw [hP]; simp [List.append_assoc]) input (hb ▸ hg0)
  · have hb1 : b + 1 = input.length + (P0 ++ [g0]).length := by simp [hb]; omega
    rw [hb1]
    exact arithRun_eval_final (P0 ++ [g0]) g1 ([g2] ++ P_rest)
      (by rw [hP]; simp [List.append_assoc]) input (hb1 ▸ hg1)
  · have hb2 : b + 2 = input.length + (P0 ++ [g0, g1]).length := by simp [hb]; omega
    rw [hb2]
    exact arithRun_eval_final (P0 ++ [g0, g1]) g2 P_rest
      (by rw [hP]; simp [List.append_assoc]) input (hb2 ▸ hg2)

lemma eval_block5 {P : List ArithInstr} (P0 : List ArithInstr) (g0 g1 g2 g3 g4 : ArithInstr)
    (P_rest : List ArithInstr) (hP : P = P0 ++ [g0, g1, g2, g3, g4] ++ P_rest) (input : List ℝ)
    (b : ℕ) (hb : b = input.length + P0.length)
    (hg0 : ReadsBelow b g0) (hg1 : ReadsBelow (b + 1) g1) (hg2 : ReadsBelow (b + 2) g2)
    (hg3 : ReadsBelow (b + 3) g3) (hg4 : ReadsBelow (b + 4) g4) :
    (arithRun P input).getD b 0 = g0.value (arithRun P input) ∧
    (arithRun P input).getD (b + 1) 0 = g1.value (arithRun P input) ∧
    (arithRun P input).getD (b + 2) 0 = g2.value (arithRun P input) ∧
    (arithRun P input).getD (b + 3) 0 = g3.value (arithRun P input) ∧
    (arithRun P input).getD (b + 4) 0 = g4.value (arithRun P input) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]
    exact arithRun_eval_final P0 g0 ([g1, g2, g3, g4] ++ P_rest)
      (by rw [hP]; simp [List.append_assoc]) input (hb ▸ hg0)
  · have hb1 : b + 1 = input.length + (P0 ++ [g0]).length := by simp [hb]; omega
    rw [hb1]
    exact arithRun_eval_final (P0 ++ [g0]) g1 ([g2, g3, g4] ++ P_rest)
      (by rw [hP]; simp [List.append_assoc]) input (hb1 ▸ hg1)
  · have hb2 : b + 2 = input.length + (P0 ++ [g0, g1]).length := by simp [hb]; omega
    rw [hb2]
    exact arithRun_eval_final (P0 ++ [g0, g1]) g2 ([g3, g4] ++ P_rest)
      (by rw [hP]; simp [List.append_assoc]) input (hb2 ▸ hg2)
  · have hb3 : b + 3 = input.length + (P0 ++ [g0, g1, g2]).length := by simp [hb]; omega
    rw [hb3]
    exact arithRun_eval_final (P0 ++ [g0, g1, g2]) g3 ([g4] ++ P_rest)
      (by rw [hP]; simp [List.append_assoc]) input (hb3 ▸ hg3)
  · have hb4 : b + 4 = input.length + (P0 ++ [g0, g1, g2, g3]).length := by simp [hb]; omega
    rw [hb4]
    exact arithRun_eval_final (P0 ++ [g0, g1, g2, g3]) g4 P_rest
      (by rw [hP]; simp [List.append_assoc]) input (hb4 ▸ hg4)

lemma fullProg_eval_consts {d n q : ℕ} (x : Fin d → ℂ) :
    let vals := arithRun (fullProg d n q) (complexInput x)
    vals.getD (idxZero d) 0 = 0 ∧
    vals.getD (idxTwo d) 0 = 2 ∧
    vals.getD (idxFour d) 0 = 4 ∧
    vals.getD (idxScaleTheta d) 0 = (2 : ℝ) ^ (q - 2) ∧
    vals.getD (idxScalePhi d) 0 = (2 : ℝ) ^ (q - 3) := by
  have hlen := complexInput_length x
  have h5 := eval_block5 (P := fullProg d n q) [] (.const 0) (.const 2) (.const 4)
    (.const ((2 : ℚ) ^ (q - 2))) (.const ((2 : ℚ) ^ (q - 3)))
    (progLeaves d n ++ progTree d n ++ progTheta d n ++ progPhi d n)
    (by simp [fullProg, progConsts])
    (complexInput x) (2 * d) (by simp [hlen])
    trivial trivial trivial trivial trivial
  dsimp [idxZero, idxTwo, idxFour, idxScaleTheta, idxScalePhi, ArithInstr.value] at h5 ⊢
  push_cast at h5
  exact h5

lemma fullProg_eval_input {d n q : ℕ} (x : Fin d → ℂ) (i : Fin d) :
    let vals := arithRun (fullProg d n q) (complexInput x)
    vals.getD (2 * i.1) 0 = (x i).re ∧
    vals.getD (2 * i.1 + 1) 0 = (x i).im := by
  have hlen := complexInput_length x
  have hi := i.isLt
  constructor
  · rw [arithRun_getD_of_lt _ _ _ (by omega), complexInput_getD_re]
  · rw [arithRun_getD_of_lt _ _ _ (by omega), complexInput_getD_im]

lemma fullProg_eval_leaf {d n q : ℕ} (x : Fin d → ℂ) (j : ℕ) (hj : j < 2 ^ n) :
    (arithRun (fullProg d n q) (complexInput x)).getD (leafIdx d j) 0 = leafWeight x j := by
  have hlen := complexInput_length x
  obtain ⟨P_b, P_a, hsplit, hblen⟩ :=
    flatMap_range_split (leafInstrs d) 3
      (fun j' => by dsimp [leafInstrs]; split_ifs <;> rfl) (2 ^ n) j hj
  set P0 := progConsts q ++ P_b
  set P_rest := P_a ++ progTree d n ++ progTheta d n ++ progPhi d n
  have hP : fullProg d n q = P0 ++ leafInstrs d j ++ P_rest := by
    simp only [fullProg, progLeaves, hsplit, P0, P_rest, List.append_assoc]
  have hb : baseLeaves d + 3 * j = (complexInput x).length + P0.length := by
    simp [baseLeaves, P0, progConsts_length, hblen, hlen]; omega
  by_cases hjd : j < d
  · have h3 := eval_block3 P0 (.mul (2 * j) (2 * j)) (.mul (2 * j + 1) (2 * j + 1))
      (.add (baseLeaves d + 3 * j) (baseLeaves d + 3 * j + 1)) P_rest
      (by simpa [leafInstrs, hjd] using hP) (complexInput x)
      (baseLeaves d + 3 * j) hb
      ⟨by dsimp [baseLeaves]; omega, by dsimp [baseLeaves]; omega⟩
      ⟨by dsimp [baseLeaves]; omega, by dsimp [baseLeaves]; omega⟩
      ⟨by omega, by omega⟩
    have hin := fullProg_eval_input (n := n) (q := q) x ⟨j, hjd⟩
    dsimp [leafIdx, leafWeight, ArithInstr.value] at h3 hin ⊢
    rw [dif_pos hjd, h3.2.2, h3.1, h3.2.1, hin.1, hin.2]
    ring
  · have h3 := eval_block3 P0 (.const 0) (.const 0) (.const 0) P_rest
      (by simpa [leafInstrs, hjd] using hP) (complexInput x)
      (baseLeaves d + 3 * j) hb trivial trivial trivial
    dsimp [leafIdx, leafWeight, ArithInstr.value] at h3 ⊢
    rw [dif_neg hjd, h3.2.2]
    norm_num

lemma treeIdx_lt_baseTree_add (d n m j : ℕ) (hj : j < 2 ^ n) :
    treeIdx d n m j < baseTree d n + m * 2 ^ n := by
  cases m with
  | zero =>
    dsimp [treeIdx, leafIdx, baseTree]
    omega
  | succ p =>
    dsimp [treeIdx]
    have : (p + 1) * 2 ^ n = p * 2 ^ n + 2 ^ n := Nat.succ_mul p (2 ^ n)
    omega

lemma fullProg_eval_tree {d n q : ℕ} (x : Fin d → ℂ) :
    ∀ (m : ℕ) (hm : m ≤ n) (j : ℕ) (hj : j < 2 ^ (n - m)),
      (arithRun (fullProg d n q) (complexInput x)).getD (treeIdx d n m j) 0 =
        treeHeightSum x m j
  | 0, hm, j, hj => by
      simpa [treeIdx, treeHeightSum] using fullProg_eval_leaf x j hj
  | p + 1, hm, j, hj => by
      have hlen := complexInput_length x
      have hp : p < n := hm
      have h2j1 : 2 * j + 1 < 2 ^ (n - p) := by
        have hsub : n - p = (n - (p + 1)) + 1 := by omega
        rw [hsub, pow_succ']
        omega
      have h2j : 2 * j < 2 ^ (n - p) := by omega
      have hle_pow : 2 ^ (n - p) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
      have h2j1_n : 2 * j + 1 < 2 ^ n := lt_of_lt_of_le h2j1 hle_pow
      have h2j_n : 2 * j < 2 ^ n := lt_of_lt_of_le h2j hle_pow
      have hj_n : j < 2 ^ n := by omega
      obtain ⟨P_tb, P_ta, hsplit_t, htblen⟩ :=
        flatMap_range_split (progTreeLevel d n) (2 ^ n) (progTreeLevel_length d n) n p hp
      obtain ⟨P_jb, P_ja, hsplit_j, hjblen⟩ :=
        flatMap_range_split (treeStepInstr d n p) 1
          (fun j' => by dsimp [treeStepInstr]; split_ifs <;> rfl) (2 ^ n) j hj_n
      set P0 := progConsts q ++ progLeaves d n ++ P_tb ++ P_jb
      set P_rest := P_ja ++ P_ta ++ progTheta d n ++ progPhi d n
      have hP : fullProg d n q =
          P0 ++ [.add (treeIdx d n p (2 * j)) (treeIdx d n p (2 * j + 1))] ++ P_rest := by
        have hstep : treeStepInstr d n p j =
            [.add (treeIdx d n p (2 * j)) (treeIdx d n p (2 * j + 1))] := by
          simp [treeStepInstr, h2j1_n]
        simp only [fullProg, progTree, progTreeLevel, hsplit_t, hsplit_j, hstep, P0, P_rest, List.append_assoc]
      have hidx : (complexInput x).length + P0.length = treeIdx d n (p + 1) j := by
        simp [P0, hlen, progConsts_length, progLeaves_length, htblen, hjblen,
          treeIdx, baseTree, baseLeaves]
        ring
      have hlt1 : treeIdx d n p (2 * j) < (complexInput x).length + P0.length := by
        rw [hidx]
        exact lt_of_lt_of_le (treeIdx_lt_baseTree_add d n p (2 * j) h2j_n)
          (by dsimp [treeIdx]; omega)
      have hlt2 : treeIdx d n p (2 * j + 1) < (complexInput x).length + P0.length := by
        rw [hidx]
        exact lt_of_lt_of_le (treeIdx_lt_baseTree_add d n p (2 * j + 1) h2j1_n)
          (by dsimp [treeIdx]; omega)
      have heval := arithRun_eval_final P0
        (.add (treeIdx d n p (2 * j)) (treeIdx d n p (2 * j + 1))) P_rest hP
        (complexInput x) ⟨hlt1, hlt2⟩
      rw [hidx] at heval
      rw [heval]
      dsimp [ArithInstr.value, treeHeightSum]
      rw [fullProg_eval_tree x p (Nat.le_of_lt hp) (2 * j) h2j,
        fullProg_eval_tree x p (Nat.le_of_lt hp) (2 * j + 1) h2j1]

lemma treeIdx_lt_baseTheta (d n m j : ℕ) (hm : m ≤ n) (hj : j < 2 ^ n) :
    treeIdx d n m j < baseTheta d n := by
  have h1 := treeIdx_lt_baseTree_add d n m j hj
  have h2 : m * 2 ^ n ≤ n * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) hm
  dsimp [baseTheta]
  omega

lemma fullProg_eval_theta {d n q : ℕ} (x : Fin d → ℂ) (k : ℕ) (hk : k < n)
    (j : ℕ) (hj : j < 2 ^ k) :
    (arithRun (fullProg d n q) (complexInput x)).getD (thetaIdx d n k j) 0 =
      exactTheta x n k j * (2 : ℝ) ^ (q - 2) := by
  have hlen := complexInput_length x
  have hle_pow : 2 ^ (k + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hk
  have h2j_k1 : 2 * j < 2 ^ (k + 1) := by rw [pow_succ']; omega
  have h2j_sub : 2 * j < 2 ^ (n - (n - (k + 1))) := by
    have : n - (n - (k + 1)) = k + 1 := by omega
    rw [this]; exact h2j_k1
  have hj_sub : j < 2 ^ (n - (n - k)) := by
    have : n - (n - k) = k := by omega
    rw [this]; exact hj
  have h2j_n : 2 * j < 2 ^ n := lt_of_lt_of_le h2j_k1 hle_pow
  have hj_n : j < 2 ^ n := by omega
  obtain ⟨P_kb, P_ka, hsplit_k, hkblen⟩ :=
    flatMap_range_split (progThetaLevel d n) (5 * 2 ^ n) (progThetaLevel_length d n) n k hk
  obtain ⟨P_jb, P_ja, hsplit_j, hjblen⟩ :=
    flatMap_range_split (thetaInstrs d n k) 5 (fun _ => rfl) (2 ^ n) j hj_n
  set P0 := progConsts q ++ progLeaves d n ++ progTree d n ++ P_kb ++ P_jb
  set P_rest := P_ja ++ P_ka ++ progPhi d n
  set b := baseTheta d n + 5 * (k * 2 ^ n + j)
  have hP : fullProg d n q = P0 ++ thetaInstrs d n k j ++ P_rest := by
    simp only [fullProg, progTheta, progThetaLevel, hsplit_k, hsplit_j, P0, P_rest, List.append_assoc]
  have hb : b = (complexInput x).length + P0.length := by
    simp [b, P0, hlen, progConsts_length, progLeaves_length, progTree_length,
      hkblen, hjblen, baseTheta, baseTree, baseLeaves]
    ring
  have hlt_t1 : treeIdx d n (n - (k + 1)) (2 * j) < b :=
    lt_of_lt_of_le (treeIdx_lt_baseTheta d n (n - (k + 1)) (2 * j) (by omega) h2j_n) (by omega)
  have hlt_t2 : treeIdx d n (n - k) j < b :=
    lt_of_lt_of_le (treeIdx_lt_baseTheta d n (n - k) j (by omega) hj_n) (by omega)
  have hlt_two : idxTwo d < b + 3 := by
    dsimp [b, baseTheta, baseTree, baseLeaves, idxTwo]; omega
  have hlt_sc : idxScaleTheta d < b + 4 := by
    dsimp [b, baseTheta, baseTree, baseLeaves, idxScaleTheta]; omega
  have h5 := eval_block5 P0
    (.div (treeIdx d n (n - (k + 1)) (2 * j)) (treeIdx d n (n - k) j))
    (.sqrt b) (.arccos (b + 1)) (.mul (idxTwo d) (b + 2)) (.mul (b + 3) (idxScaleTheta d))
    P_rest hP (complexInput x) b hb
    ⟨hlt_t1, hlt_t2⟩ (show b < b + 1 by omega)
    (show b + 1 < b + 2 by omega)
    ⟨hlt_two, by omega⟩ ⟨by omega, hlt_sc⟩
  have hc := fullProg_eval_consts (d := d) (n := n) (q := q) x
  have ht1 := fullProg_eval_tree (d := d) (n := n) (q := q) x (n - (k + 1)) (by omega) (2 * j) h2j_sub
  have ht2 := fullProg_eval_tree (d := d) (n := n) (q := q) x (n - k) (by omega) j hj_sub
  dsimp [thetaIdx, exactTheta, ArithInstr.value] at h5 hc ⊢
  rw [h5.2.2.2.2, h5.2.2.2.1, h5.2.2.1, h5.2.1, h5.1, ht1, ht2, hc.2.1, hc.2.2.2.1]

lemma fullProg_eval_phi {d n q : ℕ} (x : Fin d → ℂ) (j : ℕ) (hj : j < 2 ^ n) :
    (arithRun (fullProg d n q) (complexInput x)).getD (phiIdx d n j) 0 =
      (exactPhi x j + 4) * (2 : ℝ) ^ (q - 3) := by
  have hlen := complexInput_length x
  obtain ⟨P_jb, P_ja, hsplit_j, hjblen⟩ :=
    flatMap_range_split (phiInstrs d n) 3 (fun _ => rfl) (2 ^ n) j hj
  set P0 := progConsts q ++ progLeaves d n ++ progTree d n ++ progTheta d n ++ P_jb
  set P_rest := P_ja
  set b := basePhi d n + 3 * j
  have hP : fullProg d n q = P0 ++ phiInstrs d n j ++ P_rest := by
    simp only [fullProg, progPhi, hsplit_j, P0, P_rest, List.append_assoc]
  have hb : b = (complexInput x).length + P0.length := by
    simp [b, P0, hlen, progConsts_length, progLeaves_length, progTree_length,
      progTheta_length, hjblen, basePhi, baseTheta, baseTree, baseLeaves]
    ring
  have hlt_four : idxFour d < b + 1 := by
    dsimp [b, basePhi, baseTheta, baseTree, baseLeaves, idxFour]; omega
  have hlt_sc : idxScalePhi d < b + 2 := by
    dsimp [b, basePhi, baseTheta, baseTree, baseLeaves, idxScalePhi]; omega
  have hc := fullProg_eval_consts (d := d) (n := n) (q := q) x
  by_cases hjd : j < d
  · have h3 := eval_block3 P0 (.arg (2 * j) (2 * j + 1)) (.add b (idxFour d))
      (.mul (b + 1) (idxScalePhi d)) P_rest
      (by simpa [phiInstrs, hjd] using hP) (complexInput x) b hb
      ⟨by dsimp [b, basePhi, baseTheta, baseTree, baseLeaves]; omega,
       by dsimp [b, basePhi, baseTheta, baseTree, baseLeaves]; omega⟩
      ⟨by omega, hlt_four⟩ ⟨by omega, hlt_sc⟩
    have hin := fullProg_eval_input (n := n) (q := q) x ⟨j, hjd⟩
    dsimp [phiIdx, exactPhi, ArithInstr.value] at h3 hc hin ⊢
    rw [dif_pos hjd, h3.2.2, h3.2.1, h3.1, hin.1, hin.2, hc.2.2.1, hc.2.2.2.2]
  · have h3 := eval_block3 P0 (.const 0) (.add b (idxFour d))
      (.mul (b + 1) (idxScalePhi d)) P_rest
      (by simpa [phiInstrs, hjd] using hP) (complexInput x) b hb
      trivial ⟨by omega, hlt_four⟩ ⟨by omega, hlt_sc⟩
    dsimp [phiIdx, exactPhi, ArithInstr.value] at h3 hc ⊢
    rw [dif_neg hjd, h3.2.2, h3.2.1, h3.1, hc.2.2.1, hc.2.2.2.2]
    norm_num

/-! ### Section 8: Quantization Error, Tree Induction, and Error Propagation -/

lemma bitsToNat_natToBits_of_lt {q m : ℕ} (hm : m < 2 ^ q) :
    bitsToNat (natToBits q m) = m := by
  unfold natToBits
  have h := bitsEquivFin_apply ((bitsEquivFin q).symm ⟨m % 2 ^ q, Nat.mod_lt _ (Nat.two_pow_pos q)⟩)
  rw [Equiv.apply_symm_apply] at h
  rw [← h]
  exact Nat.mod_eq_of_lt hm

lemma quantize_bound {q s : ℕ} (hsq : s ≤ q) {v : ℝ} (hv0 : 0 ≤ v) (hvs : v < (2 : ℝ) ^ s) :
    let m := ⌊v * (2 : ℝ) ^ (q - s)⌋₊
    m < 2 ^ q ∧
    |(bitsToNat (natToBits q m) : ℝ) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q) - v| ≤
      (2 : ℝ) ^ s / (2 : ℝ) ^ q := by
  intro m
  have hpow_eq : (2 : ℝ) ^ s * (2 : ℝ) ^ (q - s) = (2 : ℝ) ^ q := by
    rw [← pow_add, Nat.add_sub_of_le hsq]
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (q - s) := by positivity
  have hpow_q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  have hv_nonneg : 0 ≤ v * (2 : ℝ) ^ (q - s) := mul_nonneg hv0 (le_of_lt hpow_pos)
  have hv_lt : v * (2 : ℝ) ^ (q - s) < ((2 ^ q : ℕ) : ℝ) := by
    push_cast
    calc v * (2 : ℝ) ^ (q - s) < (2 : ℝ) ^ s * (2 : ℝ) ^ (q - s) :=
          mul_lt_mul_of_pos_right hvs hpow_pos
      _ = (2 : ℝ) ^ q := hpow_eq
  have hm_lt : m < 2 ^ q := (Nat.floor_lt hv_nonneg).mpr hv_lt
  refine ⟨hm_lt, ?_⟩
  rw [bitsToNat_natToBits_of_lt hm_lt]
  have hfl_le : (m : ℝ) ≤ v * (2 : ℝ) ^ (q - s) := Nat.floor_le hv_nonneg
  have hlt_fl : v * (2 : ℝ) ^ (q - s) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hscale : ((2 : ℝ) ^ (q - s)) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q) = 1 := by
    rw [mul_div_assoc', mul_comm ((2 : ℝ) ^ (q - s)), hpow_eq, div_self (ne_of_gt hpow_q_pos)]
  have h1 : (m : ℝ) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q) ≤ v := by
    calc (m : ℝ) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q)
        ≤ (v * (2 : ℝ) ^ (q - s)) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q) :=
          mul_le_mul_of_nonneg_right hfl_le (by positivity)
      _ = v * (((2 : ℝ) ^ (q - s)) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q)) := by ring
      _ = v := by rw [hscale, mul_one]
  have h2 : v ≤ (m : ℝ) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q) + (2 : ℝ) ^ s / (2 : ℝ) ^ q := by
    calc v = v * (((2 : ℝ) ^ (q - s)) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q)) := by rw [hscale, mul_one]
      _ = (v * (2 : ℝ) ^ (q - s)) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q) := by ring
      _ ≤ ((m : ℝ) + 1) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q) :=
          mul_le_mul_of_nonneg_right (le_of_lt hlt_fl) (by positivity)
      _ = (m : ℝ) * ((2 : ℝ) ^ s / (2 : ℝ) ^ q) + (2 : ℝ) ^ s / (2 : ℝ) ^ q := by ring
  rw [abs_le]
  constructor <;> linarith

lemma exactTheta_bounds {d : ℕ} (x : Fin d → ℂ) (n k j : ℕ) :
    0 ≤ exactTheta x n k j ∧ exactTheta x n k j < 4 := by
  unfold exactTheta
  have hsqrt_nonneg : 0 ≤ Real.sqrt (treeHeightSum x (n - (k + 1)) (2 * j) / treeHeightSum x (n - k) j) :=
    Real.sqrt_nonneg _
  have harc_nonneg : 0 ≤ Real.arccos (Real.sqrt (treeHeightSum x (n - (k + 1)) (2 * j) / treeHeightSum x (n - k) j)) :=
    Real.arccos_nonneg _
  have harc_le : Real.arccos (Real.sqrt (treeHeightSum x (n - (k + 1)) (2 * j) / treeHeightSum x (n - k) j)) ≤ Real.pi / 2 := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    have : 0 ≤ Real.arcsin (Real.sqrt (treeHeightSum x (n - (k + 1)) (2 * j) / treeHeightSum x (n - k) j)) :=
      Real.arcsin_nonneg.mpr hsqrt_nonneg
    linarith
  constructor
  · linarith
  · linarith [Real.pi_lt_four]

lemma exactPhi_add_four_bounds {d : ℕ} (x : Fin d → ℂ) (j : ℕ) :
    0 ≤ exactPhi x j + 4 ∧ exactPhi x j + 4 < 8 := by
  unfold exactPhi
  split_ifs with h
  · have h1 := Complex.neg_pi_lt_arg (x ⟨j, h⟩)
    have h2 := Complex.arg_le_pi (x ⟨j, h⟩)
    have hpi := Real.pi_lt_four
    constructor <;> linarith
  · constructor <;> norm_num

noncomputable def approxTheta {d : ℕ} (x : Fin d → ℂ) (n q k j : ℕ) : ℝ :=
  (bitsToNat (natToBits q
    ⌊(arithRun (fullProg d n q) (complexInput x)).getD (thetaIdx d n k j) 0⌋₊) : ℝ) *
    (4 / (2 : ℝ) ^ q)

noncomputable def approxPhi {d : ℕ} (x : Fin d → ℂ) (n q j : ℕ) : ℝ :=
  (bitsToNat (natToBits q
    ⌊(arithRun (fullProg d n q) (complexInput x)).getD (phiIdx d n j) 0⌋₊) : ℝ) *
    (8 / (2 : ℝ) ^ q) - 4

lemma qramWords_stageAddr_theta {d : ℕ} (x : Fin d → ℂ) (n q : ℕ) (k : Fin n)
    (z_out : Qubits n) :
    let M := qramWords (n + 1) q (fullProg d n q) (addrMap n (addrTable d n)) x
    (bitsToNat (M (stageAddr n k.1 (Nat.le_of_lt k.2) z_out)) : ℝ) * (4 / (2 : ℝ) ^ q) =
      approxTheta x n q k.1 (prefixVal z_out k.1) := by
  dsimp [qramWords, approxTheta]
  rw [addrMap_stageAddr]
  simp [addrTable, k.isLt]

lemma qramWords_stageAddr_phi {d : ℕ} (x : Fin d → ℂ) (n q : ℕ) (z_out : Qubits n) :
    let M := qramWords (n + 1) q (fullProg d n q) (addrMap n (addrTable d n)) x
    (bitsToNat (M (stageAddr n n le_rfl z_out)) : ℝ) * (8 / (2 : ℝ) ^ q) - 4 =
      approxPhi x n q (bitsToNat z_out) := by
  dsimp [qramWords, approxPhi]
  rw [addrMap_stageAddr, prefixVal_full]
  simp [addrTable]

lemma approxTheta_error {d : ℕ} (x : Fin d → ℂ) (n q : ℕ) (hq : 3 ≤ q)
    (k : ℕ) (hk : k < n) (j : ℕ) (hj : j < 2 ^ k) :
    |approxTheta x n q k j - exactTheta x n k j| ≤ 4 / (2 : ℝ) ^ q := by
  dsimp [approxTheta]
  rw [fullProg_eval_theta x k hk j hj]
  obtain ⟨hb0, hb4⟩ := exactTheta_bounds x n k j
  have hq2 : 2 ≤ q := by omega
  have hquant := (quantize_bound hq2 hb0 (by norm_num; exact hb4)).2
  simpa [show ((2 : ℝ) ^ 2 / (2 : ℝ) ^ q) = 4 / (2 : ℝ) ^ q by norm_num] using hquant

lemma approxPhi_error {d : ℕ} (x : Fin d → ℂ) (n q : ℕ) (hq : 3 ≤ q)
    (j : ℕ) (hj : j < 2 ^ n) :
    |approxPhi x n q j - exactPhi x j| ≤ 8 / (2 : ℝ) ^ q := by
  dsimp [approxPhi]
  rw [fullProg_eval_phi x j hj]
  obtain ⟨hb0, hb8⟩ := exactPhi_add_four_bounds x j
  have hquant := (quantize_bound hq hb0 (by norm_num; exact hb8)).2
  have heq : (bitsToNat (natToBits q ⌊(exactPhi x j + 4) * (2 : ℝ) ^ (q - 3)⌋₊) : ℝ) *
      (8 / (2 : ℝ) ^ q) - 4 - exactPhi x j =
    (bitsToNat (natToBits q ⌊(exactPhi x j + 4) * (2 : ℝ) ^ (q - 3)⌋₊) : ℝ) *
      ((2 : ℝ) ^ 3 / (2 : ℝ) ^ q) - (exactPhi x j + 4) := by
    norm_num
    ring
  rw [heq]
  simpa [show ((2 : ℝ) ^ 3 / (2 : ℝ) ^ q) = 8 / (2 : ℝ) ^ q by norm_num] using hquant

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

lemma rotStep_sub {n : ℕ} (k : Fin n) (ang : ℕ → ℝ)
    (ψ φ : EuclideanSpace ℂ (Qubits n)) :
    rotStep k ang ψ - rotStep k ang φ = rotStep k ang (ψ - φ) := by
  ext z
  simp only [rotStep, toLp_ofLp_apply, sub_ofLp_apply]
  ring

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
      · have hupd_t : Function.update z k true = z := by
          rw [← hzk, Function.update_eq_self]
        have hsupp_z : ψ.ofLp z = 0 := hsupp z hzk
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, norm_mul, mul_pow,
          hsupp_z, norm_zero, sq, mul_zero, zero_add]
        linear_combination (‖ψ.ofLp (Function.update z k false)‖ * ‖ψ.ofLp (Function.update z k false)‖) * hcs
    have h1 := sum_flipAt_pair k (fun z => ‖(rotStep k ang ψ).ofLp z‖ ^ 2)
    have h2 := sum_flipAt_pair k (fun z => ‖ψ.ofLp z‖ ^ 2)
    simp_rw [hpair] at h1
    linarith
  nlinarith [norm_nonneg (rotStep k ang ψ), norm_nonneg ψ]

lemma norm_rotStep_sub_rotStep {n : ℕ} (k : Fin n) (ang1 ang2 : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hang : ∀ j < 2 ^ k.1, |ang1 j - ang2 j| ≤ δ)
    (ψ : EuclideanSpace ℂ (Qubits n)) (hsupp : ∀ z : Qubits n, z k = true → ψ.ofLp z = 0) :
    ‖rotStep k ang1 ψ - rotStep k ang2 ψ‖ ≤ δ * ‖ψ‖ := by
  have hsq : ‖rotStep k ang1 ψ - rotStep k ang2 ψ‖ ^ 2 ≤ (δ * ‖ψ‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    have hpair : ∀ z : Qubits n,
        ‖(rotStep k ang1 ψ - rotStep k ang2 ψ).ofLp z‖ ^ 2 +
          ‖(rotStep k ang1 ψ - rotStep k ang2 ψ).ofLp (flipAt k z)‖ ^ 2 ≤
          δ ^ 2 * ‖ψ.ofLp z‖ ^ 2 + δ ^ 2 * ‖ψ.ofLp (flipAt k z)‖ ^ 2 := by
      intro z
      rw [sub_ofLp_apply]
      dsimp [rotStep, flipAt]
      have hpref : prefixVal (Function.update z k (!z k)) k.1 = prefixVal z k.1 :=
        prefixVal_update_ge z k.1 k le_rfl (!z k)
      rw [hpref, Function.update_idem, Function.update_self]
      set j := prefixVal z k.1
      have hj : j < 2 ^ k.1 := prefixVal_lt z k.1 (Nat.le_of_lt k.2)
      have hdiff : |(ang1 j / 2) - (ang2 j / 2)| ≤ δ / 2 := by
        have h := hang j hj
        rw [show ang1 j / 2 - ang2 j / 2 = (ang1 j - ang2 j) / 2 by ring,
          abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      have hcos_le : ‖(Real.cos (ang1 j / 2) : ℂ) - (Real.cos (ang2 j / 2) : ℂ)‖ ≤ δ / 2 := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact le_trans (Real.abs_cos_sub_cos_le _ _) hdiff
      have hsin_le : ‖(Real.sin (ang1 j / 2) : ℂ) - (Real.sin (ang2 j / 2) : ℂ)‖ ≤ δ / 2 := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact le_trans (Real.abs_sin_sub_sin_le _ _) hdiff
      have hcs_sq :
          ‖(Real.cos (ang1 j / 2) : ℂ) - (Real.cos (ang2 j / 2) : ℂ)‖ ^ 2 +
            ‖(Real.sin (ang1 j / 2) : ℂ) - (Real.sin (ang2 j / 2) : ℂ)‖ ^ 2 ≤ δ ^ 2 := by
        have h1 : ‖(Real.cos (ang1 j / 2) : ℂ) - (Real.cos (ang2 j / 2) : ℂ)‖ ^ 2 ≤ (δ / 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hcos_le 2
        have h2 : ‖(Real.sin (ang1 j / 2) : ℂ) - (Real.sin (ang2 j / 2) : ℂ)‖ ^ 2 ≤ (δ / 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hsin_le 2
        nlinarith
      cases hzk : z k
      · have hupd_f : Function.update z k false = z := by
          rw [← hzk, Function.update_eq_self]
        have hsupp_t : ψ.ofLp (Function.update z k true) = 0 :=
          hsupp (Function.update z k true) (Function.update_self k true z)
        simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, ← sub_mul, norm_mul,
          mul_pow, hupd_f, hsupp_t, norm_zero, sq, mul_zero, add_zero]
        nlinarith [sq_nonneg ‖ψ.ofLp z‖]
      · have hsupp_z : ψ.ofLp z = 0 := hsupp z hzk
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ← sub_mul, norm_mul,
          mul_pow, hsupp_z, norm_zero, sq, mul_zero, zero_add]
        nlinarith [sq_nonneg ‖ψ.ofLp (Function.update z k false)‖]
    have h1 := sum_flipAt_pair k (fun z => ‖(rotStep k ang1 ψ - rotStep k ang2 ψ).ofLp z‖ ^ 2)
    have h2 := sum_flipAt_pair k (fun z => δ ^ 2 * ‖ψ.ofLp z‖ ^ 2)
    have hsum_le : ∑ z : Qubits n,
        (‖(rotStep k ang1 ψ - rotStep k ang2 ψ).ofLp z‖ ^ 2 +
          ‖(rotStep k ang1 ψ - rotStep k ang2 ψ).ofLp (flipAt k z)‖ ^ 2) ≤
        ∑ z : Qubits n, (δ ^ 2 * ‖ψ.ofLp z‖ ^ 2 + δ ^ 2 * ‖ψ.ofLp (flipAt k z)‖ ^ 2) :=
      Finset.sum_le_sum (fun z _ => hpair z)
    linarith
  nlinarith [norm_nonneg (rotStep k ang1 ψ - rotStep k ang2 ψ),
    mul_nonneg hδ (norm_nonneg ψ)]

def UnusedFrom {n : ℕ} (m : ℕ) (ψ : EuclideanSpace ℂ (Qubits n)) : Prop :=
  ∀ z : Qubits n, ∀ i : Fin n, m ≤ (i : ℕ) → z i = true → ψ.ofLp z = 0

lemma unusedFrom_zeroKet (n : ℕ) : UnusedFrom 0 (zeroKet n) := by
  intro z i _ hzi
  rw [zeroKet, ket_apply, if_neg]
  intro hz
  have := congrFun hz i
  simp [hzi] at this

lemma unusedFrom_rotStep {n : ℕ} (m : ℕ) (hm : m < n) (ang : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (Qubits n)) (hsupp : UnusedFrom m ψ) :
    UnusedFrom (m + 1) (rotStep ⟨m, hm⟩ ang ψ) := by
  intro z i hi hzi
  dsimp [rotStep]
  have hne : i ≠ ⟨m, hm⟩ := by
    intro heq; have := congrArg Fin.val heq; dsimp at this; omega
  have hupd_i : (Function.update z ⟨m, hm⟩ false) i = true := by
    rw [Function.update_of_ne hne, hzi]
  rw [hsupp (Function.update z ⟨m, hm⟩ false) i (by omega) hupd_i, mul_zero]

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

noncomputable def approxTreeState {d n : ℕ} (x : Fin d → ℂ) (q : ℕ) :
    ℕ → EuclideanSpace ℂ (Qubits n)
  | 0 => zeroKet n
  | m + 1 =>
      if hm : m < n then
        rotStep ⟨m, hm⟩ (approxTheta x n q m) (approxTreeState x q m)
      else
        approxTreeState x q m

lemma unusedFrom_approxTreeState {d n : ℕ} (x : Fin d → ℂ) (q : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n), UnusedFrom m (approxTreeState (n := n) x q m)
  | 0, _ => unusedFrom_zeroKet n
  | m + 1, hm => by
      have hmn : m < n := hm
      rw [approxTreeState, dif_pos hmn]
      exact unusedFrom_rotStep m hmn (approxTheta x n q m)
        (approxTreeState x q m) (unusedFrom_approxTreeState x q m (Nat.le_of_lt hmn))

lemma norm_approxTreeState {d n : ℕ} (x : Fin d → ℂ) (q : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ n), ‖approxTreeState (n := n) x q m‖ = 1
  | 0, _ => by
      change IsState (zeroKet n)
      simp [IsState, zeroKet, ket]
  | m + 1, hm => by
      have hmn : m < n := hm
      rw [approxTreeState, dif_pos hmn]
      rw [norm_rotStep ⟨m, hmn⟩ (approxTheta x n q m) (approxTreeState x q m)
          (fun z hz => unusedFrom_approxTreeState x q m (Nat.le_of_lt hmn) z ⟨m, hmn⟩ le_rfl hz),
        norm_approxTreeState x q m (Nat.le_of_lt hmn)]

lemma act_allRotStages_zeroKet {d n : ℕ} (x : Fin d → ℂ) (q : ℕ) (hq : 1 ≤ q) :
    ∀ (m : ℕ) (hm : m ≤ n),
      let M := qramWords (n + 1) q (fullProg d n q) (addrMap n (addrTable d n)) x
      act ((allRotStages n q hq m hm).unitary (fun _ => qramUnitary (n + 1) q M))
          (zeroKet (n + ((n + 1) + q))) =
        liftAncilla (w := (n + 1) + q) (approxTreeState (n := n) x q m)
  | 0, _ => by
      simp [allRotStages, act_one, approxTreeState, liftAncilla_zeroKet]
  | m + 1, hm => by
      intro M
      have hmn : m < n := hm
      rw [allRotStages, act_unitary_append, act_allRotStages_zeroKet x q hq m (Nat.le_of_lt hmn)]
      rw [approxTreeState, dif_pos hmn]
      exact act_rotStageCircuit_liftAncilla n q hq M (approxTheta x n q m) ⟨m, hmn⟩
        (qramWords_stageAddr_theta x n q ⟨m, hmn⟩) (approxTreeState x q m)
        (fun z hz => unusedFrom_approxTreeState x q m (Nat.le_of_lt hmn) z ⟨m, hmn⟩ le_rfl hz)

lemma act_fullCircuit_zeroKet {d n : ℕ} (x : Fin d → ℂ) (q : ℕ) (hq : 1 ≤ q) :
    let M := qramWords (n + 1) q (fullProg d n q) (addrMap n (addrTable d n)) x
    act ((fullCircuit n q hq).unitary (fun _ => qramUnitary (n + 1) q M))
        (zeroKet (n + ((n + 1) + q))) =
      liftAncilla (w := (n + 1) + q)
        (applyPhase (approxPhi x n q) (approxTreeState (n := n) x q n)) := by
  intro M
  rw [fullCircuit, act_unitary_append, act_allRotStages_zeroKet x q hq n le_rfl]
  exact act_phaseStageCircuit_liftAncilla n q hq M (approxPhi x n q)
    (qramWords_stageAddr_phi x n q) (approxTreeState x q n)

lemma approxTreeState_error {d n : ℕ} (hd : d ≤ 2 ^ n) (x : Fin d → ℂ) (hx : x ≠ 0)
    (q : ℕ) (hq : 3 ≤ q) :
    ∀ (m : ℕ) (hm : m ≤ n),
      ‖approxTreeState (n := n) x q m - idealState (n := n) x m‖ ≤
        (m : ℝ) * (4 / (2 : ℝ) ^ q)
  | 0, _ => by
      rw [approxTreeState, idealState_zero hd x hx, sub_self, norm_zero, Nat.cast_zero, zero_mul]
  | m + 1, hm => by
      have hmn : m < n := hm
      rw [approxTreeState, dif_pos hmn, ← rotStep_idealState x m hmn]
      set ψ_a := approxTreeState (n := n) x q m
      set ψ_i := idealState (n := n) x m
      have htri : ‖rotStep ⟨m, hm⟩ (approxTheta x n q m) ψ_a -
            rotStep ⟨m, hm⟩ (exactTheta x n m) ψ_i‖ ≤
          ‖rotStep ⟨m, hm⟩ (approxTheta x n q m) ψ_a -
            rotStep ⟨m, hm⟩ (exactTheta x n m) ψ_a‖ +
          ‖rotStep ⟨m, hm⟩ (exactTheta x n m) ψ_a -
            rotStep ⟨m, hm⟩ (exactTheta x n m) ψ_i‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h1 : ‖rotStep ⟨m, hm⟩ (approxTheta x n q m) ψ_a -
            rotStep ⟨m, hm⟩ (exactTheta x n m) ψ_a‖ ≤ (4 / (2 : ℝ) ^ q) * 1 := by
        rw [← norm_approxTreeState x q m (Nat.le_of_lt hm)]
        exact norm_rotStep_sub_rotStep ⟨m, hm⟩ (approxTheta x n q m) (exactTheta x n m)
          (4 / (2 : ℝ) ^ q) (by positivity) (approxTheta_error x n q hq m hm) ψ_a
          (fun z hz => unusedFrom_approxTreeState x q m (Nat.le_of_lt hm) z ⟨m, hm⟩ le_rfl hz)
      have h2 : ‖rotStep ⟨m, hm⟩ (exactTheta x n m) ψ_a -
            rotStep ⟨m, hm⟩ (exactTheta x n m) ψ_i‖ = ‖ψ_a - ψ_i‖ := by
        rw [rotStep_sub, norm_rotStep ⟨m, hm⟩ (exactTheta x n m) (ψ_a - ψ_i)]
        intro z hz
        simp only [sub_ofLp_apply]
        dsimp [ψ_a, ψ_i]
        rw [unusedFrom_approxTreeState x q m (Nat.le_of_lt hm) z ⟨m, hm⟩ le_rfl hz,
          unusedFrom_idealState x m z ⟨m, hm⟩ le_rfl hz, sub_zero]
      have ih := approxTreeState_error hd x hx q hq m (Nat.le_of_lt hm)
      push_cast
      linarith

lemma norm_exp_I_sub_exp_I (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have h1 : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp (((a + b) / 2 : ℝ) * Complex.I) *
        (2 * Complex.I * Complex.sin (((a - b) / 2 : ℝ))) := by
    have h2 : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
        Complex.exp (((a + b) / 2 : ℝ) * Complex.I) *
          (Complex.exp (((a - b) / 2 : ℝ) * Complex.I) -
            Complex.exp (-(((a - b) / 2 : ℝ) * Complex.I))) := by
      rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
      congr 1 <;> (congr 1; push_cast; ring)
    rw [h2, Complex.sin]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h1, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_two,
    Complex.norm_I, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
  have hsin : |Real.sin ((a - b) / 2)| ≤ |(a - b) / 2| := Real.abs_sin_le_abs
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsin
  linarith

lemma norm_applyPhase {n : ℕ} (phi : ℕ → ℝ) (ψ : EuclideanSpace ℂ (Qubits n)) :
    ‖applyPhase phi ψ‖ = ‖ψ‖ := by
  have hsq : ‖applyPhase phi ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    simp [applyPhase, norm_mul, Complex.norm_exp_ofReal_mul_I]
  nlinarith [norm_nonneg (applyPhase phi ψ), norm_nonneg ψ]

lemma applyPhase_sub {n : ℕ} (phi : ℕ → ℝ) (ψ φ : EuclideanSpace ℂ (Qubits n)) :
    applyPhase phi ψ - applyPhase phi φ = applyPhase phi (ψ - φ) := by
  ext z
  simp only [applyPhase, toLp_ofLp_apply, sub_ofLp_apply]
  ring

lemma norm_applyPhase_sub_applyPhase {n : ℕ} (phi1 phi2 : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hphi : ∀ j < 2 ^ n, |phi1 j - phi2 j| ≤ δ)
    (ψ : EuclideanSpace ℂ (Qubits n)) :
    ‖applyPhase phi1 ψ - applyPhase phi2 ψ‖ ≤ δ * ‖ψ‖ := by
  have hsq : ‖applyPhase phi1 ψ - applyPhase phi2 ψ‖ ^ 2 ≤ (δ * ‖ψ‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun z _ => ?_)
    simp only [sub_ofLp_apply, applyPhase, toLp_ofLp_apply, ← sub_mul, norm_mul, mul_pow]
    have hj : bitsToNat z < 2 ^ n := by
      rw [← bitsEquivFin_apply]
      exact (bitsEquivFin n z).isLt
    have hexp : ‖Complex.exp ((phi1 (bitsToNat z) : ℂ) * Complex.I) -
        Complex.exp ((phi2 (bitsToNat z) : ℂ) * Complex.I)‖ ≤ δ :=
      le_trans (norm_exp_I_sub_exp_I _ _) (hphi (bitsToNat z) hj)
    have hexp_sq : ‖Complex.exp ((phi1 (bitsToNat z) : ℂ) * Complex.I) -
        Complex.exp ((phi2 (bitsToNat z) : ℂ) * Complex.I)‖ ^ 2 ≤ δ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hexp 2
    exact mul_le_mul_of_nonneg_right hexp_sq (sq_nonneg _)
  nlinarith [norm_nonneg (applyPhase phi1 ψ - applyPhase phi2 ψ),
    mul_nonneg hδ (norm_nonneg ψ)]

lemma total_state_error {d n : ℕ} (hd : d ≤ 2 ^ n) (x : Fin d → ℂ) (hx : x ≠ 0)
    (q : ℕ) (hq : 3 ≤ q) :
    let M := qramWords (n + 1) q (fullProg d n q) (addrMap n (addrTable d n)) x
    ‖act ((fullCircuit n q (by omega)).unitary (fun _ => qramUnitary (n + 1) q M))
        (zeroKet (n + ((n + 1) + q))) -
      liftAncilla (w := (n + 1) + q) (padState n (normalizedVec (WithLp.toLp 2 x)))‖ ≤
      (4 * (n : ℝ) + 8) / (2 : ℝ) ^ q := by
  intro M
  rw [act_fullCircuit_zeroKet x q (by omega), liftAncilla_sub, norm_liftAncilla,
    ← applyPhase_idealState_full x]
  set ψ_a := approxTreeState (n := n) x q n
  set ψ_i := idealState (n := n) x n
  have htri : ‖applyPhase (approxPhi x n q) ψ_a - applyPhase (exactPhi x) ψ_i‖ ≤
      ‖applyPhase (approxPhi x n q) ψ_a - applyPhase (exactPhi x) ψ_a‖ +
      ‖applyPhase (exactPhi x) ψ_a - applyPhase (exactPhi x) ψ_i‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h1 : ‖applyPhase (approxPhi x n q) ψ_a - applyPhase (exactPhi x) ψ_a‖ ≤
      (8 / (2 : ℝ) ^ q) * 1 := by
    rw [← norm_approxTreeState x q n le_rfl]
    exact norm_applyPhase_sub_applyPhase (approxPhi x n q) (exactPhi x) (8 / (2 : ℝ) ^ q)
      (by positivity) (approxPhi_error x n q hq) ψ_a
  have h2 : ‖applyPhase (exactPhi x) ψ_a - applyPhase (exactPhi x) ψ_i‖ ≤
      (n : ℝ) * (4 / (2 : ℝ) ^ q) := by
    rw [applyPhase_sub, norm_applyPhase]
    exact approxTreeState_error hd x hx q hq n le_rfl
  linarith [show (8 / (2 : ℝ) ^ q) * 1 + (n : ℝ) * (4 / (2 : ℝ) ^ q) =
    (4 * (n : ℝ) + 8) / (2 : ℝ) ^ q by ring]

/-! ### Section 9: Complexity Bounds and Final Theorem -/

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

lemma log_two_add_d_pos {d : ℕ} (hd : 1 ≤ d) : 0 < Real.log (2 + (d : ℝ)) := by
  apply Real.log_pos
  have : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
  linarith

lemma log_two_le_log_two_add_d {d : ℕ} : Real.log 2 ≤ Real.log (2 + (d : ℝ)) := by
  apply Real.log_le_log (by norm_num)
  have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  linarith

lemma log_two_le_log_two_add_inv {ε : ℝ} (hε : 0 < ε) :
    Real.log 2 ≤ Real.log (2 + 1 / ε) := by
  apply Real.log_le_log (by norm_num)
  have : 0 < 1 / ε := by positivity
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

noncomputable def chooseQ (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈(Real.log (4 * (n : ℝ) + 8) + Real.log (2 + 1 / ε)) / Real.log 2⌉₊ + 3

lemma chooseQ_ge_three (n : ℕ) (ε : ℝ) : 3 ≤ chooseQ n ε := by
  dsimp [chooseQ]; omega

lemma chooseQ_error_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (4 * (n : ℝ) + 8) / (2 : ℝ) ^ (chooseQ n ε) ≤ ε := by
  set k := ⌈(Real.log (4 * (n : ℝ) + 8) + Real.log (2 + 1 / ε)) / Real.log 2⌉₊
  have hlog2 := log_two_pos
  have h4n8_pos : 0 < 4 * (n : ℝ) + 8 := by positivity
  have h2inv_pos : 0 < 2 + 1 / ε := by positivity
  have hceil : (Real.log (4 * (n : ℝ) + 8) + Real.log (2 + 1 / ε)) / Real.log 2 ≤ (k : ℝ) :=
    Nat.le_ceil _
  have hlog_le : Real.log ((4 * (n : ℝ) + 8) * (2 + 1 / ε)) ≤ Real.log ((2 : ℝ) ^ k) := by
    rw [Real.log_mul (ne_of_gt h4n8_pos) (ne_of_gt h2inv_pos), Real.log_pow]
    exact (div_le_iff₀ hlog2).mp hceil
  have hprod_le : (4 * (n : ℝ) + 8) * (2 + 1 / ε) ≤ (2 : ℝ) ^ k :=
    (Real.log_le_log_iff (mul_pos h4n8_pos h2inv_pos) (by positivity)).mp hlog_le
  have hpow_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (chooseQ n ε) :=
    pow_le_pow_right₀ (by norm_num) (by dsimp [chooseQ]; omega)
  have hinv_le : (4 * (n : ℝ) + 8) * (1 / ε) ≤ (2 : ℝ) ^ (chooseQ n ε) := by
    calc (4 * (n : ℝ) + 8) * (1 / ε)
        ≤ (4 * (n : ℝ) + 8) * (2 + 1 / ε) := by nlinarith
      _ ≤ (2 : ℝ) ^ k := hprod_le
      _ ≤ (2 : ℝ) ^ (chooseQ n ε) := hpow_le
  rw [div_le_iff₀ (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hinv_le (le_of_lt hε)
  rw [mul_assoc, one_div_mul_cancel (ne_of_gt hε), mul_one] at hmul
  linarith

lemma chooseQ_upper_bound {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    (chooseQ (Nat.clog 2 d) ε : ℝ) ≤
      (9 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by
  set n := Nat.clog 2 d
  have hlog2 := log_two_pos
  have hlogd := log_two_le_log_two_add_d (d := d)
  have hloge := log_two_le_log_two_add_inv hε
  have h4n8_le : 4 * (n : ℝ) + 8 ≤ (2 + (d : ℝ)) ^ 3 := by
    have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := n))
    have hpow_le : (2 : ℝ) ^ n ≤ 2 * (d : ℝ) := by
      exact_mod_cast pow_clog_le_two_mul hd
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hd_sq : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
    have hd_cube : 0 ≤ (d : ℝ) ^ 3 := by positivity
    nlinarith
  have hlog_4n8 : Real.log (4 * (n : ℝ) + 8) ≤ 3 * Real.log (2 + (d : ℝ)) := by
    have h := Real.log_le_log (by positivity) h4n8_le
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hnum_nonneg : 0 ≤ (Real.log (4 * (n : ℝ) + 8) + Real.log (2 + 1 / ε)) / Real.log 2 := by
    apply div_nonneg _ (le_of_lt hlog2)
    have : 0 ≤ Real.log (4 * (n : ℝ) + 8) :=
      Real.log_nonneg (by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    linarith
  have hceil_lt : (⌈(Real.log (4 * (n : ℝ) + 8) + Real.log (2 + 1 / ε)) / Real.log 2⌉₊ : ℝ) ≤
      (Real.log (4 * (n : ℝ) + 8) + Real.log (2 + 1 / ε)) / Real.log 2 + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hnum_nonneg)
  have hq_eq : (chooseQ n ε : ℝ) =
      (⌈(Real.log (4 * (n : ℝ) + 8) + Real.log (2 + 1 / ε)) / Real.log 2⌉₊ : ℝ) + 3 := by
    dsimp [chooseQ]; push_cast; ring
  have h4_le : 4 ≤ (4 / Real.log 2) * Real.log (2 + (d : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    linarith
  rw [hq_eq]
  have hdiv_le : (Real.log (4 * (n : ℝ) + 8) + Real.log (2 + 1 / ε)) / Real.log 2 ≤
      (3 * Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) / Real.log 2 :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hlog2)
  have hcomb : (3 * Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) / Real.log 2 +
      (4 / Real.log 2) * Real.log (2 + (d : ℝ)) ≤
      (9 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by
    have hpos1 : 0 ≤ Real.log (2 + (d : ℝ)) / Real.log 2 := div_nonneg (by linarith) (le_of_lt hlog2)
    have hpos2 : 0 ≤ Real.log (2 + 1 / ε) / Real.log 2 := div_nonneg (by linarith) (le_of_lt hlog2)
    linarith [show (3 * Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) / Real.log 2 +
        (4 / Real.log 2) * Real.log (2 + (d : ℝ)) =
        7 * (Real.log (2 + (d : ℝ)) / Real.log 2) + 1 * (Real.log (2 + 1 / ε) / Real.log 2) by ring,
      show (9 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) =
        9 * (Real.log (2 + (d : ℝ)) / Real.log 2) + 9 * (Real.log (2 + 1 / ε) / Real.log 2) by ring]
  linarith

end AmpEncodingQramProof

open AmpEncodingQramProof in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε →
      ∃ (a q w : ℕ) (P : List ArithInstr) (addr : Qubits a → ℕ)
        (circ : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + q) (Nat.clog 2 d + w)),
        (2 : ℝ) ^ a * q ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        (P.length : ℝ) ≤ C * d * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ^ c ∧
        (circ.queryCount 0 : ℝ) ≤ C * Real.log (2 + d) ∧
        (circ.gateCount : ℝ) ≤
          C * Real.log (2 + d) * (Real.log (2 + d) + Real.log (2 + 1 / ε)) ∧
        (∀ s ∈ circ, uncontrolledStep s) ∧
        ∀ x : Fin d → ℂ, x ≠ 0 →
          ‖act (circ.unitary fun _ => qramUnitary a q (qramWords a q P addr x))
              (zeroKet (Nat.clog 2 d + w)) -
            WithLp.toLp 2 (fun z : Qubits (Nat.clog 2 d + w) =>
              if ∀ k : Fin w, z (Fin.natAdd (Nat.clog 2 d) k) = false then
                padState (Nat.clog 2 d) (normalizedVec (WithLp.toLp 2 x))
                  (fun i => z (Fin.castAdd w i))
              else 0)‖ ≤ ε := by
  have hlog2 := log_two_pos
  set C : ℝ := 200 / (Real.log 2) ^ 2 + 200 / Real.log 2 + 200
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, 1, fun d hd ε hε => ?_⟩
  set n := Nat.clog 2 d
  set a := n + 1
  set q := chooseQ n ε
  set w := a + q
  have hq3 : 3 ≤ q := chooseQ_ge_three n ε
  have hq1 : 1 ≤ q := by omega
  refine ⟨a, q, w, fullProg d n q, addrMap n (addrTable d n), fullCircuit n q hq1,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Bound 1: 2^a * q ≤ C * d * (log(2+d) + log(2+1/ε))^1
    rw [pow_one]
    have h2a : (2 : ℝ) ^ a ≤ 4 * (d : ℝ) := by
      have hpow : (2 : ℝ) ^ n ≤ 2 * (d : ℝ) := by exact_mod_cast pow_clog_le_two_mul hd
      dsimp [a]
      rw [pow_succ']
      linarith
    have hq_ub := chooseQ_upper_bound hd hε
    have hlog_sum_nonneg : 0 ≤ Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε) := by
      have := log_two_le_log_two_add_d (d := d)
      have := log_two_le_log_two_add_inv hε
      linarith
    have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    have hprod : (2 : ℝ) ^ a * (q : ℝ) ≤
        (36 / Real.log 2) * (d : ℝ) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by
      calc (2 : ℝ) ^ a * (q : ℝ)
          ≤ (4 * (d : ℝ)) * ((9 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε))) :=
            mul_le_mul h2a hq_ub (Nat.cast_nonneg q) (by positivity)
        _ = (36 / Real.log 2) * (d : ℝ) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by ring
    have hC_ge : 36 / Real.log 2 ≤ C := by
      dsimp [C]
      have : 0 ≤ 200 / (Real.log 2) ^ 2 + 200 := by positivity
      have : 36 / Real.log 2 ≤ 200 / Real.log 2 :=
        div_le_div_of_nonneg_right (by norm_num) (le_of_lt hlog2)
      linarith
    exact le_trans hprod (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC_ge hd_nonneg) hlog_sum_nonneg)
  · -- Bound 2: P.length ≤ C * d * (log(2+d) + log(2+1/ε))^1
    rw [pow_one, fullProg_length]
    push_cast
    have hpow : (2 : ℝ) ^ n ≤ 2 * (d : ℝ) := by exact_mod_cast pow_clog_le_two_mul hd
    have hn_ub := clog_real_le_log hd
    have hlogd := log_two_le_log_two_add_d (d := d)
    have hloge := log_two_le_log_two_add_inv hε
    have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
    have hlen_le : 5 + 3 * (2 : ℝ) ^ n + (n : ℝ) * (2 : ℝ) ^ n +
        5 * ((n : ℝ) * (2 : ℝ) ^ n) + 3 * (2 : ℝ) ^ n ≤
        (17 + 12 * (n : ℝ)) * (d : ℝ) := by
      nlinarith
    have h1 : 17 ≤ (17 / Real.log 2) * Real.log (2 + (d : ℝ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      linarith
    have h2 : 17 + 12 * (n : ℝ) ≤
        (41 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by
      have hpos : 0 ≤ Real.log (2 + 1 / ε) / Real.log 2 := div_nonneg (by linarith) (le_of_lt hlog2)
      linarith [show (17 / Real.log 2) * Real.log (2 + (d : ℝ)) +
          12 * ((2 / Real.log 2) * Real.log (2 + (d : ℝ))) =
          (41 / Real.log 2) * Real.log (2 + (d : ℝ)) by ring,
        show (41 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) =
          (41 / Real.log 2) * Real.log (2 + (d : ℝ)) +
            41 * (Real.log (2 + 1 / ε) / Real.log 2) by ring]
    have hC_ge : 41 / Real.log 2 ≤ C := by
      dsimp [C]
      have : 0 ≤ 200 / (Real.log 2) ^ 2 + 200 := by positivity
      have : 41 / Real.log 2 ≤ 200 / Real.log 2 :=
        div_le_div_of_nonneg_right (by norm_num) (le_of_lt hlog2)
      linarith
    have hlog_sum_nonneg : 0 ≤ Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε) := by linarith
    calc 5 + 3 * (2 : ℝ) ^ n + (n : ℝ) * (2 : ℝ) ^ n +
          5 * ((n : ℝ) * (2 : ℝ) ^ n) + 3 * (2 : ℝ) ^ n
        ≤ (17 + 12 * (n : ℝ)) * (d : ℝ) := hlen_le
      _ ≤ ((41 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε))) * (d : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ (C * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε))) * (d : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC_ge hlog_sum_nonneg) (by positivity)
      _ = C * (d : ℝ) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by ring
  · -- Bound 3: queryCount 0 ≤ C * log(2+d)
    rw [(fullCircuit_counts n q hq1).1]
    push_cast
    have hn_ub := clog_real_le_log hd
    have hlogd := log_two_le_log_two_add_d (d := d)
    have h1 : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log (2 + (d : ℝ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      linarith
    have h2 : 2 * ((n : ℝ) + 1) ≤ (6 / Real.log 2) * Real.log (2 + (d : ℝ)) := by
      linarith [show 2 * ((2 / Real.log 2) * Real.log (2 + (d : ℝ)) +
          (1 / Real.log 2) * Real.log (2 + (d : ℝ))) =
          (6 / Real.log 2) * Real.log (2 + (d : ℝ)) by ring]
    have hC_ge : 6 / Real.log 2 ≤ C := by
      dsimp [C]
      have : 0 ≤ 200 / (Real.log 2) ^ 2 + 200 := by positivity
      have : 6 / Real.log 2 ≤ 200 / Real.log 2 :=
        div_le_div_of_nonneg_right (by norm_num) (le_of_lt hlog2)
      linarith
    exact le_trans h2 (mul_le_mul_of_nonneg_right hC_ge (by linarith))
  · -- Bound 4: gateCount ≤ C * log(2+d) * (log(2+d) + log(2+1/ε))
    have hgc : ((fullCircuit n q hq1).gateCount : ℝ) ≤
        ((n : ℝ) + 1) * (2 * (n : ℝ) + (q : ℝ) + 3) := by
      exact_mod_cast (fullCircuit_counts n q hq1).2.1
    have hn_ub := clog_real_le_log hd
    have hq_ub := chooseQ_upper_bound hd hε
    have hlogd := log_two_le_log_two_add_d (d := d)
    have hloge := log_two_le_log_two_add_inv hε
    have h1 : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log (2 + (d : ℝ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      linarith
    have hn1_ub : (n : ℝ) + 1 ≤ (3 / Real.log 2) * Real.log (2 + (d : ℝ)) := by
      linarith [show (2 / Real.log 2) * Real.log (2 + (d : ℝ)) +
          (1 / Real.log 2) * Real.log (2 + (d : ℝ)) =
          (3 / Real.log 2) * Real.log (2 + (d : ℝ)) by ring]
    have h2nq3_ub : 2 * (n : ℝ) + (q : ℝ) + 3 ≤
        (16 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by
      have hpos : 0 ≤ Real.log (2 + 1 / ε) / Real.log 2 := div_nonneg (by linarith) (le_of_lt hlog2)
      linarith [show 2 * ((2 / Real.log 2) * Real.log (2 + (d : ℝ))) +
          (9 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) +
          3 * ((1 / Real.log 2) * Real.log (2 + (d : ℝ))) =
          (16 / Real.log 2) * Real.log (2 + (d : ℝ)) +
            9 * (Real.log (2 + 1 / ε) / Real.log 2) by ring,
        show (16 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) =
          (16 / Real.log 2) * Real.log (2 + (d : ℝ)) +
            16 * (Real.log (2 + 1 / ε) / Real.log 2) by ring]
    have hprod : ((n : ℝ) + 1) * (2 * (n : ℝ) + (q : ℝ) + 3) ≤
        (48 / (Real.log 2) ^ 2) * Real.log (2 + (d : ℝ)) *
          (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by
      calc ((n : ℝ) + 1) * (2 * (n : ℝ) + (q : ℝ) + 3)
          ≤ ((3 / Real.log 2) * Real.log (2 + (d : ℝ))) *
              ((16 / Real.log 2) * (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε))) :=
            mul_le_mul hn1_ub h2nq3_ub (by positivity)
              (mul_nonneg (div_nonneg (by norm_num) (le_of_lt hlog2)) (by linarith))
        _ = (48 / (Real.log 2) ^ 2) * Real.log (2 + (d : ℝ)) *
              (Real.log (2 + (d : ℝ)) + Real.log (2 + 1 / ε)) := by ring
    have hC_ge : 48 / (Real.log 2) ^ 2 ≤ C := by
      dsimp [C]
      have : 0 ≤ 200 / Real.log 2 + 200 := by positivity
      have : 48 / (Real.log 2) ^ 2 ≤ 200 / (Real.log 2) ^ 2 :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)
      linarith
    exact le_trans hgc (le_trans hprod (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC_ge (by linarith)) (by linarith)))
  · -- Bound 5: uncontrolledStep
    exact (fullCircuit_counts n q hq1).2.2
  · -- Bound 6: State error ≤ ε
    intro x hx
    have hd_pow : d ≤ 2 ^ n := Nat.le_pow_clog (by omega) d
    exact le_trans (total_state_error hd_pow x hx q hq3) (chooseQ_error_le n hε)

end
