-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P12.approximateSynthesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:52:01.937528+00:00
-- url     : https://prove2.me/submissions/f6792cbb-a29c-4b9a-906e-7678058addf0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_reflectionDecomposition
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_reflectionApproximation
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_exactReflectionSynthesis
import Mathlib.Analysis.Complex.Trigonometric

open scoped BigOperators Matrix ComplexConjugate
open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

noncomputable section

/-! ### 1. Equivalence between Qubits (n + 1) and Bool × Qubits n -/

def qubits1Equiv : Qubits 1 ≃ Bool where
  toFun b := b 0
  invFun x := fun _ => x
  left_inv b := by ext i; fin_cases i; rfl
  right_inv x := rfl

def equivBQ (n : ℕ) : Qubits (n + 1) ≃ Bool × Qubits n :=
  ((qubitsAppendEquiv n 1).trans (Equiv.prodCongr (Equiv.refl (Qubits n)) qubits1Equiv)).trans (Equiv.prodComm (Qubits n) Bool)

def vecFromBQ {n : ℕ} (v : EuclideanSpace ℂ (Bool × Qubits n)) : EuclideanSpace ℂ (Qubits (n + 1)) :=
  WithLp.toLp 2 (v ∘ equivBQ n)

def matFromBQ {n : ℕ} (M : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ) :
    Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ :=
  M.submatrix (equivBQ n) (equivBQ n)

lemma vecFromBQ_apply {n : ℕ} (v : EuclideanSpace ℂ (Bool × Qubits n)) (z : Qubits (n + 1)) :
    vecFromBQ v z = v (equivBQ n z) := rfl

lemma matFromBQ_apply {n : ℕ} (M : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ) (y z : Qubits (n + 1)) :
    matFromBQ M y z = M (equivBQ n y) (equivBQ n z) := rfl

lemma vecFromBQ_isState {n : ℕ} {v : EuclideanSpace ℂ (Bool × Qubits n)} (hv : IsState v) :
    IsState (vecFromBQ v) := by
  unfold IsState at hv ⊢
  have h_norm : ‖vecFromBQ v‖^2 = ‖v‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    rw [← (equivBQ n).sum_comp]
    rfl
  rw [hv, one_pow] at h_norm
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h_norm

lemma vecFromBQ_denom {n : ℕ} {b : ℝ} {k : ℕ} {v : EuclideanSpace ℂ (Bool × Qubits n)}
    (h : ∀ z, HasDenominator b k (v z)) (z : Qubits (n + 1)) :
    HasDenominator b k (vecFromBQ v z) :=
  h (equivBQ n z)

lemma matFromBQ_refl {n : ℕ} (v : EuclideanSpace ℂ (Bool × Qubits n)) :
    matFromBQ (householderReflection v) = householderReflection (vecFromBQ v) := by
  ext y z
  simp [matFromBQ, householderReflection, vecFromBQ, (equivBQ n).injective.eq_iff]

lemma matFromBQ_mul {n : ℕ} (A B : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ) :
    matFromBQ (A * B) = matFromBQ A * matFromBQ B := by
  ext y z
  simp only [matFromBQ, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← (equivBQ n).sum_comp]

lemma matFromBQ_one {n : ℕ} : matFromBQ (1 : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ) = 1 := by
  ext y z
  simp [matFromBQ, Matrix.submatrix_apply, Matrix.one_apply, (equivBQ n).injective.eq_iff]

lemma matFromBQ_list_prod {n : ℕ} (L : List (Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ)) :
    matFromBQ L.prod = (L.map matFromBQ).prod := by
  induction L with
  | nil => exact matFromBQ_one
  | cons A L ih =>
    rw [List.prod_cons, matFromBQ_mul, ih, List.map_cons, List.prod_cons]

lemma matFromBQ_orderedProd {n : ℕ} {t : ℕ} (F : Fin t → Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ) :
    matFromBQ (orderedProd F) = orderedProd (fun j => matFromBQ (F j)) := by
  unfold orderedProd
  rw [matFromBQ_list_prod, List.map_reverse, List.map_ofFn]
  rfl

lemma act_matFromBQ {n : ℕ} (M : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ)
    (v : EuclideanSpace ℂ (Bool × Qubits n)) :
    act (matFromBQ M) (vecFromBQ v) = vecFromBQ (act M v) := by
  ext y
  simp only [act, vecFromBQ, matFromBQ, PiLp.toLp_apply, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp]
  change (∑ i, M (equivBQ n y) (equivBQ n i) * v (equivBQ n i)) = ∑ p, M (equivBQ n y) p * v p
  exact (equivBQ n).sum_comp (fun p => M (equivBQ n y) p * v p)

lemma vecFromBQ_tensor_ket_false {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    vecFromBQ (tensorVec (ket false) ψ) = zeroAncillaVec ψ 1 := by
  ext z
  dsimp only [vecFromBQ, tensorVec, ket, PiLp.toLp_apply, zeroAncillaVec]
  have h_cond : ((qubitsAppendEquiv n 1) z).2 = (fun _ => false) ↔ z (Fin.natAdd n 0) = false := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; ext j; fin_cases j; exact h
  rw [if_congr h_cond rfl rfl]
  cases hz : z (Fin.natAdd n 0) <;> simp [hz, equivBQ, qubitsAppendEquiv, qubits1Equiv]

/-! ### 2. Action of simulationDilation on |1⟩ ⊗ |ψ⟩ -/

lemma act_dil {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (psi : EuclideanSpace ℂ (Qubits n)) :
    act (simulationDilation U) (tensorVec (ket true) psi) = tensorVec (ket false) (act U psi) := by
  ext ⟨c, x⟩
  simp only [act, tensorVec, ket, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_bool, simulationDilation, Matrix.of_apply, PiLp.toLp_apply,
    PiLp.single_apply]
  cases c <;> simp

/-! ### 3. Single-qubit Pauli-X circuit on the dilation wire -/

def wireNatAdd (n : ℕ) : Fin 1 ↪ Fin (n + 1) where
  toFun _ := Fin.natAdd n 0
  inj' _ _ _ := Subsingleton.elim _ _

lemma wireNatAdd_apply (n : ℕ) (i : Fin 1) : wireNatAdd n i = Fin.natAdd n 0 := rfl

lemma embedOp1_apply {n : ℕ} (M : Matrix Bool Bool ℂ) (y z : Qubits (n + 1)) :
    embedOp (Gate.ofMatrix1 M).mat (wireNatAdd n) y z =
      if (∀ i : Fin n, y (Fin.castAdd 1 i) = z (Fin.castAdd 1 i)) then
        M (y (Fin.natAdd n 0)) (z (Fin.natAdd n 0))
      else 0 := by
  dsimp [embedOp, Gate.ofMatrix1, Matrix.submatrix, Matrix.of_apply]
  have h_cond : (∀ a : Fin (n + 1), a ∉ Set.range (wireNatAdd n) → y a = z a) ↔
      (∀ i : Fin n, y (Fin.castAdd 1 i) = z (Fin.castAdd 1 i)) := by
    constructor
    · intro h i
      apply h
      rintro ⟨j, hj⟩
      have : (wireNatAdd n j).val = n := rfl
      have hi : (Fin.castAdd 1 i).val < n := i.isLt
      omega
    · intro h a
      revert a
      refine Fin.addCases (fun i ha => h i) (fun j ha => ?_)
      · fin_cases j
        exfalso
        apply ha
        exact ⟨0, rfl⟩
  rw [if_congr h_cond rfl rfl]
  rfl

def boolEquivQubits1 : Bool ≃ Qubits 1 where
  toFun b := fun _ => b
  invFun q := q 0
  left_inv b := rfl
  right_inv q := by ext i; fin_cases i; rfl

lemma sum_qubits1_real (f : Qubits 1 → ℝ) : (∑ k : Qubits 1, f k) = f (fun _ => false) + f (fun _ => true) := by
  rw [← boolEquivQubits1.sum_comp f]
  rw [Fintype.sum_bool]
  exact add_comm (f (fun _ => true)) (f (fun _ => false))

lemma sum_qubits1 (f : Qubits 1 → ℂ) : (∑ k : Qubits 1, f k) = f (fun _ => false) + f (fun _ => true) := by
  rw [← boolEquivQubits1.sum_comp f]
  rw [Fintype.sum_bool]
  exact add_comm (f (fun _ => true)) (f (fun _ => false))

lemma act_embedOp1 {n : ℕ} (M : Matrix Bool Bool ℂ) (ψ : EuclideanSpace ℂ (Qubits (n + 1))) (z : Qubits (n + 1)) :
    act (embedOp (Gate.ofMatrix1 M).mat (wireNatAdd n)) ψ z =
      ∑ b : Bool, M (z (Fin.natAdd n 0)) b *
        ψ (Fin.append (fun i => z (Fin.castAdd 1 i)) (fun _ => b)) := by
  dsimp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  rw [← (qubitsAppendEquiv n 1).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  have h_out (x : Qubits n) :
      (∑ y_b : Qubits 1, embedOp (Gate.ofMatrix1 M).mat (wireNatAdd n) z ((qubitsAppendEquiv n 1).symm (x, y_b)) *
        ψ ((qubitsAppendEquiv n 1).symm (x, y_b))) =
      if x = (fun i => z (Fin.castAdd 1 i)) then
        ∑ b : Bool, M (z (Fin.natAdd n 0)) b * ψ (Fin.append (fun i => z (Fin.castAdd 1 i)) (fun _ => b))
      else 0 := by
    rw [sum_qubits1]
    have h_symm (b : Bool) : ((qubitsAppendEquiv n 1).symm (x, fun _ => b)) = Fin.append x (fun _ => b) := rfl
    rw [h_symm false, h_symm true]
    have h_cast (b : Bool) (i : Fin n) : (Fin.append x (fun _ => b)) (Fin.castAdd 1 i) = x i := by
      dsimp [Fin.append]; rw [Fin.addCases_left]
    have h_nat (b : Bool) : (Fin.append x (fun _ => b)) (Fin.natAdd n (0 : Fin 1)) = b := by
      dsimp [Fin.append]; rw [Fin.addCases_right]
    rw [embedOp1_apply, embedOp1_apply]
    simp_rw [h_cast, h_nat]
    by_cases hx : x = fun i => z (Fin.castAdd 1 i)
    · rw [if_pos hx]
      subst hx
      have hT : (∀ (i : Fin n), z (Fin.castAdd 1 i) = (fun i => z (Fin.castAdd 1 i)) i) := fun _ => rfl
      rw [if_pos hT, if_pos hT]
      rw [Fintype.sum_bool]
      ring
    · rw [if_neg hx]
      have h_ne : ¬(∀ i : Fin n, z (Fin.castAdd 1 i) = x i) := by
        intro hc; apply hx; ext i; exact (hc i).symm
      simp [h_ne]
  simp_rw [h_out]
  rw [Finset.sum_ite_eq']
  simp

lemma act_pauliX_zeroAncillaVec {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    act (embedOp (Gate.ofMatrix1 pauliX).mat (wireNatAdd n)) (zeroAncillaVec ψ 1) =
      vecFromBQ (tensorVec (ket true) ψ) := by
  ext z
  rw [act_embedOp1]
  rw [Fintype.sum_bool]
  dsimp only [zeroAncillaVec, PiLp.toLp_apply, vecFromBQ, tensorVec, ket]
  have h_symm (b : Bool) : Fin.append (fun i => z (Fin.castAdd 1 i)) (fun _ => b) =
      (qubitsAppendEquiv n 1).symm (fun i => z (Fin.castAdd 1 i), fun _ => b) := rfl
  rw [h_symm true, h_symm false]
  simp only [Equiv.apply_symm_apply]
  have h_ne : (fun _ : Fin 1 => true) ≠ (fun _ => false) := by
    intro hc; have := congrFun hc 0; contradiction
  rw [if_neg h_ne]
  simp only [if_true, mul_zero]
  dsimp only [pauliX, Matrix.of_apply]
  cases hz : z (Fin.natAdd n 0) <;> simp [hz, equivBQ, qubitsAppendEquiv, qubits1Equiv]

lemma embedOp1_mul {n : ℕ} (M₁ M₂ : Matrix Bool Bool ℂ) :
    embedOp (Gate.ofMatrix1 M₁).mat (wireNatAdd n) * embedOp (Gate.ofMatrix1 M₂).mat (wireNatAdd n) =
      embedOp (Gate.ofMatrix1 (M₁ * M₂)).mat (wireNatAdd n) := by
  ext y z
  simp only [Matrix.mul_apply, embedOp1_apply]
  rw [← (qubitsAppendEquiv n 1).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  have h_out (x : Qubits n) :
      (∑ y_b : Qubits 1,
        (if (∀ i : Fin n, y (Fin.castAdd 1 i) = ((qubitsAppendEquiv n 1).symm (x, y_b)) (Fin.castAdd 1 i)) then
          M₁ (y (Fin.natAdd n 0)) (((qubitsAppendEquiv n 1).symm (x, y_b)) (Fin.natAdd n 0)) else 0) *
        (if (∀ i : Fin n, ((qubitsAppendEquiv n 1).symm (x, y_b)) (Fin.castAdd 1 i) = z (Fin.castAdd 1 i)) then
          M₂ (((qubitsAppendEquiv n 1).symm (x, y_b)) (Fin.natAdd n 0)) (z (Fin.natAdd n 0)) else 0)) =
      if x = (fun i => y (Fin.castAdd 1 i)) then
        if (∀ i : Fin n, y (Fin.castAdd 1 i) = z (Fin.castAdd 1 i)) then
          (M₁ * M₂) (y (Fin.natAdd n 0)) (z (Fin.natAdd n 0))
        else 0
      else 0 := by
    rw [sum_qubits1]
    have h_symm (b : Bool) : ((qubitsAppendEquiv n 1).symm (x, fun _ => b)) = Fin.append x (fun _ => b) := rfl
    rw [h_symm false, h_symm true]
    have h_cast (b : Bool) (i : Fin n) : (Fin.append x (fun _ => b)) (Fin.castAdd 1 i) = x i := by
      dsimp [Fin.append]; rw [Fin.addCases_left]
    have h_nat (b : Bool) : (Fin.append x (fun _ => b)) (Fin.natAdd n (0 : Fin 1)) = b := by
      dsimp [Fin.append]; rw [Fin.addCases_right]
    simp_rw [h_cast, h_nat]
    by_cases hx : x = fun i => y (Fin.castAdd 1 i)
    · rw [if_pos hx]
      subst hx
      have hT : (∀ (i : Fin n), y (Fin.castAdd 1 i) = (fun i => y (Fin.castAdd 1 i)) i) := fun _ => rfl
      rw [if_pos hT, if_pos hT]
      by_cases hyz : ∀ i : Fin n, y (Fin.castAdd 1 i) = z (Fin.castAdd 1 i)
      · rw [if_pos hyz, if_pos hyz, if_pos hyz]
        rw [Matrix.mul_apply, Fintype.sum_bool]
        ring
      · rw [if_neg hyz, if_neg hyz, if_neg hyz]
        simp
    · rw [if_neg hx]
      have h_ne : ¬(∀ i : Fin n, y (Fin.castAdd 1 i) = x i) := by
        intro hc; apply hx; ext i; exact (hc i).symm
      simp [h_ne]
  simp_rw [h_out]
  rw [Finset.sum_ite_eq']
  simp [Matrix.mul_apply]

lemma exp_I_pi_four_pow_four : (Complex.exp (Complex.I * Real.pi / 4)) ^ 4 = -1 := by
  have h : (4 : ℂ) * (Complex.I * Real.pi / 4) = (Real.pi : ℂ) * Complex.I := by ring
  rw [← Complex.exp_nat_mul]
  have h4 : ((4 : ℕ) : ℂ) * (Complex.I * Real.pi / 4) = (Real.pi : ℂ) * Complex.I := by
    push_cast; exact h
  rw [h4, Complex.exp_pi_mul_I]

lemma gateT_four : gateT * gateT * gateT * gateT = pauliZ := by
  ext a b
  simp only [gateT, pauliZ, Matrix.mul_apply, Matrix.diagonal, Matrix.of_apply, Fintype.sum_bool]
  cases a <;> cases b <;> simp
  have : Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4) *
      Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4) =
    (Complex.exp (Complex.I * Real.pi / 4)) ^ 4 := by ring
  rw [this, exp_I_pi_four_pow_four]

lemma hadamard_pauliZ_hadamard : hadamard * pauliZ * hadamard = pauliX := by
  ext a b
  simp only [hadamard, pauliZ, pauliX, Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal, Fintype.sum_bool]
  have hr2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
    rw [← mul_inv]
    have : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    rw [this]; norm_num
  cases a <;> cases b <;> simp [hr2] <;> norm_num

lemma hadamard_T4_hadamard : hadamard * (gateT * gateT * gateT * gateT) * hadamard = pauliX := by
  rw [gateT_four, hadamard_pauliZ_hadamard]

lemma gateH_mem : Gate.ofMatrix1 hadamard ∈ htcxGateSet := by
  dsimp [htcxGateSet]; left; rfl

lemma gateT_mem : Gate.ofMatrix1 gateT ∈ htcxGateSet := by
  dsimp [htcxGateSet]; right; left; rfl

def appH (n : ℕ) : GateApp htcxGateSet (n + 1) := ⟨Gate.ofMatrix1 hadamard, gateH_mem, wireNatAdd n⟩
def appT (n : ℕ) : GateApp htcxGateSet (n + 1) := ⟨Gate.ofMatrix1 gateT, gateT_mem, wireNatAdd n⟩

def cX (n : ℕ) : Circuit htcxGateSet (n + 1) := [appH n, appT n, appT n, appT n, appT n, appH n]

lemma cX_size (n : ℕ) : (cX n).size = 6 := rfl

lemma cX_unitary (n : ℕ) :
    Circuit.unitary (cX n) = embedOp (Gate.ofMatrix1 pauliX).mat (wireNatAdd n) := by
  dsimp [Circuit.unitary, cX, List.map, List.reverse, appH, appT]
  simp only [mul_one]
  repeat rw [embedOp1_mul]
  congr 1
  congr 1
  have h1 : hadamard * (gateT * (gateT * (gateT * (gateT * hadamard)))) =
      hadamard * (gateT * gateT * gateT * gateT) * hadamard := by
    ext i j; simp [Matrix.mul_apply]; ring
  rw [h1, hadamard_T4_hadamard]

lemma act_cX_zeroAncillaVec {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    act (Circuit.unitary (cX n)) (zeroAncillaVec ψ 1) = vecFromBQ (tensorVec (ket true) ψ) := by
  rw [cX_unitary, act_pauliX_zeroAncillaVec]

/-! ### 4. Ancilla padding -/

def castAddEmb (m : ℕ) : Fin m ↪ Fin (m + 1) where
  toFun := Fin.castAdd 1
  inj' := fun _ _ h => Fin.castAdd_inj.mp h

def padGateApp {m : ℕ} (g : GateApp htcxGateSet m) : GateApp htcxGateSet (m + 1) :=
  ⟨g.gate, g.mem, g.wires.trans (castAddEmb m)⟩

def padCircuit {m : ℕ} (c : Circuit htcxGateSet m) : Circuit htcxGateSet (m + 1) :=
  c.map padGateApp

lemma padCircuit_size {m : ℕ} (c : Circuit htcxGateSet m) :
    (padCircuit c).size = c.size := by
  dsimp [Circuit.size, padCircuit]
  simp

lemma embedOp_castAddEmb {k m : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin m)
    (y z : Qubits (m + 1)) :
    embedOp M (w.trans (castAddEmb m)) y z =
      if y (Fin.natAdd m 0) = z (Fin.natAdd m 0) then
        embedOp M w (fun i => y (Fin.castAdd 1 i)) (fun i => z (Fin.castAdd 1 i))
      else 0 := by
  dsimp [embedOp, Matrix.of_apply]
  have h_range (i : Fin k) : (w.trans (castAddEmb m)) i ≠ Fin.natAdd m 0 := by
    intro h
    have h_val : (w i).val = m := congrArg Fin.val h
    have hw := (w i).isLt
    omega
  have h_cond : (∀ a : Fin (m + 1), a ∉ Set.range (w.trans (castAddEmb m)) → y a = z a) ↔
      y (Fin.natAdd m 0) = z (Fin.natAdd m 0) ∧
      ∀ i : Fin m, i ∉ Set.range w → y (Fin.castAdd 1 i) = z (Fin.castAdd 1 i) := by
    constructor
    · intro h
      refine ⟨h (Fin.natAdd m 0) (by rintro ⟨i, hi⟩; exact h_range i hi), ?_⟩
      intro i hi
      apply h (Fin.castAdd 1 i)
      rintro ⟨j, hj⟩
      apply hi
      refine ⟨j, ?_⟩
      exact Fin.castAdd_inj.mp hj
    · rintro ⟨htop, hrest⟩ a
      refine Fin.addCases (fun i ha => ?_) (fun j ha => ?_) a
      · apply hrest i
        rintro ⟨j, hj⟩
        apply ha
        refine ⟨j, ?_⟩
        exact congrArg (Fin.castAdd 1) hj
      · fin_cases j
        exact htop
  rw [if_congr h_cond rfl rfl]
  by_cases htop : y (Fin.natAdd m 0) = z (Fin.natAdd m 0)
  · simp only [htop, true_and, if_true]
    split_ifs with h_rest
    · rfl
    · rfl
  · simp only [htop, false_and, if_false]

lemma test_sum {m : ℕ} (W : Matrix (Qubits m) (Qubits m) ℂ) (z : Qubits (m + 1)) (ψ : EuclideanSpace ℂ (Qubits m)) (x : Qubits m) :
    (∑ b : Qubits 1,
      if (Fin.append x b) (Fin.natAdd m (0 : Fin 1)) = false then
        W (fun i => z (Fin.castAdd 1 i)) x * ψ x
      else 0) = W (fun i => z (Fin.castAdd 1 i)) x * ψ x := by
  rw [sum_qubits1]
  have h1 : (Fin.append x (fun _ => false)) (Fin.natAdd m (0 : Fin 1)) = false := by
    dsimp [Fin.append]; rw [Fin.addCases_right]
  have h2 : (Fin.append x (fun _ => true)) (Fin.natAdd m (0 : Fin 1)) = true := by
    dsimp [Fin.append]; rw [Fin.addCases_right]
  rw [h1, h2]
  simp

lemma act_pad_single {m : ℕ} (g : GateApp htcxGateSet m) (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (embedOp g.gate.mat (g.wires.trans (castAddEmb m))) (zeroAncillaVec ψ 1) =
      zeroAncillaVec (act (embedOp g.gate.mat g.wires) ψ) 1 := by
  ext z
  dsimp only [act, zeroAncillaVec, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  have h_cond (y : Qubits (m + 1)) : (qubitsAppendEquiv m 1 y).2 = (fun _ => false) ↔
      y (Fin.natAdd m (0 : Fin 1)) = false := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; ext j; fin_cases j; exact h
  rw [if_congr (h_cond z) rfl rfl]
  by_cases hz : z (Fin.natAdd m (0 : Fin 1)) = false
  · simp only [hz, if_true]
    have h_rew : ∀ y : Qubits (m + 1),
        embedOp g.gate.mat (g.wires.trans (castAddEmb m)) z y *
          (if (qubitsAppendEquiv m 1 y).2 = (fun _ => false) then ψ ((qubitsAppendEquiv m 1 y).1) else 0) =
        if y (Fin.natAdd m (0 : Fin 1)) = false then
          embedOp g.gate.mat g.wires (fun i => z (Fin.castAdd 1 i)) ((qubitsAppendEquiv m 1 y).1) *
            ψ ((qubitsAppendEquiv m 1 y).1)
        else 0 := by
      intro y
      rw [embedOp_castAddEmb, if_congr (h_cond y) rfl rfl]
      by_cases hy : y (Fin.natAdd m (0 : Fin 1)) = false
      · have : (fun i => y (Fin.castAdd 1 i)) = ((qubitsAppendEquiv m 1 y).1) := rfl
        rw [this]
        simp [hy, hz]
      · simp [hy, hz]
    simp_rw [h_rew]
    rw [← (qubitsAppendEquiv m 1).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Equiv.apply_symm_apply, qubitsAppendEquiv]
    have h_prod (x : Qubits m) := test_sum (embedOp g.gate.mat g.wires) z ψ x
    refine Finset.sum_congr rfl fun x _ => h_prod x
  · simp only [hz]
    apply Finset.sum_eq_zero
    intro y _
    rw [embedOp_castAddEmb, if_congr (h_cond y) rfl rfl]
    by_cases hy : y (Fin.natAdd m (0 : Fin 1)) = false
    · simp [hy, hz]
    · simp [hy]

lemma padCircuit_append {m : ℕ} (c₁ c₂ : Circuit htcxGateSet m) :
    padCircuit (c₁ ++ c₂) = padCircuit c₁ ++ padCircuit c₂ := by
  simp [padCircuit]

lemma circuit_unitary_append {n : ℕ} (c₁ c₂ : Circuit htcxGateSet n) :
    Circuit.unitary (c₁ ++ c₂) = Circuit.unitary c₂ * Circuit.unitary c₁ := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext i
  simp [act, Matrix.mulVec_mulVec]

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act 1 ψ = ψ := by
  ext i
  simp [act, Matrix.one_mulVec]

lemma act_padCircuit {m : ℕ} (c : Circuit htcxGateSet m) (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (padCircuit c).unitary (zeroAncillaVec ψ 1) =
      zeroAncillaVec (act c.unitary ψ) 1 := by
  induction c using List.reverseRecOn with
  | nil =>
    simp [padCircuit, Circuit.unitary, act_one]
  | append_singleton cs g ih =>
    rw [padCircuit_append, circuit_unitary_append, circuit_unitary_append]
    rw [act_mul, act_mul, ih]
    dsimp only [padCircuit, List.map]
    have h_g : Circuit.unitary [padGateApp g] = embedOp g.gate.mat (g.wires.trans (castAddEmb m)) := by
      dsimp [Circuit.unitary, padGateApp]; simp
    have h_g0 : Circuit.unitary [g] = embedOp g.gate.mat g.wires := by
      dsimp [Circuit.unitary]; simp
    rw [h_g, h_g0]
    exact act_pad_single g (act (Circuit.unitary cs) ψ)

lemma zeroAncillaVec_zero {m : ℕ} (ψ : EuclideanSpace ℂ (Qubits m)) :
    zeroAncillaVec ψ 0 = ψ := by
  ext z
  dsimp [zeroAncillaVec, qubitsAppendEquiv]
  have h_cond : (fun j : Fin 0 => z (Fin.natAdd m j)) = (fun _ => false) := Subsingleton.elim _ _
  simp only [h_cond, if_true]

lemma normalize_clean_ancilla {m : ℕ} (V : Matrix (Qubits m) (Qubits m) ℂ)
    (w : ℕ) (hw : w ≤ 1) (c : Circuit htcxGateSet (m + w))
    (himp : ImplementsWithCleanAncillas c.unitary V) :
    ∃ c' : Circuit htcxGateSet (m + 1),
      ImplementsWithCleanAncillas c'.unitary V ∧ c'.size = c.size := by
  interval_cases w
  · refine ⟨padCircuit c, ?_, padCircuit_size c⟩
    intro ψ
    rw [act_padCircuit]
    have h_act := himp ψ
    rw [zeroAncillaVec_zero, zeroAncillaVec_zero] at h_act
    rw [h_act]
  · exact ⟨c, himp, rfl⟩

lemma zeroAncillaVec_two {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    zeroAncillaVec ψ 2 = zeroAncillaVec (zeroAncillaVec ψ 1) 1 := by
  ext z
  dsimp only [zeroAncillaVec, PiLp.toLp_apply]
  by_cases hA : ((qubitsAppendEquiv n 2) z).2 = fun _ => false
  · have hB : ((qubitsAppendEquiv (n + 1) 1) z).2 = fun _ => false := by
      ext j; fin_cases j; exact congrFun hA 1
    have hC : ((qubitsAppendEquiv n 1) ((qubitsAppendEquiv (n + 1) 1) z).1).2 = fun _ => false := by
      ext j; fin_cases j; exact congrFun hA 0
    rw [if_pos hA, if_pos hB, if_pos hC]
    have : ((qubitsAppendEquiv n 2) z).1 = ((qubitsAppendEquiv n 1) ((qubitsAppendEquiv (n + 1) 1) z).1).1 := by
      ext i; rfl
    rw [this]
  · rw [if_neg hA]
    by_cases hB : ((qubitsAppendEquiv (n + 1) 1) z).2 = fun _ => false
    · rw [if_pos hB]
      have hC : ¬((qubitsAppendEquiv n 1) ((qubitsAppendEquiv (n + 1) 1) z).1).2 = fun _ => false := by
        intro hc
        apply hA
        ext j; fin_cases j
        · exact congrFun hc 0
        · exact congrFun hB 0
      rw [if_neg hC]
    · rw [if_neg hB]

lemma orderedProd_succ {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} (F : Fin (t + 1) → Matrix ι ι ℂ) :
    orderedProd F = orderedProd (fun i : Fin t => F i.succ) * F 0 := by
  unfold orderedProd
  rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton]

lemma orderedProd_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Fin 0 → Matrix ι ι ℂ) :
    orderedProd F = 1 := by
  unfold orderedProd
  simp

def finChain {m : ℕ} {t : ℕ} (c : Fin t → Circuit htcxGateSet (m + 1)) : Circuit htcxGateSet (m + 1) :=
  (List.ofFn c).flatten

lemma finChain_succ {m : ℕ} {t : ℕ} (c : Fin (t + 1) → Circuit htcxGateSet (m + 1)) :
    finChain c = c 0 ++ finChain (fun i : Fin t => c i.succ) := by
  dsimp [finChain]
  rw [List.ofFn_succ, List.flatten_cons]

lemma finChain_zero {m : ℕ} (c : Fin 0 → Circuit htcxGateSet (m + 1)) :
    finChain c = [] := by
  dsimp [finChain]
  simp

lemma implements_finChain {m : ℕ} {t : ℕ}
    (F : Fin t → Matrix (Qubits m) (Qubits m) ℂ)
    (c : Fin t → Circuit htcxGateSet (m + 1))
    (hc : ∀ j : Fin t, ImplementsWithCleanAncillas (c j).unitary (F j)) :
    ImplementsWithCleanAncillas (finChain c).unitary (orderedProd F) := by
  induction t with
  | zero =>
    intro ψ
    rw [finChain_zero, orderedProd_zero]
    simp [Circuit.unitary, act_one]
  | succ t ih =>
    intro ψ
    rw [finChain_succ, orderedProd_succ]
    rw [circuit_unitary_append, act_mul, act_mul]
    have h0 := hc 0 ψ
    rw [h0]
    have ih' := ih (fun i => F i.succ) (fun i => c i.succ) (fun i => hc i.succ) (act (F 0) ψ)
    exact ih'

lemma finChain_size {m : ℕ} {t : ℕ} (c : Fin t → Circuit htcxGateSet (m + 1)) :
    (finChain c).size = ∑ j : Fin t, (c j).size := by
  induction t with
  | zero =>
    rw [finChain_zero]
    rfl
  | succ t ih =>
    rw [finChain_succ]
    change (c 0 ++ finChain (fun i => c i.succ)).length = _
    rw [List.length_append]
    change (c 0).size + (finChain (fun i => c i.succ)).size = _
    rw [ih]
    rw [Fin.sum_univ_succ]

/-! ### 5. Frobenius norm & Unitary invariance -/

lemma frobNorm_sq_eq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h_norm : ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := Matrix.frobenius_norm_def A
  change ‖A‖ ^ 2 = _
  rw [h_norm]
  have h_nonneg : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _
  have h_pow : ((∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
    norm_num
  rw [h_pow]
  simp_rw [Real.rpow_two]

lemma trace_re_eq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ((Aᴴ * A).trace).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  have h_inner : ∀ j, (∑ i, star (A i j) * A i j).re = ∑ i, ‖A i j‖ ^ 2 := by
    intro j
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (A i j) * A i j = ((‖A i j‖ : ℂ) ^ 2) := RCLike.conj_mul (A i j)
    rw [this, ← Complex.ofReal_pow, Complex.ofReal_re]
  simp_rw [h_inner]
  rw [Finset.sum_comm]

lemma frobNorm_sq_eq_trace_re {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A ^ 2 = ((Aᴴ * A).trace).re := by
  rw [frobNorm_sq_eq, ← trace_re_eq]

lemma frobNorm_sq_eq_trace_mul_self_re {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    frobNorm A ^ 2 = ((A * Aᴴ).trace).re := by
  rw [frobNorm_sq_eq_trace_re, Matrix.trace_mul_comm]

lemma frobNorm_left_unitary_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (V : Matrix m m ℂ) (hV : V ∈ Matrix.unitaryGroup m ℂ) (X : Matrix m n ℂ) :
    frobNorm (V * X) = frobNorm X := by
  have hV_star : Vᴴ * V = (1 : Matrix m m ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hV
  have h_sq : frobNorm (V * X) ^ 2 = frobNorm X ^ 2 := by
    rw [frobNorm_sq_eq_trace_re, frobNorm_sq_eq_trace_re]
    have h_conj : (V * X)ᴴ = Xᴴ * Vᴴ := Matrix.conjTranspose_mul V X
    rw [h_conj]
    congr 2
    calc (Xᴴ * Vᴴ) * (V * X)
      _ = Xᴴ * (Vᴴ * (V * X)) := by rw [Matrix.mul_assoc]
      _ = Xᴴ * ((Vᴴ * V) * X) := by rw [← Matrix.mul_assoc Vᴴ V X]
      _ = Xᴴ * ((1 : Matrix m m ℂ) * X) := by rw [hV_star]
      _ = Xᴴ * X := by rw [Matrix.one_mul]
  have h1 : 0 ≤ frobNorm (V * X) := norm_nonneg _
  have h2 : 0 ≤ frobNorm X := norm_nonneg _
  exact (sq_eq_sq₀ h1 h2).mp h_sq

lemma frobNorm_right_unitary_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (Y : Matrix m n ℂ) :
    frobNorm (Y * U) = frobNorm Y := by
  have hU_star : U * Uᴴ = (1 : Matrix n n ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hU
  have h_sq : frobNorm (Y * U) ^ 2 = frobNorm Y ^ 2 := by
    rw [frobNorm_sq_eq_trace_mul_self_re, frobNorm_sq_eq_trace_mul_self_re]
    have h_conj : (Y * U)ᴴ = Uᴴ * Yᴴ := Matrix.conjTranspose_mul Y U
    rw [h_conj]
    congr 2
    calc (Y * U) * (Uᴴ * Yᴴ)
      _ = Y * (U * (Uᴴ * Yᴴ)) := by rw [Matrix.mul_assoc]
      _ = Y * ((U * Uᴴ) * Yᴴ) := by rw [← Matrix.mul_assoc U Uᴴ Yᴴ]
      _ = Y * ((1 : Matrix n n ℂ) * Yᴴ) := by rw [hU_star]
      _ = Y * Yᴴ := by rw [Matrix.one_mul]
  have h1 : 0 ≤ frobNorm (Y * U) := norm_nonneg _
  have h2 : 0 ≤ frobNorm Y := norm_nonneg _
  exact (sq_eq_sq₀ h1 h2).mp h_sq

def projMat {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun i j => v i * star (v j)

lemma refl_eq_proj {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    householderReflection v = 1 - (2 : ℂ) • projMat v := by
  ext i j
  simp [householderReflection, projMat, Matrix.one_apply, mul_assoc]

lemma projMat_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι)
    (hv : IsState v) :
    projMat v * projMat v = projMat v := by
  ext i j
  simp only [projMat, Matrix.mul_apply, Matrix.of_apply]
  have h_sum : (∑ k, v i * star (v k) * (v k * star (v j))) = v i * star (v j) * ∑ k, star (v k) * v k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  have h_norm : (∑ k, star (v k) * v k) = 1 := by
    have h_sq : ‖v‖ ^ 2 = 1 := by rw [hv, one_pow]
    have h_ip : ‖v‖ ^ 2 = ∑ k, Complex.normSq (v k) := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      exact Finset.sum_congr rfl (fun _ _ => Complex.sq_norm _)
    rw [h_sq] at h_ip
    have h_prod : ∀ k, star (v k) * v k = ((Complex.normSq (v k) : ℝ) : ℂ) := by
      intro k; rw [Complex.normSq_eq_conj_mul_self]; push_cast; rfl
    simp_rw [h_prod, ← Complex.ofReal_sum]
    exact_mod_cast congrArg Complex.ofReal h_ip.symm
  rw [h_sum, h_norm, mul_one]

lemma householderReflection_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) (hv : IsState v) :
    householderReflection v * householderReflection v = 1 := by
  rw [refl_eq_proj]
  calc (1 - (2 : ℂ) • projMat v) * (1 - (2 : ℂ) • projMat v)
    _ = 1 - (2 : ℂ) • projMat v - (2 : ℂ) • projMat v + (4 : ℂ) • (projMat v * projMat v) := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm]
      norm_num; abel
    _ = 1 - (2 : ℂ) • projMat v - (2 : ℂ) • projMat v + (4 : ℂ) • projMat v := by rw [projMat_mul_self v hv]
    _ = 1 := by
      simp only [← smul_add, sub_sub]
      have : (2 : ℂ) • (projMat v + projMat v) = (4 : ℂ) • projMat v := by
        rw [smul_add, ← add_smul]; norm_num
      rw [this, sub_add_cancel]

lemma householderReflection_is_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) (hv : IsState v) :
    householderReflection v ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h_adj : (householderReflection v)ᴴ = householderReflection v := by
    ext i j
    simp only [Matrix.conjTranspose_apply, householderReflection, Matrix.of_apply]
    simp only [star_sub, star_mul, star_star]
    have h2 : star (2 : ℂ) = (2 : ℂ) := by
      change (starRingEnd ℂ) (2 : ℂ) = 2
      have : (2 : ℂ) = ((2 : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.conj_ofReal]
    rw [h2]
    by_cases hij : i = j
    · subst hij; simp; ring
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]; ring
  rw [h_adj, householderReflection_mul_self v hv]


lemma orderedProd_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    (F : Fin t → Matrix ι ι ℂ) (hF : ∀ j, F j ∈ Matrix.unitaryGroup ι ℂ) :
    orderedProd F ∈ Matrix.unitaryGroup ι ℂ := by
  unfold orderedProd
  apply Submonoid.list_prod_mem
  intro M hM
  rw [List.mem_reverse, List.mem_ofFn] at hM
  rcases hM with ⟨j, rfl⟩
  exact hF j

lemma frobNorm_orderedProd_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ}
    (A B : Fin t → Matrix ι ι ℂ)
    (hA : ∀ j, A j ∈ Matrix.unitaryGroup ι ℂ)
    (hB : ∀ j, B j ∈ Matrix.unitaryGroup ι ℂ) :
    frobNorm (orderedProd A - orderedProd B) ≤ ∑ j : Fin t, frobNorm (A j - B j) := by
  induction t with
  | zero =>
    rw [orderedProd_zero, orderedProd_zero, sub_self]
    change ‖(0 : Matrix ι ι ℂ)‖ ≤ _
    rw [norm_zero]
    simp
  | succ t ih =>
    rw [orderedProd_succ, orderedProd_succ]
    have h_split : orderedProd (fun i : Fin t => A i.succ) * A 0 -
                   orderedProd (fun i : Fin t => B i.succ) * B 0 =
        orderedProd (fun i : Fin t => A i.succ) * (A 0 - B 0) +
        (orderedProd (fun i : Fin t => A i.succ) - orderedProd (fun i : Fin t => B i.succ)) * B 0 := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [h_split]
    calc frobNorm (orderedProd (fun i : Fin t => A i.succ) * (A 0 - B 0) +
                   (orderedProd (fun i : Fin t => A i.succ) - orderedProd (fun i : Fin t => B i.succ)) * B 0)
      _ ≤ frobNorm (orderedProd (fun i : Fin t => A i.succ) * (A 0 - B 0)) +
          frobNorm ((orderedProd (fun i : Fin t => A i.succ) - orderedProd (fun i : Fin t => B i.succ)) * B 0) := norm_add_le _ _
      _ = frobNorm (A 0 - B 0) +
          frobNorm (orderedProd (fun i : Fin t => A i.succ) - orderedProd (fun i : Fin t => B i.succ)) := by
        rw [frobNorm_left_unitary_eq _ (orderedProd_unitary _ (fun i => hA i.succ)),
            frobNorm_right_unitary_eq _ (hB 0)]
      _ ≤ frobNorm (A 0 - B 0) + ∑ i : Fin t, frobNorm (A i.succ - B i.succ) := by
        linarith [ih (fun i => A i.succ) (fun i => B i.succ) (fun i => hA i.succ) (fun i => hB i.succ)]
      _ = ∑ j : Fin (t + 1), frobNorm (A j - B j) := by
        rw [Fin.sum_univ_succ]

lemma hasDenominator_sqrt2_of_two {m : ℕ} {z : ℂ} (h : HasDenominator 2 m z) :
    HasDenominator (Real.sqrt 2) (2 * m) z := by
  rcases h with ⟨a, b, c, d, hz⟩
  refine ⟨a, b, c, d, ?_⟩
  rw [hz]
  congr 1
  rw [pow_mul]
  have : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    push_cast; rfl
  rw [this]
  push_cast; rfl

lemma sum_le_sum_embedding {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a : α, f (e a)) ≤ ∑ b : β, f b := by
  have h_img : (Finset.univ.map e) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg h_img fun b _ _ => hf b

lemma frobNorm_submatrix_equiv_eq {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    (e₁ : m' ≃ m) (e₂ : n' ≃ n) (A : Matrix m n ℂ) :
    frobNorm (A.submatrix e₁ e₂) = frobNorm A := by
  have h_sq : frobNorm (A.submatrix e₁ e₂) ^ 2 = frobNorm A ^ 2 := by
    rw [frobNorm_sq_eq, frobNorm_sq_eq]
    have h_inner (i : m') : (∑ j : n', ‖A.submatrix e₁ e₂ i j‖ ^ 2) = ∑ j' : n, ‖A (e₁ i) j'‖ ^ 2 := by
      change (∑ j : n', ‖A (e₁ i) (e₂ j)‖ ^ 2) = _
      exact e₂.sum_comp (fun j' => ‖A (e₁ i) j'‖ ^ 2)
    simp_rw [h_inner]
    exact e₁.sum_comp (fun i' => ∑ j' : n, ‖A i' j'‖ ^ 2)
  have h1 : 0 ≤ frobNorm (A.submatrix e₁ e₂) := norm_nonneg _
  have h2 : 0 ≤ frobNorm A := norm_nonneg _
  exact (sq_eq_sq₀ h1 h2).mp h_sq

lemma frobNorm_matFromBQ {n : ℕ} (M : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ) :
    frobNorm (matFromBQ M) = frobNorm M :=
  frobNorm_submatrix_equiv_eq (equivBQ n) (equivBQ n) M

def embedQubitsNatAdd (n : ℕ) : Qubits n ↪ Qubits (n + 1) where
  toFun x := Fin.append x (fun _ => false)
  inj' x1 x2 h := by
    ext i
    have := congr_fun h (Fin.castAdd 1 i)
    dsimp [Fin.append] at this
    rw [Fin.addCases_left, Fin.addCases_left] at this
    exact this

def embedQubitsNatAdd2 (n : ℕ) : Qubits n ↪ Qubits (n + 2) where
  toFun x := Fin.append x (fun _ => false)
  inj' x1 x2 h := by
    ext i
    have := congr_fun h (Fin.castAdd 2 i)
    dsimp [Fin.append] at this
    rw [Fin.addCases_left, Fin.addCases_left] at this
    exact this

lemma frobNorm_submatrix_cols_le {k l : ℕ} (A : Matrix (Qubits (k + l)) (Qubits (k + l)) ℂ) :
    (∑ y : Qubits (k + l), ∑ x : Qubits k, ‖A y (Fin.append x (fun _ => false))‖ ^ 2) ≤
      frobNorm A ^ 2 := by
  rw [frobNorm_sq_eq]
  let e : Qubits k ↪ Qubits (k + l) := ⟨fun x => Fin.append x (fun _ => false), fun x1 x2 h => by
    ext i
    have := congr_fun h (Fin.castAdd l i)
    dsimp [Fin.append] at this
    rw [Fin.addCases_left, Fin.addCases_left] at this
    exact this⟩
  refine Finset.sum_le_sum fun y _ => ?_
  exact sum_le_sum_embedding e (fun z => ‖A y z‖ ^ 2) (fun _ => by positivity)

/-! ### 6. Algebraic matrix error to idealMap -/

lemma initializedMap_mul {n w : ℕ} (A B : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ) :
    initializedMap (A * B) = A * initializedMap B := by
  ext y x; rfl

lemma idealMap_mul {n w : ℕ} (U₂ U₁ : Matrix (Qubits n) (Qubits n) ℂ) :
    idealMap (U₂ * U₁) w = idealMap U₂ w * U₁ := by
  ext y x
  simp only [idealMap, Matrix.of_apply, Matrix.mul_apply]
  split_ifs with h <;> simp

lemma mul_idealMap {n w : ℕ} (A : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ)
    (U : Matrix (Qubits n) (Qubits n) ℂ) :
    A * idealMap U w = initializedMap A * U := by
  ext y x
  change (∑ j, A y j * ((if (qubitsAppendEquiv n w j).2 = (fun _ => false) then U (qubitsAppendEquiv n w j).1 x else 0))) =
    ∑ j, A y (Fin.append j (fun _ => false)) * U j x
  rw [← (qubitsAppendEquiv n w).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero]
  simp [qubitsAppendEquiv]

/-! ### 7. Two zero coordinates for n ≥ 2 -/

def flipWire0 {n : ℕ} (hn : 2 ≤ n) (j : Qubits n) : Qubits n :=
  fun i => if i = ⟨0, by omega⟩ then !(j ⟨0, by omega⟩) else j i

def flipWire1 {n : ℕ} (hn : 2 ≤ n) (j : Qubits n) : Qubits n :=
  fun i => if i = ⟨1, by omega⟩ then !(j ⟨1, by omega⟩) else j i

lemma flipWire0_ne {n : ℕ} (hn : 2 ≤ n) (j : Qubits n) : flipWire0 hn j ≠ j := by
  intro h
  have h0 : flipWire0 hn j ⟨0, by omega⟩ = j ⟨0, by omega⟩ := congrFun h ⟨0, by omega⟩
  dsimp [flipWire0] at h0
  cases hj : j ⟨0, by omega⟩
  · rw [hj] at h0; revert h0; decide
  · rw [hj] at h0; revert h0; decide

lemma flipWire1_ne {n : ℕ} (hn : 2 ≤ n) (j : Qubits n) : flipWire1 hn j ≠ j := by
  intro h
  have h1 : flipWire1 hn j ⟨1, by omega⟩ = j ⟨1, by omega⟩ := congrFun h ⟨1, by omega⟩
  dsimp [flipWire1] at h1
  cases hj : j ⟨1, by omega⟩
  · rw [hj] at h1; revert h1; decide
  · rw [hj] at h1; revert h1; decide

lemma flipWire0_ne_flipWire1 {n : ℕ} (hn : 2 ≤ n) (j : Qubits n) : flipWire0 hn j ≠ flipWire1 hn j := by
  intro h
  have h0 : flipWire0 hn j ⟨0, by omega⟩ = flipWire1 hn j ⟨0, by omega⟩ := congrFun h ⟨0, by omega⟩
  dsimp [flipWire0, flipWire1] at h0
  cases hj : j ⟨0, by omega⟩
  · rw [hj] at h0; revert h0; decide
  · rw [hj] at h0; revert h0; decide

lemma reflectionVector_eval_true_ne {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (j : Qubits n) (x : Qubits n) (h : x ≠ j) :
    reflectionVector U j true (true, x) = 0 := by
  dsimp [reflectionVector, tensorVec, ket]
  simp [Pi.single_eq_of_ne h]

lemma reflectionVector_has_two_zero_coords {n : ℕ} (hn : 2 ≤ n)
    (U : Matrix (Qubits n) (Qubits n) ℂ) (j : Qubits n) :
    ∃ j' l' : Qubits (n + 1), j' ≠ l' ∧
      vecFromBQ (reflectionVector U j true) j' = 0 ∧
      vecFromBQ (reflectionVector U j true) l' = 0 := by
  let x0 := flipWire0 hn j
  let x1 := flipWire1 hn j
  have hx0_ne := flipWire0_ne hn j
  have hx1_ne := flipWire1_ne hn j
  have hx_diff := flipWire0_ne_flipWire1 hn j
  let j' : Qubits (n + 1) := (equivBQ n).symm (true, x0)
  let l' : Qubits (n + 1) := (equivBQ n).symm (true, x1)
  refine ⟨j', l', ?_, ?_, ?_⟩
  · intro heq
    apply hx_diff
    exact congrArg Prod.snd ((equivBQ n).symm.injective heq)
  · dsimp [vecFromBQ, j']
    rw [Equiv.apply_symm_apply]
    exact reflectionVector_eval_true_ne U j x0 hx0_ne
  · dsimp [vecFromBQ, l']
    rw [Equiv.apply_symm_apply]
    exact reflectionVector_eval_true_ne U j x1 hx1_ne

/-! ### 8. Submatrix Frobenius norm bound -/

def emb_true (n : ℕ) (x : Qubits n) : Qubits (n + 1) :=
  (equivBQ n).symm (true, x)

lemma emb_true_injective (n : ℕ) : Function.Injective (emb_true n) := by
  intro x1 x2 h
  have := (equivBQ n).symm.injective h
  exact (Prod.ext_iff.mp this).2

lemma vecFromBQ_tensor_ket_true_ket {n : ℕ} (x : Qubits n) :
    vecFromBQ (tensorVec (ket true) (ket x)) = ket (emb_true n x) := by
  ext z
  dsimp [vecFromBQ, tensorVec, ket]
  by_cases hz : z = emb_true n x
  · subst hz
    dsimp [emb_true]
    rw [Equiv.apply_symm_apply]
    simp
  · rw [Pi.single_eq_of_ne hz]
    have : (equivBQ n z) ≠ (true, x) := by
      intro h
      apply hz
      dsimp [emb_true]
      rw [← (equivBQ n).apply_eq_iff_eq]
      rw [h, Equiv.apply_symm_apply]
    by_cases h1 : (equivBQ n z).1 = true
    · by_cases h2 : (equivBQ n z).2 = x
      · exfalso; apply this; exact Prod.ext h1 h2
      · rw [Pi.single_eq_of_ne h2, mul_zero]
    · rw [Pi.single_eq_of_ne h1, zero_mul]

lemma norm_sq_zeroAncillaVec_one {n : ℕ} (v : EuclideanSpace ℂ (Qubits (n + 1))) :
    (∑ y : Qubits (n + 2), ‖(zeroAncillaVec v 1) y‖ ^ 2) = ∑ z : Qubits (n + 1), ‖v z‖ ^ 2 := by
  have h_eq : (∑ y : Qubits (n + 2), ‖(zeroAncillaVec v 1) y‖ ^ 2) =
      ∑ p : Qubits (n + 1) × Qubits 1, ‖(zeroAncillaVec v 1) ((qubitsAppendEquiv (n + 1) 1).symm p)‖ ^ 2 := by
    rw [← (qubitsAppendEquiv (n + 1) 1).symm.sum_comp]
  rw [h_eq, Fintype.sum_prod_type]
  have h_sum1 (z : Qubits (n + 1)) :
      (∑ b : Qubits 1, ‖(zeroAncillaVec v 1) ((qubitsAppendEquiv (n + 1) 1).symm (z, b))‖ ^ 2) =
      ‖v z‖ ^ 2 := by
    rw [sum_qubits1_real]
    dsimp [zeroAncillaVec]
    have h_ne : ¬(fun _ : Fin 1 => true) = (fun _ => false) := by
      intro h; have := congr_fun h 0; contradiction
    simp [h_ne]
  simp_rw [h_sum1]

lemma frobNorm_zeroAncillaVec_col_le {n : ℕ}
    (M : Matrix (Qubits (n + 2)) (Qubits n) ℂ)
    (Δ : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (hM : ∀ y x, M y x = (zeroAncillaVec (act Δ (ket (emb_true n x))) 1) y) :
    frobNorm M ≤ frobNorm Δ := by
  have h_sq : frobNorm M ^ 2 ≤ frobNorm Δ ^ 2 := by
    rw [frobNorm_sq_eq, frobNorm_sq_eq]
    have h_swap : (∑ i, ∑ j, ‖M i j‖ ^ 2) = ∑ x : Qubits n, ∑ y : Qubits (n + 2), ‖M y x‖ ^ 2 :=
      Finset.sum_comm
    rw [h_swap]
    have h_col (x : Qubits n) :
        (∑ y : Qubits (n + 2), ‖M y x‖ ^ 2) = ∑ z : Qubits (n + 1), ‖Δ z (emb_true n x)‖ ^ 2 := by
      have h1 : (∑ y : Qubits (n + 2), ‖M y x‖ ^ 2) =
          ∑ y : Qubits (n + 2), ‖(zeroAncillaVec (act Δ (ket (emb_true n x))) 1) y‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun y _ => by rw [hM y x])
      rw [h1, norm_sq_zeroAncillaVec_one]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      dsimp [act]
      simp only [Matrix.mulVec, dotProduct, ket, PiLp.single_apply, mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [h_col]
    have h_swap_Δ : (∑ i, ∑ j, ‖Δ i j‖ ^ 2) = ∑ k : Qubits (n + 1), ∑ z : Qubits (n + 1), ‖Δ z k‖ ^ 2 :=
      Finset.sum_comm
    rw [h_swap_Δ]
    let e : Qubits n ↪ Qubits (n + 1) := ⟨emb_true n, emb_true_injective n⟩
    exact sum_le_sum_embedding e (fun k => ∑ z : Qubits (n + 1), ‖Δ z k‖ ^ 2)
      (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have h1 : 0 ≤ frobNorm M := norm_nonneg _
  have h2 : 0 ≤ frobNorm Δ := norm_nonneg _
  exact (sq_le_sq₀ h1 h2).mp h_sq

def emb_false (n : ℕ) (x : Qubits n) : Qubits (n + 1) :=
  (equivBQ n).symm (false, x)

lemma emb_false_injective (n : ℕ) : Function.Injective (emb_false n) := by
  intro x1 x2 h
  have := (equivBQ n).symm.injective h
  exact (Prod.ext_iff.mp this).2

lemma vecFromBQ_tensor_ket_false_ket {n : ℕ} (x : Qubits n) :
    vecFromBQ (tensorVec (ket false) (ket x)) = ket (emb_false n x) := by
  ext z
  dsimp [vecFromBQ, tensorVec, ket]
  by_cases hz : z = emb_false n x
  · subst hz
    dsimp [emb_false]
    rw [Equiv.apply_symm_apply]
    simp
  · rw [Pi.single_eq_of_ne hz]
    have : (equivBQ n z) ≠ (false, x) := by
      intro h
      apply hz
      dsimp [emb_false]
      rw [← (equivBQ n).apply_eq_iff_eq]
      rw [h, Equiv.apply_symm_apply]
    by_cases h1 : (equivBQ n z).1 = false
    · by_cases h2 : (equivBQ n z).2 = x
      · exfalso; apply this; exact Prod.ext h1 h2
      · rw [Pi.single_eq_of_ne h2, mul_zero]
    · rw [Pi.single_eq_of_ne h1, zero_mul]

lemma frobNorm_zeroAncillaVec_col_false_le {n : ℕ}
    (M : Matrix (Qubits (n + 2)) (Qubits n) ℂ)
    (Δ : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (hM : ∀ y x, M y x = (zeroAncillaVec (act Δ (ket (emb_false n x))) 1) y) :
    frobNorm M ≤ frobNorm Δ := by
  have h_sq : frobNorm M ^ 2 ≤ frobNorm Δ ^ 2 := by
    rw [frobNorm_sq_eq, frobNorm_sq_eq]
    have h_swap : (∑ i, ∑ j, ‖M i j‖ ^ 2) = ∑ x : Qubits n, ∑ y : Qubits (n + 2), ‖M y x‖ ^ 2 :=
      Finset.sum_comm
    rw [h_swap]
    have h_col (x : Qubits n) :
        (∑ y : Qubits (n + 2), ‖M y x‖ ^ 2) = ∑ z : Qubits (n + 1), ‖Δ z (emb_false n x)‖ ^ 2 := by
      have h1 : (∑ y : Qubits (n + 2), ‖M y x‖ ^ 2) =
          ∑ y : Qubits (n + 2), ‖(zeroAncillaVec (act Δ (ket (emb_false n x))) 1) y‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun y _ => by rw [hM y x])
      rw [h1, norm_sq_zeroAncillaVec_one]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      dsimp [act]
      simp only [Matrix.mulVec, dotProduct, ket, PiLp.single_apply, mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [h_col]
    have h_swap_Δ : (∑ i, ∑ j, ‖Δ i j‖ ^ 2) = ∑ k : Qubits (n + 1), ∑ z : Qubits (n + 1), ‖Δ z k‖ ^ 2 :=
      Finset.sum_comm
    rw [h_swap_Δ]
    let e : Qubits n ↪ Qubits (n + 1) := ⟨emb_false n, emb_false_injective n⟩
    exact sum_le_sum_embedding e (fun k => ∑ z : Qubits (n + 1), ‖Δ z k‖ ^ 2)
      (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have h1 : 0 ≤ frobNorm M := norm_nonneg _
  have h2 : 0 ≤ frobNorm Δ := norm_nonneg _
  exact (sq_le_sq₀ h1 h2).mp h_sq

lemma act_identityExtension_tensor_ket_false {n : ℕ}
    (A : Matrix (Qubits n) (Qubits n) ℂ) (psi : EuclideanSpace ℂ (Qubits n)) :
    act (identityExtension A) (tensorVec (ket false) psi) = tensorVec (ket false) (act A psi) := by
  ext ⟨c, x⟩
  simp only [act, tensorVec, ket, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_bool, identityExtension, Matrix.of_apply, PiLp.toLp_apply,
    PiLp.single_apply]
  cases c <;> simp

lemma act_matFromBQ_identityExtension {n : ℕ}
    (A : Matrix (Qubits n) (Qubits n) ℂ) (psi : EuclideanSpace ℂ (Qubits n)) :
    act (matFromBQ (identityExtension A)) (zeroAncillaVec psi 1) = zeroAncillaVec (act A psi) 1 := by
  rw [← vecFromBQ_tensor_ket_false, act_matFromBQ, act_identityExtension_tensor_ket_false, vecFromBQ_tensor_ket_false]

lemma matFromBQ_sub {n : ℕ} (A B : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ) :
    matFromBQ (A - B) = matFromBQ A - matFromBQ B := by
  ext y z; rfl


/-! ### 9. Logarithmic and size bounds -/

lemma log_div_pow_two (eps : ℝ) (heps : 0 < eps) (n : ℕ) :
    Real.log (1 / (eps / (2 : ℝ) ^ n)) = Real.log (1 / eps) + (n : ℝ) * Real.log 2 := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h_div : 1 / (eps / (2 : ℝ) ^ n) = (1 / eps) * (2 : ℝ) ^ n := by
    rw [one_div_div, mul_comm, mul_one_div]
  rw [h_div, Real.log_mul (by positivity) (by positivity), Real.log_pow]

lemma log_div_pow_two_div (eps : ℝ) (heps : 0 < eps) (n : ℕ) :
    Real.log (1 / (eps / (2 : ℝ) ^ n)) / Real.log 2 =
      Real.log (1 / eps) / Real.log 2 + (n : ℝ) := by
  rw [log_div_pow_two eps heps n]
  have hlog2 : Real.log 2 ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num)
  rw [add_div, mul_div_cancel_right₀ _ hlog2]

lemma total_size_bound (A₀ C : ℝ) (hA₀ : 0 < A₀) (hC : 0 < C)
    (n m : ℕ) (hn : 1 ≤ n) (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hm_bound : (m : ℝ) ≤ (((n + 1 + 1) / 2 : ℕ) : ℝ) + C * (1 + Real.log (1 / (eps / (2 : ℝ) ^ n)) / Real.log 2))
    (S : ℝ)
    (hS : S ≤ (2 : ℝ) ^ n * (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1))) :
    (6 : ℝ) + S ≤ (16 * (C + 2) * A₀ + 6) * (4 : ℝ) ^ n * (n : ℝ) *
      (Real.log (1 / eps) / Real.log 2 + (n : ℝ)) := by
  set L := Real.log (1 / eps) / Real.log 2
  have hL_nonneg : 0 ≤ L := by
    have h1 : 1 ≤ 1 / eps := one_le_one_div heps0 heps1
    have hlog_nonneg : 0 ≤ Real.log (1 / eps) := Real.log_nonneg h1
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg hlog_nonneg hlog2_pos.le
  have h_n_ge : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have h_n2_div : (((n + 1 + 1) / 2 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    have : (n + 1 + 1) / 2 ≤ n + 1 := by omega
    have h_le : (((n + 1 + 1) / 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h_le ⊢
    linarith [h_n_ge]
  rw [log_div_pow_two_div eps heps0 n] at hm_bound
  have hm_le : (m : ℝ) ≤ (2 * C + 2) * (L + (n : ℝ)) := by
    calc (m : ℝ) ≤ (((n + 1 + 1) / 2 : ℕ) : ℝ) + C * (1 + (L + (n : ℝ))) := hm_bound
      _ ≤ 2 * (n : ℝ) + C * ((n : ℝ) + (L + (n : ℝ))) := by
        refine add_le_add h_n2_div (mul_le_mul_of_nonneg_left ?_ hC.le)
        linarith [h_n_ge]
      _ ≤ (2 * C + 2) * (L + (n : ℝ)) := by
        nlinarith [hL_nonneg, h_n_ge, hC]
  have hk1 : (((2 * m + 1 : ℕ) : ℝ) + 1) ≤ 4 * (C + 1.5) * (L + (n : ℝ)) := by
    push_cast
    linarith [hm_le, h_n_ge, hL_nonneg]
  have hn1 : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast; linarith [h_n_ge]
  have h2pow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
    rw [pow_succ, mul_comm]
  have h4pow : (2 : ℝ) ^ n * (2 : ℝ) ^ n = (4 : ℝ) ^ n := by
    rw [← mul_pow]; norm_num
  have h4_ge_one : 1 ≤ (4 : ℝ) ^ n := by
    have : (1 : ℝ) = (1 : ℝ) ^ n := by simp
    rw [this]
    refine pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h_Ln_ge : 1 ≤ L + (n : ℝ) := by linarith [hL_nonneg, h_n_ge]
  have h_one_le : 1 ≤ (4 : ℝ) ^ n * (n : ℝ) * (L + (n : ℝ)) := by
    have : 1 ≤ (4 : ℝ) ^ n * (n : ℝ) := by nlinarith [h4_ge_one, h_n_ge]
    nlinarith [this, h_Ln_ge]
  have hS_bound : S ≤ 16 * (C + 1.5) * A₀ * (4 : ℝ) ^ n * (n : ℝ) * (L + (n : ℝ)) := by
    calc S ≤ (2 : ℝ) ^ n * (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1)) := hS
      _ = A₀ * ((2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)) * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1) := by ring
      _ = A₀ * (2 * ((2 : ℝ) ^ n * (2 : ℝ) ^ n)) * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1) := by rw [h2pow]; ring
      _ = 2 * A₀ * (4 : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1) := by rw [h4pow]; ring
      _ ≤ 2 * A₀ * (4 : ℝ) ^ n * (2 * (n : ℝ)) * (4 * (C + 1.5) * (L + (n : ℝ))) := by
        refine mul_le_mul (mul_le_mul (by linarith) hn1 (by positivity) (by positivity)) hk1 (by positivity) (by positivity)
      _ = 16 * (C + 1.5) * A₀ * (4 : ℝ) ^ n * (n : ℝ) * (L + (n : ℝ)) := by ring
  have h_coeff : 16 * (C + 1.5) * A₀ ≤ 16 * (C + 2) * A₀ := by
    have : C + 1.5 ≤ C + 2 := by linarith
    nlinarith [hA₀]
  calc (6 : ℝ) + S
    _ ≤ 6 * ((4 : ℝ) ^ n * (n : ℝ) * (L + (n : ℝ))) + 16 * (C + 1.5) * A₀ * (4 : ℝ) ^ n * (n : ℝ) * (L + (n : ℝ)) := by
      linarith [h_one_le, hS_bound]
    _ ≤ 6 * ((4 : ℝ) ^ n * (n : ℝ) * (L + (n : ℝ))) + 16 * (C + 2) * A₀ * (4 : ℝ) ^ n * (n : ℝ) * (L + (n : ℝ)) := by
      have : 0 ≤ (4 : ℝ) ^ n * (n : ℝ) * (L + (n : ℝ)) := by positivity
      nlinarith [h_coeff, this]
    _ = (16 * (C + 2) * A₀ + 6) * (4 : ℝ) ^ n * (n : ℝ) * (L + (n : ℝ)) := by ring

/-! ### 10. Direct reduction when reflection vectors have two zero coordinates -/

lemma zeroAncillaVec_ket {m w : ℕ} (x : Qubits m) :
    zeroAncillaVec (ket x) w = ket (Fin.append x (fun _ => false)) := by
  ext z
  dsimp [zeroAncillaVec, ket]
  simp only [Pi.single_apply]
  have h_equiv := (qubitsAppendEquiv m w).apply_eq_iff_eq (x := z) (y := (qubitsAppendEquiv m w).symm (x, fun _ => false))
  rw [Equiv.apply_symm_apply] at h_equiv
  have h_append : (qubitsAppendEquiv m w).symm (x, fun _ => false) = Fin.append x (fun _ => false) := rfl
  rw [h_append] at h_equiv
  by_cases hz : z = Fin.append x (fun _ => false)
  · rw [if_pos hz]
    rw [← h_equiv] at hz
    have hz1 : (qubitsAppendEquiv m w z).1 = x := congrArg Prod.fst hz
    have hz2 : (qubitsAppendEquiv m w z).2 = (fun _ => false) := congrArg Prod.snd hz
    rw [if_pos hz2, if_pos hz1]
  · rw [if_neg hz]
    split_ifs with h2 h1
    · exfalso; apply hz
      rw [← h_equiv]
      exact Prod.ext h1 h2
    · rfl
    · rfl

lemma initializedMap_apply {n w : ℕ} (M : Matrix (Qubits (n + w)) (Qubits (n + w)) ℂ)
    (y : Qubits (n + w)) (x : Qubits n) :
    initializedMap M y x = act M (zeroAncillaVec (ket x) w) y := by
  rw [zeroAncillaVec_ket]
  dsimp [initializedMap, act]
  simp only [Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
    mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma idealMap_apply {n w : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (y : Qubits (n + w)) (x : Qubits n) :
    idealMap U w y x = (zeroAncillaVec (act U (ket x)) w) y := by
  dsimp [idealMap, zeroAncillaVec, act]
  simp only [Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
    mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma zeroAncillaVec_act_sub {n : ℕ}
    (P Q : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (v : EuclideanSpace ℂ (Qubits (n + 1))) (y : Qubits (n + 2)) :
    (zeroAncillaVec (act P v) 1) y - (zeroAncillaVec (act Q v) 1) y =
      (zeroAncillaVec (act (P - Q) v) 1) y := by
  dsimp [zeroAncillaVec, act]
  split_ifs with h
  · rw [Matrix.sub_mulVec]; rfl
  · simp

lemma ket_isState {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι) :
    IsState (ket x) := by
  dsimp [IsState, ket]
  rw [EuclideanSpace.norm_eq]
  have : (∑ i : ι, ‖(EuclideanSpace.single x (1 : ℂ)).ofLp i‖ ^ 2) = 1 := by
    simp only [PiLp.single_apply]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact (h (Finset.mem_univ x)).elim
  rw [this, Real.sqrt_one]

lemma initializedMap_sub_idealMap_eq {n : ℕ}
    (U : Matrix (Qubits n) (Qubits n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (phi : Fin (2 ^ n) → EuclideanSpace ℂ (Qubits (n + 1)))
    (c' : Fin (2 ^ n) → Circuit htcxGateSet ((n + 1) + 1))
    (hc'_imp : ∀ j, ImplementsWithCleanAncillas (c' j).unitary (householderReflection (phi j)))
    (y : Qubits (n + 2)) (x : Qubits n) :
    (@initializedMap n 2 (padCircuit (cX n) ++ finChain c').unitary - idealMap U 2) y x =
      (zeroAncillaVec (act (orderedProd (fun j => householderReflection (phi j)) - matFromBQ (simulationDilation U)) (ket (emb_true n x))) 1) y := by
  change @initializedMap n 2 (padCircuit (cX n) ++ finChain c').unitary y x - idealMap U 2 y x = _
  rw [initializedMap_apply, idealMap_apply]
  rw [circuit_unitary_append, act_mul]
  rw [zeroAncillaVec_two]
  have h_X : act (padCircuit (cX n)).unitary (zeroAncillaVec (zeroAncillaVec (ket x) 1) 1) =
      zeroAncillaVec (ket (emb_true n x)) 1 := by
    rw [act_padCircuit, act_cX_zeroAncillaVec, vecFromBQ_tensor_ket_true_ket]
  rw [h_X]
  have h_chain : act (finChain c').unitary (zeroAncillaVec (ket (emb_true n x)) 1) =
      zeroAncillaVec (act (orderedProd (fun j => householderReflection (phi j))) (ket (emb_true n x))) 1 := by
    exact implements_finChain (fun j => householderReflection (phi j)) c' hc'_imp _
  rw [h_chain]
  rw [zeroAncillaVec_two]
  have h_ideal : zeroAncillaVec (act U (ket x)) 1 =
      act (matFromBQ (simulationDilation U)) (ket (emb_true n x)) := by
    rw [← vecFromBQ_tensor_ket_false]
    rcases reflectionDecomposition n U hU with ⟨-, h_dil, -⟩
    have hx_state : IsState (ket x) := ket_isState x
    rw [← h_dil (ket x) hx_state]
    rw [← act_matFromBQ, vecFromBQ_tensor_ket_true_ket]
  rw [h_ideal]
  exact zeroAncillaVec_act_sub (orderedProd (fun j => householderReflection (phi j)))
    (matFromBQ (simulationDilation U)) (ket (emb_true n x)) y

lemma approximateSynthesis_of_two_zeros (A₀ C : ℝ) (hA₀ : 0 < A₀) (hC : 0 < C)
    (h_synth : ∀ n : ℕ, 1 ≤ n → ∀ kappa : ℕ,
      ∀ phi : EuclideanSpace ℂ (Qubits n), IsState phi →
        (∀ i, HasDenominator (Real.sqrt 2) kappa (phi i)) →
      ∃ w : ℕ, w ≤ 1 ∧ ∃ c : Circuit htcxGateSet (n + w),
        ImplementsWithCleanAncillas c.unitary (householderReflection phi) ∧
        (c.size : ℝ) ≤ A₀ * (2 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1))
    (h_approx : ∀ n : ℕ, 1 ≤ n →
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∃ m : ℕ, (n + 1) / 2 ≤ m ∧
        (m : ℝ) ≤ (((n + 1) / 2 : ℕ) : ℝ) +
          C * (1 + Real.log (1 / eps) / Real.log 2) ∧
      ∀ psi : EuclideanSpace ℂ (Qubits n), IsState psi →
        (∃ phi0 phi1 : EuclideanSpace ℂ (Bool × Qubits n),
          IsState phi0 ∧ IsState phi1 ∧
          (∀ z, HasDenominator 2 m (phi0 z)) ∧
          (∀ z, HasDenominator 2 m (phi1 z)) ∧
          frobNorm (householderReflection phi0 * householderReflection phi1 - identityExtension (householderReflection psi)) ≤ eps) ∧
        ((∃ j l : Qubits n, j ≠ l ∧ psi j = 0 ∧ psi l = 0) →
          ∃ phi : EuclideanSpace ℂ (Qubits n), IsState phi ∧
            (∀ z, HasDenominator 2 m (phi z)) ∧
            frobNorm (householderReflection phi - householderReflection psi) ≤ eps))
    (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix (Qubits n) (Qubits n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (h_two_zero : ∀ j : Fin (2 ^ n),
      ∃ j' l' : Qubits (n + 1), j' ≠ l' ∧
        vecFromBQ (reflectionVector U ((bitsEquivFin n).symm j) true) j' = 0 ∧
        vecFromBQ (reflectionVector U ((bitsEquivFin n).symm j) true) l' = 0)
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c : Circuit htcxGateSet (n + 2),
      frobNorm (initializedMap c.unitary - idealMap U 2) ≤ eps ∧
      (c.size : ℝ) ≤ (16 * (C + 2) * A₀ + 6) * (4 : ℝ) ^ n * (n : ℝ) *
        (Real.log (1 / eps) / Real.log 2 + (n : ℝ)) := by
  set eps' : ℝ := eps / (2 : ℝ) ^ n
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have heps'_pos : 0 < eps' := div_pos heps0 h2n_pos
  have h2n_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
    have : (1 : ℝ) = (1 : ℝ) ^ n := by simp
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have heps'_le : eps' ≤ 1 := by
    have : eps' ≤ eps := by
      dsimp [eps']
      exact div_le_self heps0.le h2n_ge_one
    linarith [heps1]
  rcases h_approx (n + 1) (by omega) eps' heps'_pos heps'_le with ⟨m, hm_ge, hm_bound, h_psi⟩
  rcases reflectionDecomposition n U hU with ⟨hU_unit, h_dil, hv_state, h_prod, -⟩
  let v : Fin (2 ^ n) → EuclideanSpace ℂ (Bool × Qubits n) :=
    fun j => reflectionVector U ((bitsEquivFin n).symm j) true
  have hv_state' (j : Fin (2 ^ n)) : IsState (v j) := hv_state ((bitsEquivFin n).symm j) true
  have h_synth_step (j : Fin (2 ^ n)) :
      ∃ phi_j : EuclideanSpace ℂ (Qubits (n + 1)), IsState phi_j ∧
        frobNorm (householderReflection phi_j - householderReflection (vecFromBQ (v j))) ≤ eps' ∧
        ∃ c'_j : Circuit htcxGateSet ((n + 1) + 1),
          ImplementsWithCleanAncillas c'_j.unitary (householderReflection phi_j) ∧
          (c'_j.size : ℝ) ≤ A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1) := by
    have hvj_state : IsState (vecFromBQ (v j)) := vecFromBQ_isState (hv_state' j)
    rcases (h_psi (vecFromBQ (v j)) hvj_state).2 (h_two_zero j) with ⟨phi_j, hphi_state, hphi_denom, hphi_frob⟩
    have hphi_denom' : ∀ z, HasDenominator (Real.sqrt 2) (2 * m) (phi_j z) :=
      fun z => hasDenominator_sqrt2_of_two (hphi_denom z)
    rcases h_synth (n + 1) (by omega) (2 * m) phi_j hphi_state hphi_denom' with ⟨w_j, hw_j, c_j, hc_j, h_size_j⟩
    rcases normalize_clean_ancilla (householderReflection phi_j) w_j hw_j c_j hc_j with ⟨c'_j, hc'_j, h_size_eq⟩
    refine ⟨phi_j, hphi_state, hphi_frob, c'_j, hc'_j, ?_⟩
    rw [h_size_eq]
    calc (c_j.size : ℝ) ≤ A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) + 1) := h_size_j
      _ ≤ A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        push_cast; linarith
  choose phi hphi_state hphi_frob c' hc'_imp hc'_size using h_synth_step
  let c_chain : Circuit htcxGateSet (n + 2) := finChain c'
  let c_X_pad : Circuit htcxGateSet (n + 2) := padCircuit (cX n)
  let c_total : Circuit htcxGateSet (n + 2) := c_X_pad ++ c_chain
  refine ⟨c_total, ?_, ?_⟩
  · have hM_eq (y : Qubits (n + 2)) (x : Qubits n) :
        (@initializedMap n 2 c_total.unitary - idealMap U 2) y x =
          (zeroAncillaVec (act (orderedProd (fun j => householderReflection (phi j)) - matFromBQ (simulationDilation U)) (ket (emb_true n x))) 1) y := by
      exact initializedMap_sub_idealMap_eq U hU phi c' hc'_imp y x
    have h_col := frobNorm_zeroAncillaVec_col_le (@initializedMap n 2 c_total.unitary - idealMap U 2) _ hM_eq
    have h_prod_mat : matFromBQ (simulationDilation U) =
        orderedProd (fun j => householderReflection (vecFromBQ (v j))) := by
      rw [h_prod, matFromBQ_orderedProd]
      congr 1
      funext j
      exact matFromBQ_refl (v j)
    rw [h_prod_mat] at h_col
    have h_prod_le : frobNorm (orderedProd (fun j => householderReflection (phi j)) - orderedProd (fun j => householderReflection (vecFromBQ (v j)))) ≤
        ∑ j : Fin (2 ^ n), frobNorm (householderReflection (phi j) - householderReflection (vecFromBQ (v j))) := by
      exact frobNorm_orderedProd_sub_le (fun j => householderReflection (phi j)) (fun j => householderReflection (vecFromBQ (v j)))
        (fun j => householderReflection_is_unitary (phi j) (hphi_state j))
        (fun j => householderReflection_is_unitary (vecFromBQ (v j)) (vecFromBQ_isState (hv_state' j)))
    have h_sum_le : (∑ j : Fin (2 ^ n), frobNorm (householderReflection (phi j) - householderReflection (vecFromBQ (v j)))) ≤ eps := by
      calc (∑ j : Fin (2 ^ n), frobNorm (householderReflection (phi j) - householderReflection (vecFromBQ (v j))))
        _ ≤ ∑ j : Fin (2 ^ n), eps' := Finset.sum_le_sum fun j _ => hphi_frob j
        _ = (2 : ℝ) ^ n * eps' := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; rfl
        _ = eps := by
          dsimp [eps']
          rw [mul_div_cancel₀ eps (by positivity)]
    linarith [h_col, h_prod_le, h_sum_le]
  · dsimp [c_total, c_X_pad, c_chain]
    change ((padCircuit (cX n) ++ finChain c').length : ℝ) ≤ _
    rw [List.length_append]
    push_cast
    change ((padCircuit (cX n)).size : ℝ) + ((finChain c').size : ℝ) ≤ _
    rw [padCircuit_size, cX_size, finChain_size]
    push_cast
    have h_sum_le : (∑ j : Fin (2 ^ n), ((c' j).size : ℝ)) ≤
        (2 : ℝ) ^ n * (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1)) := by
      calc (∑ j : Fin (2 ^ n), ((c' j).size : ℝ))
        _ ≤ ∑ j : Fin (2 ^ n), (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1)) :=
          Finset.sum_le_sum fun j _ => hc'_size j
        _ = (2 : ℝ) ^ n * (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; rfl
    exact total_size_bound A₀ C hA₀ hC n m hn eps heps0 heps1 hm_bound (∑ j : Fin (2 ^ n), ((c' j).size : ℝ)) h_sum_le

/-! ### 11. Unitary group of circuits & Composition error bound -/

lemma hadamard_unitary : hadamardᴴ * hadamard = 1 := by
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    have : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      push_cast; rfl
    calc ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)
      _ = ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ := by ring
      _ = (2 : ℂ)⁻¹ := by rw [this]
      _ = 1 / 2 := by ring
  ext a b
  fin_cases a <;> fin_cases b <;>
  · simp [hadamard, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, h2]
    try ring

lemma gateT_unitary : gateTᴴ * gateT = 1 := by
  have h_norm : ‖Complex.exp (Complex.I * Real.pi / 4)‖ = 1 := by
    have h_eq : Complex.I * (Real.pi : ℂ) / 4 = Complex.I * (Real.pi / 4 : ℝ) := by
      push_cast
      ring
    rw [h_eq]
    exact Complex.norm_exp_I_mul_ofReal (Real.pi / 4)
  have h_exp : (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4)) *
      Complex.exp (Complex.I * Real.pi / 4) = 1 := by
    have hz : (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4)) *
        Complex.exp (Complex.I * Real.pi / 4) =
        ((‖Complex.exp (Complex.I * Real.pi / 4)‖ : ℂ) ^ 2) :=
      RCLike.conj_mul _
    rw [hz, h_norm]
    norm_num
  ext a b
  fin_cases a <;> fin_cases b <;>
  · simp [gateT, Matrix.mul_apply, Matrix.diagonal_apply, h_exp]

lemma cnot_unitary : cnotᴴ * cnot = 1 := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
  · simp [cnot, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type]

lemma Gate_ofMatrix1_unitary (M : Matrix Bool Bool ℂ) (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    Gate.IsUnitary (Gate.ofMatrix1 M) := by
  dsimp [Gate.IsUnitary, Gate.ofMatrix1]
  rw [Matrix.mem_unitaryGroup_iff']
  have h_mat : (M.submatrix (fun b => b 0) (fun b => b 0)) = M.submatrix qubits1Equiv qubits1Equiv := rfl
  rw [h_mat]
  have h_star : (star (M.submatrix qubits1Equiv qubits1Equiv) : Matrix (Qubits 1) (Qubits 1) ℂ) =
      (star M).submatrix qubits1Equiv qubits1Equiv := by
    ext a b; rfl
  rw [h_star, Matrix.submatrix_mul_equiv]
  have : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM
  rw [this]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.one_apply, qubits1Equiv.apply_eq_iff_eq]

def qubits2Equiv : Qubits 2 ≃ Bool × Bool where
  toFun b := (b 0, b 1)
  invFun p := fun i => if i.1 = 0 then p.1 else p.2
  left_inv b := by
    ext ⟨i, hi⟩
    interval_cases i <;> rfl
  right_inv p := by ext <;> rfl

lemma Gate_ofMatrix2_unitary (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Gate.IsUnitary (Gate.ofMatrix2 M) := by
  dsimp [Gate.IsUnitary, Gate.ofMatrix2]
  rw [Matrix.mem_unitaryGroup_iff']
  have h_mat : (M.submatrix (fun b => (b 0, b 1)) (fun b => (b 0, b 1))) =
      M.submatrix qubits2Equiv qubits2Equiv := rfl
  rw [h_mat]
  have h_star : (star (M.submatrix qubits2Equiv qubits2Equiv) : Matrix (Qubits 2) (Qubits 2) ℂ) =
      (star M).submatrix qubits2Equiv qubits2Equiv := by
    ext a b; rfl
  rw [h_star, Matrix.submatrix_mul_equiv]
  have : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM
  rw [this]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.one_apply, qubits2Equiv.apply_eq_iff_eq]

lemma htcxGateSet_unitary (g : Gate) (hg : g ∈ htcxGateSet) : Gate.IsUnitary g := by
  simp only [htcxGateSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact Gate_ofMatrix1_unitary hadamard (Matrix.mem_unitaryGroup_iff'.mpr hadamard_unitary)
  · exact Gate_ofMatrix1_unitary gateT (Matrix.mem_unitaryGroup_iff'.mpr gateT_unitary)
  · exact Gate_ofMatrix2_unitary cnot (Matrix.mem_unitaryGroup_iff'.mpr cnot_unitary)

noncomputable def wireEquiv {k n : ℕ} (w : Fin k ↪ Fin n) :
    Fin n ≃ Fin k ⊕ {a : Fin n // a ∉ Set.range w} :=
  (Equiv.sumCompl (fun a => a ∈ Set.range w)).symm.trans
    (((Equiv.ofInjective w w.injective).symm).sumCongr (Equiv.refl _))

noncomputable def qubitsSplitEquiv {k n : ℕ} (w : Fin k ↪ Fin n) :
    Qubits n ≃ Qubits k × ({a : Fin n // a ∉ Set.range w} → Bool) :=
  (Equiv.arrowCongr (wireEquiv w) (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

lemma qubitsSplitEquiv_comp_w {k n : ℕ} (w : Fin k ↪ Fin n)
    (u : Qubits k) (v : {a : Fin n // a ∉ Set.range w} → Bool) :
    (qubitsSplitEquiv w).symm (u, v) ∘ w = u := by
  ext i
  simp [qubitsSplitEquiv, wireEquiv]

lemma qubitsSplitEquiv_apply_not_range {k n : ℕ} (w : Fin k ↪ Fin n)
    (u : Qubits k) (v : {a : Fin n // a ∉ Set.range w} → Bool)
    (a : Fin n) (ha : a ∉ Set.range w) :
    (qubitsSplitEquiv w).symm (u, v) a = v ⟨a, ha⟩ := by
  simp [qubitsSplitEquiv, wireEquiv, ha]

lemma embedOp_one_aux {k n : ℕ} (w : Fin k ↪ Fin n) :
    embedOp (1 : Matrix (Qubits k) (Qubits k) ℂ) w = 1 := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz
    simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso
      apply hyz
      ext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨i, rfl⟩ := ha
        exact congr_fun h2 i
      · exact h1 a ha
    · rfl
    · rfl

lemma conjTranspose_embedOp_aux {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    (embedOp M w)ᴴ = embedOp Mᴴ w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.conjTranspose_apply]
  split_ifs with h1 h2 h3
  · rfl
  · exfalso; apply h2; intro a ha; rw [eq_comm]; exact h1 a ha
  · exfalso; apply h1; intro a ha; rw [eq_comm]; exact h3 a ha
  · simp

lemma embedOp_mul_aux {k n : ℕ} (M N : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp M w * embedOp N w = embedOp (M * N) w := by
  ext y z
  simp only [embedOp, Matrix.mul_apply, Matrix.of_apply]
  by_cases hyz : ∀ a ∉ Set.range w, y a = z a
  · rw [if_pos hyz]
    rw [← (qubitsSplitEquiv w).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    simp_rw [qubitsSplitEquiv_comp_w]
    have h_inner : ∀ u : Qubits k,
        (∑ v : {a // a ∉ Set.range w} → Bool,
          (if ∀ a ∉ Set.range w, y a = (qubitsSplitEquiv w).symm (u, v) a then M (y ∘ w) u else 0) *
          (if ∀ a ∉ Set.range w, (qubitsSplitEquiv w).symm (u, v) a = z a then N u (z ∘ w) else 0)) =
        M (y ∘ w) u * N u (z ∘ w) := by
      intro u
      let v₀ : {a // a ∉ Set.range w} → Bool := fun ⟨a, _⟩ => y a
      have hv₀_y : ∀ a (ha : a ∉ Set.range w), y a = (qubitsSplitEquiv w).symm (u, v₀) a := fun a ha => by
        rw [qubitsSplitEquiv_apply_not_range w u v₀ a ha]
      have hv₀_z : ∀ a (ha : a ∉ Set.range w), (qubitsSplitEquiv w).symm (u, v₀) a = z a := fun a ha => by
        rw [qubitsSplitEquiv_apply_not_range w u v₀ a ha]
        exact hyz a ha
      rw [Fintype.sum_eq_single v₀]
      · rw [if_pos hv₀_y, if_pos hv₀_z]
      · intro v hv
        have : ∃ a ha, y a ≠ v ⟨a, ha⟩ := by
          by_contra hc
          apply hv
          ext ⟨a, ha⟩
          by_contra h_eq
          exact hc ⟨a, ha, Ne.symm h_eq⟩
        rcases this with ⟨a, ha, hne⟩
        have h_cond : ¬ (∀ b ∉ Set.range w, y b = (qubitsSplitEquiv w).symm (u, v) b) := by
          intro hall
          have := hall a ha
          rw [qubitsSplitEquiv_apply_not_range w u v a ha] at this
          exact hne this
        by_cases h_y : ∀ b ∉ Set.range w, y b = (qubitsSplitEquiv w).symm (u, v) b
        · exfalso; exact h_cond h_y
        · rw [if_neg h_y, MulZeroClass.zero_mul]
    simp_rw [h_inner]
  · rw [if_neg hyz]
    have : ∃ a, a ∉ Set.range w ∧ y a ≠ z a := by
      by_contra hc
      apply hyz
      intro a ha
      by_contra hne
      exact hc ⟨a, ha, hne⟩
    rcases this with ⟨a, ha, hne⟩
    apply Finset.sum_eq_zero
    intro j _
    have h_not_both : ¬ ((∀ b ∉ Set.range w, y b = j b) ∧ (∀ b ∉ Set.range w, j b = z b)) := by
      rintro ⟨h1, h2⟩
      exact hne ((h1 a ha).trans (h2 a ha))
    by_cases h1 : ∀ b ∉ Set.range w, y b = j b
    · by_cases h2 : ∀ b ∉ Set.range w, j b = z b
      · exfalso; exact h_not_both ⟨h1, h2⟩
      · rw [if_neg h2, MulZeroClass.mul_zero]
    · rw [if_neg h1, MulZeroClass.zero_mul]

lemma embedOp_mem_unitaryGroup_aux {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n)
    (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, conjTranspose_embedOp_aux, embedOp_mul_aux]
  have : Mᴴ * M = (1 : Matrix (Qubits k) (Qubits k) ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hM
  rw [this, embedOp_one_aux]

lemma Circuit_unitary_mem_unitaryGroup_aux {n : ℕ} (c : Circuit htcxGateSet n) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  dsimp [Circuit.unitary]
  apply Submonoid.list_prod_mem
  intro x hx
  rw [List.mem_reverse, List.mem_map] at hx
  rcases hx with ⟨g, _, rfl⟩
  exact embedOp_mem_unitaryGroup_aux g.gate.mat g.wires (htcxGateSet_unitary g.gate g.mem)

lemma composition_algebraic_split (c₁ c₂ : Circuit htcxGateSet (1 + 2))
    (U₁ U₂ : Matrix (Qubits 1) (Qubits 1) ℂ) :
    initializedMap (c₁ ++ c₂).unitary - idealMap (U₂ * U₁) 2 =
    c₂.unitary * (initializedMap c₁.unitary - idealMap U₁ 2) +
    (initializedMap c₂.unitary - idealMap U₂ 2) * U₁ := by
  rw [circuit_unitary_append, initializedMap_mul, idealMap_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, mul_idealMap]
  abel

lemma circuit_composition_error_bound (c₁ c₂ : Circuit htcxGateSet (1 + 2))
    (U₁ U₂ : Matrix (Qubits 1) (Qubits 1) ℂ) (hU₁ : U₁ ∈ Matrix.unitaryGroup (Qubits 1) ℂ)
    (ε₁ ε₂ : ℝ)
    (h₁ : frobNorm (initializedMap c₁.unitary - idealMap U₁ 2) ≤ ε₁)
    (h₂ : frobNorm (initializedMap c₂.unitary - idealMap U₂ 2) ≤ ε₂) :
    frobNorm (initializedMap (c₁ ++ c₂).unitary - idealMap (U₂ * U₁) 2) ≤ ε₁ + ε₂ := by
  rw [composition_algebraic_split]
  calc frobNorm (c₂.unitary * (initializedMap c₁.unitary - idealMap U₁ 2) +
                 (initializedMap c₂.unitary - idealMap U₂ 2) * U₁)
    _ ≤ frobNorm (c₂.unitary * (initializedMap c₁.unitary - idealMap U₁ 2)) +
        frobNorm ((initializedMap c₂.unitary - idealMap U₂ 2) * U₁) := norm_add_le _ _
    _ = frobNorm (initializedMap c₁.unitary - idealMap U₁ 2) +
        frobNorm (initializedMap c₂.unitary - idealMap U₂ 2) := by
      rw [frobNorm_left_unitary_eq _ (Circuit_unitary_mem_unitaryGroup_aux c₂),
          frobNorm_right_unitary_eq _ hU₁]
    _ ≤ ε₁ + ε₂ := add_le_add h₁ h₂

/-! ### 12. Householder QR factorization for 1-qubit unitaries -/

def k0 : Qubits 1 := fun _ => false
def k1 : Qubits 1 := fun _ => true

lemma qubits1_cases (x : Qubits 1) : x = k0 ∨ x = k1 := by
  cases h : x 0 <;> [left; right] <;> ext i <;> fin_cases i <;> exact h

lemma k0_ne_k1 : k0 ≠ k1 := by
  intro h; have := congr_fun h 0; contradiction

noncomputable def qr_d0 (u0 : ℂ) : ℂ :=
  if u0 = 0 then 1 else -u0 / ((‖u0‖ : ℝ) : ℂ)

noncomputable def qr_psi (u0 u1 : ℂ) : EuclideanSpace ℂ (Qubits 1) :=
  let d0 := qr_d0 u0
  WithLp.toLp 2 fun x =>
    if x = k0 then
      ((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ)
    else
      -(star d0 * u1) / ((Real.sqrt (2 * (1 + ‖u0‖)) : ℝ) : ℂ)

lemma qr_d0_norm (u0 : ℂ) : ‖qr_d0 u0‖ = 1 := by
  dsimp [qr_d0]
  split_ifs with h
  · simp
  · simp [norm_neg, h]

lemma qr_psi_isState (u0 u1 : ℂ) (h_norm : ‖u0‖ ^ 2 + ‖u1‖ ^ 2 = 1) :
    IsState (qr_psi u0 u1) := by
  dsimp [IsState]
  have h_univ : (Finset.univ : Finset (Qubits 1)) = {k0, k1} := by
    ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact qubits1_cases x
  have h_not_mem : k0 ∉ ({k1} : Finset (Qubits 1)) := by simp [k0_ne_k1]
  have h_sum : ‖qr_psi u0 u1‖ ^ 2 = ‖qr_psi u0 u1 k0‖ ^ 2 + ‖qr_psi u0 u1 k1‖ ^ 2 := by
    have h_eq := EuclideanSpace.norm_sq_eq (qr_psi u0 u1)
    rw [h_univ, Finset.sum_insert h_not_mem, Finset.sum_singleton] at h_eq
    exact h_eq
  have hk0 : qr_psi u0 u1 k0 = ((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ) := rfl
  have hk1 : qr_psi u0 u1 k1 = -(star (qr_d0 u0) * u1) / ((Real.sqrt (2 * (1 + ‖u0‖)) : ℝ) : ℂ) := by
    dsimp [qr_psi]
    rw [if_neg k0_ne_k1.symm]
  have h1_pos : 0 ≤ (1 + ‖u0‖) / 2 := by linarith [norm_nonneg u0]
  have h2_pos : 0 ≤ 2 * (1 + ‖u0‖) := by linarith [norm_nonneg u0]
  have h_term0 : ‖(((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ))‖ ^ 2 = (1 + ‖u0‖) / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt h1_pos]
  have h_term1 : ‖-(star (qr_d0 u0) * u1) / ((Real.sqrt (2 * (1 + ‖u0‖)) : ℝ) : ℂ)‖ ^ 2 =
      ‖u1‖ ^ 2 / (2 * (1 + ‖u0‖)) := by
    rw [norm_div, norm_neg, norm_mul, norm_star, qr_d0_norm, one_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt h2_pos]
  have hu1_sq : ‖u1‖ ^ 2 = 1 - ‖u0‖ ^ 2 := by linarith
  have h_diff_sq : 1 - ‖u0‖ ^ 2 = (1 - ‖u0‖) * (1 + ‖u0‖) := by ring
  have h_pos_denom : 1 + ‖u0‖ ≠ 0 := by linarith [norm_nonneg u0]
  have h_cancel : (1 - ‖u0‖) * (1 + ‖u0‖) / (2 * (1 + ‖u0‖)) = (1 - ‖u0‖) / 2 :=
    mul_div_mul_right (1 - ‖u0‖) 2 h_pos_denom
  have h_sq : ‖qr_psi u0 u1‖ ^ 2 = 1 := by
    rw [h_sum, hk0, hk1, h_term0, h_term1, hu1_sq, h_diff_sq, h_cancel]
    ring
  have h_one_sq : (1 : ℝ) ^ 2 = 1 := by norm_num
  rw [← h_one_sq] at h_sq
  exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp h_sq

lemma sqrt_ratio (u0 : ℂ) :
    Real.sqrt ((1 + ‖u0‖) / 2) / Real.sqrt (2 * (1 + ‖u0‖)) = 1 / 2 := by
  have h1_pos : 0 ≤ 1 + ‖u0‖ := by linarith [norm_nonneg u0]
  have h_pos : Real.sqrt (1 + ‖u0‖) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    linarith [norm_nonneg u0]
  have h_split1 : Real.sqrt ((1 + ‖u0‖) / 2) = Real.sqrt (1 + ‖u0‖) / Real.sqrt 2 := by
    rw [Real.sqrt_div h1_pos]
  have h_split2 : Real.sqrt (2 * (1 + ‖u0‖)) = Real.sqrt 2 * Real.sqrt (1 + ‖u0‖) := by
    rw [Real.sqrt_mul (by norm_num)]
  rw [h_split1, h_split2]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc Real.sqrt (1 + ‖u0‖) / Real.sqrt 2 / (Real.sqrt 2 * Real.sqrt (1 + ‖u0‖))
    _ = (Real.sqrt (1 + ‖u0‖) / Real.sqrt (1 + ‖u0‖)) * (1 / (Real.sqrt 2 * Real.sqrt 2)) := by ring
    _ = 1 * (1 / 2) := by rw [div_self h_pos, h2]
    _ = 1 / 2 := by ring

lemma qr_psi_k0_k0 (u0 u1 : ℂ) :
    householderReflection (qr_psi u0 u1) k0 k0 = qr_d0 u0 * star u0 := by
  dsimp [householderReflection]
  have hk0 : qr_psi u0 u1 k0 = ((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ) := rfl
  rw [hk0]
  have h1_pos : 0 ≤ (1 + ‖u0‖) / 2 := by linarith [norm_nonneg u0]
  have h_conj : (starRingEnd ℂ) (((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ)) = (((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ)) :=
    Complex.conj_ofReal (Real.sqrt ((1 + ‖u0‖) / 2))
  rw [h_conj]
  have h_mul : (((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ)) * (((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ)) =
      ((((1 + ‖u0‖) / 2 : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul h1_pos, Real.sqrt_mul_self h1_pos]
  rw [mul_assoc (2 : ℂ), h_mul]
  have h_d0 : qr_d0 u0 * (starRingEnd ℂ) u0 = -((‖u0‖ : ℝ) : ℂ) := by
    dsimp [qr_d0]
    split_ifs with h
    · simp [h]
    · have h_norm_pos : ((‖u0‖ : ℝ) : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
      have h_mc : u0 * (starRingEnd ℂ) u0 = ((‖u0‖ : ℂ) ^ 2) := RCLike.mul_conj u0
      calc (-u0 / ((‖u0‖ : ℝ) : ℂ)) * (starRingEnd ℂ) u0
        _ = -(u0 * (starRingEnd ℂ) u0) / ((‖u0‖ : ℝ) : ℂ) := by ring
        _ = -((‖u0‖ : ℂ) ^ 2) / ((‖u0‖ : ℝ) : ℂ) := by rw [h_mc]
        _ = -(((‖u0‖ : ℝ) : ℂ) * ((‖u0‖ : ℝ) : ℂ)) / ((‖u0‖ : ℝ) : ℂ) := by ring
        _ = -((‖u0‖ : ℝ) : ℂ) := by
          rw [neg_mul_eq_neg_mul, mul_div_cancel_right₀ _ h_norm_pos]
  rw [h_d0]
  push_cast
  ring

lemma qr_psi_k0_k1 (u0 u1 : ℂ) :
    householderReflection (qr_psi u0 u1) k0 k1 = qr_d0 u0 * star u1 := by
  dsimp [householderReflection]
  have hk0 : qr_psi u0 u1 k0 = ((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ) := rfl
  have hk1 : qr_psi u0 u1 k1 = -(star (qr_d0 u0) * u1) / ((Real.sqrt (2 * (1 + ‖u0‖)) : ℝ) : ℂ) := by
    dsimp [qr_psi]
    rw [if_neg k0_ne_k1.symm]
  rw [hk0, hk1]
  have h_ne : (if k0 = k1 then (1 : ℂ) else 0) = 0 := if_neg k0_ne_k1
  rw [h_ne]
  simp only [zero_sub, map_div₀, map_neg, map_mul]
  have h_conj_star : (starRingEnd ℂ) (star (qr_d0 u0)) = qr_d0 u0 := RCLike.conj_conj (qr_d0 u0)
  rw [h_conj_star]
  have h_conj_sqrt : (starRingEnd ℂ) (((Real.sqrt (2 * (1 + ‖u0‖)) : ℝ) : ℂ)) =
      (((Real.sqrt (2 * (1 + ‖u0‖)) : ℝ) : ℂ)) :=
    Complex.conj_ofReal (Real.sqrt (2 * (1 + ‖u0‖)))
  rw [h_conj_sqrt]
  have h_sqrt_ratio := sqrt_ratio u0
  have h_ratio_c : (((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ)) / (((Real.sqrt (2 * (1 + ‖u0‖)) : ℝ) : ℂ)) =
      (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_div, h_sqrt_ratio]
    push_cast; rfl
  calc -(2 * (((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ)) * (-(qr_d0 u0 * (starRingEnd ℂ) u1) / (((Real.sqrt (2 * (1 + ‖u0‖)) : ℝ) : ℂ))))
    _ = 2 * ((((Real.sqrt ((1 + ‖u0‖) / 2) : ℝ) : ℂ)) / (((Real.sqrt (2 * (1 + ‖u0‖)) : ℝ) : ℂ))) * (qr_d0 u0 * (starRingEnd ℂ) u1) := by ring
    _ = 2 * (1 / 2 : ℂ) * (qr_d0 u0 * (starRingEnd ℂ) u1) := by rw [h_ratio_c]
    _ = qr_d0 u0 * (starRingEnd ℂ) u1 := by ring

lemma D_k0_k1_zero (U : Matrix (Qubits 1) (Qubits 1) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits 1) ℂ) :
    let psi := qr_psi (U k0 k0) (U k1 k0)
    (householderReflection psi * U) k0 k1 = 0 := by
  intro psi
  have h_mul : (householderReflection psi * U) k0 k1 =
      householderReflection psi k0 k0 * U k0 k1 + householderReflection psi k0 k1 * U k1 k1 := by
    change (∑ x, householderReflection psi k0 x * U x k1) = _
    rw [sum_qubits1]
    rfl
  rw [h_mul]
  rw [qr_psi_k0_k0, qr_psi_k0_k1]
  have h_ortho : star (U k0 k0) * U k0 k1 + star (U k1 k0) * U k1 k1 = 0 := by
    have hU_star : Uᴴ * U = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.mp hU
    have h01 : (Uᴴ * U) k0 k1 = 0 := by rw [hU_star]; rfl
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h01
    rw [sum_qubits1] at h01
    exact h01
  calc qr_d0 (U k0 k0) * star (U k0 k0) * U k0 k1 + qr_d0 (U k0 k0) * star (U k1 k0) * U k1 k1
    _ = qr_d0 (U k0 k0) * (star (U k0 k0) * U k0 k1 + star (U k1 k0) * U k1 k1) := by ring
    _ = qr_d0 (U k0 k0) * 0 := by rw [h_ortho]
    _ = 0 := mul_zero _

lemma unitary_diag_of_row0_col1_zero (D : Matrix (Qubits 1) (Qubits 1) ℂ)
    (hD : D ∈ Matrix.unitaryGroup (Qubits 1) ℂ) (h01 : D k0 k1 = 0) :
    ∀ x y, x ≠ y → D x y = 0 := by
  have h_mul : D * Dᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hD
  have h_col : Dᴴ * D = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hD
  have h_row0 : (D * Dᴴ) k0 k0 = 1 := by rw [h_mul]; rfl
  have h_col0 : (Dᴴ * D) k0 k0 = 1 := by rw [h_col]; rfl
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h_row0 h_col0
  rw [sum_qubits1] at h_row0 h_col0
  change D k0 k0 * star (D k0 k0) + D k0 k1 * star (D k0 k1) = 1 at h_row0
  change star (D k0 k0) * D k0 k0 + star (D k1 k0) * D k1 k0 = 1 at h_col0
  have hr0 : D k0 k0 * star (D k0 k0) = ((‖D k0 k0‖ : ℂ) ^ 2) := RCLike.mul_conj (D k0 k0)
  have hr1 : D k0 k1 * star (D k0 k1) = ((‖D k0 k1‖ : ℂ) ^ 2) := RCLike.mul_conj (D k0 k1)
  have hc1 : star (D k1 k0) * D k1 k0 = ((‖D k1 k0‖ : ℂ) ^ 2) := RCLike.conj_mul (D k1 k0)
  have hc0 : star (D k0 k0) * D k0 k0 = ((‖D k0 k0‖ : ℂ) ^ 2) := RCLike.conj_mul (D k0 k0)
  rw [hr0, hr1, h01, norm_zero, Complex.ofReal_zero] at h_row0
  have h_norm00 : ‖D k0 k0‖ ^ 2 = 1 := by
    have h02 : (0 : ℂ) ^ 2 = 0 := by ring
    rw [h02, add_zero] at h_row0
    exact_mod_cast h_row0
  rw [hc0, hc1] at h_col0
  have h_norm10 : ‖D k1 k0‖ ^ 2 = 0 := by
    have h_re := congrArg Complex.re h_col0
    rw [Complex.add_re, Complex.one_re] at h_re
    norm_cast at h_re
    linarith
  have h10_zero : D k1 k0 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h_norm10)
  intro x y hxy
  rcases qubits1_cases x with rfl | rfl <;> rcases qubits1_cases y with rfl | rfl
  · contradiction
  · exact h01
  · exact h10_zero
  · contradiction

lemma reflectionVector_eval_false_ne {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (h_diag : ∀ a b, a ≠ b → U a b = 0)
    (j : Qubits n) (x : Qubits n) (h : x ≠ j) :
    reflectionVector U j true (false, x) = 0 := by
  dsimp [reflectionVector, tensorVec, ket]
  simp [h_diag x j h]

lemma reflectionVector_diagonal_has_two_zero_coords
    (D : Matrix (Qubits 1) (Qubits 1) ℂ)
    (h_diag : ∀ x y, x ≠ y → D x y = 0)
    (j : Fin (2 ^ 1)) :
    ∃ j' l' : Qubits (1 + 1), j' ≠ l' ∧
      vecFromBQ (reflectionVector D ((bitsEquivFin 1).symm j) true) j' = 0 ∧
      vecFromBQ (reflectionVector D ((bitsEquivFin 1).symm j) true) l' = 0 := by
  have h_cases : (bitsEquivFin 1).symm j = k0 ∨ (bitsEquivFin 1).symm j = k1 :=
    qubits1_cases ((bitsEquivFin 1).symm j)
  let ql : Qubits 1 := if (bitsEquivFin 1).symm j = k0 then k1 else k0
  have h_ne : ql ≠ (bitsEquivFin 1).symm j := by
    dsimp [ql]
    rcases h_cases with hj | hj
    · rw [if_pos hj, hj]
      exact k0_ne_k1.symm
    · rw [if_neg (by rw [hj]; exact Ne.symm k0_ne_k1), hj]
      exact k0_ne_k1
  let j' : Qubits (1 + 1) := (equivBQ 1).symm (true, ql)
  let l' : Qubits (1 + 1) := (equivBQ 1).symm (false, ql)
  have hj'l' : j' ≠ l' := by
    intro h
    have h_eq := congrArg (equivBQ 1) h
    dsimp [j', l'] at h_eq
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h_eq
    have : (true : Bool) = false := congrArg Prod.fst h_eq
    exact Bool.noConfusion this
  refine ⟨j', l', hj'l', ?_, ?_⟩
  · dsimp [vecFromBQ, j']
    rw [Equiv.apply_symm_apply]
    exact reflectionVector_eval_true_ne D ((bitsEquivFin 1).symm j) ql h_ne
  · dsimp [vecFromBQ, l']
    rw [Equiv.apply_symm_apply]
    exact reflectionVector_eval_false_ne D h_diag ((bitsEquivFin 1).symm j) ql h_ne

/-! ### 13. 1-qubit reflection synthesis -/

lemma approximateSynthesis_1qubit_reflection (A₀ C : ℝ) (hA₀ : 0 < A₀) (_hC : 0 < C)
    (h_synth : ∀ n : ℕ, 1 ≤ n → ∀ kappa : ℕ,
      ∀ phi : EuclideanSpace ℂ (Qubits n), IsState phi →
        (∀ i, HasDenominator (Real.sqrt 2) kappa (phi i)) →
      ∃ w : ℕ, w ≤ 1 ∧ ∃ c : Circuit htcxGateSet (n + w),
        ImplementsWithCleanAncillas c.unitary (householderReflection phi) ∧
        (c.size : ℝ) ≤ A₀ * (2 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1))
    (h_approx : ∀ n : ℕ, 1 ≤ n →
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∃ m : ℕ, (n + 1) / 2 ≤ m ∧
        (m : ℝ) ≤ (((n + 1) / 2 : ℕ) : ℝ) +
          C * (1 + Real.log (1 / eps) / Real.log 2) ∧
      ∀ psi : EuclideanSpace ℂ (Qubits n), IsState psi →
        (∃ phi0 phi1 : EuclideanSpace ℂ (Bool × Qubits n),
          IsState phi0 ∧ IsState phi1 ∧
          (∀ z, HasDenominator 2 m (phi0 z)) ∧
          (∀ z, HasDenominator 2 m (phi1 z)) ∧
          frobNorm (householderReflection phi0 * householderReflection phi1 - identityExtension (householderReflection psi)) ≤ eps) ∧
        ((∃ j l : Qubits n, j ≠ l ∧ psi j = 0 ∧ psi l = 0) →
          ∃ phi : EuclideanSpace ℂ (Qubits n), IsState phi ∧
            (∀ z, HasDenominator 2 m (phi z)) ∧
            frobNorm (householderReflection phi - householderReflection psi) ≤ eps))
    (psi : EuclideanSpace ℂ (Qubits 1)) (hpsi : IsState psi)
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c_R : Circuit htcxGateSet (1 + 2),
      frobNorm (initializedMap c_R.unitary - idealMap (householderReflection psi) 2) ≤ eps ∧
      (c_R.size : ℝ) ≤ 32 * A₀ * (2 * (1 + C * (1 + Real.log (1 / eps) / Real.log 2)) + 1) := by
  rcases h_approx 1 (by norm_num) eps heps0 heps1 with ⟨m, hm_ge, hm_bound, h_psi⟩
  rcases (h_psi psi hpsi).1 with ⟨phi0, phi1, hphi0_st, hphi1_st, hphi0_d, hphi1_d, h_frob⟩
  let v0 := vecFromBQ phi0
  let v1 := vecFromBQ phi1
  have hv0_st : IsState v0 := vecFromBQ_isState hphi0_st
  have hv1_st : IsState v1 := vecFromBQ_isState hphi1_st
  have hv0_d : ∀ z, HasDenominator (Real.sqrt 2) (2 * m) (v0 z) := fun z => hasDenominator_sqrt2_of_two (hphi0_d _)
  have hv1_d : ∀ z, HasDenominator (Real.sqrt 2) (2 * m) (v1 z) := fun z => hasDenominator_sqrt2_of_two (hphi1_d _)
  rcases h_synth 2 (by norm_num) (2 * m) v0 hv0_st hv0_d with ⟨w0, hw0, c0, hc0, h_sz0⟩
  rcases h_synth 2 (by norm_num) (2 * m) v1 hv1_st hv1_d with ⟨w1, hw1, c1, hc1, h_sz1⟩
  rcases normalize_clean_ancilla (householderReflection v0) w0 hw0 c0 hc0 with ⟨c'0, hc'0, h_sz0_eq⟩
  rcases normalize_clean_ancilla (householderReflection v1) w1 hw1 c1 hc1 with ⟨c'1, hc'1, h_sz1_eq⟩
  let c_R : Circuit htcxGateSet (1 + 2) := c'1 ++ c'0
  refine ⟨c_R, ?_, ?_⟩
  · let Δ : Matrix (Bool × Qubits 1) (Bool × Qubits 1) ℂ :=
      householderReflection phi0 * householderReflection phi1 - identityExtension (householderReflection psi)
    have hM_eq (y : Qubits (1 + 2)) (x : Qubits 1) :
        (@initializedMap 1 2 c_R.unitary - idealMap (householderReflection psi) 2) y x =
          (zeroAncillaVec (act (matFromBQ Δ) (ket (emb_false 1 x))) 1) y := by
      have h1_init : @initializedMap 1 2 c_R.unitary y x =
          (zeroAncillaVec (act (matFromBQ (householderReflection phi0 * householderReflection phi1)) (ket (emb_false 1 x))) 1) y := by
        rw [initializedMap_apply]
        dsimp [c_R]
        rw [circuit_unitary_append, act_mul, zeroAncillaVec_two]
        have h_ket : zeroAncillaVec (ket x) 1 = ket (emb_false 1 x) := by
          rw [← vecFromBQ_tensor_ket_false_ket, vecFromBQ_tensor_ket_false]
        rw [h_ket]
        have h1 : act c'1.unitary (zeroAncillaVec (ket (emb_false 1 x)) 1) =
            zeroAncillaVec (act (householderReflection v1) (ket (emb_false 1 x))) 1 := hc'1 _
        rw [h1]
        have h0 : act c'0.unitary (zeroAncillaVec (act (householderReflection v1) (ket (emb_false 1 x))) 1) =
            zeroAncillaVec (act (householderReflection v0) (act (householderReflection v1) (ket (emb_false 1 x)))) 1 := hc'0 _
        rw [h0, ← act_mul]
        have h_prod : householderReflection v0 * householderReflection v1 =
            matFromBQ (householderReflection phi0 * householderReflection phi1) := by
          rw [matFromBQ_mul, matFromBQ_refl, matFromBQ_refl]
        rw [h_prod]
      have h2_ideal : idealMap (householderReflection psi) 2 y x =
          (zeroAncillaVec (act (matFromBQ (identityExtension (householderReflection psi))) (ket (emb_false 1 x))) 1) y := by
        rw [idealMap_apply, zeroAncillaVec_two]
        have h_ket : ket (emb_false 1 x) = zeroAncillaVec (ket x) 1 := by
          rw [← vecFromBQ_tensor_ket_false_ket, vecFromBQ_tensor_ket_false]
        rw [h_ket, act_matFromBQ_identityExtension]
      calc (@initializedMap 1 2 c_R.unitary - idealMap (householderReflection psi) 2) y x
        _ = @initializedMap 1 2 c_R.unitary y x - idealMap (householderReflection psi) 2 y x := rfl
        _ = (zeroAncillaVec (act (matFromBQ (householderReflection phi0 * householderReflection phi1)) (ket (emb_false 1 x))) 1) y -
            (zeroAncillaVec (act (matFromBQ (identityExtension (householderReflection psi))) (ket (emb_false 1 x))) 1) y := by
          rw [h1_init, h2_ideal]
        _ = (zeroAncillaVec (act (matFromBQ Δ) (ket (emb_false 1 x))) 1) y := by
          rw [zeroAncillaVec_act_sub]
          dsimp [Δ]
          rw [matFromBQ_sub]
    have h_col := frobNorm_zeroAncillaVec_col_false_le (@initializedMap 1 2 c_R.unitary - idealMap (householderReflection psi) 2) (matFromBQ Δ) hM_eq
    have h_submat : frobNorm (matFromBQ Δ) = frobNorm Δ := frobNorm_matFromBQ Δ
    rw [h_submat] at h_col
    exact le_trans h_col h_frob
  · dsimp [c_R, Circuit.size]
    rw [List.length_append, Nat.cast_add]
    have hc'1_len : c'1.length = c1.length := h_sz1_eq
    have hc'0_len : c'0.length = c0.length := h_sz0_eq
    rw [hc'1_len, hc'0_len]
    change (c1.size : ℝ) + (c0.size : ℝ) ≤ _
    have hm1 : (((1 + 1) / 2 : ℕ) : ℝ) = 1 := by norm_num
    rw [hm1] at hm_bound
    have h_sz0_le : (c0.size : ℝ) ≤ A₀ * 8 * (2 * (1 + C * (1 + Real.log (1 / eps) / Real.log 2)) + 1) := by
      calc (c0.size : ℝ) ≤ A₀ * (2 : ℝ) ^ 2 * (2 : ℝ) * (((2 * m : ℕ) : ℝ) + 1) := h_sz0
        _ = A₀ * 8 * (2 * (m : ℝ) + 1) := by push_cast; ring
        _ ≤ A₀ * 8 * (2 * (1 + C * (1 + Real.log (1 / eps) / Real.log 2)) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hm_bound]
    have h_sz1_le : (c1.size : ℝ) ≤ A₀ * 8 * (2 * (1 + C * (1 + Real.log (1 / eps) / Real.log 2)) + 1) := by
      calc (c1.size : ℝ) ≤ A₀ * (2 : ℝ) ^ 2 * (2 : ℝ) * (((2 * m : ℕ) : ℝ) + 1) := h_sz1
        _ = A₀ * 8 * (2 * (m : ℝ) + 1) := by push_cast; ring
        _ ≤ A₀ * 8 * (2 * (1 + C * (1 + Real.log (1 / eps) / Real.log 2)) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hm_bound]
    linarith

/-! ### 14. Top-level approximate synthesis theorem -/

theorem solution :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ U : Matrix (Qubits n) (Qubits n) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits n) ℂ →
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∃ w : ℕ, w ≤ 2 ∧ ∃ c : Circuit htcxGateSet (n + w),
        frobNorm (initializedMap c.unitary - idealMap U w) ≤ eps ∧
        (c.size : ℝ) ≤ A * (4 : ℝ) ^ n * (n : ℝ) *
          (Real.log (1 / eps) / Real.log 2 + (n : ℝ)) := by
  rcases exactReflectionSynthesis with ⟨A₀, hA₀, h_synth⟩
  rcases reflectionApproximation with ⟨C, hC, h_approx⟩
  let A : ℝ := 1024 * (C + 2) * A₀ + 64
  have hA : 0 < A := by positivity
  refine ⟨A, hA, fun n hn U hU eps heps0 heps1 => ?_⟩
  by_cases hn2 : 2 ≤ n
  · rcases approximateSynthesis_of_two_zeros A₀ C hA₀ hC h_synth h_approx n hn U hU
      (fun j => reflectionVector_has_two_zero_coords hn2 U ((bitsEquivFin n).symm j)) eps heps0 heps1 with ⟨c, h_frob, h_size⟩
    refine ⟨2, le_refl 2, c, h_frob, ?_⟩
    refine le_trans h_size ?_
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      dsimp [A]
      have : 0 ≤ (C + 2) * A₀ := by positivity
      linarith
    · have hlog_nonneg : 0 ≤ Real.log (1 / eps) := Real.log_nonneg (one_le_one_div heps0 heps1)
      have hlog2_pos : 0 < Real.log 2 := by positivity
      positivity
  · have hn1 : n = 1 := by omega
    subst hn1
    have hU_star : Uᴴ * U = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.mp hU
    have h00 : (Uᴴ * U) k0 k0 = 1 := by rw [hU_star]; rfl
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h00
    rw [sum_qubits1] at h00
    change star (U k0 k0) * U k0 k0 + star (U k1 k0) * U k1 k0 = 1 at h00
    have hc0 : star (U k0 k0) * U k0 k0 = ((‖U k0 k0‖ : ℂ) ^ 2) := RCLike.conj_mul (U k0 k0)
    have hc1 : star (U k1 k0) * U k1 k0 = ((‖U k1 k0‖ : ℂ) ^ 2) := RCLike.conj_mul (U k1 k0)
    rw [hc0, hc1] at h00
    have h_norm : ‖U k0 k0‖ ^ 2 + ‖U k1 k0‖ ^ 2 = 1 := by
      have h_re := congrArg Complex.re h00
      rw [Complex.add_re, Complex.one_re] at h_re
      norm_cast at h_re
    let psi := qr_psi (U k0 k0) (U k1 k0)
    have hpsi : IsState psi := qr_psi_isState (U k0 k0) (U k1 k0) h_norm
    let R := householderReflection psi
    have hR : R ∈ Matrix.unitaryGroup (Qubits 1) ℂ := householderReflection_is_unitary psi hpsi
    let D := R * U
    have hD : D ∈ Matrix.unitaryGroup (Qubits 1) ℂ := mul_mem hR hU
    have h01 : D k0 k1 = 0 := D_k0_k1_zero U hU
    have h_diag : ∀ x y, x ≠ y → D x y = 0 := unitary_diag_of_row0_col1_zero D hD h01
    have h_two_zero := reflectionVector_diagonal_has_two_zero_coords D h_diag
    set eps' : ℝ := eps / 2
    have heps'_pos : 0 < eps' := by positivity
    have heps'_le : eps' ≤ 1 := by dsimp [eps']; linarith [heps0, heps1]
    rcases approximateSynthesis_of_two_zeros A₀ C hA₀ hC h_synth h_approx 1 (by norm_num) D hD
      h_two_zero eps' heps'_pos heps'_le with ⟨c_D, hc_D_frob, hc_D_size⟩
    rcases approximateSynthesis_1qubit_reflection A₀ C hA₀ hC h_synth h_approx psi hpsi
      eps' heps'_pos heps'_le with ⟨c_R, hc_R_frob, hc_R_size⟩
    refine ⟨2, le_refl 2, c_D ++ c_R, ?_, ?_⟩
    · have h_comp := circuit_composition_error_bound c_D c_R D R hD eps' eps' hc_D_frob hc_R_frob
      have hRD : R * D = U := by
        dsimp [D]
        rw [← Matrix.mul_assoc, householderReflection_mul_self psi hpsi, Matrix.one_mul]
      rw [hRD] at h_comp
      have h_sum : eps' + eps' = eps := by dsimp [eps']; ring
      rw [h_sum] at h_comp
      exact h_comp
    · rw [Circuit.size, List.length_append, Nat.cast_add]
      have hlog_nonneg : 0 ≤ Real.log (1 / eps) := Real.log_nonneg (one_le_one_div heps0 heps1)
      have hlog2_pos : 0 < Real.log 2 := by positivity
      have hL_nonneg : 0 ≤ Real.log (1 / eps) / Real.log 2 := div_nonneg hlog_nonneg (le_of_lt hlog2_pos)
      have h_log_eps' : Real.log (1 / eps') / Real.log 2 = Real.log (1 / eps) / Real.log 2 + 1 := by
        dsimp [eps']
        have h_div : 1 / (eps / 2) = (1 / eps) * 2 := by ring
        rw [h_div, Real.log_mul (by positivity) (by norm_num)]
        rw [add_div, div_self (ne_of_gt hlog2_pos)]
      rw [h_log_eps'] at hc_D_size hc_R_size
      have h_cD : (c_D.size : ℝ) ≤ (16 * (C + 2) * A₀ + 6) * 4 * (Real.log (1 / eps) / Real.log 2 + 2) := by
        refine le_trans hc_D_size ?_
        push_cast; linarith
      have h_cR : (c_R.size : ℝ) ≤ 32 * A₀ * (2 * (1 + C * (Real.log (1 / eps) / Real.log 2 + 2)) + 1) := by
        refine le_trans hc_R_size ?_
        linarith
      have h_L2 : Real.log (1 / eps) / Real.log 2 + 2 ≤ 2 * (Real.log (1 / eps) / Real.log 2 + 1) := by linarith
      have h1 : (c_D.size : ℝ) ≤ (16 * (C + 2) * A₀ + 6) * 4 * (2 * (Real.log (1 / eps) / Real.log 2 + 1)) := by
        refine le_trans h_cD ?_
        refine mul_le_mul_of_nonneg_left h_L2 (by positivity)
      have h2 : (c_R.size : ℝ) ≤ 32 * A₀ * (2 * (1 + C * (2 * (Real.log (1 / eps) / Real.log 2 + 1))) + 1) := by
        refine le_trans h_cR ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [hC, h_L2]
      have h_sum_le : (c_D.size : ℝ) + (c_R.size : ℝ) ≤
          (16 * (C + 2) * A₀ + 6) * 4 * (2 * (Real.log (1 / eps) / Real.log 2 + 1)) +
          32 * A₀ * (2 * (1 + C * (2 * (Real.log (1 / eps) / Real.log 2 + 1))) + 1) := add_le_add h1 h2
      refine le_trans h_sum_le ?_
      dsimp [A]
      push_cast
      have : 0 ≤ Real.log (1 / eps) / Real.log 2 + 1 := by linarith
      have : 0 ≤ (C + 2) * A₀ := by positivity
      have : 0 ≤ C * A₀ := by positivity
      have : 0 ≤ A₀ := le_of_lt hA₀
      nlinarith


end
