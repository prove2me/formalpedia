-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P12.exactSynthesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T04:33:16.748134+00:00
-- url     : https://prove2.me/submissions/1a09ae49-92fc-47bc-9991-9f3c17d66206
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_reflectionDecomposition
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P12_exactReflectionSynthesis
import Mathlib.Analysis.Complex.Trigonometric

open scoped BigOperators Matrix
open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12

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

/-! ### 5. Two-ancilla decomposition -/

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

/-! ### 6. Ordered product of circuits -/

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

/-! ### 7. Arithmetic size bound -/

lemma total_size_bound (A₀ : ℝ) (hA₀ : 0 < A₀) (n kappa : ℕ) (hn : 1 ≤ n)
    (S : ℝ) (hS : S ≤ (2 : ℝ) ^ n * (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((kappa + 1 : ℕ) : ℝ) + 1))) :
    (6 : ℝ) + S ≤ (8 * A₀ + 6) * (4 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1) := by
  have h_n_ge : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast; linarith [h_n_ge]
  have hk1 : (((kappa + 1 : ℕ) : ℝ) + 1) ≤ 2 * ((kappa : ℝ) + 1) := by
    push_cast; linarith
  have h2pow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
    rw [pow_succ, mul_comm]
  have h4pow : (2 : ℝ) ^ n * (2 : ℝ) ^ n = (4 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have h4_ge_one : 1 ≤ (4 : ℝ) ^ n := by
    have : (1 : ℝ) = (1 : ℝ) ^ n := by simp
    rw [this]
    refine pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h_k_ge : 1 ≤ (kappa : ℝ) + 1 := by linarith [show 0 ≤ (kappa : ℝ) by positivity]
  have h_one_le : 1 ≤ (4 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1) := by
    have : 1 ≤ (4 : ℝ) ^ n * (n : ℝ) := by nlinarith [h4_ge_one, h_n_ge]
    nlinarith [this, h_k_ge]
  have hS_bound : S ≤ 8 * A₀ * (4 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1) := by
    calc
      S ≤ (2 : ℝ) ^ n * (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((kappa + 1 : ℕ) : ℝ) + 1)) := hS
      _ = A₀ * ((2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)) * ((n + 1 : ℕ) : ℝ) * (((kappa + 1 : ℕ) : ℝ) + 1) := by ring
      _ = A₀ * (2 * ((2 : ℝ) ^ n * (2 : ℝ) ^ n)) * ((n + 1 : ℕ) : ℝ) * (((kappa + 1 : ℕ) : ℝ) + 1) := by rw [h2pow]; ring
      _ = 2 * A₀ * (4 : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) * (((kappa + 1 : ℕ) : ℝ) + 1) := by rw [h4pow]; ring
      _ ≤ 2 * A₀ * (4 : ℝ) ^ n * (2 * (n : ℝ)) * (2 * ((kappa : ℝ) + 1)) := by
        refine mul_le_mul (mul_le_mul (by linarith) hn1 (by positivity) (by positivity)) hk1 (by positivity) (by positivity)
      _ = 8 * A₀ * (4 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1) := by ring
  calc
    (6 : ℝ) + S ≤ 6 * ((4 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1)) + 8 * A₀ * (4 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1) := by
      linarith [h_one_le, hS_bound]
    _ = (8 * A₀ + 6) * (4 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1) := by ring

/-! ### 8. Main Solution -/

theorem solution :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n → ∀ kappa : ℕ,
      ∀ U : Matrix (Qubits n) (Qubits n) ℂ,
        U ∈ Matrix.unitaryGroup (Qubits n) ℂ →
        (∀ i j, HasDenominator (Real.sqrt 2) kappa (U i j)) →
      ∃ w : ℕ, w ≤ 2 ∧ ∃ c : Circuit htcxGateSet (n + w),
        ImplementsWithCleanAncillas c.unitary U ∧
        (c.size : ℝ) ≤ A * (4 : ℝ) ^ n * (n : ℝ) * ((kappa : ℝ) + 1) := by
  rcases exactReflectionSynthesis with ⟨A₀, hA₀, h_synth⟩
  refine ⟨8 * A₀ + 6, by positivity, ?_⟩
  intro n hn kappa U hU h_denom
  rcases reflectionDecomposition n U hU with ⟨-, -, hv_state, h_prod, hv_denom⟩
  let v : Fin (2 ^ n) → EuclideanSpace ℂ (Bool × Qubits n) :=
    fun j => reflectionVector U ((bitsEquivFin n).symm j) true
  have hv_state' (j : Fin (2 ^ n)) : IsState (v j) := hv_state ((bitsEquivFin n).symm j) true
  have hv_denom' (j : Fin (2 ^ n)) : ∀ z, HasDenominator (Real.sqrt 2) (kappa + 1) (v j z) :=
    hv_denom kappa h_denom ((bitsEquivFin n).symm j) true
  have h_synth_step (j : Fin (2 ^ n)) :
      ∃ c' : Circuit htcxGateSet ((n + 1) + 1),
        ImplementsWithCleanAncillas c'.unitary (matFromBQ (householderReflection (v j))) ∧
        (c'.size : ℝ) ≤ A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((kappa + 1 : ℕ) : ℝ) + 1) := by
    have hvj_state : IsState (vecFromBQ (v j)) := vecFromBQ_isState (hv_state' j)
    have hvj_denom : ∀ z, HasDenominator (Real.sqrt 2) (kappa + 1) (vecFromBQ (v j) z) :=
      vecFromBQ_denom (hv_denom' j)
    rcases h_synth (n + 1) (by omega) (kappa + 1) (vecFromBQ (v j)) hvj_state hvj_denom with ⟨w_j, hw_j, c_j, hc_j, h_size_j⟩
    rw [← matFromBQ_refl] at hc_j
    rcases normalize_clean_ancilla (matFromBQ (householderReflection (v j))) w_j hw_j c_j hc_j with ⟨c'_j, hc'_j, h_size_eq⟩
    refine ⟨c'_j, hc'_j, ?_⟩
    rw [h_size_eq]
    exact h_size_j
  choose c' hc'_imp hc'_size using h_synth_step
  refine ⟨2, le_refl 2, ?_⟩
  have h_rfl : (n + 1) + 1 = n + 2 := rfl
  let c_chain : Circuit htcxGateSet (n + 2) := finChain c'
  let c_X_pad : Circuit htcxGateSet (n + 2) := padCircuit (cX n)
  let c_total : Circuit htcxGateSet (n + 2) := c_X_pad ++ c_chain
  refine ⟨c_total, ?_, ?_⟩
  · intro ψ
    rw [circuit_unitary_append, act_mul]
    rw [zeroAncillaVec_two]
    have h_X : act c_X_pad.unitary (zeroAncillaVec (zeroAncillaVec ψ 1) 1) =
        zeroAncillaVec (vecFromBQ (tensorVec (ket true) ψ)) 1 := by
      dsimp [c_X_pad]
      rw [act_padCircuit, act_cX_zeroAncillaVec]
    rw [h_X]
    have h_chain : act c_chain.unitary (zeroAncillaVec (vecFromBQ (tensorVec (ket true) ψ)) 1) =
        zeroAncillaVec (act (orderedProd (fun j => matFromBQ (householderReflection (v j))))
          (vecFromBQ (tensorVec (ket true) ψ))) 1 := by
      exact implements_finChain (fun j => matFromBQ (householderReflection (v j))) c' hc'_imp _
    rw [h_chain]
    rw [← matFromBQ_orderedProd, ← h_prod]
    rw [act_matFromBQ, act_dil]
    rw [vecFromBQ_tensor_ket_false]
    rw [← zeroAncillaVec_two]
  · dsimp [c_total, c_X_pad, c_chain]
    change ((padCircuit (cX n) ++ finChain c').length : ℝ) ≤ _
    rw [List.length_append]
    push_cast
    change ((padCircuit (cX n)).size : ℝ) + ((finChain c').size : ℝ) ≤ _
    rw [padCircuit_size, cX_size, finChain_size]
    push_cast
    have h_sum_le : (∑ j : Fin (2 ^ n), ((c' j).size : ℝ)) ≤
        (2 : ℝ) ^ n * (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((kappa + 1 : ℕ) : ℝ) + 1)) := by
      calc
        (∑ j : Fin (2 ^ n), ((c' j).size : ℝ)) ≤
            ∑ j : Fin (2 ^ n), (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((kappa + 1 : ℕ) : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun j _ => hc'_size j
        _ = (2 : ℝ) ^ n * (A₀ * (2 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) * (((kappa + 1 : ℕ) : ℝ) + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          rfl
    exact total_size_bound A₀ hA₀ n kappa hn (∑ j : Fin (2 ^ n), ((c' j).size : ℝ)) h_sum_le
