-- Prove2me | solution 1 for QAlgorithms.Nannicini.densityMatrix_blockEncoding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:16:42.172732+00:00
-- url     : https://prove2.me/submissions/0cf801f9-04eb-4036-a6c7-b8ce4d0869b5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch07b_Model
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases

/-!
The prepare–swap–unprepare construction of Nannicini, Lemma 7.39, and
Gilyén–Su–Low–Wiebe, Lemma 45 (arXiv:1806.01838). Registers are ordered as
system, purifier, output. All circuit gates and wire placements are fixed before the oracle.
-/

set_option autoImplicit false
open QAlgorithms
open scoped Matrix.Norms.L2Operator

private def permMat {ι : Type*} [DecidableEq ι] (e : ι ≃ ι) : Matrix ι ι ℂ :=
  (1 : Matrix ι ι ℂ).submatrix e id

private lemma permMat_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (e f : ι ≃ ι) :
    permMat e * permMat f = permMat (e.trans f) := by
  ext x z
  simp only [permMat, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply,
    id_eq, ite_mul, one_mul, zero_mul]
  simp
  rfl

private lemma permMat_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) :
    permMat e ∈ Matrix.unitaryGroup ι ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change (1 : Matrix ι ι ℂ).submatrix e (Equiv.refl ι) *
    ((1 : Matrix ι ι ℂ).submatrix e (Equiv.refl ι)).conjTranspose = 1
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    Matrix.submatrix_mul_equiv, one_mul, Matrix.submatrix_one_equiv e]

private lemma reindex_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e :=
  (Matrix.submatrix_mul_equiv A B e e e).symm

private lemma permMat_reindex {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (f : ι ≃ ι) (e : κ ≃ ι) :
    (permMat f).submatrix e e = permMat ((e.trans f).trans e.symm) := by
  ext x y
  simp [permMat,Matrix.one_apply,Equiv.symm_apply_eq]

private def bitSwap {n : ℕ} (i j : Fin n) : Qubits n ≃ Qubits n where
  toFun x := x ∘ Equiv.swap i j
  invFun x := x ∘ Equiv.swap i j
  left_inv x := by funext k; simp
  right_inv x := by funext k; simp

private def swGate : Gate := ⟨2, permMat (bitSwap 0 1)⟩

private lemma swGate_mem : swGate ∈ twoQubitGateSet :=
  ⟨rfl, permMat_unitary _⟩

private lemma embed_swap {n : ℕ} (w : Fin 2 ↪ Fin n) :
    embedOp swGate.mat w = permMat (bitSwap (w 0) (w 1)) := by
  classical
  ext x y
  have hw : w 0 ≠ w 1 := w.injective.ne (by decide)
  have hiff : (∀ k, k ∉ Set.range w → x k = y k) ∧
      (x ∘ w) ∘ Equiv.swap 0 1 = y ∘ w ↔
      x ∘ Equiv.swap (w 0) (w 1) = y := by
    constructor
    · rintro ⟨h,h'⟩
      funext k
      by_cases h0 : k = w 0
      · subst k; simpa [Function.comp_def] using congrFun h' 0
      by_cases h1 : k = w 1
      · subst k; simpa [Function.comp_def] using congrFun h' 1
      · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1]
        apply h
        rintro ⟨i,rfl⟩
        fin_cases i <;> simp_all
    · intro h
      constructor
      · intro k hk
        have h0 : k ≠ w 0 := fun hh => hk ⟨0,hh.symm⟩
        have h1 : k ≠ w 1 := fun hh => hk ⟨1,hh.symm⟩
        simpa [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1] using congrFun h k
      · funext i
        fin_cases i
        · simpa [Function.comp_def] using congrFun h (w 0)
        · simpa [Function.comp_def] using congrFun h (w 1)
  change (if ∀ k, k ∉ Set.range w → x k = y k then
    if (x ∘ w) ∘ Equiv.swap 0 1 = y ∘ w then (1 : ℂ) else 0 else 0) =
      if x ∘ Equiv.swap (w 0) (w 1) = y then 1 else 0
  simp only [← ite_and, hiff]

private def leftWire (q a : ℕ) (i : Fin q) : Fin ((q+a)+q) :=
  Fin.castAdd q (Fin.castAdd a i)
private def rightWire (q a : ℕ) (i : Fin q) : Fin ((q+a)+q) :=
  Fin.natAdd (q+a) i
private def swapWires (q a : ℕ) (i : Fin q) : Fin 2 ↪ Fin ((q+a)+q) where
  toFun j := if j = 0 then leftWire q a i else rightWire q a i
  inj' := by
    intro j k h
    fin_cases j <;> fin_cases k
    all_goals first | rfl | skip
    all_goals have hh := congrArg Fin.val h
    all_goals norm_num [leftWire, rightWire] at hh
    all_goals omega

private def swapApp (q a : ℕ) (i : Fin q) : GateApp twoQubitGateSet ((q+a)+q) :=
  ⟨swGate, swGate_mem, swapWires q a i⟩

private def triple (q a : ℕ) : Qubits ((q+a)+q) ≃ ((Qubits q × Qubits a) × Qubits q) :=
  (qubitsAppendEquiv (q+a) q).trans
    ((qubitsAppendEquiv q a).prodCongr (Equiv.refl _))

-- Swapping a subset of coordinate pairs makes the finite gate-product induction explicit.
private def partialSwap {q a : ℕ} (s : Finset (Fin q)) :
    ((Qubits q × Qubits a) × Qubits q) ≃ ((Qubits q × Qubits a) × Qubits q) where
  toFun x := ((fun i => if i ∈ s then x.2 i else x.1.1 i, x.1.2),
    fun i => if i ∈ s then x.1.1 i else x.2 i)
  invFun x := ((fun i => if i ∈ s then x.2 i else x.1.1 i, x.1.2),
    fun i => if i ∈ s then x.1.1 i else x.2 i)
  left_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · funext i; dsimp; split_ifs <;> rfl
      · rfl
    · funext i; dsimp; split_ifs <;> rfl
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · funext i; dsimp; split_ifs <;> rfl
      · rfl
    · funext i; dsimp; split_ifs <;> rfl

private lemma bitSwap_triple (q a : ℕ) (i : Fin q) (x : Qubits ((q+a)+q)) :
    triple q a (bitSwap (leftWire q a i) (rightWire q a i) x) =
      partialSwap {i} (triple q a x) := by
  have hne : leftWire q a i ≠ rightWire q a i := by
    intro h; have := congrArg Fin.val h; dsimp [leftWire,rightWire] at this; omega
  apply Prod.ext
  · apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j; simp [triple, qubitsAppendEquiv, bitSwap, partialSwap, leftWire, rightWire]
      · change x (Equiv.swap (leftWire q a i) (rightWire q a i) (leftWire q a j)) = _
        have h0 : leftWire q a j ≠ leftWire q a i := by
          simpa [leftWire] using hj
        have h1 : leftWire q a j ≠ rightWire q a i := by
          intro h; have := congrArg Fin.val h; dsimp [leftWire,rightWire] at this; omega
        rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
        simp [partialSwap,hj,triple,qubitsAppendEquiv,leftWire]
    · funext j
      change x (Equiv.swap (leftWire q a i) (rightWire q a i)
        (Fin.castAdd q (Fin.natAdd q j))) = x (Fin.castAdd q (Fin.natAdd q j))
      rw [Equiv.swap_apply_of_ne_of_ne]
      · intro h; have := congrArg Fin.val h; dsimp [leftWire] at this; omega
      · intro h; have := congrArg Fin.val h; dsimp [rightWire] at this; omega
  · funext j
    by_cases hj : j = i
    · subst j; simp [triple, qubitsAppendEquiv, bitSwap, partialSwap, leftWire, rightWire]
    · change x (Equiv.swap (leftWire q a i) (rightWire q a i) (rightWire q a j)) = _
      have h0 : rightWire q a j ≠ leftWire q a i := by
        intro h; have := congrArg Fin.val h; dsimp [leftWire,rightWire] at this; omega
      have h1 : rightWire q a j ≠ rightWire q a i := by
        simpa [rightWire] using hj
      rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
      simp [partialSwap,hj,triple,qubitsAppendEquiv,rightWire]

private lemma partialSwap_insert {q a : ℕ} (s : Finset (Fin q)) (i : Fin q)
    (hi : i ∉ s) :
    (partialSwap (a := a) s).trans (partialSwap {i}) = partialSwap (insert i s) := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j; simp [partialSwap,hi]
      · simp [partialSwap,hj]
    · rfl
  · funext j
    by_cases hj : j = i
    · subst j; simp [partialSwap,hi]
    · simp [partialSwap,hj]

private lemma swap_reindex (q a : ℕ) (i : Fin q) :
    (embedOp (swapApp q a i).gate.mat (swapApp q a i).wires).submatrix
      (triple q a).symm (triple q a).symm = permMat (partialSwap {i}) := by
  classical
  change (embedOp swGate.mat (swapWires q a i)).submatrix _ _ = _
  rw [embed_swap]
  have hw0 : swapWires q a i 0 = leftWire q a i := by rfl
  have hw1 : swapWires q a i 1 = rightWire q a i := by rfl
  rw [hw0,hw1]
  ext x y
  have he : bitSwap (leftWire q a i) (rightWire q a i) ((triple q a).symm x) =
      (triple q a).symm (partialSwap {i} x) := by
    apply (triple q a).injective
    simpa using bitSwap_triple q a i ((triple q a).symm x)
  simp only [permMat, Matrix.submatrix_apply, Matrix.one_apply, id_eq, he]
  simp

private lemma swap_list_reindex (q a : ℕ) (l : List (Fin q)) (hl : l.Nodup)
    (U : Matrix (Qubits (q+a)) (Qubits (q+a)) ℂ) :
    (OracleCircuit.unitary (l.map fun i => OracleStep.gate (a := fun _ : Fin 1 => q+a) (swapApp q a i))
      (fun _ => U)).submatrix (triple q a).symm (triple q a).symm =
      permMat (partialSwap l.toFinset) := by
  classical
  induction l with
  | nil =>
    simp only [List.map_nil, OracleCircuit.unitary, List.reverse_nil, List.prod_nil,
      Matrix.submatrix_one_equiv]
    ext x y
    simp [permMat, partialSwap, Matrix.one_apply]
  | cons i l ih =>
    have hi : i ∉ l.toFinset := by simpa using (List.nodup_cons.mp hl).1
    simp only [List.map_cons, OracleCircuit.unitary, List.reverse_cons, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
    rw [reindex_mul]
    change (OracleCircuit.unitary (l.map fun i => OracleStep.gate (a := fun _ : Fin 1 => q+a)
      (swapApp q a i)) (fun _ => U)).submatrix _ _ *
      (embedOp (swapApp q a i).gate.mat (swapApp q a i).wires).submatrix _ _ = _
    rw [ih (List.nodup_cons.mp hl).2, swap_reindex, permMat_mul, partialSwap_insert _ _ hi]
    simp

private def firstWires (m n : ℕ) : Fin m ↪ Fin (m+n) :=
  ⟨Fin.castAdd n, Fin.castAdd_injective m n⟩

private lemma embed_first (m n : ℕ) (U : Matrix (Qubits m) (Qubits m) ℂ) :
    (embedOp U (firstWires m n)).submatrix
      (qubitsAppendEquiv m n).symm (qubitsAppendEquiv m n).symm =
      Matrix.kronecker U (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  classical
  ext x y
  have hc : (∀ k : Fin (m+n), k ∉ Set.range (firstWires m n) →
      Fin.append x.1 x.2 k = Fin.append y.1 y.2 k) ↔ x.2 = y.2 := by
    constructor
    · intro h
      funext j
      have hn : Fin.natAdd m j ∉ Set.range (firstWires m n) := by
        rintro ⟨i,hi⟩
        have hh := congrArg Fin.val hi
        dsimp [firstWires] at hh
        omega
      simpa using h (Fin.natAdd m j) hn
    · intro h k
      refine Fin.addCases (fun i hk => ?_) (fun j hk => ?_) k
      · exact False.elim (hk ⟨i,rfl⟩)
      · simp [h]
  have hx : Fin.append x.1 x.2 ∘ firstWires m n = x.1 := by funext j; simp [firstWires]
  have hy : Fin.append y.1 y.2 ∘ firstWires m n = y.1 := by funext j; simp [firstWires]
  change (if ∀ k, k ∉ Set.range (firstWires m n) →
    Fin.append x.1 x.2 k = Fin.append y.1 y.2 k then
      U (Fin.append x.1 x.2 ∘ firstWires m n) (Fin.append y.1 y.2 ∘ firstWires m n)
    else 0) = U x.1 y.1 * (1 : Matrix (Qubits n) (Qubits n) ℂ) x.2 y.2
  simp only [hc,hx,hy]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

private lemma reindex_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U.submatrix e e ∈ Matrix.unitaryGroup κ ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change U.submatrix e e * (U.submatrix e e).conjTranspose = 1
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact (congrArg (fun M : Matrix ι ι ℂ => M.submatrix e e) hU.2).trans
    (Matrix.submatrix_one_equiv e)

private lemma tensor_one_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.kronecker U (1 : Matrix κ κ ℂ) ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change Matrix.kronecker U (1 : Matrix κ κ ℂ) *
    (Matrix.kronecker U (1 : Matrix κ κ ℂ)).conjTranspose = 1
  dsimp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    show U * U.conjTranspose = 1 from hU.2, one_mul, Matrix.one_kronecker_one]

private def densityQuery (q a : ℕ) (adj : Bool) :
    OracleStep twoQubitGateSet (fun _ : Fin 1 => q+a) ((q+a)+q) :=
  .query 0 adj none (firstWires (q+a) q) (by simp)

private noncomputable def densitySwaps (q a : ℕ) :
    OracleCircuit twoQubitGateSet (fun _ : Fin 1 => q+a) ((q+a)+q) :=
  (Finset.univ.toList : List (Fin q)).map fun i => .gate (swapApp q a i)

private noncomputable def densityCircuit (q a : ℕ) :
    OracleCircuit twoQubitGateSet (fun _ : Fin 1 => q+a) ((q+a)+q) :=
  densityQuery q a false :: densitySwaps q a ++ [densityQuery q a true]

private def fullSwap (q a : ℕ) :
    (Qubits (q+a) × Qubits q) ≃ (Qubits (q+a) × Qubits q) :=
  ((qubitsAppendEquiv q a).prodCongr (Equiv.refl _)).trans
    ((partialSwap Finset.univ).trans
      ((qubitsAppendEquiv q a).prodCongr (Equiv.refl _)).symm)

private lemma fullSwap_apply (q a : ℕ) (x : Qubits (q+a) × Qubits q) :
    fullSwap q a x =
      (Fin.append x.2 ((qubitsAppendEquiv q a x.1).2), (qubitsAppendEquiv q a x.1).1) := by
  simp [fullSwap,partialSwap,qubitsAppendEquiv]

private lemma densitySwaps_unitary (q a : ℕ)
    (U : Matrix (Qubits (q+a)) (Qubits (q+a)) ℂ) :
    (OracleCircuit.unitary (densitySwaps q a) (fun _ => U)).submatrix
      (qubitsAppendEquiv (q+a) q).symm (qubitsAppendEquiv (q+a) q).symm =
      permMat (fullSwap q a) := by
  classical
  have h := swap_list_reindex q a Finset.univ.toList (Finset.nodup_toList _) U
  simp only [Finset.toList_toFinset] at h
  let e := (qubitsAppendEquiv q a).prodCongr (Equiv.refl (Qubits q))
  have hh := congrArg (fun M : Matrix ((Qubits q × Qubits a) × Qubits q)
    ((Qubits q × Qubits a) × Qubits q) ℂ => M.submatrix e e) h
  rw [permMat_reindex] at hh
  have hc : (triple q a).symm ∘ e = (qubitsAppendEquiv (q+a) q).symm := by
    funext x
    change (qubitsAppendEquiv (q+a) q).symm (e.symm (e x)) = _
    simp
  simp only [Matrix.submatrix_submatrix,hc] at hh
  exact hh

private lemma densityCircuit_unitary (q a : ℕ)
    (U : Matrix (Qubits (q+a)) (Qubits (q+a)) ℂ) :
    (OracleCircuit.unitary (densityCircuit q a) (fun _ => U)).submatrix
      (qubitsAppendEquiv (q+a) q).symm (qubitsAppendEquiv (q+a) q).symm =
      Matrix.kronecker (star U) (1 : Matrix (Qubits q) (Qubits q) ℂ) * permMat (fullSwap q a) * Matrix.kronecker U (1 : Matrix (Qubits q) (Qubits q) ℂ) := by
  classical
  have he (adj : Bool) :
      ((densityQuery q a adj).mat (fun _ => U)).submatrix
        (qubitsAppendEquiv (q+a) q).symm (qubitsAppendEquiv (q+a) q).symm =
      Matrix.kronecker (if adj then star U else U) 1 := by
    exact embed_first (q+a) q _
  simp only [densityCircuit, OracleCircuit.unitary, List.map_cons, List.map_append,
    List.map_nil,List.reverse_cons,List.reverse_append,List.reverse_nil,List.nil_append,
    List.prod_append,List.prod_cons,List.prod_nil,mul_one]
  rw [reindex_mul,reindex_mul]
  change _ * ((OracleCircuit.unitary (densitySwaps q a) (fun _ => U)).submatrix _ _ * _) = _
  rw [densitySwaps_unitary,he,he]
  simp [mul_assoc]

private lemma permMat_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (A : Matrix ι ι ℂ) (x y : ι) :
    (permMat e * A) x y = A (e x) y := by
  simp only [permMat,Matrix.mul_apply,Matrix.submatrix_apply,Matrix.one_apply,
    id_eq,ite_mul,one_mul,zero_mul]
  simp

-- The selected block is the partial trace, computed in the computational basis.
private lemma density_block (q a : ℕ)
    (U : Matrix (Qubits (q+a)) (Qubits (q+a)) ℂ) (i j : Qubits q) :
    (Matrix.kronecker (star U) (1 : Matrix (Qubits q) (Qubits q) ℂ) * permMat (fullSwap q a) * Matrix.kronecker U (1 : Matrix (Qubits q) (Qubits q) ℂ))
      ((0 : Qubits (q+a)),i) (0,j) =
    ∑ h : Qubits a, U (Fin.append i h) 0 * star (U (Fin.append j h) 0) := by
  classical
  rw [mul_assoc,Matrix.mul_apply]
  simp only [permMat_mul_apply]
  simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.star_apply,
    fullSwap_apply,Fintype.sum_prod_type]
  simp only [mul_ite,ite_mul,mul_one,mul_zero,zero_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq,Finset.mem_univ,if_true,
    Finset.sum_const_zero]
  rw [← Equiv.sum_comp (qubitsAppendEquiv q a).symm]
  simp [Fintype.sum_prod_type,qubitsAppendEquiv,mul_comm]

theorem solution (q a : ℕ) :
    ∃ c : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => q + a) ((q + a) + q),
      (c.countP fun s => match s with
        | OracleStep.query _ false _ _ _ => true
        | _ => false) ≤ 1 ∧
      (c.countP fun s => match s with
        | OracleStep.query _ true _ _ _ => true
        | _ => false) ≤ 1 ∧
      (∀ s ∈ c, match s with
        | OracleStep.query _ _ ctrl _ _ => ctrl = none
        | OracleStep.gate _ => True) ∧
      c.gateCount ≤ q + 1 ∧
      ∀ (U : Matrix (Qubits (q + a)) (Qubits (q + a)) ℂ) (ρ : Matrix (Qubits q) (Qubits q) ℂ),
        U ∈ Matrix.unitaryGroup (Qubits (q + a)) ℂ → IsDensityMatrix ρ →
        traceRight (pureDensity (WithLp.toLp 2 fun p : Qubits q × Qubits a =>
          act U (zeroKet (q + a)) ((qubitsAppendEquiv q a).symm p))) = ρ →
        IsBlockEncoding (0 : Qubits (q + a))
          ((c.unitary fun _ => U).submatrix (qubitsAppendEquiv (q + a) q).symm
            (qubitsAppendEquiv (q + a) q).symm) 1 0 ρ  := by
  classical
  refine ⟨densityCircuit q a, ?_, ?_, ?_, ?_, ?_⟩
  · simp [densityCircuit,densityQuery,densitySwaps,List.countP_append,List.countP_map]
  · simp [densityCircuit,densityQuery,densitySwaps,List.countP_append,List.countP_map]
  · intro s hs
    simp only [densityCircuit,List.mem_cons,List.mem_append] at hs
    rcases hs with (rfl | hs) | (rfl | hs)
    · rfl
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
      trivial
    · rfl
    · simp at hs
  · simp [OracleCircuit.gateCount,densityCircuit,densityQuery,densitySwaps,
      List.countP_append,List.countP_map,Function.comp_def]
  · intro U ρ hU _ hp
    rw [densityCircuit_unitary]
    refine ⟨mul_mem (mul_mem (tensor_one_unitary _ (Unitary.star_mem hU))
      (permMat_unitary _)) (tensor_one_unitary _ hU), ?_⟩
    have hket (x : Qubits (q+a)) : act U (zeroKet (q+a)) x = U x 0 := by
      change Matrix.mulVec U (Pi.single 0 1) x = U x 0
      simp
    have hb : (Matrix.of fun i j : Qubits q =>
        (Matrix.kronecker (star U) (1 : Matrix (Qubits q) (Qubits q) ℂ) *
          permMat (fullSwap q a) * Matrix.kronecker U (1 : Matrix (Qubits q) (Qubits q) ℂ)) (0,i) (0,j)) = ρ := by
      ext i j
      rw [Matrix.of_apply,density_block,←hp]
      simp [traceRight,pureDensity,hket,qubitsAppendEquiv]
    change specNorm ((↑(1 : ℝ) : ℂ) • (Matrix.of fun i j =>
      (Matrix.kronecker (star U) (1 : Matrix (Qubits q) (Qubits q) ℂ) *
        permMat (fullSwap q a) * Matrix.kronecker U (1 : Matrix (Qubits q) (Qubits q) ℂ)) (0,i) (0,j)) - ρ) ≤ 0
    rw [hb]
    simp [specNorm]
