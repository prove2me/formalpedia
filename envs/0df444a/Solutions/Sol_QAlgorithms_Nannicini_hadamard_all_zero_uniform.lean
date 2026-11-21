-- Prove2me | solution 1 for QAlgorithms.Nannicini.hadamard_all_zero_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-20T12:16:21.681342+00:00
-- url     : https://prove2.me/submissions/ff49ad05-bf74-47d3-91a4-da4cfa273872

import Definitions.Def_QAlgorithms_Defs_Adiabatic

set_option autoImplicit false
open QAlgorithms

private noncomputable abbrev scaleH : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

private noncomputable abbrev onWire {q : ℕ} (i : Fin q) :=
  embedOp (Gate.ofMatrix1 hadamard).mat (Stabilizer.wire1 i)

private lemma onWire_apply {q : ℕ} (i : Fin q) (y z : Qubits q) :
    onWire i y z = if ∀ a, a ≠ i → y a = z a then hadamard (y i) (z i) else 0 := by
  classical
  simp [onWire, embedOp, Stabilizer.wire1, Set.mem_range, Gate.ofMatrix1]
  change (if ∀ a, i ≠ a → y a = z a then hadamard (y i) (z i) else 0) = _
  apply if_congr _ rfl rfl
  exact ⟨fun h a ha => h a (Ne.symm ha), fun h a ha => h a (Ne.symm ha)⟩

-- After the gates on l, amplitudes vanish unless all untouched wires are zero.
private lemma wire_product_column {q : ℕ} (l : List (Fin q)) (hl : l.Nodup)
    (y : Qubits q) :
    (l.map onWire).prod y (fun _ => false) =
      if ∀ a, a ∉ l → y a = false then scaleH ^ l.length else 0 := by
  classical
  induction l generalizing y with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.one_apply, List.not_mem_nil, not_false_eq_true,
      forall_true_left, List.length_nil, pow_zero]
    congr 1
    exact propext ⟨fun h a => congrFun h a, fun h => funext h⟩
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, ih hl, List.length_cons]
    -- The predecessor must match y off i and must still be zero at i.
    let z₀ := Function.update y i false
    have hoff : ∀ a, a ≠ i → y a = z₀ a := by
      intro a ha
      simp [z₀, ha]
    rw [Finset.sum_eq_single z₀]
    · rw [onWire_apply, if_pos hoff]
      have hz : z₀ i = false := by simp [z₀]
      rw [hz]
      have heq : (∀ a, a ∉ l → z₀ a = false) ↔ ∀ a, a ∉ i :: l → y a = false := by
        constructor
        · intro h a ha
          have hne : a ≠ i := fun e => ha (e ▸ List.mem_cons_self ..)
          exact (hoff _ hne).trans (h _ (fun hm => ha (List.mem_cons_of_mem _ hm)))
        · intro h a ha
          by_cases hne : a = i
          · simpa only [hne] using hz
          · exact (hoff _ hne).symm.trans (h _ (by simp [hne, ha]))
      rw [if_congr heq rfl rfl]
      split <;> simp [hadamard, scaleH, pow_succ, mul_comm]
    · intro z _ hne
      rw [onWire_apply]
      split
      · rename_i h
        split
        · rename_i hzero
          exact (hne (funext (fun a => by
            by_cases ha : a = i
            · subst a
              simpa [z₀] using hzero i hi
            · exact (h a ha).symm.trans (hoff a ha)))).elim
        · simp
      · simp
    · simp

private lemma sequential_amplitude (q : ℕ) (y : Qubits q) :
    (orderedProd fun i : Fin q => onWire i) y (fun _ => false) = scaleH ^ q := by
  have hn := List.nodup_reverse.mpr (List.nodup_finRange q)
  have h := wire_product_column (List.finRange q).reverse hn y
  simpa [orderedProd, List.map_reverse, ← List.ofFn_id, List.map_ofFn, List.mem_ofFn] using h

private lemma sequential_action_amplitude (q : ℕ) (y : Qubits q) :
    act (orderedProd fun i : Fin q => onWire i) (zeroKet q) y = scaleH ^ q := by
  classical
  simpa [act, zeroKet, ket, EuclideanSpace.single, Matrix.mulVec, dotProduct, Pi.single_apply]
    using sequential_amplitude q y

private lemma sqrt_two_pow (q : ℕ) : Real.sqrt ((2 : ℝ) ^ q) = Real.sqrt 2 ^ q := by
  induction q with
  | zero => simp
  | succ q ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

private lemma uniform_amplitude (q : ℕ) (j : Qubits q) :
    ((Real.sqrt 2 : ℂ)⁻¹) ^ q = uniformState (Qubits q) j := by
  change _ = (↑(Real.sqrt (Fintype.card (Fin q → Bool))) : ℂ)⁻¹
  simp [sqrt_two_pow, inv_pow]

private lemma hadamardN_zero (q : ℕ) :
    act (hadamardN q) (zeroKet q) = uniformState (Qubits q) := by
  have hz (j : Qubits q) : dotBits (fun _ => false) j = false := by
    simp only [dotBits, Bool.false_and]
    exact Finset.sum_const_zero
  ext j
  rw [← uniform_amplitude q j]
  change ((hadamardN q).mulVec (WithLp.ofLp (ket (fun _ => false)))) j = _
  simp [ket, Matrix.mulVec, dotProduct, hadamardN, hz]

theorem solution (q : ℕ) :
    act (orderedProd fun i : Fin q =>
        embedOp (Gate.ofMatrix1 hadamard).mat (Stabilizer.wire1 i)) (zeroKet q) =
      uniformState (Qubits q) ∧
    act (hadamardN q) (zeroKet q) = uniformState (Qubits q) := by
  constructor
  · ext y
    exact (sequential_action_amplitude q y).trans (uniform_amplitude q y)
  · exact hadamardN_zero q
