-- Prove2me | solution 1 for QAlgorithms.Nannicini.seqMeasProb_eq_prob
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-20T12:16:20.254054+00:00
-- url     : https://prove2.me/submissions/fb43ad3b-f12c-4159-bdd3-935ffacb5409

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

open QAlgorithms
open scoped BigOperators

private lemma coordinate_prob {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (z : Qubits q) :
    prob ψ z = ‖ψ z‖ ^ 2 := by
  simp [prob, ket, EuclideanSpace.inner_single_left]

/-- Multiplying the collapsed probability by the probability of this branch
recovers exactly the original weight on coordinates that survive. -/
private lemma weighted_collapse {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q))
    (k : Fin q) (b : Bool) (z : Qubits q) :
    probEvent ψ (fun x => x k = b) * prob (collapseQubit ψ k b) z =
      if z k = b then prob ψ z else 0 := by
  classical
  let p := probEvent ψ (fun x => x k = b)
  change p * prob (collapseQubit ψ k b) z = _
  have hp : 0 ≤ p := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  by_cases hz : z k = b
  · rw [if_pos hz]
    by_cases hzero : p = 0
    · have hle : prob ψ z ≤ p :=
        Finset.single_le_sum (f := prob ψ) (fun x _ => sq_nonneg _)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩)
      rw [hzero, zero_mul]
      exact le_antisymm (sq_nonneg _) (hzero ▸ hle)
    · rw [coordinate_prob, coordinate_prob]
      have heq : (collapseQubit ψ k b) z = ((Real.sqrt p : ℂ)⁻¹) * ψ z := by
        simp [collapseQubit, p, hz]
      rw [heq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hp]
      field_simp
  · rw [if_neg hz, coordinate_prob]
    have heq : (collapseQubit ψ k b) z = 0 := by simp [collapseQubit, hz]
    simp [heq]

/-- Keep the mass arriving at the current branch outside every conditional
probability. This also covers branches of mass zero. -/
private lemma weighted_seq {q : ℕ} (l : List (Fin q)) (ψ : EuclideanSpace ℂ (Qubits q))
    (y : Qubits q) (w : ℝ) (hw : (∑ z, w * prob ψ z) = w) :
    w * seqMeasProb ψ l y =
      ∑ z, if l.all (fun i => z i == y i) then w * prob ψ z else 0 := by
  classical
  induction l generalizing ψ w with
  | nil => simpa [seqMeasProb] using hw.symm
  | cons k l ih =>
    let p := probEvent ψ (fun z => z k = y k)
    let φ := collapseQubit ψ k (y k)
    have hpz (z : Qubits q) :
        (w * p) * prob φ z = if z k = y k then w * prob ψ z else 0 := by
      rw [mul_assoc, weighted_collapse]
      split <;> simp_all
    have hnew : (∑ z, (w * p) * prob φ z) = w * p := by
      simp_rw [hpz]
      simp [p, probEvent, Finset.sum_filter, Finset.mul_sum, mul_ite]
    change w * (p * seqMeasProb φ l y) = _
    rw [← mul_assoc, ih φ (w * p) hnew]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases hk : z k = y k <;>
      by_cases hl : l.all (fun i => z i == y i) = true <;>
        simp [List.all_cons, hk, hl, hpz]

theorem solution {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (hψ : IsState ψ)
    (σ : Equiv.Perm (Fin q)) (j : Qubits q) :
    seqMeasProb ψ (List.ofFn fun i => σ i) j = prob ψ j := by
  classical
  have hw : (∑ z, (1 : ℝ) * prob ψ z) = 1 := by
    simp only [one_mul, coordinate_prob, ← EuclideanSpace.norm_sq_eq]
    change ‖ψ‖ = 1 at hψ
    rw [hψ, one_pow]
  have hagree (z : Qubits q) :
      ((List.ofFn fun i => σ i).all fun i => z i == j i) = true ↔ z = j := by
    simp only [List.all_eq_true, beq_iff_eq]
    constructor
    · intro h
      exact funext fun i => h i (List.mem_ofFn.mpr (σ.surjective i))
    · rintro rfl
      simp
  simpa [hagree] using weighted_seq (List.ofFn fun i => σ i) ψ j 1 hw
