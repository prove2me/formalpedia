-- Prove2me | solution 1 for PropVolSampling.Reduction.cp_le_opt
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:02:03.729996+00:00
-- url     : https://prove2.me/submissions/97a77e9e-ca40-4153-a9da-efaddcaec2c6

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

noncomputable section

open Matrix Finset

namespace PropVolSampling.Reduction.OptimalityProof

/-- The indicator of a k-set is a feasible fractional design. -/
lemma indicator_feasible {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) :
    IsRelaxFeasible k (fun i => if i ∈ S then 1 else 0) := by
  constructor
  · intro i
    dsimp only
    split_ifs <;> norm_num
  · simp [hS]

lemma gram_eq_sum {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    gram V S = ∑ i ∈ S, vecMulVec (fun a => V a i) (fun a => V a i) := by
  ext a b
  simp [gram, colSub, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
  exact Finset.sum_attach S (fun i => V a i * V b i)

lemma weightedGram_indicator {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    weightedGram V (fun i => if i ∈ S then 1 else 0) = gram V S := by
  rw [gram_eq_sum]
  simp [weightedGram, ite_smul]

lemma cp_le_opt {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ)
    (x : Fin n → ℝ) (hx : IsRelaxOptimal V k x) (S : Finset (Fin n))
    (hS : S.card = k) (hpd : (gram V S).PosDef) :
    aObj (weightedGram V x) ≤ aObj (gram V S) := by
  have hi := weightedGram_indicator V S
  have h := hx.2.2 (fun i => if i ∈ S then 1 else 0)
    (indicator_feasible S hS) (hi.symm ▸ hpd)
  simpa only [hi] using h

end PropVolSampling.Reduction.OptimalityProof

open PropVolSampling.Reduction

theorem solution {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ)
    (x : Fin n → ℝ) (hx : IsRelaxOptimal V k x) (S : Finset (Fin n))
    (hS : S.card = k) (hpd : (gram V S).PosDef) :
    aObj (weightedGram V x) ≤ aObj (gram V S) :=
  OptimalityProof.cp_le_opt V k x hx S hS hpd
