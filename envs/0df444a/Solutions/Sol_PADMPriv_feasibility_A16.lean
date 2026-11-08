-- Prove2me | solution 1 for PADMPriv.feasibility_A16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:43:23.952118+00:00
-- url     : https://prove2.me/submissions/07c3cbaa-9002-48c9-99a1-b04d34194cd2

import Mathlib
import Definitions.Def_PADMPriv_pinvRight

open Matrix

namespace Aux_PADMA16
open PADMPriv

lemma right_inv {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℝ) (hM : M.rank = m) :
    M * pinvRight M = 1 := by
  have hrank : (M * M.transpose).rank = m := by rw [Matrix.rank_self_mul_transpose, hM]
  have h1 : LinearMap.range (M * M.transpose).mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hrank)
  have hsurj : Function.Surjective (M * M.transpose).mulVec := by
    intro y
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp h1 y
    exact ⟨x, hx⟩
  have hU : IsUnit (M * M.transpose) := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  unfold pinvRight
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]

lemma key {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℝ) (hM : M.rank = m)
    (v : EuclideanSpace ℝ (Fin m)) :
    Matrix.toEuclideanLin M (Matrix.toEuclideanLin (pinvRight M) v) = v := by
  show WithLp.toLp 2 (M *ᵥ (pinvRight M *ᵥ WithLp.ofLp v)) = v
  rw [Matrix.mulVec_mulVec, right_inv M hM, Matrix.one_mulVec]

end Aux_PADMA16

open PADMPriv in
theorem solution {m p l : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin l) ℝ) (hA : A.rank = m) (hB : B.rank = m)
    (c u : EuclideanSpace ℝ (Fin m)) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin (pinvRight A) u) +
      Matrix.toEuclideanLin B (Matrix.toEuclideanLin (pinvRight B) (c - u)) = c := by
  rw [Aux_PADMA16.key A hA, Aux_PADMA16.key B hB]
  abel
