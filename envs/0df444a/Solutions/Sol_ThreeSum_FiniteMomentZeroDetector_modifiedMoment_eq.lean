-- Prove2me | solution 1 for ThreeSum.FiniteMomentZeroDetector.modifiedMoment_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:24.494165+00:00
-- url     : https://prove2.me/submissions/660cf124-ce2a-4cc8-bed5-644e81557aff

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector

set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.FiniteMomentZeroDetector
theorem _root_.solution {t : ℕ} (v w : Fin t → ℤ) (a : ℤ) (k : ℕ) :
    modifiedMoment v w a k=moment v (fun s => w s*(v s-a)^2) k := by
  unfold modifiedMoment moment
  rw [Finset.mul_sum,Finset.mul_sum]
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [pow_add,pow_one,pow_two]
  ring
end ThreeSum.FiniteMomentZeroDetector
