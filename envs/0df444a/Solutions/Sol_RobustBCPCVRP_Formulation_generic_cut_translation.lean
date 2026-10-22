-- Prove2me | solution 1 for RobustBCPCVRP.Formulation.generic_cut_translation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:20:33.139625+00:00
-- url     : https://prove2.me/submissions/bb3ffca2-0ee6-4d78-a9c7-d8ad1f28febc

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
set_option autoImplicit false
open LysgaardCVRP.Shrink RobustBCPCVRP.Formulation

theorem solution {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (x : Sym2 (Fin (n + 1)) → ℝ) (lam : List (Fin (n + 1)) →₀ ℝ)
    (h5 : ∀ e ∈ E, colSum lam e = x e) (a : Sym2 (Fin (n + 1)) → ℝ) (b : ℝ) :
    b ≤ ∑ e ∈ E, a e * x e ↔
      b ≤ ∑ r ∈ lam.support, (∑ e ∈ E, a e * (inc r e : ℝ)) * lam r := by
  have : ∑ e ∈ E, a e * x e = ∑ r ∈ lam.support, (∑ e ∈ E, a e * (inc r e : ℝ)) * lam r := by
    calc ∑ e ∈ E, a e * x e = ∑ e ∈ E, a e * colSum lam e :=
          Finset.sum_congr rfl (fun e he => by rw [h5 e he])
      _ = ∑ e ∈ E, ∑ r ∈ lam.support, a e * (lam r * (inc r e : ℝ)) := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          rw [colSum, Finset.mul_sum]
      _ = ∑ r ∈ lam.support, ∑ e ∈ E, a e * (lam r * (inc r e : ℝ)) := Finset.sum_comm
      _ = ∑ r ∈ lam.support, (∑ e ∈ E, a e * (inc r e : ℝ)) * lam r := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun e _ => by ring)
  rw [this]
