-- Prove2me | solution 1 for VdNSim.Sparse.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:32:07.877454+00:00
-- url     : https://prove2.me/submissions/445f0382-bd45-48df-b853-77c8cca9d56b

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

open VdNSim.Sparse in
theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (D : ColumnData A s) (ψ ϕ : X → ℂ) :
    matElem ϕ A ψ =
      ∑ i : Fin s, ∑ x, D.α i x * star (ϕ (D.r i x)) * ψ x := by
  unfold matElem
  calc _ = ∑ x, ∑ i : Fin s, D.α i x * star (ϕ (D.r i x)) * ψ x := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp_rw [D.eq2, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_eq_single (D.r i x)]
          · rw [if_pos rfl]; ring
          · intro b _ hb
            rw [if_neg (Ne.symm hb)]; ring
          · intro h; exact absurd (Finset.mem_univ _) h
    _ = _ := Finset.sum_comm
