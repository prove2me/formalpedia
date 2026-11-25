-- Prove2me | solution 1 for PerfectGraph.card_le_of_isColOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:39:21.07566+00:00
-- url     : https://prove2.me/submissions/89720ca1-b791-4143-a329-552e994aeaee

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Theorems.Thm_PerfectGraph_card_le_indepNum_induce

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution [Finite V] {S : Finset V} {k : ℕ} (h : IsColOn G S k) :
    S.card ≤ (G.induce (S : Set V)).indepNum * k := by
  classical
  obtain ⟨c, hc, hcv⟩ := h
  rw [Finset.card_eq_sum_card_fiberwise (f := c) (t := Finset.range k)
    (fun v hv => Finset.mem_range.2 (hc v hv))]
  calc ∑ i ∈ Finset.range k, (S.filter (fun v => c v = i)).card
      ≤ ∑ _i ∈ Finset.range k, (G.induce (S : Set V)).indepNum := by
        apply Finset.sum_le_sum
        intro i _
        apply card_le_indepNum_induce G (Finset.filter_subset _ _)
        intro u hu w hw _ huw
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hu hw
        exact hcv u hu.1 w hw.1 huw (hu.2.trans hw.2.symm)
    _ = (G.induce (S : Set V)).indepNum * k := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
end PerfectGraph
