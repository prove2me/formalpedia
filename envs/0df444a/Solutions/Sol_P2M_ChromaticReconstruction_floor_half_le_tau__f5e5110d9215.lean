-- Prove2me | solution 1 for P2M_ChromaticReconstruction_floor_half_le_tau__f5e5110d9215
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:30.092409+00:00
-- url     : https://prove2.me/submissions/932f933f-c757-4bef-ace2-b45c3b09d922

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
import Theorems.Thm_ChromaticReconstruction_PL_not_iso
import Theorems.Thm_ChromaticReconstruction_PL_isTree
import Theorems.Thm_ChromaticReconstruction_compCount_PL_step


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (k : ℕ) (hk : 4 ≤ k) : ((k / 2 : ℕ) : ℕ∞) ≤ tau k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set b := (n - 1) / 2 with hbdef
  have hb : 1 ≤ b := by omega
  have hn : 2 * b + 1 ≤ n := by omega
  have hk2 : (n + 1) / 2 = b + 1 := by omega
  unfold tau
  refine le_iInf₂ fun t ht => ?_
  rw [hk2]
  norm_cast
  by_contra htb
  push_neg at htb
  let S : {S : SimpleGraph (Fin (n + 1)) // S.IsTree} := ⟨PL n (b - 1), PL_isTree (by omega)⟩
  let S' : {S : SimpleGraph (Fin (n + 1)) // S.IsTree} := ⟨PL n b, PL_isTree (by omega)⟩
  have heq : truncationClass (n + 1) t (Quotient.mk (treeSetoid (n + 1)) S) =
      truncationClass (n + 1) t (Quotient.mk (treeSetoid (n + 1)) S') := by
    funext μ
    show compCount (PL n (b - 1)) μ.1.parts = compCount (PL n b) μ.1.parts
    have := compCount_PL_step (c := b - 1) (n := n) (by omega) μ.1.parts (by have := μ.2; omega)
    rwa [show b - 1 + 1 = b by omega] at this
  have := Quotient.exact (ht heq)
  obtain ⟨e⟩ := this
  exact (PL_not_iso hb hn).false e
end ChromaticReconstruction
