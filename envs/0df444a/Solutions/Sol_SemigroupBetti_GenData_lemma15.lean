-- Prove2me | solution 1 for SemigroupBetti.GenData.lemma15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:20:09.830615+00:00
-- url     : https://prove2.me/submissions/8d408833-452d-4f51-a2ac-9c929db841ab

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_card_pairsOf
public import Theorems.Thm_SemigroupBetti_GenData_pairsOf_antichain
public import Theorems.Thm_SemigroupBetti_GenData_pairsOf_pos
public import Theorems.Thm_SemigroupBetti_GenData_exists_coord_eq
public import Theorems.Thm_SemigroupBetti_GenData_exc_U2
public import Theorems.Thm_SemigroupBetti_GenData_exc_V2
public import Theorems.Thm_SemigroupBetti_GenData_sideQ_split
public import Theorems.Thm_SemigroupBetti_GenData_identity2
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_no_replace
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_eq_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_one_bounds
public import Theorems.Thm_SemigroupBetti_GenData_three_le_W
public import Theorems.Thm_SemigroupBetti_IsPairAntichain_corank_le
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (hA : G.A = 1) (hB : G.B = G.W - 1) (hQ : G.Q = G.W - 2) :
    (∃ D ∈ G.famQ, G.sel D {1, 3} 1 = 1) ∧
      ∀ D ∈ G.famQ, G.sel D {1, 3} 1 = 1 → G.sel D {1, 3} = ![0, 1, 0, G.W - 2] := by
  have hW := G.three_le_W
  have hK : ({1, 3} : Finset (Fin 4)).card = 2 := by decide
  have hF : ∀ d ∈ G.famQ, G.IsSplit d {1, 3} := fun d hd => G.sideQ_split hd
  refine ⟨?_, ?_⟩
  · exact G.exists_coord_eq (K := {1, 3}) (i := 3) (k := 1) (by decide) (by decide) G.famQ hF
      (fun d hd => by
        have := G.sel_one_bounds (hF d hd) hK (by decide)
        rw [hB] at this; exact this)
      (by have : G.Q = G.famQ.card := rfl; omega) (v := 1) le_rfl (by omega)
  · intro D hD hu
    have hS := hF D hD
    have hz0 : G.sel D {1, 3} 0 = 0 := G.sel_eq_zero hS hK (by decide)
    have hz2 : G.sel D {1, 3} 2 = 0 := G.sel_eq_zero hS hK (by decide)
    -- lower bound `v ≥ W - 2` from Lemma 11
    have hT := G.pairsOf_antichain (F := G.famQ) (i := 1) (k := 3) (by decide) (by decide) hF
    have hpos := G.pairsOf_pos (F := G.famQ) (i := 1) (k := 3) (by decide) (by decide) hF
    have hmem : (G.sel D {1, 3} 1, G.sel D {1, 3} 3) ∈ G.pairsOf G.famQ {1, 3} 1 3 := mem_image.2 ⟨D, hD, rfl⟩
    have hco := hT.corank_le hpos hmem
    have hfilt : (G.pairsOf G.famQ {1, 3} 1 3).filter (fun y => (G.sel D {1, 3} 1, G.sel D {1, 3} 3).1 ≤ y.1) =
        G.pairsOf G.famQ {1, 3} 1 3 := by
      apply filter_true_of_mem
      intro y hy; simp only; rw [hu]; exact (hpos y hy).1
    rw [hfilt, G.card_pairsOf (by decide) (by decide) hF] at hco
    simp only at hco
    have hQ' : G.famQ.card = G.W - 2 := hQ
    rw [hQ'] at hco
    -- upper bound `v ≤ W - 2` by the exceptional replacement
    have hv : G.sel D {1, 3} 3 ≤ G.W - 2 := by
      by_contra hv
      have hU : G.V2 ≤ G.sel D {1, 3} := by
        rw [exc_V2 hA hB]; intro j; fin_cases j <;> simp [hz0, hz2, hu]; omega
      exact G.no_replace hS hK hU G.identity2.1.symm (k := 3)
        (by rw [exc_V2 hA hB]; simp; omega) (j := 2) (by decide)
        (by rw [exc_U2 hA hB]; simp; omega)
    funext j; fin_cases j <;> simp [hz0, hz2, hu]; omega
end SemigroupBetti.GenData
