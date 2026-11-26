-- Prove2me | solution 1 for SemigroupBetti.GenData.lemma5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:39.230226+00:00
-- url     : https://prove2.me/submissions/63285619-2915-4db5-bf3c-376dbbaa4edd

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_IsSplit_compl
public import Theorems.Thm_SemigroupBetti_GenData_compSupp_disjoint
public import Theorems.Thm_SemigroupBetti_GenData_compSupp_nonempty
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_pos_of_two_le_ncomp
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
theorem _root_.solution {d : ℕ} (hd : G.contributes d) (hS : ¬ G.HasSingletonComp d) :
    G.ncomp d = 2 ∧ (G.IsSplit d {0, 1} ∨ G.IsSplit d {0, 2} ∨ G.IsSplit d {0, 3}) := by
  classical
  have hdpos := G.pos_of_two_le_ncomp hd
  have hcard2 : ∀ C : (G.nabla d).ConnectedComponent, 2 ≤ (G.compSupp C).card := by
    intro C
    have h0 := (G.compSupp_nonempty hdpos C).card_pos
    have h1 : (G.compSupp C).card ≠ 1 := fun h => hS ⟨C, h⟩
    omega
  have hnt : Nontrivial (G.nabla d).ConnectedComponent := by
    rw [← Fintype.one_lt_card_iff_nontrivial]; exact hd
  obtain ⟨C1, C2, h12⟩ := exists_pair_ne (G.nabla d).ConnectedComponent
  have hdisj := G.compSupp_disjoint h12
  have hu := card_le_univ (G.compSupp C1 ∪ G.compSupp C2)
  rw [card_union_of_disjoint hdisj, Fintype.card_fin] at hu
  have hc1 := hcard2 C1
  have hc2 := hcard2 C2
  have huniv : G.compSupp C1 ∪ G.compSupp C2 = univ := by
    apply eq_univ_of_card
    rw [card_union_of_disjoint hdisj, Fintype.card_fin]; omega
  have hcompl : G.compSupp C2 = (G.compSupp C1)ᶜ := by
    ext k
    rw [mem_compl]
    constructor
    · intro hk hk1; exact Finset.disjoint_left.1 hdisj hk1 hk
    · intro hk
      have : k ∈ G.compSupp C1 ∪ G.compSupp C2 := huniv ▸ mem_univ k
      rcases mem_union.1 this with h | h
      · exact absurd h hk
      · exact h
  -- every component is `C1` or `C2`
  have hall : ∀ C, C = C1 ∨ C = C2 := by
    intro C
    by_contra hC
    push Not at hC
    obtain ⟨k, hk⟩ := G.compSupp_nonempty hdpos C
    have : k ∈ G.compSupp C1 ∪ G.compSupp C2 := huniv ▸ mem_univ k
    rcases mem_union.1 this with h | h
    · exact Finset.disjoint_left.1 (G.compSupp_disjoint hC.1) hk h
    · exact Finset.disjoint_left.1 (G.compSupp_disjoint hC.2) hk h
  refine ⟨?_, ?_⟩
  · unfold ncomp
    rw [← card_univ, show (univ : Finset (G.nabla d).ConnectedComponent) = {C1, C2} by
      ext C; simp only [mem_univ, mem_insert, mem_singleton, true_iff]; exact hall C]
    exact card_pair h12
  · -- the component whose support contains `0`
    have hsplit1 : G.IsSplit d (G.compSupp C1) := ⟨C1, C2, h12, rfl, hcompl⟩
    have hsplit2 : G.IsSplit d (G.compSupp C2) := by
      rw [hcompl]; exact hsplit1.compl
    have hc1' : (G.compSupp C1).card = 2 := by omega
    have hc2' : (G.compSupp C2).card = 2 := by omega
    have key : ∀ K : Finset (Fin 4), K.card = 2 → 0 ∈ K → K = {0, 1} ∨ K = {0, 2} ∨ K = {0, 3} := by
      decide
    have h0 : (0 : Fin 4) ∈ G.compSupp C1 ∪ G.compSupp C2 := huniv ▸ mem_univ 0
    rcases mem_union.1 h0 with h | h
    · rcases key _ hc1' h with e | e | e <;> rw [e] at hsplit1 <;> simp [hsplit1]
    · rcases key _ hc2' h with e | e | e <;> rw [e] at hsplit2 <;> simp [hsplit2]
end SemigroupBetti.GenData
