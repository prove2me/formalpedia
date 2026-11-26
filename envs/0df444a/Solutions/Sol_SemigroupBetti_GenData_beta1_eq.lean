-- Prove2me | solution 1 for SemigroupBetti.GenData.beta1_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:34.075201+00:00
-- url     : https://prove2.me/submissions/aadb27c9-28d9-4f1a-96bf-96b18f75aa18

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_lemma5
public import Theorems.Thm_SemigroupBetti_GenData_mem_fam
public import Theorems.Thm_SemigroupBetti_GenData_isSplit_exclusive
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_singletonDegrees
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
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
theorem _root_.solution : G.beta1 = G.sigma + G.P + G.Q + G.E := by
  classical
  have hpt : ∀ d ∈ range (G.H + 1), G.ncomp d - 1 =
      (if d ∈ G.singletonDegrees then G.ncomp d - 1 else 0) + (if d ∈ G.famP then 1 else 0) +
      (if d ∈ G.famQ then 1 else 0) + (if d ∈ G.famE then 1 else 0) := by
    intro d hd
    have hdH : d ≤ G.H := Nat.lt_succ_iff.1 (mem_range.1 hd)
    simp only [famP, famQ, famE, G.mem_fam, G.mem_singletonDegrees]
    by_cases hc : G.contributes d
    · by_cases hS : G.HasSingletonComp d
      · simp [hc, hS, hdH]
      · obtain ⟨h2, hsp⟩ := G.lemma5 hc hS
        have e12 : ¬ (G.IsSplit d {0, 1} ∧ G.IsSplit d {0, 2}) := fun h =>
          absurd (G.isSplit_exclusive h.1 h.2 (i := 0) (by simp) (by simp)) (by decide)
        have e13 : ¬ (G.IsSplit d {0, 1} ∧ G.IsSplit d {0, 3}) := fun h =>
          absurd (G.isSplit_exclusive h.1 h.2 (i := 0) (by simp) (by simp)) (by decide)
        have e23 : ¬ (G.IsSplit d {0, 2} ∧ G.IsSplit d {0, 3}) := fun h =>
          absurd (G.isSplit_exclusive h.1 h.2 (i := 0) (by simp) (by simp)) (by decide)
        rcases hsp with h | h | h
        · have : ¬ G.IsSplit d {0, 2} := fun h' => e12 ⟨h, h'⟩
          have : ¬ G.IsSplit d {0, 3} := fun h' => e13 ⟨h, h'⟩
          simp [*]
        · have : ¬ G.IsSplit d {0, 1} := fun h' => e12 ⟨h', h⟩
          have : ¬ G.IsSplit d {0, 3} := fun h' => e23 ⟨h, h'⟩
          simp [*]
        · have : ¬ G.IsSplit d {0, 1} := fun h' => e13 ⟨h', h⟩
          have : ¬ G.IsSplit d {0, 2} := fun h' => e23 ⟨h', h⟩
          simp [*]
    · have : G.ncomp d ≤ 1 := by unfold contributes at hc; omega
      simp [hc]; omega
  have hsub : ∀ s : Finset ℕ, s ⊆ range (G.H + 1) →
      s.card = ∑ d ∈ range (G.H + 1), (if d ∈ s then 1 else 0) := by
    intro s hs
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hs]; simp
  have hfam : ∀ K, G.fam K ⊆ range (G.H + 1) := by
    intro K d hd; exact mem_range.2 (Nat.lt_succ_of_le (G.mem_fam.1 hd).1)
  have hsig : G.sigma = ∑ d ∈ range (G.H + 1),
      (if d ∈ G.singletonDegrees then G.ncomp d - 1 else 0) := by
    have hsd : G.singletonDegrees ⊆ range (G.H + 1) := by
      intro d hd; exact mem_range.2 (Nat.lt_succ_of_le (G.mem_singletonDegrees.1 hd).1)
    rw [sigma, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsd]
  rw [beta1, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hsig, P, Q, E, hsub G.famP (hfam _), hsub G.famQ (hfam _),
    hsub G.famE (hfam _)]
end SemigroupBetti.GenData
