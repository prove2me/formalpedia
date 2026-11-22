-- Prove2me | solution 1 for Parikh.positive_multiplicities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:45.537002+00:00
-- url     : https://prove2.me/submissions/5f9d5ce2-3c74-4a16-8b66-90aad54eec27

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
public import Theorems.Thm_Parikh_ActivationOrder_append_of_covered

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {N C : Type*} [DecidableEq C]
    (required : C → N) (added : C → Set N) (U : Set N) (D : Finset C)
    (hself : ∀ c ∈ D, required c ∈ added c) (h : Activatable required added U D)
    (m : C → ℕ) (hm : ∀ c ∈ D, 0 < m c) :
    ∃ cs : List C, ActivationOrder required added U cs ∧
      (∀ c, c ∈ cs ↔ c ∈ D) ∧ (∀ c ∈ D, cs.count c = m c) := by
  obtain ⟨order, hnd, hmem, horder⟩ := h
  -- Pay for every operation once, then append the requested extra copies.
  let extra := order.flatMap (fun c => List.replicate (m c - 1) c)
  have hextra : ∀ c ∈ extra, c ∈ D := by
    intro c hc
    obtain ⟨d, hd, hrep⟩ := List.mem_flatMap.mp hc
    have hcd := List.eq_of_mem_replicate hrep
    exact hcd ▸ (hmem d).mp hd
  have hact : ActivationOrder required added U (order ++ extra) :=
    horder.append_of_covered (by
      intro c hc
      have hD := hextra c hc
      exact Or.inr ⟨c, (hmem c).mpr hD, hself c hD⟩)
  refine ⟨order ++ extra, hact, ?_, ?_⟩
  · intro c
    constructor
    · intro hc
      rcases List.mem_append.mp hc with hc | hc
      · exact (hmem c).mp hc
      · exact hextra c hc
    · intro hc
      exact List.mem_append_left _ ((hmem c).mpr hc)
  · intro c hc
    have hone : order.count c = 1 := List.count_eq_one_of_mem hnd ((hmem c).mpr hc)
    have hcount : extra.count c = m c - 1 := by
      dsimp only [extra]
      rw [List.count_flatMap]
      have hzero : ∀ d, d ≠ c → d ∈ order →
          (List.count c ∘ fun b => List.replicate (m b - 1) b) d = 0 := by
        intro d hdc hd
        simp [List.count_replicate, hdc]
      rw [List.sum_map_eq_nsmul_single c _ hzero, hone]
      simp
    rw [List.count_append, hone, hcount]
    have hpositive := hm c hc
    omega
end Parikh
