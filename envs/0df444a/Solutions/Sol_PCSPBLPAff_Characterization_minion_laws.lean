-- Prove2me | solution 1 for PCSPBLPAff.Characterization.minion_laws
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:36:16.310916+00:00
-- url     : https://prove2.me/submissions/90d3bc6b-c191-4f00-989f-12ae8ef46f90

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

set_option autoImplicit false
open PCSPBLPAff.Characterization

lemma minor_comp_aux {ι κ μ M : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq μ]
    [AddCommMonoid M] (π : ι → κ) (σ : κ → μ) (w : ι → M) (i : μ) :
    ∑ k ∈ Finset.univ.filter (fun k => σ k = i), ∑ j ∈ Finset.univ.filter (fun j => π j = k), w j
      = ∑ j ∈ Finset.univ.filter (fun j => σ (π j) = i), w j := by
  simp only [Finset.sum_filter]
  calc _ = ∑ k, ∑ j, if σ k = i ∧ π j = k then w j else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases h : σ k = i <;> simp [h]
    _ = ∑ j, ∑ k, if σ k = i ∧ π j = k then w j else 0 := Finset.sum_comm
    _ = ∑ j, if σ (π j) = i then w j else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single (π j)]
        · simp
        · intro k _ hk
          have : ¬ (π j = k) := fun h => hk h.symm
          simp [this]
        · simp

theorem solution {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]
    (π : ι → κ) (σ : κ → μ) (w : ι → ℚ) (r : ι → ℤ) (h : IsBLPAffObj w r) :
    IsBLPAffObj (minorQ π w) (minorZ π r) ∧
    minorQ σ (minorQ π w) = minorQ (σ ∘ π) w ∧ minorZ σ (minorZ π r) = minorZ (σ ∘ π) r ∧
    minorQ id w = w ∧ minorZ id r = r := by
  obtain ⟨hw0, hw1, hr1, hwr⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg fun j _ => hw0 j
  · have := Finset.sum_fiberwise (Finset.univ : Finset ι) π w
    simpa [minorQ] using this.trans hw1
  · have := Finset.sum_fiberwise (Finset.univ : Finset ι) π r
    simpa [minorZ] using this.trans hr1
  · intro i hi
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw0 j)).mp hi
    exact Finset.sum_eq_zero fun j hj => hwr j (h0 j hj)
  · funext i
    exact minor_comp_aux π σ w i
  · funext i
    exact minor_comp_aux π σ r i
  · funext i
    simp [minorQ, Finset.sum_filter]
  · funext i
    simp [minorZ, Finset.sum_filter]
