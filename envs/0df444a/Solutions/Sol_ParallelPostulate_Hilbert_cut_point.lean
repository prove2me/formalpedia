-- Prove2me | solution 1 for ParallelPostulate.Hilbert.cut_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:20.259595+00:00
-- url     : https://prove2.me/submissions/c13b0728-9343-4fb8-8182-b702d752be07

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
public import Theorems.Thm_ParallelPostulate_Hilbert_cut_point_ordered

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Hilbert
open Pairs HyperbolicPlane
namespace ParallelPostulate.Hilbert
theorem _root_.solution {I S T : Set ℝ} (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hST : ∀ t, t ∈ I ↔ t ∈ S ∨ t ∈ T) (hdisj : ∀ t ∈ S, t ∉ T) (hSne : S.Nonempty)
    (hTne : T.Nonempty) (hS : ∀ x ∈ S, ∀ y ∈ T, ∀ z ∈ T, ¬ StrictBetween y x z)
    (hT : ∀ x ∈ T, ∀ y ∈ S, ∀ z ∈ S, ¬ StrictBetween y x z) :
    ∃! c, c ∈ I ∧ ∀ a ∈ S, ∀ b ∈ T, a ≠ c → b ≠ c → StrictBetween a c b := by
  obtain ⟨s0, hs0⟩ := hSne
  obtain ⟨t0, ht0⟩ := hTne
  have hst0 : s0 ≠ t0 := fun e => hdisj s0 hs0 (e ▸ ht0)
  rcases lt_or_gt_of_ne hst0 with hlt | hgt
  · apply cut_point_ordered hI hST ⟨s0, hs0⟩ ⟨t0, ht0⟩
    intro s hs t ht
    by_contra hts
    have hts' : t < s := lt_of_le_of_ne (not_lt.mp hts) (fun e => hdisj s hs (e ▸ ht))
    have hts0 : t ≠ s0 := fun e => hdisj s0 hs0 (e ▸ ht)
    rcases lt_or_gt_of_ne hts0 with h | h
    · exact hS s0 hs0 t ht t0 ht0 (Or.inl ⟨h, hlt⟩)
    · exact hT t ht s0 hs0 s hs (Or.inl ⟨h, hts'⟩)
  · have hST' : ∀ t, t ∈ I ↔ t ∈ T ∨ t ∈ S := fun t => (hST t).trans or_comm
    have hsep : ∀ t ∈ T, ∀ s ∈ S, t < s := by
      intro t ht s hs
      by_contra hst
      have hst' : s < t := lt_of_le_of_ne (not_lt.mp hst) (fun e => hdisj s hs (e ▸ ht))
      have hts0 : t ≠ s0 := fun e => hdisj s0 hs0 (e ▸ ht)
      rcases lt_or_gt_of_ne hts0 with h | h
      · exact hT t ht s hs s0 hs0 (Or.inl ⟨hst', h⟩)
      · exact hS s0 hs0 t0 ht0 t ht (Or.inl ⟨hgt, h⟩)
    obtain ⟨c, ⟨hcI, hc⟩, huniq⟩ := cut_point_ordered hI hST' ⟨t0, ht0⟩ ⟨s0, hs0⟩ hsep
    have hsymm : ∀ a c b : ℝ, StrictBetween a c b ↔ StrictBetween b c a :=
      fun _ _ _ => or_comm
    refine ⟨c, ⟨hcI, fun a ha b hb hac hbc => (hsymm _ _ _).mpr (hc b hb a ha hbc hac)⟩, ?_⟩
    rintro c' ⟨hc'I, hc'⟩
    exact huniq c' ⟨hc'I, fun b hb a ha hbc hac => (hsymm _ _ _).mpr (hc' a ha b hb hac hbc)⟩
end ParallelPostulate.Hilbert
