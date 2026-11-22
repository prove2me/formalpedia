-- Prove2me | solution 1 for ParallelPostulate.Hilbert.cut_point_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:19.641626+00:00
-- url     : https://prove2.me/submissions/dfd7f336-1e2f-4f00-896b-9e9a667009c6

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_ne
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Hilbert
open Pairs HyperbolicPlane
namespace ParallelPostulate.Hilbert
theorem _root_.solution {I S T : Set ℝ} (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hST : ∀ t, t ∈ I ↔ t ∈ S ∨ t ∈ T) (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hsep : ∀ s ∈ S, ∀ t ∈ T, s < t) :
    ∃! c, c ∈ I ∧ ∀ a ∈ S, ∀ b ∈ T, a ≠ c → b ≠ c → StrictBetween a c b := by
  obtain ⟨s0, hs0⟩ := hSne
  obtain ⟨t0, ht0⟩ := hTne
  have hbdd : BddAbove S := ⟨t0, fun s hs => (hsep s hs t0 ht0).le⟩
  have hle : ∀ s ∈ S, s ≤ sSup S := fun s hs => le_csSup hbdd hs
  have hge : ∀ t ∈ T, sSup S ≤ t := fun t ht => csSup_le ⟨s0, hs0⟩ fun s hs => (hsep s hs t ht).le
  have hcI : sSup S ∈ I :=
    hI s0 ((hST s0).mpr (Or.inl hs0)) t0 ((hST t0).mpr (Or.inr ht0)) _ (hle s0 hs0) (hge t0 ht0)
  refine ⟨sSup S, ⟨hcI, fun a ha b hb hac hbc =>
    Or.inl ⟨lt_of_le_of_ne (hle a ha) hac, lt_of_le_of_ne (hge b hb) hbc.symm⟩⟩, ?_⟩
  rintro c' ⟨hc'I, hc'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨s, hs, hcs⟩ := exists_lt_of_lt_csSup ⟨s0, hs0⟩ hlt
    have ht0c : c' < t0 := lt_of_lt_of_le hlt (hge t0 ht0)
    rcases hc' s hs t0 ht0 hcs.ne' ht0c.ne' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
  · set m := (sSup S + c') / 2 with hm
    have hm1 : sSup S < m := by linarith
    have hm2 : m < c' := by linarith
    have hmI : m ∈ I := hI _ hcI _ hc'I m hm1.le hm2.le
    have hmT : m ∈ T := by
      rcases (hST m).mp hmI with h | h
      · exact absurd (hle m h) (not_le.mpr hm1)
      · exact h
    have hs0c : s0 < c' := lt_of_le_of_lt (hle s0 hs0) hgt
    rcases hc' s0 hs0 m hmT hs0c.ne hm2.ne with ⟨-, h2⟩ | ⟨-, h2⟩ <;> linarith
end ParallelPostulate.Hilbert
