-- Prove2me | solution 1 for PorteusSS.CK_sS_structure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T02:47:55.139838+00:00
-- url     : https://prove2.me/submissions/b942d5b3-2320-455e-8ebf-b3a155a287f8

import Mathlib
import Definitions.Def_PorteusSS_Functions

set_option autoImplicit false

open MeasureTheory Filter Topology Set PorteusSS in
theorem solution (K : ℝ) (f : ℝ → ℝ) (hf : CK K f) :
    ∃ s S : ℝ, s ≤ S ∧ (∀ x : ℝ, f S ≤ f x) ∧ (∀ x : ℝ, x < s → f S + K < f x) ∧
      AntitoneOn f (Iio s) ∧ (∀ x y : ℝ, s ≤ x → x ≤ y → f x ≤ f y + K) := by
  unfold CK CaK at hf
  obtain ⟨_hK, hcont, _a, _hK', I, hI, _hpc, _hpf, hanti, hnk, hlim⟩ := hf
  obtain ⟨S, hS⟩ := hcont.exists_forall_le hlim
  set T : Set ℝ := {x | f x ≤ f S + K} with hT
  have hTc : IsClosed T := isClosed_le hcont continuous_const
  have hKnn : f S ≤ f S + K := by linarith
  have hSmem : S ∈ T := hKnn
  have hTb : BddBelow T := by
    have h := hlim.eventually_gt_atTop (f S + K)
    obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp h
    refine ht.bddBelow.mono ?_
    intro x hx
    by_contra hxt
    have h2 : f S + K < f x := hts hxt
    have h1 : f x ≤ f S + K := hx
    linarith
  set s := sInf T with hsdef
  have hsT : s ∈ T := hTc.csInf_mem ⟨S, hSmem⟩ hTb
  have hsS : s ≤ S := csInf_le hTb hSmem
  have hlow : ∀ x, x < s → f S + K < f x := by
    intro x hx
    by_contra h0
    have h : f x ≤ f S + K := not_lt.mp h0
    have := csInf_le hTb (show x ∈ T from h)
    linarith
  have hdown : ∀ x y : ℝ, x ≤ y → y ∈ I → x ∈ I := by
    rcases hI with rfl | rfl
    · intro x y hxy hy
      exact lt_of_le_of_lt hxy hy
    · intro x y hxy hy
      exact le_trans hxy hy
  have hsub : Iio s ⊆ I := by
    intro x hx
    by_contra hxI
    have hxs : x < s := hx
    have hSI : S ∉ I := fun h => hxI (hdown x S (le_of_lt (lt_of_lt_of_le hxs hsS)) h)
    have h1 : f x ≤ f S + K := hnk x hxI S hSI (le_of_lt (lt_of_lt_of_le hxs hsS))
    linarith [hlow x hxs]
  refine ⟨s, S, hsS, hS, hlow, hanti.mono hsub, ?_⟩
  intro x y hsx hxy
  by_cases hxI : x ∈ I
  · have hsI : s ∈ I := hdown s x hsx hxI
    have h1 : f x ≤ f s := hanti hsI hxI hsx
    have h2 : f S ≤ f y := hS y
    have h3 : f s ≤ f S + K := hsT
    linarith
  · have hyI : y ∉ I := fun h => hxI (hdown x y hxy h)
    exact hnk x hxI y hyI hxy
