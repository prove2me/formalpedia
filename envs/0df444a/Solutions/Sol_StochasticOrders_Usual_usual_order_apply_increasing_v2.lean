-- Prove2me | solution 1 for StochasticOrders.Usual.usual_order_apply_increasing_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:19:15.325327+00:00
-- url     : https://prove2.me/submissions/b0643e6f-9921-4105-923e-d06c8f23e52b

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

set_option autoImplicit false

open MeasureTheory Set in
/-- Closed rays: `μ{a ≤ X} ≤ ν{a ≤ Y}` from the open-ray order, by continuity from above. -/
theorem soUsIncV2_Ici {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hY : Measurable Y)
    (h : StochasticOrders.Usual.UsualOrder μ ν X Y) (a : ℝ) :
    μ (X ⁻¹' Ici a) ≤ ν (Y ⁻¹' Ici a) := by
  have hI : Y ⁻¹' Ici a = ⋂ n : ℕ, Y ⁻¹' Ioi (a - 1 / ((n : ℝ) + 1)) := by
    ext ω
    simp only [mem_preimage, mem_Ici, mem_iInter, mem_Ioi]
    constructor
    · intro hω n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hω
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      have := hω n
      linarith
  have hanti : Antitone (fun n : ℕ => Y ⁻¹' Ioi (a - 1 / ((n : ℝ) + 1))) := by
    intro m n hmn ω hω
    simp only [mem_preimage, mem_Ioi] at hω ⊢
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  rw [hI, hanti.measure_iInter (fun n => (hY measurableSet_Ioi).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  refine le_iInf fun n => ?_
  calc μ (X ⁻¹' Ici a) ≤ μ (X ⁻¹' Ioi (a - 1 / ((n : ℝ) + 1))) := by
        apply measure_mono
        intro ω hω
        simp only [mem_preimage, mem_Ici, mem_Ioi] at hω ⊢
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    _ ≤ ν (Y ⁻¹' Ioi (a - 1 / ((n : ℝ) + 1))) := h _

open MeasureTheory Set in
/-- Every upper set of `ℝ` is compared correctly. -/
theorem soUsIncV2_upper {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hY : Measurable Y)
    (h : StochasticOrders.Usual.UsualOrder μ ν X Y) (S : Set ℝ) (hS : IsUpperSet S) :
    μ (X ⁻¹' S) ≤ ν (Y ⁻¹' S) := by
  rcases S.eq_empty_or_nonempty with hE | hne
  · simp [hE]
  by_cases hb : BddBelow S
  · set a := sInf S with ha
    have hsub : S ⊆ Ici a := fun s hs => csInf_le hb hs
    have hsup : Ioi a ⊆ S := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx
      exact hS hsx.le hs
    by_cases haS : a ∈ S
    · have : S = Ici a := Subset.antisymm hsub (fun x hx => hS hx haS)
      rw [this]
      exact soUsIncV2_Ici μ ν X Y hY h a
    · have : S = Ioi a := by
        refine Subset.antisymm ?_ hsup
        intro x hx
        have hax : a ≤ x := hsub hx
        rcases hax.lt_or_eq with hlt | heq
        · exact hlt
        · exact absurd (heq ▸ hx) haS
      rw [this]
      exact h a
  · have : S = univ := by
      apply eq_univ_of_forall
      intro x
      rw [not_bddBelow_iff] at hb
      obtain ⟨s, hs, hsx⟩ := hb x
      exact hS hsx.le hs
    rw [this]
    simp

open StochasticOrders.Usual MeasureTheory in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (g : ℝ → ℝ) (hg : Monotone g) (h : UsualOrder μ ν X Y) :
    UsualOrder μ ν (g ∘ X) (g ∘ Y) := by
  intro t
  have hup : IsUpperSet {x : ℝ | t < g x} := fun a b hab ha => lt_of_lt_of_le ha (hg hab)
  exact soUsIncV2_upper μ ν X Y hY h _ hup
