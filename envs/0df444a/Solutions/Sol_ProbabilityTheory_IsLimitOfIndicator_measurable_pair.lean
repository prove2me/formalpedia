-- Prove2me | solution 1 for ProbabilityTheory.IsLimitOfIndicator.measurable_pair
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:28:01.336176+00:00
-- url     : https://prove2.me/submissions/0517aee8-3f38-4044-ae5a-ee5a47ae14b0

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F000
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
#

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : T → Ω → E} {c : ℝ≥0∞}
  {U : Set T}

section IndicatorProcess

variable {A : Set Ω} [hE : Nonempty E]

end IndicatorProcess

variable [PseudoEMetricSpace E] [hE : Nonempty E]
  [TopologicalSpace T] [SecondCountableTopology T]

theorem _root_.solution
    {T : Type*} [PseudoEMetricSpace T] [SecondCountableTopology T]
    [MeasurableSpace E] [BorelSpace E]
    {Y X Z X' : T → Ω → E} {U₁ U₂ : Set T}
    (hX : ∀ t, Measurable (X t)) (hX' : ∀ t, Measurable (X' t))
    (hX_pair : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X i ω, X' j ω))
    (hY : IsLimitOfIndicator Y X P U₁) (hZ : IsLimitOfIndicator Z X' P U₂)
    (s t : T) :
    Measurable[_, borel (E × E)] (fun ω ↦ (Y s ω, Z t ω)) := by
  classical
  borelize (E × E)
  obtain ⟨A, hA, -, hlim, hext, hout⟩ := hY
  obtain ⟨B, hB, -, hlim', hext', hout'⟩ := hZ
  have hne : ∀ u : T, (comap (Subtype.val : denseCountable T → T) (𝓝 u)).NeBot :=
    fun u => dense_denseCountable.comap_val_nhds_neBot u
  have hc : ∀ (W : T → Ω → E) (C : Set Ω) (V : Set T),
      (∀ t ∈ V, ∀ ω ∈ C, ∃ c, Tendsto (fun t' : denseCountable T ↦ W t' ω)
        (comap Subtype.val (𝓝 t)) (𝓝 c)) →
      ∀ u ∈ V, ∀ ω, ∃ c, Tendsto (fun t' : denseCountable T ↦ indicatorProcess W C t' ω)
        (comap Subtype.val (𝓝 u)) (𝓝 c) := by
    intro W C V hl u hu ω
    by_cases hω : ω ∈ C
    · obtain ⟨c, hc⟩ := hl u hu ω hω
      exact ⟨c, by simpa [indicatorProcess_apply, hω] using hc⟩
    · exact ⟨hE.some, by simp only [indicatorProcess_apply, hω, if_false]; exact tendsto_const_nhds⟩
  have hm : ∀ (W : T → Ω → E) (C : Set Ω) (V : Set T), (∀ t, Measurable (W t)) →
      MeasurableSet C →
      (∀ t ∈ V, ∀ ω ∈ C, ∃ c, Tendsto (fun t' : denseCountable T ↦ W t' ω)
        (comap Subtype.val (𝓝 t)) (𝓝 c)) →
      ∀ u ∈ V, Measurable fun ω ↦ dense_denseCountable.extend
        (fun t' : denseCountable T ↦ indicatorProcess W C t' ω) u := by
    intro W C V hW hC hl u hu
    simp only [Dense.extend, IsDenseInducing.extend]
    exact measurable_limUnder_of_exists_tendsto (f := fun (t' : denseCountable T) ω ↦
      indicatorProcess W C t' ω) (hc W C V hl u hu) (fun i => measurable_indicatorProcess hC hW i)
  by_cases hs : s ∈ U₁ <;> by_cases ht : t ∈ U₂
  · refine Measurable.of_edist_eq_zero (X := fun ω ↦ limUnder
      ((comap (Subtype.val : denseCountable T → T) (𝓝 s)) ×ˢ
        (comap (Subtype.val : denseCountable T → T) (𝓝 t)))
      (fun p : denseCountable T × denseCountable T ↦
        (indicatorProcess X A p.1 ω, indicatorProcess X' B p.2 ω))) ?_ ?_
    · refine measurable_limUnder_of_exists_tendsto (f := fun (p : denseCountable T × denseCountable T) ω ↦
        (indicatorProcess X A p.1 ω, indicatorProcess X' B p.2 ω)) ?_ ?_
      · intro ω
        obtain ⟨c₁, h₁⟩ := hc X A U₁ hlim s hs ω
        obtain ⟨c₂, h₂⟩ := hc X' B U₂ hlim' t ht ω
        refine ⟨(c₁, c₂), ?_⟩
        rw [nhds_prod_eq]
        exact Filter.Tendsto.prodMk (h₁.comp tendsto_fst) (h₂.comp tendsto_snd)
      · intro p
        exact measurable_pair_indicatorProcess hX hX' hX_pair hA hB p.1 p.2
    · intro ω
      have h0 := edist_limUnder_prod_eq_zero (l₁ := comap (Subtype.val : denseCountable T → T) (𝓝 s))
        (l₂ := comap (Subtype.val : denseCountable T → T) (𝓝 t))
        (hc X A U₁ hlim s hs ω) (hc X' B U₂ hlim' t ht ω)
      have h1 : edist (Y s ω, Z t ω)
          (dense_denseCountable.extend (fun t' : denseCountable T ↦ indicatorProcess X A t' ω) s,
           dense_denseCountable.extend (fun t' : denseCountable T ↦ indicatorProcess X' B t' ω) t)
          = 0 := by
        simp only [Prod.edist_eq]
        rw [hext s hs ω, hext' t ht ω, max_self]
      simp only [Dense.extend, IsDenseInducing.extend] at h1
      refine le_antisymm ?_ bot_le
      calc _ ≤ _ := edist_triangle _ _ _
        _ = 0 := by rw [h1, edist_comm, h0, add_zero]
  · refine Measurable.of_edist_eq_zero (X := fun ω ↦ (dense_denseCountable.extend
      (fun t' : denseCountable T ↦ indicatorProcess X A t' ω) s, hE.some)) ?_ ?_
    · exact (continuous_id.prodMk continuous_const : Continuous fun x : E ↦ (x, hE.some)).measurable.comp
        (hm X A U₁ hX hA hlim s hs)
    · intro ω
      simp only [Prod.edist_eq]
      rw [hext s hs ω, hout' t ht ω, max_self]
  · refine Measurable.of_edist_eq_zero (X := fun ω ↦ (hE.some, dense_denseCountable.extend
      (fun t' : denseCountable T ↦ indicatorProcess X' B t' ω) t)) ?_ ?_
    · exact (continuous_const.prodMk continuous_id : Continuous fun x : E ↦ (hE.some, x)).measurable.comp
        (hm X' B U₂ hX' hB hlim' t ht)
    · intro ω
      simp only [Prod.edist_eq]
      rw [hout s hs ω, hext' t ht ω, max_self]
  · refine Measurable.of_edist_eq_zero (X := fun _ ↦ (hE.some, hE.some)) measurable_const ?_
    intro ω
    simp only [Prod.edist_eq]
    rw [hout s hs ω, hout' t ht ω, max_self]

end ProbabilityTheory
