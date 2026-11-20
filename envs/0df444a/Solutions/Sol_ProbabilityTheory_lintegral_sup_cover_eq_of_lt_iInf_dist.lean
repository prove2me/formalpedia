-- Prove2me | solution 1 for ProbabilityTheory.lintegral_sup_cover_eq_of_lt_iInf_dist
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:44:45.324+00:00
-- url     : https://prove2.me/submissions/299a30d2-5459-45cb-be3b-f7d110e6fde9

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal Finset

section Aux

end Aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

section Measurability

variable [MeasurableSpace E] [BorelSpace E]

end Measurability

section FirstTerm

variable {J : Set T}

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}


theorem _root_.solution {C : Set T} {ε : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hJ : J.Finite) (hC : IsCover ε J C) (hC_subset : C ⊆ J)
    (hε_lt : ε < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t) :
    ∫⁻ ω, ⨆ (s : C) (t : { t : C // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      = ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P := by
  have h_le_iff {s t : T} (hs : s ∈ J) (ht : t ∈ J) : edist s t ≤ ε ↔ edist s t = 0 := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    by_contra h_ne_zero
    have h_pos : 0 < edist s t := by positivity
    refine lt_irrefl (ε : ℝ≥0∞) (hε_lt.trans_le ?_)
    refine (iInf_le _ ⟨s, hs⟩).trans <| (iInf_le _ ⟨t, ht⟩).trans ?_
    simp [h_pos, h]
  have hC_zero : IsCover 0 J C := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hC hs
    simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, Set.mem_ofPred_eq] at hst ⊢
    rw [h_le_iff hs (hC_subset ht)] at hst
    exact ⟨t, ht, hst⟩
  apply le_antisymm
  · gcongr with ω
    refine iSup_le fun s ↦ iSup_le fun t ↦ ?_
    exact le_iSup_of_le ⟨s.1, hC_subset s.2⟩ <| le_iSup_of_le ⟨⟨t.1, hC_subset t.1.2⟩, t.2⟩ le_rfl
  · choose f' hf'C hf'_edist using hC_zero
    simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, Set.mem_ofPred_eq] at hf'_edist
    let f : J → C := fun s ↦ ⟨f' s.2, hf'C s.2⟩
    have hf_edist (s : J) : edist s.1 (f s).1 = 0 := hf'_edist s.2
    have hfX_edist (s : J) : ∀ᵐ ω ∂P, edist (X s ω) (X (f s) ω) = 0 := hX.edist_eq_zero (hf_edist s)
    let g : (s : J) → { t : J // edist s t ≤ δ } → { t : C // edist (f s) t ≤ δ } := by
      refine fun s t ↦ ⟨⟨f' t.1.2, hf'C t.1.2⟩, ?_⟩
      let t' : C := ⟨f' t.1.2, hf'C t.1.2⟩
      suffices edist (f s).1 t'.1 ≤ δ from this
      calc edist (f s).1 t'.1
      _ ≤ edist (f s).1 s.1 + edist s t.1 + edist t.1.1 t' := edist_triangle4 _ _ _ _
      _ ≤ δ := by
        rw [edist_comm]
        simpa [hf_edist s, hf'_edist t.1.2, t'] using t.2
    have hg_edist (s : J) (t : { t : J // edist s t ≤ δ }) : edist t.1.1 (g s t).1 = 0 :=
      hf'_edist t.1.2
    have hgX_edist (s : J) (t : { t : J // edist s t ≤ δ }) :
      ∀ᵐ ω ∂P, edist (X t ω) (X (g s t) ω) = 0 := hX.edist_eq_zero (hg_edist s t)
    have h_edist_le (s : J) (t : { t : J // edist s t ≤ δ }) :
        ∀ᵐ ω ∂P, edist (X s ω) (X t ω) ≤ edist (X (f s) ω) (X (g s t) ω) := by
      filter_upwards [hfX_edist s, hgX_edist s t] with ω h₁ h₂
      calc edist (X s ω) (X t ω)
      _ ≤ edist (X s ω) (X (f s) ω) + edist (X (f s) ω) (X (g s t) ω)
          + edist (X (g s t) ω) (X t ω) := edist_triangle4 _ _ _ _
      _ ≤ edist (X (f s) ω) (X (g s t) ω) := by
        rw [edist_comm (X (g s t) ω)]
        simp [h₁, h₂]
    calc ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
    _ ≤ ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }),
        edist (X (f s) ω) (X (g s t) ω) ^ p ∂P := by
      have : Countable J := by simp [hJ.countable]
      have (s : J) : Countable { t : J // edist s t ≤ δ } := Subtype.countable
      simp_rw [← ae_all_iff] at h_edist_le
      refine lintegral_mono_ae ?_
      filter_upwards [h_edist_le] with ω h_edist_le
      gcongr with s t
      · exact hX.p_pos.le
      · exact h_edist_le s t
    _ ≤ ∫⁻ ω, ⨆ (s : C) (t : { t : C // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P := by
      gcongr with ω
      refine iSup_le fun s ↦ iSup_le fun t ↦ ?_
      exact le_iSup_of_le (f s) <| le_iSup_of_le (g s t) le_rfl

