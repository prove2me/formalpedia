-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.measurable_spectral_bijection
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:34:53.380213+00:00
-- url     : https://prove2.me/submissions/736801ac-1506-4e25-a9b2-403ccc1a949e

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

open Set TopologicalSpace

open scoped Topology

universe u v

open QAlgorithms.Papers.Independent.Intakethird100.P20 in
theorem solution {M : Type u} [Nonempty M] [MeasurableSpace M] :
    (∀ g : M → ℝ, Measurable g → IsMeasurableSpectralFamily (measurableSublevels g) ∧
      spectralCutInfimum (measurableSublevels g) = g) ∧
    (∀ E : ℝ → Set M, IsMeasurableSpectralFamily E →
      Measurable (spectralCutInfimum E) ∧ measurableSublevels (spectralCutInfimum E) = E ∧
      ∀ x : M, {t | x ∈ E t}.Nonempty ∧ BddBelow {t | x ∈ E t}) := by
  refine ⟨fun g hg => ?_, fun E hE => ?_⟩
  · refine ⟨⟨fun t => hg measurableSet_Iic, fun t s hts x hx => le_trans hx hts, fun t => ?_, ?_, ?_⟩, ?_⟩
    · ext x
      simp only [measurableSublevels, mem_preimage, mem_Iic, mem_iInter, Subtype.forall, mem_Ioi]
      constructor
      · intro hx s hs; linarith
      · intro h
        by_contra hc
        push_neg at hc
        have := h ((g x + t) / 2) (by linarith)
        linarith
    · ext x
      simp only [measurableSublevels, mem_iInter, mem_preimage, mem_Iic, mem_empty_iff_false,
        iff_false, not_forall, not_le]
      exact ⟨g x - 1, by linarith⟩
    · ext x
      simp only [measurableSublevels, mem_iUnion, mem_preimage, mem_Iic, mem_univ, iff_true]
      exact ⟨g x, le_rfl⟩
    · funext x
      unfold spectralCutInfimum measurableSublevels
      exact csInf_Ici
  · obtain ⟨hmeas, hmono, hright, hinter, hunion⟩ := hE
    have hne : ∀ x : M, {t | x ∈ E t}.Nonempty := by
      intro x
      have : x ∈ ⋃ t, E t := by rw [hunion]; exact mem_univ x
      obtain ⟨t, ht⟩ := mem_iUnion.mp this
      exact ⟨t, ht⟩
    have hbdd : ∀ x : M, BddBelow {t | x ∈ E t} := by
      intro x
      have : x ∉ ⋂ t, E t := by rw [hinter]; exact Set.notMem_empty x
      rw [mem_iInter] at this
      push_neg at this
      obtain ⟨t0, ht0⟩ := this
      refine ⟨t0, fun t ht => ?_⟩
      by_contra hlt
      push_neg at hlt
      exact ht0 (hmono hlt.le ht)
    have key : ∀ x t, x ∈ E t ↔ spectralCutInfimum E x ≤ t := by
      intro x t
      constructor
      · intro hx
        exact csInf_le (hbdd x) hx
      · intro hle
        rw [hright t, mem_iInter]
        rintro ⟨s, hs⟩
        have hlt : spectralCutInfimum E x < s := lt_of_le_of_lt hle hs
        obtain ⟨u, hu, hus⟩ := exists_lt_of_csInf_lt (hne x) hlt
        exact hmono hus.le hu
    have hsub : measurableSublevels (spectralCutInfimum E) = E := by
      funext t
      ext x
      simp only [measurableSublevels, mem_preimage, mem_Iic]
      exact (key x t).symm
    refine ⟨?_, hsub, fun x => ⟨hne x, hbdd x⟩⟩
    apply measurable_of_Iic
    intro t
    have : spectralCutInfimum E ⁻¹' Iic t = E t := by
      have := congrFun hsub t
      unfold measurableSublevels at this
      exact this
    rw [this]
    exact hmeas t
