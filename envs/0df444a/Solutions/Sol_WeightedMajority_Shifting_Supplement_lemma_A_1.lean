-- Prove2me | solution 1 for WeightedMajority.Shifting.Supplement.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T15:29:07.19873+00:00
-- url     : https://prove2.me/submissions/9badae3d-047e-42f5-9fa3-5bb1fd67ac6d

import Mathlib

open MeasureTheory

namespace WeightedMajority.Shifting.Supplement
end WeightedMajority.Shifting.Supplement
open WeightedMajority.Shifting.Supplement


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ η : Ω → ℝ) (hξ : Integrable ξ P) (hη : Measurable η)
    (hbinary : ∀ᵐ ω ∂P, η ω = 0 ∨ η ω = 1)
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (hfinite : Set.Finite {s : Set Ω | @MeasurableSet Ω G s}) :
    (fun ω => η ω * P[(fun z => η z * ξ z) | G] ω) =ᵐ[P]
      (fun ω => P[η | G] ω *
        P[(fun z => η z * ξ z) | G ⊔ MeasurableSpace.comap η inferInstance] ω) := by
  set f : Ω → ℝ := fun z => η z * ξ z with hf_def
  set H : MeasurableSpace Ω := G ⊔ MeasurableSpace.comap η inferInstance with hH_def
  have hH : H ≤ mΩ := sup_le hG hη.comap_le
  have hGH : G ≤ H := le_sup_left
  have hbound : ∀ᵐ ω ∂P, ‖η ω‖ ≤ 1 := by
    filter_upwards [hbinary] with ω hω
    rcases hω with h0 | h1
    · simp [h0]
    · simp [h1]
  have hηi : Integrable η P := Integrable.of_bound hη.aestronglyMeasurable 1 hbound
  have hf : Integrable f P := hξ.bdd_mul hη.aestronglyMeasurable hbound
  have hηf : (η * f) =ᵐ[P] f := by
    filter_upwards [hbinary] with ω hω
    rcases hω with h0 | h1
    · simp [hf_def, h0]
    · simp [hf_def, h1]
  have hηH : StronglyMeasurable[H] η :=
    ((comap_measurable η).mono (le_sup_right : _ ≤ H) le_rfl).stronglyMeasurable
  -- the conditional expectation given `H` vanishes where `η = 0`
  have h1 : P[f | H] =ᵐ[P] η * P[f | H] :=
    (condExp_congr_ae hηf).symm.trans
      (condExp_mul_of_stronglyMeasurable_left hηH (hf.congr hηf.symm) hf)
  -- on `{η = 1}` it agrees with a `G`-measurable function
  have hg : ∃ g : Ω → ℝ, Measurable[G] g ∧ ∀ ω, η ω = 1 → (P[f | H]) ω = g ω := by
    let E : Set Ω := {ω | η ω = 1}
    have hle : MeasurableSpace.comap (Subtype.val : E → Ω) H
        ≤ MeasurableSpace.comap (Subtype.val : E → Ω) G := by
      rw [hH_def, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
      have e : η ∘ (Subtype.val : E → Ω) = fun _ => (1 : ℝ) := funext fun x => x.2
      rw [e, MeasurableSpace.comap_const]
      simp
    have hY : Measurable[MeasurableSpace.comap (Subtype.val : E → Ω) G]
        ((P[f | H]) ∘ (Subtype.val : E → Ω)) := by
      have hm : Measurable[H] (P[f | H]) := stronglyMeasurable_condExp.measurable
      exact fun s hs => hle _ ⟨_, hm hs, rfl⟩
    obtain ⟨g, hg, he⟩ := Measurable.exists_eq_measurable_comp (mY := G)
      (f := (Subtype.val : E → Ω)) hY
    exact ⟨g, hg, fun ω hω => congrFun he ⟨ω, hω⟩⟩
  obtain ⟨g, hgm, hge⟩ := hg
  have h2 : P[f | H] =ᵐ[P] g * η := by
    filter_upwards [h1, hbinary] with ω h1ω hω
    rcases hω with h0 | h1'
    · rw [h1ω]; simp [h0]
    · rw [hge ω h1']; simp [h1']
  have h3 : P[f | G] =ᵐ[P] g * P[η | G] := by
    have a : P[P[f | H] | G] =ᵐ[P] P[f | G] := condExp_condExp_of_le hGH hH
    have b : P[P[f | H] | G] =ᵐ[P] P[g * η | G] := condExp_congr_ae h2
    have c : P[g * η | G] =ᵐ[P] g * P[η | G] :=
      condExp_mul_of_stronglyMeasurable_left hgm.stronglyMeasurable
        (integrable_condExp.congr h2) hηi
    exact a.symm.trans (b.trans c)
  filter_upwards [h2, h3] with ω h2ω h3ω
  rw [h3ω, h2ω]
  simp only [Pi.mul_apply]
  ring
