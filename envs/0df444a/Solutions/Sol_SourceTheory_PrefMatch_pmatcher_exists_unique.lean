-- Prove2me | solution 1 for SourceTheory.PrefMatch.pmatcher_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:26:29.042925+00:00
-- url     : https://prove2.me/submissions/7730f871-8f4c-43bc-96fe-27e46717f686

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.PMatchAux

open SourceTheory.Uniform

/-- A transformation (continuous probability weighting function) has an inverse transformation
on `[0, 1]`. -/
lemma inverse_transformation (w : ℝ → ℝ) (hw : IsTransformation w) :
    ∃ v : ℝ → ℝ, IsTransformation v ∧ ∀ p ∈ Icc (0 : ℝ) 1, v (w p) = p ∧ w (v p) = p := by
  obtain ⟨⟨hmaps, hmono, h0, h1⟩, hcont⟩ := hw
  let f : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun x => ⟨w x, hmaps x.2⟩
  have hf : StrictMono f := fun x y hxy => hmono x.2 y.2 hxy
  have hsurj : Function.Surjective f := by
    rintro ⟨q, hq⟩
    have hq' : q ∈ Icc (w 0) (w 1) := by rw [h0, h1]; exact hq
    obtain ⟨p, hp, hpq⟩ := intermediate_value_Icc zero_le_one hcont hq'
    exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩
  let e := StrictMono.orderIsoOfSurjective f hf hsurj
  have he : ∀ x, (e x : ℝ) = w x := fun x => rfl
  let v : ℝ → ℝ := fun p => if h : p ∈ Icc (0 : ℝ) 1 then (e.symm ⟨p, h⟩ : ℝ) else p
  have hv : ∀ p (h : p ∈ Icc (0 : ℝ) 1), v p = (e.symm ⟨p, h⟩ : ℝ) := fun p h => dif_pos h
  have hvw : ∀ p ∈ Icc (0 : ℝ) 1, v (w p) = p := by
    intro p hp
    rw [hv _ (hmaps hp)]
    have : (⟨w p, hmaps hp⟩ : Icc (0 : ℝ) 1) = e ⟨p, hp⟩ := Subtype.ext (he ⟨p, hp⟩).symm
    rw [this, e.symm_apply_apply]
  have hwv : ∀ p ∈ Icc (0 : ℝ) 1, w (v p) = p := by
    intro p hp
    rw [hv _ hp, ← he, e.apply_symm_apply]
  refine ⟨v, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, fun p hp => ⟨hvw p hp, hwv p hp⟩⟩
  · intro p hp; rw [hv _ hp]; exact (e.symm ⟨p, hp⟩).2
  · intro p hp q hq hpq
    rw [hv _ hp, hv _ hq]
    exact e.symm.strictMono (show (⟨p, hp⟩ : Icc (0 : ℝ) 1) < ⟨q, hq⟩ from hpq)
  · have := hvw 0 ⟨le_rfl, zero_le_one⟩; rwa [h0] at this
  · have := hvw 1 ⟨zero_le_one, le_rfl⟩; rwa [h1] at this
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (Icc (0 : ℝ) 1).domRestrict v = fun x => (e.symm x : ℝ) := by
      funext x; rw [Set.domRestrict_apply, hv _ x.2]
    rw [this]
    exact continuous_subtype_val.comp e.symm.continuous

lemma comp_transformation (v w : ℝ → ℝ) (hv : IsTransformation v) (hw : IsTransformation w) :
    IsTransformation (fun p => v (w p)) := by
  obtain ⟨⟨vmaps, vmono, v0, v1⟩, vcont⟩ := hv
  obtain ⟨⟨wmaps, wmono, w0, w1⟩, wcont⟩ := hw
  refine ⟨⟨vmaps.comp wmaps, vmono.comp wmono wmaps, ?_, ?_⟩, vcont.comp wcont wmaps⟩
  · simp [w0, v0]
  · simp [w1, v1]

end SourceTheory.PMatchAux

open SourceTheory.Uniform SourceTheory.PMatchAux in
theorem solution {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA) :
    ∃ φ : ℝ → ℝ, SourceTheory.Uniform.IsTransformation φ ∧ (∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p)) ∧
      ∀ φ' : ℝ → ℝ, MapsTo φ' (Icc 0 1) (Icc 0 1) → (∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ' p)) →
        ∀ p ∈ Icc (0 : ℝ) 1, φ' p = φ p := by
  obtain ⟨-, -, hwC, hwA⟩ := h2
  obtain ⟨vC, hvC, hvCinv⟩ := inverse_transformation wC hwC.1
  have hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (vC (wA p)) := fun p hp =>
    ((hvCinv (wA p) (hwA.1.1.1 hp)).2).symm
  refine ⟨fun p => vC (wA p), comp_transformation vC wA hvC hwA.1, hφA, ?_⟩
  intro φ' hφ' hφ'A p hp
  have hmem : vC (wA p) ∈ Icc (0 : ℝ) 1 := hvC.1.1 (hwA.1.1.1 hp)
  exact hwC.1.1.2.1.injOn (hφ' hp) hmem ((hφ'A p hp).symm.trans (hφA p hp))
