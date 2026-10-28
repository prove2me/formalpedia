-- Prove2me | solution 1 for SideConstrainedDTA.Existence.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:46:15.560623+00:00
-- url     : https://prove2.me/submissions/12026432-2872-4cb6-8e83-f24ebe68c2e9

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open SideConstrainedDTA.Existence

open MeasureTheory Set Filter Topology



theorem solution {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Basic) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (S : (W → ℝ → ℝ) → Prop) (A A' : Corr W) (hs : W → ℝ → ℝ)
    (hcond : ∀ p, ∀ x ∈ A p hs, Measurable x.2.1 → (∀ s, 0 ≤ x.2.1 s) →
      0 < ∫ s in Icc N.t0 N.tf, x.2.1 s →
      ∃ γ' : ℝ → ℝ, (x.1, γ', x.2.2) ∈ A' p hs ∧ Measurable γ' ∧
        (∀ s, 0 ≤ γ' s ∧ γ' s ≤ x.2.1 s) ∧ 0 < ∫ s in Icc N.t0 N.tf, γ' s) :
    IsSCDE N Φ S A' hs → IsSCDE N Φ S A hs := by
  rintro ⟨hS, hA'⟩
  refine ⟨hS, fun p t ht x hx => hA' p t ht x ?_⟩
  refine ⟨hx.1, fun δ hδ ε hε => ?_⟩
  obtain ⟨γ, hγm, hγb, hγs, hγi, hγA⟩ := hx.2 δ hδ ε hε
  obtain ⟨γ', hA'm, hγ'm, hγ'b, hγ'i⟩ :=
    hcond p (x.1, γ, x.2) hγA hγm (fun s => (hγb s).1) hγi
  refine ⟨γ', hγ'm, fun s => ⟨(hγ'b s).1, le_trans (hγ'b s).2 (hγb s).2⟩, ?_, hγ'i, hA'm⟩
  intro s hs'
  have h0 := hγs s hs'
  exact le_antisymm (h0 ▸ (hγ'b s).2) (hγ'b s).1
