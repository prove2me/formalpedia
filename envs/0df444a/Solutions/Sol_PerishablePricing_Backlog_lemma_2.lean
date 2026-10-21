-- Prove2me | solution 1 for PerishablePricing.Backlog.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:27:33.276666+00:00
-- url     : https://prove2.me/submissions/39571a66-c55f-4a7e-a26f-35d9856aa69a

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

set_option autoImplicit false
open PerishablePricing.Backlog

lemma ppb2_inf {ι κ : Type*} (x x' : ι → ℝ) (y y' : κ → ℝ) (α : ℝ) :
    (Sum.elim x y + α • (1 : ι ⊕ κ → ℝ)) ⊓ Sum.elim x' y' =
      Sum.elim ((x + α • (1 : ι → ℝ)) ⊓ x') ((y + α • (1 : κ → ℝ)) ⊓ y') := by
  funext o; cases o <;> simp

lemma ppb2_sup {ι κ : Type*} (x x' : ι → ℝ) (y y' : κ → ℝ) (α : ℝ) :
    Sum.elim x y ⊔ (Sum.elim x' y' - α • (1 : ι ⊕ κ → ℝ)) =
      Sum.elim (x ⊔ (x' - α • (1 : ι → ℝ))) (y ⊔ (y' - α • (1 : κ → ℝ))) := by
  funext o; cases o <;> simp

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] (𝒜 : Set (ι ⊕ κ → ℝ))
    (f : (ι ⊕ κ → ℝ) → ℝ) (hf : LNatConvexOn 𝒜 f)
    (hbdd : ∀ x : ι → ℝ, (∃ y : κ → ℝ, Sum.elim x y ∈ 𝒜) →
      BddBelow ((fun y => f (Sum.elim x y)) '' {y | Sum.elim x y ∈ 𝒜})) :
    LNatConvexOn {x : ι → ℝ | ∃ y : κ → ℝ, Sum.elim x y ∈ 𝒜}
      (fun x => sInf ((fun y => f (Sum.elim x y)) '' {y | Sum.elim x y ∈ 𝒜})) := by
  obtain ⟨hset, hineq⟩ := hf
  have hproj : LNatConvexSet {x : ι → ℝ | ∃ y : κ → ℝ, Sum.elim x y ∈ 𝒜} := by
    intro u hu v hv α hα
    obtain ⟨yu, hu'⟩ := hu
    obtain ⟨yv, hv'⟩ := hv
    obtain ⟨h1, h2⟩ := hset _ hu' _ hv' α hα
    rw [ppb2_inf] at h1
    rw [ppb2_sup] at h2
    exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  refine ⟨hproj, ?_⟩
  intro u hu v hv α hα
  obtain ⟨hA, hB⟩ := hproj u hu v hv α hα
  let g : (ι → ℝ) → ℝ := fun x => sInf ((fun y => f (Sum.elim x y)) '' {y | Sum.elim x y ∈ 𝒜})
  show g ((u + α • (1 : ι → ℝ)) ⊓ v) + g (u ⊔ (v - α • (1 : ι → ℝ))) ≤ g u + g v
  have key : ∀ yu yv, Sum.elim u yu ∈ 𝒜 → Sum.elim v yv ∈ 𝒜 →
      g ((u + α • (1 : ι → ℝ)) ⊓ v) + g (u ⊔ (v - α • (1 : ι → ℝ))) ≤
        f (Sum.elim u yu) + f (Sum.elim v yv) := by
    intro yu yv hyu hyv
    obtain ⟨h1, h2⟩ := hset _ hyu _ hyv α hα
    have hi := hineq _ hyu _ hyv α hα
    rw [ppb2_inf] at h1 hi
    rw [ppb2_sup] at h2 hi
    have c1 : g ((u + α • (1 : ι → ℝ)) ⊓ v) ≤
        f (Sum.elim ((u + α • (1 : ι → ℝ)) ⊓ v) ((yu + α • (1 : κ → ℝ)) ⊓ yv)) :=
      csInf_le (hbdd _ hA) ⟨_, h1, rfl⟩
    have c2 : g (u ⊔ (v - α • (1 : ι → ℝ))) ≤
        f (Sum.elim (u ⊔ (v - α • (1 : ι → ℝ))) (yu ⊔ (yv - α • (1 : κ → ℝ)))) :=
      csInf_le (hbdd _ hB) ⟨_, h2, rfl⟩
    linarith
  obtain ⟨yu0, hyu0⟩ := hu
  obtain ⟨yv0, hyv0⟩ := hv
  have step : ∀ yv, Sum.elim v yv ∈ 𝒜 →
      g ((u + α • (1 : ι → ℝ)) ⊓ v) + g (u ⊔ (v - α • (1 : ι → ℝ))) - f (Sum.elim v yv) ≤ g u := by
    intro yv hyv
    have hne : ((fun y => f (Sum.elim u y)) '' {y | Sum.elim u y ∈ 𝒜}).Nonempty :=
      ⟨_, Set.mem_image_of_mem _ hyu0⟩
    apply le_csInf hne
    rintro _ ⟨yu, hyu, rfl⟩
    have := key yu yv hyu hyv
    linarith
  have : g ((u + α • (1 : ι → ℝ)) ⊓ v) + g (u ⊔ (v - α • (1 : ι → ℝ))) - g u ≤ g v := by
    have hne : ((fun y => f (Sum.elim v y)) '' {y | Sum.elim v y ∈ 𝒜}).Nonempty :=
      ⟨_, Set.mem_image_of_mem _ hyv0⟩
    apply le_csInf hne
    rintro _ ⟨yv, hyv, rfl⟩
    have := step yv hyv
    linarith
  linarith
