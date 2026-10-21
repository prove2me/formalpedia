-- Prove2me | solution 1 for PerishablePricing.Backlog.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:22:45.580137+00:00
-- url     : https://prove2.me/submissions/f86d0088-3bb2-4eef-a940-59d3841409e4

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

set_option autoImplicit false
open PerishablePricing.Backlog

theorem solution {ι : Type*} [Fintype ι] (D : Set (Option ι → ℝ)) (g : (Option ι → ℝ) → ℝ)
    (hg : LNatConvexOn D g) :
    let argmin : (ι → ℝ) → Set ℝ := fun x =>
      {ξ | (fun o : Option ι => o.elim ξ x) ∈ D ∧
        ∀ ξ', (fun o : Option ι => o.elim ξ' x) ∈ D →
          g (fun o => o.elim ξ x) ≤ g (fun o => o.elim ξ' x)}
    (∀ x x' : ι → ℝ, ∀ ξ ξ' : ℝ, x ≤ x' → IsGreatest (argmin x) ξ →
        IsGreatest (argmin x') ξ' → ξ ≤ ξ') ∧
      (∀ x : ι → ℝ, ∀ ω ξ ξ' : ℝ, 0 < ω → IsGreatest (argmin x) ξ →
        IsGreatest (argmin (x + ω • (1 : ι → ℝ))) ξ' → ξ' ≤ ξ + ω) := by
  intro argmin
  obtain ⟨hset, hineq⟩ := hg
  constructor
  · intro x x' ξ ξ' hxx ⟨hξ, hξmax⟩ ⟨hξ', hξ'max⟩
    have hu : (fun o : Option ι => o.elim ξ' x') ∈ D := hξ'.1
    have hv : (fun o : Option ι => o.elim ξ x) ∈ D := hξ.1
    obtain ⟨hmem1, hmem2⟩ := hset _ hu _ hv 0 le_rfl
    have key := hineq _ hu _ hv 0 le_rfl
    have e1 : ((fun o : Option ι => o.elim ξ' x') + (0:ℝ) • (1 : Option ι → ℝ)) ⊓ (fun o : Option ι => o.elim ξ x)
        = fun o : Option ι => o.elim (min ξ' ξ) x := by
      funext o; cases o with
      | none => simp
      | some i => simp [min_eq_right (hxx i)]
    have e2 : (fun o : Option ι => o.elim ξ' x') ⊔ ((fun o : Option ι => o.elim ξ x) - (0:ℝ) • (1 : Option ι → ℝ))
        = fun o : Option ι => o.elim (max ξ' ξ) x' := by
      funext o; cases o with
      | none => simp
      | some i => simp [max_eq_left (hxx i)]
    rw [e1, e2] at key
    rw [e1] at hmem1
    rw [e2] at hmem2
    have h1 := hξ.2 _ hmem1
    have h3 : g (fun o : Option ι => o.elim (max ξ' ξ) x') ≤ g (fun o : Option ι => o.elim ξ' x') := by linarith
    have hmax : max ξ' ξ ∈ argmin x' := by
      refine ⟨hmem2, ?_⟩
      intro ζ hζ
      have := hξ'.2 ζ hζ
      show g (fun o => o.elim (max ξ' ξ) x') ≤ g (fun o => o.elim ζ x')
      linarith
    have := hξ'max hmax
    exact le_trans (le_max_right _ _) this
  · intro x ω ξ ξ' hω ⟨hξ, hξmax⟩ ⟨hξ', hξ'max⟩
    have hu : (fun o : Option ι => o.elim ξ x) ∈ D := hξ.1
    have hv : (fun o : Option ι => o.elim ξ' (x + ω • (1 : ι → ℝ))) ∈ D := hξ'.1
    obtain ⟨hmem1, hmem2⟩ := hset _ hu _ hv ω hω.le
    have key := hineq _ hu _ hv ω hω.le
    have e1 : ((fun o : Option ι => o.elim ξ x) + ω • (1 : Option ι → ℝ)) ⊓ (fun o : Option ι => o.elim ξ' (x + ω • (1 : ι → ℝ)))
        = fun o : Option ι => o.elim (min (ξ + ω) ξ') (x + ω • (1 : ι → ℝ)) := by
      funext o; cases o with
      | none => simp
      | some i => simp
    have e2 : (fun o : Option ι => o.elim ξ x) ⊔ ((fun o : Option ι => o.elim ξ' (x + ω • (1 : ι → ℝ))) - ω • (1 : Option ι → ℝ))
        = fun o : Option ι => o.elim (max ξ (ξ' - ω)) x := by
      funext o; cases o with
      | none => simp
      | some i => simp
    rw [e1, e2] at key
    rw [e1] at hmem1
    rw [e2] at hmem2
    have h1 := hξ'.2 _ hmem1
    have h3 : g (fun o : Option ι => o.elim (max ξ (ξ' - ω)) x) ≤ g (fun o : Option ι => o.elim ξ x) := by linarith
    have hmax : max ξ (ξ' - ω) ∈ argmin x := by
      refine ⟨hmem2, ?_⟩
      intro ζ hζ
      have := hξ.2 ζ hζ
      show g (fun o => o.elim (max ξ (ξ' - ω)) x) ≤ g (fun o => o.elim ζ x)
      linarith
    have := hξmax hmax
    have := le_trans (le_max_right _ _) this
    linarith
