-- Prove2me | solution 1 for RankBasedSDI.LoadBalancing.eq_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:12:20.517426+00:00
-- url     : https://prove2.me/submissions/f843f95c-a92c-4f35-8b7c-9bb29e90737a

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
set_option autoImplicit false
open RankBasedSDI.LoadBalancing

theorem solution {N : ℕ} (b : Fin N → ℝ) (hb : Antitone b) (x y β γ : Fin N → ℝ)
    (hβ : β ∈ driftSet b x) (hγ : γ ∈ driftSet b y) :
    ∑ i, (x i - y i) * (β i - γ i) ≤ 0 := by
  classical
  have rear : ∀ (x : Fin N → ℝ) (π σ : Equiv.Perm (Fin N)), π ∈ permSet x →
      ∑ i, x i * b (π i) ≤ ∑ i, x i * b (σ i) := by
    intro x π σ hπ
    have hav : Antivary x (b ∘ π) := by
      intro i j hij
      by_contra hxx
      push_neg at hxx
      have h1 := hπ i j hxx
      have h2 : b (π j) ≤ b (π i) := hb h1.le
      exact absurd hij (not_lt.mpr h2)
    have := hav.sum_smul_le_sum_smul_comp_perm (σ := σ.trans π.symm)
    simpa [smul_eq_mul] using this
  set F : (Fin N → ℝ) → (Fin N → ℝ) → ℝ := fun β γ => ∑ i, (x i - y i) * (β i - γ i) with hF
  have combL : ∀ β1 β2 γ (s t : ℝ), s + t = 1 →
      F (s • β1 + t • β2) γ = s * F β1 γ + t * F β2 γ := by
    intro β1 β2 γ s t hst
    simp only [hF, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : t = 1 - s := by linarith
    subst this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have combR : ∀ β γ1 γ2 (s t : ℝ), s + t = 1 →
      F β (s • γ1 + t • γ2) = s * F β γ1 + t * F β γ2 := by
    intro β γ1 γ2 s t hst
    simp only [hF, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : t = 1 - s := by linarith
    subst this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have base : ∀ π ∈ permSet x, ∀ σ ∈ permSet y, F (b ∘ π) (b ∘ σ) ≤ 0 := by
    intro π hπ σ hσ
    have h1 := rear x π σ hπ
    have h2 := rear y σ π hσ
    have : F (b ∘ π) (b ∘ σ) = (∑ i, x i * b (π i) - ∑ i, x i * b (σ i)) +
        (∑ i, y i * b (σ i) - ∑ i, y i * b (π i)) := by
      simp only [hF, Function.comp]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    linarith
  have stepA : ∀ σ ∈ permSet y, ∀ β ∈ driftSet b x, F β (b ∘ σ) ≤ 0 := by
    intro σ hσ β hβ
    unfold driftSet at hβ
    refine (convexHull_min (t := {β | F β (b ∘ σ) ≤ 0}) ?_ ?_) hβ
    · rintro _ ⟨π, hπ, rfl⟩
      exact base π hπ σ hσ
    · intro β1 h1 β2 h2 s t hs ht hst
      show F (s • β1 + t • β2) (b ∘ σ) ≤ 0
      rw [combL _ _ _ s t hst]
      have h1' : F β1 (b ∘ σ) ≤ 0 := h1
      have h2' : F β2 (b ∘ σ) ≤ 0 := h2
      nlinarith
  have stepB : ∀ β ∈ driftSet b x, ∀ γ ∈ driftSet b y, F β γ ≤ 0 := by
    intro β hβ γ hγ
    unfold driftSet at hγ
    refine (convexHull_min (t := {γ | F β γ ≤ 0}) ?_ ?_) hγ
    · rintro _ ⟨σ, hσ, rfl⟩
      exact stepA σ hσ β hβ
    · intro γ1 h1 γ2 h2 s t hs ht hst
      show F β (s • γ1 + t • γ2) ≤ 0
      rw [combR _ _ _ s t hst]
      have h1' : F β γ1 ≤ 0 := h1
      have h2' : F β γ2 ≤ 0 := h2
      nlinarith
  exact stepB β hβ γ hγ
