-- Prove2me | solution 1 for OffloadGNEP.Mono.isMonotoneOn_of_jacobian_psd
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:53:35.682825+00:00
-- url     : https://prove2.me/submissions/5b4682ff-8369-4461-aab7-91291c01b057

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

set_option autoImplicit false
open OffloadGNEP.Mono

theorem solution {N : ℕ} (S : Set (Fin N → Tier → ℝ))
    (G : (Fin N → Tier → ℝ) → (Fin N → Tier → ℝ))
    (G' : (Fin N → Tier → ℝ) → ((Fin N → Tier → ℝ) →L[ℝ] (Fin N → Tier → ℝ)))
    (hS : Convex ℝ S) (hG : ∀ x ∈ S, HasFDerivAt G (G' x) x)
    (hpsd : ∀ x ∈ S, ∀ h : Fin N → Tier → ℝ, 0 ≤ pair h (G' x h)) :
    IsMonotoneOn S G := by
  intro x hx y hy
  set d : Fin N → Tier → ℝ := y - x with hd
  set γ : ℝ → (Fin N → Tier → ℝ) := fun s => x + s • d with hγ
  have hγS : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ S := fun s hs => hS.add_smul_sub_mem hx hy hs
  set φ : ℝ → ℝ := fun s => pair d (G (γ s)) with hφ
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (pair d (G' (γ s) d)) s := by
    intro s hs
    have h1 : HasDerivAt γ d s := by
      have h0 : HasDerivAt (fun s : ℝ => s • d) d s := by
        simpa using (hasDerivAt_id s).smul_const d
      exact h0.const_add x
    have h2 : HasDerivAt (fun s => G (γ s)) (G' (γ s) d) s :=
      (hG _ (hγS s hs)).comp_hasDerivAt s h1
    unfold pair
    refine HasDerivAt.fun_sum (u := Finset.univ) (fun u _ => ?_)
    refine HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ?_)
    have h3 : HasDerivAt (fun s => G (γ s) u i) ((G' (γ s) d) u i) s :=
      hasDerivAt_pi.mp (hasDerivAt_pi.mp h2 u) i
    exact h3.const_mul (d u i)
  have hmono : MonotoneOn φ (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) ?_
      (f' := fun s => pair d (G' (γ s) d)) ?_ ?_
    · exact fun s hs => (hder s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hder s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact hpsd _ (hγS s ⟨hs.1.le, hs.2.le⟩) d
  have h01 : φ 0 ≤ φ 1 := hmono ⟨le_refl _, zero_le_one⟩ ⟨zero_le_one, le_refl _⟩ zero_le_one
  have e0 : γ 0 = x := by simp [hγ]
  have e1 : γ 1 = y := by simp [hγ, hd]
  have : pair (G y - G x) d = pair d (G y) - pair d (G x) := by
    unfold pair
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.sub_apply]
    ring
  have hfinal : 0 ≤ pair (G y - G x) d := by
    rw [this]
    have := h01
    simp only [hφ, e0, e1] at this
    linarith
  exact hfinal
