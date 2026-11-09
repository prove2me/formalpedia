-- Prove2me | solution 1 for PriceQualityService.price_step
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:57:17.98084+00:00
-- url     : https://prove2.me/submissions/4b1549c7-ab89-4814-83e7-118c2de71046

import Mathlib
import Definitions.Def_PriceQualityService_netValue
import Definitions.Def_PriceQualityService_optPrice

namespace Aux_PQS_ps

theorem aux (k1 k2 k3 a1 a2 : ℝ) :
    StrictMonoOn (fun x => (x - k1 - k2 - k3) * Real.exp (a1 - x + a2)) (Set.Iic (1 + k3 + k1 + k2)) ∧
      StrictAntiOn (fun x => (x - k1 - k2 - k3) * Real.exp (a1 - x + a2))
        (Set.Ici (1 + k3 + k1 + k2)) ∧
      (∀ x, (x - k1 - k2 - k3) * Real.exp (a1 - x + a2) ≤
        ((1 + k3 + k1 + k2) - k1 - k2 - k3) * Real.exp (a1 - (1 + k3 + k1 + k2) + a2)) ∧
      ((1 + k3 + k1 + k2) - k1 - k2 - k3) * Real.exp (a1 - (1 + k3 + k1 + k2) + a2) =
        Real.exp (a1 - (1 + k3 + k1 + k2) + a2) := by
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun x => (x - k1 - k2 - k3) * Real.exp (a1 - x + a2) :=
    ⟨_, rfl⟩
  have hd : ∀ x, HasDerivAt f (Real.exp (a1 - x + a2) * (1 - (x - k1 - k2 - k3))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x - k1 - k2 - k3) 1 x :=
      (((hasDerivAt_id' x).sub_const k1).sub_const k2).sub_const k3
    have h2 : HasDerivAt (fun x : ℝ => a1 - x + a2) (-1) x :=
      ((hasDerivAt_id' x).const_sub a1).add_const a2
    rw [hf]
    exact (h1.mul h2.exp).congr_deriv (by ring)
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hmono : StrictMonoOn f (Set.Iic (1 + k3 + k1 + k2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic _) hc.continuousOn
    intro x hx
    rw [interior_Iic] at hx
    rw [(hd x).deriv]
    exact mul_pos (Real.exp_pos _) (by simp only [Set.mem_Iio] at hx; linarith)
  have hanti : StrictAntiOn f (Set.Ici (1 + k3 + k1 + k2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici _) hc.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by simp only [Set.mem_Ioi] at hx; linarith)
  have hp : f (1 + k3 + k1 + k2) =
      ((1 + k3 + k1 + k2) - k1 - k2 - k3) * Real.exp (a1 - (1 + k3 + k1 + k2) + a2) := by
    rw [hf]
  have hmax : ∀ x, f x ≤ f (1 + k3 + k1 + k2) := by
    intro x
    rcases le_total x (1 + k3 + k1 + k2) with h | h
    · exact hmono.monotoneOn h (le_refl _ : (1 + k3 + k1 + k2) ≤ _) h
    · exact hanti.antitoneOn (le_refl _ : (1 + k3 + k1 + k2) ≤ _) h h
  rw [hf] at hmono hanti hmax
  refine ⟨hmono, hanti, hmax, ?_⟩
  have : (1 + k3 + k1 + k2) - k1 - k2 - k3 = 1 := by ring
  rw [this, one_mul]

end Aux_PQS_ps

open PriceQualityService in
theorem solution {N : ℕ} (α s a b c q t : Fin N → ℝ) (r : ℝ) (i : Fin N) :
    let h : ℝ → ℝ := fun x =>
      (x - c i * q i ^ 2 - t i * (a i - b i * q i) - r) * Real.exp (α i * q i - x + t i * s i)
    StrictMonoOn h (Set.Iic (optPrice a b c q t r i)) ∧
      StrictAntiOn h (Set.Ici (optPrice a b c q t r i)) ∧
      (∀ x, h x ≤ h (optPrice a b c q t r i)) ∧
      h (optPrice a b c q t r i) = Real.exp (netValue α s a b c q t i - r - 1) := by
  intro h
  have hopt : optPrice a b c q t r i = 1 + r + c i * q i ^ 2 + t i * (a i - b i * q i) := rfl
  obtain ⟨h1, h2, h3, h4⟩ := Aux_PQS_ps.aux (c i * q i ^ 2) (t i * (a i - b i * q i)) r
    (α i * q i) (t i * s i)
  rw [hopt]
  refine ⟨h1, h2, h3, ?_⟩
  show (1 + r + c i * q i ^ 2 + t i * (a i - b i * q i) - c i * q i ^ 2 - t i * (a i - b i * q i) - r) *
      Real.exp (α i * q i - (1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)) + t i * s i) = _
  rw [h4]
  unfold netValue
  congr 1
  ring
