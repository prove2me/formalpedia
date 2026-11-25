-- Prove2me | solution 1 for SupConGeometry.ce_l2_profile_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T16:53:51.327815+00:00
-- url     : https://prove2.me/submissions/ef3588be-2da3-438c-bb14-ac31a9d3e9b6

import Mathlib
import Definitions.Def_SupConGeometry_Basic

namespace SupConGeometry

theorem ce_l2_profile_minimizer {K : ℕ} (hK : 2 ≤ K) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    0 < ceL2Radius K ρ lam ∧
    2 * lam * ceL2Radius K ρ lam -
        ρ / (Real.exp ((K : ℝ) * ρ * ceL2Radius K ρ lam / ((K : ℝ) - 1)) + (K : ℝ) - 1) = 0 ∧
    (∀ x : ℝ, 2 * lam * x - ρ / (Real.exp ((K : ℝ) * ρ * x / ((K : ℝ) - 1)) + (K : ℝ) - 1) = 0 →
      x = ceL2Radius K ρ lam) ∧
    (∀ x : ℝ, x ≠ ceL2Radius K ρ lam →
      ceL2Profile K ρ lam (ceL2Radius K ρ lam) < ceL2Profile K ρ lam x) := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  set g : ℝ → ℝ := fun x =>
    2 * lam * x - ρ / (Real.exp ((K : ℝ) * ρ * x / ((K : ℝ) - 1)) + (K : ℝ) - 1) with hg
  have hD : ∀ x : ℝ, 1 < Real.exp ((K : ℝ) * ρ * x / ((K : ℝ) - 1)) + (K : ℝ) - 1 := by
    intro x; have := Real.exp_pos ((K : ℝ) * ρ * x / ((K : ℝ) - 1)); linarith
  have hmono : StrictMono g := by
    intro x y hxy
    simp only [hg]
    have h1 : Real.exp ((K : ℝ) * ρ * x / ((K : ℝ) - 1)) <
        Real.exp ((K : ℝ) * ρ * y / ((K : ℝ) - 1)) := by
      apply Real.exp_lt_exp.2
      apply div_lt_div_of_pos_right _ hK1
      have : 0 < (K : ℝ) * ρ := by positivity
      nlinarith
    have h2 : ρ / (Real.exp ((K : ℝ) * ρ * y / ((K : ℝ) - 1)) + (K : ℝ) - 1) <
        ρ / (Real.exp ((K : ℝ) * ρ * x / ((K : ℝ) - 1)) + (K : ℝ) - 1) :=
      div_lt_div_of_pos_left hρ (by linarith [hD x]) (by linarith)
    nlinarith
  have hcont : Continuous g := by
    simp only [hg]
    exact (continuous_const.mul continuous_id).sub (continuous_const.div (by fun_prop)
      (fun x => by linarith [hD x]))
  have hg0 : g 0 < 0 := by
    simp only [hg]; simp
    have : (0 : ℝ) < 1 + (K : ℝ) - 1 := by linarith
    positivity
  have hg1 : 0 < g (ρ / (2 * lam)) := by
    simp only [hg]
    have hd := hD (ρ / (2 * lam))
    have : ρ / (Real.exp ((K : ℝ) * ρ * (ρ / (2 * lam)) / ((K : ℝ) - 1)) + (K : ℝ) - 1) < ρ :=
      div_lt_self hρ hd
    have e : 2 * lam * (ρ / (2 * lam)) = ρ := by field_simp
    rw [e]; linarith
  obtain ⟨r, ⟨hr0, -⟩, hr⟩ := intermediate_value_Ioo (by positivity : (0 : ℝ) ≤ ρ / (2 * lam))
    hcont.continuousOn ⟨hg0, hg1⟩
  have hR : ceL2Radius K ρ lam = r := by
    show sInf {x | g x = 0} = r
    rw [show {x | g x = 0} = {r} from Set.ext fun x =>
      ⟨fun hx => hmono.injective (hx.trans hr.symm), fun hx => by
        rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hr⟩, csInf_singleton]
  rw [hR]
  refine ⟨hr0, hr, fun x hx => hmono.injective (hx.trans hr.symm), ?_⟩
  -- derivative of the profile
  have hf : ∀ x, HasDerivAt (ceL2Profile K ρ lam) (K * g x) x := by
    intro x
    have hu : HasDerivAt (fun x => 1 + ((K : ℝ) - 1) * Real.exp (-(ρ * ((K : ℝ) / ((K : ℝ) - 1)) * x)))
        (((K : ℝ) - 1) * (Real.exp (-(ρ * ((K : ℝ) / ((K : ℝ) - 1)) * x)) *
          (-(ρ * ((K : ℝ) / ((K : ℝ) - 1)) * 1)))) x :=
      ((((hasDerivAt_id x).const_mul (ρ * ((K : ℝ) / ((K : ℝ) - 1)))).neg).exp.const_mul
        ((K : ℝ) - 1)).const_add 1
    have hupos : 0 < 1 + ((K : ℝ) - 1) * Real.exp (-(ρ * ((K : ℝ) / ((K : ℝ) - 1)) * x)) := by
      positivity
    have hsq : HasDerivAt (fun x => lam * (K : ℝ) * x ^ 2) (lam * (K : ℝ) * (2 * x)) x := by
      have := ((hasDerivAt_id x).pow 2).const_mul (lam * (K : ℝ))
      refine this.congr_deriv ?_
      simp
    have := (hu.log hupos.ne').add hsq
    refine this.congr_deriv ?_
    simp only [hg]
    have e : -(ρ * ((K : ℝ) / ((K : ℝ) - 1)) * x) = -((K : ℝ) * ρ * x / ((K : ℝ) - 1)) := by
      field_simp
    rw [e, Real.exp_neg]
    have hE := Real.exp_pos ((K : ℝ) * ρ * x / ((K : ℝ) - 1))
    have hd := hD x
    field_simp
    ring
  have hfc : Continuous (ceL2Profile K ρ lam) :=
    continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hinc : StrictMonoOn (ceL2Profile K ρ lam) (Set.Ici r) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici r) hfc.continuousOn fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hf x).deriv]
    have : g r < g x := hmono hx
    have hK0 : (0 : ℝ) < K := by linarith
    rw [hr] at this
    positivity
  have hdec : StrictAntiOn (ceL2Profile K ρ lam) (Set.Iic r) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic r) hfc.continuousOn fun x hx => ?_
    rw [interior_Iic] at hx
    rw [(hf x).deriv]
    have : g x < g r := hmono hx
    have hK0 : (0 : ℝ) < K := by linarith
    rw [hr] at this
    nlinarith
  intro x hx
  rcases lt_or_gt_of_ne hx with h | h
  · exact hdec (Set.mem_Iic.2 h.le) (Set.mem_Iic.2 le_rfl) h
  · exact hinc (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h

end SupConGeometry
open SupConGeometry in
theorem solution {K : ℕ} (hK : 2 ≤ K) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    0 < ceL2Radius K ρ lam ∧
    2 * lam * ceL2Radius K ρ lam -
        ρ / (Real.exp ((K : ℝ) * ρ * ceL2Radius K ρ lam / ((K : ℝ) - 1)) + (K : ℝ) - 1) = 0 ∧
    (∀ x : ℝ, 2 * lam * x - ρ / (Real.exp ((K : ℝ) * ρ * x / ((K : ℝ) - 1)) + (K : ℝ) - 1) = 0 →
      x = ceL2Radius K ρ lam) ∧
    (∀ x : ℝ, x ≠ ceL2Radius K ρ lam →
      ceL2Profile K ρ lam (ceL2Radius K ρ lam) < ceL2Profile K ρ lam x) :=
  ce_l2_profile_minimizer hK ρ lam hρ hlam
