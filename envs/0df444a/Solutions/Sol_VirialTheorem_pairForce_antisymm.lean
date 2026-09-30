-- Prove2me | solution 1 for VirialTheorem.pairForce_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:29:24.956101+00:00
-- url     : https://prove2.me/submissions/fc313f2f-f515-4027-9e8b-e6b7d9a89d04

import Definitions.Def_virial_theorem_defs
set_option autoImplicit false
open VirialTheorem
private theorem central_gradient (V : ℝ → ℝ) (a b : Space) (hne : a ≠ b)
    (hV : DifferentiableAt ℝ V (dist b a)) :
    gradient (fun y => V (dist y a)) b = (deriv V (dist b a) / dist b a) • (b-a) := by
  have hn : ‖b-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hs := ((hasFDerivAt_id b).sub_const a).norm_sq
  have hroot := hs.sqrt (pow_ne_zero 2 hn)
  have hd : HasFDerivAt (fun y : Space => dist y a)
      (‖b-a‖⁻¹ • innerSL ℝ (b-a)) b := by
    convert! hroot using 1
    · funext y
      simp [dist_eq_norm, Real.sqrt_sq (norm_nonneg (y-a))]
    · ext y
      simp [Real.sqrt_sq (norm_nonneg (b-a))]
      field_simp
      <;> ring
  have hcomp := hV.hasDerivAt.comp_hasFDerivAt b hd
  have hg : HasGradientAt (fun y => V (dist y a))
      ((deriv V (dist b a) / dist b a) • (b-a)) b := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! hcomp using 1
    ext y
    simp [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, dist_eq_norm,
      div_eq_mul_inv, mul_assoc]
  exact hg.gradient

theorem central_force {N : ℕ} (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space)
    (j k : Fin N) (hjk : j ≠ k) (hx : x j ≠ x k)
    (hV : DifferentiableAt ℝ (V j k) (dist (x k) (x j))) :
    pairForce V x j k =
      -(deriv (V j k) (dist (x k) (x j)) / dist (x k) (x j)) • (x k - x j) := by
  rw [pairForce, if_neg hjk, central_gradient (V j k) (x j) (x k) hx hV]
  simp only [neg_smul]

theorem solution {N : ℕ} (V : Fin N → Fin N → ℝ → ℝ) (x : Fin N → Space)
    (hsymm : ∀ j k, V j k = V k j)
    (hx : ∀ j k, j ≠ k → x j ≠ x k)
    (hV : ∀ j k, j ≠ k → DifferentiableAt ℝ (V j k) (dist (x k) (x j))) :
    ∀ j k, pairForce V x j k = -pairForce V x k j := by
  intro j k
  by_cases hjk : j = k
  · subst k
    simp [pairForce]
  rw [central_force V x j k hjk (hx j k hjk) (hV j k hjk),
    central_force V x k j (Ne.symm hjk) (hx k j (Ne.symm hjk)) (hV k j (Ne.symm hjk)),
    hsymm k j, dist_comm (x j) (x k), ← neg_sub (x k) (x j), smul_neg, neg_neg]

