-- Prove2me | solution 1 for SpenglerVertical.DoubleMarginalization.lerner_identity
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:36:25.943563+00:00
-- url     : https://prove2.me/submissions/b14339a4-b1d9-4e7c-aecb-84c5cabf37bd

import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

set_option autoImplicit false
open SpenglerVertical.DoubleMarginalization

private theorem profit_first_order (D : ℝ → ℝ) (c p : ℝ)
    (hmax : IsProfitMax D c p) (hdiff : DifferentiableAt ℝ D p) :
    D p + (p - c) * deriv D p = 0 := by
  have hlocal : IsLocalMax (profit D c) p := Filter.Eventually.of_forall hmax
  have hd : HasDerivAt (profit D c) (D p + (p - c) * deriv D p) p := by
    unfold profit
    convert ((hasDerivAt_id p).sub_const c).mul hdiff.hasDerivAt using 1 <;> first | rfl | (simp only [id_eq]; ring) | ring
  exact hlocal.hasDerivAt_eq_zero hd

theorem solution (D : ℝ → ℝ) (c p : ℝ)
    (hmax : IsProfitMax D c p) (hdiff : DifferentiableAt ℝ D p) (hQ : 0 < D p) :
    deriv D p ≠ 0 ∧ p ≠ c ∧
    marginalRevenue D p = c ∧
    elasticity D p = p / (p - marginalRevenue D p) ∧
    elasticity D p = p / (p - c) ∧
    (c ≠ 0 → p = c * (elasticity D p / (elasticity D p - 1))) := by
  have hfoc := profit_first_order D c p hmax hdiff
  have hdne : deriv D p ≠ 0 := by intro h; rw [h] at hfoc; nlinarith
  have hpne : p ≠ c := by intro h; subst p; nlinarith
  have hpc : p - c ≠ 0 := sub_ne_zero.mpr hpne
  have hmr : marginalRevenue D p = c := by
    unfold marginalRevenue
    field_simp [hdne]
    nlinarith
  have hel : elasticity D p = p / (p - c) := by
    unfold elasticity
    field_simp [ne_of_gt hQ, hpc]
    nlinarith [congrArg (fun z : ℝ => p * z) hfoc]
  refine ⟨hdne, hpne, hmr, ?_, hel, ?_⟩
  · rw [hmr]
    exact hel
  · intro hc
    rw [hel]
    have hden : p / (p - c) - 1 ≠ 0 := by
      intro h
      field_simp [hpc] at h
      apply hc
      linarith
    field_simp [hpc, hden, hc]
    ring

