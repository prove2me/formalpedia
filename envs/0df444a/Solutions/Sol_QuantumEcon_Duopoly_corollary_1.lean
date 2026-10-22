-- Prove2me | solution 1 for QuantumEcon.Duopoly.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:26:28.618013+00:00
-- url     : https://prove2.me/submissions/47448acb-bea2-4be1-9daf-50afb67976e3

import Mathlib
import Definitions.Def_QuantumEcon_Duopoly_Setting
set_option autoImplicit false
open QuantumEcon.Duopoly

theorem solution (a c q₁ q₂ : ℝ) (hc : 1 < c) (hca : c < a) (hac : a < c ^ 2) :
    SupplierAudit.Competition.IsCournotNash 1 a c a (c ^ 2) q₁ q₂ ↔
      q₁ = (a - c) / 2 ∧ q₂ = 0 := by
  unfold SupplierAudit.Competition.IsCournotNash SupplierAudit.Competition.cournotPayoff
  constructor
  · rintro ⟨h1, h2, hb1, hb2⟩
    have h20 : q₂ = 0 := by
      have := hb2 0 le_rfl
      by_contra hne
      have hpos : 0 < q₂ := lt_of_le_of_ne h2 (Ne.symm hne)
      nlinarith [mul_pos hpos hpos]
    subst h20
    have := hb1 ((a - c) / 2) (by linarith)
    refine ⟨?_, rfl⟩
    nlinarith [sq_nonneg (q₁ - (a - c) / 2)]
  · rintro ⟨rfl, rfl⟩
    refine ⟨by linarith, le_rfl, ?_, ?_⟩
    · intro x hx
      nlinarith [sq_nonneg (x - (a - c) / 2)]
    · intro x hx
      nlinarith [mul_nonneg hx hx]
