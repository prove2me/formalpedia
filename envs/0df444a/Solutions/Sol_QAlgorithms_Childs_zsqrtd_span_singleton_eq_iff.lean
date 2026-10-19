-- Prove2me | solution 1 for QAlgorithms.Childs.zsqrtd_span_singleton_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:17:00.456991+00:00
-- url     : https://prove2.me/submissions/88712139-ba60-488d-b314-733902c19095

import Definitions.Def_QAlgorithms_Defs_Basic
set_option autoImplicit false

theorem solution (d : ℤ) (hd_sqfree : Squarefree d) (hd : 2 ≤ d)
    (ξ ζ : ℤ√d) :
    Ideal.span {ξ} = Ideal.span {ζ} ↔ ∃ ϵ : ℤ√d, IsUnit ϵ ∧ ξ = ζ * ϵ := by
  have hns : ∀ n : ℤ, d ≠ n * n := by
    intro n hn
    have hu : IsUnit n := hd_sqfree n (by rw [hn])
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> norm_num at hn <;> omega
  letI : NoZeroDivisors (ℤ√d) := ⟨by
    intro a b hab
    have hn : a.norm * b.norm = 0 := by
      rw [← Zsqrtd.norm_mul, hab, Zsqrtd.norm_zero]
    exact (mul_eq_zero.mp hn).imp ((Zsqrtd.norm_eq_zero hns a).mp)
      ((Zsqrtd.norm_eq_zero hns b).mp)⟩
  letI : IsDomain (ℤ√d) := NoZeroDivisors.to_isDomain _
  rw [Ideal.span_singleton_eq_span_singleton, Associated.comm]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, u.isUnit, hu.symm⟩
  · rintro ⟨ϵ, ⟨u, rfl⟩, h⟩
    exact ⟨u, h.symm⟩
