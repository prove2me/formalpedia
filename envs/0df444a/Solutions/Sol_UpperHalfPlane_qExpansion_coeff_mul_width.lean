-- Prove2me | solution 1 for UpperHalfPlane.qExpansion_coeff_mul_width
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d36e4570-d95c-553c-a699-ced78bb65b8c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_qExpansion_coeff_mul_width

set_option autoImplicit false

noncomputable section

namespace WidthChange

open UpperHalfPlane Filter Function
open scoped Real Topology Manifold

structure FnWrap where

  toFun : ℍ → ℂ

scoped instance : FunLike FnWrap ℍ ℂ where
  coe := FnWrap.toFun
  coe_injective := by rintro ⟨f⟩ ⟨g⟩ h; congr

theorem qParam_mul_width_pow {h₀ : ℝ} (hh₀ : 0 < h₀) {m' : ℕ} (hm' : 0 < m') (z : ℂ) :
    Periodic.qParam ((m' : ℝ) * h₀) z ^ m' = Periodic.qParam h₀ z := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have h1 : (h₀ : ℂ) ≠ 0 := by exact_mod_cast hh₀.ne'
  have h2 : (m' : ℂ) ≠ 0 := by exact_mod_cast hm'.ne'
  push_cast
  field_simp

theorem main (f : ℍ → ℂ) (h₀ : ℝ) (hh₀ : 0 < h₀)
    (hper : Periodic (f ∘ UpperHalfPlane.ofComplex) h₀)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : IsBoundedAtImInfty f)
    (m' : ℕ) (hm' : 0 < m') (i : ℕ) :
    PowerSeries.coeff i (qExpansion ((m' : ℝ) * h₀) f) =
      if m' ∣ i then PowerSeries.coeff (i / m') (qExpansion h₀ f) else 0 := by
  have hper' : Periodic (f ∘ UpperHalfPlane.ofComplex) (Complex.ofReal ((m' : ℝ) * h₀)) := by
    have e : Complex.ofReal ((m' : ℝ) * h₀) = (m' : ℕ) * (h₀ : ℂ) := by push_cast; ring
    rw [e]
    exact hper.nat_mul m'
  have hh : 0 < (m' : ℝ) * h₀ := by positivity
  let F : FnWrap := ⟨f⟩
  let a : ℕ → ℂ := fun n => PowerSeries.coeff n (qExpansion h₀ f)
  have hinj : Injective (fun n : ℕ => m' * n) := mul_right_injective₀ hm'.ne'
  let c : ℕ → ℂ := extend (fun n : ℕ => m' * n) a 0
  have hnot : ∀ i : ℕ, ¬ m' ∣ i → ¬ ∃ n, (fun n : ℕ => m' * n) n = i :=
    fun i hdiv ⟨n, hn⟩ => hdiv ⟨n, hn.symm⟩
  have hc : ∀ i, c i = if m' ∣ i then a (i / m') else 0 := by
    intro i
    split_ifs with hdiv
    · obtain ⟨n, rfl⟩ := hdiv
      show extend (fun n : ℕ => m' * n) a 0 (m' * n) = _
      rw [hinj.extend_apply, Nat.mul_div_cancel_left _ hm']
    · show extend (fun n : ℕ => m' * n) a 0 i = 0
      rw [extend_apply' _ _ _ (hnot i hdiv), Pi.zero_apply]
  have hsum : ∀ τ : ℍ, HasSum (fun i => c i • Periodic.qParam ((m' : ℝ) * h₀) τ ^ i) (F τ) := by
    intro τ
    have h1 := hasSum_qExpansion hh₀ hper hhol hbdd τ
    have heq : (fun i => c i • Periodic.qParam ((m' : ℝ) * h₀) τ ^ i) =
        extend (fun n : ℕ => m' * n) (fun n => a n • Periodic.qParam h₀ τ ^ n) 0 := by
      funext i
      rw [hc]
      split_ifs with hdiv
      · obtain ⟨n, rfl⟩ := hdiv
        rw [hinj.extend_apply, Nat.mul_div_cancel_left _ hm', pow_mul, qParam_mul_width_pow hh₀ hm']
      · rw [extend_apply' _ _ _ (hnot i hdiv), Pi.zero_apply, zero_smul]
    rw [heq, hasSum_extend_zero hinj]
    exact h1
  have huniq := qExpansion_coeff_unique F hh (analyticAt_cuspFunction_zero hh hper' hhol hbdd) hsum i

  change c i = PowerSeries.coeff i (qExpansion ((m' : ℝ) * h₀) f) at huniq
  rw [← huniq, hc]

end WidthChange
p2m_reactivate "P2MW.S_UpperHalfPlane_qExpansion_coeff_mul_width.WidthChange"

end
p2m_reactivate "P2MW.S_UpperHalfPlane_qExpansion_coeff_mul_width.WidthChange"

open UpperHalfPlane in
open scoped Manifold in
theorem solution (f : UpperHalfPlane → ℂ) (h₀ : ℝ) (hh₀ : 0 < h₀)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) h₀)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (m' : ℕ) (hm' : 0 < m') (i : ℕ) :
    PowerSeries.coeff i (UpperHalfPlane.qExpansion ((m' : ℝ) * h₀) f) =
      if m' ∣ i then PowerSeries.coeff (i / m') (UpperHalfPlane.qExpansion h₀ f) else 0 :=
  WidthChange.main f h₀ hh₀ hper hhol hbdd m' hm' i

#print axioms solution

end S_UpperHalfPlane_qExpansion_coeff_mul_width
end P2MW
export P2MW.S_UpperHalfPlane_qExpansion_coeff_mul_width (solution)
