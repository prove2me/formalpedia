-- Prove2me | solution 1 for TunnellMap.orthogonalFrame_exists_of_bezout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:08.170996+00:00
-- url     : https://prove2.me/submissions/ac50c427-1570-4aad-9d82-7b178061bbe1

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {p z : Triple} (hz : dot p z = 1) :
    Nonempty (OrthogonalFrame p) := by
  by_cases hg0 : Int.gcd p.x p.y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp hg0
    have hpz : p.z = 1 ∨ p.z = -1 := by
      apply Int.eq_one_or_neg_one_of_mul_eq_one
      simpa [dot, hx, hy] using hz
    rcases hpz with hpz | hpz
    · refine ⟨OrthogonalFrame.mk ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ z ?_ hz⟩
      apply Triple.ext <;> simp [cross, hx, hy, hpz]
    · refine ⟨OrthogonalFrame.mk ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ z ?_ hz⟩
      apply Triple.ext <;> simp [cross, hx, hy, hpz]
  · let G : ℤ := Int.gcd p.x p.y
    let A : ℤ := p.x.gcdA p.y
    let B : ℤ := p.x.gcdB p.y
    let a : ℤ := p.x / G
    let b : ℤ := p.y / G
    have hGne : G ≠ 0 := by
      intro h
      apply hg0
      dsimp [G] at h
      exact_mod_cast h
    have hxDiv : G * a = p.x := by
      rw [mul_comm]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_left p.x p.y)
    have hyDiv : G * b = p.y := by
      rw [mul_comm]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_right p.x p.y)
    have hBezout : G = p.x * A + p.y * B := Int.gcd_eq_gcd_ab p.x p.y
    have hAB : A * a + B * b = 1 := by
      apply mul_left_cancel₀ hGne
      calc
        G * (A * a + B * b) = (G * a) * A + (G * b) * B := by ring
        _ = p.x * A + p.y * B := by rw [hxDiv, hyDiv]
        _ = G := hBezout.symm
        _ = G * 1 := by ring
    let e₁ : Triple := ⟨-b, a, 0⟩
    let e₂ : Triple := ⟨-A * p.z, -B * p.z, G⟩
    refine ⟨OrthogonalFrame.mk e₁ e₂ z ?_ hz⟩
    apply Triple.ext
    · dsimp [e₁, e₂, cross]
      simpa [mul_comm] using hxDiv
    · dsimp [e₁, e₂, cross]
      simpa [mul_comm] using hyDiv
    · dsimp [e₁, e₂, cross]
      calc
        -b * (-B * p.z) - a * (-A * p.z) = b * B * p.z + a * A * p.z := by ring
        _ = (A * a + B * b) * p.z := by ring
        _ = p.z := by rw [hAB]; ring
end TunnellMap
