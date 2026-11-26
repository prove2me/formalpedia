-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.circle_one
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:31.746254+00:00
-- url     : https://prove2.me/submissions/708ed9d3-9333-4f1c-aa1b-a296b4abb940

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubTate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
theorem _root_.solution {z : Circle} (h : ∀ n : ℕ, ‖((z ^ n : Circle) : ℂ) - 1‖ < 1) : z = 1 := by
  first
    | (by_contra hz
       have hz' : (z : ℂ) ≠ 1 := fun h => hz (Subtype.ext h)
       have hn : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
       set θ := Complex.arg (z : ℂ) with hθ
       have hzθ : (z : ℂ) = Complex.exp (θ * Complex.I) := by
         have := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
         rw [hn] at this
         rw [← this]; simp [hθ]
       have hθ0 : θ ≠ 0 := by
         intro h0
         apply hz'
         rw [hzθ, h0]; simp
       have hπ : |θ| ≤ Real.pi := Complex.abs_arg_le_pi _
       have key : ∀ n : ℕ, ‖Complex.exp ((n * |θ| : ℝ) * Complex.I) - 1‖ < 1 := by
         intro n
         have e : ‖((z ^ n : Circle) : ℂ) - 1‖ = ‖Complex.exp ((n * θ : ℝ) * Complex.I) - 1‖ := by
           rw [Circle.coe_pow, hzθ, ← Complex.exp_nat_mul]
           congr 3; push_cast; ring
         have h1 := h n
         rw [e] at h1
         rcases abs_cases θ with ⟨ha, _⟩ | ⟨ha, _⟩
         · rw [ha]; exact h1
         · rw [ha]
           have hc : Complex.exp ((n * -θ : ℝ) * Complex.I) = (starRingEnd ℂ) (Complex.exp ((n * θ : ℝ) * Complex.I)) := by
             rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
             congr 1; push_cast; ring
           rw [hc, ← map_one (starRingEnd ℂ), ← map_sub, Complex.norm_conj]; exact h1
       have hpos : 0 < |θ| := abs_pos.2 hθ0
       have hex : ∃ n : ℕ, Real.pi / 2 ≤ n * |θ| := by
         obtain ⟨n, hn⟩ := exists_nat_ge (Real.pi / 2 / |θ|)
         exact ⟨n, (div_le_iff₀ hpos).1 hn⟩
       classical
       set n := Nat.find hex with hnd
       have hn1 : Real.pi / 2 ≤ n * |θ| := Nat.find_spec hex
       have hn2 : (n:ℝ) * |θ| ≤ 3 * Real.pi / 2 := by
         have hn0 : n ≠ 0 := by
           intro h0
           rw [h0] at hn1
           simp at hn1
           linarith [Real.pi_pos]
         have := Nat.find_min hex (show n - 1 < n by omega)
         rw [not_le] at this
         have hc : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
           rw [Nat.cast_sub (by omega)]; simp
         rw [hc] at this
         nlinarith [Real.pi_pos]
       have hcos : Real.cos (n * |θ|) ≤ 0 :=
         Real.cos_nonpos_of_pi_div_two_le_of_le hn1 (by linarith)
       have h1 := key n
       have h2 : 1 ≤ ‖Complex.exp ((n * |θ| : ℝ) * Complex.I) - 1‖ := by
         have hre : (Complex.exp ((n * |θ| : ℝ) * Complex.I) - 1).re = Real.cos (n * |θ|) - 1 := by
           rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
         have := Complex.abs_re_le_norm (Complex.exp ((n * |θ| : ℝ) * Complex.I) - 1)
         rw [hre] at this
         rw [abs_of_nonpos (by linarith)] at this
         linarith
       linarith)

