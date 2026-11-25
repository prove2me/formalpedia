-- Prove2me | solution 1 for PositivityTheory.RgJS.EulerProductLogLemmas.summable_maj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:22.265966+00:00
-- url     : https://prove2.me/submissions/2bf363b2-6f83-4e5d-9386-808706885e48

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound
import Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_x_le_half
import Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_x_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.EulerProductLogLemmas
variable {W : Type} {A B : Type} [Fintype A] [Fintype B]
namespace PositivityTheory.RgJS.EulerProductLogLemmas
theorem _root_.solution {q : W → ℕ} {s : ℂ} (hP : Primes q) (hs : 2 < s.re) {C : ℝ} (hC : 0 ≤ C) :
    Summable (maj q s C) := by
  have hx := x_le_half hP.two hs
  have hxn := x_nonneg (q := q) s
  have hgeo : ∀ w, HasSum (fun k : ℕ => C * ((q w : ℝ) ^ (1 - s.re)) ^ (k + 1))
      (C * ((q w : ℝ) ^ (1 - s.re) * (1 - (q w : ℝ) ^ (1 - s.re))⁻¹)) := by
    intro w
    have h := hasSum_geometric_of_lt_one (hxn w) (by linarith [hx w])
    have h2 := (h.mul_left ((q w : ℝ) ^ (1 - s.re))).mul_left C
    have e : (fun k : ℕ => C * ((q w : ℝ) ^ (1 - s.re)) ^ (k + 1)) =
        fun i => C * ((q w : ℝ) ^ (1 - s.re) * ((q w : ℝ) ^ (1 - s.re)) ^ i) := funext fun k => by rw [pow_succ']
    rw [e]; exact h2
  refine (summable_prod_of_nonneg (fun p => mul_nonneg hC (pow_nonneg (hxn p.1) _))).2
    ⟨fun w => (hgeo w).summable, ?_⟩
  have hconv := hP.conv (s.re - 1) (by linarith)
  refine Summable.of_nonneg_of_le (fun w => ?_) (fun w => ?_) (hconv.mul_left (2 * C))
  · rw [(hgeo w).tsum_eq]
    have : 0 < 1 - (q w : ℝ) ^ (1 - s.re) := by linarith [hx w]
    exact mul_nonneg hC (mul_nonneg (hxn w) (inv_nonneg.2 this.le))
  · rw [(hgeo w).tsum_eq]
    have e : (q w : ℝ) ^ (-(s.re - 1)) = (q w : ℝ) ^ (1 - s.re) := by congr 1; ring
    rw [e]
    have h1 : (1 - (q w : ℝ) ^ (1 - s.re))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith [hx w]) (by norm_num)]
      linarith [hx w]
    calc C * ((q w : ℝ) ^ (1 - s.re) * (1 - (q w : ℝ) ^ (1 - s.re))⁻¹)
        ≤ C * ((q w : ℝ) ^ (1 - s.re) * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (hxn w)) hC
      _ = 2 * C * (q w : ℝ) ^ (1 - s.re) := by ring
end PositivityTheory.RgJS.EulerProductLogLemmas
