-- Prove2me | solution 1 for PositivityTheory.RgJS.Common0Aux.term_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:34.272985+00:00
-- url     : https://prove2.me/submissions/43e4ebf5-a2fb-4cbb-83d4-a65985c32ec3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler
import Theorems.Thm_PositivityTheory_RgJS_Common0Aux_cpow_real

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
open Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux
variable {W X : Type} {d : X → ℕ}
namespace PositivityTheory.RgJS.Common0Aux
theorem _root_.solution (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι]
    (u : ι → X × ℝ) (σ : ℝ) (p : W × ℕ) :
    Pw q A u p.1 p.2 * conj (Pw q A u p.1 p.2) * ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) =
      ((cc q A u p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  have hqpos : (0 : ℝ) < q p.1 := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq p.1))
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, cpow_real]
  have e : ((q p.1 : ℝ) ^ (-σ)) ^ (p.2 + 1) = Real.exp (-(ll q p * σ)) := by
    rw [← Real.rpow_mul_natCast hqpos.le, Real.rpow_def_of_pos hqpos]
    unfold ll
    congr 1
    push_cast
    ring
  rw [← Complex.ofReal_pow, e]
  unfold cc
  push_cast
  ring
end PositivityTheory.RgJS.Common0Aux
