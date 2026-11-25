-- Prove2me | solution 1 for PositivityTheory.RgJS.Common0Aux.lterm_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:27.093918+00:00
-- url     : https://prove2.me/submissions/25562050-82ed-41e1-948e-7bc5064513e6

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
theorem _root_.solution (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) {α β : Type} [Fintype α] [Fintype β] (a : W → α → ℂ)
    (b : W → β → ℂ) (σ t t' : ℝ) (p : W × ℕ) :
    lterm q a b (((σ + t + t' : ℝ)) : ℂ) p =
      (∑ x, (a p.1 x * (q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1)) *
        conj (∑ y, (b p.1 y * (q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1)) *
        ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) := by
  have hq0 : (q p.1 : ℂ) ≠ 0 := by
    have := hq p.1
    exact_mod_cast (by omega : q p.1 ≠ 0)
  unfold lterm
  have e : (q p.1 : ℂ) ^ (-(((σ + t + t' : ℝ)) : ℂ)) =
      (q p.1 : ℂ) ^ (-(σ : ℂ)) * (q p.1 : ℂ) ^ (-(t : ℂ)) * (q p.1 : ℂ) ^ (-(t' : ℂ)) := by
    rw [← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
    congr 1
    push_cast
    ring
  have hr' : conj ((q p.1 : ℂ) ^ (-(t' : ℂ))) = (q p.1 : ℂ) ^ (-(t' : ℂ)) := by
    rw [cpow_real, Complex.conj_ofReal]
  have h1 : ∑ x, (a p.1 x * (q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1) =
      (∑ x, a p.1 x ^ (p.2 + 1)) * ((q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1) := by
    rw [Finset.sum_mul]
    simp only [mul_pow]
  have h2 : ∑ y, (b p.1 y * (q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1) =
      (∑ y, b p.1 y ^ (p.2 + 1)) * ((q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1) := by
    rw [Finset.sum_mul]
    simp only [mul_pow]
  rw [h1, h2, map_mul, map_pow, hr', e]
  ring
end PositivityTheory.RgJS.Common0Aux
