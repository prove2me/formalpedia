-- Prove2me | solution 1 for PositivityTheory.RgJS.EulerProductLogLemmas.lterm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:48.535594+00:00
-- url     : https://prove2.me/submissions/ed5bc714-8fdc-4392-8363-129f66ba0b31

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound

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
theorem _root_.solution (q : W → ℕ) (α : W → A → ℂ) (β : W → B → ℂ) (s : ℂ) (p : W × ℕ) :
    lterm q α β s p = ∑ a, ∑ b, zz q α β s p.1 a b ^ (p.2 + 1) / ((p.2 : ℂ) + 1) := by
  rw [lterm, map_sum, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun (a : A) _ => ?_
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun (b : B) _ => ?_
  rw [zz, map_pow]
  ring
end PositivityTheory.RgJS.EulerProductLogLemmas
