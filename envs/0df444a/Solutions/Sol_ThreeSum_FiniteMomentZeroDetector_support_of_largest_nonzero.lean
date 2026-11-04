-- Prove2me | solution 1 for ThreeSum.FiniteMomentZeroDetector.support_of_largest_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:10.43308+00:00
-- url     : https://prove2.me/submissions/5dc1282f-bbc4-499d-92ca-93818294292d

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_support_ne_zero
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_eq_zero_of_support_lt

set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.FiniteMomentZeroDetector
theorem _root_.solution {t h d : ℕ} (v w : Fin t → ℤ)
    (hv : Function.Injective v) (hw : ∀ s, w s≠0) (hth : t≤h)
    (_hdh : d≤h) (hd : (hankel v w d).det≠0)
    (hmax : ∀ k≤h, (hankel v w k).det≠0 → k≤d) : d=t := by
  have htd := hmax t hth (det_hankel_support_ne_zero v w hv hw)
  have hdt : d≤t := by
    by_contra hn
    have hz := det_hankel_eq_zero_of_support_lt v w (show t<d by omega)
    exact hd hz
  omega
end ThreeSum.FiniteMomentZeroDetector
