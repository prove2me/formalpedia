-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.det_re_le_of_sub_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:33.507857+00:00
-- url     : https://prove2.me/submissions/15260ec2-2834-4825-945c-d16135dc357c

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_gramSt_det_re_le_of_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {n : ℕ} {G H : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re :=
  gramSt_det_re_le_of_sub hG hGH
end ReciprocityTheory.GeometryOfNumbersTheory
