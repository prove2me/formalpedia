-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:47.280411+00:00
-- url     : https://prove2.me/submissions/fa17bbff-c547-4edf-a59b-91136a1850cd

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian_isCoprime____Sq_a9e3a7b07819

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℤ} (hn : n ≠ 0) : W.ΨSq n ≠ 0 := by
  intro h
  have := isCoprime_Φ_ΨSq W n
  rw [h, isCoprime_zero_right] at this
  have hdeg := natDegree_eq_zero_of_isUnit this
  rw [natDegree_Φ] at hdeg
  have : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have := pow_pos this 2
  omega
end GroundTheory.Arith.Abelian
