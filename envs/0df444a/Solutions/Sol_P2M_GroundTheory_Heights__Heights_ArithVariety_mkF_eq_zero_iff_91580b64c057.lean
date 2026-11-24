-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:03.710812+00:00
-- url     : https://prove2.me/submissions/e035a561-aa5b-47e5-bd06-6756a38205e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
variable (P : ArithVariety n)
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution (f : MvPolynomial (Coord n) ℤ) : P.mkF f = 0 ↔ f ∈ P.ideal := by
  rw [mkF, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem,
    (IsFractionRing.injective P.CoordRing P.FunField).eq_iff' (map_zero _)]
end GroundTheory.Heights₂.Heights.ArithVariety
