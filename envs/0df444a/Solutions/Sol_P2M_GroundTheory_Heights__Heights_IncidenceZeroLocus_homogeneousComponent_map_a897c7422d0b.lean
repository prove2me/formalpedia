-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_homogeneousComponent_map_a897c7422d0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:03.568204+00:00
-- url     : https://prove2.me/submissions/093434bb-38d8-4e29-9592-b6eeb3344922

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus

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
open GroundTheory.Heights₂.Heights.IncidenceZeroLocus
namespace GroundTheory.Heights₂.Heights.IncidenceZeroLocus
theorem _root_.solution {R S σ : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S)
    (N : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent N (map g p) = map g (homogeneousComponent N p) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.IncidenceZeroLocus
