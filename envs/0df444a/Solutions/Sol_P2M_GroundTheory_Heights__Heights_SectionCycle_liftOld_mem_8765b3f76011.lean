-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_mem_8765b3f76011
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:12:53.439593+00:00
-- url     : https://prove2.me/submissions/e3386f19-fd98-4941-b655-06b4dbadb486

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_1c75dcc245cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution {p : MvPolynomial (Coord n) ℤ} (hp : p ∈ P.ideal) : D.liftOld p ∈ D.extIdeal := by
  rw [AddBlockData.extIdeal, RingHom.mem_ker,
    ← finsum_weightedHomogeneousComponent (w := coordDeg n) (φ := p),
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p), map_sum, map_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [extMap_liftOld D (weightedHomogeneousComponent_isWeightedHomogeneous m p),
    (P.mkF_eq_zero_iff _).mpr (P.homogeneous p hp m), map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.SectionCycle
