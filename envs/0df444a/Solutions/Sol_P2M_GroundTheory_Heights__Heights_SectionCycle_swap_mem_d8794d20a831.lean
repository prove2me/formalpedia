-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_swap_mem_d8794d20a831
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:12.600588+00:00
-- url     : https://prove2.me/submissions/6db40ef2-d13b-4b66-9948-7090f6868c7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_liftOld_1c75dcc245cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_newCoord_1cebe4ed4869
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_isWeightedHomogeneous_form_fb02de19c0fa

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
variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution (hg : D.IsFormSystem d g) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (i j : Fin (D.size + 1)) :
    D.liftOld (g c i) * X (D.newCoord j) - D.liftOld (g c j) * X (D.newCoord i) ∈ D.extIdeal := by
  rw [AddBlockData.extIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, extMap_newCoord,
    extMap_newCoord, extMap_liftOld D (isWeightedHomogeneous_form D hg c i),
    extMap_liftOld D (isWeightedHomogeneous_form D hg c j), hg.value c hc, hg.value c hc]
  simp only [map_mul]
  ring
end GroundTheory.Heights₂.Heights.SectionCycle
