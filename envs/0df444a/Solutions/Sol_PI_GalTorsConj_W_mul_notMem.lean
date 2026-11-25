-- Prove2me | solution 1 for PI.GalTorsConj.W.mul_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:46.855349+00:00
-- url     : https://prove2.me/submissions/f1582fd8-8954-48c4-9dfb-a21d45f24371

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
namespace PI.GalTorsConj.W
theorem _root_.solution {L : PeriodPair} {c z : ℂ} {S : Finset ℂ} (hS : IsKerReps L c S)
    (hz : z ∉ L.lattice) (hzP : ∀ P ∈ S, z + P ∉ L.lattice) :
    c * z ∉ L.lattice := by
  intro hcz
  obtain ⟨Q, hQ, hzQ⟩ := hS.2.2 z hcz hz
  have h1 : c * (-Q) ∈ L.lattice := by
    rw [mul_neg]; exact L.lattice.neg_mem (hS.1 Q hQ).1
  have h2 : -Q ∉ L.lattice := fun h => (hS.1 Q hQ).2 (by simpa using L.lattice.neg_mem h)
  obtain ⟨P, hP, hQP⟩ := hS.2.2 (-Q) h1 h2
  apply hzP P hP
  have := L.lattice.sub_mem hzQ hQP
  rwa [show z - Q - (-Q - P) = z + P by ring] at this
end PI.GalTorsConj.W
