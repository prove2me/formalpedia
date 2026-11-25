-- Prove2me | solution 1 for PI.GalTorsConj.W.isOpen_veluU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:38.070148+00:00
-- url     : https://prove2.me/submissions/088f7a75-ad4c-49a2-8fd3-9891da535e5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_isOpen_compl


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
theorem _root_.solution (L : PeriodPair) (S : Finset ℂ) : IsOpen (veluU L S) := by
  have e : veluU L S = {z | z ∉ L.lattice} ∩ ⋂ P ∈ S, {z | z + P ∉ L.lattice} := by
    ext z; simp [veluU]
  rw [e]
  refine IsOpen.inter L.isClosed_lattice.isOpen_compl (isOpen_biInter_finset fun P _ => ?_)
  exact L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const)
end PI.GalTorsConj.W
