-- Prove2me | solution 1 for PI.GalTorsConj.W.ZetaDoubling.ev_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:53.255167+00:00
-- url     : https://prove2.me/submissions/17cd78d2-a5b5-4ec5-9571-986d28551776

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
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
open Filter Topology
open PI.GalTorsConj.W.ZetaDoubling
open OriginCoordinatesAdd
namespace PI.GalTorsConj.W.ZetaDoubling
theorem _root_.solution (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) : ∀ᶠ z' in 𝓝 z, z' ∉ L.lattice :=
  L.isClosed_lattice.isOpen_compl.mem_nhds hz
end PI.GalTorsConj.W.ZetaDoubling
