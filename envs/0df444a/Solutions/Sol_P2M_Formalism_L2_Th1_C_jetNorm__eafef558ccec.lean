-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_jetNorm__eafef558ccec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:12.799694+00:00
-- url     : https://prove2.me/submissions/a80daa08-2bc7-4799-a980-56933a7fbdbf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_P2M_Formalism_L2_Th1_C_jetExpIntegral__4902d939320a
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_sub
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open JetSubstitutionLemmas
namespace Formalism.L2.Th1.C
theorem _root_.solution : JetNorm := by
  intro K _ _ R l linv ph a b h hl _ hN i hi
  have := jetExpIntegral' K R l (PowerSeries.subst (mulBy l linv a) ph - (a * b) • ph) hl hN i hi
  rw [jet_sub h, jet_mulBy h, jet_smul h] at this
  convert this using 1
  ring
end Formalism.L2.Th1.C
