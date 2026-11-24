-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_jetExp__59c42dc7203e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:29:59.879194+00:00
-- url     : https://prove2.me/submissions/f149f582-f11e-4911-8d42-6f1aeac7e4de

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_exp
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_neg

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
theorem _root_.solution : JetExp := by
  intro K _ _ R l linv ph h hph hj i
  exact jet_exp h (by rw [map_neg, hph, neg_zero])
    (fun i hi => by rw [jet_neg h]; exact neg_mem (hj i hi)) i
end Formalism.L2.Th1.C
