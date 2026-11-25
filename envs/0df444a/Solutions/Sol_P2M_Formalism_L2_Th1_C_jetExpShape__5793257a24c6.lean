-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_jetExpShape__5793257a24c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:23.726765+00:00
-- url     : https://prove2.me/submissions/894ed872-24f2-49bb-9c72-316bb6686701

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_sub
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_exp
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_neg
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_sq
import Theorems.Thm_P2M_Formalism_L2_Th1_C_formalExpLaws__2cc2f6cc9e35


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
theorem _root_.solution : JetExpShape := by
  intro K _ _ R l linv ph h hph hj
  have hq0 : PowerSeries.constantCoeff (PowerSeries.C (jet l ph 2 / 2) * l ^ 2) = 0 := by simp [h.1]
  have h0 : PowerSeries.constantCoeff (ph - PowerSeries.C (jet l ph 2 / 2) * l ^ 2) = 0 := by
    rw [map_sub, hph, hq0, sub_zero]
  refine ⟨mvExp (-(ph - PowerSeries.C (jet l ph 2 / 2) * l ^ 2)), fun i => ?_, ?_⟩
  · refine jet_exp h (by rw [map_neg, h0, neg_zero]) (fun j hj1 => ?_) i
    rw [jet_neg h, jet_sub h, jet_sq h]
    by_cases h2 : j = 2
    · subst h2
      have e : (2 : K) * (jet l ph 2 / 2) = jet l ph 2 := by
        field_simp
      rw [if_pos rfl, e, sub_self, neg_zero]
      exact zero_mem R
    · rw [if_neg h2, sub_zero]
      exact neg_mem (hj j hj1 h2)
  · have e : -ph = -(PowerSeries.C (jet l ph 2 / 2) * l ^ 2) + -(ph - PowerSeries.C (jet l ph 2 / 2) * l ^ 2) := by
      ring
    have hadd := (formalExpLaws' K Unit).2.2.1 (-(PowerSeries.C (jet l ph 2 / 2) * l ^ 2))
      (-(ph - PowerSeries.C (jet l ph 2 / 2) * l ^ 2)) (by rw [map_neg, neg_eq_zero]; exact hq0)
      (by rw [map_neg, neg_eq_zero]; exact h0)
    exact (congrArg mvExp e).trans hadd
end Formalism.L2.Th1.C
