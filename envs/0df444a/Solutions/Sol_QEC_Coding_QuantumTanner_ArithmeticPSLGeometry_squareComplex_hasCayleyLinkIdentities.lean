-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticPSLGeometry.squareComplex_hasCayleyLinkIdentities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:20:55.268741+00:00
-- url     : https://prove2.me/submissions/d05186fd-45cd-4509-991a-274ccab9de82

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionPSLGenerators
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslLeft_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslLeft_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslRight_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_pslRight_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_psl_total_nonconjugacy
import Theorems.Thm_QEC_Coding_QuantumTanner_cayleySquareComplex_hasCayleyLinkIdentities


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLGeometry
open QEC.Coding.ExpanderCodes.QuaternionGenerators
universe v
variable {F K : Type v} [Field F] [Field K] [Fintype F] [Fintype K]
variable (f : F →+* K) (epsilon : F) (r y s i : K)
  (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = f epsilon)
  (hR : r ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
  (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
  (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1)
local notation "L" => pslLeft f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
local notation "R" => pslRight f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
namespace QEC.Coding.QuantumTanner.ArithmeticPSLGeometry
theorem _root_.solution :
    (squareComplex f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI).HasCayleyLinkIdentities := by
  unfold squareComplex
  exact cayleySquareComplex_hasCayleyLinkIdentities L R
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (pslLeft_injective f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslRight_injective f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslLeft_inverse f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (pslRight_inverse f epsilon r y s i hEpsilon hRoot hR hTwoF hY hOne hTwo hRatio hI)
    (fun g a b => psl_total_nonconjugacy f epsilon r y s i hEpsilon hRoot hR hTwoF
      hY hOne hTwo hRatio hI a b g)
end QEC.Coding.QuantumTanner.ArithmeticPSLGeometry
