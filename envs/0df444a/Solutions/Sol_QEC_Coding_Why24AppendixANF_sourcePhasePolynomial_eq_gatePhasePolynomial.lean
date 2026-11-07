-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourcePhasePolynomial_eq_gatePhasePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:57:25.40812+00:00
-- url     : https://prove2.me/submissions/87842e08-a6a3-4192-aeac-5f516ccde75c

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_eq_expandedGateCoefficient
import Theorems.Thm_QEC_Coding_Why24AppendixANF_gatePhasePolynomial_apply_expanded
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourcePhasePolynomial_apply


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourcePhasePolynomial = gatePhasePolynomial := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro monomial
  rw [sourcePhasePolynomial_apply, gatePhasePolynomial_apply_expanded,
    sourceCoefficient_eq_expandedGateCoefficient]
end QEC.Coding.Why24AppendixANF
