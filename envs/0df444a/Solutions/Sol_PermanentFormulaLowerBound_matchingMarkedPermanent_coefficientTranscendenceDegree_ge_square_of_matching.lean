-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_coefficientTranscendenceDegree_ge_square_of_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/deb83850-5b52-4615-a21f-70c62eeeb925

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_bitCoefficient_algebraicIndependent
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_square_of_matching_of_algebraicIndependent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n ell m : ℕ} (hn : n = (ell + ell) + m)
    (d : (Fin ell ⊕ Fin ell) ↪ Fin n × Fin n)
    (hrows : Function.Injective (fun y => (d y).1))
    (hcols : Function.Injective (fun y => (d y).2))
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    ((m * m : ℕ) : Cardinal) ≤
      coefficientTranscendenceDegree (matchingMarkedPermanent d) :=
  matchingMarkedPermanent_square_of_matching_of_algebraicIndependent
    hn d hrows hcols
    (matchingMarkedPermanent_bitCoefficient_algebraicIndependent hm hroom)
end PermanentFormulaLowerBound
