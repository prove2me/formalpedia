-- Prove2me | solution 1 for TunnellMap.BlockGen.target_eq_signAct_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:32:00.202545+00:00
-- url     : https://prove2.me/submissions/8f92e093-9554-46a3-b6cb-299555da60e7

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_RecordSign
import Theorems.Thm_TunnellMap_canonicalTargetLift_eq
import Theorems.Thm_TunnellMap_canonicalTargetLift_spec
import Theorems.Thm_TunnellMap_negTriple_residualTargetLift
import Theorems.Thm_TunnellMap_residualTargetLift_injective
import Theorems.Thm_TunnellMap_signActA_neg_one
import Theorems.Thm_TunnellMap_signActA_one
import Theorems.Thm_TunnellMap_targetLiftSign_mem
import Theorems.Thm_TunnellMap_vsmul_neg_one
import Theorems.Thm_TunnellMap_vsmul_one
attribute [local simp] TunnellMap.signActA_neg_one
attribute [local simp] TunnellMap.signActA_one



set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex)
    {t : AResidual n} (ht : residualTargetLift t = targetValue s F i) :
    t = signActA hnpos ((recordOf s F i).sign)
      (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit t)) := by
  have hspec : residualTargetLift t =
      vsmul (targetLiftSign (residualTargetLift t))
        (canonicalTargetLift (residualTargetLift t)) :=
    canonicalTargetLift_spec _
  have hsign : (recordOf s F i).sign = targetLiftSign (residualTargetLift t) := by
    rw [recordOf, ht]
  have hcanon : canonicalTargetLift (residualTargetLift t) =
      residualTargetLift (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit t)) :=
    canonicalTargetLift_eq hnpos t
  rw [hsign]
  apply residualTargetLift_injective
  rcases targetLiftSign_mem (residualTargetLift t) with hm | hm
  · rw [hm, signActA_one]
    rw [hspec, hm, hcanon, vsmul_one]
  · rw [hm, signActA_neg_one, ← negTriple_residualTargetLift]
    rw [hspec, hm, hcanon, vsmul_neg_one]
end TunnellMap.BlockGen
