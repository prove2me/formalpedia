-- Prove2me | solution 1 for TunnellMap.BlockGen.recordOf_sign_eq_etaPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:36:38.313802+00:00
-- url     : https://prove2.me/submissions/dcc54b34-0051-4dac-ba96-eb19cfeade9d

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_RecordSign
import Theorems.Thm_TunnellMap_BlockGen_retained_plus_key_lt
import Theorems.Thm_TunnellMap_BlockGen_target_eq_signAct_canonical
import Theorems.Thm_TunnellMap_BlockGen_orbitTargetLift_injective
import Theorems.Thm_TunnellMap_BlockGen_recordOf_sign_eq_one_or_neg_one
import Theorems.Thm_TunnellMap_canonicalTargetLift_eq
import Theorems.Thm_TunnellMap_etaPoint_eq_one_iff
import Theorems.Thm_TunnellMap_etaPoint_signActA
import Theorems.Thm_TunnellMap_isResidualTargetLift_iff


set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) {i : GeneratorIndex}
    (hret : Retained s F i) {o : (aResidualInvolution n hnpos).Orbit}
    (hrt : (recordOf s F i).target = orbitTargetLift hnpos o) :
    (recordOf s F i).sign =
      etaPoint s (canonicalAResidualRepresentative hnpos o) := by
  obtain ⟨t, ht⟩ :=
    (isResidualTargetLift_iff n (targetValue s F i)).mp hret.2.2.2.2.1
  have hrecTarget : (recordOf s F i).target =
      orbitTargetLift hnpos ((aResidualInvolution n hnpos).orbit t) := by
    show canonicalTargetLift (targetValue s F i) = _
    rw [← ht, canonicalTargetLift_eq hnpos t]
    rfl
  have horbit : (aResidualInvolution n hnpos).orbit t = o :=
    orbitTargetLift_injective hnpos (hrecTarget.symm.trans hrt)
  have hdecomp := target_eq_signAct_canonical hnpos F i ht
  rw [horbit] at hdecomp
  have hone : etaPoint s t = 1 :=
    (etaPoint_eq_one_iff s t).mpr (retained_plus_key_lt F hret ht)
  have hsm : (recordOf s F i).sign = 1 ∨ (recordOf s F i).sign = -1 :=
    recordOf_sign_eq_one_or_neg_one F i
  rw [hdecomp, etaPoint_signActA hnpos hsm] at hone
  rcases hsm with hm | hm <;> rw [hm] at hone ⊢ <;> omega
end TunnellMap.BlockGen
