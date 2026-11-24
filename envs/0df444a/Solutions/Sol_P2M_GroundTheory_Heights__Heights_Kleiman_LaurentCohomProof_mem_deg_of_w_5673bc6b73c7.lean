-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_deg_of_w_5673bc6b73c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:36.833806+00:00
-- url     : https://prove2.me/submissions/11770046-f45d-4e74-8d15-b3543097afeb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_negSet_131f8e45df3d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
theorem _root_.solution {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {y : Laurent S N}
    (hy : y ∈ wPart S N c J) (hJ : ¬ J ⊆ I.1 → y = 0) : y ∈ laurentDeg S N c I := by
  by_cases h : J ⊆ I.1
  · refine (Finsupp.mem_supported' S _).mpr fun a ha => ?_
    refine (Finsupp.mem_supported' S _).mp hy a fun ⟨hJa, hc⟩ => ha ⟨hc, fun j hj => ?_⟩
    by_contra hneg
    have : j ∈ negSet a := mem_negSet.mpr (by omega)
    rw [hJa] at this
    exact hj (h this)
  · rw [hJ h]; exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.LaurentCohomProof
