-- Prove2me | solution 1 for TunnellMap.representativeEdgeKey_eq_orbitEdgeKey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:54.55772+00:00
-- url     : https://prove2.me/submissions/eb85f7de-9391-41eb-b410-aabac14e83c6

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_OrbitRanking
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    (s : BResidual n) (t : AResidual n) :
    representativeEdgeKey s t =
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((aResidualInvolution n hnpos).orbit t) := by
  let BI := bResidualInvolution n
  let AI := aResidualInvolution n hnpos
  let rs := canonicalBResidualRepresentative (BI.orbit s)
  let rt := canonicalAResidualRepresentative hnpos (AI.orbit t)
  have hsOrbit : BI.orbit rs = BI.orbit s := by
    exact BI.orbit_canonicalRepresentative bResidualLexKey
      bResidualLexKey_injective _
  have htOrbit : AI.orbit rt = AI.orbit t := by
    exact AI.orbit_canonicalRepresentative aResidualLexKey
      aResidualLexKey_injective _
  have hs : s = rs ∨ s = negBResidual rs := by
    change s = rs ∨ s = BI.neg rs
    exact BI.orbit_eq_iff.mp hsOrbit
  have ht : t = rt ∨ t = negAResidual rt := by
    change t = rt ∨ t = AI.neg rt
    exact AI.orbit_eq_iff.mp htOrbit
  change representativeEdgeKey s t = representativeEdgeKey rs rt
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · rw [hs, ht]
  · rw [hs, ht]
    exact representativeEdgeKey_neg_target _ _
  · rw [hs, ht]
    exact representativeEdgeKey_neg_source _ _
  · rw [hs, ht, representativeEdgeKey_neg_source,
      representativeEdgeKey_neg_target]
end TunnellMap
