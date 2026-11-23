-- Prove2me | solution 1 for ReciprocityTheory.Coh.connNat_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:33.020878+00:00
-- url     : https://prove2.me/submissions/768ea5b4-dd30-4e93-a31b-eb158e22c15b

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_cls_congr
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : ConnNatStatement.{u} := by
  intro R _ A B C A' B' C' i p i' p' α β γ δ δ' hs hs' hiα hpγ hδ hδ' n x
  obtain ⟨b, a, hc, ha, hba, rfl⟩ := LongExactSequenceMaps.rep i p hs n x
  have hc' : C'.d n (p'.f n (β.f n b)) = 0 := by rw [← hpγ, ← γ.comm, hc, map_zero]
  have hba' : B'.d n (β.f n b) = i'.f (n + 1) (α.f (n + 1) a) := by rw [← β.comm, hba, hiα]
  rw [hδ n b a hc ha hba, LongExactSequenceMaps.H_cls, LongExactSequenceMaps.H_cls, LongExactSequenceMaps.cls_congr C' n _ _ _ hc' (hpγ n b)]
  exact hδ' n (β.f n b) (α.f (n + 1) a) hc' _ hba'
end ReciprocityTheory.Coh
