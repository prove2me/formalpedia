-- Prove2me | solution 1 for ULHC.findPath_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:17:10.911259+00:00
-- url     : https://prove2.me/submissions/3043d96b-078d-434d-b0bc-f4b8f70c2d6a

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_crpath_to_path
import Theorems.Thm_ULHC_path_to_crpath
import Theorems.Thm_ULHC_decode_posList
import Theorems.Thm_ULHC_MP_minPath_min
import Theorems.Thm_ULHC_MP_minPath_some
import Theorems.Thm_ULHC_NoTypeIII_at


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) {σ : StripSpec} {L : List StripSpec}
    (h : findPath V G = some (σ, L)) :
    CRPathCA V G σ L ∧ ∀ σ' L', CRPathCA V G σ' L' → wt σ L ≤ wt σ' L' := by
  unfold findPath at h
  cases hm : MP.minPath (candN V G) (gsrc V G) gmid gtgt (gedge V G) gw with
  | none =>
    rw [hm] at h
    cases h
  | some q =>
    rw [hm] at h
    change decode q = some (σ, L) at h
    obtain ⟨hq, hqN⟩ := MP.minPath_some _ _ _ _ _ _ hm
    obtain ⟨σ0, L0, rfl, hP, hw⟩ := path_to_crpath hGV hq hqN
    rw [decode_posList] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨hP, fun σ' L' hP' => ?_⟩
    obtain ⟨hq', hqN', hw'⟩ := crpath_to_path hGV hP'
    rw [← hw, ← hw']
    exact MP.minPath_min _ _ _ _ _ _ hm _ hq' hqN'
end ULHC
