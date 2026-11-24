-- Prove2me | solution 1 for ULHC.findPath_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:17:12.778977+00:00
-- url     : https://prove2.me/submissions/cfc9bfd4-95ec-4649-bb87-42d2ed526326

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_crpath_to_path
import Theorems.Thm_ULHC_path_to_crpath
import Theorems.Thm_ULHC_decode_posList
import Theorems.Thm_ULHC_MP_minPath_none
import Theorems.Thm_ULHC_MP_minPath_some
import Theorems.Thm_ULHC_NoTypeIII_at


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) (h : findPath V G = none) :
    ∀ σ L, ¬ CRPathCA V G σ L := by
  intro σ L hP
  unfold findPath at h
  cases hm : MP.minPath (candN V G) (gsrc V G) gmid gtgt (gedge V G) gw with
  | none =>
    obtain ⟨hq, hqN, _⟩ := crpath_to_path hGV hP
    exact MP.minPath_none _ _ _ _ _ _ hm _ hq hqN
  | some q =>
    rw [hm] at h
    change decode q = none at h
    obtain ⟨hq, hqN⟩ := MP.minPath_some _ _ _ _ _ _ hm
    obtain ⟨σ0, L0, rfl, _, _⟩ := path_to_crpath hGV hq hqN
    rw [decode_posList] at h
    cases h
end ULHC
