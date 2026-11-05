-- Prove2me | solution 1 for OffloadGNEP.Exist.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:51:19.488029+00:00
-- url     : https://prove2.me/submissions/347e2172-abdf-459a-aa0a-fae731f2d9fc

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting
import Theorems.Thm_OffloadGNEP_Exist_exists_isVISol
import Theorems.Thm_OffloadGNEP_Exist_isGNEPSol_of_isVISol

open OffloadGNEP.Exist

theorem solution {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hne : ∀ u, (Ktil P u).Nonempty) : ∃ xb, IsGNEPSol P xb := by
  obtain ⟨xb, hxb⟩ := exists_isVISol P hA hS hne
  exact ⟨xb, isGNEPSol_of_isVISol P hA hS xb hxb⟩
