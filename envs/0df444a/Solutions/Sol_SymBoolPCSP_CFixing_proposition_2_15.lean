-- Prove2me | solution 1 for SymBoolPCSP.CFixing.proposition_2_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:49:19.442667+00:00
-- url     : https://prove2.me/submissions/a343d2d0-6e85-4870-8a0e-80181d44087e

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem solution {k L : ℕ} (P : Set (Fin k → Bool)) (hP : IsSymmetricRel P)
    (f : (Fin L → Bool) → Bool) : IsSymmetricRel (image f P) := by
  rintro y ⟨M, hM, rfl⟩ σ
  exact ⟨fun l => M l ∘ σ, fun l => hP _ (hM l) σ, rfl⟩
