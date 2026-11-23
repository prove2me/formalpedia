-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:37.040545+00:00
-- url     : https://prove2.me/submissions/42c05a73-8cdb-438f-89c3-8c1a1bfb3cb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
namespace GlobalTheory.SheafLES
theorem _root_.solution (n : ℕ) (U : C) (x : Sheaf.H'.{w'} S.X₃ n U) :
    map S.f (n + 1) U (δ hS n U x) = 0 :=
  (exact₁ hS n U).apply_apply_eq_zero x
end GlobalTheory.SheafLES
