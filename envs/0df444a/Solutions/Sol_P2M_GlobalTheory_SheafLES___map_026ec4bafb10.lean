-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES___map_026ec4bafb10
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:58.166889+00:00
-- url     : https://prove2.me/submissions/7aff21d0-f74a-4ff4-a8a2-8d25581112bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece

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
theorem _root_.solution (n : ℕ) (U : C) (x : Sheaf.H'.{w'} S.X₂ n U) :
    δ hS n U (map S.g n U x) = 0 :=
  (exact₃ hS n U).apply_apply_eq_zero x
end GlobalTheory.SheafLES
