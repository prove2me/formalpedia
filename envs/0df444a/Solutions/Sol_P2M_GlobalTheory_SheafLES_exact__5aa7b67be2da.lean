-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:16.12619+00:00
-- url     : https://prove2.me/submissions/fcd2ea1e-3f4f-4839-8a5e-68dbe092e599

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective

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
theorem _root_.solution (n : ℕ) (U : C) : Function.Exact (δ.{w'} hS n U) (map.{w'} S.f (n + 1) U) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₁' ((freeYoneda J).obj U) hS n (n + 1) rfl)
end GlobalTheory.SheafLES
