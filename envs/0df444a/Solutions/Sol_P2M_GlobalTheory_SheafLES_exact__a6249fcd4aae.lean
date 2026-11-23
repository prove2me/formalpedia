-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES_exact__a6249fcd4aae
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:32.191871+00:00
-- url     : https://prove2.me/submissions/15bc7424-3409-4175-8ff7-d07da48db17a

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
include hS
namespace GlobalTheory.SheafLES
theorem _root_.solution (n : ℕ) (U : C) : Function.Exact (map.{w'} S.f n U) (map.{w'} S.g n U) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₂' ((freeYoneda J).obj U) hS n)
end GlobalTheory.SheafLES
