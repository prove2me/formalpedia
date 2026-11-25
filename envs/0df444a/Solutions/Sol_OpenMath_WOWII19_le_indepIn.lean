-- Prove2me | solution 1 for OpenMath.WOWII19.le_indepIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:38:30.936348+00:00
-- url     : https://prove2.me/submissions/0fc58b18-ca21-491c-ae1d-d9df0681b0b1

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace OpenMath.WOWII19
theorem _root_.solution {G : SimpleGraph α} {T s : Finset α} (hsT : s ⊆ T)
    (hs : (s : Set α).Pairwise fun x y => ¬ G.Adj x y) : s.card ≤ indepIn G T := by
  classical
  unfold indepIn
  have hmem : s ∈ T.powerset.filter (fun s : Finset α => (↑s : Set α).Pairwise
      fun x y => ¬ G.Adj x y) := mem_filter.mpr ⟨mem_powerset.mpr hsT, hs⟩
  convert le_sup (f := card) hmem
end OpenMath.WOWII19
