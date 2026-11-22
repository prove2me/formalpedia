-- Prove2me | solution 1 for PebblingLean.FiniteProbability.exists_not_of_uniformProbability_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:48.705837+00:00
-- url     : https://prove2.me/submissions/d9854497-885e-4144-afb4-da6165e8a16e

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω ι : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution [Fintype Ω] [Nonempty Ω]
    {P : Ω → Prop} [DecidablePred P]
    (hprob : uniformProbability P < 1) :
    ∃ ω : Ω, ¬ P ω := by
  classical
  by_contra hnone
  have hall : ∀ ω : Ω, P ω := by
    simp_all
  have hfilter :
      (Finset.univ.filter P).card = Fintype.card Ω := by
    simp_all
  have hcard_ne : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hprob_eq : uniformProbability P = 1 := by
    unfold uniformProbability
    simp_all
  linarith
end PebblingLean.FiniteProbability
