-- Prove2me | solution 1 for P010.flatten_even_ended_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:49:13.273781+00:00
-- url     : https://prove2.me/submissions/4e5ca468-8f9c-492e-8dde-77f775bc9abd

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_append_even_ended
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
public import Theorems.Thm_Nat_maxPrimeFac_eq_self_iff
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_maxPrimeFac_pow
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self
attribute [local simp] Nat.maxPrimeFac_eq_self_iff
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.maxPrimeFac_pow
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.one_le_maxPrimeFac_iff
attribute [local simp] Nat.one_lt_maxPrimeFac_iff



set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution :
    ∀ units : List (List ℕ), units ≠ [] →
      (∀ unit ∈ units, NonCoprimeChain unit ∧ EvenEnded unit) →
      NonCoprimeChain units.flatten ∧ EvenEnded units.flatten := by
  intro units
  induction units with
  | nil =>
      intro h
      exact (h rfl).elim
  | cons a rest ih =>
      intro _ hgood
      have ha : NonCoprimeChain a ∧ EvenEnded a :=
        hgood a (by simp)
      cases rest with
      | nil =>
          simpa using ha
      | cons b bs =>
          have hrest : ∀ unit ∈ b :: bs,
              NonCoprimeChain unit ∧ EvenEnded unit := by
            intro unit hu
            exact hgood unit (by simp [hu])
          have htail := ih (by simp) hrest
          simpa only [List.flatten_cons] using
            append_even_ended a (List.flatten (b :: bs))
              ha.1 htail.1 ha.2 htail.2
end P010
