-- Prove2me | solution 1 for P010.landau_implies_attachment_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:54:32.058412+00:00
-- url     : https://prove2.me/submissions/1d7a5f82-b1e7-4b4f-9b4f-48c258b029a2

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
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
theorem _root_.solution (n : ℕ) (hn : 12 ≤ n)
    (hlandau : pi (n / 2) ≤ 2 * pi (n / 4)) :
    max 1 (((pi (n / 2) - pi (n / 3)) + 1) / 2) ≤
      evenUnitCount n := by
  have htwo : 2 ≤ n / 4 := by omega
  have hpos : 0 < pi (n / 4) := by
    have hh : (n / 4).primesLE.Nonempty :=
      ⟨2, Nat.mem_primesLE.mpr ⟨htwo, by norm_num⟩⟩
    simpa [pi, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_pos.mpr hh)
  have hdiff : pi (n / 2) - pi (n / 3) ≤ 2 * pi (n / 4) :=
    by omega
  unfold evenUnitCount
  omega
end P010
