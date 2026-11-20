-- Prove2me | solution 1 for P010.packLeafClasses_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:51:05.052228+00:00
-- url     : https://prove2.me/submissions/b4af76be-8e45-488d-b41f-8ce75aa41532

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
theorem _root_.solution (core : List ℕ) :
    ∀ leafs : List ℕ,
      (packLeafClasses core leafs).flatten.Perm
        (core ++ leafs.flatMap (fun p => [p, 2 * p])) := by
  intro leafs
  induction leafs using List.twoStepInduction with
  | nil =>
      simp [packLeafClasses]
  | singleton p =>
      simpa [packLeafClasses] using
        (List.perm_append_comm :
          ([p, 2 * p] ++ core).Perm (core ++ [p, 2 * p]))
  | cons_cons p q rest ih =>
      have hswap : ([2 * q, q] : List ℕ).Perm [q, 2 * q] :=
        List.Perm.swap _ _ []
      have hswap' : ([p, 2 * p, 2 * q, q] : List ℕ).Perm
          [p, 2 * p, q, 2 * q] := (hswap.cons (2 * p)).cons p
      cases rest with
      | nil =>
          have hmove : ([p, 2 * p] ++ core).Perm
              (core ++ [p, 2 * p]) := List.perm_append_comm
          have hresult := (hmove.append_right [2 * q, q]).trans
              (hswap.append_left (core ++ [p, 2 * p]))
          simpa [packLeafClasses, List.append_assoc] using hresult
      | cons r rs =>
          have hr := ih
          have hfirst := hswap'.append hr
          have hmove : ([p, 2 * p, q, 2 * q] ++ core).Perm
              (core ++ [p, 2 * p, q, 2 * q]) :=
            List.perm_append_comm
          have hresult := hfirst.trans
            (by simpa [List.append_assoc] using
              hmove.append_right ((r :: rs).flatMap
                (fun t => [t, 2 * t])))
          simpa [packLeafClasses, List.flatMap_cons,
            List.append_assoc] using hresult
end P010
