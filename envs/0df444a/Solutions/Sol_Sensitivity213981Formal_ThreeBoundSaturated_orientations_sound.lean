-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundSaturated.orientations_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:53:32.742069+00:00
-- url     : https://prove2.me/submissions/759f3aad-dbe7-4aa2-b0c0-5892b6ddf90c

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith


namespace Sensitivity213981Formal
section
/- Budget saturation in the exact executable orientation enumerator. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace ThreeBoundSaturated
open ThreeBoundQ2
open scoped BigOperators
variable {V : Type} [DecidableEq V]

theorem orientations_sound (es : List (V × V)) (ds : List Bool) (b : V → ℕ)
    (h : ds ∈ orientations b es) : ds.length=es.length ∧ ∀ v, outCount es ds v ≤  b v := by
  induction es generalizing ds b with
  | nil =>
      have he : ds=[] := by simpa only [orientations,List.mem_singleton] using h
      subst ds
      exact ⟨rfl,fun _ => Nat.zero_le _⟩
  | cons e es ih =>
      rw [orientations,List.mem_append] at h
      rcases h with h | h
      · by_cases hp : 0< b e.1
        · rw [if_pos hp] at h
          obtain ⟨rest,hr,rfl⟩ := List.mem_map.mp h
          obtain ⟨hlen,hb⟩ := ih rest (spend b e.1) hr
          refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ hlen,?_⟩
          intro v
          have hh := hb v
          by_cases he : v=e.1
          · subst v
            simp only [outCount,Bool.false_eq_true,if_false,ite_true,spend] at hh ⊢
            omega
          · have he' := Ne.symm he
            simpa only [outCount,Bool.false_eq_true,if_false,if_neg he',Nat.zero_add,spend,if_neg he] using hh
        · rw [if_neg hp] at h
          contradiction
      · by_cases hp : 0< b e.2
        · rw [if_pos hp] at h
          obtain ⟨rest,hr,rfl⟩ := List.mem_map.mp h
          obtain ⟨hlen,hb⟩ := ih rest (spend b e.2) hr
          refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ hlen,?_⟩
          intro v
          have hh := hb v
          by_cases he : v=e.2
          · subst v
            simp only [outCount,if_true,ite_true,spend] at hh ⊢
            omega
          · have he' := Ne.symm he
            simpa only [outCount,if_true,if_neg he',Nat.zero_add,spend,if_neg he] using hh
        · rw [if_neg hp] at h
          contradiction

















end ThreeBoundSaturated





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [inst : DecidableEq.{1} V] (es : List.{0} (Prod.{0, 0} V V)) (ds : List.{0} Bool) (b : V → Nat)
  (h :
    @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
      (@Sensitivity213981Formal.ThreeBoundQ2.orientations V inst b es) ds),
  And (@Eq.{1} Nat (@List.length.{0} Bool ds) (@List.length.{0} (Prod.{0, 0} V V) es))
    (∀ (v : V), @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundQ2.outCount V inst es ds v) (b v)) := @Sensitivity213981Formal.ThreeBoundSaturated.orientations_sound
