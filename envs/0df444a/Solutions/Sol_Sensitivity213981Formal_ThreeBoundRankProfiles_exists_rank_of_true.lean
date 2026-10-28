-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankProfiles.exists_rank_of_true
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:41:29.524624+00:00
-- url     : https://prove2.me/submissions/a4cba131-ff9e-4cb1-a21a-a5a7ecfea6bf

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RankProfileBounds
import Definitions.Def_Sensitivity213981Formal_Supplement_MinmaxLocal
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Theorems.Thm_Sensitivity213981Formal_MinmaxLocal_holds_iff_lt_height


namespace Sensitivity213981Formal
section
/-
Unconditional local lemmas for the graded min/max sensitivity transfer.

This file proves actual predicates and actual one-coordinate-flip identities.
It does not assume a sensitivity-transfer theorem or a recursive seed theorem.
The exact rank is defined from the finite nested family, rather than supplied
as an unproved rank oracle.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MinmaxLocal
open scoped Classical

variable {N : ℕ} {X J I : Type}







theorem height_le (F : Fin N → X → Prop) (x : X) : height F x ≤  N := by
  classical
  unfold height
  apply Finset.sup_le
  intro i _
  split_ifs <;> omega



































section ActualFlips
open OAI.Paper320
variable [Fintype I]



















end ActualFlips















end MinmaxLocal










end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact child-rank bounds, derived from the actual nested Boolean family.
These are the local profile inequalities used by the min/max rank oracle. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankProfiles
open OAI.Paper320 ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundNumeric
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]



theorem exists_rank_of_true (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (x : I → Bool) (g : Fin n) (hg : F g x = true) :
    ∃ r : Fin n, RankState F x r ∧ g ≤  r := by
  let Q := fun i : Fin n => fun z : I → Bool => F i z = true
  have hQ : MinmaxLocal.Nested Q := hF
  let h := MinmaxLocal.height Q x
  have hpos : 0 <  h := (Nat.zero_le g.val).trans_lt
    ((MinmaxLocal.holds_iff_lt_height Q hQ x g).1 hg)
  have hle : h ≤  n := MinmaxLocal.height_le Q x
  let r : Fin n := ⟨h-1,by omega⟩
  have hr : RankState F x r := by
    intro i
    change Q i x ↔ i.val ≤  h-1
    rw [MinmaxLocal.holds_iff_lt_height Q hQ x i]
    change i.val <  h ↔ i.val ≤  h-1
    omega
  exact ⟨r,hr,(hr g).1 hg⟩





















end
end ThreeBoundRankProfiles





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I : Type} [Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (x : I → Bool) (g : Fin n) (hg : @Eq.{1} Bool (F g x) Bool.true),
  @Exists.{1} (Fin n) fun (r : Fin n) =>
    And (@Sensitivity213981Formal.ThreeBoundRankProfiles.RankState n I F x r) (@LE.le.{0} (Fin n) (@instLEFin n) g r) := @Sensitivity213981Formal.ThreeBoundRankProfiles.exists_rank_of_true
