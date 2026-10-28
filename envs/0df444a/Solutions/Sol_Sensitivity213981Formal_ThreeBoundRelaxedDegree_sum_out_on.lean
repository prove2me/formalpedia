-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRelaxedDegree.sum_out_on
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:03:14.661997+00:00
-- url     : https://prove2.me/submissions/73c49cff-068d-41a5-a684-5df04f50aa4e

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedDegreeNecessity
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
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRelaxedDegree_row_total


namespace Sensitivity213981Formal
section
/- Necessary degree and guard-incoming statistics of every actual tournament.
These exact identities justify the finite relaxed-state coverage checker. -/


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRelaxedDegree
open TournamentHighRows
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V]







theorem sum_reverse (R : V → V → Prop) (S : Finset V) :
    (∑ v ∈ S, (S.filter fun u => R u v).card)=∑ v ∈ S, (S.filter (R v)).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

theorem sum_out_on (R : V → V → Prop) (hR : IsTournament R) (S : Finset V) :
    (∑ v ∈ S, (S.filter (R v)).card)=S.card*(S.card-1)/2 := by
  have hs : 2*(∑ v ∈ S, (S.filter (R v)).card)=S.card*(S.card-1) := by
    calc
      _=(∑ v ∈ S, (S.filter (R v)).card)+(∑ v ∈ S, (S.filter fun u => R u v).card) := by
        rw [sum_reverse]
        omega
      _=∑ v ∈ S, ((S.filter (R v)).card+(S.filter fun u => R u v).card) := Finset.sum_add_distrib.symm
      _=∑ _v ∈ S, (S.card-1) := by
        apply Finset.sum_congr rfl
        intro v hv
        simpa only [indicator,if_pos hv] using row_total R hR S v
      _=_ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
  omega















end
end ThreeBoundRelaxedDegree




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [Fintype.{0} V] (R : V → V → Prop) (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R)
  (S : Finset.{0} V),
  @Eq.{1} Nat
    (@Finset.sum.{0, 0} V Nat Nat.instAddCommMonoid S fun (v : V) =>
      @Finset.card.{0} V (@Finset.filter.{0} V (R v) (fun (a : V) => Classical.propDecidable (R v a)) S))
    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Finset.card.{0} V S)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Finset.card.{0} V S)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @Sensitivity213981Formal.ThreeBoundRelaxedDegree.sum_out_on
