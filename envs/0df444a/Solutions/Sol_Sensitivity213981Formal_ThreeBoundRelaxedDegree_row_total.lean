-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRelaxedDegree.row_total
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:55:39.363373+00:00
-- url     : https://prove2.me/submissions/a732559b-5eb6-4ab1-8591-724431d0f161

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





theorem row_total (R : V → V → Prop) (hR : IsTournament R) (S : Finset V) (v : V) :
    (S.filter (R v)).card+(S.filter fun u => R u v).card=S.card-indicator S v := by
  have hd : Disjoint (S.filter (R v)) (S.filter fun u => R u v) := by
    apply Finset.disjoint_left.mpr
    intro w hw hv
    have hvw := (Finset.mem_filter.mp hw).2
    have hwv := (Finset.mem_filter.mp hv).2
    have hne : v≠w := by intro he; subst w; exact hR.loopless v hvw
    exact (hR.orient v w hne).1 hvw hwv
  have he : S.filter (R v) ∪ S.filter (fun u => R u v)=S.erase v := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨hwS,hvw⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_erase.mpr ⟨by intro hh; subst w; exact hR.loopless v hvw,hwS⟩
      · obtain ⟨hwS,hwv⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_erase.mpr ⟨by intro hh; subst w; exact hR.loopless v hwv,hwS⟩
    · intro hw
      obtain ⟨hne,hwS⟩ := Finset.mem_erase.mp hw
      by_cases hh : R v w
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hwS,hh⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hwS,(hR.orient w v hne).2 hh⟩))
  calc
    _=(S.filter (R v) ∪ S.filter (fun u => R u v)).card := (Finset.card_union_of_disjoint hd).symm
    _=(S.erase v).card := congrArg Finset.card he
    _=_ := by
      by_cases hv : v ∈ S
      · simp only [indicator,if_pos hv,Finset.card_erase_of_mem hv]
      · simp only [indicator,if_neg hv,Finset.erase_eq_of_notMem hv,Nat.sub_zero]



















end
end ThreeBoundRelaxedDegree




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [Fintype.{0} V] (R : V → V → Prop) (hR : @Sensitivity213981Formal.TournamentHighRows.IsTournament V R)
  (S : Finset.{0} V) (v : V),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Finset.card.{0} V (@Finset.filter.{0} V (R v) (fun (a : V) => Classical.propDecidable (R v a)) S))
      (@Finset.card.{0} V
        (@Finset.filter.{0} V (fun (u : V) => R u v) (fun (a : V) => Classical.propDecidable (R a v)) S)))
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Finset.card.{0} V S)
      (@Sensitivity213981Formal.ThreeBoundRelaxedDegree.indicator V S v)) := @Sensitivity213981Formal.ThreeBoundRelaxedDegree.row_total
