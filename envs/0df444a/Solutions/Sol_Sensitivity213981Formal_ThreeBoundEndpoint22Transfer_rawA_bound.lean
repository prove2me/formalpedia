-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Transfer.rawA_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:59:54.203734+00:00
-- url     : https://prove2.me/submissions/2ee912ab-230a-42f3-a1db-b1ea5c284f3c

import Definitions.Def_Sensitivity213981Formal_Endpoint22PairData
import Definitions.Def_Sensitivity213981Formal_Endpoint22Transfer
import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_Label5591Joint
import Definitions.Def_Sensitivity213981Formal_MinmaxNegative
import Definitions.Def_Sensitivity213981Formal_MinmaxPrefixCaps
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Caps
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
import Definitions.Def_Sensitivity213981Formal_Q3RecordFields
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_Sensitivity213981Formal_RankConvertedCaps
import Definitions.Def_Sensitivity213981Formal_RankCostExpressions
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_Sensitivity213981Formal_Selected5591
import Definitions.Def_Sensitivity213981Formal_SelectedBoolCaps
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Sensitivity213981Formal_Sensitivity5591BoolCaps_caps_sound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Ordinary_ordinaryA_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_marked_exclusion_card_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundRankNumeric_actual_record_cost


namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile
















@[simp] theorem maximum_cons (x : ℕ) (xs : List ℕ) :
    maximum (x::xs) = max x (maximum xs) := rfl

theorem le_maximum_of_mem {xs : List ℕ} {x : ℕ} (h : x ∈ xs) :
    x ≤  maximum xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)



theorem Expr.eval_maximum {n : ℕ} (es : List (Expr n)) (v : Profile n) :
    (Expr.maximum es).eval v = ThreeBoundNumeric.maximum (es.map (fun e => e.eval v)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [Expr.maximum, List.foldr_cons, Expr.eval,
      List.map_cons, maximum_cons] using congrArg (Nat.max (e.eval v)) ih



















end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_CompactBooleanTransfer_candidateTotalCap_bound.lean -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]





















theorem mismatch_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A B : Finset V) (h : A ⊆ B) (color : V → Fin 2) (x : V) :
    mismatch R ell A color x ⊆ mismatch R ell B color x := by
  intro y hy
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hy).1,
    (Finset.mem_filter.mp hy).2⟩





























end
end ZL
end
end z8

section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)









end Tournament



















end OAI.Paper320
namespace Sensitivity205
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205













section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)





end Nesting











section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29

section z32
set_option maxHeartbeats 3000000
noncomputable section
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)







end OAI.Paper320.Tournament
namespace SensitivityQ



















end SensitivityQ
namespace SensitivitySourceZero






















end SensitivitySourceZero
end
end z32

section z38

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace CompactTournament
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]













end CompactTournament
end
end z38

section z39

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace CompactTournament
open Finset ZL
variable {V : Type*} [Fintype V] [DecidableEq V]



end CompactTournament
end
end z39

section z40

set_option maxHeartbeats 3000000
noncomputable section
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

















end ZT
end
end z40

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



















end ZT
end
end z43

section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









end ZT
end
end z45

end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- selected_exists_labelCaps sections z8,z46 -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]





















theorem ordinaryGood_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A B : Finset V) (h : A ⊆ B) (q : ℕ) (color : V → Fin 2)
    (hg : OrdinaryGood R ell B q color) : OrdinaryGood R ell A q color := by
  intro x hx
  exact (Finset.card_le_card (mismatch_mono R ell A B h color x)).trans (hg x (h hx))

end
end ZL
end
end z8

section z46

set_option maxHeartbeats 600000
open scoped Classical BigOperators
noncomputable section

namespace ZT
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 ZL SensitivityQ
variable {k : ℕ}

theorem ordinary_exclusion_defect_bound (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (q a : ℕ)
    (h : ∀ I : OrdinaryIndex (Fin k) a,
      ¬ (ordinaryFamily T.Adj q a).bad I (fun e => label e.1 e.2)) :
    DefectBound T label q a := by
  intro S color hg
  by_contra hn
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  let I : OrdinaryIndex (Fin k) a :=
    ⟨A,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩⟩
  apply h I
  exact ⟨color,ordinaryGood_mono T.Adj (fun e => label e.1 e.2) A S hA q color hg⟩









end ZT
end
end z46


end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- A homogeneous rank transfer expression over q3 count records.
Converted arcs use the proved lower-target guard cost. -/


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace ThreeBoundRankNumeric
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped BigOperators













theorem recordCost_le_rankAExpr {n : ℕ} (caps : Caps) (perfect : ℕ) (records : List (List ℕ))
    (a c : Entry) (v : Profile n) (xs : List ℕ) (hx : xs ∈ records)
    (ha : recordAllowed n caps a c (recordOfList xs)=true) (e : ℕ) (he : e ≤  recordOfList xs 11) :
    (recordCost n caps perfect a c (recordOfList xs) e).eval v ≤ 
      (rankAExpr n caps perfect records a c).eval v := by
  rw [rankAExpr,Expr.eval_maximum]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨recordCost n caps perfect a c (recordOfList xs) e,?_,rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨xs,hx,?_⟩
  simp only [ha,if_true]
  exact List.mem_map.mpr ⟨e,List.mem_range.mpr (by omega),rfl⟩

end ThreeBoundRankNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Convert the joint 5591 exclusions to every semantic cap used by the recurrence. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Sensitivity5591BoolCaps
open Sensitivity10007Labeling Sensitivity10007BoolCaps Sensitivity5591Labeling
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]









theorem ordinaryA_eq_cutoff (q : Fin 9) :
    Caps.ordinaryA q = ThreeBoundOrdinary5591.cutoff q.val := by
  fin_cases q <;> decide +kernel

theorem ordinary_caps {k : ℕ}
    (T : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
    (ell : Fin k → Fin k → Fin 2)
    (hex : Caps.JointExclusions T.Adj (fun e => ell e.1 e.2)) :
    ThreeBoundOrdinary5591.LabelCaps T ell := by
  have ho (q : Fin 9) := ThreeBoundOrdinaryArchive.ZT.ordinary_exclusion_defect_bound
    T ell q.val (Caps.ordinaryA q) (hex.ordinary q)
  have hm (i : Fin 12) := ThreeBoundOrdinaryArchive.ZT.marked_exclusion_card_bound
    T ell (Caps.marked i).q (Caps.marked i).a (Caps.marked i).m (Caps.marked i).B (hex.marked i)
  refine ⟨?_,?_,?_⟩
  · intro q _ hq8
    have hq : q <  9 := by omega
    simpa only [ordinaryA_eq_cutoff] using ho ⟨q,hq⟩
  · exact hm 3
  · exact hm 10

end
end Sensitivity5591BoolCaps




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The indexed Paley-5591 tournament and its jointly admissible label. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Sensitivity5591Labeling.Labeling5591
open Sensitivity10007Labeling ZL
open scoped Classical
noncomputable section
attribute [local irreducible] Sensitivity5591Labeling.core



























theorem selectedLabel_spec
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800) :
    Caps.JointExclusions Adj (selectedLabel htriple) :=
  Classical.choose_spec (exists_selected_labeling htriple)







theorem label_bridge
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800) (v w : Fin 5591) :
    finTwoEquiv (archiveLabel htriple v w) = label htriple v w := by
  change finTwoEquiv (selectedLabel htriple (v,w)) = decide (selectedLabel htriple (v,w) = 1)
  generalize selectedLabel htriple (v,w) = c
  fin_cases c <;> decide

theorem selected_caps
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800) :
    ThreeBoundRankNumeric.CapsSound Adj (label htriple) ThreeBoundOrdinary5591.numericCaps 14 :=
  Sensitivity5591BoolCaps.caps_sound Adj (selectedLabel htriple) (selectedLabel_spec htriple)

theorem selected_ordinary_caps
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800) :
    ThreeBoundOrdinary5591.LabelCaps tournament (archiveLabel htriple) :=
  Sensitivity5591BoolCaps.ordinary_caps tournament (archiveLabel htriple) (selectedLabel_spec htriple)

end
end Sensitivity5591Labeling.Labeling5591




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Complete actual q0--q3 rank upward transfer. Every numerical record
field, prefix constraint, rank charge, and converted arc is justified by
the Boolean parent construction. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankNumeric
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundMinmaxNumeric (EntryMatch)
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]





theorem rankAExpr_bound (S : Stage (Fin n) I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (hQ : S.tolerance j ≤  3) (caps : Caps) (perfect : ℕ)
    (hcaps : CapsSound S.Adj S.label caps perfect)
    (records : List (List ℕ)) (hrecords : ∀ xs ∈ ThreeBoundQ3.records, xs ∈ records)
    (v : Profile n) (hv : Upper F v) (hordered : Ordered v) :
    ABound (parent S F) i j ((rankAExpr n caps perfect records a c).eval v) := by
  intro input hoff
  obtain ⟨xs,hxs,e,he,ha,hb⟩ := actual_record_cost S hR F hF i j P a c matchE input hoff
    hQ caps perfect hcaps v hv hordered
  exact hb.trans (recordCost_le_rankAExpr caps perfect records a c v xs (hrecords xs hxs) ha e he)

end
end ThreeBoundRankNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Concrete third-endpoint min/max pairing, independent of the chosen edge label. -/


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint22Pairs
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxNumeric





variable {I : Type} [Fintype I]



theorem numeric_lower (p : Fin 4) (l : Fin 22) (d : ℕ)
    (hd : d ≤  (Sensitivity5591Endpoint22.entry p l).tolerance) :
    ((Sensitivity5591Endpoint22.entry p l).threshold d).val=
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p l).lowerAt d := by
  have hd9 : d< 9 := by have hh := Sensitivity5591Endpoint22.entry_tolerance_bound p l; omega
  simp [ThreeBoundMinmaxNumeric.Endpoint22.recipe,ThreeBoundMinmaxNumeric.Entry.lowerAt,Array.getD,hd9]

theorem numeric_upper (p : Fin 4) (l : Fin 22) (d : ℕ)
    (hd : d ≤  (Sensitivity5591Endpoint22.entry p l).tolerance) :
    ((Sensitivity5591Endpoint22.entry p l).upper d).val=
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p l).upperAt d := by
  have hd9 : d< 9 := by have hh := Sensitivity5591Endpoint22.entry_tolerance_bound p l; omega
  simp [ThreeBoundMinmaxNumeric.Endpoint22.recipe,ThreeBoundMinmaxNumeric.Entry.upperAt,Array.getD,hd9]

theorem entryMatch (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ w, ¬Adj w w)
    (label : Fin 5591 → Fin 5591 → Bool) (p : Fin 4) (F : Fin 22 → (I → Bool) → Bool)
    (i j : Fin 22) (hij : i ≤  j) :
    EntryMatch ((Sensitivity5591Endpoint22.recipe Adj loopless label p).stage F) F i j
      (pairData Adj loopless label p F i j hij) (ThreeBoundMinmaxNumeric.Endpoint22.recipe p i)
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j) where
  weakTolerance := rfl
  strongTolerance := rfl
  weakGuard := rfl
  strongGuard := rfl
  weakLower := numeric_lower p i
  weakUpper := numeric_upper p i
  strongLower := numeric_lower p j
  strongUpper := numeric_upper p j

end ThreeBoundEndpoint22Pairs




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Complete semantic five-profile transfer for the third endpoint. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint22Transfer
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundNumeric ThreeBoundFullProfile
open Sensitivity5591Labeling.Labeling5591
open scoped Classical
noncomputable section







variable {I : Type} [Fintype I]

theorem stage_tournament (htriple : TripleGeometry) (p : Fin 4)
    (F : Fin 22 → (I → Bool) → Bool) :
    TournamentHighRows.IsTournament
      ((Sensitivity5591Endpoint22.recipe Adj irreflexive (label htriple) p).stage F).Adj :=
  ⟨irreflexive,edge_compl⟩





theorem stage_caps_sound (htriple : TripleGeometry) (p : Fin 4)
    (F : Fin 22 → (I → Bool) → Bool) :
    @ThreeBoundRankNumeric.CapsSound (Fin 5591) (Fin.fintype 5591)
      (fun a b => Classical.propDecidable (a=b))
      ((Sensitivity5591Endpoint22.recipe Adj irreflexive (label htriple) p).stage F).Adj
      ((Sensitivity5591Endpoint22.recipe Adj irreflexive (label htriple) p).stage F).label
      ThreeBoundOrdinary5591.numericCaps 14 := by
  have he : (fun a b : Fin 5591 => Classical.propDecidable (a=b)) =
      (inferInstance : DecidableEq (Fin 5591)) := Subsingleton.elim _ _
  rw [he]
  exact selected_caps htriple

theorem rawA_bound (htriple : TripleGeometry) (records : List (List ℕ))
    (hrecords : ∀ xs ∈ ThreeBoundQ3.records, xs ∈ records)
    (p : Fin 4) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile 22) (hv : Upper F v) (hordered : Ordered v)
    (i j : Fin 22) (hij : i ≤  j) :
    ABound (parent ((Sensitivity5591Endpoint22.recipe Adj irreflexive (label htriple) p).stage F) F) i j
      ((ThreeBoundRankNumeric.rawAExpr 22 ThreeBoundOrdinary5591.numericCaps 14 records
        (ThreeBoundMinmaxNumeric.Endpoint22.recipe p i) (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j)).eval v) := by
  by_cases hlarge : 4 ≤  (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j).tolerance
  · rw [ThreeBoundRankNumeric.rawAExpr,if_pos hlarge]
    exact ThreeBoundEndpoint22Ordinary.ordinaryA_bound Adj irreflexive (label htriple)
      tournament (archiveLabel htriple) (fun _ _ => Iff.rfl) (label_bridge htriple)
      (selected_ordinary_caps htriple) p F hF v hv i j hij hlarge
  · rw [ThreeBoundRankNumeric.rawAExpr,if_neg hlarge]
    exact ThreeBoundRankNumeric.rankAExpr_bound
      ((Sensitivity5591Endpoint22.recipe Adj irreflexive (label htriple) p).stage F)
      (stage_tournament htriple p F) F hF i j
      (ThreeBoundEndpoint22Pairs.pairData Adj irreflexive (label htriple) p F i j hij)
      (ThreeBoundMinmaxNumeric.Endpoint22.recipe p i) (ThreeBoundMinmaxNumeric.Endpoint22.recipe p j)
      (ThreeBoundEndpoint22Pairs.entryMatch Adj irreflexive (label htriple) p F i j hij)
      (show (Sensitivity5591Endpoint22.entry p j).tolerance ≤  3 from by
        change ¬4 ≤  (Sensitivity5591Endpoint22.entry p j).tolerance at hlarge
        omega)
      ThreeBoundOrdinary5591.numericCaps 14 (stage_caps_sound htriple p F) records hrecords v hv hordered



end
end ThreeBoundEndpoint22Transfer



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {I : Type} [inst : Fintype.{0} I] (htriple : Sensitivity213981Formal.ThreeBoundEndpoint22Transfer.TripleGeometry)
  (records : List.{0} (List.{0} Nat))
  (hrecords :
    ∀ (xs : List.{0} Nat),
      @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
          Sensitivity213981Formal.ThreeBoundQ3.records xs →
        @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
          records xs)
  (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (F : Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
      (@PartialOrder.toPreorder.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
        (@Fin.instPartialOrder (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
      F)
  (v :
    Sensitivity213981Formal.ThreeBoundFullProfile.Profile
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
  (hv :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Upper (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      I inst F v)
  (hordered :
    @Sensitivity213981Formal.ThreeBoundNumeric.Ordered (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      v)
  (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
  (hij :
    @LE.le.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
      (@instLEFin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) i j),
  @Sensitivity213981Formal.ThreeBoundProfiles.ABound
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
    (Prod.{0, 0} (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool) I)
    (@instFintypeProd.{0, 0}
      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool) I
      (@instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool.fintype)
      inst)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
      (@Sensitivity213981Formal.ThreeBoundWitness.MinMaxRecipe.stage
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) I
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591))))
        (Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe
          Sensitivity213981Formal.Sensitivity5591Labeling.Labeling5591.Adj
          Sensitivity213981Formal.Sensitivity5591Labeling.Labeling5591.irreflexive
          (Sensitivity213981Formal.Sensitivity5591Labeling.Labeling5591.label htriple) p)
        F)
      F)
    i j
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) v
      (Sensitivity213981Formal.ThreeBoundRankNumeric.rawAExpr
        (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
        Sensitivity213981Formal.ThreeBoundOrdinary5591.numericCaps
        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) records
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p i)
        (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p j))) := @Sensitivity213981Formal.ThreeBoundEndpoint22Transfer.rawA_bound
