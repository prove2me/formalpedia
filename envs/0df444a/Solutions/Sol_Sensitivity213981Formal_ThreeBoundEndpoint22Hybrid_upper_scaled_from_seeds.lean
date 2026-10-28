-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Hybrid.upper_scaled_from_seeds
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:04:42.7464+00:00
-- url     : https://prove2.me/submissions/15b2f474-4d2a-4d0f-9ef9-f704ba392ab7

import Definitions.Def_Sensitivity213981Formal_Endpoint22HybridTransfer
import Definitions.Def_Sensitivity213981Formal_Endpoint22PairData
import Definitions.Def_Sensitivity213981Formal_Endpoint22Transfer
import Definitions.Def_Sensitivity213981Formal_MinMaxNesting
import Definitions.Def_Sensitivity213981Formal_MinmaxHybridTransfer
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_NumericAdmissibility
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_Sensitivity213981Formal_Selected5591
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Transfer_rawA_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxHybrid_coreBounds_scale
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundMinmaxHybrid_upper_of_a_core


namespace Sensitivity213981Formal
section
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320

variable {L I V : Type}









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤  S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]















































/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/-
Dimension-independent semantics and closure rules for the five sensitivity
profiles. These prove the local soundness of the closure operations, not the
raw graded/min-max transfer formulas or their finite case-table coverage.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ThreeBoundProfiles
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320
noncomputable section
open scoped Classical

variable {L I : Type} [Preorder L] [Fintype I]















theorem rejects_of_le (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤  j) (x : I → Bool) (hi : F i x = false) : F j x = false := by
  cases hj : F j x with
  | false => rfl
  | true => have hh := hF i j hij x hj; rw [hi] at hh; contradiction

theorem up_subset (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤  j) (x : I → Bool) :
    flipsTo (F j) true x ⊆ flipsTo (F i) true x := by
  classical
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF i j hij _ (Finset.mem_filter.mp ha).2⟩



theorem a_condition_weaken (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i i' j : L) (hii' : i ≤  i') (v : ℕ) (h : ABound F i' j v) : ABound F i j v :=
  fun x hx => h x (rejects_of_le F hF i i' hii' x hx)

theorem a_target_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j j' : L) (hjj' : j ≤  j') (v : ℕ) (h : ABound F i j v) : ABound F i j' v :=
  fun x hx => (Finset.card_le_card (up_subset F hF j j' hjj' x)).trans (h x hx)









































end
end ThreeBoundProfiles






end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile





theorem Expr.eval_homogeneous {n : ℕ} (e : Expr n) (v : Profile n) (c : ℕ) :
    e.eval (fun i => c * v i) = c * e.eval v := by
  induction e with
  | zero => simp [eval]
  | var i => rfl
  | add a b ha hb => simp only [eval, ha, hb, Nat.mul_add]
  | scale k a ha => simp only [eval, ha]; ring
  | sub a b ha hb => simp only [eval, ha, hb, Nat.mul_sub_left_distrib]
  | min a b ha hb => simp only [eval, ha, hb, Nat.mul_min_mul_left]
  | max a b ha hb => simp only [eval, ha, hb, Nat.mul_max_mul_left]




































end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace ThreeBoundNesting
open ThreeBoundWitness ThreeBoundProfiles

variable {L I V : Type} [Preorder L] [Fintype V]



theorem failed_subset (r : MinMaxRecipe L V) (hr : OrderedRecipe r)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤  j) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (r.stage F) F i x v ⊆ failed (r.stage F) F j x v := by
  classical
  intro w hw
  change w ∈ Finset.univ.filter (fun z =>
    r.Adj v z ∧ F (r.guard i) (child x z (r.label v z)) = true) at hw
  change w ∈ Finset.univ.filter (fun z =>
    r.Adj v z ∧ F (r.guard j) (child x z (r.label v z)) = true)
  have hh := (Finset.mem_filter.mp hw).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1,
    hF _ _ (hr.guard hij) _ hh.2⟩

theorem target_mono (r : MinMaxRecipe L V) (hr : OrderedRecipe r)
    (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤  j) (a b : ℕ) (hab : a ≤  b)
    (hb : b ≤  r.tolerance j) (x y : I → Bool)
    (h : minmaxTarget F r.lower r.upper j b x y = true) :
    minmaxTarget F r.lower r.upper i a x y = true := by
  have ht : r.lower i a ≤  r.lower j b :=
    (hr.lower_mono i hab).trans (hr.lower_order i j hij b hb)
  have hu : r.upper i a ≤  r.upper j b :=
    (hr.upper_mono i hab).trans (hr.upper_order i j hij b hb)
  simp only [minmaxTarget, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  refine ⟨⟨hF _ _ ht x h.1.1, hF _ _ ht y h.1.2⟩, ?_⟩
  rcases h.2 with hx | hy
  · exact Or.inl (hF _ _ hu x hx)
  · exact Or.inr (hF _ _ hu y hy)

/-- The concrete parent construction used by the witness recursion preserves
nested families for every ordered min/max recipe. -/
theorem parent_nested (r : MinMaxRecipe L V) (hr : OrderedRecipe r)
    (F : L → (I → Bool) → Bool) (hF : Nested F) :
    Nested (parent (r.stage F) F) := by
  intro i j hij x hj
  obtain ⟨v, hv, ht⟩ := (parent_true_iff (r.stage F) F j x).mp hj
  have hc := Finset.card_le_card (failed_subset r hr F hF i j hij x v)
  apply (parent_true_iff (r.stage F) F i x).mpr
  refine ⟨v, hc.trans (hv.trans (hr.tolerance hij)), ?_⟩
  exact target_mono r hr F hF i j hij _ _ hc hv _ _ ht



end ThreeBoundNesting




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile











theorem ordered_scale {n : ℕ} (v : Profile n) (c : ℕ) (h : Ordered v) :
    Ordered (scale c v) := by
  intro i j hij
  obtain ⟨ha,hb,hc,hd⟩ := h i j hij
  exact ⟨Nat.mul_le_mul_left c ha,Nat.mul_le_mul_left c hb,
    Nat.mul_le_mul_left c hc,Nat.mul_le_mul_left c hd⟩











end ThreeBoundNumeric




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Literal parent A entries may be proved on a small covering set of intervals.
All remaining coordinates then use scalar conditional bounds. -/


set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxHybrid
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxRank (fullBExpr fullMExpr)
open ThreeBoundMinmaxNumeric (pCore dCore)
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]



theorem a_bounds_of_cover (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (w : Profile n) (seeds : List (Fin n × Fin n)) (c : ℕ) (cover : ACovers w seeds)
    (hs : ∀ pair ∈ seeds, ABound F pair.1 pair.2 (c*w (.a pair.1 pair.2))) :
    ∀ i j : Fin n, i ≤  j → ABound F i j (c*w (.a i j)) := by
  intro i j hij
  obtain ⟨pair,hpair,hi,hij',hj,hv⟩ := cover i j hij
  have hleft := a_condition_weaken F hF i pair.1 pair.2 hi _ (hs pair hpair)
  have hright := a_target_strengthen F hF i pair.2 j hj _ hleft
  intro x hx
  exact (hright x hx).trans (Nat.mul_le_mul_left c hv)







end
end ThreeBoundMinmaxHybrid




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









theorem selected_caps
    (htriple : ∀ M : Finset Vertex, M.card = 3 →
      (dominatedBy Sensitivity5591Labeling.Adj M).card ≤  800) :
    ThreeBoundRankNumeric.CapsSound Adj (label htriple) ThreeBoundOrdinary5591.numericCaps 14 :=
  Sensitivity5591BoolCaps.caps_sound Adj (selectedLabel htriple) (selectedLabel_spec htriple)



end
end Sensitivity5591Labeling.Labeling5591




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

theorem stage_outdegree (htriple : TripleGeometry) (p : Fin 4)
    (F : Fin 22 → (I → Bool) → Bool) (w : Fin 5591) :
    (outgoing ((Sensitivity5591Endpoint22.recipe Adj irreflexive (label htriple) p).stage F) w).card = 2795 :=
  outdegree w

theorem stage_source (htriple : TripleGeometry) (p : Fin 4)
    (F : Fin 22 → (I → Bool) → Bool) :
    @ResidualCaps.DominatorCardBound (Fin 5591) (fun a b => Classical.propDecidable (a=b))
      ((Sensitivity5591Endpoint22.recipe Adj irreflexive (label htriple) p).stage F).Adj
      ((Sensitivity5591Endpoint22.recipe Adj irreflexive (label htriple) p).stage F).label 1 19 := by
  intro A M color hdis hM hdom hmis
  apply (selected_caps htriple).source A M color hdis hM hdom
  intro w hw
  exact hmis w (by simpa only [Finset.mem_union] using hw)







end
end ThreeBoundEndpoint22Transfer



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The third endpoint needs upward arithmetic only on a covering set of entries. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundEndpoint22Hybrid
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxHybrid
open Sensitivity5591Labeling.Labeling5591
open scoped Classical
noncomputable section
variable {I : Type} [Fintype I]



theorem upper_scaled_from_seeds (records : List (List ℕ))
    (hrecords : ∀ xs ∈ ThreeBoundQ3.records, xs ∈ records)
    (p : Fin 4) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (v w : Profile 22) (seeds : List (Fin 22 × Fin 22))
    (cover : ACovers w seeds) (hs : SeedBounds records p v w seeds)
    (hc : CoreBounds 2795 18 (ThreeBoundMinmaxNumeric.Endpoint22.recipe p) v w)
    (hordered : Ordered v) (c : ℕ) (hv : Upper F (scale c v)) :
    Upper (parent ((ThreeBoundEndpoint22Selected.recipe p).stage F) F) (scale c w) := by
  let G := parent ((ThreeBoundEndpoint22Selected.recipe p).stage F) F
  have hG : Nested G := ThreeBoundNesting.parent_nested _
    (Sensitivity5591Endpoint22.recipe_ordered Adj irreflexive ThreeBoundEndpoint22Selected.label p) F hF
  have hseed : ∀ pair ∈ seeds, ABound G pair.1 pair.2 (c*w (.a pair.1 pair.2)) := by
    intro pair hpair
    obtain ⟨hij,hnum⟩ := hs pair hpair
    have hsem := ThreeBoundEndpoint22Transfer.rawA_bound Sensitivity5591Labeling.triple_common_out
      records hrecords p F hF (scale c v) hv (ordered_scale v c hordered) pair.1 pair.2 hij
    have heval (e : Expr 22) : e.eval (scale c v)=c*e.eval v := Expr.eval_homogeneous e v c
    rw [heval] at hsem
    intro x hx
    exact (hsem x hx).trans (Nat.mul_le_mul_left c hnum)
  have hA := a_bounds_of_cover G hG w seeds c cover hseed
  exact upper_of_a_core ((ThreeBoundEndpoint22Selected.recipe p).stage F)
    (ThreeBoundEndpoint22Transfer.stage_tournament Sensitivity5591Labeling.triple_common_out p F)
    F hF (ThreeBoundMinmaxNumeric.Endpoint22.recipe p)
    (ThreeBoundEndpoint22Pairs.pairData Adj irreflexive ThreeBoundEndpoint22Selected.label p F)
    (ThreeBoundEndpoint22Pairs.entryMatch Adj irreflexive ThreeBoundEndpoint22Selected.label p F)
    2795 18
    (ThreeBoundEndpoint22Transfer.stage_outdegree Sensitivity5591Labeling.triple_common_out p F)
    (ThreeBoundEndpoint22Transfer.stage_source Sensitivity5591Labeling.triple_common_out p F)
    (scale c v) (scale c w) hv hA (coreBounds_scale 2795 18 _ v w hc c)

end
end ThreeBoundEndpoint22Hybrid



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {I : Type} [inst : Fintype.{0} I] (records : List.{0} (List.{0} Nat))
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
  (v w :
    Sensitivity213981Formal.ThreeBoundFullProfile.Profile
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
  (seeds :
    List.{0}
      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))))
  (cover :
    @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.ACovers
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) w seeds)
  (hs : Sensitivity213981Formal.ThreeBoundEndpoint22Hybrid.SeedBounds records p v w seeds)
  (hc :
    @Sensitivity213981Formal.ThreeBoundMinmaxHybrid.CoreBounds
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2795) (instOfNatNat (nat_lit 2795)))
      (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
      (Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.recipe p) v w)
  (hordered :
    @Sensitivity213981Formal.ThreeBoundNumeric.Ordered (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      v)
  (c : Nat)
  (hv :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Upper (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      I inst F
      (@Sensitivity213981Formal.ThreeBoundFullProfile.scale
        (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) c v)),
  @Sensitivity213981Formal.ThreeBoundFullProfile.Upper (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
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
        (Sensitivity213981Formal.ThreeBoundEndpoint22Selected.recipe p) F)
      F)
    (@Sensitivity213981Formal.ThreeBoundFullProfile.scale
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) c w) := @Sensitivity213981Formal.ThreeBoundEndpoint22Hybrid.upper_scaled_from_seeds
