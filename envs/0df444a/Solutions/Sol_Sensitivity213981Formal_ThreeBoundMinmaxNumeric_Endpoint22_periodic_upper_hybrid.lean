-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.periodic_upper_hybrid
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:08:05.520003+00:00
-- url     : https://prove2.me/submissions/e46d626f-afd5-4dc7-b40b-3fd3d3fb4b9b

import Definitions.Def_Sensitivity213981Formal_Endpoint22Assembly
import Definitions.Def_Sensitivity213981Formal_Endpoint22HybridAssembly
import Definitions.Def_Sensitivity213981Formal_Endpoint22Invariant
import Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
import Definitions.Def_Sensitivity213981Formal_Endpoint22Selected
import Definitions.Def_Sensitivity213981Formal_MinMaxNesting
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundEndpoint22Hybrid_upper_scaled_from_seeds
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_NatTable_dominates_sound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_NatTable_lowerCheck_sound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_oneBit_upper


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
/- Soundness of the complete finite five-profile closure procedure.
The update schedule is the one in graded2_union_recurrence.IntegerModel.close.
It does not establish the raw sensitivity transfer preceding that procedure. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundFullProfile
open ThreeBoundProfiles
open scoped Classical
noncomputable section

variable {n : ℕ} {I : Type} [Fintype I]

























theorem sem_mono (F : Fin n → (I → Bool) → Bool) (c : Coord n) (a b : ℕ)
    (hab : a ≤  b) (ha : Sem F c a) : Sem F c b := by
  cases c with
  | a i j => exact fun hij x hx => (ha hij x hx).trans hab
  | b i j => exact fun hij x hx => (ha hij x hx).trans hab
  | m i j => exact fun hij hn x hx hy => (ha hij hn x hx hy).trans hab
  | p j l => exact fun hjl x hx hy => (ha hjl x hx hy).trans hab
  | d i j l => exact fun hij hjl x hx hy => (ha hij hjl x hx hy).trans hab



theorem upper_mono (F : Fin n → (I → Bool) → Bool) (v w : Profile n)
    (hvw : ∀ c, v c ≤  w c) (hv : Upper F v) : Upper F w :=
  fun c => sem_mono F c _ _ (hvw c) (hv c)









































end
end ThreeBoundFullProfile




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

/-- Nesting holds at every depth of the actual arbitrary-depth construction. -/
theorem tower_nested (r : ℕ → MinMaxRecipe L V)
    (hr : ∀ n, OrderedRecipe (r n)) (n : ℕ) :
    Nested (towerFamily r n) := by
  induction n with
  | zero => exact fun _ _ _ _ h => h
  | succ n ih => exact parent_nested (r n) (hr n) _ ih

end ThreeBoundNesting




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Actual third-endpoint recipes, certificate SHA256 c706e403ddef113743f0dacc0a95d97dd3a2f32de032f35972f7ef045be6425f.
The tournament and edge labeling remain explicit parameters until the selected
order-5591 labeling is instantiated. -/


set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Sensitivity5591Endpoint22
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting







































theorem family_nested (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool) (n : ℕ) : Nested (family Adj loopless label n) :=
  tower_nested (periodicRecipe Adj loopless label) (fun k => recipe_ordered Adj loopless label _) n

end Sensitivity5591Endpoint22




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The fully proved Paley geometry fixes an unconditional third-endpoint family. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundEndpoint22Selected
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNumeric ThreeBoundFullProfile
open Sensitivity5591Labeling.Labeling5591







theorem family_nested (n : ℕ) : Nested (family n) :=
  Sensitivity5591Endpoint22.family_nested Adj irreflexive label n





end ThreeBoundEndpoint22Selected




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile



theorem base_ab_table:NatTable.lowerCheck 1 initialABTable=true:=by decide +kernel

theorem period_table:NatTable.dominates 10121928 profileTable4 profileTable0=true:=by decide +kernel

theorem period_inequality (c:Coord 22):profile4 c≤ 10121928*profile0 c:=
  NatTable.dominates_sound 10121928 profileTable4 profileTable0 period_table (flatIndex c)

theorem base_ab_indices:∀i j:Fin 22,flatIndex (Coord.a i j)< 506∧flatIndex (Coord.b i j)< 506:=by decide +kernel

theorem base_positive:BasePositive profile0:=by
  have htable:=NatTable.lowerCheck_sound 1 initialABTable base_ab_table
  intro i j hij
  constructor
  · change 1≤ (if flatIndex (Coord.a i j)< 506 then initialABTable.get (flatIndex (.a i j)) else _)
    rw [if_pos (base_ab_indices i j).1]
    exact htable _
  · change 1≤ (if flatIndex (Coord.b i j)< 506 then initialABTable.get (flatIndex (.b i j)) else _)
    rw [if_pos (base_ab_indices i j).2]
    exact htable _

theorem ordered0:Ordered profile0:=by decide +kernel

theorem ordered1:Ordered profile1:=by decide +kernel

theorem ordered2:Ordered profile2:=by decide +kernel

theorem ordered3:Ordered profile3:=by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint22



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Four exact scaled stages and reset give the third endpoint's infinite family. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundWitness
open ThreeBoundEndpoint22Selected











theorem input_ordered (p : Fin 4) : Ordered (input p) := by
  fin_cases p
  · exact ordered0
  · exact ordered1
  · exact ordered2
  · exact ordered3

theorem actual_base_upper : Upper (ThreeBoundEndpoint22Selected.family 0) profile0 :=
  oneBit_upper profile0 base_positive



theorem family_succ_phase (d : ℕ) (p : Fin 4) (hp : d%4=p.val) :
    ThreeBoundEndpoint22Selected.family (d+1) =
      parent ((ThreeBoundEndpoint22Selected.recipe p).stage
        (ThreeBoundEndpoint22Selected.family d)) (ThreeBoundEndpoint22Selected.family d) := by
  have he : (⟨d%4,Nat.mod_lt d (by decide)⟩ : Fin 4)=p := Fin.ext hp
  simp only [ThreeBoundEndpoint22Selected.family,ThreeBoundEndpoint22Selected.recipe,
    Sensitivity5591Endpoint22.family,towerFamily,Sensitivity5591Endpoint22.periodicRecipe,he]
  rfl







end ThreeBoundMinmaxNumeric.Endpoint22




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The essential-entry numerical certificate yields the same periodic family. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundWitness
open ThreeBoundMinmaxHybrid ThreeBoundEndpoint22Hybrid



theorem stage_from_hybrid {I : Type} [Fintype I]
    (records : List (List ℕ)) (hrecords : ∀ xs ∈ ThreeBoundQ3.records, xs ∈ records)
    (seeds : Fin 4 → List (Fin 22 × Fin 22))
    (numerical : HybridNumericalBounds records seeds) (closure : ClosureBounds)
    (p : Fin 4) (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F) (c : ℕ)
    (hv : Upper F (scale c (input p))) :
    Upper (parent ((ThreeBoundEndpoint22Selected.recipe p).stage F) F) (scale c (output p)) := by
  let G := parent ((ThreeBoundEndpoint22Selected.recipe p).stage F) F
  have hG : Nested G := ThreeBoundNesting.parent_nested _
    (Sensitivity5591Endpoint22.recipe_ordered Sensitivity5591Labeling.Labeling5591.Adj
      Sensitivity5591Labeling.Labeling5591.irreflexive ThreeBoundEndpoint22Selected.label p) F hF
  have hh := upper_scaled_from_seeds records hrecords p F hF (input p) (rawInput p) (seeds p)
    (numerical p).1 (numerical p).2.1 (numerical p).2.2 (input_ordered p) c hv
  exact closure p ((Fin 5591 × Bool) × I) G hG c hh

theorem periodic_upper_hybrid (records : List (List ℕ))
    (hrecords : ∀ xs ∈ ThreeBoundQ3.records, xs ∈ records)
    (seeds : Fin 4 → List (Fin 22 × Fin 22))
    (numerical : HybridNumericalBounds records seeds) (closure : ClosureBounds) : ∀ m : ℕ,
    Upper (ThreeBoundEndpoint22Selected.family (4*m)) (scale (10121928^m) profile0) := by
  intro m
  induction m with
  | zero =>
      change Upper (ThreeBoundEndpoint22Selected.family 0) (fun coord => 1*profile0 coord)
      simpa only [one_mul] using actual_base_upper
  | succ m ih =>
      let c := 10121928^m
      have h₁ : Upper (ThreeBoundEndpoint22Selected.family (4*m+1)) (scale c profile1) := by
        rw [family_succ_phase (4*m) 0 (by omega)]
        exact stage_from_hybrid records hrecords seeds numerical closure 0 _
          (ThreeBoundEndpoint22Selected.family_nested (4*m)) c ih
      have h₂ : Upper (ThreeBoundEndpoint22Selected.family (4*m+2)) (scale c profile2) := by
        rw [show 4*m+2=(4*m+1)+1 by omega,family_succ_phase (4*m+1) 1 (by omega)]
        exact stage_from_hybrid records hrecords seeds numerical closure 1 _
          (ThreeBoundEndpoint22Selected.family_nested (4*m+1)) c h₁
      have h₃ : Upper (ThreeBoundEndpoint22Selected.family (4*m+3)) (scale c profile3) := by
        rw [show 4*m+3=(4*m+2)+1 by omega,family_succ_phase (4*m+2) 2 (by omega)]
        exact stage_from_hybrid records hrecords seeds numerical closure 2 _
          (ThreeBoundEndpoint22Selected.family_nested (4*m+2)) c h₂
      have h₄ : Upper (ThreeBoundEndpoint22Selected.family (4*m+4)) (scale c profile4) := by
        rw [show 4*m+4=(4*m+3)+1 by omega,family_succ_phase (4*m+3) 3 (by omega)]
        exact stage_from_hybrid records hrecords seeds numerical closure 3 _
          (ThreeBoundEndpoint22Selected.family_nested (4*m+3)) c h₃
      have hf : Upper (ThreeBoundEndpoint22Selected.family (4*m+4))
          (scale (10121928^(m+1)) profile0) := by
        apply upper_mono _ _ _ _ h₄
        intro coord
        have hh := Nat.mul_le_mul_left c (period_inequality coord)
        simpa only [c,scale,pow_succ,Nat.mul_assoc] using hh
      simpa only [Nat.mul_succ] using hf





end ThreeBoundMinmaxNumeric.Endpoint22




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (records : List.{0} (List.{0} Nat))
  (hrecords :
    ∀ (xs : List.{0} Nat),
      @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
          Sensitivity213981Formal.ThreeBoundQ3.records xs →
        @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
          records xs)
  (seeds :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      List.{0}
        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))))
  (numerical : Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.HybridNumericalBounds records seeds)
  (closure : Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.ClosureBounds) (m : Nat),
  @Sensitivity213981Formal.ThreeBoundFullProfile.Upper (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
    (Sensitivity213981Formal.ThreeBoundWitness.IterProd
      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
    (@Sensitivity213981Formal.ThreeBoundWitness.iterProdFintype
      (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool)
      (@instFintypeProd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 5591) (instOfNatNat (nat_lit 5591)))) Bool.fintype)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
    (Sensitivity213981Formal.ThreeBoundEndpoint22Selected.family
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m))
    (@Sensitivity213981Formal.ThreeBoundFullProfile.scale
      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 10121928) (instOfNatNat (nat_lit 10121928))) m)
      Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.profile0) := @Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.periodic_upper_hybrid
