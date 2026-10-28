-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundOrdinaryArchive.CompactTournament.augment_by_guards
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:39:54.317699+00:00
-- url     : https://prove2.me/submissions/ccc931b7-eebf-4b29-8d69-cd80e6669a6f

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
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
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
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


namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
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
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













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
open OAI.Paper320 Sensitivity205 Sensitivity2075
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



theorem neighborhood_deficiency (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) (S : Finset V) :
    S.card ≤  (S.biUnion (neighbors R)).card + 1 := by
  let U := S.biUnion (neighbors R)
  have hsmall : (S \ U).card ≤  1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxS,hxU⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyS,hyU⟩ := Finset.mem_sdiff.mp hy
    by_contra hxy
    rcases ht x y hxy with he | he
    · exact hyU (Finset.mem_biUnion.mpr ⟨x,hxS,by simp [neighbors,he]⟩)
    · exact hxU (Finset.mem_biUnion.mpr ⟨y,hyS,by simp [neighbors,he]⟩)
  have hc := Finset.card_sdiff_add_card_inter S U
  have hi := Finset.card_le_card (Finset.inter_subset_right : S ∩ U ⊆ U)
  change S.card ≤  U.card + 1
  omega

theorem exists_optional_matching (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) :
    ∃ f : V → Option V, Function.Injective f ∧
      ∀ x y, f x = some y → R x y := by
  let t : V → Finset (Option V) := fun x => insert none ((neighbors R x).image some)
  have hhall : ∀ S : Finset V, S.card ≤  (S.biUnion t).card := by
    intro S
    by_cases hS : S.Nonempty
    · have hu : S.biUnion t = insert none ((S.biUnion (neighbors R)).image some) := by
        ext z
        cases z with
        | none =>
          simp only [Finset.mem_biUnion, t, Finset.mem_insert, true_or,
            and_true, exists_prop, Finset.mem_image, reduceCtorEq, and_false,
            exists_false, or_false]
          exact iff_true_intro hS
        | some y =>
          simp [t, Finset.mem_biUnion]
      rw [hu, Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (Option.some_injective V)]
      exact neighborhood_deficiency R ht S
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [he]
  obtain ⟨f,hfi,hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  refine ⟨f,hfi,?_⟩
  intro x y hxy
  have hmem := hf x
  rw [hxy] at hmem
  simpa [t, neighbors] using hmem



theorem exists_near_coloring (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) (label : V → V → Fin 2) :
    ∃ (color : V → Fin 2) (bad : Finset V), bad.card ≤  1 ∧
      ∀ x, x ∉ bad → ∃ y, R x y ∧ label x y = color y := by
  obtain ⟨f,hfi,hf⟩ := exists_optional_matching R ht
  let color : V → Fin 2 := fun y =>
    if h : ∃ x, f x = some y then label (Classical.choose h) y else 0
  let bad : Finset V := univ.filter fun x => f x = none
  refine ⟨color,bad,?_,?_⟩
  · apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hfi ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  · intro x hx
    cases hfx : f x with
    | none => exact False.elim (hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfx⟩))
    | some y =>
      refine ⟨y,hf x y hfx,?_⟩
      have hex : ∃ z, f z = some y := ⟨x,hfx⟩
      have he : Classical.choose hex = x := hfi ((Classical.choose_spec hex).trans hfx.symm)
      simp only [color, dif_pos hex, he]



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

theorem augment_by_guards (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x)
    (ell : V × V → Fin 2) (C G : Finset V) (hdis : Disjoint C G)
    (q : ℕ) (base : V → Fin 2)
    (hC : ∀ i ∈ C, (mismatch R ell C base i).card + (outOn R G i).card ≤  q)
    (hG : ∀ i ∈ G, (mismatch R ell C base i).card + (outOn R G i).card ≤  q+1) :
    ∃ (S : Finset V) (color : V → Fin 2),
      C.card + G.card ≤  S.card + 1 ∧ OrdinaryGood R ell S q color := by
  let RG : G → G → Prop := fun i j => R i.1 j.1
  have hTG : ∀ i j : G, i ≠ j → RG i j ∨ RG j i := by
    intro i j hij
    exact ht i.1 j.1 (fun he => hij (Subtype.ext he))
  obtain ⟨colG,bad,hbad,hcover⟩ :=
    exists_near_coloring RG hTG (fun i j => ell (i.1,j.1))
  let B : Finset V := bad.image Subtype.val
  have hBG : B ⊆ G := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hBcard : B.card ≤  1 := (Finset.card_image_le).trans hbad
  let K := G \ B
  let S := C ∪ K
  let color : V → Fin 2 := fun x => if hx : x ∈ G then colG ⟨x,hx⟩ else base x
  have hcolorC (x : V) (hx : x ∈ C) : color x = base x := by
    have hnot : x ∉ G := fun hg => Finset.disjoint_left.mp hdis hx hg
    simp only [color,dif_neg hnot]
  have hmatch (i : V) (hi : i ∈ K) :
      ∃ j ∈ G, R i j ∧ ell (i,j) = color j := by
    obtain ⟨hiG,hiB⟩ := Finset.mem_sdiff.mp hi
    have hin : (⟨i,hiG⟩ : G) ∉ bad := by
      intro hb
      exact hiB (Finset.mem_image.mpr ⟨⟨i,hiG⟩,hb,rfl⟩)
    obtain ⟨j,hij,hcol⟩ := hcover ⟨i,hiG⟩ hin
    refine ⟨j.1,j.2,hij,?_⟩
    simpa only [color,dif_pos j.2] using hcol
  let charges (i : V) := mismatch R ell C base i ∪ outOn R G i
  have hchargecard (i : V) : (charges i).card =
      (mismatch R ell C base i).card + (outOn R G i).card := by
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hk).1
  have hsub (i : V) : mismatch R ell S color i ⊆ charges i := by
    intro j hj
    obtain ⟨hjS,hij,hne⟩ := Finset.mem_filter.mp hj
    rcases Finset.mem_union.mp hjS with hjC | hjK
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hjC,hij,by simpa only [hcolorC j hjC] using hne⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp hjK).1,hij⟩)
  refine ⟨S,color,?_,?_⟩
  · have hdCK : Disjoint C K := by
      apply Finset.disjoint_left.mpr
      intro i hi hk
      exact Finset.disjoint_left.mp hdis hi (Finset.mem_sdiff.mp hk).1
    have hs : S.card = C.card + K.card := Finset.card_union_of_disjoint hdCK
    have hg : K.card + B.card = G.card := Finset.card_sdiff_add_card_eq_card hBG
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hiC | hiK
    · have hh := hC i hiC
      rw [← hchargecard i] at hh
      exact (Finset.card_le_card (hsub i)).trans hh
    · obtain ⟨j,hjG,hij,hcol⟩ := hmatch i hiK
      have hjcharges : j ∈ charges i := Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hjG,hij⟩)
      have hjnot : j ∉ mismatch R ell S color i := by
        intro hj
        exact (Finset.mem_filter.mp hj).2.2 hcol
      have herase : mismatch R ell S color i ⊆ (charges i).erase j := by
        intro y hy
        exact Finset.mem_erase.mpr ⟨fun he => hjnot (he ▸ hy),hsub i hy⟩
      have hh := hG i (Finset.mem_sdiff.mp hiK).1
      have hc := Finset.card_le_card herase
      rw [Finset.card_erase_of_mem hjcharges,hchargecard i] at hc
      omega

end CompactTournament
end
end z39

section z40

set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
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
open OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



















end ZT
end
end z43

section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









end ZT
end
end z45

end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution.{u_1} :
∀ {V : Type u_1} [Fintype.{u_1} V] [DecidableEq.{u_1 + 1} V] (R : V → V → Prop)
  (ht : ∀ (x y : V), @Ne.{u_1 + 1} V x y → Or (R x y) (R y x))
  (ell : Prod.{u_1, u_1} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (C G : Finset.{u_1} V)
  (hdis : @Disjoint.{u_1} (Finset.{u_1} V) (@Finset.instPartialOrder.{u_1} V) (@Finset.instOrderBot.{u_1} V) C G)
  (q : Nat) (base : V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hC :
    ∀ (i : V),
      @Membership.mem.{u_1, u_1} V (Finset.{u_1} V)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} V) V (@Finset.instSetLike.{u_1} V)) C i →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Finset.card.{u_1} V
              (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.mismatch.{u_1} V R ell C base i))
            (@Finset.card.{u_1} V (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.outOn.{u_1} V R G i)))
          q)
  (hG :
    ∀ (i : V),
      @Membership.mem.{u_1, u_1} V (Finset.{u_1} V)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} V) V (@Finset.instSetLike.{u_1} V)) G i →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Finset.card.{u_1} V
              (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.mismatch.{u_1} V R ell C base i))
            (@Finset.card.{u_1} V (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.outOn.{u_1} V R G i)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @Exists.{u_1 + 1} (Finset.{u_1} V) fun (S : Finset.{u_1} V) =>
    @Exists.{u_1 + 1} (V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      fun (color : V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
      And
        (@LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{u_1} V C)
            (@Finset.card.{u_1} V G))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{u_1} V S)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.OrdinaryGood.{u_1} V R ell S q color) := @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.CompactTournament.augment_by_guards.{u_1}
