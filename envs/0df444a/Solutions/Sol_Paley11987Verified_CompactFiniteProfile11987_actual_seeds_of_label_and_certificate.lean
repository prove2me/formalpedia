-- Prove2me | solution 1 for Paley11987Verified.CompactFiniteProfile11987.actual_seeds_of_label_and_certificate
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:21:55.927717+00:00
-- url     : https://prove2.me/submissions/30a88b3a-1d4c-486d-9bc1-81c9ca63039a

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
import Definitions.Def_Paley11987Support_053
import Definitions.Def_Paley11987Support_054
import Definitions.Def_Paley11987Support_055
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_families_at_every_cycle

set_option autoImplicit false
set_option Elab.async false
section z55

noncomputable section
open OAI.Paper320 ZT CompactFiniteProfileClosures

namespace ZP
variable {I : Type} [Fintype I]







 

 

 theorem ScaledBounds.sensitivity {F : Fin 20 → (I → Bool) → Bool}
    {v : Profile} {c : ℕ} (hv : ScaledBounds F v c) (i : Fin 20) :
    sensitivity (F i) ≤ c*max (A v i i) (B v i i) := by
  apply Finset.sup_le
  intro x _
  cases hx : F i x with
  | false =>
      have ha := hv.a i i le_rfl x hx
      have he : sensitivityAt (F i) x = (flipsTo (F i) true x).card := by
        simp [sensitivityAt, flipsTo, hx]
      rw [he]
      exact ha.trans (Nat.mul_le_mul_left c (le_max_left _ _))
  | true =>
      have hb := hv.b i i le_rfl x hx
      have he : sensitivityAt (F i) x = (flipsTo (F i) false x).card := by
        simp [sensitivityAt, flipsTo, hx]
      rw [he]
      exact hb.trans (Nat.mul_le_mul_left c (le_max_right _ _))

end ZP
end
end z55

section z74

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical
open OAI.Paper320 Sensitivity2075

namespace CompactFiniteProfileSeeds



 

 

 

 

 
 

 

 

 

 

 

 

 

 theorem Blocks.lower {h : ℕ} {I : Type} [Fintype I]
    {F : Fin h → (I → Bool) → Bool} {n : ℕ} (w : Blocks F n) (q : Fin h) :
    n ≤ blockSensitivity (F q) := by
  have hinj : Function.Injective w.sets := by
    intro i j he
    by_contra hne
    obtain ⟨a,ha⟩ := w.nonempty i
    exact Finset.disjoint_left.mp (w.disjoint hne) ha (he ▸ ha)
  let bs := Finset.univ.image w.sets
  have hc : bs.card = n := by simp [bs,Finset.card_image_of_injective _ hinj]
  have hvalid : (∀ A ∈ bs, ∀ B ∈ bs, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ bs, B.Nonempty ∧ F q (flip (fun _ => false) B) ≠ F q (fun _ => false)) := by
    constructor
    · intro A hA B hB hne
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
      exact w.disjoint (fun he => hne (congrArg w.sets he))
    · intro B hB
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hB
      exact ⟨w.nonempty i,by rw [w.on,w.zero]; decide⟩
  have hat : n ≤ blockSensitivityAt (F q) (fun _ => false) := by
    unfold blockSensitivityAt
    rw [← hc]
    let score : Finset (Finset I) → ℕ := fun blocks =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ F q (flip (fun _ => false) B) ≠ F q (fun _ => false))
          then blocks.card else 0
    have hs : score bs ≤ Finset.univ.sup score := Finset.le_sup (Finset.mem_univ bs)
    simpa only [score,if_pos hvalid] using hs
  exact hat.trans (show blockSensitivityAt (F q) (fun _ => false) ≤
      blockSensitivity (F q) from Finset.le_sup (Finset.mem_univ (fun _ => false)))

 

 

 theorem SensitiveWitness.lower {h : ℕ} {I : Type} [Fintype I]
    {F : Fin h → (I → Bool) → Bool} {n : ℕ}
    (w : SensitiveWitness F n) (q : Fin h) : n ≤ sensitivity (F q) := by
  have hs : w.bits ⊆ Finset.univ.filter fun a => F q (flip w.input {a}) ≠ F q w.input := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [w.off q a ha,w.on q]; decide⟩
  have hcard := Finset.card_le_card hs
  rw [w.card] at hcard
  have hat : n ≤ sensitivityAt (F q) w.input := hcard
  exact hat.trans (show sensitivityAt (F q) w.input ≤ sensitivity (F q) from
    Finset.le_sup (Finset.mem_univ w.input))

end CompactFiniteProfileSeeds
end
end z74

section z78
namespace ZP
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000










theorem witness_output : max (A witness 0 0) (B witness 0 0) = C := by decide +kernel























end ZP
end z78

section z81

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical
open OAI.Paper320
namespace CompactFiniteProfileSeeds
variable {I J : Type}





theorem flip_reindex_singleton (e : I ≃ J) (x : J → Bool) (i : I) :
    (fun a => OAI.Paper320.flip x {e i} (e a)) =
      OAI.Paper320.flip (fun a => x (e a)) {i} := by
  simpa using flip_reindex e x {i}



section Finite
variable [Fintype I] [Fintype J]

theorem sensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool) (x : J → Bool) :
    sensitivityAt (reindex e f) x = sensitivityAt f (fun i => x (e i)) := by
  have hs : (Finset.univ.filter fun j =>
      reindex e f (OAI.Paper320.flip x {j}) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (OAI.Paper320.flip (fun a => x (e a)) {i}) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => OAI.Paper320.flip x {e i} (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [flip_reindex_singleton]
  simpa only [sensitivityAt, Finset.card_map] using congrArg Finset.card hs

theorem sensitivity_reindex (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x _
    rw [sensitivityAt_reindex]
    exact Finset.le_sup (Finset.mem_univ _)
  · apply Finset.sup_le
    intro x _
    have h : sensitivityAt (reindex e f) (fun j => x (e.symm j)) ≤
        sensitivity (reindex e f) := Finset.le_sup (Finset.mem_univ _)
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

end Finite



end CompactFiniteProfileSeeds
end
end z81

section z86

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileSeeds
namespace ZP



theorem _root_.solution (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2) (hCaps : LabelCaps T label)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = 5993)
    (hc : PeriodCertificate) : ActualSeedStatement := by
  intro m
  rcases _root_.Paley11987Verified.CompactFiniteProfile11987.families_at_every_cycle T label hCaps hd hc m with ⟨I,inst,F,hF,hv,⟨wb⟩,⟨ws⟩⟩
  letI := inst
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I,reindex e (F 0),?_,?_,?_⟩
  · rw [sensitivity_reindex]
    exact ws.lower 0
  · rw [sensitivity_reindex]
    have h := hv.sensitivity 0
    change sensitivity (F 0) ≤ R^m * max (A witness 0 0) (B witness 0 0) at h
    rw [witness_output] at h
    simpa only [C,R,Nat.mul_comm] using h
  · exact (wb.reindex e).lower 0

end ZP
end
end z86
