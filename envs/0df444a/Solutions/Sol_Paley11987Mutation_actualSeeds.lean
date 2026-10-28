-- Prove2me | solution 1 for Paley11987Mutation.actualSeeds
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-27T08:36:55.840149+00:00
-- url     : https://prove2.me/submissions/2c2838c3-765f-48a5-bba5-906ff95d61af

import Definitions.Def_Paley11987MutationData
import Definitions.Def_Paley11987MutationFastData
import Definitions.Def_Paley11987Support_053
import Definitions.Def_Paley11987Support_055
import Theorems.Thm_Paley11987Mutation_fastTransition0
import Theorems.Thm_Paley11987Mutation_fastTransition1
import Theorems.Thm_Paley11987Mutation_fastTransition2
import Theorems.Thm_Paley11987Mutation_fastTransition3
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_actual_rawStep
import Theorems.Thm_Paley11987Verified_CompactBooleanTransfer_selected_exists_labelCaps
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option Elab.async false
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















@[simp] theorem mem_failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) :
    j ∈ failedGuards T label F G x i ↔
      T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true := by
  simp [failedGuards]









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

include hF in
theorem failedGuards_subset {Gi Gj : Fin n} (hG : Gj ≤ Gi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    failedGuards T label F Gi x i ⊆ failedGuards T label F Gj x i := by
  intro j hj
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F Gi x i j).mp hj
  exact (mem_failedGuards T label F Gj x i j).mpr ⟨hij, hF.accepts_of_le hG hon⟩

include hF in
theorem tolerantRow_nested {Ai Aj Gi Gj : Fin n} {qi qj : ℕ}
    (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hq : qj ≤ qi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : tolerantRow T label F Aj Gj qj x i = true) :
    tolerantRow T label F Ai Gi qi x i = true := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F Aj Gj qj x i).mp hi
  exact (tolerantRow_true T label F Ai Gi qi x i).mpr
    ⟨fun c => hF.accepts_of_le hA (ht c),
      (Finset.card_le_card (failedGuards_subset T label F hF hG x i)).trans (hg.trans hq)⟩

end Nesting











section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29

section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]























theorem family_nested {n k r : ℕ} {J : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (J → Bool) → Bool) (hF : NestedFamily F)
    {Ai Aj Gi Gj : Fin n} {qi qj : ℕ}
    (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hq : qj ≤ qi)
    (x : ((Fin k × Fin r) × J) → Bool)
    (hx : tolerantFamily T label F Aj Gj qj x = true) :
    tolerantFamily T label F Ai Gi qi x = true := by
  obtain ⟨v, hv⟩ := (tolerantFamily_true T label F Aj Gj qj x).mp hx
  exact (tolerantFamily_true T label F Ai Gi qi x).mpr
    ⟨v, tolerantRow_nested T label F hF hA hG hq x v hv⟩



end ZT
end
end z30

section z54

set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
open OAI.Paper320 ZT

namespace CompactFiniteProfileClosures
variable {h : ℕ} {I : Type} [Fintype I]
variable {F : Fin h → (I → Bool) → Bool}

 theorem a_mono {i j : Fin h} {a b : ℕ} (hab : a ≤ b)
    (ha : ABound F i j a) : ABound F i j b :=
  fun x hx => (ha x hx).trans hab
 theorem b_mono {i j : Fin h} {a b : ℕ} (hab : a ≤ b)
    (ha : BBound F i j a) : BBound F i j b :=
  fun x hx => (ha x hx).trans hab
 theorem m_mono {i j k : Fin h} {a b : ℕ} (hab : a ≤ b)
    (ha : MBound F i j k a) : MBound F i j k b :=
  fun x hj hk => (ha x hj hk).trans hab
 theorem p_mono {i j k : Fin h} {a b : ℕ} (hab : a ≤ b)
    (ha : PBound F i j k a) : PBound F i j k b :=
  fun x hj hk => (ha x hj hk).trans hab
 theorem d_mono {i j k l : Fin h} {a b : ℕ} (hab : a ≤ b)
    (ha : DBound F i j k l a) : DBound F i j k l b :=
  fun x hj hk => (ha x hj hk).trans hab

 
 

 
 
 
 
 
 
 
 
 
 

 

 

 

end CompactFiniteProfileClosures
end
end z54

section z55

noncomputable section
open OAI.Paper320 ZT CompactFiniteProfileClosures

namespace ZP
variable {I : Type} [Fintype I]







 theorem RawStepBounds.refine {G : Fin 20 → (I → Bool) → Bool}
    {v w : Profile} {r : Recipe} {c : ℕ}
    (hc : TransitionCertificate v r w) (hg : RawStepBounds G v r c) :
    ScaledBounds G w c := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i j hij
    exact a_mono (Nat.mul_le_mul_left c (hc.a i j hij)) (hg.a i j hij)
  · intro i j hij
    exact b_mono (Nat.mul_le_mul_left c (hc.b i j hij)) (hg.b i j hij)
  · intro i j hij hn
    exact m_mono (Nat.mul_le_mul_left c (hc.m i j hij hn)) (hg.m i j hij hn)
  · intro j l hjl hn
    exact p_mono (Nat.mul_le_mul_left c (hc.p j l hjl)) (hg.p j l hjl hn)
  · intro i j l hij hjl hn
    exact d_mono (Nat.mul_le_mul_left c (hc.d i j l hij hjl)) (hg.d i j l hij hjl hn)

 theorem ScaledBounds.mono {F : Fin 20 → (I → Bool) → Bool}
    {v w : Profile} {c d : ℕ} (hv : ScaledBounds F v c)
    (hvw : ∀ n, c*entry v n ≤ d*entry w n) : ScaledBounds F w d := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i j hij
    exact a_mono (hvw (aIndex i j)) (hv.a i j hij)
  · intro i j hij
    exact b_mono (hvw (bIndex i j)) (hv.b i j hij)
  · intro i j hij hn
    exact m_mono (hvw (mIndex i j)) (hv.m i j hij hn)
  · intro j l hjl hn
    exact p_mono (hvw (pIndex j l)) (hv.p j l hjl hn)
  · intro i j l hij hjl hn
    exact d_mono (hvw (dIndex i j l)) (hv.d i j l hij hjl hn)

 

end ZP
end
end z55

section z57

set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileClosures
namespace ZP
variable {I : Type} [Fintype I]

















theorem stageFamily_nested {k : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin 20 → (I → Bool) → Bool) (hF : NestedFamily F)
    (r : Recipe) (hr : RecipeValid r) : NestedFamily (stageFamily T label F r hr) := by
  constructor
  intro i j x hij hx
  exact family_nested T label F hF (hr.target_mono i j hij) (hr.guard_antitone i j hij)
    (hr.tol_antitone i j hij) x hx

end ZP
end
end z57

section z73

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileClosures
namespace ZP
variable {I : Type} [Fintype I]





theorem actual_profile_transition {k : ℕ} (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hCaps : LabelCaps T label)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = 5993)
    (F : Fin 20 → (I → Bool) → Bool) (hF : NestedFamily F)
    (v w : Profile) (c : ℕ) (hv : ScaledBounds F v c)
    (r : Recipe) (hr : RecipeValid r) (hcost : GuardCostOrder v r)
    (hcert : TransitionCertificate v r w) :
    ScaledBounds (stageFamily T label F r hr) w c ∧ NestedFamily (stageFamily T label F r hr) := by
  exact ⟨RawStepBounds.refine hcert (_root_.Paley11987Verified.CompactFiniteProfile11987.actual_rawStep T label hCaps hd F hF v c hv r hr hcost),
    stageFamily_nested T label F hF r hr⟩

end ZP
end
end z73
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
section z49

namespace CompactDRT
open Finset
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Core
variable (C : Core V)














theorem edge_identity (x y : V) : 2 * C.edge x y = 1 + C.sign x y - delta x y := by
  by_cases h : x = y
  · subst y; simp [edge, Adj, C.diag]
  · rcases C.off x y h with hs | hs <;> simp [edge, Adj, hs, delta, h]

theorem sum_edge (x : V) : ∑ z, C.edge x z = (C.outCount x : ℤ) := by
  simp [edge, outCount, Finset.sum_boole]



theorem degree_identity (x : V) :
    2 * (C.outCount x : ℤ) = (Fintype.card V : ℤ) - 1 := by
  have hs := Finset.sum_congr (s₁ := (univ : Finset V)) rfl (fun z _ => C.edge_identity x z)
  simpa [← Finset.mul_sum, C.sum_edge, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, C.row] using hs











end Core

end
end CompactDRT
end z49

section z50

namespace CompactDRT
noncomputable section
open Finset









attribute [local irreducible] core11987




theorem outdegree11987 (x : Vertex11987) : (univ.filter (Adj11987 x)).card = 5993 := by
  have h := core11987.degree_identity x
  rw [vertex11987_card] at h
  change 2 * ((univ.filter (Adj11987 x)).card : ℤ) = _ at h
  omega







end
end CompactDRT
end z50

section z51

set_option maxHeartbeats 300000
noncomputable section
open scoped Classical

namespace ZT
open CompactDRT OAI.Paper320
attribute [local irreducible] core11987



theorem card_filter_of_equiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (P : V → Prop) (Q : W → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ x, P x ↔ Q (e x)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(h x).mp (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact e.injective he
  · intro y hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(h (e.symm y)).mpr ?_⟩
    simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hy).2



theorem transported_outdegree {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (G : Core V) (e : Fin k ≃ V) (i : Fin k) :
    (Finset.univ.filter ((tournamentOfCore G e).Adj i)).card =
      (Finset.univ.filter (G.Adj (e i))).card := by
  exact card_filter_of_equiv e _ _ (fun _ => Iff.rfl)









theorem selected_outdegree (i : Fin 11987) :
    (Finset.univ.filter (selectedTournament.Adj i)).card = 5993 :=
  (transported_outdegree core11987 selectedEquiv i).trans (outdegree11987 (selectedEquiv i))







end ZT
end
end z51
section z80

noncomputable section
open scoped Classical
open OAI.Paper320 Sensitivity2075 ZT
open ZP
namespace CompactFiniteProfileSeeds







 theorem leaf_nested : NestedFamily leaf := by
  constructor
  intro i j x hij hx
  exact hx

 theorem leaf_bounds (v : Profile)
    (ha : ∀ i j : Fin 20, i ≤ j → 1 ≤ A v i j)
    (hb : ∀ i j : Fin 20, i ≤ j → 1 ≤ B v i j) :
    ScaledBounds leaf v 1 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i j hij x hx
    have h : (flipsTo (leaf j) true x).card ≤ 1 := by
      simpa using Finset.card_le_card (Finset.subset_univ (flipsTo (leaf j) true x))
    simpa only [Nat.one_mul] using h.trans (ha i j hij)
  · intro i j hij x hx
    have h : (flipsTo (leaf i) false x).card ≤ 1 := by
      simpa using Finset.card_le_card (Finset.subset_univ (flipsTo (leaf i) false x))
    simpa only [Nat.one_mul] using h.trans (hb i j hij)
  · intro i j hij hn x ht hf
    change x 0 = true at ht
    change x 0 = false at hf
    rw [ht] at hf
    contradiction
  · intro j l hjl hn x ht hf
    change x 0 = true at ht
    change x 0 = false at hf
    rw [ht] at hf
    contradiction
  · intro i j l hij hjl hn x ht hf
    change x 0 = true at ht
    change x 0 = false at hf
    rw [ht] at hf
    contradiction

end CompactFiniteProfileSeeds
end
end z80

namespace Paley11987Mutation

noncomputable section
open scoped Classical
open OAI.Paper320 Sensitivity2075 ZT ZP
open CompactFiniteProfileSeeds

abbrev candidateWitness := Paley11987MutationFast.witness
abbrev candidateStage1 := Paley11987MutationFast.stage1
abbrev candidateStage2 := Paley11987MutationFast.stage2
abbrev candidateStage3 := Paley11987MutationFast.stage3
abbrev candidateStage4 := Paley11987MutationFast.stage4
abbrev candidateRecipe0 := recipe0
abbrev candidateRecipe1 := recipe1
abbrev candidateRecipe2 := recipe2
abbrev candidateRecipe3 := recipe3
abbrev candidateR := radius
abbrev candidateC := initialConstant
theorem candidateRecipe0Valid : ZP.RecipeValid candidateRecipe0 := ZP.recipe0_valid
theorem candidateRecipe2Valid : ZP.RecipeValid candidateRecipe2 := ZP.recipe2_valid
theorem candidateRecipe3Valid : ZP.RecipeValid candidateRecipe3 := ZP.recipe3_valid
theorem recipe1targetRow0 (j : Nat)
    (lower : 0 ≤ j) (upper : j < 20) : (candidateRecipe1[0]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow1 (j : Nat)
    (lower : 1 ≤ j) (upper : j < 20) : (candidateRecipe1[1]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow2 (j : Nat)
    (lower : 2 ≤ j) (upper : j < 20) : (candidateRecipe1[2]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow3 (j : Nat)
    (lower : 3 ≤ j) (upper : j < 20) : (candidateRecipe1[3]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow4 (j : Nat)
    (lower : 4 ≤ j) (upper : j < 20) : (candidateRecipe1[4]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow5 (j : Nat)
    (lower : 5 ≤ j) (upper : j < 20) : (candidateRecipe1[5]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow6 (j : Nat)
    (lower : 6 ≤ j) (upper : j < 20) : (candidateRecipe1[6]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow7 (j : Nat)
    (lower : 7 ≤ j) (upper : j < 20) : (candidateRecipe1[7]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow8 (j : Nat)
    (lower : 8 ≤ j) (upper : j < 20) : (candidateRecipe1[8]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow9 (j : Nat)
    (lower : 9 ≤ j) (upper : j < 20) : (candidateRecipe1[9]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow10 (j : Nat)
    (lower : 10 ≤ j) (upper : j < 20) : (candidateRecipe1[10]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow11 (j : Nat)
    (lower : 11 ≤ j) (upper : j < 20) : (candidateRecipe1[11]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow12 (j : Nat)
    (lower : 12 ≤ j) (upper : j < 20) : (candidateRecipe1[12]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow13 (j : Nat)
    (lower : 13 ≤ j) (upper : j < 20) : (candidateRecipe1[13]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow14 (j : Nat)
    (lower : 14 ≤ j) (upper : j < 20) : (candidateRecipe1[14]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow15 (j : Nat)
    (lower : 15 ≤ j) (upper : j < 20) : (candidateRecipe1[15]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow16 (j : Nat)
    (lower : 16 ≤ j) (upper : j < 20) : (candidateRecipe1[16]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow17 (j : Nat)
    (lower : 17 ≤ j) (upper : j < 20) : (candidateRecipe1[17]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow18 (j : Nat)
    (lower : 18 ≤ j) (upper : j < 20) : (candidateRecipe1[18]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetRow19 (j : Nat)
    (lower : 19 ≤ j) (upper : j < 20) : (candidateRecipe1[19]?.getD default).target ≤ (candidateRecipe1[j]?.getD default).target := by
  interval_cases j <;> decide +kernel

theorem recipe1targetAll (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    (candidateRecipe1[i]?.getD default).target ≤
      (candidateRecipe1[j]?.getD default).target := by
  interval_cases i
  · exact recipe1targetRow0 j firstOrder upper
  · exact recipe1targetRow1 j firstOrder upper
  · exact recipe1targetRow2 j firstOrder upper
  · exact recipe1targetRow3 j firstOrder upper
  · exact recipe1targetRow4 j firstOrder upper
  · exact recipe1targetRow5 j firstOrder upper
  · exact recipe1targetRow6 j firstOrder upper
  · exact recipe1targetRow7 j firstOrder upper
  · exact recipe1targetRow8 j firstOrder upper
  · exact recipe1targetRow9 j firstOrder upper
  · exact recipe1targetRow10 j firstOrder upper
  · exact recipe1targetRow11 j firstOrder upper
  · exact recipe1targetRow12 j firstOrder upper
  · exact recipe1targetRow13 j firstOrder upper
  · exact recipe1targetRow14 j firstOrder upper
  · exact recipe1targetRow15 j firstOrder upper
  · exact recipe1targetRow16 j firstOrder upper
  · exact recipe1targetRow17 j firstOrder upper
  · exact recipe1targetRow18 j firstOrder upper
  · exact recipe1targetRow19 j firstOrder upper

theorem recipe1guardRow0 (j : Nat)
    (lower : 0 ≤ j) (upper : j < 20) : (candidateRecipe1[0]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow1 (j : Nat)
    (lower : 1 ≤ j) (upper : j < 20) : (candidateRecipe1[1]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow2 (j : Nat)
    (lower : 2 ≤ j) (upper : j < 20) : (candidateRecipe1[2]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow3 (j : Nat)
    (lower : 3 ≤ j) (upper : j < 20) : (candidateRecipe1[3]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow4 (j : Nat)
    (lower : 4 ≤ j) (upper : j < 20) : (candidateRecipe1[4]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow5 (j : Nat)
    (lower : 5 ≤ j) (upper : j < 20) : (candidateRecipe1[5]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow6 (j : Nat)
    (lower : 6 ≤ j) (upper : j < 20) : (candidateRecipe1[6]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow7 (j : Nat)
    (lower : 7 ≤ j) (upper : j < 20) : (candidateRecipe1[7]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow8 (j : Nat)
    (lower : 8 ≤ j) (upper : j < 20) : (candidateRecipe1[8]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow9 (j : Nat)
    (lower : 9 ≤ j) (upper : j < 20) : (candidateRecipe1[9]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow10 (j : Nat)
    (lower : 10 ≤ j) (upper : j < 20) : (candidateRecipe1[10]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow11 (j : Nat)
    (lower : 11 ≤ j) (upper : j < 20) : (candidateRecipe1[11]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow12 (j : Nat)
    (lower : 12 ≤ j) (upper : j < 20) : (candidateRecipe1[12]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow13 (j : Nat)
    (lower : 13 ≤ j) (upper : j < 20) : (candidateRecipe1[13]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow14 (j : Nat)
    (lower : 14 ≤ j) (upper : j < 20) : (candidateRecipe1[14]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow15 (j : Nat)
    (lower : 15 ≤ j) (upper : j < 20) : (candidateRecipe1[15]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow16 (j : Nat)
    (lower : 16 ≤ j) (upper : j < 20) : (candidateRecipe1[16]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow17 (j : Nat)
    (lower : 17 ≤ j) (upper : j < 20) : (candidateRecipe1[17]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow18 (j : Nat)
    (lower : 18 ≤ j) (upper : j < 20) : (candidateRecipe1[18]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardRow19 (j : Nat)
    (lower : 19 ≤ j) (upper : j < 20) : (candidateRecipe1[19]?.getD default).guard ≥ (candidateRecipe1[j]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem recipe1guardAll (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    (candidateRecipe1[i]?.getD default).guard ≥
      (candidateRecipe1[j]?.getD default).guard := by
  interval_cases i
  · exact recipe1guardRow0 j firstOrder upper
  · exact recipe1guardRow1 j firstOrder upper
  · exact recipe1guardRow2 j firstOrder upper
  · exact recipe1guardRow3 j firstOrder upper
  · exact recipe1guardRow4 j firstOrder upper
  · exact recipe1guardRow5 j firstOrder upper
  · exact recipe1guardRow6 j firstOrder upper
  · exact recipe1guardRow7 j firstOrder upper
  · exact recipe1guardRow8 j firstOrder upper
  · exact recipe1guardRow9 j firstOrder upper
  · exact recipe1guardRow10 j firstOrder upper
  · exact recipe1guardRow11 j firstOrder upper
  · exact recipe1guardRow12 j firstOrder upper
  · exact recipe1guardRow13 j firstOrder upper
  · exact recipe1guardRow14 j firstOrder upper
  · exact recipe1guardRow15 j firstOrder upper
  · exact recipe1guardRow16 j firstOrder upper
  · exact recipe1guardRow17 j firstOrder upper
  · exact recipe1guardRow18 j firstOrder upper
  · exact recipe1guardRow19 j firstOrder upper

theorem recipe1tolRow0 (j : Nat)
    (lower : 0 ≤ j) (upper : j < 20) : (candidateRecipe1[0]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow1 (j : Nat)
    (lower : 1 ≤ j) (upper : j < 20) : (candidateRecipe1[1]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow2 (j : Nat)
    (lower : 2 ≤ j) (upper : j < 20) : (candidateRecipe1[2]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow3 (j : Nat)
    (lower : 3 ≤ j) (upper : j < 20) : (candidateRecipe1[3]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow4 (j : Nat)
    (lower : 4 ≤ j) (upper : j < 20) : (candidateRecipe1[4]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow5 (j : Nat)
    (lower : 5 ≤ j) (upper : j < 20) : (candidateRecipe1[5]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow6 (j : Nat)
    (lower : 6 ≤ j) (upper : j < 20) : (candidateRecipe1[6]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow7 (j : Nat)
    (lower : 7 ≤ j) (upper : j < 20) : (candidateRecipe1[7]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow8 (j : Nat)
    (lower : 8 ≤ j) (upper : j < 20) : (candidateRecipe1[8]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow9 (j : Nat)
    (lower : 9 ≤ j) (upper : j < 20) : (candidateRecipe1[9]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow10 (j : Nat)
    (lower : 10 ≤ j) (upper : j < 20) : (candidateRecipe1[10]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow11 (j : Nat)
    (lower : 11 ≤ j) (upper : j < 20) : (candidateRecipe1[11]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow12 (j : Nat)
    (lower : 12 ≤ j) (upper : j < 20) : (candidateRecipe1[12]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow13 (j : Nat)
    (lower : 13 ≤ j) (upper : j < 20) : (candidateRecipe1[13]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow14 (j : Nat)
    (lower : 14 ≤ j) (upper : j < 20) : (candidateRecipe1[14]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow15 (j : Nat)
    (lower : 15 ≤ j) (upper : j < 20) : (candidateRecipe1[15]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow16 (j : Nat)
    (lower : 16 ≤ j) (upper : j < 20) : (candidateRecipe1[16]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow17 (j : Nat)
    (lower : 17 ≤ j) (upper : j < 20) : (candidateRecipe1[17]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow18 (j : Nat)
    (lower : 18 ≤ j) (upper : j < 20) : (candidateRecipe1[18]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolRow19 (j : Nat)
    (lower : 19 ≤ j) (upper : j < 20) : (candidateRecipe1[19]?.getD default).tol ≥ (candidateRecipe1[j]?.getD default).tol := by
  interval_cases j <;> decide +kernel

theorem recipe1tolAll (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    (candidateRecipe1[i]?.getD default).tol ≥
      (candidateRecipe1[j]?.getD default).tol := by
  interval_cases i
  · exact recipe1tolRow0 j firstOrder upper
  · exact recipe1tolRow1 j firstOrder upper
  · exact recipe1tolRow2 j firstOrder upper
  · exact recipe1tolRow3 j firstOrder upper
  · exact recipe1tolRow4 j firstOrder upper
  · exact recipe1tolRow5 j firstOrder upper
  · exact recipe1tolRow6 j firstOrder upper
  · exact recipe1tolRow7 j firstOrder upper
  · exact recipe1tolRow8 j firstOrder upper
  · exact recipe1tolRow9 j firstOrder upper
  · exact recipe1tolRow10 j firstOrder upper
  · exact recipe1tolRow11 j firstOrder upper
  · exact recipe1tolRow12 j firstOrder upper
  · exact recipe1tolRow13 j firstOrder upper
  · exact recipe1tolRow14 j firstOrder upper
  · exact recipe1tolRow15 j firstOrder upper
  · exact recipe1tolRow16 j firstOrder upper
  · exact recipe1tolRow17 j firstOrder upper
  · exact recipe1tolRow18 j firstOrder upper
  · exact recipe1tolRow19 j firstOrder upper

theorem candidateRecipe1Valid : ZP.RecipeValid candidateRecipe1 where
  target_lt i := by fin_cases i <;> decide +kernel
  guard_lt i := by fin_cases i <;> decide +kernel
  guard_target i := by fin_cases i <;> decide +kernel
  target_mono i j order :=
    recipe1targetAll i.val j.val i.isLt order j.isLt
  guard_antitone i j order :=
    recipe1guardAll i.val j.val i.isLt order j.isLt
  tol_antitone i j order :=
    recipe1tolAll i.val j.val i.isLt order j.isLt
  tol_le i := by fin_cases i <;> decide +kernel
theorem guard0Row0 (j : Nat) (lower : 0 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[0]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row1 (j : Nat) (lower : 1 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[1]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row2 (j : Nat) (lower : 2 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[2]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row3 (j : Nat) (lower : 3 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[3]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row4 (j : Nat) (lower : 4 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[4]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row5 (j : Nat) (lower : 5 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[5]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row6 (j : Nat) (lower : 6 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[6]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row7 (j : Nat) (lower : 7 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[7]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row8 (j : Nat) (lower : 8 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[8]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row9 (j : Nat) (lower : 9 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[9]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row10 (j : Nat) (lower : 10 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[10]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row11 (j : Nat) (lower : 11 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[11]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row12 (j : Nat) (lower : 12 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[12]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row13 (j : Nat) (lower : 13 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[13]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row14 (j : Nat) (lower : 14 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[14]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row15 (j : Nat) (lower : 15 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[15]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row16 (j : Nat) (lower : 16 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[16]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row17 (j : Nat) (lower : 17 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[17]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row18 (j : Nat) (lower : 18 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[18]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0Row19 (j : Nat) (lower : 19 ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[19]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard0All (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[j]?.getD default).target ≤
    ZP.B candidateWitness (candidateRecipe0[j]?.getD default).guard
      (candidateRecipe0[i]?.getD default).guard := by
  interval_cases i
  · exact guard0Row0 j firstOrder upper
  · exact guard0Row1 j firstOrder upper
  · exact guard0Row2 j firstOrder upper
  · exact guard0Row3 j firstOrder upper
  · exact guard0Row4 j firstOrder upper
  · exact guard0Row5 j firstOrder upper
  · exact guard0Row6 j firstOrder upper
  · exact guard0Row7 j firstOrder upper
  · exact guard0Row8 j firstOrder upper
  · exact guard0Row9 j firstOrder upper
  · exact guard0Row10 j firstOrder upper
  · exact guard0Row11 j firstOrder upper
  · exact guard0Row12 j firstOrder upper
  · exact guard0Row13 j firstOrder upper
  · exact guard0Row14 j firstOrder upper
  · exact guard0Row15 j firstOrder upper
  · exact guard0Row16 j firstOrder upper
  · exact guard0Row17 j firstOrder upper
  · exact guard0Row18 j firstOrder upper
  · exact guard0Row19 j firstOrder upper

theorem candidateGuardCost0 : ZP.GuardCostOrder candidateWitness candidateRecipe0 := by
  intro i j order
  exact guard0All i.val j.val i.isLt order j.isLt

theorem guard1Row0 (j : Nat) (lower : 0 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[0]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row1 (j : Nat) (lower : 1 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[1]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row2 (j : Nat) (lower : 2 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[2]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row3 (j : Nat) (lower : 3 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[3]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row4 (j : Nat) (lower : 4 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[4]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row5 (j : Nat) (lower : 5 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[5]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row6 (j : Nat) (lower : 6 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[6]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row7 (j : Nat) (lower : 7 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[7]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row8 (j : Nat) (lower : 8 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[8]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row9 (j : Nat) (lower : 9 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[9]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row10 (j : Nat) (lower : 10 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[10]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row11 (j : Nat) (lower : 11 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[11]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row12 (j : Nat) (lower : 12 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[12]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row13 (j : Nat) (lower : 13 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[13]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row14 (j : Nat) (lower : 14 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[14]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row15 (j : Nat) (lower : 15 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[15]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row16 (j : Nat) (lower : 16 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[16]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row17 (j : Nat) (lower : 17 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[17]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row18 (j : Nat) (lower : 18 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[18]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1Row19 (j : Nat) (lower : 19 ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[19]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard1All (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[j]?.getD default).target ≤
    ZP.B candidateStage1 (candidateRecipe1[j]?.getD default).guard
      (candidateRecipe1[i]?.getD default).guard := by
  interval_cases i
  · exact guard1Row0 j firstOrder upper
  · exact guard1Row1 j firstOrder upper
  · exact guard1Row2 j firstOrder upper
  · exact guard1Row3 j firstOrder upper
  · exact guard1Row4 j firstOrder upper
  · exact guard1Row5 j firstOrder upper
  · exact guard1Row6 j firstOrder upper
  · exact guard1Row7 j firstOrder upper
  · exact guard1Row8 j firstOrder upper
  · exact guard1Row9 j firstOrder upper
  · exact guard1Row10 j firstOrder upper
  · exact guard1Row11 j firstOrder upper
  · exact guard1Row12 j firstOrder upper
  · exact guard1Row13 j firstOrder upper
  · exact guard1Row14 j firstOrder upper
  · exact guard1Row15 j firstOrder upper
  · exact guard1Row16 j firstOrder upper
  · exact guard1Row17 j firstOrder upper
  · exact guard1Row18 j firstOrder upper
  · exact guard1Row19 j firstOrder upper

theorem candidateGuardCost1 : ZP.GuardCostOrder candidateStage1 candidateRecipe1 := by
  intro i j order
  exact guard1All i.val j.val i.isLt order j.isLt

theorem guard2Row0 (j : Nat) (lower : 0 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[0]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row1 (j : Nat) (lower : 1 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[1]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row2 (j : Nat) (lower : 2 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[2]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row3 (j : Nat) (lower : 3 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[3]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row4 (j : Nat) (lower : 4 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[4]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row5 (j : Nat) (lower : 5 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[5]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row6 (j : Nat) (lower : 6 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[6]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row7 (j : Nat) (lower : 7 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[7]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row8 (j : Nat) (lower : 8 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[8]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row9 (j : Nat) (lower : 9 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[9]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row10 (j : Nat) (lower : 10 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[10]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row11 (j : Nat) (lower : 11 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[11]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row12 (j : Nat) (lower : 12 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[12]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row13 (j : Nat) (lower : 13 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[13]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row14 (j : Nat) (lower : 14 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[14]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row15 (j : Nat) (lower : 15 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[15]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row16 (j : Nat) (lower : 16 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[16]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row17 (j : Nat) (lower : 17 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[17]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row18 (j : Nat) (lower : 18 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[18]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2Row19 (j : Nat) (lower : 19 ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[19]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard2All (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[j]?.getD default).target ≤
    ZP.B candidateStage2 (candidateRecipe2[j]?.getD default).guard
      (candidateRecipe2[i]?.getD default).guard := by
  interval_cases i
  · exact guard2Row0 j firstOrder upper
  · exact guard2Row1 j firstOrder upper
  · exact guard2Row2 j firstOrder upper
  · exact guard2Row3 j firstOrder upper
  · exact guard2Row4 j firstOrder upper
  · exact guard2Row5 j firstOrder upper
  · exact guard2Row6 j firstOrder upper
  · exact guard2Row7 j firstOrder upper
  · exact guard2Row8 j firstOrder upper
  · exact guard2Row9 j firstOrder upper
  · exact guard2Row10 j firstOrder upper
  · exact guard2Row11 j firstOrder upper
  · exact guard2Row12 j firstOrder upper
  · exact guard2Row13 j firstOrder upper
  · exact guard2Row14 j firstOrder upper
  · exact guard2Row15 j firstOrder upper
  · exact guard2Row16 j firstOrder upper
  · exact guard2Row17 j firstOrder upper
  · exact guard2Row18 j firstOrder upper
  · exact guard2Row19 j firstOrder upper

theorem candidateGuardCost2 : ZP.GuardCostOrder candidateStage2 candidateRecipe2 := by
  intro i j order
  exact guard2All i.val j.val i.isLt order j.isLt

theorem guard3Row0 (j : Nat) (lower : 0 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[0]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row1 (j : Nat) (lower : 1 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[1]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row2 (j : Nat) (lower : 2 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[2]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row3 (j : Nat) (lower : 3 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[3]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row4 (j : Nat) (lower : 4 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[4]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row5 (j : Nat) (lower : 5 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[5]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row6 (j : Nat) (lower : 6 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[6]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row7 (j : Nat) (lower : 7 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[7]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row8 (j : Nat) (lower : 8 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[8]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row9 (j : Nat) (lower : 9 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[9]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row10 (j : Nat) (lower : 10 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[10]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row11 (j : Nat) (lower : 11 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[11]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row12 (j : Nat) (lower : 12 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[12]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row13 (j : Nat) (lower : 13 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[13]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row14 (j : Nat) (lower : 14 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[14]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row15 (j : Nat) (lower : 15 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[15]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row16 (j : Nat) (lower : 16 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[16]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row17 (j : Nat) (lower : 17 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[17]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row18 (j : Nat) (lower : 18 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[18]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3Row19 (j : Nat) (lower : 19 ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[19]?.getD default).guard := by
  interval_cases j <;> decide +kernel

theorem guard3All (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[j]?.getD default).target ≤
    ZP.B candidateStage3 (candidateRecipe3[j]?.getD default).guard
      (candidateRecipe3[i]?.getD default).guard := by
  interval_cases i
  · exact guard3Row0 j firstOrder upper
  · exact guard3Row1 j firstOrder upper
  · exact guard3Row2 j firstOrder upper
  · exact guard3Row3 j firstOrder upper
  · exact guard3Row4 j firstOrder upper
  · exact guard3Row5 j firstOrder upper
  · exact guard3Row6 j firstOrder upper
  · exact guard3Row7 j firstOrder upper
  · exact guard3Row8 j firstOrder upper
  · exact guard3Row9 j firstOrder upper
  · exact guard3Row10 j firstOrder upper
  · exact guard3Row11 j firstOrder upper
  · exact guard3Row12 j firstOrder upper
  · exact guard3Row13 j firstOrder upper
  · exact guard3Row14 j firstOrder upper
  · exact guard3Row15 j firstOrder upper
  · exact guard3Row16 j firstOrder upper
  · exact guard3Row17 j firstOrder upper
  · exact guard3Row18 j firstOrder upper
  · exact guard3Row19 j firstOrder upper

theorem candidateGuardCost3 : ZP.GuardCostOrder candidateStage3 candidateRecipe3 := by
  intro i j order
  exact guard3All i.val j.val i.isLt order j.isLt

theorem candidateStep0 :
    ZP.TransitionCertificate candidateWitness candidateRecipe0 candidateStage1 :=
  _root_.Paley11987Mutation.fastTransition0
theorem candidateStep1 :
    ZP.TransitionCertificate candidateStage1 candidateRecipe1 candidateStage2 :=
  _root_.Paley11987Mutation.fastTransition1
theorem candidateStep2 :
    ZP.TransitionCertificate candidateStage2 candidateRecipe2 candidateStage3 :=
  _root_.Paley11987Mutation.fastTransition2
theorem candidateStep3 :
    ZP.TransitionCertificate candidateStage3 candidateRecipe3 candidateStage4 :=
  _root_.Paley11987Mutation.fastTransition3
theorem candidateClosureChunk0 : ∀ i : Fin 100,
    candidateStage4 (0 + i.val) ≤
      candidateR * candidateWitness (0 + i.val) := by
  decide +kernel

theorem candidateClosureChunk1 : ∀ i : Fin 100,
    candidateStage4 (100 + i.val) ≤
      candidateR * candidateWitness (100 + i.val) := by
  decide +kernel

theorem candidateClosureChunk2 : ∀ i : Fin 100,
    candidateStage4 (200 + i.val) ≤
      candidateR * candidateWitness (200 + i.val) := by
  decide +kernel

theorem candidateClosureChunk3 : ∀ i : Fin 100,
    candidateStage4 (300 + i.val) ≤
      candidateR * candidateWitness (300 + i.val) := by
  decide +kernel

theorem candidateClosureChunk4 : ∀ i : Fin 100,
    candidateStage4 (400 + i.val) ≤
      candidateR * candidateWitness (400 + i.val) := by
  decide +kernel

theorem candidateClosureChunk5 : ∀ i : Fin 100,
    candidateStage4 (500 + i.val) ≤
      candidateR * candidateWitness (500 + i.val) := by
  decide +kernel

theorem candidateClosureChunk6 : ∀ i : Fin 100,
    candidateStage4 (600 + i.val) ≤
      candidateR * candidateWitness (600 + i.val) := by
  decide +kernel

theorem candidateClosureChunk7 : ∀ i : Fin 100,
    candidateStage4 (700 + i.val) ≤
      candidateR * candidateWitness (700 + i.val) := by
  decide +kernel

theorem candidateClosureChunk8 : ∀ i : Fin 100,
    candidateStage4 (800 + i.val) ≤
      candidateR * candidateWitness (800 + i.val) := by
  decide +kernel

theorem candidateClosureChunk9 : ∀ i : Fin 100,
    candidateStage4 (900 + i.val) ≤
      candidateR * candidateWitness (900 + i.val) := by
  decide +kernel

theorem candidateClosureChunk10 : ∀ i : Fin 100,
    candidateStage4 (1000 + i.val) ≤
      candidateR * candidateWitness (1000 + i.val) := by
  decide +kernel

theorem candidateClosureChunk11 : ∀ i : Fin 100,
    candidateStage4 (1100 + i.val) ≤
      candidateR * candidateWitness (1100 + i.val) := by
  decide +kernel

theorem candidateClosureChunk12 : ∀ i : Fin 100,
    candidateStage4 (1200 + i.val) ≤
      candidateR * candidateWitness (1200 + i.val) := by
  decide +kernel

theorem candidateClosureChunk13 : ∀ i : Fin 100,
    candidateStage4 (1300 + i.val) ≤
      candidateR * candidateWitness (1300 + i.val) := by
  decide +kernel

theorem candidateClosureChunk14 : ∀ i : Fin 100,
    candidateStage4 (1400 + i.val) ≤
      candidateR * candidateWitness (1400 + i.val) := by
  decide +kernel

theorem candidateClosureChunk15 : ∀ i : Fin 100,
    candidateStage4 (1500 + i.val) ≤
      candidateR * candidateWitness (1500 + i.val) := by
  decide +kernel

theorem candidateClosureChunk16 : ∀ i : Fin 100,
    candidateStage4 (1600 + i.val) ≤
      candidateR * candidateWitness (1600 + i.val) := by
  decide +kernel

theorem candidateClosureChunk17 : ∀ i : Fin 100,
    candidateStage4 (1700 + i.val) ≤
      candidateR * candidateWitness (1700 + i.val) := by
  decide +kernel

theorem candidateClosureChunk18 : ∀ i : Fin 100,
    candidateStage4 (1800 + i.val) ≤
      candidateR * candidateWitness (1800 + i.val) := by
  decide +kernel

theorem candidateClosureChunk19 : ∀ i : Fin 100,
    candidateStage4 (1900 + i.val) ≤
      candidateR * candidateWitness (1900 + i.val) := by
  decide +kernel

theorem candidateClosureChunk20 : ∀ i : Fin 100,
    candidateStage4 (2000 + i.val) ≤
      candidateR * candidateWitness (2000 + i.val) := by
  decide +kernel

theorem candidateClosureChunk21 : ∀ i : Fin 30,
    candidateStage4 (2100 + i.val) ≤
      candidateR * candidateWitness (2100 + i.val) := by
  decide +kernel

theorem candidateClosure (index : Nat) :
    candidateStage4 index ≤ candidateR * candidateWitness index := by
  by_cases bound : index < 2130
  · have quotientBound : index / 100 < 22 := by omega
    have remainderBound : index % 100 < 100 := Nat.mod_lt index (by decide)
    have decomposition : 100 * (index / 100) + index % 100 = index := by omega
    generalize quotientEquation : index / 100 = quotient at *
    interval_cases quotient
    · have chunkBound := candidateClosureChunk0 ⟨index % 100, by omega⟩
      have indexEquality : 0 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk1 ⟨index % 100, by omega⟩
      have indexEquality : 100 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk2 ⟨index % 100, by omega⟩
      have indexEquality : 200 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk3 ⟨index % 100, by omega⟩
      have indexEquality : 300 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk4 ⟨index % 100, by omega⟩
      have indexEquality : 400 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk5 ⟨index % 100, by omega⟩
      have indexEquality : 500 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk6 ⟨index % 100, by omega⟩
      have indexEquality : 600 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk7 ⟨index % 100, by omega⟩
      have indexEquality : 700 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk8 ⟨index % 100, by omega⟩
      have indexEquality : 800 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk9 ⟨index % 100, by omega⟩
      have indexEquality : 900 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk10 ⟨index % 100, by omega⟩
      have indexEquality : 1000 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk11 ⟨index % 100, by omega⟩
      have indexEquality : 1100 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk12 ⟨index % 100, by omega⟩
      have indexEquality : 1200 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk13 ⟨index % 100, by omega⟩
      have indexEquality : 1300 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk14 ⟨index % 100, by omega⟩
      have indexEquality : 1400 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk15 ⟨index % 100, by omega⟩
      have indexEquality : 1500 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk16 ⟨index % 100, by omega⟩
      have indexEquality : 1600 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk17 ⟨index % 100, by omega⟩
      have indexEquality : 1700 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk18 ⟨index % 100, by omega⟩
      have indexEquality : 1800 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk19 ⟨index % 100, by omega⟩
      have indexEquality : 1900 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk20 ⟨index % 100, by omega⟩
      have indexEquality : 2000 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
    · have chunkBound := candidateClosureChunk21 ⟨index % 100, by omega⟩
      have indexEquality : 2100 + index % 100 = index := by omega
      rw [← indexEquality]
      exact chunkBound
  · change (if index < 2130 then _ else 0) ≤ _
    rw [if_neg bound]
    exact Nat.zero_le _
theorem aPositiveRow0 (j : Nat) (lower : 0 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 0 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow1 (j : Nat) (lower : 1 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 1 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow2 (j : Nat) (lower : 2 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 2 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow3 (j : Nat) (lower : 3 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 3 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow4 (j : Nat) (lower : 4 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 4 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow5 (j : Nat) (lower : 5 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 5 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow6 (j : Nat) (lower : 6 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 6 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow7 (j : Nat) (lower : 7 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 7 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow8 (j : Nat) (lower : 8 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 8 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow9 (j : Nat) (lower : 9 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 9 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow10 (j : Nat) (lower : 10 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 10 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow11 (j : Nat) (lower : 11 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 11 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow12 (j : Nat) (lower : 12 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 12 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow13 (j : Nat) (lower : 13 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 13 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow14 (j : Nat) (lower : 14 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 14 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow15 (j : Nat) (lower : 15 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 15 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow16 (j : Nat) (lower : 16 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 16 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow17 (j : Nat) (lower : 17 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 17 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow18 (j : Nat) (lower : 18 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 18 j := by
  interval_cases j <;> decide +kernel

theorem aPositiveRow19 (j : Nat) (lower : 19 ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness 19 j := by
  interval_cases j <;> decide +kernel

theorem candidateAPositiveAll (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    1 ≤ ZP.A candidateWitness i j := by
  interval_cases i
  · exact aPositiveRow0 j firstOrder upper
  · exact aPositiveRow1 j firstOrder upper
  · exact aPositiveRow2 j firstOrder upper
  · exact aPositiveRow3 j firstOrder upper
  · exact aPositiveRow4 j firstOrder upper
  · exact aPositiveRow5 j firstOrder upper
  · exact aPositiveRow6 j firstOrder upper
  · exact aPositiveRow7 j firstOrder upper
  · exact aPositiveRow8 j firstOrder upper
  · exact aPositiveRow9 j firstOrder upper
  · exact aPositiveRow10 j firstOrder upper
  · exact aPositiveRow11 j firstOrder upper
  · exact aPositiveRow12 j firstOrder upper
  · exact aPositiveRow13 j firstOrder upper
  · exact aPositiveRow14 j firstOrder upper
  · exact aPositiveRow15 j firstOrder upper
  · exact aPositiveRow16 j firstOrder upper
  · exact aPositiveRow17 j firstOrder upper
  · exact aPositiveRow18 j firstOrder upper
  · exact aPositiveRow19 j firstOrder upper

theorem candidateAPositive (i j : Fin 20) (order : i ≤ j) :
    1 ≤ ZP.A candidateWitness i j :=
  candidateAPositiveAll i.val j.val i.isLt order j.isLt

theorem bPositiveRow0 (j : Nat) (lower : 0 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 0 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow1 (j : Nat) (lower : 1 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 1 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow2 (j : Nat) (lower : 2 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 2 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow3 (j : Nat) (lower : 3 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 3 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow4 (j : Nat) (lower : 4 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 4 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow5 (j : Nat) (lower : 5 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 5 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow6 (j : Nat) (lower : 6 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 6 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow7 (j : Nat) (lower : 7 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 7 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow8 (j : Nat) (lower : 8 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 8 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow9 (j : Nat) (lower : 9 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 9 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow10 (j : Nat) (lower : 10 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 10 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow11 (j : Nat) (lower : 11 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 11 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow12 (j : Nat) (lower : 12 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 12 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow13 (j : Nat) (lower : 13 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 13 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow14 (j : Nat) (lower : 14 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 14 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow15 (j : Nat) (lower : 15 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 15 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow16 (j : Nat) (lower : 16 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 16 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow17 (j : Nat) (lower : 17 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 17 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow18 (j : Nat) (lower : 18 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 18 j := by
  interval_cases j <;> decide +kernel

theorem bPositiveRow19 (j : Nat) (lower : 19 ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness 19 j := by
  interval_cases j <;> decide +kernel

theorem candidateBPositiveAll (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    1 ≤ ZP.B candidateWitness i j := by
  interval_cases i
  · exact bPositiveRow0 j firstOrder upper
  · exact bPositiveRow1 j firstOrder upper
  · exact bPositiveRow2 j firstOrder upper
  · exact bPositiveRow3 j firstOrder upper
  · exact bPositiveRow4 j firstOrder upper
  · exact bPositiveRow5 j firstOrder upper
  · exact bPositiveRow6 j firstOrder upper
  · exact bPositiveRow7 j firstOrder upper
  · exact bPositiveRow8 j firstOrder upper
  · exact bPositiveRow9 j firstOrder upper
  · exact bPositiveRow10 j firstOrder upper
  · exact bPositiveRow11 j firstOrder upper
  · exact bPositiveRow12 j firstOrder upper
  · exact bPositiveRow13 j firstOrder upper
  · exact bPositiveRow14 j firstOrder upper
  · exact bPositiveRow15 j firstOrder upper
  · exact bPositiveRow16 j firstOrder upper
  · exact bPositiveRow17 j firstOrder upper
  · exact bPositiveRow18 j firstOrder upper
  · exact bPositiveRow19 j firstOrder upper

theorem candidateBPositive (i j : Fin 20) (order : i ≤ j) :
    1 ≤ ZP.B candidateWitness i j :=
  candidateBPositiveAll i.val j.val i.isLt order j.isLt

theorem candidateOutput :
    max (ZP.A candidateWitness 0 0) (ZP.B candidateWitness 0 0) = candidateC := by
  decide +kernel
/-- Applies the four candidate recipes to one nested Boolean family. -/
def candidateCycleFamily {I : Type} (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2)
    (F : Fin 20 → (I → Bool) → Bool) :
    Fin 20 → (ZP.CycleCoord I → Bool) → Bool :=
  ZP.stageFamily T label
    (ZP.stageFamily T label
      (ZP.stageFamily T label
        (ZP.stageFamily T label F candidateRecipe0 candidateRecipe0Valid)
        candidateRecipe1 candidateRecipe1Valid)
      candidateRecipe2 candidateRecipe2Valid)
    candidateRecipe3 candidateRecipe3Valid

theorem candidateCycleFamilyNested {I : Type} [Fintype I]
    (T : Tournament 11987) (label : Fin 11987 → Fin 11987 → Fin 2)
    (F : Fin 20 → (I → Bool) → Bool) (nested : NestedFamily F) :
    NestedFamily (candidateCycleFamily T label F) := by
  apply ZP.stageFamily_nested
  apply ZP.stageFamily_nested
  apply ZP.stageFamily_nested
  exact ZP.stageFamily_nested T label F nested candidateRecipe0 candidateRecipe0Valid

/-- Transfers the candidate profile through all four recipes and closes the
cycle with the improved radius. -/
theorem candidateCycleBounds {I : Type} [Fintype I]
    (T : Tournament 11987) (label : Fin 11987 → Fin 11987 → Fin 2)
    (caps : ZT.LabelCaps T label)
    (outdegree : ∀ vertex, (Finset.univ.filter (T.Adj vertex)).card = 5993)
    (F : Fin 20 → (I → Bool) → Bool) (nested : NestedFamily F)
    (scale : Nat) (bounds : ZP.ScaledBounds F candidateWitness scale) :
    ZP.ScaledBounds (candidateCycleFamily T label F) candidateWitness
      (scale * candidateR) := by
  obtain ⟨bounds1, nested1⟩ := ZP.actual_profile_transition T label caps outdegree
    F nested candidateWitness candidateStage1 scale bounds
    candidateRecipe0 candidateRecipe0Valid candidateGuardCost0 candidateStep0
  obtain ⟨bounds2, nested2⟩ := ZP.actual_profile_transition T label caps outdegree
    _ nested1 candidateStage1 candidateStage2 scale bounds1
    candidateRecipe1 candidateRecipe1Valid candidateGuardCost1 candidateStep1
  obtain ⟨bounds3, nested3⟩ := ZP.actual_profile_transition T label caps outdegree
    _ nested2 candidateStage2 candidateStage3 scale bounds2
    candidateRecipe2 candidateRecipe2Valid candidateGuardCost2 candidateStep2
  obtain ⟨bounds4, _⟩ := ZP.actual_profile_transition T label caps outdegree
    _ nested3 candidateStage3 candidateStage4 scale bounds3
    candidateRecipe3 candidateRecipe3Valid candidateGuardCost3 candidateStep3
  apply bounds4.mono
  intro index
  simpa only [ZP.entry, Nat.mul_assoc] using
    Nat.mul_le_mul_left scale (candidateClosure index)

/-- Block witnesses multiply by the tournament order at every stage, regardless
of the concrete valid recipe values. -/
def candidateBlocksCycle {I : Type} (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2)
    (F : Fin 20 → (I → Bool) → Bool) {count : Nat}
    (witness : Blocks F count) :
    Blocks (candidateCycleFamily T label F) ((11987 ^ 4) * count) := by
  let witness1 := witness.stage T label (ZP.typedRecipe candidateRecipe0 candidateRecipe0Valid) F
  let witness2 := witness1.stage T label (ZP.typedRecipe candidateRecipe1 candidateRecipe1Valid) _
  let witness3 := witness2.stage T label (ZP.typedRecipe candidateRecipe2 candidateRecipe2Valid) _
  let witness4 := witness3.stage T label (ZP.typedRecipe candidateRecipe3 candidateRecipe3Valid) _
  have countEquality : 11987 * (11987 * (11987 * (11987 * count))) =
      (11987 ^ 4) * count := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.mul_assoc]
  exact countEquality ▸ witness4

/-- A sensitive-coordinate witness doubles at each of the four stages. -/
def candidateSensitiveCycle {I : Type} (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2)
    (F : Fin 20 → (I → Bool) → Bool)
    (zero : ∀ q, F q (fun _ => false) = false) {count : Nat}
    (witness : SensitiveWitness F count) :
    SensitiveWitness (candidateCycleFamily T label F) (16 * count) := by
  let witness1 := witness.stage T label
    (ZP.typedRecipe candidateRecipe0 candidateRecipe0Valid) F zero 0
  have zero1 := step_zero T label
    (ZP.typedRecipe candidateRecipe0 candidateRecipe0Valid) F zero
  let witness2 := witness1.stage T label
    (ZP.typedRecipe candidateRecipe1 candidateRecipe1Valid) _ zero1 0
  have zero2 := step_zero T label
    (ZP.typedRecipe candidateRecipe1 candidateRecipe1Valid) _ zero1
  let witness3 := witness2.stage T label
    (ZP.typedRecipe candidateRecipe2 candidateRecipe2Valid) _ zero2 0
  have zero3 := step_zero T label
    (ZP.typedRecipe candidateRecipe2 candidateRecipe2Valid) _ zero2
  let witness4 := witness3.stage T label
    (ZP.typedRecipe candidateRecipe3 candidateRecipe3Valid) _ zero3 0
  have countEquality : 2 * (2 * (2 * (2 * count))) = 16 * count := by omega
  exact countEquality ▸ witness4

def CandidateActualSeedStatement : Prop :=
  ∀ cycles : Nat, ∃ (n : Nat) (f : (Fin n → Bool) → Bool),
    16 ^ cycles ≤ sensitivity f ∧
    sensitivity f ≤ candidateC * candidateR ^ cycles ∧
    (11987 ^ 4) ^ cycles ≤ blockSensitivity f

theorem candidateFamiliesAtEveryCycle (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2) (caps : ZT.LabelCaps T label)
    (outdegree : ∀ vertex, (Finset.univ.filter (T.Adj vertex)).card = 5993)
    (cycles : Nat) :
    ∃ (I : Type) (instanceFintype : Fintype I)
      (F : Fin 20 → (I → Bool) → Bool),
      NestedFamily F ∧
      @ZP.ScaledBounds I instanceFintype F candidateWitness (candidateR ^ cycles) ∧
      Nonempty (Blocks F ((11987 ^ 4) ^ cycles)) ∧
      Nonempty (SensitiveWitness F (16 ^ cycles)) := by
  induction cycles with
  | zero =>
      refine ⟨Fin 1, inferInstance, leaf, leaf_nested, ?_, ⟨leaf_blocks⟩, ⟨leaf_sensitive⟩⟩
      simpa only [Nat.pow_zero] using
        leaf_bounds candidateWitness candidateAPositive candidateBPositive
  | succ cycles inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨I, instanceFintype, F, nested, bounds, ⟨blocks⟩, ⟨sensitive⟩⟩
      letI := instanceFintype
      refine ⟨ZP.CycleCoord I, inferInstance, candidateCycleFamily T label F,
        candidateCycleFamilyNested T label F nested, ?_, ?_, ?_⟩
      · simpa only [Nat.pow_succ] using
          candidateCycleBounds T label caps outdegree F nested (candidateR ^ cycles) bounds
      · refine ⟨?_⟩
        simpa only [Nat.pow_succ, Nat.mul_comm] using
          candidateBlocksCycle T label F blocks
      · refine ⟨?_⟩
        simpa only [Nat.pow_succ, Nat.mul_comm] using
          candidateSensitiveCycle T label F blocks.zero sensitive

theorem candidateActualSeedsOfLabel (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2) (caps : ZT.LabelCaps T label)
    (outdegree : ∀ vertex, (Finset.univ.filter (T.Adj vertex)).card = 5993) :
    CandidateActualSeedStatement := by
  intro cycles
  rcases candidateFamiliesAtEveryCycle T label caps outdegree cycles with
    ⟨I, instanceFintype, F, nested, bounds, ⟨blocks⟩, ⟨sensitive⟩⟩
  letI := instanceFintype
  let equivalence := Fintype.equivFin I
  refine ⟨Fintype.card I, reindex equivalence (F 0), ?_, ?_, ?_⟩
  · rw [sensitivity_reindex]
    exact sensitive.lower 0
  · rw [sensitivity_reindex]
    have upper := bounds.sensitivity 0
    change sensitivity (F 0) ≤ candidateR ^ cycles *
      max (ZP.A candidateWitness 0 0) (ZP.B candidateWitness 0 0) at upper
    rw [candidateOutput] at upper
    simpa only [Nat.mul_comm] using upper
  · exact (blocks.reindex equivalence).lower 0

theorem candidateActualSeeds : CandidateActualSeedStatement := by
  obtain ⟨label, caps⟩ := _root_.Paley11987Verified.CompactBooleanTransfer.selected_exists_labelCaps
  exact candidateActualSeedsOfLabel ZT.selectedTournament label caps ZT.selected_outdegree


end
end Paley11987Mutation

theorem solution : Paley11987Mutation.ActualSeedStatement := by
  exact Paley11987Mutation.candidateActualSeeds
