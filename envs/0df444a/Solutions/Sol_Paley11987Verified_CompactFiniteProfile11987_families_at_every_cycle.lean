-- Prove2me | solution 1 for Paley11987Verified.CompactFiniteProfile11987.families_at_every_cycle
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:18:08.808726+00:00
-- url     : https://prove2.me/submissions/c791a848-6430-4977-9848-ebbd5b35acf4

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
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_cycle_bounds

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

section z78
namespace ZP
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000








theorem witness_A_positive : ∀ i j : Fin 20, i ≤ j → 1 ≤ A witness i j := by decide +kernel
theorem witness_B_positive : ∀ i j : Fin 20, i ≤ j → 1 ≤ B witness i j := by decide +kernel
























end ZP
end z78

section z79

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileSeeds
namespace ZP










 theorem cycleFamily_nested {I : Type} [Fintype I] (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2) (F : Fin 20 → (I → Bool) → Bool)
    (hF : NestedFamily F) : NestedFamily (cycleFamily T label F) := by
  apply stageFamily_nested
  apply stageFamily_nested
  apply stageFamily_nested
  exact stageFamily_nested T label F hF recipe0 recipe0_valid

 

 

 

end ZP
end
end z79

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
    (hc : PeriodCertificate) (m : Nat) :
    ∃ (I : Type) (inst : Fintype I) (F : Fin 20 → (I → Bool) → Bool),
      NestedFamily F ∧ @ScaledBounds I inst F witness (R^m) ∧
      Nonempty (Blocks F ((11987^4)^m)) ∧ Nonempty (SensitiveWitness F (16^m)) := by
  induction m with
  | zero =>
      refine ⟨Fin 1,inferInstance,leaf,leaf_nested,?_,⟨leaf_blocks⟩,⟨leaf_sensitive⟩⟩
      simpa only [Nat.pow_zero] using leaf_bounds witness witness_A_positive witness_B_positive
  | succ m ih =>
      rcases ih with ⟨I,inst,F,hF,hv,⟨wb⟩,⟨ws⟩⟩
      letI := inst
      refine ⟨CycleCoord I,inferInstance,cycleFamily T label F,
        cycleFamily_nested T label F hF,?_,?_,?_⟩
      · simpa only [Nat.pow_succ] using _root_.Paley11987Verified.CompactFiniteProfile11987.cycle_bounds T label hCaps hd hc F hF (R^m) hv
      · refine ⟨?_⟩
        simpa only [Nat.pow_succ,Nat.mul_comm] using blocks_cycle T label F wb
      · refine ⟨?_⟩
        simpa only [Nat.pow_succ,Nat.mul_comm] using sensitive_cycle T label F wb.zero ws



end ZP
end
end z86
