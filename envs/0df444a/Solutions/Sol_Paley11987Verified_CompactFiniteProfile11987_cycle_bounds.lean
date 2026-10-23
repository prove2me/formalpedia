-- Prove2me | solution 1 for Paley11987Verified.CompactFiniteProfile11987.cycle_bounds
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:13:36.909025+00:00
-- url     : https://prove2.me/submissions/87aac2dc-e06f-4bf2-9e4e-9d23943625f8

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
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile11987_actual_rawStep

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

section z78
namespace ZP
set_option maxHeartbeats 20000000
set_option maxRecDepth 200000

theorem guardCost0 (i j : Fin 20) (hij : i ≤ j) :
    B witness (recipe0[j.val]?.getD default).guard (recipe0[j.val]?.getD default).target ≤
      B witness (recipe0[j.val]?.getD default).guard (recipe0[i.val]?.getD default).guard := by
  have h : ∀ i j : Fin 20, i ≤ j →
      B witness (recipe0[j.val]?.getD default).guard (recipe0[j.val]?.getD default).target ≤
        B witness (recipe0[j.val]?.getD default).guard (recipe0[i.val]?.getD default).guard := by decide +kernel
  exact h i j hij

theorem guardCost1 (i j : Fin 20) (hij : i ≤ j) :
    B stage1 (recipe1[j.val]?.getD default).guard (recipe1[j.val]?.getD default).target ≤
      B stage1 (recipe1[j.val]?.getD default).guard (recipe1[i.val]?.getD default).guard := by
  have h : ∀ i j : Fin 20, i ≤ j →
      B stage1 (recipe1[j.val]?.getD default).guard (recipe1[j.val]?.getD default).target ≤
        B stage1 (recipe1[j.val]?.getD default).guard (recipe1[i.val]?.getD default).guard := by decide +kernel
  exact h i j hij

theorem guardCost2 (i j : Fin 20) (hij : i ≤ j) :
    B stage2 (recipe2[j.val]?.getD default).guard (recipe2[j.val]?.getD default).target ≤
      B stage2 (recipe2[j.val]?.getD default).guard (recipe2[i.val]?.getD default).guard := by
  have h : ∀ i j : Fin 20, i ≤ j →
      B stage2 (recipe2[j.val]?.getD default).guard (recipe2[j.val]?.getD default).target ≤
        B stage2 (recipe2[j.val]?.getD default).guard (recipe2[i.val]?.getD default).guard := by decide +kernel
  exact h i j hij

theorem guardCost3 (i j : Fin 20) (hij : i ≤ j) :
    B stage3 (recipe3[j.val]?.getD default).guard (recipe3[j.val]?.getD default).target ≤
      B stage3 (recipe3[j.val]?.getD default).guard (recipe3[i.val]?.getD default).guard := by
  have h : ∀ i j : Fin 20, i ≤ j →
      B stage3 (recipe3[j.val]?.getD default).guard (recipe3[j.val]?.getD default).target ≤
        B stage3 (recipe3[j.val]?.getD default).guard (recipe3[i.val]?.getD default).guard := by decide +kernel
  exact h i j hij



theorem invariant_chunk0 : ∀ i : Fin 100,
    entry stage4 (0+i.val) ≤ R*entry witness (0+i.val) := by decide +kernel
theorem invariant_chunk1 : ∀ i : Fin 100,
    entry stage4 (100+i.val) ≤ R*entry witness (100+i.val) := by decide +kernel
theorem invariant_chunk2 : ∀ i : Fin 100,
    entry stage4 (200+i.val) ≤ R*entry witness (200+i.val) := by decide +kernel
theorem invariant_chunk3 : ∀ i : Fin 100,
    entry stage4 (300+i.val) ≤ R*entry witness (300+i.val) := by decide +kernel
theorem invariant_chunk4 : ∀ i : Fin 100,
    entry stage4 (400+i.val) ≤ R*entry witness (400+i.val) := by decide +kernel
theorem invariant_chunk5 : ∀ i : Fin 100,
    entry stage4 (500+i.val) ≤ R*entry witness (500+i.val) := by decide +kernel
theorem invariant_chunk6 : ∀ i : Fin 100,
    entry stage4 (600+i.val) ≤ R*entry witness (600+i.val) := by decide +kernel
theorem invariant_chunk7 : ∀ i : Fin 100,
    entry stage4 (700+i.val) ≤ R*entry witness (700+i.val) := by decide +kernel
theorem invariant_chunk8 : ∀ i : Fin 100,
    entry stage4 (800+i.val) ≤ R*entry witness (800+i.val) := by decide +kernel
theorem invariant_chunk9 : ∀ i : Fin 100,
    entry stage4 (900+i.val) ≤ R*entry witness (900+i.val) := by decide +kernel
theorem invariant_chunk10 : ∀ i : Fin 100,
    entry stage4 (1000+i.val) ≤ R*entry witness (1000+i.val) := by decide +kernel
theorem invariant_chunk11 : ∀ i : Fin 100,
    entry stage4 (1100+i.val) ≤ R*entry witness (1100+i.val) := by decide +kernel
theorem invariant_chunk12 : ∀ i : Fin 100,
    entry stage4 (1200+i.val) ≤ R*entry witness (1200+i.val) := by decide +kernel
theorem invariant_chunk13 : ∀ i : Fin 100,
    entry stage4 (1300+i.val) ≤ R*entry witness (1300+i.val) := by decide +kernel
theorem invariant_chunk14 : ∀ i : Fin 100,
    entry stage4 (1400+i.val) ≤ R*entry witness (1400+i.val) := by decide +kernel
theorem invariant_chunk15 : ∀ i : Fin 100,
    entry stage4 (1500+i.val) ≤ R*entry witness (1500+i.val) := by decide +kernel
theorem invariant_chunk16 : ∀ i : Fin 100,
    entry stage4 (1600+i.val) ≤ R*entry witness (1600+i.val) := by decide +kernel
theorem invariant_chunk17 : ∀ i : Fin 100,
    entry stage4 (1700+i.val) ≤ R*entry witness (1700+i.val) := by decide +kernel
theorem invariant_chunk18 : ∀ i : Fin 100,
    entry stage4 (1800+i.val) ≤ R*entry witness (1800+i.val) := by decide +kernel
theorem invariant_chunk19 : ∀ i : Fin 100,
    entry stage4 (1900+i.val) ≤ R*entry witness (1900+i.val) := by decide +kernel
theorem invariant_chunk20 : ∀ i : Fin 100,
    entry stage4 (2000+i.val) ≤ R*entry witness (2000+i.val) := by decide +kernel
theorem invariant_chunk21 : ∀ i : Fin 30,
    entry stage4 (2100+i.val) ≤ R*entry witness (2100+i.val) := by decide +kernel
theorem final_invariant (n : Nat) : entry stage4 n ≤ R*entry witness n := by
  by_cases hn : n < 2130
  · have hq : n / 100 < 22 := by omega
    have hr : n % 100 < 100 := Nat.mod_lt n (by decide)
    have he : 100*(n/100)+n%100=n := by omega
    generalize hdiv : n/100=q at *
    interval_cases q
    · have h := invariant_chunk0 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 0+n%100=n by omega] using h
    · have h := invariant_chunk1 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 100+n%100=n by omega] using h
    · have h := invariant_chunk2 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 200+n%100=n by omega] using h
    · have h := invariant_chunk3 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 300+n%100=n by omega] using h
    · have h := invariant_chunk4 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 400+n%100=n by omega] using h
    · have h := invariant_chunk5 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 500+n%100=n by omega] using h
    · have h := invariant_chunk6 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 600+n%100=n by omega] using h
    · have h := invariant_chunk7 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 700+n%100=n by omega] using h
    · have h := invariant_chunk8 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 800+n%100=n by omega] using h
    · have h := invariant_chunk9 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 900+n%100=n by omega] using h
    · have h := invariant_chunk10 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1000+n%100=n by omega] using h
    · have h := invariant_chunk11 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1100+n%100=n by omega] using h
    · have h := invariant_chunk12 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1200+n%100=n by omega] using h
    · have h := invariant_chunk13 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1300+n%100=n by omega] using h
    · have h := invariant_chunk14 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1400+n%100=n by omega] using h
    · have h := invariant_chunk15 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1500+n%100=n by omega] using h
    · have h := invariant_chunk16 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1600+n%100=n by omega] using h
    · have h := invariant_chunk17 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1700+n%100=n by omega] using h
    · have h := invariant_chunk18 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1800+n%100=n by omega] using h
    · have h := invariant_chunk19 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 1900+n%100=n by omega] using h
    · have h := invariant_chunk20 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 2000+n%100=n by omega] using h
    · have h := invariant_chunk21 ⟨n%100,by omega⟩
      simpa only [Fin.val_mk,show 2100+n%100=n by omega] using h
  · change (if n < 2130 then _ else 0) ≤ _
    rw [if_neg hn]
    exact Nat.zero_le _
end ZP
end z78

section z79

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical
open OAI.Paper320 Sensitivity2075 ZT
open CompactFiniteProfileSeeds
namespace ZP










 

 theorem _root_.solution {I : Type} [Fintype I] (T : Tournament 11987)
    (label : Fin 11987 → Fin 11987 → Fin 2) (hCaps : LabelCaps T label)
    (hd : ∀ v, (Finset.univ.filter (T.Adj v)).card = 5993)
    (hc : PeriodCertificate)
    (F : Fin 20 → (I → Bool) → Bool) (hF : NestedFamily F)
    (c : Nat) (h : ScaledBounds F witness c) :
    ScaledBounds (cycleFamily T label F) witness (c*R) := by
  obtain ⟨h1,n1⟩ := actual_profile_transition T label hCaps hd F hF
    witness stage1 c h recipe0 recipe0_valid guardCost0 hc.step0
  obtain ⟨h2,n2⟩ := actual_profile_transition T label hCaps hd _ n1
    stage1 stage2 c h1 recipe1 recipe1_valid guardCost1 hc.step1
  obtain ⟨h3,n3⟩ := actual_profile_transition T label hCaps hd _ n2
    stage2 stage3 c h2 recipe2 recipe2_valid guardCost2 hc.step2
  obtain ⟨h4,_⟩ := actual_profile_transition T label hCaps hd _ n3
    stage3 stage4 c h3 recipe3 recipe3_valid guardCost3 hc.step3
  apply h4.mono
  intro n
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c (final_invariant n)

 

 

end ZP
end
end z79
