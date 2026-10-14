-- Prove2me | solution 1 for WorstCaseEq.Identical.theorem3_price_of_anarchy_two_links
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-13T05:00:59.181066+00:00
-- url     : https://prove2.me/submissions/d6d6b86e-acee-4376-a288-7269108beb0c

-- Complete checked reconstruction of the full native two-link mixed-Nash makespan theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_WorstCaseEq_Identical_Model
import Definitions.Def_agt_games
import Mathlib


-- Begin Canonical
section ModuleScope_Canonical

end ModuleScope_Canonical
-- End Canonical

-- Begin LoadBasic
section ModuleScope_LoadBasic

open scoped BigOperators
namespace WorstCaseEq.Identical.Proof
open Finset

 theorem load_nonneg {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (s : Fin n → Fin 2) (j : Fin 2) : 0 ≤ load w s j := by
  exact sum_nonneg (fun i _ => hw i)

 theorem load_le_makespan {n : ℕ} (w : Fin n → ℝ) (s : Fin n → Fin 2) (j : Fin 2) :
    load w s j ≤ makespan w s :=
  Finset.le_sup' (f := load w s) (Finset.mem_univ j)

 theorem makespan_eq_max {n : ℕ} (w : Fin n → ℝ) (s : Fin n → Fin 2) :
    makespan w s = max (load w s 0) (load w s 1) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (load_le_makespan w s 0) (load_le_makespan w s 1)

 theorem load_total {n : ℕ} (w : Fin n → ℝ) (s : Fin n → Fin 2) :
    load w s 0 + load w s 1 = ∑ i, w i := by
  simp only [load, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize s i = j
  fin_cases j <;> norm_num

 theorem weight_le_load {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (s : Fin n → Fin 2) (i : Fin n) : w i ≤ load w s (s i) := by
  apply Finset.single_le_sum (fun k _ => hw k)
  simp

 theorem opt_weight {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (i : Fin n) :
    w i ≤ opt 2 w := by
  apply Finset.le_inf'
  intro s _
  exact (weight_le_load hw s i).trans (load_le_makespan w s (s i))

 theorem opt_total {n : ℕ} (w : Fin n → ℝ) :
    ∑ i, w i ≤ 2 * opt 2 w := by
  have h : (∑ i, w i) / 2 ≤ opt 2 w := by
    apply Finset.le_inf'
    intro s _
    have h0 := load_le_makespan w s 0
    have h1 := load_le_makespan w s 1
    have hsum := load_total w s
    linarith
  linarith

 theorem opt_nonneg {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) : 0 ≤ opt 2 w := by
  apply Finset.le_inf'
  intro s _
  exact (load_nonneg hw s 0).trans (load_le_makespan w s 0)

end WorstCaseEq.Identical.Proof
end ModuleScope_LoadBasic
-- End LoadBasic

-- Begin FirstMaximum
section ModuleScope_FirstMaximum

open scoped BigOperators
namespace WorstCaseEq.Identical.Proof
open Finset

 theorem first_max_exists {n : ℕ} (w : Fin n → ℝ) (s : Fin n → Fin 2) :
    ∃ j : Fin 2, IsFirstMaxLink w s j := by
  by_cases h : load w s 1 ≤ load w s 0
  · refine ⟨0, ?_, ?_⟩
    · rw [makespan_eq_max, max_eq_left h]
    · intro j hj
      exact (not_lt_of_ge (Fin.zero_le j) hj).elim
  · refine ⟨1, ?_, ?_⟩
    · rw [makespan_eq_max, max_eq_right (le_of_not_ge h)]
    · intro j hj
      have hj0 : j = 0 := by fin_cases j <;> simp_all
      rw [hj0, makespan_eq_max, max_eq_right (le_of_not_ge h)]
      exact lt_of_not_ge h

 theorem first_max_unique {n : ℕ} {w : Fin n → ℝ} {s : Fin n → Fin 2} {j k : Fin 2}
    (hj : IsFirstMaxLink w s j) (hk : IsFirstMaxLink w s k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · have hh := hk.2 j h
    rw [hj.1] at hh
    exact (lt_irrefl _ hh).elim
  · exact h
  · have hh := hj.2 k h
    rw [hk.1] at hh
    exact (lt_irrefl _ hh).elim

 open Classical in
 noncomputable def contributes {n : ℕ} (w : Fin n → ℝ) (s : Fin n → Fin 2) (i : Fin n) : ℝ :=
  if IsFirstMaxLink w s (s i) then 1 else 0

 theorem contributes_bounds {n : ℕ} (w : Fin n → ℝ) (s : Fin n → Fin 2) (i : Fin n) :
    0 ≤ contributes w s i ∧ contributes w s i ≤ 1 := by
  classical
  unfold contributes
  split_ifs <;> norm_num

 theorem makespan_contributions {n : ℕ} (w : Fin n → ℝ) (s : Fin n → Fin 2) :
    makespan w s = ∑ i, contributes w s i * w i := by
  classical
  obtain ⟨j,hj⟩ := first_max_exists w s
  rw [← hj.1]
  simp only [load, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have hiff : IsFirstMaxLink w s (s i) ↔ s i = j :=
    ⟨fun hi => first_max_unique hi hj,fun hi => hi.symm ▸ hj⟩
  simp only [contributes,hiff]
  split_ifs <;> simp

 theorem contributes_pair {n : ℕ} (w : Fin n → ℝ) (s : Fin n → Fin 2) (i k : Fin n) :
    contributes w s i + contributes w s k ≤ 1 + if s i = s k then (1:ℝ) else 0 := by
  classical
  unfold contributes
  split_ifs with hi hk he
  all_goals try norm_num
  exact (he (first_max_unique hi hk)).elim

end WorstCaseEq.Identical.Proof
end ModuleScope_FirstMaximum
-- End FirstMaximum

-- Begin ProfileBasic
section ModuleScope_ProfileBasic

open scoped BigOperators
namespace WorstCaseEq.Identical.Proof

noncomputable def expect {n m : ℕ} (p : Fin n → Fin m → ℝ) (f : (Fin n → Fin m) → ℝ) : ℝ :=
  ∑ s, AGT.profileProb p s*f s

lemma profile_nonneg {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p)
    (s : Fin n → Fin m) : 0 ≤ AGT.profileProb p s :=
  Finset.prod_nonneg (fun i _ => (hp i).1 (s i))

lemma profile_sum_one {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p) :
    (∑ s,AGT.profileProb p s)=1 := by
  simp only [AGT.profileProb]
  rw [← Fintype.prod_sum]
  simp only [(hp _).2,Finset.prod_const_one]

lemma expect_one {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p) :
    expect p (fun _ => 1)=1 := by
  simpa only [expect,mul_one] using profile_sum_one hp

lemma expect_mono {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p)
    {f g : (Fin n → Fin m) → ℝ} (h : ∀ s,f s≤g s) : expect p f≤expect p g :=
  Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s) (profile_nonneg hp s))

lemma expect_add {n m : ℕ} (p : Fin n → Fin m → ℝ) (f g : (Fin n → Fin m) → ℝ) :
    expect p (fun s=>f s+g s)=expect p f+expect p g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

lemma expect_const {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p) (c : ℝ) :
    expect p (fun _ => c)=c := by
  rw [expect,← Finset.sum_mul,profile_sum_one hp,one_mul]

lemma expect_product {n m : ℕ} (p f : Fin n → Fin m → ℝ) :
    expect p (fun s => ∏ i,f i (s i))=∏ i,∑ j,p i j*f i j := by
  simp only [expect,AGT.profileProb,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j=>p i j*f i j)).symm

lemma expect_coordinate {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p)
    (i : Fin n) (g : Fin m → ℝ) : expect p (fun s=>g (s i))=∑ j,p i j*g j := by
  classical
  let f : Fin n → Fin m → ℝ := fun k j=>if k=i then g j else 1
  have hf (s : Fin n → Fin m) : (∏ k,f k (s k))=g (s i) := by simp [f]
  have hs (k : Fin n) : (∑ j,p k j*f k j)=if k=i then ∑ j,p i j*g j else 1 := by
    by_cases hk : k=i
    · subst k; simp [f]
    · simp [f,hk,(hp k).2]
  have hh := expect_product p f
  simpa only [hf,hs,Finset.prod_ite_eq',Finset.mem_univ,if_pos] using hh

lemma prod_two_ite {n : ℕ} (i k : Fin n) (hik : i≠k) (g h : Fin n → ℝ) :
    (∏ a,if a=i then g a else if a=k then h a else 1)=g i*h k := by
  classical
  have he (a : Fin n) : (if a=i then g a else if a=k then h a else 1)=
      (if a=i then g a else 1)*(if a=k then h a else 1) := by
    by_cases hi : a=i
    · subst a; simp [hik]
    · simp [hi]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

lemma expect_two_coordinates {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p)
    (i k : Fin n) (hik : i≠k) (g h : Fin m → ℝ) :
    expect p (fun s=>g (s i)*h (s k))=(∑ j,p i j*g j)*(∑ j,p k j*h j) := by
  classical
  let f : Fin n → Fin m → ℝ := fun a j=>if a=i then g j else if a=k then h j else 1
  have hf (s : Fin n → Fin m) : (∏ a,f a (s a))=g (s i)*h (s k) := by
    exact prod_two_ite i k hik (fun a=>g (s a)) (fun a=>h (s a))
  have hs (a : Fin n) : (∑ j,p a j*f a j)=
      if a=i then ∑ j,p i j*g j else if a=k then ∑ j,p k j*h j else 1 := by
    by_cases hi : a=i
    · subst a; simp [f]
    · by_cases hk : a=k
      · subst a; simp [f,Ne.symm hik]
      · simp [f,hi,hk,(hp a).2]
  have hh := expect_product p f
  simp_rw [hf,hs] at hh
  rw [prod_two_ite i k hik] at hh
  exact hh

end WorstCaseEq.Identical.Proof
end ModuleScope_ProfileBasic
-- End ProfileBasic

-- Begin CollisionLaw
section ModuleScope_CollisionLaw

open scoped BigOperators
namespace WorstCaseEq.Identical.Proof

lemma expect_sum {n m : ℕ} {I : Type*} (J : Finset I) (p : Fin n → Fin m → ℝ)
    (f : I → (Fin n → Fin m) → ℝ) :
    expect p (fun s=>∑ i∈J,f i s)=∑ i∈J,expect p (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

lemma expect_mul_const {n m : ℕ} (p : Fin n → Fin m → ℝ)
    (f : (Fin n → Fin m) → ℝ) (c : ℝ) : expect p (fun s=>f s*c)=expect p f*c := by
  simp only [expect,Finset.sum_mul,mul_assoc]

lemma expect_collision {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p)
    (i k : Fin n) (hik : i≠k) :
    expect p (fun s=>if s i=s k then 1 else 0)=collisionProb p i k := by
  classical
  have he (s : Fin n → Fin m) : (if s i=s k then (1:ℝ) else 0)=
      ∑ j : Fin m,(if s i=j then 1 else 0)*(if s k=j then 1 else 0) := by
    simp [eq_comm]
  have hh := congrArg (expect p) (funext he)
  rw [hh,expect_sum]
  unfold collisionProb
  apply Finset.sum_congr rfl
  intro j _
  simpa using expect_two_coordinates hp i k hik (fun a=>if a=j then 1 else 0) (fun a=>if a=j then 1 else 0)

end WorstCaseEq.Identical.Proof
end ModuleScope_CollisionLaw
-- End CollisionLaw

-- Begin Contributions
section ModuleScope_Contributions

open scoped BigOperators
namespace WorstCaseEq.Identical.Proof
open Finset

 theorem contribProb_expect {n : ℕ} (w : Fin n → ℝ) (p : Fin n → Fin 2 → ℝ) (i : Fin n) :
    contribProb w p i = expect p (fun s => contributes w s i) := rfl

 theorem contribProb_bounds {n : ℕ} (w : Fin n → ℝ) {p : Fin n → Fin 2 → ℝ}
    (hp : AGT.IsMixedProfile p) (i : Fin n) : 0 ≤ contribProb w p i ∧ contribProb w p i ≤ 1 := by
  rw [contribProb_expect]
  constructor
  · calc
      0 = expect p (fun _ => 0) := (expect_const hp 0).symm
      _ ≤ _ := expect_mono hp (fun s => (contributes_bounds w s i).1)
  · calc
      _ ≤ expect p (fun _ => 1) := expect_mono hp (fun s => (contributes_bounds w s i).2)
      _ = 1 := expect_one hp

 theorem socialCost_contrib {n : ℕ} (w : Fin n → ℝ) (p : Fin n → Fin 2 → ℝ) :
    socialCost w p = ∑ i, contribProb w p i * w i := by
  simp only [socialCost, makespan_contributions, Finset.mul_sum, contribProb_expect,
    expect, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro s _
  ring

 theorem contribProb_pair {n : ℕ} (w : Fin n → ℝ) {p : Fin n → Fin 2 → ℝ}
    (hp : AGT.IsMixedProfile p) (i k : Fin n) (hik : i ≠ k) :
    contribProb w p i + contribProb w p k ≤ 1 + collisionProb p i k := by
  have hh := expect_mono hp (fun s => contributes_pair w s i k)
  rw [expect_add, expect_add, expect_one hp, expect_collision hp i k hik] at hh
  exact hh

end WorstCaseEq.Identical.Proof
end ModuleScope_Contributions
-- End Contributions

-- Begin CostLaw
section ModuleScope_CostLaw

open scoped BigOperators
namespace WorstCaseEq.Identical.Proof

lemma expCost_eq_expect {n m : ℕ} (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) :
    expCost w p i=expect p (fun s=>load w s (s i)) := by
  simp [expCost,AGT.expectedPayoff,payoff,expect]

lemma load_eq_self_collisions {n m : ℕ} (w : Fin n → ℝ) (s : Fin n → Fin m) (i : Fin n) :
    load w s (s i)=w i+∑ k∈Finset.univ.erase i,(if s i=s k then 1 else 0)*w k := by
  classical
  have he : load w s (s i)=∑ k : Fin n,(if s i=s k then 1 else 0)*w k := by
    simp [load,Finset.sum_filter,eq_comm]
  rw [he,← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  simp

lemma expCost_eq_collision {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p)
    (w : Fin n → ℝ) (i : Fin n) :
    expCost w p i=w i+∑ k∈Finset.univ.erase i,collisionProb p i k*w k := by
  rw [expCost_eq_expect]
  simp only [load_eq_self_collisions]
  rw [expect_add,expect_const hp,expect_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [expect_mul_const,expect_collision hp i k (Ne.symm (Finset.mem_erase.mp hk).1)]

end WorstCaseEq.Identical.Proof
end ModuleScope_CostLaw
-- End CostLaw

-- Begin UniformDeviation
section ModuleScope_UniformDeviation

open scoped BigOperators
namespace WorstCaseEq.Identical.Proof

lemma uniform_lottery : AGT.IsLottery (fun _ : Fin 2 => (1/2:ℝ)) := by
  constructor
  · intro j; norm_num
  · norm_num [Fin.sum_univ_two]

lemma profile_update {n m : ℕ} {p : Fin n → Fin m → ℝ} (hp : AGT.IsMixedProfile p)
    (i : Fin n) (a : Fin m → ℝ) (ha : AGT.IsLottery a) :
    AGT.IsMixedProfile (Function.update p i a) := by
  intro k
  by_cases hk : k=i
  · subst k; simpa using ha
  · simpa [Function.update_of_ne hk] using hp k

lemma uniform_deviation_cost {n : ℕ} {p : Fin n → Fin 2 → ℝ} (hp : AGT.IsMixedProfile p)
    (w : Fin n → ℝ) (i : Fin n) :
    expCost w (Function.update p i (fun _ => 1/2)) i=((∑ k,w k)+w i)/2 := by
  classical
  rw [expCost_eq_collision (profile_update hp i _ uniform_lottery)]
  have hc (k : Fin n) (hk : k∈Finset.univ.erase i) :
      collisionProb (Function.update p i (fun _=>1/2)) i k=1/2 := by
    have hki := (Finset.mem_erase.mp hk).1
    simp only [collisionProb,Function.update_self,Function.update_of_ne hki,← Finset.mul_sum]
    rw [(hp k).2,mul_one]
  have he : (∑ k ∈ Finset.univ.erase i, collisionProb (Function.update p i (fun _ => 1/2)) i k * w k) = ∑ k ∈ Finset.univ.erase i, (1/2:ℝ) * w k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hc k hk]
  rw [he]
  rw [← Finset.mul_sum]
  have hs := Finset.sum_erase_add Finset.univ (fun k=>w k) (Finset.mem_univ i)
  linarith

lemma expCost_le_half {n : ℕ} (w : Fin n → ℝ) (p : Fin n → Fin 2 → ℝ)
    (hp : IsNash w p) (i : Fin n) : expCost w p i≤((∑ k,w k)+w i)/2 := by
  have h := hp.2 i (fun _=>1/2) uniform_lottery
  have hh : expCost w p i≤expCost w (Function.update p i (fun _=>1/2)) i := neg_le_neg h
  rw [uniform_deviation_cost hp.1] at hh
  exact hh

end WorstCaseEq.Identical.Proof
end ModuleScope_UniformDeviation
-- End UniformDeviation

-- Begin ScalarCombination
section ModuleScope_ScalarCombination

open scoped BigOperators
namespace WorstCaseEq.Identical.Proof
open Finset

 theorem socialCost_fixed_agent {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    {p : Fin n → Fin 2 → ℝ} (hp : IsNash w p) (i : Fin n) :
    socialCost w p ≤ (3/2 - contribProb w p i) * (∑ k, w k) +
      (2 * contribProb w p i - 3/2) * w i := by
  have hpair := Finset.sum_le_sum (s := Finset.univ.erase i)
    (fun k hk => mul_le_mul_of_nonneg_right (contribProb_pair w hp.1 i k (Ne.symm (Finset.mem_erase.mp hk).1)) (hw k))
  have hcost := expCost_eq_collision hp.1 w i
  have hbound := expCost_le_half w p hp i
  have hw_sum : ∑ k ∈ Finset.univ.erase i, w k = (∑ k, w k) - w i := by
    exact (Finset.sum_erase_eq_sub (Finset.mem_univ i))
  have hq_sum : ∑ k ∈ Finset.univ.erase i, contribProb w p k * w k =
      socialCost w p - contribProb w p i * w i := by
    rw [socialCost_contrib]
    exact Finset.sum_erase_eq_sub (Finset.mem_univ i)
  simp only [add_mul, one_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hpair
  rw [hw_sum, hq_sum] at hpair
  nlinarith

 theorem two_link_bound {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (p : Fin n → Fin 2 → ℝ) (hp : IsNash w p) : socialCost w p ≤ (3/2:ℝ) * opt 2 w := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  by_cases h : ∃ i, 3/4 ≤ contribProb w p i
  · obtain ⟨i, hi⟩ := h
    have hq := contribProb_bounds w hp.1 i
    have hb := socialCost_fixed_agent hw0 hp i
    have h1 := mul_le_mul_of_nonneg_left (opt_total w) (show 0 ≤ 3/2 - contribProb w p i by linarith)
    have h2 := mul_le_mul_of_nonneg_left (opt_weight hw0 i) (show 0 ≤ 2 * contribProb w p i - 3/2 by linarith)
    nlinarith
  · have hq : ∀ i, contribProb w p i ≤ 3/4 := by
      intro i
      exact (lt_of_not_ge (fun hi => h ⟨i, hi⟩)).le
    rw [socialCost_contrib]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => mul_le_mul_of_nonneg_right (hq i) (hw0 i))
    rw [← Finset.mul_sum] at hh
    have ht := opt_total w
    linarith

end WorstCaseEq.Identical.Proof
end ModuleScope_ScalarCombination
-- End ScalarCombination

-- Begin RootAssembly
section ModuleScope_RootAssembly

namespace WorstCaseEq.Identical

/-- Theorem 3, PDF p. 5: for any number of agents and `m = 2` identical links, every Nash equilibrium has
social cost (expected maximum link traffic) at most `3/2` times the optimum. -/
theorem theorem3_price_of_anarchy_two_links {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (p : Fin n → Fin 2 → ℝ) (hp : IsNash w p) :
    socialCost w p ≤ (3 / 2 : ℝ) * opt 2 w := by
  exact Proof.two_link_bound w hw p hp

end WorstCaseEq.Identical
end ModuleScope_RootAssembly
-- End RootAssembly

-- Begin Solution
section ModuleScope_Solution

open WorstCaseEq.Identical

theorem solution {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (p : Fin n → Fin 2 → ℝ) (hp : IsNash w p) :
    socialCost w p ≤ (3 / 2 : ℝ) * opt 2 w := by
  exact WorstCaseEq.Identical.theorem3_price_of_anarchy_two_links w hw p hp

end ModuleScope_Solution
-- End Solution
