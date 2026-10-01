-- Prove2me | solution 1 for SingleMachineSched.AlphaJSched.eq_3_10
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:20:59.534952+00:00
-- url     : https://prove2.me/submissions/bcd79557-8aba-4422-bc71-1afe3a67e19f

import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_LPStructure
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaPoints
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Definitions.Def_SingleMachineSched_LPRelax_LPSchedule
import Definitions.Def_SingleMachineSched_LPRelax_RelaxationD
import Mathlib.Tactic
open Set Finset
open SingleMachineSched.LPRelax

private theorem run_spec {n : ℕ} (p r : Fin n → ℕ) (t : ℕ) (j : Fin n)
    (h : lpRun p r t=some j) : r j ≤ t ∧ 0 < lpRemaining p r t j ∧
      ∀ k,r k ≤ t → 0 < lpRemaining p r t k → j ≤ k := by
  unfold lpRun lpPick at h
  split_ifs at h with he
  · have hj := Option.some.inj h
    have hm := Finset.min'_mem _ he
    have hm : r j ≤ t ∧ 0 < lpRemaining p r t j := by simpa only [hj,Finset.mem_filter,Finset.mem_univ,true_and] using hm
    refine ⟨hm.1,hm.2,?_⟩
    intro k hk hr
    rw [← hj]
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk,hr⟩)

private theorem run_exists {n : ℕ} (p r : Fin n → ℕ) (t : ℕ) (k : Fin n)
    (hk : r k ≤ t) (hr : 0 < lpRemaining p r t k) : ∃ j,lpRun p r t=some j ∧ j ≤ k := by
  have he : (Finset.univ.filter (fun j => r j ≤ t ∧ 0 < lpRemaining p r t j)).Nonempty :=
    ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk,hr⟩⟩
  refine ⟨(Finset.univ.filter (fun j => r j ≤ t ∧ 0 < lpRemaining p r t j)).min' he,?_,?_⟩
  · simp only [lpRun,lpPick,dif_pos he]
  · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk,hr⟩)

private theorem remaining_le {n : ℕ} (p r : Fin n → ℕ) (t : ℕ) (j : Fin n) : lpRemaining p r t j ≤ p j := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [lpRemaining]
    split_ifs <;> omega

private def served {n : ℕ} (p r : Fin n → ℕ) (t : ℕ) (j : Fin n) := p j-lpRemaining p r t j

private theorem served_step {n : ℕ} (p r : Fin n → ℕ) (t : ℕ) (j : Fin n) :
    served p r (t+1) j=served p r t j+(if lpRun p r t=some j then 1 else 0) := by
  have hrem := remaining_le p r t j
  change p j-(if lpRun p r t=some j then lpRemaining p r t j-1 else lpRemaining p r t j)=
    p j-lpRemaining p r t j+(if lpRun p r t=some j then 1 else 0)
  by_cases hh : lpRun p r t=some j
  · have hpos := (run_spec p r t j hh).2.1
    rw [if_pos hh,if_pos hh]
    omega
  · rw [if_neg hh,if_neg hh,Nat.add_zero]

private theorem served_le {n : ℕ} (p r : Fin n → ℕ) (t : ℕ) (j : Fin n) : served p r t j ≤ p j := Nat.sub_le _ _

private theorem served_before {n : ℕ} (p r : Fin n → ℕ) (t : ℕ) (j : Fin n) (ht : t ≤ r j) : served p r t j=0 := by
  induction t with
  | zero => simp [served,lpRemaining]
  | succ t ih =>
    have hn : lpRun p r t ≠ some j := fun hh => by have hr := (run_spec p r t j hh).1;omega
    rw [served_step,if_neg hn,ih (by omega)]

private def processed {n : ℕ} (p r : Fin n → ℕ) (S : Finset (Fin n)) (t : ℕ) : ℝ := ∑ j ∈ S,(served p r t j : ℝ)

private theorem processed_mono {n : ℕ} (p r : Fin n → ℕ) (S : Finset (Fin n)) (t : ℕ) : processed p r S t ≤ processed p r S (t+1) := by
  apply Finset.sum_le_sum
  intro j hj
  exact_mod_cast (show served p r t j ≤ served p r (t+1) j by rw [served_step];omega)

private theorem processed_run {n : ℕ} (p r : Fin n → ℕ) (S : Finset (Fin n)) (t : ℕ)
    (j : Fin n) (hj : j∈S) (hrun : lpRun p r t=some j) : processed p r S (t+1)=processed p r S t+1 := by
  simp only [processed,served_step,hrun,Nat.cast_add,Finset.sum_add_distrib]
  congr 1
  simp [eq_comm,hj]

private theorem processed_idle {n : ℕ} (p r : Fin n → ℕ) (S : Finset (Fin n)) (t : ℕ)
    (h : ¬∃ j∈S,r j ≤ t ∧ 0 < lpRemaining p r t j) :
    processed p r S t=∑ j ∈ S,if r j ≤ t then (p j : ℝ) else 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hr : r j ≤ t
  · have hz : lpRemaining p r t j=0 := by
      by_contra hn
      exact h ⟨j,hj,hr,Nat.pos_of_ne_zero hn⟩
    simp [served,hz,hr]
  · rw [served_before p r t j (by omega)]
    simp [hr]

private theorem feasible_row_total {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (y : Fin n → ℕ → ℝ)
    (hy : FeasibleD p r T y) (j : Fin n) : ∑ t ∈ Finset.range T,y j t=(p j : ℝ) := by
  rw [← hy.2.2.2 j]
  symm
  apply Finset.sum_subset
  · intro t ht
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
  · intro t ht hnot
    have hlt : t<r j := by
      have hh := Finset.mem_range.mp ht
      have hh' : ¬(r j ≤ t ∧ t<T) := by simpa only [Finset.mem_Ico] using hnot
      omega
    exact hy.2.1 j t (Or.inl hlt)

private def fractional_processed {n : ℕ} (y : Fin n → ℕ → ℝ) (S : Finset (Fin n)) (t : ℕ) : ℝ :=
  ∑ j ∈ S,∑ τ ∈ Finset.range t,y j τ

private theorem fractional_step {n : ℕ} (y : Fin n → ℕ → ℝ) (S : Finset (Fin n)) (t : ℕ) :
    fractional_processed y S (t+1)=fractional_processed y S t+∑ j∈S,y j t := by
  simp only [fractional_processed,Finset.sum_range_succ,Finset.sum_add_distrib]

private theorem fractional_demand {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (y : Fin n → ℕ → ℝ)
    (hy : FeasibleD p r T y) (S : Finset (Fin n)) (t : ℕ) (ht : t<T) :
    fractional_processed y S (t+1) ≤ ∑ j∈S,if r j ≤ t then (p j : ℝ) else 0 := by
  apply Finset.sum_le_sum
  intro j hj
  by_cases hr : r j ≤ t
  · rw [if_pos hr,← feasible_row_total p r T y hy j]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun τ _ _ => hy.1 j τ)
  · rw [if_neg hr]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro τ hτ
    have hτ := Finset.mem_range.mp hτ
    exact hy.2.1 j τ (Or.inl (by omega))

private theorem greedy_prefix {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (y : Fin n → ℕ → ℝ)
    (hy : FeasibleD p r T y) (S : Finset (Fin n))
    (hS : ∀ i∈S,∀ j : Fin n,j ≤ i → j∈S) (t : ℕ) (ht : t ≤ T) :
    fractional_processed y S t ≤ processed p r S t := by
  induction t with
  | zero => simp [fractional_processed,processed,served,lpRemaining]
  | succ t ih =>
    have ih := ih (by omega)
    by_cases hel : ∃ j∈S,r j ≤ t ∧ 0 < lpRemaining p r t j
    · obtain ⟨k,hk,hr,hem⟩ := hel
      obtain ⟨j,hrun,hjk⟩ := run_exists p r t k hr hem
      rw [processed_run p r S t j (hS k hk j hjk) hrun,fractional_step]
      have hcol : (∑ j∈S,y j t) ≤ 1 := by
        apply le_trans _ (hy.2.2.1 t (by omega))
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun j _ _ => hy.1 j t)
      linarith only [ih,hcol]
    · calc
        fractional_processed y S (t+1) ≤ ∑ j∈S,if r j ≤ t then (p j : ℝ) else 0 := fractional_demand p r T y hy S t (by omega)
        _ = processed p r S t := (processed_idle p r S t hel).symm
        _ ≤ processed p r S (t+1) := processed_mono p r S t

private theorem feasible_exists {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hT : IsMakespanBound p r T) : ∃ y,FeasibleD p r T y := by
  classical
  obtain ⟨s,hs,hd,hT⟩ := hT
  have hs0 (j : Fin n) : 0 ≤ s j := (Nat.cast_nonneg _).trans (hs j)
  let a : Fin n → ℕ := fun j => ⌊s j⌋₊
  have har (j : Fin n) : r j ≤ a j := Nat.le_floor (hs j)
  have haT (j : Fin n) : a j+p j ≤ T := by
    simpa only [Nat.floor_add_natCast (hs0 j),a] using Nat.floor_le_of_le (hT j)
  have had (j k : Fin n) (hne : j ≠ k) : a j+p j ≤ a k ∨ a k+p k ≤ a j := by
    rcases hd j k hne with h|h
    · left;simpa only [Nat.floor_add_natCast (hs0 j),a] using Nat.floor_mono h
    · right;simpa only [Nat.floor_add_natCast (hs0 k),a] using Nat.floor_mono h
  let y : Fin n → ℕ → ℝ := fun j τ => if a j ≤ τ ∧ τ<a j+p j then 1 else 0
  refine ⟨y,?_,?_,?_,?_⟩
  · intro j τ;dsimp [y];split_ifs <;> norm_num
  · intro j τ hbad
    have hn : ¬(a j ≤ τ ∧ τ<a j+p j) := by have hr := har j;have ht := haT j;omega
    simp only [y,if_neg hn]
  · intro τ hτ
    by_cases hex : ∃ j,a j ≤ τ ∧ τ<a j+p j
    · obtain ⟨j,hj⟩ := hex
      have ho (k : Fin n) (hne : k ≠ j) : ¬(a k ≤ τ ∧ τ<a k+p k) := by
        have hh := had k j hne
        omega
      rw [Finset.sum_eq_single j]
      · simp [y,hj]
      · intro k hk hkj;exact if_neg (ho k hkj)
      · simp
    · have hz (j : Fin n) : y j τ=0 := if_neg (fun hj => hex ⟨j,hj⟩)
      simp only [hz,Finset.sum_const_zero,zero_le_one]
  · intro j
    have he : (Finset.Ico (r j) T).filter (fun τ => a j ≤ τ ∧ τ<a j+p j)=Finset.Ico (a j) (a j+p j) := by
      ext τ
      have hr := har j
      have ht := haT j
      simp only [Finset.mem_filter,Finset.mem_Ico]
      omega
    change (∑ τ∈Finset.Ico (r j) T,if a j ≤ τ ∧ τ<a j+p j then (1:ℝ) else 0)=(p j : ℝ)
    rw [← Finset.sum_filter,he]
    simp

private theorem remaining_zero_at {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hT : IsMakespanBound p r T) (j : Fin n) : lpRemaining p r T j=0 := by
  obtain ⟨y,hy⟩ := feasible_exists p r T hT
  have hh := greedy_prefix p r T y hy Finset.univ (by simp) T le_rfl
  have heq : (∑ j : Fin n,(served p r T j : ℝ))=∑ j : Fin n,(p j : ℝ) := by
    apply le_antisymm (Finset.sum_le_sum (fun j _ => Nat.cast_le.mpr (served_le p r T j)))
    simpa only [fractional_processed,processed,feasible_row_total p r T y hy] using hh
  have hj : (served p r T j : ℝ)=(p j : ℝ) := (Finset.sum_eq_sum_iff_of_le (fun j _ => Nat.cast_le.mpr (served_le p r T j))).mp heq j (Finset.mem_univ _)
  have hj : served p r T j=p j := by exact_mod_cast hj
  have hr := remaining_le p r T j
  dsimp [served] at hj
  omega

open MeasureTheory

private theorem remaining_antitone {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : Antitone (fun t => lpRemaining p r t j) := by
  apply antitone_nat_of_succ_le
  intro t
  simp only [lpRemaining]
  split_ifs <;> omega

private theorem run_lt {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hT : IsMakespanBound p r T)
    (t : ℕ) (j : Fin n) (h : lpRun p r t=some j) : t<T := by
  by_contra hn
  have hh := remaining_antitone p r j (show T ≤ t by omega)
  dsimp only at hh
  rw [remaining_zero_at p r T hT j] at hh
  have hp := (run_spec p r t j h).2.1
  omega

private theorem yLP_sum {n : ℕ} (p r : Fin n → ℕ) (t : ℕ) (j : Fin n) :
    (∑ τ ∈ Finset.range t,yLP p r j τ)=(served p r t j : ℝ) := by
  induction t with
  | zero => simp [served,lpRemaining]
  | succ t ih =>
    rw [Finset.sum_range_succ,ih,served_step,Nat.cast_add]
    congr 1
    unfold yLP
    split_ifs <;> norm_num

private theorem yLP_feasible {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hT : IsMakespanBound p r T) :
    FeasibleD p r T (yLP p r) := by
  have hzero (j : Fin n) (τ : ℕ) (hh : τ<r j ∨ T ≤ τ) : yLP p r j τ=0 := by
    apply if_neg
    intro hr
    have hrel := (run_spec p r τ j hr).1
    have hend := run_lt p r T hT τ j hr
    omega
  refine ⟨?_,hzero,?_,?_⟩
  · intro j τ;unfold yLP;split_ifs <;> norm_num
  · intro τ hτ
    cases he : lpRun p r τ with
    | none => simp [yLP,he]
    | some j => simp [yLP,he,eq_comm]
  · intro j
    have he : (∑ τ ∈ Finset.Ico (r j) T,yLP p r j τ)=∑ τ ∈ Finset.range T,yLP p r j τ := by
      apply Finset.sum_subset
      · intro τ hτ;exact Finset.mem_range.mpr (Finset.mem_Ico.mp hτ).2
      · intro τ hτ hnot
        have hτ := Finset.mem_range.mp hτ
        have hn : ¬(r j ≤ τ ∧ τ<T) := by simpa only [Finset.mem_Ico] using hnot
        exact hzero j τ (Or.inl (by omega))
    rw [he,yLP_sum]
    simp [served,remaining_zero_at p r T hT j]

private theorem lpSet_finite {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hT : IsMakespanBound p r T) (j : Fin n) :
    lpSet p r j=⋃ τ∈(Finset.Ico (r j) T).filter (fun τ => lpRun p r τ=some j),Ico (τ : ℝ) (τ+1) := by
  ext t
  constructor
  · intro ht
    change t∈⋃ (τ : ℕ) (_ : lpRun p r τ=some j),Ico (τ : ℝ) (τ+1) at ht
    obtain ⟨τ,hτ,ht⟩ := mem_iUnion₂.mp ht
    exact mem_iUnion₂.mpr ⟨τ,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨(run_spec p r τ j hτ).1,run_lt p r T hT τ j hτ⟩,hτ⟩,ht⟩
  · intro ht
    obtain ⟨τ,hτ,ht⟩ := mem_iUnion₂.mp ht
    exact mem_iUnion₂.mpr ⟨τ,(Finset.mem_filter.mp hτ).2,ht⟩

private theorem nat_intervals_disjoint : Pairwise (fun τ σ : ℕ => Disjoint (Ico (τ : ℝ) (τ+1)) (Ico (σ : ℝ) (σ+1))) := by
  intro τ σ hne
  apply Set.disjoint_left.mpr
  intro t hτ hσ
  rcases lt_or_gt_of_ne hne with h|h
  · have hh : (τ : ℝ)+1 ≤ σ := by exact_mod_cast h
    linarith [hτ.2,hσ.1]
  · have hh : (σ : ℝ)+1 ≤ τ := by exact_mod_cast h
    linarith [hσ.2,hτ.1]

private theorem lp_integral {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hT : IsMakespanBound p r T) (j : Fin n) :
    (∫ t in lpSet p r j,t)=∑ τ∈Finset.Ico (r j) T,yLP p r j τ*((τ : ℝ)+1/2) := by
  rw [lpSet_finite p r T hT j]
  rw [MeasureTheory.integral_biUnion_finset (f := fun t : ℝ => t) (μ := volume) _ (fun _ _ => measurableSet_Ico)
    (fun τ _ σ _ hn => nat_intervals_disjoint hn)
    (fun τ _ => continuous_id.integrableOn_Icc.mono_set Ico_subset_Icc_self)]
  have hi (τ : ℕ) : (∫ t in Ico (τ : ℝ) (τ+1),t)=(τ : ℝ)+1/2 := by
    rw [MeasureTheory.integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith),integral_id]
    ring
  simp only [hi,Finset.sum_filter,yLP,ite_mul,one_mul,zero_mul]

private theorem makespan_exists {n : ℕ} (p r : Fin n → ℕ) : ∃ T,IsMakespanBound p r T := by
  let R := Finset.univ.sup r
  let P := Finset.univ.sup p
  have hr (j : Fin n) : r j ≤ R := Finset.le_sup (f := r) (Finset.mem_univ j)
  have hp (j : Fin n) : p j ≤ P := Finset.le_sup (f := p) (Finset.mem_univ j)
  refine ⟨R+n*P,fun j => (R+j.val*P : ℕ),?_,?_,?_⟩
  · intro j
    dsimp only
    exact_mod_cast (show r j ≤ R+j.val*P by have := hr j;omega)
  · intro j k hjk
    rcases lt_or_gt_of_ne hjk with hh|hh
    · left
      have hval : j.val+1 ≤ k.val := hh
      have hm := Nat.mul_le_mul_right P hval
      have hj := hp j
      dsimp only
      norm_cast
      nlinarith
    · right
      have hval : k.val+1 ≤ j.val := hh
      have hm := Nat.mul_le_mul_right P hval
      have hk := hp k
      dsimp only
      norm_cast
      nlinarith
  · intro j
    have hm := Nat.mul_le_mul_right P j.isLt
    have hj := hp j
    dsimp only
    norm_cast
    nlinarith

private theorem lp_schedule {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hT : IsMakespanBound p r T) :
    SingleMachineSched.Shared.IsPreemptiveSchedule p r (lpSet p r) := by
  classical
  have hf := yLP_feasible p r T hT
  constructor
  · intro j
    rw [lpSet_finite p r T hT j]
    exact MeasurableSet.biUnion (Finset.finite_toSet _).countable (fun _ _ => measurableSet_Ico)
  · intro j t ht
    obtain ⟨τ,hτ,ht⟩ := mem_iUnion₂.mp ht
    have hr := (run_spec p r τ j hτ).1
    exact (show (r j : ℝ) ≤ τ by exact_mod_cast hr).trans ht.1
  · intro j
    rw [lpSet_finite p r T hT j,measure_biUnion_finset (fun τ _ σ _ hne => nat_intervals_disjoint hne) (fun _ _ => measurableSet_Ico)]
    have he : ((Finset.Ico (r j) T).filter (fun τ => lpRun p r τ=some j)).card=p j := by
      have hh := hf.2.2.2 j
      simp only [yLP] at hh
      simpa only [Finset.sum_boole, Nat.cast_inj] using hh
    simp [Real.volume_Ico,he]
  · intro j k hjk
    apply Set.disjoint_left.mpr
    intro t htj htk
    obtain ⟨τ,hτ,htτ⟩ := mem_iUnion₂.mp htj
    obtain ⟨σ,hσ,htσ⟩ := mem_iUnion₂.mp htk
    by_cases hτσ : τ=σ
    · subst σ
      exact hjk (Option.some.inj (hτ.symm.trans hσ))
    · exact Set.disjoint_left.mp (nat_intervals_disjoint hτσ) htτ htσ
  · intro j
    rw [lpSet_finite p r T hT j]
    exact (Bornology.isBounded_biUnion_finset _).mpr (fun _ _ => isCompact_Icc.isBounded.subset Ico_subset_Icc_self)

private theorem lp_moment {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hp : ∀ j,0 < p j)
    (hT : IsMakespanBound p r T) (j : Fin n) :
    (p j : ℝ)*mLP p r j=∑ τ∈Finset.range T,((τ : ℝ)+1/2)*yLP p r j τ := by
  have hpj : (p j : ℝ) ≠ 0 := by exact_mod_cast (hp j).ne'
  unfold mLP SingleMachineSched.Shared.meanBusyTime
  rw [lp_integral p r T hT j]
  have he : (p j : ℝ)*(1/(p j : ℝ))=1 := by field_simp
  rw [← mul_assoc,he,one_mul]
  rw [Finset.sum_subset (show Finset.Ico (r j) T ⊆ Finset.range T by intro τ hτ;exact Finset.mem_range.mpr (Finset.mem_Ico.mp hτ).2)]
  · apply Finset.sum_congr rfl
    intro τ hτ
    ring
  · intro τ hτ hn
    have hn : ¬(r j ≤ τ ∧ τ<T) := by simpa only [Finset.mem_Ico] using hn
    have ht := Finset.mem_range.mp hτ
    rw [(yLP_feasible p r T hT).2.1 j τ (Or.inl (by omega)),zero_mul]

private theorem between_job_runs {n : ℕ} (p r : Fin n → ℕ) (j k : Fin n) (a b t : ℕ)
    (hja : lpRun p r a=some j) (hjb : lpRun p r b=some j)
    (hat : a ≤ t) (htb : t ≤ b) (hkt : lpRun p r t=some k) (hkj : k ≠ j) :
    k < j ∧ a < r k ∧ lpRemaining p r b k=0 ∧
      ∀ u,lpRun p r u=some k → a < u ∧ u < b := by
  have hrelj : r j ≤ t := (run_spec p r a j hja).1.trans hat
  have hposj : 0 < lpRemaining p r t j := by
    have hh := remaining_antitone p r j htb
    have hh2 := (run_spec p r b j hjb).2.1
    dsimp only at hh
    omega
  have hklt : k < j := lt_of_le_of_ne ((run_spec p r t k hkt).2.2 j hrelj hposj) hkj
  have hrka : a < r k := by
    by_contra hn
    have hrel : r k ≤ a := by omega
    have hh := remaining_antitone p r k hat
    have hh2 := (run_spec p r t k hkt).2.1
    dsimp only at hh
    have hpos : 0 < lpRemaining p r a k := by omega
    have hjk := (run_spec p r a j hja).2.2 k hrel hpos
    exact (not_le_of_gt hklt) hjk
  have hkdone : lpRemaining p r b k=0 := by
    by_contra hn
    have hrel : r k ≤ b := (run_spec p r t k hkt).1.trans htb
    have hjk := (run_spec p r b j hjb).2.2 k hrel (Nat.pos_of_ne_zero hn)
    exact (not_le_of_gt hklt) hjk
  refine ⟨hklt,hrka,hkdone,?_⟩
  intro u hku
  refine ⟨hrka.trans_le (run_spec p r u k hku).1,?_⟩
  by_contra hn
  have hh := remaining_antitone p r k (show b ≤ u by omega)
  have hh2 := (run_spec p r u k hku).2.1
  dsimp only at hh
  omega

private theorem no_j_between_k {n : ℕ} (p r : Fin n → ℕ) (j k : Fin n) (u v t : ℕ)
    (hkj : k < j) (hku : lpRun p r u=some k) (hkv : lpRun p r v=some k)
    (hut : u ≤ t) (htv : t ≤ v) : lpRun p r t ≠ some j := by
  intro hjt
  have hrel : r k ≤ t := (run_spec p r u k hku).1.trans hut
  have hpos : 0 < lpRemaining p r t k := by
    have hh := remaining_antitone p r k htv
    have hh2 := (run_spec p r v k hkv).2.1
    dsimp only at hh
    omega
  have hh := (run_spec p r t j hjt).2.2 k hrel hpos
  exact (not_le_of_gt hkj) hh

private theorem all_busy_between_j {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) (a b t : ℕ)
    (hja : lpRun p r a=some j) (hjb : lpRun p r b=some j) (hat : a ≤ t) (htb : t ≤ b) :
    ∃ k,lpRun p r t=some k := by
  have hrel : r j ≤ t := (run_spec p r a j hja).1.trans hat
  have hpos : 0 < lpRemaining p r t j := by
    have hh := remaining_antitone p r j htb
    have hh2 := (run_spec p r b j hjb).2.1
    dsimp only at hh
    omega
  obtain ⟨k,hk,hle⟩ := run_exists p r t j hrel hpos
  exact ⟨k,hk⟩

private theorem job_endpoints {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hp : ∀ j,0 < p j)
    (hT : IsMakespanBound p r T) (j : Fin n) :
    ∃ a b : ℕ,a ≤ b ∧ lpRun p r a=some j ∧ lpRun p r b=some j ∧
      (∀ t,lpRun p r t=some j → a ≤ t ∧ t ≤ b) ∧
      sInf (lpSet p r j)=(a : ℝ) ∧ sSup (lpSet p r j)=(b : ℝ)+1 := by
  classical
  let A := (Finset.Ico (r j) T).filter (fun τ => lpRun p r τ=some j)
  have hcard : A.card=p j := by
    have hh := (yLP_feasible p r T hT).2.2.2 j
    simpa only [yLP,Finset.sum_boole,Nat.cast_inj] using hh
  have hA : A.Nonempty := Finset.card_pos.mp (by rw [hcard];exact hp j)
  let a := A.min' hA
  let b := A.max' hA
  have ha : a∈A := Finset.min'_mem A hA
  have hb : b∈A := Finset.max'_mem A hA
  have hja : lpRun p r a=some j := (Finset.mem_filter.mp ha).2
  have hjb : lpRun p r b=some j := (Finset.mem_filter.mp hb).2
  have hbounds (t : ℕ) (ht : lpRun p r t=some j) : a ≤ t ∧ t ≤ b := by
    have htA : t∈A := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨(run_spec p r t j ht).1,run_lt p r T hT t j ht⟩,ht⟩
    exact ⟨Finset.min'_le A t htA,Finset.le_max' A t htA⟩
  have hUa : (a : ℝ)∈lpSet p r j := mem_iUnion₂.mpr ⟨a,hja,by constructor;rfl;linarith⟩
  have hUbound : ∀ t∈lpSet p r j,(a : ℝ) ≤ t ∧ t ≤ (b : ℝ)+1 := by
    intro t ht
    obtain ⟨τ,hτ,ht⟩ := mem_iUnion₂.mp ht
    have hl : (a : ℝ) ≤ τ := by exact_mod_cast (hbounds τ hτ).1
    have hu : (τ : ℝ) ≤ b := by exact_mod_cast (hbounds τ hτ).2
    constructor <;> linarith [ht.1,ht.2]
  refine ⟨a,b,(hbounds b hjb).1,hja,hjb,hbounds,?_,?_⟩
  · apply IsLeast.csInf_eq
    exact ⟨hUa,fun t ht => (hUbound t ht).1⟩
  · apply le_antisymm
    · exact csSup_le ⟨a,hUa⟩ (fun t ht => (hUbound t ht).2)
    · have hi : Ico (b : ℝ) (b+1) ⊆ lpSet p r j := fun t ht => mem_iUnion₂.mpr ⟨b,hjb,ht⟩
      have hh := csSup_le_csSup ⟨(b : ℝ)+1,fun t ht => (hUbound t ht).2⟩ (Set.nonempty_Ico.mpr (by linarith : (b : ℝ)<b+1)) hi
      simpa only [csSup_Ico (by linarith : (b : ℝ)<b+1)] using hh

private theorem interruption_iff_slot {n : ℕ} (p r : Fin n → ℕ) (j k : Fin n) (a b : ℕ)
    (hja : lpRun p r a=some j) (hjb : lpRun p r b=some j) (hkj : k ≠ j) :
    0 < volume (lpSet p r k ∩ Ioo (a : ℝ) (b+1)) ↔
      ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k := by
  constructor
  · intro hpos
    obtain ⟨x,hxA,hxab⟩ := nonempty_of_measure_ne_zero hpos.ne'
    obtain ⟨t,ht,hxt⟩ := mem_iUnion₂.mp hxA
    have hat : a ≤ t := by
      have hh : (a : ℝ) < (t : ℝ)+1 := hxab.1.trans hxt.2
      have hh : a < t+1 := by exact_mod_cast hh
      omega
    have htb : t ≤ b := by
      have hh : (t : ℝ) < (b : ℝ)+1 := hxt.1.trans_lt hxab.2
      have hh : t < b+1 := by exact_mod_cast hh
      omega
    have hta : t ≠ a := by intro he;subst t;exact hkj (Option.some.inj (ht.symm.trans hja))
    have htbne : t ≠ b := by intro he;subst t;exact hkj (Option.some.inj (ht.symm.trans hjb))
    exact ⟨t,lt_of_le_of_ne hat hta.symm,lt_of_le_of_ne htb htbne,ht⟩
  · rintro ⟨t,hat,htb,ht⟩
    have hs : Ico (t : ℝ) (t+1) ⊆ lpSet p r k ∩ Ioo (a : ℝ) (b+1) := by
      intro x hx
      refine ⟨mem_iUnion₂.mpr ⟨t,ht,hx⟩,?_,?_⟩
      · have hh : (a : ℝ) < t := by exact_mod_cast hat
        exact hh.trans_le hx.1
      · have hh : (t : ℝ)+1 ≤ b+1 := by exact_mod_cast Nat.add_le_add_right htb.le 1
        exact hx.2.trans_le hh
    have hvol := measure_mono (μ := volume) hs
    have hv : volume (Ico (t : ℝ) (t+1))=1 := by simp [Real.volume_Ico]
    rw [hv] at hvol
    exact lt_of_lt_of_le (by norm_num) hvol

private theorem lp_cdf_integer {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) (u : ℕ) :
    (volume (lpSet p r j ∩ Iic (u : ℝ))).toReal=(served p r u j : ℝ) := by
  classical
  have he : (lpSet p r j ∩ Iic (u : ℝ) : Set ℝ) =ᵐ[volume] (lpSet p r j ∩ Iio (u : ℝ) : Set ℝ) := by
    filter_upwards [volume.ae_ne (u : ℝ)] with t ht
    apply propext
    change (t∈lpSet p r j ∧ t ≤ (u : ℝ)) ↔ (t∈lpSet p r j ∧ t < (u : ℝ))
    constructor
    · intro h;exact ⟨h.1,lt_of_le_of_ne h.2 ht⟩
    · intro h;exact ⟨h.1,h.2.le⟩
  have hset : lpSet p r j ∩ Iio (u : ℝ)=
      ⋃ τ∈(Finset.range u).filter (fun τ => lpRun p r τ=some j),Ico (τ : ℝ) (τ+1) := by
    ext t
    constructor
    · rintro ⟨ht,hlt⟩
      obtain ⟨τ,hτ,ht⟩ := mem_iUnion₂.mp ht
      have hτu : τ < u := by exact_mod_cast ht.1.trans_lt hlt
      exact mem_iUnion₂.mpr ⟨τ,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hτu,hτ⟩,ht⟩
    · intro ht
      obtain ⟨τ,hτ,ht⟩ := mem_iUnion₂.mp ht
      refine ⟨mem_iUnion₂.mpr ⟨τ,(Finset.mem_filter.mp hτ).2,ht⟩,?_⟩
      have hh : (τ : ℝ)+1 ≤ u := by exact_mod_cast Finset.mem_range.mp (Finset.mem_filter.mp hτ).1
      exact ht.2.trans_le hh
  rw [measure_congr he,hset,measure_biUnion_finset
    (fun τ _ σ _ hn => nat_intervals_disjoint hn) (fun _ _ => measurableSet_Ico)]
  simp only [Real.volume_Ico,add_sub_cancel_left,ENNReal.ofReal_one,Finset.sum_const,nsmul_eq_mul,mul_one,ENNReal.toReal_natCast]
  simpa only [yLP,Finset.sum_boole] using yLP_sum p r u j

private theorem served_step_real {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) (t : ℕ) :
    (served p r (t+1) j : ℝ)=(served p r t j : ℝ)+yLP p r j t := by
  rw [← yLP_sum,Finset.sum_range_succ,yLP_sum]

private theorem served_self_sum {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) (t : ℕ) :
    (∑ τ∈Finset.range t,(served p r τ j : ℝ)*yLP p r j τ)=
      (served p r t j : ℝ)*((served p r t j : ℝ)-1)/2 := by
  induction t with
  | zero => simp [served,lpRemaining]
  | succ t ih =>
    rw [Finset.sum_range_succ,ih,served_step_real]
    have he : (yLP p r j t)^2=yLP p r j t := by unfold yLP;split_ifs <;> norm_num
    nlinarith

private theorem served_zero_first {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) (a : ℕ)
    (ha : ∀ t,lpRun p r t=some j → a ≤ t) : served p r a j=0 := by
  have hh := yLP_sum p r a j
  have hz : (∑ τ∈Finset.range a,yLP p r j τ)=0 := by
    apply Finset.sum_eq_zero
    intro τ hτ
    unfold yLP
    rw [if_neg (by intro ht;have h1 := ha τ ht;have h2 := Finset.mem_range.mp hτ;omega)]
  rw [hz] at hh
  exact_mod_cast hh.symm

private theorem served_const_no_runs {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) (a b : ℕ)
    (hab : a ≤ b) (hn : ∀ t,a ≤ t → t < b → lpRun p r t ≠ some j) :
    served p r b j=served p r a j := by
  induction b,hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [served_step,if_neg (hn b hab (by omega)),Nat.add_zero]
    exact ih (fun t hat htb => hn t hat (by omega))

private theorem processed_busy_span {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) (a b t : ℕ)
    (hja : lpRun p r a=some j) (hjb : lpRun p r b=some j) (hat : a ≤ t) (htb : t ≤ b) :
    processed p r Finset.univ t=processed p r Finset.univ a+(t : ℝ)-a := by
  induction t,hat using Nat.le_induction with
  | base => ring
  | succ t hat ih =>
    obtain ⟨k,hk⟩ := all_busy_between_j p r j a b t hja hjb hat (by omega)
    rw [processed_run p r Finset.univ t k (Finset.mem_univ _) hk,ih (by omega)]
    push_cast
    ring

open Classical in
private theorem time_at_run {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) (a b : ℕ)
    (hja : lpRun p r a=some j) (hjb : lpRun p r b=some j)
    (hbounds : ∀ t,lpRun p r t=some j → a ≤ t ∧ t ≤ b)
    (τ : ℕ) (hτ : lpRun p r τ=some j) :
    (τ : ℝ)=(a : ℝ)+(served p r τ j : ℝ)+
      ∑ k∈Finset.univ.filter (fun k => k ≠ j ∧ ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k),(served p r τ k : ℝ) := by
  classical
  have hspan := processed_busy_span p r j a b τ hja hjb (hbounds τ hτ).1 (hbounds τ hτ).2
  have hjzero := served_zero_first p r j a (fun t ht => (hbounds t ht).1)
  have hterm (k : Fin n) : (served p r τ k : ℝ)-(served p r a k : ℝ)=
      (if k=j then (served p r τ j : ℝ) else 0)+
      (if k ≠ j ∧ ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k then (served p r τ k : ℝ) else 0) := by
    by_cases hkj : k=j
    · subst k;simp [hjzero]
    · by_cases hk : ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k
      · obtain ⟨t,hat,htb,hkt⟩ := hk
        have hrel := (between_job_runs p r j k a b t hja hjb hat.le htb.le hkt hkj).2.1
        have hz := served_before p r a k hrel.le
        simp [hkj,show ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k from ⟨t,hat,htb,hkt⟩,hz]
      · have he : served p r τ k=served p r a k := by
          apply served_const_no_runs p r k a τ (hbounds τ hτ).1
          intro t hat htt hkt
          have hta : t ≠ a := by intro he;subst t;exact hkj (Option.some.inj (hkt.symm.trans hja))
          exact hk ⟨t,lt_of_le_of_ne hat hta.symm,htt.trans_le (hbounds τ hτ).2,hkt⟩
        simp [hkj,hk,he]
  have he : processed p r Finset.univ τ-processed p r Finset.univ a=
      (served p r τ j : ℝ)+∑ k∈Finset.univ.filter (fun k => k ≠ j ∧ ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k),(served p r τ k : ℝ) := by
    simp only [processed,← Finset.sum_sub_distrib,hterm,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_filter]
  linarith

private theorem yLP_tail {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hT : IsMakespanBound p r T)
    (j k : Fin n) (u : ℕ) (hku : lpRun p r u=some k) (hkj : k ≠ j) :
    (∑ τ∈Finset.range T,if u < τ then yLP p r j τ else 0)=(p j : ℝ)-(served p r u j : ℝ) := by
  classical
  have huT := run_lt p r T hT u k hku
  have hzero : yLP p r j u=0 := by unfold yLP;rw [if_neg (by intro hh;exact hkj (Option.some.inj (hku.symm.trans hh)))]
  have hf : (Finset.range T).filter (fun τ => ¬u < τ)=Finset.range (u+1) := by
    ext τ
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  have he := Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun τ => u < τ) (yLP p r j)
  rw [hf,yLP_sum,yLP_sum,served_step_real,hzero,add_zero] at he
  have hdone : served p r T j=p j := by simp [served,remaining_zero_at p r T hT j]
  rw [hdone,Finset.sum_filter] at he
  linarith

private theorem interruption_partial {n : ℕ} (p r : Fin n → ℕ) (j k : Fin n) (u τ : ℕ)
    (hkj : k < j) (hku : lpRun p r u=some k) (hτ : lpRun p r τ=some j)
    (hfirst : ∀ t,lpRun p r t=some k → u ≤ t) :
    (served p r τ k : ℝ)=if u < τ then (p k : ℝ) else 0 := by
  by_cases hut : u < τ
  · rw [if_pos hut]
    have hd : lpRemaining p r τ k=0 := by
      by_contra hn
      have hh := (run_spec p r τ j hτ).2.2 k ((run_spec p r u k hku).1.trans hut.le) (Nat.pos_of_ne_zero hn)
      exact (not_le_of_gt hkj) hh
    simp [served,hd]
  · rw [if_neg hut]
    have hz := served_zero_first p r k τ (fun t ht => (show τ ≤ u by omega).trans (hfirst t ht))
    simp [hz]

private theorem interruption_cross_sum {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hT : IsMakespanBound p r T)
    (j k : Fin n) (u : ℕ) (hkj : k < j) (hku : lpRun p r u=some k)
    (hfirst : ∀ t,lpRun p r t=some k → u ≤ t) :
    (∑ τ∈Finset.range T,(served p r τ k : ℝ)*yLP p r j τ)=
      (p k : ℝ)*((p j : ℝ)-(served p r u j : ℝ)) := by
  have he (τ : ℕ) : (served p r τ k : ℝ)*yLP p r j τ=
      (p k : ℝ)*(if u < τ then yLP p r j τ else 0) := by
    by_cases hτ : lpRun p r τ=some j
    · rw [interruption_partial p r j k u τ hkj hku hτ hfirst]
      split_ifs <;> simp
    · simp [yLP,hτ]
  simp only [he,← Finset.mul_sum,yLP_tail p r T hT j k u hku hkj.ne]

open Classical in
private theorem moment_interruptions {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hp : ∀ j,0 < p j) (hT : IsMakespanBound p r T) (j : Fin n) (a b : ℕ)
    (hja : lpRun p r a=some j) (hjb : lpRun p r b=some j)
    (hbounds : ∀ t,lpRun p r t=some j → a ≤ t ∧ t ≤ b)
    (u : Fin n → ℕ) (hu : ∀ k,lpRun p r (u k)=some k)
    (hfirst : ∀ k t,lpRun p r t=some k → u k ≤ t) :
    (p j : ℝ)*mLP p r j=(p j : ℝ)*((a : ℝ)+(p j : ℝ)/2)+
      ∑ k∈Finset.univ.filter (fun k => k ≠ j ∧ ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k),
        (p k : ℝ)*((p j : ℝ)-(served p r (u k) j : ℝ)) := by
  classical
  let K := Finset.univ.filter (fun k => k ≠ j ∧ ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k)
  have he (τ : ℕ) : ((τ : ℝ)+1/2)*yLP p r j τ=
      ((a : ℝ)+1/2)*yLP p r j τ+(served p r τ j : ℝ)*yLP p r j τ+
        ∑ k∈K,(served p r τ k : ℝ)*yLP p r j τ := by
    by_cases hτ : lpRun p r τ=some j
    · have hh := time_at_run p r j a b hja hjb hbounds τ hτ
      have hy : yLP p r j τ=1 := by simp [yLP,hτ]
      rw [hy]
      simp only [mul_one]
      change (τ : ℝ)+1/2=(a : ℝ)+1/2+(served p r τ j : ℝ)+
        ∑ k∈Finset.univ.filter (fun k => k ≠ j ∧ ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k),(served p r τ k : ℝ)
      linarith
    · simp [yLP,hτ]
  have hdone : served p r T j=p j := by simp [served,remaining_zero_at p r T hT j]
  have hcross (k) (hk : k∈K) :
      (∑ τ∈Finset.range T,(served p r τ k : ℝ)*yLP p r j τ)=
        (p k : ℝ)*((p j : ℝ)-(served p r (u k) j : ℝ)) := by
    obtain ⟨hkj,t,hat,htb,hkt⟩ := (Finset.mem_filter.mp hk).2
    have hklt := (between_job_runs p r j k a b t hja hjb hat.le htb.le hkt hkj).1
    exact interruption_cross_sum p r T hT j k (u k) hklt (hu k) (hfirst k)
  rw [lp_moment p r T hp hT j]
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [yLP_sum,served_self_sum,hdone,Finset.sum_comm]
  have hx : (∑ k∈K,∑ τ∈Finset.range T,(served p r τ k : ℝ)*yLP p r j τ)=
      ∑ k∈K,(p k : ℝ)*((p j : ℝ)-(served p r (u k) j : ℝ)) := Finset.sum_congr rfl hcross
  rw [hx]
  change ((a : ℝ)+1/2)*(p j : ℝ)+(p j : ℝ)*((p j : ℝ)-1)/2+_= _
  ring

private theorem alpha_set_eq {n : ℕ} (p r : Fin n → ℕ) :
    SingleMachineSched.AlphaJSched.lpSet p r=lpSet p r := by
  have hr : SingleMachineSched.AlphaJSched.lpRemaining p r=lpRemaining p r := by
    funext t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext j
      simp only [SingleMachineSched.AlphaJSched.lpRemaining,lpRemaining,ih]
      rfl
  funext j
  unfold SingleMachineSched.AlphaJSched.lpSet lpSet
  simp only [SingleMachineSched.AlphaJSched.lpRun,lpRun,hr]
  rfl

theorem solution {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j,0 < p j) (hw : ∀ j,0 < w j)
    (hsort : ∀ j k : Fin n,j ≤ k → w k/p k ≤ w j/p j) (j : Fin n) :
    SingleMachineSched.AlphaJSched.mLP p r j=SingleMachineSched.AlphaJSched.startTime (SingleMachineSched.AlphaJSched.lpSet p r) j+
      ∑ k∈SingleMachineSched.AlphaJSched.N2 p r j,(1-SingleMachineSched.AlphaJSched.mu p r j k)*(p k : ℝ)+(p j : ℝ)/2 := by
  classical
  obtain ⟨T,hT⟩ := makespan_exists p r
  choose u v huv hur hvr hbds hstarts hends using fun k => job_endpoints p r T hp hT k
  let K := Finset.univ.filter (fun k => k ≠ j ∧ ∃ t : ℕ,u j < t ∧ t < v j ∧ lpRun p r t=some k)
  have hN : SingleMachineSched.AlphaJSched.N2 p r j=K := by
    ext k
    simp only [SingleMachineSched.AlphaJSched.N2,SingleMachineSched.AlphaJSched.lpCompletion,
      SingleMachineSched.AlphaJSched.startTime,alpha_set_eq,hstarts,hends,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨hkj,hvol⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkj,(interruption_iff_slot p r j k (u j) (v j) (hur j) (hvr j) hkj).mp hvol⟩
    · intro hk
      obtain ⟨hkj,hslot⟩ := (Finset.mem_filter.mp hk).2
      exact ⟨hkj,(interruption_iff_slot p r j k (u j) (v j) (hur j) (hvr j) hkj).mpr hslot⟩
  have hmu (k) : SingleMachineSched.AlphaJSched.mu p r j k=(served p r (u k) j : ℝ)/(p j : ℝ) := by
    unfold SingleMachineSched.AlphaJSched.mu SingleMachineSched.AlphaJSched.startTime
    rw [alpha_set_eq,hstarts,lp_cdf_integer]
  have hm := moment_interruptions p r T hp hT j (u j) (v j) (hur j) (hvr j) (hbds j) u hur (fun k t ht => (hbds k t ht).1)
  have hpj : (p j : ℝ) ≠ 0 := by exact_mod_cast (hp j).ne'
  have he (k) : (p k : ℝ)*((p j : ℝ)-(served p r (u k) j : ℝ))=
      (p j : ℝ)*((1-(served p r (u k) j : ℝ)/(p j : ℝ))*(p k : ℝ)) := by field_simp <;> ring
  rw [hN]
  simp only [hmu,SingleMachineSched.AlphaJSched.startTime,alpha_set_eq,hstarts,SingleMachineSched.AlphaJSched.mLP]
  change mLP p r j=(u j : ℝ)+∑ k∈K,(1-(served p r (u k) j : ℝ)/(p j : ℝ))*(p k : ℝ)+(p j : ℝ)/2
  apply mul_left_cancel₀ hpj
  rw [hm]
  simp only [he,← Finset.mul_sum]
  change (p j : ℝ)*((u j : ℝ)+(p j : ℝ)/2)+(p j : ℝ)*(∑ k∈K,(1-(served p r (u k) j : ℝ)/(p j : ℝ))*(p k : ℝ))=_
  ring
