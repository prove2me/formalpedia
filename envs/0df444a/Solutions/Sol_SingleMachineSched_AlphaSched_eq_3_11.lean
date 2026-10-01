-- Prove2me | solution 1 for SingleMachineSched.AlphaSched.eq_3_11
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:26:03.52363+00:00
-- url     : https://prove2.me/submissions/b0f961a0-6f56-408b-9312-73097ecd56f0

import Definitions.Def_SingleMachineSched_AlphaSched_AlphaSchedule
import Definitions.Def_SingleMachineSched_AlphaSched_AlphaPoints
import Mathlib.Data.Finset.Sort
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

private theorem slot_cdf (s t : ℝ) :
    (volume (Ico s (s+1) ∩ Iic t)).toReal=max (min (s+1) t-s) 0 := by
  have he : (Ico s (s+1) ∩ Iic t : Set ℝ) =ᵐ[volume] (Icc s (s+1) ∩ Iic t : Set ℝ) := by
    filter_upwards [Ico_ae_eq_Icc (μ := volume) (a := s) (b := s+1)] with x hx
    exact congrArg (fun b => b ∧ x∈Iic t) hx
  have he2 : Icc s (s+1) ∩ Iic t=Icc s (min (s+1) t) := by ext x;simp only [mem_inter_iff,Set.mem_Icc,Set.mem_Iic,le_min_iff];tauto
  rw [measure_congr he,he2,Real.volume_Icc,ENNReal.toReal_ofReal']

private theorem slots_disjoint {p : ℕ} (s : Fin p → ℕ) (hs : StrictMono s) :
    Pairwise (fun i j => Disjoint (Ico (s i : ℝ) (s i+1)) (Ico (s j : ℝ) (s j+1))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hh|hh
  · have hl : (s i : ℝ)+1 ≤ s j := by exact_mod_cast hs hh
    linarith [hi.2,hj.1]
  · have hl : (s j : ℝ)+1 ≤ s i := by exact_mod_cast hs hh
    linarith [hj.2,hi.1]

private theorem slots_cdf {p : ℕ} (s : Fin p → ℕ) (hs : StrictMono s) (t : ℝ) :
    (volume ((⋃ i,Ico (s i : ℝ) (s i+1)) ∩ Iic t)).toReal=
      ∑ i,max (min ((s i : ℝ)+1) t-(s i : ℝ)) 0 := by
  rw [iUnion_inter,measure_iUnion]
  · rw [tsum_fintype]
    rw [ENNReal.toReal_sum]
    · simp only [slot_cdf]
    · intro i hi
      exact (measure_mono (inter_subset_left)).trans_lt (by simp [Real.volume_Ico]) |>.ne
  · intro i j hij
    exact (slots_disjoint s hs hij).mono inter_subset_left inter_subset_left
  · intro i
    exact measurableSet_Ico.inter measurableSet_Iic
private theorem slots_cdf_at {p : ℕ} (s : Fin p → ℕ) (hs : StrictMono s) (i : Fin p) (t : ℝ)
    (hti : (s i : ℝ) ≤ t) (hit : t ≤ (s i : ℝ)+1) :
    (volume ((⋃ j,Ico (s j : ℝ) (s j+1)) ∩ Iic t)).toReal=(i.val : ℝ)+t-s i := by
  classical
  rw [slots_cdf s hs t]
  have he (j : Fin p) : max (min ((s j : ℝ)+1) t-(s j : ℝ)) 0=
      (if j < i then 1 else 0)+(if j=i then t-(s i : ℝ) else 0) := by
    rcases lt_trichotomy j i with h|h|h
    · have hj : (s j : ℝ)+1 ≤ s i := by exact_mod_cast hs h
      have htj : (s j : ℝ)+1 ≤ t := hj.trans hti
      rw [min_eq_left htj]
      simp [h,ne_of_lt h]
    · subst j
      rw [min_eq_right hit,max_eq_left (sub_nonneg.mpr hti)]
      simp
    · have hj : (s i : ℝ)+1 ≤ s j := by exact_mod_cast hs h
      have htj : t ≤ s j := hit.trans hj
      have hmin : min ((s j : ℝ)+1) t-(s j : ℝ) ≤ 0 := by have := min_le_right ((s j : ℝ)+1) t;linarith
      rw [max_eq_right hmin]
      simp [not_lt_of_gt h,ne_of_gt h]
  simp only [he,Finset.sum_add_distrib]
  have hfilter : Finset.univ.filter (fun j : Fin p => j < i)=Finset.Iio i := by ext j;simp
  simp only [Finset.sum_boole,Finset.sum_ite_eq',Finset.mem_univ,if_true,hfilter,Fin.card_Iio]
  ring

private theorem slot_quantile {p : ℕ} (s : Fin p → ℕ) (hs : StrictMono s) (i : Fin p) (x : ℝ)
    (hix : (i.val : ℝ) < x) (hxi : x ≤ (i.val : ℝ)+1) :
    sInf {t : ℝ | x ≤ (volume ((⋃ j,Ico (s j : ℝ) (s j+1)) ∩ Iic t)).toReal}=
      (s i : ℝ)+x-i.val := by
  let q : ℝ := (s i : ℝ)+x-i.val
  have hqlo : (s i : ℝ) ≤ q := by dsimp [q];linarith
  have hqhi : q ≤ (s i : ℝ)+1 := by dsimp [q];linarith
  have hq : (volume ((⋃ j,Ico (s j : ℝ) (s j+1)) ∩ Iic q)).toReal=x := by
    rw [slots_cdf_at s hs i q hqlo hqhi]
    dsimp [q]
    ring
  apply IsLeast.csInf_eq
  refine ⟨?_,?_⟩
  · exact hq.ge
  · intro t ht
    by_contra hn
    have htq : t < q := lt_of_not_ge hn
    let u := max t (s i : ℝ)
    have huq : u < q := max_lt htq (by dsimp [q];linarith)
    have hmono : (volume ((⋃ j,Ico (s j : ℝ) (s j+1)) ∩ Iic t)).toReal ≤
        (volume ((⋃ j,Ico (s j : ℝ) (s j+1)) ∩ Iic u)).toReal := by
      apply ENNReal.toReal_mono
      · have hf : volume (⋃ j,Ico (s j : ℝ) (s j+1)) ≠ ⊤ := by
          rw [measure_iUnion (slots_disjoint s hs) (fun _ => measurableSet_Ico),tsum_fintype]
          simp [Real.volume_Ico]
        exact ne_top_of_le_ne_top hf (measure_mono inter_subset_left)
      · apply measure_mono
        exact inter_subset_inter_right _ (Iic_subset_Iic.mpr (le_max_left _ _))
    have hu := slots_cdf_at s hs i u (le_max_right _ _) (huq.le.trans hqhi)
    rw [hu] at hmono
    dsimp [q] at huq
    change x ≤ (volume ((⋃ j,Ico (s j : ℝ) (s j+1)) ∩ Iic t)).toReal at ht
    linarith
private theorem slots_quantile_integral {p : ℕ} (hp : 0 < p) (s : Fin p → ℕ) (hs : StrictMono s) :
    (∫ a in Ioc (0 : ℝ) 1,sInf {t : ℝ | a*(p : ℝ) ≤ (volume ((⋃ j,Ico (s j : ℝ) (s j+1)) ∩ Iic t)).toReal})=
      (1/(p : ℝ))*∑ i,((s i : ℝ)+1/2) := by
  let Q := fun x : ℝ => sInf {t : ℝ | x ≤ (volume ((⋃ j,Ico (s j : ℝ) (s j+1)) ∩ Iic t)).toReal}
  have hlocal (i : Fin p) : Set.EqOn Q (fun x => (s i : ℝ)+x-i.val) (Ioc (i.val : ℝ) (i.val+1)) := by
    intro x hx
    exact slot_quantile s hs i x hx.1 hx.2
  have hint (i : Fin p) : IntervalIntegrable Q volume (i.val : ℝ) (i.val+1) := by
    apply ((show Continuous (fun x : ℝ => (s i : ℝ)+x-i.val) by fun_prop).intervalIntegrable _ _).congr
    rw [Set.uIoc_of_le (by linarith : (i.val : ℝ) ≤ i.val+1)]
    exact fun x hx => (hlocal i hx).symm
  have hlocalint (i : Fin p) : (∫ x in (i.val : ℝ)..(i.val+1),Q x)=(s i : ℝ)+1/2 := by
    rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => hlocal i (by simpa only [Set.uIoc_of_le (by linarith : (i.val : ℝ) ≤ i.val+1)] using hx)))]
    have hi : (∫ x in (i.val : ℝ)..(i.val+1),(s i : ℝ)+x-i.val)=
        (s i : ℝ)+1/2 := by
      rw [intervalIntegral.integral_sub,intervalIntegral.integral_add,intervalIntegral.integral_const,integral_id,intervalIntegral.integral_const]
      · simp only [smul_eq_mul]
        ring
      all_goals apply Continuous.intervalIntegrable;fun_prop
    exact hi
  have htotal : (∫ x in (0 : ℝ)..p,Q x)=∑ i,((s i : ℝ)+1/2) := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ)) (n := p)
      (fun k hk => by simpa only [Nat.cast_add,Nat.cast_one] using hint ⟨k,hk⟩)
    simp only [Nat.cast_zero] at hh
    rw [← hh]
    rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => ∫ x in (k : ℝ)..(k+1 : ℕ),Q x)]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Nat.cast_add,Nat.cast_one] using hlocalint i
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ a in (0 : ℝ)..1,Q (a*(p : ℝ)))=_
  rw [intervalIntegral.integral_comp_mul_right Q (by exact_mod_cast hp.ne')]
  simp only [zero_mul,one_mul,smul_eq_mul,htotal,one_div]

private theorem lp_quantile_mean {n : ℕ} (p r : Fin n → ℕ) (T : ℕ) (hp : ∀ j,0 < p j)
    (hT : IsMakespanBound p r T) (j : Fin n) :
    mLP p r j=∫ a in Ioc (0 : ℝ) 1,sInf {t : ℝ | a*(p j : ℝ) ≤ (volume (lpSet p r j ∩ Iic t)).toReal} := by
  classical
  let A := (Finset.Ico (r j) T).filter (fun τ => lpRun p r τ=some j)
  have hcard : A.card=p j := by
    have hh := (yLP_feasible p r T hT).2.2.2 j
    simpa only [yLP,Finset.sum_boole,Nat.cast_inj] using hh
  let e := A.orderIsoOfFin hcard
  let s : Fin (p j) → ℕ := fun i => e i
  have hs : StrictMono s := fun i k hik => e.strictMono hik
  have hset : lpSet p r j=⋃ i,Ico (s i : ℝ) (s i+1) := by
    rw [lpSet_finite p r T hT j]
    ext t
    constructor
    · intro ht
      obtain ⟨τ,hτ,ht⟩ := mem_iUnion₂.mp ht
      obtain ⟨i,hi⟩ := e.surjective ⟨τ,hτ⟩
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      simpa only [s,hi] using ht
    · intro ht
      obtain ⟨i,hi⟩ := mem_iUnion.mp ht
      exact mem_iUnion₂.mpr ⟨s i,(e i).property,hi⟩
  have hint : (∫ t in lpSet p r j,t)=∑ i,((s i : ℝ)+1/2) := by
    rw [hset,integral_iUnion_fintype (f := fun t : ℝ => t) (μ := volume) (fun _ => measurableSet_Ico) (slots_disjoint s hs)
      (fun _ => continuous_id.integrableOn_Icc.mono_set Ico_subset_Icc_self)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith),integral_id]
    ring
  unfold mLP SingleMachineSched.Shared.meanBusyTime
  rw [hint,hset,slots_quantile_integral (hp j) s hs]

private theorem alpha_set_eq {n : ℕ} (p r : Fin n → ℕ) :
    SingleMachineSched.AlphaSched.lpSet p r=lpSet p r := by
  have hr : SingleMachineSched.AlphaSched.lpRemaining p r=lpRemaining p r := by
    funext t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext j
      simp only [SingleMachineSched.AlphaSched.lpRemaining,lpRemaining,ih]
      rfl
  funext j
  unfold SingleMachineSched.AlphaSched.lpSet lpSet
  simp only [SingleMachineSched.AlphaSched.lpRun,lpRun,hr]
  rfl

private theorem unit_index {p : ℕ} (x : ℝ) (hx : 0 < x) (hxp : x ≤ p) :
    ∃ i : Fin p,(i.val : ℝ) < x ∧ x ≤ (i.val : ℝ)+1 := by
  have hpceil : 0 < Nat.ceil x := Nat.ceil_pos.mpr hx
  have hceilp : Nat.ceil x ≤ p := Nat.ceil_le.mpr hxp
  refine ⟨⟨Nat.ceil x-1,by omega⟩,?_,?_⟩
  · have hh := Nat.ceil_lt_add_one hx.le
    have he : (Nat.ceil x-1 : ℝ)=(Nat.ceil x : ℝ)-1 := by norm_cast
    simp only [Fin.val_mk]
    rw [Nat.cast_sub hpceil]
    norm_num
    linarith
  · have hh := Nat.le_ceil x
    simp only [Fin.val_mk]
    rw [Nat.cast_sub hpceil]
    norm_num
    linarith

private theorem capacity_window {n : ℕ} (A : Fin n → Set ℝ)
    (hm : ∀ j,MeasurableSet (A j)) (hd : Pairwise (fun j k => Disjoint (A j) (A k)))
    (hf : ∀ j,volume (A j) ≠ ⊤) (S : Finset (Fin n)) (s t : ℝ) (hst : s ≤ t) :
    (∑ j∈S,((volume (A j ∩ Iic t)).toReal-(volume (A j ∩ Iic s)).toReal)) ≤ t-s := by
  have hwin (j : Fin n) :
      (volume (A j ∩ Iic t)).toReal-(volume (A j ∩ Iic s)).toReal=(volume (A j ∩ Ioc s t)).toReal := by
    have he : (A j ∩ Iic s) ∪ (A j ∩ Ioc s t)=A j ∩ Iic t := by
      ext x
      simp only [mem_union,mem_inter_iff,Set.mem_Iic,Set.mem_Ioc]
      constructor
      · rintro (⟨hA,hx⟩|⟨hA,hx⟩)
        · exact ⟨hA,hx.trans hst⟩
        · exact ⟨hA,hx.2⟩
      · rintro ⟨hA,hxt⟩
        by_cases hxs : x ≤ s
        · exact Or.inl ⟨hA,hxs⟩
        · exact Or.inr ⟨hA,lt_of_not_ge hxs,hxt⟩
    have hdis : Disjoint (A j ∩ Iic s) (A j ∩ Ioc s t) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact (not_lt_of_ge hx.2) hy.2.1
    have heq := measure_union (μ := volume) hdis ((hm j).inter measurableSet_Ioc)
    rw [he] at heq
    have h1 : volume (A j ∩ Iic s) ≠ ⊤ := ne_top_of_le_ne_top (hf j) (measure_mono inter_subset_left)
    have h2 : volume (A j ∩ Ioc s t) ≠ ⊤ := ne_top_of_le_ne_top (hf j) (measure_mono inter_subset_left)
    have hr := congrArg ENNReal.toReal heq
    rw [ENNReal.toReal_add h1 h2] at hr
    linarith
  simp only [hwin]
  have hu : volume (⋃ j∈S,A j ∩ Ioc s t)=∑ j∈S,volume (A j ∩ Ioc s t) :=
    measure_biUnion_finset (fun i hi j hj hij => (hd hij).mono inter_subset_left inter_subset_left)
      (fun j hj => (hm j).inter measurableSet_Ioc)
  have hle : volume (⋃ j∈S,A j ∩ Ioc s t) ≤ volume (Ioc s t) := by
    apply measure_mono
    intro x hx
    obtain ⟨j,hj,hx⟩ := mem_iUnion₂.mp hx
    exact hx.2
  have hr := ENNReal.toReal_mono (by simp [Real.volume_Ioc]) hle
  rw [hu,ENNReal.toReal_sum (fun j hj => ne_top_of_le_ne_top (hf j) (measure_mono inter_subset_left)),Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] at hr
  exact hr


private theorem completion_from_cdf {n : ℕ} (p r : Fin n → ℕ) (a x : Fin n → ℝ)
    (C : Fin n → ℝ → ℝ) (O : Fin n → Fin n → Prop) [DecidableRel O]
    (hp : ∀ j,0 < p j) (ha : ∀ j,0 < a j) (hself : ∀ j,O j j)
    (horder : ∀ j k,O j k → x j ≤ x k) (hrel : ∀ j,(r j : ℝ) ≤ x j)
    (hmono : ∀ j,Monotone (C j)) (hupper : ∀ j t,C j t ≤ p j)
    (hpoint : ∀ j,C j (x j)=a j*(p j : ℝ))
    (hcap : ∀ (S : Finset (Fin n)) (s t : ℝ),s ≤ t → (∑ k ∈ S, (C k t - C k s)) ≤ t-s) (j : Fin n) :
    (Finset.univ.filter (fun k => O k j)).sup'
      ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hself j⟩⟩
      (fun k => (r k : ℝ)+∑ i∈Finset.univ.filter (fun i => O k i ∧ O i j),(p i : ℝ)) ≤
    x j+∑ k∈Finset.univ.filter (fun k => a k ≤ C k (x j)/p k),(1+a k-C k (x j)/p k)*(p k : ℝ) := by
  classical
  let D := fun k => (1+a k-C k (x j)/p k)*(p k : ℝ)
  have hpR (k) : (0 : ℝ) < p k := by exact_mod_cast hp k
  have hD (k) : D k=(p k : ℝ)-(C k (x j)-a k*(p k : ℝ)) := by dsimp [D];field_simp [(hpR k).ne'];ring
  have hDnonneg (k) : 0 ≤ D k := by rw [hD];have hh := hupper k (x j);have hh2 := mul_pos (ha k) (hpR k);linarith
  apply Finset.sup'_le
  intro i hi
  have hij := (Finset.mem_filter.mp hi).2
  let K := Finset.univ.filter (fun k => O i k ∧ O k j)
  have hsum : (∑ k∈K,(C k (x j)-a k*(p k : ℝ))) ≤ x j-x i := by
    apply le_trans _ (hcap K (x i) (x j) (horder i j hij))
    apply Finset.sum_le_sum
    intro k hk
    have hh := hmono k (horder i k (Finset.mem_filter.mp hk).2.1)
    rw [hpoint] at hh
    linarith
  have hKsub : K ⊆ Finset.univ.filter (fun k => a k ≤ C k (x j)/p k) := by
    intro k hk
    have hh := hmono k (horder k j (Finset.mem_filter.mp hk).2.2)
    rw [hpoint] at hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(le_div_iff₀ (hpR k)).mpr hh⟩
  have hsumD : (∑ k∈K,D k)=(∑ k∈K,(p k : ℝ))-(∑ k∈K,(C k (x j)-a k*(p k : ℝ))) := by
    simp only [hD,Finset.sum_sub_distrib]
  have hext := Finset.sum_le_sum_of_subset_of_nonneg hKsub (fun k hk hn => hDnonneg k)
  have hr := hrel i
  change (r i : ℝ)+(∑ k∈K,(p k : ℝ)) ≤ x j+∑ k∈Finset.univ.filter (fun k => a k ≤ C k (x j)/p k),D k
  linarith

private theorem lp_quantile_properties {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hp : ∀ j,0 < p j) (hT : IsMakespanBound p r T) (j : Fin n) (α : ℝ) (hα : 0 < α ∧ α ≤ 1) :
    let q := sInf {t : ℝ | α*(p j : ℝ) ≤ (volume (lpSet p r j ∩ Iic t)).toReal}
    (r j : ℝ) ≤ q ∧ (volume (lpSet p r j ∩ Iic q)).toReal=α*(p j : ℝ) := by
  classical
  let A := (Finset.Ico (r j) T).filter (fun τ => lpRun p r τ=some j)
  have hcard : A.card=p j := by
    have hh := (yLP_feasible p r T hT).2.2.2 j
    simpa only [yLP,Finset.sum_boole,Nat.cast_inj] using hh
  let e := A.orderIsoOfFin hcard
  let s : Fin (p j) → ℕ := fun i => e i
  have hs : StrictMono s := fun i k hik => e.strictMono hik
  have hsr (i : Fin (p j)) : r j ≤ s i := (Finset.mem_Ico.mp (Finset.mem_filter.mp (e i).property).1).1
  have hset : lpSet p r j=⋃ i,Ico (s i : ℝ) (s i+1) := by
    rw [lpSet_finite p r T hT j]
    ext t
    constructor
    · intro ht
      obtain ⟨τ,hτ,ht⟩ := mem_iUnion₂.mp ht
      obtain ⟨i,hi⟩ := e.surjective ⟨τ,hτ⟩
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      simpa only [s,hi] using ht
    · intro ht
      obtain ⟨i,hi⟩ := mem_iUnion.mp ht
      exact mem_iUnion₂.mpr ⟨s i,(e i).property,hi⟩
  have hpj : (0 : ℝ) < p j := by exact_mod_cast hp j
  obtain ⟨i,hix,hxi⟩ := unit_index (α*(p j : ℝ)) (mul_pos hα.1 hpj) (by nlinarith [hα.2])
  dsimp only
  rw [hset,slot_quantile s hs i _ hix hxi]
  refine ⟨?_,?_⟩
  · have hr : (r j : ℝ) ≤ s i := by exact_mod_cast hsr i
    linarith
  · rw [slots_cdf_at s hs i _ (by linarith) (by linarith)]
    ring

private theorem alpha_corollary {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j,0 < p j) (hw : ∀ j,0 < w j)
    (hsort : ∀ j k : Fin n,j ≤ k → w k/p k ≤ w j/p j)
    (α : Fin n → ℝ) (hα : ∀ k,0 < α k ∧ α k ≤ 1) (j : Fin n) :
    SingleMachineSched.AlphaSched.alphaCompletion p r α j ≤
      SingleMachineSched.AlphaSched.alphaPoint p (SingleMachineSched.AlphaSched.lpSet p r) j (α j)+
      ∑ k∈Finset.univ.filter (fun k => α k ≤ SingleMachineSched.AlphaSched.eta p (SingleMachineSched.AlphaSched.lpSet p r) j (α j) k),
        (1+α k-SingleMachineSched.AlphaSched.eta p (SingleMachineSched.AlphaSched.lpSet p r) j (α j) k)*(p k : ℝ) := by
  classical
  obtain ⟨T,hT⟩ := makespan_exists p r
  let A := SingleMachineSched.AlphaSched.lpSet p r
  let x := fun j => SingleMachineSched.AlphaSched.alphaPoint p A j (α j)
  let C := fun j t => (volume (A j ∩ Iic t)).toReal
  have hA : SingleMachineSched.Shared.IsPreemptiveSchedule p r A := by
    simpa only [A,alpha_set_eq] using lp_schedule p r T hT
  have hf (k) : volume (A k) ≠ ⊤ := by rw [hA.volume_eq];simp
  have hprop (k) : (r k : ℝ) ≤ x k ∧ C k (x k)=α k*(p k : ℝ) := by
    dsimp [x,C,A,SingleMachineSched.AlphaSched.alphaPoint]
    rw [alpha_set_eq]
    exact lp_quantile_properties p r T hp hT k (α k) (hα k)
  apply completion_from_cdf p r α x C (SingleMachineSched.AlphaSched.alphaOrder p r α) hp (fun k => (hα k).1)
  · intro k;exact Or.inr ⟨rfl,le_rfl⟩
  · intro k l hkl
    exact hkl.elim le_of_lt (fun h => h.1.le)
  · exact fun k => (hprop k).1
  · intro k s t hst
    apply ENNReal.toReal_mono
    · exact ne_top_of_le_ne_top (hf k) (measure_mono inter_subset_left)
    · exact measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.mpr hst))
  · intro k t
    calc
      C k t ≤ (volume (A k)).toReal := ENNReal.toReal_mono (hf k) (measure_mono inter_subset_left)
      _=(p k : ℝ) := by rw [hA.volume_eq];simp
  · exact fun k => (hprop k).2
  · exact capacity_window A hA.measurable hA.disjoint hf

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

private theorem lp_quantile_slot {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hp : ∀ j,0 < p j) (hT : IsMakespanBound p r T) (j : Fin n) (α : ℝ) (hα : 0 < α ∧ α ≤ 1) :
    let q := sInf {t : ℝ | α*(p j : ℝ) ≤ (volume (lpSet p r j ∩ Iic t)).toReal}
    ∃ τ : ℕ,lpRun p r τ=some j ∧ (τ : ℝ) < q ∧ q ≤ (τ : ℝ)+1 ∧
      (served p r τ j : ℝ) < α*(p j : ℝ) ∧ α*(p j : ℝ) ≤ (served p r τ j : ℝ)+1 ∧
      q=(τ : ℝ)+α*(p j : ℝ)-(served p r τ j : ℝ) := by
  classical
  let A := (Finset.Ico (r j) T).filter (fun τ => lpRun p r τ=some j)
  have hcard : A.card=p j := by
    have hh := (yLP_feasible p r T hT).2.2.2 j
    simpa only [yLP,Finset.sum_boole,Nat.cast_inj] using hh
  let e := A.orderIsoOfFin hcard
  let s : Fin (p j) → ℕ := fun i => e i
  have hs : StrictMono s := fun i k hik => e.strictMono hik
  have hsr (i : Fin (p j)) : r j ≤ s i := (Finset.mem_Ico.mp (Finset.mem_filter.mp (e i).property).1).1
  have hset : lpSet p r j=⋃ i,Ico (s i : ℝ) (s i+1) := by
    rw [lpSet_finite p r T hT j]
    ext t
    constructor
    · intro ht
      obtain ⟨τ,hτ,ht⟩ := mem_iUnion₂.mp ht
      obtain ⟨i,hi⟩ := e.surjective ⟨τ,hτ⟩
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      simpa only [s,hi] using ht
    · intro ht
      obtain ⟨i,hi⟩ := mem_iUnion.mp ht
      exact mem_iUnion₂.mpr ⟨s i,(e i).property,hi⟩
  have hpj : (0 : ℝ) < p j := by exact_mod_cast hp j
  obtain ⟨i,hix,hxi⟩ := unit_index (α*(p j : ℝ)) (mul_pos hα.1 hpj) (by nlinarith [hα.2])
  have hrank : (served p r (s i) j : ℝ)=(i.val : ℝ) := by
    rw [← lp_cdf_integer p r j (s i),hset,slots_cdf_at s hs i (s i : ℝ) le_rfl (by linarith)]
    ring
  dsimp only
  rw [hset,slot_quantile s hs i _ hix hxi]
  refine ⟨s i,(Finset.mem_filter.mp (e i).property).2,?_,?_,?_,?_,?_⟩
  all_goals try rw [hrank]
  all_goals linarith

private theorem served_monotone {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : Monotone (fun t => served p r t j) := by
  intro a b hab
  exact Nat.sub_le_sub_left (remaining_antitone p r j hab) _

open Classical in
private theorem quantile_interruptions {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hp : ∀ j,0 < p j) (hT : IsMakespanBound p r T) (j : Fin n) (a b : ℕ)
    (hja : lpRun p r a=some j) (hjb : lpRun p r b=some j)
    (hbounds : ∀ t,lpRun p r t=some j → a ≤ t ∧ t ≤ b)
    (u : Fin n → ℕ) (hu : ∀ k,lpRun p r (u k)=some k)
    (hfirst : ∀ k t,lpRun p r t=some k → u k ≤ t) (α : ℝ) (hα : 0 < α ∧ α ≤ 1) :
    let q := sInf {t : ℝ | α*(p j : ℝ) ≤ (volume (lpSet p r j ∩ Iic t)).toReal}
    let K := Finset.univ.filter (fun k => k ≠ j ∧ ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k)
    (q=(a : ℝ)+α*(p j : ℝ)+∑ k∈K,(if (served p r (u k) j : ℝ) < α*(p j : ℝ) then (p k : ℝ) else 0)) ∧
      ∀ k∈K,(volume (lpSet p r k ∩ Iic q)).toReal=
        if (served p r (u k) j : ℝ) < α*(p j : ℝ) then (p k : ℝ) else 0 := by
  classical
  dsimp only
  let q := sInf {t : ℝ | α*(p j : ℝ) ≤ (volume (lpSet p r j ∩ Iic t)).toReal}
  let K := Finset.univ.filter (fun k => k ≠ j ∧ ∃ t : ℕ,a < t ∧ t < b ∧ lpRun p r t=some k)
  obtain ⟨τ,hτ,hτq,hqτ,hlo,hhi,hqeq⟩ := lp_quantile_slot p r T hp hT j α hα
  have hpoint := (lp_quantile_properties p r T hp hT j α hα).2
  have hA := lp_schedule p r T hT
  have hf (k) : volume (lpSet p r k) ≠ ⊤ := by rw [hA.volume_eq];simp
  have hcut (k) (hkj : k ≠ j) : u k < τ ↔ (served p r (u k) j : ℝ) < α*(p j : ℝ) := by
    constructor
    · intro hh
      have hm : (served p r (u k) j : ℝ) ≤ served p r τ j := by exact_mod_cast served_monotone p r j hh.le
      linarith
    · intro hh
      by_contra hn
      have hut : τ < u k := by
        have hne : τ ≠ u k := by intro he;rw [he,hu k] at hτ;exact hkj (Option.some.inj hτ)
        omega
      have hm : (served p r (τ+1) j : ℝ) ≤ served p r (u k) j := by exact_mod_cast served_monotone p r j hut
      rw [served_step_real] at hm
      have hy : yLP p r j τ=1 := by simp [yLP,hτ]
      rw [hy] at hm
      linarith
  have hpart (k) (hk : k∈K) : (served p r τ k : ℝ)=
      if (served p r (u k) j : ℝ) < α*(p j : ℝ) then (p k : ℝ) else 0 := by
    obtain ⟨hkj,t,hat,htb,hkt⟩ := (Finset.mem_filter.mp hk).2
    have hklt := (between_job_runs p r j k a b t hja hjb hat.le htb.le hkt hkj).1
    rw [interruption_partial p r j k (u k) τ hklt (hu k) hτ (hfirst k)]
    simp only [hcut k hkj]
  constructor
  · have ht := time_at_run p r j a b hja hjb hbounds τ hτ
    have hs : (∑ k∈K,(served p r τ k : ℝ))=
        ∑ k∈K,if (served p r (u k) j : ℝ) < α*(p j : ℝ) then (p k : ℝ) else 0 := Finset.sum_congr rfl hpart
    change q=(a : ℝ)+α*(p j : ℝ)+_
    change (τ : ℝ)=(a : ℝ)+(served p r τ j : ℝ)+∑ k∈K,(served p r τ k : ℝ) at ht
    rw [hs] at ht
    linarith
  · intro k hk
    have hkj := (Finset.mem_filter.mp hk).2.1
    have hc := capacity_window (lpSet p r) hA.measurable hA.disjoint hf {j,k} (τ : ℝ) q hτq.le
    simp only [Finset.sum_pair hkj.symm,lp_cdf_integer] at hc
    have hmono : (volume (lpSet p r k ∩ Iic (τ : ℝ))).toReal ≤ (volume (lpSet p r k ∩ Iic q)).toReal := by
      apply ENNReal.toReal_mono (ne_top_of_le_ne_top (hf k) (measure_mono inter_subset_left))
      exact measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.mpr hτq.le))
    rw [lp_cdf_integer] at hmono
    have he : (volume (lpSet p r k ∩ Iic q)).toReal=(served p r τ k : ℝ) := by
      change (volume (lpSet p r j ∩ Iic q)).toReal=α*(p j : ℝ) at hpoint
      rw [hpoint] at hc
      linarith
    rw [he]
    exact hpart k hk

open Classical in
private theorem alpha_structure_bound {n : ℕ} (p : Fin n → ℕ) (α η : Fin n → ℝ) (j : Fin n)
    (K : Finset (Fin n)) (D : Fin n → Prop) (s q C : ℝ)
    (hα : ∀ k,0 < α k ∧ α k ≤ 1) (hjK : j∉K) (hηj : η j=α j)
    (hηK : ∀ k∈K,η k=if D k then 1 else 0)
    (hq : q=s+α j*(p j : ℝ)+∑ k∈K,if D k then (p k : ℝ) else 0)
    (hC : C ≤ q+∑ k∈Finset.univ.filter (fun k => α k ≤ η k),(1+α k-η k)*(p k : ℝ)) :
    C ≤ s+∑ k∈(Finset.univ.filter (fun k => k ≠ j ∧ k∉K)).filter (fun k => α k ≤ η k),(1+α k-η k)*(p k : ℝ)+
      ∑ k∈K.filter D,(1+α k)*(p k : ℝ)+(1+α j)*(p j : ℝ) := by
  classical
  let F := fun k => if α k ≤ η k then (1+α k-η k)*(p k : ℝ) else 0
  have hpoint (k) : F k=(if k=j then (p j : ℝ) else 0)+
      (if k ≠ j ∧ k∉K then F k else 0)+(if k∈K then (if D k then α k*(p k : ℝ) else 0) else 0) := by
    by_cases hkj : k=j
    · subst k;simp [F,hηj,hjK]
    · by_cases hk : k∈K
      · rw [show F k=if D k then α k*(p k : ℝ) else 0 by
          dsimp [F]
          rw [hηK k hk]
          by_cases hd : D k
          · simp [hd,(hα k).2]
          · simp [hd,not_le.mpr (hα k).1]]
        simp [hkj,hk]
      · simp [hkj,hk]
  have hsplit : (∑ k,F k)=(p j : ℝ)+
      (∑ k∈Finset.univ.filter (fun k => k ≠ j ∧ k∉K),F k)+
      (∑ k∈K,if D k then α k*(p k : ℝ) else 0) := by
    conv_lhs => arg 2;ext k;rw [hpoint]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,← Finset.sum_filter]
    simp
  have hjoin : (∑ k∈K,if D k then (p k : ℝ) else 0)+(∑ k∈K,if D k then α k*(p k : ℝ) else 0)=
      ∑ k∈K.filter D,(1+α k)*(p k : ℝ) := by
    rw [← Finset.sum_add_distrib,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> ring
  have hNF : (∑ k∈Finset.univ.filter (fun k => k ≠ j ∧ k∉K),F k)=
      ∑ k∈(Finset.univ.filter (fun k => k ≠ j ∧ k∉K)).filter (fun k => α k ≤ η k),(1+α k-η k)*(p k : ℝ) := by simp only [Finset.sum_filter,F]
  have he : (∑ k∈Finset.univ.filter (fun k => α k ≤ η k),(1+α k-η k)*(p k : ℝ))=∑ k,F k := by simp only [Finset.sum_filter,F]
  rw [he,hsplit,hNF,hq] at hC
  linarith

theorem solution {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j,0 < p j) (hw : ∀ j,0 < w j)
    (hsort : ∀ j k : Fin n,j ≤ k → w k/p k ≤ w j/p j)
    (α : Fin n → ℝ) (hα : ∀ k,0 < α k ∧ α k ≤ 1) (j : Fin n) :
    SingleMachineSched.AlphaSched.alphaCompletion p r α j ≤
      SingleMachineSched.AlphaSched.startTime (SingleMachineSched.AlphaSched.lpSet p r) j+
      ∑ k∈(SingleMachineSched.AlphaSched.N1 p r j).filter (fun k => α k ≤ SingleMachineSched.AlphaSched.eta p (SingleMachineSched.AlphaSched.lpSet p r) j (α j) k),
        (1+α k-SingleMachineSched.AlphaSched.eta p (SingleMachineSched.AlphaSched.lpSet p r) j (α j) k)*(p k : ℝ)+
      ∑ k∈(SingleMachineSched.AlphaSched.N2 p r j).filter (fun k => SingleMachineSched.AlphaSched.mu p r j k < α j),(1+α k)*(p k : ℝ)+
      (1+α j)*(p j : ℝ) := by
  classical
  obtain ⟨T,hT⟩ := makespan_exists p r
  choose u v huv hur hvr hbds hstarts hends using fun k => job_endpoints p r T hp hT k
  let K := Finset.univ.filter (fun k => k ≠ j ∧ ∃ t : ℕ,u j < t ∧ t < v j ∧ lpRun p r t=some k)
  have hN : SingleMachineSched.AlphaSched.N2 p r j=K := by
    ext k
    simp only [SingleMachineSched.AlphaSched.N2,SingleMachineSched.AlphaSched.lpCompletion,
      SingleMachineSched.AlphaSched.startTime,alpha_set_eq,hstarts,hends,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨hkj,hvol⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkj,(interruption_iff_slot p r j k (u j) (v j) (hur j) (hvr j) hkj).mp hvol⟩
    · intro hk
      obtain ⟨hkj,hslot⟩ := (Finset.mem_filter.mp hk).2
      exact ⟨hkj,(interruption_iff_slot p r j k (u j) (v j) (hur j) (hvr j) hkj).mpr hslot⟩
  have hmu (k) : SingleMachineSched.AlphaSched.mu p r j k=(served p r (u k) j : ℝ)/(p j : ℝ) := by
    unfold SingleMachineSched.AlphaSched.mu SingleMachineSched.AlphaSched.startTime
    rw [alpha_set_eq,hstarts,lp_cdf_integer]
  have hpR (k) : (0 : ℝ) < p k := by exact_mod_cast hp k
  have hcut (k) : SingleMachineSched.AlphaSched.mu p r j k < α j ↔ (served p r (u k) j : ℝ) < α j*(p j : ℝ) := by
    rw [hmu,div_lt_iff₀ (hpR j)]
  have hs := quantile_interruptions p r T hp hT j (u j) (v j) (hur j) (hvr j) (hbds j) u hur
    (fun k t ht => (hbds k t ht).1) (α j) (hα j)
  dsimp only at hs
  apply alpha_structure_bound p α (fun k => SingleMachineSched.AlphaSched.eta p (SingleMachineSched.AlphaSched.lpSet p r) j (α j) k)
    j (SingleMachineSched.AlphaSched.N2 p r j) (fun k => SingleMachineSched.AlphaSched.mu p r j k < α j)
    (SingleMachineSched.AlphaSched.startTime (SingleMachineSched.AlphaSched.lpSet p r) j)
    (SingleMachineSched.AlphaSched.alphaPoint p (SingleMachineSched.AlphaSched.lpSet p r) j (α j))
    (SingleMachineSched.AlphaSched.alphaCompletion p r α j) hα
  · rw [hN]
    simp [K]
  · unfold SingleMachineSched.AlphaSched.eta SingleMachineSched.AlphaSched.alphaPoint
    rw [alpha_set_eq,(lp_quantile_properties p r T hp hT j (α j) (hα j)).2]
    field_simp [(hpR j).ne']
  · intro k hk
    unfold SingleMachineSched.AlphaSched.eta SingleMachineSched.AlphaSched.alphaPoint
    rw [alpha_set_eq]
    have hk' : k∈K := hN ▸ hk
    rw [hs.2 k hk']
    simp only [hcut]
    split_ifs <;> simp [(hpR k).ne']
  · unfold SingleMachineSched.AlphaSched.alphaPoint SingleMachineSched.AlphaSched.startTime
    rw [alpha_set_eq,hstarts,hN]
    simp only [hcut]
    exact hs.1
  · exact alpha_corollary p r w hp hw hsort α hα j
