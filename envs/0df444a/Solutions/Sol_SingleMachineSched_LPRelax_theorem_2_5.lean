-- Prove2me | solution 1 for SingleMachineSched.LPRelax.theorem_2_5
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:35:32.208701+00:00
-- url     : https://prove2.me/submissions/b400a913-1756-4dc3-96ec-80e9b0eea32b

import Definitions.Def_SingleMachineSched_Shared_RelaxationR
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

private theorem period_sum (a b : ℕ) (hab : a ≤ b) :
    (∑ t∈Finset.Ico a b,((t : ℝ)+1/2))=((b : ℝ)-a)*((a : ℝ)+((b : ℝ)-a)/2) := by
  induction b,hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab,ih]
    push_cast
    ring

private theorem first_busy_period {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hp : ∀ j,0 < p j) (hT : IsMakespanBound p r T) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hwork : ∀ t,(∃ j∈S,r j ≤ t ∧ 0 < lpRemaining p r t j) → ∃ j∈S,lpRun p r t=some j) :
    ∃ a b : ℕ,a < b ∧ b ≤ T ∧
      (∀ j∈S,a ≤ r j) ∧ (∃ j∈S,r j=a) ∧
      (∀ j∈S,r j < b → lpRemaining p r b j=0) ∧
      (∀ t,a ≤ t → t < b → ∃ j∈S,lpRun p r t=some j) ∧
      ¬∃ j∈S,lpRun p r b=some j := by
  classical
  let a := S.inf' hS r
  have hamin (j) (hj : j∈S) : a ≤ r j := Finset.inf'_le r hj
  obtain ⟨j₀,hj₀,hja⟩ := Finset.exists_mem_eq_inf' hS r
  have hja : r j₀=a := hja.symm
  have haT : a < T := by
    obtain ⟨s,hr,hd,ht⟩ := hT
    have h1 := hr j₀
    have h2 := ht j₀
    have h3 : (0 : ℝ) < p j₀ := by exact_mod_cast hp j₀
    rw [hja] at h1
    exact_mod_cast (show (a : ℝ) < T by linarith)
  have hex : ∃ b : ℕ,a ≤ b ∧ ¬∃ j∈S,lpRun p r b=some j := by
    refine ⟨T,haT.le,?_⟩
    rintro ⟨j,hj,hrun⟩
    exact (run_lt p r T hT T j hrun).false
  let b := Nat.find hex
  have hb : a ≤ b ∧ ¬∃ j∈S,lpRun p r b=some j := Nat.find_spec hex
  have hbt : b ≤ T := Nat.find_min' hex ⟨haT.le,by rintro ⟨j,hj,hrun⟩;exact (run_lt p r T hT T j hrun).false⟩
  have hrem : lpRemaining p r a j₀=p j₀ := by
    have hh := served_before p r a j₀ (by omega)
    have hl := remaining_le p r a j₀
    dsimp [served] at hh
    omega
  have hab : a < b := by
    have ha := hwork a ⟨j₀,hj₀,by omega,by rw [hrem];exact hp j₀⟩
    by_contra hn
    have he : a=b := by omega
    rw [he] at ha
    exact hb.2 ha
  refine ⟨a,b,hab,hbt,hamin,⟨j₀,hj₀,hja⟩,?_,?_,hb.2⟩
  · intro j hj hr
    by_contra hn
    exact hb.2 (hwork b ⟨j,hj,hr.le,Nat.pos_of_ne_zero hn⟩)
  · intro t hat htb
    by_contra hn
    exact Nat.find_min hex htb ⟨hat,hn⟩

private theorem period_slot_sum {n : ℕ} (p r : Fin n → ℕ) (S : Finset (Fin n)) (a b : ℕ)
    (hmin : ∀ j∈S,a ≤ r j)
    (hdone : ∀ j∈S,r j < b → lpRemaining p r b j=0)
    (hbusy : ∀ t,a ≤ t → t < b → ∃ j∈S,lpRun p r t=some j) (t : ℕ) :
    (∑ j∈S.filter (fun j => r j < b),yLP p r j t)=if a ≤ t ∧ t < b then 1 else 0 := by
  classical
  by_cases ht : a ≤ t ∧ t < b
  · obtain ⟨j,hj,hr⟩ := hbusy t ht.1 ht.2
    have hj' : j∈S.filter (fun j => r j < b) := Finset.mem_filter.mpr ⟨hj,(run_spec p r t j hr).1.trans_lt ht.2⟩
    simp [yLP,hr,ht,eq_comm,hj']
  · have hn (j) (hj : j∈S.filter (fun j => r j < b)) : lpRun p r t ≠ some j := by
      intro hr
      have hs := run_spec p r t j hr
      have hm := hmin j (Finset.mem_filter.mp hj).1
      have htb : b ≤ t := by omega
      have hd := hdone j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
      have he := remaining_antitone p r j htb
      dsimp only at he
      omega
    rw [if_neg ht]
    exact Finset.sum_eq_zero (fun j hj => by simp [yLP,hn j hj])

private theorem interval_slots (a b T : ℕ) (hbT : b ≤ T) (f : ℕ → ℝ) :
    (∑ t∈Finset.range T,f t*(if a ≤ t ∧ t < b then 1 else 0))=∑ t∈Finset.Ico a b,f t := by
  classical
  simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
  omega

private theorem period_tight {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hp : ∀ j,0 < p j) (hT : IsMakespanBound p r T) (S : Finset (Fin n))
    (a b : ℕ) (hab : a < b) (hbT : b ≤ T) (hmin : ∀ j∈S,a ≤ r j)
    (hwit : ∃ j∈S,r j=a)
    (hslot : ∀ t,(∑ j∈S,yLP p r j t)=if a ≤ t ∧ t < b then 1 else 0) :
    ∀ hS : S.Nonempty,
      (∑ j∈S,(p j : ℝ)*mLP p r j)=SingleMachineSched.Shared.pSum p S*
        (SingleMachineSched.Shared.rmin r S hS+SingleMachineSched.Shared.pSum p S/2) := by
  intro hS
  have hpS : SingleMachineSched.Shared.pSum p S=(b : ℝ)-a := by
    calc
      SingleMachineSched.Shared.pSum p S=∑ j∈S,∑ t∈Finset.range T,yLP p r j t := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (feasible_row_total p r T _ (yLP_feasible p r T hT) j).symm
      _=∑ t∈Finset.range T,if a ≤ t ∧ t < b then (1 : ℝ) else 0 := by rw [Finset.sum_comm];simp only [hslot]
      _=∑ t∈Finset.Ico a b,(1 : ℝ) := by simpa using interval_slots a b T hbT (fun _ => 1)
      _=(b : ℝ)-a := by simp [Nat.cast_sub hab.le]
  have hrS : SingleMachineSched.Shared.rmin r S hS=(a : ℝ) := by
    change S.inf' hS (fun j => (r j : ℝ))=(a : ℝ)
    apply le_antisymm
    · obtain ⟨j,hj,hr⟩ := hwit
      calc
        S.inf' hS (fun j => (r j : ℝ)) ≤ (r j : ℝ) := Finset.inf'_le _ hj
        _=(a : ℝ) := by rw [hr]
    · apply Finset.le_inf'
      intro j hj
      exact_mod_cast hmin j hj
  calc
    (∑ j∈S,(p j : ℝ)*mLP p r j)=∑ t∈Finset.range T,((t : ℝ)+1/2)*(∑ j∈S,yLP p r j t) := by
      simp only [lp_moment p r T hp hT,Finset.mul_sum]
      rw [Finset.sum_comm]
    _=∑ t∈Finset.Ico a b,((t : ℝ)+1/2) := by simp only [hslot];exact interval_slots a b T hbT _
    _=_ := by rw [period_sum a b hab.le,hpS,hrS]

private theorem work_subset_bound {n : ℕ} (p r : Fin n → ℕ) (T : ℕ)
    (hp : ∀ j,0 < p j) (hT : IsMakespanBound p r T) (M : Fin n → ℝ)
    (hM : SingleMachineSched.Shared.FeasibleR p r M) (S : Finset (Fin n))
    (hwork : ∀ t,(∃ j∈S,r j ≤ t ∧ 0 < lpRemaining p r t j) → ∃ j∈S,lpRun p r t=some j) :
    (∑ j∈S,(p j : ℝ)*mLP p r j) ≤ ∑ j∈S,(p j : ℝ)*M j := by
  classical
  revert hwork
  refine Finset.strongInductionOn S ?_
  intro S ih hwork
  by_cases hS : S.Nonempty
  · obtain ⟨a,b,hab,hbT,hmin,hwit,hdone,hbusy,hidle⟩ := first_busy_period p r T hp hT S hS hwork
    let A := S.filter (fun j => r j < b)
    let B := S.filter (fun j => b ≤ r j)
    have hA : A.Nonempty := by
      obtain ⟨j,hj,hr⟩ := hwit
      exact ⟨j,Finset.mem_filter.mpr ⟨hj,by omega⟩⟩
    have hB : B ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _,?_⟩
      intro he
      obtain ⟨j,hj,hr⟩ := hwit
      have hh : j∈B := he.symm ▸ hj
      have hb := (Finset.mem_filter.mp hh).2
      omega
    have hwB : ∀ t,(∃ j∈B,r j ≤ t ∧ 0 < lpRemaining p r t j) → ∃ j∈B,lpRun p r t=some j := by
      intro t ht
      obtain ⟨j,hj,hrel,hrem⟩ := ht
      have hbt : b ≤ t := ((Finset.mem_filter.mp hj).2).trans hrel
      obtain ⟨k,hk,hrun⟩ := hwork t ⟨j,(Finset.mem_filter.mp hj).1,hrel,hrem⟩
      have hkr : b ≤ r k := by
        by_contra hn
        have hd := hdone k hk (by omega)
        have he := remaining_antitone p r k hbt
        have hr := (run_spec p r t k hrun).2.1
        dsimp only at he
        omega
      exact ⟨k,Finset.mem_filter.mpr ⟨hk,hkr⟩,hrun⟩
    have hsmall := ih B hB hwB
    have htight := period_tight p r T hp hT A a b hab hbT
      (fun j hj => hmin j (Finset.mem_filter.mp hj).1)
      (by obtain ⟨j,hj,hr⟩ := hwit;exact ⟨j,Finset.mem_filter.mpr ⟨hj,by omega⟩,hr⟩)
      (period_slot_sum p r S a b hmin hdone hbusy) hA
    have hlarge : (∑ j∈A,(p j : ℝ)*mLP p r j) ≤ ∑ j∈A,(p j : ℝ)*M j := by rw [htight];exact hM A hA
    have hsplit (f : Fin n → ℝ) : (∑ j∈A,f j)+(∑ j∈B,f j)=∑ j∈S,f j := by
      simpa [A,B,not_lt] using Finset.sum_filter_add_sum_filter_not S (fun j => r j < b) f
    rw [← hsplit (fun j => (p j : ℝ)*mLP p r j),← hsplit (fun j => (p j : ℝ)*M j)]
    exact add_le_add hlarge hsmall
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [he]

open MeasureTheory
private theorem bounded_integrable (A : Set ℝ) (hA : Bornology.IsBounded A) : IntegrableOn (fun t : ℝ => t) A :=
  (continuous_id.continuousOn.integrableOn_compact hA.isCompact_closure).mono_set subset_closure

private theorem interval_minimum (A : Set ℝ) (hA : MeasurableSet A)
    (hbound : Bornology.IsBounded A) (a p : ℝ) (hp : 0 ≤ p)
    (hsub : A ⊆ Ici a) (hvol : volume A=ENNReal.ofReal p) :
    p*(a+p/2) ≤ ∫ t in A,t ∧
      ((∫ t in A,t)=p*(a+p/2) ↔ A =ᵐ[volume] Ico a (a+p)) := by
  let d := a+p
  let J := Ico a d
  have had : a ≤ d := by dsimp [d];linarith
  have hJ : MeasurableSet J := measurableSet_Ico
  have hiA : IntegrableOn (fun t : ℝ => t) A := bounded_integrable A hbound
  have hiJ : IntegrableOn (fun t : ℝ => t) J := continuous_id.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hcA : IntegrableOn (fun _ : ℝ => d) A := integrableOn_const (by rw [hvol];finiteness)
  have hcJ : IntegrableOn (fun _ : ℝ => d) J := integrableOn_const (by dsimp [J];rw [Real.volume_Ico];exact ENNReal.ofReal_ne_top)
  have hvA : volume.real A=p := by simp [Measure.real,hvol,ENNReal.toReal_ofReal hp]
  have hvJ : volume.real J=p := by simp [Measure.real,J,d,Real.volume_Ico,ENNReal.toReal_ofReal hp]
  have hintJ : (∫ t in J,t)=p*(a+p/2) := by
    dsimp [J]
    rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le had,integral_id]
    dsimp [d]
    ring
  let f : ℝ → ℝ := J.indicator (fun t => t-d)
  let g : ℝ → ℝ := A.indicator (fun t => t-d)
  have hf : Integrable f := (hiJ.sub hcJ).integrable_indicator hJ
  have hg : Integrable g := (hiA.sub hcA).integrable_indicator hA
  have hfg (t : ℝ) : f t ≤ g t := by
    dsimp [f,g]
    by_cases htA : t∈A <;> by_cases htJ : t∈J
    · simp only [indicator_of_mem htA,indicator_of_mem htJ]
      exact le_rfl
    · simp only [indicator_of_mem htA,indicator_of_notMem htJ]
      have hta := hsub htA
      have htd : d ≤ t := le_of_not_gt (fun hh => htJ ⟨hta,hh⟩)
      linarith only [htd]
    · simp only [indicator_of_notMem htA,indicator_of_mem htJ]
      exact sub_nonpos.mpr htJ.2.le
    · simp only [indicator_of_notMem htA,indicator_of_notMem htJ,le_refl]
  have hfval : (∫ t,f t)=p*(a+p/2)-p*d := by
    rw [integral_indicator hJ,integral_sub hiJ hcJ,hintJ,setIntegral_const,hvJ,smul_eq_mul]
  have hgval : (∫ t,g t)=(∫ t in A,t)-p*d := by
    rw [integral_indicator hA,integral_sub hiA hcA,setIntegral_const,hvA,smul_eq_mul]
  have hineq := integral_mono hf hg hfg
  rw [hfval,hgval] at hineq
  refine ⟨by linarith only [hineq],?_⟩
  have hei : ((∫ t in A,t)=p*(a+p/2)) ↔ (∫ t,f t)=(∫ t,g t) := by rw [hfval,hgval];constructor <;> intro h <;> linarith only [h]
  rw [hei,integral_eq_iff_of_ae_le hf hg (Filter.Eventually.of_forall hfg)]
  constructor
  · intro he
    filter_upwards [he,volume.ae_ne d] with t ht hne
    apply propext
    change (t∈A ↔ t∈J)
    dsimp [f,g] at ht
    by_cases htA : t∈A <;> by_cases htJ : t∈J
    · exact iff_of_true htA htJ
    · simp only [indicator_of_mem htA,indicator_of_notMem htJ] at ht
      exact (hne (by linarith only [ht])).elim
    · simp only [indicator_of_notMem htA,indicator_of_mem htJ] at ht
      exact (hne (by linarith only [ht])).elim
    · exact iff_of_false htA htJ
  · intro he
    filter_upwards [he] with t ht
    change J.indicator (fun t : ℝ => t-d) t=A.indicator (fun t : ℝ => t-d) t
    by_cases htA : t∈A
    · have htJ : t∈J := ht.mp htA
      simp only [indicator_of_mem htA,indicator_of_mem htJ]
    · have htJ : t∉J := fun hj => htA (ht.mpr hj)
      simp only [indicator_of_notMem htA,indicator_of_notMem htJ]


private theorem schedule_subset {n : ℕ} (p r : Fin n → ℕ) (hp : ∀ j,0 < p j) (A : Fin n → Set ℝ)
    (hA : SingleMachineSched.Shared.IsPreemptiveSchedule p r A) (S : Finset (Fin n)) (hS : S.Nonempty) :
    SingleMachineSched.Shared.pSum p S*(SingleMachineSched.Shared.rmin r S hS+SingleMachineSched.Shared.pSum p S/2) ≤
        ∑ j ∈ S,(p j : ℝ)*SingleMachineSched.Shared.meanBusyTime p A j ∧
      ((∑ j ∈ S,(p j : ℝ)*SingleMachineSched.Shared.meanBusyTime p A j)=
          SingleMachineSched.Shared.pSum p S*(SingleMachineSched.Shared.rmin r S hS+SingleMachineSched.Shared.pSum p S/2) ↔
        (⋃ j ∈ S,A j) =ᵐ[volume] Ico (SingleMachineSched.Shared.rmin r S hS)
          (SingleMachineSched.Shared.rmin r S hS+SingleMachineSched.Shared.pSum p S)) := by
  let U := ⋃ j ∈ S,A j
  have hU : MeasurableSet U := MeasurableSet.biUnion S.finite_toSet.countable (fun j _ => hA.measurable j)
  have hUb : Bornology.IsBounded U := (Bornology.isBounded_biUnion_finset S).mpr (fun j _ => hA.bounded j)
  have hdis : (↑S : Set (Fin n)).PairwiseDisjoint A := fun i hi j hj hij => hA.disjoint hij
  have hUsub : U ⊆ Ici (SingleMachineSched.Shared.rmin r S hS) := by
    intro t ht
    obtain ⟨j,hj,htj⟩ := mem_iUnion₂.mp ht
    exact (Finset.inf'_le (fun j => (r j : ℝ)) hj).trans (hA.release j htj)
  have hvol : volume U=ENNReal.ofReal (SingleMachineSched.Shared.pSum p S) := by
    rw [measure_biUnion_finset hdis (fun j _ => hA.measurable j)]
    simp only [hA.volume_eq,SingleMachineSched.Shared.pSum]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Nat.cast_nonneg _)]
    simp
  have hint : (∫ t in U,t)=∑ j ∈ S,(p j : ℝ)*SingleMachineSched.Shared.meanBusyTime p A j := by
    rw [integral_biUnion_finset S (fun j _ => hA.measurable j) hdis (fun j _ => bounded_integrable _ (hA.bounded j))]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [SingleMachineSched.Shared.meanBusyTime]
    have hpj : (p j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hp j))
    field_simp
  have htot : 0 ≤ SingleMachineSched.Shared.pSum p S := Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
  simpa only [hint] using interval_minimum U hU hUb (SingleMachineSched.Shared.rmin r S hS) (SingleMachineSched.Shared.pSum p S) htot hUsub hvol

private theorem weighted_prefix {n : ℕ} (w a b : Fin n → ℝ)
    (hw : ∀ j,0 ≤ w j) (hmono : Antitone w)
    (hpre : ∀ k : Fin n,(∑ j∈Finset.univ.filter (fun j => j ≤ k),a j) ≤ ∑ j∈Finset.univ.filter (fun j => j ≤ k),b j) :
    (∑ j,w j*a j) ≤ ∑ j,w j*b j := by
  induction n with
  | zero => simp
  | succ n ih =>
    let v : Fin n → ℝ := fun j => w j.castSucc-w (Fin.last n)
    have hv (j : Fin n) : 0 ≤ v j := sub_nonneg.mpr (hmono (Fin.le_last _))
    have hvmono : Antitone v := fun i j hij => sub_le_sub_right (hmono (by exact_mod_cast hij)) _
    have hp (k : Fin n) :
        (∑ j∈Finset.univ.filter (fun j : Fin n => j ≤ k),a j.castSucc) ≤
          ∑ j∈Finset.univ.filter (fun j : Fin n => j ≤ k),b j.castSucc := by
      have hh := hpre k.castSucc
      simpa [Finset.sum_filter,Fin.sum_univ_castSucc] using hh
    have hi := ih v (fun j => a j.castSucc) (fun j => b j.castSucc) hv hvmono hp
    have htotal : (∑ j,a j) ≤ ∑ j,b j := by
      have hf : Finset.univ.filter (fun j : Fin (n+1) => j ≤ Fin.last n)=Finset.univ := Finset.filter_eq_self.mpr (fun j _ => Fin.le_last j)
      simpa only [hf] using hpre (Fin.last n)
    have hm := mul_le_mul_of_nonneg_left htotal (hw (Fin.last n))
    have hd (c : Fin (n+1) → ℝ) :
        (∑ j,w j*c j)=(∑ j : Fin n,v j*c j.castSucc)+w (Fin.last n)*(∑ j,c j) := by
      rw [Fin.sum_univ_castSucc (fun j => w j*c j),Fin.sum_univ_castSucc c]
      simp only [v,sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
      ring
    rw [hd a,hd b]
    exact add_le_add hi hm

private theorem lp_optimal_R {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j,0 < p j) (hw : ∀ j,0 ≤ w j)
    (hsort : ∀ j k : Fin n,j ≤ k → w k/p k ≤ w j/p j) :
    SingleMachineSched.Shared.FeasibleR p r (mLP p r) ∧
      ∀ M : Fin n → ℝ,SingleMachineSched.Shared.FeasibleR p r M →
        SingleMachineSched.Shared.objR p w (mLP p r) ≤ SingleMachineSched.Shared.objR p w M := by
  classical
  obtain ⟨T,hT⟩ := makespan_exists p r
  refine ⟨fun S hS => (schedule_subset p r hp (lpSet p r) (lp_schedule p r T hT) S hS).1,?_⟩
  intro M hM
  have hpre (k : Fin n) :
      (∑ j∈Finset.univ.filter (fun j => j ≤ k),(p j : ℝ)*mLP p r j) ≤
      ∑ j∈Finset.univ.filter (fun j => j ≤ k),(p j : ℝ)*M j := by
    apply work_subset_bound p r T hp hT M hM
    intro t ht
    obtain ⟨j,hj,hr,hrem⟩ := ht
    obtain ⟨i,hirun,hij⟩ := run_exists p r t j hr hrem
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij.trans (Finset.mem_filter.mp hj).2⟩,hirun⟩
  have hh := weighted_prefix (fun j => w j/p j) (fun j => (p j : ℝ)*mLP p r j) (fun j => (p j : ℝ)*M j)
    (fun j => div_nonneg (hw j) (Nat.cast_nonneg _)) hsort hpre
  have he (j : Fin n) (v : ℝ) : (w j/p j)*((p j : ℝ)*v)=w j*v := by
    have hj : (p j : ℝ) ≠ 0 := by exact_mod_cast (hp j).ne'
    field_simp
  simp only [he] at hh
  simp only [SingleMachineSched.Shared.objR,mul_add,Finset.sum_add_distrib]
  linarith

theorem solution {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j,0 < p j) (hw : ∀ j,0 ≤ w j)
    (hsort : ∀ j k : Fin n,j ≤ k → w k/p k ≤ w j/p j) :
    SingleMachineSched.Shared.FeasibleR p r (mLP p r) ∧
      ∀ M : Fin n → ℝ,SingleMachineSched.Shared.FeasibleR p r M →
        SingleMachineSched.Shared.objR p w (mLP p r) ≤ SingleMachineSched.Shared.objR p w M :=
  lp_optimal_R p r w hp hw hsort
