-- Prove2me | solution 1 for YoungConventions.Perturbed.markov_chain_tree_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:53:36.735265+00:00
-- url     : https://prove2.me/submissions/d77057f1-55e1-4bc9-87e7-8808eb84e2b9

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree

open Finset


namespace YoungConventions.Perturbed

theorem iter_update_reach_core {X : Type*} [DecidableEq X] (F : X → X) (r t : X) :
    ∀ n : ℕ, ∀ v, F^[n] v = r → ∃ m, (Function.update F r t)^[m] v = r := by
  intro n
  induction n with
  | zero => intro v hv; exact ⟨0, by simpa using hv⟩
  | succ n ih =>
    intro v hv
    by_cases h : v = r
    · exact ⟨0, by simpa using h⟩
    rw [Function.iterate_succ_apply] at hv
    obtain ⟨m, hm⟩ := ih (F v) hv
    refine ⟨m + 1, ?_⟩
    rw [Function.iterate_succ_apply, Function.update_of_ne h]
    exact hm

/-- `F` is a unicyclic map through `y`. -/
def IsUni {X : Type*} (y : X) (F : X → X) : Prop :=
  (∃ n, F^[n + 1] y = y) ∧ ∀ v, ∃ n, F^[n] v = y

theorem pred_unique_core {X : Type*} (F : X → X) (x y : X) (k : ℕ)
    (hFx : F x = y) (hk : F^[k] y = x) :
    x = F^[Function.minimalPeriod F y - 1] y := by
  have hper : Function.IsPeriodicPt F (k + 1) y := by
    show F^[k + 1] y = y
    rw [Function.iterate_succ_apply', hk, hFx]
  have hp := hper.minimalPeriod_pos (Nat.succ_pos k)
  obtain ⟨c, hc⟩ := hper.minimalPeriod_dvd
  set p := Function.minimalPeriod F y with hpdef
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h] at hc; omega
    · exact h
  have hkeq : k = (p - 1) + p * (c - 1) := by
    have : p * c = p * (c - 1) + p := by
      conv_lhs => rw [show c = (c - 1) + 1 by omega]
      ring
    omega
  have hmc : F^[p * (c - 1)] y = y := ((Function.isPeriodicPt_minimalPeriod F y).mul_const (c - 1)).eq
  rw [← hk, hkeq, Function.iterate_add_apply, hmc]

theorem tree_pos_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (hirr : A.IsIrreducible) (z : X) :
    ∃ T : X → X, IsInTree z T ∧ ∀ v, v ≠ z → 0 < A v (T v) := by
  classical
  have hnn : ∀ i j, 0 ≤ A i j := (Matrix.mem_rowStochastic_iff_sum.mp hA).1
  have hpnn : ∀ n : ℕ, ∀ i j, 0 ≤ (A ^ n) i j := fun n =>
    (Matrix.mem_rowStochastic_iff_sum.mp (pow_mem hA n)).1
  have hreach := (Matrix.isIrreducible_iff_exists_pow_pos hnn).mp hirr
  have hex : ∀ v, ∃ n, 0 < (A ^ n) v z := fun v => by
    obtain ⟨k, -, hk⟩ := hreach v z; exact ⟨k, hk⟩
  let d : X → ℕ := fun v => Nat.find (hex v)
  have hd : ∀ v, 0 < (A ^ d v) v z := fun v => Nat.find_spec (hex v)
  have hdmin : ∀ v n, 0 < (A ^ n) v z → d v ≤ n := fun v n h => Nat.find_min' (hex v) h
  have hstep : ∀ v, v ≠ z → ∃ u, 0 < A v u ∧ d u < d v := by
    intro v hv
    have h0 := hd v
    rcases Nat.eq_zero_or_pos (d v) with h | h
    · rw [h, pow_zero, Matrix.one_apply_ne hv] at h0; exact absurd h0 (lt_irrefl 0)
    obtain ⟨m, hm⟩ : ∃ m, d v = m + 1 := ⟨d v - 1, by omega⟩
    rw [hm, pow_succ', Matrix.mul_apply] at h0
    by_contra hcon
    push Not at hcon
    have : ∑ k, A v k * (A ^ m) k z ≤ 0 := by
      apply Finset.sum_nonpos
      intro k _
      by_contra hk
      push Not at hk
      have h1 : 0 < A v k := by
        rcases lt_or_eq_of_le (hnn v k) with h' | h'
        · exact h'
        · rw [← h'] at hk; simp at hk
      have h2 : 0 < (A ^ m) k z := by
        rcases lt_or_eq_of_le (hpnn m k z) with h' | h'
        · exact h'
        · rw [← h'] at hk; simp at hk
      have := hcon k h1
      have := hdmin k m h2
      omega
    linarith
  let T : X → X := fun v => if h : v = z then z else Classical.choose (hstep v h)
  have hTz : T z = z := by simp [T]
  have hTv : ∀ v, v ≠ z → 0 < A v (T v) ∧ d (T v) < d v := by
    intro v hv
    simp only [T, dif_neg hv]
    exact Classical.choose_spec (hstep v hv)
  refine ⟨T, ⟨hTz, ?_⟩, fun v hv => (hTv v hv).1⟩
  have key : ∀ n, ∀ v, d v ≤ n → ∃ m, T^[m] v = z := by
    intro n
    induction n with
    | zero =>
      intro v hv
      refine ⟨0, ?_⟩
      by_contra hne
      have := (hTv v hne).2
      omega
    | succ n ih =>
      intro v hv
      by_cases hvz : v = z
      · exact ⟨0, hvz⟩
      obtain ⟨m, hm⟩ := ih (T v) (by have := (hTv v hvz).2; omega)
      exact ⟨m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩
  intro v
  exact key (d v) v le_rfl

theorem treeWeight_pos_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (hirr : A.IsIrreducible) (z : X) : 0 < treeWeight A z := by
  classical
  have hnn : ∀ i j, 0 ≤ A i j := (Matrix.mem_rowStochastic_iff_sum.mp hA).1
  obtain ⟨T, hT, hpos⟩ := tree_pos_core A hA hirr z
  unfold treeWeight
  apply Finset.sum_pos'
  · intro T' _
    exact Finset.prod_nonneg (fun v _ => hnn _ _)
  · refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩, ?_⟩
    exact Finset.prod_pos (fun v hv => hpos v (Finset.ne_of_mem_erase hv))

open Classical in
theorem lhs_eq_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (y : X) :
    ∑ x, treeWeight A x * A x y =
      ∑ F ∈ (univ : Finset (X → X)).filter (fun F => IsUni y F), ∏ v, A v (F v) := by
  classical
  have h1 : ∑ x, treeWeight A x * A x y =
      ∑ p ∈ (univ : Finset (X × (X → X))).filter (fun p => IsInTree p.1 p.2),
        (∏ v ∈ univ.erase p.1, A v (p.2 v)) * A p.1 y := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    unfold treeWeight
    rw [Finset.sum_mul, Finset.sum_filter]
  rw [h1]
  apply Finset.sum_bij'
    (fun p _ => Function.update p.2 p.1 y)
    (fun F _ => (F^[Function.minimalPeriod F y - 1] y,
      Function.update F (F^[Function.minimalPeriod F y - 1] y) (F^[Function.minimalPeriod F y - 1] y)))
  · -- hi
    rintro ⟨x, T⟩ hp
    have hT : IsInTree x T := (Finset.mem_filter.mp hp).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hreach : ∀ v, ∃ m, (Function.update T x y)^[m] v = x := fun v => by
      obtain ⟨n, hn⟩ := hT.2 v
      exact iter_update_reach_core T x y n v hn
    refine ⟨?_, fun v => ?_⟩
    · obtain ⟨m, hm⟩ := hreach y
      exact ⟨m, by rw [Function.iterate_succ_apply', hm, Function.update_self]⟩
    · obtain ⟨m, hm⟩ := hreach v
      exact ⟨m + 1, by rw [Function.iterate_succ_apply', hm, Function.update_self]⟩
  · -- hj
    intro F hF
    have hU : IsUni y F := (Finset.mem_filter.mp hF).2
    set x := F^[Function.minimalPeriod F y - 1] y with hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    refine ⟨Function.update_self _ _ _, fun v => ?_⟩
    obtain ⟨n, hn⟩ := hU.2 v
    have : F^[(Function.minimalPeriod F y - 1) + n] v = x := by
      rw [Function.iterate_add_apply, hn]
    exact iter_update_reach_core F x x _ v this
  · -- left_inv
    rintro ⟨x, T⟩ hp
    have hT : IsInTree x T := (Finset.mem_filter.mp hp).2
    obtain ⟨n, hn⟩ := hT.2 y
    obtain ⟨m, hm⟩ := iter_update_reach_core T x y n y hn
    have hxe := pred_unique_core (Function.update T x y) x y m (Function.update_self _ _ _) hm
    simp only
    rw [← hxe]
    simp only [Function.update_idem, Prod.mk.injEq, true_and]
    exact Function.update_eq_self_iff.mpr hT.1.symm
  · -- right_inv
    intro F hF
    have hU : IsUni y F := (Finset.mem_filter.mp hF).2
    simp only [Function.update_idem]
    have hFx : F (F^[Function.minimalPeriod F y - 1] y) = y := by
      obtain ⟨n, hn⟩ := hU.1
      have hper : Function.IsPeriodicPt F (n + 1) y := hn
      have hp := hper.minimalPeriod_pos (Nat.succ_pos n)
      rw [← Function.iterate_succ_apply' F, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
      exact (Function.isPeriodicPt_minimalPeriod F y).eq
    exact Function.update_eq_self_iff.mpr hFx.symm
  · -- weights
    rintro ⟨x, T⟩ _
    simp only
    rw [← Finset.prod_erase_mul univ _ (Finset.mem_univ x), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

open Classical in
theorem rhs_eq_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (y : X) :
    ∑ x, treeWeight A y * A y x =
      ∑ F ∈ (univ : Finset (X → X)).filter (fun F => IsUni y F), ∏ v, A v (F v) := by
  classical
  have h1 : ∑ x, treeWeight A y * A y x =
      ∑ p ∈ (univ : Finset (X × (X → X))).filter (fun p => IsInTree y p.2),
        (∏ v ∈ univ.erase y, A v (p.2 v)) * A y p.1 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    unfold treeWeight
    rw [Finset.sum_mul, Finset.sum_filter]
  rw [h1]
  apply Finset.sum_bij'
    (fun (p : X × (X → X)) _ => Function.update p.2 y p.1)
    (fun (F : X → X) _ => (F y, Function.update F y y))
  · rintro ⟨x, T⟩ hp
    have hT : IsInTree y T := (Finset.mem_filter.mp hp).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hreach : ∀ v, ∃ m, (Function.update T y x)^[m] v = y := fun v => by
      obtain ⟨n, hn⟩ := hT.2 v
      exact iter_update_reach_core T y x n v hn
    refine ⟨?_, hreach⟩
    obtain ⟨m, hm⟩ := hreach x
    exact ⟨m, by rw [Function.iterate_succ_apply, Function.update_self, hm]⟩
  · intro F hF
    have hU : IsUni y F := (Finset.mem_filter.mp hF).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    refine ⟨Function.update_self _ _ _, fun v => ?_⟩
    obtain ⟨n, hn⟩ := hU.2 v
    exact iter_update_reach_core F y y n v hn
  · rintro ⟨x, T⟩ hp
    have hT : IsInTree y T := (Finset.mem_filter.mp hp).2
    simp only [Function.update_self, Function.update_idem, Prod.mk.injEq, true_and]
    exact Function.update_eq_self_iff.mpr hT.1.symm
  · intro F _
    simp only [Function.update_idem, Function.update_eq_self]
  · rintro ⟨x, T⟩ _
    simp only
    rw [← Finset.prod_erase_mul univ _ (Finset.mem_univ y), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

theorem mctf_core {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (hirr : A.IsIrreducible) :
    (∀ z, 0 < treeWeight A z) ∧
    IsStationaryDist A (fun z => treeWeight A z / ∑ x, treeWeight A x) ∧
    ∀ ν : X → ℝ, IsStationaryDist A ν → ν = fun z => treeWeight A z / ∑ x, treeWeight A x := by
  have hnn : ∀ i j, 0 ≤ A i j := (Matrix.mem_rowStochastic_iff_sum.mp hA).1
  have hrow : ∀ i, ∑ j, A i j = 1 := (Matrix.mem_rowStochastic_iff_sum.mp hA).2
  have hpos := treeWeight_pos_core A hA hirr
  set S := ∑ x, treeWeight A x with hS
  have hSpos : 0 < S := Finset.sum_pos (fun z _ => hpos z) Finset.univ_nonempty
  have hbal : ∀ y, ∑ x, treeWeight A x * A x y = treeWeight A y := by
    intro y
    rw [lhs_eq_core, ← rhs_eq_core, ← Finset.mul_sum, hrow, mul_one]
  have hstat : IsStationaryDist A (fun z => treeWeight A z / S) := by
    refine ⟨fun z => (div_pos (hpos z) hSpos).le, ?_, fun y => ?_⟩
    · rw [← Finset.sum_div, div_self hSpos.ne']
    · simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div, hbal]
  refine ⟨hpos, hstat, ?_⟩
  intro ν hν
  obtain ⟨hν0, hν1, hνA⟩ := hν
  set μ : X → ℝ := fun z => treeWeight A z / S with hμ
  have hμpos : ∀ z, 0 < μ z := fun z => div_pos (hpos z) hSpos
  obtain ⟨z0, -, hz0⟩ := Finset.exists_min_image univ (fun z => ν z / μ z) Finset.univ_nonempty
  set t := ν z0 / μ z0 with ht
  let w : X → ℝ := fun z => ν z - t * μ z
  have hw0 : ∀ z, 0 ≤ w z := by
    intro z
    have := hz0 z (Finset.mem_univ _)
    rw [le_div_iff₀ (hμpos z)] at this
    simp only [w]; linarith
  have hwz0 : w z0 = 0 := by
    simp only [w, ht]; field_simp [(hμpos z0).ne']; ring
  have hwA : Matrix.vecMul w A = w := by
    funext y
    simp only [Matrix.vecMul, dotProduct, w, sub_mul, Finset.sum_sub_distrib, mul_assoc]
    rw [← Finset.mul_sum, hνA y]
    have := hstat.2.2 y
    rw [this]
  have hwn : ∀ n : ℕ, Matrix.vecMul w (A ^ n) = w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hwA]
  have hpnn : ∀ n : ℕ, ∀ i j, 0 ≤ (A ^ n) i j := fun n =>
    (Matrix.mem_rowStochastic_iff_sum.mp (pow_mem hA n)).1
  have hreach := (Matrix.isIrreducible_iff_exists_pow_pos hnn).mp hirr
  have hwall : ∀ x, w x = 0 := by
    intro x
    obtain ⟨k, -, hk⟩ := hreach x z0
    have h := congrFun (hwn k) z0
    simp only [Matrix.vecMul, dotProduct] at h
    rw [hwz0] at h
    have hle : w x * (A ^ k) x z0 ≤ ∑ x', w x' * (A ^ k) x' z0 :=
      Finset.single_le_sum (f := fun x' => w x' * (A ^ k) x' z0)
        (fun x' _ => mul_nonneg (hw0 x') (hpnn k x' z0)) (Finset.mem_univ x)
    rw [h] at hle
    have := mul_nonneg (hw0 x) (hpnn k x z0)
    have h0 : w x * (A ^ k) x z0 = 0 := le_antisymm hle this
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact h'
    · linarith
  have hνeq : ∀ z, ν z = t * μ z := fun z => by
    have := hwall z; simp only [w] at this; linarith
  have ht1 : t = 1 := by
    have h1 : ∑ z, ν z = t * ∑ z, μ z := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => hνeq z)
    rw [hν1, hstat.2.1, mul_one] at h1
    exact h1.symm
  funext z
  rw [hνeq z, ht1, one_mul]

end YoungConventions.Perturbed

open YoungConventions.Perturbed


theorem solution {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (hirr : A.IsIrreducible) (hap : IsAperiodic A) :
    (∀ z, 0 < treeWeight A z) ∧
    IsStationaryDist A (fun z => treeWeight A z / ∑ x, treeWeight A x) ∧
    ∀ ν : X → ℝ, IsStationaryDist A ν → ν = fun z => treeWeight A z / ∑ x, treeWeight A x := by
  exact mctf_core A hA hirr
