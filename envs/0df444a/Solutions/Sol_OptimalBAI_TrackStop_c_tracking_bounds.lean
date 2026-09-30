-- Prove2me | solution 1 for OptimalBAI.TrackStop.c_tracking_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:08:31.213472+00:00
-- url     : https://prove2.me/submissions/b79181f4-ce0e-48e3-b41f-ee2a40ee2dfb

import Definitions.Def_OptimalBAI_TrackStop_Tracking
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

open scoped BigOperators
open BanditAlgorithm OptimalBAI.TrackStop

private theorem cumulative_tracking {K : ℕ} (hK : 0 < K) (n : ℕ) (hn : 0 < n)
    (p : ℕ → Fin K → ℝ)
    (hp : ∀ k, 1 ≤ k → k ≤ n → (∀ a, 0 ≤ p k a) ∧ ∑ a, p k a = 1)
    (N : ℕ → Fin K → ℝ) (I : ℕ → Fin K)
    (hN0 : N 0 = 0)
    (hI : ∀ k, k < n → ∀ i : Fin K,
      (∑ j ∈ Finset.Icc 1 (k + 1), p j i) - N k i ≤
        (∑ j ∈ Finset.Icc 1 (k + 1), p j (I (k + 1))) - N k (I (k + 1)))
    (hN : ∀ k, k < n → N (k + 1) = N k + Pi.single (I (k + 1)) (1 : ℝ)) :
    ∀ i : Fin K, |N n i - ∑ j ∈ Finset.Icc 1 n, p j i| ≤ (K : ℝ) - 1 := by
  let P : ℕ → Fin K → ℝ := fun k i => ∑ j ∈ Finset.Icc 1 k, p j i
  have hP0 : ∀ i, P 0 i = 0 := by simp [P]
  have hPstep : ∀ k i, P (k+1) i = P k i + p (k+1) i := by
    intro k i
    dsimp [P]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1)]
  have hPsum : ∀ k, k ≤ n → ∑ i, P k i = (k : ℝ) := by
    intro k
    induction k with
    | zero => simp [P]
    | succ k ih =>
      intro hk
      simp_rw [hPstep]
      rw [Finset.sum_add_distrib, ih (by omega), (hp (k+1) (by omega) hk).2]
      simp
  have hNsum : ∀ k, k ≤ n → ∑ i, N k i = (k : ℝ) := by
    intro k
    induction k with
    | zero => simp [hN0]
    | succ k ih =>
      intro hk
      rw [hN k (by omega)]
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      rw [ih (by omega)]
      simp
  have hu : ∀ k, k ≤ n → ∀ i, N k i - P k i ≤ 1 := by
    intro k
    induction k with
    | zero => simp [hN0, hP0]
    | succ k ih =>
      intro hk i
      have hk' : k < n := by omega
      have hs : ∑ a, (P (k+1) a - N k a) = 1 := by
        rw [Finset.sum_sub_distrib, hPsum (k+1) hk, hNsum k (by omega)]
        push_cast
        ring
      have hbest : 0 ≤ P (k+1) (I (k+1)) - N k (I (k+1)) := by
        by_contra hh
        have hneg : P (k+1) (I (k+1)) - N k (I (k+1)) < 0 := lt_of_not_ge hh
        have hall : ∑ a, (P (k+1) a - N k a) ≤ 0 :=
          Finset.sum_nonpos (fun a _ => (hI k hk' a).trans hneg.le)
        linarith
      by_cases hi : i = I (k+1)
      · subst i
        rw [hN k hk']
        simp only [Pi.add_apply, Pi.single_eq_same]
        linarith
      · have hprev := ih (by omega) i
        have hpi := (hp (k+1) (by omega) hk).1 i
        rw [hN k hk', hPstep]
        simp only [Pi.add_apply, Pi.single_apply, if_neg hi, add_zero]
        linarith
  have hz : ∑ i, (N n i - P n i) = 0 := by
    rw [Finset.sum_sub_distrib, hNsum n le_rfl, hPsum n le_rfl, sub_self]
  intro i
  have hlow : -((K : ℝ)-1) ≤ N n i - P n i := by
    have he := Finset.sum_erase_add Finset.univ (fun a => N n a - P n a)
      (Finset.mem_univ i)
    have hbound : ∑ a ∈ Finset.univ.erase i, (N n a - P n a) ≤
        ∑ _a ∈ Finset.univ.erase i, (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ => hu n le_rfl a)
    have hc : (∑ _a ∈ Finset.univ.erase i, (1 : ℝ)) = (K : ℝ)-1 := by
      simp [Finset.card_erase_of_mem, Nat.cast_sub (Nat.succ_le_of_lt hK)]
    rw [hc] at hbound
    rw [hz] at he
    linarith
  have hu' : N n i - P n i ≤ (K : ℝ)-1 := by
    by_cases hK1 : K = 1
    · subst K
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using le_of_eq hz
    · have hk2 : (2 : ℝ) ≤ K := by exact_mod_cast (show 2 ≤ K by omega)
      linarith [hu n le_rfl i]
  exact abs_le.mpr ⟨hlow, hu'⟩

private theorem eps_bounds {K : ℕ} (hK : 0 < K) (s : ℕ) :
    0 < cEps K s ∧ cEps K s ≤ 1/(K:ℝ) ∧
    Real.sqrt ((K:ℝ)^2+(s:ℝ)+1)-Real.sqrt ((K:ℝ)^2+(s:ℝ)) ≤ cEps K s ∧
    cEps K s ≤ Real.sqrt ((s:ℝ)+1)-Real.sqrt (s:ℝ) := by
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0:ℝ) < K := by positivity
  have hs : (0:ℝ) ≤ s := by positivity
  have hsq : (0:ℝ) < (K:ℝ)^2+(s:ℝ) := by positivity
  have hr : 0 < Real.sqrt ((K:ℝ)^2+(s:ℝ)) := Real.sqrt_pos.mpr hsq
  have hr2 := Real.sq_sqrt hsq.le
  have hn2 := Real.sq_sqrt (show 0 ≤ (K:ℝ)^2+(s:ℝ)+1 by positivity)
  have hs2 := Real.sq_sqrt hs
  have hs12 := Real.sq_sqrt (show 0 ≤ (s:ℝ)+1 by positivity)
  have hrK : (K:ℝ) ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)) := by nlinarith
  have hmon : Real.sqrt ((K:ℝ)^2+(s:ℝ)) ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)+1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hdiff : 0 ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)+1)-Real.sqrt ((K:ℝ)^2+(s:ℝ)) := sub_nonneg.mpr hmon
  have hdiff2 : 0 ≤ Real.sqrt ((s:ℝ)+1)-Real.sqrt (s:ℝ) := sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hsup1 : Real.sqrt ((s:ℝ)+1) ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)) := Real.sqrt_le_sqrt (by nlinarith)
  have hsup0 : Real.sqrt (s:ℝ) ≤ Real.sqrt ((K:ℝ)^2+(s:ℝ)) := Real.sqrt_le_sqrt (by nlinarith)
  dsimp [cEps]
  refine ⟨by positivity,?_,?_,?_⟩
  · apply (one_div_le_one_div (by positivity) hKpos).2
    linarith
  · apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt ((K:ℝ)^2+(s:ℝ)))).mpr
    nlinarith [mul_nonneg hdiff hdiff]
  · apply (div_le_iff₀ (by positivity : 0 < 2*Real.sqrt ((K:ℝ)^2+(s:ℝ)))).mpr
    nlinarith [mul_nonneg hdiff2 (sub_nonneg.mpr hsup1),mul_nonneg hdiff2 (sub_nonneg.mpr hsup0)]

private theorem eps_sums {K : ℕ} (hK : 0 < K) (t : ℕ) :
    Real.sqrt ((K:ℝ)^2+(t:ℝ))-(K:ℝ) ≤ ∑ s ∈ Finset.range t,cEps K s ∧
    ∑ s ∈ Finset.range t,cEps K s ≤ Real.sqrt (t:ℝ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he := eps_bounds hK t
    rw [Finset.sum_range_succ]
    push_cast
    simp only [← add_assoc]
    constructor <;> linarith [he.2.2.1,he.2.2.2]

private theorem projection_distance {K : ℕ} (hK : 0 < K)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ μ,wt μ ∈ simplex K)
    (wp : ℝ → (Fin K → ℝ) → Fin K → ℝ) (hp : IsLinftyProjection K wt wp)
    (ε : ℝ) (he : 0 < ε) (heK : ε ≤ 1/(K:ℝ)) (μ : Fin K → ℝ) (a : Fin K) :
    |wp ε μ a-wt μ a| ≤ (K:ℝ)*ε := by
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0:ℝ) < K := by positivity
  have hKe : (K:ℝ)*ε ≤ 1 := by nlinarith [(le_div_iff₀ hKpos).mp heK]
  have hcoef : 0 ≤ 1-(K:ℝ)*ε := by linarith
  have hw : (∀ a,0 ≤ wt μ a) ∧ ∑ a,wt μ a=1 := hwt μ
  have hw1 (a : Fin K) : wt μ a ≤ 1 := by
    rw [← hw.2]
    exact Finset.single_le_sum (fun b _ => hw.1 b) (Finset.mem_univ a)
  let v : Fin K → ℝ := fun b => (1-(K:ℝ)*ε)*wt μ b+ε
  have hv : v ∈ simplexEps K ε := by
    constructor
    · intro b
      dsimp [v]
      constructor
      · nlinarith [mul_nonneg hcoef (hw.1 b)]
      · nlinarith [mul_le_mul_of_nonneg_left (hw1 b) hcoef]
    · simp [v,Finset.sum_add_distrib,← Finset.mul_sum,hw.2]
  have hnorm : ‖v-wt μ‖ ≤ (K:ℝ)*ε := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro b
    simp only [Pi.sub_apply,Real.norm_eq_abs]
    rw [abs_le]
    dsimp [v]
    have hh := mul_le_mul_of_nonneg_left (hw1 b) (by positivity : 0 ≤ (K:ℝ)*ε)
    have hn := mul_nonneg (show 0 ≤ (K:ℝ)*ε by positivity) (hw.1 b)
    have heK1 := mul_le_mul_of_nonneg_right hKr he.le
    constructor <;> nlinarith
  have hpdist := le_trans ((hp ε he heK μ).2 v hv) hnorm
  exact (pi_norm_le_iff_of_nonneg (by positivity)).mp hpdist a

private theorem prefix_count {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    armPullCount a (banditTrajPrefix K t ω) = trajPullCount a t ω := by
  classical
  unfold armPullCount
  rw [Set.toFinset_ofPred,Finset.card_filter]
  unfold trajPullCount
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then 1 else 0) t

private theorem prefix_mean {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    armEmpiricalMean a (banditTrajPrefix K t ω) = trajEmpiricalMean a t ω := by
  classical
  unfold armEmpiricalMean
  rw [Set.toFinset_ofPred,Finset.sum_filter,prefix_count]
  unfold trajEmpiricalMean
  rw [Finset.sum_filter]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then (ω i).2 else 0) t

private theorem hist_mean_prefix {K : ℕ} (ω : ℕ → Fin K × ℝ) (t s : ℕ) (hs : s ≤ t) :
    histMeanAt (banditTrajPrefix K t ω) s = trajMeanVec s ω := by
  ext a
  dsimp [histMeanAt,trajMeanVec]
  have he : (fun i : Fin (min s t) => banditTrajPrefix K t ω (Fin.castLE (Nat.min_le_right s t) i)) = banditTrajPrefix K (min s t) ω := rfl
  rw [he,prefix_mean,Nat.min_eq_left hs]

private theorem count_step {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) (a : Fin K) :
    (trajPullCount a (t+1) ω : ℝ) = (trajPullCount a t ω : ℝ) + if a=(ω t).1 then 1 else 0 := by
  simp only [trajPullCount,Finset.range_add_one,Finset.filter_insert]
  by_cases ha : a=(ω t).1
  · simp [ha,Finset.mem_filter,Finset.mem_range]
  · simp [ha,Ne.symm ha]

private theorem shifted_sum (p : ℕ → ℝ) (t : ℕ) :
    ∑ j ∈ Finset.Icc 1 t,p (j-1) = ∑ j ∈ Finset.range t,p j := by
  rw [← Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp

theorem solution {K : ℕ} (wt : (Fin K → ℝ) → (Fin K → ℝ))
    (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsCTracking wt ω) :
    ∀ t : ℕ, 1 ≤ t → ∀ a : Fin K,
      Real.sqrt ((t : ℝ) + (K : ℝ) ^ 2) - 2 * (K : ℝ) ≤ (trajPullCount a t ω : ℝ) ∧
      |(trajPullCount a t ω : ℝ) - ∑ s ∈ Finset.range t, wt (trajMeanVec s ω) a| ≤
        (K : ℝ) * (1 + Real.sqrt (t : ℝ)) := by
  classical
  obtain ⟨wp,hwp,hsel⟩ := hω
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) (ω 0).1.isLt
  have hpt : ∀ j, wp (cEps K j) (trajMeanVec j ω) ∈ simplexEps K (cEps K j) := by
    intro j
    exact (hwp _ (eps_bounds hK j).1 (eps_bounds hK j).2.1 _).1
  intro t ht a
  have hc := cumulative_tracking hK t ht
    (fun j => wp (cEps K (j-1)) (trajMeanVec (j-1) ω))
    (fun j _ _ => ⟨fun b => le_trans (eps_bounds hK (j-1)).1.le ((hpt (j-1)).1 b).1,(hpt (j-1)).2⟩)
    (fun k b => (trajPullCount b k ω : ℝ)) (fun j => (ω (j-1)).1)
    (by ext b; simp [trajPullCount]) ?_ ?_ a
  · rw [shifted_sum (fun j => wp (cEps K j) (trajMeanVec j ω) a)] at hc
    have hlp : ∑ s ∈ Finset.range t,cEps K s ≤
        ∑ s ∈ Finset.range t,wp (cEps K s) (trajMeanVec s ω) a := by
      apply Finset.sum_le_sum
      intro s _
      exact ((hpt s).1 a).1
    have hd : |(∑ s ∈ Finset.range t,wp (cEps K s) (trajMeanVec s ω) a)-
        ∑ s ∈ Finset.range t,wt (trajMeanVec s ω) a| ≤ (K:ℝ)*Real.sqrt (t:ℝ) := by
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ s ∈ Finset.range t,|wp (cEps K s) (trajMeanVec s ω) a-wt (trajMeanVec s ω) a| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s ∈ Finset.range t,(K:ℝ)*cEps K s := by
          apply Finset.sum_le_sum
          intro s _
          exact projection_distance hK wt hwt_simplex wp hwp _ (eps_bounds hK s).1 (eps_bounds hK s).2.1 _ a
        _ ≤ (K:ℝ)*Real.sqrt (t:ℝ) := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (eps_sums hK t).2 (by positivity)
    constructor
    · have he := (eps_sums hK t).1
      rw [add_comm ((K:ℝ)^2) (t:ℝ)] at he
      have hh := (abs_le.mp hc).1
      linarith
    · have hh := abs_add_le ((trajPullCount a t ω : ℝ)-∑ s ∈ Finset.range t,wp (cEps K s) (trajMeanVec s ω) a)
        ((∑ s ∈ Finset.range t,wp (cEps K s) (trajMeanVec s ω) a)-∑ s ∈ Finset.range t,wt (trajMeanVec s ω) a)
      simp only [sub_add_sub_cancel] at hh
      linarith
  · intro k hk b
    have htar (b : Fin K) : cTarget wp (banditTrajPrefix K k ω) b =
        ∑ s ∈ Finset.range (k+1),wp (cEps K s) (trajMeanVec s ω) b := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hist_mean_prefix ω k s (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hs)]
    have hh := hsel k b
    change cTarget wp (banditTrajPrefix K k ω) b-(armPullCount b (banditTrajPrefix K k ω):ℝ) ≤
      cTarget wp (banditTrajPrefix K k ω) (ω k).1-(armPullCount (ω k).1 (banditTrajPrefix K k ω):ℝ) at hh
    rw [htar,htar,prefix_count,prefix_count] at hh
    simp only [Nat.add_sub_cancel]
    rw [shifted_sum (fun j => wp (cEps K j) (trajMeanVec j ω) b),
      shifted_sum (fun j => wp (cEps K j) (trajMeanVec j ω) (ω k).1)]
    exact hh
  · intro k hk
    ext b
    simp only [Pi.add_apply,Nat.add_sub_cancel,Pi.single_apply]
    simpa [eq_comm] using count_step ω k b

