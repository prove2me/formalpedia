-- Prove2me | solution 1 for OptimalBAI.TrackStop.d_tracking_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:51:06.185003+00:00
-- url     : https://prove2.me/submissions/fc848517-a37c-4820-ab51-0a5501c47bf8

import Definitions.Def_OptimalBAI_TrackStop_Tracking
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open scoped BigOperators
open BanditAlgorithm OptimalBAI.TrackStop
namespace DTrackProof
private theorem forced_lower {K : ℕ} (hK : 2 ≤ K) (N : ℕ → Fin K → ℕ) (I : ℕ → Fin K)
    (hstep : ∀ t a, N (t+1) a = N t a + if a = I t then 1 else 0)
    (hsel : ∀ (t : ℕ) a, (N t a : ℝ) < Real.sqrt (t : ℝ) - (K : ℝ)/2 → N t (I t) ≤ N t a) :
    ∀ (t : ℕ) a, max (Real.sqrt (t : ℝ)-(K : ℝ)/2) 0 - 1 ≤ (N t a : ℝ) := by
  classical
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hmono : ∀ a, Monotone (fun t => N t a) := fun a => monotone_nat_of_le_succ fun t => by
    rw [hstep]; omega
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro a
    by_contra! hbad
    let q := N t a
    have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
    have hbad' : (q : ℝ)+1 < Real.sqrt (t : ℝ)-(K : ℝ)/2 := by
      have hmax := (lt_max_iff.mp (show (q : ℝ)+1 < max (Real.sqrt (t : ℝ)-(K : ℝ)/2) 0 by linarith))
      rcases hmax with ht | ht
      · exact ht
      · linarith
    have hsqt := Real.sq_sqrt (Nat.cast_nonneg t)
    have htK : K ≤ t := by
      have : (K : ℝ) < t := by nlinarith [sq_nonneg ((K : ℝ)/2)]
      exact_mod_cast this.le
    let u := t-K
    have hu : u < t := by dsimp [u]; omega
    have hu_cast : (u : ℝ) = (t : ℝ)-(K : ℝ) := by dsimp [u]; exact Nat.cast_sub htK
    have hsqu := Real.sq_sqrt (Nat.cast_nonneg u)
    have hsqrt : Real.sqrt (t : ℝ)-1 < Real.sqrt (u : ℝ) := by
      apply (sq_lt_sq₀ (by linarith : 0 ≤ Real.sqrt (t : ℝ)-1) (Real.sqrt_nonneg _)).mp
      rw [hsqu, hu_cast]
      nlinarith
    have huq : (q : ℝ) < Real.sqrt (u : ℝ)-(K : ℝ)/2 := by linarith
    have hbase : ∀ b, q ≤ N u b := by
      intro b
      have hh := ih u hu b
      have hm := le_max_left (Real.sqrt (u : ℝ)-(K : ℝ)/2) 0
      have hc : (q : ℝ) < (N u b : ℝ)+1 := by linarith
      have hc' : q < N u b+1 := by exact_mod_cast hc
      omega
    have hchoose : ∀ j, u ≤ j → j < t → N j (I j) = q := by
      intro j hj hjt
      have hja : N j a ≤ q := hmono a hjt.le
      have ht : (N j a : ℝ) < Real.sqrt (j : ℝ)-(K : ℝ)/2 := by
        have hsj := Real.sqrt_le_sqrt (show (u : ℝ) ≤ j by exact_mod_cast hj)
        have hjr : (N j a : ℝ) ≤ q := by exact_mod_cast hja
        linarith
      exact le_antisymm ((hsel j a ht).trans hja) ((hbase (I j)).trans (hmono (I j) hj))
    let S : ℕ → ℕ := fun j => ∑ b, min (N j b) (q+1)
    have hSstep : ∀ j, u ≤ j → j < t → S (j+1) = S j+1 := by
      intro j hj hjt
      have he : ∀ b, min (N (j+1) b) (q+1) = min (N j b) (q+1) + if b = I j then 1 else 0 := by
        intro b
        rw [hstep]
        by_cases hb : b = I j
        · subst b; rw [hchoose j hj hjt]; simp
        · simp [hb]
      dsimp only [S]
      simp_rw [he]
      rw [Finset.sum_add_distrib]
      simp
    have hSeq : ∀ j, u ≤ j → j ≤ t → S j = S u+(j-u) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => simp
      | succ j hj ih =>
        intro hjt
        rw [hSstep j hj (by omega), ih (by omega)]
        omega
    have hSlower : K*q ≤ S u := by
      calc K*q = ∑ _b : Fin K, q := by simp
           _ ≤ S u := Finset.sum_le_sum (fun b _ => le_min (hbase b) (by omega))
    have hSupper : S t < K*(q+1) := by
      calc S t < ∑ _b : Fin K, (q+1) := by
             dsimp only [S]
             apply Finset.sum_lt_sum (fun b _ => min_le_right _ _)
             refine ⟨a, Finset.mem_univ a, ?_⟩
             dsimp only [q]; omega
           _ = K*(q+1) := by simp
    have htS := hSeq t (by dsimp [u]; omega) le_rfl
    have htu : t-u = K := by dsimp [u]; omega
    rw [htu] at htS
    nlinarith
private theorem sqrt_small (ε : ℝ) (hε : 0 < ε) (T : ℕ) (hT : 1/ε^2 ≤ (T : ℝ))
    (t : ℕ) (ht : T ≤ t) : Real.sqrt (t : ℝ) ≤ ε*(t : ℝ) := by
  have he : ε^2 ≠ 0 := pow_ne_zero _ hε.ne'
  have hmul : 1 ≤ ε^2*(t : ℝ) := by
    have hh : 1/ε^2 ≤ (t : ℝ) := hT.trans (by exact_mod_cast ht)
    exact (div_le_iff₀ (sq_pos_of_pos hε)).mp hh |>.trans_eq (mul_comm _ _)
  have hs := Real.sq_sqrt (Nat.cast_nonneg t)
  have heq : (ε*Real.sqrt (t : ℝ))^2 = ε^2*(t : ℝ) := by rw [mul_pow, hs]
  have h1 : 1 ≤ ε*Real.sqrt (t : ℝ) := by
    have hn : 0 ≤ ε*Real.sqrt (t : ℝ) := by positivity
    nlinarith
  have hh := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (t : ℝ))
  nlinarith
private theorem tracking_upper {K : ℕ} (N : ℕ → Fin K → ℕ) (I : ℕ → Fin K)
    (hstep : ∀ t a, N (t+1) a = N t a + if a = I t then 1 else 0)
    (hsum : ∀ t, ∑ a, N t a = t)
    (w : Fin K → ℝ) (hw : ∀ a, 0 ≤ w a) (ε : ℝ) (hε : 0 < ε)
    (T : ℕ) (hT : 1 ≤ T)
    (hsel : ∀ t, T ≤ t → (N t (I t) : ℝ) ≤ (t : ℝ)*(w (I t)+ε)) :
    ∀ t, T ≤ t → ∀ a, (N t a : ℝ) ≤ (t : ℝ)*(w a+ε)+(T : ℝ) := by
  classical
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro a
    have ha : N T a ≤ T := (Finset.single_le_sum (fun b _ => Nat.zero_le (N T b)) (Finset.mem_univ a)).trans_eq (hsum T)
    have har : (N T a : ℝ) ≤ T := by exact_mod_cast ha
    have hh : 0 ≤ (T : ℝ)*(w a+ε) := mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hw a) hε.le)
    linarith
  | succ t ht ih =>
    intro a
    rw [hstep]
    by_cases ha : a = I t
    · subst a; rw [if_pos rfl, Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
      have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
      nlinarith [hsel t ht, hw (I t)]
    · rw [if_neg ha, add_zero, Nat.cast_add, Nat.cast_one]
      nlinarith [ih a, hw a]
private theorem simplex_error {K : ℕ} (hK : 2 ≤ K) (v w : Fin K → ℝ)
    (hs : ∑ a, v a = ∑ a, w a) (ε : ℝ) (hε : 0 < ε)
    (hu : ∀ a, v a-w a ≤ 2*ε) : ∀ a, |v a-w a| ≤ 3*((K : ℝ)-1)*ε := by
  classical
  have hsum : ∑ a, (v a-w a) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  intro a
  have he := Finset.sum_erase_add Finset.univ (fun b => v b-w b) (Finset.mem_univ a)
  have hb : ∑ b ∈ Finset.univ.erase a, (v b-w b) ≤ ∑ _b ∈ Finset.univ.erase a, 2*ε :=
    Finset.sum_le_sum fun b _ => hu b
  have hc : (∑ _b ∈ Finset.univ.erase a, 2*ε) = ((K : ℝ)-1)*(2*ε) := by
    simp [Finset.card_erase_of_mem, Nat.cast_sub (by omega : 1 ≤ K)]
  rw [hc] at hb
  rw [hsum] at he
  apply abs_le.mpr
  constructor <;> nlinarith [hu a, mul_nonneg (by linarith : 0 ≤ (K : ℝ)-1) hε.le]

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
    trajPullCount a (t+1) ω = trajPullCount a t ω + if a=(ω t).1 then 1 else 0 := by
  simp only [trajPullCount,Finset.range_add_one,Finset.filter_insert]
  by_cases ha : a=(ω t).1
  · simp [ha,Finset.mem_filter,Finset.mem_range]
  · simp [ha,Ne.symm ha]


private theorem count_sum {K : ℕ} (ω : ℕ → Fin K × ℝ) (t : ℕ) :
    ∑ a, trajPullCount a t ω = t := by
  induction t with
  | zero => simp [trajPullCount]
  | succ t ih => simp_rw [count_step]; rw [Finset.sum_add_distrib, ih]; simp
private theorem forced_choice {K : ℕ} (wt : (Fin K → ℝ) → Fin K → ℝ)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsDTracking wt ω) (t : ℕ) (a : Fin K)
    (ha : (trajPullCount a t ω : ℝ) < Real.sqrt (t : ℝ)-(K : ℝ)/2) :
    trajPullCount (ω t).1 t ω ≤ trajPullCount a t ω := by
  have ham : a ∈ forcedSet (banditTrajPrefix K t ω) := by
    change (armPullCount a (banditTrajPrefix K t ω) : ℝ) < _
    simpa only [prefix_count] using ha
  rcases hω t with ⟨_, _, hmin⟩ | ⟨hem, _⟩
  · simpa only [prefix_count] using hmin a ham
  · rw [hem] at ham; exact False.elim ham
private theorem chosen_upper {K : ℕ} (wt : (Fin K → ℝ) → Fin K → ℝ)
    (hwt : ∀ μ, wt μ ∈ simplex K)
    (ω : ℕ → Fin K × ℝ) (hω : FollowsDTracking wt ω) (t : ℕ) :
    (trajPullCount (ω t).1 t ω : ℝ) ≤ max (Real.sqrt (t : ℝ)) ((t : ℝ)*wt (trajMeanVec t ω) (ω t).1) := by
  rcases hω t with ⟨_, hmem, _⟩ | ⟨_, hmax⟩
  · change (armPullCount (ω t).1 (banditTrajPrefix K t ω) : ℝ) < _ at hmem
    rw [prefix_count] at hmem
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    exact (by linarith : (trajPullCount (ω t).1 t ω : ℝ) ≤ Real.sqrt (t : ℝ)).trans (le_max_left _ _)
  · simp only [prefix_count, hist_mean_prefix ω t t le_rfl] at hmax
    have hsum : ∑ b, ((t : ℝ)*wt (trajMeanVec t ω) b - (trajPullCount b t ω : ℝ)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, (hwt _).2]
      have hc : (∑ b, (trajPullCount b t ω : ℝ)) = (t : ℝ) := by exact_mod_cast count_sum ω t
      rw [hc]; ring
    have hn : 0 ≤ (t : ℝ)*wt (trajMeanVec t ω) (ω t).1 - (trajPullCount (ω t).1 t ω : ℝ) := by
      by_contra! hh
      have hneg : (∑ b, ((t : ℝ)*wt (trajMeanVec t ω) b - (trajPullCount b t ω : ℝ))) < ∑ _b : Fin K, (0 : ℝ) := by
        apply Finset.sum_lt_sum (fun b _ => (hmax b).trans hh.le)
        exact ⟨(ω t).1, Finset.mem_univ _, hh⟩
      simp only [hsum, Finset.sum_const_zero] at hneg
      linarith
    have hbound : (trajPullCount (ω t).1 t ω : ℝ) ≤ (t : ℝ)*wt (trajMeanVec t ω) (ω t).1 := by linarith
    exact hbound.trans (le_max_right _ _)
private theorem uniform_tracking {K : ℕ} (hK : 2 ≤ K) (w : Fin K → ℝ) (hw : w ∈ simplex K)
    (wt : (Fin K → ℝ) → Fin K → ℝ) (hwt : ∀ μ, wt μ ∈ simplex K)
    (ε : ℝ) (hε : 0 < ε) (t₀ : ℕ) : ∃ tε : ℕ, t₀ ≤ tε ∧
    ∀ ω : ℕ → Fin K × ℝ, FollowsDTracking wt ω →
      (∀ t, t₀ ≤ t → ∀ a, |wt (trajMeanVec t ω) a-w a| ≤ ε) →
      ∀ t, tε ≤ t → ∀ a, |(trajPullCount a t ω : ℝ)/(t : ℝ)-w a| ≤ 3*((K : ℝ)-1)*ε := by
  obtain ⟨T₁,hT₁⟩ := exists_nat_gt (1/ε^2)
  let T := max t₀ (max 1 T₁)
  have hT0 : t₀ ≤ T := le_max_left _ _
  have hT1 : 1 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hT2 : T₁ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hTr : 1/ε^2 ≤ (T : ℝ) := hT₁.le.trans (by exact_mod_cast hT2)
  obtain ⟨T₂,hT₂⟩ := exists_nat_gt ((T : ℝ)/ε)
  refine ⟨max T T₂, hT0.trans ((le_max_left _ _)), ?_⟩
  intro ω hω hclose
  have hsel : ∀ t, T ≤ t → (trajPullCount (ω t).1 t ω : ℝ) ≤ (t : ℝ)*(w (ω t).1+ε) := by
    intro t ht
    apply (chosen_upper wt hwt ω hω t).trans
    apply max_le
    · have hh := sqrt_small ε hε T hTr t ht
      have hw0 := hw.1 (ω t).1
      nlinarith [Nat.cast_nonneg (α := ℝ) t]
    · have hh := (abs_le.mp (hclose t (hT0.trans ht) (ω t).1)).2
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hub := tracking_upper (fun t a => trajPullCount a t ω) (fun t => (ω t).1)
    (count_step ω) (count_sum ω) w hw.1 ε hε T hT1 hsel
  intro t ht
  have hTt : T ≤ t := (le_max_left _ _).trans ht
  have hT₂t : T₂ ≤ t := (le_max_right _ _).trans ht
  have htp : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hterr : (T : ℝ) ≤ ε*(t : ℝ) := by
    have hh : (T : ℝ)/ε ≤ (t : ℝ) := hT₂.le.trans (by exact_mod_cast hT₂t)
    have hh' := (div_le_iff₀ hε).mp hh
    nlinarith
  have hsum : (∑ a, (trajPullCount a t ω : ℝ)/(t : ℝ)) = ∑ a, w a := by
    rw [← Finset.sum_div, hw.2]
    have hc : (∑ b, (trajPullCount b t ω : ℝ)) = (t : ℝ) := by exact_mod_cast count_sum ω t
    rw [hc, div_self htp.ne']
  apply simplex_error hK (fun a => (trajPullCount a t ω : ℝ)/(t : ℝ)) w hsum ε hε
  intro a
  have hh := (div_le_iff₀ htp).mpr (show (trajPullCount a t ω : ℝ) ≤ (w a+2*ε)*(t : ℝ) by nlinarith [hub t hTt a])
  linarith

end DTrackProof

theorem solution (F : ExpFamily) {K : ℕ} (hK : 2 ≤ K)
    (μ : Fin K → ℝ) (hμ : μ ∈ bestArmMeans F K) (w : Fin K → ℝ) (hw : IsOptimalProportion F μ w)
    (wt : (Fin K → ℝ) → (Fin K → ℝ)) (hwt_simplex : ∀ μ', wt μ' ∈ simplex K)
    (hwt_opt : ∀ μ' ∈ bestArmMeans F K, IsOptimalProportion F μ' (wt μ')) :
    (∀ ω : ℕ → Fin K × ℝ, FollowsDTracking wt ω → ∀ (t : ℕ) (a : Fin K),
      max (Real.sqrt (t : ℝ) - (K : ℝ) / 2) 0 - 1 ≤ (trajPullCount a t ω : ℝ)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℕ, ∃ tε : ℕ, t₀ ≤ tε ∧
      ∀ ω : ℕ → Fin K × ℝ, FollowsDTracking wt ω →
        ((∀ t : ℕ, t₀ ≤ t → ∀ a : Fin K, |wt (trajMeanVec t ω) a - w a| ≤ ε) →
          ∀ t : ℕ, tε ≤ t → ∀ a : Fin K,
            |(trajPullCount a t ω : ℝ) / (t : ℝ) - w a| ≤ 3 * ((K : ℝ) - 1) * ε) := by
  constructor
  · intro ω hω
    exact DTrackProof.forced_lower hK (fun t a => trajPullCount a t ω) (fun t => (ω t).1)
      (DTrackProof.count_step ω) (DTrackProof.forced_choice wt ω hω)
  · intro ε hε t₀
    exact DTrackProof.uniform_tracking hK w hw.1 wt hwt_simplex ε hε t₀
