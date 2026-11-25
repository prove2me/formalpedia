-- Prove2me | solution 1 for PandoraKnapsack.Skipping.dyadic_plan_spec
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:35:11.017524+00:00
-- url     : https://prove2.me/submissions/cfad9f29-8838-43b0-8e0a-f1fd9c88337f

import Definitions.Def_PandoraKnapsack_Skipping_DyadicPlan
import Theorems.Thm_PandoraPacking_normalized_packing_spec

namespace PandoraKnapsack.Skipping
open PandoraPacking
noncomputable section
variable {n m T : ℕ}

private lemma labelCount_pos (T : ℕ) : 0 < labelCount T := by unfold labelCount; split <;> omega

private def zeroLabel (T : ℕ) : Fin (labelCount T) := ⟨0,labelCount_pos T⟩

theorem timeLabel_le (k : Fin (labelCount T)) : timeLabel k ≤ T := by
  unfold timeLabel
  split_ifs with hk
  · omega
  · have h := k.isLt
    unfold labelCount at h
    split_ifs at h with hz
    · omega
    · exact (Nat.pow_le_pow_right (by decide : 0 < 2) (show k.val-1 ≤ Nat.log 2 T by omega)).trans
        (Nat.pow_log_le_self 2 hz)

theorem timeLabel_mem (k : Fin (labelCount T)) : timeLabel k ∈ breakpoints T := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := timeLabel_le k; omega), ?_⟩
  unfold timeLabel
  split_ifs <;> simp_all

theorem timeLabel_injective : Function.Injective (@timeLabel T) := by
  intro k l e
  unfold timeLabel at e
  split_ifs at e with a b b
  · exact Fin.ext (by omega)
  · have := pow_pos (by decide : 0 < 2) (l.val-1)
    omega
  · have := pow_pos (by decide : 0 < 2) (k.val-1)
    omega
  · have := Nat.pow_right_injective (by decide : 2 ≤ 2) e
    exact Fin.ext (by omega)

private lemma label_preimage {t : ℕ} (ht : t ∈ breakpoints T) :
    ∃ k : Fin (labelCount T), timeLabel k = t := by
  classical
  obtain ⟨htb,ht⟩ := Finset.mem_filter.mp ht
  rcases ht with rfl | ⟨l,rfl⟩
  · exact ⟨zeroLabel T,by simp [timeLabel,zeroLabel]⟩
  · have hl : 2^l ≤ T := by simpa using htb
    have hT : T ≠ 0 := by have := pow_pos (by decide : 0 < 2) l; omega
    have hh := Nat.log_mono_right (b := 2) hl
    rw [Nat.log_pow (by decide)] at hh
    exact ⟨⟨l+1,by simp [labelCount,hT]; omega⟩,by simp [timeLabel]⟩

private lemma flat_sum (f : Fin (columnCount n m T) → ℝ) :
    (∑ col, f col) = ∑ i, ∑ j, ∑ k, f (columns n m T (i,j,k)) := by
  rw [← (columns n m T).sum_comp f, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => Fintype.sum_prod_type _)

private lemma spread_sum (v : Vec (columnCount n m T)) (i : Fin n) (j : Fin m)
    (u : ℕ) (w : ℕ → ℝ) :
    (∑ t ∈ Finset.range (u+1), w t * spreadVector v i j t) =
      ∑ k, if timeLabel k ≤ u then w (timeLabel k) * v (columns n m T (i,j,k)) else 0 := by
  simp only [spreadVector,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.sum_ite_eq,Finset.mem_range,Nat.lt_succ_iff]

theorem spread_at (v : Vec (columnCount n m T)) (i : Fin n) (j : Fin m)
    (k : Fin (labelCount T)) :
    spreadVector v i j (timeLabel k) = v (columns n m T (i,j,k)) := by
  simp [spreadVector,timeLabel_injective.eq_iff]

private lemma spread_off (v : Vec (columnCount n m T)) (i : Fin n) (j : Fin m)
    (t : ℕ) (ht : t ∉ breakpoints T) : spreadVector v i j t = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  apply if_neg
  rintro rfl
  exact ht (timeLabel_mem k)

private lemma item_dot (I : Instance n m T) (v : Vec (columnCount n m T)) (a : Fin n) :
    dot (packingRows I (clockRow (Sum.inl a))) v =
      ∑ j, ∑ t ∈ Finset.range (T+1), spreadVector v a j t := by
  unfold dot
  rw [flat_sum]
  simp [packingRows,clockRow,ite_mul,Finset.sum_ite_irrel]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [one_mul,if_pos (timeLabel_le _)] using (spread_sum v a j T (fun _ => 1)).symm

private def load (I : Instance n m T) (z : LPArray n m) (u : ℕ) : ℝ :=
  ∑ i, ∑ j, ∑ t ∈ Finset.range (u+1), z i j t * mu I i j u

private lemma load_spread (I : Instance n m T) (v : Vec (columnCount n m T)) (u : ℕ) :
    load I (spreadVector v) u = ∑ i, ∑ j, ∑ k : Fin (labelCount T),
      if timeLabel k ≤ u then mu I i j u * v (columns n m T (i,j,k)) else 0 := by
  unfold load
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa only [mul_comm (spreadVector _ _ _ _) _] using spread_sum v i j u (fun _ => mu I i j u)

private lemma time_dot (I : Instance n m T) (v : Vec (columnCount n m T)) (h : Fin (labelCount T))
    (hr : timeLabel h ≠ 0) :
    dot (packingRows I (clockRow (Sum.inr h))) v = load I (spreadVector v) (timeLabel h) / (2 * (timeLabel h : ℝ)) := by
  unfold dot
  rw [flat_sum,load_spread]
  simp only [packingRows,clockRow,Equiv.symm_apply_apply,if_neg hr,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

private lemma mu_bounds (I : Instance n m T) (i : Fin n) (j : Fin m) (t : ℕ) :
    0 ≤ mu I i j t ∧ mu I i j t ≤ t := by
  unfold mu truncMean
  constructor
  · positivity
  calc
    _ ≤ ∑ s, (I.sizeLaw i j s).toReal * t :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (min_le_right ..) ENNReal.toReal_nonneg)
    _ = t := by
      rw [← Finset.sum_mul, ← ENNReal.toReal_sum (fun s _ => (I.sizeLaw i j).apply_ne_top s)]
      have hp := congrArg ENNReal.toReal (I.sizeLaw i j).tsum_coe
      simp only [tsum_fintype, ENNReal.toReal_one] at hp
      rw [hp,one_mul]

private lemma rows_cube (I : Instance n m T) (a : Fin (timeRows n T)) : Cube (packingRows I a) := by
  intro col
  unfold packingRows
  dsimp only
  split
  · split_ifs <;> norm_num
  · rename_i k _
    split_ifs with hz hs
    · norm_num
    · have hm := mu_bounds I ((columns n m T).symm col).1 ((columns n m T).symm col).2.1 (timeLabel k)
      constructor
      · exact div_nonneg hm.1 (by positivity)
      · apply (div_le_iff₀ (by positivity : (0:ℝ) < 2 * (timeLabel k : ℝ))).2
        linarith [show (0:ℝ) ≤ timeLabel k by positivity]
    · norm_num

private lemma label_floor_le {u : ℕ} (k : Fin (labelCount T))
    (hk : timeLabel k ≤ u) : timeLabel k ≤ 2 ^ Nat.log 2 u := by
  unfold timeLabel at hk ⊢
  split_ifs at hk ⊢ with h
  · exact Nat.zero_le _
  · apply Nat.pow_le_pow_right (by decide)
    have hh := Nat.log_mono_right (b := 2) hk
    simpa only [Nat.log_pow (by decide : 1 < 2)] using hh

private lemma mu_scaled (I : Instance n m T) (i : Fin n) (j : Fin m) {d c : ℕ}
    {k : ℝ} (hk : 1 ≤ k) (hd : (d : ℝ) ≤ (c : ℝ) * k) :
    mu I i j d ≤ mu I i j c * k := by
  unfold mu truncMean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  rcases le_total (s.val : ℝ) c with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (le_mul_of_one_le_right (by positivity) hk)
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans hd

private lemma spread_feasible (I : Instance n m T) (v : Vec (columnCount n m T))
    (hv : Feasible (packingRows I) v) : PsiFeasible I T (spreadVector v) := by
  constructor
  · intro u hu
    change load I (spreadVector v) u ≤ _
    by_cases hz : u = 0
    · subst u
      simp [load,mu,truncMean]
    let r := 2 ^ Nat.log 2 u
    have hr0 : 0 < r := pow_pos (by decide) _
    have hru : r ≤ u := Nat.pow_log_le_self 2 hz
    have hrb : r ∈ breakpoints T := by
      classical
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Or.inr ⟨_,rfl⟩⟩
    obtain ⟨h,he⟩ := label_preimage hrb
    have hp := hv.2 (clockRow (Sum.inr h))
    rw [time_dot I v h (by omega), he] at hp
    have hrR : (0:ℝ) < r := by exact_mod_cast hr0
    have hcap : load I (spreadVector v) r ≤ 2 * (r:ℝ) := by
      simpa only [one_mul] using (div_le_iff₀ (show 0 < 2 * (r:ℝ) by positivity)).mp hp
    let s : ℝ := (u:ℝ)/r
    have hsr : (r:ℝ)*s = u := by dsimp [s]; field_simp
    have hs : 1 ≤ s := (le_div_iff₀ hrR).mpr (by rw [one_mul];exact_mod_cast hru)
    calc
      load I (spreadVector v) u ≤ load I (spreadVector v) r * s := by
        simp only [load_spread, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : timeLabel k ≤ u
        · have hl : timeLabel k ≤ r := label_floor_le k hk
          rw [if_pos hk,if_pos hl]
          have hm := mu_scaled I i j (d := u) (c := r) hs hsr.ge
          have hb := mul_le_mul_of_nonneg_right hm (hv.1 (columns n m T (i,j,k))).1
          simpa only [mul_right_comm (mu I i j r) s _] using hb
        · rw [if_neg hk,if_neg (fun h => hk (h.trans hru)),zero_mul]
      _ ≤ (2*(r:ℝ))*s := mul_le_mul_of_nonneg_right hcap (by linarith)
      _ = _ := by rw [mul_assoc,hsr]
  constructor
  · intro i
    exact (item_dot I v i) ▸ hv.2 (clockRow (Sum.inl i))
  · intro i j t _
    by_cases ht : t ∈ breakpoints T
    · obtain ⟨k,rfl⟩ := label_preimage ht
      simpa only [spread_at] using hv.1 (columns n m T (i,j,k))
    · simp [spread_off _ _ _ _ ht]

private def gather (z : LPArray n m) (col : Fin (columnCount n m T)) : ℝ :=
  let p := (columns n m T).symm col
  z p.1 p.2.1 (timeLabel p.2.2)

private lemma spread_gather (z : LPArray n m)
    (hs : ∀ i j t, t ∉ breakpoints T → z i j t = 0) :
    spreadVector (gather (T := T) z) = z := by
  funext i j t
  by_cases ht : t ∈ breakpoints T
  · obtain ⟨k,rfl⟩ := label_preimage ht
    simp [spread_at,gather]
  · rw [spread_off _ _ _ _ ht,hs _ _ _ ht]

private lemma gather_feasible (I : Instance n m T) (z : LPArray n m) (hz : PsiFeasible I T z)
    (hs : ∀ i j t, t ∉ breakpoints T → z i j t = 0) :
    Feasible (packingRows I) (gather z) := by
  refine ⟨fun col => hz.2.2 _ _ _ (timeLabel_le _),fun row => ?_⟩
  obtain ⟨i | h, rfl⟩ := finSumFinEquiv.surjective row
  · rw [show finSumFinEquiv (Sum.inl i) = clockRow (T := T) (Sum.inl i) from rfl,
      item_dot,spread_gather z hs]
    exact hz.2.1 i
  · change dot (packingRows I (clockRow (Sum.inr h))) _ ≤ 1
    by_cases he : timeLabel h = 0
    · simp [dot, packingRows,clockRow,he]
    · rw [time_dot I _ h he,spread_gather z hs]
      apply (div_le_iff₀ (show 0 < 2 * (timeLabel h : ℝ) by positivity)).mpr
      simpa [load] using hz.1 (timeLabel h) (timeLabel_le h)

private lemma objective_spread (I : Instance n m T) (v : Vec (columnCount n m T)) :
    psiObjective I T (spreadVector v) = dot (columnWeight I) v := by
  unfold psiObjective dot
  rw [flat_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa only [columnWeight, Equiv.symm_apply_apply,if_pos (timeLabel_le _)] using
    spread_sum v i j T (effWeight I i j)
private lemma earlier_weight (I : Instance n m T) (hI : IsValid I) (i : Fin n) (j : Fin m)
    {u t : ℕ} (h : u ≤ t) : effWeight I i j t ≤ effWeight I i j u := by
  have hc : 0 ≤ cdf I i j ((T : ℝ) - (0 : ℕ)) := by
    unfold cdf
    positivity
  have hv : 0 ≤ I.value i := by
    by_contra! hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg hn.le hc
    have hp := hI.2.2 i j
    unfold effWeight at hp
    linarith [hI.2.1 i j]
  unfold effWeight
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ hv
  unfold cdf
  apply Finset.sum_le_sum
  intro s hs
  have h' : (u : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
  split_ifs <;> first | rfl | positivity | linarith

private lemma zero_le_maxWeight (I : Instance n m T) : 0 ≤ maxWeight I :=
  Finset.le_max' _ 0 (Finset.mem_insert_self ..)

private lemma initial_le_maxWeight (I : Instance n m T) (i : Fin n) (j : Fin m) :
    effWeight I i j 0 ≤ maxWeight I := by
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩

private lemma weight_le_maxWeight (I : Instance n m T) (hI : IsValid I) (col : Fin (columnCount n m T)) :
    columnWeight I col ≤ maxWeight I :=
  (earlier_weight I hI _ _ (Nat.zero_le _)).trans (initial_le_maxWeight I _ _)

private lemma profits_cube (I : Instance n m T) (hI : IsValid I) : Cube (packingProfits I) := by
  intro col
  unfold packingProfits
  split_ifs with hz
  · norm_num
  · have hp : 0 < maxWeight I := lt_of_le_of_ne (zero_le_maxWeight I) (Ne.symm hz)
    exact ⟨div_nonneg (le_max_left ..) hp.le, (div_le_one hp).mpr
      (max_le (zero_le_maxWeight I) (weight_le_maxWeight I hI col))⟩

private lemma maxWeight_anchor (I : Instance n m T) (hp : 0 < maxWeight I) :
    ∃ a : Fin (columnCount n m T), packingProfits I a = 1 := by
  classical
  have h := (Finset.max'_mem _ _ : maxWeight I ∈
    insert 0 (Finset.univ.image fun p : Fin n × Fin m => effWeight I p.1 p.2 0))
  rcases Finset.mem_insert.mp h with hz | hm
  · exact False.elim (hp.ne' hz)
  obtain ⟨⟨i,j⟩,_,hm⟩ := Finset.mem_image.mp hm
  change effWeight I i j 0 = maxWeight I at hm
  refine ⟨columns n m T (i,j,zeroLabel T), ?_⟩
  simp [packingProfits,hp.ne',columnWeight,timeLabel,zeroLabel,hm,max_eq_right hp.le]

private def point {d : ℕ} (a : Fin d) : Vec d := fun j => if j = a then 1 else 0

private lemma dot_point {d : ℕ} (c : Vec d) (a : Fin d) : dot c (point a) = c a := by
  simp [dot,point,mul_ite]

private lemma point_feasible (I : Instance n m T) (a : Fin (columnCount n m T)) :
    Feasible (packingRows I) (point a) := by
  constructor
  · intro col
    unfold point
    split_ifs <;> norm_num
  · intro r
    rw [dot_point]
    exact ((rows_cube I r) a).2

private lemma plan_vector_feasible (I : Instance n m T) : Feasible (packingRows I) (planVector I) := by
  let v := solve (packingRows I) (packingProfits I)
  have hv : Feasible (packingRows I) v := (normalized_packing_spec _ _).1
  have hle (c) : planVector I c ≤ v c := by
    unfold planVector
    split_ifs <;> first | exact le_rfl | exact (hv.1 c).1
  constructor
  · intro c
    unfold planVector
    split_ifs
    · exact hv.1 c
    · norm_num
  · intro r
    apply le_trans _ (hv.2 r)
    apply Finset.sum_le_sum
    intro col _
    exact mul_le_mul_of_nonneg_left (hle col) (rows_cube I r col).1

theorem dyadicPlan_feasible (I : Instance n m T) : PsiFeasible I T (dyadicPlan I) :=
  spread_feasible I _ (plan_vector_feasible I)

theorem dyadicPlan_support (I : Instance n m T) (i : Fin n) (j : Fin m) (t : ℕ)
    (ht : t ∉ breakpoints T) : dyadicPlan I i j t = 0 :=
  spread_off _ _ _ _ ht

theorem dyadicPlan_weight (I : Instance n m T) (i : Fin n) (j : Fin m) (t : ℕ)
    (hp : 0 < dyadicPlan I i j t) : 0 ≤ effWeight I i j t := by
  by_cases ht : t ∈ breakpoints T
  · obtain ⟨k,rfl⟩ := label_preimage ht
    by_contra! hneg
    simp [dyadicPlan,spread_at,planVector,columnWeight,not_le.mpr hneg] at hp
  · rw [dyadicPlan_support I i j t ht] at hp
    exact False.elim (lt_irrefl _ hp)

private lemma objective_plan (I : Instance n m T) (hm : 0 < maxWeight I) :
    psiObjective I T (dyadicPlan I) =
      maxWeight I * dot (packingProfits I) (solve (packingRows I) (packingProfits I)) := by
  rw [dyadicPlan, objective_spread]
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col _
  simp only [packingProfits,if_neg hm.ne',planVector]
  by_cases h : 0 ≤ columnWeight I col
  · rw [if_pos h,max_eq_right h]
    field_simp
  · simp [h,max_eq_left (le_of_not_ge h)]

private lemma profit_bound (I : Instance n m T) (hm : 0 < maxWeight I)
    (v : Vec (columnCount n m T)) (hv : Cube v) :
    dot (columnWeight I) v ≤ maxWeight I * dot (packingProfits I) v := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro col _
  calc
    _ ≤ (max 0 (columnWeight I col))*v col :=
      mul_le_mul_of_nonneg_right (le_max_right ..) (hv col).1
    _ = _ := by unfold packingProfits; rw [if_neg hm.ne']; field_simp

theorem dyadicPlan_half (I : Instance n m T) (hI : IsValid I)
    (z : LPArray n m) (hz : PsiFeasible I T z)
    (hs : ∀ i j t, t ∉ breakpoints T → z i j t = 0) :
    psiObjective I T z ≤ 2 * psiObjective I T (dyadicPlan I) := by
  by_cases hn : n = 0
  · subst n
    simp [psiObjective]
  by_cases hj : m = 0
  · subst m
    simp [psiObjective]
  have hm := (hI.2.2 ⟨0,by omega⟩ ⟨0,by omega⟩).trans_le
    (initial_le_maxWeight I _ _)
  obtain ⟨a,ha⟩ := maxWeight_anchor I hm
  have hz' := gather_feasible I z hz hs
  have q := (normalized_packing_spec (packingRows I) (packingProfits I)).2 (rows_cube I) (profits_cube I hI)
    (point a) (point_feasible I a) (by rw [dot_point,ha]) (gather z) hz'
  have hobj : psiObjective I T z = dot (columnWeight I) (gather z) := by
    simpa only [spread_gather z hs] using objective_spread I (gather (T := T) z)
  rw [hobj,objective_plan I hm]
  exact (profit_bound I hm _ hz'.1).trans (by
    simpa only [mul_left_comm (maxWeight I) 2 _] using mul_le_mul_of_nonneg_left q hm.le)

end
end PandoraKnapsack.Skipping

open PandoraKnapsack.Skipping

theorem solution {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) :
    PsiFeasible I T (dyadicPlan I) ∧
    (∀ i j t, 0 < dyadicPlan I i j t → 0 ≤ effWeight I i j t) ∧
    ∀ z, PsiFeasible I T z → (∀ i j t, t ∉ breakpoints T → z i j t = 0) →
      psiObjective I T z ≤ 2 * psiObjective I T (dyadicPlan I) := by
  exact ⟨dyadicPlan_feasible I,dyadicPlan_weight I,dyadicPlan_half I hI⟩
