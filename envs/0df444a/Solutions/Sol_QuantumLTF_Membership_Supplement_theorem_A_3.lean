-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_A_3
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T01:17:29.372237+00:00
-- url     : https://prove2.me/submissions/9f357de9-a96d-43c8-92d2-14b00f2ae974

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_QueryTree
import Theorems.Thm_QuantumLTF_Membership_lemma_2_1

namespace Aux_w_a3

open MeasureTheory QuantumLTF.Membership

private lemma ltf_eq_one_or_neg_one {n : ℕ} (w x : EuclideanSpace ℝ (Fin n)) :
    ltf w 0 x = 1 ∨ ltf w 0 x = -1 := by
  unfold ltf sgn
  split_ifs <;> simp

private def leafList {n : ℕ} {α : Type} : QueryTree n α → List α
  | .leaf a => [a]
  | .query _ next => leafList (next 1) ++ leafList (next (-1))

private lemma leafList_length_le {n : ℕ} {α : Type} (t : QueryTree n α) :
    (leafList t).length ≤ 2 ^ t.depth := by
  induction t with
  | leaf a => simp [leafList, QueryTree.depth]
  | query x next ih =>
    simp only [leafList, QueryTree.depth, List.length_append]
    have h1 : (leafList (next 1)).length ≤ 2 ^ max (next 1).depth (next (-1)).depth :=
      (ih 1).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
    have h2 : (leafList (next (-1))).length ≤ 2 ^ max (next 1).depth (next (-1)).depth :=
      (ih (-1)).trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    calc (leafList (next 1)).length + (leafList (next (-1))).length
      _ ≤ 2 ^ max (next 1).depth (next (-1)).depth +
            2 ^ max (next 1).depth (next (-1)).depth := Nat.add_le_add h1 h2
      _ = 2 ^ (1 + max (next 1).depth (next (-1)).depth) := by ring

private lemma run_mem_leafList {n : ℕ} {α : Type} (t : QueryTree n α)
    (f : EuclideanSpace ℝ (Fin n) → ℤ) (hf : ∀ x, f x = 1 ∨ f x = -1) :
    t.run f ∈ leafList t := by
  induction t with
  | leaf a => simp [QueryTree.run, leafList]
  | query x next ih =>
    simp only [QueryTree.run, leafList, List.mem_append]
    rcases hf x with hfx | hfx
    · left; rw [hfx]; exact ih 1
    · right; rw [hfx]; exact ih (-1)

private lemma disagree_triangle {n : ℕ} (f g h : EuclideanSpace ℝ (Fin n) → ℤ) :
    disagree f g ≤ disagree h f + disagree h g := by
  unfold disagree
  set μg : Measure (EuclideanSpace ℝ (Fin n)) :=
    ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))
  have hsub : {x | f x ≠ g x} ⊆ {x | h x ≠ f x} ∪ {x | h x ≠ g x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    by_contra hnot
    push Not at hnot
    exact hx (hnot.1.symm.trans hnot.2)
  have h1 : μg {x | h x ≠ f x} ≠ ⊤ := measure_ne_top μg _
  have h2 : μg {x | h x ≠ g x} ≠ ⊤ := measure_ne_top μg _
  calc (μg {x | f x ≠ g x}).toReal
    _ ≤ (μg ({x | h x ≠ f x} ∪ {x | h x ≠ g x})).toReal :=
        ENNReal.toReal_mono (measure_ne_top μg _) (measure_mono hsub)
    _ ≤ (μg {x | h x ≠ f x} + μg {x | h x ≠ g x}).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h1, h2⟩) (measure_union_le _ _)
    _ = (μg {x | h x ≠ f x}).toReal + (μg {x | h x ≠ g x}).toReal :=
        ENNReal.toReal_add h1 h2

lemma counting_lower_bound {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : Ω → QueryTree n (EuclideanSpace ℝ (Fin n) → ℤ)) (q : ℕ)
    (ht_depth : ∀ ω, (t ω).depth ≤ q) (ε : ℝ)
    (P : Finset (EuclideanSpace ℝ (Fin n)))
    (hP_norm : ∀ w ∈ P, ‖w‖ = 1)
    (hP_sep : ∀ u ∈ P, ∀ w ∈ P, u ≠ w → 2 * ε < disagree (ltf u 0) (ltf w 0))
    (h_succ : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
      ∃ S : Set Ω, MeasurableSet S ∧
        S ⊆ {ω | disagree ((t ω).run (ltf w 0)) (ltf w 0) ≤ ε} ∧ (2 / 3 : ENNReal) ≤ μ S) :
    2 * P.card ≤ 3 * 2 ^ q := by
  classical
  choose S hS_meas hS_sub hS_prob using fun (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) =>
    h_succ w hw
  let Sw (w : EuclideanSpace ℝ (Fin n)) : Set Ω :=
    if hw : w ∈ P then S w (hP_norm w hw) else ∅
  have hSw_meas : ∀ w, MeasurableSet (Sw w) := by
    intro w
    by_cases hw : w ∈ P
    · simp only [Sw, dif_pos hw]; exact hS_meas w (hP_norm w hw)
    · simp only [Sw, dif_neg hw]; exact MeasurableSet.empty
  have hSw_sub : ∀ w ∈ P, Sw w ⊆ {ω | disagree ((t ω).run (ltf w 0)) (ltf w 0) ≤ ε} := by
    intro w hw
    simp only [Sw, dif_pos hw]
    exact hS_sub w (hP_norm w hw)
  have hSw_prob : ∀ w ∈ P, (2 / 3 : ENNReal) ≤ μ (Sw w) := by
    intro w hw
    simp only [Sw, dif_pos hw]
    exact hS_prob w (hP_norm w hw)
  have hpointwise : ∀ ω : Ω,
      ∑ w ∈ P, (Sw w).indicator (fun _ => (1 : ENNReal)) ω ≤ ((2 ^ q : ℕ) : ENNReal) := by
    intro ω
    let P_good := P.filter (fun w => ω ∈ Sw w)
    have hsum_eq : ∑ w ∈ P, (Sw w).indicator (fun _ => (1 : ENNReal)) ω = (P_good.card : ENNReal) := by
      have h1 : ∀ w ∈ P, (Sw w).indicator (fun _ => (1 : ENNReal)) ω =
          if ω ∈ Sw w then (1 : ENNReal) else 0 := fun w _ => by
        simp [Set.indicator]
      rw [Finset.sum_congr rfl h1, Finset.sum_boole]
    rw [hsum_eq]
    norm_cast
    let leaves := (leafList (t ω)).toFinset
    have hcard_leaves : leaves.card ≤ 2 ^ q := by
      calc leaves.card
        _ ≤ (leafList (t ω)).length := List.toFinset_card_le _
        _ ≤ 2 ^ (t ω).depth := leafList_length_le (t ω)
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (ht_depth ω)
    have hinj : Set.InjOn (fun w => (t ω).run (ltf w 0)) (P_good : Set (EuclideanSpace ℝ (Fin n))) := by
      intro u hu v hv huv
      simp only [Finset.mem_coe, P_good, Finset.mem_filter] at hu hv
      dsimp only at huv
      by_contra hne
      have htri := disagree_triangle (ltf u 0) (ltf v 0) ((t ω).run (ltf u 0))
      have hu_err : disagree ((t ω).run (ltf u 0)) (ltf u 0) ≤ ε := hSw_sub u hu.1 hu.2
      have hv_err : disagree ((t ω).run (ltf u 0)) (ltf v 0) ≤ ε := by
        rw [huv]; exact hSw_sub v hv.1 hv.2
      have hsep := hP_sep u hu.1 v hv.1 hne
      linarith
    have hmaps : ∀ w ∈ P_good, (t ω).run (ltf w 0) ∈ leaves := by
      intro w _
      simp only [leaves, List.mem_toFinset]
      exact run_mem_leafList (t ω) (ltf w 0) (ltf_eq_one_or_neg_one w)
    exact (Finset.card_le_card_of_injOn (fun w => (t ω).run (ltf w 0)) hmaps hinj).trans hcard_leaves
  have hsum_prob : (P.card : ENNReal) * (2 / 3 : ENNReal) ≤ ((2 ^ q : ℕ) : ENNReal) := by
    calc (P.card : ENNReal) * (2 / 3 : ENNReal)
      _ = ∑ _w ∈ P, (2 / 3 : ENNReal) := by simp
      _ ≤ ∑ w ∈ P, μ (Sw w) := Finset.sum_le_sum (fun w hw => hSw_prob w hw)
      _ = ∑ w ∈ P, ∫⁻ ω, (Sw w).indicator (fun _ => (1 : ENNReal)) ω ∂μ := by
          refine Finset.sum_congr rfl fun w _ => ?_
          exact (lintegral_indicator_one (hSw_meas w)).symm
      _ = ∫⁻ ω, ∑ w ∈ P, (Sw w).indicator (fun _ => (1 : ENNReal)) ω ∂μ := by
          refine (lintegral_finsetSum P fun w _ => ?_).symm
          exact measurable_const.indicator (hSw_meas w)
      _ ≤ ∫⁻ _ω, ((2 ^ q : ℕ) : ENNReal) ∂μ := lintegral_mono hpointwise
      _ = ((2 ^ q : ℕ) : ENNReal) := by simp
  have hmul3 : ((2 * P.card : ℕ) : ENNReal) ≤ ((3 * 2 ^ q : ℕ) : ENNReal) := by
    have h23 : (2 / 3 : ENNReal) * 3 = 2 := ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    calc ((2 * P.card : ℕ) : ENNReal)
      _ = (P.card : ENNReal) * 2 := by push_cast; ring
      _ = (P.card : ENNReal) * ((2 / 3 : ENNReal) * 3) := by rw [h23]
      _ = (P.card : ENNReal) * (2 / 3 : ENNReal) * 3 := by ring
      _ ≤ ((2 ^ q : ℕ) : ENNReal) * 3 := mul_le_mul_of_nonneg_right hsum_prob (by positivity)
      _ = ((3 * 2 ^ q : ℕ) : ENNReal) := by push_cast; ring
  exact_mod_cast hmul3

lemma disagree_ltf_gt_of_norm_sub_gt {n : ℕ} (u w : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {ε : ℝ} (hdist : 2 * Real.pi * ε < ‖u - w‖) :
    2 * ε < disagree (ltf u 0) (ltf w 0) := by
  have h21 := (lemma_2_1 u w hu hw 0 0).2
  rw [h21, lt_div_iff₀ Real.pi_pos]
  set θ := Real.arccos (inner ℝ u w)
  have hinner_abs : |inner ℝ u w| ≤ 1 := by
    calc |inner ℝ u w|
      _ ≤ ‖u‖ * ‖w‖ := abs_real_inner_le_norm u w
      _ = 1 := by rw [hu, hw]; ring
  have hcos : Real.cos θ = inner ℝ u w := by
    have hb := abs_le.mp hinner_abs
    exact Real.cos_arccos hb.1 hb.2
  have hnorm_sq : ‖u - w‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    have hsub := norm_sub_sq_real u w
    rw [hu, hw] at hsub
    have htrig : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h1 := Real.cos_two_mul (θ / 2)
      have h2 := Real.sin_sq_add_cos_sq (θ / 2)
      have h2θ : 2 * (θ / 2) = θ := by ring
      rw [h2θ] at h1
      linarith
    linarith
  have hsin_sq : Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 :=
    sq_le_sq.mpr Real.abs_sin_le_abs
  have hsq_le : ‖u - w‖ ^ 2 ≤ θ ^ 2 := by
    calc ‖u - w‖ ^ 2
      _ = 4 * Real.sin (θ / 2) ^ 2 := hnorm_sq
      _ ≤ 4 * (θ / 2) ^ 2 := by linarith
      _ = θ ^ 2 := by ring
  have hnorm_le_θ : ‖u - w‖ ≤ θ :=
    (abs_le_of_sq_le_sq' hsq_le (Real.arccos_nonneg _)).2
  linarith

noncomputable def liftSphere {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.snoc y.ofLp (Real.sqrt (1 - ‖y‖ ^ 2)))

lemma norm_liftSphere {m : ℕ} {y : EuclideanSpace ℝ (Fin m)} (hy : ‖y‖ ≤ 1) :
    ‖liftSphere y‖ = 1 := by
  have h1 : 0 ≤ 1 - ‖y‖ ^ 2 := by
    have hsq : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
    linarith
  have hsq_norm : ‖liftSphere y‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [liftSphere, Real.norm_eq_abs, sq_abs, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last]
    have hy_sq : ∑ i : Fin m, (y.ofLp i) ^ 2 = ‖y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hy_sq, Real.sq_sqrt h1]
    ring
  nlinarith [norm_nonneg (liftSphere y)]

lemma norm_sub_le_liftSphere {m : ℕ} (y y' : EuclideanSpace ℝ (Fin m)) :
    ‖y - y'‖ ≤ ‖liftSphere y - liftSphere y'‖ := by
  have hsq : ‖y - y'‖ ^ 2 ≤ ‖liftSphere y - liftSphere y'‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, liftSphere, Fin.sum_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (abs_le_of_sq_le_sq' hsq (norm_nonneg _)).2

lemma liftSphere_injective {m : ℕ} : Function.Injective (liftSphere (m := m)) := by
  intro y y' h
  have hle := norm_sub_le_liftSphere y y'
  rw [h, sub_self, norm_zero] at hle
  have h0 : ‖y - y'‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

lemma euclidean_ball_packing (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    ∃ Y : Finset (EuclideanSpace ℝ (Fin m)),
      (∀ y ∈ Y, ‖y‖ ≤ 1 / 2) ∧
      (∀ u ∈ Y, ∀ v ∈ Y, u ≠ v → δ < ‖u - v‖) ∧
      (1 / 2 : ℝ) ^ m ≤ (Y.card : ℝ) * δ ^ m := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  have : NeZero m := ⟨by omega⟩
  let B : Set E := Metric.closedBall 0 (1 / 2)
  let Valid (Y : Finset E) : Prop :=
    (↑Y : Set E) ⊆ B ∧ ∀ u ∈ Y, ∀ v ∈ Y, u ≠ v → δ < dist u v
  let V : ENNReal := volume (Metric.ball (0 : E) 1)
  have hV_pos : 0 < V := Metric.measure_ball_pos volume 0 zero_lt_one
  have hV_lt : V < ⊤ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : E) 1).measure_lt_top
  have hV_ne0 : V ≠ 0 := hV_pos.ne'
  have hV_neTop : V ≠ ⊤ := hV_lt.ne
  have hcard_ub : ∀ Y : Finset E, Valid Y → Y.card ≤ Nat.floor ((2 / δ) ^ m) := by
    intro Y hY
    have hdisj : (↑Y : Set E).PairwiseDisjoint (fun u => Metric.ball u (δ / 2)) := by
      intro u hu v hv huv
      dsimp only [Function.onFun]
      rw [Set.disjoint_iff]
      intro z hz
      simp only [Set.mem_inter_iff, Metric.mem_ball] at hz
      have htri := dist_triangle u z v
      rw [dist_comm u z] at htri
      have hsep := hY.2 u hu v hv huv
      linarith
    have hsub : (⋃ u ∈ Y, Metric.ball u (δ / 2)) ⊆ Metric.ball (0 : E) 1 := by
      intro z hz
      simp only [Set.mem_iUnion, Metric.mem_ball] at hz ⊢
      rcases hz with ⟨u, hu, hzu⟩
      have huB : dist u 0 ≤ 1 / 2 := hY.1 hu
      linarith [dist_triangle z u 0]
    have hvol_sum : (Y.card : ENNReal) * ENNReal.ofReal ((δ / 2) ^ m) * V ≤ 1 * V := by
      calc (Y.card : ENNReal) * ENNReal.ofReal ((δ / 2) ^ m) * V
        _ = ∑ _u ∈ Y, ENNReal.ofReal ((δ / 2) ^ m) * V := by simp [mul_assoc]
        _ = ∑ u ∈ Y, volume (Metric.ball u (δ / 2)) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Measure.addHaar_ball volume u (by positivity), finrank_euclideanSpace_fin]
        _ = volume (⋃ u ∈ Y, Metric.ball u (δ / 2)) :=
            (measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)).symm
        _ ≤ volume (Metric.ball (0 : E) 1) := measure_mono hsub
        _ = 1 * V := by simp [V]
    have hle1 : (Y.card : ENNReal) * ENNReal.ofReal ((δ / 2) ^ m) ≤ 1 :=
      (ENNReal.mul_le_mul_iff_left hV_ne0 hV_neTop).mp hvol_sum
    have hle1_real : (Y.card : ℝ) * (δ / 2) ^ m ≤ 1 := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_one] at hle1
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hle1
    have hpow_pos : 0 < (δ / 2) ^ m := by positivity
    have hdiv : (Y.card : ℝ) ≤ (2 / δ) ^ m := by
      calc (Y.card : ℝ)
        _ ≤ 1 / (δ / 2) ^ m := (le_div_iff₀ hpow_pos).mpr hle1_real
        _ = (2 / δ) ^ m := by rw [one_div, ← inv_pow, inv_div]
    exact Nat.le_floor hdiv
  let M : ℕ := Nat.floor ((2 / δ) ^ m)
  let Snat : Finset ℕ :=
    (Finset.range (M + 1)).filter (fun k => ∃ Y : Finset E, Valid Y ∧ Y.card = k)
  have h0_mem : 0 ∈ Snat := by
    simp only [Snat, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.zero_lt_succ M, ∅, ?_, rfl⟩
    refine ⟨by simp, by simp⟩
  have hS_ne : Snat.Nonempty := ⟨0, h0_mem⟩
  let kmax := Snat.max' hS_ne
  have hkmax_mem : kmax ∈ Snat := Finset.max'_mem Snat hS_ne
  simp only [Snat, Finset.mem_filter, Finset.mem_range] at hkmax_mem
  rcases hkmax_mem.2 with ⟨Y, hY_valid, hY_card⟩
  have hcover : B ⊆ ⋃ y ∈ Y, Metric.closedBall y δ := by
    intro x hxB
    by_cases hxY : x ∈ Y
    · exact Set.mem_biUnion hxY (Metric.mem_closedBall_self hδ_pos.le)
    · by_contra hnot
      simp only [Set.mem_iUnion, Metric.mem_closedBall, not_exists, not_le] at hnot
      have hValid_ins : Valid (insert x Y) := by
        refine ⟨?_, ?_⟩
        · intro u hu
          simp only [Finset.mem_coe, Finset.mem_insert] at hu
          rcases hu with rfl | huY
          · exact hxB
          · exact hY_valid.1 huY
        · intro u hu v hv huv
          simp only [Finset.mem_insert] at hu hv
          rcases hu with rfl | huY <;> rcases hv with rfl | hvY
          · exact absurd rfl huv
          · exact hnot v hvY
          · rw [dist_comm]; exact hnot u huY
          · exact hY_valid.2 u huY v hvY huv
      have hins_card : (insert x Y).card = kmax + 1 := by
        rw [Finset.card_insert_of_notMem hxY, hY_card]
      have hleM : kmax + 1 ≤ M := hins_card ▸ hcard_ub (insert x Y) hValid_ins
      have hk1_mem : kmax + 1 ∈ Snat := by
        simp only [Snat, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le hleM, insert x Y, hValid_ins, hins_card⟩
      have hle_max := Finset.le_max' Snat (kmax + 1) hk1_mem
      omega
  have hvol_lb : ENNReal.ofReal ((1 / 2 : ℝ) ^ m) * V ≤
      (Y.card : ENNReal) * ENNReal.ofReal (δ ^ m) * V := by
    calc ENNReal.ofReal ((1 / 2 : ℝ) ^ m) * V
      _ = volume B := by
          rw [Measure.addHaar_closedBall volume (0 : E) (by norm_num), finrank_euclideanSpace_fin]
      _ ≤ volume (⋃ y ∈ Y, Metric.closedBall y δ) := measure_mono hcover
      _ ≤ ∑ y ∈ Y, volume (Metric.closedBall y δ) := measure_biUnion_finset_le Y _
      _ = ∑ _y ∈ Y, ENNReal.ofReal (δ ^ m) * V := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Measure.addHaar_closedBall volume y hδ_pos.le, finrank_euclideanSpace_fin]
      _ = (Y.card : ENNReal) * ENNReal.ofReal (δ ^ m) * V := by simp [mul_assoc]
  have hvol_cancel : ENNReal.ofReal ((1 / 2 : ℝ) ^ m) ≤ (Y.card : ENNReal) * ENNReal.ofReal (δ ^ m) :=
    (ENNReal.mul_le_mul_iff_left hV_ne0 hV_neTop).mp hvol_lb
  have hreal_lb : (1 / 2 : ℝ) ^ m ≤ (Y.card : ℝ) * δ ^ m := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hvol_cancel
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol_cancel
  refine ⟨Y, ?_, ?_, hreal_lb⟩
  · intro y hy
    have hyB : y ∈ B := hY_valid.1 hy
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hyB
  · intro u hu v hv huv
    have h := hY_valid.2 u hu v hv huv
    rwa [dist_eq_norm] at h

end Aux_w_a3

open MeasureTheory QuantumLTF.Membership

theorem solution :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (t : Ω → QueryTree n (EuclideanSpace ℝ (Fin n) → ℤ)) (q : ℕ),
        (∀ ω, (t ω).depth ≤ q) →
        (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∃ S : Set Ω, MeasurableSet S ∧
            S ⊆ {ω | disagree ((t ω).run (ltf w 0)) (ltf w 0) ≤ ε} ∧ (2 / 3 : ENNReal) ≤ μ S) →
          c * n * Real.log (1 / ε) ≤ q := by
  refine ⟨1 / 256, by norm_num, 3 / (16 * Real.log 2), ?_, ?_⟩
  · exact div_pos (by norm_num) (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  · intro n hn ε hε_pos hε_le Ω _ μ _ t q ht_depth h_succ
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ m := by omega
    let δ : ℝ := 2 * Real.pi * ε
    have hδ_pos : 0 < δ := by positivity
    have hδ_le : δ ≤ 1 := by
      have hpi := Real.pi_lt_four
      nlinarith
    obtain ⟨Y, hY_norm, hY_sep, hY_vol⟩ := Aux_w_a3.euclidean_ball_packing m hm δ hδ_pos hδ_le
    let P : Finset (EuclideanSpace ℝ (Fin (m + 1))) := Y.image Aux_w_a3.liftSphere
    have hP_card : P.card = Y.card := Finset.card_image_of_injective Y Aux_w_a3.liftSphere_injective
    have hP_norm : ∀ w ∈ P, ‖w‖ = 1 := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨y, hy, rfl⟩
      exact Aux_w_a3.norm_liftSphere (by linarith [hY_norm y hy])
    have hP_sep : ∀ u ∈ P, ∀ w ∈ P, u ≠ w → 2 * ε < disagree (ltf u 0) (ltf w 0) := by
      intro u hu w hw huw
      rcases Finset.mem_image.mp hu with ⟨y₁, hy₁, rfl⟩
      rcases Finset.mem_image.mp hw with ⟨y₂, hy₂, rfl⟩
      have hy_ne : y₁ ≠ y₂ := fun h => huw (congrArg Aux_w_a3.liftSphere h)
      have hdist_y : δ < ‖y₁ - y₂‖ := hY_sep y₁ hy₁ y₂ hy₂ hy_ne
      have hdist_w : 2 * Real.pi * ε < ‖Aux_w_a3.liftSphere y₁ - Aux_w_a3.liftSphere y₂‖ :=
        lt_of_lt_of_le hdist_y (Aux_w_a3.norm_sub_le_liftSphere y₁ y₂)
      exact Aux_w_a3.disagree_ltf_gt_of_norm_sub_gt _ _
        (Aux_w_a3.norm_liftSphere (by linarith [hY_norm y₁ hy₁]))
        (Aux_w_a3.norm_liftSphere (by linarith [hY_norm y₂ hy₂]))
        hdist_w
    have hcount : 2 * P.card ≤ 3 * 2 ^ q :=
      Aux_w_a3.counting_lower_bound μ t q ht_depth ε P hP_norm hP_sep h_succ
    rw [hP_card] at hcount
    have hcount_real : (2 / 3 : ℝ) * (Y.card : ℝ) ≤ (2 : ℝ) ^ q := by
      have hcr : (2 : ℝ) * (Y.card : ℝ) ≤ 3 * (2 : ℝ) ^ q := by exact_mod_cast hcount
      linarith
    have hδ_lt_8ε : δ ≤ 8 * ε := by
      have hpi := Real.pi_lt_four
      nlinarith
    have hY_vol_8ε : (1 / 2 : ℝ) ^ m ≤ (Y.card : ℝ) * (8 * ε) ^ m := by
      have hpow : δ ^ m ≤ (8 * ε) ^ m := pow_le_pow_left₀ hδ_pos.le hδ_lt_8ε m
      exact hY_vol.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))
    have h16ε_pos : 0 < 16 * ε := by positivity
    have hY_lb : (1 / (16 * ε)) ^ m ≤ (Y.card : ℝ) := by
      have h8ε_pow_pos : 0 < (8 * ε) ^ m := by positivity
      calc (1 / (16 * ε)) ^ m
        _ = (1 / 2 : ℝ) ^ m / (8 * ε) ^ m := by
            rw [← div_pow]
            congr 1
            field_simp
            norm_num
        _ ≤ (Y.card : ℝ) := (div_le_iff₀ h8ε_pow_pos).mpr hY_vol_8ε
    have hmain_exp : (2 / 3 : ℝ) * (1 / (16 * ε)) ^ m ≤ (2 : ℝ) ^ q := by
      calc (2 / 3 : ℝ) * (1 / (16 * ε)) ^ m
        _ ≤ (2 / 3 : ℝ) * (Y.card : ℝ) := by linarith
        _ ≤ (2 : ℝ) ^ q := hcount_real
    have hlog_le : Real.log ((2 / 3 : ℝ) * (1 / (16 * ε)) ^ m) ≤ Real.log ((2 : ℝ) ^ q) :=
      Real.log_le_log (by positivity) hmain_exp
    have hlhs : Real.log ((2 / 3 : ℝ) * (1 / (16 * ε)) ^ m) =
        Real.log (2 / 3) + (m : ℝ) * (Real.log (1 / ε) - Real.log 16) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      congr 1
      have hdiv : 1 / (16 * ε) = (1 / ε) / 16 := by ring
      rw [hdiv, Real.log_div (by positivity) (by norm_num)]
    have hrhs : Real.log ((2 : ℝ) ^ q) = (q : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [hlhs, hrhs] at hlog_le
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog23 : -Real.log 2 ≤ Real.log (2 / 3) := by
      have h12 : Real.log (1 / 2) ≤ Real.log (2 / 3) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rwa [one_div, Real.log_inv] at h12
    have hlog_inv_ε : 8 * Real.log 2 ≤ Real.log (1 / ε) := by
      have h256 : (256 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε_pos).mpr (by linarith)
      have hlog256 : Real.log (256 : ℝ) ≤ Real.log (1 / ε) :=
        Real.log_le_log (by norm_num) h256
      have h28 : (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) := by norm_num
      rw [h28, Real.log_pow] at hlog256
      simpa using hlog256
    have hlog16 : Real.log 16 = 4 * Real.log 2 := by
      have h24 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      rw [h24, Real.log_pow]
      norm_num
    have hlog_diff : (1 / 2 : ℝ) * Real.log (1 / ε) ≤ Real.log (1 / ε) - Real.log 16 := by
      linarith
    have hm_ge : ((m + 1 : ℕ) : ℝ) / 2 ≤ (m : ℝ) := by
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      push_cast
      linarith
    have hterm1 : (1 / 4 : ℝ) * ((m + 1 : ℕ) : ℝ) * Real.log (1 / ε) ≤
        (m : ℝ) * (Real.log (1 / ε) - Real.log 16) := by
      have h0 : 0 ≤ Real.log (1 / ε) := by linarith
      calc (1 / 4 : ℝ) * ((m + 1 : ℕ) : ℝ) * Real.log (1 / ε)
        _ = (((m + 1 : ℕ) : ℝ) / 2) * ((1 / 2 : ℝ) * Real.log (1 / ε)) := by ring
        _ ≤ (m : ℝ) * ((1 / 2 : ℝ) * Real.log (1 / ε)) :=
            mul_le_mul_of_nonneg_right hm_ge (by linarith)
        _ ≤ (m : ℝ) * (Real.log (1 / ε) - Real.log 16) :=
            mul_le_mul_of_nonneg_left hlog_diff (Nat.cast_nonneg m)
    have hterm2 : -(1 / 16 : ℝ) * ((m + 1 : ℕ) : ℝ) * Real.log (1 / ε) ≤ Real.log (2 / 3) := by
      have hn2 : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn
      have h16log2 : 16 * Real.log 2 ≤ ((m + 1 : ℕ) : ℝ) * Real.log (1 / ε) := by
        calc 16 * Real.log 2
          _ = 2 * (8 * Real.log 2) := by ring
          _ ≤ ((m + 1 : ℕ) : ℝ) * (8 * Real.log 2) :=
              mul_le_mul_of_nonneg_right hn2 (by positivity)
          _ ≤ ((m + 1 : ℕ) : ℝ) * Real.log (1 / ε) :=
              mul_le_mul_of_nonneg_left hlog_inv_ε (by positivity)
      linarith
    have hcomb : (3 / 16 : ℝ) * ((m + 1 : ℕ) : ℝ) * Real.log (1 / ε) ≤ (q : ℝ) * Real.log 2 := by
      linarith
    calc 3 / (16 * Real.log 2) * ↑(m + 1) * Real.log (1 / ε)
      _ = ((3 / 16 : ℝ) * ((m + 1 : ℕ) : ℝ) * Real.log (1 / ε)) / Real.log 2 := by ring
      _ ≤ ((q : ℝ) * Real.log 2) / Real.log 2 := div_le_div_of_nonneg_right hcomb hlog2_pos.le
      _ = (q : ℝ) := mul_div_cancel_right₀ (q : ℝ) hlog2_pos.ne'
