-- Prove2me | solution 1 for PGDMap20261031.entropy_single_profile
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T17:14:30.866195+00:00
-- url     : https://prove2.me/submissions/3f5c2021-336a-42a3-a761-52e16876a1e3

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_PGDMap20261031_entropy_necessary_alternation
import Theorems.Thm_PGDMap20261031_entropy_error_lub
import Theorems.Thm_PGDMap20261031_entropy_error_monotone
import Theorems.Thm_PGDMap20261031_power_single_crossing
import Theorems.Thm_PGDMap20261031_power_threshold
import Definitions.Def_PGDMap20261031_Entropy

open PGDMap20261031 Set Filter
open scoped Topology
noncomputable section

private def skew (c t : ℝ) : ℝ :=
  (Real.rpow (1 - t) (-c) - Real.rpow (1 + t) (-c)) /
    (Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c))

private lemma curvature_pos (c t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    0 < powerCurvature c t := by
  unfold powerCurvature
  exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
    (Real.rpow_pos_of_pos (by linarith [ht.2]) _)) (by norm_num)

private lemma skew_nonneg_mono (c₁ c₂ t : ℝ) (hc₁ : 0 ≤ c₁) (hc : c₁ ≤ c₂)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) : 0 ≤ skew c₁ t ∧ skew c₁ t ≤ skew c₂ t := by
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hbase : 1 ≤ (1 + t) / (1 - t) := by
    apply (le_div_iff₀ hminus).2
    linarith [ht.1]
  have hratio (c : ℝ) :
      Real.rpow (1 - t) (-c) / Real.rpow (1 + t) (-c) =
        Real.rpow ((1 + t) / (1 - t)) c := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hminus.le, Real.rpow_neg hplus.le,
      inv_div_inv, Real.div_rpow hplus.le hminus.le]
  have ha₁ : 0 < Real.rpow (1 - t) (-c₁) := Real.rpow_pos_of_pos hminus _
  have hb₁ : 0 < Real.rpow (1 + t) (-c₁) := Real.rpow_pos_of_pos hplus _
  have ha₂ : 0 < Real.rpow (1 - t) (-c₂) := Real.rpow_pos_of_pos hminus _
  have hb₂ : 0 < Real.rpow (1 + t) (-c₂) := Real.rpow_pos_of_pos hplus _
  have hratio₁ : 1 ≤ Real.rpow (1 - t) (-c₁) / Real.rpow (1 + t) (-c₁) := by
    rw [hratio]
    simpa using Real.rpow_le_rpow_of_exponent_le hbase hc₁
  have hratios : Real.rpow (1 - t) (-c₁) / Real.rpow (1 + t) (-c₁) ≤
      Real.rpow (1 - t) (-c₂) / Real.rpow (1 + t) (-c₂) := by
    rw [hratio, hratio]
    exact Real.rpow_le_rpow_of_exponent_le hbase hc
  have horder := (le_div_iff₀ hb₁).mp hratio₁
  have hcross := (div_le_div_iff₀ hb₁ hb₂).mp hratios
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · unfold skew
    apply (div_le_div_iff₀ (add_pos ha₁ hb₁) (add_pos ha₂ hb₂)).2
    nlinarith only [hcross]

private lemma curvature_hasDerivAt (c t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivAt (powerCurvature c)
      (powerCurvature c t * (c * (t + skew c t)) / (1 - t ^ 2)) t := by
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hp := ((hasDerivAt_id t).const_add 1).rpow_const
    (Or.inl (ne_of_gt hplus) : 1 + t ≠ 0 ∨ 1 ≤ -c)
  have hm := ((hasDerivAt_id t).const_sub 1).rpow_const
    (Or.inl (ne_of_gt hminus) : 1 - t ≠ 0 ∨ 1 ≤ -c)
  have hsum : Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c) ≠ 0 :=
    ne_of_gt (add_pos (Real.rpow_pos_of_pos hminus _) (Real.rpow_pos_of_pos hplus _))
  have hden : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  convert (hp.add hm).div_const 2 using 1 <;> try rfl
  unfold powerCurvature skew
  simp only [id_eq, Real.rpow_eq_pow] at hsum ⊢
  rw [Real.rpow_sub_one (ne_of_gt hplus), Real.rpow_sub_one (ne_of_gt hminus)]
  field_simp [hsum, hden, ne_of_gt hplus, ne_of_gt hminus]
  <;> ring

private lemma skew_deriv (c t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (skew c) (c * (1 - skew c t ^ 2) / (1 - t ^ 2)) t := by
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hp := ((hasDerivAt_id t).const_add 1).rpow_const
    (Or.inl (ne_of_gt hplus) : 1 + t ≠ 0 ∨ 1 ≤ -c)
  have hm := ((hasDerivAt_id t).const_sub 1).rpow_const
    (Or.inl (ne_of_gt hminus) : 1 - t ≠ 0 ∨ 1 ≤ -c)
  have hsum : Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c) ≠ 0 :=
    ne_of_gt (add_pos (Real.rpow_pos_of_pos hminus _) (Real.rpow_pos_of_pos hplus _))
  have hden : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  convert (hm.sub hp).div (hm.add hp) hsum using 1 <;> try rfl
  unfold skew
  simp only [id_eq, Pi.sub_apply, Pi.add_apply, Real.rpow_eq_pow] at hsum ⊢
  rw [Real.rpow_sub_one (ne_of_gt hplus), Real.rpow_sub_one (ne_of_gt hminus)]
  field_simp [hsum, hden, ne_of_gt hplus, ne_of_gt hminus]
  <;> ring

private lemma skew_one (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : skew 1 t = t := by
  have hm : 1 - t ≠ 0 := ne_of_gt (by linarith [ht.2])
  have hp : 1 + t ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hsum : (1 - t)⁻¹ + (1 + t)⁻¹ ≠ 0 := ne_of_gt
    (add_pos (inv_pos.mpr (by linarith [ht.2])) (inv_pos.mpr (by linarith [ht.1])))
  unfold skew
  simp only [Real.rpow_eq_pow, Real.rpow_neg_one]
  field_simp [hm, hp, hsum]
  <;> ring

private lemma skew_zero (c : ℝ) : skew c 0 = 0 := by simp [skew]

private lemma skew_basic (c t : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ht : t ∈ Ico (0 : ℝ) 1) : 0 ≤ skew c t ∧ skew c t ≤ t := by
  obtain ⟨h0, h1⟩ := skew_nonneg_mono c 1 t hc0 hc1 ht
  rw [skew_one t ht] at h1
  exact ⟨h0, h1⟩

private def W (c t : ℝ) : ℝ :=
  ((1 - t) * Real.rpow (1 + t) (1 - c) +
    (1 + t) * Real.rpow (1 - t) (1 - c)) / 2

private def RR (M : EntropyMixture) (t : ℝ) : ℝ :=
  (1 - t ^ 2) * mixtureCurvature M t

private def EE (M : EntropyMixture) (c p t : ℝ) : ℝ :=
  (p * W c t - RR M t) / (p * W c t + M.lambda)

private lemma W_comp_cont {α : Type*} [TopologicalSpace α] {fc ft : α → ℝ} {x : α}
    (hc : ContinuousAt fc x) (ht : ContinuousAt ft x) (hc1 : fc x < 1) :
    ContinuousAt (fun z => W (fc z) (ft z)) x := by
  unfold W
  exact (((ht.const_sub 1).mul ((ht.const_add 1).rpow (hc.const_sub 1)
    (Or.inr (by simpa using sub_pos.mpr hc1)))).add
      ((ht.const_add 1).mul ((ht.const_sub 1).rpow (hc.const_sub 1)
        (Or.inr (by simpa using sub_pos.mpr hc1))))).div_const 2

private lemma W_value (c t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    W c t = (1 - t ^ 2) * powerCurvature c t := by
  have hp : 0 < 1 + t := by linarith [ht.1]
  have hm : 0 < 1 - t := by linarith [ht.2]
  have hr (v : ℝ) (hv : 0 < v) : Real.rpow v (1 - c) = v * Real.rpow v (-c) := by
    simp only [Real.rpow_eq_pow]
    rw [sub_eq_add_neg, Real.rpow_add hv, Real.rpow_one]
  dsimp [W, powerCurvature]
  simp only [Real.rpow_eq_pow] at hr
  rw [hr _ hp, hr _ hm]
  ring

private lemma W_nonneg (c t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ W c t := by
  unfold W
  exact div_nonneg (add_nonneg (mul_nonneg (by linarith [ht.2]) (Real.rpow_nonneg (by linarith [ht.1]) _))
    (mul_nonneg (by linarith [ht.1]) (Real.rpow_nonneg (by linarith [ht.2]) _))) (by norm_num)

private lemma W_pos (c t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : 0 < W c t := by
  rw [W_value c t ht]
  exact mul_pos (by nlinarith [ht.1, ht.2]) (curvature_pos c t ht)

private lemma W_zero (c : ℝ) : W c 0 = 1 := by simp [W]

private lemma W_one (c : ℝ) (hc1 : c < 1) : W c 1 = 0 := by
  simp [W, Real.zero_rpow (ne_of_gt (sub_pos.mpr hc1))]

private lemma scaled_den (M : EntropyMixture) (j : Fin M.m) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 < 1 - M.a j * t ^ 2 := by
  have htsq : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  nlinarith [M.a_pos j, M.a_lt_one j, sq_nonneg t]

private lemma A_cont (M : EntropyMixture) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (mixtureCurvature M) t := by
  unfold mixtureCurvature
  have hterm (j : Fin M.m) : ContinuousAt
      (fun s : ℝ => M.weight j * M.a j / (1 - M.a j * s ^ 2)) t :=
    continuousAt_const.div
      (continuousAt_const.sub (continuousAt_const.mul (continuousAt_id.pow 2)))
      (ne_of_gt (scaled_den M j t ht))
  generalize (Finset.univ : Finset (Fin M.m)) = s
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hterm i).add ih

private lemma RR_cont (M : EntropyMixture) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (RR M) t :=
  (continuousAt_const.sub (continuousAt_id.pow 2)).mul (A_cont M t ht)

private lemma EE_value (M : EntropyMixture) (c p t : ℝ) (hp : 0 < p)
    (ht : t ∈ Ico (0 : ℝ) 1) : EE M c p t = curvatureError M c p t := by
  have hs : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  rw [EE, W_value c t ht, RR]
  unfold curvatureError entropyCurvature
  field_simp [hs]
  <;> ring

private lemma EE_joint_cont (M : EntropyMixture) (c p t : ℝ) (hc1 : c < 1) (hp : 0 < p)
    (ht : t ∈ Icc (0 : ℝ) 1) : ContinuousAt
      (fun z : (ℝ × ℝ) × ℝ => EE M z.1.1 z.1.2 z.2) ((c, p), t) := by
  have hW : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => W z.1.1 z.2) ((c, p), t) :=
    W_comp_cont (continuousAt_fst.fst) continuousAt_snd hc1
  have hRR : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => RR M z.2) ((c, p), t) := by
    exact (RR_cont M t ht).comp_of_eq
      (f := fun z : (ℝ × ℝ) × ℝ => z.2) continuousAt_snd rfl
  have hd : 0 < p * W c t + M.lambda :=
    add_pos_of_nonneg_of_pos (mul_nonneg hp.le (W_nonneg c t ht)) M.lambda_pos
  exact ((continuousAt_fst.snd.mul hW).sub hRR).div
    ((continuousAt_fst.snd.mul hW).add continuousAt_const) (ne_of_gt hd)

private lemma EE_one (M : EntropyMixture) (c p : ℝ) (hc1 : c < 1) : EE M c p 1 = 0 := by
  simp [EE, RR, W_one c hc1]

private lemma profile_bound_closed (M : EntropyMixture) (c p : ℝ)
    (hv : validGeometry (c, p)) (hc1 : c < 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, |EE M c p t| ≤ contraction M c p := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · subst t
    rw [EE_one M c p hc1, abs_zero]
    exact le_trans (abs_nonneg _) ((entropy_error_lub M c p hv).1
      ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩)
  · rw [EE_value M c p t hv.2.2 ⟨ht.1, hlt⟩]
    exact (entropy_error_lub M c p hv).1 ⟨t, ⟨ht.1, hlt⟩, rfl⟩

private lemma W_deriv (c t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (W c) (powerCurvature c t * (c * (t + skew c t) - 2 * t)) t := by
  have heq : W c =ᶠ[𝓝 t] (fun s => (1 - s ^ 2) * powerCurvature c s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact W_value c s ⟨hs.1.le, hs.2⟩
  apply heq.hasDerivAt_iff.mpr
  convert (((hasDerivAt_id t).pow 2).const_sub 1).mul
    (curvature_hasDerivAt c t ⟨ht.1.le, ht.2⟩) using 1 <;> try rfl
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by omega,
    pow_one, mul_one]
  field_simp [ne_of_gt (show 0 < 1 - t ^ 2 by nlinarith [ht.1, ht.2])]
  <;> ring

private lemma W_decreasing (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    StrictAntiOn (W c) (Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · intro t _
    exact (W_comp_cont continuousAt_const continuousAt_id hc1).continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(W_deriv c t ht).deriv]
    have hs := skew_basic c t hc0 hc1.le ⟨ht.1.le, ht.2⟩
    have hle := mul_le_mul_of_nonneg_left (show t + skew c t ≤ 2 * t by linarith) hc0
    have hlt := mul_lt_mul_of_pos_right hc1 (show 0 < 2 * t by linarith [ht.1])
    exact mul_neg_of_pos_of_neg (curvature_pos c t ⟨ht.1.le, ht.2⟩) (by nlinarith)

private lemma A0pos (M : EntropyMixture) : 0 < curvatureAtZero M := by
  unfold curvatureAtZero
  exact Finset.sum_pos (fun j _ => mul_pos (M.weight_pos j) (M.a_pos j))
    ⟨⟨0, M.m_pos⟩, Finset.mem_univ _⟩

private lemma A_zero (M : EntropyMixture) : mixtureCurvature M 0 = curvatureAtZero M := by
  simp [mixtureCurvature, curvatureAtZero]

private lemma RR_zero (M : EntropyMixture) : RR M 0 = curvatureAtZero M := by
  simp [RR, A_zero]

private lemma RR_one (M : EntropyMixture) : RR M 1 = 0 := by simp [RR]

private lemma RR_sum (M : EntropyMixture) (t : ℝ) :
    RR M t = ∑ j, M.weight j * M.a j * (1 - t ^ 2) / (1 - M.a j * t ^ 2) := by
  unfold RR mixtureCurvature
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma RR_decreasing (M : EntropyMixture) : StrictAntiOn (RR M) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [RR_sum, RR_sum]
  have hsq : x ^ 2 < y ^ 2 := by simpa only [sq] using mul_self_lt_mul_self hx.1 hxy
  have hterm (j : Fin M.m) :
      M.weight j * M.a j * (1 - y ^ 2) / (1 - M.a j * y ^ 2) <
      M.weight j * M.a j * (1 - x ^ 2) / (1 - M.a j * x ^ 2) := by
    apply (div_lt_div_iff₀ (scaled_den M j y hy) (scaled_den M j x hx)).2
    have hpos := mul_pos (mul_pos (mul_pos (M.weight_pos j) (M.a_pos j))
      (sub_pos.mpr (M.a_lt_one j))) (sub_pos.mpr hsq)
    nlinarith only [hpos]
  apply Finset.sum_lt_sum (fun j _ => (hterm j).le)
  exact ⟨⟨0, M.m_pos⟩, Finset.mem_univ _, hterm _⟩

private lemma E_positive_V (M : EntropyMixture) (c p t : ℝ) (hp : 0 < p)
    (ht : t ∈ Ico (0 : ℝ) 1) (he : 0 < curvatureError M c p t) :
    mixtureCurvature M t / powerCurvature c t < p := by
  have hk := curvature_pos c t ht
  have hd : 0 < p * powerCurvature c t + entropyCurvature M t :=
    add_pos (mul_pos hp hk) (div_pos M.lambda_pos (by nlinarith [ht.1, ht.2]))
  have hnum := (lt_div_iff₀ hd).mp he
  apply (div_lt_iff₀ hk).2
  linarith

private lemma E_negative_V (M : EntropyMixture) (c p t : ℝ) (hp : 0 < p)
    (ht : t ∈ Ico (0 : ℝ) 1) (he : curvatureError M c p t < 0) :
    p < mixtureCurvature M t / powerCurvature c t := by
  have hk := curvature_pos c t ht
  have hd : 0 < p * powerCurvature c t + entropyCurvature M t :=
    add_pos (mul_pos hp hk) (div_pos M.lambda_pos (by nlinarith [ht.1, ht.2]))
  have hnum := (div_lt_iff₀ hd).mp he
  apply (lt_div_iff₀ hk).2
  linarith

private lemma RR_bounds (M : EntropyMixture) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ RR M t ∧ RR M t ≤ curvatureAtZero M := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hlo := (RR_decreasing M).antitoneOn ht h1 ht.2
  have hhi := (RR_decreasing M).antitoneOn h0 ht ht.1
  rw [RR_one] at hlo
  rw [RR_zero] at hhi
  exact ⟨hlo, hhi⟩

private lemma threshold_bounds (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    0 < threshold a ∧ threshold a < 1 := by
  have hs := Real.sqrt_nonneg (1 + 8 * a)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + 8 * a by linarith)
  unfold threshold
  constructor <;> nlinarith

private lemma candidate_curvature (M : EntropyMixture) :
    ∃ c ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      RR M t ≤ curvatureAtZero M * W c t := by
  obtain ⟨jmax, _, hmax⟩ := Finset.exists_max_image Finset.univ M.a
    ⟨⟨0, M.m_pos⟩, Finset.mem_univ _⟩
  let a := M.a jmax
  let c := threshold a
  have ha : 0 < a := M.a_pos jmax
  have ha1 : a < 1 := M.a_lt_one jmax
  have hc : c ∈ Ioo (0 : ℝ) 1 := threshold_bounds a ha ha1
  refine ⟨c, hc, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · subst t
    rw [RR_one, W_one c hc.2, mul_zero]
  · have htsq : t ^ 2 ∈ Ico (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [ht.1, hlt]⟩
    have hqmono := (power_threshold a c ha ha1 hc.1 hc.2).1 le_rfl
    have hq : 1 ≤ (1 - a * t ^ 2) * powerCurvature c t := by
      have hge := hqmono.monotoneOn ⟨le_rfl, by norm_num⟩ htsq (sq_nonneg t)
      simpa [thresholdProfile, powerCurvature, Real.sqrt_sq ht.1] using hge
    have hden : 0 < 1 - a * t ^ 2 := scaled_den M jmax t ht
    have hAbound : mixtureCurvature M t ≤ curvatureAtZero M / (1 - a * t ^ 2) := by
      unfold mixtureCurvature curvatureAtZero
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro j _
      apply (div_le_div_iff₀ (scaled_den M j t ht) hden).2
      have horder := hmax j (Finset.mem_univ j)
      have hprod := mul_nonneg (mul_nonneg (mul_pos (M.weight_pos j) (M.a_pos j)).le
        (sq_nonneg t)) (sub_nonneg.mpr horder)
      dsimp [a] at *
      nlinarith only [hprod]
    have hAk : mixtureCurvature M t ≤ curvatureAtZero M * powerCurvature c t := by
      have hk : 1 / (1 - a * t ^ 2) ≤ powerCurvature c t := (div_le_iff₀ hden).2 (by nlinarith [hq])
      have hmul := mul_le_mul_of_nonneg_left hk (A0pos M).le
      exact le_trans hAbound (by simpa only [mul_one_div] using hmul)
    rw [W_value c t ⟨ht.1, hlt⟩, RR]
    have hs : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, hlt]
    nlinarith [mul_le_mul_of_nonneg_left hAk hs]

private lemma W_le_one (c t : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : W c t ≤ 1 := by
  have h := (W_decreasing c hc0 hc1).antitoneOn
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩) ht ht.1
  simpa only [W_zero] using h

private lemma negative_envelope (M : EntropyMixture) (c p : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hp : 0 < p) (hpA : p ≤ curvatureAtZero M)
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1, RR M t ≤ curvatureAtZero M * W c t) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      -(curvatureAtZero M - p) / (p + M.lambda) ≤ EE M c p t := by
  intro t ht
  have hW := W_nonneg c t ht
  have hW1 := W_le_one c t hc0 hc1 ht
  have hd : 0 < p * W c t + M.lambda :=
    add_pos_of_nonneg_of_pos (mul_nonneg hp.le hW) M.lambda_pos
  unfold EE
  apply (div_le_div_iff₀ (add_pos hp M.lambda_pos) hd).2
  have hR := mul_le_mul_of_nonneg_right (hdom t ht) (add_pos hp M.lambda_pos).le
  have hprod := mul_nonneg (mul_nonneg M.lambda_pos.le (sub_nonneg.mpr hpA))
    (sub_nonneg.mpr hW1)
  nlinarith only [hR, hprod]

private lemma strict_candidate (M : EntropyMixture) :
    ∃ c p : ℝ, validGeometry (c, p) ∧ c < 1 ∧ contraction M c p < entropyBaseline M := by
  obtain ⟨c, hc, hdom⟩ := candidate_curvature M
  let p0 := curvatureAtZero M / 2
  have hp0 : 0 < p0 := by dsimp [p0]; positivity [A0pos M]
  have hbase : 0 < entropyBaseline M := div_pos (A0pos M)
    (add_pos (A0pos M) (mul_pos (by norm_num) M.lambda_pos))
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : EE M c p0 t < entropyBaseline M := by
    by_cases ht0 : t = 0
    · subst t
      have heq : EE M c p0 0 = -entropyBaseline M := by
        rw [EE, W_zero, RR_zero]
        dsimp [p0, entropyBaseline]
        field_simp
        <;> ring
      rw [heq]
      linarith
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hWlt : W c t < 1 := by
        have h := (W_decreasing c hc.1.le hc.2)
          (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩) ht htpos
        simpa only [W_zero] using h
      have hW := W_nonneg c t ht
      have hd : 0 < p0 * W c t + M.lambda :=
        add_pos_of_nonneg_of_pos (mul_nonneg hp0.le hW) M.lambda_pos
      have hden : 0 < curvatureAtZero M + 2 * M.lambda := by positivity [A0pos M, M.lambda_pos]
      unfold EE entropyBaseline
      apply (div_lt_div_iff₀ hd hden).2
      have hR := (RR_bounds M t ht).1
      have hRmul := mul_nonneg hR hden.le
      have hgap := mul_pos (mul_pos (A0pos M) M.lambda_pos) (sub_pos.mpr hWlt)
      dsimp [p0] at *
      nlinarith only [hgap, hRmul]
  have hevent : ∀ᶠ p in 𝓝 p0, ∀ t ∈ Icc (0 : ℝ) 1, EE M c p t < entropyBaseline M := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hcont : ContinuousAt (fun z : ℝ × ℝ => EE M c z.1 z.2) (p0, t) := by
      exact (EE_joint_cont M c p0 t hc.2 hp0 ht).comp_of_eq
        (f := fun z : ℝ × ℝ => ((c, z.1), z.2))
        ((continuousAt_const.prodMk continuousAt_fst).prodMk continuousAt_snd) rfl
    exact hcont.preimage_mem_nhds (Iio_mem_nhds (hpos t ht))
  have hevent' : ∀ᶠ p in 𝓝[>] p0, ∀ t ∈ Icc (0 : ℝ) 1, EE M c p t < entropyBaseline M :=
    hevent.filter_mono nhdsWithin_le_nhds
  have hltA : p0 < curvatureAtZero M := by dsimp [p0]; linarith [A0pos M]
  have hpAevent : ∀ᶠ p in 𝓝[>] p0, p < curvatureAtZero M :=
    (show ∀ᶠ p in 𝓝 p0, p < curvatureAtZero M from Iio_mem_nhds hltA).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨p, hposp, hpA, hpgt⟩ := (hevent'.and (hpAevent.and self_mem_nhdsWithin)).exists
  have hp : 0 < p := lt_trans hp0 hpgt
  have hneg := negative_envelope M c p hc.1.le hc.2 hp hpA.le hdom
  have hnegbetter : -(curvatureAtZero M - p) / (p + M.lambda) > -entropyBaseline M := by
    have hd : 0 < p + M.lambda := add_pos hp M.lambda_pos
    have hden : 0 < curvatureAtZero M + 2 * M.lambda := by positivity [A0pos M, M.lambda_pos]
    unfold entropyBaseline
    rw [neg_div]
    apply neg_lt_neg
    apply (div_lt_div_iff₀ hd hden).2
    dsimp [p0] at hpgt
    have hgap := mul_pos (show 0 < 2 * p - curvatureAtZero M by linarith) (A0pos M)
    have hgap' := mul_pos (show 0 < 2 * p - curvatureAtZero M by linarith) M.lambda_pos
    nlinarith
  have hcont : ContinuousOn (fun t => |EE M c p t|) (Icc (0 : ℝ) 1) := by
    intro t ht
    have hct : ContinuousAt (fun s => EE M c p s) t := by
      exact (EE_joint_cont M c p t hc.2 hp ht).comp_of_eq
        (f := fun s : ℝ => ((c, p), s)) (continuousAt_const.prodMk continuousAt_id) rfl
    exact hct.abs.continuousWithinAt
  obtain ⟨tmax, htmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, le_rfl, by norm_num⟩) hcont
  have hmaxlt : |EE M c p tmax| < entropyBaseline M :=
    abs_lt.mpr ⟨lt_of_lt_of_le hnegbetter (hneg tmax htmax), hposp tmax htmax⟩
  have hv : validGeometry (c, p) := ⟨hc.1.le, by linarith [hc.2], hp⟩
  refine ⟨c, p, hv, hc.2, lt_of_le_of_lt ?_ hmaxlt⟩
  apply (entropy_error_lub M c p hv).2
  rintro v ⟨t, ht, rfl⟩
  rw [← EE_value M c p t hp ht]
  exact hmax ⟨ht.1, ht.2.le⟩

private lemma near_one : ∀ᶠ t : ℝ in 𝓝[<] 1, t ∈ Ico (0 : ℝ) 1 := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t :=
    (show ∀ᶠ t : ℝ in 𝓝 1, 0 < t from Ioi_mem_nhds (by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with t ht ht1
  exact ⟨ht.le, ht1⟩

private lemma one_sub_tendsto : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hid : Tendsto (fun t : ℝ => t) (𝓝[<] 1) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa only [sub_self] using hid.const_sub 1
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change t < 1 at ht
    exact sub_pos.mpr ht

private lemma W_unbounded (c : ℝ) (hc : 1 < c) : Tendsto (W c) (𝓝[<] 1) atTop := by
  have hr := (tendsto_rpow_neg_nhdsGT_zero (show 1 - c < 0 by linarith)).comp one_sub_tendsto
  have hrl : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.rpow (1 - t) (1 - c)) (𝓝[<] 1) atTop :=
    hr.const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' _ _ hrl
  filter_upwards [near_one] with t ht
  have hp : 0 ≤ Real.rpow (1 + t) (1 - c) := Real.rpow_nonneg (by linarith [ht.1]) _
  have hm : 0 ≤ Real.rpow (1 - t) (1 - c) := Real.rpow_nonneg (by linarith [ht.2]) _
  dsimp [W]
  simp only [Real.rpow_eq_pow] at hp hm
  nlinarith [mul_nonneg (show 0 ≤ 1 - t by linarith [ht.2]) hp,
    mul_nonneg ht.1 hm]

private lemma k_unbounded (c : ℝ) (hc : 0 < c) :
    Tendsto (powerCurvature c) (𝓝[<] 1) atTop := by
  have hr := (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hc)).comp one_sub_tendsto
  have hrl : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.rpow (1 - t) (-c)) (𝓝[<] 1) atTop :=
    hr.const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' _ _ hrl
  filter_upwards [near_one] with t ht
  dsimp [powerCurvature]
  linarith [Real.rpow_nonneg (show 0 ≤ 1 + t by linarith [ht.1]) (-c)]

private lemma A_increasing (M : EntropyMixture) :
    StrictMonoOn (mixtureCurvature M) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  unfold mixtureCurvature
  have hsq : x ^ 2 < y ^ 2 := by simpa only [sq] using mul_self_lt_mul_self hx.1 hxy
  have hterm (j : Fin M.m) :
      M.weight j * M.a j / (1 - M.a j * x ^ 2) <
      M.weight j * M.a j / (1 - M.a j * y ^ 2) := by
    apply (div_lt_div_iff₀ (scaled_den M j x hx) (scaled_den M j y hy)).2
    have hp := mul_pos (mul_pos (mul_pos (M.weight_pos j) (M.a_pos j)) (M.a_pos j))
      (sub_pos.mpr hsq)
    nlinarith only [hp]
  apply Finset.sum_lt_sum (fun j _ => (hterm j).le)
  exact ⟨⟨0, M.m_pos⟩, Finset.mem_univ _, hterm _⟩

private lemma A_one (M : EntropyMixture) : mixtureCurvature M 1 = curvatureAtBoundary M := by
  simp [mixtureCurvature, curvatureAtBoundary]

private lemma contraction_pos (M : EntropyMixture) (c p : ℝ) (hv : validGeometry (c, p)) :
    0 < contraction M c p := by
  have hr0 : 0 ≤ contraction M c p := le_trans (abs_nonneg _) ((entropy_error_lub M c p hv).1
    ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩)
  by_contra hn
  have hr : contraction M c p = 0 := le_antisymm (le_of_not_gt hn) hr0
  have hmatch (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : p * powerCurvature c t = mixtureCurvature M t := by
    have he := (entropy_error_lub M c p hv).1 ⟨t, ht, rfl⟩
    rw [hr] at he
    have hezero : curvatureError M c p t = 0 := abs_eq_zero.mp
      (le_antisymm he (abs_nonneg _))
    have hd : 0 < p * powerCurvature c t + entropyCurvature M t :=
      add_pos (mul_pos hv.2.2 (curvature_pos c t ht))
        (div_pos M.lambda_pos (by nlinarith [ht.1, ht.2]))
    have hn := (div_eq_iff (ne_of_gt hd)).mp hezero
    linarith
  rcases eq_or_lt_of_le hv.1 with hc | hc
  · have hc0 : c = 0 := hc.symm
    have hm0 := hmatch 0 ⟨le_rfl, by norm_num⟩
    have hmhalf := hmatch (1 / 2) ⟨by norm_num, by norm_num⟩
    simp [hc0, powerCurvature, Real.rpow_eq_pow] at hm0 hmhalf
    have hlt := A_increasing M (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩)
      (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, by norm_num⟩) (by norm_num)
    linarith
  · have hevent := (k_unbounded c hc).eventually_gt_atTop (curvatureAtBoundary M / p)
    obtain ⟨t, ht, hgt⟩ := (near_one.and hevent).exists
    have hmatcht := hmatch t ht
    have hAbound := (A_increasing M).monotoneOn ⟨ht.1, ht.2.le⟩
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, le_rfl⟩) ht.2.le
    rw [A_one] at hAbound
    have hpgt := (div_lt_iff₀ hv.2.2).mp hgt
    nlinarith

private lemma small_contraction_power (M : EntropyMixture) (c p : ℝ)
    (hv : validGeometry (c, p)) (hr : contraction M c p < 1) : c ≤ 1 := by
  by_contra hn
  let r := contraction M c p
  let C := (curvatureAtZero M + r * M.lambda) / (p * (1 - r))
  have hpr : 0 < p * (1 - r) := mul_pos hv.2.2 (sub_pos.mpr hr)
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : W c t ≤ C := by
    have hd : 0 < p * W c t + M.lambda :=
      add_pos (mul_pos hv.2.2 (W_pos c t ht)) M.lambda_pos
    have he := (abs_le.mp ((entropy_error_lub M c p hv).1 ⟨t, ht, rfl⟩)).2
    rw [← EE_value M c p t hv.2.2 ht] at he
    have hexp := (div_le_iff₀ hd).mp he
    have hR := (RR_bounds M t ⟨ht.1, ht.2.le⟩).2
    apply (le_div_iff₀ hpr).2
    dsimp [r] at *
    nlinarith
  have hlarge := (W_unbounded c (lt_of_not_ge hn)).eventually_gt_atTop C
  obtain ⟨t, ht, hgt⟩ := (near_one.and hlarge).exists
  exact (not_lt_of_ge (hbound t ht)) hgt

private lemma W_entropy (t : ℝ) : W 1 t = 1 := by
  simp [W, Real.rpow_eq_pow]

private lemma EE_zero (M : EntropyMixture) (c p : ℝ) :
    EE M c p 0 = (p - curvatureAtZero M) / (p + M.lambda) := by
  rw [EE, W_zero, RR_zero, mul_one]

private lemma entropy_boundary_bound (M : EntropyMixture) (p : ℝ) (hp : 0 < p) :
    p / (p + M.lambda) ≤ contraction M 1 p := by
  have hcont : ContinuousAt (fun t => (p - RR M t) / (p + M.lambda)) 1 :=
    (continuousAt_const.sub (RR_cont M 1 ⟨by norm_num, le_rfl⟩)).div_const _
  have hlim : Tendsto (fun t => EE M 1 p t) (𝓝[<] (1 : ℝ)) (𝓝 (p / (p + M.lambda))) := by
    have ht : Tendsto (fun t => (p - RR M t) / (p + M.lambda)) (𝓝[<] (1 : ℝ))
        (𝓝 ((p - RR M 1) / (p + M.lambda))) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [EE, W_entropy, mul_one, RR_one, sub_zero] using ht
  apply le_of_tendsto hlim
  filter_upwards [near_one] with t ht
  rw [EE_value M 1 p t hp ht]
  exact le_trans (le_abs_self _) ((entropy_error_lub M 1 p
    ⟨by norm_num, by norm_num, hp⟩).1 ⟨t, ht, rfl⟩)

private lemma entropy_lower (M : EntropyMixture) (p : ℝ) (hp : 0 < p)
    (hr1 : contraction M 1 p < 1) : entropyBaseline M ≤ contraction M 1 p := by
  let r := contraction M 1 p
  have hr0 : 0 ≤ r := (contraction_pos M 1 p ⟨by norm_num, by norm_num, hp⟩).le
  have hd : 0 < p + M.lambda := add_pos hp M.lambda_pos
  have h1 : p ≤ r * (p + M.lambda) := (div_le_iff₀ hd).mp (entropy_boundary_bound M p hp)
  have h0 : curvatureAtZero M - p ≤ r * (p + M.lambda) := by
    have he := (abs_le.mp ((entropy_error_lub M 1 p
      ⟨by norm_num, by norm_num, hp⟩).1 ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩)).1
    rw [← EE_value M 1 p 0 hp ⟨le_rfl, by norm_num⟩, EE_zero] at he
    have he' := (le_div_iff₀ hd).mp he
    dsimp [r] at *
    nlinarith
  have hmul0 := mul_nonneg (sub_nonneg.mpr hr1.le)
    (sub_nonneg.mpr h0)
  have hmul1 := mul_nonneg (show 0 ≤ 1 + r by linarith) (sub_nonneg.mpr h1)
  unfold entropyBaseline
  apply (div_le_iff₀ (show 0 < curvatureAtZero M + 2 * M.lambda by
    positivity [A0pos M, M.lambda_pos])).2
  dsimp [r] at *
  nlinarith

private lemma baseline_lt_one (M : EntropyMixture) : entropyBaseline M < 1 := by
  unfold entropyBaseline
  apply (div_lt_one (show 0 < curvatureAtZero M + 2 * M.lambda by
    positivity [A0pos M, M.lambda_pos])).2
  linarith [M.lambda_pos]

private lemma optimum_basic (M : EntropyMixture) (z : ℝ × ℝ) (hz : IsGeometryOptimum M z) :
    z.1 < 1 ∧ 0 < contraction M z.1 z.2 ∧ contraction M z.1 z.2 < entropyBaseline M := by
  obtain ⟨c, p, hv, _, hr⟩ := strict_candidate M
  have hsmall : contraction M z.1 z.2 < entropyBaseline M := lt_of_le_of_lt (hz.2 (c, p) hv) hr
  have hsmall1 := lt_trans hsmall (baseline_lt_one M)
  have hc := small_contraction_power M z.1 z.2 hz.1 hsmall1
  have hcne : z.1 ≠ 1 := by
    intro heq
    have hlow := entropy_lower M z.2 hz.1.2.2 (by simpa only [← heq] using hsmall1)
    rw [← heq] at hlow
    exact (not_lt_of_ge hlow) hsmall
  exact ⟨lt_of_le_of_ne hc hcne, contraction_pos M z.1 z.2 hz.1, hsmall⟩

private lemma EE_cont_state (M : EntropyMixture) (c p : ℝ) (hc1 : c < 1) (hp : 0 < p) :
    ContinuousOn (EE M c p) (Icc (0 : ℝ) 1) := by
  intro t ht
  have hct : ContinuousAt (fun s => EE M c p s) t := by
    exact (EE_joint_cont M c p t hc1 hp ht).comp_of_eq
      (f := fun s : ℝ => ((c, p), s)) (continuousAt_const.prodMk continuousAt_id) rfl
  exact hct.continuousWithinAt

private lemma profile_strict (M : EntropyMixture) (c p r : ℝ) (hv : validGeometry (c, p))
    (hc1 : c < 1) (hstrict : ∀ t ∈ Icc (0 : ℝ) 1, |EE M c p t| < r) :
    contraction M c p < r := by
  obtain ⟨tmax, htmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, le_rfl, by norm_num⟩)
    (EE_cont_state M c p hc1 hv.2.2).abs
  apply lt_of_le_of_lt _ (hstrict tmax htmax)
  apply (entropy_error_lub M c p hv).2
  rintro v ⟨t, ht, rfl⟩
  rw [← EE_value M c p t hv.2.2 ht]
  exact hmax ⟨ht.1, ht.2.le⟩

private lemma uniform_open (M : EntropyMixture) (c p σ r : ℝ) (hc1 : c < 1) (hp : 0 < p)
    (K : Set ℝ) (hK : IsCompact K) (hsub : K ⊆ Icc (0 : ℝ) 1)
    (hstrict : ∀ t ∈ K, σ * EE M c p t < r) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 (c, p), ∀ t ∈ K, σ * EE M z.1 z.2 t < r := by
  apply hK.eventually_forall_of_forall_eventually
  intro t ht
  have hc := (EE_joint_cont M c p t hc1 hp (hsub ht)).const_mul σ
  exact hc.preimage_mem_nhds (Iio_mem_nhds (hstrict t ht))

private lemma EE_step_strict (M : EntropyMixture) (c p q t : ℝ)
    (hp : 0 < p) (hpq : p < q) (ht : t ∈ Ico (0 : ℝ) 1) :
    EE M c p t < EE M c q t := by
  have hRR : 0 < RR M t := by
    have h := (RR_decreasing M) ⟨ht.1, ht.2.le⟩
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, le_rfl⟩) ht.2
    simpa only [RR_one] using h
  have hW := W_pos c t ht
  exact (entropy_error_monotone (RR M t) M.lambda hRR M.lambda_pos)
    (mul_pos hp hW) (mul_pos (lt_trans hp hpq) hW) (mul_lt_mul_of_pos_right hpq hW)

private lemma both_signs (M : EntropyMixture) (c p : ℝ) (hopt : IsGeometryOptimum M (c, p))
    (hc1 : c < 1) (hr : 0 < contraction M c p) :
    (∃ t ∈ Icc (0 : ℝ) 1, EE M c p t = contraction M c p) ∧
    (∃ t ∈ Icc (0 : ℝ) 1, EE M c p t = -contraction M c p) := by
  let r := contraction M c p
  have hp : 0 < p := hopt.1.2.2
  have hb := profile_bound_closed M c p hopt.1 hc1
  have hparam : Tendsto (fun q : ℝ => (c, q)) (𝓝 p) (𝓝 (c, p)) :=
    (show ContinuousAt (fun q : ℝ => (c, q)) p from
      continuousAt_const.prodMk continuousAt_id).tendsto
  constructor
  · by_contra hn
    have hpos : ∀ t ∈ Icc (0 : ℝ) 1, (1 : ℝ) * EE M c p t < r := by
      intro t ht
      have he : EE M c p t ≠ r := by intro he; exact hn ⟨t, ht, he⟩
      have hle := (abs_le.mp (hb t ht)).2
      simpa only [one_mul] using lt_of_le_of_ne hle he
    have hevent := hparam.eventually (uniform_open M c p 1 r hc1 hp _ isCompact_Icc
      (fun _ h => h) hpos)
    have hevent' : ∀ᶠ q in 𝓝[>] p, ∀ t ∈ Icc (0 : ℝ) 1, EE M c q t < r := by
      simpa only [one_mul] using hevent.filter_mono (nhdsWithin_le_nhds (s := Ioi p))
    obtain ⟨q, hqpos, hpq⟩ := (hevent'.and self_mem_nhdsWithin).exists
    have hq : 0 < q := lt_trans hp hpq
    have hnew : contraction M c q < r := by
      apply profile_strict M c q r ⟨hopt.1.1, hopt.1.2.1, hq⟩ hc1
      intro t ht
      refine abs_lt.mpr ⟨?_, hqpos t ht⟩
      rcases eq_or_lt_of_le ht.2 with ht1 | ht1
      · subst t
        rw [EE_one M c q hc1]
        linarith
      · exact lt_of_le_of_lt (abs_le.mp (hb t ht)).1
          (EE_step_strict M c p q t hp hpq ⟨ht.1, ht1⟩)
    exact (not_lt_of_ge (hopt.2 (c, q) ⟨hopt.1.1, hopt.1.2.1, hq⟩)) hnew


  · by_contra hn
    have hneg : ∀ t ∈ Icc (0 : ℝ) 1, (-1 : ℝ) * EE M c p t < r := by
      intro t ht
      have he : EE M c p t ≠ -r := by intro he; exact hn ⟨t, ht, he⟩
      have hle := (abs_le.mp (hb t ht)).1
      have hlt : -r < EE M c p t := lt_of_le_of_ne hle (Ne.symm he)
      nlinarith
    have hevent := hparam.eventually (uniform_open M c p (-1) r hc1 hp _ isCompact_Icc
      (fun _ h => h) hneg)
    have hevent' : ∀ᶠ q in 𝓝[<] p, ∀ t ∈ Icc (0 : ℝ) 1, -r < EE M c q t := by
      have ht : ∀ᶠ q in 𝓝[<] p, ∀ t ∈ Icc (0 : ℝ) 1, (-1 : ℝ) * EE M c q t < r :=
        hevent.filter_mono nhdsWithin_le_nhds
      filter_upwards [ht] with q hq t ht
      nlinarith [hq t ht]
    have hqposevent : ∀ᶠ q in 𝓝[<] p, 0 < q :=
      (show ∀ᶠ q in 𝓝 p, 0 < q from Ioi_mem_nhds hp).filter_mono nhdsWithin_le_nhds
    obtain ⟨q, hqneg, hq, hqp⟩ := (hevent'.and (hqposevent.and self_mem_nhdsWithin)).exists
    have hnew : contraction M c q < r := by
      apply profile_strict M c q r ⟨hopt.1.1, hopt.1.2.1, hq⟩ hc1
      intro t ht
      refine abs_lt.mpr ⟨hqneg t ht, ?_⟩
      rcases eq_or_lt_of_le ht.2 with ht1 | ht1
      · subst t
        rw [EE_one M c q hc1]
        exact hr
      · exact lt_of_lt_of_le (EE_step_strict M c q p t hq hqp ⟨ht.1, ht1⟩)
          (abs_le.mp (hb t ht)).2
    exact (not_lt_of_ge (hopt.2 (c, q) ⟨hopt.1.1, hopt.1.2.1, hq⟩)) hnew


private def normalizedP (c p u d : ℝ) : ℝ :=
  p * powerCurvature c u / powerCurvature d u

private lemma normalized_at (c p u : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) :
    normalizedP c p u c = p := by
  unfold normalizedP
  exact mul_div_cancel_right₀ p (ne_of_gt (curvature_pos c u hu))

private lemma normalized_cont (c p u : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun d => (d, normalizedP c p u d)) (𝓝 c) (𝓝 (c, p)) := by
  have hpbase : 0 < 1 + u := by linarith [hu.1]
  have hmbase : 0 < 1 - u := by linarith [hu.2]
  have hkp : ContinuousAt (fun d : ℝ => powerCurvature d u) c := by
    unfold powerCurvature
    exact ((continuousAt_const.rpow continuousAt_id.neg (Or.inl (ne_of_gt hpbase))).add
      (continuousAt_const.rpow continuousAt_id.neg (Or.inl (ne_of_gt hmbase)))).div_const 2
  have hpn : ContinuousAt (normalizedP c p u) c :=
    continuousAt_const.div hkp (ne_of_gt (curvature_pos c u hu))
  have ht := (continuousAt_id.prodMk hpn).tendsto
  simpa only [normalized_at c p u hu, id_eq] using ht

private lemma normalized_positive (c p u d : ℝ) (hp : 0 < p)
    (hu : u ∈ Ico (0 : ℝ) 1) : 0 < normalizedP c p u d :=
  div_pos (mul_pos hp (curvature_pos c u hu)) (curvature_pos d u hu)

private lemma normalized_contact (c p u d : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) :
    normalizedP c p u d * powerCurvature d u = p * powerCurvature c u := by
  exact div_mul_cancel₀ _ (ne_of_gt (curvature_pos d u hu))

private lemma scaled_relative (c p d q u : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (hcd : c < d)
    (hd : d ≤ 2) (hu : u ∈ Ico (0 : ℝ) 1)
    (heq : q * powerCurvature d u = p * powerCurvature c u) :
    (∀ t ∈ Ico (0 : ℝ) 1, t < u → q * powerCurvature d t < p * powerCurvature c t) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, u < t → p * powerCurvature c t < q * powerCurvature d t) := by
  have hm := power_single_crossing c d hc hcd hd
  constructor
  · intro t ht htu
    have hr := (div_lt_div_iff₀ (curvature_pos c t ht) (curvature_pos c u hu)).mp (hm ht hu htu)
    have hrp := mul_lt_mul_of_pos_left hr hp
    have he := congrArg (fun v : ℝ => v * powerCurvature d t) heq
    apply (mul_lt_mul_iff_of_pos_left (curvature_pos d u hu)).mp
    nlinarith only [hrp, he]
  · intro t ht hut
    have hr := (div_lt_div_iff₀ (curvature_pos c u hu) (curvature_pos c t ht)).mp (hm hu ht hut)
    have hrp := mul_lt_mul_of_pos_left hr hp
    have he := congrArg (fun v : ℝ => v * powerCurvature d t) heq
    apply (mul_lt_mul_iff_of_pos_left (curvature_pos d u hu)).mp
    nlinarith only [hrp, he]

private lemma EE_scaled_strict (M : EntropyMixture) (c p d q t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : t ∈ Ico (0 : ℝ) 1)
    (hscaled : p * powerCurvature c t < q * powerCurvature d t) :
    EE M c p t < EE M d q t := by
  rw [EE_value M c p t hp ht, EE_value M d q t hq ht]
  have hA : 0 < mixtureCurvature M t := by
    have hle := (A_increasing M).monotoneOn
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩) ⟨ht.1, ht.2.le⟩ ht.1
    rw [A_zero] at hle
    exact lt_of_lt_of_le (A0pos M) hle
  have hB : 0 < entropyCurvature M t :=
    div_pos M.lambda_pos (by nlinarith [ht.1, ht.2])
  exact (entropy_error_monotone _ _ hA hB)
    (mul_pos hp (curvature_pos c t ht)) (mul_pos hq (curvature_pos d t ht)) hscaled

private lemma EE_scaled_eq (M : EntropyMixture) (c p d q t : ℝ)
    (hp : 0 < p) (hq : 0 < q) (ht : t ∈ Ico (0 : ℝ) 1)
    (heq : p * powerCurvature c t = q * powerCurvature d t) :
    EE M c p t = EE M d q t := by
  rw [EE_value M c p t hp ht, EE_value M d q t hq ht]
  simp only [curvatureError, heq]

private lemma split_family (M : EntropyMixture) (c p r u σ : ℝ) (hc1 : c < 1)
    (hp : 0 < p) (hr : 0 < r) (hu : u ∈ Ioo (0 : ℝ) 1) (hσ : σ = 1 ∨ σ = -1)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |EE M c p t| ≤ r)
    (hleft : ∀ t ∈ Icc 0 u, -r < σ * EE M c p t)
    (hright : ∀ t ∈ Icc u 1, σ * EE M c p t < r)
    (l : Filter ℝ) [l.NeBot] (φ : ℝ → ℝ × ℝ)
    (hcont : Tendsto φ l (𝓝 (c, p)))
    (hvalid : ∀ᶠ d in l, validGeometry (φ d) ∧ (φ d).1 < 1)
    (horder : ∀ᶠ d in l, ∀ t ∈ Ico (0 : ℝ) 1,
      (t < u → σ * EE M (φ d).1 (φ d).2 t < σ * EE M c p t) ∧
      (u < t → σ * EE M c p t < σ * EE M (φ d).1 (φ d).2 t)) :
    ∃ z, validGeometry z ∧ contraction M z.1 z.2 < r := by
  have hlo := uniform_open M c p (-σ) r hc1 hp (Icc 0 u) isCompact_Icc
    (by intro t ht; exact ⟨ht.1, le_trans ht.2 hu.2.le⟩) (by
      intro t ht
      nlinarith [hleft t ht])
  have hhi := uniform_open M c p σ r hc1 hp (Icc u 1) isCompact_Icc
    (by intro t ht; exact ⟨le_trans hu.1.le ht.1, ht.2⟩) hright
  obtain ⟨d, hlow, hhigh, hv, hord⟩ :=
    ((hcont.eventually hlo).and ((hcont.eventually hhi).and (hvalid.and horder))).exists
  refine ⟨φ d, hv.1, ?_⟩
  apply profile_strict M (φ d).1 (φ d).2 r hv.1 hv.2
  intro t ht
  have hbσ : -r ≤ σ * EE M c p t ∧ σ * EE M c p t ≤ r := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hb t ht)
    rcases hσ with hσ | hσ <;> rw [hσ] <;> constructor <;> nlinarith
  have hnew : -r < σ * EE M (φ d).1 (φ d).2 t ∧
      σ * EE M (φ d).1 (φ d).2 t < r := by
    rcases eq_or_lt_of_le ht.2 with ht1 | ht1
    · subst t
      rw [EE_one M (φ d).1 (φ d).2 hv.2, mul_zero]
      constructor <;> linarith
    · rcases lt_trichotomy t u with htu | htu | hut
      · exact ⟨by nlinarith [hlow t ⟨ht.1, htu.le⟩],
          lt_of_lt_of_le ((hord t ⟨ht.1, ht1⟩).1 htu) hbσ.2⟩
      · subst t
        exact ⟨by nlinarith [hlow u ⟨hu.1.le, le_rfl⟩], hhigh u ⟨le_rfl, hu.2.le⟩⟩
      · exact ⟨lt_of_le_of_lt hbσ.1 ((hord t ⟨ht.1, ht1⟩).2 hut),
          hhigh t ⟨hut.le, ht.2⟩⟩
  apply abs_lt.mpr
  rcases hσ with hσ | hσ <;> rw [hσ] at hnew <;> constructor <;> nlinarith [hnew.1, hnew.2]

private lemma rising_split (M : EntropyMixture) (c p r u : ℝ) (hc0 : 0 ≤ c)
    (hc1 : c < 1) (hp : 0 < p) (hr : 0 < r) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |EE M c p t| ≤ r)
    (hleft : ∀ t ∈ Icc 0 u, -r < EE M c p t)
    (hright : ∀ t ∈ Icc u 1, EE M c p t < r) :
    ∃ z, validGeometry z ∧ contraction M z.1 z.2 < r := by
  let φ := fun d => (d, normalizedP c p u d)
  have hu' : u ∈ Ico (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
  have hcont : Tendsto φ (𝓝[>] c) (𝓝 (c, p)) :=
    (normalized_cont c p u hu').mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ d in 𝓝[>] c, c < d ∧ d < 1 := by
    have he : ∀ᶠ d in 𝓝[>] c, d < 1 :=
      (show ∀ᶠ d in 𝓝 c, d < 1 from Iio_mem_nhds hc1).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, he] with d hd hd1
    exact ⟨hd, hd1⟩
  apply split_family M c p r u 1 hc1 hp hr hu (Or.inl rfl) hb
    (by simpa only [one_mul] using hleft) (by simpa only [one_mul] using hright)
    (𝓝[>] c) φ hcont
  · filter_upwards [hnear] with d hd
    exact ⟨⟨le_trans hc0 hd.1.le, by linarith [hd.2], normalized_positive c p u d hp hu'⟩, hd.2⟩
  · filter_upwards [hnear] with d hd t ht
    have hs := scaled_relative c p d (normalizedP c p u d) u hp hc0 hd.1 (by linarith [hd.2])
      hu' (normalized_contact c p u d hu')
    have hq := normalized_positive c p u d hp hu'
    constructor
    · intro htu
      simpa only [one_mul] using EE_scaled_strict M d (normalizedP c p u d) c p t hq hp ht
        (hs.1 t ht htu)
    · intro hut
      simpa only [one_mul] using EE_scaled_strict M c p d (normalizedP c p u d) t hp hq ht
        (hs.2 t ht hut)

private lemma falling_split (M : EntropyMixture) (c p r u : ℝ) (hc0 : 0 < c)
    (hc1 : c < 1) (hp : 0 < p) (hr : 0 < r) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |EE M c p t| ≤ r)
    (hleft : ∀ t ∈ Icc 0 u, EE M c p t < r)
    (hright : ∀ t ∈ Icc u 1, -r < EE M c p t) :
    ∃ z, validGeometry z ∧ contraction M z.1 z.2 < r := by
  let φ := fun d => (d, normalizedP c p u d)
  have hu' : u ∈ Ico (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
  have hcont : Tendsto φ (𝓝[<] c) (𝓝 (c, p)) :=
    (normalized_cont c p u hu').mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ d in 𝓝[<] c, 0 < d ∧ d < c := by
    have he : ∀ᶠ d in 𝓝[<] c, 0 < d :=
      (show ∀ᶠ d in 𝓝 c, 0 < d from Ioi_mem_nhds hc0).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, he] with d hd hd0
    exact ⟨hd0, hd⟩
  apply split_family M c p r u (-1) hc1 hp hr hu (Or.inr rfl) hb
    (by intro t ht; nlinarith [hleft t ht]) (by intro t ht; nlinarith [hright t ht])
    (𝓝[<] c) φ hcont
  · filter_upwards [hnear] with d hd
    exact ⟨⟨hd.1.le, by linarith [hd.2, hc1], normalized_positive c p u d hp hu'⟩,
      lt_trans hd.2 hc1⟩
  · filter_upwards [hnear] with d hd t ht
    have hq := normalized_positive c p u d hp hu'
    have hs := scaled_relative d (normalizedP c p u d) c p u hq hd.1.le hd.2 (by linarith)
      hu' (normalized_contact c p u d hu').symm
    constructor
    · intro htu
      have he := EE_scaled_strict M c p d (normalizedP c p u d) t hp hq ht (hs.1 t ht htu)
      dsimp [φ]
      nlinarith


    · intro hut
      have he := EE_scaled_strict M d (normalizedP c p u d) c p t hq hp ht (hs.2 t ht hut)
      dsimp [φ]
      nlinarith

private lemma active_compact (M : EntropyMixture) (c p v : ℝ) (hc1 : c < 1) (hp : 0 < p) :
    IsCompact {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ EE M c p t = v} := by
  have hclosed : IsClosed ((Icc (0 : ℝ) 1) ∩ (EE M c p) ⁻¹' {v}) :=
    (EE_cont_state M c p hc1 hp).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  exact isCompact_Icc.of_isClosed_subset hclosed inter_subset_left

private lemma W_quadratic (t : ℝ) : W 0 t = 1 - t ^ 2 := by
  simp [W, Real.rpow_eq_pow]
  ring

private lemma quadratic_positive_step (M : EntropyMixture) (p r : ℝ) (hp : 0 < p)
    (hr : 0 < r) (hpos : ∃ t ∈ Icc (0 : ℝ) 1, EE M 0 p t = r) : curvatureAtZero M < p := by
  obtain ⟨t, ht, he⟩ := hpos
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst t
      rw [EE_one M 0 p (by norm_num)] at he
      linarith
    · exact h
  have hraw : 0 < curvatureError M 0 p t := by rw [← EE_value M 0 p t hp ⟨ht.1, ht1⟩, he]; exact hr
  have hk : powerCurvature 0 t = 1 := by simp [powerCurvature, Real.rpow_eq_pow]
  have hB : 0 < entropyCurvature M t := div_pos M.lambda_pos (by nlinarith [ht.1, ht1])
  unfold curvatureError at hraw
  rw [hk, mul_one] at hraw
  have hnum := (lt_div_iff₀ (add_pos hp hB)).mp hraw
  have hA := (A_increasing M).monotoneOn
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩) ht ht.1
  rw [A_zero] at hA
  nlinarith

private lemma quadratic_peak (M : EntropyMixture) (p : ℝ) (hp : curvatureAtZero M < p)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ht0 : 0 < t) :
    EE M 0 p t < EE M 0 p 0 := by
  have hp0 : 0 < p := lt_trans (A0pos M) hp
  have hW := W_nonneg 0 t ht
  have hWlt : W 0 t < 1 := by
    have h := (W_decreasing 0 le_rfl (by norm_num))
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩) ht ht0
    simpa only [W_zero] using h
  have hA := (A_increasing M).monotoneOn
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩) ht ht.1
  rw [A_zero] at hA
  have hR : curvatureAtZero M * W 0 t ≤ RR M t := by
    rw [W_quadratic, RR]
    nlinarith [mul_le_mul_of_nonneg_left hA (show 0 ≤ 1 - t ^ 2 by nlinarith [ht.1, ht.2])]
  have hd : 0 < p * W 0 t + M.lambda :=
    add_pos_of_nonneg_of_pos (mul_nonneg hp0.le hW) M.lambda_pos
  rw [EE_zero, EE]
  apply (div_lt_div_iff₀ hd (add_pos hp0 M.lambda_pos)).2
  have hRmul := mul_le_mul_of_nonneg_right hR (add_pos hp0 M.lambda_pos).le
  have hgap := mul_pos (mul_pos M.lambda_pos (sub_pos.mpr hp)) (sub_pos.mpr hWlt)
  nlinarith only [hRmul, hgap]

private lemma optimum_power_pos (M : EntropyMixture) (z : ℝ × ℝ) (hz : IsGeometryOptimum M z) :
    0 < z.1 := by
  rcases eq_or_lt_of_le hz.1.1 with hc0 | hc0
  · exfalso
    have hzc : z.1 = 0 := hc0.symm
    let p := z.2
    have hopt : IsGeometryOptimum M (0, p) := by simpa only [← hzc, p, Prod.eta] using hz
    let r := contraction M 0 p
    have hp : 0 < p := hopt.1.2.2
    have hr : 0 < r := contraction_pos M 0 p hopt.1
    have hb := profile_bound_closed M 0 p hopt.1 (by norm_num)
    obtain ⟨hpos, hneg⟩ := both_signs M 0 p hopt (by norm_num) hr
    have hpA := quadratic_positive_step M p r hp hr hpos
    have hpeak : ∀ t ∈ Icc (0 : ℝ) 1, EE M 0 p t = r → t = 0 := by
      intro t ht he
      by_contra ht0
      have hlt := quadratic_peak M p hpA t ht (lt_of_le_of_ne ht.1 (Ne.symm ht0))
      have hb0 := (abs_le.mp (hb 0 ⟨le_rfl, by norm_num⟩)).2
      dsimp [r] at *
      rw [he] at hlt
      linarith
    have he0 : EE M 0 p 0 = r := by
      obtain ⟨t, ht, he⟩ := hpos
      rwa [hpeak t ht he] at he
    let K := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ EE M 0 p t = -r}
    have hK : IsCompact K := active_compact M 0 p (-r) (by norm_num) hp
    obtain ⟨v, hv, hvmin⟩ := hK.exists_isMinOn hneg continuousOn_id
    have hv0 : 0 < v := by
      have hne : v ≠ 0 := by intro h; have he := hv.2; rw [h, he0] at he; linarith
      exact lt_of_le_of_ne hv.1.1 (Ne.symm hne)
    have hv1 : v < 1 := by
      have hne : v ≠ 1 := by intro h; have he := hv.2; rw [h, EE_one M 0 p (by norm_num)] at he; linarith
      exact lt_of_le_of_ne hv.1.2 hne
    let u := v / 2
    have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [u]; linarith, by dsimp [u]; linarith⟩
    have hleft : ∀ t ∈ Icc 0 u, -r < EE M 0 p t := by
      intro t ht
      have htK : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, le_trans ht.2 hu.2.le⟩
      have hle := (abs_le.mp (hb t htK)).1
      apply lt_of_le_of_ne hle
      intro he
      have hmin := hvmin (show t ∈ K from ⟨htK, he.symm⟩)
      dsimp [u] at ht
      change v ≤ t at hmin
      linarith [ht.2]
    have hright : ∀ t ∈ Icc u 1, EE M 0 p t < r := by
      intro t ht
      have htK : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans hu.1.le ht.1, ht.2⟩
      have hle := (abs_le.mp (hb t htK)).2
      apply lt_of_le_of_ne hle
      intro he
      have ht0 := hpeak t htK he
      rw [ht0] at ht
      linarith [hu.1, ht.1]
    obtain ⟨w, hw, hwr⟩ := rising_split M 0 p r u le_rfl (by norm_num) hp hr hu hb hleft hright
    exact (not_lt_of_ge (hopt.2 w hw)) hwr
  · exact hc0

private lemma E0 (M : EntropyMixture) (c p : ℝ) :
    curvatureError M c p 0 = (p - curvatureAtZero M) / (p + M.lambda) := by
  simp [curvatureError, powerCurvature, mixtureCurvature, entropyCurvature, curvatureAtZero]

private lemma compact_p (M : EntropyMixture) (c p : ℝ) (hv : validGeometry (c, p))
    (hr : contraction M c p ≤ entropyBaseline M) :
    p ∈ Icc (curvatureAtZero M / 2)
      (curvatureAtZero M * (curvatureAtZero M + 3 * M.lambda) / (2 * M.lambda)) := by
  have hA := A0pos M
  have hl := M.lambda_pos
  have hd : 0 < p + M.lambda := add_pos hv.2.2 hl
  have he := le_trans ((entropy_error_lub M c p hv).1
    ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩) hr
  rw [E0] at he
  obtain ⟨hneg, hpos⟩ := abs_le.mp he
  rw [le_div_iff₀ hd] at hneg
  rw [div_le_iff₀ hd] at hpos
  have hden : 0 < curvatureAtZero M + 2 * M.lambda := by positivity
  dsimp [entropyBaseline] at hneg hpos
  have hneg' := mul_le_mul_of_nonneg_right hneg hden.le
  have hpos' := mul_le_mul_of_nonneg_right hpos hden.le
  field_simp [ne_of_gt hden] at hneg' hpos'
  constructor
  · nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 2 * M.lambda)).2
    nlinarith

private lemma geometry_lsc (M : EntropyMixture) (K : Set (ℝ × ℝ))
    (hvalid : ∀ z ∈ K, validGeometry z) :
    LowerSemicontinuousOn (fun z => contraction M z.1 z.2) K := by
  intro z hz
  apply lowerSemicontinuousWithinAt_iff.mpr
  intro y hy
  have hv := hvalid z hz
  obtain ⟨v, ⟨t, ht, rfl⟩, hyt, _⟩ := (entropy_error_lub M z.1 z.2 hv).exists_between hy
  have hkp : ContinuousAt (fun u : ℝ × ℝ => powerCurvature u.1 t) z := by
    unfold powerCurvature
    exact ((continuousAt_const.rpow continuousAt_fst.neg
      (Or.inl (ne_of_gt (by linarith [ht.1]) : 1 + t ≠ 0))).add
      (continuousAt_const.rpow continuousAt_fst.neg
        (Or.inl (ne_of_gt (by linarith [ht.2]) : 1 - t ≠ 0)))).div_const 2
  have hd : 0 < z.2 * powerCurvature z.1 t + entropyCurvature M t :=
    add_pos (mul_pos hv.2.2 (curvature_pos z.1 t ht))
      (div_pos M.lambda_pos (by nlinarith [ht.1, ht.2]))
  have hcont : ContinuousAt (fun u : ℝ × ℝ => |curvatureError M u.1 u.2 t|) z :=
    (((continuousAt_snd.mul hkp).sub continuousAt_const).div
      ((continuousAt_snd.mul hkp).add continuousAt_const) (ne_of_gt hd)).abs
  have hevent : ∀ᶠ u in 𝓝[K] z, y < |curvatureError M u.1 u.2 t| :=
    (show ∀ᶠ u in 𝓝 z, y < |curvatureError M u.1 u.2 t| from
      hcont.preimage_mem_nhds (Ioi_mem_nhds hyt)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hevent, self_mem_nhdsWithin] with u hu huK
  exact lt_of_lt_of_le hu ((entropy_error_lub M u.1 u.2 (hvalid u huK)).1 ⟨t, ht, rfl⟩)

private lemma optimum_exists (M : EntropyMixture) : ∃ z, IsGeometryOptimum M z := by
  let a := curvatureAtZero M / 2
  let b := curvatureAtZero M * (curvatureAtZero M + 3 * M.lambda) / (2 * M.lambda)
  let K := (Icc (0 : ℝ) 1) ×ˢ Icc a b
  have ha : 0 < a := by dsimp [a]; positivity [A0pos M]
  have hab : a ≤ b := by
    dsimp [a, b]
    apply (le_div_iff₀ (by positivity [M.lambda_pos] : 0 < 2 * M.lambda)).2
    nlinarith [A0pos M, M.lambda_pos]
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hne : K.Nonempty := ⟨(0, a), ⟨le_rfl, by norm_num⟩, le_rfl, hab⟩
  have hvalid (z : ℝ × ℝ) (hz : z ∈ K) : validGeometry z :=
    ⟨hz.1.1, by linarith [hz.1.2], lt_of_lt_of_le ha hz.2.1⟩
  have hinK (z : ℝ × ℝ) (hz : validGeometry z)
      (hval : contraction M z.1 z.2 ≤ entropyBaseline M) : z ∈ K := by
    refine ⟨⟨hz.1, ?_⟩, compact_p M z.1 z.2 hz hval⟩
    exact small_contraction_power M z.1 z.2 hz (lt_of_le_of_lt hval (baseline_lt_one M))
  obtain ⟨z, hzK, hzmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK (geometry_lsc M K hvalid)
  obtain ⟨c, p, hv, _, hr⟩ := strict_candidate M
  have hzk : contraction M z.1 z.2 < entropyBaseline M :=
    lt_of_le_of_lt (hzmin (hinK (c, p) hv hr.le)) hr
  refine ⟨z, hvalid z hzK, ?_⟩
  intro u hu
  by_cases hsmall : contraction M u.1 u.2 ≤ entropyBaseline M
  · exact hzmin (hinK u hu hsmall)
  · exact le_of_lt (lt_trans hzk (lt_of_not_ge hsmall))

private lemma V_sum (M : EntropyMixture) (c t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    mixtureCurvature M t / powerCurvature c t =
      ∑ j, M.weight j * M.a j / ((1 - M.a j * t ^ 2) * powerCurvature c t) := by
  unfold mixtureCurvature
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  exact div_div _ _ _

private lemma threshold_scale_mono (a b : ℝ) (hab : a ≤ b) : threshold a ≤ threshold b := by
  unfold threshold
  have hs := Real.sqrt_le_sqrt (show 1 + 8 * a ≤ 1 + 8 * b by linarith)
  linarith

private lemma V_decreasing (hthr : PowerThresholdClaim) (M : EntropyMixture) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hscales : ∀ j, threshold (M.a j) ≤ c) :
    StrictAntiOn (fun t => mixtureCurvature M t / powerCurvature c t) (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  change mixtureCurvature M y / powerCurvature c y < mixtureCurvature M x / powerCurvature c x
  rw [V_sum M c y hy, V_sum M c x hx]
  have hsq : x ^ 2 < y ^ 2 := by simpa only [sq] using mul_self_lt_mul_self hx.1 hxy
  have hx2 : x ^ 2 ∈ Ico (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [hx.1, hx.2]⟩
  have hy2 : y ^ 2 ∈ Ico (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [hy.1, hy.2]⟩
  have hterm (j : Fin M.m) :
      M.weight j * M.a j / ((1 - M.a j * y ^ 2) * powerCurvature c y) <
      M.weight j * M.a j / ((1 - M.a j * x ^ 2) * powerCurvature c x) := by
    have hmono := (hthr (M.a j) c (M.a_pos j) (M.a_lt_one j) hc0 hc1).1 (hscales j)
    have hq := hmono hx2 hy2 hsq
    simp only [thresholdProfile, Real.sqrt_sq hx.1, Real.sqrt_sq hy.1] at hq
    have hdx := mul_pos (scaled_den M j x ⟨hx.1, hx.2.le⟩) (curvature_pos c x hx)
    have hdy := mul_pos (scaled_den M j y ⟨hy.1, hy.2.le⟩) (curvature_pos c y hy)
    apply (div_lt_div_iff₀ hdy hdx).2
    exact mul_lt_mul_of_pos_left hq (mul_pos (M.weight_pos j) (M.a_pos j))
  apply Finset.sum_lt_sum (fun j _ => (hterm j).le)
  exact ⟨⟨0, M.m_pos⟩, Finset.mem_univ _, hterm _⟩

private lemma optimum_location (hthr : PowerThresholdClaim) (halt : NecessaryAlternationClaim)
    (M : EntropyMixture) (z : ℝ × ℝ) (hz : IsGeometryOptimum M z) : LocationBounds M z := by
  have hbasic := optimum_basic M z hz
  have hc0 := optimum_power_pos M z hz
  have hc1 := hbasic.1
  have hp := hz.1.2.2
  have hr := hbasic.2.1
  have hsmall := hbasic.2.2
  obtain ⟨jmax, _, hmax⟩ := Finset.exists_max_image Finset.univ M.a
    ⟨⟨0, M.m_pos⟩, Finset.mem_univ _⟩
  have hne : (range M.a).Nonempty := ⟨M.a jmax, jmax, rfl⟩
  have hLUB : IsLUB (range M.a) (M.a jmax) := by
    constructor
    · rintro v ⟨j, rfl⟩
      exact hmax j (Finset.mem_univ _)
    · intro b hb
      exact hb ⟨jmax, rfl⟩
  have hMax : maxScale M = M.a jmax := hLUB.csSup_eq hne
  have hchi1 : threshold (maxScale M) < 1 := by
    rw [hMax]
    exact (threshold_bounds _ (M.a_pos jmax) (M.a_lt_one jmax)).2
  have hcchi : z.1 < threshold (maxScale M) := by
    by_contra hn
    have hch : threshold (maxScale M) ≤ z.1 := le_of_not_gt hn
    have hv : StrictAntiOn (fun t => mixtureCurvature M t / powerCurvature z.1 t)
        (Ico (0 : ℝ) 1) := by
      apply V_decreasing hthr M z.1 hc0 hc1
      intro j
      apply le_trans _ hch
      rw [hMax]
      exact threshold_scale_mono _ _ (hmax j (Finset.mem_univ _))
    obtain ⟨t₁, t₂, t₃, σ, ht₁, h12, h23, ht₃, hσ, he₁, he₂, he₃⟩ := (halt M z hz).2
    have h1 : t₁ ∈ Ico (0 : ℝ) 1 := ⟨ht₁, lt_trans h12 (lt_trans h23 ht₃)⟩
    have h2 : t₂ ∈ Ico (0 : ℝ) 1 := ⟨(lt_of_le_of_lt ht₁ h12).le, lt_trans h23 ht₃⟩
    have h3 : t₃ ∈ Ico (0 : ℝ) 1 := ⟨(lt_of_le_of_lt h2.1 h23).le, ht₃⟩
    rcases hσ with hσ | hσ
    · have hpos := E_positive_V M z.1 z.2 t₁ hp h1 (by rw [he₁, hσ, one_mul]; exact hr)
      have hneg := E_negative_V M z.1 z.2 t₂ hp h2 (by rw [he₂, hσ]; nlinarith)
      have hdec := hv h1 h2 h12
      dsimp only at hdec
      linarith
    · have hpos := E_positive_V M z.1 z.2 t₂ hp h2 (by rw [he₂, hσ]; nlinarith)
      have hneg := E_negative_V M z.1 z.2 t₃ hp h3 (by rw [he₃, hσ]; nlinarith)
      have hdec := hv h2 h3 h23
      dsimp only at hdec
      linarith
  have hpcompact := compact_p M z.1 z.2 hz.1 hsmall.le
  have hpneq : z.2 ≠ curvatureAtZero M / 2 := by
    intro heq
    have he := (entropy_error_lub M z.1 z.2 hz.1).1
      ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩
    rw [E0, heq] at he
    have hcalc : (curvatureAtZero M / 2 - curvatureAtZero M) /
        (curvatureAtZero M / 2 + M.lambda) = -entropyBaseline M := by
      unfold entropyBaseline
      field_simp
      <;> ring
    rw [hcalc, abs_neg, abs_of_pos (lt_trans hr hsmall)] at he
    rw [← heq] at he
    exact (not_lt_of_ge he) hsmall
  have hpLower : curvatureAtZero M / 2 < z.2 := lt_of_le_of_ne hpcompact.1 (Ne.symm hpneq)
  have hpUpper : z.2 < curvatureAtBoundary M := by
    obtain ⟨_, ⟨t, ht, he⟩⟩ := both_signs M z.1 z.2 hz hc1 hr
    have ht1 : t < 1 := by
      have hne : t ≠ 1 := by
        intro h
        rw [h, EE_one M z.1 z.2 hc1] at he
        linarith
      exact lt_of_le_of_ne ht.2 hne
    have htco : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht1⟩
    have hneg : curvatureError M z.1 z.2 t < 0 := by
      rw [← EE_value M z.1 z.2 t hp htco, he]
      linarith
    have hVp := E_negative_V M z.1 z.2 t hp htco hneg
    have hpk : z.2 * powerCurvature z.1 t < mixtureCurvature M t :=
      (lt_div_iff₀ (curvature_pos z.1 t htco)).mp hVp
    have hk : 1 ≤ powerCurvature z.1 t := by
      have hmono := (power_single_crossing 0 z.1 le_rfl hc0 hz.1.2.1).monotoneOn
        (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩) htco ht.1
      have hkzero (u : ℝ) : powerCurvature 0 u = 1 := by simp [powerCurvature, Real.rpow_eq_pow]
      have hk0 : powerCurvature z.1 0 = 1 := by simp [powerCurvature, Real.rpow_eq_pow]
      simpa only [hkzero, hk0, div_one] using hmono
    have hAbound := (A_increasing M).monotoneOn ht
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, le_rfl⟩) ht.2
    rw [A_one] at hAbound
    nlinarith [mul_le_mul_of_nonneg_left hk hp.le]
  exact ⟨hc0, hcchi, hchi1, hpLower, hpUpper, hr, hsmall, baseline_lt_one M⟩

private lemma entropy_hasDerivAt (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt entropy (artanh t) t := by
  have hp : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
  have hm : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := (hasDerivAt_id t).const_sub 1
  have hplus : 1 + t ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hminus : 1 - t ≠ 0 := ne_of_gt (by linarith [ht.2])
  convert ((hp.mul (hp.log hplus)).add (hm.mul (hm.log hminus))).div_const 2 using 1
    <;> try rfl
  unfold artanh
  field_simp [hplus, hminus]
  <;> ring

private lemma basic_den {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]

private lemma atan_deriv {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt artanh (1 / (1 - t ^ 2)) t := by
  have hp := ((hasDerivAt_id t).const_add 1).log
    (ne_of_gt (by linarith [ht.1]) : 1 + t ≠ 0)
  have hm := ((hasDerivAt_id t).const_sub 1).log
    (ne_of_gt (by linarith [ht.2]) : 1 - t ≠ 0)
  convert (hp.sub hm).div_const 2 using 1 <;> try rfl
  simp only [id_eq]
  field_simp [ne_of_gt (basic_den ht),
    (ne_of_gt (by linarith [ht.1]) : 1 + t ≠ 0),
    (ne_of_gt (by linarith [ht.2]) : 1 - t ≠ 0)]
  <;> ring

private lemma mix_deriv (M : EntropyMixture) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (mixtureSlope M) (mixtureCurvature M t) t := by
  unfold mixtureSlope mixtureCurvature
  apply HasDerivAt.fun_sum
  intro j _
  have hs : 0 < Real.sqrt (M.a j) := Real.sqrt_pos.mpr (M.a_pos j)
  have hsq := Real.sq_sqrt (le_of_lt (M.a_pos j))
  have hlt : Real.sqrt (M.a j) < 1 := by nlinarith [M.a_lt_one j]
  have ht' : Real.sqrt (M.a j) * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [mul_lt_mul_of_pos_left ht.1 hs,
      mul_lt_mul_of_pos_left ht.2 hs]
  convert ((atan_deriv ht').comp t ((hasDerivAt_id t).const_mul
    (Real.sqrt (M.a j)))).const_mul (M.weight j * Real.sqrt (M.a j)) using 1
    <;> try rfl
  rw [mul_pow, hsq]
  ring_nf
  rw [hsq]
  ring

private lemma mixture_value_deriv (M : EntropyMixture) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : HasDerivAt (mixtureValue M) (mixtureSlope M t) t := by
  unfold mixtureValue mixtureSlope
  apply HasDerivAt.fun_sum
  intro j _
  have hspos : 0 < Real.sqrt (M.a j) := Real.sqrt_pos.mpr (M.a_pos j)
  have hslt : Real.sqrt (M.a j) < 1 := by
    nlinarith [Real.sq_sqrt (le_of_lt (M.a_pos j)), M.a_lt_one j]
  have hscaled : Real.sqrt (M.a j) * t ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_lt_mul_of_pos_left ht.1 hspos]
    · nlinarith [mul_lt_mul_of_pos_left ht.2 hspos]
  convert ((entropy_hasDerivAt _ hscaled).comp t
    ((hasDerivAt_id t).const_mul (Real.sqrt (M.a j)))).const_mul (M.weight j) using 1
    <;> first | rfl | ring

private lemma single_inside (a t : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) : Real.sqrt a * t ∈ Ioo (-1 : ℝ) 1 := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hs1 : Real.sqrt a < 1 := by nlinarith [Real.sq_sqrt ha.le]
  constructor <;> nlinarith [mul_lt_mul_of_pos_left ht.1 hs, mul_lt_mul_of_pos_left ht.2 hs]

private lemma single_value_deriv (a t : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => entropy (Real.sqrt a * t))
      (Real.sqrt a * artanh (Real.sqrt a * t)) t := by
  convert (entropy_hasDerivAt _ (single_inside a t ha ha1 ht)).comp t
    ((hasDerivAt_id t).const_mul (Real.sqrt a)) using 1 <;> first | rfl | ring

private lemma single_slope_deriv (a t : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => Real.sqrt a * artanh (Real.sqrt a * t))
      (a / (1 - a * t ^ 2)) t := by
  convert ((atan_deriv (single_inside a t ha ha1 ht)).comp t
    ((hasDerivAt_id t).const_mul (Real.sqrt a))).const_mul (Real.sqrt a) using 1 <;> try rfl
  rw [mul_pow, Real.sq_sqrt ha.le]
  ring_nf
  rw [Real.sq_sqrt ha.le]
  ring

private lemma single_curvature (M : EntropyMixture) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hprofile : ∀ t ∈ Ioo (-1 : ℝ) 1, mixtureValue M t = entropy (Real.sqrt a * t)) :
    ∀ t ∈ Ioo (-1 : ℝ) 1, mixtureCurvature M t = a / (1 - a * t ^ 2) := by
  have hslope : ∀ t ∈ Ioo (-1 : ℝ) 1,
      mixtureSlope M t = Real.sqrt a * artanh (Real.sqrt a * t) := by
    intro t ht
    have heq : mixtureValue M =ᶠ[𝓝 t] (fun t => entropy (Real.sqrt a * t)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hprofile s hs
    exact (heq.hasDerivAt_iff.mp (mixture_value_deriv M ht)).unique
      (single_value_deriv a t ha ha1 ht)
  intro t ht
  have heq : mixtureSlope M =ᶠ[𝓝 t] (fun t => Real.sqrt a * artanh (Real.sqrt a * t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hslope s hs
  exact (heq.hasDerivAt_iff.mp (mix_deriv M ht)).unique (single_slope_deriv a t ha ha1 ht)

private def canonical (a lambda : ℝ) (ha : 0 < a) (ha1 : a < 1) (hl : 0 < lambda) : EntropyMixture where
  m := 1
  m_pos := by norm_num
  a := fun _ => a
  weight := fun _ => 1
  lambda := lambda
  a_pos := fun _ => ha
  a_lt_one := fun _ => ha1
  weight_pos := fun _ => by norm_num
  lambda_pos := hl

private lemma canonical_curvature (a lambda t : ℝ) (ha : 0 < a) (ha1 : a < 1) (hl : 0 < lambda) :
    mixtureCurvature (canonical a lambda ha ha1 hl) t = a / (1 - a * t ^ 2) := by
  change (∑ _j : Fin 1, 1 * a / (1 - a * t ^ 2)) = a / (1 - a * t ^ 2)
  simp

private lemma canonical_bounds (M : EntropyMixture) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hcurv : ∀ t ∈ Ioo (-1 : ℝ) 1, mixtureCurvature M t = a / (1 - a * t ^ 2))
    (z : ℝ × ℝ) (hz : IsGeometryOptimum M z) :
    z.1 < threshold a ∧ z.2 < a / (1 - a) := by
  let S := canonical a M.lambda ha ha1 M.lambda_pos
  have he (c p t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      curvatureError M c p t = curvatureError S c p t := by
    unfold curvatureError entropyCurvature
    rw [hcurv t ⟨by linarith [ht.1], ht.2⟩, canonical_curvature]
    rfl
  have heq (c p : ℝ) : contraction M c p = contraction S c p := by
    apply congrArg sSup
    ext v
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by rw [he c p t ht]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by rw [he c p t ht]⟩
  have hoptS : IsGeometryOptimum S z := ⟨hz.1, by
    intro u hu
    rw [← heq, ← heq]
    exact hz.2 u hu⟩
  have hloc := optimum_location power_threshold entropy_necessary_alternation S z hoptS
  have hscale : maxScale S = a := by simp [maxScale, S, canonical]
  have hA1 : curvatureAtBoundary S = a / (1 - a) := by
    change (∑ _j : Fin 1, 1 * a / (1 - a)) = a / (1 - a)
    simp
  exact ⟨by simpa only [hscale] using hloc.2.1, by simpa only [hA1] using hloc.2.2.2.2.1⟩

private def V (a c t : ℝ) : ℝ := a / ((1 - a * t ^ 2) * powerCurvature c t)

private lemma V_shape (a c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hc1 : c < 1) (hct : c < threshold a) :
    ∃ v ∈ Ioo (0 : ℝ) 1, StrictMonoOn (V a c) (Icc 0 v) ∧ StrictAntiOn (V a c) (Ico v 1) := by
  obtain ⟨u, hu, hanti, hmono⟩ := (power_threshold a c ha ha1 hc hc1).2 hct
  let v := Real.sqrt u
  have hv : v ∈ Ioo (0 : ℝ) 1 := ⟨Real.sqrt_pos.mpr hu.1,
    (Real.sqrt_lt hu.1.le (by norm_num : (0 : ℝ) ≤ 1)).2 (by simpa using hu.2)⟩
  have hvsq : v ^ 2 = u := Real.sq_sqrt hu.1.le
  have hd (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : 0 < (1 - a * t ^ 2) * powerCurvature c t := by
    have hs : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
    exact mul_pos (by nlinarith [ha, ha1, sq_nonneg t]) (curvature_pos c t ht)
  refine ⟨v, hv, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxco : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 hv.2⟩
    have hyco : y ∈ Ico (0 : ℝ) 1 := ⟨hy.1, lt_of_le_of_lt hy.2 hv.2⟩
    have hx2 : x ^ 2 ∈ Icc (0 : ℝ) u := ⟨sq_nonneg _, by nlinarith [hx.2, hx.1, hv.1]⟩
    have hy2 : y ^ 2 ∈ Icc (0 : ℝ) u := ⟨sq_nonneg _, by nlinarith [hy.2, hy.1, hv.1]⟩
    have hsquare : x ^ 2 < y ^ 2 := by simpa only [sq] using mul_self_lt_mul_self hx.1 hxy
    have hQ := hanti hx2 hy2 hsquare
    simp only [thresholdProfile, Real.sqrt_sq hx.1, Real.sqrt_sq hy.1] at hQ
    apply (div_lt_div_iff₀ (hd x hxco) (hd y hyco)).2
    exact mul_lt_mul_of_pos_left hQ ha
  · intro x hx y hy hxy
    have hxco : x ∈ Ico (0 : ℝ) 1 := ⟨le_trans hv.1.le hx.1, hx.2⟩
    have hyco : y ∈ Ico (0 : ℝ) 1 := ⟨le_trans hv.1.le hy.1, hy.2⟩
    have hx2 : x ^ 2 ∈ Ico u 1 := ⟨by nlinarith [hx.1, hxco.1, hv.1], by nlinarith [hxco.1, hxco.2]⟩
    have hy2 : y ^ 2 ∈ Ico u 1 := ⟨by nlinarith [hy.1, hyco.1, hv.1], by nlinarith [hyco.1, hyco.2]⟩
    have hsquare : x ^ 2 < y ^ 2 := by simpa only [sq] using mul_self_lt_mul_self hxco.1 hxy
    have hQ := hmono hx2 hy2 hsquare
    simp only [thresholdProfile, Real.sqrt_sq hxco.1, Real.sqrt_sq hyco.1] at hQ
    apply (div_lt_div_iff₀ (hd y hyco) (hd x hxco)).2
    exact mul_lt_mul_of_pos_left hQ ha

theorem solution : SingleProfileClaim := by
  intro M a ha ha1 hprofile z hz
  have hcurv := single_curvature M a ha ha1 hprofile
  have hcanonical := canonical_bounds M a ha ha1 hcurv z hz
  have hbasic := optimum_basic M z hz
  have hc0 := optimum_power_pos M z hz
  have hc1 := hbasic.1
  have hp := hz.1.2.2
  let r := contraction M z.1 z.2
  have hr : 0 < r := hbasic.2.1
  obtain ⟨v, hv, hinc, hdec⟩ := V_shape a z.1 ha ha1 hc0 hc1 hcanonical.1
  have hVeq (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      mixtureCurvature M t / powerCurvature z.1 t = V a z.1 t := by
    rw [hcurv t ⟨by linarith [ht.1], ht.2⟩]
    exact div_div _ _ _
  obtain ⟨t₁, t₂, t₃, σ, ht₁, h12, h23, ht₃, hσ, he₁, he₂, he₃⟩ :=
    (entropy_necessary_alternation M z hz).2
  have h1 : t₁ ∈ Ico (0 : ℝ) 1 := ⟨ht₁, lt_trans h12 (lt_trans h23 ht₃)⟩
  have h2 : t₂ ∈ Ico (0 : ℝ) 1 := ⟨(lt_of_le_of_lt ht₁ h12).le, lt_trans h23 ht₃⟩
  have h3 : t₃ ∈ Ico (0 : ℝ) 1 := ⟨(lt_of_le_of_lt h2.1 h23).le, ht₃⟩
  have hsign : σ = 1 := by
    rcases hσ with hσ | hσ
    · exact hσ
    · exfalso
      have hp1 : z.2 < V a z.1 t₁ := by
        rw [← hVeq t₁ h1]
        exact E_negative_V M z.1 z.2 t₁ hp h1 (by rw [he₁, hσ]; nlinarith)
      have hp2 : V a z.1 t₂ < z.2 := by
        rw [← hVeq t₂ h2]
        exact E_positive_V M z.1 z.2 t₂ hp h2 (by rw [he₂, hσ]; nlinarith)
      have hp3 : z.2 < V a z.1 t₃ := by
        rw [← hVeq t₃ h3]
        exact E_negative_V M z.1 z.2 t₃ hp h3 (by rw [he₃, hσ]; nlinarith)
      by_cases ht2v : t₂ ≤ v
      · have hlt := hinc ⟨h1.1, le_trans h12.le ht2v⟩ ⟨h2.1, ht2v⟩ h12
        change V a z.1 t₁ < V a z.1 t₂ at hlt
        linarith
      · have hv2 : v < t₂ := lt_of_not_ge ht2v
        have hlt := hdec ⟨hv2.le, h2.2⟩ ⟨(lt_trans hv2 h23).le, h3.2⟩ h23
        change V a z.1 t₃ < V a z.1 t₂ at hlt
        linarith
  have hp1 : V a z.1 t₁ < z.2 := by
    rw [← hVeq t₁ h1]
    exact E_positive_V M z.1 z.2 t₁ hp h1 (by rw [he₁, hsign]; nlinarith)
  have hp2 : z.2 < V a z.1 t₂ := by
    rw [← hVeq t₂ h2]
    exact E_negative_V M z.1 z.2 t₂ hp h2 (by rw [he₂, hsign]; nlinarith)
  have ht1v : t₁ < v := by
    by_contra hn
    have hv1 : v ≤ t₁ := le_of_not_gt hn
    have hlt := hdec ⟨hv1, h1.2⟩ ⟨le_trans hv1 h12.le, h2.2⟩ h12
    change V a z.1 t₂ < V a z.1 t₁ at hlt
    linarith
  have hV0 : V a z.1 0 = a := by simp [V, powerCurvature, Real.rpow_eq_pow]
  have hVge : a ≤ V a z.1 t₁ := by
    have hle := hinc.monotoneOn
      (show (0 : ℝ) ∈ Icc (0 : ℝ) v from ⟨le_rfl, hv.1.le⟩) ⟨h1.1, ht1v.le⟩ h1.1
    simpa only [hV0] using hle
  have hpa : a < z.2 := lt_of_le_of_lt hVge hp1
  have ht10 : t₁ = 0 := by
    by_contra hn
    have ht1pos : 0 < t₁ := lt_of_le_of_ne h1.1 (Ne.symm hn)
    have hW := W_nonneg z.1 t₁ ⟨h1.1, h1.2.le⟩
    have hWlt : W z.1 t₁ < 1 := by
      have hlt := (W_decreasing z.1 hc0.le hc1)
        (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩)
        ⟨h1.1, h1.2.le⟩ ht1pos
      simpa only [W_zero] using hlt
    have hA0 : curvatureAtZero M = a := by
      simpa only [A_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero, div_one]
        using hcurv 0 ⟨by norm_num, by norm_num⟩
    have hR : a * W z.1 t₁ ≤ RR M t₁ := by
      have hVk := (le_div_iff₀ (curvature_pos z.1 t₁ h1)).mp
        (show a ≤ mixtureCurvature M t₁ / powerCurvature z.1 t₁ from by
          rw [hVeq t₁ h1]; exact hVge)
      rw [W_value z.1 t₁ h1, RR]
      have hs : 0 ≤ 1 - t₁ ^ 2 := by nlinarith [h1.1, h1.2]
      nlinarith [mul_le_mul_of_nonneg_left hVk hs]
    have hd : 0 < z.2 * W z.1 t₁ + M.lambda :=
      add_pos_of_nonneg_of_pos (mul_nonneg hp.le hW) M.lambda_pos
    have hpeak : EE M z.1 z.2 t₁ < EE M z.1 z.2 0 := by
      rw [EE_zero, hA0, EE]
      apply (div_lt_div_iff₀ hd (add_pos hp M.lambda_pos)).2
      have hRmul := mul_le_mul_of_nonneg_right hR (add_pos hp M.lambda_pos).le
      have hgap := mul_pos (mul_pos M.lambda_pos (sub_pos.mpr hpa)) (sub_pos.mpr hWlt)
      nlinarith only [hRmul, hgap]
    have hupper := (profile_bound_closed M z.1 z.2 hz.1 hc1) 0 ⟨le_rfl, by norm_num⟩
    have het : EE M z.1 z.2 t₁ = r := by rw [EE_value M z.1 z.2 t₁ hp h1, he₁, hsign, one_mul]
    rw [het] at hpeak
    nlinarith [le_abs_self (EE M z.1 z.2 0)]
  refine ⟨hpa, hcanonical.2, t₂, t₃, ?_, h23, ht₃, ?_, ?_, ?_⟩
  · simpa only [ht10] using h12
  · simpa only [ht10, hsign, one_mul] using he₁
  · simpa only [hsign, neg_one_mul] using he₂
  · simpa only [hsign, one_mul] using he₃
