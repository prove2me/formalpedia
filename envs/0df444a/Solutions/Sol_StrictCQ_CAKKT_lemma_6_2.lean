-- Prove2me | solution 1 for StrictCQ.CAKKT.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:51:10.785788+00:00
-- url     : https://prove2.me/submissions/089e72e0-233f-481c-bc48-8148d5bbbd13

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Theorems.Thm_StrictCQ_CAKKT_lemma_6_1

open Filter Topology
open scoped InnerProductSpace
open StrictCQ.CAKKT

lemma cakkt_hasDerivAt_maxsq (u : ℝ) :
    HasDerivAt (fun t : ℝ => (max 0 t) ^ 2) (2 * max 0 u) u := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hev : (fun t : ℝ => (max 0 t) ^ 2) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [gt_mem_nhds hu] with t ht
      simp [max_eq_left ht.le]
    rw [max_eq_left hu.le, mul_zero]
    exact (hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq hev
  · subst hu
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hc] with t ht
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    simp only [max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      mul_zero, smul_zero, Real.norm_eq_abs]
    have h1 : |max 0 t ^ 2| ≤ |t| * |t| := by
      rw [abs_of_nonneg (sq_nonneg _), ← abs_mul, ← sq, abs_of_nonneg (sq_nonneg t)]
      rcases le_total t 0 with h | h
      · rw [max_eq_left h]; nlinarith [sq_nonneg t]
      · rw [max_eq_right h]
    calc |max 0 t ^ 2| ≤ |t| * |t| := h1
      _ ≤ c * |t| := by gcongr
  · have hev : (fun t : ℝ => (max 0 t) ^ 2) =ᶠ[𝓝 u] fun t => t ^ 2 := by
      filter_upwards [lt_mem_nhds hu] with t ht
      simp [max_eq_right ht.le]
    rw [max_eq_right hu.le]
    have := hasDerivAt_pow 2 u
    norm_num at this
    exact this.congr_of_eventuallyEq hev

theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xbar y : EuclideanSpace ℝ (Fin n)} (hxbar : xbar ∈ C.feasible)
    (hy : y ∈ StrictCQ.AGP.polar (tangentCone C.feasible xbar)) :
    ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Fin m → ℝ) (mu : ℕ → Fin p → ℝ) (c : ℕ → ℝ),
      (∀ k j, 0 ≤ mu k j) ∧ (∀ k, 0 ≤ c k) ∧
      Tendsto x atTop (𝓝 xbar) ∧
      Tendsto (fun k => ∑ i, lam k i • gradient (C.h i) (x k) +
        ∑ j, mu k j • gradient (C.g j) (x k)) atTop (𝓝 y) ∧
      (∀ k j, mu k j = c k * max 0 (C.g j (x k))) ∧
      Tendsto (fun k => ∑ i, |lam k i * C.h i (x k)| + ∑ j, |mu k j * C.g j (x k)|)
        atTop (𝓝 0) := by
  obtain ⟨F, hF, hFy, hFmin⟩ := lemma_6_1 C hC hxbar hy
  have hhc : ∀ i, Continuous (C.h i) := fun i => (hC.1 i).continuous
  have hgc : ∀ j, Continuous (C.g j) := fun j => (hC.2 j).continuous
  have hFc : Continuous F := hF.continuous
  -- the penalty function
  set P : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ i, (C.h i x) ^ 2 + ∑ j, (max 0 (C.g j x)) ^ 2 with hP
  have hPc : Continuous P := by
    simp only [hP]
    fun_prop
  have hP0 : ∀ x, 0 ≤ P x := fun x => by simp only [hP]; positivity
  have hPbar : P xbar = 0 := by
    simp [hP, hxbar.1, max_eq_left (hxbar.2 _)]
  have hPzero : ∀ x, P x = 0 → x ∈ C.feasible := by
    intro x hx
    simp only [hP] at hx
    have h1 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (C.h i x))
    have h2 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (max 0 (C.g j x)))
    have e1 : ∑ i, (C.h i x) ^ 2 = 0 := by linarith
    have e2 : ∑ j, (max 0 (C.g j x)) ^ 2 = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at e1 e2
    refine ⟨fun i => by simpa using e1 i (Finset.mem_univ _), fun j => ?_⟩
    have := e2 j (Finset.mem_univ _)
    have : max 0 (C.g j x) = 0 := by simpa using this
    exact max_eq_left_iff.1 this
  set Fk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k x => F x + ((k:ℝ) / 2) * P x with hFk
  set B := Metric.closedBall xbar (1:ℝ)
  have hB : IsCompact B := isCompact_closedBall _ _
  have hBne : B.Nonempty := ⟨xbar, Metric.mem_closedBall_self zero_le_one⟩
  have hmin : ∀ k, ∃ x ∈ B, IsMinOn (Fk k) B x := fun k =>
    hB.exists_isMinOn hBne (by simp only [hFk]; fun_prop)
  choose x hxB hxmin using hmin
  obtain ⟨xm, -, hxm⟩ := hB.exists_isMinOn hBne hFc.continuousOn
  set M := F xbar - F xm
  -- key inequality
  have hKI : ∀ k : ℕ, (k:ℝ) * P (x k) ≤ 2 * (F xbar - F (x k)) := by
    intro k
    have := hxmin k (Metric.mem_closedBall_self zero_le_one)
    simp only [hFk, hPbar, mul_zero, add_zero, Set.mem_ofPred_eq] at this
    linarith
  have hFle : ∀ k : ℕ, F (x k) ≤ F xbar := fun k => by
    have := hKI k
    have : 0 ≤ (k:ℝ) * P (x k) := mul_nonneg (Nat.cast_nonneg k) (hP0 _)
    linarith
  have hKM : ∀ k : ℕ, (k:ℝ) * P (x k) ≤ 2 * M := fun k => by
    have := hKI k; have := hxm (hxB k); simp only [Set.mem_ofPred_eq] at this
    simp only [M]; linarith
  -- convergence of the minimizers
  have hxconv : Tendsto x atTop (𝓝 xbar) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set K := B ∩ {z | ε ≤ dist z xbar} ∩ {z | F z ≤ F xbar}
    have hKc : IsCompact K :=
      (hB.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))).inter_right
        (isClosed_le hFc continuous_const)
    rcases K.eq_empty_or_nonempty with hK | hK
    · refine ⟨0, fun k _ => ?_⟩
      by_contra hc
      push Not at hc
      have : x k ∈ K := ⟨⟨hxB k, hc⟩, hFle k⟩
      rw [hK] at this; exact this
    · obtain ⟨x0, hx0K, hx0⟩ := hKc.exists_isMinOn hK hPc.continuousOn
      have hδ : 0 < P x0 := by
        rcases (hP0 x0).lt_or_eq with h | h
        · exact h
        · exfalso
          have hfe := hPzero x0 h.symm
          have hne : x0 ≠ xbar := by
            intro he; have := hx0K.1.2; simp [he] at this; linarith
          have := hFmin x0 hfe hne
          have h2 : F x0 ≤ F xbar := hx0K.2
          linarith
      obtain ⟨N, hN⟩ := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop
        (2 * M / P x0) |> eventually_atTop.1
      refine ⟨N, fun k hk => ?_⟩
      by_contra hc
      push Not at hc
      have hmem : x k ∈ K := ⟨⟨hxB k, hc⟩, hFle k⟩
      have h1 : P x0 ≤ P (x k) := hx0 hmem
      have h2 := hN k hk
      rw [div_lt_iff₀ hδ] at h2
      have h3 := hKM k
      have : (k:ℝ) * P x0 ≤ (k:ℝ) * P (x k) := by gcongr
      linarith
  -- penalty residual tends to zero
  have hkP : Tendsto (fun k : ℕ => (k:ℝ) * P (x k)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k : ℕ => 2 * (F xbar - F (x k))) atTop (𝓝 (2 * (F xbar - F xbar))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub ((hFc.tendsto xbar).comp hxconv))
    simp only [sub_self, mul_zero] at hlim
    exact squeeze_zero (fun k : ℕ => mul_nonneg (Nat.cast_nonneg k) (hP0 _)) hKI hlim
  -- first-order condition, eventually
  have hgradF : Continuous (gradient F) := by
    have : gradient F = fun z => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ F z) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp (hF.continuous_fderiv one_ne_zero)
  have hFOC : ∀ᶠ k : ℕ in atTop, ∑ i, ((k:ℝ) * C.h i (x k)) • gradient (C.h i) (x k) +
      ∑ j, ((k:ℝ) * max 0 (C.g j (x k))) • gradient (C.g j) (x k) = - gradient F (x k) := by
    filter_upwards [hxconv.eventually (Metric.ball_mem_nhds xbar one_pos)] with k hk
    have hloc : IsLocalMin (Fk k) (x k) :=
      (hxmin k).isLocalMin (Metric.closedBall_mem_nhds_of_mem hk)
    have hdF : HasFDerivAt F (fderiv ℝ F (x k)) (x k) :=
      ((hF.differentiable one_ne_zero) _).hasFDerivAt
    have hdh : ∀ i, HasFDerivAt (fun z => (C.h i z) ^ 2)
        ((2 * C.h i (x k)) • fderiv ℝ (C.h i) (x k)) (x k) := fun i => by
      have := ((((hC.1 i).differentiable one_ne_zero) (x k)).hasFDerivAt).pow 2
      refine this.congr_fderiv ?_
      simp
    have hdg : ∀ j, HasFDerivAt (fun z => (max 0 (C.g j z)) ^ 2)
        ((2 * max 0 (C.g j (x k))) • fderiv ℝ (C.g j) (x k)) (x k) := fun j =>
      (cakkt_hasDerivAt_maxsq (C.g j (x k))).comp_hasFDerivAt (x k)
        (((hC.2 j).differentiable one_ne_zero) _).hasFDerivAt
    have hP' : HasFDerivAt P (∑ i, (2 * C.h i (x k)) • fderiv ℝ (C.h i) (x k) +
        ∑ j, (2 * max 0 (C.g j (x k))) • fderiv ℝ (C.g j) (x k)) (x k) := by
      have h1 := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hdh i)
      have h2 := HasFDerivAt.sum (u := Finset.univ) (fun j _ => hdg j)
      have := h1.add h2
      have heq : P = (∑ i, fun z => C.h i z ^ 2) + ∑ i, fun z => max 0 (C.g i z) ^ 2 := by
        ext z; simp [hP, Finset.sum_apply]
      rw [heq]; exact this
    have hFk' := hdF.add (hP'.const_mul ((k:ℝ) / 2))
    have h0 := hloc.hasFDerivAt_eq_zero hFk'
    have h0' := congrArg (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm h0
    simp only [map_add, map_smul, map_sum, map_zero] at h0'
    have hgr : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f (x k)) =
      gradient f (x k) := fun f => rfl
    simp only [hgr] at h0'
    rw [eq_neg_iff_add_eq_zero, add_comm]
    rw [← h0']
    congr 1
    rw [smul_add, Finset.smul_sum, Finset.smul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> rw [smul_smul] <;> ring_nf
  refine ⟨x, fun k i => (k:ℝ) * C.h i (x k), fun k j => (k:ℝ) * max 0 (C.g j (x k)),
    fun k => (k:ℝ), fun k j => by positivity, fun k => Nat.cast_nonneg k, hxconv, ?_,
    fun k j => rfl, ?_⟩
  · have hlim : Tendsto (fun k => - gradient F (x k)) atTop (𝓝 y) := by
      rw [← hFy]; exact ((hgradF.tendsto xbar).comp hxconv).neg
    exact hlim.congr' (hFOC.mono fun k hk => hk.symm)
  · refine hkP.congr' (Eventually.of_forall fun k => ?_)
    simp only [hP, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) (mul_self_nonneg _))]
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hm : max 0 (C.g j (x k)) * C.g j (x k) = (max 0 (C.g j (x k))) ^ 2 := by
        rcases le_total (C.g j (x k)) 0 with h | h
        · simp [max_eq_left h]
        · simp [max_eq_right h, sq]
      rw [mul_assoc, hm, abs_of_nonneg (by positivity)]
