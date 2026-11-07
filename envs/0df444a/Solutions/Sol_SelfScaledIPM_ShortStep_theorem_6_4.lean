-- Prove2me | solution 1 for SelfScaledIPM.ShortStep.theorem_6_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:39:55.188196+00:00
-- url     : https://prove2.me/submissions/5b2f2519-7ae9-48f5-9a08-bb3521ca9c87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Theorems.Thm_SelfScaledIPM_ShortStep_lemma_6_2
import Theorems.Thm_SelfScaledIPM_ShortStep_lemma_6_3
import Theorems.Thm_SelfScaledIPM_ShortStep_corollary_3_14
import Theorems.Thm_SelfScaledIPM_ShortStep_eq_6_10
import Theorems.Thm_SelfScaledLongStep_PathFollow_theorem_4_3
import Theorems.Thm_SelfScaledIPM_FuncProx_proposition_3_5

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

/-- Triangle inequality for `u ↦ √⟪P u, u⟫` when the quadratic form of `P` is nonnegative. -/
theorem sqrt_form_add_le {n : ℕ}
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hP : ∀ u, 0 ≤ ⟪P u, u⟫_ℝ) (a b : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt ⟪P (a + b), a + b⟫_ℝ ≤ Real.sqrt ⟪P a, a⟫_ℝ + Real.sqrt ⟪P b, b⟫_ℝ := by
  set qa := ⟪P a, a⟫_ℝ
  set qb := ⟪P b, b⟫_ℝ
  set c := ⟪P a, b⟫_ℝ + ⟪P b, a⟫_ℝ
  have hqa : 0 ≤ qa := hP a
  have hqb : 0 ≤ qb := hP b
  have hexp : ∀ t : ℝ, ⟪P (t • a + b), t • a + b⟫_ℝ = qa * t * t + c * t + qb := by
    intro t
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, qa, qb, c]
    simp only [RCLike.conj_to_real]
    ring
  have hdisc : discrim qa c qb ≤ 0 := by
    apply discrim_le_zero
    intro t
    have := hP (t • a + b)
    rw [hexp t] at this
    linarith
  unfold discrim at hdisc
  have hsa := Real.sq_sqrt hqa
  have hsb := Real.sq_sqrt hqb
  have hsa0 := Real.sqrt_nonneg qa
  have hsb0 := Real.sqrt_nonneg qb
  have hc : c ≤ 2 * Real.sqrt qa * Real.sqrt qb := by
    have h1 : c ^ 2 ≤ (2 * Real.sqrt qa * Real.sqrt qb) ^ 2 := by
      have : (2 * Real.sqrt qa * Real.sqrt qb) ^ 2 = 4 * qa * qb := by
        rw [mul_pow, mul_pow, hsa, hsb]; ring
      rw [this]; linarith
    have := abs_le_of_sq_le_sq' h1 (by positivity)
    exact this.2
  have hab : ⟪P (a + b), a + b⟫_ℝ = qa + c + qb := by
    have := hexp 1
    simpa using this
  rw [hab]
  calc Real.sqrt (qa + c + qb) ≤ Real.sqrt ((Real.sqrt qa + Real.sqrt qb) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = Real.sqrt qa + Real.sqrt qb := Real.sqrt_sq (by positivity)

theorem absn_nonneg' {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (c u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ absn C c u := by
  unfold absn sigma
  exact le_max_of_le_left (Real.sInf_nonneg (fun _ hb => hb.1))

theorem inverse_form_nonneg {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ z, 0 ≤ ⟪H z, z⟫_ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪H.inverse u, u⟫_ℝ := by
  by_cases h : ∃ e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = H
  · obtain ⟨e, rfl⟩ := h
    rw [ContinuousLinearMap.inverse_equiv]
    have := hH (e.symm u)
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at this
    rw [real_inner_comm] at this
    simpa using this
  · rw [ContinuousLinearMap.inverse_of_not_isInvertible h]
    simp

theorem mu_pos_aux {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x s : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) : 0 < mu ν x s := by
  have hx0 : x ≠ 0 := by
    intro h0
    have := hF.1.2.2.2.1 x hx 2 (by norm_num)
    rw [h0, smul_zero] at this
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hs)
  set t := r / (2 * ‖x‖)
  have ht : 0 < t := by positivity
  have hmem : s - t • x ∈ Metric.ball s r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have : t * ‖x‖ = r / 2 := by simp only [t]; field_simp
    rw [this]; linarith
  have h1 := hball hmem x (interior_subset hx)
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
  have h2 : 0 < ⟪x, s⟫_ℝ := by
    have : 0 < t * ‖x‖ ^ 2 := by positivity
    linarith
  unfold mu
  rw [real_inner_comm] at h2
  exact div_pos h2 (by linarith)

theorem solution {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (β κ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n))
    (hN : InN K F A b c ν β x y s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : IsScalingPoint K F x s w)
    (qx : EuclideanSpace ℝ (Fin n)) (qy : EuclideanSpace ℝ (Fin m)) (qs : EuclideanSpace ℝ (Fin n))
    (hq : IsShortStepDir F A x s w (muPlus ν κ x s) qx qy qs)
    (hη : eta K F ν κ x s < 1) :
    let δ := lambdaInf K F ν x s
    let ε := lambda2 F ν x s
    let μp := muPlus ν κ x s
    let xp := x - qx
    let sp := s - qs
    (xp ∈ interior K ∧ sp ∈ interior (ConvexOptimization.dualCone K)) ∧
    mu ν xp sp = μp ∧
    lambda2 F ν xp sp = lambda2bar F xp sp μp ∧
    lambda2bar F xp sp μp ≤ (2 + δ - κ) * (ε + κ) ^ 2 / ((1 - δ) ^ 2 * (1 - κ) ^ 3) := by
  intro δ ε μp xp sp
  obtain ⟨hP, hD, hl2⟩ := hN
  have hx := hP.1
  have hs := hD.1
  obtain ⟨hdp_ep, hdp_up, hep_up⟩ :=
    SelfScaledIPM.ShortStep.lemma_6_2 K hK F ν hν hF β κ hβ0 hβ1 hκ0 hκ1 x s hx hs hl2
  obtain ⟨⟨-, hep1⟩, hLq, -, hP', hD', -, hdn⟩ :=
    SelfScaledIPM.ShortStep.lemma_6_3 K hK F ν hν hF A hA b c β κ hβ0 hβ1 hκ0 hκ1 x y s
      ⟨hP, hD, hl2⟩ w hw qx qy qs hq hη
  obtain ⟨-, -, hmu⟩ :=
    SelfScaledIPM.ShortStep.eq_6_10 K hK F ν hν hF A hA b c x y s hP hD w hw μp qx qy qs hq
  obtain ⟨hp1, hp2, -, -⟩ := SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF
  -- basic positivity
  have hδε : δ ≤ ε := (hp2 x hx _).1
  have hδ1 : δ < 1 := lt_of_le_of_lt (le_trans hδε hl2) hβ1
  have hδ0 : 0 ≤ δ := absn_nonneg' _ _ _
  have hμ : 0 < mu ν x s := mu_pos_aux K F ν hν hF x s hx hs
  have hsq : 1 ≤ Real.sqrt ν := by rw [Real.one_le_sqrt]; exact hν
  have hμp : 0 < μp := by
    have : κ / Real.sqrt ν < 1 := by rw [div_lt_one (by linarith)]; linarith
    exact mul_pos (by linarith) hμ
  refine ⟨⟨hP'.1, hD'.1⟩, hmu, ?_, ?_⟩
  · show lambda2bar F xp sp (mu ν xp sp) = _
    rw [hmu]
  -- main inequality
  set δp := absn (ConvexOptimization.dualCone K) (-gradient F x) (μp⁻¹ • s + gradient F x)
    with hδp_def
  set εp := lambda2bar F x s μp with hεp_def
  set η := eta K F ν κ x s with hη_def
  have hηeq : η = εp / (1 - δ) := rfl
  have hεp0 : 0 ≤ εp := Real.sqrt_nonneg _
  have hδp0 : 0 ≤ δp := absn_nonneg' _ _ _
  have hcor := (SelfScaledIPM.ShortStep.corollary_3_14 K hK F ν hν hF x s w hx hs hw μp hμp
    (lt_of_le_of_lt hdp_ep hep1)).1 qx
  have ht43 := SelfScaledLongStep.PathFollow.theorem_4_3 K hK F ν hν hF x xp hx hP'.1
  set L := lnorm F x qx with hL_def
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hxpx : xp - x = -qx := by simp [xp]
  have hLneg : lnorm F x (-qx) = L := by
    simp [lnorm, L]
  have hab := (hp1 x hx (-qx)).1
  rw [hLneg] at hab
  rw [hxpx, hLneg] at ht43
  set T1 := (μp⁻¹ • hess F w - hess F x) qx
  set T2 := gradient F xp - gradient F x - hess F x (-qx)
  have hvec : μp⁻¹ • sp + gradient F xp = T1 + T2 := by
    have h1 : s = hess F w qx + qs - μp • gradient F x := by
      rw [hq.1]; abel
    simp only [T1, T2, sp]
    rw [h1]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_neg,
      smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hμp.ne', one_smul]
    abel
  have hpsd : ∀ z, 0 ≤ ⟪hess F xp z, z⟫_ℝ := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · exact (hF.1.2.2.2.2 xp hP'.1 z hz).le
  have htri : lambda2bar F xp sp μp ≤ dnorm F xp T1 + dnorm F xp T2 := by
    show dnorm F xp (μp⁻¹ • sp + gradient F xp) ≤ _
    rw [hvec]
    exact sqrt_form_add_le _ (inverse_form_nonneg _ hpsd) T1 T2
  have hT1 : dnorm F xp T1 ≤ (1 + η) * (δp * L) := by
    have hη0 : 0 ≤ η := le_trans hL0 hLq
    calc dnorm F xp T1 ≤ (1 + η) * dnorm F x T1 := hdn T1
      _ ≤ (1 + η) * (δp * L) := mul_le_mul_of_nonneg_left hcor (by linarith)
  have hT2 : dnorm F xp T2 ≤ L * L := by
    calc dnorm F xp T2 ≤ absn K x (-qx) * L := ht43
      _ ≤ L * L := mul_le_mul_of_nonneg_right hab hL0
  have hη0 : 0 ≤ η := le_trans hL0 hLq
  have hD0 : 0 < 1 - δ := by linarith
  have hεpη : εp = η * (1 - δ) := by rw [hηeq]; field_simp
  have hdpη : δp ≤ η := by
    calc δp ≤ εp := hdp_ep
      _ = η * (1 - δ) := hεpη
      _ ≤ η := by nlinarith
  have hstep1 : lambda2bar F xp sp μp ≤ (2 + δp) * η ^ 2 := by
    have a1 : (1 + η) * (δp * L) ≤ (1 + η) * (δp * η) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLq hδp0) (by linarith)
    have a2 : L * L ≤ η * η := mul_le_mul hLq hLq hL0 hη0
    have a3 : δp * η ≤ η * η := mul_le_mul_of_nonneg_right hdpη hη0
    nlinarith
  have hk0 : 0 < 1 - κ := by linarith
  have hA1 : 2 + δp ≤ (2 + δ - κ) / (1 - κ) := by
    rw [le_div_iff₀ hk0]
    have := (le_div_iff₀ hk0).mp hdp_up
    nlinarith
  have hA2 : η ^ 2 ≤ ((ε + κ) / (1 - κ)) ^ 2 / (1 - δ) ^ 2 := by
    rw [hηeq, div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ hεp0 hep_up 2
  calc lambda2bar F xp sp μp ≤ (2 + δp) * η ^ 2 := hstep1
    _ ≤ (2 + δ - κ) / (1 - κ) * (((ε + κ) / (1 - κ)) ^ 2 / (1 - δ) ^ 2) :=
        mul_le_mul hA1 hA2 (sq_nonneg _) (by
          have : 0 ≤ 2 + δp := by linarith
          exact le_trans this hA1)
    _ = (2 + δ - κ) * (ε + κ) ^ 2 / ((1 - δ) ^ 2 * (1 - κ) ^ 3) := by
        field_simp
