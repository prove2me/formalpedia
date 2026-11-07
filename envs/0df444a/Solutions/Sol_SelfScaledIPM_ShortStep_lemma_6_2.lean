-- Prove2me | solution 1 for SelfScaledIPM.ShortStep.lemma_6_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:48:36.508587+00:00
-- url     : https://prove2.me/submissions/af245ae3-daf1-42fe-8306-12a4b909c34a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Theorems.Thm_ExpConeIPM_Corrector_homogeneity_identities
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


theorem dual_add' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) {y₁ y₂ : EuclideanSpace ℝ (Fin n)}
    (h₁ : y₁ ∈ ConvexOptimization.dualCone K) (h₂ : y₂ ∈ ConvexOptimization.dualCone K) :
    y₁ + y₂ ∈ ConvexOptimization.dualCone K := by
  intro z hz
  rw [inner_add_right]
  exact add_nonneg (h₁ z hz) (h₂ z hz)

theorem dual_smul' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) {y : EuclideanSpace ℝ (Fin n)}
    (h : y ∈ ConvexOptimization.dualCone K) {t : ℝ} (ht : 0 ≤ t) :
    t • y ∈ ConvexOptimization.dualCone K := by
  intro z hz
  rw [real_inner_smul_right]
  exact mul_nonneg ht (h z hz)

theorem sigma_set_nonempty {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} (hc : c ∈ interior (ConvexOptimization.dualCone K))
    (u : EuclideanSpace ℝ (Fin n)) :
    ∃ β : ℝ, 0 ≤ β ∧ β • c - u ∈ ConvexOptimization.dualCone K := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc)
  set β := 2 * ‖u‖ / r + 1
  have hβ : 0 < β := by positivity
  refine ⟨β, hβ.le, ?_⟩
  have hmem : c - β⁻¹ • u ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hβ]
    rw [inv_mul_lt_iff₀ hβ]
    have : β * r = 2 * ‖u‖ + r := by simp only [β]; field_simp
    rw [this]; have := norm_nonneg u; linarith
  have := dual_smul' K (hball hmem) hβ.le
  rwa [smul_sub, smul_smul, mul_inv_cancel₀ hβ.ne', one_smul] at this

theorem sigma_le_of {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (c u : EuclideanSpace ℝ (Fin n)) {β : ℝ} (hβ : 0 ≤ β)
    (h : β • c - u ∈ ConvexOptimization.dualCone K) :
    sigma (ConvexOptimization.dualCone K) c u ≤ β :=
  csInf_le ⟨0, fun _ hb => hb.1⟩ ⟨hβ, h⟩

theorem sigma_nonneg' {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (c u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ sigma C c u :=
  Real.sInf_nonneg (fun _ hb => hb.1)

theorem le_sigma_of {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} (hc : c ∈ interior (ConvexOptimization.dualCone K))
    (u : EuclideanSpace ℝ (Fin n)) {a : ℝ}
    (h : ∀ β, 0 ≤ β → β • c - u ∈ ConvexOptimization.dualCone K → a ≤ β) :
    a ≤ sigma (ConvexOptimization.dualCone K) c u := by
  obtain ⟨β, hβ, hm⟩ := sigma_set_nonempty K hc u
  exact le_csInf ⟨β, hβ, hm⟩ (fun b hb => h b hb.1 hb.2)

theorem sigma_add_le' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} (hc : c ∈ interior (ConvexOptimization.dualCone K))
    (u v : EuclideanSpace ℝ (Fin n)) :
    sigma (ConvexOptimization.dualCone K) c (u + v) ≤
      sigma (ConvexOptimization.dualCone K) c u + sigma (ConvexOptimization.dualCone K) c v := by
  have key : ∀ β₁, 0 ≤ β₁ → β₁ • c - u ∈ ConvexOptimization.dualCone K →
      ∀ β₂, 0 ≤ β₂ → β₂ • c - v ∈ ConvexOptimization.dualCone K →
      sigma (ConvexOptimization.dualCone K) c (u + v) ≤ β₁ + β₂ := by
    intro β₁ h₁ m₁ β₂ h₂ m₂
    apply sigma_le_of K c _ (add_nonneg h₁ h₂)
    have := dual_add' K m₁ m₂
    convert this using 1
    rw [add_smul]; abel
  have h1 : sigma (ConvexOptimization.dualCone K) c (u + v) -
      sigma (ConvexOptimization.dualCone K) c v ≤ sigma (ConvexOptimization.dualCone K) c u := by
    apply le_sigma_of K hc
    intro β₁ h₁ m₁
    have : sigma (ConvexOptimization.dualCone K) c (u + v) - β₁ ≤
        sigma (ConvexOptimization.dualCone K) c v := by
      apply le_sigma_of K hc
      intro β₂ h₂ m₂
      have := key β₁ h₁ m₁ β₂ h₂ m₂
      linarith
    linarith
  linarith

theorem sigma_smul_le' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} (hc : c ∈ interior (ConvexOptimization.dualCone K))
    (u : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    sigma (ConvexOptimization.dualCone K) c (t • u) ≤
      t * sigma (ConvexOptimization.dualCone K) c u := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [zero_smul, zero_mul]
    apply sigma_le_of K c 0 le_rfl
    simp only [zero_smul, sub_zero]
    intro z _; simp
  · have : sigma (ConvexOptimization.dualCone K) c (t • u) / t ≤
        sigma (ConvexOptimization.dualCone K) c u := by
      apply le_sigma_of K hc
      intro β hβ hm
      rw [div_le_iff₀ hpos]
      apply sigma_le_of K c _ (by positivity)
      have := dual_smul' K hm ht
      convert this using 1
      rw [smul_sub, smul_smul, mul_comm]
    rwa [div_le_iff₀ hpos, mul_comm] at this

theorem absn_add_le' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} (hc : c ∈ interior (ConvexOptimization.dualCone K))
    (u v : EuclideanSpace ℝ (Fin n)) :
    absn (ConvexOptimization.dualCone K) c (u + v) ≤
      absn (ConvexOptimization.dualCone K) c u + absn (ConvexOptimization.dualCone K) c v := by
  unfold absn
  have h1 := sigma_add_le' K hc u v
  have h2 := sigma_add_le' K hc (-u) (-v)
  rw [← neg_add] at h2
  apply max_le
  · linarith [le_max_left (sigma (ConvexOptimization.dualCone K) c u)
      (sigma (ConvexOptimization.dualCone K) c (-u)),
      le_max_left (sigma (ConvexOptimization.dualCone K) c v)
      (sigma (ConvexOptimization.dualCone K) c (-v))]
  · linarith [le_max_right (sigma (ConvexOptimization.dualCone K) c u)
      (sigma (ConvexOptimization.dualCone K) c (-u)),
      le_max_right (sigma (ConvexOptimization.dualCone K) c v)
      (sigma (ConvexOptimization.dualCone K) c (-v))]

theorem absn_smul_le' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} (hc : c ∈ interior (ConvexOptimization.dualCone K))
    (u : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    absn (ConvexOptimization.dualCone K) c (t • u) ≤
      t * absn (ConvexOptimization.dualCone K) c u := by
  unfold absn
  have h1 := sigma_smul_le' K hc u ht
  have h2 := sigma_smul_le' K hc (-u) ht
  rw [smul_neg] at h2
  apply max_le
  · exact h1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) ht)
  · exact h2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)

theorem absn_neg' {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (c u : EuclideanSpace ℝ (Fin n)) :
    absn C c (-u) = absn C c u := by
  unfold absn; rw [neg_neg, max_comm]

theorem dnorm_smul' {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (x u : EuclideanSpace ℝ (Fin n))
    (t : ℝ) : dnorm F x (t • u) = |t| * dnorm F x u := by
  unfold dnorm
  rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← sq,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (β κ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (x s : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) (hl2 : lambda2 F ν x s ≤ β) :
    let δ := lambdaInf K F ν x s
    let ε := lambda2 F ν x s
    let μp := muPlus ν κ x s
    let δp := absn (ConvexOptimization.dualCone K) (-gradient F x) (μp⁻¹ • s + gradient F x)
    let εp := lambda2bar F x s μp
    δp ≤ εp ∧ δp ≤ (δ + κ) / (1 - κ) ∧ εp ≤ (ε + κ) / (1 - κ) := by
  intro δ ε μp δp εp
  obtain ⟨-, hp2, -, -⟩ := SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF
  obtain ⟨-, -, hHx, -, -⟩ :=
    ExpConeIPM.Corrector.homogeneity_identities K F ν hK hF.1 x hx 1 one_pos
  have hgx : ⟪gradient F x, x⟫_ℝ = -ν :=
    (ExpConeIPM.Corrector.homogeneity_identities K F ν hK hF.1 x hx 1 one_pos).2.2.2.2
  set g := gradient F x with hg_def
  set μ := mu ν x s with hμ_def
  have hμ : 0 < μ := mu_pos_aux K F ν hν hF x s hx hs
  have hsq : 1 ≤ Real.sqrt ν := by rw [Real.one_le_sqrt]; exact hν
  set θ := κ / Real.sqrt ν with hθ_def
  have hθ0 : 0 < θ := by positivity
  have hθκ : θ ≤ κ := by
    rw [hθ_def, div_le_iff₀ (by linarith)]; nlinarith
  have hθ1 : θ < 1 := by linarith
  have hμp : μp = (1 - θ) * μ := rfl
  set a := (1 - θ)⁻¹ with ha_def
  have ha1 : 1 ≤ a := by rw [ha_def]; exact one_le_inv₀ (by linarith) |>.mpr (by linarith)
  set U := μ⁻¹ • s + g with hU_def
  have hdecomp : μp⁻¹ • s + g = a • U + (a - 1) • (-g) := by
    rw [hμp, hU_def, ha_def, mul_inv, smul_add, smul_smul, smul_neg, sub_smul, one_smul]
    abel
  -- center is interior
  have hc : -g ∈ interior (ConvexOptimization.dualCone K) := by
    have := (hF.2 x hx x hx).1
    rwa [hHx] at this
  have hδ0 : 0 ≤ δ := le_max_of_le_left (sigma_nonneg' _ _ _)
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  refine ⟨(hp2 x hx _).1, ?_, ?_⟩
  · -- δp bound
    have habs_g : absn (ConvexOptimization.dualCone K) (-g) (-g) ≤ 1 := by
      unfold absn
      apply max_le
      · apply sigma_le_of K _ _ zero_le_one
        rw [one_smul, sub_self]; intro z _; simp
      · apply sigma_le_of K _ _ zero_le_one
        rw [one_smul, neg_neg]
        rw [show -g - g = (2:ℝ) • (-g) by rw [two_smul]; abel]
        exact dual_smul' K (interior_subset hc) (by norm_num)
    have h1 : δp ≤ a * δ + (a - 1) * 1 := by
      show absn _ _ (μp⁻¹ • s + g) ≤ _
      rw [hdecomp]
      calc _ ≤ absn (ConvexOptimization.dualCone K) (-g) (a • U) +
            absn (ConvexOptimization.dualCone K) (-g) ((a - 1) • (-g)) := absn_add_le' K hc _ _
        _ ≤ a * δ + (a - 1) * 1 := by
          apply add_le_add (absn_smul_le' K hc U (by linarith))
          exact (absn_smul_le' K hc (-g) (by linarith)).trans
            (mul_le_mul_of_nonneg_left habs_g (by linarith))
    have h2 : a * δ + (a - 1) * 1 = (δ + θ) / (1 - θ) := by
      have hne : 1 - θ ≠ 0 := by linarith
      rw [ha_def]; field_simp; ring
    rw [h2] at h1
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · -- εp bound
    have hdg : dnorm F x (-g) ≤ Real.sqrt ν := by
      unfold dnorm
      apply Real.sqrt_le_sqrt
      by_cases h : (hess F x).IsInvertible
      · obtain ⟨e, he⟩ := h
        rw [← he, ContinuousLinearMap.inverse_equiv]
        have : (e.symm (-g)) = x := by
          rw [← hHx, ← he]; simp
        simp only [ContinuousLinearEquiv.coe_coe] at *
        rw [this, inner_neg_right, real_inner_comm, hgx]; simp
      · rw [ContinuousLinearMap.inverse_of_not_isInvertible h]; simp; linarith
    have hpsd : ∀ z, 0 ≤ ⟪hess F x z, z⟫_ℝ := by
      intro z
      by_cases hz : z = 0
      · simp [hz]
      · exact (hF.1.2.2.2.2 x hx z hz).le
    have h1 : εp ≤ a * ε + (a - 1) * Real.sqrt ν := by
      show dnorm F x (μp⁻¹ • s + g) ≤ _
      rw [hdecomp]
      calc _ ≤ dnorm F x (a • U) + dnorm F x ((a - 1) • (-g)) :=
            sqrt_form_add_le _ (inverse_form_nonneg _ hpsd) _ _
        _ = a * ε + (a - 1) * dnorm F x (-g) := by
          rw [dnorm_smul', dnorm_smul', abs_of_nonneg (by linarith),
            abs_of_nonneg (by linarith)]; rfl
        _ ≤ a * ε + (a - 1) * Real.sqrt ν := by
          gcongr
    have h2 : a * ε + (a - 1) * Real.sqrt ν = (ε + κ) / (1 - θ) := by
      rw [ha_def, hθ_def]
      have : Real.sqrt ν ≠ 0 := by linarith
      have hne : Real.sqrt ν - κ ≠ 0 := by nlinarith
      have hne' : 1 - κ / Real.sqrt ν ≠ 0 := by rw [← hθ_def]; linarith
      field_simp; ring
    rw [h2] at h1
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
