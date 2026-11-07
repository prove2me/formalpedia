-- Prove2me | solution 1 for SelfScaledIPM.ShortStep.lemma_6_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:56:51.50521+00:00
-- url     : https://prove2.me/submissions/b7e5b5a3-fae2-4bcd-9fd0-0bf475180cdb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Theorems.Thm_SelfScaledIPM_ShortStep_lemma_3_13
import Theorems.Thm_SelfScaledIPM_ShortStep_theorem_3_6
import Theorems.Thm_SelfScaledIPM_ShortStep_eq_6_10
import Theorems.Thm_SelfScaledIPM_ShortStep_lemma_6_3_qs_bound
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


theorem hess_inner_eq' {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (x v w : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ F) x v w := by
  unfold hess
  have : gradient F = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ∘ fderiv ℝ F := by
    funext y; rfl
  rw [this, LinearIsometryEquiv.comp_fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

theorem cs_form {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsym : ∀ v w, ⟪H v, w⟫_ℝ = ⟪H w, v⟫_ℝ) (hpsd : ∀ z, 0 ≤ ⟪H z, z⟫_ℝ)
    (p v : EuclideanSpace ℝ (Fin n)) :
    ⟪H p, v⟫_ℝ ≤ Real.sqrt ⟪H p, p⟫_ℝ * Real.sqrt ⟪H v, v⟫_ℝ := by
  set a := ⟪H p, p⟫_ℝ
  set c := ⟪H v, v⟫_ℝ
  set b := ⟪H p, v⟫_ℝ
  have hexp : ∀ t : ℝ, ⟪H (t • p + v), t • p + v⟫_ℝ = a * t * t + (2 * b) * t + c := by
    intro t
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real, a, b, c]
    rw [hsym v p]; ring
  have hdisc : discrim a (2 * b) c ≤ 0 := by
    apply discrim_le_zero
    intro t
    have := hpsd (t • p + v)
    rw [hexp t] at this
    linarith
  unfold discrim at hdisc
  have ha := hpsd p
  have hc := hpsd v
  have h1 : b ^ 2 ≤ (Real.sqrt a * Real.sqrt c) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hc]; nlinarith
  exact (abs_le_of_sq_le_sq' h1 (by positivity)).2


theorem hess_symm' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (v w : EuclideanSpace ℝ (Fin n)) : ⟪hess F x v, w⟫_ℝ = ⟪hess F x w, v⟫_ℝ := by
  have hcd : ContDiffAt ℝ 3 F x :=
    hF.1.1.2.1.contDiffAt (isOpen_interior.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℝ F x :=
    hcd.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast (by norm_num : (2:ℕ) ≤ 3))
  rw [hess_inner_eq', hess_inner_eq', hsymm v w]

theorem hess_psd' {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (z : EuclideanSpace ℝ (Fin n)) : 0 ≤ ⟪hess F x z, z⟫_ℝ := by
  by_cases hz : z = 0
  · simp [hz]
  · exact (hF.1.2.2.2.2 x hx z hz).le

theorem cs_dual {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (ν : ℝ) (hF : IsSelfScaledBarrier K F ν) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (u v : EuclideanSpace ℝ (Fin n)) : ⟪u, v⟫_ℝ ≤ dnorm F x u * lnorm F x v := by
  set H := hess F x
  have hinj : Function.Injective H := by
    intro z₁ z₂ h
    by_contra hne
    have hz : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
    have := hF.1.2.2.2.2 x hx (z₁ - z₂) hz
    rw [map_sub, h, sub_self, inner_zero_left] at this
    exact lt_irrefl _ this
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofInjectiveEndo H.toLinearMap hinj).toContinuousLinearEquiv
  have he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = H := by
    ext z; rfl
  set p := e.symm u
  have hu : u = H p := by rw [← he]; simp [p]
  have hd : dnorm F x u = Real.sqrt ⟪H p, p⟫_ℝ := by
    show Real.sqrt ⟪H.inverse u, u⟫_ℝ = _
    rw [← he, ContinuousLinearMap.inverse_equiv]
    simp only [ContinuousLinearEquiv.coe_coe, p, ContinuousLinearEquiv.apply_symm_apply]
    rw [real_inner_comm]
  rw [hd, hu]
  exact cs_form H (hess_symm' K F ν hF x hx) (hess_psd' K F ν hF x hx) p v

/-- For a cone `C` closed under addition, `int C + C ⊆ int C`. -/
theorem interior_add_mem {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hadd : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C) {z k : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ interior C) (hk : k ∈ C) : z + k ∈ interior C := by
  rw [mem_interior]
  refine ⟨(fun y => y - k) ⁻¹' interior C, ?_, ?_, ?_⟩
  · intro y hy
    have := hadd _ (interior_subset hy) k hk
    simpa using this
  · exact isOpen_interior.preimage (continuous_id.sub continuous_const)
  · simpa using hz

theorem interior_smul_mem {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hsmul : ∀ a ∈ C, ∀ t : ℝ, 0 ≤ t → t • a ∈ C) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ interior C) {t : ℝ} (ht : 0 < t) : t • z ∈ interior C := by
  rw [mem_interior]
  refine ⟨(fun y => t⁻¹ • y) ⁻¹' interior C, ?_, ?_, ?_⟩
  · intro y hy
    have := hsmul _ (interior_subset hy) t ht.le
    simp only [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at this
    exact this
  · exact isOpen_interior.preimage (continuous_const_smul _)
  · simp [smul_smul, inv_mul_cancel₀ ht.ne', hz]

/-- If `|q|_z < 1` (cone `C`, centre `z ∈ int C`), then `z − q ∈ int C`. -/
theorem sub_mem_interior_of_absn_lt {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hadd : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C) (hsmul : ∀ a ∈ C, ∀ t : ℝ, 0 ≤ t → t • a ∈ C)
    {z q : EuclideanSpace ℝ (Fin n)} (hz : z ∈ interior C) (h : absn C z q < 1) :
    z - q ∈ interior C := by
  have hσ : sigma C z q < 1 := lt_of_le_of_lt (le_max_left _ _) h
  -- the set is nonempty
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  have hne : {β : ℝ | 0 ≤ β ∧ β • z - q ∈ C}.Nonempty := by
    set β := 2 * ‖q‖ / r + 1
    have hβ : 0 < β := by positivity
    refine ⟨β, hβ.le, ?_⟩
    have hmem : z - β⁻¹ • q ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hβ]
      rw [inv_mul_lt_iff₀ hβ]
      have : β * r = 2 * ‖q‖ + r := by simp only [β]; field_simp
      rw [this]; have := norm_nonneg q; linarith
    have := hsmul _ (hball hmem) β hβ.le
    rwa [smul_sub, smul_smul, mul_inv_cancel₀ hβ.ne', one_smul] at this
  obtain ⟨β, ⟨hβ0, hβm⟩, hβ1⟩ := exists_lt_of_csInf_lt hne hσ
  have h1 : (1 - β) • z ∈ interior C := interior_smul_mem C hsmul hz (by linarith)
  have := interior_add_mem C hadd h1 hβm
  convert this using 1
  rw [sub_smul, one_smul]; abel

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
    let μp := muPlus ν κ x s
    let δp := absn (ConvexOptimization.dualCone K) (-gradient F x) (μp⁻¹ • s + gradient F x)
    let εp := lambda2bar F x s μp
    let η := eta K F ν κ x s
    (δp ≤ εp ∧ εp < 1) ∧
    lnorm F x qx ≤ η ∧ lnorm (conj K F) s qs ≤ η ∧
    IsPrimalStrict K A b (x - qx) ∧ IsDualStrict K A c (y - qy) (s - qs) ∧
    (∀ v : EuclideanSpace ℝ (Fin n), lnorm F (x - qx) v ≤ (1 - η)⁻¹ * lnorm F x v) ∧
    (∀ u : EuclideanSpace ℝ (Fin n), dnorm F (x - qx) u ≤ (1 + η) * dnorm F x u) := by
  intro μp δp εp η
  have hqs := SelfScaledIPM.ShortStep.lemma_6_3_qs_bound K hK F ν hν hF A hA b c β κ hβ0 hβ1
    hκ0 hκ1 x y s hN w hw qx qy qs hq hη
  obtain ⟨hP, hD, hl2⟩ := hN
  have hx := hP.1
  have hs := hD.1
  obtain ⟨hp1, hp2, hp3, -⟩ := SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF
  obtain ⟨hAx, hAy, -⟩ :=
    SelfScaledIPM.ShortStep.eq_6_10 K hK F ν hν hF A hA b c x y s hP hD w hw μp qx qy qs hq
  set δ := lambdaInf K F ν x s with hδ_def
  set ε := lambda2 F ν x s with hε_def
  set g := gradient F x with hg_def
  have hδε : δ ≤ ε := (hp2 x hx _).1
  have hδ1 : δ < 1 := lt_of_le_of_lt (le_trans hδε hl2) hβ1
  have hδ0 : 0 ≤ δ := absn_nonneg' _ _ _
  set μ := mu ν x s with hμ_def
  have hμ : 0 < μ := mu_pos_aux K F ν hν hF x s hx hs
  have hsq : 1 ≤ Real.sqrt ν := by rw [Real.one_le_sqrt]; exact hν
  set θ := κ / Real.sqrt ν with hθ_def
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by
    rw [hθ_def, div_lt_one (by linarith)]; linarith
  have hμp_eq : μp = (1 - θ) * μ := rfl
  have hμp : 0 < μp := by rw [hμp_eq]; exact mul_pos (by linarith) hμ
  have hηeq : η = εp / (1 - δ) := rfl
  have hεp0 : 0 ≤ εp := Real.sqrt_nonneg _
  have hD0 : 0 < 1 - δ := by linarith
  have hη0 : 0 ≤ η := by rw [hηeq]; positivity
  have hεpη : εp = η * (1 - δ) := by rw [hηeq]; field_simp
  -- ‖q_x‖_x ≤ η
  set L := lnorm F x qx with hL_def
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hLsq : L ^ 2 = ⟪hess F x qx, qx⟫_ℝ := Real.sq_sqrt (hess_psd' K F ν hF x hx qx)
  have h313 := (SelfScaledIPM.ShortStep.lemma_3_13 K hK F ν hν hF x s w hx hs hw μ hμ hδ1).1 qx
  have horth : ⟪qs, qx⟫_ℝ = 0 := by
    have : qs = -(ContinuousLinearMap.adjoint A qy) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hq.2.2
    rw [this, inner_neg_left, ContinuousLinearMap.adjoint_inner_left, hq.2.1, inner_zero_right,
      neg_zero]
  have hw_eq : ⟪hess F w qx, qx⟫_ℝ = μp * ⟪μp⁻¹ • s + g, qx⟫_ℝ := by
    have h1 : ⟪hess F w qx + qs, qx⟫_ℝ = ⟪s + μp • g, qx⟫_ℝ := by rw [hq.1]
    rw [inner_add_left, horth, add_zero] at h1
    rw [h1, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      mul_add, ← mul_assoc, mul_inv_cancel₀ hμp.ne', one_mul]
  have hcs : ⟪μp⁻¹ • s + g, qx⟫_ℝ ≤ εp * L := cs_dual K F ν hF x hx _ _
  have hLη : L ≤ η := by
    have k1 : (1 - δ) * L ^ 2 ≤ μp * (εp * L) / μ := by
      rw [hLsq]
      calc (1 - δ) * ⟪hess F x qx, qx⟫_ℝ ≤ ⟪hess F w qx, qx⟫_ℝ / μ := h313.1
        _ ≤ μp * (εp * L) / μ := by
          rw [hw_eq]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcs hμp.le) hμ.le
    have k2 : μp * (εp * L) / μ = (1 - θ) * (εp * L) := by
      rw [hμp_eq]; field_simp
    rw [k2, hεpη] at k1
    have k3 : 0 ≤ η * L := mul_nonneg hη0 hL0
    have k4 : L ^ 2 ≤ η * L := by
      have h0 : 0 ≤ η * (1 - δ) * L := by positivity
      have h1 : (1 - θ) * (η * (1 - δ) * L) ≤ η * (1 - δ) * L := by nlinarith
      have h2 : (1 - θ) * (η * (1 - δ) * L) = (1 - θ) * (η * (1 - δ) * L) := rfl
      have : (1 - δ) * L ^ 2 ≤ (1 - δ) * (η * L) := by
        have e1 : (1 - δ) * (η * L) = η * (1 - δ) * L := by ring
        have e2 : (1 - θ) * (η * (1 - δ) * L) = (1 - θ) * (η * (1 - δ) * L) := rfl
        rw [e1]
        calc (1 - δ) * L ^ 2 ≤ (1 - θ) * (η * (1 - δ) * L) := k1
          _ ≤ η * (1 - δ) * L := h1
      exact le_of_mul_le_mul_left this hD0
    nlinarith
  have hLlt : L < 1 := lt_of_le_of_lt hLη hη
  -- feasibility
  have hKadd : ∀ a ∈ K, ∀ b ∈ K, a + b ∈ K := by
    intro a ha b hb
    have hmid := hK.2.1 ha hb (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)
    have := hK.2.2.1 _ hmid 2 (by norm_num)
    convert this using 1
    rw [smul_add, smul_smul, smul_smul]; norm_num
  have hKsmul : ∀ a ∈ K, ∀ t : ℝ, 0 ≤ t → t • a ∈ K := fun a ha t ht => hK.2.2.1 a ha t ht
  have hDadd : ∀ a ∈ ConvexOptimization.dualCone K, ∀ b ∈ ConvexOptimization.dualCone K,
      a + b ∈ ConvexOptimization.dualCone K := fun a ha b hb => dual_add' K ha hb
  have hDsmul : ∀ a ∈ ConvexOptimization.dualCone K, ∀ t : ℝ, 0 ≤ t →
      t • a ∈ ConvexOptimization.dualCone K := fun a ha t ht => dual_smul' K ha ht
  have habsx : absn K x qx ≤ η := le_trans (hp1 x hx qx).1 hLη
  have hxp : x - qx ∈ interior K :=
    sub_mem_interior_of_absn_lt K hKadd hKsmul hx (lt_of_le_of_lt habsx hη)
  have hsp : s - qs ∈ interior (ConvexOptimization.dualCone K) :=
    sub_mem_interior_of_absn_lt _ hDadd hDsmul hs
      (lt_of_le_of_lt (le_trans (hp3 s hs qs).1 hqs) hη)
  -- Theorem 3.6 with δ := η
  have h36 := SelfScaledIPM.ShortStep.theorem_3_6 K hK F ν hν hF x (x - qx) hx hxp η hη
    (by rw [show x - qx - x = -qx by abel, absn_neg']; exact habsx)
  obtain ⟨-, -, hall⟩ := h36
  refine ⟨⟨(hp2 x hx _).1, ?_⟩, hLη, hqs, ⟨hxp, hAx⟩, ⟨hsp, hAy⟩, ?_, ?_⟩
  · rw [hεpη]
    have : η * (1 - δ) ≤ η := by nlinarith
    linarith
  · intro v
    obtain ⟨-, -, a3, a4⟩ := (hall v 0).1
    exact a3.trans a4
  · intro u
    obtain ⟨-, -, b3, b4⟩ := (hall 0 u).2.1
    exact b3.trans b4
