-- Prove2me | solution 1 for YeIPA.Random.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:52:24.302553+00:00
-- url     : https://prove2.me/submissions/3f98f309-6d05-4de6-aa52-9f016481e306

import Mathlib
import Definitions.Def_YeIPA_Random_Setting

open Matrix MeasureTheory Filter Topology

namespace Y65Aux

open YeIPA.Random Metric
open scoped Pointwise

local notation "E" k => EuclideanSpace ℝ (Fin k)

lemma cone_sub {k : ℕ} (a : E k) (ha : ‖a‖ ≤ 1) (t : ℝ) (ht0 : 0 < t) (ht : t ^ 2 ≤ 1 / 2) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' {v : sphere (0 : E k) 1 | t < inner ℝ a (v : E k)}) ⊆
      ball (t • a) (Real.sqrt (1 - t ^ 2)) := by
  rintro x ⟨ρ, ⟨hρ0, hρ1⟩, _, ⟨v, hv, rfl⟩, rfl⟩
  simp only [Set.mem_ofPred_eq] at hv
  have hvn : ‖(v : E k)‖ = 1 := by simp
  rw [mem_ball, dist_eq_norm]
  apply Real.lt_sqrt_of_sq_lt
  rw [norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hvn,
    real_inner_comm a, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hρ0, abs_of_pos ht0]
  simp only [conj_trivial]
  have ha2 : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  have h3 := mul_lt_mul_of_pos_left hv (mul_pos hρ0 ht0)
  have h4 : (ρ - 1) * (ρ + 1 - 2 * t ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_left ha2 (sq_nonneg t)]

lemma cap_bound {k : ℕ} (hk : k ≠ 0) (a : E k) (ha : ‖a‖ ≤ 1) (t : ℝ) (ht0 : 0 < t)
    (ht : t ^ 2 ≤ 1 / 2) :
    uniformSphere k {v | t < inner ℝ a (v : E k)} ≤
      ENNReal.ofReal (Real.sqrt (1 - t ^ 2) ^ k) := by
  have : Nontrivial (E k) := by
    have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
    infer_instance
  have hmeas : MeasurableSet {v : sphere (0 : E k) 1 | t < inner ℝ a (v : E k)} :=
    (isOpen_lt continuous_const
      ((continuous_const.inner continuous_subtype_val))).measurableSet
  have hr : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 (by linarith)
  set V := (volume : Measure (E k)) (ball 0 1)
  have hV0 : V ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hc : (volume : Measure (E k)).toSphere Set.univ = (k : ENNReal) * V := by
    rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
  have hc0 : (k : ENNReal) * V ≠ 0 := mul_ne_zero (by exact_mod_cast hk) hV0
  have hct : (k : ENNReal) * V ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hVt
  unfold uniformSphere
  rw [Measure.smul_apply, smul_eq_mul, hc, Measure.toSphere_apply' _ hmeas,
    finrank_euclideanSpace_fin]
  calc ((k : ENNReal) * V)⁻¹ * (k * volume (Set.Ioo (0 : ℝ) 1 •
          (Subtype.val '' {v : sphere (0 : E k) 1 | t < inner ℝ a (v : E k)})))
      ≤ ((k : ENNReal) * V)⁻¹ * (k * volume (ball (t • a) (Real.sqrt (1 - t ^ 2)))) := by
        gcongr; exact cone_sub a ha t ht0 ht
    _ = ENNReal.ofReal (Real.sqrt (1 - t ^ 2) ^ k) * (((k : ENNReal) * V)⁻¹ * (k * V)) := by
        rw [Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace_fin]; ring
    _ = ENNReal.ofReal (Real.sqrt (1 - t ^ 2) ^ k) := by
        rw [ENNReal.inv_mul_cancel hc0 hct, mul_one]

lemma univ_eq_one {k : ℕ} (hk : k ≠ 0) : uniformSphere k Set.univ = 1 := by
  have : Nontrivial (E k) := by
    have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
    infer_instance
  unfold uniformSphere
  rw [Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel
  · rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]
    exact mul_ne_zero (by exact_mod_cast hk) (measure_ball_pos _ _ one_pos).ne'
  · exact measure_ne_top _ _

/-- the rows of `H` have norm `≤ 1`. -/
lemma row_norm {k : ℕ} (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (hF : Fᵀ * F = 1)
    (i : Fin (k + 1)) :
    ‖(WithLp.toLp 2 (fun j : Fin k => F i j.succ) : E k)‖ ≤ 1 := by
  have h1 : F * Fᵀ = 1 := mul_eq_one_comm.1 hF
  have hii : ∑ j : Fin (k + 1), F i j * F i j = 1 := by
    have := congrFun (congrFun h1 i) i
    simpa [Matrix.mul_apply] using this
  rw [EuclideanSpace.norm_eq]
  rw [Real.sqrt_le_one]
  rw [Fin.sum_univ_succ] at hii
  have : ∀ j : Fin k, ‖F i j.succ‖ ^ 2 = F i j.succ * F i j.succ := by
    intro j; rw [Real.norm_eq_abs, sq_abs, sq]
  simp only [this]
  nlinarith [mul_self_nonneg (F i 0)]

lemma row_inner {k : ℕ} (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (i : Fin (k + 1))
    (v : E k) :
    (F.submatrix id Fin.succ *ᵥ v.ofLp) i =
      inner ℝ (WithLp.toLp 2 (fun j : Fin k => F i j.succ) : E k) v := by
  simp [Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]

lemma real_limit :
    Tendsto (fun k : ℕ => 2 * Real.exp (-(Real.log ((k : ℝ) + 1) / 4))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp (h1.atTop_div_const (by norm_num : (0:ℝ) < 4))
  simpa using h2.const_mul 2

lemma eventually_small :
    ∀ᶠ k : ℕ in atTop, 6 ≤ k ∧ 3 * Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) ≤ 1 / 2 := by
  have h0 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hb := (Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ) < 1 / 6))
  have := h0.eventually hb
  filter_upwards [this, eventually_ge_atTop 6] with k hk h6
  refine ⟨h6, ?_⟩
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  simp only [Real.norm_eq_abs, id] at hk
  rw [div_le_iff₀ hpos]
  have := le_abs_self (Real.log ((k : ℝ) + 1))
  rw [abs_of_pos hpos] at hk
  linarith

end Y65Aux

open YeIPA.Random in
theorem solution (F : (k : ℕ) → Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hF : ∀ k, (F k)ᵀ * F k = 1) :
    Tendsto (fun k : ℕ => uniformSphere k
        {v | ∀ i, |((F k).submatrix id Fin.succ *ᵥ (v : EuclideanSpace ℝ (Fin k)).ofLp) i| ≤
          Real.sqrt (3 * Real.log (k + 1 : ℝ) / (k + 1 : ℝ))})
      atTop (𝓝 1) := by
  classical
  set G : (k : ℕ) → Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) := fun k =>
    {v | ∀ i, |((F k).submatrix id Fin.succ *ᵥ (v : EuclideanSpace ℝ (Fin k)).ofLp) i| ≤
          Real.sqrt (3 * Real.log (k + 1 : ℝ) / (k + 1 : ℝ))} with hG
  have hev : ∀ᶠ k : ℕ in atTop,
      1 - ENNReal.ofReal (2 * Real.exp (-(Real.log ((k : ℝ) + 1) / 4))) ≤ uniformSphere k (G k) := by
    filter_upwards [Y65Aux.eventually_small] with k ⟨hk6, hsmall⟩
    have hk : k ≠ 0 := by omega
    set n : ℝ := (k : ℝ) + 1 with hn
    have hn1 : (1 : ℝ) < n := by rw [hn]; have : (6:ℝ) ≤ k := by exact_mod_cast hk6
                                 linarith
    have hnpos : (0 : ℝ) < n := by linarith
    have hL : 0 < Real.log n := Real.log_pos hn1
    set τ := Real.sqrt (3 * Real.log n / n) with hτ
    have hτ2 : τ ^ 2 = 3 * Real.log n / n := Real.sq_sqrt (by positivity)
    have hτ0 : 0 < τ := Real.sqrt_pos.2 (by positivity)
    have hτs : τ ^ 2 ≤ 1 / 2 := by rw [hτ2]; exact hsmall
    set r := Real.sqrt (1 - τ ^ 2) with hr
    let a : Fin (k + 1) → EuclideanSpace ℝ (Fin k) :=
      fun i => WithLp.toLp 2 (fun j : Fin k => F k i j.succ)
    have hsub : (G k)ᶜ ⊆ ⋃ i, ({v | τ < inner ℝ (a i) (v : EuclideanSpace ℝ (Fin k))} ∪
        {v | τ < inner ℝ (-a i) (v : EuclideanSpace ℝ (Fin k))}) := by
      intro v hv
      simp only [hG, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hv
      obtain ⟨i, hi⟩ := hv
      rw [Y65Aux.row_inner] at hi
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, inner_neg_left]
      exact ⟨i, lt_abs.1 hi⟩
    have hbad : uniformSphere k (G k)ᶜ ≤
        ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (r ^ k + r ^ k)) := by
      calc uniformSphere k (G k)ᶜ ≤ uniformSphere k (⋃ i, ({v | τ < inner ℝ (a i)
              (v : EuclideanSpace ℝ (Fin k))} ∪
              {v | τ < inner ℝ (-a i) (v : EuclideanSpace ℝ (Fin k))})) := measure_mono hsub
        _ ≤ ∑ i, uniformSphere k ({v | τ < inner ℝ (a i) (v : EuclideanSpace ℝ (Fin k))} ∪
              {v | τ < inner ℝ (-a i) (v : EuclideanSpace ℝ (Fin k))}) :=
            measure_iUnion_fintype_le _ _
        _ ≤ ∑ _i : Fin (k + 1), (ENNReal.ofReal (r ^ k) + ENNReal.ofReal (r ^ k)) := by
            gcongr with i
            refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
            · exact Y65Aux.cap_bound hk _ (Y65Aux.row_norm _ (hF k) i) τ hτ0 hτs
            · exact Y65Aux.cap_bound hk _ (by rw [norm_neg]; exact Y65Aux.row_norm _ (hF k) i)
                τ hτ0 hτs
        _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (r ^ k + r ^ k)) := by
            have hrk : 0 ≤ r ^ k := by positivity
            rw [← ENNReal.ofReal_add hrk hrk, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast]
    have hreal : ((k + 1 : ℕ) : ℝ) * (r ^ k + r ^ k) ≤
        2 * Real.exp (-(Real.log ((k : ℝ) + 1) / 4)) := by
      have hr1 : r ≤ Real.exp (-(τ ^ 2) / 2) := by
        have h1 : 1 - τ ^ 2 ≤ Real.exp (-(τ ^ 2) / 2) ^ 2 := by
          rw [← Real.exp_nat_mul]; push_cast
          have := Real.add_one_le_exp (-(τ ^ 2)); ring_nf at this ⊢; linarith
        calc r ≤ Real.sqrt (Real.exp (-(τ ^ 2) / 2) ^ 2) := Real.sqrt_le_sqrt h1
          _ = _ := Real.sqrt_sq (Real.exp_pos _).le
      have hrk : r ^ k ≤ Real.exp (k * (-(τ ^ 2) / 2)) := by
        rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hr1 k
      have hexp : Real.log n + k * (-(τ ^ 2) / 2) ≤ -(Real.log n / 4) := by
        rw [hτ2]
        have hk6' : (6 : ℝ) ≤ k := by exact_mod_cast hk6
        rw [show (k : ℝ) * (-(3 * Real.log n / n) / 2) = -(3 * k * Real.log n) / (2 * n) by
          field_simp]
        rw [div_eq_mul_inv]
        have hinv : n * n⁻¹ = 1 := mul_inv_cancel₀ hnpos.ne'
        have : 3 * k * Real.log n * n⁻¹ ≥ 5 / 2 * Real.log n := by
          have h5 : (3 * k - 5 / 2 * n) * Real.log n ≥ 0 := by
            apply mul_nonneg _ hL.le; rw [hn]; linarith
          have hni : 0 < n⁻¹ := inv_pos.2 hnpos
          nlinarith [mul_nonneg h5 hni.le]
        have : -(3 * k * Real.log n) * (2 * n)⁻¹ = -(3 * k * Real.log n * n⁻¹) / 2 := by
          rw [mul_inv]; ring
        linarith
      have hcast : ((k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
      rw [hcast]
      calc n * (r ^ k + r ^ k) = 2 * (n * r ^ k) := by ring
        _ ≤ 2 * (n * Real.exp (k * (-(τ ^ 2) / 2))) := by gcongr
        _ = 2 * Real.exp (Real.log n + k * (-(τ ^ 2) / 2)) := by
            rw [Real.exp_add, Real.exp_log hnpos]
        _ ≤ 2 * Real.exp (-(Real.log n / 4)) := by gcongr
    have huniv := Y65Aux.univ_eq_one hk
    have h1 : 1 ≤ uniformSphere k (G k) + uniformSphere k (G k)ᶜ := by
      rw [← huniv, ← Set.union_compl_self (G k)]; exact measure_union_le _ _
    rw [tsub_le_iff_right]
    calc (1 : ENNReal) ≤ uniformSphere k (G k) + uniformSphere k (G k)ᶜ := h1
      _ ≤ uniformSphere k (G k) + ENNReal.ofReal (2 * Real.exp (-(Real.log ((k : ℝ) + 1) / 4))) := by
          gcongr; exact hbad.trans (ENNReal.ofReal_le_ofReal hreal)
  have hle : ∀ᶠ k : ℕ in atTop, uniformSphere k (G k) ≤ 1 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [← Y65Aux.univ_eq_one (by omega : k ≠ 0)]; exact measure_mono (Set.subset_univ _)
  have hlow : Tendsto (fun k : ℕ =>
      1 - ENNReal.ofReal (2 * Real.exp (-(Real.log ((k : ℝ) + 1) / 4)))) atTop (𝓝 1) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ENNReal)))
      (ENNReal.tendsto_ofReal Y65Aux.real_limit) (Or.inl ENNReal.one_ne_top)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds hev hle
