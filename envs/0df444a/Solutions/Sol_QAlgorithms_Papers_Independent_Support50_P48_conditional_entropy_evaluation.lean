-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P48.conditional_entropy_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:32:12.514989+00:00
-- url     : https://prove2.me/submissions/f0ea36d8-17fa-4a2d-ad43-6f82a715cdcc

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P48

noncomputable section

open Filter
open scoped BigOperators ENNReal NNReal Topology
open QAlgorithms.Papers.Independent.Support50.P48
open QAlgorithms.Papers.Independent.Dependency50.P30
  (PureLossBroadcastParameters thermalEntropyBits)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats finiteEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq


lemma geom_mix (N X : ℝ) (hN : 0 ≤ N) (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (k : ℕ) :
    HasSum (fun l : ℕ => N^(k+l)/(N+1)^(k+l+1) * (((l+k).choose k : ℕ) : ℝ) * X^k * (1-X)^l)
      ((N*X)^k/(1+N*X)^(k+1)) := by
  have hN1 : 0 < N + 1 := by linarith
  set r : ℝ := (1-X) * N / (N+1) with hr
  have hr0 : 0 ≤ r := by
    have : 0 ≤ 1 - X := by linarith
    positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one hN1]
    nlinarith
  have h := hasSum_choose_mul_geometric_of_norm_lt_one k (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  have h2 := h.mul_left (N^k * X^k / (N+1)^(k+1))
  have e1 : (fun l : ℕ => N^(k+l)/(N+1)^(k+l+1) * (((l+k).choose k : ℕ) : ℝ) * X^k * (1-X)^l)
      = fun i : ℕ => N ^ k * X ^ k / (N + 1) ^ (k + 1) * ((((i + k).choose k : ℕ) : ℝ) * r ^ i) := by
    funext l
    simp only [hr, div_pow, mul_pow, pow_add, pow_succ]
    field_simp
  have e2 : (N*X)^k/(1+N*X)^(k+1) = N ^ k * X ^ k / (N + 1) ^ (k + 1) * (1 / (1 - r) ^ (k + 1)) := by
    have : 1 - r = (1 + N*X)/(N+1) := by rw [hr]; field_simp; ring
    rw [this, div_pow]
    have h3 : 0 < 1 + N*X := by positivity
    field_simp
    ring
  rw [e1, e2]
  exact h2



noncomputable def geomP (x : ℝ) (k : ℕ) : ℝ := x^k/(x+1)^(k+1)

lemma geomP_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ geomP x k := by
  unfold geomP; positivity

lemma geomP_hasSum {x : ℝ} (hx : 0 ≤ x) : HasSum (geomP x) 1 := by
  have hq0 : 0 ≤ x/(x+1) := by positivity
  have hq1 : x/(x+1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1/(x+1))
  have e : (fun k => 1/(x+1) * (x/(x+1))^k) = geomP x := by
    funext k; unfold geomP; rw [div_pow]; field_simp; ring
  rw [e] at h
  have : 1 - x/(x+1) = 1/(x+1) := by field_simp; ring
  rw [this] at h
  have hv : 1/(x+1) * (1/(x+1))⁻¹ = 1 := by field_simp
  rwa [hv] at h

lemma geomP_mean {x : ℝ} (hx : 0 ≤ x) : HasSum (fun k : ℕ => (k:ℝ) * geomP x k) x := by
  have hq0 : 0 ≤ x/(x+1) := by positivity
  have hq1 : x/(x+1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := x/(x+1))
    (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)).mul_left (1/(x+1))
  have e : (fun k : ℕ => 1/(x+1) * ((k:ℝ) * (x/(x+1))^k)) = fun k : ℕ => (k:ℝ) * geomP x k := by
    funext k; unfold geomP; rw [div_pow]; field_simp; ring
  rw [e] at h
  have : 1 - x/(x+1) = 1/(x+1) := by field_simp; ring
  rw [this] at h
  have hv : 1/(x+1) * (x/(x+1) / (1/(x+1))^2) = x := by field_simp
  rwa [hv] at h

/-- entropy in nats of geometric distribution -/
noncomputable def thermalNats (x : ℝ) : ℝ := (1 + x) * Real.log (1 + x) - x * Real.log x

lemma geomP_entropy_hasSum {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun k => -(geomP x k) * Real.log (geomP x k)) (thermalNats x) := by
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0
    have : (fun k => -(geomP 0 k) * Real.log (geomP 0 k)) = fun _ => 0 := by
      funext k; unfold geomP
      rcases k with _ | k <;> simp
    rw [this]; simp only [thermalNats]; simpa using hasSum_zero
  · have key : ∀ k : ℕ, -(geomP x k) * Real.log (geomP x k) =
        (k+1:ℝ) * geomP x k * Real.log (x+1) - (k:ℝ) * geomP x k * Real.log x := by
      intro k
      have hg : geomP x k = x^k/(x+1)^(k+1) := rfl
      have hxp : 0 < x := hpos
      have : Real.log (geomP x k) = k * Real.log x - (k+1) * Real.log (x+1) := by
        rw [hg, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        push_cast; first | done | ring
      rw [this]; ring
    simp_rw [key]
    have h1 := (geomP_mean hx)
    have h2 := geomP_hasSum hx
    have h3 : HasSum (fun k : ℕ => (k+1:ℝ) * geomP x k) (x + 1) := by
      have := h1.add h2
      have e : (fun k : ℕ => (k+1:ℝ) * geomP x k) = fun k : ℕ => (k:ℝ) * geomP x k + geomP x k := by
        funext k; ring
      rw [e]; exact this
    have := (h3.mul_right (Real.log (x+1))).sub (h1.mul_right (Real.log x))
    have ev : thermalNats x = (x + 1) * Real.log (x+1) - x * Real.log x := by
      simp only [thermalNats]; ring_nf
    rw [ev]; exact this



lemma therm_sub_logb_tendsto :
    Tendsto (fun x : ℝ => thermalEntropyBits x - Real.logb 2 x) atTop (𝓝 (1 / Real.log 2)) := by
  have h1 : Tendsto (fun x : ℝ => x * Real.log (1 + 1 / x)) atTop (𝓝 1) :=
    Real.tendsto_mul_log_one_add_div_atTop 1
  have h2 : Tendsto (fun x : ℝ => Real.log (1 + 1 / x)) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    have h := ((Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp (by simpa using this))
    simpa [Function.comp_def] using h
  have h3 := (h2.add h1).div_const (Real.log 2)
  simp only [zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  unfold thermalEntropyBits Real.logb
  have : Real.log (1 + x) = Real.log x + Real.log (1 + 1/x) := by
    rw [← Real.log_mul hx.ne' (by positivity)]
    congr 1; field_simp; ring
  rw [this]; ring

lemma therm_diff_tendsto {c d : ℝ} (hd : 0 < d) (hc : 0 < c) :
    Tendsto (fun N : ℝ => thermalEntropyBits (c * N) - thermalEntropyBits (d * N)) atTop
      (𝓝 (Real.logb 2 (c / d))) := by
  have hc' : Tendsto (fun N : ℝ => c * N) atTop atTop := tendsto_id.const_mul_atTop hc
  have hd' : Tendsto (fun N : ℝ => d * N) atTop atTop := tendsto_id.const_mul_atTop hd
  have h := (therm_sub_logb_tendsto.comp hc').sub (therm_sub_logb_tendsto.comp hd')
  simp only [sub_self] at h
  have h2 : Tendsto (fun N : ℝ => Real.logb 2 (c * N) - Real.logb 2 (d * N)) atTop
      (𝓝 (Real.logb 2 (c / d))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.logb_mul hc.ne' hN.ne', Real.logb_mul hd.ne' hN.ne', Real.logb_div hc.ne' hd.ne']; ring
  have h3 := h.add h2
  rw [zero_add] at h3
  refine h3.congr' ?_
  filter_upwards with N
  simp only [Function.comp]; ring

lemma therm_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℝ => thermalEntropyBits (c * N)) atTop atTop := by
  have hc' : Tendsto (fun N : ℝ => c * N) atTop atTop := tendsto_id.const_mul_atTop hc
  have h := (Real.tendsto_logb_atTop (b := 2) (by norm_num)).comp hc'
  have h2 := therm_sub_logb_tendsto.comp hc'
  have := h.atTop_add h2
  refine this.congr' ?_
  filter_upwards with N
  simp only [Function.comp]; ring



section EV
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma aeval_mulVec_eigen (A : Matrix n n ℂ) (v : n → ℂ) (μ : ℝ)
    (hv : A.mulVec v = (μ : ℂ) • v) (q : Polynomial ℝ) :
    (Polynomial.aeval A q).mulVec v = ((q.eval μ : ℝ) : ℂ) • v := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp [map_add, Matrix.add_mulVec, hp, hq, add_smul]
  | monomial m c =>
    have hpow : ∀ m : ℕ, (A ^ m).mulVec v = ((μ ^ m : ℝ) : ℂ) • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul]
        push_cast; ring_nf
    simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    have : (algebraMap ℝ (Matrix n n ℂ) c * A ^ m).mulVec v = ((c * μ ^ m : ℝ) : ℂ) • v := by
      rw [← Matrix.mulVec_mulVec, hpow]
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, ← Complex.coe_smul c, smul_smul]
      push_cast; rfl
    exact this

lemma cfc_mulVec_eigen (A : Matrix n n ℂ) (hA : A.IsHermitian) (v : n → ℂ) (μ : ℝ)
    (hv : A.mulVec v = (μ : ℂ) • v) (f : ℝ → ℝ) :
    (cfc f A).mulVec v = ((f μ : ℝ) : ℂ) • v := by
  classical
  have hsa : IsSelfAdjoint A := hA
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  let σ : Finset ℝ := insert μ hfin.toFinset
  let q : Polynomial ℝ := Lagrange.interpolate σ id f
  have hq : ∀ x ∈ σ, q.eval x = f x := by
    intro x hx
    exact Lagrange.eval_interpolate_at_node f Function.injective_id.injOn hx
  have h1 : cfc f A = cfc (fun x => q.eval x) A := by
    apply cfc_congr
    intro x hx
    exact (hq x (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hx))).symm
  rw [h1, cfc_polynomial q A hsa, aeval_mulVec_eigen A v μ hv q,
    hq μ (Finset.mem_insert_self _ _)]
end EV


section FE
variable {F : Type} [Fintype F] [DecidableEq F]

noncomputable def blockMat (β : F → ℕ) (w : F → ℝ) : Matrix F F ℂ :=
  fun i j => if β i = β j then ((w i * w j : ℝ) : ℂ) else 0

noncomputable def lam (β : F → ℕ) (w : F → ℝ) (k : ℕ) : ℝ := ∑ i, if β i = k then w i ^ 2 else 0

lemma blockMat_herm (β : F → ℕ) (w : F → ℝ) : (blockMat β w).IsHermitian := by
  ext i j
  simp only [blockMat, Matrix.conjTranspose_apply]
  by_cases h : β j = β i
  · simp [h, mul_comm]
  · simp [h, Ne.symm h]

noncomputable def blockVec (β : F → ℕ) (w : F → ℝ) (k : ℕ) : F → ℂ :=
  fun i => if β i = k then (w i : ℂ) else 0

lemma blockMat_eig (β : F → ℕ) (w : F → ℝ) (k : ℕ) :
    (blockMat β w).mulVec (blockVec β w k) = ((lam β w k : ℝ) : ℂ) • blockVec β w k := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  by_cases h : β i = k
  · have : ∀ j, blockMat β w i j * blockVec β w k j = ((w i : ℂ)) * ((if β j = k then w j ^ 2 else 0 : ℝ) : ℂ) := by
      intro j
      by_cases hj : β j = k
      · simp [blockMat, blockVec, hj, h]; ring
      · simp [blockMat, blockVec, hj]
    simp only [this, ← Finset.mul_sum]
    simp only [lam, blockVec, h, if_true, Complex.ofReal_sum]
    ring
  · have : ∀ j, blockMat β w i j * blockVec β w k j = 0 := by
      intro j
      by_cases hj : β j = k
      · have : β i ≠ β j := fun h' => h (h'.trans hj)
        simp [blockMat, this]
      · simp [blockVec, hj]
    rw [Finset.sum_eq_zero (fun j _ => this j)]
    simp [blockVec, h]

lemma blockMat_decomp (β : F → ℕ) (w : F → ℝ) :
    blockMat β w = ∑ k ∈ Finset.univ.image β, Matrix.vecMulVec (blockVec β w k) (star (blockVec β w k)) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, blockVec, blockMat, Pi.star_apply]
  rw [Finset.sum_eq_single (β i)]
  · by_cases h : β i = β j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro b _ hb
    by_cases h : β i = b
    · exact absurd h.symm hb
    · simp [h]
  · intro h; exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ i)) h

lemma trace_vecMulVec_mul' (a b : F → ℂ) (B : Matrix F F ℂ) :
    (Matrix.vecMulVec a b * B).trace = b ⬝ᵥ (B.mulVec a) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

lemma blockVec_dot (β : F → ℕ) (w : F → ℝ) (k : ℕ) :
    star (blockVec β w k) ⬝ᵥ blockVec β w k = ((lam β w k : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, blockVec, lam, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : β i = k <;> simp [h, sq]

lemma trace_mul_cfc (β : F → ℕ) (w : F → ℝ) (f : ℝ → ℝ) :
    ((blockMat β w) * cfc f (blockMat β w)).trace =
      ((∑ k ∈ Finset.univ.image β, lam β w k * f (lam β w k) : ℝ) : ℂ) := by
  have hH := blockMat_herm β w
  have e : blockMat β w * cfc f (blockMat β w) =
      (∑ k ∈ Finset.univ.image β, Matrix.vecMulVec (blockVec β w k) (star (blockVec β w k))) *
        cfc f (blockMat β w) := by
    congr 1; exact blockMat_decomp β w
  rw [e, Finset.sum_mul, Matrix.trace_sum]
  push_cast
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [trace_vecMulVec_mul', cfc_mulVec_eigen _ hH _ (lam β w k) (blockMat_eig β w k) f,
    dotProduct_smul, blockVec_dot, smul_eq_mul]
  ring

lemma trace_blockMat (β : F → ℕ) (w : F → ℝ) :
    (blockMat β w).trace = ((∑ i, w i ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, blockMat, sq]

lemma finiteEntropy_blockMat (β : F → ℕ) (w : F → ℝ) :
    finiteEntropy (blockMat β w) = ENNReal.ofReal ((∑ i, w i ^ 2) * Real.log (∑ i, w i ^ 2) -
      ∑ k ∈ Finset.univ.image β, lam β w k * Real.log (lam β w k)) := by
  unfold finiteEntropy
  rw [trace_blockMat, trace_mul_cfc]
  simp only [Complex.ofReal_re]
end FE



/-- real Gibbs-type inequality -/
lemma gibbs_ineq (K : Finset ℕ) (a L : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (haL : ∀ k, a k ≤ L k)
    (hL : ∑ k ∈ K, L k ≤ 1) :
    (∑ k ∈ K, a k) * Real.log (∑ k ∈ K, a k) - ∑ k ∈ K, a k * Real.log (a k) ≤
      ∑ k ∈ K, (-L k * Real.log (L k)) := by
  set t := ∑ k ∈ K, a k with ht
  have hL0 : ∀ k, 0 ≤ L k := fun k => (ha k).trans (haL k)
  have hLle : ∀ k ∈ K, L k ≤ 1 := by
    intro k hk
    have := Finset.single_le_sum (f := L) (fun j _ => hL0 j) hk
    linarith
  have hη : ∀ k ∈ K, 0 ≤ -L k * Real.log (L k) := by
    intro k hk
    have := Real.log_nonpos (hL0 k) (hLle k hk)
    nlinarith [hL0 k]
  have ht0 : 0 ≤ t := Finset.sum_nonneg (fun k _ => ha k)
  rcases ht0.eq_or_lt with h0 | hpos
  · have : ∀ k ∈ K, a k = 0 := by
      intro k hk
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).1 h0.symm k hk
    have hz : ∀ k ∈ K, a k * Real.log (a k) = 0 := by
      intro k hk; rw [this k hk]; simp
    rw [Finset.sum_congr rfl hz, ← h0]
    simp only [Real.log_zero, mul_zero, Finset.sum_const_zero, sub_zero]
    exact Finset.sum_nonneg hη
  · have key : ∀ k ∈ K, a k * (Real.log t - Real.log (a k)) ≤
        -(a k) * Real.log (L k) + (t * L k - a k) := by
      intro k hk
      rcases (ha k).eq_or_lt with h | h
      · rw [← h]; simp; nlinarith [hL0 k]
      · have hLk : 0 < L k := lt_of_lt_of_le h (haL k)
        have : Real.log (t * L k / a k) ≤ t * L k / a k - 1 := Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (by positivity) h.ne', Real.log_mul hpos.ne' hLk.ne'] at this
        have h2 := mul_le_mul_of_nonneg_left this h.le
        have h3 : a k * (t * L k / a k - 1) = t * L k - a k := by field_simp
        nlinarith
    have step1 : (∑ k ∈ K, a k) * Real.log t - ∑ k ∈ K, a k * Real.log (a k) =
        ∑ k ∈ K, a k * (Real.log t - Real.log (a k)) := by
      rw [Finset.sum_mul]; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [step1]
    calc ∑ k ∈ K, a k * (Real.log t - Real.log (a k))
        ≤ ∑ k ∈ K, (-(a k) * Real.log (L k) + (t * L k - a k)) := Finset.sum_le_sum key
      _ = ∑ k ∈ K, (-(a k) * Real.log (L k)) + (t * ∑ k ∈ K, L k - t) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ ≤ ∑ k ∈ K, (-L k * Real.log (L k)) := by
          have h1 : t * ∑ k ∈ K, L k - t ≤ 0 := by nlinarith
          have h2 : ∑ k ∈ K, (-(a k) * Real.log (L k)) ≤ ∑ k ∈ K, (-L k * Real.log (L k)) := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            have := Real.log_nonpos (hL0 k) (hLle k hk)
            nlinarith [haL k]
          linarith


section BL

/-- sup-form of finite entropy: sum over any finset of labels containing the range of `β`. -/
lemma finiteEntropy_blockMat_sup {F : Type} [Fintype F] [DecidableEq F] (β : F → ℕ) (w : F → ℝ)
    (K : Finset ℕ) (hK : ∀ i, β i ∈ K) :
    finiteEntropy (blockMat β w) = ENNReal.ofReal ((∑ i, w i ^ 2) * Real.log (∑ i, w i ^ 2) -
      ∑ k ∈ K, lam β w k * Real.log (lam β w k)) := by
  rw [finiteEntropy_blockMat]
  congr 2
  refine (Finset.sum_subset (fun k hk => ?_) (fun k _ hk => ?_))
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hk; exact hK i
  · have : lam β w k = 0 := by
      unfold lam
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have : β i ≠ k := fun h => hk (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩)
      simp [this]
    simp [this]

def Lam {I : Type} (β : I → ℕ) (w : I → ℝ) (k : ℕ) : ℝ := ∑' i, if β i = k then w i ^ 2 else 0

lemma summable_ite_sq {I : Type} (β : I → ℕ) (w : I → ℝ) (hs : Summable (fun i => w i ^ 2)) (k : ℕ) :
    Summable (fun i => if β i = k then w i ^ 2 else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hs
  · split_ifs <;> positivity
  · split_ifs <;> simp [sq_nonneg]

lemma hasSum_Lam {I : Type} (β : I → ℕ) (w : I → ℝ) (hs : HasSum (fun i => w i ^ 2) 1) :
    HasSum (Lam β w) 1 := by
  have h := hs.tsum_fiberwise β
  have e : Lam β w = fun c => ∑' b : (β ⁻¹' {c}), w b ^ 2 := by
    funext k
    unfold Lam
    rw [tsum_subtype (β ⁻¹' {k}) (fun b => w b ^ 2)]
    congr 1
    funext i
    simp [Set.indicator]
  rw [e]; exact h

lemma Lam_nonneg {I : Type} (β : I → ℕ) (w : I → ℝ) (k : ℕ) : 0 ≤ Lam β w k :=
  tsum_nonneg (fun i => by split_ifs <;> positivity)

end BL

section BL2
variable {I : Type}

def lamS (β : I → ℕ) (w : I → ℝ) (s : Finset I) (k : ℕ) : ℝ := ∑ i ∈ s, if β i = k then w i ^ 2 else 0

lemma lam_sub (β : I → ℕ) (w : I → ℝ) (s : Finset I) (k : ℕ) :
    lam (fun i : s => β i.val) (fun i : s => w i.val) k = lamS β w s k := by
  unfold lam lamS
  exact Finset.sum_coe_sort s (fun i => if β i = k then w i ^ 2 else 0)

lemma sq_sub (w : I → ℝ) (s : Finset I) :
    ∑ i : s, (fun i : s => w i.val) i ^ 2 = ∑ i ∈ s, w i ^ 2 :=
  Finset.sum_coe_sort s (fun i => w i ^ 2)

lemma fin_sub (β : I → ℕ) (w : I → ℝ) (s : Finset I) (K : Finset ℕ) (hK : ∀ i ∈ s, β i ∈ K) :
    finiteEntropy ((blockMat β w).submatrix (fun i : s => i.val) (fun i : s => i.val)) =
      ENNReal.ofReal ((∑ i ∈ s, w i ^ 2) * Real.log (∑ i ∈ s, w i ^ 2) -
        ∑ k ∈ K, lamS β w s k * Real.log (lamS β w s k)) := by
  have : (blockMat β w).submatrix (fun i : s => i.val) (fun i : s => i.val) =
      blockMat (fun i : s => β i.val) (fun i : s => w i.val) := rfl
  rw [this, finiteEntropy_blockMat_sup (fun i : s => β i.val) (fun i : s => w i.val) K (fun i => hK i.val i.property)]
  simp only [lam_sub, sq_sub]

lemma sum_lamS (β : I → ℕ) (w : I → ℝ) (s : Finset I) (K : Finset ℕ) (hK : ∀ i ∈ s, β i ∈ K) :
    ∑ k ∈ K, lamS β w s k = ∑ i ∈ s, w i ^ 2 := by
  unfold lamS
  rw [← Finset.sum_fiberwise_of_maps_to hK (fun i => w i ^ 2)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_filter]

lemma lamS_le_Lam (β : I → ℕ) (w : I → ℝ) (hs : HasSum (fun i => w i ^ 2) 1) (s : Finset I) (k : ℕ) :
    lamS β w s k ≤ Lam β w k :=
  sum_le_hasSum s (fun i _ => by split_ifs <;> positivity) (summable_ite_sq β w hs.summable k).hasSum

theorem extendedEntropy_blockMat (β : I → ℕ) (w : I → ℝ) (hs : HasSum (fun i => w i ^ 2) 1) :
    extendedEntropyNats (blockMat β w) =
      ∑' k : ℕ, ENNReal.ofReal (-(Lam β w k) * Real.log (Lam β w k)) := by
  have hL1 := hasSum_Lam β w hs
  have hLsum : ∀ K : Finset ℕ, ∑ k ∈ K, Lam β w k ≤ 1 :=
    fun K => sum_le_hasSum K (fun k _ => Lam_nonneg β w k) hL1
  have hLle : ∀ k, Lam β w k ≤ 1 := by
    intro k
    have := hLsum {k}
    simpa using this
  unfold extendedEntropyNats
  refine le_antisymm (iSup_le fun s => ?_) ?_
  · -- upper bound
    classical
    set K := s.image β with hKdef
    have hK : ∀ i ∈ s, β i ∈ K := fun i hi => Finset.mem_image_of_mem _ hi
    rw [fin_sub β w s K hK]
    have hg := gibbs_ineq K (lamS β w s) (Lam β w)
      (fun k => Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity))
      (lamS_le_Lam β w hs s) (hLsum K)
    rw [sum_lamS β w s K hK] at hg
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal (∑ k ∈ K, (-(Lam β w k) * Real.log (Lam β w k))) :=
          ENNReal.ofReal_le_ofReal hg
      _ = ∑ k ∈ K, ENNReal.ofReal (-(Lam β w k) * Real.log (Lam β w k)) := by
          refine ENNReal.ofReal_sum_of_nonneg (fun k _ => ?_)
          have := Real.log_nonpos (Lam_nonneg β w k) (hLle k)
          nlinarith [Lam_nonneg β w k]
      _ ≤ _ := ENNReal.sum_le_tsum K
  · -- lower bound
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun K0 => ?_
    classical
    set t : Finset I → ℝ := fun s => ∑ i ∈ s, w i ^ 2 with ht
    set g : Finset I → ℝ := fun s => ∑ k ∈ K0, lamS β w s k * (Real.log (t s) - Real.log (lamS β w s k)) with hg
    have hconv : Tendsto g atTop (𝓝 (∑ k ∈ K0, (-(Lam β w k) * Real.log (Lam β w k)))) := by
      have ht1 : Tendsto t atTop (𝓝 1) := hs
      have hlog : Tendsto (fun s => Real.log (t s)) atTop (𝓝 0) := by
        have := ht1.log (by norm_num)
        simpa using this
      have hk : ∀ k, Tendsto (fun s => lamS β w s k) atTop (𝓝 (Lam β w k)) := fun k =>
        (summable_ite_sq β w hs.summable k).hasSum
      have hterm : ∀ k ∈ K0, Tendsto (fun s => lamS β w s k * (Real.log (t s) - Real.log (lamS β w s k)))
          atTop (𝓝 (-(Lam β w k) * Real.log (Lam β w k))) := by
        intro k _
        have h1 := (hk k).mul hlog
        have h2 := (Real.continuous_mul_log.tendsto (Lam β w k)).comp (hk k)
        have h3 := h1.sub h2
        have e : (fun s => lamS β w s k * (Real.log (t s) - Real.log (lamS β w s k))) =
            fun s => lamS β w s k * Real.log (t s) - (fun x : ℝ => x * Real.log x) (lamS β w s k) := by
          funext s; simp only [mul_sub]
        have e2 : -(Lam β w k) * Real.log (Lam β w k) =
            Lam β w k * 0 - Lam β w k * Real.log (Lam β w k) := by ring
        rw [e, e2]; exact h3
      exact tendsto_finsetSum K0 hterm
    have key : ∀ s : Finset I, ENNReal.ofReal (g s) ≤
        finiteEntropy ((blockMat β w).submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
      intro s
      set K := K0 ∪ s.image β with hKdef
      have hK : ∀ i ∈ s, β i ∈ K := fun i hi =>
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
      rw [fin_sub β w s K hK]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsum : ∑ k ∈ K, lamS β w s k = t s := sum_lamS β w s K hK
      have hnn : ∀ k, 0 ≤ lamS β w s k :=
        fun k => Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
      have he : ∀ k ∈ K, 0 ≤ lamS β w s k * (Real.log (t s) - Real.log (lamS β w s k)) := by
        intro k hk
        rcases (hnn k).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · have hle : lamS β w s k ≤ t s := by
            rw [← hsum]
            exact Finset.single_le_sum (f := lamS β w s) (fun j _ => hnn j) hk
          have := Real.log_le_log hpos hle
          exact mul_nonneg hpos.le (by linarith)
      have hΦ : (∑ i ∈ s, w i ^ 2) * Real.log (∑ i ∈ s, w i ^ 2) -
          ∑ k ∈ K, lamS β w s k * Real.log (lamS β w s k) =
          ∑ k ∈ K, lamS β w s k * (Real.log (t s) - Real.log (lamS β w s k)) := by
        have : (∑ i ∈ s, w i ^ 2) = t s := rfl
        have h1 : t s * Real.log (t s) = ∑ k ∈ K, lamS β w s k * Real.log (t s) := by
          rw [← Finset.sum_mul, hsum]
        rw [this, h1, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => by ring)
      rw [hΦ]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun k hk _ => he k hk)
    have hlim := (ENNReal.tendsto_ofReal hconv)
    have hle : ENNReal.ofReal (∑ k ∈ K0, (-(Lam β w k) * Real.log (Lam β w k))) ≤
        ⨆ s : Finset I, finiteEntropy ((blockMat β w).submatrix (fun i : s => i.val) (fun i : s => i.val)) :=
      le_of_tendsto' hlim (fun s => (key s).trans (le_iSup (fun s : Finset I => finiteEntropy
        ((blockMat β w).submatrix (fun i : s => i.val) (fun i : s => i.val))) s))
    have hnn' : ∀ k ∈ K0, 0 ≤ -(Lam β w k) * Real.log (Lam β w k) := by
      intro k _
      have := Real.log_nonpos (Lam_nonneg β w k) (hLle k)
      nlinarith [Lam_nonneg β w k]
    rw [ENNReal.ofReal_sum_of_nonneg hnn'] at hle
    exact hle
end BL2

section Thin
open scoped Polynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma thin_coeff (ω : ι → ℝ) (b : ι → ℕ) (n k : ℕ) :
    ∑ o ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
      (if ∑ j, b j * o j = k then ((Nat.multinomial Finset.univ o : ℕ) : ℝ) * ∏ j, ω j ^ o j else 0)
    = ((∑ j, Polynomial.C (ω j) * Polynomial.X ^ b j : Polynomial ℝ) ^ n).coeff k := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  have h1 : (∏ j, (Polynomial.C (ω j) * Polynomial.X ^ b j) ^ o j : Polynomial ℝ) =
      Polynomial.C (∏ j, ω j ^ o j) * Polynomial.X ^ (∑ j, b j * o j) := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← Polynomial.C_pow, map_prod, ← pow_mul,
      Finset.prod_pow_eq_pow_sum]
  rw [h1]
  have h2 : ((Nat.multinomial Finset.univ o : ℕ) : Polynomial ℝ) *
      (Polynomial.C (∏ j, ω j ^ o j) * Polynomial.X ^ (∑ j, b j * o j)) =
      Polynomial.C (((Nat.multinomial Finset.univ o : ℕ) : ℝ) * ∏ j, ω j ^ o j) *
        Polynomial.X ^ (∑ j, b j * o j) := by
    rw [Polynomial.C_mul]
    simp only [map_natCast]
    ring
  rw [h2, Polynomial.coeff_C_mul_X_pow]
  by_cases h : k = ∑ j, b j * o j
  · simp [h]
  · simp [h, Ne.symm h]
end Thin

section Thin2
open scoped Polynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma thin_binom (ω : ι → ℝ) (P : ι → Prop) [DecidablePred P] (n k : ℕ) :
    ∑ o ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
      (if ∑ j, (if P j then o j else 0) = k then
        ((Nat.multinomial Finset.univ o : ℕ) : ℝ) * ∏ j, ω j ^ o j else 0)
    = (n.choose k : ℝ) * (∑ j, if P j then ω j else 0) ^ k * (∑ j, if P j then 0 else ω j) ^ (n - k) := by
  have h0 := thin_coeff ω (fun j => if P j then 1 else 0) n k
  have e1 : ∀ o : ι → ℕ, ∑ j, (if P j then 1 else 0) * o j = ∑ j, (if P j then o j else 0) := by
    intro o; refine Finset.sum_congr rfl (fun j _ => ?_); split_ifs <;> simp
  simp only [e1] at h0
  rw [h0]
  have e2 : (∑ j, Polynomial.C (ω j) * Polynomial.X ^ (if P j then 1 else 0) : Polynomial ℝ) =
      Polynomial.C (∑ j, if P j then ω j else 0) * Polynomial.X +
        Polynomial.C (∑ j, if P j then 0 else ω j) := by
    simp only [map_sum]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> simp
  rw [e2, add_pow, Polynomial.finsetSum_coeff]
  set W := ∑ j, if P j then ω j else 0
  set Wc := ∑ j, if P j then 0 else ω j
  have e3 : ∀ m ∈ Finset.range (n+1),
      ((Polynomial.C W * Polynomial.X) ^ m * Polynomial.C Wc ^ (n - m) * (n.choose m : Polynomial ℝ)).coeff k =
      if m = k then (n.choose m : ℝ) * W ^ m * Wc ^ (n - m) else 0 := by
    intro m _
    have : (Polynomial.C W * Polynomial.X) ^ m * Polynomial.C Wc ^ (n - m) * (n.choose m : Polynomial ℝ) =
        Polynomial.C ((n.choose m : ℝ) * W ^ m * Wc ^ (n - m)) * Polynomial.X ^ m := by
      simp only [mul_pow, map_mul, map_pow, map_natCast]
      ring
    rw [this, Polynomial.coeff_C_mul_X_pow]
    by_cases h : k = m
    · simp [h]
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl e3]
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hm; simp [hm]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) h
  · have hk := not_le.1 hk
    rw [Nat.choose_eq_zero_of_lt hk]
    refine (Finset.sum_eq_zero (fun m hm => ?_)).trans (by simp)
    have : m ≠ k := by
      have := Finset.mem_range.1 hm; omega
    simp [this]
end Thin2

section Model
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- single-mode amplitude for photon number `x`. -/
def phiA (w : ℝ) (x : ℕ) : ℝ := Real.sqrt w ^ x / Real.sqrt (x.factorial : ℝ)

def gamA (N : ℝ) (n : ℕ) : ℝ := Real.sqrt (N ^ n / (N + 1) ^ (n + 1)) * Real.sqrt (n.factorial : ℝ)

/-- model amplitude -/
def psiM (N : ℝ) (ω : ι → ℝ) (f : Option ι → ℕ) : ℝ :=
  if ∑ j, f (some j) = f none then gamA N (f none) * ∏ j, phiA (ω j) (f (some j)) else 0

lemma phiA_nonneg (w : ℝ) (x : ℕ) : 0 ≤ phiA w x := by unfold phiA; positivity
lemma gamA_nonneg (N : ℝ) (n : ℕ) : 0 ≤ gamA N n := by unfold gamA; positivity

lemma psiM_nonneg (N : ℝ) (ω : ι → ℝ) (f : Option ι → ℕ) : 0 ≤ psiM N ω f := by
  unfold psiM
  split_ifs
  · exact mul_nonneg (gamA_nonneg _ _) (Finset.prod_nonneg (fun j _ => phiA_nonneg _ _))
  · exact le_refl _

lemma phiA_sq {w : ℝ} (hw : 0 ≤ w) (x : ℕ) : phiA w x ^ 2 = w ^ x / (x.factorial : ℝ) := by
  unfold phiA
  rw [div_pow, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hw, Real.sq_sqrt (by positivity)]

lemma gamA_sq {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    gamA N n ^ 2 = N ^ n / (N + 1) ^ (n + 1) * (n.factorial : ℝ) := by
  unfold gamA
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

/-- extension of an occupation vector of the receivers to the full one -/
def extO (o : ι → ℕ) : Option ι → ℕ := fun i => Option.elim i (∑ j, o j) o

lemma psiM_extO_sq {N : ℝ} (hN : 0 ≤ N) {ω : ι → ℝ} (hω : ∀ j, 0 ≤ ω j) (o : ι → ℕ) :
    psiM N ω (extO o) ^ 2 = N ^ (∑ j, o j) / (N + 1) ^ (∑ j, o j + 1) *
      (((Nat.multinomial Finset.univ o : ℕ) : ℝ) * ∏ j, ω j ^ o j) := by
  unfold psiM
  simp only [extO, Option.elim, if_true]
  rw [mul_pow, gamA_sq hN, ← Finset.prod_pow]
  have h1 : ∀ j ∈ Finset.univ, phiA (ω j) (o j) ^ 2 = ω j ^ o j / (o j).factorial := fun j _ => phiA_sq (hω j) _
  rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib]
  have h2 := Nat.multinomial_spec (Finset.univ : Finset ι) o
  have h3 : (∏ j, ((o j).factorial : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun j _ => by positivity)
  have h4 : ((∏ j, (o j).factorial : ℕ) : ℝ) * ((Nat.multinomial Finset.univ o : ℕ) : ℝ) =
      ((∑ j, o j).factorial : ℝ) := by exact_mod_cast h2
  push_cast at h4
  field_simp
  rw [← h4]
  ring
end Model

section PL
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma extO_comp_some (o : ι → ℕ) : extO o ∘ some = o := rfl

lemma extO_injective : Function.Injective (extO : (ι → ℕ) → Option ι → ℕ) := by
  intro o1 o2 h
  have := congrArg (fun f => f ∘ some) h
  simpa [extO_comp_some] using this

lemma psiM_ne_zero_ext {N : ℝ} {ω : ι → ℝ} {f : Option ι → ℕ} (h : psiM N ω f ≠ 0) :
    f = extO (f ∘ some) := by
  unfold psiM at h
  by_cases hc : ∑ j, f (some j) = f none
  · funext i
    rcases i with _ | j
    · simp [extO, hc]
    · rfl
  · simp [hc] at h

lemma cls_extO (X : Finset (Option ι)) (hX : none ∉ X) (o : ι → ℕ) :
    ∑ i ∈ X, extO o i = ∑ j, (if some j ∈ X then o j else 0) := by
  have h1 : ∑ i ∈ X, extO o i = ∑ i, (if i ∈ X then extO o i else 0) := by
    rw [Finset.sum_ite_mem]; simp
  rw [h1, Fintype.sum_option]
  simp [hX, extO]

lemma ofReal_geomP_sum {N : ℝ} (hN : 0 ≤ N) {W : ℝ} (hW0 : 0 ≤ W) (hW1 : W ≤ 1) (k : ℕ) :
    ∑' n : ℕ, ENNReal.ofReal (N ^ n / (N + 1) ^ (n + 1) *
      ((n.choose k : ℝ) * W ^ k * (1 - W) ^ (n - k))) = ENNReal.ofReal (geomP (N * W) k) := by
  have h := geom_mix N W hN hW0 hW1 k
  have hnn : ∀ n : ℕ, 0 ≤ N ^ n / (N + 1) ^ (n + 1) *
      ((n.choose k : ℝ) * W ^ k * (1 - W) ^ (n - k)) := by
    intro n
    have : 0 ≤ 1 - W := by linarith
    positivity
  have hsh : HasSum (fun n : ℕ => N ^ n / (N + 1) ^ (n + 1) *
      ((n.choose k : ℝ) * W ^ k * (1 - W) ^ (n - k))) (geomP (N * W) k) := by
    rw [← hasSum_nat_add_iff' k]
    have hz : ∑ i ∈ Finset.range k, N ^ i / (N + 1) ^ (i + 1) *
        ((i.choose k : ℝ) * W ^ k * (1 - W) ^ (i - k)) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hi)]; simp
    rw [hz, sub_zero]
    have e : (fun n : ℕ => N ^ (n + k) / (N + 1) ^ (n + k + 1) *
        (((n + k).choose k : ℝ) * W ^ k * (1 - W) ^ (n + k - k))) =
        fun l : ℕ => N ^ (k + l) / (N + 1) ^ (k + l + 1) * (((l + k).choose k : ℕ) : ℝ) * W ^ k * (1 - W) ^ l := by
      funext l
      rw [Nat.add_sub_cancel, add_comm l k]
      ring_nf
    rw [e]
    have e2 : geomP (N * W) k = (N * W) ^ k / (1 + N * W) ^ (k + 1) := by
      unfold geomP; rw [add_comm (N * W) 1]
    rw [e2]
    exact h
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsh.summable, hsh.tsum_eq]

end PL

section PL2
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem P_hasSum {N : ℝ} (hN : 0 ≤ N) {ω : ι → ℝ} (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1)
    (X : Finset (Option ι)) (hX : none ∉ X) (k : ℕ) :
    HasSum (fun f : Option ι → ℕ => if ∑ i ∈ X, f i = k then psiM N ω f ^ 2 else 0)
      (geomP (N * ∑ j, (if some j ∈ X then ω j else 0)) k) := by
  set W : ℝ := ∑ j, (if some j ∈ X then ω j else 0) with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hω j])
  have hWc : (∑ j, (if some j ∈ X then 0 else ω j)) = 1 - W := by
    have : ∑ j, (if some j ∈ X then ω j else 0) + ∑ j, (if some j ∈ X then 0 else ω j) = ∑ j, ω j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_); split_ifs <;> simp
    linarith
  have hW1 : W ≤ 1 := by
    have : 0 ≤ ∑ j, (if some j ∈ X then 0 else ω j) := Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hω j])
    linarith
  set G : (Option ι → ℕ) → ℝ := fun f => if ∑ i ∈ X, f i = k then psiM N ω f ^ 2 else 0 with hG
  have hG0 : ∀ f, 0 ≤ G f := fun f => by
    simp only [hG]; split_ifs <;> positivity
  -- ENNReal computation
  have hE : ∑' f, ENNReal.ofReal (G f) = ENNReal.ofReal (geomP (N * W) k) := by
    have s1 : ∑' f, ENNReal.ofReal (G f) = ∑' o : ι → ℕ, ENNReal.ofReal (G (extO o)) := by
      symm
      refine Function.Injective.tsum_eq (f := fun f => ENNReal.ofReal (G f)) extO_injective ?_
      intro f hf
      have hne : G f ≠ 0 := by
        intro h0; apply hf; simp [h0]
      have : psiM N ω f ≠ 0 := by
        intro h0; apply hne; simp [hG, h0]
      exact ⟨f ∘ some, (psiM_ne_zero_ext this).symm⟩
    rw [s1, ← ENNReal.tsum_fiberwise (fun o => ENNReal.ofReal (G (extO o))) (fun o => ∑ j, o j)]
    have s2 : ∀ n : ℕ, ∑' b : (fun o : ι → ℕ => ∑ j, o j) ⁻¹' {n}, ENNReal.ofReal (G (extO b)) =
        ENNReal.ofReal (N ^ n / (N + 1) ^ (n + 1) * ((n.choose k : ℝ) * W ^ k * (1 - W) ^ (n - k))) := by
      intro n
      have hset : ((fun o : ι → ℕ => ∑ j, o j) ⁻¹' {n} : Set (ι → ℕ)) =
          ↑(Finset.piAntidiag (Finset.univ : Finset ι) n) := by
        ext o; simp [Finset.mem_piAntidiag]
      rw [hset]
      rw [Finset.tsum_subtype' (Finset.piAntidiag (Finset.univ : Finset ι) n) (fun o => ENNReal.ofReal (G (extO o)))]
      have hterm : ∀ o ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
          G (extO o) = N ^ n / (N + 1) ^ (n + 1) *
            (if ∑ j, (if some j ∈ X then o j else 0) = k then
              ((Nat.multinomial Finset.univ o : ℕ) : ℝ) * ∏ j, ω j ^ o j else 0) := by
        intro o ho
        have hn : ∑ j, o j = n := (Finset.mem_piAntidiag.1 ho).1
        simp only [hG, cls_extO X hX o]
        rw [psiM_extO_sq hN hω o, hn]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun o ho => by rw [hterm o ho])]
      rw [← ENNReal.ofReal_sum_of_nonneg, ← Finset.mul_sum, thin_binom, hWc]
      intro o _
      have : 0 ≤ (1 - W) := by linarith
      have h1 : 0 ≤ N ^ n / (N + 1) ^ (n + 1) := by positivity
      refine mul_nonneg h1 ?_
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun j _ => pow_nonneg (hω j) _))
      · exact le_refl _
    rw [tsum_congr s2]
    exact ofReal_geomP_sum hN hW0 hW1 k
  have hne : ∑' f, ENNReal.ofReal (G f) ≠ ⊤ := by rw [hE]; exact ENNReal.ofReal_ne_top
  have hsm : Summable G := by
    have := ENNReal.summable_toReal hne
    refine this.congr (fun f => ?_)
    exact ENNReal.toReal_ofReal (hG0 f)
  have hgeom : 0 ≤ geomP (N * W) k := geomP_nonneg (by positivity) k
  have := ENNReal.ofReal_tsum_of_nonneg hG0 hsm
  rw [hE] at this
  have h2 := (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hG0) hgeom).1 this
  rw [← h2]
  exact hsm.hasSum

end PL2

section GT

lemma fact_tsum {A E : Type} (ψ' : A → E → ℝ) (β : A → ℕ) (μ : E → ℕ) (c : A → ℝ)
    (hc : ∀ a, 0 ≤ c a) (U : E → ℝ)
    (h : ∀ a e, ψ' a e = c a * (if μ e = β a then U e else 0)) (a b : A) :
    ∑' e, ψ' a e * ψ' b e =
      if β a = β b then Real.sqrt (∑' e, ψ' a e ^ 2) * Real.sqrt (∑' e, ψ' b e ^ 2) else 0 := by
  by_cases hab : β a = β b
  · rw [if_pos hab]
    set M : ℝ := ∑' e, (if μ e = β a then U e ^ 2 else 0) with hM
    have hM0 : 0 ≤ M := tsum_nonneg (fun e => by split_ifs <;> positivity)
    have e1 : ∀ e, ψ' a e * ψ' b e = (c a * c b) * (if μ e = β a then U e ^ 2 else 0) := by
      intro e
      rw [h a e, h b e, ← hab]
      split_ifs <;> ring
    have e2 : ∀ e, ψ' a e ^ 2 = (c a ^ 2) * (if μ e = β a then U e ^ 2 else 0) := by
      intro e; rw [h a e]; split_ifs <;> ring
    have e3 : ∀ e, ψ' b e ^ 2 = (c b ^ 2) * (if μ e = β a then U e ^ 2 else 0) := by
      intro e; rw [h b e, ← hab]; split_ifs <;> ring
    simp only [e1, e2, e3, tsum_mul_left]
    rw [← hM, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (hc a), Real.sqrt_sq (hc b)]
    have : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0
    rw [show c a * Real.sqrt M * (c b * Real.sqrt M) = c a * c b * (Real.sqrt M * Real.sqrt M) by ring, this]
  · rw [if_neg hab]
    refine (tsum_congr (fun e => ?_)).trans tsum_zero
    rw [h a e, h b e]
    by_cases ha : μ e = β a
    · have : μ e ≠ β b := fun h' => hab (ha.symm.trans h')
      simp [this]
    · simp [ha]
end GT

section GT2
variable {J : Type} [Fintype J]

def mergeF (S : Finset J) (a : S → ℕ) (e : {i : J // i ∉ S} → ℕ) : J → ℕ :=
  fun i => if h : i ∈ S then a ⟨i, h⟩ else e ⟨i, h⟩

lemma subsystem_eq (S : Finset J) (X : Matrix (J → ℕ) (J → ℕ) ℂ) (a b : S → ℕ) :
    subsystem S X a b = ∑' e : {i : J // i ∉ S} → ℕ, X (mergeF S a e) (mergeF S b e) := rfl

noncomputable def mergeEquiv (S : Finset J) : (J → ℕ) ≃ (S → ℕ) × ({i : J // i ∉ S} → ℕ) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => ℕ)

lemma mergeEquiv_symm (S : Finset J) (a : S → ℕ) (e : {i : J // i ∉ S} → ℕ) :
    (mergeEquiv S).symm (a, e) = mergeF S a e := rfl

end GT2

section GT3
variable {J : Type} [Fintype J]

theorem GT (S : Finset J) (ψ : (J → ℕ) → ℝ) (X : Matrix (J → ℕ) (J → ℕ) ℂ)
    (hX : ∀ a b, X a b = (ψ a : ℂ) * (ψ b : ℂ)) (hψ0 : ∀ f, 0 ≤ ψ f)
    (hψ1 : HasSum (fun f => ψ f ^ 2) 1)
    (cls : (J → ℕ) → ℕ) (β : (S → ℕ) → ℕ) (c : (S → ℕ) → ℝ) (hc : ∀ a, 0 ≤ c a)
    (μ : ({i : J // i ∉ S} → ℕ) → ℕ) (U : ({i : J // i ∉ S} → ℕ) → ℝ)
    (hfact : ∀ a e, ψ (mergeF S a e) = c a * (if μ e = β a then U e else 0))
    (hcls : ∀ a e, ψ (mergeF S a e) ≠ 0 → cls (mergeF S a e) = β a)
    (x : ℝ) (hx : 0 ≤ x)
    (hP : ∀ k, HasSum (fun f => if cls f = k then ψ f ^ 2 else 0) (geomP x k)) :
    extendedEntropyNats (subsystem S X) =
      ENNReal.ofReal (thermalNats x) := by
  set w : (S → ℕ) → ℝ := fun a => Real.sqrt (∑' e, ψ (mergeF S a e) ^ 2) with hw
  have hmat : subsystem S X = blockMat β w := by
    funext a b
    rw [subsystem_eq]
    have h1 : ∀ e, (ψ (mergeF S a e) : ℂ) * (ψ (mergeF S b e) : ℂ) =
        ((ψ (mergeF S a e) * ψ (mergeF S b e) : ℝ) : ℂ) := fun e => by push_cast; rfl
    simp only [hX, h1]
    rw [← Complex.ofReal_tsum]
    rw [fact_tsum (fun a e => ψ (mergeF S a e)) β μ c hc U hfact a b]
    unfold blockMat
    split_ifs <;> simp [hw]
  -- the 2D summability facts
  have hprod : HasSum (fun p : (S → ℕ) × ({i : J // i ∉ S} → ℕ) => ψ (mergeF S p.1 p.2) ^ 2) 1 := by
    have := (mergeEquiv S).symm.hasSum_iff.2 hψ1
    exact this
  have hw2 : ∀ a, w a ^ 2 = ∑' e, ψ (mergeF S a e) ^ 2 := by
    intro a; rw [hw]; simp only; rw [Real.sq_sqrt]; exact tsum_nonneg (fun e => by positivity)
  have hfib : ∀ a, HasSum (fun e => ψ (mergeF S a e) ^ 2) (w a ^ 2) := by
    intro a
    rw [hw2]
    exact (hprod.summable.prod_factor a).hasSum
  have hwsum : HasSum (fun a => w a ^ 2) 1 := by
    have := hprod.prod_fiberwise hfib
    exact this
  -- block masses
  have hLam : ∀ k, Lam β w k = geomP x k := by
    intro k
    have hG := hP k
    have hG2 := (mergeEquiv S).symm.hasSum_iff.2 hG
    have hpt : ∀ p : (S → ℕ) × ({i : J // i ∉ S} → ℕ),
        (if β p.1 = k then ψ (mergeF S p.1 p.2) ^ 2 else 0) =
        (fun f => if cls f = k then ψ f ^ 2 else 0) ((mergeEquiv S).symm p) := by
      intro p
      obtain ⟨a, e⟩ := p
      simp only [mergeEquiv_symm]
      by_cases h0 : ψ (mergeF S a e) = 0
      · simp [h0]
      · have := hcls a e h0
        simp only [this]
    have hG3 : HasSum (fun p : (S → ℕ) × ({i : J // i ∉ S} → ℕ) =>
        if β p.1 = k then ψ (mergeF S p.1 p.2) ^ 2 else 0) (geomP x k) := by
      have : (fun p : (S → ℕ) × ({i : J // i ∉ S} → ℕ) => if β p.1 = k then ψ (mergeF S p.1 p.2) ^ 2 else 0) =
          (fun f => if cls f = k then ψ f ^ 2 else 0) ∘ (mergeEquiv S).symm := funext hpt
      rw [this]; exact hG2
    have hfib2 : ∀ a, HasSum (fun e => if β a = k then ψ (mergeF S a e) ^ 2 else 0)
        (if β a = k then w a ^ 2 else 0) := by
      intro a
      split_ifs
      · exact hfib a
      · simpa using hasSum_zero
    have := hG3.prod_fiberwise hfib2
    unfold Lam
    exact this.tsum_eq
  rw [hmat, extendedEntropy_blockMat β w hwsum]
  simp only [hLam]
  have h := geomP_entropy_hasSum hx
  have hle : ∀ k, geomP x k ≤ 1 := fun k =>
    le_hasSum (geomP_hasSum hx) k (fun j _ => geomP_nonneg hx j)
  have hnn : ∀ k, 0 ≤ -(geomP x k) * Real.log (geomP x k) := by
    intro k
    have := Real.log_nonpos (geomP_nonneg hx k) (hle k)
    nlinarith [geomP_nonneg hx k]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn h.summable, h.tsum_eq]
end GT3

section Rep
variable {m : ℕ}

lemma resourceAmplitude_eq (p : PureLossBroadcastParameters m) (N : ℝ≥0) (f : ResourceMode m → ℕ) :
    resourceAmplitude p N f = psiM (N : ℝ) (fun j => (portWeight p j : ℝ)) f := by
  unfold resourceAmplitude vacuumAmplitude psiM tmsvWeight
  by_cases h : ∑ j, f (some j) = f none
  · rw [if_pos h, if_pos h]
    set n := f none
    have hf : (0:ℝ) ≤ n.factorial := by positivity
    have hprod : (0:ℝ) ≤ ∏ j, ((f (some j)).factorial : ℝ) := Finset.prod_nonneg (fun _ _ => by positivity)
    rw [Real.sqrt_div hf, Real.sqrt_prod _ (fun j _ => by positivity)]
    unfold gamA phiA
    rw [Finset.prod_div_distrib]
    push_cast
    ring
  · rw [if_neg h, if_neg h, mul_zero]

end Rep

section Merge
variable {J : Type} [Fintype J]

theorem Fintype_sum_dite' {α β : Type*} [Fintype α] {p : α → Prop} [DecidablePred p] [AddCommMonoid β]
    (f : ∀ a, p a → β) (g : ∀ a, ¬p a → β) :
    (∑ a, dite (p a) (f a) (g a)) =
    (∑ a : { a // p a }, f a a.2) + ∑ a : { a // ¬p a }, g a a.2 := by
  simp only [Finset.sum_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).sum_comp fun x : { x // p x } => f x x.2
  · exact (Equiv.subtypeEquivRight <| by simp).sum_comp fun x : { x // ¬p x } => g x x.2

lemma prod_merge (S : Finset J) (F : J → ℕ → ℝ) (a : S → ℕ) (e : {i : J // i ∉ S} → ℕ) :
    ∏ i, F i (mergeF S a e i) = (∏ i : S, F i (a i)) * ∏ i : {i : J // i ∉ S}, F i (e i) := by
  have h : ∀ i : J, F i (mergeF S a e i) =
      if h : i ∈ S then F i (a ⟨i, h⟩) else F i (e ⟨i, h⟩) := by
    intro i; unfold mergeF; split_ifs <;> rfl
  simp only [h]
  rw [Fintype.prod_dite]
  convert rfl

lemma sum_merge (S : Finset J) (F : J → ℕ → ℕ) (a : S → ℕ) (e : {i : J // i ∉ S} → ℕ) :
    ∑ i, F i (mergeF S a e i) = (∑ i : S, F i (a i)) + ∑ i : {i : J // i ∉ S}, F i (e i) := by
  have h : ∀ i : J, F i (mergeF S a e i) =
      if h : i ∈ S then F i (a ⟨i, h⟩) else F i (e ⟨i, h⟩) := by
    intro i; unfold mergeF; split_ifs <;> rfl
  simp only [h]
  rw [Fintype_sum_dite']
  convert rfl

lemma sum_merge_cls (S : Finset J) (a : S → ℕ) (e : {i : J // i ∉ S} → ℕ) :
    ∑ i ∈ Sᶜ, mergeF S a e i = ∑ i : {i : J // i ∉ S}, e i := by
  have h1 : ∑ i ∈ Sᶜ, mergeF S a e i = ∑ i, (if i ∈ Sᶜ then mergeF S a e i else 0) := by
    rw [Finset.sum_ite_mem]; simp
  rw [h1]
  have h2 : ∀ i : J, (if i ∈ Sᶜ then mergeF S a e i else 0) =
      if h : i ∈ S then 0 else e ⟨i, h⟩ := by
    intro i; unfold mergeF; by_cases h : i ∈ S <;> simp [h]
  simp only [h2]
  rw [Fintype_sum_dite']; simp

lemma sum_merge_cls' (S : Finset J) (a : S → ℕ) (e : {i : J // i ∉ S} → ℕ) :
    ∑ i ∈ S, mergeF S a e i = ∑ i : S, a i := by
  have h1 : ∑ i ∈ S, mergeF S a e i = ∑ i, (if i ∈ S then mergeF S a e i else 0) := by
    rw [Finset.sum_ite_mem]; simp
  rw [h1]
  have h2 : ∀ i : J, (if i ∈ S then mergeF S a e i else 0) =
      if h : i ∈ S then a ⟨i, h⟩ else 0 := by
    intro i; unfold mergeF; by_cases h : i ∈ S <;> simp [h]
  simp only [h2]
  rw [Fintype_sum_dite']; simp
  convert rfl
  ext x; simp

end Merge

section CaseGen
variable {J : Type} [Fintype J]

lemma mergeF_mem (S : Finset J) (z : J) (hz : z ∈ S) (a : S → ℕ)
    (e : {i : J // i ∉ S} → ℕ) : mergeF S a e z = a ⟨z, hz⟩ := by
  unfold mergeF; simp [hz]

lemma mergeF_not_mem (S : Finset J) (z : J) (hz : z ∉ S) (a : S → ℕ)
    (e : {i : J // i ∉ S} → ℕ) : mergeF S a e z = e ⟨z, hz⟩ := by
  unfold mergeF; simp [hz]

theorem factA_gen (z : J) (nu : J → ℕ → ℕ) (hnu : ∀ i x, i ≠ z → nu i x = x)
    (Phi : J → ℕ → ℝ) (hPhi : ∀ i x, 0 ≤ Phi i x) (gam : ℕ → ℝ) (hgam : ∀ n, 0 ≤ gam n)
    (ψ : (J → ℕ) → ℝ)
    (hrep : ∀ f, ψ f = if (∑ i, nu i (f i)) = f z then gam (f z) * ∏ i, Phi i (f i) else 0)
    (S : Finset J) (hz : z ∈ S) :
    ∃ (β : (S → ℕ) → ℕ) (c : (S → ℕ) → ℝ) (μ : ({i : J // i ∉ S} → ℕ) → ℕ)
      (U : ({i : J // i ∉ S} → ℕ) → ℝ),
      (∀ a, 0 ≤ c a) ∧
      (∀ a e, ψ (mergeF S a e) = c a * (if μ e = β a then U e else 0)) ∧
      (∀ a e, ψ (mergeF S a e) ≠ 0 → ∑ i ∈ Sᶜ, mergeF S a e i = β a) := by
  refine ⟨fun a => a ⟨z, hz⟩ - ∑ i : S, nu i.1 (a i),
    fun a => if ∑ i : S, nu i.1 (a i) ≤ a ⟨z, hz⟩ then gam (a ⟨z, hz⟩) * ∏ i : S, Phi i.1 (a i) else 0,
    fun e => ∑ i : {i : J // i ∉ S}, nu i.1 (e i),
    fun e => ∏ i : {i : J // i ∉ S}, Phi i.1 (e i), ?_, ?_, ?_⟩
  · intro a
    beta_reduce
    split_ifs
    · exact mul_nonneg (hgam _) (Finset.prod_nonneg (fun i _ => hPhi _ _))
    · exact le_refl _
  · intro a e
    rw [hrep, sum_merge S (fun i x => nu i x) a e, prod_merge S Phi a e, mergeF_mem S z hz]
    beta_reduce
    split_ifs <;> first | ring1 | (exfalso; omega) | simp_all
  · intro a e h0
    beta_reduce
    rw [hrep, sum_merge S (fun i x => nu i x) a e, prod_merge S Phi a e, mergeF_mem S z hz] at h0
    have hc : ∑ i : S, nu i.1 (a i) + ∑ i : {i : J // i ∉ S}, nu i.1 (e i) = a ⟨z, hz⟩ := by
      by_contra hne; exact h0 (if_neg hne)
    have h2 : ∑ i ∈ Sᶜ, mergeF S a e i = ∑ i : {i : J // i ∉ S}, nu i.1 (e i) := by
      rw [sum_merge_cls]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have : i.1 ≠ z := fun h => i.2 (h ▸ hz)
      rw [hnu _ _ this]
    rw [h2]; omega

theorem factB_gen (z : J) (nu : J → ℕ → ℕ) (hnu : ∀ i x, i ≠ z → nu i x = x)
    (Phi : J → ℕ → ℝ) (hPhi : ∀ i x, 0 ≤ Phi i x) (gam : ℕ → ℝ) (hgam : ∀ n, 0 ≤ gam n)
    (ψ : (J → ℕ) → ℝ)
    (hrep : ∀ f, ψ f = if (∑ i, nu i (f i)) = f z then gam (f z) * ∏ i, Phi i (f i) else 0)
    (S : Finset J) (hz : z ∉ S) :
    ∃ (β : (S → ℕ) → ℕ) (c : (S → ℕ) → ℝ) (μ : ({i : J // i ∉ S} → ℕ) → ℕ)
      (U : ({i : J // i ∉ S} → ℕ) → ℝ),
      (∀ a, 0 ≤ c a) ∧
      (∀ a e, ψ (mergeF S a e) = c a * (if μ e = β a then U e else 0)) ∧
      (∀ a e, ψ (mergeF S a e) ≠ 0 → ∑ i ∈ S, mergeF S a e i = β a) := by
  refine ⟨fun a => ∑ i : S, nu i.1 (a i),
    fun a => ∏ i : S, Phi i.1 (a i),
    fun e => e ⟨z, hz⟩ - ∑ i : {i : J // i ∉ S}, nu i.1 (e i),
    fun e => if ∑ i : {i : J // i ∉ S}, nu i.1 (e i) ≤ e ⟨z, hz⟩ then
      gam (e ⟨z, hz⟩) * ∏ i : {i : J // i ∉ S}, Phi i.1 (e i) else 0, ?_, ?_, ?_⟩
  · intro a
    exact Finset.prod_nonneg (fun i _ => hPhi _ _)
  · intro a e
    rw [hrep, sum_merge S (fun i x => nu i x) a e, prod_merge S Phi a e, mergeF_not_mem S z hz]
    beta_reduce
    split_ifs <;> first | ring1 | (exfalso; omega) | simp_all
  · intro a e _
    beta_reduce
    rw [sum_merge_cls']
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : i.1 ≠ z := fun h => hz (h ▸ i.2)
    rw [hnu _ _ this]
end CaseGen

section CaseOpt
variable {ι : Type} [Fintype ι]

def nuF : Option ι → ℕ → ℕ
  | none, _ => 0
  | some _, x => x

def PhiF (ω : ι → ℝ) : Option ι → ℕ → ℝ
  | none, _ => 1
  | some j, x => phiA (ω j) x

lemma PhiF_nonneg (ω : ι → ℝ) (i : Option ι) (x : ℕ) : 0 ≤ PhiF ω i x := by
  rcases i with _ | j <;> simp [PhiF, phiA_nonneg]

lemma psiM_eq' (N : ℝ) (ω : ι → ℝ) (f : Option ι → ℕ) :
    psiM N ω f = if (∑ i, nuF i (f i)) = f none then gamA N (f none) * ∏ i, PhiF ω i (f i) else 0 := by
  simp [psiM, Fintype.sum_option, Fintype.prod_option, nuF, PhiF]

lemma nuF_eq (i : Option ι) (x : ℕ) (h : i ≠ none) : nuF i x = x := by
  rcases i with _ | j
  · exact absurd rfl h
  · rfl

theorem caseA (N : ℝ) (hN0 : 0 ≤ N) (ω : ι → ℝ) (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1)
    (S : Finset (Option ι)) (hN : none ∈ S) (X : Matrix (Option ι → ℕ) (Option ι → ℕ) ℂ)
    (hX : ∀ a b, X a b = (psiM N ω a : ℂ) * (psiM N ω b : ℂ)) :
    extendedEntropyNats (subsystem S X) =
      ENNReal.ofReal (thermalNats (N * ∑ j, (if some j ∈ Sᶜ then ω j else 0))) := by
  classical
  have hX0 : none ∉ (Sᶜ : Finset (Option ι)) := by simp [hN]
  have hψ1 : HasSum (fun f => psiM N ω f ^ 2) 1 := by
    have := P_hasSum hN0 hω hsum (∅ : Finset (Option ι)) (by simp) 0
    simpa [geomP] using this
  obtain ⟨β, c, μ, U, hc, hfact, hcls⟩ := factA_gen (none : Option ι) nuF
    (fun i x h => nuF_eq i x h) (PhiF ω) (PhiF_nonneg ω) (gamA N) (gamA_nonneg N) (psiM N ω)
    (psiM_eq' N ω) S hN
  have hcls' : ∀ a e, psiM N ω (mergeF S a e) ≠ 0 → ∑ i ∈ Sᶜ, mergeF S a e i = β a := by
    intro a e h
    convert hcls a e h
  exact GT S (psiM N ω) X hX (psiM_nonneg N ω) hψ1 (fun f => ∑ i ∈ Sᶜ, f i) β c hc μ U hfact hcls' _
    (mul_nonneg hN0 (Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hω j])))
    (fun k => P_hasSum hN0 hω hsum (Sᶜ) hX0 k)

theorem caseB (N : ℝ) (hN0 : 0 ≤ N) (ω : ι → ℝ) (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1)
    (S : Finset (Option ι)) (hN : none ∉ S) (X : Matrix (Option ι → ℕ) (Option ι → ℕ) ℂ)
    (hX : ∀ a b, X a b = (psiM N ω a : ℂ) * (psiM N ω b : ℂ)) :
    extendedEntropyNats (subsystem S X) =
      ENNReal.ofReal (thermalNats (N * ∑ j, (if some j ∈ S then ω j else 0))) := by
  classical
  have hψ1 : HasSum (fun f => psiM N ω f ^ 2) 1 := by
    have := P_hasSum hN0 hω hsum (∅ : Finset (Option ι)) (by simp) 0
    simpa [geomP] using this
  obtain ⟨β, c, μ, U, hc, hfact, hcls⟩ := factB_gen (none : Option ι) nuF
    (fun i x h => nuF_eq i x h) (PhiF ω) (PhiF_nonneg ω) (gamA N) (gamA_nonneg N) (psiM N ω)
    (psiM_eq' N ω) S hN
  exact GT S (psiM N ω) X hX (psiM_nonneg N ω) hψ1 (fun f => ∑ i ∈ S, f i) β c hc μ U hfact hcls _
    (mul_nonneg hN0 (Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hω j])))
    (fun k => P_hasSum hN0 hω hsum S hN k)

end CaseOpt

section Final
variable {m : ℕ}

lemma thermalNats_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ thermalNats x := by
  have h := geomP_entropy_hasSum hx
  refine h.nonneg (fun k => ?_)
  have hle : geomP x k ≤ 1 := le_hasSum (geomP_hasSum hx) k (fun j _ => geomP_nonneg hx j)
  have := Real.log_nonpos (geomP_nonneg hx k) hle
  nlinarith [geomP_nonneg hx k]

lemma thermalNats_div (x : ℝ) : thermalNats x / Real.log 2 = thermalEntropyBits x := by
  unfold thermalNats thermalEntropyBits Real.logb
  ring

lemma portWeight_nonneg (p : PureLossBroadcastParameters m) (j : Option (Fin m)) :
    0 ≤ (portWeight p j : ℝ) := NNReal.coe_nonneg _

lemma portWeight_sum (p : PureLossBroadcastParameters m) :
    ∑ j : Option (Fin m), (portWeight p j : ℝ) = 1 := by
  rw [Fintype.sum_option]
  have h := p.total_le_one
  simp only [portWeight]
  rw [NNReal.coe_sub h]
  push_cast
  ring

/-- the Alice-free mass of a subsystem -/
def Wd (p : PureLossBroadcastParameters m) (S : Finset (ResourceMode m)) : ℝ :=
  if none ∈ S then ∑ j : Option (Fin m), (if some j ∈ Sᶜ then (portWeight p j : ℝ) else 0)
  else ∑ j : Option (Fin m), (if some j ∈ S then (portWeight p j : ℝ) else 0)

lemma Wd_nonneg (p : PureLossBroadcastParameters m) (S : Finset (ResourceMode m)) : 0 ≤ Wd p S := by
  unfold Wd
  split_ifs <;> exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp)

theorem resourceEntropyBits_eq (p : PureLossBroadcastParameters m) (N : ℝ≥0)
    (S : Finset (ResourceMode m)) :
    resourceEntropyBits p N S = ENNReal.ofReal (thermalEntropyBits ((N : ℝ) * Wd p S)) := by
  have hX : ∀ a b, purifiedResource p N a b =
      (psiM (N : ℝ) (fun j => (portWeight p j : ℝ)) a : ℂ) *
        (psiM (N : ℝ) (fun j => (portWeight p j : ℝ)) b : ℂ) := by
    intro a b
    unfold purifiedResource
    simp only [resourceAmplitude_eq]
  have hN0 : (0:ℝ) ≤ N := NNReal.coe_nonneg N
  have hx : 0 ≤ (N:ℝ) * Wd p S := mul_nonneg hN0 (Wd_nonneg p S)
  unfold resourceEntropyBits
  have hent : extendedEntropyNats (subsystem S (purifiedResource p N)) =
      ENNReal.ofReal (thermalNats ((N : ℝ) * Wd p S)) := by
    unfold Wd
    split_ifs with hS
    · convert caseA (N : ℝ) hN0 (fun j => (portWeight p j : ℝ)) (portWeight_nonneg p) (portWeight_sum p)
        S hS _ hX
    · convert caseB (N : ℝ) hN0 (fun j => (portWeight p j : ℝ)) (portWeight_nonneg p) (portWeight_sum p)
        S hS _ hX
  rw [hent, ← ENNReal.ofReal_div_of_pos (Real.log_pos (by norm_num)), thermalNats_div]

end Final

section Final2
variable {m : ℕ}

lemma Wd_alice (p : PureLossBroadcastParameters m) (U : Finset (Fin m)) :
    Wd p (aliceWith U) = (portWeight p none : ℝ) + ∑ i ∈ Finset.univ \ U, (p.transmissivity i : ℝ) := by
  unfold Wd
  have h1 : (none : ResourceMode m) ∈ aliceWith U := by simp [aliceWith]
  rw [if_pos h1, Fintype.sum_option]
  have h2 : (some none : ResourceMode m) ∈ (aliceWith U)ᶜ := by
    simp [aliceWith, receiverModes]
  rw [if_pos h2]
  congr 1
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun i _ => rfl)
  ext i
  simp [aliceWith, receiverModes, portWeight]

lemma Wd_env (p : PureLossBroadcastParameters m) (T : Finset (Fin m)) :
    Wd p (environmentWith T) = (portWeight p none : ℝ) + ∑ i ∈ T, (p.transmissivity i : ℝ) := by
  unfold Wd
  have h1 : (none : ResourceMode m) ∉ environmentWith T := by simp [environmentWith, receiverModes]
  rw [if_neg h1, Fintype.sum_option]
  have h2 : (some none : ResourceMode m) ∈ environmentWith T := by
    simp [environmentWith]
  rw [if_pos h2]
  congr 1
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun i _ => rfl)
  ext i
  simp [environmentWith, receiverModes, portWeight]

end Final2

section Dens
variable {m : ℕ}

lemma hasSum_sq_resource (p : PureLossBroadcastParameters m) (N : ℝ≥0) :
    HasSum (fun f : ResourceMode m → ℕ => resourceAmplitude p N f ^ 2) 1 := by
  have := P_hasSum (ι := Option (Fin m)) (N := (N : ℝ)) (NNReal.coe_nonneg N) (ω := fun j => (portWeight p j : ℝ))
    (portWeight_nonneg p) (portWeight_sum p) (∅ : Finset (Option (Option (Fin m)))) (by simp) 0
  simp only [Finset.notMem_empty, if_false, Finset.sum_const_zero, mul_zero, Finset.sum_empty] at this
  have e : geomP 0 0 = 1 := by simp [geomP]
  rw [e] at this
  have e2 : (fun f : ResourceMode m → ℕ => resourceAmplitude p N f ^ 2) =
      fun f => psiM (N : ℝ) (fun j => (portWeight p j : ℝ)) f ^ 2 := by
    funext f; rw [resourceAmplitude_eq]
  rw [e2]; exact this

end Dens

section Dens2
variable {m : ℕ}
open QAlgorithms.Papers.Independent.Dependency50.P33 in
theorem isDensity_purified (p : PureLossBroadcastParameters m) (N : ℝ≥0) :
    IsDensity (purifiedResource p N) := by
  set ψ : (ResourceMode m → ℕ) → ℝ := fun f => resourceAmplitude p N f with hψ
  have h1 := hasSum_sq_resource p N
  have hX : ∀ a b, purifiedResource p N a b = (ψ a : ℂ) * (ψ b : ℂ) := fun a b => rfl
  -- Hilbert vector
  have hmem : Memℓp (fun f : ResourceMode m → ℕ => ((ψ f : ℝ) : ℂ)) 2 := by
    refine memℓp_gen ?_
    have : (fun f : ResourceMode m → ℕ => ‖((ψ f : ℝ) : ℂ)‖ ^ (2:ENNReal).toReal) = fun f => ψ f ^ 2 := by
      funext f
      simp only [Complex.norm_real, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [this]
    exact h1.summable
  let v : QAlgorithms.RealRegisters.Hilbert (ResourceMode m → ℕ) := ⟨_, hmem⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨{ left := fun n => if n = 0 then v else 0
              right := fun n => if n = 0 then v else 0
              summable := ?_
              coefficients := ?_ }⟩
    · refine summable_of_ne_finset_zero (s := {0}) (fun n hn => ?_)
      have : n ≠ 0 := by simpa using hn
      simp [this]
    · intro i j
      rw [tsum_eq_single 0]
      · simp [hX, v]
      · intro n hn
        simp [hn]
  · intro s z
    set t : ℂ := ∑ j ∈ s, (ψ j : ℂ) * z j with ht
    have hsum : (∑ i ∈ s, ∑ j ∈ s, star (z i) * purifiedResource p N i j * z j) = star t * t := by
      have e1 : ∀ i j, star (z i) * purifiedResource p N i j * z j =
          (star (z i) * (ψ i : ℂ)) * ((ψ j : ℂ) * z j) := by
        intro i j; rw [hX]; ring
      simp only [e1]
      rw [← Finset.sum_mul_sum]
      congr 1
      rw [ht, star_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [mul_comm]
    rw [hsum]
    have : star t * t = ((Complex.normSq t : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [this]
    simp [Complex.normSq_nonneg]
  · have : (fun i : ResourceMode m → ℕ => (purifiedResource p N i i).re) = fun i => ψ i ^ 2 := by
      funext i; rw [hX]; simp [sq]
    rw [this]; exact h1.summable
  · have : (fun i : ResourceMode m → ℕ => (purifiedResource p N i i).re) = fun i => ψ i ^ 2 := by
      funext i; rw [hX]; simp [sq]
    rw [this]; exact h1.tsum_eq

end Dens2

section Final3
variable {m : ℕ}

lemma thermalEntropyBits_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ thermalEntropyBits x := by
  rw [← thermalNats_div]
  exact div_nonneg (thermalNats_nonneg hx) (Real.log_pos (by norm_num)).le

lemma resourceEntropyBits_toReal (p : PureLossBroadcastParameters m) (N : ℝ≥0)
    (S : Finset (ResourceMode m)) :
    (resourceEntropyBits p N S).toReal = thermalEntropyBits ((N : ℝ) * Wd p S) := by
  rw [resourceEntropyBits_eq, ENNReal.toReal_ofReal
    (thermalEntropyBits_nonneg (mul_nonneg (NNReal.coe_nonneg N) (Wd_nonneg p S)))]

lemma resourceEntropyBits_ne_top (p : PureLossBroadcastParameters m) (N : ℝ≥0)
    (S : Finset (ResourceMode m)) : resourceEntropyBits p N S ≠ ⊤ := by
  rw [resourceEntropyBits_eq]; exact ENNReal.ofReal_ne_top

lemma reverseCutYield_eq (p : PureLossBroadcastParameters m) (N : ℝ≥0) (T : Finset (Fin m)) :
    reverseCutYield p N T =
      thermalEntropyBits (((portWeight p none : ℝ) + (∑ i ∈ T, (p.transmissivity i : ℝ))) * (N : ℝ)) -
        thermalEntropyBits ((portWeight p none : ℝ) * (N : ℝ)) := by
  unfold reverseCutYield
  rw [resourceEntropyBits_toReal, resourceEntropyBits_toReal, Wd_alice, Wd_alice,
    Finset.sdiff_sdiff_eq_self (Finset.subset_univ T), Finset.sdiff_self]
  simp only [Finset.sum_empty, add_zero, mul_comm (N : ℝ)]

lemma reverseCutYield_eq' (p : PureLossBroadcastParameters m) (N : ℝ≥0) (T : Finset (Fin m)) :
    reverseCutYield p N T =
      (resourceEntropyBits p N (environmentWith T)).toReal -
        (resourceEntropyBits p N (environmentWith ∅)).toReal := by
  rw [reverseCutYield_eq, resourceEntropyBits_toReal, resourceEntropyBits_toReal, Wd_env, Wd_env]
  simp only [Finset.sum_empty, add_zero, mul_comm (N : ℝ)]

end Final3


theorem solution {m : ℕ} (hm : 0 < m)
    (p : PureLossBroadcastParameters m) (T : Finset (Fin m)) (hT : T.Nonempty) :
    (∀ N : ℝ≥0, IsDensity (purifiedResource p N) ∧
      (∀ S : Finset (ResourceMode m), resourceEntropyBits p N S ≠ ⊤) ∧
      reverseCutYield p N T =
        (resourceEntropyBits p N (environmentWith T)).toReal -
          (resourceEntropyBits p N (environmentWith ∅)).toReal ∧
      reverseCutYield p N T =
        thermalEntropyBits (((portWeight p none : ℝ) +
          (∑ i ∈ T, (p.transmissivity i : ℝ))) * (N : ℝ)) -
        thermalEntropyBits ((portWeight p none : ℝ) * (N : ℝ))) ∧
    Tendsto (fun N : ℝ≥0 => ENNReal.ofReal (reverseCutYield p N T))
      atTop (𝓝 (extendedCutBound p T)) := by
  refine ⟨fun N => ⟨isDensity_purified p N, resourceEntropyBits_ne_top p N,
    reverseCutYield_eq' p N T, reverseCutYield_eq p N T⟩, ?_⟩
  set sel : ℝ≥0 := ∑ i ∈ T, p.transmissivity i with hsel
  set loss : ℝ≥0 := portWeight p none with hloss
  have hselR : (∑ i ∈ T, (p.transmissivity i : ℝ)) = (sel : ℝ) := by
    rw [hsel]; push_cast; rfl
  have hfun : (fun N : ℝ≥0 => ENNReal.ofReal (reverseCutYield p N T)) =
      fun N : ℝ≥0 => ENNReal.ofReal (thermalEntropyBits (((loss : ℝ) + (sel : ℝ)) * (N : ℝ)) -
        thermalEntropyBits ((loss : ℝ) * (N : ℝ))) := by
    funext N; rw [reverseCutYield_eq, hselR]
  rw [hfun]
  unfold extendedCutBound
  simp only []
  by_cases hs : sel = 0
  · rw [if_pos hs]
    have : (fun N : ℝ≥0 => ENNReal.ofReal (thermalEntropyBits (((loss : ℝ) + (sel : ℝ)) * (N : ℝ)) -
        thermalEntropyBits ((loss : ℝ) * (N : ℝ)))) = fun _ => 0 := by
      funext N; simp [hs]
    rw [this]; exact tendsto_const_nhds
  · rw [if_neg hs]
    have hspos : (0:ℝ) < sel := by
      have := pos_iff_ne_zero.2 hs
      exact_mod_cast this
    by_cases hl : loss = 0
    · rw [if_pos hl]
      have hl0 : (loss : ℝ) = 0 := by rw [hl]; simp
      have : (fun N : ℝ≥0 => ENNReal.ofReal (thermalEntropyBits (((loss : ℝ) + (sel : ℝ)) * (N : ℝ)) -
          thermalEntropyBits ((loss : ℝ) * (N : ℝ)))) =
          fun N : ℝ≥0 => ENNReal.ofReal (thermalEntropyBits ((sel : ℝ) * (N : ℝ))) := by
        funext N; simp [hl0, thermalEntropyBits]
      rw [this]
      have h1 : Tendsto (fun N : ℝ => thermalEntropyBits ((sel : ℝ) * N)) atTop atTop :=
        therm_tendsto_atTop hspos
      have h2 := (ENNReal.tendsto_ofReal_atTop.comp h1).comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
      exact h2
    · rw [if_neg hl]
      have hlpos : (0:ℝ) < loss := by
        have := pos_iff_ne_zero.2 hl
        exact_mod_cast this
      have h1 := therm_diff_tendsto (c := (loss : ℝ) + (sel : ℝ)) (d := (loss : ℝ)) hlpos (by positivity)
      have h2 := (ENNReal.tendsto_ofReal h1).comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
      have e : ((loss : ℝ) + (sel : ℝ)) / (loss : ℝ) = (((loss : ℝ) + (sel : ℝ)) / (loss : ℝ)) := rfl
      exact h2
end
