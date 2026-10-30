-- Prove2me | solution 1 for RobustPCA.Recovery.lemma_2_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T11:42:19.514573+00:00
-- url     : https://prove2.me/submissions/dfdb911c-339a-4e27-b9ed-fa7d4a814a04

import Mathlib
import Definitions.Def_RobustPCA_Recovery_Setup
import Theorems.Thm_candes_recht_theorem41_bernoulli_tangent_sampling_concentration

set_option autoImplicit false

open MatrixCompletion


section HoeffNet
open MeasureTheory ProbabilityTheory Metric
open scoped NNReal ENNReal


lemma hoeff_two (q θ c : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hθ : 0 < θ) :
    q * Real.exp (θ * (c * (1 - 1 / q))) + (1 - q) * Real.exp (θ * c) ≤
      Real.exp (θ ^ 2 * c ^ 2 / (8 * q ^ 2)) := by
  let ν : Measure Bool := ENNReal.ofReal q • Measure.dirac true +
    ENNReal.ofReal (1 - q) • Measure.dirac false
  have hν : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hq0.le (by linarith)]
    simp
  let X : Bool → ℝ := fun b => if b then c * (1 - 1 / q) else c
  have hint : ∀ f : Bool → ℝ, ∫ b, f b ∂ν = q * f true + (1 - q) * f false := by
    intro f
    simp only [ν]
    rw [integral_add_measure (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
      (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
      integral_smul_measure, integral_dirac, integral_dirac, ENNReal.toReal_ofReal hq0.le,
      ENNReal.toReal_ofReal (by linarith)]
    simp [smul_eq_mul]
  have hmean : ∫ b, X b ∂ν = 0 := by
    rw [hint]
    simp only [X, if_true, Bool.false_eq_true, if_false]
    field_simp
    ring
  have hb : ∀ᵐ b ∂ν, X b ∈ Set.Icc (min (c * (1 - 1 / q)) c) (max (c * (1 - 1 / q)) c) := by
    refine Filter.Eventually.of_forall (fun b => ?_)
    cases b
    · simp [X]
    · simp [X]
  have h := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero (μ := ν) (X := X)
    (Measurable.of_discrete).aemeasurable hb hmean hθ
  rw [mgf, hint] at h
  simp only [X, if_true, Bool.false_eq_true, if_false] at h
  refine le_trans h (le_of_eq ?_)
  congr 1
  have e : ‖max (c * (1 - 1 / q)) c - min (c * (1 - 1 / q)) c‖ = |c| / q := by
    rw [Real.norm_eq_abs, max_sub_min_eq_abs, abs_abs,
      show c - c * (1 - 1 / q) = c / q by field_simp; ring, abs_div, abs_of_pos hq0]
  push_cast
  rw [e, div_pow, div_pow, sq_abs]
  field_simp
  ring



lemma sep_card_le {n : ℕ} (hn : 0 < n) (C : Finset (EuclideanSpace ℝ (Fin n)))
    (hC : ∀ x ∈ C, ‖x‖ ≤ 1) (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 1 / 4 < dist x y) :
    (C.card : ℝ) ≤ 9 ^ n := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, hn⟩ 1, fun h => ?_⟩⟩
    have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hn⟩) h
    simp at this
  have hV0 : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
    (measure_ball_pos volume _ one_pos).ne'
  have hVt : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hdisj : (C : Set (EuclideanSpace ℝ (Fin n))).PairwiseDisjoint
      (fun x => ball x (1 / 8)) := by
    intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    have h0 := hsep x hx y hy hxy
    have h1 := mem_ball.mp hzx
    have h2 := mem_ball.mp hzy
    have h3 := dist_triangle_left x y z
    linarith
  have hsub : (⋃ x ∈ C, ball x (1 / 8)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (9 / 8) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    rw [mem_ball, dist_zero_right]
    have h0 := hC x hx
    have h1 := mem_ball.mp hzx
    have h2 : ‖z‖ ≤ ‖x‖ + dist z x := by
      rw [dist_eq_norm]
      calc ‖z‖ = ‖x + (z - x)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖z - x‖ := norm_add_le _ _
    linarith
  have hmeas := measure_biUnion_finset (μ := volume) hdisj (fun x _ => measurableSet_ball)
  have hle := measure_mono (μ := volume) hsub
  rw [hmeas] at hle
  simp only [Measure.addHaar_ball volume _ (by norm_num : (0 : ℝ) ≤ 1 / 8),
    Measure.addHaar_ball volume _ (by norm_num : (0 : ℝ) ≤ 9 / 8), finrank_euclideanSpace_fin,
    Finset.sum_const, nsmul_eq_mul] at hle
  rw [← mul_assoc] at hle
  have h2 := (ENNReal.mul_le_mul_iff_left hV0 hVt).mp hle
  have h3 : (C.card : ℝ) * (1 / 8) ^ n ≤ (9 / 8) ^ n := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
    exact h2
  have e : (9 / 8 : ℝ) ^ n = 9 ^ n * (1 / 8) ^ n := by rw [← mul_pow]; norm_num
  rw [e] at h3
  exact le_of_mul_le_mul_right h3 (by positivity)

lemma net_exists {n : ℕ} (hn : 0 < n) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)), (∀ x ∈ N, ‖x‖ ≤ 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ N, ‖x - y‖ ≤ 1 / 4) ∧
      (N.card : ℝ) ≤ 9 ^ n := by
  set A : Set (EuclideanSpace ℝ (Fin n)) := closedBall 0 1 with hA
  set ε : ℝ≥0 := 1 / 4 with hε
  have hfin : ∀ C ⊆ A, IsSeparated (ε : ℝ≥0∞) C → C.encard ≤ ((9 ^ n : ℕ) : ℕ∞) := by
    intro C hCA hsep
    by_contra hlt
    push Not at hlt
    have hk : (((9 ^ n + 1 : ℕ)) : ℕ∞) ≤ C.encard := by
      rw [Nat.cast_add, Nat.cast_one]
      exact Order.add_one_le_of_lt hlt
    obtain ⟨D, hDC, hDcard⟩ := Set.exists_subset_encard_eq hk
    have hDfin : D.Finite := Set.finite_of_encard_eq_coe hDcard
    have hcard' : (hDfin.toFinset.card : ℕ∞) = ((9 ^ n + 1 : ℕ) : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, hDcard]
    have hcard : hDfin.toFinset.card = 9 ^ n + 1 := by exact_mod_cast hcard'
    have hb := sep_card_le hn hDfin.toFinset (fun x hx => by
        have := hCA (hDC (hDfin.mem_toFinset.mp hx))
        rw [hA, mem_closedBall, dist_zero_right] at this
        exact this)
      (fun x hx y hy hxy => by
        have h : (ε : ℝ≥0∞) < edist x y :=
          hsep (hDC (hDfin.mem_toFinset.mp hx)) (hDC (hDfin.mem_toFinset.mp hy)) hxy
        rw [edist_dist] at h
        have h' : ((ε : ℝ≥0∞)) = ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_coe_nnreal, hε]; congr 1
        rw [h', ENNReal.ofReal_lt_ofReal_iff (dist_pos.mpr hxy)] at h
        exact h)
    rw [hcard] at hb
    push_cast at hb
    linarith
  have hpack : packingNumber ε A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.coe_ne_top (9 ^ n))
    unfold packingNumber
    exact iSup_le (fun C => iSup_le (fun hCA => iSup_le (fun hsep => hfin C hCA hsep)))
  set M := maximalSeparatedSet ε A with hM
  have hMsub : M ⊆ A := maximalSeparatedSet_subset
  have hMcov : IsCover ε A M := isCover_maximalSeparatedSet hpack
  have hMcard : M.encard ≤ ((9 ^ n : ℕ) : ℕ∞) := hfin M hMsub isSeparated_maximalSeparatedSet
  have hMfin : M.Finite := Set.finite_of_encard_le_coe hMcard
  refine ⟨hMfin.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have := hMsub (hMfin.mem_toFinset.mp hx)
    rw [hA, mem_closedBall, dist_zero_right] at this
    exact this
  · intro x hx
    have hxA : x ∈ A := by rw [hA, mem_closedBall, dist_zero_right]; exact hx
    obtain ⟨y, hyM, hxy⟩ := hMcov hxA
    refine ⟨y, hMfin.mem_toFinset.mpr hyM, ?_⟩
    have h1 : edist x y ≤ (ε : ℝ≥0∞) := hxy
    rw [edist_le_coe] at h1
    rw [← dist_eq_norm]
    have h2 : (nndist x y : ℝ) ≤ (ε : ℝ) := by exact_mod_cast h1
    rw [coe_nndist, hε] at h2
    simpa using h2
  · have h1 : (hMfin.toFinset.card : ℕ∞) ≤ ((9 ^ n : ℕ) : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset]; exact hMcard
    have h2 : hMfin.toFinset.card ≤ 9 ^ n := by exact_mod_cast h1
    exact_mod_cast h2

/-- Spectral norm from a `1/4`-net of the unit ball. -/
lemma opNorm_le_net {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : Finset (EuclideanSpace ℝ (Fin n))) (hN1 : ∀ x ∈ N, ‖x‖ ≤ 1)
    (hcov : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ N, ‖x - y‖ ≤ 1 / 4) (M : ℝ)
    (hM : ∀ x ∈ N, ∀ y ∈ N, inner ℝ x (L y) ≤ M) : ‖L‖ ≤ 2 * M := by
  -- step 1: `‖L y‖ ≤ 4/3 M` on the net
  have h1 : ∀ y ∈ N, ‖L y‖ ≤ 4 / 3 * M := by
    intro y hy
    set u : EuclideanSpace ℝ (Fin n) := (‖L y‖)⁻¹ • L y with hu
    have hun : ‖u‖ ≤ 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm]
      rcases eq_or_ne ‖L y‖ 0 with h | h
      · rw [h]; simp
      · rw [inv_mul_cancel₀ h]
    have hinner : inner ℝ u (L y) = ‖L y‖ := by
      rw [hu, real_inner_smul_left, real_inner_self_eq_norm_sq]
      rcases eq_or_ne ‖L y‖ 0 with h | h
      · rw [h]; simp
      · field_simp
    obtain ⟨x, hx, hux⟩ := hcov u hun
    have hsplit : inner ℝ u (L y) = inner ℝ x (L y) + inner ℝ (u - x) (L y) := by
      rw [inner_sub_left]; ring
    have hcs : inner ℝ (u - x) (L y) ≤ ‖u - x‖ * ‖L y‖ := real_inner_le_norm _ _
    have hLy : 0 ≤ ‖L y‖ := norm_nonneg _
    have hb : ‖u - x‖ * ‖L y‖ ≤ 1 / 4 * ‖L y‖ := mul_le_mul_of_nonneg_right hux hLy
    have := hM x hx y hy
    linarith
  -- `M ≥ 0`
  have hM0 : 0 ≤ M := by
    obtain ⟨y, hy, _⟩ := hcov 0 (by simp)
    have := h1 y hy
    have := norm_nonneg (L y)
    linarith
  -- step 2: every unit vector
  have h2 : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ 1 → ‖L v‖ ≤ 4 / 3 * M + ‖L‖ / 4 := by
    intro v hv
    obtain ⟨y, hy, hvy⟩ := hcov v hv
    have e : L v = L y + L (v - y) := by rw [map_sub]; abel
    rw [e]
    calc ‖L y + L (v - y)‖ ≤ ‖L y‖ + ‖L (v - y)‖ := norm_add_le _ _
      _ ≤ 4 / 3 * M + ‖L‖ * ‖v - y‖ := add_le_add (h1 y hy) (L.le_opNorm _)
      _ ≤ 4 / 3 * M + ‖L‖ / 4 := by
          have := mul_le_mul_of_nonneg_left hvy (norm_nonneg L)
          linarith
  have h3 : ‖L‖ ≤ 4 / 3 * M + ‖L‖ / 4 := by
    refine L.opNorm_le_bound (by positivity) (fun v => ?_)
    rcases eq_or_ne v 0 with h | h
    · rw [h]; simp
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr h
      have hw : ‖(‖v‖)⁻¹ • v‖ ≤ 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
      have := h2 _ hw
      rw [map_smul, norm_smul, norm_inv, norm_norm] at this
      rw [inv_mul_le_iff₀ hvpos] at this
      linarith
  linarith

end HoeffNet

namespace RPCA29
open RobustPCA.Recovery
open scoped BigOperators Classical

lemma prod_ite_univ {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) (a b : ℝ) :
    ∏ x, (if x ∈ B then a else b) = a ^ B.card * b ^ (Fintype.card α - B.card) := by
  rw [← Finset.prod_mul_prod_compl B]
  have h1 : ∏ x ∈ B, (if x ∈ B then a else b) = ∏ x ∈ B, a :=
    Finset.prod_congr rfl (fun x hx => by simp [hx])
  have h2 : ∏ x ∈ Bᶜ, (if x ∈ B then a else b) = ∏ x ∈ Bᶜ, b :=
    Finset.prod_congr rfl (fun x hx => by rw [Finset.mem_compl] at hx; simp [hx])
  rw [h1, h2, Finset.prod_const, Finset.prod_const, Finset.card_compl]

lemma bw_eq_prod {N : ℕ} (p : ℝ) (A : Finset (Fin N × Fin N)) :
    bernoulliObservationWeight p A = ∏ x, (if x ∈ A then p else 1 - p) := by
  unfold bernoulliObservationWeight
  rw [prod_ite_univ]

/-! ## Frobenius inner product and the coordinate form of `P_T` -/

lemma bw_sum_one {N : ℕ} (p : ℝ) :
    ∑ A : Finset (Fin N × Fin N), bernoulliObservationWeight p A = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ : Finset (Fin N × Fin N))
  rw [Finset.powerset_univ, Finset.card_univ, show p + (1 - p) = 1 by ring, one_pow] at h
  exact h

lemma bw_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset (Fin N × Fin N)) :
    0 ≤ bernoulliObservationWeight p A := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

lemma prod_split {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) (F G : α → ℝ) :
    ∏ x, (if x ∈ t then F x else G x) = (∏ x ∈ t, F x) * ∏ x ∈ Finset.univ \ t, G x := by
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext x; simp
  · congr 1; ext x; simp

lemma sum_prod_ite {N : ℕ} (F G : Fin N × Fin N → ℝ) :
    ∑ Ω : Finset (Fin N × Fin N), ∏ x, (if x ∈ Ω then F x else G x) = ∏ x, (F x + G x) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  exact Finset.sum_congr rfl (fun t _ => prod_split t F G)

lemma bil_eq {n : ℕ} (A : RealMatrix n n) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) y) =
      ∑ i, ∑ j, x i * A i j * y j := by
  rw [LinearMap.coe_toContinuousLinearMap']
  change inner ℝ x (WithLp.toLp 2 (Matrix.mulVec A (WithLp.ofLp y)) :
    EuclideanSpace ℝ (Fin n)) = _
  simp only [PiLp.inner_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct, RCLike.inner_apply,
    conj_trivial]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma euc_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ∑ i, x i ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])

open scoped Matrix.Norms.L2Operator in
lemma spec_eq {n : ℕ} (X : RealMatrix n n) : MatrixCompletion.spectralNorm X = ‖X‖ := rfl

lemma g32_count (n : ℝ) (k : ℝ) (hn : 0 < n) (hk0 : 0 ≤ k) (hk : k ≤ 9 ^ (⌊n⌋₊)) (hnat : (⌊n⌋₊ : ℝ) = n) :
    k ^ 2 * Real.exp (-(25 * n)) ≤ n ^ (-11 : ℤ) := by
  have h9 : (9 : ℝ) ≤ Real.exp 3 := by
    have h := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    nlinarith [sq_nonneg (Real.exp 1)]
  have hk2 : k ^ 2 ≤ Real.exp (6 * n) := by
    have h1 : (9 : ℝ) ^ (⌊n⌋₊) ≤ Real.exp 3 ^ (⌊n⌋₊) := pow_le_pow_left₀ (by norm_num) h9 _
    rw [← Real.exp_nat_mul, hnat] at h1
    have h2 : k ^ 2 ≤ Real.exp (3 * n) ^ 2 := pow_le_pow_left₀ hk0 (le_trans hk (by
      rw [show (3 : ℝ) * n = n * 3 by ring]; exact h1)) 2
    rw [← Real.exp_nat_mul] at h2
    convert h2 using 2; push_cast; ring
  have hlog : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn; linarith
  have e : n ^ (-11 : ℤ) = Real.exp (-11 * Real.log n) := by
    rw [show (-11 : ℝ) * Real.log n = ((-11 : ℤ) : ℝ) * Real.log n by norm_num,
      ← Real.log_zpow, Real.exp_log (zpow_pos hn _)]
  rw [e]
  calc k ^ 2 * Real.exp (-(25 * n)) ≤ Real.exp (6 * n) * Real.exp (-(25 * n)) :=
        mul_le_mul_of_nonneg_right hk2 (Real.exp_pos _).le
    _ = Real.exp (-(19 * n)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-11 * Real.log n) := Real.exp_le_exp.mpr (by linarith)

end RPCA29

namespace RPCA29
open RobustPCA.Recovery
open scoped BigOperators Classical

lemma sign_inner {n : ℕ} (Ω : Finset (Fin n × Fin n)) (a : Fin n × Fin n → ℝ) :
    ∑ P ∈ Ω.powerset, (1 / 2 : ℝ) ^ Ω.card *
      Real.exp (∑ x, a x * signPattern Ω P x.1 x.2) = ∏ x ∈ Ω, Real.cosh (a x) := by
  have key : ∀ P ∈ Ω.powerset, Real.exp (∑ x, a x * signPattern Ω P x.1 x.2) =
      (∏ x ∈ P, Real.exp (a x)) * ∏ x ∈ Ω \ P, Real.exp (-a x) := by
    intro P hP
    rw [Finset.mem_powerset] at hP
    rw [Real.exp_sum]
    have h1 : ∀ x : Fin n × Fin n, Real.exp (a x * signPattern Ω P x.1 x.2) =
        if x ∈ Ω then (if x ∈ P then Real.exp (a x) else Real.exp (-a x)) else 1 := by
      intro x
      simp only [signPattern, Prod.mk.eta]
      by_cases hxP : x ∈ P
      · simp [hxP, hP hxP]
      · by_cases hxΩ : x ∈ Ω
        · simp [hxP, hxΩ]
        · simp [hxP, hxΩ]
    rw [Finset.prod_congr rfl (fun x _ => h1 x), Fintype.prod_ite_mem, Finset.prod_ite]
    congr 1
    · exact Finset.prod_congr (by
        ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hP h, h⟩⟩)
        (fun _ _ => rfl)
    · exact Finset.prod_congr (by ext x; simp [Finset.mem_sdiff]) (fun _ _ => rfl)
  rw [Finset.sum_congr rfl (fun P hP => by rw [key P hP]), ← Finset.mul_sum, ← Finset.prod_add,
    show (1 / 2 : ℝ) ^ Ω.card = ∏ _x ∈ Ω, (1 / 2 : ℝ) from (Finset.prod_const _).symm,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  rw [Real.cosh_eq]; ring

lemma sign_mgf {n : ℕ} (ρ : ℝ) (a : Fin n × Fin n → ℝ) :
    ∑ Ω : Finset (Fin n × Fin n), ∑ P ∈ Ω.powerset, bernoulliObservationWeight ρ Ω *
      (1 / 2 : ℝ) ^ Ω.card * Real.exp (∑ x, a x * signPattern Ω P x.1 x.2) =
      ∏ x, (1 - ρ + ρ * Real.cosh (a x)) := by
  have h : ∀ Ω : Finset (Fin n × Fin n), ∑ P ∈ Ω.powerset, bernoulliObservationWeight ρ Ω *
      (1 / 2 : ℝ) ^ Ω.card * Real.exp (∑ x, a x * signPattern Ω P x.1 x.2) =
      ∏ x, (if x ∈ Ω then ρ * Real.cosh (a x) else 1 - ρ) := by
    intro Ω
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, sign_inner, bw_eq_prod, prod_split, prod_split, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl (fun Ω _ => h Ω), sum_prod_ite]
  exact Finset.prod_congr rfl (fun x _ => by ring)

lemma ind_le_exp (p : Prop) [Decidable p] (A B : ℝ) (h : p → A ≤ B) :
    (if p then (1 : ℝ) else 0) ≤ Real.exp (B - A) := by
  split_ifs with hp
  · exact Real.one_le_exp (by linarith [h hp])
  · exact (Real.exp_pos _).le

lemma rsp_tail {n : ℕ} (ρ θ t : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hθ : 0 ≤ θ)
    (c : Fin n × Fin n → ℝ) :
    randomSignProb ρ (fun E : RealMatrix n n => t ≤ ∑ x, c x * E x.1 x.2) ≤
      Real.exp (-θ * t) * ∏ x, (1 - ρ + ρ * Real.cosh (θ * c x)) := by
  have hm := sign_mgf ρ (fun x => θ * c x)
  beta_reduce at hm
  rw [← hm, Finset.mul_sum]
  unfold randomSignProb
  refine Finset.sum_le_sum (fun Ω _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun P _ => ?_)
  have hw : 0 ≤ bernoulliObservationWeight ρ Ω * (1 / 2 : ℝ) ^ Ω.card :=
    mul_nonneg (bw_nonneg hρ0 hρ1 Ω) (by positivity)
  have hi := ind_le_exp (t ≤ ∑ x, c x * signPattern Ω P x.1 x.2) (θ * t)
    (∑ x, θ * c x * signPattern Ω P x.1 x.2) (fun h => by
      have := mul_le_mul_of_nonneg_left h hθ
      rw [Finset.mul_sum] at this
      have e : ∑ x, θ * c x * signPattern Ω P x.1 x.2 =
          ∑ x, θ * (c x * signPattern Ω P x.1 x.2) :=
        Finset.sum_congr rfl (fun x _ => by ring)
      linarith)
  calc bernoulliObservationWeight ρ Ω * (1 / 2 : ℝ) ^ Ω.card *
        (if t ≤ ∑ x, c x * signPattern Ω P x.1 x.2 then 1 else 0)
      ≤ bernoulliObservationWeight ρ Ω * (1 / 2 : ℝ) ^ Ω.card *
        Real.exp ((∑ x, θ * c x * signPattern Ω P x.1 x.2) - θ * t) :=
        mul_le_mul_of_nonneg_left hi hw
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring_nf

lemma factor_bd (ρ u B : ℝ) (hρ0 : 0 ≤ ρ) (hu : u ^ 2 ≤ B) :
    1 - ρ + ρ * Real.cosh u ≤ Real.exp (ρ * Real.exp (B / 2) * (u ^ 2 / 2)) := by
  have h1 : Real.cosh u ≤ Real.exp (u ^ 2 / 2) := Real.cosh_le_exp_half_sq u
  have hE0 := Real.exp_pos (u ^ 2 / 2)
  have h2 : Real.exp (u ^ 2 / 2) - 1 ≤ (u ^ 2 / 2) * Real.exp (u ^ 2 / 2) := by
    have := Real.add_one_le_exp (-(u ^ 2 / 2))
    have e : Real.exp (u ^ 2 / 2) * Real.exp (-(u ^ 2 / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_left this hE0.le
    rw [e] at this
    nlinarith
  have h3 : Real.exp (u ^ 2 / 2) ≤ Real.exp (B / 2) := Real.exp_le_exp.mpr (by linarith)
  have hv : 0 ≤ u ^ 2 / 2 := by positivity
  have h4 : Real.cosh u - 1 ≤ (u ^ 2 / 2) * Real.exp (B / 2) := by
    have := mul_le_mul_of_nonneg_left h3 hv
    linarith
  have h5 := Real.add_one_le_exp (ρ * (Real.cosh u - 1))
  have h6 : ρ * (Real.cosh u - 1) ≤ ρ * Real.exp (B / 2) * (u ^ 2 / 2) := by
    have := mul_le_mul_of_nonneg_left h4 hρ0
    linarith
  calc 1 - ρ + ρ * Real.cosh u = ρ * (Real.cosh u - 1) + 1 := by ring
    _ ≤ Real.exp (ρ * (Real.cosh u - 1)) := h5
    _ ≤ _ := Real.exp_le_exp.mpr h6

lemma prod_bd {ι : Type*} [Fintype ι] (ρ B θ : ℝ) (c : ι → ℝ) (hρ0 : 0 ≤ ρ)
    (hu : ∀ x, (θ * c x) ^ 2 ≤ B) :
    ∏ x, (1 - ρ + ρ * Real.cosh (θ * c x)) ≤
      Real.exp (ρ * Real.exp (B / 2) * θ ^ 2 / 2 * ∑ x, c x ^ 2) := by
  calc ∏ x, (1 - ρ + ρ * Real.cosh (θ * c x))
      ≤ ∏ x, Real.exp (ρ * Real.exp (B / 2) * ((θ * c x) ^ 2 / 2)) := by
        apply Finset.prod_le_prod
        · intro x _
          have := Real.one_le_cosh (θ * c x)
          nlinarith
        · intro x _
          exact factor_bd ρ _ B hρ0 (hu x)
    _ = Real.exp (∑ x, ρ * Real.exp (B / 2) * ((θ * c x) ^ 2 / 2)) := (Real.exp_sum _ _).symm
    _ = _ := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun x _ => by ring)

lemma heavy_bd (T s v e : ℝ) (hT : 0 < T) (hs : 0 < s) (he : |e| ≤ 1) :
    (v - (if |v| ≤ T / s then v else 0)) * e ≤ (s / T) * v ^ 2 := by
  split_ifs with h
  · rw [sub_self, zero_mul]; positivity
  · push Not at h
    rw [sub_zero]
    have h1 : T < s * |v| := by rwa [div_lt_iff₀ hs, mul_comm] at h
    have h2 : v * e ≤ |v| := by
      calc v * e ≤ |v * e| := le_abs_self _
        _ = |v| * |e| := abs_mul _ _
        _ ≤ |v| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg _)
        _ = |v| := mul_one _
    have h3 : |v| ≤ (s / T) * v ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT]
      have hv : v ^ 2 = |v| * |v| := by rw [← sq_abs]; ring
      rw [hv]
      nlinarith [abs_nonneg v]
    linarith

lemma vsq {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∑ p : Fin n × Fin n, (x p.1 * y p.2) ^ 2 ≤ 1 := by
  have e : ∑ p : Fin n × Fin n, (x p.1 * y p.2) ^ 2 = (∑ i, x i ^ 2) * ∑ j, y j ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    simp_rw [mul_pow]
  rw [e, euc_sq, euc_sq]
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hy2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
  nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]

lemma sign_abs {n : ℕ} (Ω P : Finset (Fin n × Fin n)) (i j : Fin n) :
    |signPattern Ω P i j| ≤ 1 := by
  unfold signPattern
  split_ifs <;> simp

lemma rsp_union {n : ℕ} {ι : Type*} [Fintype ι] {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (F : RealMatrix n n → Prop) (G : ι → RealMatrix n n → Prop)
    (h : ∀ Ω P, F (signPattern Ω P) → ∃ i, G i (signPattern Ω P)) :
    randomSignProb ρ F ≤ ∑ i, randomSignProb ρ (G i) := by
  unfold randomSignProb
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun Ω _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun P _ => ?_)
  have hw : 0 ≤ bernoulliObservationWeight ρ Ω * (1 / 2 : ℝ) ^ Ω.card :=
    mul_nonneg (bw_nonneg hρ0 hρ1 Ω) (by positivity)
  by_cases hF : F (signPattern Ω P)
  · obtain ⟨i, hi⟩ := h Ω P hF
    rw [if_pos hF]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => bernoulliObservationWeight ρ Ω *
      (1 / 2 : ℝ) ^ Ω.card * (if G i (signPattern Ω P) then 1 else 0))
      (fun j _ => mul_nonneg hw (by split_ifs <;> norm_num)) (Finset.mem_univ i))
    simp only [if_pos hi]
    exact le_refl _
  · rw [if_neg hF, mul_zero]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg hw (by split_ifs <;> norm_num))

lemma rsp_compl {n : ℕ} (ρ : ℝ) (F : RealMatrix n n → Prop) :
    randomSignProb ρ F + randomSignProb ρ (fun E => ¬ F E) = 1 := by
  unfold randomSignProb
  rw [← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl (fun Ω _ => ?_)).trans (bw_sum_one (N := n) ρ)
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun P _ => show _ = bernoulliObservationWeight ρ Ω *
      (1 / 2 : ℝ) ^ Ω.card by split_ifs <;> simp_all)]
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  push_cast
  rw [mul_comm, mul_assoc, ← mul_pow]
  norm_num

noncomputable def cL {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (p : Fin n × Fin n) : ℝ :=
  if |x p.1 * y p.2| ≤ 64 / Real.sqrt n then x p.1 * y p.2 else 0

lemma bil_split {n : ℕ} (hn : 0 < n) (E : RealMatrix n n) (hE : ∀ i j, |E i j| ≤ 1)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    inner ℝ x ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin E)) y) ≤
      ∑ p : Fin n × Fin n, cL x y p * E p.1 p.2 + Real.sqrt n / 64 := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have e : ∑ i, ∑ j, x i * E i j * y j = ∑ p : Fin n × Fin n, x p.1 * E p.1 p.2 * y p.2 :=
    (Fintype.sum_prod_type (f := fun p : Fin n × Fin n => x p.1 * E p.1 p.2 * y p.2)).symm
  have hv := vsq x y hx hy
  calc inner ℝ x ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin E)) y)
      = ∑ p : Fin n × Fin n, x p.1 * E p.1 p.2 * y p.2 := by rw [bil_eq]; exact e
    _ = ∑ p : Fin n × Fin n, cL x y p * E p.1 p.2 +
          ∑ p : Fin n × Fin n, (x p.1 * y p.2 - cL x y p) * E p.1 p.2 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ ∑ p : Fin n × Fin n, cL x y p * E p.1 p.2 +
          ∑ p : Fin n × Fin n, (Real.sqrt n / 64) * (x p.1 * y p.2) ^ 2 :=
        add_le_add (le_refl _) (Finset.sum_le_sum (fun p _ => by
          show (x p.1 * y p.2 - cL x y p) * E p.1 p.2 ≤ (Real.sqrt n / 64) * (x p.1 * y p.2) ^ 2
          unfold cL; exact heavy_bd 64 _ _ _ (by norm_num) hs (hE _ _)))
    _ = ∑ p : Fin n × Fin n, cL x y p * E p.1 p.2 +
          (Real.sqrt n / 64) * ∑ p : Fin n × Fin n, (x p.1 * y p.2) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := add_le_add (le_refl _) (mul_le_of_le_one_right (div_nonneg hs.le (by norm_num : (0:ℝ) ≤ 64)) hv)

lemma cL_sq {n : ℕ} (hn : 0 < n) (x y : EuclideanSpace ℝ (Fin n)) (p : Fin n × Fin n) :
    cL x y p ^ 2 ≤ 64 ^ 2 / n := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  unfold cL
  split_ifs with h
  · calc (x p.1 * y p.2) ^ 2 = |x p.1 * y p.2| ^ 2 := (sq_abs _).symm
      _ ≤ (64 / Real.sqrt n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 64 ^ 2 / n := by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  · rw [zero_pow two_ne_zero]; positivity

lemma cL_sum {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∑ p : Fin n × Fin n, cL x y p ^ 2 ≤ 1 := by
  refine le_trans (Finset.sum_le_sum (fun p _ => ?_)) (vsq x y hx hy)
  unfold cL
  split_ifs
  · exact le_refl _
  · rw [zero_pow two_ne_zero]; positivity

lemma tail_xy {n : ℕ} (hn : 0 < n) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρK : ρ * Real.exp ((1664 * 64) ^ 2 / 2) * 1664 ^ 2 ≤ 1)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    randomSignProb ρ (fun E : RealMatrix n n =>
      Real.sqrt n / 64 ≤ ∑ p : Fin n × Fin n, cL x y p * E p.1 p.2) ≤ Real.exp (-(25 * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1664 * Real.sqrt n := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ2 : θ ^ 2 = 1664 ^ 2 * n := by rw [hθ, mul_pow, Real.sq_sqrt hnR.le]
  have hθs : θ * (Real.sqrt n / 64) = 26 * n := by
    rw [hθ, show 1664 * Real.sqrt n * (Real.sqrt n / 64) = 26 * (Real.sqrt n * Real.sqrt n) by ring,
      Real.mul_self_sqrt hnR.le]
  have hu : ∀ p : Fin n × Fin n, (θ * cL x y p) ^ 2 ≤ (1664 * 64) ^ 2 := by
    intro p
    have h1 := mul_le_mul_of_nonneg_left (cL_sq hn x y p) (sq_nonneg θ)
    rw [mul_pow]
    calc θ ^ 2 * cL x y p ^ 2 ≤ θ ^ 2 * (64 ^ 2 / n) := h1
      _ = (1664 * 64) ^ 2 := by rw [hθ2]; field_simp
  have h1 := rsp_tail ρ θ (Real.sqrt n / 64) hρ0 hρ1 hθ0 (cL x y)
  have h2 := prod_bd ρ ((1664 * 64) ^ 2) θ (cL x y) hρ0 hu
  have hS := cL_sum x y hx hy
  set K := Real.exp ((1664 * 64) ^ 2 / 2) with hK
  have hK0 : 0 < K := Real.exp_pos _
  have hA0 : 0 ≤ ρ * K * θ ^ 2 / 2 := by positivity
  have h3 : ρ * K * θ ^ 2 / 2 * ∑ p : Fin n × Fin n, cL x y p ^ 2 ≤ n / 2 := by
    calc ρ * K * θ ^ 2 / 2 * ∑ p : Fin n × Fin n, cL x y p ^ 2 ≤ ρ * K * θ ^ 2 / 2 :=
          mul_le_of_le_one_right hA0 hS
      _ = (ρ * K * 1664 ^ 2) * n / 2 := by rw [hθ2]; ring
      _ ≤ 1 * n / 2 := by gcongr
      _ = n / 2 := by ring
  calc randomSignProb ρ (fun E : RealMatrix n n =>
        Real.sqrt n / 64 ≤ ∑ p : Fin n × Fin n, cL x y p * E p.1 p.2)
      ≤ Real.exp (-θ * (Real.sqrt n / 64)) *
          Real.exp (ρ * K * θ ^ 2 / 2 * ∑ p : Fin n × Fin n, cL x y p ^ 2) :=
        le_trans h1 (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
    _ = Real.exp (-(θ * (Real.sqrt n / 64)) +
          ρ * K * θ ^ 2 / 2 * ∑ p : Fin n × Fin n, cL x y p ^ 2) := by
        rw [← Real.exp_add, neg_mul]
    _ ≤ Real.exp (-(25 * n)) := by
        apply Real.exp_le_exp.mpr
        rw [hθs]
        linarith

theorem E1 : ∃ ρs : ℝ, 0 < ρs ∧ ρs ≤ 1 ∧ ∀ (n : ℕ) (ρ : ℝ), 0 < n → 0 ≤ ρ → ρ ≤ ρs →
    randomSignProb ρ (fun E : RealMatrix n n =>
      MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16) ≥ 1 - (n : ℝ) ^ (-11 : ℤ) := by
  have hK1 : 1 ≤ Real.exp ((1664 * 64 : ℝ) ^ 2 / 2) := Real.one_le_exp (by positivity)
  refine ⟨1 / (Real.exp ((1664 * 64) ^ 2 / 2) * 1664 ^ 2), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; nlinarith
  intro n ρ hn hρ0 hρ
  have hρK : ρ * Real.exp ((1664 * 64) ^ 2 / 2) * 1664 ^ 2 ≤ 1 := by
    have := (le_div_iff₀ (by positivity)).mp hρ
    linarith [mul_assoc ρ (Real.exp ((1664 * 64) ^ 2 / 2)) (1664 ^ 2 : ℝ)]
  have hρ1 : ρ ≤ 1 := by nlinarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  obtain ⟨N, hN1, hcov, hcard⟩ := net_exists hn
  have himp : ∀ Ω P, (fun E : RealMatrix n n =>
      ¬ MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16) (signPattern Ω P) →
      ∃ i : N × N, (fun E : RealMatrix n n => Real.sqrt n / 64 ≤ ∑ p : Fin n × Fin n,
        cL (i.1 : EuclideanSpace ℝ (Fin n)) (i.2 : EuclideanSpace ℝ (Fin n)) p * E p.1 p.2)
        (signPattern Ω P) := by
    intro Ω P hΩ
    by_contra hno
    push Not at hno
    apply hΩ
    have hb := opNorm_le_net (LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (signPattern Ω P))) N hN1 hcov (Real.sqrt n / 32)
      (fun x hx y hy => by
        have h1 := bil_split hn (signPattern Ω P) (sign_abs Ω P) x y (hN1 x hx) (hN1 y hy)
        have h2 := hno ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
        linarith)
    unfold MatrixCompletion.spectralNorm
    linarith
  have hbad : randomSignProb ρ (fun E : RealMatrix n n =>
      ¬ MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16) ≤ (n : ℝ) ^ (-11 : ℤ) := by
    calc _ ≤ ∑ i : N × N, randomSignProb ρ (fun E : RealMatrix n n =>
          Real.sqrt n / 64 ≤ ∑ p : Fin n × Fin n,
            cL (i.1 : EuclideanSpace ℝ (Fin n)) (i.2 : EuclideanSpace ℝ (Fin n)) p * E p.1 p.2) :=
          rsp_union hρ0 hρ1 _ _ himp
      _ ≤ ∑ _i : N × N, Real.exp (-(25 * n)) := Finset.sum_le_sum (fun i _ =>
          tail_xy hn ρ hρ0 hρ1 hρK _ _ (hN1 _ i.1.2) (hN1 _ i.2.2))
      _ = (N.card : ℝ) ^ 2 * Real.exp (-(25 * n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
            nsmul_eq_mul]
          push_cast
          ring
      _ ≤ (n : ℝ) ^ (-11 : ℤ) :=
          g32_count n N.card (by positivity) (by positivity)
            (by rw [Nat.floor_natCast]; exact hcard) (by rw [Nat.floor_natCast])
  have hc := rsp_compl ρ (fun E : RealMatrix n n =>
      MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16)
  rw [ge_iff_le]
  linarith

end RPCA29

namespace RPCA29
open RobustPCA.Recovery
open scoped BigOperators Classical

/-- inner random-sign average over `P ⊆ Ω` (copied from decomp/429b6866/reduction.lean) -/
noncomputable def RSF {n : ℕ} (G : RealMatrix n n → Prop) (Ω : Finset (Fin n × Fin n)) : ℝ :=
  ∑ P ∈ Ω.powerset, (1 / 2 : ℝ) ^ Ω.card * (if G (signPattern Ω P) then 1 else 0)

lemma rs_eq {n : ℕ} (ρ : ℝ) (G : RealMatrix n n → Prop) :
    randomSignProb ρ G = ∑ Ω, bernoulliObservationWeight ρ Ω * RSF G Ω := by
  unfold randomSignProb RSF
  refine Finset.sum_congr rfl (fun Ω _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  ring

lemma half_sum_one {n : ℕ} (Ω : Finset (Fin n × Fin n)) :
    ∑ _P ∈ Ω.powerset, (1 / 2 : ℝ) ^ Ω.card = 1 := by
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  push_cast
  rw [← mul_pow]
  norm_num

lemma RSF_nonneg {n : ℕ} (G : RealMatrix n n → Prop) (Ω : Finset (Fin n × Fin n)) :
    0 ≤ RSF G Ω := by
  unfold RSF
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num))

lemma RSF_le_one {n : ℕ} (G : RealMatrix n n → Prop) (Ω : Finset (Fin n × Fin n)) :
    RSF G Ω ≤ 1 := by
  unfold RSF
  calc _ ≤ ∑ _P ∈ Ω.powerset, (1 / 2 : ℝ) ^ Ω.card :=
        Finset.sum_le_sum (fun P _ => mul_le_of_le_one_right (by positivity)
          (by split_ifs <;> norm_num))
    _ = 1 := half_sum_one Ω

/-- conditioning on the support: bad supports plus a uniform bound on the good ones -/
lemma rs_cond {n : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (G : RealMatrix n n → Prop)
    (good : Finset (Fin n × Fin n) → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ Ω, good Ω → RSF G Ω ≤ δ) :
    randomSignProb ρ G ≤ bernoulliEventProb ρ (fun Ω => ¬ good Ω) + δ := by
  rw [rs_eq]
  unfold bernoulliEventProb
  have hδ' : δ = ∑ Ω : Finset (Fin n × Fin n), bernoulliObservationWeight ρ Ω * δ := by
    rw [← Finset.sum_mul, bw_sum_one, one_mul]
  rw [hδ', ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun Ω _ => ?_)
  have hw := bw_nonneg hρ0 hρ1 Ω
  by_cases hg : good Ω
  · rw [if_neg (not_not.mpr hg), zero_add]
    exact mul_le_mul_of_nonneg_left (h Ω hg) hw
  · rw [if_pos hg]
    have := mul_le_mul_of_nonneg_left (RSF_le_one G Ω) hw
    have := mul_nonneg hw hδ
    linarith

lemma RSF_union {n : ℕ} {ι : Type*} [Fintype ι] (Ω : Finset (Fin n × Fin n))
    (F : RealMatrix n n → Prop) (G : ι → RealMatrix n n → Prop)
    (h : ∀ P ⊆ Ω, F (signPattern Ω P) → ∃ i, G i (signPattern Ω P)) :
    RSF F Ω ≤ ∑ i, RSF (G i) Ω := by
  unfold RSF
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun P hP => ?_)
  rw [Finset.mem_powerset] at hP
  have hw : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Ω.card := by positivity
  by_cases hF : F (signPattern Ω P)
  · obtain ⟨i, hi⟩ := h P hP hF
    rw [if_pos hF]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => (1 / 2 : ℝ) ^ Ω.card *
      (if G i (signPattern Ω P) then 1 else 0))
      (fun j _ => mul_nonneg hw (by split_ifs <;> norm_num)) (Finset.mem_univ i))
    simp only [if_pos hi]
    exact le_refl _
  · rw [if_neg hF, mul_zero]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg hw (by split_ifs <;> norm_num))

/-- Hoeffding over the uniform signs on a fixed support -/
lemma sign_hoeff {n : ℕ} (Ω : Finset (Fin n × Fin n)) (M : Fin n × Fin n → ℝ) (θ t : ℝ)
    (hθ : 0 ≤ θ) :
    RSF (fun E : RealMatrix n n => t ≤ ∑ p : Fin n × Fin n, M p * E p.1 p.2) Ω ≤
      Real.exp (-θ * t + θ ^ 2 / 2 * ∑ p ∈ Ω, M p ^ 2) := by
  have hm := sign_inner Ω (fun p => θ * M p)
  beta_reduce at hm
  unfold RSF
  calc _ ≤ ∑ P ∈ Ω.powerset, Real.exp (-θ * t) * ((1 / 2 : ℝ) ^ Ω.card *
        Real.exp (∑ x, θ * M x * signPattern Ω P x.1 x.2)) := by
        refine Finset.sum_le_sum (fun P _ => ?_)
        have hi := ind_le_exp (t ≤ ∑ p : Fin n × Fin n, M p * signPattern Ω P p.1 p.2) (θ * t)
          (∑ x, θ * M x * signPattern Ω P x.1 x.2) (fun h => by
            have := mul_le_mul_of_nonneg_left h hθ
            rw [Finset.mul_sum] at this
            have e : ∑ x, θ * M x * signPattern Ω P x.1 x.2 =
                ∑ x, θ * (M x * signPattern Ω P x.1 x.2) :=
              Finset.sum_congr rfl (fun x _ => by ring)
            linarith)
        calc (1 / 2 : ℝ) ^ Ω.card *
              (if t ≤ ∑ p : Fin n × Fin n, M p * signPattern Ω P p.1 p.2 then 1 else 0)
            ≤ (1 / 2 : ℝ) ^ Ω.card *
              Real.exp ((∑ x, θ * M x * signPattern Ω P x.1 x.2) - θ * t) :=
              mul_le_mul_of_nonneg_left hi (by positivity)
          _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring_nf
    _ = Real.exp (-θ * t) * ∏ x ∈ Ω, Real.cosh (θ * M x) := by rw [← Finset.mul_sum, hm]
    _ ≤ Real.exp (-θ * t) * ∏ x ∈ Ω, Real.exp ((θ * M x) ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun x _ => ?_)
          (fun x _ => Real.cosh_le_exp_half_sq _)) (Real.exp_pos _).le
        exact le_trans zero_le_one (Real.one_le_cosh _)
    _ = _ := by
        rw [← Real.exp_sum, ← Real.exp_add, Finset.mul_sum]
        congr 1
        congr 1
        exact Finset.sum_congr rfl (fun x _ => by ring)

end RPCA29

namespace RPCA29
open RobustPCA.Recovery
open scoped BigOperators Classical

noncomputable def projM {n r : ℕ} (u : Fin r → Fin n → ℝ) : RealMatrix n n :=
  fun i a => ∑ k, u k i * u k a

/-- `P_U` as a matrix. -/
noncomputable def PU {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.u

/-- `P_V` as a matrix. -/
noncomputable def PV {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.v

lemma orth_idem {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) :
    projM u * projM u = projM u := by
  ext i c
  simp only [Matrix.mul_apply, projM]
  have h1 : ∀ a, (∑ k, u k i * u k a) * (∑ l, u l a * u l c) =
      ∑ k, ∑ l, u k i * u l c * (u k a * u l a) := by
    intro a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  have h2 : ∀ l, ∑ a, u k i * u l c * (u k a * u l a) =
      u k i * u l c * (if k = l then 1 else 0) := by
    intro l
    rw [← Finset.mul_sum, hu]
  simp_rw [h2]
  simp

lemma PU_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PU SV * PU SV = PU SV :=
  orth_idem SV.u SV.u_orthonormal

lemma PV_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PV SV * PV SV = PV SV :=
  orth_idem SV.v SV.v_orthonormal

lemma tangent_eq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV X = PU SV * X + X * PV SV - PU SV * X * PV SV := by
  ext i j
  simp only [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, PU, PV, projM]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

lemma tangent_add {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    tangentProjection SV (X + Y) = tangentProjection SV X + tangentProjection SV Y := by
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul]
  abel

lemma tangent_smul {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (c : ℝ) (X : RealMatrix n n) :
    tangentProjection SV (c • X) = c • tangentProjection SV X := by
  simp only [tangent_eq, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]

lemma tangent_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV (tangentProjection SV X) = tangentProjection SV X := by
  have hA := PU_idem SV
  have hB := PV_idem SV
  have hB' : ∀ Y : RealMatrix n n, Y * PV SV * PV SV = Y * PV SV := by
    intro Y; rw [Matrix.mul_assoc, hB]
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    ← Matrix.mul_assoc, hA, hB']
  abel

lemma tangent_normal {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV (normalProjection SV X) = 0 := by
  have h : tangentProjection SV (X - tangentProjection SV X) =
      tangentProjection SV X - tangentProjection SV (tangentProjection SV X) := by
    simp only [tangent_eq, Matrix.mul_sub, Matrix.sub_mul]
    abel
  simp only [normalProjection, h, tangent_idem, sub_self]

/-! ## Norm facts -/

lemma spectral_add {n : ℕ} (A B : RealMatrix n n) :
    MatrixCompletion.spectralNorm (A + B) ≤
      MatrixCompletion.spectralNorm A + MatrixCompletion.spectralNorm B := by
  unfold MatrixCompletion.spectralNorm
  rw [map_add, map_add]
  exact norm_add_le _ _

lemma entrySup_nonneg {n : ℕ} (A : RealMatrix n n) : 0 ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))

lemma le_entrySup {n : ℕ} (A : RealMatrix n n) (i j : Fin n) : |A i j| ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact le_ciSup_of_le (Finite.bddAbove_range _) i
    (le_ciSup (f := fun j => |A i j|) (Finite.bddAbove_range _) j)

lemma entrySup_add {n : ℕ} (A B : RealMatrix n n) :
    entrySupNorm (A + B) ≤ entrySupNorm A + entrySupNorm B := by
  have h0 : 0 ≤ entrySupNorm A + entrySupNorm B :=
    add_nonneg (entrySup_nonneg A) (entrySup_nonneg B)
  unfold entrySupNorm
  refine Real.iSup_le (fun i => Real.iSup_le (fun j => ?_) h0) h0
  calc |(A + B) i j| = |A i j + B i j| := rfl
    _ ≤ |A i j| + |B i j| := abs_add_le _ _
    _ ≤ entrySupNorm A + entrySupNorm B := add_le_add (le_entrySup A i j) (le_entrySup B i j)

lemma compProj_add {n : ℕ} (Ω : Finset (Fin n × Fin n)) (A B : RealMatrix n n) :
    compProj Ω (A + B) = compProj Ω A + compProj Ω B := by
  ext i j
  simp only [compProj, samplingProjection, Matrix.sub_apply, Matrix.add_apply]
  split_ifs <;> ring

lemma abs_le_frob {n : ℕ} (X : RealMatrix n n) (i j : Fin n) : |X i j| ≤ frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  apply Real.abs_le_sqrt
  calc X i j ^ 2 ≤ ∑ j', X i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => X i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', X i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', X i' j' ^ 2)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)

lemma frob_sampling_le {n : ℕ} (Ω : Finset (Fin n × Fin n)) (X : RealMatrix n n) :
    frobeniusNorm (samplingProjection Ω X) ≤ frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  simp only [samplingProjection]
  split_ifs
  · exact le_rfl
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; exact sq_nonneg _

/-! ## The Neumann-series certificate: `𝒫_Ω W^S = λ E` -/

/-- `𝒜 X = 𝒫_Ω 𝒫_T 𝒫_Ω X` as a linear map. -/
noncomputable def Alin {n r : ℕ} {L0 : RealMatrix n n} (Ω : Finset (Fin n × Fin n))
    (SV : SVD L0 r) : RealMatrix n n →ₗ[ℝ] RealMatrix n n where
  toFun X := samplingProjection Ω (tangentProjection SV (samplingProjection Ω X))
  map_add' X Y := by
    have h1 : samplingProjection Ω (X + Y) = samplingProjection Ω X + samplingProjection Ω Y := by
      ext i j; simp only [samplingProjection, Matrix.add_apply]; split_ifs <;> ring
    rw [h1, tangent_add]
    ext i j; simp only [samplingProjection, Matrix.add_apply]; split_ifs <;> ring
  map_smul' c X := by
    have h1 : samplingProjection Ω (c • X) = c • samplingProjection Ω X := by
      ext i j; simp only [samplingProjection, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> ring
    rw [h1, tangent_smul]
    ext i j; simp only [samplingProjection, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

lemma PTOpNormLe_mono {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)}
    {SV : SVD L0 r} {σ τ : ℝ} (h : PTOpNormLe Ω SV σ) (hστ : σ ≤ τ) : PTOpNormLe Ω SV τ := by
  intro X
  have hX : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
  exact (h X).trans (mul_le_mul_of_nonneg_right hστ hX)

lemma Alin_bound {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)}
    {SV : SVD L0 r} {σ : ℝ} (hσ0 : 0 ≤ σ) (h : PTOpNormLe Ω SV σ) (X : RealMatrix n n) :
    frobeniusNorm (Alin Ω SV X) ≤ σ * frobeniusNorm X := by
  show frobeniusNorm (samplingProjection Ω (tangentProjection SV (samplingProjection Ω X))) ≤ _
  exact (h _).trans (mul_le_mul_of_nonneg_left (frob_sampling_le Ω X) hσ0)

lemma Alin_iter_bound {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)}
    {SV : SVD L0 r} {σ : ℝ} (hσ0 : 0 ≤ σ) (h : PTOpNormLe Ω SV σ) (E : RealMatrix n n) (k : ℕ) :
    frobeniusNorm ((Alin Ω SV)^[k] E) ≤ σ ^ k * frobeniusNorm E := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc frobeniusNorm (Alin Ω SV ((Alin Ω SV)^[k] E))
        ≤ σ * frobeniusNorm ((Alin Ω SV)^[k] E) := Alin_bound hσ0 h _
      _ ≤ σ * (σ ^ k * frobeniusNorm E) := mul_le_mul_of_nonneg_left ih hσ0
      _ = σ ^ (k + 1) * frobeniusNorm E := by ring

lemma iter_summable {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)}
    {SV : SVD L0 r} {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (h : PTOpNormLe Ω SV σ)
    (E : RealMatrix n n) : Summable (fun k => (Alin Ω SV)^[k] E) := by
  refine Pi.summable.2 (fun i => Pi.summable.2 (fun j => ?_))
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hσ0 hσ1).mul_right
    (frobeniusNorm E)) (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_le_frob _ i j).trans (Alin_iter_bound hσ0 h E k)

/-- evaluation at an entry -/
def evL {n : ℕ} (i j : Fin n) : RealMatrix n n →ₗ[ℝ] ℝ where
  toFun X := X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma entry_tsum {n : ℕ} {f : ℕ → RealMatrix n n} (hf : Summable f) (i j : Fin n) :
    (∑' k, f k) i j = ∑' k, f k i j :=
  ((hf.hasSum.map (evL i j) (LinearMap.continuous_of_finiteDimensional _)).tsum_eq).symm


lemma projM_transpose {n r : ℕ} (u : Fin r → Fin n → ℝ) :
    Matrix.transpose (projM u) = projM u := by
  ext i a
  simp only [Matrix.transpose_apply, projM]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)


lemma inner_eq_trace {n : ℕ} (X Y : RealMatrix n n) :
    matrixInner X Y = (Matrix.transpose X * Y).trace := by
  simp only [matrixInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma inner_tangent {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    matrixInner (tangentProjection SV X) Y = matrixInner X (tangentProjection SV Y) := by
  rw [inner_eq_trace, inner_eq_trace, tangent_eq, tangent_eq]
  have hU : Matrix.transpose (PU SV) = PU SV := projM_transpose _
  have hV : Matrix.transpose (PV SV) = PV SV := projM_transpose _
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, hU, hV,
    Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_add, Matrix.mul_assoc]
  have e1 : (PV SV * (Matrix.transpose X * Y)).trace =
      (Matrix.transpose X * (Y * PV SV)).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have e2 : (PV SV * (Matrix.transpose X * (PU SV * Y))).trace =
      (Matrix.transpose X * (PU SV * (Y * PV SV))).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1, e2]


lemma inner_sampling {n : ℕ} (Ω : Finset (Fin n × Fin n)) (X Y : RealMatrix n n) :
    matrixInner (samplingProjection Ω X) Y = matrixInner X (samplingProjection Ω Y) := by
  unfold matrixInner samplingProjection
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  split_ifs <;> ring

lemma inner_comm' {n : ℕ} (X Y : RealMatrix n n) : matrixInner X Y = matrixInner Y X := by
  unfold matrixInner
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))

lemma inner_Alin {n r : ℕ} {L0 : RealMatrix n n} (Ω : Finset (Fin n × Fin n)) (SV : SVD L0 r)
    (X Y : RealMatrix n n) : matrixInner (Alin Ω SV X) Y = matrixInner X (Alin Ω SV Y) := by
  show matrixInner (samplingProjection Ω (tangentProjection SV (samplingProjection Ω X))) Y =
    matrixInner X (samplingProjection Ω (tangentProjection SV (samplingProjection Ω Y)))
  rw [inner_sampling, inner_tangent, inner_sampling]

lemma inner_iter {n r : ℕ} {L0 : RealMatrix n n} (Ω : Finset (Fin n × Fin n)) (SV : SVD L0 r)
    (k : ℕ) (X Y : RealMatrix n n) :
    matrixInner ((Alin Ω SV)^[k] X) Y = matrixInner X ((Alin Ω SV)^[k] Y) := by
  induction k generalizing Y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', inner_Alin, ih, ← Function.iterate_succ_apply]

def pairL {n : ℕ} (Z : RealMatrix n n) : RealMatrix n n →ₗ[ℝ] ℝ where
  toFun Y := matrixInner Z Y
  map_add' X Y := by
    unfold matrixInner
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    unfold matrixInner
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma inner_tsum_right {n : ℕ} (Z : RealMatrix n n) {f : ℕ → RealMatrix n n} (hf : Summable f) :
    matrixInner Z (∑' k, f k) = ∑' k, matrixInner Z (f k) :=
  ((hf.hasSum.map (pairL Z) (LinearMap.continuous_of_finiteDimensional _)).tsum_eq).symm

/-- duality: the Neumann series of the self-adjoint map `Alin` moves across the pairing -/
lemma dual_tsum {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)} {SV : SVD L0 r}
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (h : PTOpNormLe Ω SV σ) (Z Y : RealMatrix n n) :
    matrixInner Z (∑' k, (Alin Ω SV)^[k] Y) = matrixInner (∑' k, (Alin Ω SV)^[k] Z) Y := by
  rw [inner_tsum_right Z (iter_summable hσ0 hσ1 h Y), inner_comm' _ Y,
    inner_tsum_right Y (iter_summable hσ0 hσ1 h Z)]
  refine tsum_congr (fun k => ?_)
  rw [← inner_iter, inner_comm']

end RPCA29

namespace RPCA29
open RobustPCA.Recovery
open scoped BigOperators Classical

/-- A matrix as a vector of `EuclideanSpace ℝ (Fin n × Fin n)` (from decomp/0363db4b). -/
noncomputable def toE {n : ℕ} (X : RealMatrix n n) : EuclideanSpace ℝ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => X p.1 p.2)

lemma toE_apply {n : ℕ} (X : RealMatrix n n) (p : Fin n × Fin n) : toE X p = X p.1 p.2 := rfl

lemma frob_toE {n : ℕ} (X : RealMatrix n n) : frobeniusNorm X = ‖toE X‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold frobeniusNorm frobeniusNormSq
  congr 1
  rw [Fintype.sum_prod_type]
  simp [toE_apply, sq_abs]

noncomputable def toEL {n : ℕ} : RealMatrix n n →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n) where
  toFun := toE
  map_add' X Y := by ext p; simp [toE_apply]
  map_smul' c X := by ext p; simp [toE_apply]

lemma frob_tsum_le {n : ℕ} {f : ℕ → RealMatrix n n} (hf : Summable f) (b : ℕ → ℝ)
    (hb : Summable b) (hfb : ∀ k, frobeniusNorm (f k) ≤ b k) :
    frobeniusNorm (∑' k, f k) ≤ ∑' k, b k := by
  have e : toE (∑' k, f k) = ∑' k, toE (f k) :=
    ((hf.hasSum.map (toEL (n := n)) (LinearMap.continuous_of_finiteDimensional _)).tsum_eq).symm
  have hfb' : ∀ k, ‖toE (f k)‖ ≤ b k := fun k => by rw [← frob_toE]; exact hfb k
  have hs : Summable (fun k => ‖toE (f k)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hfb' hb
  rw [frob_toE, e]
  exact le_trans (norm_tsum_le_tsum_norm hs) (hasSum_le hfb' hs.hasSum hb.hasSum)

/-- the Neumann remainder `∑_{k ≥ 1} A^k Z` is small -/
lemma rem_bound {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)} {SV : SVD L0 r}
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (h : PTOpNormLe Ω SV σ) (Z : RealMatrix n n) :
    frobeniusNorm ((∑' k, (Alin Ω SV)^[k] Z) - Z) ≤ σ / (1 - σ) * frobeniusNorm Z := by
  have hs := iter_summable hσ0 hσ1 h Z
  rw [hs.tsum_eq_zero_add]
  simp only [Function.iterate_zero, id_eq, add_sub_cancel_left]
  have hg := summable_geometric_of_lt_one hσ0 hσ1
  have hb : Summable (fun k : ℕ => σ * σ ^ k * frobeniusNorm Z) := (hg.mul_left σ).mul_right _
  refine le_trans (frob_tsum_le ((summable_nat_add_iff 1).mpr hs) _ hb (fun k => ?_)) ?_
  · have := Alin_iter_bound hσ0 h Z (k + 1)
    rw [pow_succ'] at this
    exact this
  · rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hσ0 hσ1, div_eq_mul_inv]

end RPCA29

namespace RPCA29
open RobustPCA.Recovery
open scoped BigOperators Classical

noncomputable def outerM {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : RealMatrix n n :=
  fun i j => x i * y j

noncomputable def remM {n r : ℕ} {L0 : RealMatrix n n} (Ω : Finset (Fin n × Fin n)) (SV : SVD L0 r)
    (Z : RealMatrix n n) : RealMatrix n n :=
  (∑' k, (Alin Ω SV)^[k] Z) - Z

lemma bil_inner {n : ℕ} (A : RealMatrix n n) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) y) =
      matrixInner (outerM x y) A := by
  rw [bil_eq]
  unfold matrixInner outerM
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma frob_outer {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    frobeniusNorm (outerM x y) ≤ 1 := by
  unfold frobeniusNorm frobeniusNormSq outerM
  rw [Real.sqrt_le_one]
  have := vsq x y hx hy
  rw [Fintype.sum_prod_type] at this
  exact this

lemma pair_sum {n : ℕ} (M E : RealMatrix n n) :
    matrixInner M E = ∑ p : Fin n × Fin n, M p.1 p.2 * E p.1 p.2 := by
  unfold matrixInner
  exact (Fintype.sum_prod_type (f := fun p : Fin n × Fin n => M p.1 p.2 * E p.1 p.2)).symm

lemma sumsq_le {n : ℕ} (M : RealMatrix n n) (Ω : Finset (Fin n × Fin n)) :
    ∑ p ∈ Ω, M p.1 p.2 ^ 2 ≤ frobeniusNorm M ^ 2 := by
  have h0 : 0 ≤ frobeniusNormSq M := by unfold frobeniusNormSq; positivity
  unfold frobeniusNorm
  rw [Real.sq_sqrt h0]
  unfold frobeniusNormSq
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n => M p.1 p.2 ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Ω) (fun _ _ _ => sq_nonneg _)

lemma inner_sub_r {n : ℕ} (Z A B : RealMatrix n n) :
    matrixInner Z (A - B) = matrixInner Z A - matrixInner Z B :=
  (pairL Z).map_sub A B

lemma inner_sub_l {n : ℕ} (Z A B : RealMatrix n n) :
    matrixInner (A - B) Z = matrixInner A Z - matrixInner B Z := by
  rw [inner_comm', inner_sub_r, inner_comm' Z, inner_comm' Z]

/-- E3: on a good support, the Neumann remainder applied to the random signs has small norm -/
lemma E3 {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Ω : Finset (Fin n × Fin n))
    (hn : 0 < n) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2000) (h : PTOpNormLe Ω SV s) :
    RSF (fun E : RealMatrix n n => ¬ MatrixCompletion.spectralNorm
      ((∑' k, (Alin Ω SV)^[k] E) - E) ≤ Real.sqrt n / 16) Ω ≤ (n : ℝ) ^ (-11 : ℤ) := by
  have hs1 : s < 1 := by linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨N, hN1, hcov, hcard⟩ := net_exists hn
  have himp : ∀ P ⊆ Ω, (fun E : RealMatrix n n => ¬ MatrixCompletion.spectralNorm
      ((∑' k, (Alin Ω SV)^[k] E) - E) ≤ Real.sqrt n / 16) (signPattern Ω P) →
      ∃ i : N × N, (fun E : RealMatrix n n => Real.sqrt n / 32 ≤
        ∑ p : Fin n × Fin n, remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
          (i.2 : EuclideanSpace ℝ (Fin n))) p.1 p.2 * E p.1 p.2) (signPattern Ω P) := by
    intro P _ hP
    by_contra hno
    push Not at hno
    apply hP
    have hb := opNorm_le_net (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      ((∑' k, (Alin Ω SV)^[k] (signPattern Ω P)) - signPattern Ω P))) N hN1 hcov
      (Real.sqrt n / 32) (fun x hx y hy => by
        have h2 := hno ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
        rw [bil_inner, inner_sub_r, dual_tsum hs0 hs1 h, ← inner_sub_l, pair_sum]
        exact h2.le)
    unfold MatrixCompletion.spectralNorm
    linarith
  have htail : ∀ i : N × N, RSF (fun E : RealMatrix n n => Real.sqrt n / 32 ≤
        ∑ p : Fin n × Fin n, remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
          (i.2 : EuclideanSpace ℝ (Fin n))) p.1 p.2 * E p.1 p.2) Ω ≤
        Real.exp (-(25 * n)) := by
    intro i
    have hM : frobeniusNorm (remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
        (i.2 : EuclideanSpace ℝ (Fin n)))) ≤ s / (1 - s) * frobeniusNorm
        (outerM (i.1 : EuclideanSpace ℝ (Fin n)) (i.2 : EuclideanSpace ℝ (Fin n))) :=
      rem_bound hs0 hs1 h _
    have hO := frob_outer _ _ (hN1 _ i.1.2) (hN1 _ i.2.2)
    have hO0 : 0 ≤ frobeniusNorm (outerM (i.1 : EuclideanSpace ℝ (Fin n))
        (i.2 : EuclideanSpace ℝ (Fin n))) := Real.sqrt_nonneg _
    have hq0 : 0 ≤ s / (1 - s) := div_nonneg hs0 (by linarith)
    have hq : s / (1 - s) ≤ 2 * s := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hM2 : frobeniusNorm (remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
        (i.2 : EuclideanSpace ℝ (Fin n)))) ≤ 2 * s := by
      have := mul_le_mul_of_nonneg_left hO hq0
      linarith
    have hMn : 0 ≤ frobeniusNorm (remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
        (i.2 : EuclideanSpace ℝ (Fin n)))) := Real.sqrt_nonneg _
    have hF := sumsq_le (remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
        (i.2 : EuclideanSpace ℝ (Fin n)))) Ω
    have hF2 : ∑ p ∈ Ω, remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
        (i.2 : EuclideanSpace ℝ (Fin n))) p.1 p.2 ^ 2 ≤ 1 / 1000000 := by
      have h1 : frobeniusNorm (remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
          (i.2 : EuclideanSpace ℝ (Fin n)))) ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ hMn hM2 2
      have h2 : (2 * s) ^ 2 ≤ (2 * (1 / 2000)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      norm_num at h2
      linarith
    refine le_trans (sign_hoeff Ω (fun p => remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
        (i.2 : EuclideanSpace ℝ (Fin n))) p.1 p.2) (1600 * Real.sqrt n) _ (by positivity)) ?_
    apply Real.exp_le_exp.mpr
    beta_reduce
    have e1 : 1600 * Real.sqrt n * (Real.sqrt n / 32) = 50 * n := by
      rw [show 1600 * Real.sqrt n * (Real.sqrt n / 32) = 50 * (Real.sqrt n * Real.sqrt n) by ring,
        Real.mul_self_sqrt hnR.le]
    have e2 : (1600 * Real.sqrt n) ^ 2 = 1600 ^ 2 * n := by
      rw [mul_pow, Real.sq_sqrt hnR.le]
    rw [neg_mul, e1, e2]
    have := mul_le_mul_of_nonneg_left hF2 (by positivity : (0 : ℝ) ≤ 1600 ^ 2 * n / 2)
    linarith
  calc _ ≤ ∑ i : N × N, RSF (fun E : RealMatrix n n => Real.sqrt n / 32 ≤
        ∑ p : Fin n × Fin n, remM Ω SV (outerM (i.1 : EuclideanSpace ℝ (Fin n))
          (i.2 : EuclideanSpace ℝ (Fin n))) p.1 p.2 * E p.1 p.2) Ω := RSF_union Ω _ _ himp
    _ ≤ ∑ _i : N × N, Real.exp (-(25 * n)) := Finset.sum_le_sum (fun i _ => htail i)
    _ = (N.card : ℝ) ^ 2 * Real.exp (-(25 * n)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (n : ℝ) ^ (-11 : ℤ) :=
        g32_count n N.card (by positivity) (by positivity)
          (by rw [Nat.floor_natCast]; exact hcard) (by rw [Nat.floor_natCast])

end RPCA29
namespace RPCA29
open RobustPCA.Recovery
open scoped BigOperators Classical

/-! ## E2 tools (copied from scratch/decomp/38087c24/reduction.lean) -/

lemma normal_eq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    normalProjection SV X = (1 - PU SV) * X * (1 - PV SV) := by
  simp only [normalProjection, tangent_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one]
  abel

open scoped Matrix.Norms.L2Operator in
lemma proj_norm_le {n : ℕ} (P : RealMatrix n n) (hP : P * P = P)
    (hT : Matrix.transpose P = P) : ‖(1 - P : RealMatrix n n)‖ ≤ 1 := by
  have hQ : (1 - P : RealMatrix n n) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hP]
    abel
  have hH : Matrix.conjTranspose (1 - P : RealMatrix n n) = 1 - P := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_one, hT]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (1 - P : RealMatrix n n)
  rw [hH, hQ] at h
  have h0 : 0 ≤ ‖(1 - P : RealMatrix n n)‖ := norm_nonneg _
  nlinarith

open scoped Matrix.Norms.L2Operator in
lemma spectral_normal_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    MatrixCompletion.spectralNorm (normalProjection SV X) ≤ MatrixCompletion.spectralNorm X := by
  rw [spec_eq, spec_eq, normal_eq]
  have hU := proj_norm_le (PU SV) (PU_idem SV) (projM_transpose SV.u)
  have hV := proj_norm_le (PV SV) (PV_idem SV) (projM_transpose SV.v)
  calc ‖(1 - PU SV) * X * (1 - PV SV)‖ ≤ ‖(1 - PU SV) * X‖ * ‖(1 - PV SV)‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(1 - PU SV)‖ * ‖X‖) * ‖(1 - PV SV)‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 := by
        apply mul_le_mul _ hV (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hU (norm_nonneg _)
    _ = ‖X‖ := by ring


lemma entrySup_le {n : ℕ} (A : RealMatrix n n) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i j, |A i j| ≤ b) : entrySupNorm A ≤ b := by
  unfold entrySupNorm
  exact Real.iSup_le (fun i => Real.iSup_le (fun j => h i j) hb) hb

lemma inner_coord {n : ℕ} (a b : Fin n) (M : RealMatrix n n) :
    matrixInner (coordinateMatrix a b) M = M a b := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero; intro j _; simp [hi]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma inner_coord' {n : ℕ} (a b : Fin n) (M : RealMatrix n n) :
    ∑ i, ∑ j, M i j * coordinateMatrix a b i j = M a b := by
  rw [← inner_coord a b M]
  unfold matrixInner
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))

/-- `P_T e_ab`, the coefficient matrix of the entry `(a, b)` of `P_T`. -/
noncomputable def Ecoef {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b : Fin n) :
    RealMatrix n n :=
  tangentProjection SV (coordinateMatrix a b)

lemma tangent_entry {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Y : RealMatrix n n)
    (a b : Fin n) : tangentProjection SV Y a b = ∑ i, ∑ j, Ecoef SV a b i j * Y i j := by
  rw [← inner_coord a b (tangentProjection SV Y), ← inner_tangent]
  rfl

lemma Ecoef_sq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b : Fin n) :
    ∑ i, ∑ j, Ecoef SV a b i j ^ 2 = Ecoef SV a b a b := by
  have h := tangent_entry SV (Ecoef SV a b) a b
  rw [Ecoef, tangent_idem] at h
  rw [Ecoef, h]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma Ecoef_self {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b i j : Fin n) :
    Ecoef SV a b i j = ∑ x, ∑ y, Ecoef SV i j x y * Ecoef SV a b x y := by
  have h := tangent_entry SV (Ecoef SV a b) i j
  rw [Ecoef, tangent_idem] at h
  rw [Ecoef, h]

lemma Ecoef_diag {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a b : Fin n) :
    Ecoef SV a b a b = PU SV a a + PV SV b b - PU SV a a * PV SV b b := by
  rw [Ecoef, tangent_eq]
  simp [Matrix.mul_apply, coordinateMatrix, Matrix.sub_apply, Matrix.add_apply, ite_and]

lemma PU_diag {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a : Fin n) :
    PU SV a a = ∑ k, SV.u k a ^ 2 := by
  unfold PU projM
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma PV_diag {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (b : Fin n) :
    PV SV b b = ∑ k, SV.v k b ^ 2 := by
  unfold PV projM
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma Ecoef_sq_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ)
    (hinc : Incoherent SV μ) (a b : Fin n) :
    ∑ i, ∑ j, Ecoef SV a b i j ^ 2 ≤ 2 * μ * r / n := by
  rw [Ecoef_sq, Ecoef_diag, PU_diag, PV_diag]
  have h1 := hinc.1 a
  have h2 := hinc.2.1 b
  have h3 : 0 ≤ ∑ k, SV.u k a ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h4 : 0 ≤ ∑ k, SV.v k b ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h5 := mul_nonneg h3 h4
  have e : 2 * μ * r / n = μ * r / n + μ * r / n := by ring
  rw [e]
  linarith

lemma bep_false {N : ℕ} (p : ℝ) (F : Finset (Fin N × Fin N) → Prop) (h : ∀ Ω, ¬ F Ω) :
    bernoulliEventProb p F = 0 := by
  unfold bernoulliEventProb
  exact Finset.sum_eq_zero (fun Ω _ => if_neg (h Ω))


lemma bep_not {N : ℕ} (p : ℝ) (P : Finset (Fin N × Fin N) → Prop) :
    bernoulliEventProb p (fun B => ¬ P B) = 1 - bernoulliEventProb p P := by
  unfold bernoulliEventProb
  rw [← bw_sum_one (N := N) p, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  by_cases h : P B
  · rw [if_neg (not_not.mpr h), if_pos h]; ring
  · rw [if_pos h, if_neg h]; ring

lemma bep_not_and3 {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q R : Finset (Fin N × Fin N) → Prop) :
    bernoulliEventProb p (fun B => ¬ (P B ∧ Q B ∧ R B)) ≤
      bernoulliEventProb p (fun B => ¬ P B) + bernoulliEventProb p (fun B => ¬ Q B) +
        bernoulliEventProb p (fun B => ¬ R B) := by
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun B _ => ?_)
  have hw := bw_nonneg hp0 hp1 B
  split_ifs <;> first | linarith | (exfalso; tauto)

lemma bep_mono {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q : Finset (Fin N × Fin N) → Prop) (h : ∀ B, P B → Q B) :
    bernoulliEventProb p P ≤ bernoulliEventProb p Q := by
  unfold bernoulliEventProb
  refine Finset.sum_le_sum (fun B _ => ?_)
  have hw := bw_nonneg hp0 hp1 B
  split_ifs with h1 h2 <;> first | linarith | (exfalso; exact h2 (h B h1))

lemma bep_eq_sum {N : ℕ} (p : ℝ) (P : Finset (Fin N × Fin N) → Prop) :
    bernoulliEventProb p P =
      ∑ B : Finset (Fin N × Fin N), bernoulliObservationWeight p B * (if P B then 1 else 0) := by
  unfold bernoulliEventProb
  refine Finset.sum_congr rfl (fun B _ => ?_)
  split_ifs <;> simp

theorem ctamp_prod_ins_out {α : Type*} [DecidableEq α] (p q : ℝ) {s t : Finset α} {x : α}
    (hx : x ∉ s) (ht : t ⊆ s) :
    (∏ y ∈ insert x s, if y ∈ t then p else q) = q * ∏ y ∈ s, if y ∈ t then p else q := by
  rw [Finset.prod_insert hx]
  have : x ∉ t := fun h => hx (ht h)
  simp [this]

theorem ctamp_prod_ins_in {α : Type*} [DecidableEq α] (p q : ℝ) {s t : Finset α} {x : α}
    (hx : x ∉ s) :
    (∏ y ∈ insert x s, if y ∈ insert x t then p else q) = p * ∏ y ∈ s, if y ∈ t then p else q := by
  rw [Finset.prod_insert hx]
  simp only [Finset.mem_insert, true_or, if_true]
  congr 1
  refine Finset.prod_congr rfl (fun y hy => ?_)
  have hyx : y ≠ x := fun h => hx (h ▸ hy)
  simp [hyx]

theorem ctamp_mass {α : Type*} [DecidableEq α] (p : ℝ) (s : Finset α) :
    (∑ t ∈ s.powerset, ∏ y ∈ s, if y ∈ t then p else 1 - p) = 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_powerset_insert hx]
    have h1 : (∑ t ∈ s.powerset, ∏ y ∈ insert x s, if y ∈ t then p else 1 - p)
        = (1 - p) * ∑ t ∈ s.powerset, ∏ y ∈ s, if y ∈ t then p else 1 - p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      exact ctamp_prod_ins_out p (1 - p) hx (Finset.mem_powerset.mp ht)
    have h2 : (∑ t ∈ s.powerset, ∏ y ∈ insert x s, if y ∈ insert x t then p else 1 - p)
        = p * ∑ t ∈ s.powerset, ∏ y ∈ s, if y ∈ t then p else 1 - p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      exact ctamp_prod_ins_in p (1 - p) hx
    rw [h1, h2, ih]; ring

theorem ctamp_coupling {α : Type*} [DecidableEq α] (a b : ℝ) (s : Finset α) :
    ∀ f : Finset α → ℝ,
    (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
      ((∏ y ∈ s, if y ∈ t₁ then a else 1 - a) * (∏ y ∈ s, if y ∈ t₂ then b else 1 - b)) *
        f (t₁ ∪ t₂))
      = ∑ t ∈ s.powerset,
          (∏ y ∈ s, if y ∈ t then (a + b - a * b) else 1 - (a + b - a * b)) * f t := by
  induction s using Finset.induction_on with
  | empty => intro f; simp
  | insert x s hx ih =>
    intro f
    set A := ∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
      ((∏ y ∈ s, if y ∈ t₁ then a else 1 - a) * (∏ y ∈ s, if y ∈ t₂ then b else 1 - b)) *
        f (t₁ ∪ t₂) with hA
    set B := ∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
      ((∏ y ∈ s, if y ∈ t₁ then a else 1 - a) * (∏ y ∈ s, if y ∈ t₂ then b else 1 - b)) *
        f (insert x (t₁ ∪ t₂)) with hB
    have IA := ih f
    have IB := ih (fun t => f (insert x t))
    rw [← hA] at IA
    rw [← hB] at IB
    simp only [Finset.sum_powerset_insert hx, Finset.sum_add_distrib]
    have h1 : (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
        ((∏ y ∈ insert x s, if y ∈ t₁ then a else 1 - a) *
          (∏ y ∈ insert x s, if y ∈ t₂ then b else 1 - b)) * f (t₁ ∪ t₂))
        = (1 - a) * (1 - b) * A := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₁ h₁ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₂ h₂ => ?_)
      rw [ctamp_prod_ins_out a (1 - a) hx (Finset.mem_powerset.mp h₁),
        ctamp_prod_ins_out b (1 - b) hx (Finset.mem_powerset.mp h₂)]
      ring
    have h2 : (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
        ((∏ y ∈ insert x s, if y ∈ t₁ then a else 1 - a) *
          (∏ y ∈ insert x s, if y ∈ insert x t₂ then b else 1 - b)) * f (t₁ ∪ insert x t₂))
        = (1 - a) * b * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₁ h₁ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₂ _ => ?_)
      rw [ctamp_prod_ins_out a (1 - a) hx (Finset.mem_powerset.mp h₁),
        ctamp_prod_ins_in b (1 - b) hx, Finset.union_insert]
      ring
    have h3 : (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
        ((∏ y ∈ insert x s, if y ∈ insert x t₁ then a else 1 - a) *
          (∏ y ∈ insert x s, if y ∈ t₂ then b else 1 - b)) * f (insert x t₁ ∪ t₂))
        = a * (1 - b) * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₁ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₂ h₂ => ?_)
      rw [ctamp_prod_ins_in a (1 - a) hx,
        ctamp_prod_ins_out b (1 - b) hx (Finset.mem_powerset.mp h₂), Finset.insert_union]
      ring
    have h4 : (∑ t₁ ∈ s.powerset, ∑ t₂ ∈ s.powerset,
        ((∏ y ∈ insert x s, if y ∈ insert x t₁ then a else 1 - a) *
          (∏ y ∈ insert x s, if y ∈ insert x t₂ then b else 1 - b)) *
            f (insert x t₁ ∪ insert x t₂))
        = a * b * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₁ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t₂ _ => ?_)
      rw [ctamp_prod_ins_in a (1 - a) hx, ctamp_prod_ins_in b (1 - b) hx,
        Finset.insert_union, Finset.union_insert, Finset.insert_idem]
      ring
    have r1 : (∑ t ∈ s.powerset,
        (∏ y ∈ insert x s, if y ∈ t then (a + b - a * b) else 1 - (a + b - a * b)) * f t)
        = (1 - (a + b - a * b)) * ∑ t ∈ s.powerset,
          (∏ y ∈ s, if y ∈ t then (a + b - a * b) else 1 - (a + b - a * b)) * f t := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [ctamp_prod_ins_out _ _ hx (Finset.mem_powerset.mp ht)]
      ring
    have r2 : (∑ t ∈ s.powerset,
        (∏ y ∈ insert x s, if y ∈ insert x t then (a + b - a * b) else 1 - (a + b - a * b)) *
          f (insert x t))
        = (a + b - a * b) * ∑ t ∈ s.powerset,
          (∏ y ∈ s, if y ∈ t then (a + b - a * b) else 1 - (a + b - a * b)) * f (insert x t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [ctamp_prod_ins_in _ _ hx]
      ring
    rw [h1, h2, h3, h4, r1, r2, ← IA, ← IB]
    ring

theorem ctamp_weight_eq {n₁ n₂ : ℕ} (p : ℝ) (Ω : Finset (Fin n₁ × Fin n₂)) :
    bernoulliObservationWeight p Ω =
      ∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ Ω then p else 1 - p := by
  unfold bernoulliObservationWeight
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 2
  · congr 1; ext y; simp
  · rw [Finset.filter_not, Finset.card_sdiff]
    simp [Finset.card_univ]

theorem ctamp_eventProb_eq {n₁ n₂ : ℕ} (p : ℝ) (E : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p E =
      ∑ t ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then p else 1 - p) *
          (if E t then 1 else 0) := by
  unfold bernoulliEventProb
  rw [Finset.powerset_univ]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [ctamp_weight_eq]
  split_ifs <;> simp

theorem ctamp_compl' {n₁ n₂ : ℕ} (p : ℝ) (E F : Finset (Fin n₁ × Fin n₂) → Prop)
    (hF : ∀ t, F t ↔ ¬ E t) :
    bernoulliEventProb p F = 1 - bernoulliEventProb p E := by
  rw [ctamp_eventProb_eq, ctamp_eventProb_eq]
  have hm := ctamp_mass p (Finset.univ : Finset (Fin n₁ × Fin n₂))
  have key : (∑ t ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then p else 1 - p) *
          (if F t then (1 : ℝ) else 0)) +
      (∑ t ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then p else 1 - p) *
          (if E t then (1 : ℝ) else 0)) =
      ∑ t ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t then p else 1 - p) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h : E t
    · have : ¬ F t := fun h' => (hF t).mp h' h
      simp [h, this]
    · have : F t := (hF t).mpr h
      simp [h, this]
  linarith [key, hm]

theorem ctamp_compl {n₁ n₂ : ℕ} (p : ℝ) (E : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p (fun Ω => ¬ E Ω) = 1 - bernoulliEventProb p E :=
  ctamp_compl' p E (fun Ω => ¬ E Ω) (fun _ => Iff.rfl)

theorem ctamp_nonneg {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Fin n₁ × Fin n₂) → Prop) : 0 ≤ bernoulliEventProb p E := by
  rw [ctamp_eventProb_eq]
  refine Finset.sum_nonneg (fun t _ => mul_nonneg ?_ ?_)
  · exact Finset.prod_nonneg (fun y _ => by split_ifs <;> linarith)
  · split_ifs <;> norm_num

theorem ctamp_fail_mul {n₁ n₂ : ℕ} (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (F : Finset (Fin n₁ × Fin n₂) → Prop)
    (hF : ∀ Ω Ω' : Finset (Fin n₁ × Fin n₂), Ω ⊆ Ω' → F Ω' → F Ω) :
    bernoulliEventProb (a + b - a * b) F ≤ bernoulliEventProb a F * bernoulliEventProb b F := by
  rw [ctamp_eventProb_eq, ctamp_eventProb_eq, ctamp_eventProb_eq, Finset.sum_mul_sum,
    ← ctamp_coupling a b Finset.univ (fun t => if F t then 1 else 0)]
  refine Finset.sum_le_sum (fun t₁ _ => Finset.sum_le_sum (fun t₂ _ => ?_))
  have w1 : 0 ≤ ∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then a else 1 - a :=
    Finset.prod_nonneg (fun y _ => by split_ifs <;> linarith)
  have w2 : 0 ≤ ∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₂ then b else 1 - b :=
    Finset.prod_nonneg (fun y _ => by split_ifs <;> linarith)
  have key : (if F (t₁ ∪ t₂) then (1 : ℝ) else 0) ≤
      (if F t₁ then 1 else 0) * (if F t₂ then 1 else 0) := by
    by_cases h : F (t₁ ∪ t₂)
    · have h1 : F t₁ := hF _ _ Finset.subset_union_left h
      have h2 : F t₂ := hF _ _ Finset.subset_union_right h
      simp [h, h1, h2]
    · simp only [h, if_false]
      split_ifs <;> norm_num
  calc ((∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then a else 1 - a) *
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₂ then b else 1 - b)) *
        (if F (t₁ ∪ t₂) then (1 : ℝ) else 0)
      ≤ ((∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₁ then a else 1 - a) *
        (∏ y ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)), if y ∈ t₂ then b else 1 - b)) *
        ((if F t₁ then 1 else 0) * (if F t₂ then 1 else 0)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg w1 w2)
    _ = _ := by ring

theorem ctamp_fail_antitone {n₁ n₂ : ℕ} (q p : ℝ) (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1)
    (E : Finset (Fin n₁ × Fin n₂) → Prop)
    (hE : ∀ Ω Ω' : Finset (Fin n₁ × Fin n₂), Ω ⊆ Ω' → E Ω → E Ω') :
    bernoulliEventProb p (fun Ω => ¬ E Ω) ≤ bernoulliEventProb q (fun Ω => ¬ E Ω) := by
  rcases eq_or_lt_of_le (le_trans hqp hp1) with hq1 | hq1
  · have : p = q := by linarith
    rw [this]
  · set s := (p - q) / (1 - q) with hs
    have h1q : 0 < 1 - q := by linarith
    have hs0 : 0 ≤ s := div_nonneg (by linarith) h1q.le
    have hs1 : s ≤ 1 := by rw [hs, div_le_one h1q]; linarith
    have hps : q + s - q * s = p := by
      rw [hs]; field_simp; ring
    have hm := ctamp_fail_mul q s hq0 (le_trans hqp hp1) hs0 hs1 (fun Ω => ¬ E Ω)
      (fun Ω Ω' h hn hE' => hn (hE Ω Ω' h hE'))
    rw [hps] at hm
    have f0 : 0 ≤ bernoulliEventProb q (fun Ω => ¬ E Ω) := ctamp_nonneg q hq0 (le_trans hqp hp1) _
    have f1 : bernoulliEventProb s (fun Ω => ¬ E Ω) ≤ 1 := by
      rw [ctamp_compl]; have := ctamp_nonneg s hs0 hs1 E; linarith
    calc bernoulliEventProb p (fun Ω => ¬ E Ω)
        ≤ bernoulliEventProb q (fun Ω => ¬ E Ω) * bernoulliEventProb s (fun Ω => ¬ E Ω) := hm
      _ ≤ bernoulliEventProb q (fun Ω => ¬ E Ω) * 1 := mul_le_mul_of_nonneg_left f1 f0
      _ = _ := mul_one _

def T41 : Prop :=
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        MatrixCompletion.A0 S μ₀ → MatrixCompletion.A1 S μ₁ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingConcentration Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ((1 : ℝ) / 2)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β)

lemma frobSq_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ frobeniusNormSq X := by
  unfold frobeniusNormSq; positivity

lemma frob_nonneg' {n : ℕ} (X : RealMatrix n n) : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _

lemma frob_sq {n : ℕ} (X : RealMatrix n n) : frobeniusNorm X ^ 2 = frobeniusNormSq X :=
  Real.sq_sqrt (frobSq_nonneg X)

lemma frobSq_eq_inner {n : ℕ} (X : RealMatrix n n) : frobeniusNormSq X = matrixInner X X := by
  simp only [frobeniusNormSq, matrixInner, sq]

lemma inner_abs_le {n : ℕ} (X Y : RealMatrix n n) :
    |matrixInner X Y| ≤ frobeniusNorm X * frobeniusNorm Y := by
  unfold frobeniusNorm
  rw [← Real.sqrt_mul (frobSq_nonneg X)]
  apply Real.abs_le_sqrt
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
  simp only [Fintype.sum_prod_type] at h
  simpa only [matrixInner, frobeniusNormSq] using h

lemma inner_sub_smul {n : ℕ} (X A B : RealMatrix n n) (c : ℝ) :
    matrixInner X (A - c • B) = matrixInner X A - c * matrixInner X B := by
  unfold matrixInner
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring

lemma inner_T_right {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n)
    (hX : tangentProjection SV X = X) :
    matrixInner X (tangentProjection SV Y) = matrixInner X Y := by
  rw [← inner_tangent SV, hX]

lemma frob_T_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    frobeniusNorm (tangentProjection SV X) ≤ frobeniusNorm X := by
  have h1 : frobeniusNorm (tangentProjection SV X) ^ 2 =
      matrixInner X (tangentProjection SV X) := by
    rw [frob_sq, frobSq_eq_inner, inner_tangent SV, tangent_idem]
  have h2 := le_trans (le_abs_self _) (inner_abs_le X (tangentProjection SV X))
  have h3 := frob_nonneg' (tangentProjection SV X)
  have h4 := frob_nonneg' X
  nlinarith

lemma inner_samp_mono {n : ℕ} {Ω Ω' : Finset (Fin n × Fin n)} (h : Ω ⊆ Ω') (X : RealMatrix n n) :
    matrixInner X (samplingProjection Ω X) ≤ matrixInner X (samplingProjection Ω' X) := by
  unfold matrixInner samplingProjection
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  by_cases h1 : (i, j) ∈ Ω
  · rw [if_pos h1, if_pos (h h1)]
  · rw [if_neg h1, mul_zero]
    split_ifs
    · exact mul_self_nonneg _
    · simp

def LoEv {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (a : ℝ) (Ω : Finset (Fin n × Fin n)) :
    Prop :=
  ∀ X : RealMatrix n n, tangentProjection SV X = X →
    a * frobeniusNormSq X ≤ matrixInner X (samplingProjection Ω X)

def UpEv {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (b : ℝ) (Ω : Finset (Fin n × Fin n)) :
    Prop :=
  ∀ X : RealMatrix n n, tangentProjection SV X = X →
    matrixInner X (samplingProjection Ω X) ≤ b * frobeniusNormSq X

lemma tsc_bounds {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Ω : Finset (Fin n × Fin n))
    (p : ℝ) (hp : 0 ≤ p) (h : TangentSamplingConcentration Ω SV p ((1 : ℝ) / 2)) :
    LoEv SV (p / 2) Ω ∧ UpEv SV (3 * p / 2) Ω := by
  have key : ∀ X : RealMatrix n n, tangentProjection SV X = X →
      |matrixInner X (samplingProjection Ω X) - p * frobeniusNormSq X| ≤
        p / 2 * frobeniusNormSq X := by
    intro X hX
    have h1 := h X hX
    have hcs := inner_abs_le X (tangentProjection SV (samplingProjection Ω X) - p • X)
    have e : matrixInner X (tangentProjection SV (samplingProjection Ω X) - p • X) =
        matrixInner X (samplingProjection Ω X) - p * frobeniusNormSq X := by
      rw [inner_sub_smul, inner_T_right SV _ _ hX, frobSq_eq_inner]
    rw [e] at hcs
    have hf := frob_nonneg' X
    have h2 : frobeniusNorm X *
        frobeniusNorm (tangentProjection SV (samplingProjection Ω X) - p • X) ≤
        frobeniusNorm X * (1 / 2 * p * frobeniusNorm X) := mul_le_mul_of_nonneg_left h1 hf
    have h3 : frobeniusNorm X * (1 / 2 * p * frobeniusNorm X) = p / 2 * frobeniusNormSq X := by
      rw [← frob_sq]; ring
    linarith
  refine ⟨fun X hX => ?_, fun X hX => ?_⟩
  · have := (abs_le.mp (key X hX)).1; linarith
  · have := (abs_le.mp (key X hX)).2; linarith

lemma bep_not_and2 {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q : Finset (Fin N × Fin N) → Prop) :
    bernoulliEventProb p (fun B => ¬ (P B ∧ Q B)) ≤
      bernoulliEventProb p (fun B => ¬ P B) + bernoulliEventProb p (fun B => ¬ Q B) := by
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun B _ => ?_)
  have hw := bw_nonneg hp0 hp1 B
  split_ifs <;> first | linarith | (exfalso; tauto)

lemma mu_ge_one {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ) (hn : 0 < n) (hr : 0 < r)
    (hinc : Incoherent SV μ) : 1 ≤ μ := by
  have hsum : ∑ i : Fin n, ∑ k, (SV.u k i) ^ 2 = r := by
    simp only [sq]
    rw [Finset.sum_comm]
    simp [SV.u_orthonormal]
  have hle : ∑ i : Fin n, ∑ k, (SV.u k i) ^ 2 ≤ ∑ _i : Fin n, μ * r / n :=
    Finset.sum_le_sum (fun i _ => hinc.1 i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] at hle
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have e : (n : ℝ) * (μ * r / n) = μ * r := by field_simp
  rw [e] at hle
  by_contra hc
  push_neg at hc
  nlinarith

lemma A0_of_inc {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ) (hn : 0 < n) (hr : 0 < r)
    (hinc : Incoherent SV μ) : MatrixCompletion.A0 SV μ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have key : ∀ (u : Fin r → Fin n → ℝ), (∀ i, ∑ k, (u k i) ^ 2 ≤ μ * r / n) →
      coherence n r u ≤ μ := by
    intro u hu
    unfold coherence
    have h1 : (⨆ i : Fin n, ∑ k, (u k i) ^ 2) ≤ μ * r / n := ciSup_le hu
    calc (n : ℝ) / r * ⨆ i : Fin n, ∑ k, (u k i) ^ 2 ≤ (n : ℝ) / r * (μ * r / n) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = μ := by field_simp
  exact ⟨key SV.u hinc.1, key SV.v hinc.2.1⟩

lemma A1_of_inc {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ) (hμ : 1 ≤ μ)
    (hinc : Incoherent SV μ) : MatrixCompletion.A1 SV μ := by
  intro i j
  have h := hinc.2.2 i j
  have e : Real.sqrt (μ * r / ((n : ℝ) * n)) = Real.sqrt μ * Real.sqrt ((r : ℝ) / ((n : ℝ) * n)) := by
    rw [← Real.sqrt_mul (by linarith)]; congr 1; ring
  have hs : Real.sqrt μ ≤ μ := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  rw [e] at h
  exact le_trans h (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))

lemma rpow_eq_zpow11 (x : ℝ) : Real.rpow x (-11) = x ^ (-11 : ℤ) := by
  rw [Real.rpow_eq_pow, show (-11 : ℝ) = ((-11 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]



/-! ## E2: the support condition `‖𝒫_Ω 𝒫_T‖ ≤ 1/2000` w.h.p., from Candes-Recht Thm 4.1 -/

lemma frob_samp_mono {n : ℕ} {Ω Ω' : Finset (Fin n × Fin n)} (h : Ω ⊆ Ω') (Y : RealMatrix n n) :
    frobeniusNorm (samplingProjection Ω Y) ≤ frobeniusNorm (samplingProjection Ω' Y) := by
  unfold frobeniusNorm frobeniusNormSq samplingProjection
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  by_cases h1 : (i, j) ∈ Ω
  · rw [if_pos h1, if_pos (h h1)]
  · rw [if_neg h1]
    split_ifs
    · nlinarith [sq_nonneg (Y i j)]
    · exact le_refl _

lemma frobSq_samp {n : ℕ} (Ω : Finset (Fin n × Fin n)) (Y : RealMatrix n n) :
    frobeniusNormSq (samplingProjection Ω Y) = matrixInner Y (samplingProjection Ω Y) := by
  unfold frobeniusNormSq matrixInner samplingProjection
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  split_ifs <;> ring

lemma up_to_PT {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Ω : Finset (Fin n × Fin n))
    (b s : ℝ) (hs : 0 ≤ s) (hbs : b ≤ s ^ 2) (h : UpEv SV b Ω) : PTOpNormLe Ω SV s := by
  intro X
  have hY : tangentProjection SV (tangentProjection SV X) = tangentProjection SV X :=
    tangent_idem SV X
  have h1 := h _ hY
  rw [← frobSq_samp, ← frob_sq, ← frob_sq] at h1
  have hYX := frob_T_le SV X
  have hY0 := frob_nonneg' (tangentProjection SV X)
  have hA0 := frob_nonneg' (samplingProjection Ω (tangentProjection SV X))
  have hX0 := frob_nonneg' X
  have h2 : b * frobeniusNorm (tangentProjection SV X) ^ 2 ≤ (s * frobeniusNorm X) ^ 2 := by
    have : frobeniusNorm (tangentProjection SV X) ^ 2 ≤ frobeniusNorm X ^ 2 := by nlinarith
    have hy2 : 0 ≤ frobeniusNorm (tangentProjection SV X) ^ 2 := by positivity
    calc b * frobeniusNorm (tangentProjection SV X) ^ 2
        ≤ s ^ 2 * frobeniusNorm (tangentProjection SV X) ^ 2 :=
          mul_le_mul_of_nonneg_right hbs hy2
      _ ≤ s ^ 2 * frobeniusNorm X ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = (s * frobeniusNorm X) ^ 2 := by ring
  have hB0 : 0 ≤ s * frobeniusNorm X := mul_nonneg hs hX0
  nlinarith [h1.trans h2]

theorem E2 (h41 : T41) : ∃ ρs0 ρr0 c0 : ℝ, 0 < ρs0 ∧ 0 < ρr0 ∧ 0 < c0 ∧
    ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ρ : ℝ),
      (4000 : ℝ) ≤ n → Incoherent SV μ → (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr0 * n →
      0 ≤ ρ → ρ ≤ ρs0 →
      bernoulliEventProb ρ (fun Ω => ¬ PTOpNormLe Ω SV (1 / 2000)) ≤
        c0 * (n : ℝ) ^ (-11 : ℤ) := by
  obtain ⟨C, c, hC, hc, H⟩ := h41
  refine ⟨1 / 12000000, 1 / (132000000 * C), c, by norm_num, by positivity, hc, ?_⟩
  intro n r L0 SV μ ρ hn0 hinc hrank hρ0 hρs
  have hnR : (0 : ℝ) < n := by linarith
  have hn : 0 < n := by exact_mod_cast hnR
  have hz : 0 ≤ (n : ℝ) ^ (-11 : ℤ) := zpow_nonneg hnR.le _
  have hρ1 : ρ ≤ 1 := by linarith
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hT : ∀ X : RealMatrix n n, tangentProjection SV X = 0 := by
      intro X; rw [tangent_eq]; ext i j; simp [PU, PV, projM, Matrix.mul_apply]
    have hall : ∀ Ω : Finset (Fin n × Fin n), PTOpNormLe Ω SV (1 / 2000) := by
      intro Ω X
      have e : samplingProjection Ω (tangentProjection SV X) = 0 := by
        rw [hT X]; ext i j; simp [samplingProjection]
      rw [e]
      have : frobeniusNorm (0 : RealMatrix n n) = 0 := by simp [frobeniusNorm, frobeniusNormSq]
      rw [this]; exact mul_nonneg (by norm_num) (frob_nonneg' X)
    rw [bep_false ρ _ (fun Ω hΩ => hΩ (hall Ω))]
    exact mul_nonneg hc.le hz
  have hμ := mu_ge_one SV μ hn hr hinc
  have hA0 := A0_of_inc SV μ hn hr hinc
  have hA1 := A1_of_inc SV μ hμ hinc
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnR]
    have := Real.exp_one_lt_d9; linarith
  set N : ℝ := (n : ℝ) * n with hN
  have hNpos : 0 < N := by positivity
  set K : ℝ := C * μ * n * r * Real.log n with hK
  have hKN : 11 * K ≤ N / 12000000 := by
    have hpos : 0 ≤ (r : ℝ) * μ * Real.log n :=
      mul_nonneg (mul_nonneg hrR.le (by linarith)) (by linarith)
    have h1 : (r : ℝ) * μ * Real.log n ≤ 1 / (132000000 * C) * n := by
      nlinarith [mul_le_mul_of_nonneg_left hlog1 hpos]
    have e : K = C * n * ((r : ℝ) * μ * Real.log n) := by rw [hK]; ring
    rw [e, hN]
    have hCn : 0 ≤ C * n := by positivity
    calc 11 * (C * n * ((r : ℝ) * μ * Real.log n))
        ≤ 11 * (C * n * (1 / (132000000 * C) * n)) := by gcongr
      _ = n * n / 12000000 := by field_simp; ring
  set x : ℝ := max (11 * K) (ρ * N) with hx
  have hx0 : 0 ≤ x := le_trans (mul_nonneg hρ0 hNpos.le) (le_max_right _ _)
  have hxN : x ≤ N / 12000000 := max_le hKN (by nlinarith)
  have hN1 : 1 ≤ N / 12000000 := by rw [hN]; nlinarith
  set m := ⌈x⌉₊ with hm
  have hmge : x ≤ m := Nat.le_ceil x
  have hmlt : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hmN : m ≤ n * n := by
    have h' : (m : ℝ) ≤ (n : ℝ) * n := by rw [← hN]; linarith
    exact_mod_cast h'
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (m : ℝ) / N := ⟨_, rfl⟩
  have hcast : (m : ℝ) / ((n : ℝ) * (n : ℝ)) = p := by rw [hp, hN]
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hNpos]; linarith
  have hρp : ρ ≤ p := by
    rw [hp, le_div_iff₀ hNpos]; linarith [le_max_right (11 * K) (ρ * N)]
  have hpsmall : 3 * p / 2 ≤ (1 / 2000 : ℝ) ^ 2 := by
    have : p ≤ 1 / 6000000 := by
      rw [hp, div_le_iff₀ hNpos]; linarith
    nlinarith
  have hmaxR : ((max n n : ℕ) : ℝ) = n := by rw [max_self]
  have hcond : (m : ℝ) ≥ C * μ * (↑(max n n)) * (r : ℝ) * (11 * Real.log (↑(max n n))) := by
    rw [hmaxR]
    have : C * μ * (n : ℝ) * r * (11 * Real.log n) = 11 * K := by rw [hK]; ring
    rw [this]; linarith [le_max_left (11 * K) (ρ * N)]
  have hz' : Real.rpow (↑(max n n) : ℝ) (-11) = (n : ℝ) ^ (-11 : ℤ) := by
    rw [hmaxR, rpow_eq_zpow11]
  have T := H C le_rfl 11 (by norm_num) n n r m L0 μ μ SV hn hn hr hmN hμ hμ hA0 hA1 hcond
  rw [hz', hcast] at T
  have hPp : bernoulliEventProb p (fun Ω => PTOpNormLe Ω SV (1 / 2000)) ≥
      1 - c * (n : ℝ) ^ (-11 : ℤ) :=
    le_trans T (bep_mono (N := n) hp0 hp1
      (fun Omega => TangentSamplingConcentration Omega SV p ((1 : ℝ) / 2))
      (fun Ω => PTOpNormLe Ω SV (1 / 2000))
      (fun B hB => up_to_PT SV B _ _ (by norm_num) hpsmall (tsc_bounds SV B p hp0 hB).2))
  have hGmono : ∀ Ω Ω' : Finset (Fin n × Fin n), Ω ⊆ Ω' →
      (¬ PTOpNormLe Ω SV (1 / 2000)) → ¬ PTOpNormLe Ω' SV (1 / 2000) :=
    fun Ω Ω' h hG hG' => hG (fun X => le_trans (frob_samp_mono h _) (hG' X))
  have FU := ctamp_fail_antitone ρ p hρ0 hρp hp1
    (fun Ω => ¬ PTOpNormLe Ω SV (1 / 2000)) hGmono
  have n1 := bep_not (N := n) p (fun Ω => ¬ PTOpNormLe Ω SV (1 / 2000))
  have n2 := bep_not (N := n) ρ (fun Ω => ¬ PTOpNormLe Ω SV (1 / 2000))
  have n3 := bep_not (N := n) p (fun Ω => PTOpNormLe Ω SV (1 / 2000))
  linarith

end RPCA29

namespace RPCA29
open RobustPCA.Recovery
open scoped BigOperators Classical

/-! ## E4 (off-support entries) and the final glue -/

lemma frob_tri {n : ℕ} (A Z : RealMatrix n n) :
    frobeniusNorm A ≤ frobeniusNorm (A - Z) + frobeniusNorm Z := by
  rw [frob_toE, frob_toE, frob_toE]
  have e : toE (A - Z) = toE A - toE Z := toEL.map_sub A Z
  rw [e]
  have := norm_sub_norm_le (toE A) (toE Z)
  linarith

lemma M_frob_le {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)} {SV : SVD L0 r}
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (h : PTOpNormLe Ω SV s) (Z : RealMatrix n n) :
    frobeniusNorm (∑' k, (Alin Ω SV)^[k] Z) ≤ 2 * frobeniusNorm Z := by
  have hs1 : s < 1 := by linarith
  have hr := rem_bound hs0 hs1 h Z
  have ht := frob_tri (∑' k, (Alin Ω SV)^[k] Z) Z
  have hq : s / (1 - s) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hZ := frob_nonneg' Z
  have : s / (1 - s) * frobeniusNorm Z ≤ 1 * frobeniusNorm Z := mul_le_mul_of_nonneg_right hq hZ
  linarith

lemma G_off {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)} {SV : SVD L0 r}
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (h : PTOpNormLe Ω SV s) (E : RealMatrix n n)
    (i j : Fin n) (hij : (i, j) ∉ Ω) (hE : E i j = 0) :
    (∑' k, (Alin Ω SV)^[k] E) i j = 0 := by
  rw [entry_tsum (iter_summable hs0 hs1 h E)]
  have hk : ∀ k, ((Alin Ω SV)^[k] E) i j = 0 := by
    intro k
    cases k with
    | zero => simpa using hE
    | succ k =>
      rw [Function.iterate_succ_apply']
      show samplingProjection Ω _ i j = 0
      simp [samplingProjection, hij]
  simp [hk]

lemma E4 {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Ω : Finset (Fin n × Fin n))
    (μ ρr : ℝ) (hinc : Incoherent SV μ) (hn : 0 < n) (hlog : 1 ≤ Real.log n)
    (hrank : (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr * n) (hρr : ρr ≤ 1 / 200000)
    (h : PTOpNormLe Ω SV (1 / 2000)) :
    RSF (fun E : RealMatrix n n => ¬ ∀ i j : Fin n,
      |matrixInner (Ecoef SV i j) (∑' k, (Alin Ω SV)^[k] E)| ≤ 1 / 8) Ω ≤
      2 * (n : ℝ) ^ (-11 : ℤ) := by
  have hs0 : (0 : ℝ) ≤ 1 / 2000 := by norm_num
  have hs1 : (1 / 2000 : ℝ) < 1 := by norm_num
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ (i j : Fin n) (E : RealMatrix n n),
      matrixInner (Ecoef SV i j) (∑' k, (Alin Ω SV)^[k] E) =
        ∑ p : Fin n × Fin n, (∑' k, (Alin Ω SV)^[k] (Ecoef SV i j)) p.1 p.2 * E p.1 p.2 := by
    intro i j E
    rw [dual_tsum hs0 hs1 h, pair_sum]
  have himp : ∀ P ⊆ Ω, (fun E : RealMatrix n n => ¬ ∀ i j : Fin n,
      |matrixInner (Ecoef SV i j) (∑' k, (Alin Ω SV)^[k] E)| ≤ 1 / 8) (signPattern Ω P) →
      ∃ t : Fin n × Fin n × Bool, (fun E : RealMatrix n n => (1 / 8 : ℝ) ≤
        ∑ p : Fin n × Fin n, ((if t.2.2 then (1 : ℝ) else -1) *
          (∑' k, (Alin Ω SV)^[k] (Ecoef SV t.1 t.2.1)) p.1 p.2) * E p.1 p.2) (signPattern Ω P) := by
    intro P _ hF
    simp only [not_forall, not_le] at hF
    obtain ⟨i, j, hij⟩ := hF
    rw [key] at hij
    rcases lt_abs.mp hij with h1 | h1
    · refine ⟨(i, j, true), ?_⟩
      simp only [if_true, one_mul]
      exact h1.le
    · refine ⟨(i, j, false), ?_⟩
      have e : ∑ p : Fin n × Fin n, ((if (false : Bool) = true then (1 : ℝ) else -1) *
          (∑' k, (Alin Ω SV)^[k] (Ecoef SV i j)) p.1 p.2) * signPattern Ω P p.1 p.2 =
          -∑ p : Fin n × Fin n, (∑' k, (Alin Ω SV)^[k] (Ecoef SV i j)) p.1 p.2 *
            signPattern Ω P p.1 p.2 := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        simp
      show (1 / 8 : ℝ) ≤ ∑ p : Fin n × Fin n, ((if (false : Bool) = true then (1 : ℝ) else -1) *
          (∑' k, (Alin Ω SV)^[k] (Ecoef SV i j)) p.1 p.2) * signPattern Ω P p.1 p.2
      rw [e]; exact h1.le
  refine le_trans (RSF_union Ω _ (fun (t : Fin n × Fin n × Bool) (E : RealMatrix n n) =>
    (1 / 8 : ℝ) ≤ ∑ p : Fin n × Fin n, ((if t.2.2 then (1 : ℝ) else -1) *
          (∑' k, (Alin Ω SV)^[k] (Ecoef SV t.1 t.2.1)) p.1 p.2) * E p.1 p.2) himp) ?_
  have hexp : Real.exp (-13 * Real.log n) = (n : ℝ) ^ (-13 : ℤ) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hnR]
    congr 1; push_cast; ring
  have hq : μ * r / n * Real.log n ^ 2 ≤ ρr := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hnR]; nlinarith
  have hterm : ∀ t : Fin n × Fin n × Bool, RSF (fun E : RealMatrix n n => (1 / 8 : ℝ) ≤
        ∑ p : Fin n × Fin n, ((if t.2.2 then (1 : ℝ) else -1) *
          (∑' k, (Alin Ω SV)^[k] (Ecoef SV t.1 t.2.1)) p.1 p.2) * E p.1 p.2) Ω ≤
      (n : ℝ) ^ (-13 : ℤ) := by
    intro t
    refine le_trans (sign_hoeff Ω _ (208 * Real.log n) (1 / 8) (by positivity)) ?_
    set Mt := ∑' k, (Alin Ω SV)^[k] (Ecoef SV t.1 t.2.1) with hMt
    have e : ∀ p : Fin n × Fin n, ((if t.2.2 then (1 : ℝ) else -1) * Mt p.1 p.2) ^ 2 =
        Mt p.1 p.2 ^ 2 := by
      intro p; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun p _ => e p)]
    have hS := sumsq_le Mt Ω
    have hM := M_frob_le hs0 (by norm_num) h (Ecoef SV t.1 t.2.1)
    rw [← hMt] at hM
    have hZ : frobeniusNorm (Ecoef SV t.1 t.2.1) ^ 2 ≤ 2 * μ * r / n := by
      rw [frob_sq]; exact Ecoef_sq_le SV μ hinc _ _
    have h0 := frob_nonneg' Mt
    have h0' := frob_nonneg' (Ecoef SV t.1 t.2.1)
    have h4 : frobeniusNorm Mt ^ 2 ≤ (2 * frobeniusNorm (Ecoef SV t.1 t.2.1)) ^ 2 :=
      pow_le_pow_left₀ h0 hM 2
    have hZ' : frobeniusNorm (Ecoef SV t.1 t.2.1) ^ 2 ≤ 2 * (μ * r / n) := by
      rw [show 2 * (μ * (r : ℝ) / n) = 2 * μ * r / n by ring]; exact hZ
    have hM2 : frobeniusNorm Mt ^ 2 ≤ 8 * (μ * r / n) :=
      calc frobeniusNorm Mt ^ 2 ≤ (2 * frobeniusNorm (Ecoef SV t.1 t.2.1)) ^ 2 := h4
        _ = 4 * frobeniusNorm (Ecoef SV t.1 t.2.1) ^ 2 := by ring
        _ ≤ 4 * (2 * (μ * r / n)) := by linarith
        _ = 8 * (μ * r / n) := by ring
    have hSq : ∑ p ∈ Ω, Mt p.1 p.2 ^ 2 ≤ 8 * (μ * r / n) := le_trans hS hM2
    have hL2 : 0 ≤ (208 * Real.log n) ^ 2 / 2 := by positivity
    have h1 : (208 * Real.log n) ^ 2 / 2 * ∑ p ∈ Ω, Mt p.1 p.2 ^ 2 ≤
        (208 * Real.log n) ^ 2 / 2 * (8 * (μ * r / n)) := mul_le_mul_of_nonneg_left hSq hL2
    have h2 : (208 * Real.log n) ^ 2 / 2 * (8 * (μ * r / n)) =
        173056 * (μ * r / n * Real.log n ^ 2) := by ring
    rw [← hexp]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc ∑ t : Fin n × Fin n × Bool, RSF (fun E : RealMatrix n n => (1 / 8 : ℝ) ≤
        ∑ p : Fin n × Fin n, ((if t.2.2 then (1 : ℝ) else -1) *
          (∑' k, (Alin Ω SV)^[k] (Ecoef SV t.1 t.2.1)) p.1 p.2) * E p.1 p.2) Ω
      ≤ ∑ _t : Fin n × Fin n × Bool, (n : ℝ) ^ (-13 : ℤ) :=
        Finset.sum_le_sum (fun t _ => hterm t)
    _ = 2 * (n : ℝ) ^ (-11 : ℤ) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
        have h11 : (n : ℝ) ^ (-11 : ℤ) = (n : ℝ) ^ (2 : ℤ) * (n : ℝ) ^ (-13 : ℤ) := by
          rw [← zpow_add₀ hnR.ne']; norm_num
        rw [h11, zpow_two]; push_cast; ring

open scoped Matrix.Norms.L2Operator in
lemma spec_smul {n : ℕ} (c : ℝ) (X : RealMatrix n n) :
    MatrixCompletion.spectralNorm (c • X) = |c| * MatrixCompletion.spectralNorm X := by
  rw [spec_eq, spec_eq, norm_smul, Real.norm_eq_abs]

lemma supp_signPattern {n : ℕ} (Ω P : Finset (Fin n × Fin n)) (hP : P ⊆ Ω) :
    supp (signPattern Ω P) = Ω := by
  ext ⟨i, j⟩
  simp only [supp, signPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : (i, j) ∈ P
  · simp [h1, hP h1]
  · by_cases h2 : (i, j) ∈ Ω <;> simp [h1, h2]

/-- the target event -/
def Ev29 {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (lam : ℝ) (E : RealMatrix n n) : Prop :=
  (∃ σ < 1 / 2, PTOpNormLe (supp E) SV σ) ∧
    MatrixCompletion.spectralNorm (WS lam (supp E) SV E) < 1 / 4 ∧
    entrySupNorm (compProj (supp E) (WS lam (supp E) SV E)) < lam / 4

lemma glue_det {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Ω P : Finset (Fin n × Fin n))
    (hP : P ⊆ Ω) (hn : 0 < n) (h : PTOpNormLe Ω SV (1 / 2000))
    (hA : MatrixCompletion.spectralNorm (signPattern Ω P) ≤ Real.sqrt n / 16)
    (h3 : MatrixCompletion.spectralNorm
      ((∑' k, (Alin Ω SV)^[k] (signPattern Ω P)) - signPattern Ω P) ≤ Real.sqrt n / 16)
    (h4 : ∀ i j : Fin n,
      |matrixInner (Ecoef SV i j) (∑' k, (Alin Ω SV)^[k] (signPattern Ω P))| ≤ 1 / 8) :
    Ev29 SV (1 / Real.sqrt n) (signPattern Ω P) := by
  unfold Ev29
  rw [supp_signPattern Ω P hP]
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hlam : 0 < 1 / Real.sqrt n := by positivity
  have hW : WS (1 / Real.sqrt n) Ω SV (signPattern Ω P) =
      (1 / Real.sqrt n) • normalProjection SV (∑' k, (Alin Ω SV)^[k] (signPattern Ω P)) := rfl
  refine ⟨⟨1 / 2000, by norm_num, h⟩, ?_, ?_⟩
  · rw [hW, spec_smul, abs_of_pos hlam]
    have h1 := spectral_normal_le SV (∑' k, (Alin Ω SV)^[k] (signPattern Ω P))
    have h2 := spectral_add ((∑' k, (Alin Ω SV)^[k] (signPattern Ω P)) - signPattern Ω P)
      (signPattern Ω P)
    rw [sub_add_cancel] at h2
    have h5 : MatrixCompletion.spectralNorm
        (normalProjection SV (∑' k, (Alin Ω SV)^[k] (signPattern Ω P))) ≤ Real.sqrt n / 8 := by
      linarith
    calc 1 / Real.sqrt n * MatrixCompletion.spectralNorm
          (normalProjection SV (∑' k, (Alin Ω SV)^[k] (signPattern Ω P)))
        ≤ 1 / Real.sqrt n * (Real.sqrt n / 8) := mul_le_mul_of_nonneg_left h5 hlam.le
      _ = 1 / 8 := by field_simp
      _ < 1 / 4 := by norm_num
  · have hb : entrySupNorm (compProj Ω (WS (1 / Real.sqrt n) Ω SV (signPattern Ω P))) ≤
        1 / Real.sqrt n / 8 := by
      refine entrySup_le _ _ (by positivity) (fun i j => ?_)
      rw [hW]
      by_cases hij : (i, j) ∈ Ω
      · simp only [compProj, samplingProjection, Matrix.sub_apply, if_pos hij, sub_self, abs_zero]
        positivity
      · have hnP : (i, j) ∉ P := fun h' => hij (hP h')
        have hGij : (∑' k, (Alin Ω SV)^[k] (signPattern Ω P)) i j = 0 :=
          G_off (by norm_num) (by norm_num) h _ i j hij (by simp [signPattern, hnP, hij])
        have hT : tangentProjection SV (∑' k, (Alin Ω SV)^[k] (signPattern Ω P)) i j =
            matrixInner (Ecoef SV i j) (∑' k, (Alin Ω SV)^[k] (signPattern Ω P)) := by
          rw [tangent_entry]; rfl
        have e : compProj Ω ((1 / Real.sqrt n) •
            normalProjection SV (∑' k, (Alin Ω SV)^[k] (signPattern Ω P))) i j =
            (1 / Real.sqrt n) * -(matrixInner (Ecoef SV i j)
              (∑' k, (Alin Ω SV)^[k] (signPattern Ω P))) := by
          simp only [compProj, samplingProjection, Matrix.sub_apply, if_neg hij, sub_zero,
            Matrix.smul_apply, normalProjection, smul_eq_mul, hGij, hT, zero_sub]
        rw [e, abs_mul, abs_neg, abs_of_pos hlam]
        calc 1 / Real.sqrt n * |matrixInner (Ecoef SV i j)
              (∑' k, (Alin Ω SV)^[k] (signPattern Ω P))|
            ≤ 1 / Real.sqrt n * (1 / 8) := mul_le_mul_of_nonneg_left (h4 i j) hlam.le
          _ = 1 / Real.sqrt n / 8 := by ring
    have : 1 / Real.sqrt n / 8 < 1 / Real.sqrt n / 4 := by linarith
    linarith

theorem main29 (h41 : T41) :
    ∃ ρs ρr c : ℝ, 0 < ρs ∧ 0 < ρr ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ρ : ℝ),
        0 < n → Incoherent SV μ → (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr * n →
        0 < ρ → ρ ≤ ρs →
        let lam := 1 / Real.sqrt n
        randomSignProb ρ (fun E : RealMatrix n n =>
            (∃ σ < 1 / 2, PTOpNormLe (supp E) SV σ) ∧
            MatrixCompletion.spectralNorm (WS lam (supp E) SV E) < 1 / 4 ∧
            entrySupNorm (compProj (supp E) (WS lam (supp E) SV E)) < lam / 4) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  obtain ⟨ρ1, hρ10, hρ11, HE1⟩ := E1
  obtain ⟨ρs0, ρr0, c0, hρs0, hρr0, hc0, HE2⟩ := E2 h41
  refine ⟨min ρ1 ρs0, min ρr0 (1 / 200000), c0 + 4 + 4000 ^ 10, lt_min hρ10 hρs0,
    lt_min hρr0 (by norm_num), by positivity, ?_⟩
  intro n r L0 SV μ ρ hn hinc hrank hρ0 hρs
  show randomSignProb ρ (Ev29 SV (1 / Real.sqrt n)) ≥ _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ1 : ρ ≤ 1 := le_trans hρs (le_trans (min_le_left _ _) hρ11)
  have hrsp0 : ∀ F : RealMatrix n n → Prop, 0 ≤ randomSignProb ρ F := fun F => by
    rw [rs_eq]
    exact Finset.sum_nonneg (fun Ω _ => mul_nonneg (bw_nonneg hρ0.le hρ1 Ω) (RSF_nonneg F Ω))
  have hz10 : 0 ≤ (n : ℝ) ^ (-10 : ℤ) := zpow_nonneg hnR.le _
  have hz11 : 0 ≤ (n : ℝ) ^ (-11 : ℤ) := zpow_nonneg hnR.le _
  by_cases hsmall : (n : ℝ) < 4000
  · have h10 : (n : ℝ) ^ (10 : ℕ) ≤ 4000 ^ 10 := pow_le_pow_left₀ hnR.le hsmall.le 10
    have hz : (n : ℝ) ^ (-10 : ℤ) * (n : ℝ) ^ (10 : ℕ) = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hnR.ne']; norm_num
    have hA : (n : ℝ) ^ (-10 : ℤ) * (n : ℝ) ^ (10 : ℕ) ≤ (n : ℝ) ^ (-10 : ℤ) * 4000 ^ 10 :=
      mul_le_mul_of_nonneg_left h10 hz10
    have hc : 0 ≤ (c0 + 4) * (n : ℝ) ^ (-10 : ℤ) := mul_nonneg (by linarith) hz10
    refine le_trans ?_ (hrsp0 _)
    nlinarith
  have hn4 : (4000 : ℝ) ≤ n := le_of_not_gt hsmall
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnR]
    have := Real.exp_one_lt_d9; linarith
  have hrank0 : (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr0 * n :=
    le_trans hrank (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR.le)
  have hrank1 : (r : ℝ) * μ * Real.log n ^ 2 ≤ 1 / 200000 * n :=
    le_trans hrank (mul_le_mul_of_nonneg_right (min_le_right _ _) hnR.le)
  have h1110 : (n : ℝ) ^ (-11 : ℤ) ≤ (n : ℝ) ^ (-10 : ℤ) :=
    zpow_le_zpow_right₀ (by linarith) (by norm_num)
  -- split off the event of E1
  have hU := rsp_union (ι := Bool) hρ0.le hρ1 (fun E => ¬ Ev29 SV (1 / Real.sqrt n) E)
    (fun b => cond b (fun E : RealMatrix n n =>
        ¬ MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16)
      (fun E => MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16 ∧
        ¬ Ev29 SV (1 / Real.sqrt n) E))
    (fun Ω P hF => by
      by_cases hA : MatrixCompletion.spectralNorm (signPattern Ω P) ≤ Real.sqrt n / 16
      · exact ⟨false, hA, hF⟩
      · exact ⟨true, hA⟩)
  rw [Fintype.sum_bool] at hU
  change _ ≤ randomSignProb ρ (fun E : RealMatrix n n =>
        ¬ MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16) +
      randomSignProb ρ (fun E => MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16 ∧
        ¬ Ev29 SV (1 / Real.sqrt n) E) at hU
  have hE1 := HE1 n ρ hn hρ0.le (le_trans hρs (min_le_left _ _))
  have hc1 := rsp_compl ρ (fun E : RealMatrix n n =>
    MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16)
  have hc2 := rsp_compl ρ (Ev29 SV (1 / Real.sqrt n))
  have hF2 := rs_cond hρ0.le hρ1 (fun E => MatrixCompletion.spectralNorm E ≤ Real.sqrt n / 16 ∧
        ¬ Ev29 SV (1 / Real.sqrt n) E) (fun Ω => PTOpNormLe Ω SV (1 / 2000))
    (3 * (n : ℝ) ^ (-11 : ℤ)) (by positivity) (fun Ω hg => by
      have hU2 := RSF_union (ι := Bool) Ω (fun E => MatrixCompletion.spectralNorm E ≤
          Real.sqrt n / 16 ∧ ¬ Ev29 SV (1 / Real.sqrt n) E)
        (fun b => cond b (fun E : RealMatrix n n => ¬ MatrixCompletion.spectralNorm
            ((∑' k, (Alin Ω SV)^[k] E) - E) ≤ Real.sqrt n / 16)
          (fun E => ¬ ∀ i j : Fin n,
            |matrixInner (Ecoef SV i j) (∑' k, (Alin Ω SV)^[k] E)| ≤ 1 / 8))
        (fun P hP hF => by
          by_cases h3 : MatrixCompletion.spectralNorm
              ((∑' k, (Alin Ω SV)^[k] (signPattern Ω P)) - signPattern Ω P) ≤ Real.sqrt n / 16
          · by_cases h4 : ∀ i j : Fin n, |matrixInner (Ecoef SV i j)
                (∑' k, (Alin Ω SV)^[k] (signPattern Ω P))| ≤ 1 / 8
            · exact absurd (glue_det SV Ω P hP hn hg hF.1 h3 h4) hF.2
            · exact ⟨false, h4⟩
          · exact ⟨true, h3⟩)
      rw [Fintype.sum_bool] at hU2
      change _ ≤ RSF (fun E : RealMatrix n n => ¬ MatrixCompletion.spectralNorm
            ((∑' k, (Alin Ω SV)^[k] E) - E) ≤ Real.sqrt n / 16) Ω +
          RSF (fun E => ¬ ∀ i j : Fin n,
            |matrixInner (Ecoef SV i j) (∑' k, (Alin Ω SV)^[k] E)| ≤ 1 / 8) Ω at hU2
      have h3b := E3 SV Ω hn (1 / 2000) (by norm_num) le_rfl hg
      have h4b := E4 SV Ω μ (1 / 200000) hinc hn hlog hrank1 le_rfl hg
      linarith)
  have hE2 := HE2 n r L0 SV μ ρ hn4 hinc hrank0 hρ0.le (le_trans hρs (min_le_right _ _))
  have hfin : (c0 + 4) * (n : ℝ) ^ (-11 : ℤ) ≤ (c0 + 4) * (n : ℝ) ^ (-10 : ℤ) :=
    mul_le_mul_of_nonneg_left h1110 (by linarith)
  have hbig : 0 ≤ 4000 ^ 10 * (n : ℝ) ^ (-10 : ℤ) := mul_nonneg (by positivity) hz10
  nlinarith

end RPCA29


open RobustPCA.Recovery in
theorem solution :
    ∃ ρs ρr c : ℝ, 0 < ρs ∧ 0 < ρr ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ρ : ℝ),
        0 < n → Incoherent SV μ → (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr * n →
        0 < ρ → ρ ≤ ρs →
        let lam := 1 / Real.sqrt n
        randomSignProb ρ (fun E : RealMatrix n n =>
            (∃ σ < 1 / 2, PTOpNormLe (supp E) SV σ) ∧
            spectralNorm (WS lam (supp E) SV E) < 1 / 4 ∧
            entrySupNorm (compProj (supp E) (WS lam (supp E) SV E)) < lam / 4) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  exact RPCA29.main29 candes_recht_theorem41_bernoulli_tangent_sampling_concentration
