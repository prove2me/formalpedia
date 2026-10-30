-- Prove2me | solution 1 for RobustPCA.Recovery.lemma_2_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T10:57:03.75907+00:00
-- url     : https://prove2.me/submissions/102ce5ae-a16d-4811-8039-9b4b297f25c0

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

namespace RPCA28

open RobustPCA.Recovery
open scoped BigOperators Classical

/-! ## Projection algebra (copied from scratch/decomp/429b6866 and 0363db4b) -/

noncomputable def projM {n r : ℕ} (u : Fin r → Fin n → ℝ) : RealMatrix n n :=
  fun i a => ∑ k, u k i * u k a

noncomputable def PU {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.u

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

lemma projM_transpose {n r : ℕ} (u : Fin r → Fin n → ℝ) :
    Matrix.transpose (projM u) = projM u := by
  ext i a
  simp only [Matrix.transpose_apply, projM]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

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

lemma tangent_sub {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    tangentProjection SV (X - Y) = tangentProjection SV X - tangentProjection SV Y := by
  simp only [tangent_eq, Matrix.mul_sub, Matrix.sub_mul]
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

lemma projM_mul_vmv {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) (k : Fin r) (w : Fin n → ℝ) :
    projM u * Matrix.vecMulVec (u k) w = Matrix.vecMulVec (u k) w := by
  ext i j
  simp only [Matrix.mul_apply, projM, Matrix.vecMulVec_apply]
  have h1 : ∀ a, (∑ l, u l i * u l a) * (u k a * w j) = ∑ l, u l i * w j * (u l a * u k a) := by
    intro a
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hu]
  simp

lemma vmv_mul_projM {n r : ℕ} (v : Fin r → Fin n → ℝ)
    (hv : ∀ k l, ∑ i, v k i * v l i = if k = l then 1 else 0) (k : Fin r) (w : Fin n → ℝ) :
    Matrix.vecMulVec w (v k) * projM v = Matrix.vecMulVec w (v k) := by
  ext i j
  simp only [Matrix.mul_apply, projM, Matrix.vecMulVec_apply]
  have h1 : ∀ b, w i * v k b * (∑ l, v l b * v l j) = ∑ l, w i * v l j * (v k b * v l b) := by
    intro b
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hv]
  simp

lemma PU_mul_sign {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    PU SV * signMatrix SV = signMatrix SV := by
  unfold signMatrix PU
  rw [Matrix.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => projM_mul_vmv SV.u SV.u_orthonormal k (SV.v k))

lemma sign_mul_PV {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    signMatrix SV * PV SV = signMatrix SV := by
  unfold signMatrix PV
  rw [Matrix.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => vmv_mul_projM SV.v SV.v_orthonormal k (SV.u k))

lemma tangent_sign {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    tangentProjection SV (signMatrix SV) = signMatrix SV := by
  rw [tangent_eq, PU_mul_sign, sign_mul_PV]
  abel

lemma normal_eq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    normalProjection SV X = (1 - PU SV) * X * (1 - PV SV) := by
  simp only [normalProjection, tangent_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one]
  abel

lemma normal_add {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    normalProjection SV (X + Y) = normalProjection SV X + normalProjection SV Y := by
  simp only [normalProjection, tangent_add]
  abel

lemma normal_sub {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    normalProjection SV (X - Y) = normalProjection SV X - normalProjection SV Y := by
  simp only [normalProjection, tangent_sub]
  abel

/-! ## Norm facts -/

open scoped Matrix.Norms.L2Operator in
lemma spec_eq {n : ℕ} (X : RealMatrix n n) : MatrixCompletion.spectralNorm X = ‖X‖ := rfl

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

lemma spectral_sub {n : ℕ} (A B : RealMatrix n n) :
    MatrixCompletion.spectralNorm (A - B) ≤
      MatrixCompletion.spectralNorm A + MatrixCompletion.spectralNorm B := by
  unfold MatrixCompletion.spectralNorm
  rw [map_sub, map_sub]
  exact norm_sub_le _ _

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

lemma entrySup_le {n : ℕ} (A : RealMatrix n n) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i j, |A i j| ≤ b) : entrySupNorm A ≤ b := by
  unfold entrySupNorm
  exact Real.iSup_le (fun i => Real.iSup_le (fun j => h i j) hb) hb

lemma frob_le_entrySup {n : ℕ} (A : RealMatrix n n) :
    frobeniusNorm A ≤ n * entrySupNorm A := by
  have h0 := entrySup_nonneg A
  unfold frobeniusNorm frobeniusNormSq
  rw [Real.sqrt_le_left (by positivity)]
  calc ∑ i, ∑ j, A i j ^ 2 ≤ ∑ _i : Fin n, ∑ _j : Fin n, entrySupNorm A ^ 2 := by
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
        have := le_entrySup A i j
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = (n * entrySupNorm A) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

lemma frob_sampling_le {n : ℕ} (Ω : Finset (Fin n × Fin n)) (X : RealMatrix n n) :
    frobeniusNorm (samplingProjection Ω X) ≤ frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
  simp only [samplingProjection]
  split_ifs
  · exact le_refl _
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity

lemma sampling_add {n : ℕ} (Ω : Finset (Fin n × Fin n)) (A B : RealMatrix n n) :
    samplingProjection Ω (A + B) = samplingProjection Ω A + samplingProjection Ω B := by
  ext i j
  simp only [samplingProjection, Matrix.add_apply]
  split_ifs <;> simp

/-! ## Bernoulli sums -/

lemma bw_sum_one {N : ℕ} (p : ℝ) :
    ∑ A : Finset (Fin N × Fin N), bernoulliObservationWeight p A = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ : Finset (Fin N × Fin N))
  rw [Finset.powerset_univ, Finset.card_univ, show p + (1 - p) = 1 by ring, one_pow] at h
  exact h

lemma bw_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset (Fin N × Fin N)) :
    0 ≤ bernoulliObservationWeight p A := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

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

lemma prodW_sum_one {n j0 : ℕ} (q : ℝ) :
    ∑ Ωs : Fin j0 → Finset (Fin n × Fin n), ∏ k, bernoulliObservationWeight q (Ωs k) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin j0) (B : Finset (Fin n × Fin n)) =>
    bernoulliObservationWeight q B)]
  simp [bw_sum_one]

lemma prodW_nonneg {n j0 : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (Ωs : Fin j0 → Finset (Fin n × Fin n)) :
    0 ≤ ∏ k, bernoulliObservationWeight q (Ωs k) :=
  Finset.prod_nonneg (fun k _ => bw_nonneg hq0 hq1 _)

lemma golf_swap {n j0 : ℕ} (q : ℝ) (j : Fin j0)
    (G : (Fin j0 → Finset (Fin n × Fin n)) → ℝ) :
    ∑ Ωs : Fin j0 → Finset (Fin n × Fin n), (∏ k, bernoulliObservationWeight q (Ωs k)) * G Ωs =
    ∑ Ωs : Fin j0 → Finset (Fin n × Fin n), (∏ k, bernoulliObservationWeight q (Ωs k)) *
      ∑ B : Finset (Fin n × Fin n),
        bernoulliObservationWeight q B * G (Function.update Ωs j B) := by
  classical
  have hW : ∀ (Ωs : Fin j0 → Finset (Fin n × Fin n)) (B : Finset (Fin n × Fin n)),
      (∏ k, bernoulliObservationWeight q (Ωs k)) * bernoulliObservationWeight q B =
      (∏ k, bernoulliObservationWeight q (Function.update Ωs j B k)) *
        bernoulliObservationWeight q (Ωs j) := by
    intro Ωs B
    rw [← Finset.mul_prod_erase Finset.univ (fun k => bernoulliObservationWeight q (Ωs k))
        (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ
        (fun k => bernoulliObservationWeight q (Function.update Ωs j B k)) (Finset.mem_univ j)]
    simp only [Function.update_self]
    have he : ∏ k ∈ Finset.univ.erase j, bernoulliObservationWeight q (Function.update Ωs j B k) =
        ∏ k ∈ Finset.univ.erase j, bernoulliObservationWeight q (Ωs k) :=
      Finset.prod_congr rfl (fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])
    rw [he]
    ring
  have hinv : Function.Involutive
      (fun p : (Fin j0 → Finset (Fin n × Fin n)) × Finset (Fin n × Fin n) =>
        (Function.update p.1 j p.2, p.1 j)) := by
    intro p
    ext1
    · simp
    · simp
  let F : (Fin j0 → Finset (Fin n × Fin n)) × Finset (Fin n × Fin n) → ℝ := fun p =>
    (∏ k, bernoulliObservationWeight q (p.1 k)) * G p.1 * bernoulliObservationWeight q p.2
  have h1 := Equiv.sum_comp (hinv.toPerm _) F
  calc ∑ Ωs : Fin j0 → Finset (Fin n × Fin n), (∏ k, bernoulliObservationWeight q (Ωs k)) * G Ωs
        = ∑ p, F p := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun X _ => ?_)
          simp only [F]
          rw [← Finset.mul_sum, bw_sum_one, mul_one]
    _ = ∑ p, F ((hinv.toPerm _) p) := h1.symm
    _ = _ := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun X _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun B _ => ?_)
          simp only [F, Function.Involutive.coe_toPerm]
          have := hW X B
          calc (∏ k, bernoulliObservationWeight q (Function.update X j B k)) *
                G (Function.update X j B) * bernoulliObservationWeight q (X j)
              = ((∏ k, bernoulliObservationWeight q (Function.update X j B k)) *
                  bernoulliObservationWeight q (X j)) * G (Function.update X j B) := by ring
            _ = ((∏ k, bernoulliObservationWeight q (X k)) * bernoulliObservationWeight q B) *
                  G (Function.update X j B) := by rw [this]
            _ = _ := by ring

lemma golf_union {n j0 : ℕ} (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (Bad : Fin j0 → (Fin j0 → Finset (Fin n × Fin n)) → Prop)
    (hB : ∀ j Ωs, bernoulliEventProb q (fun B => Bad j (Function.update Ωs j B)) ≤ δ)
    (E : (Fin j0 → Finset (Fin n × Fin n)) → Prop) (hE : ∀ Ωs, (∀ j, ¬ Bad j Ωs) → E Ωs) :
    golfingProb q j0 E ≥ 1 - j0 * δ := by
  unfold golfingProb
  have hpt : ∀ Ωs : Fin j0 → Finset (Fin n × Fin n),
      (∏ k, bernoulliObservationWeight q (Ωs k)) *
        (1 - ∑ j, (if Bad j Ωs then (1 : ℝ) else 0)) ≤
      (∏ k, bernoulliObservationWeight q (Ωs k)) * (if E Ωs then 1 else 0) := by
    intro Ωs
    apply mul_le_mul_of_nonneg_left _ (prodW_nonneg hq0 hq1 Ωs)
    split_ifs with h
    · have : (0 : ℝ) ≤ ∑ j, (if Bad j Ωs then (1 : ℝ) else 0) :=
        Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
      linarith
    · have h' : ∃ j, Bad j Ωs := by
        by_contra hc
        exact h (hE Ωs (fun j hj => hc ⟨j, hj⟩))
      obtain ⟨j, hj⟩ := h'
      have : (if Bad j Ωs then (1 : ℝ) else 0) ≤ ∑ j, (if Bad j Ωs then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun j => if Bad j Ωs then (1 : ℝ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
      rw [if_pos hj] at this
      linarith
  have hstep : ∀ j : Fin j0,
      ∑ Ωs : Fin j0 → Finset (Fin n × Fin n),
        (∏ k, bernoulliObservationWeight q (Ωs k)) * (if Bad j Ωs then (1 : ℝ) else 0) ≤ δ := by
    intro j
    rw [golf_swap q j]
    calc ∑ Ωs : Fin j0 → Finset (Fin n × Fin n), (∏ k, bernoulliObservationWeight q (Ωs k)) *
          ∑ B : Finset (Fin n × Fin n), bernoulliObservationWeight q B *
            (if Bad j (Function.update Ωs j B) then (1 : ℝ) else 0)
        ≤ ∑ Ωs : Fin j0 → Finset (Fin n × Fin n),
            (∏ k, bernoulliObservationWeight q (Ωs k)) * δ := by
          refine Finset.sum_le_sum (fun Ωs _ => ?_)
          apply mul_le_mul_of_nonneg_left _ (prodW_nonneg hq0 hq1 Ωs)
          have := hB j Ωs
          rw [bep_eq_sum] at this
          convert this using 3
      _ = δ := by rw [← Finset.sum_mul, prodW_sum_one, one_mul]
  calc 1 - (j0 : ℝ) * δ = ∑ Ωs : Fin j0 → Finset (Fin n × Fin n),
        (∏ k, bernoulliObservationWeight q (Ωs k)) - ∑ _j : Fin j0, δ := by
          rw [prodW_sum_one]; simp
    _ ≤ ∑ Ωs : Fin j0 → Finset (Fin n × Fin n),
          (∏ k, bernoulliObservationWeight q (Ωs k)) -
        ∑ j : Fin j0, ∑ Ωs : Fin j0 → Finset (Fin n × Fin n),
          (∏ k, bernoulliObservationWeight q (Ωs k)) * (if Bad j Ωs then (1 : ℝ) else 0) := by
          have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hstep j)
          linarith
    _ = ∑ Ωs : Fin j0 → Finset (Fin n × Fin n), (∏ k, bernoulliObservationWeight q (Ωs k)) *
          (1 - ∑ j, (if Bad j Ωs then (1 : ℝ) else 0)) := by
          rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun Ωs _ => ?_)
          rw [mul_sub, mul_one, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum (fun Ωs _ => hpt Ωs)

lemma golf_mono {n j0 : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (E F : (Fin j0 → Finset (Fin n × Fin n)) → Prop) (h : ∀ Ωs, E Ωs → F Ωs) :
    golfingProb q j0 E ≤ golfingProb q j0 F := by
  unfold golfingProb
  refine Finset.sum_le_sum (fun Ωs _ => ?_)
  apply mul_le_mul_of_nonneg_left _ (prodW_nonneg hq0 hq1 Ωs)
  split_ifs with h1 h2 <;> first | (exfalso; exact h2 (h Ωs h1)) | norm_num

lemma golf_nonneg {n j0 : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (E : (Fin j0 → Finset (Fin n × Fin n)) → Prop) : 0 ≤ golfingProb q j0 E := by
  unfold golfingProb
  refine Finset.sum_nonneg (fun Ωs _ => mul_nonneg (prodW_nonneg hq0 hq1 Ωs) ?_)
  split_ifs <;> norm_num

/-! ## The golfing iterates -/

noncomputable def Zg {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (q : ℝ) {j0 : ℕ}
    (Ωs : Fin j0 → Finset (Fin n × Fin n)) (j : ℕ) : RealMatrix n n :=
  tangentProjection SV (signMatrix SV - golfY SV q Ωs j)

section golf
variable {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (q : ℝ) {j0 : ℕ}
    (Ωs : Fin j0 → Finset (Fin n × Fin n))

lemma golfY_zero : golfY SV q Ωs 0 = 0 := by rw [golfY]

lemma golfY_succ (j : ℕ) (h : j < j0) :
    golfY SV q Ωs (j + 1) = golfY SV q Ωs j + q⁻¹ • samplingProjection (Ωs ⟨j, h⟩)
      (Zg SV q Ωs j) := by
  rw [golfY, dif_pos h]; rfl

lemma Zg_zero : Zg SV q Ωs 0 = signMatrix SV := by
  rw [Zg, golfY_zero, sub_zero, tangent_sign]

lemma Zg_T (j : ℕ) : tangentProjection SV (Zg SV q Ωs j) = Zg SV q Ωs j := tangent_idem SV _

lemma Zg_succ (j : ℕ) (h : j < j0) :
    Zg SV q Ωs (j + 1) = Zg SV q Ωs j -
      q⁻¹ • tangentProjection SV (samplingProjection (Ωs ⟨j, h⟩) (Zg SV q Ωs j)) := by
  rw [Zg, golfY_succ SV q Ωs j h, show signMatrix SV - (golfY SV q Ωs j +
      q⁻¹ • samplingProjection (Ωs ⟨j, h⟩) (Zg SV q Ωs j)) = (signMatrix SV - golfY SV q Ωs j) -
      q⁻¹ • samplingProjection (Ωs ⟨j, h⟩) (Zg SV q Ωs j) by abel, tangent_sub, tangent_smul]
  rfl

lemma golfY_update (i : Fin j0) (B : Finset (Fin n × Fin n)) :
    ∀ k, k ≤ i.val → golfY SV q (Function.update Ωs i B) k = golfY SV q Ωs k := by
  intro k
  induction k with
  | zero => intro _; rw [golfY_zero, golfY_zero]
  | succ k ih =>
    intro hk
    have hk' : k < j0 := by omega
    rw [golfY_succ SV q _ k hk', golfY_succ SV q _ k hk']
    have hne : (⟨k, hk'⟩ : Fin j0) ≠ i := by
      intro h; rw [← h] at hk; simp at hk
    have e1 : Zg SV q (Function.update Ωs i B) k = Zg SV q Ωs k := by
      rw [Zg, Zg, ih (by omega)]
    rw [ih (by omega), e1, Function.update_of_ne hne]

lemma Zg_update (i : Fin j0) (B : Finset (Fin n × Fin n)) :
    Zg SV q (Function.update Ωs i B) i.val = Zg SV q Ωs i.val := by
  rw [Zg, Zg, golfY_update SV q Ωs i B i.val le_rfl]

lemma sampling_golfY (k : ℕ) : samplingProjection (golfOmega Ωs) (golfY SV q Ωs k) = 0 := by
  induction k with
  | zero => rw [golfY_zero]; ext a b; simp [samplingProjection]
  | succ k ih =>
    by_cases h : k < j0
    · rw [golfY_succ SV q Ωs k h]
      ext a b
      have hIH := congrFun (congrFun ih a) b
      simp only [samplingProjection, Matrix.zero_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul] at hIH ⊢
      by_cases h1 : (a, b) ∈ golfOmega Ωs
      · have h2 : (a, b) ∉ Ωs ⟨k, h⟩ := by
          intro h2
          simp only [golfOmega, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion,
            true_and, not_exists] at h1
          exact h1 _ h2
        rw [if_pos h1] at hIH
        rw [if_pos h1, if_neg h2, hIH]; ring
      · rw [if_neg h1]
    · rw [golfY, dif_neg h]; exact ih

lemma sign_add_WL :
    signMatrix SV + WL SV q Ωs = Zg SV q Ωs j0 + golfY SV q Ωs j0 := by
  simp only [WL, normalProjection, Zg, tangent_sub, tangent_sign]
  abel

lemma normal_Zg (j : ℕ) : normalProjection SV (Zg SV q Ωs j) = 0 := by
  rw [normalProjection, Zg_T, sub_self]

lemma normal_golfY_succ (j : ℕ) (h : j < j0) :
    normalProjection SV (golfY SV q Ωs (j + 1)) = normalProjection SV (golfY SV q Ωs j) -
      normalProjection SV (Zg SV q Ωs j - q⁻¹ • samplingProjection (Ωs ⟨j, h⟩) (Zg SV q Ωs j)) := by
  rw [golfY_succ SV q Ωs j h, normal_add, normal_sub, normal_Zg]
  abel

end golf


/-! ## Stage 2: deterministic bounds on the good event -/

lemma normal_zero {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) :
    normalProjection SV (0 : RealMatrix n n) = 0 := by
  rw [normalProjection, tangent_eq]; simp

open scoped Matrix.Norms.L2Operator in
lemma spectral_zero {n : ℕ} : MatrixCompletion.spectralNorm (0 : RealMatrix n n) = 0 := by
  rw [spec_eq]; exact norm_zero

lemma entrySup_zero {n : ℕ} : entrySupNorm (0 : RealMatrix n n) = 0 :=
  le_antisymm (entrySup_le _ 0 le_rfl (fun i j => by simp)) (entrySup_nonneg _)

lemma entrySup_compProj_le {n : ℕ} (Ω : Finset (Fin n × Fin n)) (X : RealMatrix n n) :
    entrySupNorm (compProj Ω X) ≤ entrySupNorm X := by
  apply entrySup_le _ _ (entrySup_nonneg X)
  intro i j
  simp only [compProj, samplingProjection, Matrix.sub_apply]
  split_ifs
  · simp [entrySup_nonneg]
  · simpa using le_entrySup X i j

lemma frob_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _

section det
variable {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (q : ℝ) {j0 : ℕ}
    (Ωs : Fin j0 → Finset (Fin n × Fin n))

lemma det_bound (ε1 ε a D : ℝ) (hq : 0 < q) (hε10 : 0 ≤ ε1) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hD : 0 ≤ D)
    (ha : entrySupNorm (signMatrix SV) ≤ a)
    (hG : ∀ j : Fin j0,
      (∀ X : RealMatrix n n, frobeniusNorm (tangentProjection SV X -
            q⁻¹ • tangentProjection SV (samplingProjection (Ωs j) (tangentProjection SV X))) ≤
            ε1 * frobeniusNorm X) ∧
      entrySupNorm (Zg SV q Ωs j.val - q⁻¹ • tangentProjection SV
          (samplingProjection (Ωs j) (Zg SV q Ωs j.val))) ≤ ε * entrySupNorm (Zg SV q Ωs j.val) ∧
      MatrixCompletion.spectralNorm (Zg SV q Ωs j.val -
          q⁻¹ • samplingProjection (Ωs j) (Zg SV q Ωs j.val)) ≤
        D * entrySupNorm (Zg SV q Ωs j.val)) :
    MatrixCompletion.spectralNorm (WL SV q Ωs) ≤ D * a / (1 - ε) ∧
    frobeniusNorm (samplingProjection (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) ≤
      ε1 ^ j0 * frobeniusNorm (signMatrix SV) ∧
    entrySupNorm (compProj (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) ≤
      ε ^ j0 * a + q⁻¹ * a / (1 - ε) := by
  have ha0 : 0 ≤ a := le_trans (entrySup_nonneg _) ha
  have hne : (1 - ε) ≠ 0 := by intro h; linarith
  have hpos : 0 < 1 - ε := by linarith
  have hZf : ∀ k, k ≤ j0 → frobeniusNorm (Zg SV q Ωs k) ≤ ε1 ^ k * frobeniusNorm (signMatrix SV) := by
    intro k
    induction k with
    | zero => intro _; rw [Zg_zero, pow_zero, one_mul]
    | succ k ih =>
      intro hk
      have hk' : k < j0 := by omega
      have g := (hG ⟨k, hk'⟩).1 (Zg SV q Ωs k)
      rw [Zg_T] at g
      rw [Zg_succ SV q Ωs k hk']
      calc _ ≤ ε1 * frobeniusNorm (Zg SV q Ωs k) := g
        _ ≤ ε1 * (ε1 ^ k * frobeniusNorm (signMatrix SV)) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hε10
        _ = ε1 ^ (k + 1) * frobeniusNorm (signMatrix SV) := by ring
  have hZe : ∀ k, k ≤ j0 → entrySupNorm (Zg SV q Ωs k) ≤ ε ^ k * a := by
    intro k
    induction k with
    | zero => intro _; rw [Zg_zero, pow_zero, one_mul]; exact ha
    | succ k ih =>
      intro hk
      have hk' : k < j0 := by omega
      have g : entrySupNorm (Zg SV q Ωs k - q⁻¹ • tangentProjection SV
          (samplingProjection (Ωs ⟨k, hk'⟩) (Zg SV q Ωs k))) ≤
          ε * entrySupNorm (Zg SV q Ωs k) := (hG ⟨k, hk'⟩).2.1
      rw [Zg_succ SV q Ωs k hk']
      calc _ ≤ ε * entrySupNorm (Zg SV q Ωs k) := g
        _ ≤ ε * (ε ^ k * a) := mul_le_mul_of_nonneg_left (ih (by omega)) hε0
        _ = ε ^ (k + 1) * a := by ring
  have hYe : ∀ k, k ≤ j0 → entrySupNorm (golfY SV q Ωs k) ≤ q⁻¹ * a / (1 - ε) * (1 - ε ^ k) := by
    intro k
    induction k with
    | zero => intro _; rw [golfY_zero, pow_zero, sub_self, mul_zero, entrySup_zero]
    | succ k ih =>
      intro hk
      have hk' : k < j0 := by omega
      rw [golfY_succ SV q Ωs k hk']
      have hnn : 0 ≤ q⁻¹ * (ε ^ k * a) :=
        mul_nonneg (inv_nonneg.mpr hq.le) (mul_nonneg (pow_nonneg hε0 _) ha0)
      have h1 : entrySupNorm (q⁻¹ • samplingProjection (Ωs ⟨k, hk'⟩) (Zg SV q Ωs k)) ≤
          q⁻¹ * (ε ^ k * a) := by
        apply entrySup_le _ _ hnn
        intro i j
        simp only [Matrix.smul_apply, smul_eq_mul, samplingProjection]
        rw [abs_mul, abs_of_pos (inv_pos.mpr hq)]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hq.le)
        split_ifs
        · exact le_trans (le_entrySup _ i j) (hZe k (by omega))
        · simp only [abs_zero]; exact mul_nonneg (pow_nonneg hε0 _) ha0
      calc _ ≤ entrySupNorm (golfY SV q Ωs k) +
            entrySupNorm (q⁻¹ • samplingProjection (Ωs ⟨k, hk'⟩) (Zg SV q Ωs k)) :=
            entrySup_add _ _
        _ ≤ q⁻¹ * a / (1 - ε) * (1 - ε ^ k) + q⁻¹ * (ε ^ k * a) := add_le_add (ih (by omega)) h1
        _ = q⁻¹ * a / (1 - ε) * (1 - ε ^ (k + 1)) := by field_simp; ring
  have hNs : ∀ k, k ≤ j0 → MatrixCompletion.spectralNorm (normalProjection SV (golfY SV q Ωs k)) ≤
      D * a / (1 - ε) * (1 - ε ^ k) := by
    intro k
    induction k with
    | zero => intro _; rw [golfY_zero, normal_zero, spectral_zero]; simp
    | succ k ih =>
      intro hk
      have hk' : k < j0 := by omega
      have g : MatrixCompletion.spectralNorm (Zg SV q Ωs k -
          q⁻¹ • samplingProjection (Ωs ⟨k, hk'⟩) (Zg SV q Ωs k)) ≤
          D * entrySupNorm (Zg SV q Ωs k) := (hG ⟨k, hk'⟩).2.2
      rw [normal_golfY_succ SV q Ωs k hk']
      calc _ ≤ MatrixCompletion.spectralNorm (normalProjection SV (golfY SV q Ωs k)) +
            MatrixCompletion.spectralNorm (normalProjection SV (Zg SV q Ωs k -
              q⁻¹ • samplingProjection (Ωs ⟨k, hk'⟩) (Zg SV q Ωs k))) := spectral_sub _ _
        _ ≤ D * a / (1 - ε) * (1 - ε ^ k) + D * (ε ^ k * a) := by
            apply add_le_add (ih (by omega))
            exact le_trans (spectral_normal_le SV _)
              (le_trans g (mul_le_mul_of_nonneg_left (hZe k (by omega)) hD))
        _ = D * a / (1 - ε) * (1 - ε ^ (k + 1)) := by field_simp; ring
  have hεj : 0 ≤ ε ^ j0 := pow_nonneg hε0 _
  refine ⟨?_, ?_, ?_⟩
  · have := hNs j0 le_rfl
    have hc : 0 ≤ D * a / (1 - ε) := div_nonneg (mul_nonneg hD ha0) hpos.le
    calc MatrixCompletion.spectralNorm (WL SV q Ωs)
        = MatrixCompletion.spectralNorm (normalProjection SV (golfY SV q Ωs j0)) := rfl
      _ ≤ D * a / (1 - ε) * (1 - ε ^ j0) := this
      _ ≤ D * a / (1 - ε) := mul_le_of_le_one_right hc (by linarith)
  · rw [sign_add_WL, sampling_add, sampling_golfY, add_zero]
    exact le_trans (frob_sampling_le _ _) (hZf j0 le_rfl)
  · rw [sign_add_WL]
    have hc : 0 ≤ q⁻¹ * a / (1 - ε) := div_nonneg (mul_nonneg (inv_nonneg.mpr hq.le) ha0) hpos.le
    calc _ ≤ entrySupNorm (Zg SV q Ωs j0 + golfY SV q Ωs j0) := entrySup_compProj_le _ _
      _ ≤ entrySupNorm (Zg SV q Ωs j0) + entrySupNorm (golfY SV q Ωs j0) := entrySup_add _ _
      _ ≤ ε ^ j0 * a + q⁻¹ * a / (1 - ε) * (1 - ε ^ j0) :=
          add_le_add (hZe j0 le_rfl) (hYe j0 le_rfl)
      _ ≤ ε ^ j0 * a + q⁻¹ * a / (1 - ε) := by
          have := mul_le_of_le_one_right hc (show 1 - ε ^ j0 ≤ 1 by linarith)
          linarith

end det

/-! ## Real-number facts -/

lemma q_lower (ρ : ℝ) (j0 : ℕ) (hj : 1 ≤ j0) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ Real.exp (-1)) :
    1 / ((j0 : ℝ) + 1) ≤ 1 - ρ ^ ((1 : ℝ) / j0) := by
  have hj' : (0 : ℝ) < j0 := by exact_mod_cast hj
  have hx0 : (0 : ℝ) < 1 / j0 := by positivity
  have h1 : ρ ^ ((1 : ℝ) / j0) ≤ Real.exp (-1) ^ ((1 : ℝ) / j0) :=
    Real.rpow_le_rpow hρ0.le hρ1 hx0.le
  have h2 : Real.exp (-1) ^ ((1 : ℝ) / j0) = (Real.exp ((1 : ℝ) / j0))⁻¹ := by
    rw [← Real.exp_mul, ← Real.exp_neg]; ring_nf
  have h3 : (1 : ℝ) / j0 + 1 ≤ Real.exp ((1 : ℝ) / j0) := Real.add_one_le_exp _
  have h4 : (Real.exp ((1 : ℝ) / j0))⁻¹ ≤ ((1 : ℝ) / j0 + 1)⁻¹ := inv_anti₀ (by positivity) h3
  have h5 : 1 - ((1 : ℝ) / j0 + 1)⁻¹ = 1 / ((j0 : ℝ) + 1) := by field_simp; ring
  linarith

lemma eps_pow_le (n j0 : ℕ) (hn : (0 : ℝ) < n) (hj : 2 * Real.log n ≤ j0) :
    Real.exp (-1) ^ j0 ≤ 1 / (n : ℝ) ^ 2 := by
  rw [← Real.exp_nat_mul]
  have h1 : Real.exp (j0 * -1) ≤ Real.exp (-(2 * Real.log n)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(2 * Real.log n)) = 1 / (n : ℝ) ^ 2 := by
    rw [Real.exp_neg, show 2 * Real.log n = ((2 : ℕ) : ℝ) * Real.log n by norm_num,
      Real.exp_nat_mul, Real.exp_log hn, one_div]
  linarith


lemma aux_h5 (C0 L n N0 : ℝ) (hC0 : 0 < C0) (hL4 : L ^ 4 / 24 ≤ n)
    (hN0 : N0 = 600 * C0 ^ 2 + 3) (hbig : N0 ≤ n) : 5 * C0 * L ^ 2 ≤ n := by
  rcases le_or_gt (120 * C0) (L ^ 2) with hc | hc
  · nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg L)]
  · nlinarith

lemma aux_condC (C0 L n : ℝ) (hL : 0 < L) (hn : 0 < n) (h5 : 5 * C0 * L ^ 2 ≤ n) :
    C0 * 1 * L / n ≤ 1 / (5 * L) := by
  rw [div_le_div_iff₀ hn (by positivity)]; nlinarith

lemma aux_div (X ε : ℝ) (hX : 0 ≤ X) (hε : ε ≤ 1 / 2) : X / (1 - ε) ≤ 2 * X := by
  rw [div_le_iff₀ (by linarith)]; nlinarith

lemma aux_a (X C1 δ : ℝ) (hX : X ≤ 3 * C1 * δ) (h : δ * (25 * C1) ≤ 1) : 2 * X < 1 / 4 := by
  nlinarith

lemma aux_b (a s n δ : ℝ) (ha : 0 ≤ a) (hs : 0 < s) (has : a * s ≤ δ) (hδ : δ ≤ 1 / 50)
    (hn : 3 ≤ n) : a / n < 1 / s / 4 := by
  rw [div_div, div_lt_div_iff₀ (by linarith) (by positivity)]; nlinarith

lemma aux_c (a s L δ : ℝ) (hs : 0 < s) (has : a * s ≤ δ) (huL : a * s * L ≤ δ)
    (hδ : δ ≤ 1 / 50) : a + 10 * L * a < 1 / s / 4 := by
  rw [div_div, lt_div_iff₀ (by positivity)]; nlinarith

lemma aux_u (j0 n c δp z10 N0 : ℝ) (hj : j0 ≤ 2 * n) (hδp : 0 ≤ δp) (hc : δp = c * z10 / n)
    (hn : 0 < n) (hz : 0 ≤ z10) (hc0 : 0 ≤ c) :
    1 - (2 * c + N0 ^ 10) * z10 ≤ 1 - j0 * δp := by
  have h1 : j0 * δp ≤ 2 * n * δp := mul_le_mul_of_nonneg_right hj hδp
  have h2 : 2 * n * δp = 2 * c * z10 := by rw [hc]; field_simp
  have h3 : 0 ≤ N0 ^ 10 * z10 := mul_nonneg (by positivity) hz
  nlinarith


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

lemma Ecoef_abs_le {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ : ℝ)
    (hinc : Incoherent SV μ) (a b i j : Fin n) :
    |Ecoef SV a b i j| ≤ 2 * μ * r / n := by
  have hK : 0 ≤ 2 * μ * r / n :=
    le_trans (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
      (Ecoef_sq_le SV μ hinc a b)
  rw [Ecoef_self]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun y => Ecoef SV i j y.1 y.2) (fun y => Ecoef SV a b y.1 y.2)
  simp only [Fintype.sum_prod_type] at hcs
  have hA := Ecoef_sq_le SV μ hinc i j
  have hB := Ecoef_sq_le SV μ hinc a b
  have hsq : (∑ x, ∑ y, Ecoef SV i j x y * Ecoef SV a b x y) ^ 2 ≤
      (2 * μ * r / n) ^ 2 := by
    refine le_trans hcs ?_
    rw [sq]
    exact mul_le_mul hA hB (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => sq_nonneg _))) hK
  rw [← sq_abs] at hsq
  exact (sq_le_sq₀ (abs_nonneg _) hK).mp hsq

/-- The deviation `Z - q⁻¹ P_T P_Ω Z` for `Z ∈ T`, entrywise, as a Bernoulli sum. -/
lemma dev_entry {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Z : RealMatrix n n)
    (hZ : tangentProjection SV Z = Z) (q : ℝ) (Ω : Finset (Fin n × Fin n)) (a b : Fin n) :
    (Z - q⁻¹ • tangentProjection SV (samplingProjection Ω Z)) a b =
      ∑ y : Fin n × Fin n, Ecoef SV a b y.1 y.2 * Z y.1 y.2 *
        (1 - (if y ∈ Ω then 1 else 0) / q) := by
  have h1 : Z a b = ∑ i, ∑ j, Ecoef SV a b i j * Z i j := by
    have := tangent_entry SV Z a b
    rwa [hZ] at this
  have h2 := tangent_entry SV (samplingProjection Ω Z) a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [h2]
  rw [h1, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [samplingProjection]
  split_ifs <;> ring

/-! ## Bernstein-type tail for weighted centred Bernoulli sums -/

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

lemma mgf_eq {N : ℕ} (q θ : ℝ) (c : Fin N × Fin N → ℝ) :
    ∑ Ω : Finset (Fin N × Fin N), bernoulliObservationWeight q Ω *
        Real.exp (θ * ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) =
      ∏ x, (q * Real.exp (θ * (c x * (1 - 1 / q))) + (1 - q) * Real.exp (θ * c x)) := by
  rw [← sum_prod_ite]
  refine Finset.sum_congr rfl (fun Ω _ => ?_)
  rw [bw_eq_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  split_ifs <;> simp

lemma factor_le (q θ c : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (hθ : 0 ≤ θ) (hM : θ * |c| ≤ q) :
    q * Real.exp (θ * (c * (1 - 1 / q))) + (1 - q) * Real.exp (θ * c) ≤
      Real.exp (θ ^ 2 * c ^ 2 / q) := by
  have hy2 : |θ * c| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hθ]; linarith
  have hq' : 1 ≤ 1 / q := by rw [le_div_iff₀ hq0]; linarith
  have h1q : |1 - 1 / q| ≤ 1 / q := by
    rw [abs_le]; constructor <;> linarith
  have hy1 : |θ * (c * (1 - 1 / q))| ≤ 1 := by
    rw [show θ * (c * (1 - 1 / q)) = (θ * c) * (1 - 1 / q) by ring, abs_mul]
    calc |θ * c| * |1 - 1 / q| ≤ |θ * c| * (1 / q) :=
          mul_le_mul_of_nonneg_left h1q (abs_nonneg _)
      _ = (θ * |c|) / q := by rw [abs_mul, abs_of_nonneg hθ]; ring
      _ ≤ 1 := by rw [div_le_one hq0]; exact hM
  have e1 := Real.abs_exp_sub_one_sub_id_le hy1
  have e2 := Real.abs_exp_sub_one_sub_id_le hy2
  have f1 := (abs_le.mp e1).2
  have f2 := (abs_le.mp e2).2
  have key : q * (1 + θ * (c * (1 - 1 / q)) + (θ * (c * (1 - 1 / q))) ^ 2) +
      (1 - q) * (1 + θ * c + (θ * c) ^ 2) = 1 + θ ^ 2 * c ^ 2 * (1 - q) / q := by
    field_simp; ring
  have g1 := mul_le_mul_of_nonneg_left (show Real.exp (θ * (c * (1 - 1 / q))) ≤
    1 + θ * (c * (1 - 1 / q)) + (θ * (c * (1 - 1 / q))) ^ 2 by linarith) hq0.le
  have g2 := mul_le_mul_of_nonneg_left (show Real.exp (θ * c) ≤
    1 + θ * c + (θ * c) ^ 2 by linarith) (show (0 : ℝ) ≤ 1 - q by linarith)
  have g3 : θ ^ 2 * c ^ 2 * (1 - q) / q ≤ θ ^ 2 * c ^ 2 / q := by
    apply div_le_div_of_nonneg_right _ hq0.le
    have : 0 ≤ θ ^ 2 * c ^ 2 := by positivity
    nlinarith
  have g4 := Real.add_one_le_exp (θ ^ 2 * c ^ 2 / q)
  linarith

lemma tail_one {N : ℕ} (q θ t : ℝ) (c : Fin N × Fin N → ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hθ : 0 ≤ θ) (hM : ∀ x, θ * |c x| ≤ q) :
    bernoulliEventProb q (fun Ω => t ≤ ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) ≤
      Real.exp (-θ * t + θ ^ 2 * (∑ x, c x ^ 2) / q) := by
  have step1 : bernoulliEventProb q
      (fun Ω => t ≤ ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) ≤
      Real.exp (-θ * t) * ∑ Ω : Finset (Fin N × Fin N), bernoulliObservationWeight q Ω *
        Real.exp (θ * ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) := by
    unfold bernoulliEventProb
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Ω _ => ?_)
    have hw := bw_nonneg hq0.le hq1 Ω
    split_ifs with h
    · have h1 : 1 ≤ Real.exp (-θ * t) *
          Real.exp (θ * ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      nlinarith
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hw (Real.exp_pos _).le)
  rw [mgf_eq] at step1
  refine le_trans step1 ?_
  have hprod : ∏ x, (q * Real.exp (θ * (c x * (1 - 1 / q))) + (1 - q) * Real.exp (θ * c x)) ≤
      ∏ x, Real.exp (θ ^ 2 * c x ^ 2 / q) := by
    apply Finset.prod_le_prod
    · intro x _
      exact add_nonneg (mul_nonneg hq0.le (Real.exp_pos _).le)
        (mul_nonneg (by linarith) (Real.exp_pos _).le)
    · intro x _
      exact factor_le q θ (c x) hq0 hq1 hθ (hM x)
  calc _ ≤ Real.exp (-θ * t) * ∏ x, Real.exp (θ ^ 2 * c x ^ 2 / q) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-θ * t + θ ^ 2 * (∑ x, c x ^ 2) / q) := by
        rw [← Real.exp_sum, ← Real.exp_add]
        congr 1
        rw [Finset.mul_sum, Finset.sum_div]

lemma bep_union {N : ℕ} {ι : Type*} [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : Finset (Fin N × Fin N) → Prop) (G : ι → Finset (Fin N × Fin N) → Prop)
    (h : ∀ Ω, F Ω → ∃ i, G i Ω) :
    bernoulliEventProb p F ≤ ∑ i, bernoulliEventProb p (G i) := by
  unfold bernoulliEventProb
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun Ω _ => ?_)
  have hw := bw_nonneg hp0 hp1 Ω
  have hnn : ∀ i ∈ (Finset.univ : Finset ι),
      0 ≤ (if G i Ω then bernoulliObservationWeight p Ω else 0) := by
    intro i _; split_ifs <;> first | exact hw | exact le_refl _
  split_ifs with hF
  · obtain ⟨i, hi⟩ := h Ω hF
    calc bernoulliObservationWeight p Ω =
          (if G i Ω then bernoulliObservationWeight p Ω else 0) := by rw [if_pos hi]
      _ ≤ _ := Finset.single_le_sum hnn (Finset.mem_univ i)
  · exact Finset.sum_nonneg hnn

lemma bep_false {N : ℕ} (p : ℝ) (F : Finset (Fin N × Fin N) → Prop) (h : ∀ Ω, ¬ F Ω) :
    bernoulliEventProb p F = 0 := by
  unfold bernoulliEventProb
  exact Finset.sum_eq_zero (fun Ω _ => if_neg (h Ω))


/-! ## G31: entrywise concentration on `T` (CLMW Lemma 3.1, failure `2 n^-11`) -/

def G31 : Prop :=
  ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
    ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ : ℝ) (Z : RealMatrix n n)
      (ε ρ0 : ℝ),
      0 < n → Incoherent SV μ → tangentProjection SV Z = Z → 0 < ε → ε ≤ 1 →
      0 < ρ0 → ρ0 ≤ 1 → ρ0 ≥ C0 * ε⁻¹ ^ 2 * μ * r * Real.log n / n →
      bernoulliEventProb ρ0 (fun Ω =>
          entrySupNorm (Z - ρ0⁻¹ • tangentProjection SV (samplingProjection Ω Z)) ≤
            ε * entrySupNorm Z) ≥
        1 - c * (n : ℝ) ^ (-11 : ℤ)

lemma g31_exp (ε q K Zs S2 : ℝ) (hK : 0 < K) (hZs : 0 < Zs) (hq : 0 < q)
    (hS : S2 ≤ Zs ^ 2 * K) :
    -(ε * q / (2 * K * Zs)) * (ε * Zs) + (ε * q / (2 * K * Zs)) ^ 2 * S2 / q ≤
      -(ε ^ 2 * q / (4 * K)) := by
  have h1 : (ε * q / (2 * K * Zs)) ^ 2 * S2 / q ≤
      (ε * q / (2 * K * Zs)) ^ 2 * (Zs ^ 2 * K) / q := by
    apply div_le_div_of_nonneg_right _ hq.le
    exact mul_le_mul_of_nonneg_left hS (sq_nonneg _)
  have h2 : -(ε * q / (2 * K * Zs)) * (ε * Zs) +
      (ε * q / (2 * K * Zs)) ^ 2 * (Zs ^ 2 * K) / q = -(ε ^ 2 * q / (4 * K)) := by
    field_simp
    ring
  linarith

lemma g31_log (ε q μ r n : ℝ) (hn : 0 < n) (hμr : 0 < μ * r) (hε : 0 < ε)
    (hq : q ≥ 104 * ε⁻¹ ^ 2 * μ * r * Real.log n / n) :
    -(ε ^ 2 * q / (4 * (2 * μ * r / n))) ≤ -13 * Real.log n := by
  have e : ε ^ 2 * q / (4 * (2 * μ * r / n)) = ε ^ 2 * q * n / (8 * (μ * r)) := by
    field_simp
    ring
  rw [e]
  have hεn : (0 : ℝ) ≤ ε ^ 2 * n := by positivity
  have h0 := mul_le_mul_of_nonneg_left hq hεn
  have e2 : ε ^ 2 * n * (104 * ε⁻¹ ^ 2 * μ * r * Real.log n / n) =
      104 * (μ * r) * Real.log n := by
    field_simp
  have h1 : 104 * (μ * r) * Real.log n ≤ ε ^ 2 * q * n := by
    rw [← e2]; linarith
  have h2 : 13 * Real.log n ≤ ε ^ 2 * q * n / (8 * (μ * r)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

lemma count_pow (x : ℝ) (hx : 0 < x) :
    x * x * 2 * Real.exp (-13 * Real.log x) = 2 * x ^ (-11 : ℤ) := by
  rw [show (-13 : ℝ) * Real.log x = ((-13 : ℤ) : ℝ) * Real.log x by norm_num,
    ← Real.log_zpow, Real.exp_log (zpow_pos hx _)]
  have h : x ^ (2 : ℤ) * x ^ (-13 : ℤ) = x ^ (-11 : ℤ) := by
    rw [← zpow_add₀ hx.ne']; norm_num
  rw [← h, zpow_two]
  ring

lemma g31_core {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (μ ε q : ℝ)
    (Z : RealMatrix n n) (hn : 0 < n) (hinc : Incoherent SV μ)
    (hZ : tangentProjection SV Z = Z) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hcond : q ≥ 104 * ε⁻¹ ^ 2 * μ * r * Real.log n / n) :
    bernoulliEventProb q (fun Ω => ¬ entrySupNorm
        (Z - q⁻¹ • tangentProjection SV (samplingProjection Ω Z)) ≤ ε * entrySupNorm Z) ≤
      2 * (n : ℝ) ^ (-11 : ℤ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * μ * r / n := ⟨_, rfl⟩
  obtain ⟨Zs, hZsdef⟩ : ∃ Zs : ℝ, Zs = entrySupNorm Z := ⟨_, rfl⟩
  have hZs0 : 0 ≤ Zs := hZsdef ▸ entrySup_nonneg Z
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact le_trans (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
      (Ecoef_sq_le SV μ hinc ⟨0, hn⟩ ⟨0, hn⟩)
  have hEabs : ∀ a b i j, |Ecoef SV a b i j| ≤ K := by
    intro a b i j; rw [hKdef]; exact Ecoef_abs_le SV μ hinc a b i j
  have hEsq : ∀ a b, ∑ i, ∑ j, Ecoef SV a b i j ^ 2 ≤ K := by
    intro a b; rw [hKdef]; exact Ecoef_sq_le SV μ hinc a b
  have hZle : ∀ i j, |Z i j| ≤ Zs := by
    intro i j; rw [hZsdef]; exact le_entrySup Z i j
  have hcabs : ∀ (ab y : Fin n × Fin n),
      |Ecoef SV ab.1 ab.2 y.1 y.2 * Z y.1 y.2| ≤ K * Zs := by
    intro ab y
    rw [abs_mul]
    exact mul_le_mul (hEabs _ _ _ _) (hZle _ _) (abs_nonneg _) hK0
  have hcsq : ∀ ab : Fin n × Fin n,
      ∑ y : Fin n × Fin n, (Ecoef SV ab.1 ab.2 y.1 y.2 * Z y.1 y.2) ^ 2 ≤ Zs ^ 2 * K := by
    intro ab
    have h1 : ∀ y : Fin n × Fin n, (Ecoef SV ab.1 ab.2 y.1 y.2 * Z y.1 y.2) ^ 2 ≤
        Zs ^ 2 * Ecoef SV ab.1 ab.2 y.1 y.2 ^ 2 := by
      intro y
      rw [mul_pow, mul_comm (Zs ^ 2)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [← sq_abs (Z _ _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hZle _ _) 2
    calc ∑ y : Fin n × Fin n, (Ecoef SV ab.1 ab.2 y.1 y.2 * Z y.1 y.2) ^ 2
        ≤ ∑ y : Fin n × Fin n, Zs ^ 2 * Ecoef SV ab.1 ab.2 y.1 y.2 ^ 2 :=
          Finset.sum_le_sum (fun y _ => h1 y)
      _ = Zs ^ 2 * ∑ i, ∑ j, Ecoef SV ab.1 ab.2 i j ^ 2 := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type]
      _ ≤ Zs ^ 2 * K := mul_le_mul_of_nonneg_left (hEsq _ _) (sq_nonneg _)
  rcases (mul_nonneg hK0 hZs0).eq_or_lt with h0 | hpos
  · -- degenerate case: every coefficient vanishes
    rw [bep_false]
    · positivity
    intro Ω hΩ
    apply hΩ
    have hmul : 0 ≤ ε * entrySupNorm Z := mul_nonneg hε0.le (entrySup_nonneg Z)
    refine entrySup_le _ _ hmul (fun a b => ?_)
    rw [dev_entry SV Z hZ q Ω a b]
    have hz : ∀ y : Fin n × Fin n, Ecoef SV a b y.1 y.2 * Z y.1 y.2 = 0 := by
      intro y
      have := hcabs (a, b) y
      rw [← h0] at this
      exact abs_nonpos_iff.mp this
    simp only [hz, zero_mul, Finset.sum_const_zero, abs_zero]
    exact hmul
  · have hK : 0 < K := by
      rcases hK0.eq_or_lt with h | h
      · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have hZs : 0 < Zs := by
      rcases hZs0.eq_or_lt with h | h
      · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have hμr : 0 < μ * r := by
      have h := mul_pos hK hnR
      rw [hKdef, div_mul_cancel₀ _ hnR.ne'] at h
      linarith
    obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ε * q / (2 * K * Zs) := ⟨_, rfl⟩
    have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
    have himp : ∀ Ω : Finset (Fin n × Fin n), ¬ entrySupNorm
        (Z - q⁻¹ • tangentProjection SV (samplingProjection Ω Z)) ≤ ε * entrySupNorm Z →
        ∃ i : (Fin n × Fin n) × Bool, ε * Zs ≤ ∑ y : Fin n × Fin n,
          ((if i.2 then 1 else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)) *
            (1 - (if y ∈ Ω then 1 else 0) / q) := by
      intro Ω hΩ
      by_contra hno
      push Not at hno
      apply hΩ
      rw [← hZsdef]
      refine entrySup_le _ _ (by positivity) (fun a b => ?_)
      rw [dev_entry SV Z hZ q Ω a b, abs_le]
      have h1 := hno ((a, b), true)
      have h2 := hno ((a, b), false)
      simp only [if_true, one_mul, Bool.false_eq_true, if_false, neg_one_mul, neg_mul,
        Finset.sum_neg_distrib] at h1 h2
      constructor <;> linarith
    have htail : ∀ i : (Fin n × Fin n) × Bool, bernoulliEventProb q (fun Ω =>
        ε * Zs ≤ ∑ y : Fin n × Fin n,
          ((if i.2 then 1 else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)) *
            (1 - (if y ∈ Ω then 1 else 0) / q)) ≤ Real.exp (-13 * Real.log n) := by
      intro i
      have hM : ∀ y : Fin n × Fin n,
          θ * |(if i.2 then 1 else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)| ≤ q := by
        intro y
        have hs : |(if i.2 then (1 : ℝ) else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)| =
            |Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2| := by
          split_ifs <;> simp
        rw [hs]
        calc θ * |Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2| ≤ θ * (K * Zs) :=
              mul_le_mul_of_nonneg_left (hcabs _ _) hθ0
          _ = ε * q / 2 := by rw [hθdef]; field_simp
          _ ≤ q := by nlinarith
      refine le_trans (tail_one q θ (ε * Zs) _ hq0 hq1 hθ0 hM) ?_
      apply Real.exp_le_exp.mpr
      have hsq : ∑ y : Fin n × Fin n,
          ((if i.2 then (1 : ℝ) else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)) ^ 2 =
          ∑ y : Fin n × Fin n, (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2) ^ 2 := by
        refine Finset.sum_congr rfl (fun y _ => ?_); split_ifs <;> ring
      rw [hsq]
      have e1 := g31_exp ε q K Zs _ hK hZs hq0 (hcsq i.1)
      have e2 := g31_log ε q μ r n hnR hμr hε0 hcond
      rw [← hKdef] at e2
      rw [hθdef]
      linarith
    calc _ ≤ ∑ i : (Fin n × Fin n) × Bool, bernoulliEventProb q (fun Ω =>
          ε * Zs ≤ ∑ y : Fin n × Fin n,
            ((if i.2 then 1 else -1) * (Ecoef SV i.1.1 i.1.2 y.1 y.2 * Z y.1 y.2)) *
              (1 - (if y ∈ Ω then 1 else 0) / q)) := bep_union hq0.le hq1 _ _ himp
      _ ≤ ∑ _i : (Fin n × Fin n) × Bool, Real.exp (-13 * Real.log n) :=
          Finset.sum_le_sum (fun i _ => htail i)
      _ = 2 * (n : ℝ) ^ (-11 : ℤ) := by
          rw [Finset.sum_const, Finset.card_univ]
          simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
          push_cast
          exact count_pow _ hnR

theorem g31 : G31 := by
  refine ⟨104, 2, by norm_num, by norm_num, ?_⟩
  intro n r L0 SV μ Z ε ρ0 hn hinc hZ hε0 hε1 hρ0 hρ1 hcond
  have h := g31_core SV μ ε ρ0 Z hn hinc hZ hε0 hε1 hρ0 hρ1 hcond
  rw [bep_not] at h
  linarith


/-! ## G32 in the dense regime: spectral norm of `Z - q⁻¹ P_Ω Z` via a net + Hoeffding -/

def G32d : Prop :=
  ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧
    ∀ (n : ℕ) (Z : RealMatrix n n) (ρ0 : ℝ),
      0 < n → 0 < ρ0 → ρ0 ≤ 1 → 1 ≤ ρ0 * (2 * Real.log n + 3) →
      bernoulliEventProb ρ0 (fun Ω =>
          MatrixCompletion.spectralNorm (Z - ρ0⁻¹ • samplingProjection Ω Z) ≤
            C1 * Real.sqrt (n * Real.log n / ρ0) * entrySupNorm Z) ≥
        1 - c * (n : ℝ) ^ (-11 : ℤ)

lemma tail_hoeff {N : ℕ} (q θ t : ℝ) (c : Fin N × Fin N → ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hθ : 0 < θ) :
    bernoulliEventProb q (fun Ω => t ≤ ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) ≤
      Real.exp (-θ * t + θ ^ 2 * (∑ x, c x ^ 2) / (8 * q ^ 2)) := by
  have step1 : bernoulliEventProb q
      (fun Ω => t ≤ ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) ≤
      Real.exp (-θ * t) * ∑ Ω : Finset (Fin N × Fin N), bernoulliObservationWeight q Ω *
        Real.exp (θ * ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) := by
    unfold bernoulliEventProb
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Ω _ => ?_)
    have hw := bw_nonneg hq0.le hq1 Ω
    split_ifs with h
    · have h1 : 1 ≤ Real.exp (-θ * t) *
          Real.exp (θ * ∑ x, c x * (1 - (if x ∈ Ω then 1 else 0) / q)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      nlinarith
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hw (Real.exp_pos _).le)
  rw [mgf_eq] at step1
  refine le_trans step1 ?_
  have hprod : ∏ x, (q * Real.exp (θ * (c x * (1 - 1 / q))) + (1 - q) * Real.exp (θ * c x)) ≤
      ∏ x, Real.exp (θ ^ 2 * c x ^ 2 / (8 * q ^ 2)) := by
    apply Finset.prod_le_prod
    · intro x _
      exact add_nonneg (mul_nonneg hq0.le (Real.exp_pos _).le)
        (mul_nonneg (by linarith) (Real.exp_pos _).le)
    · intro x _
      exact hoeff_two q θ (c x) hq0 hq1 hθ
  calc _ ≤ Real.exp (-θ * t) * ∏ x, Real.exp (θ ^ 2 * c x ^ 2 / (8 * q ^ 2)) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-θ * t + θ ^ 2 * (∑ x, c x ^ 2) / (8 * q ^ 2)) := by
        rw [← Real.exp_sum, ← Real.exp_add]
        congr 1
        rw [Finset.mul_sum, Finset.sum_div]

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

lemma bil_dev {n : ℕ} (Z : RealMatrix n n) (q : ℝ) (Ω : Finset (Fin n × Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x ((LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (Z - q⁻¹ • samplingProjection Ω Z))) y) =
      ∑ p : Fin n × Fin n, (x p.1 * Z p.1 p.2 * y p.2) *
        (1 - (if p ∈ Ω then 1 else 0) / q) := by
  rw [bil_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, samplingProjection]
  split_ifs <;> ring

lemma euc_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ∑ i, x i ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])

lemma coef_sq_le {n : ℕ} (Z : RealMatrix n n) (Zs : ℝ) (hZ : ∀ i j, |Z i j| ≤ Zs)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∑ p : Fin n × Fin n, (x p.1 * Z p.1 p.2 * y p.2) ^ 2 ≤ Zs ^ 2 := by
  have h1 : ∀ p : Fin n × Fin n, (x p.1 * Z p.1 p.2 * y p.2) ^ 2 ≤
      Zs ^ 2 * (x p.1 ^ 2 * y p.2 ^ 2) := by
    intro p
    have hz : Z p.1 p.2 ^ 2 ≤ Zs ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hZ _ _) 2
    have : 0 ≤ x p.1 ^ 2 * y p.2 ^ 2 := by positivity
    calc (x p.1 * Z p.1 p.2 * y p.2) ^ 2 = Z p.1 p.2 ^ 2 * (x p.1 ^ 2 * y p.2 ^ 2) := by ring
      _ ≤ Zs ^ 2 * (x p.1 ^ 2 * y p.2 ^ 2) := mul_le_mul_of_nonneg_right hz this
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hy2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
  calc ∑ p : Fin n × Fin n, (x p.1 * Z p.1 p.2 * y p.2) ^ 2
      ≤ ∑ p : Fin n × Fin n, Zs ^ 2 * (x p.1 ^ 2 * y p.2 ^ 2) := Finset.sum_le_sum (fun p _ => h1 p)
    _ = Zs ^ 2 * ((∑ i, x i ^ 2) * ∑ j, y j ^ 2) := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_mul_sum]
    _ = Zs ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2) := by rw [euc_sq, euc_sq]
    _ ≤ Zs ^ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]
    _ = Zs ^ 2 := mul_one _

lemma g32_exp (q t Zs S : ℝ) (hq : 0 < q) (hZs : 0 < Zs) (hS : S ≤ Zs ^ 2) :
    -(4 * q ^ 2 * t / Zs ^ 2) * t + (4 * q ^ 2 * t / Zs ^ 2) ^ 2 * S / (8 * q ^ 2) ≤
      -(2 * q ^ 2 * t ^ 2 / Zs ^ 2) := by
  have h1 : (4 * q ^ 2 * t / Zs ^ 2) ^ 2 * S / (8 * q ^ 2) ≤
      (4 * q ^ 2 * t / Zs ^ 2) ^ 2 * Zs ^ 2 / (8 * q ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hS (sq_nonneg _)
  have h2 : -(4 * q ^ 2 * t / Zs ^ 2) * t + (4 * q ^ 2 * t / Zs ^ 2) ^ 2 * Zs ^ 2 / (8 * q ^ 2) =
      -(2 * q ^ 2 * t ^ 2 / Zs ^ 2) := by
    field_simp
    ring
  linarith

lemma g32_val (n q Zs : ℝ) (hn : 3 ≤ n) (hq0 : 0 < q) (hZs : 0 < Zs)
    (hq : 1 ≤ q * (2 * Real.log n + 3)) :
    -(2 * q ^ 2 * (8 * Real.sqrt (n * Real.log n / q) * Zs) ^ 2 / Zs ^ 2) ≤ -(25 * n) := by
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hnl : 0 ≤ n * Real.log n / q := by positivity
  have e : 2 * q ^ 2 * (8 * Real.sqrt (n * Real.log n / q) * Zs) ^ 2 / Zs ^ 2 =
      128 * (q * n * Real.log n) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hnl]
    field_simp
    norm_num
  rw [e]
  have h1 : n ≤ 5 * (q * n * Real.log n) := by
    have h2 : 2 * Real.log n + 3 ≤ 5 * Real.log n := by linarith
    have h3 : 1 ≤ q * (5 * Real.log n) := le_trans hq (mul_le_mul_of_nonneg_left h2 hq0.le)
    nlinarith
  linarith

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


lemma bep_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Finset (Fin N × Fin N) → Prop) :
    0 ≤ bernoulliEventProb p F := by
  unfold bernoulliEventProb
  refine Finset.sum_nonneg (fun Ω _ => ?_)
  split_ifs
  · exact bw_nonneg hp0 hp1 Ω
  · exact le_refl 0

lemma g32_core {n : ℕ} (Z : RealMatrix n n) (q : ℝ) (hn : 3 ≤ n) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hq : 1 ≤ q * (2 * Real.log n + 3)) :
    bernoulliEventProb q (fun Ω => ¬ MatrixCompletion.spectralNorm
        (Z - q⁻¹ • samplingProjection Ω Z) ≤
        16 * Real.sqrt (n * Real.log n / q) * entrySupNorm Z) ≤ (n : ℝ) ^ (-11 : ℤ) := by
  have hn0 : 0 < n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  obtain ⟨Zs, hZsdef⟩ : ∃ Zs : ℝ, Zs = entrySupNorm Z := ⟨_, rfl⟩
  have hZs0 : 0 ≤ Zs := hZsdef ▸ entrySup_nonneg Z
  have hZle : ∀ i j, |Z i j| ≤ Zs := by intro i j; rw [hZsdef]; exact le_entrySup Z i j
  rcases hZs0.eq_or_lt with h0 | hZs
  · rw [bep_false]
    · positivity
    intro Ω hΩ
    apply hΩ
    have hZ0 : Z = 0 := by
      ext i j
      have := hZle i j
      rw [← h0] at this
      exact abs_nonpos_iff.mp this
    have hS : samplingProjection Ω Z = 0 := by
      rw [hZ0]; ext i j; simp [samplingProjection]
    rw [hS, smul_zero, sub_zero, hZ0, spectral_zero, entrySup_zero, mul_zero]
  · obtain ⟨N, hN1, hcov, hcard⟩ := net_exists hn0
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = 8 * Real.sqrt (n * Real.log n / q) * Zs := ⟨_, rfl⟩
    have htpos : 0 < t := by
      rw [htdef]
      have : 0 < Real.sqrt (n * Real.log n / q) := Real.sqrt_pos.mpr (by positivity)
      positivity
    have himp : ∀ Ω : Finset (Fin n × Fin n), ¬ MatrixCompletion.spectralNorm
        (Z - q⁻¹ • samplingProjection Ω Z) ≤
          16 * Real.sqrt (n * Real.log n / q) * entrySupNorm Z →
        ∃ i : N × N, t ≤ ∑ p : Fin n × Fin n,
          ((i.1 : EuclideanSpace ℝ (Fin n)) p.1 * Z p.1 p.2 *
            (i.2 : EuclideanSpace ℝ (Fin n)) p.2) * (1 - (if p ∈ Ω then 1 else 0) / q) := by
      intro Ω hΩ
      by_contra hno
      push Not at hno
      apply hΩ
      have hb := opNorm_le_net (LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (Z - q⁻¹ • samplingProjection Ω Z))) N hN1 hcov t
        (fun x hx y hy => by rw [bil_dev]; exact (hno ⟨⟨x, hx⟩, ⟨y, hy⟩⟩).le)
      rw [← hZsdef]
      unfold MatrixCompletion.spectralNorm
      rw [htdef] at hb
      linarith
    have htail : ∀ i : N × N, bernoulliEventProb q (fun Ω => t ≤ ∑ p : Fin n × Fin n,
          ((i.1 : EuclideanSpace ℝ (Fin n)) p.1 * Z p.1 p.2 *
            (i.2 : EuclideanSpace ℝ (Fin n)) p.2) * (1 - (if p ∈ Ω then 1 else 0) / q)) ≤
        Real.exp (-(25 * n)) := by
      intro i
      have hθ : 0 < 4 * q ^ 2 * t / Zs ^ 2 := by positivity
      refine le_trans (tail_hoeff q _ t _ hq0 hq1 hθ) ?_
      apply Real.exp_le_exp.mpr
      have e1 := g32_exp q t Zs _ hq0 hZs
        (coef_sq_le Z Zs hZle i.1 i.2 (hN1 _ i.1.2) (hN1 _ i.2.2))
      have e2 := g32_val n q Zs hnR hq0 hZs hq
      rw [← htdef] at e2
      beta_reduce
      linarith
    calc _ ≤ ∑ i : N × N, bernoulliEventProb q (fun Ω => t ≤ ∑ p : Fin n × Fin n,
          ((i.1 : EuclideanSpace ℝ (Fin n)) p.1 * Z p.1 p.2 *
            (i.2 : EuclideanSpace ℝ (Fin n)) p.2) * (1 - (if p ∈ Ω then 1 else 0) / q)) :=
          bep_union hq0.le hq1 _ _ himp
      _ ≤ ∑ _i : N × N, Real.exp (-(25 * n)) := Finset.sum_le_sum (fun i _ => htail i)
      _ = (N.card : ℝ) ^ 2 * Real.exp (-(25 * n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
            nsmul_eq_mul]
          push_cast
          ring
      _ ≤ (n : ℝ) ^ (-11 : ℤ) :=
          g32_count n N.card (by positivity) (by positivity)
            (by rw [Nat.floor_natCast]; exact hcard) (by rw [Nat.floor_natCast])

theorem g32 : G32d := by
  refine ⟨16, 2048, by norm_num, by norm_num, ?_⟩
  intro n Z ρ0 hn hρ0 hρ1 hq
  rcases lt_or_ge n 3 with hsmall | hbig
  · have hnR : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : 1 ≤ 2048 * (n : ℝ) ^ (-11 : ℤ) := by
      rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      calc (n : ℝ) ^ 11 ≤ 2 ^ 11 := pow_le_pow_left₀ hnpos.le hnR 11
        _ = 2048 := by norm_num
    rw [ge_iff_le]
    exact le_trans (by linarith) (bep_nonneg hρ0.le hρ1 _)
  · have h := g32_core Z ρ0 hbig hρ0 hρ1 hq
    rw [bep_not] at h
    have : 0 ≤ (n : ℝ) ^ (-11 : ℤ) := by positivity
    linarith


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

/-! ## G26 by transfer from Candes-Recht Thm 4.1 (Proved 5768a99b): rate sandwich + monotone coupling
 + polarization. -/

/-- The statement of 5768a99b `candes_recht_theorem41_bernoulli_tangent_sampling_concentration`. -/
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

def G26h : Prop :=
  ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
    ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ρ0 : ℝ),
      0 < n → Incoherent SV μ → 0 < ρ0 → ρ0 ≤ 1 → 15 ≤ ρ0 * ((n : ℝ) * n) →
      ρ0 ≥ C0 * μ * r * Real.log n / n →
      bernoulliEventProb ρ0 (fun Ω => ∀ X : RealMatrix n n,
          frobeniusNorm (tangentProjection SV X -
            ρ0⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
            (3 / 5) * frobeniusNorm X) ≥
        1 - c * (n : ℝ) ^ (-11 : ℤ)

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

noncomputable def wf {n : ℕ} (Ω : Finset (Fin n × Fin n)) (ρ : ℝ) (i j : Fin n) : ℝ :=
  1 - ρ⁻¹ * (if (i, j) ∈ Ω then 1 else 0)

lemma B_eq {n : ℕ} (Ω : Finset (Fin n × Fin n)) (ρ : ℝ) (U V : RealMatrix n n) :
    matrixInner U V - ρ⁻¹ * matrixInner U (samplingProjection Ω V) =
      ∑ i, ∑ j, wf Ω ρ i j * V i j * U i j := by
  unfold matrixInner samplingProjection
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold wf
  split_ifs <;> ring

lemma Q_eq {n : ℕ} (Ω : Finset (Fin n × Fin n)) (ρ : ℝ) (W : RealMatrix n n) :
    frobeniusNormSq W - ρ⁻¹ * matrixInner W (samplingProjection Ω W) =
      ∑ i, ∑ j, wf Ω ρ i j * W i j ^ 2 := by
  rw [frobSq_eq_inner, B_eq]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

lemma dsum_lin {n : ℕ} (f g h : Fin n → Fin n → ℝ) (a b : ℝ)
    (H : ∀ i j, f i j = a * g i j + b * h i j) :
    ∑ i, ∑ j, f i j = a * ∑ i, ∑ j, g i j + b * ∑ i, ∑ j, h i j := by
  simp only [H, Finset.sum_add_distrib, Finset.mul_sum]

lemma dsum_lin3 {n : ℕ} (f g h k : Fin n → Fin n → ℝ) (a b c : ℝ)
    (H : ∀ i j, f i j = a * g i j + b * h i j + c * k i j) :
    ∑ i, ∑ j, f i j = a * ∑ i, ∑ j, g i j + b * ∑ i, ∑ j, h i j + c * ∑ i, ∑ j, k i j := by
  simp only [H, Finset.sum_add_distrib, Finset.mul_sum]

lemma polar {n : ℕ} (w : Fin n → Fin n → ℝ) (Y Z : RealMatrix n n) (κ : ℝ) (hκ : 0 < κ)
    (hp : |∑ i, ∑ j, w i j * (Y + κ⁻¹ • Z) i j ^ 2| ≤ κ * frobeniusNormSq (Y + κ⁻¹ • Z))
    (hm : |∑ i, ∑ j, w i j * (Y - κ⁻¹ • Z) i j ^ 2| ≤ κ * frobeniusNormSq (Y - κ⁻¹ • Z))
    (hZ : frobeniusNormSq Z = ∑ i, ∑ j, w i j * Y i j * Z i j) :
    frobeniusNormSq Z ≤ κ ^ 2 * frobeniusNormSq Y := by
  set t := κ⁻¹ with ht_def
  have ht : κ * t = 1 := mul_inv_cancel₀ hκ.ne'
  have e1 : ∑ i, ∑ j, w i j * (Y + t • Z) i j ^ 2 =
      1 * ∑ i, ∑ j, w i j * (Y - t • Z) i j ^ 2 + (4 * t) * ∑ i, ∑ j, w i j * Y i j * Z i j :=
    dsum_lin _ _ _ _ _ (fun i j => by
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring)
  have e2 : frobeniusNormSq (Y + t • Z) =
      2 * frobeniusNormSq Y + (2 * t ^ 2) * frobeniusNormSq Z +
        (-1) * frobeniusNormSq (Y - t • Z) := by
    unfold frobeniusNormSq
    exact dsum_lin3 _ _ _ _ _ _ _ (fun i j => by
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring)
  have a1 := (abs_le.mp hp).2
  have a2 := (abs_le.mp hm).1
  rw [← hZ] at e1
  have h3 : 4 * t * frobeniusNormSq Z ≤
      κ * (2 * frobeniusNormSq Y + 2 * t ^ 2 * frobeniusNormSq Z) := by
    have : κ * frobeniusNormSq (Y + t • Z) + κ * frobeniusNormSq (Y - t • Z) =
        κ * (2 * frobeniusNormSq Y + 2 * t ^ 2 * frobeniusNormSq Z) := by
      rw [e2]; ring
    linarith
  have h4 : κ * (2 * frobeniusNormSq Y + 2 * t ^ 2 * frobeniusNormSq Z) =
      2 * κ * frobeniusNormSq Y + 2 * t * frobeniusNormSq Z := by
    have : κ * (2 * frobeniusNormSq Y + 2 * t ^ 2 * frobeniusNormSq Z) =
        2 * κ * frobeniusNormSq Y + 2 * (κ * t) * t * frobeniusNormSq Z := by ring
    rw [this, ht]; ring
  have h5 : t * frobeniusNormSq Z ≤ κ * frobeniusNormSq Y := by linarith
  have h6 : κ * (t * frobeniusNormSq Z) ≤ κ * (κ * frobeniusNormSq Y) :=
    mul_le_mul_of_nonneg_left h5 hκ.le
  rw [← mul_assoc, ht, one_mul] at h6
  rw [sq]; linarith

lemma qbound (F I a b ρ κ : ℝ) (hρ : 0 < ρ) (hF : 0 ≤ F) (ha : a * F ≤ I) (hb : I ≤ b * F)
    (ha' : (1 - κ) * ρ ≤ a) (hb' : b ≤ (1 + κ) * ρ) :
    |F - ρ⁻¹ * I| ≤ κ * F := by
  have h1 : ρ⁻¹ * I ≤ (1 + κ) * F := by
    rw [inv_mul_le_iff₀ hρ]; nlinarith [mul_le_mul_of_nonneg_right hb' hF]
  have h2 : (1 - κ) * F ≤ ρ⁻¹ * I := by
    rw [le_inv_mul_iff₀ hρ]; nlinarith [mul_le_mul_of_nonneg_right ha' hF]
  rw [abs_le]; constructor <;> linarith

lemma det26 {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (Ω : Finset (Fin n × Fin n))
    (ρ a b : ℝ) (hρ : 0 < ρ) (hlo : LoEv SV a Ω) (hup : UpEv SV b Ω)
    (ha' : (1 - 3 / 5) * ρ ≤ a) (hb' : b ≤ (1 + 3 / 5) * ρ) (X : RealMatrix n n) :
    frobeniusNorm (tangentProjection SV X -
      ρ⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
      (3 / 5) * frobeniusNorm X := by
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = tangentProjection SV X := ⟨_, rfl⟩
  have hYT : tangentProjection SV Y = Y := by rw [hYdef, tangent_idem]
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = Y - ρ⁻¹ • tangentProjection SV (samplingProjection Ω Y) :=
    ⟨_, rfl⟩
  rw [← hYdef, ← hZdef]
  have hZT : tangentProjection SV Z = Z := by
    rw [hZdef, tangent_sub, tangent_smul, tangent_idem, hYT]
  have hQ : ∀ W : RealMatrix n n, tangentProjection SV W = W →
      |∑ i, ∑ j, wf Ω ρ i j * W i j ^ 2| ≤ (3 / 5) * frobeniusNormSq W := by
    intro W hW
    rw [← Q_eq]
    exact qbound _ _ a b ρ (3 / 5) hρ (frobSq_nonneg W) (hlo W hW) (hup W hW) ha' hb'
  have hκ : (0 : ℝ) < 3 / 5 := by norm_num
  have hWp : tangentProjection SV (Y + (3 / 5 : ℝ)⁻¹ • Z) = Y + (3 / 5 : ℝ)⁻¹ • Z := by
    rw [tangent_add, tangent_smul, hYT, hZT]
  have hWm : tangentProjection SV (Y - (3 / 5 : ℝ)⁻¹ • Z) = Y - (3 / 5 : ℝ)⁻¹ • Z := by
    rw [tangent_sub, tangent_smul, hYT, hZT]
  have hZZ : frobeniusNormSq Z = ∑ i, ∑ j, wf Ω ρ i j * Y i j * Z i j := by
    have e0 : matrixInner Z (Y - ρ⁻¹ • tangentProjection SV (samplingProjection Ω Y)) =
        matrixInner Z Y - ρ⁻¹ * matrixInner Z (samplingProjection Ω Y) := by
      rw [inner_sub_smul, inner_T_right SV _ _ hZT]
    rw [frobSq_eq_inner]
    nth_rewrite 2 [hZdef]
    rw [e0, B_eq]
  have hmain := polar (wf Ω ρ) Y Z (3 / 5) hκ (hQ _ hWp) (hQ _ hWm) hZZ
  have hfY := frob_T_le SV X
  rw [← hYdef] at hfY
  have hZ0 := frob_nonneg' Z
  have hY0 := frob_nonneg' Y
  have hsq : frobeniusNorm Z ^ 2 ≤ (3 / 5 * frobeniusNorm Y) ^ 2 := by
    rw [frob_sq, mul_pow, frob_sq]; exact hmain
  have hZY : frobeniusNorm Z ≤ 3 / 5 * frobeniusNorm Y :=
    (pow_le_pow_iff_left₀ hZ0 (by positivity) (by norm_num)).mp hsq
  linarith

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

theorem g26 (h41 : T41) : G26h := by
  obtain ⟨C, c, hC, hc, H⟩ := h41
  refine ⟨12 * C, 2 * c, by positivity, by positivity, ?_⟩
  intro n r L0 SV μ ρ hn hinc hρ0 hρ1 h15 hrate
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : 0 ≤ (n : ℝ) ^ (-11 : ℤ) := zpow_nonneg hnR.le _
  rcases Nat.eq_zero_or_pos r with hr | hr
  · -- rank zero: the tangent space is trivial
    subst hr
    have hT : ∀ X : RealMatrix n n, tangentProjection SV X = 0 := by
      intro X; rw [tangent_eq]; ext i j; simp [PU, PV, projM, Matrix.mul_apply]
    have hall : bernoulliEventProb ρ (fun Ω => ∀ X : RealMatrix n n,
          frobeniusNorm (tangentProjection SV X -
            ρ⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
            (3 / 5) * frobeniusNorm X) = 1 := by
      unfold bernoulliEventProb
      rw [← bw_sum_one (N := n) ρ]
      refine Finset.sum_congr rfl (fun B _ => if_pos (fun X => ?_))
      simp only [hT, smul_zero, sub_zero]
      have : frobeniusNorm (0 : RealMatrix n n) = 0 := by
        simp [frobeniusNorm, frobeniusNormSq]
      rw [this]; have := frob_nonneg' X; linarith
    rw [hall]; have := mul_nonneg hc.le hz; linarith
  have hμ := mu_ge_one SV μ hn hr hinc
  have hA0 := A0_of_inc SV μ hn hr hinc
  have hA1 := A1_of_inc SV μ hμ hinc
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  set N : ℝ := (n : ℝ) * n with hN
  have hNpos : 0 < N := by positivity
  set x : ℝ := ρ * N with hx
  have hx0 : 0 ≤ x := by positivity
  have hxN : x ≤ N := by rw [hx]; nlinarith [hρ1, hNpos]
  set K : ℝ := C * μ * n * r * Real.log n with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ C * μ * n * r :=
      mul_nonneg (mul_nonneg (mul_nonneg hC.le (by linarith)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    exact mul_nonneg this hlog
  have hxK : 12 * K ≤ x := by
    have e : 12 * C * μ * r * Real.log n / n * N = 12 * K := by
      rw [hN, hK]; first | (field_simp; ring) | field_simp
    have := mul_le_mul_of_nonneg_right hrate hNpos.le
    rw [e] at this; rw [hx]; linarith
  set m1 := ⌊x⌋₊ with hm1
  set m2 := ⌈x⌉₊ with hm2
  have hm1le : (m1 : ℝ) ≤ x := Nat.floor_le hx0
  have hm1gt : x - 1 < m1 := Nat.sub_one_lt_floor x
  have hm2ge : x ≤ m2 := Nat.le_ceil x
  have hm2lt : (m2 : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hm2N : m2 ≤ n * n := by
    rw [hm2]; apply Nat.ceil_le.mpr; push_cast; linarith [hxN, hN]
  have hm1N : m1 ≤ n * n := le_trans (Nat.floor_le_ceil x) hm2N
  have hcast : ∀ m : ℕ, (m : ℝ) / ((n : ℝ) * (n : ℝ)) = (m : ℝ) / N := fun m => by rw [hN]
  set p1 : ℝ := (m1 : ℝ) / N with hp1
  set p2 : ℝ := (m2 : ℝ) / N with hp2
  have hp10 : 0 ≤ p1 := by positivity
  have hp1ρ : p1 ≤ ρ := by rw [hp1, div_le_iff₀ hNpos]; linarith [hm1le, hx]
  have hρp2 : ρ ≤ p2 := by rw [hp2, le_div_iff₀ hNpos]; linarith [hm2ge, hx]
  have hp21 : p2 ≤ 1 := by
    have : (m2 : ℝ) ≤ (n : ℝ) * n := by exact_mod_cast hm2N
    rw [hp2, div_le_one hNpos]; linarith [hN]
  have hp1lo : (1 - 3 / 5) * ρ ≤ p1 / 2 := by
    have h8 : (4 / 5) * x ≤ m1 := by linarith
    have : (4 / 5) * ρ ≤ p1 := by rw [hp1, le_div_iff₀ hNpos]; rw [hx] at h8; linarith
    linarith
  have hp2up : 3 * p2 / 2 ≤ (1 + 3 / 5) * ρ := by
    have h9 : (m2 : ℝ) ≤ (16 / 15) * x := by linarith
    have : p2 ≤ (16 / 15) * ρ := by rw [hp2, div_le_iff₀ hNpos]; rw [hx] at h9; linarith
    linarith
  have hmaxR : ((max n n : ℕ) : ℝ) = n := by rw [max_self]
  have hcond : ∀ m : ℕ, (m : ℝ) ≥ 11 * K →
      (m : ℝ) ≥ C * μ * (↑(max n n)) * (r : ℝ) * (11 * Real.log (↑(max n n))) := by
    intro m hm
    rw [hmaxR]
    have : C * μ * (n : ℝ) * r * (11 * Real.log n) = 11 * K := by rw [hK]; ring
    rw [this]; exact hm
  have hz' : Real.rpow (↑(max n n) : ℝ) (-11) = (n : ℝ) ^ (-11 : ℤ) := by
    rw [hmaxR, rpow_eq_zpow11]
  have T1 := H C le_rfl 11 (by norm_num) n n r m1 L0 μ μ SV hn hn hr hm1N hμ hμ hA0 hA1
    (hcond m1 (by linarith))
  have T2 := H C le_rfl 11 (by norm_num) n n r m2 L0 μ μ SV hn hn hr hm2N hμ hμ hA0 hA1
    (hcond m2 (by linarith))
  rw [hz', hcast] at T1 T2
  -- lower event at rate p1, upper event at rate p2
  have hp20 : 0 ≤ p2 := le_trans hp10 (le_trans hp1ρ hρp2)
  have L1 : bernoulliEventProb p1 (LoEv SV (p1 / 2)) ≥ 1 - c * (n : ℝ) ^ (-11 : ℤ) :=
    le_trans T1 (bep_mono (N := n) hp10 (le_trans hp1ρ hρ1)
      (fun Omega => TangentSamplingConcentration Omega SV p1 ((1 : ℝ) / 2)) (LoEv SV (p1 / 2))
      (fun B hB => (tsc_bounds SV B p1 hp10 hB).1))
  have U2 : bernoulliEventProb p2 (UpEv SV (3 * p2 / 2)) ≥ 1 - c * (n : ℝ) ^ (-11 : ℤ) :=
    le_trans T2 (bep_mono (N := n) hp20 hp21
      (fun Omega => TangentSamplingConcentration Omega SV p2 ((1 : ℝ) / 2)) (UpEv SV (3 * p2 / 2))
      (fun B hB => (tsc_bounds SV B p2 hp20 hB).2))
  have hLmono : ∀ Ω Ω' : Finset (Fin n × Fin n), Ω ⊆ Ω' →
      LoEv SV (p1 / 2) Ω → LoEv SV (p1 / 2) Ω' :=
    fun Ω Ω' h hL X hX => le_trans (hL X hX) (inner_samp_mono h X)
  have hUmono : ∀ Ω Ω' : Finset (Fin n × Fin n), Ω ⊆ Ω' →
      (¬ UpEv SV (3 * p2 / 2) Ω) → ¬ UpEv SV (3 * p2 / 2) Ω' :=
    fun Ω Ω' h hU hU' => hU (fun X hX => le_trans (inner_samp_mono h X) (hU' X hX))
  have FL := ctamp_fail_antitone p1 ρ hp10 hp1ρ hρ1 (LoEv SV (p1 / 2)) hLmono
  have FU := ctamp_fail_antitone ρ p2 hρ0.le hρp2 hp21
    (fun Ω => ¬ UpEv SV (3 * p2 / 2) Ω) hUmono
  have nL1 := bep_not (N := n) p1 (LoEv SV (p1 / 2))
  have nLρ := bep_not (N := n) ρ (LoEv SV (p1 / 2))
  have nU2 := bep_not (N := n) p2 (fun Ω => ¬ UpEv SV (3 * p2 / 2) Ω)
  have nUρ := bep_not (N := n) ρ (fun Ω => ¬ UpEv SV (3 * p2 / 2) Ω)
  have nU2' := bep_not (N := n) p2 (UpEv SV (3 * p2 / 2))
  have hand := bep_not_and2 (N := n) hρ0.le hρ1 (LoEv SV (p1 / 2)) (UpEv SV (3 * p2 / 2))
  have nand := bep_not (N := n) ρ (fun Ω => LoEv SV (p1 / 2) Ω ∧ UpEv SV (3 * p2 / 2) Ω)
  have hfin := bep_mono (N := n) hρ0.le hρ1
    (fun Ω => LoEv SV (p1 / 2) Ω ∧ UpEv SV (3 * p2 / 2) Ω)
    (fun Ω => ∀ X : RealMatrix n n,
          frobeniusNorm (tangentProjection SV X -
            ρ⁻¹ • tangentProjection SV (samplingProjection Ω (tangentProjection SV X))) ≤
            (3 / 5) * frobeniusNorm X)
    (fun Ω h X => det26 SV Ω ρ (p1 / 2) (3 * p2 / 2) hρ0 h.1 h.2 hp1lo hp2up X)
  linarith


lemma eps35_pow_le (n j0 : ℕ) (hn : (0 : ℝ) < n) (hj : 2 * Real.log n ≤ j0) :
    (3 / 5 : ℝ) ^ j0 ≤ 1 / n := by
  have hs : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have hpos := Real.exp_pos (1 / 2)
  have h53 : Real.exp (1 / 2) ≤ 5 / 3 := by nlinarith
  have h1 : (3 / 5 : ℝ) ≤ Real.exp (-(1 / 2)) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) hpos]
    have : ((3 : ℝ) / 5)⁻¹ = 5 / 3 := by norm_num
    rw [this]; exact h53
  have h2 : (3 / 5 : ℝ) ^ j0 ≤ Real.exp (-(1 / 2)) ^ j0 := pow_le_pow_left₀ (by norm_num) h1 j0
  rw [← Real.exp_nat_mul] at h2
  have h3 : Real.exp (j0 * -(1 / 2)) ≤ Real.exp (-Real.log n) := Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg, Real.exp_log hn, ← one_div] at h3
  linarith

set_option maxHeartbeats 1000000 in
theorem main2 (h26 : G26h) (h31 : G31) (h32 : G32d) :
    ∃ ρs ρr c : ℝ, 0 < ρs ∧ 0 < ρr ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ρ : ℝ),
        0 < n → Incoherent SV μ → (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr * n →
        0 < ρ → ρ ≤ ρs →
        let j0 := 2 * ⌈Real.log n⌉₊
        let q := 1 - ρ ^ ((1 : ℝ) / j0)
        let lam := 1 / Real.sqrt n
        golfingProb q j0 (fun Ωs =>
            MatrixCompletion.spectralNorm (WL SV q Ωs) < 1 / 4 ∧
            frobeniusNorm (samplingProjection (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) <
              lam / 4 ∧
            entrySupNorm (compProj (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) < lam / 4) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  obtain ⟨A0, ca, hA0, hca, H26⟩ := h26
  obtain ⟨B0, cb, hB0, hcb, H31⟩ := h31
  obtain ⟨C1, cc, hC1, hcc, H32⟩ := h32
  obtain ⟨δ, hδ0, hδ1, hδC1, hδA, hδB⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 50 ∧ δ * (25 * C1) ≤ 1 ∧
      δ * (45 * A0) ≤ 1 ∧ δ * (45 * B0) ≤ 1 := by
    refine ⟨min (1 / 50) (min (1 / (25 * C1)) (min (1 / (45 * A0)) (1 / (45 * B0)))),
      by positivity, min_le_left _ _, ?_, ?_, ?_⟩
    · rw [← le_div_iff₀ (by positivity)]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    · rw [← le_div_iff₀ (by positivity)]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · rw [← le_div_iff₀ (by positivity)]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℝ, N0 = 75 := ⟨_, rfl⟩
  have hN3 : 3 ≤ N0 := by rw [hN0]; norm_num
  have hcpos : 0 < 2 * (ca + cb + cc) + N0 ^ 10 := by
    have h1 : 0 < N0 ^ 10 := pow_pos (by linarith) 10
    linarith
  refine ⟨Real.exp (-1), δ ^ 2, 2 * (ca + cb + cc) + N0 ^ 10, Real.exp_pos _, by positivity,
    hcpos, ?_⟩
  intro n r L0 SV μ ρ hn hinc hrank hρ0 hρs j0 q lam
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ1 : ρ ≤ 1 := le_trans hρs (Real.exp_le_one_iff.mpr (by norm_num))
  have hrp0 : 0 ≤ ρ ^ ((1 : ℝ) / j0) := Real.rpow_nonneg hρ0.le _
  have hrp1 : ρ ^ ((1 : ℝ) / j0) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by positivity)
  have hq0 : 0 ≤ q := by show 0 ≤ 1 - ρ ^ ((1 : ℝ) / j0); linarith
  have hq1 : q ≤ 1 := by show 1 - ρ ^ ((1 : ℝ) / j0) ≤ 1; linarith
  have hz10 : (n : ℝ) ^ (-10 : ℤ) = 1 / (n : ℝ) ^ 10 := by rw [zpow_neg, zpow_ofNat, one_div]
  rcases lt_or_ge (n : ℝ) N0 with hsmall | hbig
  · refine le_trans ?_ (golf_nonneg hq0 hq1 _)
    rw [hz10]
    have hpow : (n : ℝ) ^ 10 ≤ N0 ^ 10 := pow_le_pow_left₀ hnR.le hsmall.le 10
    have hpos : 0 < (n : ℝ) ^ 10 := by positivity
    have : 1 ≤ (2 * (ca + cb + cc) + N0 ^ 10) * (1 / (n : ℝ) ^ 10) := by
      rw [mul_one_div, le_div_iff₀ hpos]; linarith [hca, hcb, hcc, hpow]
    linarith
  have hn3 : (3 : ℝ) ≤ n := le_trans hN3 hbig
  have hL1 : 1 ≤ Real.log n := le_of_lt ((Real.lt_log_iff_exp_lt hnR).mpr
    (by have := Real.exp_one_lt_d9; linarith))
  have hLpos : 0 < Real.log n := by linarith
  have hLn : Real.log n ≤ n - 1 := Real.log_le_sub_one_of_pos hnR
  have hc1 : Real.log n ≤ (⌈Real.log n⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈Real.log n⌉₊ : ℝ) < Real.log n + 1 := Nat.ceil_lt_add_one (by linarith)
  have hj0R : (j0 : ℝ) = 2 * (⌈Real.log n⌉₊ : ℝ) := by
    show ((2 * ⌈Real.log n⌉₊ : ℕ) : ℝ) = _; push_cast; ring
  have hj1 : 1 ≤ j0 := by
    have : (1 : ℝ) ≤ j0 := by rw [hj0R]; linarith
    exact_mod_cast this
  have hqlow := q_lower ρ j0 hj1 hρ0 hρs
  have hq5 : 1 / (5 * Real.log n) ≤ q :=
    le_trans (one_div_le_one_div_of_le (by positivity) (by rw [hj0R]; linarith)) hqlow
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hq5
  have hqinv : q⁻¹ ≤ 5 * Real.log n := by
    rw [inv_le_comm₀ hqpos (by positivity), ← one_div]; exact hq5
  have hε0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hε1 : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num); rwa [Real.exp_zero] at this
  have he1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have he2 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have hεhalf : Real.exp (-1) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left he2 hε0.le; linarith
  have hεinv : (Real.exp (-1))⁻¹ ^ 2 ≤ 9 := by
    rw [show (Real.exp (-1))⁻¹ = Real.exp 1 by rw [Real.exp_neg, inv_inv]]
    have h3 := mul_le_mul he3.le he3.le (Real.exp_pos 1).le (by norm_num); rw [sq]; linarith
  have hεj' := eps35_pow_le n j0 hnR (by rw [hj0R]; linarith)
  obtain ⟨a, ha⟩ : ∃ a, a = entrySupNorm (signMatrix SV) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; exact entrySup_nonneg _
  have haS : a ≤ Real.sqrt (μ * r / ((n : ℝ) * n)) := by
    rw [ha]; exact entrySup_le _ _ (Real.sqrt_nonneg _) hinc.2.2
  have hu : a ^ 2 * n * Real.log n ^ 2 ≤ δ ^ 2 := by
    rcases le_or_gt 0 (μ * r / ((n : ℝ) * n)) with hx | hx
    · have h1 : a ^ 2 ≤ μ * r / ((n : ℝ) * n) := by
        have := pow_le_pow_left₀ ha0 haS 2
        rwa [Real.sq_sqrt hx] at this
      have h2 : μ * r / ((n : ℝ) * n) * n * Real.log n ^ 2 = (r * μ * Real.log n ^ 2) / n := by
        field_simp
      have h3 : (r * μ * Real.log n ^ 2) / n ≤ δ ^ 2 := by rw [div_le_iff₀ hnR]; exact hrank
      calc a ^ 2 * n * Real.log n ^ 2 ≤ μ * r / ((n : ℝ) * n) * n * Real.log n ^ 2 := by gcongr
        _ ≤ δ ^ 2 := by rw [h2]; exact h3
    · have h0 : Real.sqrt (μ * r / ((n : ℝ) * n)) = 0 := Real.sqrt_eq_zero'.mpr hx.le
      rw [h0] at haS
      have ha00 : a = 0 := le_antisymm haS ha0
      rw [ha00]; have := sq_nonneg δ
      have e : (0 : ℝ) ^ 2 * n * Real.log n ^ 2 = 0 := by ring
      linarith
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt n := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hnR
  have hs2 : s ^ 2 = n := by rw [hs]; exact Real.sq_sqrt hnR.le
  have huL : a * s * Real.log n ≤ δ := by
    have h : (a * s * Real.log n) ^ 2 ≤ δ ^ 2 := by rw [mul_pow, mul_pow, hs2]; exact hu
    exact (pow_le_pow_iff_left₀ (by positivity) hδ0.le (by norm_num)).mp h
  have has : a * s ≤ δ := le_trans (le_mul_of_one_le_right (mul_nonneg ha0 hs0.le) hL1) huL
  have hsq : Real.sqrt (n * Real.log n / q) ≤ 3 * s * Real.log n := by
    have h1 : n * Real.log n / q ≤ (3 * s * Real.log n) ^ 2 := by
      rw [mul_pow, mul_pow, hs2, div_eq_mul_inv]
      have : (n : ℝ) * Real.log n * q⁻¹ ≤ n * Real.log n * (5 * Real.log n) :=
        mul_le_mul_of_nonneg_left hqinv (by positivity)
      have hp : 0 ≤ (n : ℝ) * Real.log n ^ 2 := by positivity
      linarith [this, hp]
    calc Real.sqrt (n * Real.log n / q) ≤ Real.sqrt ((3 * s * Real.log n) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = 3 * s * Real.log n := Real.sqrt_sq (by positivity)
  have hmuL : μ * r * Real.log n / n ≤ δ ^ 2 / Real.log n := by
    rw [div_le_div_iff₀ hnR hLpos]; linarith [hrank]
  have hcondA : q ≥ A0 * μ * r * Real.log n / n := by
    have e : A0 * μ * r * Real.log n / n = A0 * (μ * r * Real.log n / n) := by ring
    rw [e]
    have h1 : A0 * (μ * r * Real.log n / n) ≤ (A0 * 9) * (δ ^ 2 / Real.log n) := by
      calc _ ≤ A0 * (δ ^ 2 / Real.log n) := mul_le_mul_of_nonneg_left hmuL hA0.le
        _ ≤ (A0 * 9) * (δ ^ 2 / Real.log n) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have k : 45 * A0 * δ ^ 2 ≤ 1 := by
      calc 45 * A0 * δ ^ 2 = (δ * (45 * A0)) * δ := by ring
        _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hδA hδ0.le
        _ ≤ 1 := by linarith
    have h2 : (A0 * 9) * (δ ^ 2 / Real.log n) ≤ 1 / (5 * Real.log n) := by
      calc (A0 * 9) * (δ ^ 2 / Real.log n) = (45 * A0 * δ ^ 2) * (1 / (5 * Real.log n)) := by
            field_simp <;> ring
        _ ≤ 1 * (1 / (5 * Real.log n)) := mul_le_mul_of_nonneg_right k (by positivity)
        _ = 1 / (5 * Real.log n) := one_mul _
    linarith
  have hcondB : q ≥ B0 * (Real.exp (-1))⁻¹ ^ 2 * μ * r * Real.log n / n := by
    have e : B0 * (Real.exp (-1))⁻¹ ^ 2 * μ * r * Real.log n / n =
        (B0 * (Real.exp (-1))⁻¹ ^ 2) * (μ * r * Real.log n / n) := by ring
    rw [e]
    have h1 : (B0 * (Real.exp (-1))⁻¹ ^ 2) * (μ * r * Real.log n / n) ≤
        (B0 * 9) * (δ ^ 2 / Real.log n) := by
      calc _ ≤ (B0 * (Real.exp (-1))⁻¹ ^ 2) * (δ ^ 2 / Real.log n) :=
            mul_le_mul_of_nonneg_left hmuL (mul_nonneg hB0.le (by positivity))
        _ ≤ (B0 * 9) * (δ ^ 2 / Real.log n) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεinv hB0.le) (by positivity)
    have k : 45 * B0 * δ ^ 2 ≤ 1 := by
      calc 45 * B0 * δ ^ 2 = (δ * (45 * B0)) * δ := by ring
        _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hδB hδ0.le
        _ ≤ 1 := by linarith
    have h2 : (B0 * 9) * (δ ^ 2 / Real.log n) ≤ 1 / (5 * Real.log n) := by
      calc (B0 * 9) * (δ ^ 2 / Real.log n) = (45 * B0 * δ ^ 2) * (1 / (5 * Real.log n)) := by
            field_simp <;> ring
        _ ≤ 1 * (1 / (5 * Real.log n)) := mul_le_mul_of_nonneg_right k (by positivity)
        _ = 1 / (5 * Real.log n) := one_mul _
    linarith
  have hcondD : 1 ≤ q * (2 * Real.log n + 3) := by
    have hj : (j0 : ℝ) + 1 ≤ 2 * Real.log n + 3 := by rw [hj0R]; linarith
    have hql : 1 / ((j0 : ℝ) + 1) ≤ q := hqlow
    rw [div_le_iff₀ (by positivity)] at hql
    linarith [mul_le_mul_of_nonneg_left hj hqpos.le]
  have h15 : 15 ≤ q * ((n : ℝ) * n) := by
    have hq' : 1 / (5 * (n : ℝ)) ≤ q :=
      le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) hq5
    have h1 := mul_le_mul_of_nonneg_right hq' (by positivity : (0 : ℝ) ≤ (n : ℝ) * n)
    have e : 1 / (5 * (n : ℝ)) * ((n : ℝ) * n) = n / 5 := by
      first | (field_simp; ring) | field_simp
    have hn75 : (75 : ℝ) ≤ n := by rw [hN0] at hbig; exact hbig
    linarith
  let Bad : Fin j0 → (Fin j0 → Finset (Fin n × Fin n)) → Prop := fun j Ωs =>
    ¬ ((∀ X : RealMatrix n n, frobeniusNorm (tangentProjection SV X -
          q⁻¹ • tangentProjection SV (samplingProjection (Ωs j) (tangentProjection SV X))) ≤
          (3 / 5) * frobeniusNorm X) ∧
      entrySupNorm (Zg SV q Ωs j.val - q⁻¹ • tangentProjection SV
          (samplingProjection (Ωs j) (Zg SV q Ωs j.val))) ≤
        Real.exp (-1) * entrySupNorm (Zg SV q Ωs j.val) ∧
      MatrixCompletion.spectralNorm (Zg SV q Ωs j.val -
          q⁻¹ • samplingProjection (Ωs j) (Zg SV q Ωs j.val)) ≤
        C1 * Real.sqrt (n * Real.log n / q) * entrySupNorm (Zg SV q Ωs j.val))
  have hB : ∀ j Ωs, bernoulliEventProb q (fun B => Bad j (Function.update Ωs j B)) ≤
      (ca + cb + cc) * (n : ℝ) ^ (-11 : ℤ) := by
    intro j Ωs
    have hfun : (fun B => Bad j (Function.update Ωs j B)) = (fun B =>
        ¬ ((∀ X : RealMatrix n n, frobeniusNorm (tangentProjection SV X -
            q⁻¹ • tangentProjection SV (samplingProjection B (tangentProjection SV X))) ≤
            (3 / 5) * frobeniusNorm X) ∧
        entrySupNorm (Zg SV q Ωs j.val - q⁻¹ • tangentProjection SV
            (samplingProjection B (Zg SV q Ωs j.val))) ≤
          Real.exp (-1) * entrySupNorm (Zg SV q Ωs j.val) ∧
        MatrixCompletion.spectralNorm (Zg SV q Ωs j.val -
            q⁻¹ • samplingProjection B (Zg SV q Ωs j.val)) ≤
          C1 * Real.sqrt (n * Real.log n / q) * entrySupNorm (Zg SV q Ωs j.val))) := by
      funext B
      simp only [Bad, Function.update_self, Zg_update]
    have e1 := H26 n r L0 SV μ q hn hinc hqpos hq1 h15 hcondA
    have e2 := H31 n r L0 SV μ (Zg SV q Ωs j.val) (Real.exp (-1)) q hn hinc (Zg_T SV q Ωs _)
      hε0 hε1.le hqpos hq1 hcondB
    have e3 := H32 n (Zg SV q Ωs j.val) q hn hqpos hq1 hcondD
    rw [hfun]
    refine le_trans (bep_not_and3 hq0 hq1 _ _ _) ?_
    rw [bep_not, bep_not, bep_not]
    linarith
  have hj0n : (j0 : ℝ) ≤ 2 * n := by rw [hj0R]; linarith
  have hz : (n : ℝ) * (n : ℝ) ^ (-11 : ℤ) = (n : ℝ) ^ (-10 : ℤ) := by
    rw [show (-10 : ℤ) = 1 + (-11) by norm_num, zpow_add₀ hnR.ne', zpow_one]
  have hz0 : 0 ≤ (n : ℝ) ^ (-11 : ℤ) := by positivity
  have hz0' : 0 ≤ (n : ℝ) ^ (-10 : ℤ) := by positivity
  refine le_trans ?_ (golf_union q ((ca + cb + cc) * (n : ℝ) ^ (-11 : ℤ)) hq0 hq1 Bad hB _ ?_)
  · have hδp : (ca + cb + cc) * (n : ℝ) ^ (-11 : ℤ) = (ca + cb + cc) * (n : ℝ) ^ (-10 : ℤ) / n := by
      rw [← hz]; field_simp
    exact aux_u j0 n (ca + cb + cc) _ _ N0 hj0n (by positivity) hδp hnR hz0' (by linarith)
  · intro Ωs hgood
    have hG := fun j => not_not.mp (hgood j)
    obtain ⟨k1, k2, k3⟩ := det_bound SV q Ωs (3 / 5) (Real.exp (-1)) a
      (C1 * Real.sqrt (n * Real.log n / q)) hqpos (by norm_num) hε0.le hε1
      (mul_nonneg hC1.le (Real.sqrt_nonneg _)) (le_of_eq ha.symm) hG
    have hpos1 : 0 < 1 - Real.exp (-1) := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have hD : C1 * Real.sqrt (n * Real.log n / q) * a ≤ 3 * C1 * δ := by
        calc C1 * Real.sqrt (n * Real.log n / q) * a ≤ C1 * (3 * s * Real.log n) * a :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC1.le) ha0
          _ = 3 * C1 * (a * s * Real.log n) := by ring
          _ ≤ 3 * C1 * δ := mul_le_mul_of_nonneg_left huL (by positivity)
      have hD0 : 0 ≤ C1 * Real.sqrt (n * Real.log n / q) * a :=
        mul_nonneg (mul_nonneg hC1.le (Real.sqrt_nonneg _)) ha0
      have h2 := aux_div (C1 * Real.sqrt (n * Real.log n / q) * a) (Real.exp (-1)) hD0 hεhalf
      calc MatrixCompletion.spectralNorm (WL SV q Ωs) ≤ _ := k1
        _ ≤ 2 * (C1 * Real.sqrt (n * Real.log n / q) * a) := h2
        _ < 1 / 4 := aux_a _ C1 δ hD hδC1
    · show _ < 1 / Real.sqrt n / 4
      rw [← hs]
      have hf : frobeniusNorm (signMatrix SV) ≤ n * a := by rw [ha]; exact frob_le_entrySup _
      have h1 : (3 / 5 : ℝ) ^ j0 * frobeniusNorm (signMatrix SV) ≤ 1 / (n : ℝ) * (n * a) :=
        mul_le_mul hεj' hf (frob_nonneg _) (by positivity)
      have h2 : 1 / (n : ℝ) * (n * a) = a := by field_simp
      have h3 := aux_c a s (Real.log n) δ hs0 has huL hδ1
      have h4 : 0 ≤ 10 * Real.log n * a := mul_nonneg (mul_nonneg (by norm_num) hLpos.le) ha0
      linarith
    · show _ < 1 / Real.sqrt n / 4
      rw [← hs]
      have h1 : Real.exp (-1) ^ j0 * a ≤ a :=
        mul_le_of_le_one_left ha0 (pow_le_one₀ hε0.le hε1.le)
      have hqa : 0 ≤ q⁻¹ * a := mul_nonneg (inv_nonneg.mpr hqpos.le) ha0
      have h2 := aux_div (q⁻¹ * a) (Real.exp (-1)) hqa hεhalf
      have h3 : q⁻¹ * a ≤ 5 * Real.log n * a := mul_le_mul_of_nonneg_right hqinv ha0
      have h4 := aux_c a s (Real.log n) δ hs0 has huL hδ1
      linarith


end RPCA28

open RobustPCA.Recovery in
theorem solution :
    ∃ ρs ρr c : ℝ, 0 < ρs ∧ 0 < ρr ∧ 0 < c ∧
      ∀ (n r : ℕ) (L0 : RealMatrix n n) (SV : SVD L0 r) (μ ρ : ℝ),
        0 < n → Incoherent SV μ → (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr * n →
        0 < ρ → ρ ≤ ρs →
        let j0 := 2 * ⌈Real.log n⌉₊
        let q := 1 - ρ ^ ((1 : ℝ) / j0)
        let lam := 1 / Real.sqrt n
        golfingProb q j0 (fun Ωs =>
            spectralNorm (WL SV q Ωs) < 1 / 4 ∧
            frobeniusNorm (samplingProjection (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) <
              lam / 4 ∧
            entrySupNorm (compProj (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) < lam / 4) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  exact RPCA28.main2 (RPCA28.g26 candes_recht_theorem41_bernoulli_tangent_sampling_concentration)
    RPCA28.g31 RPCA28.g32
