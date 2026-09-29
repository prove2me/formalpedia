-- Prove2me | solution 1 for RobustSDP.Uniqueness.dual_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:40:11.934909+00:00
-- url     : https://prove2.me/submissions/65887e33-0ea5-444d-beda-9d1c4321d0f8

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix


namespace RobustSDP.Uniqueness

lemma psd_near_one {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ)
    (h : ∀ i j, |Q i j - (1 : Matrix ι ι ℝ) i j| ≤ 1 / (Fintype.card ι + 1)) (v : ι → ℝ) :
    0 ≤ v ⬝ᵥ (Q *ᵥ v) := by
  set k : ℝ := (Fintype.card ι : ℝ) with hk
  have hk0 : 0 ≤ k := by positivity
  have key : ∀ i j, v i * (1 : Matrix ι ι ℝ) i j * v j - (v i ^ 2 + v j ^ 2) / (2 * (k + 1))
      ≤ v i * Q i j * v j := by
    intro i j
    have hb := h i j
    rw [abs_le] at hb
    set e := Q i j - (1 : Matrix ι ι ℝ) i j
    have hQ : Q i j = (1 : Matrix ι ι ℝ) i j + e := by ring
    rw [hQ]
    have hpos : 0 < 2 * (k + 1) := by positivity
    have h1 : e * (k + 1) ≤ 1 := by
      have := hb.2; rw [le_div_iff₀ (by positivity)] at this; linarith
    have h2 : -1 ≤ e * (k + 1) := by
      have := hb.1; rw [neg_le, le_div_iff₀ (by positivity)] at this; linarith
    have h3 : -(e * (v i * v j)) * (2 * (k + 1)) ≤ v i ^ 2 + v j ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (v i + v j)),
        mul_nonneg (neg_le_iff_add_nonneg.1 h2) (sq_nonneg (v i - v j))]
    have h4 : -(e * (v i * v j)) ≤ (v i ^ 2 + v j ^ 2) / (2 * (k + 1)) := by
      rw [le_div_iff₀ hpos]; linarith
    have h5 : v i * ((1 : Matrix ι ι ℝ) i j + e) * v j
        = v i * (1 : Matrix ι ι ℝ) i j * v j + e * (v i * v j) := by ring
    rw [h5]; linarith
  have hsum : v ⬝ᵥ (Q *ᵥ v) = ∑ i, ∑ j, v i * Q i j * v j := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [hsum]
  have hle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => key i j))
  refine le_trans ?_ hle
  simp only [Finset.sum_sub_distrib, one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← hk]
  have hS : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [sub_nonneg, div_le_iff₀ (by positivity)]
  have : ∑ x, v x * v x = ∑ i, v i ^ 2 := by simp [sq]
  rw [this]
  have h6 : ∑ x, k * v x ^ 2 = k * ∑ x, v x ^ 2 := by rw [Finset.mul_sum]
  rw [h6]
  nlinarith


section Dual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- quadratic form as double sum -/
def qf (P : ι → ι → ℝ) (v : ι → ℝ) : ℝ := ∑ i, ∑ j, v i * P i j * v j

lemma qf_eq (P : Matrix ι ι ℝ) (v : ι → ℝ) : v ⬝ᵥ (P *ᵥ v) = qf P v := by
  simp [qf, dotProduct, mulVec, Finset.mul_sum, mul_comm, mul_left_comm]

def T0 : Set ((ι → ι → ℝ) × ℝ) := {z | (∀ v, 0 ≤ qf z.1 v) ∧ z.2 ≤ 0}

lemma T0_convex : Convex ℝ (T0 (ι := ι)) := by
  intro z hz w hw a b ha hb _
  refine ⟨fun v => ?_, ?_⟩
  · have e : qf (a • z + b • w).1 v = a * qf z.1 v + b * qf w.1 v := by
      simp only [qf, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [e]
    exact add_nonneg (mul_nonneg ha (hz.1 v)) (mul_nonneg hb (hw.1 v))
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    nlinarith [hz.2, hw.2]

lemma T0_smul {z : (ι → ι → ℝ) × ℝ} (hz : z ∈ T0) {k : ℝ} (hk : 0 ≤ k) : k • z ∈ T0 := by
  refine ⟨fun v => ?_, ?_⟩
  · have e : qf (k • z).1 v = k * qf z.1 v := by
      simp only [qf, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)); ring
    rw [e]; exact mul_nonneg hk (hz.1 v)
  · simp only [Prod.smul_snd, smul_eq_mul]; nlinarith [hz.2]

def a0 : (ι → ι → ℝ) × ℝ := (((1 : Matrix ι ι ℝ) : ι → ι → ℝ), -1)

lemma a0_mem_interior : (a0 : (ι → ι → ℝ) × ℝ) ∈ interior (T0 (ι := ι)) := by
  rw [mem_interior]
  refine ⟨Metric.ball a0 (1 / (Fintype.card ι + 1)), fun z hz => ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity)⟩
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hz
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun v => ?_, ?_⟩
  · have hq := psd_near_one (Matrix.of z.1) ?_ v
    · rwa [qf_eq] at hq
    intro i j
    have := (norm_le_pi_norm (z.1 - (a0 (ι := ι)).1) i).trans_lt (by rwa [dist_eq_norm] at h1)
    have := (norm_le_pi_norm ((z.1 - (a0 (ι := ι)).1) i) j).trans this.le
    simp only [a0, Real.norm_eq_abs] at this
    exact le_trans (le_of_eq rfl) this
  · rw [Real.dist_eq] at h2
    have hle : 1 / ((Fintype.card ι : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg (Fintype.card ι) : (0:ℝ) ≤ _)]
    have := (abs_lt.mp (lt_of_lt_of_le h2 hle))
    simp [a0] at this
    linarith [this.2]


lemma f_repr (f : StrongDual ℝ ((ι → ι → ℝ) × ℝ)) (P : ι → ι → ℝ) (t : ℝ) :
    f (P, t) = ∑ i, ∑ j, P i j * f ((Pi.single i (Pi.single j (1:ℝ)) : ι → ι → ℝ), (0:ℝ))
      + t * f ((0 : ι → ι → ℝ), (1:ℝ)) := by
  have e : (P, t) = ∑ i, ∑ j, P i j • ((Pi.single i (Pi.single j (1:ℝ)) : ι → ι → ℝ), (0:ℝ))
      + t • ((0 : ι → ι → ℝ), (1:ℝ)) := by
    ext a b
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  conv_lhs => rw [e]
  rw [map_add, map_sum]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma qf_psd {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (v : ι → ℝ) : 0 ≤ qf M v := by
  have := hM.dotProduct_mulVec_nonneg v
  rwa [star_trivial, qf_eq] at this

lemma psd_of_qf {M : Matrix ι ι ℝ} (hs : M.IsSymm) (h : ∀ v, 0 ≤ qf M v) : M.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.2 hs)
    (fun v => by rw [star_trivial, qf_eq]; exact h v)

lemma trace_sym (Y M : Matrix ι ι ℝ) (hY : ∀ i j, Y i j = Y j i) :
    (Y * M).trace = ∑ i, ∑ j, M i j * Y i j := by
  simp only [trace, diag, mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hY]; ring

open scoped MatrixOrder in
lemma pd_pair_zero (M N : Matrix ι ι ℝ) (hM : M.PosDef) (hN : N.PosSemidef)
    (h : ∑ i, ∑ j, M i j * N i j = 0) : N = 0 := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN.nonneg
  have e : ∑ i, ∑ j, M i j * (star B * B) i j = ∑ k, qf M (fun a => B k a) := by
    simp only [qf, mul_apply, star_eq_conjTranspose, conjTranspose_apply, star_trivial,
      Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [e] at h
  have hnn : ∀ k, 0 ≤ qf M (fun a => B k a) := fun k => qf_psd hM.posSemidef _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnn k)).1 h
  have hB : B = 0 := by
    ext k a
    by_contra hne
    have hv : (fun a => B k a) ≠ 0 := fun h0 => hne (by simpa using congrFun h0 a)
    have := hM.dotProduct_mulVec_pos hv
    rw [star_trivial, qf_eq, hz k (Finset.mem_univ _)] at this
    exact lt_irrefl _ this
  simp [hB]

lemma qf_single (i j : ι) (v : ι → ℝ) :
    qf (Pi.single i (Pi.single j (1:ℝ))) v = v i * v j := by
  simp [qf, Pi.single_apply, ite_apply, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma pair_single (i j : ι) (Y : Matrix ι ι ℝ) :
    ∑ a, ∑ b, (Pi.single i (Pi.single j (1:ℝ)) : ι → ι → ℝ) a b * Y a b = Y i j := by
  simp [Pi.single_apply, ite_apply, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma qf_sub (P Q : ι → ι → ℝ) (v : ι → ℝ) : qf (P - Q) v = qf P v - qf Q v := by
  simp [qf, sub_mul, mul_sub, Finset.sum_sub_distrib]

def pe (M : Matrix ι ι ℝ) (t : ℝ) : (ι → ι → ℝ) × ℝ := (M, t)

lemma pe_add (M N : Matrix ι ι ℝ) (s t : ℝ) : pe M s + pe N t = pe (M + N) (s + t) := rfl
lemma pe_smul (c : ℝ) (M : Matrix ι ι ℝ) (t : ℝ) : c • pe M t = pe (c • M) (c * t) := rfl

theorem sdp_dual {V : Type*} [AddCommGroup V] [Module ℝ V] (A0 : Matrix ι ι ℝ)
    (𝓐 : V →ₗ[ℝ] Matrix ι ι ℝ) (cl : V →ₗ[ℝ] ℝ) (hsym : ∀ y, (A0 + 𝓐 y).IsSymm) (ys : V)
    (hfeas : (A0 + 𝓐 ys).PosSemidef) (hopt : ∀ y, (A0 + 𝓐 y).PosSemidef → cl ys ≤ cl y)
    (hsl : ∃ y0, (A0 + 𝓐 y0).PosDef) :
    ∃ Y : Matrix ι ι ℝ, Y.PosSemidef ∧ (∀ d, (Y * 𝓐 d).trace = cl d) ∧
      (Y * (A0 + 𝓐 ys)).trace = 0 := by
  set Sf : V → (ι → ι → ℝ) × ℝ := fun d => pe (A0 + 𝓐 (ys + d)) (cl d) with hSf
  have hSc : Convex ℝ (Set.range Sf) := by
    rintro _ ⟨d1, rfl⟩ _ ⟨d2, rfl⟩ a b ha hb hab
    refine ⟨a • d1 + b • d2, ?_⟩
    obtain rfl : b = 1 - a := by linarith
    simp only [hSf, pe_smul, pe_add, map_add, map_smul, smul_eq_mul]
    congr 1
    · ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have disj : Disjoint (interior (T0 (ι := ι))) (Set.range Sf) := by
    rw [Set.disjoint_left]
    rintro z hzI ⟨d, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hzI
    have hz' : (((Sf d).1 : ι → ι → ℝ), (Sf d).2 + ε / 2) ∈ T0 := by
      apply interior_subset
      apply hball
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨by simp [hε], ?_⟩
      rw [Real.dist_eq]; simp; rw [abs_of_pos (by positivity)]; linarith
    have h2 : cl d < 0 := by have := hz'.2; simp [hSf, pe] at this; linarith
    have hpsd := psd_of_qf (hsym (ys + d)) (interior_subset hzI).1
    have := hopt _ hpsd
    rw [map_add] at this
    linarith
  obtain ⟨f, u, hlt, hge⟩ :=
    geometric_hahn_banach_open T0_convex.interior isOpen_interior hSc disj
  have ha0 := a0_mem_interior (ι := ι)
  have hfle : ∀ b ∈ T0 (ι := ι), f b ≤ 0 := by
    intro b hb
    by_contra hpos
    push_neg at hpos
    set k := (2 * |u| + |f a0| + 1) / f b with hk
    have hk0 : 0 ≤ k := by positivity
    have hmem := T0_convex.combo_interior_self_mem_interior ha0 (T0_smul hb hk0)
      (a := 1/2) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
    have := hlt _ hmem
    rw [map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hk,
      div_mul_cancel₀ _ (ne_of_gt hpos)] at this
    have h1 := neg_abs_le (f a0)
    have h2 := le_abs_self u
    linarith
  have hu : 0 ≤ u := by
    by_contra hneg
    push_neg at hneg
    have hfa := hlt _ ha0
    have hfa0 : f a0 < 0 := by linarith
    set θ := u / (2 * f a0) with hθ
    have hθ0 : 0 < θ := div_pos_of_neg_of_neg hneg (by linarith)
    have hθ1 : θ ≤ 1 := by
      rw [hθ, div_le_one_of_neg (by linarith)]; linarith
    have hmem := T0_convex.combo_interior_self_mem_interior ha0
      (show (0 : (ι → ι → ℝ) × ℝ) ∈ T0 from ⟨fun v => by simp [qf], le_rfl⟩)
      (a := θ) (b := 1 - θ) hθ0 (by linarith) (by ring)
    have := hlt _ hmem
    rw [smul_zero, add_zero, map_smul, smul_eq_mul, hθ, div_mul_eq_mul_div,
      mul_div_mul_right _ _ (ne_of_lt hfa0)] at this
    linarith
  have hSd : ∀ d : V, Sf d = Sf 0 + pe (𝓐 d) (cl d) := by
    intro d; simp only [hSf, pe_add, map_add, map_zero, add_zero]
    congr 1
    · rw [add_assoc]
    · simp
  have hS0mem : Sf 0 ∈ T0 (ι := ι) := by
    refine ⟨fun v => ?_, by simp [hSf, pe]⟩
    simpa [hSf, pe] using qf_psd hfeas v
  have hS0 : f (Sf 0) = 0 := le_antisymm (hfle _ hS0mem) (le_trans hu (hge _ ⟨0, rfl⟩))
  have hg : ∀ d : V, f (pe (𝓐 d) (cl d)) = 0 := by
    intro d
    by_contra hne
    set t := (u - 1) / f (pe (𝓐 d) (cl d))
    have := hge _ ⟨t • d, rfl⟩
    rw [hSd, map_add, hS0, map_smul, map_smul, smul_eq_mul, ← pe_smul, map_smul,
      smul_eq_mul, div_mul_cancel₀ _ hne] at this
    linarith
  set Y0 : Matrix ι ι ℝ := Matrix.of fun i j =>
    f ((Pi.single i (Pi.single j (1:ℝ)) : ι → ι → ℝ), (0:ℝ)) with hY0
  set lam := f ((0 : ι → ι → ℝ), (1:ℝ)) with hlam_def
  have hrep : ∀ P t, f (P, t) = ∑ i, ∑ j, P i j * Y0 i j + t * lam := fun P t => f_repr f P t
  have hrep' : ∀ (M : Matrix ι ι ℝ) t, f (pe M t) = ∑ i, ∑ j, M i j * Y0 i j + t * lam :=
    fun M t => f_repr f M t
  have hlam : 0 ≤ lam := by
    have := hfle ((0 : ι → ι → ℝ), (-1 : ℝ)) ⟨fun v => by simp [qf], by norm_num⟩
    rw [hrep] at this; simp at this; linarith
  have hsym0 : ∀ i j, Y0 i j = Y0 j i := by
    intro i j
    set P : ι → ι → ℝ := Pi.single i (Pi.single j (1:ℝ)) - Pi.single j (Pi.single i (1:ℝ))
    have hq : ∀ v, qf P v = 0 := by
      intro v; rw [qf_sub, qf_single, qf_single]; ring
    have h1 := hfle (P, 0) ⟨fun v => by rw [hq], le_rfl⟩
    have h2 := hfle (-P, 0) ⟨fun v => by
      have : qf (-P) v = - qf P v := by simp [qf, Finset.sum_neg_distrib]
      rw [this, hq]; simp, le_rfl⟩
    rw [hrep] at h1 h2
    have e1 : ∑ a, ∑ b, P a b * Y0 a b = Y0 i j - Y0 j i := by
      simp only [P, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, pair_single]
    have e2 : ∑ a, ∑ b, (-P) a b * Y0 a b = -(Y0 i j - Y0 j i) := by
      rw [← e1]; simp [Finset.sum_neg_distrib]
    rw [e1] at h1; rw [e2] at h2
    linarith
  have hneg : ∀ v, qf Y0 v ≤ 0 := by
    intro v
    set P : ι → ι → ℝ := fun a b => v a * v b
    have hq : ∀ w, 0 ≤ qf P w := by
      intro w
      have : qf P w = (∑ a, w a * v a) ^ 2 := by
        simp only [qf, P, sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_)); ring
      rw [this]; positivity
    have h1 := hfle (P, 0) ⟨hq, le_rfl⟩
    rw [hrep] at h1
    have : qf Y0 v = ∑ a, ∑ b, P a b * Y0 a b := by
      simp only [qf, P]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_)); ring
    rw [this]; simpa using h1
  have hlampos : 0 < lam := by
    rcases hlam.lt_or_eq with h | h
    · exact h
    exfalso
    obtain ⟨y0, hy0⟩ := hsl
    have hnegpsd : (-Y0).PosSemidef := by
      apply psd_of_qf
      · ext i j; simp [hsym0 i j]
      · intro v
        have : qf (-Y0) v = - qf Y0 v := by simp [qf, Finset.sum_neg_distrib]
        rw [this]; linarith [hneg v]
    have hA : ∀ d : V, ∑ i, ∑ j, (𝓐 d) i j * Y0 i j = 0 := by
      intro d; have := hg d; rw [hrep', ← h] at this; simpa using this
    have hB : ∑ i, ∑ j, (A0 + 𝓐 ys) i j * Y0 i j = 0 := by
      have := hS0; rw [hSf] at this; simp only at this; rw [hrep'] at this; simpa using this
    have hC : ∑ i, ∑ j, (A0 + 𝓐 y0) i j * (-Y0) i j = 0 := by
      have e : A0 + 𝓐 y0 = (A0 + 𝓐 ys) + 𝓐 (y0 - ys) := by rw [map_sub]; abel
      rw [e]
      simp only [Matrix.add_apply, Matrix.neg_apply, add_mul, mul_neg, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
      have := hA (y0 - ys)
      simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib] at hB
      linarith
    have hY : -Y0 = 0 := pd_pair_zero _ _ hy0 hnegpsd hC
    have hY0 : Y0 = 0 := neg_eq_zero.mp hY
    have := hlt _ ha0
    rw [hrep] at this
    have h2 := hge _ ⟨0, rfl⟩
    rw [hS0] at h2
    simp [hY0, ← h, a0] at this
    linarith
  refine ⟨(-lam⁻¹) • Y0, ?_, ?_, ?_⟩
  · apply psd_of_qf
    · ext i j; simp [hsym0 i j]
    · intro v
      have : qf ((-lam⁻¹) • Y0) v = -lam⁻¹ * qf Y0 v := by
        simp only [qf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_)); ring
      rw [this]
      have := hneg v
      have : 0 < lam⁻¹ := inv_pos.mpr hlampos
      nlinarith
  · intro d
    rw [trace_sym _ _ (fun i j => by simp [hsym0 i j])]
    have := hg d
    rw [hrep'] at this
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e : ∑ i, ∑ j, (𝓐 d) i j * (-lam⁻¹ * Y0 i j)
        = -lam⁻¹ * ∑ i, ∑ j, (𝓐 d) i j * Y0 i j := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_)); ring
    rw [e]
    field_simp
    linarith
  · rw [trace_sym _ _ (fun i j => by simp [hsym0 i j])]
    have := hS0
    rw [hSf] at this; simp only at this; rw [hrep'] at this
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e : ∑ i, ∑ j, (A0 + 𝓐 ys) i j * (-lam⁻¹ * Y0 i j)
        = -lam⁻¹ * ∑ i, ∑ j, (A0 + 𝓐 ys) i j * Y0 i j := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_)); ring
    rw [e]
    rw [map_zero, zero_mul, add_zero, add_zero] at this
    rw [this]; ring

end Dual


lemma trace_fb {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℝ) (B : Matrix (Fin a) (Fin b) ℝ)
    (C : Matrix (Fin b) (Fin a) ℝ) (E : Matrix (Fin b) (Fin b) ℝ) :
    (fromBlocks A B C E).trace = A.trace + E.trace := by
  simp [trace, Fintype.sum_sum_type]

open scoped MatrixOrder in
lemma psd_mul_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (Y M : Matrix ι ι ℝ)
    (hY : Y.PosSemidef) (hM : M.PosSemidef) (h : (Y * M).trace = 0) : Y * M = 0 := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  simp only [star_eq_conjTranspose] at *
  have e : (Bᴴ * B * (Cᴴ * C)).trace = ((C * Bᴴ)ᴴ * (C * Bᴴ)).trace := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show B * Cᴴ * (C * Bᴴ) = (B * (Cᴴ * C)) * Bᴴ by simp only [Matrix.mul_assoc],
      trace_mul_comm (B * (Cᴴ * C)) Bᴴ]
    simp only [Matrix.mul_assoc]
  rw [e, trace_conjTranspose_mul_self_eq_zero_iff] at h
  have h2 : B * Cᴴ = 0 := by
    have := congrArg conjTranspose h
    simpa [conjTranspose_mul] using this
  calc Bᴴ * B * (Cᴴ * C) = Bᴴ * (B * Cᴴ) * C := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h2]; simp

variable {m n p q : ℕ}

def Alin (D : SDPData m n p q) :
    ((Fin m → ℝ) × ℝ) →ₗ[ℝ] Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ where
  toFun y := fromBlocks (∑ i, y.1 i • D.Fs i - y.2 • (D.L * D.Lᵀ)) (∑ i, y.1 i • D.Rs i)ᵀ
    (∑ i, y.1 i • D.Rs i) (y.2 • (1 : Matrix (Fin q) (Fin q) ℝ))
  map_add' y z := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib,
      transpose_add, fromBlocks_add]
    congr 1; abel
  map_smul' c y := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      fromBlocks_smul]
    congr 1
    · simp only [smul_sub, Finset.smul_sum, smul_smul]
    · rw [← transpose_smul, Finset.smul_sum]; simp only [smul_smul]
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · rw [smul_smul]

def clin (c : Fin m → ℝ) : ((Fin m → ℝ) × ℝ) →ₗ[ℝ] ℝ where
  toFun y := c ⬝ᵥ y.1
  map_add' y z := by simp [dotProduct_add]
  map_smul' a y := by simp [dotProduct_smul]

lemma lmi_eq (D : SDPData m n p q) (y : (Fin m → ℝ) × ℝ) :
    D.lmi 0 0 + Alin D y = D.lmi y.1 y.2 := by
  simp only [SDPData.lmi, Alin, LinearMap.coe_mk, AddHom.coe_mk, fromBlocks_add, SDPData.F,
    SDPData.R, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, sub_zero,
    transpose_add, zero_add]
  congr 1; abel

lemma lmi_symm (D : SDPData m n p q) (hsym : D.Symmetric) (x : Fin m → ℝ) (τ : ℝ) :
    (D.lmi x τ).IsSymm := by
  apply IsSymm.fromBlocks
  · have hF : (D.F x).IsSymm := by
      unfold SDPData.F
      show (D.F0 + ∑ i, x i • D.Fs i)ᵀ = _
      rw [transpose_add, transpose_sum]
      simp only [transpose_smul, (hsym.2 _).eq, hsym.1.eq]
    have hL : (D.L * D.Lᵀ).IsSymm := by
      simp [IsSymm, transpose_mul]
    exact hF.sub (hL.smul _)
  · rfl
  · exact (isSymm_one).smul _

lemma tau_pos (D : SDPData m n p q) (h3a : D.H3a) (x : Fin m → ℝ) (τ : ℝ)
    (hf : (D.lmi x τ).PosSemidef) : 0 < τ := by
  by_contra hτ
  push_neg at hτ
  obtain ⟨N, hN, hker⟩ := h3a
  have hR : D.R x ≠ 0 := by
    intro h0
    have := hker 1 x (Or.inl one_ne_zero)
    have hp : D.pencil 1 x = D.R x := by simp [SDPData.pencil, SDPData.R]
    rw [hp, h0] at this
    apply hN; rw [← this]; ext v; simp
  obtain ⟨k, j, hkj⟩ : ∃ k j, D.R x k j ≠ 0 := by
    by_contra hc; push_neg at hc; exact hR (by ext k j; exact hc k j)
  set M := D.lmi x τ
  have hq : ∀ a b : ℝ, 0 ≤ a * a * M (Sum.inl j) (Sum.inl j) + a * b * M (Sum.inl j) (Sum.inr k)
      + b * a * M (Sum.inr k) (Sum.inl j) + b * b * M (Sum.inr k) (Sum.inr k) := by
    intro a b
    have := hf.dotProduct_mulVec_nonneg (Pi.single (Sum.inl j) a + Pi.single (Sum.inr k) b)
    rw [star_trivial] at this
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, single_dotProduct,
      Matrix.mulVec, dotProduct_single] at this
    simp [Pi.single_apply, mul_comm, mul_assoc, mul_left_comm, add_assoc] at this
    linarith
  set C := M (Sum.inl j) (Sum.inl j)
  have h12 : M (Sum.inl j) (Sum.inr k) = D.R x k j := by simp [M, SDPData.lmi]
  have h21 : M (Sum.inr k) (Sum.inl j) = D.R x k j := by simp [M, SDPData.lmi]
  have h22 : M (Sum.inr k) (Sum.inr k) = τ := by simp [M, SDPData.lmi]
  set r := D.R x k j
  have hr2 : 0 < r ^ 2 := by positivity
  set s := (|C| + 1) / (2 * r ^ 2) with hs
  have hs0 : 0 < s := by positivity
  have := hq 1 (-s * r)
  rw [h12, h21, h22] at this
  have hsr : s * r ^ 2 * 2 = |C| + 1 := by rw [hs]; field_simp
  have hC := le_abs_self C
  nlinarith [mul_nonneg (mul_nonneg hs0.le hs0.le) (mul_nonneg (sq_nonneg r) (neg_nonneg.2 hτ))]


lemma Alin_ei (D : SDPData m n p q) (i : Fin m) :
    Alin D (Pi.single i 1, 0) = fromBlocks (D.Fs i) (D.Rs i)ᵀ (D.Rs i) 0 := by
  simp [Alin, Pi.single_apply, ite_smul, Finset.sum_ite_eq']

lemma Alin_tau (D : SDPData m n p q) :
    Alin D (0, 1) = fromBlocks (-(D.L * D.Lᵀ)) 0 0 1 := by
  simp [Alin]

theorem dual_core (D : SDPData m n p q) (c : Fin m → ℝ) (hc : c ≠ 0)
    (hsym : D.Symmetric) (h1 : D.Slater) (h3a : D.H3a)
    (x : Fin m → ℝ) (τ : ℝ) (hopt : D.IsOptimal c (x, τ)) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧ Z ≠ 0 ∧
      (Z * D.G (x, τ)).trace = 0 ∧
      (∀ i : Fin m,
        (Z * (D.Fs i - τ⁻¹ • ((D.R x)ᵀ * D.Rs i + (D.Rs i)ᵀ * D.R x))).trace = c i) ∧
      τ ^ 2 * (D.L * D.Lᵀ * Z).trace = ((D.R x)ᵀ * D.R x * Z).trace := by
  have hfeas : (D.lmi x τ).PosSemidef := hopt.1
  have hτ := tau_pos D h3a x τ hfeas
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  obtain ⟨Y, hY, hstat, hcomp⟩ := sdp_dual (D.lmi 0 0) (Alin D) (clin c)
    (fun y => by rw [lmi_eq]; exact lmi_symm D hsym _ _) (x, τ)
    (by rw [lmi_eq]; exact hfeas)
    (fun y hy => by rw [lmi_eq] at hy; exact hopt.2 y hy)
    (by obtain ⟨x0, τ0, h⟩ := h1; exact ⟨(x0, τ0), by rw [lmi_eq]; exact h⟩)
  rw [lmi_eq] at hcomp
  have hYM := psd_mul_zero Y _ hY hfeas hcomp
  have hYsym : Yᵀ = Y := by
    have := hY.isHermitian; rw [isHermitian_iff_isSymm] at this; exact this
  set Z := Y.toBlocks₁₁ with hZ
  set V := Y.toBlocks₁₂ with hV
  set W := Y.toBlocks₂₁ with hW
  set U := Y.toBlocks₂₂ with hU
  have hYb : Y = fromBlocks Z V W U := (fromBlocks_toBlocks Y).symm
  have hWV : W = Vᵀ := by
    ext i j; simp only [hW, hV, toBlocks₂₁, toBlocks₁₂, transpose_apply, of_apply]
    exact congrFun (congrFun hYsym (Sum.inl j)) (Sum.inr i)
  have hZsym : Zᵀ = Z := by
    ext i j; simp only [hZ, toBlocks₁₁, transpose_apply, of_apply]
    exact congrFun (congrFun hYsym (Sum.inl i)) (Sum.inl j)
  set R := D.R x with hR
  have hlmi : D.lmi x τ = fromBlocks (D.F x - τ • (D.L * D.Lᵀ)) Rᵀ R
      (τ • (1 : Matrix (Fin q) (Fin q) ℝ)) := rfl
  rw [hYb, hlmi, fromBlocks_multiply, ← fromBlocks_zero] at hYM
  obtain ⟨e11, e12, e21, e22⟩ := fromBlocks_inj.mp hYM
  simp only [Matrix.mul_smul, Matrix.mul_one] at e12 e22
  have hVe : V = -τ⁻¹ • (Z * Rᵀ) := by
    have : τ • V = -(Z * Rᵀ) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact e12
    rw [neg_smul, ← smul_neg, ← this, smul_smul, inv_mul_cancel₀ hτ0, one_smul]
  have hUe : τ • U = τ⁻¹ • (R * Z * Rᵀ) := by
    have : τ • U = -(W * Rᵀ) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact e22
    rw [this, hWV, hVe, transpose_smul, transpose_mul, hZsym, transpose_transpose,
      Matrix.smul_mul, neg_smul, neg_neg]
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  · have := hY.submatrix (Sum.inl : Fin n → Fin n ⊕ Fin q)
    exact this
  · intro hZ0
    apply hc
    have hV0 : V = 0 := by rw [hVe, hZ0]; simp
    have hW0 : W = 0 := by rw [hWV, hV0]; simp
    have hU0 : U = 0 := by
      have : τ • U = 0 := by rw [hUe, hZ0]; simp
      rwa [smul_eq_zero, or_iff_right hτ0] at this
    have hY0 : Y = 0 := by rw [hYb, hZ0, hV0, hW0, hU0, fromBlocks_zero]
    funext i
    have := hstat (Pi.single i 1, 0)
    rw [hY0] at this
    simpa [clin] using this.symm
  · have e11' : Z * (D.F x - τ • (D.L * D.Lᵀ)) - τ⁻¹ • (Z * (Rᵀ * R)) = 0 := by
      rw [hVe] at e11
      have : -τ⁻¹ • (Z * Rᵀ) * R = -(τ⁻¹ • (Z * (Rᵀ * R))) := by
        rw [Matrix.smul_mul, Matrix.mul_assoc, neg_smul]
      rw [this, ← sub_eq_add_neg] at e11; exact e11
    have : Z * D.G (x, τ) = Z * (D.F x - τ • (D.L * D.Lᵀ)) - τ⁻¹ • (Z * (Rᵀ * R)) := by
      simp only [SDPData.G, Matrix.mul_sub, Matrix.mul_smul, hR]
    rw [this, e11', trace_zero]
  · intro i
    have := hstat (Pi.single i 1, 0)
    rw [Alin_ei, hYb, fromBlocks_multiply, trace_fb] at this
    simp only [clin, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_single, mul_one] at this
    rw [← this, hWV, hVe]
    simp only [Matrix.mul_zero, add_zero, trace_add, Matrix.mul_sub, Matrix.mul_add,
      Matrix.mul_smul, trace_sub, trace_smul, transpose_smul, transpose_mul, hZsym,
      transpose_transpose, Matrix.smul_mul, trace_smul, smul_eq_mul, neg_mul]
    have t1 : (R * Z * (D.Rs i)ᵀ).trace = (Z * ((D.Rs i)ᵀ * R)).trace := by
      rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
    have t2 : (Z * Rᵀ * D.Rs i).trace = (Z * (Rᵀ * D.Rs i)).trace := by
      rw [Matrix.mul_assoc]
    rw [t1, t2]
    ring
  · have := hstat (0, 1)
    rw [Alin_tau, hYb, fromBlocks_multiply, trace_fb] at this
    simp only [clin, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_zero, Matrix.mul_zero,
      add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, trace_neg] at this
    have hU2 : τ ^ 2 * U.trace = (Rᵀ * R * Z).trace := by
      have := congrArg (fun M => τ * M.trace) hUe
      simp only [trace_smul, smul_eq_mul] at this
      rw [sq, mul_assoc, this, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul,
        Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
      exact trace_mul_comm _ _
    rw [trace_mul_comm (D.L * D.Lᵀ) Z, ← hU2]
    have : U.trace = (Z * (D.L * D.Lᵀ)).trace := by linarith
    rw [this]

end RobustSDP.Uniqueness

open RobustSDP.Uniqueness


theorem solution {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (hc : c ≠ 0)
    (hsym : D.Symmetric) (h1 : D.Slater) (h2 : D.InfCompact c) (h3a : D.H3a)
    (x : Fin m → ℝ) (τ : ℝ) (hopt : D.IsOptimal c (x, τ)) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧ Z ≠ 0 ∧
      (Z * D.G (x, τ)).trace = 0 ∧
      (∀ i : Fin m,
        (Z * (D.Fs i - τ⁻¹ • ((D.R x)ᵀ * D.Rs i + (D.Rs i)ᵀ * D.R x))).trace = c i) ∧
      τ ^ 2 * (D.L * D.Lᵀ * Z).trace = ((D.R x)ᵀ * D.R x * Z).trace := by
  exact dual_core D c hc hsym h1 h3a x τ hopt
