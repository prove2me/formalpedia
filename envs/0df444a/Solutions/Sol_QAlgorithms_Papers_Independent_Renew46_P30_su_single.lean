-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P30.su_single
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:35:37.810582+00:00
-- url     : https://prove2.me/submissions/2814f753-8cb4-4c5b-9e93-60d2b1d82c2c

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30
noncomputable section
open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)
open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)
open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)
open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

theorem g66d_coe_cont {d : ℕ} (i j : Fin d) :
    Continuous (fun U : SU d => (U : Matrix (Fin d) (Fin d) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem g66d_F_cont {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    Continuous (fun U : SU d => ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact continuous_finsetSum _ fun k _ =>
    (continuous_finsetSum _ fun l _ => (g66d_coe_cont i l).mul continuous_const).mul
      (g66d_coe_cont j k).star

theorem g66d_scalar {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ W ∈ Matrix.unitaryGroup (Fin d) ℂ, W * T * Wᴴ = T) :
    ∀ a b, T a b = if a = b then T a a else 0 := by
  intro a b
  split_ifs with hab
  · subst hab; rfl
  · -- diagonal sign matrix
    set s : Fin d → ℂ := fun k => if k = a then -1 else 1
    have hW : Matrix.diagonal s ∈ Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]; congr 1; funext k
      simp only [s, Pi.star_apply]; split_ifs <;> simp
    have := congrFun (congrFun (h _ hW) a) b
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    simp only [Pi.star_apply, s, if_pos rfl, if_neg (Ne.symm hab), star_one, mul_one] at this
    have : 2 * T a b = 0 := by linear_combination -this
    simpa using this

theorem g66d_diag {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ W ∈ Matrix.unitaryGroup (Fin d) ℂ, W * T * Wᴴ = T) (a b : Fin d) :
    T a a = T b b := by
  set W : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => if j = Equiv.swap a b i then 1 else 0
  have hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    simp only [W, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
    simp only [apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, (Equiv.swap a b).injective.ne hij, eq_comm]
  have := congrFun (congrFun (h _ hW) a) a
  rw [← this]
  simp only [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp only [apply_ite star, star_one, star_zero, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul]
  simp [Finset.sum_ite_eq', Equiv.swap_apply_left]

theorem g66d_root {d : ℕ} (hd : 0 < d) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ c : ℂ, star c * c = 1 ∧ c • W ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  set w := W.det
  have hw : star w * w = 1 := by
    have h1 : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
    exact this
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
  set r : ℂ := w ^ ((d : ℂ)⁻¹)
  have hr : r ^ d = w := Complex.cpow_nat_inv_pow w (by omega)
  have hr0 : r ≠ 0 := by intro h0; rw [h0, zero_pow (by omega)] at hr; exact hw0 hr.symm
  have hrn : ‖r‖ = 1 := by
    have h2 : ‖w‖ = 1 := by
      have : ‖star w * w‖ = 1 := by rw [hw]; simp
      rw [norm_mul, norm_star] at this
      nlinarith [norm_nonneg w]
    rw [← hr, norm_pow] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg r) (by omega)).mp h2
  refine ⟨r⁻¹, ?_, ?_⟩
  · have : star r * r = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hrn]; simp
    rw [star_inv₀, ← mul_inv, this, inv_one]
  · rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hW ⊢
      rw [star_smul, smul_mul_smul_comm, hW]
      have : r⁻¹ * star r⁻¹ = 1 := by
        rw [star_inv₀, Complex.star_def, ← mul_inv, Complex.mul_conj', hrn]; simp
      rw [this, one_smul]
    · rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hr]
      exact inv_mul_cancel₀ hw0

theorem g66d_twirl {d : ℕ} (hd : 0 < d) (mu : Measure (SU d)) [mu.IsHaarMeasure]
    [IsProbabilityMeasure mu] (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    Integrable (fun U : SU d => ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j) mu ∧
    (∫ U : SU d, ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j ∂mu) =
      (X.trace / d) * (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  have hint : ∀ i j, Integrable (fun U : SU d => ((U : Matrix (Fin d) (Fin d) ℂ) * X *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j) mu := fun i j =>
    (g66d_F_cont X i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint i j, ?_⟩
  set T : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => ∫ U : SU d,
    ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i j ∂mu with hT
  -- invariance under SU
  have hSU : ∀ V : SU d, (V : Matrix (Fin d) (Fin d) ℂ) * T * (V : Matrix (Fin d) (Fin d) ℂ)ᴴ = T := by
    intro V
    ext a b
    have e1 : ∀ U : SU d, ((V * U : SU d) : Matrix (Fin d) (Fin d) ℂ) * X * ((V * U : SU d) : Matrix (Fin d) (Fin d) ℂ)ᴴ
        = (V : Matrix (Fin d) (Fin d) ℂ) * ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) *
          (V : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
      intro U
      rw [Submonoid.coe_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    have e2 := integral_mul_left_eq_self (μ := mu) (fun U : SU d => ((U : Matrix (Fin d) (Fin d) ℂ) * X *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) a b) V
    simp only [e1] at e2
    rw [hT, Matrix.of_apply, ← e2]
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_mul_const, integral_finsetSum]
      · refine congrArg (· * _) (Finset.sum_congr rfl fun l _ => ?_)
        rw [integral_const_mul]
      · intro l _; exact (hint l k).const_mul _
    · intro k _
      exact (integrable_finsetSum _ fun l _ => (hint l k).const_mul _).mul_const _
  have hU : ∀ W ∈ Matrix.unitaryGroup (Fin d) ℂ, W * T * Wᴴ = T := by
    intro W hW
    obtain ⟨c, hc, hcW⟩ := g66d_root hd W hW
    have := hSU ⟨c • W, hcW⟩
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at this
    rw [show star c * c = 1 from hc, one_smul] at this
    exact this
  -- trace
  have htr : T.trace = X.trace := by
    simp only [Matrix.trace, Matrix.diag, hT, Matrix.of_apply]
    rw [← integral_finsetSum _ fun k _ => hint k k]
    have : ∀ U : SU d, ∑ k, ((U : Matrix (Fin d) (Fin d) ℂ) * X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) k k = X.trace := by
      intro U
      have h1 : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * (U : Matrix (Fin d) (Fin d) ℂ) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp U.2.1
      have := Matrix.trace_mul_cycle (U : Matrix (Fin d) (Fin d) ℂ) X (U : Matrix (Fin d) (Fin d) ℂ)ᴴ
      rw [h1, Matrix.one_mul] at this
      exact this
    simp only [this, integral_const, probReal_univ, one_smul]
    rfl
  have hsc := g66d_scalar T hU
  have hdg := g66d_diag T hU
  have a0 : Fin d := ⟨0, hd⟩
  have htr2 : T.trace = d * T i i := by
    simp only [Matrix.trace, Matrix.diag]
    rw [Finset.sum_congr rfl fun k _ => hdg k i]; simp
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hii : T i i = X.trace / d := by rw [← htr, htr2]; field_simp
  change T i j = _
  rw [hsc i j, Matrix.one_apply]
  split_ifs with h
  · rw [hii]; ring
  · ring

theorem g66d_hsum {d : ℕ} (psi : EuclideanSpace ℂ (Fin d)) (hn : ‖psi‖ = 1) :
    ∑ a, psi a * conj (psi a) = 1 := by
  have h := EuclideanSpace.norm_eq psi
  rw [hn] at h
  have h2 : ∑ i, ‖psi i‖ ^ 2 = (1 : ℝ) := by
    have := congrArg (· ^ 2) h
    simp only [one_pow] at this
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at this
    exact this.symm
  simp only [Complex.mul_conj']
  exact_mod_cast h2

theorem g66d_trBP {d : ℕ} (psi : EuclideanSpace ℂ (Fin d)) (hn : ‖psi‖ = 1)
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.PosSemidef) :
    (B * QAlgorithms.pureDensity psi).trace.re ≤ B.trace.re := by
  set P := QAlgorithms.pureDensity psi
  have hs := g66d_hsum psi hn
  have hPP : P * P = P := by
    ext a b
    simp only [P, QAlgorithms.pureDensity, Matrix.mul_apply, Matrix.of_apply]
    calc ∑ k, psi a * conj (psi k) * (psi k * conj (psi b))
        = psi a * conj (psi b) * ∑ k, psi k * conj (psi k) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by rw [hs, mul_one]
  have hPh : Pᴴ = P := by
    ext a b
    simp [P, QAlgorithms.pureDensity, Matrix.conjTranspose_apply, mul_comm]
  set Q := 1 - P
  have hQh : Qᴴ = Q := by simp [Q, Matrix.conjTranspose_sub, hPh]
  have hQQ : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]; abel
  have hpsd := hB.conjTranspose_mul_mul_same Q
  rw [hQh] at hpsd
  have ht := hpsd.trace_nonneg
  have e : (Q * B * Q).trace = B.trace - (B * P).trace := by
    rw [Matrix.trace_mul_cycle, hQQ]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_mul_comm P B]
  rw [e] at ht
  have := (Complex.nonneg_iff.mp ht).1
  simp only [Complex.sub_re, Complex.zero_re] at this
  linarith

open QAlgorithms.Papers.Independent.Renew46.P30

theorem solution (d : ℕ) (hd : 0 < d) (mu : Measure (SU d))
    [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (psi : EuclideanSpace ℂ (Fin d)) (hn : ‖psi‖ = 1) :
    MatrixMaximum mu (fun g : SU d => (g : Matrix (Fin d) (Fin d) ℂ)) psi
      ((d : ℂ) • QAlgorithms.pureDensity psi) d := by
  have hs := g66d_hsum psi hn
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hPpsd : (QAlgorithms.pureDensity psi).PosSemidef := by
    have : QAlgorithms.pureDensity psi = Matrix.vecMulVec (WithLp.ofLp psi) (star (WithLp.ofLp psi)) := by
      ext a b; simp [QAlgorithms.pureDensity, Matrix.vecMulVec]
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _
  have htrP : (QAlgorithms.pureDensity psi).trace = 1 := by
    simp only [Matrix.trace, Matrix.diag, QAlgorithms.pureDensity, Matrix.of_apply]; exact hs
  refine ⟨⟨hPpsd.smul (by positivity), ?_, ?_⟩, ?_, ?_⟩
  · intro i j
    obtain ⟨h1, h2⟩ := g66d_twirl hd mu ((d : ℂ) • QAlgorithms.pureDensity psi) i j
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.trace_smul, htrP, smul_eq_mul, mul_one, div_self hdne, one_mul]
  · rintro g ⟨c, hc, hgc⟩
    set G : Matrix (Fin d) (Fin d) ℂ := (g : Matrix (Fin d) (Fin d) ℂ)
    have hact : ∀ a, ∑ k, G a k * psi k = c * psi a := by
      intro a
      have := congrArg (fun v : EuclideanSpace ℂ (Fin d) => v a) hgc
      simpa [QAlgorithms.act, Matrix.mulVec, dotProduct] using this
    have hu : Gᴴ * G = 1 := Matrix.mem_unitaryGroup_iff'.mp g.2.1
    have hcc : c * conj c = 1 := by
      rw [Complex.mul_conj', hc]; simp
    have hrow : ∀ b, ∑ k, G k b * conj (psi k) = c * conj (psi b) := by
      intro b
      have h1 : (Gᴴ * G) *ᵥ (WithLp.ofLp psi) = WithLp.ofLp psi := by rw [hu, Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec] at h1
      have h2 := congrFun h1 b
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply] at h2
      have h3 : ∀ k, (fun j => ∑ x, G j x * (WithLp.ofLp psi) x) k = c * psi k := by
        intro k; simpa using hact k
      simp only [h3] at h2
      have h4 := congrArg conj h2
      simp only [map_sum, map_mul, RCLike.star_def, Complex.conj_conj] at h4
      calc ∑ k, G k b * conj (psi k) = c * (∑ k, G k b * (conj c * conj (psi k))) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
            linear_combination (-(G k b * conj (psi k))) * hcc
        _ = c * conj (psi b) := by
            rw [show (∑ k, G k b * (conj c * conj (psi k))) = conj (psi b) by simpa using h4]
    ext a b
    simp only [Matrix.mul_apply, Matrix.smul_apply, QAlgorithms.pureDensity, Matrix.of_apply, smul_eq_mul]
    calc ∑ k, G a k * (↑d * (psi k * conj (psi b)))
        = ↑d * conj (psi b) * ∑ k, G a k * psi k := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = ↑d * psi a * ∑ k, G k b * conj (psi k) := by rw [hact, hrow]; ring
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  · unfold QAlgorithms.effectProb
    rw [Matrix.smul_mul]
    have hPP : (QAlgorithms.pureDensity psi * QAlgorithms.pureDensity psi).trace = 1 := by
      simp only [Matrix.trace, Matrix.diag, QAlgorithms.pureDensity, Matrix.mul_apply, Matrix.of_apply]
      calc ∑ a, ∑ k, psi a * conj (psi k) * (psi k * conj (psi a))
          = ∑ a, (psi a * conj (psi a)) * ∑ k, psi k * conj (psi k) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = 1 := by rw [hs]; simp [hs]
    rw [Matrix.trace_smul, hPP]; simp
  · rintro B ⟨hB, hN, -⟩
    have htrB : B.trace = d := by
      obtain ⟨_, h2⟩ := g66d_twirl hd mu B ⟨0, hd⟩ ⟨0, hd⟩
      have h3 := (hN ⟨0, hd⟩ ⟨0, hd⟩).2
      rw [h2] at h3
      simp only [Matrix.one_apply_eq, mul_one] at h3
      field_simp at h3; exact h3
    have := g66d_trBP psi hn B hB
    unfold QAlgorithms.effectProb
    rw [htrB] at this; simpa using this

end
