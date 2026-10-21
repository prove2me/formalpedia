-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P44.pureGramBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:52:09.855142+00:00
-- url     : https://prove2.me/submissions/c70be318-a4bc-4d6e-95db-42b331bd9822

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44
noncomputable section

open QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P16 (opCoeff)
open scoped Matrix

theorem g65a_tracePair_rankOne {I : Type} (w u : Hilbert I) :
    tracePair (InnerProductSpace.rankOne ℂ w w) (TC.rankOne u) = ‖inner ℂ w u‖ ^ 2 := by
  unfold tracePair
  have h1 : ∀ i j, opCoeff (InnerProductSpace.rankOne ℂ w w) i j * TC.rankOne u j i =
      (w i * star (u i)) * (star (w j) * u j) := by
    intro i j
    simp only [opCoeff, InnerProductSpace.rankOne_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.inner_single_right]
    simp [QAlgorithms.Papers.Independent.Dependency50.P33.rankOne]
    ring
  simp_rw [h1, tsum_mul_left]
  have h2 : ∑' j, star (w j) * u j = inner ℂ w u := by
    rw [lp.inner_eq_tsum]; exact tsum_congr (fun i => by simp [mul_comm])
  have h3 : ∑' i, w i * star (u i) = inner ℂ u w := by
    rw [lp.inner_eq_tsum]; exact tsum_congr (fun i => by simp)
  rw [h2, tsum_mul_right, h3, ← inner_conj_symm u w]
  rw [mul_comm, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq]
  norm_cast
theorem g65a_bessel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {M : ℕ}
    (w : Fin M → E) (h : (1 - Matrix.gram ℂ w).PosSemidef) (x : E) :
    ∑ k, ‖inner ℂ (w k) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  set a : Fin M → ℂ := fun k => inner ℂ (w k) x
  set u : E := ∑ k, a k • w k
  have hux : inner ℂ u x = ((∑ k, ‖a k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [u, sum_inner, inner_smul_left]
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [a]
    rw [← Complex.mul_conj', mul_comm]
  have hq := h.dotProduct_mulVec_nonneg a
  have hgram := Matrix.star_dotProduct_gram_mulVec (𝕜 := ℂ) w a a
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hgram] at hq
  have haa : star a ⬝ᵥ a = ((∑ k, ‖a k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Complex.mul_conj', mul_comm]; rfl
  rw [haa] at hq
  have hq' : ‖u‖ ^ 2 ≤ ∑ k, ‖a k‖ ^ 2 := by
    have h1 := (Complex.le_def.1 hq).1
    simp only [Complex.zero_re, Complex.sub_re, Complex.ofReal_re] at h1
    have : (inner ℂ u u).re = ‖u‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    linarith
  have hn := norm_sub_sq (𝕜 := ℂ) x u
  have hre : (inner ℂ x u).re = ∑ k, ‖a k‖ ^ 2 := by
    rw [← inner_conj_symm, hux, Complex.conj_ofReal, Complex.ofReal_re]
  have : 0 ≤ ‖x - u‖ ^ 2 := by positivity
  have hrr : RCLike.re (inner ℂ x u) = (inner ℂ x u).re := rfl
  have : ∑ k, ‖inner ℂ (w k) x‖ ^ 2 = ∑ k, ‖a k‖ ^ 2 := rfl
  linarith
def g65a_f (x : ℝ) : ℝ := if 0 < x then (Real.sqrt x)⁻¹ else 0

theorem g65a_cfc_facts {M : ℕ} (G : Matrix (Fin M) (Fin M) ℂ) (hG : 0 ≤ G) :
    cfc g65a_f G * G = CFC.sqrt G ∧ IsSelfAdjoint (cfc g65a_f G) ∧
    0 ≤ 1 - cfc g65a_f G * G * cfc g65a_f G := by
  have hsa : IsSelfAdjoint G := hG.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ G, 0 ≤ x := fun x hx => spectrum_nonneg_of_nonneg hG hx
  have hcont : ContinuousOn g65a_f (spectrum ℝ G) := (Matrix.finite_real_spectrum).continuousOn _
  refine ⟨?_, cfc_predicate _ _, ?_⟩
  · rw [CFC.sqrt_eq_real_sqrt G hG, cfcₙ_eq_cfc (hf := Real.continuous_sqrt.continuousOn) (hf0 := by simp)]
    nth_rewrite 2 [← cfc_id' ℝ G]
    rw [← cfc_mul g65a_f (fun x => x) G hcont]
    apply cfc_congr
    intro x hx
    have := hspec x hx
    simp only [g65a_f]
    split_ifs with h
    · have hs := Real.sqrt_pos.2 h
      have : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt this).symm
      field_simp
      nth_rewrite 1 [this]; ring
    · have : x = 0 := by linarith
      simp [this]
  · nth_rewrite 2 [← cfc_id' ℝ G]
    rw [← cfc_mul g65a_f (fun x => x) G hcont, ← cfc_mul _ g65a_f G ((Matrix.finite_real_spectrum).continuousOn _) hcont, ← cfc_one ℝ G,
      ← cfc_sub _ _ G]
    refine cfc_nonneg (fun x hx => ?_)
    have := hspec x hx
    simp only [g65a_f, Pi.one_apply]
    split_ifs with h
    · have hs := Real.sqrt_pos.2 h
      have : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt this).symm
      have e : (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = 1 := by
        nth_rewrite 2 [this]; field_simp
      rw [e]; norm_num
    · simp

theorem g65a_re_eff {I : Type} (u x : Hilbert I) :
    (inner ℂ x (InnerProductSpace.rankOne ℂ u u x)).re = ‖inner ℂ u x‖ ^ 2 := by
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm x u,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

set_option maxHeartbeats 1000000 in
theorem solution {I : Type} (M : ℕ) (hM : 0 < M)
    (v : Fin M → Hilbert I) (hv : ∀ k, ‖v k‖ = 1) :
    optimalCollectiveError (fun k => TC.rankOne (v k)) ≤
      ENNReal.ofReal (2 / (M : ℝ) * (Matrix.trace (1 - CFC.sqrt (pureSignalGram v))).re) ∧
    2 / (M : ℝ) * (Matrix.trace (1 - CFC.sqrt (pureSignalGram v))).re =
      (Matrix.trace ((1 - CFC.sqrt (pureSignalGram v)) ^ 2)).re / (M : ℝ) ∧
    optimalCollectiveError (fun k => TC.rankOne (v k)) ≤
      ENNReal.ofReal ((Matrix.trace ((1 - pureSignalGram v) ^ 2)).re / (M : ℝ)) ∧
    (Matrix.trace ((1 - pureSignalGram v) ^ 2)).re / (M : ℝ) =
      (∑ r : Fin M, ∑ s : Fin M, if r = s then 0 else
        ‖inner ℂ (v r) (v s)‖ ^ 2) / (M : ℝ) := by
  set G := pureSignalGram v with hGdef
  have hGg : G = Matrix.gram ℂ v := by ext i j; rfl
  have hG0 : 0 ≤ G := by rw [hGg]; exact Matrix.nonneg_iff_posSemidef.2 (Matrix.posSemidef_gram ℂ v)
  obtain ⟨hcG, hcsa, hH⟩ := g65a_cfc_facts G hG0
  set c := cfc g65a_f G with hc
  set S := CFC.sqrt G with hS
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg G
  have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.1 hS0
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG0
  have hSh : Sᴴ = S := hSpsd.1
  have hc_herm : ∀ i j, star (c j i) = c i j := by
    intro i j
    have : cᴴ = c := hcsa
    have h := congrFun (congrFun this i) j
    rw [Matrix.conjTranspose_apply] at h
    exact h
  have hGkk : ∀ k, G k k = 1 := by
    intro k
    show inner ℂ (v k) (v k) = 1
    rw [inner_self_eq_norm_sq_to_K, hv k]; simp
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have htrG : Matrix.trace G = (M : ℂ) := by
    simp [Matrix.trace, hGkk]
  -- vectors
  set w : Fin M → Hilbert I := fun k => ∑ j, (c j k) • v j with hw
  have hwv : ∀ k l, inner ℂ (w k) (v l) = S k l := by
    intro k l
    rw [← hcG]
    simp only [hw, sum_inner, inner_smul_left, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [starRingEnd_apply, hc_herm]; rfl
  have hww : Matrix.gram ℂ w = c * G * c := by
    ext k l
    simp only [Matrix.gram_apply, hw, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [starRingEnd_apply, hc_herm, hGdef]
    simp only [pureSignalGram]
    ring
  have hbes : (1 - Matrix.gram ℂ w).PosSemidef := by
    rw [hww]; exact Matrix.nonneg_iff_posSemidef.1 hH
  let X : Receiver I M :=
    { effect := fun k => InnerProductSpace.rankOne ℂ (w k) (w k)
      selfAdjoint := fun k => by simp
      positive := fun k x => by rw [g65a_re_eff]; positivity
      subidentity := fun x => by
        simp only [g65a_re_eff]
        exact g65a_bessel w hbes x }
  -- diagonal of S is real
  have hSre : ∀ k, S k k = ((S k k).re : ℂ) := by
    intro k
    have h1 : star (S k k) = S k k := by
      have := congrFun (congrFun hSh k) k
      simpa [Matrix.conjTranspose_apply] using this
    apply Complex.ext
    · simp
    · have := congrArg Complex.im h1
      simp at this
      simp; linarith
  have herr : collectiveAverageError (fun k => TC.rankOne (v k)) X =
      (∑ k, (1 - (S k k).re ^ 2)) / M := by
    unfold collectiveAverageError
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show 1 - tracePair (InnerProductSpace.rankOne ℂ (w k) (w k)) (TC.rankOne (v k)) = _
    rw [g65a_tracePair_rankOne, hwv, hSre k, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp
  have htr1S : (Matrix.trace (1 - S)).re = ∑ k, (1 - (S k k).re) := by
    simp [Matrix.trace, Matrix.sub_apply, Matrix.one_apply_eq]
  have hbound : collectiveAverageError (fun k => TC.rankOne (v k)) X ≤
      2 / (M : ℝ) * (Matrix.trace (1 - S)).re := by
    rw [herr, htr1S, show 2 / (M:ℝ) * ∑ k, (1 - (S k k).re) = (∑ k, 2 * (1 - (S k k).re)) / M by
      rw [← Finset.mul_sum]; ring]
    apply div_le_div_of_nonneg_right _ hMpos.le
    apply Finset.sum_le_sum
    intro k _
    nlinarith [sq_nonneg (1 - (S k k).re)]
  have hP1 : optimalCollectiveError (fun k => TC.rankOne (v k)) ≤
      ENNReal.ofReal (2 / (M : ℝ) * (Matrix.trace (1 - S)).re) :=
    iInf_le_of_le X (ENNReal.ofReal_le_ofReal hbound)
  -- part 2
  have hsq : (1 - S) ^ 2 = (2:ℂ) • (1 - S) + (G - 1) := by
    rw [← hSS, sq, two_smul]; noncomm_ring
  have htr1 : Matrix.trace (1 : Matrix (Fin M) (Fin M) ℂ) = (M : ℂ) := by simp
  have hP2 : 2 / (M : ℝ) * (Matrix.trace (1 - S)).re =
      (Matrix.trace ((1 - S) ^ 2)).re / (M : ℝ) := by
    rw [hsq, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub G, htrG, htr1]
    simp only [sub_self, add_zero, smul_eq_mul, Complex.mul_re]
    norm_num
    ring
  -- part 3
  have hid : (1 - G) ^ 2 = (2:ℂ) • (1 - S) + (G - 1) + ((1 - S) * S)ᴴ * ((1 - S) * S) +
      (2:ℂ) • ((1 - S)ᴴ * S * (1 - S)) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hSh, ← hSS,
      sq, two_smul, two_smul]
    noncomm_ring
  have hA : 0 ≤ (Matrix.trace (((1 - S) * S)ᴴ * ((1 - S) * S))).re :=
    (Complex.le_def.1 (Matrix.posSemidef_conjTranspose_mul_self ((1 - S) * S)).trace_nonneg).1
  have hB : 0 ≤ (Matrix.trace ((1 - S)ᴴ * S * (1 - S))).re :=
    (Complex.le_def.1 (hSpsd.conjTranspose_mul_mul_same (1 - S)).trace_nonneg).1
  have hP3 : 2 / (M : ℝ) * (Matrix.trace (1 - S)).re ≤
      (Matrix.trace ((1 - G) ^ 2)).re / (M : ℝ) := by
    rw [hid, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.trace_sub G 1, htrG, htr1, sub_self, add_zero, smul_eq_mul,
      smul_eq_mul]
    have h2re : ∀ z : ℂ, ((2:ℂ) * z).re = 2 * z.re := fun z => by simp
    simp only [Complex.add_re, h2re]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have : (0:ℝ) ≤ (M:ℝ)⁻¹ := by positivity
    nlinarith
  -- part 4
  have hP4 : (Matrix.trace ((1 - G) ^ 2)).re =
      ∑ r : Fin M, ∑ s : Fin M, if r = s then 0 else ‖inner ℂ (v r) (v s)‖ ^ 2 := by
    rw [sq, Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
    by_cases hrs : r = s
    · subst hrs; simp [hGkk]
    · rw [if_neg hrs, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_ne hrs,
        Matrix.one_apply_ne (Ne.symm hrs)]
      show ((0 - inner ℂ (v r) (v s)) * (0 - inner ℂ (v s) (v r))).re = _
      rw [← inner_conj_symm (v s) (v r), zero_sub, zero_sub, neg_mul_neg, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      norm_cast
  refine ⟨hP1, hP2, le_trans hP1 (ENNReal.ofReal_le_ofReal hP3), by rw [hP4]⟩
