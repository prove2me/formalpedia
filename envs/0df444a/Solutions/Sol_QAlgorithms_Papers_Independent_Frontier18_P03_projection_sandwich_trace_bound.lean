-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P03.projection_sandwich_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:45:46.709195+00:00
-- url     : https://prove2.me/submissions/7c9391f0-714a-484f-a3d2-d33cc99f9dbd

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P03

open QAlgorithms.Papers.Independent.Frontier18.P03
open scoped InnerProductSpace

namespace X6F03L6

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

theorem proj_compl {P : H →L[ℂ] H} (hP : IsOrthogonalProjection P) :
    IsOrthogonalProjection (1 - P) := by
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun v => ?_, fun u v => ?_⟩
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub, h1]
    abel
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_left,
      inner_sub_right, h2]

theorem re_sym {P : H →L[ℂ] H} (hP : IsOrthogonalProjection P) (u w : H) :
    (⟪P u, w⟫).re = (⟪u, P w⟫).re := by rw [hP.2]

theorem re_swap (u w : H) : (⟪u, w⟫).re = (⟪w, u⟫).re := by
  rw [← inner_conj_symm, Complex.conj_re]

theorem nonneg {P : H →L[ℂ] H} (hP : IsOrthogonalProjection P) (u : H) :
    0 ≤ (⟪u, P u⟫).re := by
  have : ⟪u, P u⟫ = ⟪P u, P u⟫ := by rw [hP.2, hP.1]
  rw [this]
  have := @inner_self_nonneg ℂ H _ _ _ (P u)
  simpa using this

/-- per-vector inequality -/
theorem per_vec {nu tau : H →L[ℂ] H} (hnu : IsOrthogonalProjection nu)
    (htau : IsOrthogonalProjection tau) (v : H) :
    2 * (⟪nu v, (1 - tau) (v - nu v)⟫).re ≤
      (⟪v, (tau.comp (nu.comp tau)) v⟫).re - (⟪v, nu v⟫).re + 2 * (⟪v, (1 - tau) v⟫).re := by
  set T := 1 - tau with hT
  have hTp := proj_compl htau
  have htauT : ∀ w, tau w = w - T w := by intro w; simp [hT]
  have hexp : (⟪v, (tau.comp (nu.comp tau)) v⟫).re =
      (⟪v, nu v⟫).re - 2 * (⟪T v, nu v⟫).re + (⟪v, T (nu (T v))⟫).re := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [htauT v, map_sub, htauT (nu v - nu (T v))]
    simp only [inner_sub_right, Complex.sub_re, map_sub]
    have e1 : (⟪v, T (nu v)⟫).re = (⟪T v, nu v⟫).re := (re_sym hTp v (nu v)).symm
    have e2 : (⟪v, nu (T v)⟫).re = (⟪T v, nu v⟫).re := by
      rw [← re_sym hnu v (T v), re_swap]
    rw [e1, e2]; ring
  have h1 := nonneg hnu (T v)
  have h1' : (⟪v, T (nu (T v))⟫).re = (⟪T v, nu (T v)⟫).re := (re_sym hTp v _).symm
  have h2 := nonneg hTp (v - nu v)
  -- ⟪T v, v - nu v⟫ = ⟪T (nu v), v - nu v⟫ + ⟪T (v - nu v), v - nu v⟫
  have h3 : (⟪T v, v - nu v⟫).re = (⟪nu v, T (v - nu v)⟫).re + (⟪v - nu v, T (v - nu v)⟫).re := by
    have : T v = T (nu v) + T (v - nu v) := by rw [← map_add]; congr 1; abel
    rw [this, inner_add_left, Complex.add_re, re_sym hTp, re_sym hTp]
  have h4 : (⟪T v, v - nu v⟫).re = (⟪v, T v⟫).re - (⟪T v, nu v⟫).re := by
    rw [inner_sub_right, Complex.sub_re, re_sym hTp]
  rw [hexp, h1']
  linarith


theorem pars {I : Type*} (e : HilbertBasis I ℂ H) (x : H) :
    HasSum (fun i => ‖⟪e i, x⟫‖ ^ 2) (‖x‖ ^ 2) := by
  have := lp.hasSum_norm (p := 2) (by norm_num) (e.repr x)
  simp only [HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map] at this
  simpa [Real.rpow_two] using this

theorem summ_smul (a b : ℕ → H) (ha : Summable fun k => ‖a k‖ ^ 2)
    (hb : Summable fun k => ‖b k‖ ^ 2) (Z : H →L[ℂ] H) (w : H) :
    Summable fun k => ⟪a k, Z w⟫ • b k := by
  refine Summable.of_norm_bounded ((ha.add hb).mul_left (‖Z‖ * ‖w‖ / 2)) fun k => ?_
  rw [norm_smul]
  have h1 : ‖⟪a k, Z w⟫‖ ≤ ‖a k‖ * (‖Z‖ * ‖w‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (Z.le_opNorm w) (norm_nonneg _))
  have h2 : ‖a k‖ * ‖b k‖ ≤ (‖a k‖ ^ 2 + ‖b k‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]
  have h3 : 0 ≤ ‖Z‖ * ‖w‖ := by positivity
  calc ‖⟪a k, Z w⟫‖ * ‖b k‖ ≤ ‖a k‖ * (‖Z‖ * ‖w‖) * ‖b k‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = (‖Z‖ * ‖w‖) * (‖a k‖ * ‖b k‖) := by ring
    _ ≤ (‖Z‖ * ‖w‖) * ((‖a k‖ ^ 2 + ‖b k‖ ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 h3
    _ = ‖Z‖ * ‖w‖ / 2 * (‖a k‖ ^ 2 + ‖b k‖ ^ 2) := by ring

/-- vanishing of the cross trace -/
theorem cross (a b : ℕ → H) (ha : Summable fun k => ‖a k‖ ^ 2)
    (hb : Summable fun k => ‖b k‖ ^ 2) (h0 : ∀ w, ∑' k, ⟪a k, w⟫ • b k = 0) (Z : H →L[ℂ] H) :
    ∑' k, ⟪a k, Z (b k)⟫ = 0 := by
  obtain ⟨I, e, -⟩ := exists_hilbertBasis ℂ H
  set F : ℕ → I → ℂ := fun k i => ⟪a k, Z (e i)⟫ * ⟪e i, b k⟫
  have hrow : ∀ k, HasSum (fun i => F k i) ⟪a k, Z (b k)⟫ := by
    intro k
    have := ((e.hasSum_repr (b k)).mapL Z).mapL (innerSL ℂ (a k))
    refine this.congr_fun fun i => ?_
    simp only [F, innerSL_apply_apply, map_smul, inner_smul_right, HilbertBasis.repr_apply_apply]
    ring
  set Zs := ContinuousLinearMap.adjoint Z
  set G : ℕ × I → ℝ := fun p => (‖⟪e p.2, Zs (a p.1)⟫‖ ^ 2 + ‖⟪e p.2, b p.1⟫‖ ^ 2) / 2
  have hG : Summable G := by
    rw [summable_prod_of_nonneg (fun p => by positivity)]
    refine ⟨fun k => ?_, ?_⟩
    · exact (((pars e (Zs (a k))).summable).add (pars e (b k)).summable).div_const 2
    · have : (fun k => ∑' i, G (k, i)) = fun k => (‖Zs (a k)‖ ^ 2 + ‖b k‖ ^ 2) / 2 := by
        funext k
        exact (((pars e (Zs (a k))).add (pars e (b k))).div_const 2).tsum_eq
      rw [this]
      refine ((Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
        (ha.mul_left (‖Zs‖ ^ 2))).add hb).div_const 2
      have := Zs.le_opNorm (a k)
      have h0 : 0 ≤ ‖Zs (a k)‖ := norm_nonneg _
      calc ‖Zs (a k)‖ ^ 2 ≤ (‖Zs‖ * ‖a k‖) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = ‖Zs‖ ^ 2 * ‖a k‖ ^ 2 := by ring
  have hF : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded hG fun p => ?_
    simp only [Function.uncurry, F, G, norm_mul]
    have : ⟪a p.1, Z (e p.2)⟫ = ⟪Zs (a p.1), e p.2⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [this, norm_inner_symm]
    nlinarith [sq_nonneg (‖⟪e p.2, Zs (a p.1)⟫‖ - ‖⟪e p.2, b p.1⟫‖)]
  have hcol : ∀ i, ∑' k, F k i = 0 := by
    intro i
    have hs := summ_smul a b ha hb Z (e i)
    have := (innerSL ℂ (e i)).map_tsum hs
    rw [h0 (Z (e i)), map_zero] at this
    rw [this]
    congr 1; funext k
    simp only [F, innerSL_apply_apply, inner_smul_right]
  calc ∑' k, ⟪a k, Z (b k)⟫ = ∑' k, ∑' i, F k i := by
        congr 1; funext k; exact (hrow k).tsum_eq.symm
    _ = ∑' i, ∑' k, F k i := hF.tsum_comm.symm
    _ = 0 := by simp [hcol]

end X6F03L6

open X6F03L6 in
theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (rho : DensityPresentation H) (nu tau : H →L[ℂ] H)
    (hnu : IsOrthogonalProjection nu) (htau : IsOrthogonalProjection tau)
    (hcomm : ∀ v, densityAction rho (nu v) = nu (densityAction rho v)) :
    traceAgainst rho (tau.comp (nu.comp tau)) ≥
      traceAgainst rho nu - 2 * traceAgainst rho (1 - tau) := by
  set v := rho.vectors
  have hv : Summable fun k => ‖v k‖ ^ 2 := rho.mass.summable
  have sq_bound : ∀ (A : H →L[ℂ] H), Summable fun k => ‖A (v k)‖ ^ 2 := by
    intro A
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hv.mul_left (‖A‖ ^ 2))
    have := A.le_opNorm (v k)
    calc ‖A (v k)‖ ^ 2 ≤ (‖A‖ * ‖v k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = ‖A‖ ^ 2 * ‖v k‖ ^ 2 := by ring
  have sre : ∀ A : H →L[ℂ] H, Summable fun k => (inner ℂ (v k) (A (v k))).re := by
    intro A
    refine Summable.of_norm_bounded (hv.mul_left ‖A‖) fun k => ?_
    calc ‖(inner ℂ (v k) (A (v k))).re‖ ≤ ‖inner ℂ (v k) (A (v k))‖ := by
          simpa using Complex.abs_re_le_norm _
      _ ≤ ‖v k‖ * ‖A (v k)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v k‖ * (‖A‖ * ‖v k‖) := mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖ * ‖v k‖ ^ 2 := by ring
  set a : ℕ → H := fun k => nu (v k)
  set b : ℕ → H := fun k => (1 - nu) (v k)
  have hb_eq : ∀ k, b k = v k - a k := fun k => by simp [b, a]
  have ha : Summable fun k => ‖a k‖ ^ 2 := sq_bound nu
  have hb : Summable fun k => ‖b k‖ ^ 2 := sq_bound (1 - nu)
  -- commutation gives the vanishing operator
  have hsv : ∀ w, Summable fun k => inner ℂ (v k) w • v k := fun w => by
    have := summ_smul v v hv hv 1 w
    simpa using this
  have hsa : ∀ w, Summable fun k => inner ℂ (a k) w • v k := fun w => by
    have := summ_smul a v ha hv 1 w
    simpa using this
  have h0 : ∀ w, ∑' k, inner ℂ (a k) w • b k = 0 := by
    intro w
    have hc := hcomm w
    simp only [densityAction] at hc
    change ∑' k, inner ℂ (v k) (nu w) • v k = nu (∑' k, inner ℂ (v k) w • v k) at hc
    have e1 : ∀ k, inner ℂ (v k) (nu w) = inner ℂ (a k) w := fun k => (hnu.2 _ _).symm
    simp only [e1] at hc
    rw [nu.map_tsum (hsv w)] at hc
    -- hc : ∑' ⟪a k, w⟫ • v k = ∑' ⟪v k, w⟫ • nu (v k)
    have hc2 := congrArg nu hc
    rw [nu.map_tsum (hsa w), nu.map_tsum ((hsv w).mapL nu)] at hc2
    simp only [map_smul, hnu.1] at hc2
    -- hc2 : ∑' ⟪a k, w⟫ • a k = ∑' ⟪v k, w⟫ • a k
    have hsplit : ∀ k, inner ℂ (a k) w • b k = inner ℂ (a k) w • v k - inner ℂ (a k) w • a k := by
      intro k; rw [hb_eq, smul_sub]
    simp only [hsplit]
    have hsaa : Summable fun k => inner ℂ (a k) w • a k := by
      have := summ_smul a a ha ha 1 w; simpa using this
    rw [Summable.tsum_sub (hsa w) hsaa, hc, hc2]
    simp only [map_smul]
    exact sub_self _
  have hcross := cross a b ha hb h0 (1 - tau)
  have hcs : Summable fun k => inner ℂ (a k) ((1 - tau) (b k)) := by
    refine Summable.of_norm_bounded ((ha.add hb).mul_left (‖(1 - tau : H →L[ℂ] H)‖ / 2)) fun k => ?_
    have h1 := (norm_inner_le_norm (𝕜 := ℂ) (a k) ((1 - tau) (b k))).trans
      (mul_le_mul_of_nonneg_left ((1 - tau).le_opNorm (b k)) (norm_nonneg _))
    have h2 : ‖a k‖ * ‖b k‖ ≤ (‖a k‖ ^ 2 + ‖b k‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]
    have h3 : 0 ≤ ‖(1 - tau : H →L[ℂ] H)‖ := norm_nonneg _
    nlinarith
  have hre : ∑' k, 2 * (inner ℂ (a k) ((1 - tau) (b k))).re = 0 := by
    have := (hcs.hasSum.mapL Complex.reCLM).mul_left 2
    rw [hcross] at this
    simpa using this.tsum_eq
  have hle : ∀ k, 2 * (inner ℂ (a k) ((1 - tau) (b k))).re ≤
      (inner ℂ (v k) ((tau.comp (nu.comp tau)) (v k))).re - (inner ℂ (v k) (nu (v k))).re +
        2 * (inner ℂ (v k) ((1 - tau) (v k))).re := by
    intro k
    have := per_vec hnu htau (v k)
    rwa [show (1 - tau) (v k - nu (v k)) = (1 - tau) (b k) by rw [hb_eq]] at this
  have hsum := Summable.tsum_le_tsum hle
    (((hcs.mapL Complex.reCLM).mul_left 2))
    (((sre _).sub (sre nu)).add ((sre (1 - tau)).mul_left 2))
  rw [hre, Summable.tsum_add ((sre _).sub (sre nu)) ((sre (1 - tau)).mul_left 2),
    Summable.tsum_sub (sre _) (sre nu), tsum_mul_left] at hsum
  simp only [traceAgainst, ge_iff_le]
  linarith
