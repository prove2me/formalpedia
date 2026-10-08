-- Prove2me | solution 1 for QueueingFundamentals.GG1.mdc_pgf
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:03:40.415897+00:00
-- url     : https://prove2.me/submissions/c2311b3a-1c8b-41e9-9d88-cc0c47c608d1

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_MDc



namespace QueueingFundamentals.GG1

section QFB

open Metric Set MeasureTheory

namespace QFBrouwerAux

/-! Brouwer fixed-point theorem, analytic (Milnor–Rogers) route.

* (A)–(D), (L1): there is no `C¹` retraction `r` of the closed unit ball `B ⊆ ℝᵈ` onto the
  sphere. For small `t`, `x ↦ x + t (r x - x)` is a bijection of `B`, so by change of variables
  `∫_B det(1 + t A) = vol B`; the left side is a polynomial in `t`, hence equals `vol B` at
  `t = 1`, where the integrand `det (Dr)` vanishes because `r` takes values on the sphere.
* (L2): a fixed-point-free `C¹` self-map of `B` would give such a retraction.
* (L3): continuous maps are approximated by `C¹` maps (Stone–Weierstrass).
* (L4): a compact convex set is a retract of a ball (nearest-point map) after a linear
  identification of `E` with `ℝᵈ`. -/

/-- Helper for `A_perturb`: a Lipschitz map vanishing on the sphere is controlled by the
distance to any point outside the ball. -/
theorem A_perturb_boundary {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : NNReal) (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0)
    {x z : EuclideanSpace ℝ (Fin d)} (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hz : z ∉ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ‖h x‖ ≤ L * dist x z := by
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  have hz' : 1 < ‖z‖ := by simpa using hz
  have hcont : ContinuousOn (fun s : ℝ => ‖x + s • (z - x)‖) (Icc 0 1) := by
    fun_prop
  have h1 : (1 : ℝ) ∈ Icc ((fun s : ℝ => ‖x + s • (z - x)‖) 0)
      ((fun s : ℝ => ‖x + s • (z - x)‖) 1) := by
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel]
    exact ⟨hx', hz'.le⟩
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := intermediate_value_Icc zero_le_one hcont h1
  have hwS : x + s • (z - x) ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by simpa using hs
  have hwB : x + s • (z - x) ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    sphere_subset_closedBall hwS
  have hhw : h (x + s • (z - x)) = 0 := h0 _ hwS
  calc ‖h x‖ = dist (h x) (h (x + s • (z - x))) := by rw [hhw, dist_zero_right]
    _ ≤ L * dist x (x + s • (z - x)) := hL.dist_le_mul x hx _ hwB
    _ ≤ L * dist x z := by
      gcongr
      rw [dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg hs0, norm_sub_rev]
      exact mul_le_of_le_one_left (norm_nonneg _) hs1

/-- Helper for `A_perturb`: the extension by zero outside the ball is globally Lipschitz. -/
theorem A_perturb_ext_lip {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : NNReal) (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0) :
    LipschitzWith L ((closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator h) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 <;>
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact hL.dist_le_mul x hx y hy
  · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hy, dist_zero_right]
    exact A_perturb_boundary h L hL h0 hx hy
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hy, dist_zero_left, dist_comm]
    exact A_perturb_boundary h L hL h0 hy hx
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy, dist_self]
    positivity

/-- (A) Lipschitz perturbation of the identity on the unit ball: injective and onto the ball. -/
theorem A_perturb {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : NNReal)
    (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0)
    (hB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, x + h x ∈ closedBall 0 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htL : t * L < 1) :
    InjOn (fun x => x + t • h x) (closedBall 0 1) ∧
      (fun x => x + t • h x) '' closedBall 0 1 = closedBall 0 1 := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only at hxy
    have h1 : x - y = t • h y - t • h x := by
      rw [sub_eq_sub_iff_add_eq_add, hxy, add_comm]
    have h2 : ‖x - y‖ ≤ t * L * ‖x - y‖ := by
      calc ‖x - y‖ = t * ‖h y - h x‖ := by
            rw [h1, ← smul_sub, norm_smul, Real.norm_of_nonneg ht0]
        _ ≤ t * (L * ‖y - x‖) := by
          gcongr
          rw [← dist_eq_norm, ← dist_eq_norm]
          exact hL.dist_le_mul y hy x hx
        _ = t * L * ‖x - y‖ := by rw [norm_sub_rev]; ring
    have h3 : ‖x - y‖ ≤ 0 := by
      have := norm_nonneg (x - y)
      nlinarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h3)
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hc : x + t • h x = (1 - t) • x + t • (x + h x) := by
        rw [smul_add, sub_smul, one_smul]; abel
      simp only
      rw [hc]
      exact convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 hx (hB x hx)
        (sub_nonneg.2 ht1) ht0 (by ring)
    · intro y hy
      set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
        (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator h with hg
      have hgL : LipschitzWith L g := A_perturb_ext_lip h L hL h0
      set G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => y - t • g x
        with hG
      have hGc : ContractingWith (Real.toNNReal t * L) G := by
        refine ⟨?_, ?_⟩
        · rw [← NNReal.coe_lt_coe]
          simpa [Real.coe_toNNReal t ht0] using htL
        · refine LipschitzWith.of_dist_le_mul fun a b => ?_
          have : dist (G a) (G b) = t * dist (g a) (g b) := by
            simp only [hG, dist_eq_norm]
            rw [sub_sub_sub_cancel_left, ← smul_sub, norm_smul, Real.norm_of_nonneg ht0,
              norm_sub_rev]
          rw [this, NNReal.coe_mul, Real.coe_toNNReal t ht0, mul_assoc]
          gcongr
          exact hgL.dist_le_mul a b
      set x := ContractingWith.fixedPoint G hGc with hx
      have hfix : G x = x := ContractingWith.fixedPoint_isFixedPt hGc
      by_cases hxB : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
      · refine ⟨x, hxB, ?_⟩
        have : y - t • h x = x := by simpa [hG, hg, Set.indicator_of_mem hxB] using hfix
        exact (sub_eq_iff_eq_add.mp this).symm
      · exfalso
        have : y = x := by simpa [hG, hg, Set.indicator_of_notMem hxB] using hfix
        exact hxB (this ▸ hy)

section C_poly_section
open Polynomial

/-- `t ↦ det (1 + t • T)` is a real polynomial of degree `≤ d`. -/
theorem C_poly_det_poly {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ p : ℝ[X], p.natDegree ≤ d ∧ ∀ t : ℝ, (1 + t • T).det = p.eval t := by
  classical
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let M := LinearMap.toMatrix b b (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin d) (Fin d) ℝ).map C), ?_, ?_⟩
  · simpa using natDegree_det_X_add_C_le M 1
  · intro t
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, ← Polynomial.coe_evalRingHom,
      RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [M, h] <;> ring

/-- Lagrange interpolation at `d + 1` distinct nodes recovers the value at `1`
of any polynomial of degree `≤ d`. -/
theorem C_poly_interp {d : ℕ} (v : Fin (d+1) → ℝ) (hv : Function.Injective v) (p : ℝ[X])
    (hp : p.natDegree ≤ d) :
    p.eval 1 = ∑ i, (Lagrange.basis Finset.univ v i).eval 1 * p.eval (v i) := by
  have hdeg : p.degree < ((Finset.univ : Finset (Fin (d+1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact (Polynomial.degree_le_of_natDegree_le hp).trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
  conv_lhs => rw [Lagrange.eq_interpolate hv.injOn hdeg]
  simp [Lagrange.interpolate_apply, eval_finsetSum, mul_comm]

end C_poly_section

/-- (C) If `t ↦ ∫_s det(1 + t A)` is constant on an interval `(0, t₀)`, it has the same value at `t = 1`. -/
theorem C_poly {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (s : Set (EuclideanSpace ℝ (Fin d))) (hs : MeasurableSet s) (hfin : volume s < ⊤)
    (hA : ∃ C, ∀ x ∈ s, ‖A x‖ ≤ C) (hmeas : AEStronglyMeasurable A (volume.restrict s))
    (c t₀ : ℝ) (ht₀ : 0 < t₀)
    (hconst : ∀ t ∈ Ioo 0 t₀, ∫ x in s, (1 + t • A x).det = c) :
    ∫ x in s, (1 + A x).det = c := by
  classical
  obtain ⟨C, hC⟩ := hA
  -- interpolation nodes in `(0, t₀)`
  set v : Fin (d+1) → ℝ := fun i => t₀ * ((i : ℕ) + 1 : ℝ) / ((d : ℝ) + 2) with hv_def
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hv_inj : Function.Injective v := by
    intro i j hij
    simp only [v] at hij
    have h1 : t₀ * (((i : ℕ) : ℝ) + 1) = t₀ * (((j : ℕ) : ℝ) + 1) := by
      have := congrArg (· * ((d : ℝ) + 2)) hij
      simpa [div_mul_cancel₀, hd2.ne'] using this
    have h2 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
      have := mul_left_cancel₀ ht₀.ne' h1
      linarith
    exact Fin.ext (by exact_mod_cast h2)
  have hv_mem : ∀ i, v i ∈ Ioo 0 t₀ := by
    intro i
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (d : ℝ) + 1 := by
      have : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.isLt
      have : ((i : ℕ) : ℝ) ≤ d := by exact_mod_cast this
      linarith
    refine ⟨by positivity, ?_⟩
    simp only [v]
    rw [div_lt_iff₀ hd2]
    nlinarith
  -- interpolation weights
  set ℓ : Fin (d+1) → ℝ := fun i => (Lagrange.basis Finset.univ v i).eval 1 with hℓ_def
  have key : ∀ T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      (1 + T).det = ∑ i, ℓ i * (1 + v i • T).det := by
    intro T
    obtain ⟨p, hp, hpt⟩ := C_poly_det_poly T
    have hint := C_poly_interp v hv_inj p hp
    rw [show (1 + T) = 1 + (1 : ℝ) • T by simp, hpt 1, hint]
    simp [ℓ, hpt]
  have hsum : ∑ i, ℓ i = 1 := by
    have h0 : ∀ a : ℝ, a • (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) = 0 :=
      fun a => by ext x; simp
    have h1 : (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).det = 1 := by
      simp [ContinuousLinearMap.det]
    have := key 0
    simp only [h0, add_zero, h1, mul_one] at this
    exact this.symm
  -- integrability of `x ↦ det (1 + t • A x)` on `s`
  have hint : ∀ t : ℝ, IntegrableOn (fun x => (1 + t • A x).det) s volume := by
    intro t
    have hcont : Continuous fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) =>
        (1 + t • T).det :=
      ContinuousLinearMap.continuous_det.comp (continuous_const.add (continuous_const_smul t))
    obtain ⟨K, hK⟩ := (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) C).exists_bound_of_continuousOn
      hcont.continuousOn
    refine IntegrableOn.of_bound hfin (hcont.comp_aestronglyMeasurable hmeas) K ?_
    refine ae_restrict_of_forall_mem hs (fun x hx => hK _ ?_)
    rw [mem_closedBall, dist_zero_right]
    exact hC x hx
  calc ∫ x in s, (1 + A x).det = ∫ x in s, ∑ i, ℓ i * (1 + v i • A x).det := by
        congr 1
        funext x
        exact key (A x)
    _ = ∑ i, ∫ x in s, ℓ i * (1 + v i • A x).det :=
        integral_finsetSum _ (fun i _ => (hint (v i)).const_mul (ℓ i))
    _ = ∑ i, ℓ i * c := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_const_mul, hconst _ (hv_mem i)]
    _ = c := by rw [← Finset.sum_mul, hsum, one_mul]

/-- (D) A map with values on the unit sphere near `x` has singular derivative at `x`. -/
theorem D_det_zero {d : ℕ} (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (U : Set (EuclideanSpace ℝ (Fin d))) (hU : U ∈ nhds x)
    (hr : DifferentiableAt ℝ r x) (hsph : ∀ y ∈ U, ‖r y‖ = 1) :
    (fderiv ℝ r x).det = 0 := by
  classical
  set Dr := fderiv ℝ r x with hDr
  -- derivative of `y ↦ ⟪r y, r y⟫` via the product rule
  have hφ : HasFDerivAt (fun y => inner ℝ (r y) (r y))
      ((fderivInnerCLM ℝ (r x, r x)).comp (Dr.prod Dr)) x :=
    hr.hasFDerivAt.inner ℝ hr.hasFDerivAt
  -- but `⟪r y, r y⟫ = 1` near `x`, so the derivative vanishes
  have hconst : (fun y => inner ℝ (r y) (r y)) =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [hU] with y hy
    rw [real_inner_self_eq_norm_sq, hsph y hy]
    norm_num
  have h0 : HasFDerivAt (fun y => inner ℝ (r y) (r y))
      (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hconst
  have heq := hφ.unique h0
  have horth : ∀ v, inner ℝ (r x) (Dr v) = 0 := by
    intro v
    have hv := congrArg (fun L => L v) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, zero_apply] at hv
    have hc := real_inner_comm (Dr v) (r x)
    linarith
  -- if `det Dr ≠ 0`, then `Dr` is surjective, so `r x ∈ range Dr`, forcing `⟪r x, r x⟫ = 0`
  by_contra hdet
  have hunit : IsUnit (Dr : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hsurj : Function.Surjective
      (Dr : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [← LinearMap.range_eq_top]
    exact (LinearMap.isUnit_iff_range_eq_top _).1 hunit
  obtain ⟨v, hv⟩ := hsurj (r x)
  have h1 := horth v
  have hv' : Dr v = r x := hv
  rw [hv', real_inner_self_eq_norm_sq, hsph x (mem_of_mem_nhds hU)] at h1
  norm_num at h1

/-- Helper: `1 + T` has positive determinant when `‖T‖ < 1`. -/
theorem L1_no_retraction_det_pos {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hT : ‖T‖ < 1) :
    0 < (1 + T).det := by
  set f : ℝ → ℝ := fun s => (1 + s • T).det with hf
  have hcont : Continuous f :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, f s ≠ 0 := by
    intro s hs
    have hn : ‖-(s • T)‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖T‖ ≤ 1 * ‖T‖ := by gcongr; exact hs.2
        _ = ‖T‖ := one_mul _
        _ < 1 := hT
    have hu : IsUnit (1 + s • T) := by
      have := (Units.oneSub (-(s • T)) hn).isUnit
      simpa [Units.val_oneSub, sub_neg_eq_add] using this
    have hu' : IsUnit ((1 + s • T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
      hu.map ContinuousLinearMap.toLinearMapRingHom
    exact (LinearMap.isUnit_det _ hu').ne_zero
  have h0 : f 0 = 1 := by simp [hf, ContinuousLinearMap.det]
  by_contra hneg
  rw [not_lt] at hneg
  have h1 : f 1 ≤ 0 := by simpa [hf] using hneg
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (f 1) (f 0) from ⟨h1, by rw [h0]; exact zero_le_one⟩)
  exact hne s hs hs0

/-- (L1) No `C¹` retraction of the closed unit ball onto the unit sphere. -/
theorem L1_no_retraction {d : ℕ} (hd : 0 < d)
    (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hBU : closedBall 0 1 ⊆ U)
    (hr : ContDiffOn ℝ 1 r U)
    (hmaps : MapsTo r (closedBall 0 1) (sphere 0 1))
    (hid : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, r x = x) : False := by
  classical
  have hdiff : ∀ x ∈ U, HasFDerivAt r (fderiv ℝ r x) x := fun x hx =>
    ((hr.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hcontD : ContinuousOn (fderiv ℝ r) U := hr.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).exists_bound_of_continuousOn
    (hcontD.mono hBU)
  set K : ℝ := max M 0 + 1 with hK
  have hK1 : 1 ≤ K := by
    have := le_max_right M 0
    linarith
  have hKpos : 0 < K := by linarith
  set A : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
    fun x => fderiv ℝ r x - 1 with hA
  have hAbound : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖A x‖ ≤ K := by
    intro x hx
    calc ‖A x‖ ≤ ‖fderiv ℝ r x‖ +
          ‖(1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ := norm_sub_le _ _
      _ ≤ max M 0 + 1 :=
          add_le_add ((hM x hx).trans (le_max_left _ _)) ContinuousLinearMap.norm_id_le
  set h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => r x - x with hh
  have hhderiv : ∀ x ∈ U, HasFDerivAt h (A x) x := fun x hx =>
    (hdiff x hx).sub (hasFDerivAt_id x)
  set L : NNReal := ⟨K, hKpos.le⟩ with hL
  have hLip : LipschitzOnWith L h (closedBall 0 1) := by
    apply (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := A)
    · intro x hx
      exact (hhderiv x (hBU hx)).hasFDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hAbound x hx
  have h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0 := by
    intro x hx
    simp [hh, hid x hx]
  have hB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, x + h x ∈ closedBall 0 1 := by
    intro x hx
    have : x + h x = r x := by simp [hh]
    rw [this]
    exact sphere_subset_closedBall (hmaps hx)
  set t₀ : ℝ := 1 / K with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  have ht₀le : t₀ ≤ 1 := by
    rw [ht₀, div_le_one hKpos]
    exact hK1
  have hconst : ∀ t ∈ Ioo 0 t₀, ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      (1 + t • A x).det = volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    intro t ht
    have htK : t * K < 1 := by
      have := ht.2
      rw [ht₀, lt_div_iff₀ hKpos] at this
      exact this
    have htL : t * (L : ℝ) < 1 := htK
    obtain ⟨hinj, himg⟩ := A_perturb h L hLip h0 hB ht.1.le (ht.2.le.trans ht₀le) htL
    have hFd : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
        HasFDerivWithinAt (fun x => x + t • h x) (1 + t • A x) (closedBall 0 1) x := by
      intro x hx
      exact ((hasFDerivAt_id x).add ((hhderiv x (hBU hx)).const_smul t)).hasFDerivWithinAt
    have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_closedBall
      hFd hinj (fun _ => (1 : ℝ))
    rw [himg, setIntegral_const, smul_eq_mul, mul_one] at hcov
    rw [hcov]
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    simp only [smul_eq_mul, mul_one]
    have hn : ‖t • A x‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      calc t * ‖A x‖ ≤ t * K := mul_le_mul_of_nonneg_left (hAbound x hx) ht.1.le
        _ < 1 := htK
    exact (abs_of_pos (L1_no_retraction_det_pos _ hn)).symm
  have hmeas : AEStronglyMeasurable A (volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
    (measurable_fderiv ℝ r).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hC := C_poly A (closedBall 0 1) measurableSet_closedBall measure_closedBall_lt_top
    ⟨K, hAbound⟩ hmeas _ t₀ ht₀pos hconst
  simp only [hA, add_sub_cancel] at hC
  have hzero : ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, (fderiv ℝ r x).det = 0 := by
    have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
      Module.finrank_pos_iff.1 (by rw [finrank_euclideanSpace_fin]; exact hd)
    have hsph : volume (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) = 0 :=
      Measure.addHaar_sphere volume 0 1
    have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        x ∉ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      measure_eq_zero_iff_ae_notMem.1 hsph
    have : ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, (fderiv ℝ r x).det =
        ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, (0 : ℝ) := by
      apply setIntegral_congr_ae measurableSet_closedBall
      filter_upwards [hae] with x hx hxB
      have hxb : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := lt_of_le_of_ne hxB hx
      refine D_det_zero r x (ball 0 1) (isOpen_ball.mem_nhds hxb)
        (hdiff x (hBU (ball_subset_closedBall hxb))).differentiableAt ?_
      intro y hy
      have := hmaps (ball_subset_closedBall hy)
      simpa using this
    rw [this, integral_zero]
  have hpos : 0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  rw [hzero] at hC
  linarith

/-- Expansion of `‖x + λ v‖²`. -/
theorem L2_brouwer_C1_norm_sq_eq {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    ‖x + lam • v‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam * inner ℝ x v + lam ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- (L2) Brouwer for globally `C¹` self-maps of the closed unit ball. -/
theorem L2_brouwer_C1 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContDiff ℝ 1 f) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨0, by simp, Subsingleton.elim _ _⟩
  by_contra hne
  push Not at hne
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      v = fun x => x - f x := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : EuclideanSpace ℝ (Fin d) → ℝ, a = fun x => inner ℝ x (v x) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : EuclideanSpace ℝ (Fin d) → ℝ, b = fun x => ‖v x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℝ (Fin d) → ℝ, c = fun x => 1 - ‖x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨disc, hdisc⟩ : ∃ disc : EuclideanSpace ℝ (Fin d) → ℝ,
      disc = fun x => a x ^ 2 + b x * c x := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : EuclideanSpace ℝ (Fin d) → ℝ,
      lam = fun x => (-(a x) + Real.sqrt (disc x)) / b x := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      r = fun x => x + lam x • v x := ⟨_, rfl⟩
  -- smoothness of the ingredients
  have hvC : ContDiff ℝ 1 v := by rw [hv]; exact contDiff_id.sub hf
  have haC : ContDiff ℝ 1 a := by rw [ha]; exact contDiff_id.inner ℝ hvC
  have hbC : ContDiff ℝ 1 b := by rw [hb]; exact hvC.norm_sq ℝ
  have hcC : ContDiff ℝ 1 c := by rw [hc]; exact contDiff_const.sub (contDiff_norm_sq ℝ)
  have hdiscC : ContDiff ℝ 1 disc := by rw [hdisc]; exact (haC.pow 2).add (hbC.mul hcC)
  -- the open set
  set U : Set (EuclideanSpace ℝ (Fin d)) := {x | 0 < disc x ∧ 0 < b x} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const hdiscC.continuous).inter
      (isOpen_lt continuous_const hbC.continuous)
  -- key identity: `2 a = ‖x‖² - ‖f x‖² + b`
  have hkey : ∀ x, 2 * a x = ‖x‖ ^ 2 - ‖f x‖ ^ 2 + b x := by
    intro x
    have hfx : f x = x - v x := by rw [hv]; simp
    have h2 := norm_sub_sq_real x (v x)
    rw [← hfx] at h2
    rw [ha, hb]
    simp only
    linarith
  have hb_pos : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, 0 < b x := by
    intro x hx
    have hvx : v x ≠ 0 := by
      rw [hv]; exact sub_ne_zero.mpr (hne x hx).symm
    rw [hb]
    simp only
    have := norm_pos_iff.mpr hvx
    positivity
  have hfx1 : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖f x‖ ≤ 1 :=
    fun x hx => mem_closedBall_zero_iff.mp (hmaps hx)
  have hc_nonneg : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, 0 ≤ c x := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    rw [hc]
    simp only
    nlinarith [norm_nonneg x]
  have hdisc_pos : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, 0 < disc x := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hbx := hb_pos x hx
    have hk := hkey x
    have hf1 := hfx1 x hx
    have hcx := hc_nonneg x hx
    rw [hdisc]
    simp only
    rcases hx1.lt_or_eq with hlt | heq
    · have hcpos : 0 < c x := by
        rw [hc]; simp only; nlinarith [norm_nonneg x]
      nlinarith [sq_nonneg (a x), mul_pos hbx hcpos]
    · have hax : 0 < a x := by
        rw [heq] at hk; nlinarith [norm_nonneg (f x)]
      nlinarith [mul_nonneg hbx.le hcx]
  have hBU : closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ U :=
    fun x hx => ⟨hdisc_pos x hx, hb_pos x hx⟩
  -- `r` is `C¹` on `U`
  have hrC : ContDiffOn ℝ 1 r U := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    have hsq : ContDiffAt ℝ 1 (fun y => Real.sqrt (disc y)) x :=
      hdiscC.contDiffAt.sqrt hx.1.ne'
    have hlamC : ContDiffAt ℝ 1 lam x := by
      rw [hlam]
      exact (haC.contDiffAt.neg.add hsq).fun_div hbC.contDiffAt hx.2.ne'
    rw [hr]
    exact contDiffAt_id.add (hlamC.smul hvC.contDiffAt)
  -- `r` maps the ball to the sphere
  have hr_norm : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖r x‖ = 1 := by
    intro x hx
    have hbx := hb_pos x hx
    have hdx := hdisc_pos x hx
    have hs : Real.sqrt (disc x) ^ 2 = a x ^ 2 + b x * c x := by
      rw [Real.sq_sqrt hdx.le, hdisc]
    have hl : lam x * b x = -(a x) + Real.sqrt (disc x) := by
      rw [hlam]; simp only; field_simp
    have hcx : c x = 1 - ‖x‖ ^ 2 := by rw [hc]
    have h1 : ‖r x‖ ^ 2 = 1 := by
      have e : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam x * a x + lam x ^ 2 * b x := by
        rw [hr, ha, hb]
        simp only
        exact L2_brouwer_C1_norm_sq_eq x (v x) (lam x)
      rw [e]
      apply mul_left_cancel₀ hbx.ne'
      linear_combination (lam x * b x + Real.sqrt (disc x) + a x) * hl + hs + b x * hcx
    have h0 := norm_nonneg (r x)
    nlinarith
  have hmapsr : MapsTo r (closedBall 0 1) (sphere 0 1) :=
    fun x hx => mem_sphere_zero_iff_norm.mpr (hr_norm x hx)
  -- `r` is the identity on the sphere
  have hid : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, r x = x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hxB : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      sphere_subset_closedBall hx
    have hbx := hb_pos x hxB
    have hk := hkey x
    have hf1 := hfx1 x hxB
    have hcx : c x = 0 := by rw [hc]; simp [hx1]
    have hax : 0 < a x := by
      rw [hx1] at hk; nlinarith [norm_nonneg (f x)]
    have hdx : disc x = a x ^ 2 := by rw [hdisc]; simp [hcx]
    have hlx : lam x = 0 := by
      rw [hlam]; simp only; rw [hdx, Real.sqrt_sq hax.le]; simp
    rw [hr]; simp [hlx]
  exact L1_no_retraction hd r U hUo hBU hrC hmapsr hid

theorem L3_brouwer_ball_scalar_approx {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContinuousOn φ (closedBall 0 1)) (η : ℝ) (hη : 0 < η) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |G x - φ x| < η := by
  set B : Set (EuclideanSpace ℝ (Fin d)) := closedBall 0 1 with hB
  have : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let A : Subalgebra ℝ C(B, ℝ) :=
    { carrier := {g | ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧ ∀ x : B, g x = G x}
      mul_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x * Gb x, hGa.mul hGb, fun x => by simp [ha, hb]⟩
      add_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x + Gb x, hGa.add hGb, fun x => by simp [ha, hb]⟩
      algebraMap_mem' := fun r => ⟨fun _ => r, contDiff_const, fun x => by simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have : ∃ i, (x : EuclideanSpace ℝ (Fin d)) i ≠ (y : EuclideanSpace ℝ (Fin d)) i := by
      by_contra h
      push Not at h
      apply hxy
      apply Subtype.ext
      ext i
      exact h i
    obtain ⟨i, hi⟩ := this
    refine ⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, ?_, hi⟩
    refine ⟨⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, by fun_prop⟩, ?_, rfl⟩
    exact ⟨fun z => z i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff,
      fun z => rfl⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hsep
    (fun x : B => φ x) hφ.domRestrict η hη
  obtain ⟨G, hG, hgG⟩ := g.2
  refine ⟨G, hG, fun x hx => ?_⟩
  have := hg ⟨x, hx⟩
  rw [Real.norm_eq_abs] at this
  simpa [hgG] using this

theorem L3_brouwer_ball_vec_approx {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x - f x‖ < δ := by
  set η : ℝ := δ / (d + 1) with hη_def
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hη : 0 < η := div_pos hδ hd1
  have hcoord : ∀ i : Fin d, ∃ Gi : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 Gi ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |Gi x - f x i| < η := by
    intro i
    refine L3_brouwer_ball_scalar_approx (fun x => f x i) ?_ η hη
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn hf
  choose Gi hGi hGiapprox using hcoord
  refine ⟨fun x => (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x), ?_, ?_⟩
  · exact (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff.comp (contDiff_pi.2 fun i => hGi i)
  · intro x hx
    set v := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x) - f x with hv
    have hvi : ∀ i, v i = Gi i x - f x i := by
      intro i
      simp [hv]
    have hsq : ‖v‖ ^ 2 ≤ d * η ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin d, η ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [hvi i]
            have := hGiapprox i x hx
            rw [← sq_abs]
            have h0 : 0 ≤ |Gi i x - f x i| := abs_nonneg _
            nlinarith
        _ = d * η ^ 2 := by simp
    have hlt : ‖v‖ ^ 2 < δ ^ 2 := by
      have hδη : δ = (d + 1) * η := by rw [hη_def]; field_simp
      rw [hδη]
      have : (d : ℝ) * η ^ 2 < ((d : ℝ) + 1) ^ 2 * η ^ 2 := by
        have hdd : (d : ℝ) < ((d : ℝ) + 1) ^ 2 := by nlinarith
        have := pow_pos hη 2
        nlinarith
      nlinarith
    have hn : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith

/-- (L3) Brouwer for continuous self-maps of the closed unit ball. -/
theorem L3_brouwer_ball {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by
  by_contra hno
  push Not at hno
  -- Step 1: minimal displacement
  have hcpt : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := isCompact_closedBall 0 1
  have hne : (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty :=
    ⟨0, mem_closedBall_self zero_le_one⟩
  have hcont : ContinuousOn (fun x => ‖f x - x‖) (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (hf.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
  set ε : ℝ := ‖f x₀ - x₀‖ with hε_def
  have hε : 0 < ε := norm_pos_iff.2 (sub_ne_zero.2 (hno x₀ hx₀))
  have hεle : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ε ≤ ‖f x - x‖ :=
    fun x hx => hmin hx
  -- Step 2: smooth approximation
  set η : ℝ := ε / 2 with hη_def
  have hη : 0 < η := half_pos hε
  obtain ⟨G, hG, hGapprox⟩ := L3_brouwer_ball_vec_approx f hf η hη
  -- Step 3: rescale
  set c : ℝ := 1 + η with hc_def
  have hc : 0 < c := by positivity
  set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => c⁻¹ • G x with hg_def
  have hgC1 : ContDiff ℝ 1 g := hG.const_smul c⁻¹
  have hGnorm : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x‖ ≤ c := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    calc ‖G x‖ = ‖(G x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ c := by rw [hc_def]; linarith
  have hgmaps : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    rw [mem_closedBall_zero_iff, hg_def]
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
    calc c⁻¹ * ‖G x‖ ≤ c⁻¹ * c := by
          exact mul_le_mul_of_nonneg_left (hGnorm x hx) (inv_pos.2 hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hgf : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖g x - f x‖ < ε := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    have hkey : c • (g x - f x) = (G x - f x) - η • f x := by
      rw [hg_def]
      simp only
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hc_def, add_smul, one_smul]
      abel
    have hnorm : c * ‖g x - f x‖ ≤ ‖G x - f x‖ + η * ‖f x‖ := by
      have := congrArg norm hkey
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at this
      rw [this]
      calc ‖(G x - f x) - η • f x‖ ≤ ‖G x - f x‖ + ‖η • f x‖ := norm_sub_le _ _
        _ = ‖G x - f x‖ + η * ‖f x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have hc1 : 1 ≤ c := by rw [hc_def]; linarith
    have hn0 : 0 ≤ ‖g x - f x‖ := norm_nonneg _
    have : η * ‖f x‖ ≤ η := by nlinarith
    nlinarith
  obtain ⟨x, hx, hfix⟩ := L2_brouwer_C1 g hgC1 hgmaps
  have h1 := hεle x hx
  have h2 := hgf x hx
  rw [hfix, norm_sub_rev] at h2
  linarith

/-- Nearest-point retraction onto a nonempty complete convex set in a real inner product space. -/
theorem L4_retraction {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    ∃ p : F → F, Continuous p ∧ (∀ x, p x ∈ K) ∧ (∀ x ∈ K, p x = x) := by
  choose p hpK hpeq using exists_norm_eq_iInf_of_complete_convex hne hc hconv
  have hin : ∀ x, ∀ w ∈ K, inner ℝ (x - p x) (w - p x) ≤ 0 := fun x =>
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hpK x)).1 (hpeq x)
  refine ⟨p, ?_, hpK, ?_⟩
  · have hlip : LipschitzWith 1 p := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [NNReal.coe_one, one_mul, dist_eq_norm]
      have h1 := hin x (p y) (hpK y)
      have h2 := hin y (p x) (hpK x)
      have key : ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by
        have e : inner ℝ (x - y) (p x - p y) - ‖p x - p y‖ ^ 2 =
            -inner ℝ (x - p x) (p y - p x) - inner ℝ (y - p y) (p x - p y) := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_sub_left, inner_sub_right, real_inner_comm]
          ring
        linarith
      have hcs := real_inner_le_norm (x - y) (p x - p y)
      rcases eq_or_lt_of_le (norm_nonneg (p x - p y)) with h | h
      · rw [← h]; exact norm_nonneg _
      · nlinarith
    exact hlip.continuous
  · intro x hx
    have h0 : ‖x - p x‖ ^ 2 ≤ 0 := by
      rw [← real_inner_self_eq_norm_sq]; exact hin x x hx
    have h1 : ‖x - p x‖ = 0 := by nlinarith [norm_nonneg (x - p x)]
    exact (norm_sub_eq_zero_iff.1 h1).symm

/-- Brouwer for compact convex nonempty subsets of `EuclideanSpace ℝ (Fin d)`. -/
theorem L4_brouwer_euclid {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hKconv : Convex ℝ K)
    (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f K)
    (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  obtain ⟨p, hpc, hpK, hpid⟩ := L4_retraction hKne hKcpt.isComplete hKconv
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKcpt.isBounded
  set R : ℝ := max R₀ 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun z => R⁻¹ • f (p (R • z))
  have hgc : ContinuousOn g (closedBall 0 1) := by
    have hc : ContinuousOn (fun z => f (p (R • z))) univ :=
      hf.comp (hpc.comp (continuous_const_smul R)).continuousOn (fun z _ => hpK _)
    exact (hc.mono (subset_univ _)).const_smul R⁻¹
  have hgm : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro z _
    have h1 := hKR (hfK (hpK (R • z)))
    rw [mem_closedBall_zero_iff] at h1 ⊢
    simp only [g, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRpos]
    rw [inv_mul_le_iff₀ hRpos]
    linarith
  obtain ⟨z, -, hz⟩ := L3_brouwer_ball g hgc hgm
  have hx : f (p (R • z)) = R • z := by
    have := congrArg (fun v => R • v) hz
    simpa [g, smul_smul, mul_inv_cancel₀ hRpos.ne'] using this
  have hxK : R • z ∈ K := hx ▸ hfK (hpK _)
  refine ⟨R • z, hxK, ?_⟩
  rw [hpid _ hxK] at hx
  exact hx

end QFBrouwerAux

open QFBrouwerAux in
/-- (L4) The target statement. -/
theorem qf_brouwer {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  classical
  let φ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hconv' : Convex ℝ (φ '' K) :=
    hKconv.linear_image (φ : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  have hcont : ContinuousOn (φ ∘ f ∘ φ.symm) (φ '' K) := by
    refine φ.continuous.comp_continuousOn (hf.comp φ.symm.continuous.continuousOn ?_)
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  have hmaps : MapsTo (φ ∘ f ∘ φ.symm) (φ '' K) (φ '' K) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨f y, hfK hy, by simp⟩
  obtain ⟨x, ⟨y, hyK, rfl⟩, hx⟩ :=
    L4_brouwer_euclid hconv' (hKcpt.image φ.continuous) (hKne.image φ) _ hcont hmaps
  refine ⟨y, hyK, ?_⟩
  apply φ.injective
  simpa using hx

end QFB


lemma mdc_hasSum_a (lam : ℝ) (z : ℂ) :
    HasSum (fun m => (poissonProb lam m : ℂ) * z ^ m) (Complex.exp (lam * (z - 1))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ((lam : ℂ) * z)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have h2 := h.mul_left (Complex.exp (-(lam : ℂ)))
  have he : Complex.exp (-(lam:ℂ)) * Complex.exp (lam * z) = Complex.exp (lam * (z - 1)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [he] at h2
  refine h2.congr_fun ?_
  intro m
  unfold poissonProb
  push_cast
  rw [mul_pow]
  field_simp

lemma mdc_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma mdc_identity (lam : ℝ) (hlam : 0 ≤ lam) (c : ℕ) (p : ℕ → ℝ) (hp : IsMDcStationary lam c p) (z : ℂ)
    (hz : ‖z‖ ≤ 1) :
    QueueingFundamentals.MG1.pgf p z * (1 - z ^ c * Complex.exp ((lam : ℂ) * (1 - z))) =
      (∑ n ∈ Finset.range (c + 1), (p n : ℂ) * z ^ n) - (cumProb p c : ℂ) * z ^ c := by
  obtain ⟨hnn, hsum, hbal⟩ := hp
  have hps : Summable p := hsum.summable
  have hpn : ∀ n, 0 ≤ poissonProb lam n ∨ True := fun _ => Or.inr trivial
  -- generating sequences
  set b : ℕ → ℝ := fun k => if k = 0 then cumProb p c else p (c + k) with hb
  set g : ℕ → ℂ := fun k => (b k : ℂ) * z ^ k with hg
  set ga : ℕ → ℂ := fun m => (poissonProb lam m : ℂ) * z ^ m with hga
  have hzpow : ∀ k : ℕ, ‖z ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have hpnorm : ∀ n, ‖(p n : ℂ) * z ^ n‖ ≤ p n := fun n => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn n)]
    exact mul_le_of_le_one_right (hnn n) (hzpow n)
  have hPsum : Summable (fun n => ‖(p n : ℂ) * z ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpnorm hps
  have hgsum : Summable (fun k => ‖g k‖) := by
    rw [← summable_nat_add_iff 1]
    have : Summable (fun k => p (k + (c + 1))) := (summable_nat_add_iff (c+1)).mpr hps
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) this
    simp only [hg, hb, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    rw [show k + (c+1) = c + (k+1) by ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn _)]
    exact mul_le_of_le_one_right (hnn _) (hzpow _)
  have haa : HasSum ga (Complex.exp (lam * (z - 1))) := mdc_hasSum_a lam z
  have hapos : ∀ m, 0 ≤ poissonProb lam m → True := fun _ _ => trivial
  have hgasum : Summable (fun m => ‖ga m‖) := by
    have h1 := (mdc_hasSum_a lam (1 : ℂ)).summable
    simp only [one_pow, mul_one] at h1
    have h2 : Summable (poissonProb lam) := Complex.summable_ofReal.mp h1
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) h2
    have ha0 : 0 ≤ poissonProb lam m := by unfold poissonProb; positivity
    simp only [hga]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
    exact mul_le_of_le_one_right ha0 (hzpow _)
  -- Cauchy product
  have hP : QueueingFundamentals.MG1.pgf p z = (∑' k, g k) * (∑' m, ga m) := by
    rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hgsum hgasum]
    unfold QueueingFundamentals.MG1.pgf
    congr 1; funext n
    have hterm : ∀ k ∈ Finset.range (n + 1), g k * ga (n - k) =
        ((b k * poissonProb lam (n - k) : ℝ) : ℂ) * z ^ n := by
      intro k hk
      simp only [Finset.mem_range] at hk
      simp only [hg, hga]
      rw [show z ^ n = z ^ k * z ^ (n - k) by rw [← pow_add]; congr 1; omega]
      push_cast; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    congr 1
    rw [hbal n, mdc_sum_Icc, Finset.sum_range_succ']
    push_cast
    simp only [hb, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true, Nat.sub_zero]
    push_cast
    ring_nf
  have hgs : Summable g := hgsum.of_norm
  have hB : (∑' k, g k) = (cumProb p c : ℂ) + ∑' k, g (k + 1) := by
    rw [hgs.tsum_eq_zero_add]
    simp [hg, hb]
  have hR : z ^ c * ∑' k, g (k + 1) =
      QueueingFundamentals.MG1.pgf p z - ∑ n ∈ Finset.range (c + 1), (p n : ℂ) * z ^ n := by
    unfold QueueingFundamentals.MG1.pgf
    have hs : Summable (fun n => (p n : ℂ) * z ^ n) := hPsum.of_norm
    rw [← hs.sum_add_tsum_nat_add (c + 1), add_sub_cancel_left, ← tsum_mul_left]
    congr 1; funext k
    simp only [hg, hb, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    rw [show k + (c + 1) = c + (k + 1) by ring, pow_add]; ring
  have hEA : Complex.exp ((lam : ℂ) * (1 - z)) * Complex.exp (lam * (z - 1)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
  rw [hP, haa.tsum_eq]
  rw [hP, haa.tsum_eq] at hR
  rw [hB] at hR ⊢
  linear_combination (-(z ^ c) * (↑(cumProb p c) + ∑' (k : ℕ), g (k + 1))) * hEA - hR




open Finset Filter Topology

lemma mdx_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma mdx_pp_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (m : ℕ) : 0 ≤ poissonProb lam m := by
  unfold poissonProb; positivity

lemma mdx_hasSum_real (lam x : ℝ) :
    HasSum (fun m => poissonProb lam m * x ^ m) (Real.exp (lam * (x - 1))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (lam * x)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-lam))
  have he : Real.exp (-lam) * Real.exp (lam * x) = Real.exp (lam * (x - 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at h2
  refine h2.congr_fun ?_
  intro m
  unfold poissonProb
  rw [mul_pow]
  field_simp

lemma mdx_hasSum_one (lam : ℝ) : HasSum (poissonProb lam) 1 := by
  have := mdx_hasSum_real lam 1
  simp only [one_pow, mul_one, sub_self, mul_zero, Real.exp_zero] at this
  exact this

lemma mdx_reindex (f : ℕ → ℝ) (m d : ℕ) :
    ∑ j ∈ range (m + d), (if m ≤ j then f (j - m) else 0) = ∑ l ∈ range d, f l := by
  induction d with
  | zero =>
    simp only [add_zero, range_zero, sum_empty]
    apply sum_eq_zero; intro j hj; simp at hj; simp [show ¬ m ≤ j by omega]
  | succ d ih =>
    rw [show m + (d+1) = (m + d) + 1 by ring, sum_range_succ, ih, sum_range_succ]
    simp

/-- truncated kernel -/
noncomputable def kerT (lam : ℝ) (c N i j : ℕ) : ℝ :=
  if j < N then (if i - c ≤ j then poissonProb lam (j - (i - c)) else 0)
  else if j = N then 1 - ∑ l ∈ range (N - (i - c)), poissonProb lam l else 0

lemma kerT_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (c N i j : ℕ) : 0 ≤ kerT lam c N i j := by
  unfold kerT
  split_ifs
  · exact mdx_pp_nonneg hlam _
  · exact le_refl _
  · have := (mdx_hasSum_one lam).summable
    have h2 := sum_le_hasSum (range (N - (i - c))) (fun l _ => mdx_pp_nonneg hlam l)
      (mdx_hasSum_one lam)
    linarith
  · exact le_refl _

lemma kerT_row {lam : ℝ} (c N i : ℕ) (hi : i ≤ N) :
    ∑ j ∈ range (N + 1), kerT lam c N i j = 1 := by
  rw [sum_range_succ]
  have h1 : ∀ j ∈ range N, kerT lam c N i j =
      if i - c ≤ j then poissonProb lam (j - (i - c)) else 0 := by
    intro j hj; simp at hj; unfold kerT; simp [hj]
  rw [sum_congr rfl h1]
  have hN : N = (i - c) + (N - (i - c)) := by omega
  conv_lhs => rw [hN]
  rw [mdx_reindex]
  unfold kerT
  simp only [lt_irrefl, if_false, if_true]
  rw [← hN]; ring

lemma kerT_lyap {lam : ℝ} (hlam : 0 ≤ lam) (c N i : ℕ) (hi : i ≤ N) (r : ℝ) (hr : 1 ≤ r) :
    ∑ j ∈ range (N + 1), kerT lam c N i j * r ^ j ≤
      r ^ (i - c) * Real.exp (lam * (r - 1)) := by
  set m := i - c with hm
  set d := N - m with hd
  have hN : N = m + d := by omega
  have ha := mdx_hasSum_one lam
  have hb := (mdx_hasSum_real lam r).mul_left (r ^ m)
  rw [sum_range_succ]
  have h1 : ∀ j ∈ range N, kerT lam c N i j * r ^ j =
      if m ≤ j then (r ^ m * (poissonProb lam (j - m) * r ^ (j - m))) else 0 := by
    intro j hj; simp at hj; unfold kerT; simp only [hj, if_true, ← hm]
    split_ifs with hmj
    · rw [show r ^ j = r ^ m * r ^ (j - m) by rw [← pow_add]; congr 1; omega]; ring
    · simp
  rw [sum_congr rfl h1]
  rw [show range N = range (m + d) by rw [← hN]]
  rw [mdx_reindex (fun l => r ^ m * (poissonProb lam l * r ^ l))]
  have htail : kerT lam c N i N = ∑' l, poissonProb lam (l + d) := by
    unfold kerT
    simp only [lt_irrefl, if_false, if_true, ← hm, ← hd]
    have := ha.summable.sum_add_tsum_nat_add d
    rw [ha.tsum_eq] at this
    linarith
  rw [htail]
  have hsb : Summable (fun l => r ^ m * (poissonProb lam l * r ^ l)) := hb.summable
  have hsplit := hsb.sum_add_tsum_nat_add d
  rw [hb.tsum_eq] at hsplit
  rw [← hsplit]
  gcongr
  rw [← tsum_mul_right]
  apply Summable.tsum_le_tsum _ ((summable_nat_add_iff d).mpr ha.summable |>.mul_right _)
    ((summable_nat_add_iff d).mpr hsb)
  intro l
  rw [hN, pow_add]
  have h0 := mdx_pp_nonneg hlam (l + d)
  have hpow : r ^ d ≤ r ^ (l + d) := pow_le_pow_right₀ hr (by omega)
  have hrm : 0 ≤ r ^ m := by positivity
  calc poissonProb lam (l + d) * (r ^ m * r ^ d)
      = r ^ m * (poissonProb lam (l + d) * r ^ d) := by ring
    _ ≤ r ^ m * (poissonProb lam (l + d) * r ^ (l + d)) := by gcongr

/-- finite truncated stationary vector via Brouwer -/
lemma mdx_trunc {lam : ℝ} (hlam : 0 ≤ lam) (c N : ℕ) :
    ∃ q : ℕ → ℝ, (∀ n, 0 ≤ q n) ∧ (∀ n, N < n → q n = 0) ∧ ∑ n ∈ range (N + 1), q n = 1 ∧
      ∀ j ≤ N, q j = ∑ i ∈ range (N + 1), q i * kerT lam c N i j := by
  classical
  let K : Set (Fin (N + 1) → ℝ) := {π | (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1}
  let f : (Fin (N + 1) → ℝ) → (Fin (N + 1) → ℝ) :=
    fun π j => ∑ i, π i * kerT lam c N i j
  have hconv : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hx.1 i; have := hy.1 i; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hx.2, hy.2]
      linarith
  have hclosed : IsClosed K := by
    have h1 : IsClosed {π : Fin (N+1) → ℝ | ∀ i, 0 ≤ π i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
    have h2 : IsClosed {π : Fin (N+1) → ℝ | ∑ i, π i = 1} :=
      isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
    exact h1.inter h2
  have hsub : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1) := by
    intro π hπ i _
    refine ⟨hπ.1 i, ?_⟩
    rw [← hπ.2]
    exact single_le_sum (fun j _ => hπ.1 j) (mem_univ i)
  have hcpt : IsCompact K :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hclosed hsub
  have hne : K.Nonempty := by
    refine ⟨fun i => if i = 0 then 1 else 0, fun i => by dsimp only; split_ifs <;> norm_num, ?_⟩
    simp
  have hcont : ContinuousOn f K := by
    apply Continuous.continuousOn
    apply continuous_pi; intro j
    exact continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)
  have hrow : ∀ i : Fin (N+1), ∑ j : Fin (N+1), kerT lam c N i j = 1 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun j => kerT lam c N i j)]
    exact kerT_row c N i (by omega)
  have hmaps : Set.MapsTo f K K := by
    intro π hπ
    refine ⟨fun j => sum_nonneg (fun i _ => mul_nonneg (hπ.1 i) (kerT_nonneg hlam _ _ _ _)), ?_⟩
    simp only [f]
    rw [sum_comm]
    simp_rw [← mul_sum, hrow, mul_one]
    exact hπ.2
  obtain ⟨π, hπK, hπf⟩ := qf_brouwer hconv hcpt hne f hcont hmaps
  refine ⟨fun n => if h : n < N + 1 then π ⟨n, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro n; dsimp only; split_ifs; exact hπK.1 _; exact le_refl _
  · intro n hn; simp [show ¬ n < N + 1 by omega]
  · rw [← hπK.2, ← Fin.sum_univ_eq_sum_range (fun n => if h : n < N + 1 then π ⟨n, h⟩ else 0)]
    refine sum_congr rfl (fun x _ => ?_)
    rw [dif_pos x.isLt]
  · intro j hj
    have := congrFun hπf ⟨j, by omega⟩
    simp only [f] at this
    show (if h : j < N + 1 then π ⟨j, h⟩ else 0) = ∑ i ∈ range (N + 1), (if h : i < N + 1 then π ⟨i, h⟩ else 0) * kerT lam c N i j
    rw [dif_pos (by omega), ← this]
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if h : i < N + 1 then π ⟨i, h⟩ else 0) * kerT lam c N i j)]
    refine sum_congr rfl (fun x _ => ?_)
    rw [dif_pos x.isLt]

lemma mdx_bal (lam : ℝ) (c N : ℕ) (q : ℕ → ℝ)
    (hq : ∀ j ≤ N, q j = ∑ i ∈ range (N + 1), q i * kerT lam c N i j) (n : ℕ) (hn : n + c < N) :
    q n = (∑ i ∈ range (c + 1), q i) * poissonProb lam n +
      ∑ k ∈ Icc 1 n, q (c + k) * poissonProb lam (n - k) := by
  rw [hq n (by omega), show N + 1 = (c + 1) + (n + (N - c - n)) by omega,
    sum_range_add _ (c + 1) (n + (N - c - n)), sum_range_add _ n (N - c - n), mdx_sum_Icc, sum_mul]
  have e1 : ∀ i ∈ range (c + 1), q i * kerT lam c N i n = q i * poissonProb lam n := by
    intro i hi; simp at hi; unfold kerT
    simp [show n < N by omega, show i - c = 0 by omega]
  have e2 : ∀ k ∈ range n, q (c + 1 + k) * kerT lam c N (c + 1 + k) n =
      q (c + (k + 1)) * poissonProb lam (n - (k + 1)) := by
    intro k hk; simp at hk; unfold kerT
    rw [if_pos (by omega), if_pos (by omega), show c + 1 + k - c = k + 1 by omega,
      show c + 1 + k = c + (k + 1) by ring]
  have e3 : ∀ k ∈ range (N - c - n), q (c + 1 + (n + k)) * kerT lam c N (c + 1 + (n + k)) n = 0 := by
    intro k hk; unfold kerT
    rw [if_pos (by omega), if_neg (by omega), mul_zero]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3, sum_const_zero, add_zero]

lemma mdx_moment {lam : ℝ} (hlam : 0 ≤ lam) (c N : ℕ) (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n)
    (hq1 : ∑ n ∈ range (N + 1), q n = 1)
    (hq : ∀ j ≤ N, q j = ∑ i ∈ range (N + 1), q i * kerT lam c N i j)
    (r : ℝ) (hr : 1 ≤ r) (hθ : Real.exp (lam * (r - 1)) < r ^ c) :
    ∑ n ∈ range (N + 1), q n * r ^ n ≤
      Real.exp (lam * (r - 1)) / (1 - Real.exp (lam * (r - 1)) / r ^ c) := by
  set G := Real.exp (lam * (r - 1)) with hG
  have hrc : 0 < r ^ c := by positivity
  set θ := G / r ^ c with hθdef
  have hθ1 : θ < 1 := by rw [hθdef, div_lt_one hrc]; exact hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hG0 : 0 < G := Real.exp_pos _
  set S := ∑ n ∈ range (N + 1), q n * r ^ n with hS
  have key : S ≤ θ * S + G := by
    have h1 : S = ∑ i ∈ range (N + 1), q i * ∑ j ∈ range (N + 1), kerT lam c N i j * r ^ j := by
      rw [hS]
      have : ∀ j ∈ range (N + 1), q j * r ^ j =
          ∑ i ∈ range (N + 1), q i * kerT lam c N i j * r ^ j := by
        intro j hj; simp at hj; rw [hq j (by omega), sum_mul]
      rw [sum_congr rfl this, sum_comm]
      apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j _; ring
    have h2 : ∀ i ∈ range (N + 1), q i * ∑ j ∈ range (N + 1), kerT lam c N i j * r ^ j ≤
        θ * (q i * r ^ i) + G * q i := by
      intro i hi; simp at hi
      have hl := kerT_lyap hlam c N i (by omega) r hr
      have hb : r ^ (i - c) * G ≤ θ * r ^ i + G := by
        by_cases hic : c ≤ i
        · have : r ^ (i - c) * G = θ * r ^ i := by
            rw [hθdef, pow_sub₀ _ (by linarith) hic]; field_simp
          rw [this]; linarith
        · rw [show i - c = 0 by omega, pow_zero, one_mul]
          have : 0 ≤ θ * r ^ i := by positivity
          linarith
      calc q i * ∑ j ∈ range (N + 1), kerT lam c N i j * r ^ j
          ≤ q i * (r ^ (i - c) * G) := mul_le_mul_of_nonneg_left hl (hq0 i)
        _ ≤ q i * (θ * r ^ i + G) := mul_le_mul_of_nonneg_left hb (hq0 i)
        _ = θ * (q i * r ^ i) + G * q i := by ring
    calc S = _ := h1
      _ ≤ ∑ i ∈ range (N + 1), (θ * (q i * r ^ i) + G * q i) := sum_le_sum h2
      _ = θ * S + G := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hq1, mul_one]
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma mdx_tail (N : ℕ) (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n)
    (hq1 : ∑ n ∈ range (N + 1), q n = 1) (r C : ℝ) (hr : 1 ≤ r)
    (hC : ∑ n ∈ range (N + 1), q n * r ^ n ≤ C) (M : ℕ) :
    1 - C * (r⁻¹) ^ M ≤ ∑ n ∈ range M, q n := by
  rw [← sum_filter_add_sum_filter_not (range (N + 1)) (fun n => n < M)] at hq1
  have hA : ∑ n ∈ (range (N + 1)).filter (fun n => n < M), q n ≤ ∑ n ∈ range M, q n := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn; simp at hn ⊢; exact hn.2
    · intro n _ _; exact hq0 n
  have hB : (∑ n ∈ (range (N + 1)).filter (fun n => ¬ n < M), q n) * r ^ M ≤ C := by
    rw [sum_mul]
    calc _ ≤ ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n < M), q n * r ^ n := by
          apply sum_le_sum; intro n hn; simp at hn
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (by omega)) (hq0 n)
      _ ≤ ∑ n ∈ range (N + 1), q n * r ^ n := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro n _ _; exact mul_nonneg (hq0 n) (by positivity)
      _ ≤ C := hC
  have hrM : 0 < r ^ M := by positivity
  have : ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n < M), q n ≤ C * (r⁻¹) ^ M := by
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hrM]; exact hB
  linarith

lemma mdx_choose_r {lam : ℝ} (hlam : 0 < lam) (c : ℕ) (hc : lam < c) :
    ∃ r : ℝ, 1 < r ∧ Real.exp (lam * (r - 1)) < r ^ c := by
  set δ := (c - lam) / ((c:ℝ) ^ 2 + 1) with hδ
  have hc0 : (0:ℝ) < c := by linarith
  have hden : (0:ℝ) < (c:ℝ) ^ 2 + 1 := by positivity
  have hδpos : 0 < δ := div_pos (by linarith) hden
  refine ⟨1 + δ, by linarith, ?_⟩
  have hx : |lam * δ| ≤ 1 := by
    rw [abs_of_pos (by positivity), hδ, mul_div_assoc', div_le_one hden]
    nlinarith [mul_le_mul_of_nonneg_right hc.le (sub_nonneg.2 hc.le), hlam, hc]
  have h1 := Real.abs_exp_sub_one_sub_id_le hx
  have h2 : Real.exp (lam * δ) ≤ 1 + lam * δ + (lam * δ) ^ 2 := by
    have := (abs_le.mp h1).2; linarith
  have h3 := one_add_mul_le_pow (show (-2:ℝ) ≤ δ by linarith) c
  have h4 : lam ^ 2 * δ < c - lam := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ hden]
    have hl2 : lam ^ 2 < (c:ℝ) ^ 2 + 1 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right hl2 (sub_pos.2 hc)]
  rw [show lam * (1 + δ - 1) = lam * δ by ring]
  have : lam * δ + (lam * δ) ^ 2 < c * δ := by nlinarith [mul_lt_mul_of_pos_right h4 hδpos]
  linarith

theorem mdc_exists_core (lam : ℝ) (hlam : 0 < lam) (c : ℕ) (hstab : lam < c) :
    ∃ p : ℕ → ℝ, IsMDcStationary lam c p := by
  obtain ⟨r, hr1, hθ⟩ := mdx_choose_r hlam c hstab
  set C := Real.exp (lam * (r - 1)) / (1 - Real.exp (lam * (r - 1)) / r ^ c) with hCdef
  have hex := fun N => mdx_trunc hlam.le c N
  choose Q hQ0 hQz hQ1 hQ using hex
  have hQS : ∀ N, Q N ∈ Set.pi Set.univ (fun _ : ℕ => Set.Icc (0:ℝ) 1) := by
    intro N n _
    refine ⟨hQ0 N n, ?_⟩
    by_cases hn : n ≤ N
    · rw [← hQ1 N]; exact single_le_sum (fun j _ => hQ0 N j) (by simp; omega)
    · rw [hQz N n (by omega)]; norm_num
  obtain ⟨p, hpS, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi (fun _ : ℕ => isCompact_Icc (a := (0:ℝ)) (b := 1))).tendsto_subseq hQS
  have hpt : ∀ n, Tendsto (fun k => Q (φ k) n) atTop (𝓝 (p n)) := fun n =>
    ((continuous_apply n).tendsto p).comp hlim
  have hp0 : ∀ n, 0 ≤ p n := fun n => (hpS n (Set.mem_univ n)).1
  have hpsum : ∀ M, Tendsto (fun k => ∑ n ∈ range M, Q (φ k) n) atTop (𝓝 (∑ n ∈ range M, p n)) :=
    fun M => tendsto_finsetSum _ (fun n _ => hpt n)
  have hmom : ∀ N, ∑ n ∈ range (N + 1), Q N n * r ^ n ≤ C := fun N =>
    mdx_moment hlam.le c N (Q N) (hQ0 N) (hQ1 N) (hQ N) r hr1.le hθ
  have hlow : ∀ M, 1 - C * (r⁻¹) ^ M ≤ ∑ n ∈ range M, p n := by
    intro M
    exact ge_of_tendsto' (hpsum M) (fun k => mdx_tail (φ k) (Q (φ k)) (hQ0 _) (hQ1 _) r C hr1.le
      (hmom _) M)
  have hup : ∀ M, ∑ n ∈ range M, p n ≤ 1 := by
    intro M
    refine le_of_tendsto' (hpsum M) (fun k => ?_)
    have hNk := hQ1 (φ k)
    by_cases hM : M ≤ φ k + 1
    · rw [← hNk]
      exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hM) (fun n _ _ => hQ0 _ n)
    · rw [show M = (φ k + 1) + (M - (φ k + 1)) by omega, sum_range_add, hNk]
      have : ∑ x ∈ range (M - (φ k + 1)), Q (φ k) (φ k + 1 + x) = 0 :=
        sum_eq_zero (fun x _ => hQz _ _ (by omega))
      rw [this]; norm_num
  have hHas : HasSum p 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hp0]
    have hr' : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
    have hlim0 : Tendsto (fun M : ℕ => 1 - C * (r⁻¹) ^ M) atTop (𝓝 (1 - C * 0)) :=
      tendsto_const_nhds.sub ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr').const_mul C)
    rw [mul_zero, sub_zero] at hlim0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim0 tendsto_const_nhds hlow hup
  refine ⟨p, hp0, hHas, ?_⟩
  intro n
  have hev : ∀ᶠ k in atTop, Q (φ k) n = (∑ i ∈ range (c + 1), Q (φ k) i) * poissonProb lam n +
      ∑ j ∈ Icc 1 n, Q (φ k) (c + j) * poissonProb lam (n - j) := by
    filter_upwards [eventually_ge_atTop (n + c + 1)] with k hk
    exact mdx_bal lam c (φ k) (Q (φ k)) (hQ (φ k)) n (by have : k ≤ φ k := hφ.id_le k; omega)
  have hR : Tendsto (fun k => (∑ i ∈ range (c + 1), Q (φ k) i) * poissonProb lam n +
      ∑ j ∈ Icc 1 n, Q (φ k) (c + j) * poissonProb lam (n - j)) atTop
      (𝓝 ((∑ i ∈ range (c + 1), p i) * poissonProb lam n +
      ∑ j ∈ Icc 1 n, p (c + j) * poissonProb lam (n - j))) :=
    ((hpsum (c+1)).mul_const _).add (tendsto_finsetSum _ (fun j _ => (hpt (c + j)).mul_const _))
  have := tendsto_nhds_unique (hR.congr' (hev.mono fun k hk => hk.symm)) (hpt n)
  unfold cumProb
  exact this.symm


theorem mdc_pgf_core (lam : ℝ) (hlam : 0 < lam) (c : ℕ) (hc : 1 ≤ c) :
    ((lam < c) → ∃ p : ℕ → ℝ, IsMDcStationary lam c p) ∧
    ∀ p : ℕ → ℝ, IsMDcStationary lam c p → ∀ z : ℂ, ‖z‖ ≤ 1 →
      QueueingFundamentals.MG1.pgf p z * (1 - z ^ c * Complex.exp ((lam : ℂ) * (1 - z))) =
          (∑ n ∈ Finset.range (c + 1), (p n : ℂ) * z ^ n) - (cumProb p c : ℂ) * z ^ c ∧
      QueueingFundamentals.MG1.pgf p z * (1 - z ^ c * Complex.exp ((lam : ℂ) * (1 - z))) =
          ∑ n ∈ Finset.range c, (p n : ℂ) * (z ^ n - z ^ c) := by
  refine ⟨fun h => mdc_exists_core lam hlam c h, fun p hp z hz => ?_⟩
  have h1 := mdc_identity lam hlam.le c p hp z hz
  refine ⟨h1, h1.trans ?_⟩
  unfold cumProb
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_range_succ, sub_self, add_zero]
  refine Finset.sum_congr rfl (fun n _ => by ring)

end QueueingFundamentals.GG1

open QueueingFundamentals.GG1


theorem solution (lam : ℝ) (hlam : 0 < lam) (c : ℕ) (hc : 1 ≤ c) :
    ((lam < c) → ∃ p : ℕ → ℝ, IsMDcStationary lam c p) ∧
    ∀ p : ℕ → ℝ, IsMDcStationary lam c p → ∀ z : ℂ, ‖z‖ ≤ 1 →
      QueueingFundamentals.MG1.pgf p z * (1 - z ^ c * Complex.exp ((lam : ℂ) * (1 - z))) =
          (∑ n ∈ Finset.range (c + 1), (p n : ℂ) * z ^ n) - (cumProb p c : ℂ) * z ^ c ∧
      QueueingFundamentals.MG1.pgf p z * (1 - z ^ c * Complex.exp ((lam : ℂ) * (1 - z))) =
          ∑ n ∈ Finset.range c, (p n : ℂ) * (z ^ n - z ^ c) := by
  exact mdc_pgf_core lam hlam c hc
