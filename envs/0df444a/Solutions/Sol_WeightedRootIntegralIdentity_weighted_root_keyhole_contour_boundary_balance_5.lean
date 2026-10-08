-- Prove2me | solution 5 for WeightedRootIntegralIdentity.weighted_root_keyhole_contour_boundary_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-20T11:30:25.299991+00:00
-- url     : https://prove2.me/submissions/1839bf83-41ee-4bcb-b010-9b0e318642ea

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_cpow_zero_boundary
import Theorems.Thm_WeightedRootIntegralIdentity_cpow_finset_boundary_product
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_reciprocal_deriv_at_zero

open scoped BigOperators Interval
open Set Filter

namespace WeightedRootIntegralIdentity

noncomputable section

/-- Principal-power product occurring in the weighted root identity. -/
def weightedRootF (n : ℕ) (a w : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)

/-- Reciprocal-variable product used to read off the coefficient at infinity. -/
def weightedRootP (n : ℕ) (a w : ℕ → ℝ) (u : ℂ) : ℂ :=
  ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)

/-- Renormalised boundary function.  The `dslope` removes the apparent pole at zero. -/
def weightedRootH (n : ℕ) (a w : ℕ → ℝ) (z : ℂ) : ℂ :=
  dslope (weightedRootF n a w) 0 z - 1

/-- Existing zero-boundary theorem in the notation used by the contour layer. -/
theorem weightedRootF_zero
    (n : ℕ) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    weightedRootF n a w 0 =
      -((∏ i ∈ Finset.range n, Real.rpow (a i) (w i) : ℝ) : ℂ) := by
  simpa [weightedRootF] using
    weighted_root_cpow_zero_boundary n a w hpos hwsum

/-- Existing reciprocal derivative theorem in the notation used by the contour layer. -/
theorem weightedRootP_hasDerivAt_zero
    (n : ℕ) (a w : ℕ → ℝ) :
    HasDerivAt (weightedRootP n a w)
      (-((∑ i ∈ Finset.range n, w i * a i : ℝ) : ℂ)) 0 := by
  have h := weighted_root_reciprocal_deriv_at_zero n a w
  have hfun : weightedRootP n a w =
      (fun z : ℂ => ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * z) ^ (w i : ℂ)) := by
    funext z
    simp [weightedRootP]
  rw [hfun]
  simpa using h

/-- The reciprocal-variable product is normalised to one at the origin. -/
theorem weightedRootP_zero (n : ℕ) (a w : ℕ → ℝ) :
    weightedRootP n a w 0 = 1 := by
  simp [weightedRootP]

/-- A finite product of real-cast complex numbers has zero imaginary part. -/
private theorem ofReal_prod_im (n : ℕ) (f : ℕ → ℝ) :
    (∏ i ∈ Finset.range n, ((f i : ℝ) : ℂ)).im = 0 := by
  have hcast : (∏ i ∈ Finset.range n, ((f i : ℝ) : ℂ)) =
      ((∏ i ∈ Finset.range n, f i : ℝ) : ℂ) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, Complex.ofReal_mul]
  rw [hcast]
  exact Complex.ofReal_im _

/-- `x + S * I` is nonzero when `S ≠ 0`. -/
private theorem ofReal_add_mul_I_ne_zero {x S : ℝ} (hS : S ≠ 0) :
    (x : ℂ) + (S : ℂ) * Complex.I ≠ 0 := by
  intro hx
  have him : ((x : ℂ) + (S : ℂ) * Complex.I).im = S := by simp
  rw [hx] at him
  simp at him
  exact hS him.symm

/-- `r + y * I` is nonzero when `r ≠ 0`. -/
private theorem ofReal_const_add_mul_I_ne_zero {r y : ℝ} (hr : r ≠ 0) :
    (r : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
  intro hx
  have hre : ((r : ℂ) + (y : ℂ) * Complex.I).re = r := by simp
  rw [hx] at hre
  simp at hre
  exact hr hre.symm

/-- `-r + y * I` is nonzero when `r ≠ 0`. -/
private theorem neg_ofReal_add_mul_I_ne_zero {r y : ℝ} (hr : r ≠ 0) :
    -(r : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
  intro hx
  have hre : (-(r : ℂ) + (y : ℂ) * Complex.I).re = -r := by simp
  rw [hx] at hre
  simp at hre
  exact hr (by simpa using hre)

/-- Exact removal of the `dslope`: multiplying `H` by `z` leaves the first-order remainder
    `F z - F 0 - z`.  This identity is valid even at `z = 0`. -/
theorem weightedRoot_mul_H
    (n : ℕ) (a w : ℕ → ℝ) (z : ℂ) :
    z * weightedRootH n a w z =
      weightedRootF n a w z - weightedRootF n a w 0 - z := by
  have hmul := sub_smul_dslope (weightedRootF n a w) 0 z
  rw [weightedRootH]
  rw [sub_zero, smul_eq_mul] at hmul
  calc
    z * (dslope (weightedRootF n a w) 0 z - 1) =
        z * dslope (weightedRootF n a w) 0 z - z := by ring
    _ = weightedRootF n a w z - weightedRootF n a w 0 - z := by rw [hmul]

/-- The adjacent inequalities imply monotonicity between any two indices in the active
    range.  Carrying the upper-range condition through `Nat.le_induction` avoids extending
    `a` beyond the indices controlled by `hmono`. -/
theorem weighted_root_index_mono
    (n : ℕ) (a : ℕ → ℝ)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≤ j) :
    a i ≤ a j := by
  refine Nat.le_induction (m := i)
    (P := fun k _ => k < n → a i ≤ a k) ?_ ?_ j hij hj
  · intro _
    exact le_rfl
  · intro k hik ih hk1
    have hk : k < n := by omega
    have hksub : k < n - 1 := by omega
    exact le_trans (ih hk) (hmono k hksub)

/-- The ordered endpoints really are ordered.  Kept separate because this fact is used by
    both interval-congruence and contour-support arguments. -/
theorem weighted_root_endpoint_le
    (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1)) :
    a 0 ≤ a (n - 1) := by
  exact weighted_root_index_mono n a hmono (by omega) (by omega) (by omega)

/-- Local analytic model at zero.  Moving the minus sign outside the full product puts
    every individual principal power on the positive real side at the base point. -/
def weightedRootQ (n : ℕ) (a w : ℕ → ℝ) (z : ℂ) : ℂ :=
  -∏ i ∈ Finset.range n, ((a i : ℂ) - z) ^ (w i : ℂ)

/-- Negating a point in the right half-plane and on or below the real axis adds `π`
    to the principal argument.  For a real exponent this extracts the corresponding phase
    from the principal complex power. -/
private theorem cpow_neg_of_re_pos_of_im_nonpos
    (z : ℂ) (w : ℝ) (hre : 0 < z.re) (him : z.im ≤ 0) :
    (-z) ^ (w : ℂ) =
      z ^ (w : ℂ) * Complex.exp ((((Real.pi * w : ℝ) : ℂ) * Complex.I)) := by
  have hz : z ≠ 0 := by
    intro hzero
    simp [hzero] at hre
  have harg : (-z).arg = z.arg + Real.pi := by
    rcases lt_or_eq_of_le him with himneg | himzero
    · exact Complex.arg_neg_eq_arg_add_pi_of_im_neg himneg
    · exact Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inr ⟨himzero, hre⟩)
  have hlog : Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, harg]
  rw [Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr hz),
      Complex.cpow_def_of_ne_zero hz, hlog]
  rw [show (Complex.log z + (Real.pi : ℂ) * Complex.I) * (w : ℂ) =
      Complex.log z * (w : ℂ) + (((Real.pi * w : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
  exact Complex.exp_add _ _

/-- Negating a point in the right half-plane and strictly above the real axis subtracts `π`
    from the principal argument. -/
private theorem cpow_neg_of_re_pos_of_im_pos
    (z : ℂ) (w : ℝ) (hre : 0 < z.re) (him : 0 < z.im) :
    (-z) ^ (w : ℂ) =
      z ^ (w : ℂ) * Complex.exp (-(((Real.pi * w : ℝ) : ℂ) * Complex.I)) := by
  have hz : z ≠ 0 := by
    intro hzero
    simp [hzero] at hre
  have harg : (-z).arg = z.arg - Real.pi :=
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos him
  have hlog : Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, harg]
  rw [Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr hz),
      Complex.cpow_def_of_ne_zero hz, hlog]
  rw [show (Complex.log z - (Real.pi : ℂ) * Complex.I) * (w : ℂ) =
      Complex.log z * (w : ℂ) - (((Real.pi * w : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
  rw [Complex.exp_sub]
  simp [Complex.exp_neg, div_eq_mul_inv]

/-- Near zero the total principal-power branch phase is exactly `-1` on both banks because
    the weights sum to one.  This is the sole branch-cancellation obligation needed for
    differentiability of the complete product at zero. -/
theorem weighted_root_eventually_eq_zero_model
    (n : ℕ) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    weightedRootF n a w =ᶠ[nhds 0] weightedRootQ n a w := by
  have hnear :
      ∀ᶠ z : ℂ in nhds 0, ∀ i ∈ Finset.range n, 0 < ((a i : ℂ) - z).re := by
    rw [Finset.eventually_all]
    intro i hi
    have hc : ContinuousAt (fun z : ℂ => ((a i : ℂ) - z).re) 0 :=
      Complex.continuous_re.continuousAt.comp (continuousAt_const.sub continuousAt_id : ContinuousAt (fun z : ℂ => (a i : ℂ) - z) 0)
    have hval : 0 < (((a i : ℂ) - (0 : ℂ)).re) := by
      simpa using hpos i (Finset.mem_range.mp hi)
    exact continuousAt_const.eventually_lt hc hval
  have hwsumC : (∑ i ∈ Finset.range n, (w i : ℂ)) = 1 := by
    exact_mod_cast hwsum
  filter_upwards [hnear] with z hz
  unfold weightedRootF weightedRootQ
  by_cases him : 0 ≤ z.im
  · have hphase :
        (∑ i ∈ Finset.range n,
            (((Real.pi * w i : ℝ) : ℂ) * Complex.I)) =
          (Real.pi : ℂ) * Complex.I := by
      push_cast
      rw [← Finset.sum_mul, ← Finset.mul_sum, hwsumC]
      ring
    calc
      (∏ i ∈ Finset.range n,
          (z - (a i : ℂ)) ^ (w i : ℂ)) =
          ∏ i ∈ Finset.range n,
            (-((a i : ℂ) - z)) ^ (w i : ℂ) := by
        apply Finset.prod_congr rfl
        intro i hi
        congr 1
        ring
      _ = ∏ i ∈ Finset.range n,
          (((a i : ℂ) - z) ^ (w i : ℂ) *
            Complex.exp ((((Real.pi * w i : ℝ) : ℂ) * Complex.I))) := by
        apply Finset.prod_congr rfl
        intro i hi
        apply cpow_neg_of_re_pos_of_im_nonpos
        · exact hz i hi
        · simp only [Complex.sub_im, Complex.ofReal_im]
          linarith
      _ = (∏ i ∈ Finset.range n, ((a i : ℂ) - z) ^ (w i : ℂ)) *
          (∏ i ∈ Finset.range n,
            Complex.exp ((((Real.pi * w i : ℝ) : ℂ) * Complex.I))) := by
        rw [Finset.prod_mul_distrib]
      _ = (∏ i ∈ Finset.range n, ((a i : ℂ) - z) ^ (w i : ℂ)) *
          Complex.exp
            (∑ i ∈ Finset.range n,
              (((Real.pi * w i : ℝ) : ℂ) * Complex.I)) := by
        rw [← Complex.exp_sum]
      _ = -(∏ i ∈ Finset.range n, ((a i : ℂ) - z) ^ (w i : ℂ)) := by
        rw [hphase, Complex.exp_pi_mul_I]
        ring
  · have himneg : z.im < 0 := lt_of_not_ge him
    have hphase :
        (∑ i ∈ Finset.range n,
            -(((Real.pi * w i : ℝ) : ℂ) * Complex.I)) =
          -((Real.pi : ℂ) * Complex.I) := by
      push_cast
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hwsumC]
      ring
    calc
      (∏ i ∈ Finset.range n,
          (z - (a i : ℂ)) ^ (w i : ℂ)) =
          ∏ i ∈ Finset.range n,
            (-((a i : ℂ) - z)) ^ (w i : ℂ) := by
        apply Finset.prod_congr rfl
        intro i hi
        congr 1
        ring
      _ = ∏ i ∈ Finset.range n,
          (((a i : ℂ) - z) ^ (w i : ℂ) *
            Complex.exp (-(((Real.pi * w i : ℝ) : ℂ) * Complex.I))) := by
        apply Finset.prod_congr rfl
        intro i hi
        apply cpow_neg_of_re_pos_of_im_pos
        · exact hz i hi
        · simp only [Complex.sub_im, Complex.ofReal_im]
          linarith
      _ = (∏ i ∈ Finset.range n, ((a i : ℂ) - z) ^ (w i : ℂ)) *
          (∏ i ∈ Finset.range n,
            Complex.exp (-(((Real.pi * w i : ℝ) : ℂ) * Complex.I))) := by
        rw [Finset.prod_mul_distrib]
      _ = (∏ i ∈ Finset.range n, ((a i : ℂ) - z) ^ (w i : ℂ)) *
          Complex.exp
            (∑ i ∈ Finset.range n,
              -(((Real.pi * w i : ℝ) : ℂ) * Complex.I)) := by
        rw [← Complex.exp_sum]
      _ = -(∏ i ∈ Finset.range n, ((a i : ℂ) - z) ^ (w i : ℂ)) := by
        rw [hphase, Complex.exp_neg, Complex.exp_pi_mul_I]
        simp

/-- The positive-side local model is holomorphic at zero factor by factor. -/
theorem weightedRootQ_differentiableAt_zero
    (n : ℕ) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i) :
    DifferentiableAt ℂ (weightedRootQ n a w) 0 := by
  unfold weightedRootQ
  apply DifferentiableAt.neg
  apply DifferentiableAt.fun_finsetProd
  intro i hi
  apply DifferentiableAt.cpow_const
  · exact DifferentiableAt.sub (differentiableAt_const (a i : ℂ)) differentiableAt_id
  · rw [Complex.mem_slitPlane_iff]
    left
    simpa using hpos i (Finset.mem_range.mp hi)

/-- Cancellation of the total branch phase makes the whole product differentiable at zero,
    even though the individual principal powers are based on negative real numbers there. -/
theorem weighted_root_differentiableAt_zero
    (n : ℕ) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    DifferentiableAt ℂ (weightedRootF n a w) 0 := by
  have heq :
      weightedRootF n a w =ᶠ[nhds (0 : ℂ)] weightedRootQ n a w :=
    weighted_root_eventually_eq_zero_model n a w hpos hwsum
  have hQ :
      DifferentiableAt ℂ (weightedRootQ n a w) (0 : ℂ) :=
    weightedRootQ_differentiableAt_zero n a w hpos
  exact heq.differentiableAt_iff.2 hQ

/-- A positive real exponent gives one-sided continuity of a shifted principal power on
    the closed upper half-plane.  The only nontrivial case is a negative real base, where we
    use the upper-bank continuity theorem for `Complex.log`. -/
private theorem continuousWithinAt_shift_cpow_upper
    (a w : ℝ) (hw : 0 < w) {z : ℂ} (hz : 0 ≤ z.im) :
    ContinuousWithinAt
      (fun ζ : ℂ => (ζ - (a : ℂ)) ^ (w : ℂ))
      {ζ : ℂ | 0 ≤ ζ.im} z := by
  let g : ℂ → ℂ := fun ζ => ζ - (a : ℂ)
  let S : Set ℂ := {ζ : ℂ | 0 ≤ ζ.im}
  have hg : ContinuousWithinAt g S z :=
    (continuousAt_id.sub continuousAt_const).continuousWithinAt
  by_cases hgood : 0 ≤ (g z).re ∨ (g z).im ≠ 0
  · have hp : ContinuousAt (fun u : ℂ => u ^ (w : ℂ)) (g z) :=
      Complex.continuousAt_cpow_const_of_re_pos hgood (by simpa using hw)
    simpa [g, S, Function.comp_def] using hp.comp_continuousWithinAt hg
  · have hre : (g z).re < 0 := by
      have hnot : ¬ 0 ≤ (g z).re := by
        intro h
        exact hgood (Or.inl h)
      exact lt_of_not_ge hnot
    have him : (g z).im = 0 := by
      by_contra hne
      exact hgood (Or.inr hne)
    have hg0 : g z ≠ 0 := by
      intro hzero
      have hzre : (g z).re = 0 := by simp [hzero]
      linarith
    have hmaps : Set.MapsTo g S S := by
      intro ζ hζ
      simpa [g, S] using hζ
    have hlog :
        ContinuousWithinAt (fun ζ : ℂ => Complex.log (g ζ)) S z := by
      simpa [Function.comp_def] using
        (Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre him).comp hg hmaps
    have hexp :
        ContinuousWithinAt
          (fun ζ : ℂ => Complex.exp (Complex.log (g ζ) * (w : ℂ))) S z :=
      (hlog.mul continuousWithinAt_const).cexp
    have heq :
        (fun ζ : ℂ => (g ζ) ^ (w : ℂ)) =ᶠ[nhdsWithin z S]
          (fun ζ : ℂ => Complex.exp (Complex.log (g ζ) * (w : ℂ))) := by
      exact (cpow_eq_nhds (a := g z) (b := (w : ℂ)) hg0).comp_tendsto hg.tendsto
    have hpoint :
        (g z) ^ (w : ℂ) = Complex.exp (Complex.log (g z) * (w : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero hg0]
    have hcpow : ContinuousWithinAt (fun ζ : ℂ => (g ζ) ^ (w : ℂ)) S z :=
      hexp.congr_of_eventuallyEq heq hpoint
    simpa [g, S] using hcpow

/-- Upper-bank continuity of the principal-power product, including the real boundary and
branch points.  Positivity of the weights controls continuity at a branch point. -/
theorem weighted_root_continuousOn_upper
    (n : ℕ) (a w : ℕ → ℝ)
    (hwpos : ∀ i < n, 0 < w i) :
    ContinuousOn (weightedRootF n a w) {z : ℂ | 0 ≤ z.im} := by
  unfold weightedRootF
  refine continuousOn_finsetProd (Finset.range n) ?_
  intro i hi
  intro z hz
  exact continuousWithinAt_shift_cpow_upper (a i) (w i)
    (hwpos i (Finset.mem_range.mp hi)) hz

/-- Holomorphy in the open upper half-plane.  Each `z - a i` is in `Complex.slitPlane`. -/
theorem weighted_root_differentiableOn_upper
    (n : ℕ) (a w : ℕ → ℝ) :
    DifferentiableOn ℂ (weightedRootF n a w) {z : ℂ | 0 < z.im} := by
  unfold weightedRootF
  apply DifferentiableOn.fun_finsetProd
  intro i hi
  apply DifferentiableOn.cpow_const
  · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const (a i : ℂ))
  · intro z hz
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using (ne_of_gt hz)

/-- Continuity of the pole-removed function on the closed upper half-plane. -/
theorem weighted_root_H_continuousOn_upper
    (n : ℕ) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    ContinuousOn (weightedRootH n a w) {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  unfold weightedRootH
  have hds :
      ContinuousWithinAt (dslope (weightedRootF n a w) 0)
        {z : ℂ | 0 ≤ z.im} z := by
    by_cases hz0 : z = 0
    · subst z
      exact
        ((continuousAt_dslope_same.mpr
          (weighted_root_differentiableAt_zero n a w hpos hwpos hwsum))).continuousWithinAt
    · exact
        (continuousWithinAt_dslope_of_ne hz0).mpr
          ((weighted_root_continuousOn_upper n a w hwpos) z hz)
  exact hds.sub continuousWithinAt_const

/-- Holomorphy of the pole-removed function in the open upper half-plane. -/
theorem weighted_root_H_differentiableOn_upper
    (n : ℕ) (a w : ℕ → ℝ) :
    DifferentiableOn ℂ (weightedRootH n a w) {z : ℂ | 0 < z.im} := by
  unfold weightedRootH
  have h0 : (0 : ℂ) ∉ {z : ℂ | 0 < z.im} := by simp
  have hds :
      DifferentiableOn ℂ (dslope (weightedRootF n a w) 0) {z : ℂ | 0 < z.im} :=
    (differentiableOn_dslope_of_notMem h0).mpr
      (weighted_root_differentiableOn_upper n a w)
  exact hds.sub (differentiableOn_const (1 : ℂ))

/-- On the positive real axis, taking the imaginary part of the pole-removed function gives
exactly the boundary integrand from the target theorem. -/
theorem weighted_root_H_im_of_pos
    (n : ℕ) (a w : ℕ → ℝ)
    (hF0 : (weightedRootF n a w 0).im = 0)
    {x : ℝ} (hx : 0 < x) :
    (weightedRootH n a w (x : ℂ)).im =
      (weightedRootF n a w (x : ℂ)).im / x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hmul := sub_smul_dslope (weightedRootF n a w) 0 (x : ℂ)
  have him := congrArg Complex.im hmul
  rw [weightedRootH]
  simp only [Complex.sub_im, Complex.one_im, sub_zero]
  rw [eq_div_iff hx0]
  simpa [hF0, mul_comm] using him

/-- The principal-power product itself is real off the effective slit.  If a factor
    vanishes then the whole product vanishes; otherwise the existing finite-product boundary
    formula has phase `π` on the left and phase `0` on the right. -/
theorem weightedRootF_im_eq_zero_outside
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1)
    {x : ℝ}
    (hx : x ≤ a 0 ∨ a (n - 1) ≤ x) :
    (weightedRootF n a w (x : ℂ)).im = 0 := by
  by_cases hz : ∃ i ∈ Finset.range n, x - a i = 0
  · rcases hz with ⟨i, hi, hxi⟩
    have hwi : (w i : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hwpos i (Finset.mem_range.mp hi)))
    have hfac : ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ) = 0 := by
      have hbase : (x : ℂ) - (a i : ℂ) = 0 := by
        exact_mod_cast hxi
      rw [hbase]
      exact Complex.zero_cpow hwi
    unfold weightedRootF
    rw [Finset.prod_eq_zero hi hfac]
    simp
  · have hnz : ∀ i ∈ Finset.range n, x - a i ≠ 0 := by
      intro i hi hzero
      exact hz ⟨i, hi, hzero⟩
    have hb := cpow_finset_boundary_product
      (Finset.range n) (fun i => x - a i) w hnz
    have hprod :
        weightedRootF n a w (x : ℂ) =
          ((∏ i ∈ Finset.range n, Real.rpow |x - a i| (w i) : ℝ) : ℂ) *
            Complex.exp
              ((((Real.pi *
                (∑ i ∈ (Finset.range n).filter (fun j => x - a j < 0), w i) : ℝ) : ℝ) : ℂ) *
                Complex.I) := by
      simpa [weightedRootF] using hb
    rw [hprod]
    rcases hx with hxL | hxR
    · have hfilter :
          (Finset.range n).filter (fun j => x - a j < 0) = Finset.range n := by
        apply Finset.filter_eq_self.mpr
        intro i hi
        have h0i : a 0 ≤ a i :=
          weighted_root_index_mono n a hmono (by omega)
            (Finset.mem_range.mp hi) (Nat.zero_le i)
        have hle : x - a i ≤ 0 := by linarith
        exact lt_of_le_of_ne hle (hnz i hi)
      rw [hfilter, hwsum]
      simp
      exact ofReal_prod_im n (fun i => |x - a i| ^ w i)
    · have hfilter :
          (Finset.range n).filter (fun j => x - a j < 0) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i hi
        have hilast : a i ≤ a (n - 1) :=
          weighted_root_index_mono n a hmono (Finset.mem_range.mp hi)
            (Nat.sub_lt (by omega) (by norm_num))
            (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))
        have hnonneg : 0 ≤ x - a i := by linarith
        exact not_lt_of_ge hnonneg
      rw [hfilter]
      simp
      exact ofReal_prod_im n (fun i => |x - a i| ^ w i)

/-- Away from the single removable point `x = 0`, the imaginary part of the renormalised
    boundary value is supported on the effective slit.  The point `0` is irrelevant to the
    interval integral and is therefore deliberately excluded from this support lemma. -/
theorem weighted_root_H_im_eq_zero_outside
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1)
    {x : ℝ} (hx0 : x ≠ 0)
    (hx : x ≤ a 0 ∨ a (n - 1) ≤ x) :
    (weightedRootH n a w (x : ℂ)).im = 0 := by
  have hF0 : (weightedRootF n a w 0).im = 0 := by
    rw [weightedRootF_zero n a w hpos hwsum]
    simp
    exact ofReal_prod_im n (fun i => a i ^ w i)
  have hFx : (weightedRootF n a w (x : ℂ)).im = 0 :=
    weightedRootF_im_eq_zero_outside n hn a w hmono hwpos hwsum hx
  have hmul := sub_smul_dslope (weightedRootF n a w) 0 (x : ℂ)
  have him := congrArg Complex.im hmul
  rw [weightedRootH]
  simp only [Complex.sub_im, Complex.one_im, sub_zero]
  rw [sub_zero, smul_eq_mul] at him
  have him' : x * (dslope (weightedRootF n a w) 0 (x : ℂ)).im = 0 := by
    simpa [Complex.mul_im, hF0, hFx] using him
  exact (mul_eq_zero.mp him').resolve_left hx0

/-- If two nonzero factors and their product lie in the closed upper half-plane, and the
    sum of the two principal arguments is strictly below `2π`, then no `2π` wrap occurs in
    the principal argument of the product.  This packages the only argument-bookkeeping
    needed by the reciprocal factorisation below. -/
private theorem arg_add_mem_Ioc_of_im_nonneg
    {x y : ℂ} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxim : 0 ≤ x.im) (hyim : 0 ≤ y.im)
    (hxyim : 0 ≤ (x * y).im)
    (hsum_lt : x.arg + y.arg < 2 * Real.pi) :
    x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hxarg : 0 ≤ x.arg := Complex.arg_nonneg_iff.mpr hxim
  have hyarg : 0 ≤ y.arg := Complex.arg_nonneg_iff.mpr hyim
  constructor
  · linarith [Real.pi_pos]
  · by_contra hnot
    have hpi_lt : Real.pi < x.arg + y.arg := lt_of_not_ge hnot
    have hmem : x.arg + y.arg ∈ Set.Ioc Real.pi (3 * Real.pi) := by
      constructor
      · exact hpi_lt
      · linarith [hsum_lt, Real.pi_pos]
    have hwrap :
        ((↑(x.arg + y.arg) : Real.Angle).toReal) =
          x.arg + y.arg - 2 * Real.pi :=
      Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr hmem
    have hangle :
        (↑((x * y).arg) : Real.Angle) =
          (↑(x.arg + y.arg) : Real.Angle) := by
      rw [Real.Angle.coe_add]
      exact Complex.arg_mul_coe_angle hx0 hy0
    have hto :
        (x * y).arg = ((↑(x.arg + y.arg) : Real.Angle).toReal) := by
      calc
        (x * y).arg = ((↑((x * y).arg) : Real.Angle).toReal) := by
          symm
          exact Complex.arg_coe_angle_toReal_eq_arg (x * y)
        _ = ((↑(x.arg + y.arg) : Real.Angle).toReal) := by rw [hangle]
    have hprodarg : 0 ≤ (x * y).arg := Complex.arg_nonneg_iff.mpr hxyim
    rw [hto, hwrap] at hprodarg
    linarith

/-- On the closed upper half-plane, a shifted principal power factors through the reciprocal
    variable without crossing the logarithm branch cut.  The zero second-factor case is
    handled separately, so the logarithm argument only sees nonzero factors. -/
private theorem cpow_shift_factor_upper
    (z : ℂ) (a w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hz0 : z ≠ 0) (hzim : 0 ≤ z.im) :
    (z - (a : ℂ)) ^ (w : ℂ) =
      z ^ (w : ℂ) * (1 - (a : ℂ) * z⁻¹) ^ (w : ℂ) := by
  let q : ℂ := 1 - (a : ℂ) * z⁻¹
  have hprod : z * q = z - (a : ℂ) := by
    dsimp [q]
    calc
      z * (1 - (a : ℂ) * z⁻¹) = z - (a : ℂ) * (z * z⁻¹) := by ring
      _ = z - (a : ℂ) := by rw [mul_inv_cancel₀ hz0, mul_one]
  by_cases hq0 : q = 0
  · have hbase0 : z - (a : ℂ) = 0 := by rw [← hprod, hq0, mul_zero]
    have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hw
    rw [show 1 - (a : ℂ) * z⁻¹ = q by rfl, hq0, hbase0,
      Complex.zero_cpow hw0, mul_zero]
  · have hinv_im : z⁻¹.im ≤ 0 := by
      rw [Complex.inv_im]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hzim) (Complex.normSq_nonneg z)
    have hqim : 0 ≤ q.im := by
      dsimp [q]
      simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, zero_sub]
      have hmul_nonpos : a * z⁻¹.im ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hinv_im
      linarith only [hmul_nonpos]
    have hprod_im : 0 ≤ (z * q).im := by
      rw [hprod]
      simpa using hzim
    have hsum_lt : z.arg + q.arg < 2 * Real.pi := by
      have hzle : z.arg ≤ Real.pi := Complex.arg_le_pi z
      have hqle : q.arg ≤ Real.pi := Complex.arg_le_pi q
      by_cases hz_im0 : z.im = 0
      · by_cases hzre : 0 ≤ z.re
        · have hzlt : z.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inl hzre)
          linarith
        · have hzre_neg : z.re < 0 := lt_of_not_ge hzre
          have hnormSq : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
          have hinv_re_neg : z⁻¹.re < 0 := by
            rw [Complex.inv_re]
            exact div_neg_of_neg_of_pos hzre_neg hnormSq
          have hqre : 0 < q.re := by
            dsimp [q]
            simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, zero_mul, sub_zero]
            have hmul_neg : a * z⁻¹.re < 0 :=
              mul_neg_of_pos_of_neg ha hinv_re_neg
            linarith only [hmul_neg]
          have hqlt : q.arg < Real.pi :=
            Complex.arg_lt_pi_iff.mpr (Or.inl (le_of_lt hqre))
          linarith
      · have hzlt : z.arg < Real.pi :=
          Complex.arg_lt_pi_iff.mpr (Or.inr hz_im0)
        linarith
    have hargs : z.arg + q.arg ∈ Set.Ioc (-Real.pi) Real.pi :=
      arg_add_mem_Ioc_of_im_nonneg hz0 hq0 hzim hqim hprod_im hsum_lt
    have hlog : Complex.log (z * q) = Complex.log z + Complex.log q :=
      Complex.log_mul hz0 hq0 hargs
    rw [show z - (a : ℂ) = z * q by exact hprod.symm,
      show 1 - (a : ℂ) * z⁻¹ = q by rfl,
      Complex.cpow_def_of_ne_zero (mul_ne_zero hz0 hq0),
      Complex.cpow_def_of_ne_zero hz0,
      Complex.cpow_def_of_ne_zero hq0, hlog]
    rw [show (Complex.log z + Complex.log q) * (w : ℂ) =
        Complex.log z * (w : ℂ) + Complex.log q * (w : ℂ) by ring,
      Complex.exp_add]

/-- Finite products of principal powers with a fixed nonzero base combine by adding their
    real exponents. -/
private theorem finset_prod_cpow_same_base
    (n : ℕ) (z : ℂ) (w : ℕ → ℝ) (hz0 : z ≠ 0) :
    (∏ i ∈ Finset.range n, z ^ (w i : ℂ)) =
      z ^ (((∑ i ∈ Finset.range n, w i : ℝ) : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
      push_cast
      rw [Complex.cpow_add _ _ hz0]

/-- Exact reciprocal factorisation of the full weighted product on the closed upper
    half-plane.  The total power of `z` collapses to `z` because the weights sum to one. -/
theorem weightedRootF_eq_mul_P_inv_upper
    (n : ℕ) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1)
    {z : ℂ} (hz0 : z ≠ 0) (hzim : 0 ≤ z.im) :
    weightedRootF n a w z = z * weightedRootP n a w z⁻¹ := by
  have hwsumC : (((∑ i ∈ Finset.range n, w i : ℝ) : ℂ)) = 1 := by
    exact_mod_cast hwsum
  unfold weightedRootF weightedRootP
  calc
    (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) =
        ∏ i ∈ Finset.range n,
          (z ^ (w i : ℂ) *
            (1 - (a i : ℂ) * z⁻¹) ^ (w i : ℂ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact cpow_shift_factor_upper z (a i) (w i)
        (hpos i (Finset.mem_range.mp hi))
        (hwpos i (Finset.mem_range.mp hi)) hz0 hzim
    _ = (∏ i ∈ Finset.range n, z ^ (w i : ℂ)) *
        (∏ i ∈ Finset.range n,
          (1 - (a i : ℂ) * z⁻¹) ^ (w i : ℂ)) := by
      rw [Finset.prod_mul_distrib]
    _ = z ^ (((∑ i ∈ Finset.range n, w i : ℝ) : ℂ)) *
        (∏ i ∈ Finset.range n,
          (1 - (a i : ℂ) * z⁻¹) ^ (w i : ℂ)) := by
      rw [finset_prod_cpow_same_base n z w hz0]
    _ = z * ∏ i ∈ Finset.range n,
          (1 - (a i : ℂ) * z⁻¹) ^ (w i : ℂ) := by
      rw [hwsumC, Complex.cpow_one]

/-- Uniform first-order expansion in the closed upper half-plane.  This is the exact strength
needed for the three non-real sides of a large rectangle: `z * H z` tends uniformly to
`P'(0) - F(0)`. -/
theorem weighted_root_H_inv_asymptotic_upper
    (n : ℕ) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ →
        ‖z * weightedRootH n a w z -
          (deriv (weightedRootP n a w) 0 - weightedRootF n a w 0)‖ < ε := by
  intro ε hε
  have hD := weightedRootP_hasDerivAt_zero n a w
  have hslope := hD.tendsto_slope_zero
  rw [Metric.tendsto_nhdsWithin_nhds] at hslope
  rcases hslope ε hε with ⟨δ, hδ, hclose⟩
  let R : ℝ := δ⁻¹ + 1
  have hR : 0 < R := by
    dsimp [R]
    have hinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr (le_of_lt hδ)
    linarith
  refine ⟨R, hR, ?_⟩
  intro z hzim hzR
  have hnormpos : 0 < ‖z‖ := lt_of_lt_of_le hR hzR
  have hz0 : z ≠ 0 := norm_pos_iff.mp hnormpos
  have hRlt : δ⁻¹ < ‖z‖ := by
    dsimp [R] at hzR
    linarith
  have hinvnorm : ‖z‖⁻¹ < δ :=
    (inv_lt_comm₀ hδ hnormpos).mp hRlt
  have ht0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
  have htdist : dist z⁻¹ 0 < δ := by
    simpa [dist_zero, norm_inv] using hinvnorm
  have hs := hclose (by simpa using ht0) htdist
  have hfac := weightedRootF_eq_mul_P_inv_upper
    n a w hpos hwpos hwsum hz0 hzim
  have hp0 := weightedRootP_zero n a w
  have hs' :
      ‖z * (weightedRootP n a w z⁻¹ - 1) -
        deriv (weightedRootP n a w) 0‖ < ε := by
    simpa [smul_eq_mul, hp0, dist_eq_norm, (weightedRootP_hasDerivAt_zero n a w).deriv] using hs
  rw [weightedRoot_mul_H, hfac]
  convert hs' using 1 <;> ring

/-- Generic upper-half-plane rectangle lemma.  The coefficient at infinity is assumed real;
this is exactly the case needed for the weighted-root application.  The asymptotic hypothesis is
stated as a uniform epsilon bound because it controls the top and both vertical sides of a large
square directly. -/
theorem upper_halfplane_rectangle_im_integral
    (H : ℂ → ℂ) (c : ℂ) (L U : ℝ)
    (hLU : L ≤ U)
    (hcont : ContinuousOn H {z : ℂ | 0 ≤ z.im})
    (hdiff : DifferentiableOn ℂ H {z : ℂ | 0 < z.im})
    (hsupp : ∀ x : ℝ, x ≠ 0 → x ≤ L ∨ U ≤ x → (H (x : ℂ)).im = 0)
    (hcim : c.im = 0)
    (hasym : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖z * H z - c‖ < ε) :
    (∫ x in L..U, (H (x : ℂ)).im) = -Real.pi * c.re := by
  have htarget : ∀ ε : ℝ, 0 < ε →
      |(∫ x in L..U, (H (x : ℂ)).im) + Real.pi * c.re| < ε := by
    intro ε hε
    obtain ⟨R, hR, hRasym⟩ := hasym (ε / 8) (by positivity)

    let M : ℝ := max R (max (-L) U)
    let S : ℝ := M + 1
    have hRM : R ≤ M := by simp [M]
    have hnegLM : -L ≤ M := by
      dsimp [M]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hUM : U ≤ M := by
      dsimp [M]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hMS : M < S := by simp [S]
    have hRS : R ≤ S := hRM.trans hMS.le
    have hS : 0 < S := lt_of_lt_of_le hR hRS
    have hLS : -S ≤ L := by linarith
    have hUS : U ≤ S := by linarith
    have hminusS_le_S : -S ≤ S := by linarith

    have hbottom_int : IntervalIntegrable (fun x : ℝ => H (x : ℂ)) MeasureTheory.volume (-S) S := by
      refine (hcont.comp ?_ ?_).intervalIntegrable
      · fun_prop
      · intro x hx
        simp
    have htop_int :
        IntervalIntegrable (fun x : ℝ => H ((x : ℂ) + (S : ℂ) * Complex.I))
         MeasureTheory.volume (-S) S := by
      refine (hcont.comp ?_ ?_).intervalIntegrable
      · fun_prop
      · intro x hx
        simp [hS.le]
    have hright_int :
        IntervalIntegrable (fun y : ℝ => H ((S : ℂ) + (y : ℂ) * Complex.I))
         MeasureTheory.volume 0 S := by
      refine (hcont.comp ?_ ?_).intervalIntegrable
      · fun_prop
      · intro y hy
        rw [uIcc_of_le hS.le] at hy
        simpa using hy.1
    have hleft_int :
        IntervalIntegrable (fun y : ℝ => H ((-S : ℂ) + (y : ℂ) * Complex.I))
         MeasureTheory.volume 0 S := by
      refine (hcont.comp ?_ ?_).intervalIntegrable
      · fun_prop
      · intro y hy
        rw [uIcc_of_le hS.le] at hy
        simpa using hy.1

    have htop_model_int :
        IntervalIntegrable
          (fun x : ℝ => c / ((x : ℂ) + (S : ℂ) * Complex.I)) MeasureTheory.volume (-S) S := by
      apply Continuous.intervalIntegrable
      exact Continuous.div continuous_const (by fun_prop) (fun x => ofReal_add_mul_I_ne_zero (ne_of_gt hS))
    have hright_model_int :
        IntervalIntegrable
          (fun y : ℝ => c / ((S : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume 0 S := by
      apply Continuous.intervalIntegrable
      exact Continuous.div continuous_const (by fun_prop) (fun y => ofReal_const_add_mul_I_ne_zero (ne_of_gt hS))
    have hleft_model_int :
        IntervalIntegrable
          (fun y : ℝ => c / ((-S : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume 0 S := by
      apply Continuous.intervalIntegrable
      exact Continuous.div continuous_const (by fun_prop) (fun y => neg_ofReal_add_mul_I_ne_zero (ne_of_gt hS))

    have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      H (-S : ℂ) ((S : ℂ) + (S : ℂ) * Complex.I) (by
        apply hcont.mono
        intro z hz
        have hzim : z.im ∈ [[(0 : ℝ), S]] := by
          simpa using hz.2
        rw [uIcc_of_le hS.le] at hzim
        exact hzim.1) (by
        apply hdiff.mono
        intro z hz
        have hzim : z.im ∈ Set.Ioo (0 : ℝ) S := by
          simpa [min_eq_left hS.le, max_eq_right hS.le] using hz.2
        exact hzim.1)
    have hrect_im := congrArg Complex.im hrect
    simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_zero, Complex.ofReal_neg, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add, one_mul,
      Complex.zero_im, Complex.sub_im, neg_zero, smul_eq_mul] at hrect_im
    have hImB :
        Complex.im (∫ x in (-S)..S, H (x : ℂ)) =
          ∫ x in (-S)..S, Complex.im (H (x : ℂ)) := by
      simpa only [RCLike.im_eq_complex_im] using
        (intervalIntegral.intervalIntegral_im
          (𝕜 := ℂ) (μ := MeasureTheory.volume) hbottom_int).symm
    have hImT :
        Complex.im (∫ x in (-S)..S, H ((x : ℂ) + (S : ℂ) * Complex.I)) =
          ∫ x in (-S)..S, Complex.im (H ((x : ℂ) + (S : ℂ) * Complex.I)) := by
      simpa only [RCLike.im_eq_complex_im] using
        (intervalIntegral.intervalIntegral_im
          (𝕜 := ℂ) (μ := MeasureTheory.volume) htop_int).symm
    have hReR :
        Complex.re (∫ y in (0 : ℝ)..S, H ((S : ℂ) + (y : ℂ) * Complex.I)) =
          ∫ y in (0 : ℝ)..S, Complex.re (H ((S : ℂ) + (y : ℂ) * Complex.I)) := by
      simpa only [RCLike.re_eq_complex_re] using
        (intervalIntegral.intervalIntegral_re
          (𝕜 := ℂ) (μ := MeasureTheory.volume) hright_int).symm
    have hReL :
        Complex.re (∫ y in (0 : ℝ)..S, H ((-S : ℂ) + (y : ℂ) * Complex.I)) =
          ∫ y in (0 : ℝ)..S, Complex.re (H ((-S : ℂ) + (y : ℂ) * Complex.I)) := by
      simpa only [RCLike.re_eq_complex_re] using
        (intervalIntegral.intervalIntegral_re
          (𝕜 := ℂ) (μ := MeasureTheory.volume) hleft_int).symm
    rw [hImB, hImT, hReR, hReL] at hrect_im

    have hrealH : Continuous (fun x : ℝ => H (x : ℂ)) := by
      rw [← continuousOn_univ]
      exact hcont.comp Complex.continuous_ofReal.continuousOn (by
        intro x hx
        simp)
    have hreal_cont : Continuous (fun x : ℝ => (H (x : ℂ)).im) := by
      simpa only [Function.comp_def, RCLike.im_eq_complex_im] using
        Complex.continuous_im.comp hrealH
    have hreal_int : ∀ p q : ℝ,
        IntervalIntegrable (fun x : ℝ => (H (x : ℂ)).im) MeasureTheory.volume p q := by
      intro p q
      exact hreal_cont.intervalIntegrable p q

    have hleft_zero : (∫ x in -S..L, (H (x : ℂ)).im) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [(MeasureTheory.volume : MeasureTheory.Measure ℝ).ae_ne 0] with x hx0
      intro hxmem
      rw [uIoc_of_le hLS] at hxmem
      exact hsupp x hx0 (Or.inl hxmem.2)
    have hright_zero : (∫ x in U..S, (H (x : ℂ)).im) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [(MeasureTheory.volume : MeasureTheory.Measure ℝ).ae_ne 0] with x hx0
      intro hxmem
      rw [uIoc_of_le hUS] at hxmem
      exact hsupp x hx0 (Or.inr hxmem.1.le)
    have hbottom_support :
        (∫ x in -S..S, (H (x : ℂ)).im) = ∫ x in L..U, (H (x : ℂ)).im := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hreal_int (-S) L) (hreal_int L U)
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hreal_int (-S) U) (hreal_int U S)
      rw [hleft_zero] at h1
      rw [hright_zero] at h2
      linarith

    have htop_model :
        (∫ x in -S..S, (c / ((x : ℂ) + (S : ℂ) * Complex.I)).im) =
          -(Real.pi / 2) * c.re := by
      have hpoint : ∀ x : ℝ,
          (c / ((x : ℂ) + (S : ℂ) * Complex.I)).im =
            -c.re * (S / (S ^ 2 + x ^ 2)) := by
        intro x
        simp [Complex.div_im, Complex.normSq_apply, hcim, sq]
        ring
      calc
        (∫ x in -S..S, (c / ((x : ℂ) + (S : ℂ) * Complex.I)).im)
            = ∫ x in -S..S, -c.re * (S / (S ^ 2 + x ^ 2)) := by
                apply intervalIntegral.integral_congr
                intro x hx
                exact hpoint x
        _ = -c.re * (∫ x in -S..S, S / (S ^ 2 + x ^ 2)) := by
              rw [intervalIntegral.integral_const_mul]
        _ = -(Real.pi / 2) * c.re := by
              rw [integral_div_sq_add_sq]
              simp [hS.ne', Real.arctan_one, Real.arctan_neg]
              ring

    have hright_model :
        (∫ y in 0..S, (c / ((S : ℂ) + (y : ℂ) * Complex.I)).re) =
          Real.pi / 4 * c.re := by
      have hpoint : ∀ y : ℝ,
          (c / ((S : ℂ) + (y : ℂ) * Complex.I)).re =
            c.re * (S / (S ^ 2 + y ^ 2)) := by
        intro y
        simp [Complex.div_re, Complex.normSq_apply, hcim, sq]
        ring
      calc
        (∫ y in 0..S, (c / ((S : ℂ) + (y : ℂ) * Complex.I)).re)
            = ∫ y in 0..S, c.re * (S / (S ^ 2 + y ^ 2)) := by
                apply intervalIntegral.integral_congr
                intro y hy
                exact hpoint y
        _ = c.re * (∫ y in 0..S, S / (S ^ 2 + y ^ 2)) := by
              rw [intervalIntegral.integral_const_mul]
        _ = Real.pi / 4 * c.re := by
              rw [integral_div_sq_add_sq]
              simp [hS.ne', Real.arctan_one]
              ring

    have hleft_model :
        (∫ y in 0..S, (c / ((-S : ℂ) + (y : ℂ) * Complex.I)).re) =
          -(Real.pi / 4) * c.re := by
      have hpoint : ∀ y : ℝ,
          (c / ((-S : ℂ) + (y : ℂ) * Complex.I)).re =
            -c.re * (S / (S ^ 2 + y ^ 2)) := by
        intro y
        simp [Complex.div_re, Complex.normSq_apply, hcim, sq]
        ring
      calc
        (∫ y in 0..S, (c / ((-S : ℂ) + (y : ℂ) * Complex.I)).re)
            = ∫ y in 0..S, -c.re * (S / (S ^ 2 + y ^ 2)) := by
                apply intervalIntegral.integral_congr
                intro y hy
                exact hpoint y
        _ = -c.re * (∫ y in 0..S, S / (S ^ 2 + y ^ 2)) := by
              rw [intervalIntegral.integral_const_mul]
        _ = -(Real.pi / 4) * c.re := by
              rw [integral_div_sq_add_sq]
              simp [hS.ne', Real.arctan_one]
              ring

    have hside_error : ∀ z : ℂ, 0 ≤ z.im → S ≤ ‖z‖ →
        ‖H z - c / z‖ < ε / (8 * S) := by
      intro z hzim hznorm
      have hz0 : z ≠ 0 := by
        intro hz
        subst z
        have hSnonpos : S ≤ 0 := by
          simpa only [norm_zero] using hznorm
        linarith only [hS, hSnonpos]
      have ha := hRasym z hzim (hRS.trans hznorm)
      have hdiv : H z - c / z = (z * H z - c) / z := by
        field_simp [hz0]
      rw [hdiv, norm_div]
      have hden : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      calc
        ‖z * H z - c‖ / ‖z‖ < (ε / 8) / ‖z‖ :=
          div_lt_div_of_pos_right ha hden
        _ ≤ (ε / 8) / S :=
          div_le_div_of_nonneg_left (by positivity) hS hznorm
        _ = ε / (8 * S) := by field_simp [hS.ne']

    have htop_im_int :
        IntervalIntegrable
          (fun x : ℝ => (H ((x : ℂ) + (S : ℂ) * Complex.I)).im)
          MeasureTheory.volume (-S) S := by
      constructor
      · simpa only [MeasureTheory.IntegrableOn, RCLike.im_eq_complex_im] using htop_int.1.im
      · simpa only [MeasureTheory.IntegrableOn, RCLike.im_eq_complex_im] using htop_int.2.im
    have htop_model_im_int :
        IntervalIntegrable
          (fun x : ℝ => (c / ((x : ℂ) + (S : ℂ) * Complex.I)).im)
          MeasureTheory.volume (-S) S := by
      constructor
      · simpa only [MeasureTheory.IntegrableOn, RCLike.im_eq_complex_im] using htop_model_int.1.im
      · simpa only [MeasureTheory.IntegrableOn, RCLike.im_eq_complex_im] using htop_model_int.2.im
    have hright_re_int :
        IntervalIntegrable
          (fun y : ℝ => (H ((S : ℂ) + (y : ℂ) * Complex.I)).re)
          MeasureTheory.volume 0 S := by
      constructor
      · simpa only [MeasureTheory.IntegrableOn, RCLike.re_eq_complex_re] using hright_int.1.re
      · simpa only [MeasureTheory.IntegrableOn, RCLike.re_eq_complex_re] using hright_int.2.re
    have hright_model_re_int :
        IntervalIntegrable
          (fun y : ℝ => (c / ((S : ℂ) + (y : ℂ) * Complex.I)).re)
          MeasureTheory.volume 0 S := by
      constructor
      · simpa only [MeasureTheory.IntegrableOn, RCLike.re_eq_complex_re] using hright_model_int.1.re
      · simpa only [MeasureTheory.IntegrableOn, RCLike.re_eq_complex_re] using hright_model_int.2.re
    have hleft_re_int :
        IntervalIntegrable
          (fun y : ℝ => (H ((-S : ℂ) + (y : ℂ) * Complex.I)).re)
          MeasureTheory.volume 0 S := by
      constructor
      · simpa only [MeasureTheory.IntegrableOn, RCLike.re_eq_complex_re] using hleft_int.1.re
      · simpa only [MeasureTheory.IntegrableOn, RCLike.re_eq_complex_re] using hleft_int.2.re
    have hleft_model_re_int :
        IntervalIntegrable
          (fun y : ℝ => (c / ((-S : ℂ) + (y : ℂ) * Complex.I)).re)
          MeasureTheory.volume 0 S := by
      constructor
      · simpa only [MeasureTheory.IntegrableOn, RCLike.re_eq_complex_re] using hleft_model_int.1.re
      · simpa only [MeasureTheory.IntegrableOn, RCLike.re_eq_complex_re] using hleft_model_int.2.re
    have htop_err :
        |(∫ x in -S..S, (H ((x : ℂ) + (S : ℂ) * Complex.I)).im) -
          (∫ x in -S..S, (c / ((x : ℂ) + (S : ℂ) * Complex.I)).im)| ≤ ε / 4 := by
      rw [← intervalIntegral.integral_sub htop_im_int htop_model_im_int]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (-S : ℝ)) (b := S)
        (f := fun x : ℝ =>
          (H ((x : ℂ) + (S : ℂ) * Complex.I)).im -
            (c / ((x : ℂ) + (S : ℂ) * Complex.I)).im)
        (C := ε / (8 * S)) (by
          intro x hx
          rw [Real.norm_eq_abs]
          have hzbound : S ≤ ‖(x : ℂ) + (S : ℂ) * Complex.I‖ := by
            have hh := Complex.abs_im_le_norm ((x : ℂ) + (S : ℂ) * Complex.I)
            simpa [abs_of_pos hS] using hh
          have he := hside_error ((x : ℂ) + (S : ℂ) * Complex.I)
            (by simp [hS.le]) hzbound
          simpa only [Complex.sub_im] using (Complex.abs_im_le_norm
            (H ((x : ℂ) + (S : ℂ) * Complex.I) -
              c / ((x : ℂ) + (S : ℂ) * Complex.I))).trans he.le)
      rw [Real.norm_eq_abs] at hb
      have hlen : |S - (-S)| = 2 * S := by
        have h2 : S - (-S) = 2 * S := by ring
        rw [h2, abs_of_pos (by linarith : (0 : ℝ) < 2 * S)]
      rw [hlen] at hb
      calc
        |∫ x in -S..S,
            (H ((x : ℂ) + (S : ℂ) * Complex.I)).im -
              (c / ((x : ℂ) + (S : ℂ) * Complex.I)).im|
            ≤ ε / (8 * S) * (2 * S) := hb
        _ = ε / 4 := by field_simp [hS.ne']; ring

    have hright_err :
        |(∫ y in 0..S, (H ((S : ℂ) + (y : ℂ) * Complex.I)).re) -
          (∫ y in 0..S, (c / ((S : ℂ) + (y : ℂ) * Complex.I)).re)| ≤ ε / 8 := by
      rw [← intervalIntegral.integral_sub hright_re_int hright_model_re_int]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := S)
        (f := fun y : ℝ =>
          (H ((S : ℂ) + (y : ℂ) * Complex.I)).re -
            (c / ((S : ℂ) + (y : ℂ) * Complex.I)).re)
        (C := ε / (8 * S)) (by
          intro y hy
          rw [Real.norm_eq_abs]
          have hzbound : S ≤ ‖(S : ℂ) + (y : ℂ) * Complex.I‖ := by
            have hh := Complex.abs_re_le_norm ((S : ℂ) + (y : ℂ) * Complex.I)
            simpa [abs_of_pos hS] using hh
          have hy' : y ∈ Set.Ioc 0 S := by
            simpa only [uIoc_of_le hS.le] using hy
          have he := hside_error ((S : ℂ) + (y : ℂ) * Complex.I)
            (by simpa using hy'.1.le) hzbound
          simpa only [Complex.sub_re] using (Complex.abs_re_le_norm
            (H ((S : ℂ) + (y : ℂ) * Complex.I) -
              c / ((S : ℂ) + (y : ℂ) * Complex.I))).trans he.le)
      rw [Real.norm_eq_abs] at hb
      have hCS : ε / (8 * S) * S = ε / 8 := by field_simp [hS.ne']
      simpa [abs_of_pos hS, hCS] using hb

    have hleft_err :
        |(∫ y in 0..S, (H ((-S : ℂ) + (y : ℂ) * Complex.I)).re) -
          (∫ y in 0..S, (c / ((-S : ℂ) + (y : ℂ) * Complex.I)).re)| ≤ ε / 8 := by
      rw [← intervalIntegral.integral_sub hleft_re_int hleft_model_re_int]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := S)
        (f := fun y : ℝ =>
          (H ((-S : ℂ) + (y : ℂ) * Complex.I)).re -
            (c / ((-S : ℂ) + (y : ℂ) * Complex.I)).re)
        (C := ε / (8 * S)) (by
          intro y hy
          rw [Real.norm_eq_abs]
          have hzbound : S ≤ ‖(-S : ℂ) + (y : ℂ) * Complex.I‖ := by
            have hh := Complex.abs_re_le_norm ((-S : ℂ) + (y : ℂ) * Complex.I)
            simpa [abs_of_pos hS] using hh
          have hy' : y ∈ Set.Ioc 0 S := by
            simpa only [uIoc_of_le hS.le] using hy
          have he := hside_error ((-S : ℂ) + (y : ℂ) * Complex.I)
            (by simpa using hy'.1.le) hzbound
          simpa only [Complex.sub_re] using (Complex.abs_re_le_norm
            (H ((-S : ℂ) + (y : ℂ) * Complex.I) -
              c / ((-S : ℂ) + (y : ℂ) * Complex.I))).trans he.le)
      rw [Real.norm_eq_abs] at hb
      have hCS : ε / (8 * S) * S = ε / 8 := by field_simp [hS.ne']
      simpa [abs_of_pos hS, hCS] using hb

    rw [hbottom_support] at hrect_im
    rw [htop_model] at htop_err
    rw [hright_model] at hright_err
    rw [hleft_model] at hleft_err
    have hEq :
        (∫ x in L..U, (H (x : ℂ)).im) + Real.pi * c.re =
          ((∫ x in -S..S, (H ((x : ℂ) + (S : ℂ) * Complex.I)).im) -
              (-(Real.pi / 2) * c.re)) -
          ((∫ y in 0..S, (H ((S : ℂ) + (y : ℂ) * Complex.I)).re) -
              (Real.pi / 4 * c.re)) +
          ((∫ y in 0..S, (H ((-S : ℂ) + (y : ℂ) * Complex.I)).re) -
              (-(Real.pi / 4) * c.re)) := by
      linarith [hrect_im]
    rw [hEq]
    calc
      |((∫ x in -S..S, (H ((x : ℂ) + (S : ℂ) * Complex.I)).im) -
            (-(Real.pi / 2) * c.re)) -
          ((∫ y in 0..S, (H ((S : ℂ) + (y : ℂ) * Complex.I)).re) -
            (Real.pi / 4 * c.re)) +
          ((∫ y in 0..S, (H ((-S : ℂ) + (y : ℂ) * Complex.I)).re) -
            (-(Real.pi / 4) * c.re))|
          ≤ |(∫ x in -S..S, (H ((x : ℂ) + (S : ℂ) * Complex.I)).im) -
                (-(Real.pi / 2) * c.re)| +
            |(∫ y in 0..S, (H ((S : ℂ) + (y : ℂ) * Complex.I)).re) -
                (Real.pi / 4 * c.re)| +
            |(∫ y in 0..S, (H ((-S : ℂ) + (y : ℂ) * Complex.I)).re) -
                (-(Real.pi / 4) * c.re)| := by
            have h1 :
                |((∫ x in -S..S, (H ((x : ℂ) + (S : ℂ) * Complex.I)).im) -
                      (-(Real.pi / 2) * c.re)) -
                    ((∫ y in 0..S, (H ((S : ℂ) + (y : ℂ) * Complex.I)).re) -
                      (Real.pi / 4 * c.re)) +
                    ((∫ y in 0..S, (H ((-S : ℂ) + (y : ℂ) * Complex.I)).re) -
                      (-(Real.pi / 4) * c.re))|
                  ≤ |((∫ x in -S..S, (H ((x : ℂ) + (S : ℂ) * Complex.I)).im) -
                        (-(Real.pi / 2) * c.re)) -
                      ((∫ y in 0..S, (H ((S : ℂ) + (y : ℂ) * Complex.I)).re) -
                        (Real.pi / 4 * c.re))| +
                    |(∫ y in 0..S, (H ((-S : ℂ) + (y : ℂ) * Complex.I)).re) -
                      (-(Real.pi / 4) * c.re)| :=
              abs_add_le _ _
            have h2 :
                |((∫ x in -S..S, (H ((x : ℂ) + (S : ℂ) * Complex.I)).im) -
                      (-(Real.pi / 2) * c.re)) -
                    ((∫ y in 0..S, (H ((S : ℂ) + (y : ℂ) * Complex.I)).re) -
                      (Real.pi / 4 * c.re))|
                  ≤ |(∫ x in -S..S, (H ((x : ℂ) + (S : ℂ) * Complex.I)).im) -
                      (-(Real.pi / 2) * c.re)| +
                    |(∫ y in 0..S, (H ((S : ℂ) + (y : ℂ) * Complex.I)).re) -
                      (Real.pi / 4 * c.re)| := by
              have h :=
                abs_add_le
                  ((∫ x in -S..S, (H ((x : ℂ) + (S : ℂ) * Complex.I)).im) -
                    (-(Real.pi / 2) * c.re))
                  (-(((∫ y in 0..S, (H ((S : ℂ) + (y : ℂ) * Complex.I)).re) -
                    (Real.pi / 4 * c.re))))
              simpa only [sub_eq_add_neg, abs_neg] using h
            linarith
      _ ≤ ε / 4 + ε / 8 + ε / 8 := by gcongr
      _ < ε := by linarith

  have habszero : |(∫ x in L..U, (H (x : ℂ)).im) + Real.pi * c.re| = 0 := by
    apply le_antisymm
    · by_contra hne
      have hp : 0 < |(∫ x in L..U, (H (x : ℂ)).im) + Real.pi * c.re| :=
        lt_of_not_ge hne
      exact (lt_irrefl _ (htarget _ hp))
    · exact abs_nonneg _
  have hz : (∫ x in L..U, (H (x : ℂ)).im) + Real.pi * c.re = 0 :=
    abs_eq_zero.mp habszero
  linarith

end

end WeightedRootIntegralIdentity

open WeightedRootIntegralIdentity

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    2 * (∫ x in a 0..a (n - 1),
        (∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)).im / x) =
      2 * Real.pi *
        (-(deriv
          (fun u : ℂ =>
            ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
          (∏ i ∈ Finset.range n,
            (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re) := by
  let F : ℂ → ℂ := weightedRootF n a w
  let P : ℂ → ℂ := weightedRootP n a w
  let H : ℂ → ℂ := weightedRootH n a w

  have hLU : a 0 ≤ a (n - 1) :=
    weighted_root_endpoint_le n hn a hmono

  have hF0eq :
      F 0 = -((∏ i ∈ Finset.range n, Real.rpow (a i) (w i) : ℝ) : ℂ) := by
    simpa [F] using weightedRootF_zero n a w hpos hwsum

  have hF0 : (F 0).im = 0 := by
    rw [hF0eq]
    simp
    exact ofReal_prod_im n (fun i => a i ^ w i)

  have hrect :
      (∫ x in a 0..a (n - 1), (H (x : ℂ)).im) =
        -Real.pi * (deriv P 0 - F 0).re := by
    refine upper_halfplane_rectangle_im_integral H
      (deriv P 0 - F 0) (a 0) (a (n - 1)) hLU ?_ ?_ ?_ ?_ ?_
    · simpa [H] using weighted_root_H_continuousOn_upper n a w hpos hwpos hwsum
    · simpa [H] using weighted_root_H_differentiableOn_upper n a w
    · intro x hx0 hx
      simpa [H] using
        weighted_root_H_im_eq_zero_outside n hn a w hpos hmono hwpos hwsum hx0 hx
    · have hD := (weightedRootP_hasDerivAt_zero n a w).deriv
      have hDim : (deriv P 0).im = 0 := by
        rw [show deriv P 0 =
          -((∑ i ∈ Finset.range n, w i * a i : ℝ) : ℂ) by simpa [P] using hD]
        simp
      rw [Complex.sub_im, hDim, hF0]
      ring
    · simpa [H, P, F] using
        weighted_root_H_inv_asymptotic_upper n a w hpos hwpos hwsum

  have hboundary :
      (∫ x in a 0..a (n - 1), (H (x : ℂ)).im) =
        ∫ x in a 0..a (n - 1),
          (F (x : ℂ)).im / x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hLU
    intro x hx
    have h0n : 0 < n := by omega
    have ha0 : 0 < a 0 := hpos 0 h0n
    have hxpos : 0 < x := lt_trans ha0 hx.1
    have hF0' : (weightedRootF n a w 0).im = 0 := by
      simpa [F] using hF0
    simpa [H, F] using weighted_root_H_im_of_pos n a w hF0' hxpos

  have hmain :
      (∫ x in a 0..a (n - 1), (F (x : ℂ)).im / x) =
        Real.pi * (-(deriv P 0).re + (F 0).re) := by
    rw [hboundary] at hrect
    calc
      (∫ x in a 0..a (n - 1), (F (x : ℂ)).im / x)
          = -Real.pi * (deriv P 0 - F 0).re := hrect
      _ = Real.pi * (-(deriv P 0).re + (F 0).re) := by
        simp
        ring

  have hmain' :
      (∫ x in a 0..a (n - 1),
          (∏ i ∈ Finset.range n,
            ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)).im / x) =
        Real.pi *
          (-(deriv
            (fun u : ℂ =>
              ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
            (∏ i ∈ Finset.range n,
              (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re) := by
    have hPfun : P =
        (fun u : ℂ => ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) := by
      funext u
      simp [P, weightedRootP]
    simpa [hPfun, F, P, weightedRootF, weightedRootP] using hmain

  calc
    2 * (∫ x in a 0..a (n - 1),
        (∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)).im / x)
        = 2 * (Real.pi *
          (-(deriv
            (fun u : ℂ =>
              ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
            (∏ i ∈ Finset.range n,
              (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re)) := by rw [hmain']
    _ = 2 * Real.pi *
        (-(deriv
          (fun u : ℂ =>
            ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
          (∏ i ∈ Finset.range n,
            (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re) := by ring
