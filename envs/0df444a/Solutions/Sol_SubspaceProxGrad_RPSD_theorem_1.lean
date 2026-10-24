-- Prove2me | solution 1 for SubspaceProxGrad.RPSD.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T08:39:22.57538+00:00
-- url     : https://prove2.me/submissions/3cadf29f-5557-45ba-b351-154c804acc1f

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_SubspaceProxGrad_RPSD_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

theorem rpsd_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem rpsd_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := rpsd_line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫) ⟪G x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  have hmono : AntitoneOn g (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hg t).continuousAt.continuousWithinAt
    · exact fun t _ => (hg t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hg t).deriv]
      have hc : ⟪G (x + t • w), w⟫ - ⟪G x, w⟫ ≤ L * t * ‖w‖ ^ 2 := by
        rw [← inner_sub_left]
        calc ⟪G (x + t • w) - G x, w⟫ ≤ ‖G (x + t • w) - G x‖ * ‖w‖ := real_inner_le_norm _ _
          _ ≤ (L * ‖x + t • w - x‖) * ‖w‖ := by gcongr; exact hG _ _
          _ = L * t * ‖w‖ ^ 2 := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]; ring
      nlinarith
  have := hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [g, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

theorem rpsd_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : E) : F x + ⟪G x, y - x⟫ ≤ F y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => F (x + t • w)) := by
    have := hc.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => F (x + t • w)) = F ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using rpsd_line_deriv hF x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  linarith

/-- strong convexity lower bound -/
theorem rpsd_lower_sc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {μ : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hsc : StrongConvexOn Set.univ μ F) (x y : E) :
    F x + ⟪G x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ F y := by
  have hc := strongConvexOn_iff_convex.1 hsc
  have hgr : ∀ z, HasGradientAt (fun x => F x - μ / (2:ℝ) * ‖x‖ ^ 2) (G z - μ • z) z := by
    intro z
    have h1 := hasGradientAt_iff_hasFDerivAt.mp (hF z)
    have h2 : HasFDerivAt (fun x : E => ‖x‖ ^ 2) (2 • (innerSL ℝ z)) z := hasStrictFDerivAt_norm_sq z |>.hasFDerivAt
    rw [hasGradientAt_iff_hasFDerivAt]
    refine (h1.sub (h2.const_mul (μ / 2))).congr_fderiv ?_
    ext v
    simp
    ring
  have h := rpsd_convex_fo hgr hc x y
  have hid : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
    have := norm_add_sq_real x (y - x)
    rw [add_sub_cancel] at this
    exact this
  simp only [inner_sub_left, real_inner_smul_left] at h
  have h3 : μ / 2 * ‖y‖ ^ 2 = μ / 2 * ‖x‖ ^ 2 + μ * ⟪x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 := by
    rw [hid]; ring
  linarith

theorem rpsd_cocoercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {K : ℝ} (hK : 0 < K)
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2)
    (hlo : ∀ x y, F x + ⟪G x, y - x⟫ ≤ F y) (x y : E) :
    ‖G y - G x‖ ^ 2 ≤ 2 * K * (F y - F x - ⟪G x, y - x⟫) := by
  set v := G y - G x with hv
  have h1 := hlo x (y - (1 / K) • v)
  have h2 := hup y (y - (1 / K) • v)
  have e1 : y - (1 / K) • v - y = -((1 / K) • v) := by abel
  have e2 : y - (1 / K) • v - x = (y - x) - (1 / K) • v := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / K)] at h2
  rw [e2, inner_sub_right, real_inner_smul_right] at h1
  have hGv : ⟪G y, v⟫ - ⟪G x, v⟫ = ‖v‖ ^ 2 := by
    rw [← inner_sub_left, ← hv, real_inner_self_eq_norm_sq]
  have hK' : K ≠ 0 := hK.ne'
  have hGv' : 1 / K * ⟪G y, v⟫ - 1 / K * ⟪G x, v⟫ = 1 / K * ‖v‖ ^ 2 := by
    rw [← mul_sub, hGv]
  have key : F y - F x - ⟪G x, y - x⟫ ≥ (1 / K) * ‖v‖ ^ 2 - K / 2 * ((1 / K) * ‖v‖) ^ 2 := by
    linarith
  have : (1 / K) * ‖v‖ ^ 2 - K / 2 * ((1 / K) * ‖v‖) ^ 2 = ‖v‖ ^ 2 / (2 * K) := by
    field_simp; ring
  rw [this] at key
  rw [ge_iff_le, div_le_iff₀ (by positivity)] at key
  linarith

theorem rpsd_cocoercive_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {K : ℝ} (hK : 0 < K)
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2)
    (hlo : ∀ x y, F x + ⟪G x, y - x⟫ ≤ F y) (x y : E) :
    ‖G x - G y‖ ^ 2 ≤ K * ⟪G x - G y, x - y⟫ := by
  have c1 := rpsd_cocoercive hK hup hlo y x
  have c2 := rpsd_cocoercive hK hup hlo x y
  rw [norm_sub_rev] at c2
  have e : ⟪G x, y - x⟫ = -⟪G x, x - y⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [e] at c2
  rw [inner_sub_left]
  linarith

/-- cocoercivity with a nonnegative constant (limit of `K + ε`). -/
theorem rpsd_cocoercive_pair0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {K : ℝ} (hK : 0 ≤ K)
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2)
    (hlo : ∀ x y, F x + ⟪G x, y - x⟫ ≤ F y) (x y : E) :
    ‖G x - G y‖ ^ 2 ≤ K * ⟪G x - G y, x - y⟫ := by
  have hε : ∀ ε : ℝ, 0 < ε → ‖G x - G y‖ ^ 2 ≤ (K + ε) * ⟪G x - G y, x - y⟫ := by
    intro ε hε
    apply rpsd_cocoercive_pair (by linarith) _ hlo
    intro a b
    have := hup a b
    have : 0 ≤ ε / 2 * ‖b - a‖ ^ 2 := by positivity
    nlinarith
  have h1 := hε 1 one_pos
  have hnn : 0 ≤ ⟪G x - G y, x - y⟫ := by
    have := sq_nonneg ‖G x - G y‖
    nlinarith
  have hlim : Filter.Tendsto (fun ε : ℝ => (K + ε) * ⟪G x - G y, x - y⟫)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (K * ⟪G x - G y, x - y⟫)) := by
    have : Continuous (fun ε : ℝ => (K + ε) * ⟪G x - G y, x - y⟫) := by fun_prop
    have h := this.tendsto 0
    simp only [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε' => hε ε hε')

/-- the gradient step is a contraction. -/
theorem rpsd_grad_contract {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} {G : E → E} {L μ t : ℝ} (hμ : 0 < μ) (hL : 0 < L) (ht : 0 < t)
    (htL : t ≤ 2 / (μ + L))
    (hup : ∀ x y, F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hlo : ∀ x y, F x + ⟪G x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ F y) (x y : E) :
    ‖(x - t • G x) - (y - t • G y)‖ ^ 2 ≤ (1 - 2 * t * μ * L / (μ + L)) * ‖x - y‖ ^ 2 := by
  have hid : ∀ x y : E, ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
    intro x y
    have := norm_add_sq_real x (y - x)
    rw [add_sub_cancel] at this
    exact this
  have hm : 0 < μ + L := by linarith
  have htL' : t * (μ + L) ≤ 2 := by rwa [le_div_iff₀ hm] at htL
  rcases le_or_gt μ L with hμL | hμL
  · have hK : 0 ≤ L - μ := by linarith
    have hup' : ∀ x y : E, (fun z => F z - μ / 2 * ‖z‖ ^ 2) y ≤
        (fun z => F z - μ / 2 * ‖z‖ ^ 2) x + ⟪(fun z => G z - μ • z) x, y - x⟫
          + (L - μ) / 2 * ‖y - x‖ ^ 2 := by
      intro x y
      have h := hup x y
      have h2 := hid x y
      simp only [inner_sub_left, real_inner_smul_left]
      nlinarith
    have hlo' : ∀ x y : E, (fun z => F z - μ / 2 * ‖z‖ ^ 2) x +
        ⟪(fun z => G z - μ • z) x, y - x⟫ ≤ (fun z => F z - μ / 2 * ‖z‖ ^ 2) y := by
      intro x y
      have h := hlo x y
      have h2 := hid x y
      simp only [inner_sub_left, real_inner_smul_left]
      nlinarith
    have hp := rpsd_cocoercive_pair0 hK hup' hlo' x y
    have hw : (G x - μ • x) - (G y - μ • y) = (G x - G y) - μ • (x - y) := by
      simp only [smul_sub]; abel
    rw [hw] at hp
    set D := G x - G y with hD
    have e1 : ‖D - μ • (x - y)‖ ^ 2 = ‖D‖ ^ 2 - 2 * μ * ⟪D, x - y⟫ + μ ^ 2 * ‖x - y‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have e2 : ⟪D - μ • (x - y), x - y⟫ = ⟪D, x - y⟫ - μ * ‖x - y‖ ^ 2 := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [e1, e2] at hp
    have hexp : ‖(x - t • G x) - (y - t • G y)‖ ^ 2 =
        ‖x - y‖ ^ 2 - 2 * t * ⟪G x - G y, x - y⟫ + t ^ 2 * ‖G x - G y‖ ^ 2 := by
      have e : (x - t • G x) - (y - t • G y) = (x - y) - t • (G x - G y) := by
        simp only [smul_sub]; abel
      rw [e, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        real_inner_comm]
      ring
    rw [hexp]
    set P := ⟪D, x - y⟫
    set Q := ‖D‖ ^ 2
    set R := ‖x - y‖ ^ 2
    have hR : 0 ≤ R := by positivity
    have hQ : 0 ≤ Q := by positivity
    have hineq : Q ≤ (μ + L) * P - μ * L * R := by
      nlinarith
    have hPc : μ * L * R ≤ (μ + L) * P := by nlinarith
    have hs : 0 ≤ t * (2 - t * (μ + L)) := mul_nonneg ht.le (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hineq (sq_nonneg t)
    have h2 := mul_nonneg hs (sub_nonneg.2 hPc)
    have goal : R - 2 * t * P + t ^ 2 * Q ≤ (1 - 2 * t * μ * L / (μ + L)) * R := by
      have e : (1 - 2 * t * μ * L / (μ + L)) * R = R - 2 * t * μ * L * R / (μ + L) := by
        field_simp
      rw [e]
      have : 2 * t * μ * L * R / (μ + L) ≤ 2 * t * P - t ^ 2 * Q := by
        rw [div_le_iff₀ hm]
        nlinarith
      linarith
    exact goal
  · -- μ > L forces all points equal
    have hxy : x = y := by
      have h1 := hup x y
      have h2 := hlo x y
      have : ‖y - x‖ ^ 2 = 0 := by
        have hn : 0 ≤ ‖y - x‖ ^ 2 := by positivity
        nlinarith
      have : y - x = 0 := by simpa using this
      exact (sub_eq_zero.1 this).symm
    subst hxy
    simp

theorem rpsd_nonneg_of_small (A B : ℝ) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ A + t * B) : 0 ≤ A := by
  have hlim : Filter.Tendsto (fun t : ℝ => A + t * B) (nhdsWithin 0 (Set.Ioi 0)) (nhds A) := by
    have : Continuous (fun t : ℝ => A + t * B) := by fun_prop
    have h := this.tendsto 0
    simp only [zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
  exact h t ht.1 ht.2.le

theorem rpsd_prox_vi {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ConvexOn ℝ C g) {γ : ℝ} (hγ : 0 < γ) {v x : EuclideanSpace ℝ (Fin n)}
    (hp : BoydADMM.Prox.IsProx C g (1 / γ) v x) :
    ∀ x' ∈ C, 0 ≤ γ * (g x' - g x) + ⟪x - v, x' - x⟫ := by
  intro x' hx'
  apply rpsd_nonneg_of_small _ (‖x' - x‖ ^ 2 / 2)
  intro t ht0 ht1
  have hmem : (1 - t) • x + t • x' ∈ C := hg.1 hp.1 hx' (by linarith) ht0.le (by ring)
  have hmin := hp.2 _ hmem
  have hcv := hg.2 hp.1 hx' (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
  simp only [smul_eq_mul] at hcv
  have e : (1 - t) • x + t • x' - v = (x - v) + t • (x' - x) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [e, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs] at hmin
  set c := 1 / γ / 2 with hc
  have h4 : 0 ≤ t * (g x' - g x) + c * (2 * (t * ⟪x - v, x' - x⟫) + t ^ 2 * ‖x' - x‖ ^ 2) := by
    nlinarith
  have key : 0 ≤ t * (γ * (g x' - g x) + ⟪x - v, x' - x⟫ + t * (‖x' - x‖ ^ 2 / 2)) := by
    calc (0:ℝ) ≤ γ * (t * (g x' - g x) + c * (2 * (t * ⟪x - v, x' - x⟫) + t ^ 2 * ‖x' - x‖ ^ 2)) :=
          mul_nonneg hγ.le h4
      _ = t * (γ * (g x' - g x) + ⟪x - v, x' - x⟫ + t * (‖x' - x‖ ^ 2 / 2)) := by
          rw [hc]; field_simp; ring
  exact (mul_nonneg_iff_of_pos_left ht0).1 key

theorem rpsd_vi_min {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ConvexOn ℝ C g)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hconv : ∀ x y, f x + ⟪G x, y - x⟫ ≤ f y)
    {L : ℝ} (hGL : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) {γ : ℝ} (hγ : 0 < γ)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : SubspaceProxGrad.RPSD.IsMinimizer C f g xs) :
    ∀ x' ∈ C, 0 ≤ γ * (g x' - g xs) + ⟪xs - (xs - γ • G xs), x' - xs⟫ := by
  intro x' hx'
  have e0 : xs - (xs - γ • G xs) = γ • G xs := by abel
  rw [e0, real_inner_smul_left, ← mul_add]
  apply mul_nonneg hγ.le
  set d := x' - xs with hd
  apply rpsd_nonneg_of_small _ (L * ‖d‖ ^ 2)
  intro t ht0 ht1
  have hmem : (1 - t) • xs + t • x' ∈ C := hg.1 hxs.1 hx' (by linarith) ht0.le (by ring)
  have ext : (1 - t) • xs + t • x' = xs + t • d := by
    simp only [hd, sub_smul, one_smul, smul_sub]; abel
  have hmin := hxs.2 _ hmem
  have hcv := hg.2 hxs.1 hx' (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
  simp only [smul_eq_mul] at hcv
  rw [ext] at hmin hcv
  have hfo := hconv (xs + t • d) xs
  have e1 : xs - (xs + t • d) = -(t • d) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right] at hfo
  have hgb : ⟪G (xs + t • d), d⟫ ≤ ⟪G xs, d⟫ + L * t * ‖d‖ ^ 2 := by
    have : ⟪G (xs + t • d), d⟫ - ⟪G xs, d⟫ ≤ L * t * ‖d‖ ^ 2 := by
      rw [← inner_sub_left]
      calc ⟪G (xs + t • d) - G xs, d⟫ ≤ ‖G (xs + t • d) - G xs‖ * ‖d‖ := real_inner_le_norm _ _
        _ ≤ (L * ‖xs + t • d - xs‖) * ‖d‖ := by gcongr; exact hGL _ _
        _ = L * t * ‖d‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]; ring
    linarith
  have key : 0 ≤ t * (g x' - g xs + ⟪G xs, d⟫ + t * (L * ‖d‖ ^ 2)) := by
    have h5 : t * ⟪G (xs + t • d), d⟫ ≤ t * (⟪G xs, d⟫ + L * t * ‖d‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hgb ht0.le
    nlinarith
  have := (mul_nonneg_iff_of_pos_left ht0).1 key
  linarith

theorem rpsd_nonexp {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {γ : ℝ} {x1 v1 x2 v2 : EuclideanSpace ℝ (Fin n)}
    (hx1 : x1 ∈ C) (hx2 : x2 ∈ C)
    (h1 : ∀ x' ∈ C, 0 ≤ γ * (g x' - g x1) + ⟪x1 - v1, x' - x1⟫)
    (h2 : ∀ x' ∈ C, 0 ≤ γ * (g x' - g x2) + ⟪x2 - v2, x' - x2⟫) :
    ‖x1 - x2‖ ≤ ‖v1 - v2‖ := by
  have a := h1 x2 hx2
  have b := h2 x1 hx1
  have e : ⟪x1 - v1, x2 - x1⟫ + ⟪x2 - v2, x1 - x2⟫ = ⟪v1 - v2, x1 - x2⟫ - ‖x1 - x2‖ ^ 2 := by
    have h3 : x2 - x1 = -(x1 - x2) := by abel
    have h4 : v1 - v2 = (x2 - v2) - (x1 - v1) + (x1 - x2) := by abel
    rw [h3, inner_neg_right, h4, inner_add_left, inner_sub_left (x2 - v2) (x1 - v1) (x1 - x2),
      real_inner_self_eq_norm_sq]
    ring
  have hle : ‖x1 - x2‖ ^ 2 ≤ ‖v1 - v2‖ * ‖x1 - x2‖ := by
    have := real_inner_le_norm (v1 - v2) (x1 - x2)
    nlinarith
  rcases (norm_nonneg (x1 - x2)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

theorem rpsd_prox_sel {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ConvexOn ℝ C g) {γ : ℝ} (hγ : 0 < γ) :
    ∃ p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), Continuous p ∧
      ∀ v x, BoydADMM.Prox.IsProx C g (1 / γ) v x → p v = x := by
  classical
  set D := {v : EuclideanSpace ℝ (Fin n) | ∃ x, BoydADMM.Prox.IsProx C g (1 / γ) v x}
  let p0 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun v =>
    if h : ∃ x, BoydADMM.Prox.IsProx C g (1 / γ) v x then h.choose else 0
  have hp0 : ∀ v x, BoydADMM.Prox.IsProx C g (1 / γ) v x → p0 v = x := by
    intro v x hx
    have hex : ∃ x, BoydADMM.Prox.IsProx C g (1 / γ) v x := ⟨x, hx⟩
    have hc := hex.choose_spec
    have h := rpsd_nonexp hc.1 hx.1 (rpsd_prox_vi hg hγ hc) (rpsd_prox_vi hg hγ hx)
    simp only [sub_self, norm_zero] at h
    have : hex.choose = x := by
      have := norm_le_zero_iff.1 h
      exact sub_eq_zero.1 this
    simp only [p0, dif_pos hex, this]
  have hlip : LipschitzOnWith 1 (fun v => WithLp.ofLp (p0 v)) D := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v1 hv1 v2 hv2
    obtain ⟨x1, hx1⟩ := hv1
    obtain ⟨x2, hx2⟩ := hv2
    have h1 := (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ)).dist_le_mul (p0 v1) (p0 v2)
    rw [hp0 v1 x1 hx1, hp0 v2 x2 hx2] at h1 ⊢
    have h2 := rpsd_nonexp hx1.1 hx2.1 (rpsd_prox_vi hg hγ hx1) (rpsd_prox_vi hg hγ hx2)
    rw [← dist_eq_norm, ← dist_eq_norm] at h2
    simp only [NNReal.coe_one, one_mul] at h1 ⊢
    exact h1.trans h2
  obtain ⟨q, hq, heq⟩ := hlip.extend_pi
  refine ⟨fun v => WithLp.toLp 2 (q v), (PiLp.continuous_toLp 2 _).comp hq.continuous, ?_⟩
  intro v x hx
  have hv : v ∈ D := ⟨x, hx⟩
  have := heq hv
  simp only at this
  show WithLp.toLp 2 (q v) = x
  rw [← this, WithLp.toLp_ofLp]
  exact hp0 v x hx

open SubspaceProxGrad.RPSD in
theorem rpsd_la {n : ℕ} (P Q Qinv : E n →L[ℝ] E n) (hQ : Q.IsPositive)
    (hQPQ : Q ∘L P ∘L Q = ContinuousLinearMap.id ℝ (E n))
    (hQi : Q ∘L Qinv = ContinuousLinearMap.id ℝ (E n))
    (hQi' : Qinv ∘L Q = ContinuousLinearMap.id ℝ (E n)) :
    (∀ u, Qinv (Q u) = u) ∧ (∀ u, Q (Qinv u) = u) ∧ (∀ b, ⟪b, P b⟫ = ‖Qinv b‖ ^ 2) ∧
    (∀ w, ⟪Q w, P (Q w)⟫ = ‖w‖ ^ 2) := by
  have h1 : ∀ u, Qinv (Q u) = u := fun u => by
    simpa using congrArg (fun T : E n →L[ℝ] E n => T u) hQi'
  have h2 : ∀ u, Q (Qinv u) = u := fun u => by
    simpa using congrArg (fun T : E n →L[ℝ] E n => T u) hQi
  have h3 : ∀ u, Q (P (Q u)) = u := fun u => by
    simpa using congrArg (fun T : E n →L[ℝ] E n => T u) hQPQ
  have hPu : ∀ u, P u = Qinv (Qinv u) := by
    intro u
    have := h3 (Qinv u)
    rw [h2] at this
    rw [← this, h1]
  have hQs : ∀ u v, ⟪Q u, v⟫ = ⟪u, Q v⟫ := hQ.inner_left_eq_inner_right
  have hQis : ∀ u v, ⟪Qinv u, v⟫ = ⟪u, Qinv v⟫ := by
    intro u v
    calc ⟪Qinv u, v⟫ = ⟪Qinv u, Q (Qinv v)⟫ := by rw [h2]
      _ = ⟪Q (Qinv u), Qinv v⟫ := (hQs _ _).symm
      _ = ⟪u, Qinv v⟫ := by rw [h2]
  refine ⟨h1, h2, ?_, ?_⟩
  · intro b
    rw [hPu, ← hQis, real_inner_self_eq_norm_sq]
  · intro w
    rw [hPu, h1, hQs, h2, real_inner_self_eq_norm_sq]

open SubspaceProxGrad.RPSD in
theorem rpsd_unit {n : ℕ} {b : E n} (hb : b ≠ 0) :
    ‖b‖⁻¹ • b ∈ Metric.sphere (0 : E n) 1 := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbn.ne']

open SubspaceProxGrad.RPSD in
theorem rpsd_ray_lo {n : ℕ} (P : E n →L[ℝ] E n) (hnn : ∀ x : E n, 0 ≤ ⟪x, P x⟫) (b : E n) :
    lamMin P * ‖b‖ ^ 2 ≤ ⟪b, P b⟫ := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hle : lamMin P ≤ ⟪‖b‖⁻¹ • b, P (‖b‖⁻¹ • b)⟫ := by
    unfold lamMin
    exact ciInf_le (f := fun x : Metric.sphere (0 : E n) 1 => ⟪(x : E n), P x⟫)
      ⟨0, by rintro _ ⟨x, rfl⟩; exact hnn x⟩ ⟨‖b‖⁻¹ • b, rpsd_unit hb⟩
  have hee : ⟪‖b‖⁻¹ • b, P (‖b‖⁻¹ • b)⟫ = ‖b‖⁻¹ ^ 2 * ⟪b, P b⟫ := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  rw [hee] at hle
  have : ‖b‖⁻¹ ^ 2 * ⟪b, P b⟫ * ‖b‖ ^ 2 = ⟪b, P b⟫ := by field_simp
  calc lamMin P * ‖b‖ ^ 2 ≤ ‖b‖⁻¹ ^ 2 * ⟪b, P b⟫ * ‖b‖ ^ 2 := by gcongr
    _ = ⟪b, P b⟫ := this

open SubspaceProxGrad.RPSD in
theorem rpsd_ray_hi {n : ℕ} (P : E n →L[ℝ] E n) (b : E n) :
    ⟪b, P b⟫ ≤ lamMax P * ‖b‖ ^ 2 := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hle : ⟪‖b‖⁻¹ • b, P (‖b‖⁻¹ • b)⟫ ≤ lamMax P := by
    unfold lamMax
    refine le_ciSup (f := fun x : Metric.sphere (0 : E n) 1 => ⟪(x : E n), P x⟫)
      ⟨‖P‖, ?_⟩ ⟨‖b‖⁻¹ • b, rpsd_unit hb⟩
    rintro _ ⟨x, rfl⟩
    have hx : ‖(x : E n)‖ = 1 := by simpa using x.2
    calc ⟪(x : E n), P x⟫ ≤ ‖(x : E n)‖ * ‖P x‖ := real_inner_le_norm _ _
      _ ≤ ‖(x : E n)‖ * (‖P‖ * ‖(x : E n)‖) := by gcongr; exact P.le_opNorm _
      _ = ‖P‖ := by rw [hx]; ring
  have hee : ⟪‖b‖⁻¹ • b, P (‖b‖⁻¹ • b)⟫ = ‖b‖⁻¹ ^ 2 * ⟪b, P b⟫ := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  rw [hee] at hle
  have : ‖b‖ ^ 2 * (‖b‖⁻¹ ^ 2 * ⟪b, P b⟫) = ⟪b, P b⟫ := by field_simp
  calc ⟪b, P b⟫ = ‖b‖ ^ 2 * (‖b‖⁻¹ ^ 2 * ⟪b, P b⟫) := this.symm
    _ ≤ ‖b‖ ^ 2 * lamMax P := by gcongr
    _ = lamMax P * ‖b‖ ^ 2 := by ring

open SubspaceProxGrad.RPSD in
theorem rpsd_lammin_le_one {n : ℕ} (P : E n →L[ℝ] E n) (hnn : ∀ x : E n, 0 ≤ ⟪x, P x⟫)
    (hle : ∀ x : E n, ⟪x, P x⟫ ≤ ‖x‖ ^ 2) : lamMin P ≤ 1 := by
  rcases isEmpty_or_nonempty (Metric.sphere (0 : E n) 1) with h | h
  · unfold lamMin; rw [Real.iInf_of_isEmpty]; norm_num
  · obtain ⟨e⟩ := h
    unfold lamMin
    have he : ‖(e : E n)‖ = 1 := by simpa using e.2
    calc (⨅ x : Metric.sphere (0 : E n) 1, ⟪(x : E n), P x⟫) ≤ ⟪(e : E n), P e⟫ :=
          ciInf_le (f := fun x : Metric.sphere (0 : E n) 1 => ⟪(x : E n), P x⟫)
            ⟨0, by rintro _ ⟨x, rfl⟩; exact hnn x⟩ e
      _ ≤ ‖(e : E n)‖ ^ 2 := hle e
      _ = 1 := by rw [he]; norm_num

open SubspaceProxGrad.RPSD in
theorem rpsd_lammin_pos {n : ℕ} (hn : 0 < n) (P Q Qinv : E n →L[ℝ] E n)
    (h2 : ∀ u, Q (Qinv u) = u) (hq : ∀ b, ⟪b, P b⟫ = ‖Qinv b‖ ^ 2) : 0 < lamMin P := by
  have hkey : ∀ x : E n, ‖x‖ ≤ ‖Q‖ * ‖Qinv x‖ := by
    intro x
    calc ‖x‖ = ‖Q (Qinv x)‖ := by rw [h2]
      _ ≤ ‖Q‖ * ‖Qinv x‖ := Q.le_opNorm _
  set e : E n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hQpos : 0 < ‖Q‖ := by
    have := hkey e
    rw [he] at this
    rcases (norm_nonneg Q).eq_or_lt with h | h
    · rw [← h] at this; simp at this; linarith
    · exact h
  have hne : Nonempty (Metric.sphere (0 : E n) 1) := ⟨⟨e, by simpa using he⟩⟩
  have hb : 1 / ‖Q‖ ^ 2 ≤ lamMin P := by
    unfold lamMin
    apply le_ciInf
    intro x
    have hx : ‖(x : E n)‖ = 1 := by simpa using x.2
    have h1 := hkey x
    rw [hx] at h1
    rw [hq, div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ ‖Qinv x‖ := norm_nonneg _
    nlinarith
  exact lt_of_lt_of_le (by positivity) hb

theorem rpsd_proj_sq {n : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖S.starProjection v‖ ^ 2 = ⟪v, S.starProjection v⟫ := by
  have h := Submodule.starProjection_inner_eq_zero (K := S) v (S.starProjection v)
    (S.starProjection_apply_mem v)
  rw [inner_sub_left, sub_eq_zero] at h
  rw [← real_inner_self_eq_norm_sq, ← h]

theorem rpsd_step_id {n : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (a b : EuclideanSpace ℝ (Fin n)) :
    ‖S.starProjection a + (b - S.starProjection b)‖ ^ 2 =
      ⟪a, S.starProjection a⟫ + ‖b‖ ^ 2 - ⟪b, S.starProjection b⟫ := by
  have h0 : ⟪S.starProjection a, b - S.starProjection b⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero (K := S) b _ (S.starProjection_apply_mem a)
  rw [norm_add_sq_real, h0, rpsd_proj_sq, norm_sub_sq_real, rpsd_proj_sq]
  ring

open SubspaceProxGrad.RPSD in
theorem rpsd_expect {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr]
    (S : Ω → Submodule ℝ (E n)) (hS : ∀ x, Measurable fun ω => (S ω).starProjection x)
    (P : E n →L[ℝ] E n) (hP : IsAvgProj pr S P) (a b : E n) :
    ∫⁻ ω, ENNReal.ofReal (‖(S ω).starProjection a + (b - (S ω).starProjection b)‖ ^ 2) ∂pr
      = ENNReal.ofReal (⟪a, P a⟫ + ‖b‖ ^ 2 - ⟪b, P b⟫) := by
  have hint : ∀ x, Integrable (fun ω => (S ω).starProjection x) pr := fun x =>
    Integrable.of_bound (hS x).aestronglyMeasurable ‖x‖
      (Filter.Eventually.of_forall fun ω => Submodule.norm_starProjection_apply_le (K := S ω) x)
  have hin : ∀ x, ∫ ω, ⟪x, (S ω).starProjection x⟫ ∂pr = ⟪x, P x⟫ := by
    intro x; rw [hP x, integral_inner (hint x)]
  have hfi : ∀ x, Integrable (fun ω => ⟪x, (S ω).starProjection x⟫) pr :=
    fun x => (hint x).const_inner x
  simp_rw [rpsd_step_id]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    have e1 : ∫ ω, (⟪a, (S ω).starProjection a⟫ + ‖b‖ ^ 2 - ⟪b, (S ω).starProjection b⟫) ∂pr
        = (∫ ω, (⟪a, (S ω).starProjection a⟫ + ‖b‖ ^ 2) ∂pr)
          - ∫ ω, ⟪b, (S ω).starProjection b⟫ ∂pr :=
      integral_sub ((hfi a).add (integrable_const _)) (hfi b)
    have e2 : ∫ ω, (⟪a, (S ω).starProjection a⟫ + ‖b‖ ^ 2) ∂pr
        = (∫ ω, ⟪a, (S ω).starProjection a⟫ ∂pr) + ∫ ω, ‖b‖ ^ 2 ∂pr :=
      integral_add (hfi a) (integrable_const _)
    rw [e1, e2, hin, hin]
    simp
  · exact ((hfi a).add (integrable_const _)).sub (hfi b)
  · exact Filter.Eventually.of_forall fun ω => by
      simp only [Pi.zero_apply]
      rw [← rpsd_step_id]; positivity

theorem rpsd_run_meas {Ω Θ V : Type*} [MeasurableSpace Ω] [mΘ : MeasurableSpace Θ]
    [MeasurableSpace V]
    (ξ : ℕ → Ω → Θ) (T : V × Θ → V) (hT : Measurable T) (z : ℕ → Ω → V) (z0 : V)
    (h0 : ∀ ω, z 0 ω = z0) (hs : ∀ k ω, z (k + 1) ω = T (z k ω, ξ k ω)) (k : ℕ) :
    Measurable[⨆ j ∈ Set.Iio k, MeasurableSpace.comap (ξ j) mΘ] (z k) := by
  induction k with
  | zero =>
    have : z 0 = fun _ => z0 := funext h0
    rw [this]; exact measurable_const
  | succ k ih =>
    have hle : (⨆ j ∈ Set.Iio k, MeasurableSpace.comap (ξ j) mΘ)
        ≤ ⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (ξ j) mΘ :=
      biSup_mono (fun j (hj : j < k) => (lt_trans hj (Nat.lt_succ_self k) : j < k + 1))
    have h2 : Measurable[⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (ξ j) mΘ] (ξ k) := by
      have : MeasurableSpace.comap (ξ k) mΘ
          ≤ ⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (ξ j) mΘ :=
        le_iSup₂ (f := fun j (_ : j ∈ Set.Iio (k + 1)) => MeasurableSpace.comap (ξ j) mΘ) k
          (Nat.lt_succ_self k)
      exact (comap_measurable _).mono this le_rfl
    have : z (k + 1) = fun ω => T (z k ω, ξ k ω) := funext (hs k)
    rw [this]
    exact hT.comp ((ih.mono hle le_rfl).prodMk h2)

theorem rpsd_step_lintegral {Ω Θ V : Type*} [mΩ : MeasurableSpace Ω] [mΘ : MeasurableSpace Θ]
    [MeasurableSpace V]
    (pr : Measure Ω) [IsProbabilityMeasure pr]
    (ξ : ℕ → Ω → Θ) (hξ : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ pr)
    (hid : ∀ k, IdentDistrib (ξ k) (ξ 0) pr pr)
    (Z : Ω → V) (k : ℕ) (hZ : Measurable[⨆ j ∈ Set.Iio k, MeasurableSpace.comap (ξ j) mΘ] Z)
    (H : V × Θ → ENNReal) (hH : Measurable H) :
    ∫⁻ ω, H (Z ω, ξ k ω) ∂pr = ∫⁻ ω, ∫⁻ ω', H (Z ω, ξ 0 ω') ∂pr ∂pr := by
  have hle : (⨆ j ∈ Set.Iio k, MeasurableSpace.comap (ξ j) mΘ) ≤ mΩ :=
    iSup₂_le (fun j _ => (hξ j).comap_le)
  have hZm : Measurable Z := hZ.mono hle le_rfl
  have hI : IndepFun Z (ξ k) pr := by
    rw [IndepFun_iff_Indep]
    have hi : iIndep (fun j => MeasurableSpace.comap (ξ j) mΘ) pr :=
      (iIndepFun_iff_iIndep (fun _ => mΘ) ξ pr).1 hind
    have h2 := indep_iSup_of_disjoint (fun j => (hξ j).comap_le) hi
      (S := Set.Iio k) (T := {k}) (by simp)
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h2 hZ.comap_le) ?_
    exact le_iSup₂ (f := fun j (_ : j ∈ ({k} : Set ℕ)) => MeasurableSpace.comap (ξ j) mΘ) k rfl
  have hmap : pr.map (fun ω => (Z ω, ξ k ω)) = (pr.map Z).prod (pr.map (ξ 0)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZm.aemeasurable (hξ k).aemeasurable).1 hI,
      (hid k).map_eq]
  calc ∫⁻ ω, H (Z ω, ξ k ω) ∂pr = ∫⁻ q, H q ∂(pr.map (fun ω => (Z ω, ξ k ω))) :=
        (lintegral_map hH (hZm.prodMk (hξ k))).symm
    _ = ∫⁻ q, H q ∂((pr.map Z).prod (pr.map (ξ 0))) := by rw [hmap]
    _ = ∫⁻ v, ∫⁻ θ, H (v, θ) ∂(pr.map (ξ 0)) ∂(pr.map Z) := lintegral_prod _ hH.aemeasurable
    _ = ∫⁻ ω, ∫⁻ θ, H (Z ω, θ) ∂(pr.map (ξ 0)) ∂pr := lintegral_map hH.lintegral_prod_right' hZm
    _ = ∫⁻ ω, ∫⁻ ω', H (Z ω, ξ 0 ω') ∂pr ∂pr := by
        congr 1; funext ω
        exact lintegral_map (hH.comp (measurable_const.prodMk measurable_id)) (hξ 0)

set_option maxHeartbeats 1000000 in
open SubspaceProxGrad.RPSD MeasureTheory ProbabilityTheory in
theorem solution {n : ℕ} {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (pr : Measure Ω) [IsProbabilityMeasure pr]
    (sel : Θ → Submodule ℝ (E n)) (hsel : ∀ x : E n, Measurable fun θ => (sel θ).starProjection x)
    (ξ : ℕ → Ω → Θ) (hξ : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ pr)
    (hid : ∀ k, IdentDistrib (ξ k) (ξ 0) pr pr)
    (hadm : IsAdmissible pr (fun ω => sel (ξ 0 ω)))
    (P : E n →L[ℝ] E n) (hP : IsAvgProj pr (fun ω => sel (ξ 0 ω)) P)
    (Q Qinv : E n →L[ℝ] E n) (hQ : Q.IsPositive)
    (hQPQ : Q ∘L P ∘L Q = ContinuousLinearMap.id ℝ (E n))
    (hQi : Q ∘L Qinv = ContinuousLinearMap.id ℝ (E n))
    (hQi' : Qinv ∘L Q = ContinuousLinearMap.id ℝ (E n))
    (f : E n → ℝ) (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L) (hfd : Differentiable ℝ f)
    (hfs : StrongConvexOn Set.univ μ f)
    (hfL : ∀ x y : E n, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (C : Set (E n)) (g : E n → ℝ) (hC : C.Nonempty) (hg : ConvexOn ℝ C g)
    (hgl : IsClosed {p : E n × ℝ | p.1 ∈ C ∧ g p.1 ≤ p.2})
    (xs : E n) (hxs : IsMinimizer C f g xs)
    (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 2 / (μ + L))
    (z0 : E n) (z x : ℕ → Ω → E n) (hrun : IsRPSDRun sel ξ C f g γ Q Qinv z0 z x) :
    (∀ k : ℕ, ∫ ω, ‖x (k + 1) ω - xs‖ ^ 2 ∂pr ≤
      (1 - lamMin P * (2 * γ * μ * L / (μ + L))) ^ k *
        (lamMax P * ‖z0 - Q (xs - γ • gradient f xs)‖ ^ 2)) ∧
    (∀ᵐ ω ∂pr, Filter.Tendsto (fun k => x k ω) Filter.atTop (nhds xs)) := by
  classical
  obtain ⟨h1, h2, hqP, hqPQ⟩ := rpsd_la P Q Qinv hQ hQPQ hQi hQi'
  have hnn : ∀ v : E n, 0 ≤ ⟪v, P v⟫ := fun v => by rw [hqP]; positivity
  have hSm : ∀ v, Measurable fun ω => (sel (ξ 0 ω)).starProjection v :=
    fun v => (hsel v).comp (hξ 0)
  have hPle : ∀ v : E n, ⟪v, P v⟫ ≤ ‖v‖ ^ 2 := by
    intro v
    have h := rpsd_expect pr (fun ω => sel (ξ 0 ω)) hSm P hP v 0
    simp only [map_zero, sub_self, add_zero, norm_zero, inner_zero_left, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    have hb : ∫⁻ ω, ENNReal.ofReal (‖(sel (ξ 0 ω)).starProjection v‖ ^ 2) ∂pr
        ≤ ENNReal.ofReal (‖v‖ ^ 2) := by
      calc _ ≤ ∫⁻ ω, ENNReal.ofReal (‖v‖ ^ 2) ∂pr :=
            lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
              (Submodule.norm_starProjection_apply_le (K := sel (ξ 0 ω)) v) 2)
        _ = _ := by simp
    rw [h] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb
  have hm : 0 < μ + L := by linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 2 * γ * μ * L / (μ + L) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one hm]
    have hγ' : γ * (μ + L) ≤ 2 := by rwa [le_div_iff₀ hm] at hγ1
    have hA : (μ + L) * (2 * γ * μ * L) ≤ (μ + L) * (μ + L) := by
      nlinarith [mul_le_mul_of_nonneg_left hγ' (by positivity : (0:ℝ) ≤ 2 * μ * L),
        sq_nonneg (μ - L)]
    exact le_of_mul_le_mul_left hA hm
  have hl0 : 0 ≤ lamMin P := by unfold lamMin; exact Real.iInf_nonneg fun v => hnn v
  have hl1 := rpsd_lammin_le_one P hnn hPle
  have hL0 : 0 ≤ lamMax P := by unfold lamMax; exact Real.iSup_nonneg fun v => hnn v
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 - lamMin P * ρ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; nlinarith
  rw [← hρ, ← hr]
  -- analysis of f
  have hgrad : ∀ v, HasGradientAt f (gradient f v) v := fun v => (hfd v).hasGradientAt
  have hup := rpsd_descent hgrad hfL
  have hlo := rpsd_lower_sc hgrad hfs
  have hconv : ∀ a b, f a + ⟪gradient f a, b - a⟫ ≤ f b := fun a b => by
    have := hlo a b
    have : 0 ≤ μ / 2 * ‖b - a‖ ^ 2 := by positivity
    linarith
  have hcontr := rpsd_grad_contract hμ hL hγ0 hγ1 hup hlo
  rw [← hρ] at hcontr
  have hvis := rpsd_vi_min hg hconv hfL hγ0 hxs
  obtain ⟨us, hus⟩ : ∃ us : E n, us = xs - γ • gradient f xs := ⟨_, rfl⟩
  rw [← hus] at hvis ⊢
  obtain ⟨zs, hzs⟩ : ∃ zs : E n, zs = Q us := ⟨_, rfl⟩
  rw [← hzs]
  have hQinvzs : Qinv zs = us := by rw [hzs, h1]
  obtain ⟨p, hpc, hp⟩ := rpsd_prox_sel hg hγ0
  have hxp : ∀ k ω, x (k + 1) ω = p (Qinv (z k ω)) := fun k ω =>
    (hp _ _ ((hrun ω).2 k).1).symm
  -- deterministic one-step bounds
  have hdet : ∀ k ω,
      ⟪Q (x (k + 1) ω - γ • gradient f (x (k + 1) ω)) - zs,
        P (Q (x (k + 1) ω - γ • gradient f (x (k + 1) ω)) - zs)⟫
        + ‖z k ω - zs‖ ^ 2 - ⟪z k ω - zs, P (z k ω - zs)⟫ ≤ r * ‖z k ω - zs‖ ^ 2 ∧
      ‖x (k + 1) ω - xs‖ ^ 2 ≤ lamMax P * ‖z k ω - zs‖ ^ 2 := by
    intro k ω
    have hprox := ((hrun ω).2 k).1
    have hne : ‖x (k + 1) ω - xs‖ ≤ ‖Qinv (z k ω) - us‖ :=
      rpsd_nonexp hprox.1 hxs.1 (rpsd_prox_vi hg hγ0 hprox) hvis
    have hb : ‖Qinv (z k ω) - us‖ ^ 2 = ⟪z k ω - zs, P (z k ω - zs)⟫ := by
      rw [hqP, map_sub, hQinvzs]
    have hne2 : ‖x (k + 1) ω - xs‖ ^ 2 ≤ ⟪z k ω - zs, P (z k ω - zs)⟫ := by
      rw [← hb]; exact pow_le_pow_left₀ (norm_nonneg _) hne 2
    have ha : ⟪Q (x (k + 1) ω - γ • gradient f (x (k + 1) ω)) - zs,
        P (Q (x (k + 1) ω - γ • gradient f (x (k + 1) ω)) - zs)⟫
        = ‖(x (k + 1) ω - γ • gradient f (x (k + 1) ω)) - us‖ ^ 2 := by
      rw [hzs, ← map_sub]; exact hqPQ _
    have hc := hcontr (x (k + 1) ω) xs
    rw [← hus] at hc
    have hlo2 := rpsd_ray_lo P hnn (z k ω - zs)
    have hhi := rpsd_ray_hi P (z k ω - zs)
    constructor
    · rw [ha]
      have h1ρ : 0 ≤ 1 - ρ := by linarith
      have h5 := mul_le_mul_of_nonneg_left hne2 h1ρ
      have h6 := mul_le_mul_of_nonneg_left hlo2 hρ0
      rw [hr]
      nlinarith
    · exact hne2.trans hhi
  -- measurability
  have hGc : Continuous (gradient f) :=
    (LipschitzWith.of_dist_le_mul (K := Real.toNNReal L) fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]; exact hfL a b).continuous
  have hY : Continuous (fun w : E n => Q (p (Qinv w) - γ • gradient f (p (Qinv w)))) :=
    Q.continuous.comp ((hpc.comp Qinv.continuous).sub
      ((hGc.comp (hpc.comp Qinv.continuous)).const_smul γ))
  have hPj : Measurable (fun q : E n × Θ => (sel q.2).starProjection q.1) :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fun (w : E n) (θ : Θ) => (sel θ).starProjection w)
      (fun θ => (sel θ).starProjection.continuous) hsel
  let T : E n × Θ → E n := fun q =>
    (sel q.2).starProjection (Q (p (Qinv q.1) - γ • gradient f (p (Qinv q.1))))
      + (q.1 - (sel q.2).starProjection q.1)
  have hT : Measurable T :=
    (hPj.comp ((hY.measurable.comp measurable_fst).prodMk measurable_snd)).add
      (measurable_fst.sub hPj)
  have hzT : ∀ k ω, z (k + 1) ω = T (z k ω, ξ k ω) := fun k ω => by
    have := ((hrun ω).2 k).2
    rw [hxp k ω] at this
    exact this
  have hzm := rpsd_run_meas ξ T hT z z0 (fun ω => (hrun ω).1) hzT
  have hzm' : ∀ k, Measurable (z k) := fun k =>
    (hzm k).mono (iSup₂_le (fun j _ => (hξ j).comap_le)) le_rfl
  -- the expectation recursion
  have hstep : ∀ k, ∫⁻ ω, ENNReal.ofReal (‖z (k + 1) ω - zs‖ ^ 2) ∂pr ≤
      ENNReal.ofReal r * ∫⁻ ω, ENNReal.ofReal (‖z k ω - zs‖ ^ 2) ∂pr := by
    intro k
    let H : E n × Θ → ENNReal := fun q => ENNReal.ofReal (‖T q - zs‖ ^ 2)
    have hH : Measurable H :=
      ENNReal.measurable_ofReal.comp (((hT.sub_const zs).norm).pow_const 2)
    calc ∫⁻ ω, ENNReal.ofReal (‖z (k + 1) ω - zs‖ ^ 2) ∂pr
        = ∫⁻ ω, H (z k ω, ξ k ω) ∂pr := by
          refine lintegral_congr fun ω => ?_
          simp only [H]; rw [hzT]
      _ = ∫⁻ ω, ∫⁻ ω', H (z k ω, ξ 0 ω') ∂pr ∂pr :=
          rpsd_step_lintegral pr ξ hξ hind hid (z k) k (hzm k) H hH
      _ ≤ ∫⁻ ω, ENNReal.ofReal r * ENNReal.ofReal (‖z k ω - zs‖ ^ 2) ∂pr := by
          refine lintegral_mono fun ω => ?_
          have eT : ∀ θ, T (z k ω, θ) - zs =
              (sel θ).starProjection (Q (x (k + 1) ω - γ • gradient f (x (k + 1) ω)) - zs)
                + ((z k ω - zs) - (sel θ).starProjection (z k ω - zs)) := by
            intro θ
            simp only [T, map_sub, hxp k ω]
            abel
          have : (fun ω' => H (z k ω, ξ 0 ω')) = fun ω' => ENNReal.ofReal
              (‖(sel (ξ 0 ω')).starProjection
                  (Q (x (k + 1) ω - γ • gradient f (x (k + 1) ω)) - zs)
                + ((z k ω - zs) - (sel (ξ 0 ω')).starProjection (z k ω - zs))‖ ^ 2) := by
            funext ω'; simp only [H]; rw [eT]
          rw [this, rpsd_expect pr (fun ω => sel (ξ 0 ω)) hSm P hP, ← ENNReal.ofReal_mul hr0]
          exact ENNReal.ofReal_le_ofReal (hdet k ω).1
      _ = ENNReal.ofReal r * ∫⁻ ω, ENNReal.ofReal (‖z k ω - zs‖ ^ 2) ∂pr :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            (((hzm' k).sub_const zs).norm.pow_const 2))
  have he0 : ∫⁻ ω, ENNReal.ofReal (‖z 0 ω - zs‖ ^ 2) ∂pr = ENNReal.ofReal (‖z0 - zs‖ ^ 2) := by
    rw [lintegral_congr fun ω => by rw [(hrun ω).1]]
    simp
  have hek : ∀ k, ∫⁻ ω, ENNReal.ofReal (‖z k ω - zs‖ ^ 2) ∂pr ≤
      ENNReal.ofReal r ^ k * ENNReal.ofReal (‖z0 - zs‖ ^ 2) := by
    intro k
    induction k with
    | zero => rw [he0]; simp
    | succ k ih =>
      calc _ ≤ ENNReal.ofReal r * ∫⁻ ω, ENNReal.ofReal (‖z k ω - zs‖ ^ 2) ∂pr := hstep k
        _ ≤ ENNReal.ofReal r * (ENNReal.ofReal r ^ k * ENNReal.ofReal (‖z0 - zs‖ ^ 2)) := by
            gcongr
        _ = _ := by ring
  have hX : ∀ k, ∫⁻ ω, ENNReal.ofReal (‖x (k + 1) ω - xs‖ ^ 2) ∂pr ≤
      ENNReal.ofReal (r ^ k * (lamMax P * ‖z0 - zs‖ ^ 2)) := by
    intro k
    calc ∫⁻ ω, ENNReal.ofReal (‖x (k + 1) ω - xs‖ ^ 2) ∂pr
        ≤ ∫⁻ ω, ENNReal.ofReal (lamMax P) * ENNReal.ofReal (‖z k ω - zs‖ ^ 2) ∂pr := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul hL0]
          exact ENNReal.ofReal_le_ofReal (hdet k ω).2
      _ = ENNReal.ofReal (lamMax P) * ∫⁻ ω, ENNReal.ofReal (‖z k ω - zs‖ ^ 2) ∂pr :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            (((hzm' k).sub_const zs).norm.pow_const 2))
      _ ≤ ENNReal.ofReal (lamMax P) * (ENNReal.ofReal r ^ k * ENNReal.ofReal (‖z0 - zs‖ ^ 2)) := by
          gcongr; exact hek k
      _ = ENNReal.ofReal (r ^ k * (lamMax P * ‖z0 - zs‖ ^ 2)) := by
          rw [ENNReal.ofReal_mul (pow_nonneg hr0 k), ENNReal.ofReal_pow hr0,
            ENNReal.ofReal_mul hL0]
          ring
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hint : Integrable (fun ω => ‖x (k + 1) ω - xs‖ ^ 2) pr
    · have heq := ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun ω => by positivity)
      rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), heq]
      exact hX k
    · rw [integral_undef hint]; positivity
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : ∀ v : E 0, v = 0 := fun v => by
        rw [← norm_eq_zero, EuclideanSpace.norm_eq]; simp
      filter_upwards with ω
      rw [show (fun k => x k ω) = fun _ => xs from funext fun k => by rw [h0 (x k ω), h0 xs]]
      exact tendsto_const_nhds
    · have hlpos := rpsd_lammin_pos hn P Q Qinv h2 hqP
      have hρpos : 0 < ρ := by rw [hρ]; positivity
      have hr1 : r < 1 := by rw [hr]; nlinarith [mul_pos hlpos hρpos]
      have hUm : ∀ k, Measurable (fun ω => ENNReal.ofReal (‖x (k + 1) ω - xs‖ ^ 2)) := by
        intro k
        have : (fun ω => ENNReal.ofReal (‖x (k + 1) ω - xs‖ ^ 2)) =
            fun ω => ENNReal.ofReal (‖p (Qinv (z k ω)) - xs‖ ^ 2) := by
          funext ω; rw [hxp]
        rw [this]
        exact ENNReal.measurable_ofReal.comp
          ((((hpc.comp Qinv.continuous).measurable.comp (hzm' k)).sub_const xs).norm.pow_const 2)
      have hsum : ∫⁻ ω, ∑' k, ENNReal.ofReal (‖x (k + 1) ω - xs‖ ^ 2) ∂pr ≠ ⊤ := by
        rw [lintegral_tsum (fun k => (hUm k).aemeasurable)]
        have hb : ∀ k, ∫⁻ ω, ENNReal.ofReal (‖x (k + 1) ω - xs‖ ^ 2) ∂pr ≤
            ENNReal.ofReal (lamMax P * ‖z0 - zs‖ ^ 2) * ENNReal.ofReal r ^ k := by
          intro k
          refine (hX k).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (pow_nonneg hr0 k), ENNReal.ofReal_pow hr0]
          ring
        refine ne_of_lt ((ENNReal.tsum_le_tsum hb).trans_lt ?_)
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [ENNReal.inv_lt_top]
        exact tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hr1)
      have hae := ae_lt_top (Measurable.ennreal_tsum hUm) hsum
      filter_upwards [hae] with ω hω
      have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
      have h3 : Filter.Tendsto (fun k => ‖x (k + 1) ω - xs‖ ^ 2) Filter.atTop (nhds 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
        simp only [ENNReal.toReal_zero] at this
        refine this.congr (fun k => ?_)
        simp only [Function.comp]
        exact ENNReal.toReal_ofReal (by positivity)
      have h4 : Filter.Tendsto (fun k => ‖x (k + 1) ω - xs‖) Filter.atTop (nhds 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp h3
        rw [Real.sqrt_zero] at this
        refine this.congr (fun k => ?_)
        simp only [Function.comp]
        exact Real.sqrt_sq (norm_nonneg _)
      have h5 : Filter.Tendsto (fun k => x (k + 1) ω) Filter.atTop (nhds xs) :=
        tendsto_iff_norm_sub_tendsto_zero.2 h4
      exact (Filter.tendsto_add_atTop_iff_nat 1).1 h5
