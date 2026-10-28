-- Prove2me | solution 1 for PenaltyLag.Asymptotic.eq_4_11_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:46:23.883075+00:00
-- url     : https://prove2.me/submissions/05a25e55-3f16-41c8-9790-58b79c94be5d

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace Aux_PLA411
open PenaltyLag.Asymptotic

lemma hasDerivAt_thsq (t : ℝ) : HasDerivAt (fun s => theta s ^ 2) (2 * theta t) t := by
  rcases lt_trichotomy t 0 with h | h | h
  · have ht : theta t = 0 := max_eq_left h.le
    rw [ht, mul_zero]
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [theta, max_eq_left (Set.mem_Iio.1 hs).le]
  · subst h
    have ht : theta 0 = 0 := by simp [theta]
    rw [ht, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, ht, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      smul_zero]
    refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_id (n := 2)
      (by norm_num))
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall (fun s => ?_))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _), one_mul]
    unfold theta
    rcases le_total s 0 with hs | hs
    · rw [max_eq_left hs]; nlinarith [sq_nonneg s]
    · rw [max_eq_right hs]
  · have ht : theta t = t := max_eq_right h.le
    rw [ht]
    have := hasDerivAt_pow 2 t
    apply (this.congr_deriv (by norm_num)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp [theta, max_eq_right (Set.mem_Ioi.1 hs).le]

lemma coord_val (y f r : ℝ) (hr : 0 < r) :
    1 / (4 * r) * (2 * theta (y + 2 * r * f) - 2 * y) = max (-y / (2 * r)) f := by
  unfold theta
  rcases le_total (y + 2 * r * f) 0 with h | h
  · rw [max_eq_left h]
    have : f ≤ -y / (2 * r) := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [max_eq_left this]
    field_simp
    ring
  · rw [max_eq_right h]
    have : -y / (2 * r) ≤ f := by rw [div_le_iff₀ (by positivity)]; linarith
    rw [max_eq_right this]
    field_simp
    ring

lemma coord_min (y f r v : ℝ) (hr : 0 < r) (hv : f ≤ v) :
    r * (v - max (-y / (2 * r)) f) ^ 2 ≤
      (v * y + r * v ^ 2) - (max (-y / (2 * r)) f * y + r * (max (-y / (2 * r)) f) ^ 2) := by
  set u := max (-y / (2 * r)) f with hu
  have key : (v * y + r * v ^ 2) - (u * y + r * u ^ 2) - r * (v - u) ^ 2 =
      (v - u) * (y + 2 * r * u) := by ring
  have : 0 ≤ (v - u) * (y + 2 * r * u) := by
    rcases le_total f (-y / (2 * r)) with h | h
    · have hu' : u = -y / (2 * r) := max_eq_left h
      have : y + 2 * r * u = 0 := by rw [hu']; field_simp; ring
      rw [this, mul_zero]
    · have hu' : u = f := max_eq_right h
      have h2 : 0 ≤ y + 2 * r * f := by
        rw [div_le_iff₀ (by positivity)] at h; linarith
      rw [hu']
      exact mul_nonneg (by linarith) h2
  linarith

lemma coord_val2 (y f r : ℝ) (hr : 0 < r) :
    max (-y / (2 * r)) f * y + r * (max (-y / (2 * r)) f) ^ 2 =
      1 / (4 * r) * (theta (y + 2 * r * f) ^ 2 - y ^ 2) := by
  unfold theta
  rcases le_total (y + 2 * r * f) 0 with h | h
  · rw [max_eq_left h]
    have : f ≤ -y / (2 * r) := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [max_eq_left this]
    field_simp
    ring
  · rw [max_eq_right h]
    have : -y / (2 * r) ≤ f := by rw [div_le_iff₀ (by positivity)]; linarith
    rw [max_eq_right this]
    field_simp
    ring

lemma grad_coord {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (hr : 0 < r)
    (x : E) (y : Mult m) (i : Fin m) :
    (gradient (fun y' : Mult m => Lr f₀ f r x y') y) i = max (-(y i) / (2 * r)) (f i x) := by
  set ψ' : Fin m → ℝ := fun j => 2 * theta (y j + 2 * r * f j x) - 2 * y j with hψ'
  have hψ : ∀ j, HasDerivAt (fun t : ℝ => theta (t + 2 * r * f j x) ^ 2 - t ^ 2) (ψ' j) (y j) := by
    intro j
    have h1 := (hasDerivAt_thsq (y j + 2 * r * f j x)).comp (y j)
      ((hasDerivAt_id (y j)).add_const (2 * r * f j x))
    have h2 := h1.sub (hasDerivAt_pow 2 (y j))
    refine h2.congr_deriv ?_
    simp [hψ']
  set L : Mult m →L[ℝ] ℝ := (1 / (4 * r)) • ∑ j, ψ' j • (EuclideanSpace.proj j : StrongDual ℝ (Mult m)) with hL
  have hF : HasFDerivAt (fun y' : Mult m => Lr f₀ f r x y') L y := by
    have hj : ∀ j ∈ Finset.univ, HasFDerivAt
        (fun y' : Mult m => theta (y' j + 2 * r * f j x) ^ 2 - y' j ^ 2)
        (ψ' j • (EuclideanSpace.proj j : StrongDual ℝ (Mult m))) y := by
      intro j _
      exact (hψ j).comp_hasFDerivAt y (EuclideanSpace.proj j : StrongDual ℝ (Mult m)).hasFDerivAt
    have := ((HasFDerivAt.fun_sum hj).const_mul (1 / (4 * r))).const_add (f₀ x)
    exact this
  have hg : gradient (fun y' : Mult m => Lr f₀ f r x y') y = (InnerProductSpace.toDual ℝ _).symm L := by
    rw [gradient, hF.fderiv]
  have hcomp : (gradient (fun y' : Mult m => Lr f₀ f r x y') y) i =
      inner ℝ (gradient (fun y' : Mult m => Lr f₀ f r x y') y) (EuclideanSpace.single i (1 : ℝ)) := by
    rw [EuclideanSpace.inner_single_right]; simp
  rw [hcomp, hg, InnerProductSpace.toDual_symm_apply, hL]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    EuclideanSpace.coe_proj, smul_eq_mul, PiLp.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hψ']
  exact coord_val (y i) (f i x) r hr

lemma inner_norm {m : ℕ} (v y : Mult m) (r : ℝ) :
    inner ℝ v y + r * ‖v‖ ^ 2 = ∑ i, (v i * y i + r * v i ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  simp [PiLp.inner_apply, mul_comm]

end Aux_PLA411

open PenaltyLag.Asymptotic Aux_PLA411 in
theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (x : E) (hx : x ∈ X) (y : Mult m) :
    (∀ v : Mult m,
      Fr f₀ f 0 x (gradient (fun y' : Mult m => Lr f₀ f r x y') y)
          + ((inner ℝ (gradient (fun y' : Mult m => Lr f₀ f r x y') y) y
              + r * ‖gradient (fun y' : Mult m => Lr f₀ f r x y') y‖ ^ 2 : ℝ) : EReal)
        ≤ Fr f₀ f 0 x v + ((inner ℝ v y + r * ‖v‖ ^ 2 : ℝ) : EReal)) ∧
    Fr f₀ f 0 x (gradient (fun y' : Mult m => Lr f₀ f r x y') y)
          + ((inner ℝ (gradient (fun y' : Mult m => Lr f₀ f r x y') y) y
              + r * ‖gradient (fun y' : Mult m => Lr f₀ f r x y') y‖ ^ 2 : ℝ) : EReal)
        = (Lr f₀ f r x y : EReal) ∧
    ∀ u : Mult m,
      (∀ v : Mult m, Fr f₀ f 0 x u + ((inner ℝ u y + r * ‖u‖ ^ 2 : ℝ) : EReal)
          ≤ Fr f₀ f 0 x v + ((inner ℝ v y + r * ‖v‖ ^ 2 : ℝ) : EReal)) →
      u = gradient (fun y' : Mult m => Lr f₀ f r x y') y := by
  set g := gradient (fun y' : Mult m => Lr f₀ f r x y') y with hgdef
  have hgc : ∀ i, g i = max (-(y i) / (2 * r)) (f i x) := grad_coord f₀ f r hr x y
  have hgfeas : ∀ i, f i x ≤ g i := fun i => by rw [hgc]; exact le_max_right _ _
  have hFr : ∀ v : Mult m, (∀ i, f i x ≤ v i) → Fr f₀ f 0 x v = ((f₀ x : ℝ) : EReal) := by
    intro v hv; simp [Fr, hv]
  have hFr' : ∀ v : Mult m, ¬ (∀ i, f i x ≤ v i) → Fr f₀ f 0 x v = ⊤ := by
    intro v hv; simp only [Fr, if_neg hv]
  have hcmp : ∀ v : Mult m, (∀ i, f i x ≤ v i) →
      r * ∑ i, (v i - g i) ^ 2 ≤ (inner ℝ v y + r * ‖v‖ ^ 2) - (inner ℝ g y + r * ‖g‖ ^ 2) := by
    intro v hv
    rw [inner_norm, inner_norm, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hgc]
    exact coord_min (y i) (f i x) r (v i) hr (hv i)
  have hval : inner ℝ g y + r * ‖g‖ ^ 2 = Lr f₀ f r x y - f₀ x := by
    rw [inner_norm]
    simp only [Lr, add_sub_cancel_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hgc]
    exact coord_val2 (y i) (f i x) r hr
  have hmin : ∀ v : Mult m, Fr f₀ f 0 x g + ((inner ℝ g y + r * ‖g‖ ^ 2 : ℝ) : EReal)
      ≤ Fr f₀ f 0 x v + ((inner ℝ v y + r * ‖v‖ ^ 2 : ℝ) : EReal) := by
    intro v
    rw [hFr g hgfeas]
    by_cases hv : ∀ i, f i x ≤ v i
    · rw [hFr v hv, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have := hcmp v hv
      have h0 : 0 ≤ r * ∑ i, (v i - g i) ^ 2 :=
        mul_nonneg hr.le (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      linarith
    · rw [hFr' v hv, EReal.top_add_coe]
      exact le_top
  refine ⟨hmin, ?_, ?_⟩
  · rw [hFr g hgfeas, ← EReal.coe_add, hval]
    congr 1
    ring
  · intro u hu
    have h1 := hu g
    have hufeas : ∀ i, f i x ≤ u i := by
      by_contra hc
      rw [hFr' u hc, EReal.top_add_coe, hFr g hgfeas, ← EReal.coe_add] at h1
      exact absurd h1 (not_le.2 (EReal.coe_lt_top _))
    rw [hFr u hufeas, hFr g hgfeas, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    have h2 := hcmp u hufeas
    have hsum : ∑ i, (u i - g i) ^ 2 ≤ 0 := by
      have : r * ∑ i, (u i - g i) ^ 2 ≤ 0 := by linarith
      by_contra hc
      push Not at hc
      have := mul_pos hr hc
      linarith
    have hz : ∀ i ∈ Finset.univ, (u i - g i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1
        (le_antisymm hsum (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
    ext i
    have := hz i (Finset.mem_univ i)
    have : u i - g i = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linarith
