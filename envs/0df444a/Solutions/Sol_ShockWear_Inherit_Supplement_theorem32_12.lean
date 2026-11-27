-- Prove2me | solution 1 for ShockWear.Inherit.Supplement.theorem32_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:37.441385+00:00
-- url     : https://prove2.me/submissions/239bc64f-065e-4385-b88d-d4f5fa197309

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_ReversedAgeing

open ShockWear
open ShockWear.Inherit
open ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hnwue : ∀ k, ENNReal.ofReal (P k) * (∑' j, ENNReal.ofReal (P j)) ≤
      ∑' j, ENNReal.ofReal (P (j + k))) :
    IsNWUE (ShockWear.CumDamage.shockSurv lam P) := by
      have hpw_nn : ∀ u, 0 ≤ u → ∀ k, 0 ≤ ShockWear.CumDamage.poisW lam u k := by
        intro u hu k
        unfold ShockWear.CumDamage.poisW
        have : 0 ≤ lam * u := mul_nonneg hlam.le hu
        positivity
      have hP1 : ∀ k, P k ≤ 1 := fun k => (hanti (Nat.zero_le k)).trans hP0
      have hsum : ∀ u, Summable (fun k => ShockWear.CumDamage.poisW lam u k) := by
        intro u
        have := (Real.summable_pow_div_factorial (lam * u)).mul_left (Real.exp (-(lam * u)))
        refine this.congr (fun k => ?_)
        unfold ShockWear.CumDamage.poisW
        ring
      have hsurv : ∀ u, 0 ≤ u → ENNReal.ofReal (ShockWear.CumDamage.shockSurv lam P u) =
          ∑' k, ENNReal.ofReal (P k) * ENNReal.ofReal (ShockWear.CumDamage.poisW lam u k) := by
        intro u hu
        have hs : Summable (fun k => P k * ShockWear.CumDamage.poisW lam u k) := by
          refine (hsum u).of_nonneg_of_le (fun k => mul_nonneg (hnn k) (hpw_nn u hu k)) (fun k => ?_)
          have := hpw_nn u hu k
          nlinarith [hP1 k]
        unfold ShockWear.CumDamage.shockSurv
        rw [if_neg (not_lt.mpr hu), ENNReal.ofReal_tsum_of_nonneg
          (fun k => mul_nonneg (hnn k) (hpw_nn u hu k)) hs]
        congr 1
        funext k
        rw [ENNReal.ofReal_mul (hnn k)]
      have hderiv0 : ∀ x, HasDerivAt (fun u => ShockWear.CumDamage.poisW lam u 0)
          (-(lam * ShockWear.CumDamage.poisW lam x 0)) x := by
        intro x
        unfold ShockWear.CumDamage.poisW
        have h1 : HasDerivAt (fun u => -(lam * u)) (-(lam * 1)) x :=
          ((hasDerivAt_id x).const_mul lam).neg
        have h2 := h1.exp
        convert h2 using 1
        · funext u; simp
        · simp; ring
      have hderivS : ∀ k x, HasDerivAt (fun u => ShockWear.CumDamage.poisW lam u (k+1))
          (lam * ShockWear.CumDamage.poisW lam x k - lam * ShockWear.CumDamage.poisW lam x (k+1)) x := by
        intro k x
        unfold ShockWear.CumDamage.poisW
        have h1 : HasDerivAt (fun u => -(lam * u)) (-(lam * 1)) x :=
          ((hasDerivAt_id x).const_mul lam).neg
        have h2 := h1.exp
        have h3 : HasDerivAt (fun u => (lam * u) ^ (k+1)) (((k+1:ℕ):ℝ) * (lam * x) ^ k * (lam * 1)) x := by
          have := (hasDerivAt_pow (k+1) (lam*x)).comp x ((hasDerivAt_id x).const_mul lam)
          simpa [Function.comp_def] using this
        have h4 := (h2.mul h3).div_const (((k+1).factorial : ℕ) : ℝ)
        refine h4.congr_deriv ?_
        rw [Nat.factorial_succ]
        push_cast
        have hf : (k.factorial : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      have hQ : ∀ k x, HasDerivAt
          (fun u => ∑ j ∈ Finset.range (k+1), ShockWear.CumDamage.poisW lam u j)
          (-(lam * ShockWear.CumDamage.poisW lam x k)) x := by
        intro k
        induction k with
        | zero => intro x; simpa using hderiv0 x
        | succ k ih =>
          intro x
          have := (ih x).add (hderivS k x)
          have e : (fun u => ∑ j ∈ Finset.range (k+1+1), ShockWear.CumDamage.poisW lam u j) =
              (fun u => ∑ j ∈ Finset.range (k+1), ShockWear.CumDamage.poisW lam u j) +
              (fun u => ShockWear.CumDamage.poisW lam u (k+1)) := by
            funext u; rw [Pi.add_apply, Finset.sum_range_succ]
          rw [e]
          exact this.congr_deriv (by ring)
      have hlim : ∀ k, Filter.Tendsto
          (fun u => ∑ j ∈ Finset.range (k+1), ShockWear.CumDamage.poisW lam u j)
          Filter.atTop (nhds 0) := by
        intro k
        have : ∀ j, Filter.Tendsto (fun u => ShockWear.CumDamage.poisW lam u j)
            Filter.atTop (nhds 0) := by
          intro j
          have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
            (Filter.tendsto_id.const_mul_atTop hlam)).div_const ((j.factorial : ℕ) : ℝ)
          rw [zero_div] at h1
          refine h1.congr (fun u => ?_)
          simp only [Function.comp_def, id, ShockWear.CumDamage.poisW]
          ring
        simpa using tendsto_finsetSum (Finset.range (k+1)) (fun j _ => this j)
      have hint : ∀ k t, 0 ≤ t → ∫⁻ x in Set.Ioi 0,
          ENNReal.ofReal (ShockWear.CumDamage.poisW lam (x+t) k) =
          ENNReal.ofReal lam⁻¹ * ∑ j ∈ Finset.range (k+1),
            ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) := by
        intro k t ht
        set g : ℝ → ℝ := fun x => -(lam⁻¹ *
          ∑ j ∈ Finset.range (k+1), ShockWear.CumDamage.poisW lam (x+t) j) with hg
        have hd : ∀ x ∈ Set.Ici (0:ℝ), HasDerivAt g (ShockWear.CumDamage.poisW lam (x+t) k) x := by
          intro x _
          have := (((hQ k (x+t)).comp_add_const x t).const_mul lam⁻¹).neg
          refine this.congr_deriv ?_
          field_simp
        have hl : Filter.Tendsto g Filter.atTop (nhds 0) := by
          have := (((hlim k).comp (Filter.tendsto_atTop_add_const_right _ t Filter.tendsto_id)).const_mul
            lam⁻¹).neg
          simpa [Function.comp_def] using this
        have hnn' : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ ShockWear.CumDamage.poisW lam (x+t) k := by
          intro x hx
          exact hpw_nn _ (by have : (0:ℝ) < x := hx; linarith) k
        have hI := integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn' hl
        have hInt := integrableOn_Ioi_deriv_of_nonneg' hd hnn' hl
        rw [← ofReal_integral_eq_lintegral_ofReal hInt
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hnn')), hI]
        simp only [hg, zero_add, zero_sub, neg_neg]
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le),
          ENNReal.ofReal_sum_of_nonneg (fun j _ => hpw_nn t ht j)]
      have hres : ∀ t, 0 ≤ t → ShockWear.Inherit.resInt (ShockWear.CumDamage.shockSurv lam P) t =
          ∑' k, ENNReal.ofReal (P k) * (ENNReal.ofReal lam⁻¹ * ∑ j ∈ Finset.range (k+1),
            ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j)) := by
        intro t ht
        unfold ShockWear.Inherit.resInt
        rw [setLIntegral_congr_fun measurableSet_Ioi (fun x hx => hsurv (x+t)
          (by have : (0:ℝ) < x := hx; linarith))]
        rw [lintegral_tsum]
        · congr 1
          funext k
          rw [lintegral_const_mul, hint k t ht]
          unfold ShockWear.CumDamage.poisW
          fun_prop
        · intro k
          unfold ShockWear.CumDamage.poisW
          fun_prop
      have hQ0 : ∀ k, ∑ j ∈ Finset.range (k+1),
          ENNReal.ofReal (ShockWear.CumDamage.poisW lam 0 j) = 1 := by
        intro k
        rw [Finset.sum_range_succ']
        simp [ShockWear.CumDamage.poisW]
      intro t ht hpos
      rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hpos).ne')
        (Or.inl ENNReal.ofReal_ne_top), hres 0 le_rfl, hres t ht, hsurv t ht]
      simp only [hQ0, mul_one]
      set c := ENNReal.ofReal lam⁻¹ with hc
      set S := ∑' j, ENNReal.ofReal (P j) with hS
      have hR : ∑' k, ENNReal.ofReal (P k) * (c * ∑ j ∈ Finset.range (k+1),
            ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j)) =
          ∑' j, c * ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) *
            ∑' i, ENNReal.ofReal (P (i + j)) := by
        have h1 : ∀ k, ENNReal.ofReal (P k) * (c * ∑ j ∈ Finset.range (k+1),
            ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j)) =
            ∑' j, ENNReal.ofReal (P k) * (c * if j ≤ k then
              ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) else 0) := by
          intro k
          rw [tsum_eq_sum (s := Finset.range (k+1))]
          · rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
          · intro j hj
            rw [if_neg (by intro h; exact hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))]
            simp
        simp_rw [h1]
        rw [ENNReal.tsum_comm]
        congr 1
        funext j
        rw [← (ENNReal.summable).sum_add_tsum_nat_add' (k := j)]
        rw [Finset.sum_eq_zero (fun i hi => by
          rw [if_neg (by have := Finset.mem_range.mp hi; omega)]; simp), zero_add]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext i
        rw [if_pos (by omega)]
        ring
      rw [hR, ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum (fun j => ?_)
      calc S * c * (ENNReal.ofReal (P j) * ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j))
          = c * ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) * (ENNReal.ofReal (P j) * S) := by
            ring
        _ ≤ c * ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) *
            ∑' i, ENNReal.ofReal (P (i + j)) := by
            gcongr
            exact hnwue j
