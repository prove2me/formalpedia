-- Prove2me | solution 1 for ShockWear.Inherit.Supplement.theorem32_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:06.697678+00:00
-- url     : https://prove2.me/submissions/e7abd1a6-ad8d-48dd-8af3-eac1cfdeaebc

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
    (htail : MonotoneOn
      (fun k => (∑' j, ENNReal.ofReal (P (j + k))) / ENNReal.ofReal (P k))
      {k | 0 < P k}) :
    IsIMRL (ShockWear.CumDamage.shockSurv lam P) := by
      classical
      have hpw_nn : ∀ u, 0 ≤ u → ∀ k, 0 ≤ ShockWear.CumDamage.poisW lam u k := by
        intro u hu k
        unfold ShockWear.CumDamage.poisW
        have : 0 ≤ lam * u := mul_nonneg hlam.le hu
        positivity
      have hP1 : ∀ k, P k ≤ 1 := fun k => (hanti (Nat.zero_le k)).trans hP0
      have hsum : ∀ u, 0 ≤ u → Summable (fun k => P k * ShockWear.CumDamage.poisW lam u k) := by
        intro u hu
        have hs : Summable (fun k => ShockWear.CumDamage.poisW lam u k) := by
          have := (Real.summable_pow_div_factorial (lam * u)).mul_left (Real.exp (-(lam * u)))
          refine this.congr ?_
          intro k
          unfold ShockWear.CumDamage.poisW
          ring
        refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hnn k) (hpw_nn u hu k)) ?_ hs
        intro k
        calc P k * ShockWear.CumDamage.poisW lam u k ≤ 1 * ShockWear.CumDamage.poisW lam u k :=
              mul_le_mul_of_nonneg_right (hP1 k) (hpw_nn u hu k)
          _ = _ := one_mul _
      -- survival as an ENNReal series
      have hS : ∀ t, 0 ≤ t → ENNReal.ofReal (ShockWear.CumDamage.shockSurv lam P t)
          = ∑' j, ENNReal.ofReal (P j) * ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) := by
        intro t ht
        have : ShockWear.CumDamage.shockSurv lam P t = ∑' k, P k * ShockWear.CumDamage.poisW lam t k := by
          simp [ShockWear.CumDamage.shockSurv, not_lt.mpr ht]
        rw [this, ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hnn k) (hpw_nn t ht k)) (hsum t ht)]
        congr 1
        ext k
        rw [ENNReal.ofReal_mul (hnn k)]
      -- derivatives of the Poisson weights
      have hd0 : ∀ u, HasDerivAt (fun u => ShockWear.CumDamage.poisW lam u 0)
          (-(lam * ShockWear.CumDamage.poisW lam u 0)) u := by
        intro u
        have h := (((hasDerivAt_id u).const_mul lam).neg).exp
        convert h using 1
        · ext x; simp [ShockWear.CumDamage.poisW]
        · simp [ShockWear.CumDamage.poisW]; ring
      have hd1 : ∀ k u, HasDerivAt (fun u => ShockWear.CumDamage.poisW lam u (k + 1))
          (lam * ShockWear.CumDamage.poisW lam u k - lam * ShockWear.CumDamage.poisW lam u (k + 1)) u := by
        intro k u
        have h1 : HasDerivAt (fun x => lam * x) lam u := by simpa using (hasDerivAt_id u).const_mul lam
        have h := ((h1.neg.exp).mul (h1.pow (k + 1))).div_const ((k + 1).factorial : ℝ)
        refine h.congr_deriv ?_
        simp only [ShockWear.CumDamage.poisW, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
          Nat.cast_one, Nat.add_sub_cancel, Pi.neg_apply, Pi.pow_apply]
        have hf : (k.factorial : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      have hD : ∀ k u, HasDerivAt (fun u => ∑ j ∈ Finset.range (k + 1), ShockWear.CumDamage.poisW lam u j)
          (-(lam * ShockWear.CumDamage.poisW lam u k)) u := by
        intro k
        induction k with
        | zero => intro u; simpa using hd0 u
        | succ k ih =>
          intro u
          have h := (ih u).add (hd1 k u)
          have e : (fun u => ∑ j ∈ Finset.range (k + 1 + 1), ShockWear.CumDamage.poisW lam u j)
              = (fun u => ∑ j ∈ Finset.range (k + 1), ShockWear.CumDamage.poisW lam u j)
                + (fun u => ShockWear.CumDamage.poisW lam u (k + 1)) := by
            funext x; simp [Finset.sum_range_succ]
          rw [e]
          exact h.congr_deriv (by ring)
      have hlim : ∀ (t : ℝ) (j : ℕ), Filter.Tendsto (fun x => ShockWear.CumDamage.poisW lam (x + t) j)
          Filter.atTop (nhds 0) := by
        intro t j
        have h1 : Filter.Tendsto (fun x : ℝ => lam * (x + t)) Filter.atTop Filter.atTop :=
          Filter.Tendsto.const_mul_atTop hlam (Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id)
        have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp h1).div_const (j.factorial : ℝ)
        rw [zero_div] at h2
        refine h2.congr ?_
        intro x
        simp [ShockWear.CumDamage.poisW]
        ring
      have hI : ∀ t, 0 ≤ t → ∀ k, ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (ShockWear.CumDamage.poisW lam (x + t) k)
          = (ENNReal.ofReal lam)⁻¹ * ∑ j ∈ Finset.range (k + 1),
              ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) := by
        intro t ht k
        set g : ℝ → ℝ := fun x => -(lam⁻¹ * ∑ j ∈ Finset.range (k + 1), ShockWear.CumDamage.poisW lam (x + t) j)
          with hg
        have hgd : ∀ x ∈ Set.Ici (0:ℝ), HasDerivAt g (ShockWear.CumDamage.poisW lam (x + t) k) x := by
          intro x _
          have h := (((hD k (x + t)).comp_add_const x t).const_mul lam⁻¹).neg
          refine h.congr_deriv ?_
          field_simp
        have hgpos : ∀ x ∈ Set.Ioi (0:ℝ), 0 ≤ ShockWear.CumDamage.poisW lam (x + t) k := by
          intro x hx
          exact hpw_nn _ (by have := hx.out; linarith) k
        have hgl : Filter.Tendsto g Filter.atTop (nhds 0) := by
          have := ((tendsto_finsetSum (Finset.range (k + 1)) (fun j _ => hlim t j)).const_mul lam⁻¹).neg
          simpa [hg] using this
        have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hgd hgpos hgl
        have hintg := integrableOn_Ioi_deriv_of_nonneg' hgd hgpos hgl
        rw [← ofReal_integral_eq_lintegral_ofReal hintg]
        · rw [hint]
          simp only [hg, zero_add, zero_sub, neg_neg]
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le), ENNReal.ofReal_inv_of_pos hlam,
            ENNReal.ofReal_sum_of_nonneg (fun j _ => hpw_nn t ht j)]
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact hgpos x hx
      have hR : ∀ t, 0 ≤ t → ShockWear.Inherit.resInt (ShockWear.CumDamage.shockSurv lam P) t
          = (ENNReal.ofReal lam)⁻¹ * ∑' j, ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j)
              * ∑' i, ENNReal.ofReal (P (i + j)) := by
        intro t ht
        unfold ShockWear.Inherit.resInt
        rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun x => ∑' k, ENNReal.ofReal (P k)
          * ENNReal.ofReal (ShockWear.CumDamage.poisW lam (x + t) k))
          (fun x hx => hS (x + t) (by have := hx.out; linarith))]
        rw [lintegral_tsum (fun k => by
          have hc : Continuous (fun x => ShockWear.CumDamage.poisW lam (x + t) k) := by
            unfold ShockWear.CumDamage.poisW; fun_prop
          exact ((ENNReal.measurable_ofReal.comp hc.measurable).const_mul _).aemeasurable)]
        have h1 : ∀ k, ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (P k)
            * ENNReal.ofReal (ShockWear.CumDamage.poisW lam (x + t) k)
            = (ENNReal.ofReal lam)⁻¹ * ∑' j, (if j ≤ k then ENNReal.ofReal (P k)
                * ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) else 0) := by
          intro k
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hI t ht k,
            tsum_eq_sum (s := Finset.range (k + 1))]
          · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            rw [if_pos this]; ring
          · intro j hj
            have : ¬ j ≤ k := fun h => hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
            rw [if_neg this]
        simp_rw [h1]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
        congr 1
        refine tsum_congr (fun j => ?_)
        have h2 : ∀ k, (if j ≤ k then ENNReal.ofReal (P k)
                * ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) else 0)
            = (if j ≤ k then ENNReal.ofReal (P k) else 0)
                * ENNReal.ofReal (ShockWear.CumDamage.poisW lam t j) := by
          intro k; split_ifs <;> simp
        simp_rw [h2]
        rw [ENNReal.tsum_mul_right, mul_comm]
        congr 1
        rw [← (ENNReal.summable).sum_add_tsum_nat_add' (k := j)
          (f := fun k => if j ≤ k then ENNReal.ofReal (P k) else 0)]
        rw [Finset.sum_eq_zero (fun i hi => by
          have : ¬ j ≤ i := by have := Finset.mem_range.mp hi; omega
          simp [this])]
        simp
      -- abstract the weights
      obtain ⟨w, hw⟩ : ∃ w : ℝ → ℕ → ℝ≥0∞,
          w = fun u j => ENNReal.ofReal (ShockWear.CumDamage.poisW lam u j) := ⟨_, rfl⟩
      obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ≥0∞, T = fun j => ∑' i, ENNReal.ofReal (P (i + j)) := ⟨_, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ≥0∞, b = fun j => ENNReal.ofReal (P j) := ⟨_, rfl⟩
      have hS' : ∀ t, 0 ≤ t → ENNReal.ofReal (ShockWear.CumDamage.shockSurv lam P t)
          = ∑' j, b j * w t j := by
        intro t ht; rw [hb, hw]; exact hS t ht
      have hR' : ∀ t, 0 ≤ t → ShockWear.Inherit.resInt (ShockWear.CumDamage.shockSurv lam P) t
          = (ENNReal.ofReal lam)⁻¹ * ∑' j, w t j * T j := by
        intro t ht; rw [hT, hw]; exact hR t ht
      have hxy : ∀ j k, j ≤ k → T j * b k ≤ T k * b j := by
        intro j k hjk
        by_cases hk : P k = 0
        · rw [hb]; simp [hk]
        have hkpos : 0 < P k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
        have hjpos : 0 < P j := lt_of_lt_of_le hkpos (hanti hjk)
        have h : T j / b j ≤ T k / b k := by rw [hT, hb]; exact htail hjpos hkpos hjk
        have hbj0 : b j ≠ 0 := by rw [hb]; exact (ENNReal.ofReal_pos.mpr hjpos).ne'
        have hbk0 : b k ≠ 0 := by rw [hb]; exact (ENNReal.ofReal_pos.mpr hkpos).ne'
        have hbjt : b j ≠ ⊤ := by rw [hb]; exact ENNReal.ofReal_ne_top
        have hbkt : b k ≠ ⊤ := by rw [hb]; exact ENNReal.ofReal_ne_top
        calc T j * b k = (T j / b j * b j) * b k := by rw [ENNReal.div_mul_cancel hbj0 hbjt]
          _ ≤ (T k / b k * b j) * b k := by gcongr
          _ = T k * b j := by rw [mul_right_comm, ENNReal.div_mul_cancel hbk0 hbkt]
      have hqp : ∀ s t, 0 ≤ s → s ≤ t → ∀ j k, j ≤ k → w t j * w s k ≤ w s j * w t k := by
        intro s t hs hst j k hjk
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
        have ht : 0 ≤ t := hs.trans hst
        rw [hw]
        simp only
        rw [← ENNReal.ofReal_mul (hpw_nn t ht j), ← ENNReal.ofReal_mul (hpw_nn s hs j)]
        apply ENNReal.ofReal_le_ofReal
        unfold ShockWear.CumDamage.poisW
        have hu : 0 ≤ lam * s := mul_nonneg hlam.le hs
        have huv : lam * s ≤ lam * t := mul_le_mul_of_nonneg_left hst hlam.le
        set u := lam * s
        set v := lam * t
        have key : v ^ j * u ^ (j + m) ≤ u ^ j * v ^ (j + m) := by
          rw [pow_add, pow_add]
          have : u ^ m ≤ v ^ m := pow_le_pow_left₀ hu huv m
          have hv : 0 ≤ v := hu.trans huv
          calc v ^ j * (u ^ j * u ^ m) = (u ^ j * v ^ j) * u ^ m := by ring
            _ ≤ (u ^ j * v ^ j) * v ^ m := mul_le_mul_of_nonneg_left this (by positivity)
            _ = u ^ j * (v ^ j * v ^ m) := by ring
        have e1 : Real.exp (-v) * v ^ j / (j.factorial : ℝ) * (Real.exp (-u) * u ^ (j + m) / ((j + m).factorial : ℝ))
            = (Real.exp (-v) * Real.exp (-u) / ((j.factorial : ℝ) * ((j + m).factorial : ℝ))) * (v ^ j * u ^ (j + m)) := by
          ring
        have e2 : Real.exp (-u) * u ^ j / (j.factorial : ℝ) * (Real.exp (-v) * v ^ (j + m) / ((j + m).factorial : ℝ))
            = (Real.exp (-v) * Real.exp (-u) / ((j.factorial : ℝ) * ((j + m).factorial : ℝ))) * (u ^ j * v ^ (j + m)) := by
          ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left key (by positivity)
      have hsym : ∀ F : ℕ → ℕ → ℝ≥0∞, (∑' j, ∑' k, F j k) + (∑' j, ∑' k, F j k)
          = ∑' j, ∑' k, (F j k + F k j) := by
        intro F
        nth_rewrite 2 [ENNReal.tsum_comm]
        rw [← ENNReal.tsum_add]
        refine tsum_congr (fun j => ?_)
        rw [← ENNReal.tsum_add]
      have hkey : ∀ s t, 0 ≤ s → s ≤ t →
          (∑' j, w s j * T j) * (∑' k, b k * w t k) ≤ (∑' j, w t j * T j) * (∑' k, b k * w s k) := by
        intro s t hs hst
        have hpt : ∀ j k, j ≤ k →
            T j * b k * (w s j * w t k) + T k * b j * (w s k * w t j)
              ≤ T j * b k * (w t j * w s k) + T k * b j * (w t k * w s j) := by
          intro j k hjk
          have hq := hqp s t hs hst j k hjk
          have hx := hxy j k hjk
          obtain ⟨d, hd⟩ := exists_add_of_le hq
          rw [mul_comm (w s k) (w t j), mul_comm (w t k) (w s j), hd]
          calc T j * b k * (w t j * w s k + d) + T k * b j * (w t j * w s k)
              = (T j * b k * (w t j * w s k) + T k * b j * (w t j * w s k)) + T j * b k * d := by ring
            _ ≤ (T j * b k * (w t j * w s k) + T k * b j * (w t j * w s k)) + T k * b j * d := by gcongr
            _ = T j * b k * (w t j * w s k) + T k * b j * (w t j * w s k + d) := by ring
        have hpt' : ∀ j k,
            T j * b k * (w s j * w t k) + T k * b j * (w s k * w t j)
              ≤ T j * b k * (w t j * w s k) + T k * b j * (w t k * w s j) := by
          intro j k
          rcases le_total j k with h | h
          · exact hpt j k h
          · have := hpt k j h
            rw [add_comm, add_comm (T j * b k * (w t j * w s k))]
            exact this
        have eA : (∑' j, w s j * T j) * (∑' k, b k * w t k)
            = ∑' j, ∑' k, T j * b k * (w s j * w t k) := by
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr (fun j => ?_)
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun k => ?_)
          ring
        have eB : (∑' j, w t j * T j) * (∑' k, b k * w s k)
            = ∑' j, ∑' k, T j * b k * (w t j * w s k) := by
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr (fun j => ?_)
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun k => ?_)
          ring
        rw [eA, eB]
        have h2 : (∑' j, ∑' k, T j * b k * (w s j * w t k)) + (∑' j, ∑' k, T j * b k * (w s j * w t k))
            ≤ (∑' j, ∑' k, T j * b k * (w t j * w s k)) + (∑' j, ∑' k, T j * b k * (w t j * w s k)) := by
          rw [hsym (fun j k => T j * b k * (w s j * w t k)), hsym (fun j k => T j * b k * (w t j * w s k))]
          exact ENNReal.tsum_le_tsum (fun j => ENNReal.tsum_le_tsum (fun k => hpt' j k))
        by_contra hc
        rw [not_le] at hc
        exact absurd h2 (not_le.mpr (ENNReal.add_lt_add hc hc))
      intro s hs t ht hst
      have hs0 : 0 ≤ s := hs.1
      have ht0 : 0 ≤ t := ht.1
      have hBs : (∑' k, b k * w s k) ≠ 0 := by rw [← hS' s hs0]; exact (ENNReal.ofReal_pos.mpr hs.2).ne'
      have hBt : (∑' k, b k * w t k) ≠ 0 := by rw [← hS' t ht0]; exact (ENNReal.ofReal_pos.mpr ht.2).ne'
      have hBs' : (∑' k, b k * w s k) ≠ ⊤ := by rw [← hS' s hs0]; exact ENNReal.ofReal_ne_top
      have hBt' : (∑' k, b k * w t k) ≠ ⊤ := by rw [← hS' t ht0]; exact ENNReal.ofReal_ne_top
      show ShockWear.Inherit.resInt (ShockWear.CumDamage.shockSurv lam P) s
          / ENNReal.ofReal (ShockWear.CumDamage.shockSurv lam P s)
        ≤ ShockWear.Inherit.resInt (ShockWear.CumDamage.shockSurv lam P) t
          / ENNReal.ofReal (ShockWear.CumDamage.shockSurv lam P t)
      rw [hR' s hs0, hR' t ht0, hS' s hs0, hS' t ht0]
      set c := (ENNReal.ofReal lam)⁻¹
      set As := ∑' j, w s j * T j
      set At := ∑' j, w t j * T j
      set Bs := ∑' k, b k * w s k
      set Bt := ∑' k, b k * w t k
      have hk := hkey s t hs0 hst
      rw [← ENNReal.mul_div_mul_right (c * As) Bs hBt hBt', ← ENNReal.mul_div_mul_right (c * At) Bt hBs hBs',
        mul_comm Bt Bs]
      apply ENNReal.div_le_div_right
      rw [mul_assoc, mul_assoc]
      gcongr
