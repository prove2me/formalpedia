-- Prove2me | solution 1 for SupplyChainCarbon.Necessity.double_counting_necessary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T13:11:02.710196+00:00
-- url     : https://prove2.me/submissions/270ad487-2c06-4ea6-a4d1-4602e63f60ba

import Mathlib
import Definitions.Def_SupplyChainCarbon_Necessity_Marginals

set_option autoImplicit false

namespace SCCAux

/-- A function antitone on `[0,A]` has nonpositive derivative at an interior point. -/
theorem deriv_nonpos_of_antitoneOn_Icc {g : ℝ → ℝ} {A t0 : ℝ}
    (hg : AntitoneOn g (Set.Icc 0 A)) (ht : t0 ∈ Set.Ioo 0 A) : deriv g t0 ≤ 0 := by
  have hA : 0 ≤ A := ht.1.le.trans ht.2.le
  set c : ℝ → ℝ := fun t => max 0 (min A t) with hcdef
  have hc : ∀ t, c t ∈ Set.Icc 0 A := fun t => ⟨le_max_left _ _, max_le hA (min_le_left _ _)⟩
  have hmono : Monotone c := fun a b hab => max_le_max le_rfl (min_le_min le_rfl hab)
  have hanti : Antitone (g ∘ c) := fun a b hab => hg (hc a) (hc b) (hmono hab)
  have heq : (g ∘ c) =ᶠ[nhds t0] g := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t htt
    simp [c, min_eq_right htt.2.le, max_eq_right htt.1.le]
  rw [← heq.deriv_eq]
  exact hanti.deriv_nonpos

/-- A function monotone on `[0,A]` has nonnegative derivative at an interior point. -/
theorem deriv_nonneg_of_monotoneOn_Icc {g : ℝ → ℝ} {A t0 : ℝ}
    (hg : MonotoneOn g (Set.Icc 0 A)) (ht : t0 ∈ Set.Ioo 0 A) : 0 ≤ deriv g t0 := by
  have hA : 0 ≤ A := ht.1.le.trans ht.2.le
  set c : ℝ → ℝ := fun t => max 0 (min A t) with hcdef
  have hc : ∀ t, c t ∈ Set.Icc 0 A := fun t => ⟨le_max_left _ _, max_le hA (min_le_left _ _)⟩
  have hmono : Monotone c := fun a b hab => max_le_max le_rfl (min_le_min le_rfl hab)
  have hmon : Monotone (g ∘ c) := fun a b hab => hg (hc a) (hc b) (hmono hab)
  have heq : (g ∘ c) =ᶠ[nhds t0] g := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t htt
    simp [c, min_eq_right htt.2.le, max_eq_right htt.1.le]
  rw [← heq.deriv_eq]
  exact hmon.deriv_nonneg

/-- Chain rule: `fderiv H φ w` as a sum of coordinate directional derivatives. -/
theorem fderiv_apply_eq_sum {I : ℕ} (L : (Fin I → ℝ) →L[ℝ] ℝ) (w : Fin I → ℝ) :
    L w = ∑ i, L (Pi.single i 1) * w i := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (Pi.single i (w i) : Fin I → ℝ) = w i • (Pi.single i 1 : Fin I → ℝ) by
    ext k; by_cases hk : k = i
    · subst hk; simp
    · simp [hk]]
  rw [map_smul, smul_eq_mul, mul_comm]

end SCCAux

-- Proposition 2, p. 12; influence is evaluated at eStar, as in Appendix A.1.
open SupplyChainCarbon.Necessity in
theorem solution
    (N I : ℕ) (m : Fin N → ℕ) (C : Technology N I m)
    (pS : ℝ) (hpS : 0 < pS) (R : PaymentRule N I pS)
    (eStar : Effort N m)
    (hfirst : CarbonDoubleCount.Planner.IsFirstBest C.bound (profit C) C.footprint pS eStar)
    (hunique : ∀ e ∈ effortBox m C.bound,
      CarbonDoubleCount.Planner.IsFirstBest C.bound (profit C) C.footprint pS e → e = eStar)
    (hinterior : ∀ n j, 0 < eStar n j ∧ eStar n j < C.bound)
    (hrelevant : relevantIncidence C eStar)
    (hjoint : jointProduction C eStar)
    (hincreasing : ∀ n, MonotoneOn (R.payment n) (footprintOrthant I))
    (reservation : Fin N → ℝ)
    (hparticipation : participation C R reservation eStar)
    (hnash : isNash C R eStar) :
    ∃ i, pS < aggregateMarginal R (C.footprint eStar) i := by
  classical
  -- membership helpers
  have memBox : ∀ e : Effort N m, (∀ n j, 0 ≤ e n j ∧ e n j ≤ C.bound) →
      e ∈ effortBox m C.bound := fun e h => h
  have memFirm : ∀ n (x : Fin (m n) → ℝ), (∀ j, 0 ≤ x j ∧ x j ≤ C.bound) →
      x ∈ firmBox m C.bound n := fun n x h => h
  have memOrth : ∀ φ : Footprint I, (∀ i, 0 ≤ φ i) → φ ∈ footprintOrthant I := fun φ h => h
  have hbox : eStar ∈ effortBox m C.bound := hfirst.1
  -- neighbourhoods
  have hboxN : effortBox m C.bound ∈ nhds eStar := by
    have hS : ∀ᶠ e in nhds eStar, ∀ n j, 0 < e n j ∧ e n j < C.bound := by
      refine Filter.eventually_all.2 fun n => Filter.eventually_all.2 fun j => ?_
      have hc : Continuous fun e : Effort N m => e n j :=
        (continuous_apply j).comp (continuous_apply n)
      filter_upwards [hc.continuousAt.eventually_mem
        (Ioo_mem_nhds (hinterior n j).1 (hinterior n j).2)] with e he
      exact he
    filter_upwards [hS] with e he
    exact memBox e fun n j => ⟨(he n j).1.le, (he n j).2.le⟩
  have hfirmN : ∀ n, firmBox m C.bound n ∈ nhds (eStar n) := by
    intro n
    have hS : ∀ᶠ x in nhds (eStar n), ∀ j, 0 < x j ∧ x j < C.bound := by
      refine Filter.eventually_all.2 fun j => ?_
      have hc : Continuous fun x : Fin (m n) → ℝ => x j := continuous_apply j
      filter_upwards [hc.continuousAt.eventually_mem
        (Ioo_mem_nhds (hinterior n j).1 (hinterior n j).2)] with x hx
      exact hx
    filter_upwards [hS] with x hx
    exact memFirm n x fun j => ⟨(hx j).1.le, (hx j).2.le⟩
  have hFdiff : ∀ i, DifferentiableAt ℝ (fun x => C.footprint x i) eStar :=
    fun i => (C.footprint_diff i).differentiableAt hboxN
  have hEP : ∀ i n j, effortPartial C eStar i n j =
      fderiv ℝ (fun x => C.footprint x i) eStar (Pi.single n (Pi.single j 1)) := by
    intro i n j
    unfold effortPartial
    rw [fderivWithin_of_mem_nhds hboxN]
  have hcost : ∀ n, DifferentiableAt ℝ (C.cost n) (eStar n) :=
    fun n => (C.cost_diff n).differentiableAt (hfirmN n)
  -- the lines moving one action
  let u : (n : Fin N) → Fin (m n) → ℝ → Effort N m :=
    fun n j t => eStar + (t - eStar n j) • (Pi.single n (Pi.single j (1 : ℝ)) : Effort N m)
  have hu_same : ∀ n (j : Fin (m n)) t k,
      u n j t n k = eStar n k + (t - eStar n j) * (Pi.single j (1 : ℝ) : Fin (m n) → ℝ) k := by
    intro n j t k
    simp [u]
  have hu_ne : ∀ n (j : Fin (m n)) t m' (k : Fin (m m')), m' ≠ n → u n j t m' k = eStar m' k := by
    intro n j t m' k hm
    simp [u, Pi.single_eq_of_ne hm]
  have hu_ne' : ∀ n (j : Fin (m n)) t m', m' ≠ n → u n j t m' = eStar m' := by
    intro n j t m' hm
    funext k
    exact hu_ne n j t m' k hm
  have hu_t0 : ∀ n (j : Fin (m n)), u n j (eStar n j) = eStar := by
    intro n j
    simp [u]
  have hu_upd : ∀ n (j : Fin (m n)) t, Function.update eStar n (u n j t n) = u n j t := by
    intro n j t
    funext m'
    rcases eq_or_ne m' n with rfl | hm
    · simp
    · rw [Function.update_of_ne hm, hu_ne' n j t m' hm]
  have hu_deriv : ∀ n (j : Fin (m n)) t,
      HasDerivAt (u n j) (Pi.single n (Pi.single j (1 : ℝ)) : Effort N m) t := by
    intro n j t
    have h := (((hasDerivAt_id t).sub_const (eStar n j)).smul_const
      (Pi.single n (Pi.single j (1 : ℝ)) : Effort N m)).const_add eStar
    rw [one_smul] at h
    exact h
  have hu_box : ∀ n (j : Fin (m n)) t, t ∈ Set.Icc 0 C.bound → u n j t ∈ effortBox m C.bound := by
    intro n j t ht
    apply memBox
    intro m' k
    rcases eq_or_ne m' n with rfl | hm
    · rw [hu_same]
      rcases eq_or_ne k j with rfl | hk
      · simp only [Pi.single_eq_same, mul_one]
        constructor <;> linarith [ht.1, ht.2]
      · simp only [Pi.single_eq_of_ne hk, mul_zero, add_zero]
        exact hbox m' k
    · rw [hu_ne n j t m' k hm]
      exact hbox m' k
  have hu_mono : ∀ n (j : Fin (m n)), Monotone (u n j) := by
    intro n j a b hab m' k
    have hv : (0 : ℝ) ≤ (Pi.single n (Pi.single j (1 : ℝ)) : Effort N m) m' k := by
      rcases eq_or_ne m' n with rfl | hm
      · rw [Pi.single_eq_same, Pi.single_apply]; split_ifs <;> norm_num
      · rw [Pi.single_eq_of_ne hm]; exact le_refl _
    show eStar m' k + (a - eStar n j) * _ ≤ eStar m' k + (b - eStar n j) * _
    have : (a - eStar n j) * (Pi.single n (Pi.single j (1 : ℝ)) : Effort N m) m' k ≤
        (b - eStar n j) * (Pi.single n (Pi.single j (1 : ℝ)) : Effort N m) m' k :=
      mul_le_mul_of_nonneg_right (by linarith) hv
    linarith
  have hmemIoo : ∀ n j, eStar n j ∈ Set.Ioo 0 C.bound :=
    fun n j => ⟨(hinterior n j).1, (hinterior n j).2⟩
  -- footprint derivatives along the lines
  have hF : ∀ n (j : Fin (m n)) i, HasDerivAt (fun t => C.footprint (u n j t) i)
      (effortPartial C eStar i n j) (eStar n j) := by
    intro n j i
    rw [hEP]
    exact (hFdiff i).hasFDerivAt.comp_hasDerivAt_of_eq (eStar n j) (hu_deriv n j _)
      (hu_t0 n j).symm
  have hE : ∀ i n (j : Fin (m n)), effortPartial C eStar i n j ≤ 0 := by
    intro i n j
    rw [← (hF n j i).deriv]
    apply SCCAux.deriv_nonpos_of_antitoneOn_Icc (A := C.bound) _ (hmemIoo n j)
    intro a ha b hb hab
    exact C.footprint_decreasing i (hu_box n j a ha) (hu_box n j b hb) (hu_mono n j hab)
  -- footprints are strictly positive at eStar
  have hpos : ∀ i, 0 < C.footprint eStar i := by
    intro i
    have h1 := hrelevant.2 i
    obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun n => incidence C eStar n i) (by omega)
    have hlt : ∑ j, effortPartial C eStar i n j < 0 := by
      by_contra hc
      exact hn (by simp only [incidence, if_neg hc])
    obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt
      (show ∑ j, effortPartial C eStar i n j < ∑ _j : Fin (m n), (0 : ℝ) by simpa using hlt)
    by_contra hle
    have hz : C.footprint eStar i = 0 :=
      le_antisymm (not_lt.1 hle) (C.footprint_nonneg eStar hbox i)
    have hmin : IsLocalMin (fun t => C.footprint (u n j t) i) (eStar n j) := by
      filter_upwards [Ioo_mem_nhds (hmemIoo n j).1 (hmemIoo n j).2] with t ht
      show C.footprint (u n j (eStar n j)) i ≤ C.footprint (u n j t) i
      rw [hu_t0, hz]
      exact C.footprint_nonneg _ (hu_box n j t ⟨ht.1.le, ht.2.le⟩) i
    have := hmin.hasDerivAt_eq_zero (hF n j i)
    linarith
  have hOrthN : footprintOrthant I ∈ nhds (C.footprint eStar) := by
    have hS : ∀ᶠ φ in nhds (C.footprint eStar), ∀ i, 0 < φ i := by
      refine Filter.eventually_all.2 fun i => ?_
      have hc : Continuous fun φ : Footprint I => φ i := continuous_apply i
      exact hc.continuousAt.eventually (lt_mem_nhds (hpos i))
    filter_upwards [hS] with φ hφ
    exact memOrth φ fun i => (hφ i).le
  have hPdiff : ∀ n, DifferentiableAt ℝ (R.payment n) (C.footprint eStar) :=
    fun n => (R.payment_diff n).differentiableAt hOrthN
  have hPP : ∀ n i, paymentPartial R (C.footprint eStar) n i =
      fderiv ℝ (R.payment n) (C.footprint eStar) (Pi.single i 1) := by
    intro n i
    unfold paymentPartial
    rw [fderivWithin_of_mem_nhds hOrthN]
  have hP0 : ∀ n i, 0 ≤ paymentPartial R (C.footprint eStar) n i := by
    intro n i
    set φ := C.footprint eStar with hφdef
    have hd : HasDerivAt (fun t => R.payment n (Function.update φ i t))
        (fderiv ℝ (R.payment n) φ (Pi.single i 1)) (φ i) :=
      (hPdiff n).hasFDerivAt.comp_hasDerivAt_of_eq (φ i) (hasDerivAt_update φ i (φ i))
        (Function.update_eq_self i φ).symm
    rw [hPP, ← hd.deriv]
    apply SCCAux.deriv_nonneg_of_monotoneOn_Icc (A := φ i + 1) _ ⟨hpos i, by linarith⟩
    have hupd_mem : ∀ t, 0 ≤ t → Function.update φ i t ∈ footprintOrthant I := by
      intro t ht
      apply memOrth
      intro k
      rcases eq_or_ne k i with rfl | hk
      · simpa using ht
      · rw [Function.update_of_ne hk]; exact (hpos k).le
    intro a ha b hb hab
    apply hincreasing n (hupd_mem a ha.1) (hupd_mem b hb.1)
    intro k
    rcases eq_or_ne k i with rfl | hk
    · simpa using hab
    · simp [Function.update_of_ne hk]
  -- the two first-order conditions combine into one identity per action
  have key : ∀ n (j : Fin (m n)), ∑ i, (pS - paymentPartial R (C.footprint eStar) n i) *
      effortPartial C eStar i n j = 0 := by
    intro n j
    set t0 := eStar n j with ht0
    have hcn : DifferentiableAt ℝ (C.cost n) (u n j t0 n) := by
      rw [hu_t0]; exact hcost n
    have hun : DifferentiableAt ℝ (fun t => u n j t n) t0 :=
      (differentiableAt_pi.1 (hu_deriv n j t0).differentiableAt) n
    have hVd : DifferentiableAt ℝ (fun t => profit C n (u n j t n)) t0 := by
      unfold profit
      exact (differentiableAt_const _).sub (hcn.comp t0 hun)
    have hV := hVd.hasDerivAt
    have hsum : ∀ t, ∑ m', profit C m' (u n j t m') =
        profit C n (u n j t n) + ∑ m' ∈ Finset.univ.erase n, profit C m' (eStar m') := by
      intro t
      rw [← Finset.add_sum_erase _ (fun m' => profit C m' (u n j t m')) (Finset.mem_univ n)]
      congr 1
      apply Finset.sum_congr rfl
      intro m' hm
      rw [hu_ne' n j t m' (Finset.ne_of_mem_erase hm)]
    -- first best FOC
    have hFB : deriv (fun t => profit C n (u n j t n)) t0
        - pS * ∑ i, effortPartial C eStar i n j = 0 := by
      have hD : HasDerivAt (fun t => profit C n (u n j t n)
          + ∑ m' ∈ Finset.univ.erase n, profit C m' (eStar m')
          - pS * ∑ i, C.footprint (u n j t) i)
          (deriv (fun t => profit C n (u n j t n)) t0
            - pS * ∑ i, effortPartial C eStar i n j) t0 :=
        (hV.add_const _).fun_sub
          ((HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hF n j i)).const_mul pS)
      have hmax : IsLocalMax (fun t => profit C n (u n j t n)
          + ∑ m' ∈ Finset.univ.erase n, profit C m' (eStar m')
          - pS * ∑ i, C.footprint (u n j t) i) t0 := by
        filter_upwards [Ioo_mem_nhds (hmemIoo n j).1 (hmemIoo n j).2] with t ht
        have h1 := hfirst.2 (u n j t) (hu_box n j t ⟨ht.1.le, ht.2.le⟩)
        unfold CarbonDoubleCount.Planner.socialValue at h1
        rw [hsum t] at h1
        have e3 := hsum t0
        rw [hu_t0] at e3
        rw [e3] at h1
        show _ ≤ profit C n (u n j t0 n)
          + ∑ m' ∈ Finset.univ.erase n, profit C m' (eStar m')
          - pS * ∑ i, C.footprint (u n j t0) i
        rw [hu_t0]
        exact h1
      exact hmax.hasDerivAt_eq_zero hD
    -- Nash FOC
    have hNE : deriv (fun t => profit C n (u n j t n)) t0
        - ∑ i, paymentPartial R (C.footprint eStar) n i * effortPartial C eStar i n j = 0 := by
      have hΦ : HasDerivAt (fun t => C.footprint (u n j t))
          (fun i => effortPartial C eStar i n j) t0 := hasDerivAt_pi.2 (hF n j)
      have hc := (hPdiff n).hasFDerivAt.comp_hasDerivAt_of_eq t0 hΦ
        (by rw [hu_t0])
      rw [SCCAux.fderiv_apply_eq_sum] at hc
      simp only [← hPP] at hc
      have hD := hV.fun_sub hc
      have hmax : IsLocalMax (fun t => profit C n (u n j t n)
          - R.payment n (C.footprint (u n j t))) t0 := by
        filter_upwards [Ioo_mem_nhds (hmemIoo n j).1 (hmemIoo n j).2] with t ht
        have hx : u n j t n ∈ firmBox m C.bound n := by
          have := hu_box n j t ⟨ht.1.le, ht.2.le⟩
          exact memFirm n _ fun k => this n k
        have h1 := hnash.2 n _ hx
        rw [hu_upd] at h1
        show _ ≤ profit C n (u n j t0 n) - R.payment n (C.footprint (u n j t0))
        rw [hu_t0]
        exact h1
      exact hmax.hasDerivAt_eq_zero hD
    have e1 : ∑ i, (pS - paymentPartial R (C.footprint eStar) n i) * effortPartial C eStar i n j
        = pS * ∑ i, effortPartial C eStar i n j
          - ∑ i, paymentPartial R (C.footprint eStar) n i * effortPartial C eStar i n j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e1]; linarith
  -- conclude
  by_contra hnot
  have hle : ∀ i, aggregateMarginal R (C.footprint eStar) i ≤ pS := by
    intro i
    by_contra hi
    exact hnot ⟨i, lt_of_not_ge hi⟩
  have Hle : ∀ n i, paymentPartial R (C.footprint eStar) n i ≤ pS := fun n i =>
    (Finset.single_le_sum (fun m' _ => hP0 m' i) (Finset.mem_univ n)).trans (hle i)
  obtain ⟨i0, hi0⟩ := hjoint
  have hfull : ∀ n, incidence C eStar n i0 = 1 →
      paymentPartial R (C.footprint eStar) n i0 = pS := by
    intro n hn
    have hlt : ∑ j, effortPartial C eStar i0 n j < 0 := by
      by_contra hc
      have : incidence C eStar n i0 = 0 := by simp only [incidence, if_neg hc]
      omega
    obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt
      (show ∑ j, effortPartial C eStar i0 n j < ∑ _j : Fin (m n), (0 : ℝ) by simpa using hlt)
    have hz := (Finset.sum_eq_zero_iff_of_nonpos
      (fun i _ => mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (Hle n i)) (hE i n j))).1
      (key n j) i0 (Finset.mem_univ _)
    rcases mul_eq_zero.1 hz with h1 | h1
    · linarith
    · linarith
  have hge : ∀ n, (incidence C eStar n i0 : ℝ) * pS ≤ paymentPartial R (C.footprint eStar) n i0 := by
    intro n
    by_cases hc : (∑ j, effortPartial C eStar i0 n j) < 0
    · have hn : incidence C eStar n i0 = 1 := by simp only [incidence, if_pos hc]
      rw [hfull n hn, hn]; simp
    · have hn : incidence C eStar n i0 = 0 := by simp only [incidence, if_neg hc]
      rw [hn]; simpa using hP0 n i0
  have hsumge : (∑ n, (incidence C eStar n i0 : ℝ)) * pS ≤
      aggregateMarginal R (C.footprint eStar) i0 := by
    unfold aggregateMarginal
    rw [Finset.sum_mul]; exact Finset.sum_le_sum (fun n _ => hge n)
  have h2 : (2 : ℝ) ≤ ∑ n, (incidence C eStar n i0 : ℝ) := by exact_mod_cast hi0
  have := hle i0
  nlinarith
