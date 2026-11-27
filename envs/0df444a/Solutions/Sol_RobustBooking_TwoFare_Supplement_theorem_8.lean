-- Prove2me | solution 1 for RobustBooking.TwoFare.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:46.195975+00:00
-- url     : https://prove2.me/submissions/c3e725bc-7422-4cb0-8891-6bea9f755735

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Supplement_DiscreteBidPrice

open RobustBooking
open RobustBooking.TwoFare
open RobustBooking.TwoFare.Supplement

/-- Theorem 8 (Ball–Queyranne 2009, p. 961). Let `0 < f_min < f_max`, `r = f_min / f_max`, and let
`ρ` satisfy `0 < ρ < 1 / (1 - ln r)`. If the integer capacity `n` satisfies (20),
`n ≥ max {1 / (1 - ρ), (1/ρ) G^(-1)(r^(-ρ/(1-ρ)))}`, then on every instance of unit orders with
fares in `[f_min, f_max]` the discrete order quantity control policy based on `P_ρ` earns at least
`ρ (1 - 1 / (ρ (ρ n + 1)))` times the optimal offline revenue, i.e. its competitive ratio is at
least (21). -/
theorem solution (fmin fmax ρ : ℝ) (n : ℕ) (hfmin : 0 < fmin) (hfmax : fmin < fmax)
    (hρ : 0 < ρ) (hρr : ρ < 1 / (1 - Real.log (fmin / fmax)))
    (h20 : max (1 / (1 - ρ)) ((1 / ρ) * Ginv ((fmin / fmax) ^ (-(ρ / (1 - ρ))))) ≤ (n : ℝ))
    (I : List ℝ) (hI : ∀ O ∈ I, fmin ≤ O ∧ O ≤ fmax) :
    ρ * (1 - 1 / (ρ * (ρ * n + 1))) * bpOpt n I ≤ bpRevenue n (orderQtyPolicy fmin ρ n) I := by
      set_option maxHeartbeats 1200000 in
      have hfmax0 : 0 < fmax := lt_trans hfmin hfmax
      have hr0 : 0 < fmin / fmax := div_pos hfmin hfmax0
      have hr1 : fmin / fmax < 1 := (div_lt_one hfmax0).2 hfmax
      have hlr : Real.log (fmin / fmax) < 0 := Real.log_neg hr0 hr1
      have hρ1 : ρ < 1 := lt_of_lt_of_le hρr ((div_le_one (by linarith)).2 (by linarith))
      have hδ : 0 < 1 - ρ := sub_pos.mpr hρ1
      have hnfirst : 1 / (1 - ρ) ≤ (n : ℝ) := le_trans (le_max_left _ _) h20
      have hnlarge : ρ * (n : ℝ) + 1 ≤ n := by
        have := (div_le_iff₀ hδ).1 hnfirst
        nlinarith
      have hn0 : 0 < (n : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hxn : 0 < ρ * (n : ℝ) := mul_pos hρ hn0
      let x : ℝ := ρ * n
      let b : ℝ := 1 + 1 / x
      let m : ℕ := ⌊x⌋₊
      have hx : 0 < x := hxn
      have hb : 1 < b := by dsimp [b]; linarith [one_div_pos.mpr hx]
      have hb0 : 0 < b := lt_trans zero_lt_one hb
      have hmle : (m : ℝ) ≤ x := Nat.floor_le hx.le
      have hmlt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
      have hmn : m < n := by exact_mod_cast (show (m : ℝ) < n by dsimp [x] at hmle; nlinarith)
      let T : ℕ → ℝ := fun q => fmin * b ^ (q - m)
      let S : ℕ → ℝ := fun q => ∑ i ∈ Finset.range q, T i
      have hTpos : ∀ q, 0 < T q := by intro q; dsimp [T]; positivity
      have hTmono : Monotone T := by
        intro q q' hqq
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb.le (Nat.sub_le_sub_right hqq m)) hfmin.le
      have hTflat : ∀ q, q ≤ m → T q = fmin := by
        intro q hq; simp [T, Nat.sub_eq_zero_of_le hq]
      have hTstep : ∀ q, m ≤ q → T (q + 1) = b * T q := by
        intro q hq
        have hsub : q + 1 - m = (q - m) + 1 := by omega
        simp only [T, hsub, pow_succ]
        ring
      have hSstep : ∀ q, S (q + 1) = S q + T q := by intro q; exact Finset.sum_range_succ _ q
      have hS0 : S 0 = 0 := by simp [S]
      have hSnonneg : ∀ q, 0 ≤ S q := by
        intro q; exact Finset.sum_nonneg (fun i hi => (hTpos i).le)
      have hSbound : ∀ q, m ≤ q → x * T q - fmin ≤ S q := by
        have hSm : S m = (m : ℝ) * fmin := by
          dsimp [S]
          rw [Finset.sum_congr rfl (fun i hi => hTflat i (Nat.le_of_lt (Finset.mem_range.mp hi)))]
          simp
        have hbase : x * T m - fmin ≤ S m := by rw [hTflat m le_rfl, hSm]; nlinarith
        intro q hq
        induction q, hq using Nat.le_induction with
        | base => exact hbase
        | succ q hq ih =>
          rw [hSstep, hTstep q hq]
          have hxb : x * b = x + 1 := by dsimp [b]; field_simp
          nlinarith [hTpos q]
      have hSratio : ∀ q, m ≤ q → (x - 1) * T q ≤ S q := by
        intro q hq
        have ht : fmin ≤ T q := by
          simpa only [hTflat 0 (Nat.zero_le m)] using hTmono (Nat.zero_le q)
        nlinarith [hSbound q hq]
      have hceil : ∀ q : ℕ, ⌈(q : ℝ) - ρ * n - 1⌉ = (q : ℤ) - (m : ℤ) - 1 := by
        intro q
        apply Int.ceil_eq_iff.mpr
        dsimp [x] at hmle hmlt
        push_cast
        constructor <;> linarith
      have hflat : ∀ q : ℕ, (q : ℤ) ≤ ⌈ρ * (n : ℝ)⌉ - 1 ↔ (q : ℝ) < x := by
        intro q
        have h := (Int.lt_ceil (a := x) (z := (q : ℤ)))
        dsimp [x] at *
        constructor
        · intro hq; exact h.mp (by omega)
        · intro hq; have := h.mpr hq; omega
      have hP : ∀ q, Prho fmin ρ n q ≤ T q := by
        intro q
        unfold Prho
        simp only [hceil, hflat]
        change (if (q : ℝ) < x then fmin else fmin * b ^ ((q : ℤ) - (m : ℤ) - 1)) ≤ T q
        split_ifs with hq
        · dsimp [T]
          exact le_mul_of_one_le_right hfmin.le (one_le_pow₀ hb.le)
        · dsimp [T]
          rw [← zpow_natCast b (q - m)]
          apply mul_le_mul_of_nonneg_left _ hfmin.le
          apply zpow_le_zpow_right₀ hb.le
          omega
      have hPnext : ∀ q, m ≤ q → Prho fmin ρ n (q + 1) = T q := by
        intro q hq
        unfold Prho
        simp only [hceil, hflat]
        have hqx : ¬ ((q + 1 : ℕ) : ℝ) < x := by
          have hmq : (m : ℝ) ≤ q := by exact_mod_cast hq
          push_cast
          linarith
        rw [if_neg hqx]
        change fmin * b ^ (((q + 1 : ℕ) : ℤ) - (m : ℤ) - 1) = fmin * b ^ (q - m)
        rw [← zpow_natCast b (q - m)]
        congr 2
        omega
      have hPeq : ∀ q, q < m → Prho fmin ρ n q = T q := by
        intro q hq
        unfold Prho
        simp only [hflat]
        have hqx : (q : ℝ) < x := by
          have hqm : (q : ℝ) < m := by exact_mod_cast hq
          linarith
        rw [if_pos hqx]
        exact (hTflat q (Nat.le_of_lt hq)).symm
      have hpolicy : ∀ hist O, orderQtyPolicy fmin ρ n hist O = decide (T (acceptedCount hist) ≤ O) := by
        intro hist O
        unfold orderQtyPolicy
        congr 1
        apply propext
        constructor
        · intro h
          by_cases hq : m ≤ acceptedCount hist
          · simpa only [hPnext _ hq] using h.2
          · simpa only [hPeq _ (Nat.lt_of_not_ge hq)] using h.1
        · intro h
          constructor
          · exact le_trans (hP _) h
          · by_cases hq : m ≤ acceptedCount hist
            · simpa only [hPnext _ hq] using h
            · have hqm : acceptedCount hist + 1 ≤ m := by omega
              rw [hTflat _ (by omega)] at h
              exact le_trans (hP _) (by simpa only [hTflat _ hqm] using h)
      have hcount : ∀ hist O a, acceptedCount (hist ++ [(O, a)]) =
          if a then acceptedCount hist + 1 else acceptedCount hist := by
        intro hist O a
        cases a <;> simp [acceptedCount, List.filter_append]
      let R : List (ℝ × Bool) → ℕ → List ℝ → ℝ := fun hist u J =>
        (List.zipWith (fun O a => if a then O else 0) J
          (bpRunFrom n (orderQtyPolicy fmin ρ n) hist u J)).sum
      let E : ℝ → List ℝ → ℝ := fun t J => (J.map (fun O => max (O - t) 0)).sum
      have hRtrue : ∀ hist u O J,
          (decide (u < n) && orderQtyPolicy fmin ρ n hist O) = true →
          R hist u (O :: J) = O + R (hist ++ [(O, true)]) (u + 1) J := by
        intro hist u O J ha
        simp [R, bpRunFrom, ha]
      have hRfalse : ∀ hist u O J,
          (decide (u < n) && orderQtyPolicy fmin ρ n hist O) = false →
          R hist u (O :: J) = R (hist ++ [(O, false)]) u J := by
        intro hist u O J ha
        simp [R, bpRunFrom, ha]
      have hrun : ∀ (J : List ℝ) (hist : List (ℝ × Bool)) (u : ℕ),
          (∀ O ∈ J, fmin ≤ O ∧ O ≤ fmax) → acceptedCount hist = u → u ≤ n →
          ∃ q, u ≤ q ∧ q ≤ n ∧
            (q ≤ m → R hist u J = J.sum) ∧
            (∀ t : ℝ, T q ≤ t → (q = n → fmax ≤ t) →
              E t J + S q - S u ≤ R hist u J) := by
        intro J
        induction J with
        | nil =>
          intro hist u hJ hu hun
          refine ⟨u, le_rfl, hun, ?_, ?_⟩
          · intro h; simp [R, bpRunFrom]
          · intro t ht hnt; simp [R, bpRunFrom, E]
        | cons O J ih =>
          intro hist u hJ hu hun
          have hO := hJ O (by simp)
          have hJ' : ∀ O ∈ J, fmin ≤ O ∧ O ≤ fmax := fun O h => hJ O (by simp [h])
          by_cases hac : u < n ∧ T u ≤ O
          · have ha : (decide (u < n) && orderQtyPolicy fmin ρ n hist O) = true := by
              simpa only [hpolicy, hu, Bool.and_eq_true, decide_eq_true_eq] using hac
            have hcount' : acceptedCount (hist ++ [(O, true)]) = u + 1 := by simp [hcount, hu]
            obtain ⟨q, huq, hqn, hearly, hbound⟩ := ih (hist ++ [(O, true)]) (u + 1) hJ' hcount' (by omega)
            refine ⟨q, by omega, hqn, ?_, ?_⟩
            · intro hqm
              rw [hRtrue hist u O J ha, hearly hqm, List.sum_cons]
            · intro t ht hnt
              have htail := hbound t ht hnt
              have htu : T u ≤ t := le_trans (hTmono (by omega)) ht
              have hex : max (O - t) 0 ≤ O - T u := by
                apply max_le <;> linarith [hac.2]
              rw [hRtrue hist u O J ha]
              change max (O - t) 0 + E t J + S q - S u ≤ _
              rw [hSstep] at htail
              linarith
          · have ha : (decide (u < n) && orderQtyPolicy fmin ρ n hist O) = false := by
              apply Bool.eq_false_iff.mpr
              intro ha'
              apply hac
              simpa only [hpolicy, hu, Bool.and_eq_true, decide_eq_true_eq] using ha'
            have hcount' : acceptedCount (hist ++ [(O, false)]) = u := by simp [hcount, hu]
            obtain ⟨q, huq, hqn, hearly, hbound⟩ := ih (hist ++ [(O, false)]) u hJ' hcount' hun
            refine ⟨q, huq, hqn, ?_, ?_⟩
            · intro hqm
              have hum : u ≤ m := le_trans huq hqm
              have hut : u < n := lt_of_le_of_lt hum hmn
              have hprice : T u ≤ O := by rw [hTflat u hum]; exact hO.1
              exact False.elim (hac ⟨hut, hprice⟩)
            · intro t ht hnt
              have hot : O ≤ t := by
                by_cases hut : u < n
                · have hprice : O < T u := lt_of_not_ge (fun h => hac ⟨hut, h⟩)
                  exact le_trans hprice.le (le_trans (hTmono huq) ht)
                · have hqn' : q = n := by omega
                  exact le_trans hO.2 (hnt hqn')
              have hex : max (O - t) 0 = 0 := max_eq_right (sub_nonpos.mpr hot)
              rw [hRfalse hist u O J ha]
              simpa only [E, List.map_cons, List.sum_cons, hex, zero_add] using hbound t ht hnt
      have hsumindex : ∀ g : ℝ → ℝ, (∑ i : Fin I.length, g (I.get i)) = (I.map g).sum := by
        intro g
        rw [← List.sum_ofFn]
        change (List.ofFn (g ∘ I.get)).sum = _
        rw [← List.map_ofFn, List.ofFn_get]
      have hsumsub : ∀ J : Finset (Fin I.length), (∑ i ∈ J, I.get i) ≤ I.sum := by
        intro J
        calc
          (∑ i ∈ J, I.get i) ≤ ∑ i : Fin I.length, I.get i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i hi hni => le_trans hfmin.le (hI _ (I.get_mem i)).1)
          _ = I.sum := by simpa using hsumindex id
      have hoptempty : (0 : ℝ) ∈ {v : ℝ | ∃ J : Finset (Fin I.length), J.card ≤ n ∧ v = ∑ i ∈ J, I.get i} := by
        exact ⟨∅, by simp, by simp⟩
      have hoptall : bpOpt n I ≤ I.sum := by
        apply csSup_le ⟨0, hoptempty⟩
        rintro v ⟨J, hJn, rfl⟩
        exact hsumsub J
      have hopt0 : 0 ≤ bpOpt n I := by
        exact le_csSup ⟨I.sum, by rintro v ⟨J, hJn, rfl⟩; exact hsumsub J⟩ hoptempty
      have hdual : ∀ t : ℝ, 0 ≤ t → bpOpt n I ≤ (n : ℝ) * t + E t I := by
        intro t ht
        apply csSup_le ⟨0, hoptempty⟩
        rintro v ⟨J, hJn, rfl⟩
        calc
          (∑ i ∈ J, I.get i) ≤ ∑ i ∈ J, (t + max (I.get i - t) 0) := by
            apply Finset.sum_le_sum
            intro i hi
            linarith [le_max_left (I.get i - t) 0]
          _ = (J.card : ℝ) * t + ∑ i ∈ J, max (I.get i - t) 0 := by simp [Finset.sum_add_distrib]
          _ ≤ (n : ℝ) * t + ∑ i : Fin I.length, max (I.get i - t) 0 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hJn) ht
            · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i hi hni => le_max_right _ _)
          _ = (n : ℝ) * t + E t I := by rw [hsumindex (fun O => max (O - t) 0)]
      let a : ℝ := (fmin / fmax) ^ (-(ρ / (1 - ρ)))
      have ha0 : 0 < a := Real.rpow_pos_of_pos hr0 _
      have hloga : Real.log a = -(ρ / (1 - ρ)) * Real.log (fmin / fmax) := Real.log_rpow hr0 _
      have hLa : Real.log a < 1 := by
        have hh : ρ * (1 - Real.log (fmin / fmax)) < 1 :=
          (lt_div_iff₀ (by linarith : 0 < 1 - Real.log (fmin / fmax))).mp hρr
        have hid : (-(ρ / (1 - ρ)) * Real.log (fmin / fmax)) * (1 - ρ) =
            -ρ * Real.log (fmin / fmax) := by field_simp [hδ.ne', hρ.ne']
        rw [hloga]
        apply (mul_lt_mul_iff_left₀ hδ).mp
        rw [hid]
        nlinarith only [hh]
      have hGbdd : BddAbove {y : ℝ | 0 < y ∧ Gfun y ≤ a} := by
        refine ⟨Real.log a / (1 - Real.log a), ?_⟩
        intro y hy
        have hy0 : 0 < y := hy.1
        have hbase : 0 < 1 + 1 / y := by positivity
        have hg0 : 0 < Gfun y := Real.rpow_pos_of_pos hbase _
        have hlogupper : Real.log (Gfun y) ≤ Real.log a := Real.log_le_log hg0 hy.2
        have hloglower : y / (y + 1) ≤ Real.log (Gfun y) := by
          have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hbase)
          rw [Real.log_inv] at hh
          have hid : y * (1 - (1 + 1 / y)⁻¹) = y / (y + 1) := by
            field_simp [hy0.ne']
            ring
          rw [Gfun, Real.log_rpow hbase, ← hid]
          apply mul_le_mul_of_nonneg_left _ hy0.le
          linarith only [hh]
        have hmul : y ≤ Real.log a * (y + 1) :=
          (div_le_iff₀ (by positivity : 0 < y + 1)).mp (le_trans hloglower hlogupper)
        apply (le_div_iff₀ (by linarith only [hLa] : 0 < 1 - Real.log a)).mpr
        nlinarith only [hmul]
      have hGinv : Ginv a ≤ x := by
        have hh : (1 / ρ) * Ginv a ≤ (n : ℝ) := le_trans (le_max_right _ _) h20
        calc
          Ginv a = ρ * ((1 / ρ) * Ginv a) := by field_simp [hδ.ne', hρ.ne']
          _ ≤ ρ * (n : ℝ) := mul_le_mul_of_nonneg_left hh hρ.le
          _ = x := rfl
      have hGge : a ≤ Gfun x := by
        by_contra hnot
        have hlt : Gfun x < a := lt_of_not_ge hnot
        have hc : ContinuousAt Gfun x := by
          unfold Gfun
          apply ContinuousAt.rpow
          · exact continuousAt_const.add (continuousAt_const.div continuousAt_id hx.ne')
          · exact continuousAt_id
          · left; positivity
        have he1 : ∀ᶠ y : ℝ in nhds x, 0 < y :=
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x).eventually_lt continuousAt_id hx
        have he2 : ∀ᶠ y : ℝ in nhds x, Gfun y < a := hc.eventually_lt continuousAt_const hlt
        obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (he1.and he2)
        have hmid : (x + u) / 2 ∈ Set.Ioo l u := by constructor <;> linarith [hxu.1, hxu.2]
        have hy := hsub hmid
        have hmem : (x + u) / 2 ∈ {y : ℝ | 0 < y ∧ Gfun y ≤ a} := ⟨hy.1, hy.2.le⟩
        have hh : (x + u) / 2 ≤ Ginv a := le_csSup hGbdd hmem
        linarith only [hh, hGinv, hxu.2]
      have hTn : fmax ≤ T n := by
        have hlogG : -(ρ / (1 - ρ)) * Real.log (fmin / fmax) ≤ x * Real.log b := by
          have hh := Real.log_le_log ha0 hGge
          rw [hloga] at hh
          simpa only [Gfun, Real.log_rpow (by positivity : 0 < 1 + 1 / x)] using hh
        have hscale : -Real.log (fmin / fmax) ≤ ((1 - ρ) * (n : ℝ)) * Real.log b := by
          apply (mul_le_mul_iff_right₀ hρ).mp
          calc
            ρ * -Real.log (fmin / fmax) =
                (1 - ρ) * (-(ρ / (1 - ρ)) * Real.log (fmin / fmax)) := by field_simp [hδ.ne', hρ.ne']
            _ ≤ (1 - ρ) * (x * Real.log b) := mul_le_mul_of_nonneg_left hlogG hδ.le
            _ = ρ * (((1 - ρ) * (n : ℝ)) * Real.log b) := by dsimp [x]; ring
        have hexp : (1 - ρ) * (n : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
          rw [Nat.cast_sub hmn.le]
          dsimp [x] at hmle
          nlinarith only [hmle]
        have hmul := mul_le_mul_of_nonneg_right hexp (Real.log_nonneg hb.le)
        apply (Real.log_le_log_iff hfmax0 (hTpos n)).mp
        dsimp [T]
        rw [Real.log_mul hfmin.ne' (pow_ne_zero _ hb0.ne'), Real.log_pow]
        rw [Real.log_div hfmin.ne' hfmax0.ne'] at hscale
        linarith only [hscale, hmul]
      obtain ⟨q, hq0, hqn, hearly, hbound⟩ := hrun I [] 0 hI (by simp [acceptedCount]) (Nat.zero_le n)
      have hrunbound : E (T q) I + S q ≤ R [] 0 I := by
        have hh := hbound (T q) le_rfl (by intro hq; simpa only [hq] using hTn)
        simpa only [hS0, sub_zero] using hh
      have hE0 : 0 ≤ E (T q) I := by
        dsimp [E]
        apply List.sum_nonneg
        intro z hz
        obtain ⟨O, hO, rfl⟩ := List.mem_map.mp hz
        exact le_max_right _ _
      have hR0 : 0 ≤ R [] 0 I := by linarith only [hrunbound, hE0, hSnonneg q]
      let c : ℝ := ρ * (1 - 1 / (ρ * (x + 1)))
      have hceq : c = ρ - 1 / (x + 1) := by
        dsimp [c]
        field_simp
      have hc1 : c ≤ 1 := by
        rw [hceq]
        have hh : 0 < 1 / (x + 1) := by positivity
        linarith only [hρ1, hh]
      have hcN : c * (n : ℝ) ≤ x - 1 := by
        have hh : 1 ≤ (n : ℝ) / (x + 1) := (le_div_iff₀ (by positivity)).mpr (by simpa only [x, one_mul] using hnlarge)
        rw [hceq]
        calc
          (ρ - 1 / (x + 1)) * (n : ℝ) = x - (n : ℝ) / (x + 1) := by dsimp [x]; ring
          _ ≤ x - 1 := by linarith
      change c * bpOpt n I ≤ R [] 0 I
      by_cases hc0 : c ≤ 0
      · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc0 hopt0) hR0
      · have hcpos : 0 ≤ c := (lt_of_not_ge hc0).le
        by_cases hqm : q ≤ m
        · calc
            c * bpOpt n I ≤ 1 * bpOpt n I := mul_le_mul_of_nonneg_right hc1 hopt0
            _ ≤ R [] 0 I := by rw [hearly hqm, one_mul]; exact hoptall
        · have hsq : c * (n : ℝ) * T q ≤ S q :=
            le_trans (mul_le_mul_of_nonneg_right hcN (hTpos q).le) (hSratio q (by omega))
          calc
            c * bpOpt n I ≤ c * ((n : ℝ) * T q + E (T q) I) :=
              mul_le_mul_of_nonneg_left (hdual (T q) (hTpos q).le) hcpos
            _ = c * (n : ℝ) * T q + c * E (T q) I := by ring
            _ ≤ S q + E (T q) I := add_le_add hsq (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hE0)
            _ ≤ R [] 0 I := by simpa only [add_comm] using hrunbound
