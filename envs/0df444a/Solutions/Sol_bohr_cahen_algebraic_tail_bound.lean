-- Prove2me | solution 1 for bohr_cahen_algebraic_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T06:39:18.908702+00:00
-- url     : https://prove2.me/submissions/ec18bd68-a3d3-40bf-abef-c44f5ca2e5e8

import Mathlib
import Definitions.Def_timepiece_corrector
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (P : ℕ) (s s₀ : ℂ) (hs : s.re > s₀.re)
    (M_P : ℝ) (hM_nonneg : 0 ≤ M_P) :
    ∀ (ω : Ω_infty), (∀ N, ‖S_recip_random N P s₀ ω‖ ≤ M_P) →
    ∀ m N, 0 < m → m ≤ N →
      ‖∑ n ∈ Icc m N, ((μ n : ℂ) * X_mult n P ω) / (n ^ s)‖ ≤
      (M_P * (2 + ‖s - s₀‖ + ‖s - s₀‖ / (s.re - s₀.re))) *
        (m : ℝ) ^ (s₀.re - s.re) := by
          intro ω hω m N hm hN
          set S := fun k : ℕ => ∑ i ∈ Finset.Icc 1 k, (μ i : ℂ) * X_mult i P ω / (i : ℂ) ^ s₀
          have hS : ∀ k : ℕ, ‖S k‖ ≤ M_P := by
            aesop;
          -- We use Abel summation by parts for Dirichlet series tails.
          have h_abel : ∑ n ∈ Finset.Icc m N, (μ n : ℂ) * X_mult n P ω / (n : ℂ) ^ s = ∑ n ∈ Finset.Icc m N, (S n - S (n - 1)) * (n : ℂ) ^ (s₀ - s) := by
            refine' Finset.sum_congr rfl fun n hn => _;
            rcases n <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
            simp +zetaDelta at *;
            norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
            rw [ div_mul ];
            rw [ ← Complex.cpow_sub _ _ ( Nat.cast_add_one_ne_zero _ ) ] ; ring;
          -- We bound the sum using the triangle inequality and the fact that $|S_n| \leq M_P$.
          have h_bound : ‖∑ n ∈ Finset.Icc m N, (S n - S (n - 1)) * (n : ℂ) ^ (s₀ - s)‖ ≤ M_P * (‖(N : ℂ) ^ (s₀ - s)‖ + ‖(m : ℂ) ^ (s₀ - s)‖ + ∑ n ∈ Finset.Icc m (N - 1), ‖(n : ℂ) ^ (s₀ - s) - (n + 1 : ℂ) ^ (s₀ - s)‖) := by
            have h_bound : ∑ n ∈ Finset.Icc m N, (S n - S (n - 1)) * (n : ℂ) ^ (s₀ - s) = S N * (N : ℂ) ^ (s₀ - s) - S (m - 1) * (m : ℂ) ^ (s₀ - s) - ∑ n ∈ Finset.Icc m (N - 1), S n * ((n + 1 : ℂ) ^ (s₀ - s) - (n : ℂ) ^ (s₀ - s)) := by
              induction hN <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
              · ring;
              · erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] at *;
                any_goals linarith;
                rename_i k hk ih;
                refine' Nat.le_induction _ _ k hk <;> intros <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
                grind;
            rw [ h_bound ];
            refine' le_trans ( norm_sub_le _ _ ) ( le_trans ( add_le_add ( norm_sub_le _ _ ) ( norm_sum_le _ _ ) ) _ );
            norm_num [ mul_add, Finset.mul_sum _ _ _ ];
            exact add_le_add_three ( mul_le_mul_of_nonneg_right ( hS _ ) ( norm_nonneg _ ) ) ( mul_le_mul_of_nonneg_right ( hS _ ) ( norm_nonneg _ ) ) ( Finset.sum_le_sum fun i hi => by rw [ norm_sub_rev ] ; exact mul_le_mul_of_nonneg_right ( hS _ ) ( norm_nonneg _ ) );
          -- We bound the sum $\sum_{n=m}^{N-1} \|n^{s₀-s} - (n+1)^{s₀-s}\|$ using the mean value theorem.
          have h_mean_value : ∀ n : ℕ, m ≤ n → n < N → ‖(n : ℂ) ^ (s₀ - s) - (n + 1 : ℂ) ^ (s₀ - s)‖ ≤ ‖s - s₀‖ * (n : ℝ) ^ (s₀.re - s.re - 1) := by
            intro n hn hn'; have h_mean_value : ‖(n : ℂ) ^ (s₀ - s) - (n + 1 : ℂ) ^ (s₀ - s)‖ ≤ ‖s - s₀‖ * (n : ℝ) ^ (s₀.re - s.re - 1) := by
              have h_integral : (n : ℂ) ^ (s₀ - s) - (n + 1 : ℂ) ^ (s₀ - s) = ∫ t in (n : ℝ)..((n + 1) : ℝ), (s - s₀) * (t : ℂ) ^ (s₀ - s - 1) := by
                rw [ intervalIntegral.integral_const_mul, integral_cpow ] <;> norm_num;
                · rw [ mul_div, eq_div_iff ] <;> ring ; norm_num [ show s₀ - s ≠ 0 from sub_ne_zero_of_ne <| by rintro rfl; linarith ];
                · exact Or.inr ⟨ sub_ne_zero_of_ne <| by rintro rfl; linarith, by intros; linarith ⟩
              rw [ h_integral, intervalIntegral.integral_of_le ] <;> norm_num;
              refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) _;
              refine' le_trans ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun x hx => _ ) _;
              use fun x => ‖s - s₀‖ * x ^ (s₀.re - s.re - 1);
              · refine' ContinuousOn.integrableOn_Icc _ |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
                refine' ContinuousOn.norm _;
                refine' ContinuousOn.mul continuousOn_const _;
                exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.cpow ( Complex.continuous_ofReal.continuousAt ) continuousAt_const <| Or.inl <| by norm_cast; linarith [ hx.1, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ;
              · exact ( ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.mul continuousAt_const <| ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ) ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
              · norm_num [ Complex.norm_cpow_eq_rpow_re_of_pos ( show 0 < x by linarith [ hx.1 ] ) ];
              · rw [ ← intervalIntegral.integral_of_le ] <;> norm_num;
                rw [ intervalIntegral.integral_of_le ( by norm_num ) ];
                refine' mul_le_mul_of_nonneg_left _ ( norm_nonneg _ );
                refine' le_trans ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun x hx => Real.rpow_le_rpow_of_nonpos ( by linarith [ hx.1, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ) hx.1.le ( by linarith ) ) _ <;> norm_num;
                exact ( ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ) ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
            exact h_mean_value;
          -- We bound the sum $\sum_{n=m}^{N-1} n^{s₀.re - s.re - 1}$ using the integral test.
          have h_integral_test : ∑ n ∈ Finset.Icc m (N - 1), (n : ℝ) ^ (s₀.re - s.re - 1) ≤ (m : ℝ) ^ (s₀.re - s.re - 1) + ∫ x in (m : ℝ)..N, x ^ (s₀.re - s.re - 1) := by
            have h_integral_test : ∀ n : ℕ, m ≤ n → n < N → (n + 1 : ℝ) ^ (s₀.re - s.re - 1) ≤ ∫ x in (n : ℝ).. (n + 1 : ℝ), x ^ (s₀.re - s.re - 1) := by
              intros n hn hnN
              have h_integral_bound : ∀ x ∈ Set.Icc (n : ℝ) (n + 1), x ^ (s₀.re - s.re - 1) ≥ (n + 1 : ℝ) ^ (s₀.re - s.re - 1) := by
                intros x hx;
                rw [ ge_iff_le, Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hx.1, hx.2, show ( n : ℝ ) ≥ 1 by norm_cast; linarith ];
              refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_integral_bound ) <;> norm_num;
              apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
              exact Or.inr fun h => by linarith;
            have h_integral_test_sum : ∑ n ∈ Finset.Icc (m + 1) N, (n : ℝ) ^ (s₀.re - s.re - 1) ≤ ∫ x in (m : ℝ)..N, x ^ (s₀.re - s.re - 1) := by
              have h_integral_test_sum : ∑ n ∈ Finset.Icc (m + 1) N, (n : ℝ) ^ (s₀.re - s.re - 1) ≤ ∑ n ∈ Finset.Icc (m) (N - 1), ∫ x in (n : ℝ).. (n + 1 : ℝ), x ^ (s₀.re - s.re - 1) := by
                erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
                simp +zetaDelta at *;
                rw [ Nat.sub_add_cancel ( by linarith ) ];
                exact Finset.sum_le_sum fun i hi => by convert h_integral_test ( m + i ) ( by linarith ) ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel hN ] ) using 1 <;> push_cast <;> first | ring | rfl;
              convert h_integral_test_sum using 1;
              erw [ Finset.sum_Ico_eq_sum_range ];
              symm;
              convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
              · ring;
              · omega;
              · intro k hk; apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
                exact Or.inr fun h => by linarith [ show ( m : ℝ ) ≥ 1 by norm_cast ] ;
            erw [ Finset.sum_Ico_eq_sub _ _ ] at * <;> norm_num at *;
            · rw [ Nat.sub_add_cancel ( by linarith ) ];
              norm_num [ Finset.sum_range_succ ] at * ; linarith [ show ( 0 : ℝ ) ≤ ( N : ℝ ) ^ ( s₀.re - s.re - 1 ) by exact Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ] ;
            · linarith;
            · linarith;
            · linarith;
            · omega;
          -- We bound the integral $\int_{m}^{N} x^{s₀.re - s.re - 1} \, dx$.
          have h_integral_bound : ∫ x in (m : ℝ)..N, x ^ (s₀.re - s.re - 1) ≤ (m : ℝ) ^ (s₀.re - s.re) / (s.re - s₀.re) := by
            rw [ integral_rpow ] <;> norm_num;
            · rw [ ← neg_div_neg_eq ] ; ring_nf ; norm_num;
              exact mul_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( inv_nonneg.mpr ( by linarith ) );
            · exact Or.inr ⟨ by linarith, Set.notMem_uIcc_of_lt ( by norm_num; linarith ) ( by norm_num; linarith ) ⟩;
          -- We bound the terms $\|N^{s₀-s}\|$ and $\|m^{s₀-s}\|$.
          have h_term_bounds : ‖(N : ℂ) ^ (s₀ - s)‖ ≤ (m : ℝ) ^ (s₀.re - s.re) ∧ ‖(m : ℂ) ^ (s₀ - s)‖ ≤ (m : ℝ) ^ (s₀.re - s.re) := by
            constructor <;> rw [ Complex.norm_cpow_of_ne_zero ] <;> norm_num [ hm.ne', show N ≠ 0 by linarith ];
            rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith [ show ( m : ℝ ) ≥ 1 by norm_cast, show ( N : ℝ ) ≥ m by norm_cast ];
          -- We combine the bounds to conclude the proof.
          have h_combined : ‖∑ n ∈ Finset.Icc m N, (S n - S (n - 1)) * (n : ℂ) ^ (s₀ - s)‖ ≤ M_P * (2 * (m : ℝ) ^ (s₀.re - s.re) + ‖s - s₀‖ * ((m : ℝ) ^ (s₀.re - s.re - 1) + (m : ℝ) ^ (s₀.re - s.re) / (s.re - s₀.re))) := by
            refine le_trans h_bound ?_;
            refine' mul_le_mul_of_nonneg_left _ hM_nonneg;
            refine' le_trans ( add_le_add_three h_term_bounds.1 h_term_bounds.2 ( Finset.sum_le_sum fun n hn => h_mean_value n ( Finset.mem_Icc.mp hn |>.1 ) ( Finset.mem_Icc.mp hn |>.2.trans_lt ( Nat.pred_lt ( ne_bot_of_gt ( show 0 < N from by linarith ) ) ) ) ) ) _;
            rw [ ← Finset.mul_sum _ _ _ ] ; nlinarith [ norm_nonneg ( s - s₀ ) ] ;
          have h_key : ‖∑ n ∈ Finset.Icc m N, (μ n : ℂ) * X_mult n P ω / (n : ℂ) ^ s‖
              = ‖∑ n ∈ Finset.Icc m N, (S n - S (n - 1)) * (n : ℂ) ^ (s₀ - s)‖ := by
            rw [h_abel]
          have h_last : M_P * (2 * (m : ℝ) ^ (s₀.re - s.re) + ‖s - s₀‖ * ((m : ℝ) ^ (s₀.re - s.re - 1)
                + (m : ℝ) ^ (s₀.re - s.re) / (s.re - s₀.re)))
              ≤ (M_P * (2 + ‖s - s₀‖ + ‖s - s₀‖ / (s.re - s₀.re))) * (m : ℝ) ^ (s₀.re - s.re) := by
            have h1 : (m : ℝ) ^ (s₀.re - s.re - 1) ≤ (m : ℝ) ^ (s₀.re - s.re) :=
              Real.rpow_le_rpow_of_exponent_le (by have := Nat.succ_le_of_lt hm; exact_mod_cast this)
                (sub_le_self _ (by norm_num))
            have h2 : (0 : ℝ) ≤ ‖s - s₀‖ * ((m : ℝ) ^ (s₀.re - s.re) - (m : ℝ) ^ (s₀.re - s.re - 1)) :=
              mul_nonneg (norm_nonneg (s - s₀)) (sub_nonneg.mpr h1)
            have h4 : (0 : ℝ) ≤ ‖s - s₀‖ * (m : ℝ) ^ (s₀.re - s.re) - ‖s - s₀‖ * (m : ℝ) ^ (s₀.re - s.re - 1) := by
              linarith [h2]
            rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ hM_nonneg
            simp only [add_mul, mul_div_assoc, div_mul_eq_mul_div]
            linarith
          rw [h_key]
          exact le_trans h_combined h_last
