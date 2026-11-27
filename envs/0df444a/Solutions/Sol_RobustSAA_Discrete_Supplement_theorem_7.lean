-- Prove2me | solution 1 for RobustSAA.Discrete.Supplement.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:28.433401+00:00
-- url     : https://prove2.me/submissions/b477677b-1760-4b32-82f6-e533f7266693

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_LCX

open RobustSAA
open RobustSAA.Discrete
open RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Convergence

theorem solution {d : ℕ} (Ξ : Set (Pt d)) (hΞ : IsClosed Ξ) (hbdd : Bornology.IsBounded Ξ)
    (QC QR : ℕ → ℝ) (hQC : Tendsto QC atTop (𝓝 0)) (hQR : Tendsto QR atTop (𝓝 0)) :
    IsUniformlyConsistent (lcxDUS (Ξ := Ξ) QC QR) := by
      classical
      have hcs : CompactSpace ↥Ξ :=
        isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded hΞ hbdd)
      obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ ξ : ↥Ξ, ‖(ξ : Pt d)‖ ≤ R := by
        obtain ⟨R, hR⟩ := hbdd.exists_norm_le
        exact ⟨max R 0, le_max_right _ _, fun ξ => (hR _ ξ.2).trans (le_max_left _ _)⟩
      have hint : ∀ (μ : Measure ↥Ξ) [IsFiniteMeasure μ] (f : ↥Ξ → ℝ), Continuous f → Integrable f μ := by
        intro μ _ f hf
        have := hf.continuousOn.integrableOn_compact (μ := μ) (K := Set.univ) isCompact_univ
        simpa [IntegrableOn] using this
      have hhc2 : ∀ a : Pt d, Continuous (Function.uncurry fun (b : ℝ) (ξ : ↥Ξ) => hinge a b (ξ : Pt d)) := by
        intro a
        unfold hinge Function.uncurry
        fun_prop
      have hhc : ∀ (a : Pt d) (b : ℝ), Continuous (fun ξ : ↥Ξ => hinge a b (ξ : Pt d)) := by
        intro a b
        unfold hinge
        fun_prop
      -- the class of functions on which G is asymptotically dominated by P
      obtain ⟨S, hS⟩ : ∃ S : (↥Ξ → ℝ) → Prop, ∀ f, S f ↔ (Continuous f ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∀ (G P : Measure ↥Ξ) [IsProbabilityMeasure G] [IsProbabilityMeasure P] (q r : ℝ),
            0 ≤ q → 0 ≤ r →
            (∀ (a : Pt d) (b : ℝ), l1norm a + |b| ≤ 1 →
              ∫ ξ, hinge a b (ξ : Pt d) ∂G ≤ ∫ ξ, hinge a b (ξ : Pt d) ∂P + q) →
            (∫ ξ, ‖(ξ : Pt d)‖ ^ 2 ∂P - r ≤ ∫ ξ, ‖(ξ : Pt d)‖ ^ 2 ∂G) →
            ∫ ξ, f ξ ∂G ≤ ∫ ξ, f ξ ∂P + C * (q + r)) := ⟨_, fun _ => Iff.rfl⟩
      have S_add : ∀ f g, S f → S g → S (fun ξ => f ξ + g ξ) := by
        intro f g hf hg
        rw [hS] at *
        obtain ⟨cf, C, hC, hf⟩ := hf
        obtain ⟨cg, D, hD, hg⟩ := hg
        refine ⟨cf.add cg, C + D, add_nonneg hC hD, ?_⟩
        intro G P _ _ q r hq hr h1 h2
        rw [integral_add (hint _ _ cf) (hint _ _ cg), integral_add (hint _ _ cf) (hint _ _ cg)]
        have := hf G P q r hq hr h1 h2
        have := hg G P q r hq hr h1 h2
        nlinarith
      have S_smul : ∀ (c : ℝ) f, 0 ≤ c → S f → S (fun ξ => c * f ξ) := by
        intro c f hc hf
        rw [hS] at *
        obtain ⟨cf, C, hC, hf⟩ := hf
        refine ⟨continuous_const.mul cf, c * C, mul_nonneg hc hC, ?_⟩
        intro G P _ _ q r hq hr h1 h2
        rw [integral_const_mul, integral_const_mul]
        have := mul_le_mul_of_nonneg_left (hf G P q r hq hr h1 h2) hc
        linarith
      have S_const : ∀ c : ℝ, S (fun _ => c) := by
        intro c
        rw [hS]
        refine ⟨continuous_const, 0, le_rfl, ?_⟩
        intro G P _ _ q r hq hr h1 h2
        simp
      have S_sum : ∀ (s : Finset (Fin d)) (f : Fin d → ↥Ξ → ℝ), (∀ i, S (f i)) →
          S (fun ξ => ∑ i ∈ s, f i ξ) := by
        intro s f hf
        induction s using Finset.induction_on with
        | empty => simpa using S_const 0
        | insert i s hi ih =>
          simp only [Finset.sum_insert hi]
          exact S_add _ _ (hf i) ih
      -- scaled hinge bound
      have hinge_all : ∀ (G P : Measure ↥Ξ) (q : ℝ), (∀ (a : Pt d) (b : ℝ), l1norm a + |b| ≤ 1 →
              ∫ ξ, hinge a b (ξ : Pt d) ∂G ≤ ∫ ξ, hinge a b (ξ : Pt d) ∂P + q) →
              ∀ (a : Pt d) (b : ℝ), ∫ ξ, hinge a b (ξ : Pt d) ∂G ≤
                ∫ ξ, hinge a b (ξ : Pt d) ∂P + (l1norm a + |b| + 1) * q := by
        intro G P q h a b
        have hl : 0 ≤ l1norm a := Finset.sum_nonneg fun _ _ => abs_nonneg _
        set c : ℝ := l1norm a + |b| + 1 with hc
        have hcpos : 0 < c := by have := abs_nonneg b; linarith
        have hscale : ∀ ξ : Pt d, hinge (c⁻¹ • a) (c⁻¹ * b) ξ = c⁻¹ * hinge a b ξ := by
          intro ξ
          unfold hinge
          rw [real_inner_smul_left, ← mul_sub, mul_max_of_nonneg _ _ (inv_nonneg.mpr hcpos.le), mul_zero]
        have hle : l1norm (c⁻¹ • a) + |c⁻¹ * b| ≤ 1 := by
          have e1 : l1norm (c⁻¹ • a) = c⁻¹ * l1norm a := by
            unfold l1norm
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp [abs_mul, abs_of_pos hcpos]
          rw [e1, abs_mul, abs_of_pos (inv_pos.mpr hcpos), ← mul_add, inv_mul_le_iff₀ hcpos]
          linarith
        have := h _ _ hle
        simp only [hscale, integral_const_mul] at this
        have h3 := mul_le_mul_of_nonneg_left this hcpos.le
        rw [mul_add, mul_inv_cancel_left₀ hcpos.ne', mul_inv_cancel_left₀ hcpos.ne'] at h3
        exact h3
      have S_hinge : ∀ (a : Pt d) (b : ℝ), S (fun ξ => hinge a b (ξ : Pt d)) := by
        intro a b
        rw [hS]
        have hl : 0 ≤ l1norm a := Finset.sum_nonneg fun _ _ => abs_nonneg _
        refine ⟨hhc a b, l1norm a + |b| + 1, by positivity, ?_⟩
        intro G P _ _ q r hq hr h1 h2
        have := hinge_all G P q h1 a b
        have : 0 ≤ (l1norm a + |b| + 1) * r := by positivity
        linarith
      have S_ridge : ∀ (a : Pt d) (M : ℝ) (w : ℝ → ℝ), 0 ≤ M → Continuous w →
          (∀ b, b ≤ M → 0 ≤ w b) →
          S (fun ξ => ∫ b in (-M)..M, w b * hinge a b (ξ : Pt d)) := by
        intro a M w hM hw hw0
        rw [hS]
        have hl : 0 ≤ l1norm a := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have hW : 0 ≤ ∫ b in (-M)..M, w b :=
          intervalIntegral.integral_nonneg (by linarith) fun u hu => hw0 u hu.2
        have hu : Continuous (Function.uncurry fun (b : ℝ) (ξ : ↥Ξ) => w b * hinge a b (ξ : Pt d)) :=
          (hw.comp continuous_fst).mul (hhc2 a)
        refine ⟨?_, (∫ b in (-M)..M, w b) * (l1norm a + M + 1), by positivity, ?_⟩
        · refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
          exact hu.comp continuous_swap
        intro G P _ _ q r hq hr h1 h2
        have hswap : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ],
            ∫ ξ, (∫ b in (-M)..M, w b * hinge a b (ξ : Pt d)) ∂μ =
              ∫ b in (-M)..M, w b * ∫ ξ, hinge a b (ξ : Pt d) ∂μ := by
          intro μ _
          simp only [← integral_const_mul]
          refine (intervalIntegral_integral_swap ?_).symm
          have h3 : IntegrableOn (Function.uncurry fun (b : ℝ) (ξ : ↥Ξ) => w b * hinge a b (ξ : Pt d))
              (Set.Icc (-M) M ×ˢ Set.univ) ((volume : Measure ℝ).prod μ) :=
            hu.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_univ)
          have h4 := h3.mono_set (s := Set.uIoc (-M) M ×ˢ Set.univ) (by
            refine Set.prod_mono ?_ le_rfl
            rw [Set.uIoc_of_le (by linarith)]
            exact Set.Ioc_subset_Icc_self)
          rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h4
          exact h4
        have hcont : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ],
            Continuous fun b : ℝ => ∫ ξ, hinge a b (ξ : Pt d) ∂μ := by
          intro μ _
          have := continuous_parametric_integral_of_continuous (μ := μ) (hhc2 a) isCompact_univ
          simpa using this
        rw [hswap G, hswap P]
        have hmono : ∫ b in (-M)..M, w b * ∫ ξ, hinge a b (ξ : Pt d) ∂G ≤
            ∫ b in (-M)..M, (w b * ∫ ξ, hinge a b (ξ : Pt d) ∂P + w b * ((l1norm a + M + 1) * q)) := by
          refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
          · exact (hw.mul (hcont G)).intervalIntegrable _ _
          · exact ((hw.mul (hcont P)).add (hw.mul continuous_const)).intervalIntegrable _ _
          · intro b hb
            rw [← mul_add]
            refine mul_le_mul_of_nonneg_left ?_ (hw0 b hb.2)
            refine (hinge_all G P q h1 a b).trans ?_
            have : |b| ≤ M := abs_le.mpr hb
            have : (l1norm a + |b| + 1) * q ≤ (l1norm a + M + 1) * q :=
              mul_le_mul_of_nonneg_right (by linarith) hq
            linarith
        have hsplit : ∫ b in (-M)..M, (w b * ∫ ξ, hinge a b (ξ : Pt d) ∂P + w b * ((l1norm a + M + 1) * q)) =
            (∫ b in (-M)..M, w b * ∫ ξ, hinge a b (ξ : Pt d) ∂P) +
              ∫ b in (-M)..M, w b * ((l1norm a + M + 1) * q) :=
          intervalIntegral.integral_add ((hw.mul (hcont P)).intervalIntegrable _ _)
            ((hw.mul continuous_const).intervalIntegrable _ _)
        rw [hsplit, intervalIntegral.integral_mul_const] at hmono
        have : 0 ≤ (∫ b in (-M)..M, w b) * (l1norm a + M + 1) * r := by positivity
        linarith
      have hFTC : ∀ (M t : ℝ) (w F : ℝ → ℝ), -M ≤ t → t ≤ M → Continuous w →
          (∀ b, HasDerivAt F (w b * (t - b)) b) →
          ∫ b in (-M)..M, w b * max (t - b) 0 = F t - F (-M) := by
        intro M t w F h1 h2 hw hF
        have hc : Continuous fun b => w b * max (t - b) 0 := by fun_prop
        rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-M) t)
          (hc.intervalIntegrable t M)]
        have e1 : ∫ b in (-M)..t, w b * max (t - b) 0 = ∫ b in (-M)..t, w b * (t - b) := by
          refine intervalIntegral.integral_congr fun b hb => ?_
          rw [Set.uIcc_of_le h1] at hb
          rw [max_eq_left (by linarith [hb.2])]
        have e2 : ∫ b in t..M, w b * max (t - b) 0 = 0 := by
          have : ∫ b in t..M, w b * max (t - b) 0 = ∫ b in t..M, (0 : ℝ) := by
            refine intervalIntegral.integral_congr fun b hb => ?_
            rw [Set.uIcc_of_le h2] at hb
            rw [max_eq_right (by linarith [hb.1]), mul_zero]
          rw [this]; simp
        rw [e1, e2, add_zero]
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun b _ => hF b) ?_
        have : Continuous fun b => w b * (t - b) := by fun_prop
        exact this.intervalIntegrable _ _
      have hM : ∀ (a : Pt d) (ξ : ↥Ξ), -(‖a‖ * R) ≤ inner ℝ a (ξ : Pt d) ∧
          inner ℝ a (ξ : Pt d) ≤ ‖a‖ * R := by
        intro a ξ
        rw [← abs_le]
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hR ξ) (norm_nonneg _))
      have hM0 : ∀ a : Pt d, 0 ≤ ‖a‖ * R := fun a => mul_nonneg (norm_nonneg _) hR0
      have S_lin : ∀ a : Pt d, S (fun ξ => inner ℝ a (ξ : Pt d)) := by
        intro a
        have := S_add _ _ (S_hinge a (-(‖a‖ * R))) (S_const (-(‖a‖ * R)))
        convert this using 2 with ξ
        unfold hinge
        rw [max_eq_left (by linarith [(hM a ξ).1])]
        ring
      have S_sq : ∀ a : Pt d, S (fun ξ => (inner ℝ a (ξ : Pt d)) ^ 2) := by
        intro a
        have := S_add _ _ (S_add _ _ (S_ridge a (‖a‖ * R) (fun _ => 2) (hM0 a) continuous_const
          (fun _ _ => by norm_num)) (S_lin ((-2 * (‖a‖ * R)) • a))) (S_const (-(‖a‖ * R) ^ 2))
        convert this using 2 with ξ
        unfold hinge
        rw [hFTC (‖a‖ * R) (inner ℝ a (ξ : Pt d)) (fun _ => 2)
          (fun b => -(inner ℝ a (ξ : Pt d) - b) ^ 2) (hM a ξ).1 (hM a ξ).2 continuous_const ?_]
        · rw [real_inner_smul_left]
          ring
        · intro b
          have := (((hasDerivAt_id b).const_sub (inner ℝ a (ξ : Pt d))).pow 2).neg
          refine this.congr_deriv ?_
          simp
      have hderexp : ∀ t b : ℝ, HasDerivAt (fun b => Real.exp b * (t - b + 1)) (Real.exp b * (t - b)) b := by
        intro t b
        have := (Real.hasDerivAt_exp b).mul (((hasDerivAt_id b).const_sub t).add_const 1)
        refine this.congr_deriv ?_
        simp
        ring
      have S_exp : ∀ a : Pt d, S (fun ξ => Real.exp (inner ℝ a (ξ : Pt d))) := by
        intro a
        have := S_add _ _ (S_add _ _ (S_ridge a (‖a‖ * R) Real.exp (hM0 a) Real.continuous_exp
          (fun _ _ => (Real.exp_pos _).le)) (S_lin ((Real.exp (-(‖a‖ * R))) • a)))
          (S_const (Real.exp (-(‖a‖ * R)) * (‖a‖ * R + 1)))
        convert this using 2 with ξ
        unfold hinge
        rw [hFTC (‖a‖ * R) (inner ℝ a (ξ : Pt d)) Real.exp
          _ (hM a ξ).1 (hM a ξ).2 Real.continuous_exp (hderexp _)]
        rw [real_inner_smul_left]
        ring
      have S_mexp : ∀ a : Pt d, S (fun ξ => Real.exp (‖a‖ * R) * (inner ℝ a (ξ : Pt d)) ^ 2 -
          Real.exp (inner ℝ a (ξ : Pt d))) := by
        intro a
        set K := Real.exp (‖a‖ * R) with hK
        have hKpos : 0 < K := Real.exp_pos _
        have := S_add _ _ (S_add _ _ (S_ridge a (‖a‖ * R) (fun b => 2 * K - Real.exp b) (hM0 a)
          (by fun_prop)
          (fun b hb => by have := Real.exp_le_exp.mpr hb; linarith))
          (S_lin ((-2 * K * (‖a‖ * R) - Real.exp (-(‖a‖ * R))) • a)))
          (S_const (-K * (‖a‖ * R) ^ 2 - Real.exp (-(‖a‖ * R)) * (‖a‖ * R + 1)))
        convert this using 2 with ξ
        unfold hinge
        rw [hFTC (‖a‖ * R) (inner ℝ a (ξ : Pt d)) (fun b => 2 * K - Real.exp b)
          (fun b => -K * (inner ℝ a (ξ : Pt d) - b) ^ 2 -
            Real.exp b * (inner ℝ a (ξ : Pt d) - b + 1)) (hM a ξ).1 (hM a ξ).2 (by fun_prop) ?_]
        · rw [real_inner_smul_left]
          ring
        · intro b
          have := ((((hasDerivAt_id b).const_sub (inner ℝ a (ξ : Pt d))).pow 2).const_mul (-K)).sub
            (hderexp (inner ℝ a (ξ : Pt d)) b)
          refine this.congr_deriv ?_
          simp
          ring
      have S_cross : ∀ a : Pt d, S (fun ξ => ‖a‖ ^ 2 * ‖(ξ : Pt d)‖ ^ 2 - (inner ℝ a (ξ : Pt d)) ^ 2) := by
        intro a
        have := S_smul (1 / 2) _ (by norm_num) (S_sum Finset.univ _ fun i => S_sum Finset.univ _ fun j =>
          S_sq (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)))
        convert this using 2 with ξ
        have e1 : ‖a‖ ^ 2 = ∑ i, a i ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]; simp
        have e2 : ‖(ξ : Pt d)‖ ^ 2 = ∑ i, (ξ : Pt d) i ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]; simp
        have e3 : inner ℝ a (ξ : Pt d) = ∑ i, a i * (ξ : Pt d) i := by
          rw [PiLp.inner_apply]; simp [mul_comm]
        have e4 : ∀ i j, inner ℝ (a i • EuclideanSpace.single j (1 : ℝ) - a j • EuclideanSpace.single i (1 : ℝ)) (ξ : Pt d)
            = a i * (ξ : Pt d) j - a j * (ξ : Pt d) i := by
          intro i j
          rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
            EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
          simp
        simp only [e4]
        have e5 : ∀ i j, (a i * (ξ : Pt d) j - a j * (ξ : Pt d) i) ^ 2 =
            a i ^ 2 * (ξ : Pt d) j ^ 2 + (ξ : Pt d) i ^ 2 * a j ^ 2
              - 2 * ((a i * (ξ : Pt d) i) * (a j * (ξ : Pt d) j)) := by
          intro i j; ring
        simp only [e5, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [e1, e2, e3]
        ring
      have S_mnorm : S (fun ξ => -‖(ξ : Pt d)‖ ^ 2) := by
        rw [hS]
        refine ⟨by fun_prop, 1, by norm_num, ?_⟩
        intro G P _ _ q r hq hr h1 h2
        rw [integral_neg, integral_neg]
        linarith
      have S_nexp : ∀ a : Pt d, S (fun ξ => -Real.exp (inner ℝ a (ξ : Pt d))) := by
        intro a
        have hKpos : 0 ≤ Real.exp (‖a‖ * R) := (Real.exp_pos _).le
        have := S_add _ _ (S_mexp a) (S_add _ _ (S_smul _ _ hKpos (S_cross a))
          (S_smul (Real.exp (‖a‖ * R) * ‖a‖ ^ 2) _ (by positivity) S_mnorm))
        convert this using 2 with ξ
        ring
      -- exponential estimate
      have key : ∀ a : Pt d, ∃ C : ℝ, 0 ≤ C ∧
          ∀ (G P : Measure ↥Ξ) [IsProbabilityMeasure G] [IsProbabilityMeasure P] (q r : ℝ),
            0 ≤ q → 0 ≤ r →
            (∀ (a : Pt d) (b : ℝ), l1norm a + |b| ≤ 1 →
              ∫ ξ, hinge a b (ξ : Pt d) ∂G ≤ ∫ ξ, hinge a b (ξ : Pt d) ∂P + q) →
            (∫ ξ, ‖(ξ : Pt d)‖ ^ 2 ∂P - r ≤ ∫ ξ, ‖(ξ : Pt d)‖ ^ 2 ∂G) →
            |∫ ξ, Real.exp (inner ℝ a (ξ : Pt d)) ∂G - ∫ ξ, Real.exp (inner ℝ a (ξ : Pt d)) ∂P|
              ≤ C * (q + r) := by
        intro a
        obtain ⟨-, C, hC, h⟩ := (hS _).1 (S_exp a)
        obtain ⟨-, D, hD, h'⟩ := (hS _).1 (S_nexp a)
        refine ⟨C + D, add_nonneg hC hD, ?_⟩
        intro G P _ _ q r hq hr h1 h2
        have k1 := h G P q r hq hr h1 h2
        have k2 := h' G P q r hq hr h1 h2
        rw [integral_neg, integral_neg] at k2
        have : 0 ≤ C * (q + r) := by positivity
        have : 0 ≤ D * (q + r) := by positivity
        rw [abs_le]
        constructor <;> linarith
      intro F
      obtain ⟨av, hav⟩ : ∃ av : (Fin d → ℕ) → Pt d, ∀ n i, av n i = (n i : ℝ) :=
        ⟨fun n => WithLp.toLp 2 fun i => (n i : ℝ), fun n i => rfl⟩
      have hSL : ∀ f : ↥Ξ → ℝ, Continuous f → ∀ᵐ ω ∂(dataLaw F),
          Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, f (ω i)) / N) atTop
            (𝓝 (∫ ξ, f ξ ∂(F : Measure ↥Ξ))) := by
        intro f hf
        have hmp : ∀ i : ℕ, MeasurePreserving (Function.eval i) (dataLaw F) (F : Measure ↥Ξ) :=
          fun i => measurePreserving_eval_infinitePi (fun _ : ℕ => (F : Measure ↥Ξ)) i
        have hiF : Integrable f (F : Measure ↥Ξ) := hint _ _ hf
        have h := ProbabilityTheory.strong_law_ae_real (μ := dataLaw F) (fun (i : ℕ) (ω : ℕ → ↥Ξ) => f (ω i))
          ((hmp 0).integrable_comp_of_integrable hiF) ?_ ?_
        · have e : ∫ ω, f (ω 0) ∂(dataLaw F) = ∫ ξ, f ξ ∂(F : Measure ↥Ξ) := by
            rw [← (hmp 0).map_eq, integral_map (hmp 0).measurable.aemeasurable
              hf.measurable.aestronglyMeasurable]
          rw [e] at h
          exact h
        · have hI := ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => (F : Measure ↥Ξ))
            (X := fun _ : ℕ => f) (fun _ => hf.measurable)
          intro i j hij
          exact hI.indepFun hij
        · intro i
          refine ⟨(hf.measurable.comp (hmp i).measurable).aemeasurable,
            (hf.measurable.comp (hmp 0).measurable).aemeasurable, ?_⟩
          have e : ∀ i : ℕ, Measure.map (fun ω : ℕ → ↥Ξ => f (ω i)) (dataLaw F) =
              Measure.map f (F : Measure ↥Ξ) := by
            intro i
            rw [← (hmp i).map_eq, Measure.map_map hf.measurable (hmp i).measurable]
            rfl
          rw [e i, e 0]
      have hcexp : ∀ a : Pt d, Continuous fun ξ : ↥Ξ => Real.exp (inner ℝ a (ξ : Pt d)) := by
        intro a; fun_prop
      have hae := (ae_all_iff (μ := dataLaw F)).2 fun n : Fin d → ℕ => hSL _ (hcexp (av n))
      filter_upwards [hae] with ω hω
      intro G hG hfreq
      apply hG
      simp only [not_not] at hfreq
      -- convergence on exponentials
      have hexp : ∀ n : Fin d → ℕ, Tendsto (fun N => ∫ ξ, Real.exp (inner ℝ (av n) (ξ : Pt d)) ∂(G N : Measure ↥Ξ))
          atTop (𝓝 (∫ ξ, Real.exp (inner ℝ (av n) (ξ : Pt d)) ∂(F : Measure ↥Ξ))) := by
        intro n
        obtain ⟨C, hC, hk⟩ := key (av n)
        have hb : ∀ᶠ N in atTop, |∫ ξ, Real.exp (inner ℝ (av n) (ξ : Pt d)) ∂(G N : Measure ↥Ξ) -
            (∑ i ∈ Finset.range N, Real.exp (inner ℝ (av n) (ω i : Pt d))) / N| ≤ C * (|QC N| + |QR N|) := by
          filter_upwards [hfreq, eventually_ge_atTop 1] with N hN hN1
          obtain ⟨hc1, hc2⟩ := hN
          have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
          obtain ⟨P, hP⟩ : ∃ P : Measure ↥Ξ, P = (N : ENNReal)⁻¹ • ∑ i ∈ Finset.range N, Measure.dirac (ω i) :=
            ⟨_, rfl⟩
          have hPp : IsProbabilityMeasure P := by
            constructor
            rw [hP]
            simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
              Finset.sum_const, Finset.card_range, smul_eq_mul, nsmul_eq_mul, mul_one]
            exact ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : N ≠ 0)) (ENNReal.natCast_ne_top N)
          have hPi : ∀ f : ↥Ξ → ℝ, Continuous f → ∫ ξ, f ξ ∂P = (∑ i ∈ Finset.range N, f (ω i)) / N := by
            intro f hf
            rw [hP, integral_smul_measure, integral_finsetSum_measure]
            · simp [div_eq_inv_mul]
            · intro i _
              exact hint _ _ hf
          rw [← hPi _ (hcexp (av n))]
          have hsum : ∀ f : ↥Ξ → ℝ, Continuous f → (1 / (N : ℝ)) * ∑ i, f (sample ω N i) = ∫ ξ, f ξ ∂P := by
            intro f hf
            rw [hPi f hf, Finset.sum_range, one_div, div_eq_inv_mul]
            rfl
          refine hk (G N : Measure ↥Ξ) P _ _ (abs_nonneg _) (abs_nonneg _) ?_ ?_
          · intro a b hab
            have h1 : ((hingeMean (G N) a b : ENNReal) : EReal) -
              (((1 / (N : ℝ)) * ∑ i, hinge a b ((sample ω N i : ↥Ξ) : Pt d) : ℝ) : EReal) ≤ (QC N : EReal) := by
              refine le_trans ?_ hc1
              unfold lcxStat
              exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl))
            have h2 : hingeMean (G N) a b = ENNReal.ofReal (∫ ξ, hinge a b (ξ : Pt d) ∂(G N : Measure ↥Ξ)) := by
              unfold hingeMean
              rw [ofReal_integral_eq_lintegral_ofReal (hint _ _ (hhc a b))]
              exact Eventually.of_forall fun ξ => le_max_right _ _
            have h3 : 0 ≤ ∫ ξ, hinge a b (ξ : Pt d) ∂(G N : Measure ↥Ξ) :=
              integral_nonneg fun ξ => le_max_right _ _
            rw [h2, EReal.coe_ennreal_ofReal, max_eq_left h3, hsum _ (hhc a b), ← EReal.coe_sub,
              EReal.coe_le_coe_iff] at h1
            have := le_abs_self (QC N)
            linarith
          · have hcn : Continuous fun ξ : ↥Ξ => ‖(ξ : Pt d)‖ ^ 2 := by fun_prop
            have h2 : secondMoment (G N) = ENNReal.ofReal (∫ ξ, ‖(ξ : Pt d)‖ ^ 2 ∂(G N : Measure ↥Ξ)) := by
              unfold secondMoment
              rw [ofReal_integral_eq_lintegral_ofReal (hint _ _ hcn)]
              exact Eventually.of_forall fun ξ => by positivity
            have h3 : 0 ≤ ∫ ξ, ‖(ξ : Pt d)‖ ^ 2 ∂(G N : Measure ↥Ξ) :=
              integral_nonneg fun ξ => by positivity
            unfold empSecondMoment at hc2
            rw [h2, EReal.coe_ennreal_ofReal, max_eq_left h3, hsum _ hcn, EReal.coe_le_coe_iff] at hc2
            have := le_abs_self (QR N)
            linarith
        have h0 : Tendsto (fun N => C * (|QC N| + |QR N|)) atTop (𝓝 0) := by
          have := (hQC.abs.add hQR.abs).const_mul C
          simpa using this
        have h1 : Tendsto (fun N : ℕ => ∫ ξ, Real.exp (inner ℝ (av n) (ξ : Pt d)) ∂(G N : Measure ↥Ξ) -
            (∑ i ∈ Finset.range N, Real.exp (inner ℝ (av n) (ω i : Pt d))) / N) atTop (𝓝 0) :=
          squeeze_zero_norm' hb h0
        have h2 := h1.add (hω n)
        simpa using h2
      -- Stone-Weierstrass
      let e : (Fin d → ℕ) → C(↥Ξ, ℝ) := fun n => ⟨_, hcexp (av n)⟩
      have hemul : ∀ m n, e m * e n = e (m + n) := by
        intro m n
        ext ξ
        change Real.exp _ * Real.exp _ = Real.exp _
        rw [← Real.exp_add, ← inner_add_left]
        congr 2
        ext i
        simp [hav]
      have hone : e 0 = 1 := by
        ext ξ
        change Real.exp _ = 1
        have : av 0 = 0 := by ext i; simp [hav]
        rw [this]; simp
      let Mo : Submonoid C(↥Ξ, ℝ) :=
        { carrier := Set.range e
          one_mem' := ⟨0, hone⟩
          mul_mem' := by
            rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
            exact ⟨m + n, (hemul m n).symm⟩ }
      let A : Subalgebra ℝ C(↥Ξ, ℝ) := Algebra.adjoin ℝ (Set.range e)
      have hAspan : ∀ f ∈ A, f ∈ Submodule.span ℝ (Set.range e) := by
        intro f hf
        have h1 : f ∈ Subalgebra.toSubmodule A := hf
        rw [Algebra.adjoin_eq_span] at h1
        have h2 : Submonoid.closure (Set.range e) ≤ Mo := Submonoid.closure_le.2 (fun x hx => hx)
        exact Submodule.span_mono h2 h1
      have hsep : A.SeparatesPoints := by
        intro x y hxy
        have : ∃ i, (x : Pt d) i ≠ (y : Pt d) i := by
          by_contra hcon
          push Not at hcon
          apply hxy
          apply Subtype.ext
          ext i
          exact hcon i
        obtain ⟨i, hi⟩ := this
        refine ⟨_, ⟨e (Pi.single i 1), Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩, ?_⟩
        change Real.exp _ ≠ Real.exp _
        intro h
        rw [Real.exp_eq_exp] at h
        have hv : av (Pi.single i 1) = EuclideanSpace.single i (1 : ℝ) := by
          ext j
          rw [hav]
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
        rw [hv, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left] at h
        simp at h
        exact hi h
      have hspan : ∀ f ∈ Submodule.span ℝ (Set.range e), Tendsto (fun N => ∫ ξ, f ξ ∂(G N : Measure ↥Ξ))
          atTop (𝓝 (∫ ξ, f ξ ∂(F : Measure ↥Ξ))) := by
        intro f hf
        induction hf using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨n, rfl⟩ := hx
          exact hexp n
        | zero => simp
        | add x y _ _ hx hy =>
          have := hx.add hy
          simp only [← integral_add (hint _ _ x.continuous) (hint _ _ y.continuous)] at this
          exact this
        | smul c x _ hx =>
          have := hx.const_mul c
          simp only [← integral_const_mul] at this
          exact this
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨⟨g, hgA⟩, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hsep
        f.toContinuousMap (ε / 4) (by linarith)
      have hgf : ∀ ξ, |g ξ - f ξ| ≤ ε / 4 := by
        intro ξ
        have := (g - f.toContinuousMap).norm_coe_le_norm ξ
        exact this.trans hg.le
      have hgi : ∀ (μ : Measure ↥Ξ) [IsProbabilityMeasure μ], |∫ ξ, g ξ ∂μ - ∫ ξ, f ξ ∂μ| ≤ ε / 4 := by
        intro μ _
        rw [← integral_sub (hint _ _ g.continuous) (hint _ _ f.continuous)]
        have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ξ => g ξ - f ξ) (C := ε / 4)
          (Eventually.of_forall hgf)
        simpa using this
      obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 (hspan g (hAspan g hgA))) (ε / 4) (by linarith)
      refine ⟨N0, fun N hN => ?_⟩
      have h1 := hN0 N hN
      have h2 := hgi (G N : Measure ↥Ξ)
      have h3 := hgi (F : Measure ↥Ξ)
      rw [Real.dist_eq] at h1 ⊢
      rw [abs_lt] at h1 ⊢
      rw [abs_le] at h2 h3
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
