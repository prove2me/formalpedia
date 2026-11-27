-- Prove2me | solution 1 for SingleMachineSched.AlphaJSched.Supplement.theorem_3_14
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:26:50.054055+00:00
-- url     : https://prove2.me/submissions/1951dce6-1b3a-4113-b765-087c69d89d85

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_OnlineSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_Optima
import Definitions.Def_SingleMachineSched_AlphaJSched_DensityG

open SingleMachineSched
open SingleMachineSched.AlphaJSched
open SingleMachineSched.AlphaJSched.Supplement

open MeasureTheory ProbabilityTheory

/-- Theorem 3.14: deterministic and randomized competitive bounds against OPT,
plus the on-line property for every valid vector of α_j: the schedule up to time t
is the same in every instance (of any size) whose jobs released by t are the same, in the
same relative priority order. Running time is not encoded. -/
theorem solution {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) :
    (1 + Real.sqrt 2 ≤ (2.4143 : ℝ) ∧
      ∑ j, w j * onlineCompletion p r (fun _ => 1 / Real.sqrt 2) j ≤
        (1 + Real.sqrt 2) * optValue p r w) ∧
    (∀ γ : ℝ, (0 < γ ∧ γ < 1 ∧
        γ + Real.log (2 - γ) = Real.exp (-γ) * ((2 - γ) * Real.exp γ - 1)) →
      cConst γ < 1.6853 ∧
        ∀ μ : Measure (Fin n → ℝ), IsProbabilityMeasure μ →
          (∀ j, μ.map (fun a => a j) = gMeasure γ) →
          (∀ j k, j ≠ k → IndepFun (fun a => a j) (fun a => a k) μ) →
          Integrable (fun a => ∑ j, w j * onlineCompletion p r a j) μ ∧
            ∫ a, ∑ j, w j * onlineCompletion p r a j ∂μ ≤
              cConst γ * optValue p r w) ∧
    (∀ (m : ℕ) (p' r' : Fin m → ℕ) (w' : Fin m → ℝ) (α : Fin n → ℝ) (α' : Fin m → ℝ),
      (∀ j, 0 < p' j) → (∀ j, 0 < w' j) →
      (∀ j k : Fin m, j ≤ k → w' k / p' k ≤ w' j / p' j) →
      (∀ j, 0 < α j ∧ α j ≤ 1) → (∀ j, 0 < α' j ∧ α' j ≤ 1) →
      ∀ (t : ℝ) (e : Fin n → Fin m),
        (∀ j k, (r j : ℝ) ≤ t → (r k : ℝ) ≤ t → (j < k ↔ e j < e k)) →
        (∀ k', (r' k' : ℝ) ≤ t → ∃ j, (r j : ℝ) ≤ t ∧ e j = k') →
        (∀ j, (r j : ℝ) ≤ t →
          p' (e j) = p j ∧ r' (e j) = r j ∧ w' (e j) = w j ∧ α' (e j) = α j) →
        ∀ j, (r j : ℝ) ≤ t →
          ((onlineCompletion p r α j - (p j : ℝ) ≤ t ↔
            onlineCompletion p' r' α' (e j) - (p' (e j) : ℝ) ≤ t) ∧
          (onlineCompletion p r α j - (p j : ℝ) ≤ t →
            onlineCompletion p r α j - (p j : ℝ) =
              onlineCompletion p' r' α' (e j) - (p' (e j) : ℝ)))) := by
                classical
                have hsqrt : 1 + Real.sqrt 2 ≤ (2.4143 : ℝ) := by
                  have h : Real.sqrt 2 ≤ 1.4143 := by
                    rw [Real.sqrt_le_left (by norm_num)]; norm_num
                  linarith
                have hGf : ∀ γ : ℝ, (0 < γ ∧ γ < 1 ∧
                      γ + Real.log (2 - γ) = Real.exp (-γ) * ((2 - γ) * Real.exp γ - 1)) →
                    cConst γ < 1.6853 ∧ ∃ K : ℝ, 0 < K ∧ cConst γ = 1 + K ∧ 2 - γ ≤ 1 + K ∧
                      (∀ᵐ x ∂(gMeasure γ), x ∈ Set.Ioc (0:ℝ) 1) ∧
                      (∀ η : ℝ, 0 ≤ η → η ≤ 1 → ∫ x, (if x ≤ η then 1 + x - η else 0) ∂(gMeasure γ) ≤ K * η) ∧
                      (∫ x, x ∂(gMeasure γ) = 1 - γ) ∧
                      (∀ ν : ℝ, 0 ≤ ν → ν ≤ 1 →
                        (2 - γ) * ∫ x, (if ν < x then (1:ℝ) else 0) ∂(gMeasure γ) ≤ (1 + K) * (1 - ν)) := by
                  clear hsort hw hp w r p hsqrt
                  intro γ hγ
                  have hc : cConst γ < 1.6853 := by
                    obtain ⟨h0, h1, heq⟩ := hγ
                    have hE1 : Real.exp (-(4834/10000 : ℝ)) < 0.61669 ∧ (0.61668 : ℝ) < Real.exp (-(4834/10000 : ℝ)) := by
                      have h := Real.exp_bound (x := -(4834/10000 : ℝ)) (by rw [abs_le]; constructor <;> norm_num) (n := 8) (by norm_num)
                      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
                      rw [abs_le] at h
                      norm_num at h
                      constructor <;> linarith [h.1, h.2]
                    have hL1 : Real.log (2 - 4834/10000) < 0.41648 := by
                      have h := Real.exp_bound (x := (0.41648 : ℝ)) (by rw [abs_le]; constructor <;> norm_num) (n := 8) (by norm_num)
                      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
                      rw [abs_le] at h
                      norm_num at h
                      rw [Real.log_lt_iff_lt_exp (by norm_num)]
                      norm_num
                      linarith [h.1, h.2]
                    set x := Real.exp (-γ) with hx
                    have hxpos : 0 < x := Real.exp_pos _
                    have hxe : x * Real.exp γ = 1 := by rw [hx, ← Real.exp_add]; simp
                    have heq' : γ + Real.log (2 - γ) = (2 - γ) - x := by
                      rw [heq]; linear_combination (2 - γ) * hxe
                    have hx1 : x < 1 := by rw [hx]; exact Real.exp_lt_one_iff.mpr (by linarith)
                    have h2γ : 0 < 2 - γ := by linarith only [h1]
                    -- lower bound on γ
                    have hlow : 4834/10000 < γ := by
                      by_contra hle
                      push Not at hle
                      set d := 4834/10000 - γ with hd
                      have hd0 : 0 ≤ d := by linarith
                      -- log bound
                      have hlog : Real.log (2 - γ) ≤ Real.log (2 - 4834/10000) + d / (2 - 4834/10000) := by
                        have := Real.log_le_sub_one_of_pos (x := (2 - γ) / (2 - 4834/10000)) (div_pos h2γ (by norm_num))
                        rw [Real.log_div h2γ.ne' (by norm_num)] at this
                        have : (2 - γ) / (2 - 4834/10000) - 1 = d / (2 - 4834/10000) := by
                          rw [hd]; field_simp; ring
                        linarith
                      -- exp bound
                      have hexp : x ≤ Real.exp (-(4834/10000 : ℝ)) + d := by
                        have h2 : Real.exp (-(4834/10000:ℝ)) = x * Real.exp (-d) := by
                          rw [hx, ← Real.exp_add]; congr 1; rw [hd]; ring
                        have h3 : -d + 1 ≤ Real.exp (-d) := Real.add_one_le_exp _
                        have h5 := mul_le_mul_of_nonneg_left h3 hxpos.le
                        have h6 := mul_le_of_le_one_left hd0 hx1.le
                        rw [h2]; linarith only [h5, h6]
                      have hdd : d / (2 - 4834/10000) = d * (10000/15166) := by ring
                      rw [hdd] at hlog
                      linarith only [hE1.1, hL1, hlog, heq', hd, hexp, hle, hd0]
                    -- final
                    have hD : cConst γ = 1 + x / ((2 - γ) - x) := by
                      unfold cConst delta; rw [heq']
                    set d := γ - 4834/10000 with hd
                    have hd0 : 0 < d := by linarith only [hd, hlow]
                    have hy := Real.quadratic_le_exp_of_nonneg hd0.le
                    have hxy : x * Real.exp d = Real.exp (-(4834/10000 : ℝ)) := by
                      rw [hx, ← Real.exp_add]; congr 1; rw [hd]; ring
                    have hden : 0 < (2 - γ) - x := by linarith only [hx1, h1]
                    rw [hD, show (1.6853 : ℝ) = 1 + 0.6853 by norm_num, add_lt_add_iff_left, div_lt_iff₀ hden]
                    have hd1 : d < 1 - 4834/10000 := by linarith only [hd, h1]
                    have hQ : x * (1 + d + d ^ 2 / 2) ≤ Real.exp (-(4834/10000 : ℝ)) := by
                      rw [← hxy]; exact mul_le_mul_of_nonneg_left hy hxpos.le
                    have hγd : γ = 4834/10000 + d := by rw [hd]; ring
                    have hE2 := hE1.1
                    rw [hγd]
                    clear hE1 hL1 hx hxe heq' heq hx1 hlow hD hy hxy hden
                    by_contra hcon
                    push Not at hcon
                    have m1 := mul_le_mul_of_nonneg_right hcon (show 0 ≤ 1 + d + d ^ 2 / 2 by positivity)
                    have m2 := mul_le_mul_of_nonneg_left hd1.le hd0.le
                    have m3 : 0 ≤ d * (5166/10000 - 2417/10000 * d - d * d / 2) := mul_nonneg hd0.le (by linarith only [m2, hd1])
                    linarith only [m1, m3, hQ, hE2, hd0]
                  refine ⟨hc, ?_⟩
                  clear hc
                  obtain ⟨hγ0, hγ1, hγeq⟩ := hγ
                  have hexpγ : Real.exp (-γ) * Real.exp γ = 1 := by rw [← Real.exp_add]; simp
                  obtain ⟨δ, hδ⟩ : ∃ δ, δ = delta γ := ⟨_, rfl⟩
                  have hδ1 : δ = 2 - γ - Real.exp (-γ) := by
                    rw [hδ]; unfold delta; rw [hγeq]; linear_combination (2 - γ) * hexpγ
                  have hδ2 : Real.exp δ = Real.exp γ * (2 - γ) := by
                    rw [hδ]; unfold delta; rw [Real.exp_add, Real.exp_log (by linarith)]
                  have hδle : δ ≤ 1 := by
                    have := Real.add_one_le_exp (-γ); linarith
                  have hδpos : 0 < δ := by
                    rw [hδ]; unfold delta
                    have := Real.log_pos (show 1 < 2 - γ by linarith)
                    linarith
                  obtain ⟨K, hK⟩ : ∃ K, K = Real.exp (-γ) / δ := ⟨_, rfl⟩
                  have hKpos : 0 < K := by rw [hK]; exact div_pos (Real.exp_pos _) hδpos
                  have hKδ : K * δ = Real.exp (-γ) := by rw [hK]; field_simp
                  have hcK : cConst γ = 1 + K := by unfold cConst; rw [hK, hδ]
                  have hcδ : (1 + K) * δ = 2 - γ := by rw [add_mul, hKδ, hδ1]; ring
                  have hKe : K * δ * Real.exp δ = 2 - γ := by rw [hKδ, hδ2, ← mul_assoc, hexpγ, one_mul]
                  have hgm : Measurable (fun a => ENNReal.ofReal (gDens γ a)) := by
                    apply Measurable.ennreal_ofReal
                    unfold gDens
                    refine Measurable.ite ?_ (by fun_prop) measurable_const
                    exact measurableSet_Ioc
                  have hgI : ∀ f : ℝ → ℝ, ∫ x, f x ∂(gMeasure γ) = ∫ x in Set.Ioc 0 δ, K * Real.exp x * f x := by
                    intro f
                    unfold gMeasure
                    rw [integral_withDensity_eq_integral_toReal_smul hgm (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
                      ← integral_indicator measurableSet_Ioc]
                    congr 1
                    ext x
                    simp only [Set.indicator_apply, Set.mem_Ioc, gDens, ← hδ, hcK, add_sub_cancel_left, smul_eq_mul]
                    split_ifs with h
                    · rw [ENNReal.toReal_ofReal (by positivity)]
                    · simp
                  have hgIi : ∀ f : ℝ → ℝ, ∀ u v : ℝ, (∀ x, x ∈ Set.Ioc 0 δ ∩ {x | f x ≠ 0} → x ∈ Set.Ioc u v) → 
                      (Set.Ioc u v ⊆ Set.Ioc 0 δ) → ∫ x, f x ∂(gMeasure γ) = ∫ x in Set.Ioc u v, K * Real.exp x * f x := by
                    intro f u v h1 h2
                    rw [hgI]
                    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc h2
                    rintro x ⟨hx1, hx2⟩
                    by_cases hf : f x = 0
                    · rw [hf, mul_zero]
                    · exact absurd (h1 x ⟨hx1, hf⟩) hx2
                  -- (i)
                  have hLi : ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
                      ∫ x, (if x ≤ η then 1 + x - η else 0) ∂(gMeasure γ) ≤ K * η := by
                    intro η h0 h1
                    obtain ⟨v, hv⟩ : ∃ v, v = min η δ := ⟨_, rfl⟩
                    have hv0 : 0 ≤ v := by rw [hv]; exact le_min h0 hδpos.le
                    rw [hgIi _ 0 v, setIntegral_congr_fun (g := fun x => K * ((1 + x - η) * Real.exp x)) measurableSet_Ioc,
                      ← intervalIntegral.integral_of_le hv0]
                    · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => K * ((x - η) * Real.exp x))]
                      · have hle : (v - η) * Real.exp v ≤ 0 :=
                          mul_nonpos_of_nonpos_of_nonneg (by rw [hv]; linarith [min_le_left η δ]) (Real.exp_pos _).le
                        simp only [Real.exp_zero]
                        have hKle := mul_nonpos_of_nonneg_of_nonpos hKpos.le hle
                        linarith
                      · intro x _
                        have hd := ((((hasDerivAt_id x).sub_const η).mul (Real.hasDerivAt_exp x)).const_mul K)
                        refine hd.congr_deriv ?_
                        simp only [id]
                        ring
                      · apply Continuous.intervalIntegrable; fun_prop
                    · intro x hx
                      try simp only
                      rw [if_pos (hx.2.trans (by rw [hv]; exact min_le_left _ _))]; ring
                    · rintro x ⟨hx1, hx2⟩
                      refine ⟨hx1.1, ?_⟩
                      rw [hv]; refine le_min ?_ hx1.2
                      by_contra hc
                      simp [hc] at hx2
                    · apply Set.Ioc_subset_Ioc_right; rw [hv]; exact min_le_right _ _
                  -- mean
                  have hE : ∫ x, x ∂(gMeasure γ) = 1 - γ := by
                    rw [hgI, setIntegral_congr_fun (g := fun x => K * (x * Real.exp x)) measurableSet_Ioc,
                      ← intervalIntegral.integral_of_le hδpos.le,
                      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => K * ((x - 1) * Real.exp x))]
                    · simp only [Real.exp_zero]
                      have hK1 : K * (Real.exp δ) = 1 + K := by
                        have : δ * (K * Real.exp δ - (1 + K)) = 0 := by linarith
                        rcases mul_eq_zero.mp this with h | h
                        · exact absurd h hδpos.ne'
                        · linarith
                      linarith
                    · intro x _
                      have hd := ((((hasDerivAt_id x).sub_const 1).mul (Real.hasDerivAt_exp x)).const_mul K)
                      refine hd.congr_deriv ?_
                      simp only [id]
                      ring
                    · apply Continuous.intervalIntegrable; fun_prop
                    · intro x hx; ring
                  -- (ii)
                  have hLii : ∀ ν : ℝ, 0 ≤ ν → ν ≤ 1 →
                      (2 - γ) * ∫ x, (if ν < x then (1:ℝ) else 0) ∂(gMeasure γ) ≤ (1 + K) * (1 - ν) := by
                    intro ν h0 h1
                    rcases le_or_gt ν δ with h | h
                    · rw [hgIi _ ν δ, setIntegral_congr_fun (g := fun x => K * Real.exp x) measurableSet_Ioc,
                        ← intervalIntegral.integral_of_le h, intervalIntegral.integral_const_mul, integral_exp]
                      · have hx := Real.add_one_le_exp (ν - γ)
                        have e1 : Real.exp (ν - γ) = K * δ * Real.exp ν := by
                          rw [hKδ, ← Real.exp_add]; congr 1; ring
                        rw [e1] at hx
                        have hc0 : 0 < 1 + K := by linarith
                        have e2 : (2 - γ) * (K * (Real.exp δ - Real.exp ν)) = (1 + K) * (K * δ * Real.exp δ - K * δ * Real.exp ν) := by
                          rw [← hcδ]; ring
                        rw [e2, hKe]
                        apply mul_le_mul_of_nonneg_left _ hc0.le
                        linarith
                      · intro x hx
                        try simp only
                        rw [if_pos hx.1, mul_one]
                      · rintro x ⟨hx1, hx2⟩
                        refine ⟨?_, hx1.2⟩
                        by_contra hc
                        simp [hc] at hx2
                      · exact Set.Ioc_subset_Ioc_left h0
                    · rw [hgIi _ 0 0]
                      · simp
                        have : 0 ≤ 1 - ν := by linarith
                        positivity
                      · rintro x ⟨hx1, hx2⟩
                        exfalso
                        apply hx2
                        try simp only
                        rw [if_neg]
                        linarith [hx1.2]
                      · simp
                  refine ⟨K, hKpos, hcK, ?_, ?_, hLi, hE, hLii⟩
                  · rw [← hcδ]
                    exact mul_le_of_le_one_right (by linarith) hδle
                  · unfold gMeasure
                    rw [ae_withDensity_iff hgm]
                    refine Filter.Eventually.of_forall fun x hx => ?_
                    unfold gDens at hx
                    rw [← hδ] at hx
                    by_cases hc : 0 < x ∧ x ≤ δ
                    · exact ⟨hc.1, hc.2.trans hδle⟩
                    · simp [hc] at hx
                have GEN : ∀ (n : ℕ) (p r : Fin n → ℕ), (∀ j, 0 < p j) → ∀ j x, 0 < x → x ≤ 1 →
                    (r j:ℝ) ≤ alphaPoint p (lpSet p r) j x ∧ ∀ s, alphaPoint p (lpSet p r) j x ≤ s ↔
                      x * (p j:ℝ) ≤ (volume (lpSet p r j ∩ Set.Iic s)).toReal := by
                  clear hGf hsort hw hp hsqrt
                  clear w r p
                  intro n p r hp
                  have hrun_some : ∀ τ j, lpRun p r τ = some j → r j ≤ τ ∧ 0 < lpRemaining p r τ j ∧
                      ∀ k, r k ≤ τ → 0 < lpRemaining p r τ k → j ≤ k := by
                    intro τ j h
                    unfold lpRun lpPick at h
                    split_ifs at h with hne
                    have h' := Option.some.inj h
                    have hm := Finset.min'_mem _ hne
                    rw [h'] at hm
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
                    refine ⟨hm.1, hm.2, fun k h1 h2 => ?_⟩
                    rw [← h']
                    exact Finset.min'_le _ _ (by simp [h1, h2])
                  have hrun_none : ∀ τ, lpRun p r τ = none → ∀ k, r k ≤ τ → lpRemaining p r τ k = 0 := by
                    intro τ h k hk
                    unfold lpRun lpPick at h
                    split_ifs at h with hne
                    by_contra hc
                    exact hne ⟨k, by simp [hk]; omega⟩
                  have hsucc : ∀ τ j, lpRemaining p r (τ+1) j =
                      if lpRun p r τ = some j then lpRemaining p r τ j - 1 else lpRemaining p r τ j := by
                    intro τ j; rfl
                  have hcnt : ∀ b j, lpRemaining p r b j +
                      ∑ τ ∈ Finset.range b, (if lpRun p r τ = some j then 1 else 0) = p j := by
                    intro b j
                    induction b with
                    | zero => simp [lpRemaining]
                    | succ b ih =>
                      rw [Finset.sum_range_succ, hsucc]
                      split_ifs with h
                      · have := (hrun_some b j h).2.1
                        omega
                      · omega
                  have hnotrel : ∀ b j, b ≤ r j → lpRemaining p r b j = p j := by
                    intro b j
                    induction b with
                    | zero => simp [lpRemaining]
                    | succ b ih =>
                      intro hb
                      rw [hsucc, if_neg, ih (by omega)]
                      intro h
                      have := (hrun_some b j h).1
                      omega
                  have hmono : ∀ b c j, b ≤ c → lpRemaining p r c j ≤ lpRemaining p r b j := by
                    intro b c j hbc
                    induction hbc with
                    | refl => exact le_rfl
                    | step _ ih => 
                      refine le_trans ?_ ih
                      rw [hsucc]; split_ifs <;> omega
                  have hT : ∃ T, ∀ b, T ≤ b → ∀ j, lpRemaining p r b j = 0 := by
                    have key : ∀ s, ∑ j, lpRemaining p r ((∑ j, r j) + s) j ≤ (∑ j, p j) - s := by
                      intro s
                      induction s with
                      | zero =>
                        simp only [add_zero, Nat.sub_zero]
                        exact Finset.sum_le_sum fun j _ => by have := hcnt (∑ j, r j) j; omega
                      | succ s ih =>
                        rcases hc : lpRun p r ((∑ j, r j) + s) with _ | k
                        · have h0 : ∀ j, lpRemaining p r ((∑ j, r j) + (s+1)) j = 0 := by
                            intro j
                            rw [← add_assoc, hsucc, hc]
                            simp only [reduceCtorEq, if_false]
                            exact hrun_none _ hc j (by
                              have := Finset.single_le_sum (f := r) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
                              omega)
                          simp [h0]
                        · have hk := (hrun_some _ _ hc).2.1
                          have hlt : ∑ j, lpRemaining p r ((∑ j, r j) + (s+1)) j
                              < ∑ j, lpRemaining p r ((∑ j, r j) + s) j := by
                            apply Finset.sum_lt_sum
                            · intro j _; exact hmono _ _ _ (by omega)
                            · refine ⟨k, Finset.mem_univ _, ?_⟩
                              rw [← add_assoc, hsucc, hc, if_pos rfl]
                              omega
                          omega
                    refine ⟨(∑ j, r j) + ∑ j, p j, fun b hb j => ?_⟩
                    have h1 := key (∑ j, p j)
                    have h2 := Finset.single_le_sum (f := fun j => lpRemaining p r ((∑ j, r j) + ∑ j, p j) j) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
                    have h3 := hmono _ _ j hb
                    omega
                  obtain ⟨T, hT⟩ := hT
                  have hAeq : ∀ j, lpSet p r j = ⋃ τ ∈ (Finset.range T).filter (fun τ => lpRun p r τ = some j),
                      Set.Ico (τ:ℝ) (τ+1) := by
                    intro j
                    ext x
                    simp only [lpSet, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
                    constructor
                    · rintro ⟨τ, h1, h2⟩
                      refine ⟨τ, ⟨?_, h1⟩, h2⟩
                      by_contra hc
                      have e1 := (hrun_some τ j h1).2.1
                      have e2 := hT τ (by omega) j
                      omega
                    · rintro ⟨τ, ⟨_, h1⟩, h2⟩
                      exact ⟨τ, h1, h2⟩
                  have hIco : ∀ a b : ℕ, a ≠ b → Disjoint (Set.Ico (a:ℝ) (a+1)) (Set.Ico (b:ℝ) (b+1)) := by
                    intro a b hab
                    rw [Set.disjoint_left]
                    rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
                    have e1 : (a:ℝ) < b + 1 := by linarith
                    have e2 : (b:ℝ) < a + 1 := by linarith
                    have e3 : a < b + 1 := by exact_mod_cast e1
                    have e4 : b < a + 1 := by exact_mod_cast e2
                    omega
                  have hAmeas : ∀ j, MeasurableSet (lpSet p r j) := by
                    intro j
                    rw [hAeq]
                    exact Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ico
                  have hAvol : ∀ j, volume (lpSet p r j) = (p j : ENNReal) := by
                    intro j
                    rw [hAeq, measure_biUnion_finset (fun a _ b _ hab => hIco a b hab) (fun _ _ => measurableSet_Ico)]
                    simp only [Real.volume_Ico, add_sub_cancel_left, ENNReal.ofReal_one]
                    have e := hcnt T j
                    rw [hT T le_rfl j, zero_add] at e
                    rw [← e, Finset.sum_filter]
                    push_cast
                    rfl
                  have hAr : ∀ j, ∀ x ∈ lpSet p r j, (r j : ℝ) ≤ x := by
                    intro j x hx
                    simp only [lpSet, Set.mem_iUnion, exists_prop] at hx
                    obtain ⟨τ, h1, h2⟩ := hx
                    have e : (r j : ℝ) ≤ τ := by exact_mod_cast (hrun_some τ j h1).1
                    exact e.trans h2.1
                  have hAT : ∀ j, ∀ x ∈ lpSet p r j, x ≤ T := by
                    intro j x hx
                    rw [hAeq] at hx
                    simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_range] at hx
                    obtain ⟨τ, h1, h2⟩ := hx
                    have e : ((τ:ℝ) + 1 ) ≤ T := by exact_mod_cast h1.1
                    exact h2.2.le.trans e
                  -- F
                  obtain ⟨F, hF⟩ : ∃ F : Fin n → ℝ → ℝ, ∀ j t, F j t = (volume (lpSet p r j ∩ Set.Iic t)).toReal := ⟨_, fun _ _ => rfl⟩
                  have hfin : ∀ j (s : Set ℝ), volume (lpSet p r j ∩ s) ≠ ⊤ := by
                    intro j s
                    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_left)
                    rw [hAvol]; exact ENNReal.natCast_ne_top _
                  have hF0 : ∀ j t, 0 ≤ F j t := fun j t => by rw [hF]; exact ENNReal.toReal_nonneg
                  have hFvol : ∀ j t, volume (lpSet p r j ∩ Set.Iic t) = ENNReal.ofReal (F j t) := by
                    intro j t
                    rw [hF, ENNReal.ofReal_toReal (hfin _ _)]
                  have hFmono : ∀ j s t, s ≤ t → F j s ≤ F j t := by
                    intro j s t hst
                    rw [hF, hF]
                    exact ENNReal.toReal_mono (hfin _ _) (measure_mono (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr hst)))
                  have hFp : ∀ j t, F j t ≤ p j := by
                    intro j t
                    rw [hF]
                    have := ENNReal.toReal_mono (by rw [hAvol]; exact ENNReal.natCast_ne_top _) (measure_mono (μ := volume) (Set.inter_subset_left (s := lpSet p r j) (t := Set.Iic t)))
                    rw [hAvol] at this
                    simpa using this
                  have hFT : ∀ j, F j T = p j := by
                    intro j
                    rw [hF, Set.inter_eq_left.mpr (show lpSet p r j ⊆ Set.Iic (T:ℝ) from fun x hx => hAT j x hx), hAvol]
                    simp
                  have hFr : ∀ j (t : ℝ), t < r j → F j t = 0 := by
                    intro j t ht
                    rw [hF]
                    have : lpSet p r j ∩ Set.Iic t = ∅ := by
                      ext x
                      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_and, not_le]
                      intro hx
                      exact lt_of_lt_of_le ht (hAr j x hx)
                    rw [this]; simp
                  have hFcont : ∀ j, Continuous (F j) := by
                    intro j
                    refine (LipschitzWith.of_le_add (f := F j) fun x y => ?_).continuous
                    rw [hF, hF, Real.dist_eq]
                    have e1 : volume (lpSet p r j ∩ Set.Iic x) ≤ volume (lpSet p r j ∩ Set.Iic y) + ENNReal.ofReal |x - y| := by
                      refine (measure_mono (t := (lpSet p r j ∩ Set.Iic y) ∪ Set.Ioc y x) ?_).trans ((measure_union_le _ _).trans ?_)
                      · rintro z ⟨h1, h2⟩
                        by_cases h : z ≤ y
                        · exact Or.inl ⟨h1, h⟩
                        · exact Or.inr ⟨not_le.mp h, h2⟩
                      · rw [Real.volume_Ioc]
                        gcongr
                        exact le_abs_self _
                    have e2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _ _, ENNReal.ofReal_ne_top⟩) e1
                    rwa [ENNReal.toReal_add (hfin _ _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (abs_nonneg _)] at e2
                  -- alpha points
                  obtain ⟨tt, htt⟩ : ∃ tt : Fin n → ℝ → ℝ, ∀ j x, tt j x = alphaPoint p (lpSet p r) j x := ⟨_, fun _ _ => rfl⟩
                  have htt' : ∀ j x, tt j x = sInf {t | x * (p j : ℝ) ≤ F j t} := by
                    intro j x
                    rw [htt]; unfold alphaPoint
                    simp only [hF]
                  have hpR : ∀ j, (0:ℝ) < p j := fun j => by exact_mod_cast hp j
                  have hEr : ∀ j x, 0 < x → ∀ t, x * (p j : ℝ) ≤ F j t → (r j : ℝ) ≤ t := by
                    intro j x hx t ht
                    by_contra hc
                    rw [hFr j t (not_le.mp hc)] at ht
                    have := mul_pos hx (hpR j)
                    linarith
                  have hG : ∀ j x, 0 < x → x ≤ 1 → ∀ s, tt j x ≤ s ↔ x * (p j : ℝ) ≤ F j s := by
                    intro j x hx0 hx1 s
                    have hbdd : BddBelow {t | x * (p j : ℝ) ≤ F j t} := ⟨r j, fun t ht => hEr j x hx0 t ht⟩
                    have hne : {t | x * (p j : ℝ) ≤ F j t}.Nonempty := ⟨T, by
                      simp only [Set.mem_ofPred_eq, hFT]
                      exact mul_le_of_le_one_left (hpR j).le hx1⟩
                    have hcl : IsClosed {t | x * (p j : ℝ) ≤ F j t} := isClosed_le continuous_const (hFcont j)
                    have hmem := hcl.csInf_mem hne hbdd
                    rw [htt']
                    constructor
                    · intro h
                      exact le_trans hmem (hFmono j _ _ h)
                    · intro h
                      exact csInf_le hbdd h
                  have htr : ∀ j x, 0 < x → x ≤ 1 → (r j : ℝ) ≤ tt j x := by
                    intro j x h0 h1
                    exact hEr j x h0 _ ((hG j x h0 h1 _).mp le_rfl)
                  intro j x h0 h1
                  refine ⟨by rw [← htt]; exact htr j x h0 h1, fun s => ?_⟩
                  rw [← htt, ← hF]; exact hG j x h0 h1 s
                have hchar : ∀ (n : ℕ) (p r : Fin n → ℕ) (τ : ℕ) (j : Fin n), lpRun p r τ = some j ↔
                    (r j ≤ τ ∧ 0 < lpRemaining p r τ j ∧ ∀ k, r k ≤ τ → 0 < lpRemaining p r τ k → j ≤ k) := by
                  intro n p r τ j
                  constructor
                  · intro h
                    unfold lpRun lpPick at h
                    split_ifs at h with hne
                    have h' := Option.some.inj h
                    have hm := Finset.min'_mem _ hne
                    rw [h'] at hm
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
                    refine ⟨hm.1, hm.2, fun k h1 h2 => ?_⟩
                    rw [← h']
                    exact Finset.min'_le _ _ (by simp [h1, h2])
                  · rintro ⟨h1, h2, h3⟩
                    have hne : (Finset.univ.filter (fun j => r j ≤ τ ∧ 0 < lpRemaining p r τ j)).Nonempty :=
                      ⟨j, by simp [h1, h2]⟩
                    unfold lpRun lpPick
                    rw [dif_pos hne]
                    congr 1
                    apply le_antisymm
                    · exact Finset.min'_le _ _ (by simp [h1, h2])
                    · have hm := Finset.min'_mem _ hne
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
                      exact h3 _ hm.1 hm.2
                have hOC : ∀ (n : ℕ) (p r : Fin n → ℕ) (α : Fin n → ℝ) (j : Fin n) (x : ℝ),
                    onlineCompletion p r α j ≤ x ↔ ∀ k, precedes p r α k j →
                      max (r k : ℝ) (alphaPoint p (lpSet p r) k (α k)) +
                        ∑ i ∈ Finset.univ.filter (fun i => precedes p r α k i ∧ precedes p r α i j), (p i : ℝ) ≤ x := by
                  intro n p r α j x
                  unfold onlineCompletion
                  refine (Finset.sup'_le_iff _ _).trans ?_
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                have honline : ∀ (m : ℕ) (p' r' : Fin m → ℕ) (w' : Fin m → ℝ) (α : Fin n → ℝ) (α' : Fin m → ℝ),
                    (∀ j, 0 < p' j) → (∀ j, 0 < w' j) →
                    (∀ j k : Fin m, j ≤ k → w' k / p' k ≤ w' j / p' j) →
                    (∀ j, 0 < α j ∧ α j ≤ 1) → (∀ j, 0 < α' j ∧ α' j ≤ 1) →
                    ∀ (t : ℝ) (e : Fin n → Fin m),
                      (∀ j k, (r j : ℝ) ≤ t → (r k : ℝ) ≤ t → (j < k ↔ e j < e k)) →
                      (∀ k', (r' k' : ℝ) ≤ t → ∃ j, (r j : ℝ) ≤ t ∧ e j = k') →
                      (∀ j, (r j : ℝ) ≤ t →
                        p' (e j) = p j ∧ r' (e j) = r j ∧ w' (e j) = w j ∧ α' (e j) = α j) →
                      ∀ j, (r j : ℝ) ≤ t →
                        ((onlineCompletion p r α j - (p j : ℝ) ≤ t ↔
                          onlineCompletion p' r' α' (e j) - (p' (e j) : ℝ) ≤ t) ∧
                        (onlineCompletion p r α j - (p j : ℝ) ≤ t →
                          onlineCompletion p r α j - (p j : ℝ) =
                            onlineCompletion p' r' α' (e j) - (p' (e j) : ℝ))) := by
                  clear hGf hsqrt hsort
                  intro m p' r' w' α α' hp' hw' hsort' hα hα' t e hord hsurj hagree
                  have hle : ∀ j k, (r j : ℝ) ≤ t → (r k : ℝ) ≤ t → (e j ≤ e k ↔ j ≤ k) := by
                    intro j k hj hk
                    rw [← not_lt, ← not_lt, hord k j hk hj]
                  have hpick : ∀ τ : ℕ, (τ:ℝ) ≤ t →
                      (∀ j, (r j:ℝ) ≤ t → lpRemaining p' r' τ (e j) = lpRemaining p r τ j) →
                      ∀ j, (r j:ℝ) ≤ t → (lpRun p' r' τ = some (e j) ↔ lpRun p r τ = some j) := by
                    intro τ hτ hR j hj
                    rw [hchar, hchar, hR j hj, (hagree j hj).2.1]
                    refine and_congr_right fun h1 => and_congr_right fun h2 => ⟨fun h k hk1 hk2 => ?_, fun h k' hk1 hk2 => ?_⟩
                    · have hkt : (r k:ℝ) ≤ t := le_trans (by exact_mod_cast hk1) hτ
                      exact (hle j k hj hkt).mp (h (e k) (by rw [(hagree k hkt).2.1]; exact hk1) (by rw [hR k hkt]; exact hk2))
                    · obtain ⟨k, hkt, rfl⟩ := hsurj k' (le_trans (by exact_mod_cast hk1) hτ)
                      rw [(hagree k hkt).2.1] at hk1
                      rw [hR k hkt] at hk2
                      exact (hle j k hj hkt).mpr (h k hk1 hk2)
                  have hrem : ∀ τ : ℕ, (τ:ℝ) ≤ t → ∀ j, (r j:ℝ) ≤ t → lpRemaining p' r' τ (e j) = lpRemaining p r τ j := by
                    intro τ
                    induction τ with
                    | zero => intro _ j hj; exact (hagree j hj).1
                    | succ τ ih =>
                      intro hτ j hj
                      have hτ' : (τ:ℝ) ≤ t := le_trans (by push_cast; linarith) hτ
                      have h1 := hpick τ hτ' (ih hτ') j hj
                      have e1 : lpRemaining p' r' (τ+1) (e j) = if lpRun p' r' τ = some (e j) then lpRemaining p' r' τ (e j) - 1 else lpRemaining p' r' τ (e j) := rfl
                      have e2 : lpRemaining p r (τ+1) j = if lpRun p r τ = some j then lpRemaining p r τ j - 1 else lpRemaining p r τ j := rfl
                      rw [e1, e2, ih hτ' j hj]
                      simp only [h1]
                  have hset : ∀ s ≤ t, ∀ j, (r j:ℝ) ≤ t → lpSet p' r' (e j) ∩ Set.Iic s = lpSet p r j ∩ Set.Iic s := by
                    intro s hs j hj
                    ext x
                    simp only [lpSet, Set.mem_inter_iff, Set.mem_iUnion, exists_prop, Set.mem_Iic]
                    refine and_congr_left fun hx => exists_congr fun τ => ?_
                    refine and_congr_left fun hxτ => ?_
                    have hτ : (τ:ℝ) ≤ t := le_trans hxτ.1 (hx.trans hs)
                    exact hpick τ hτ (hrem τ hτ) j hj
                  obtain ⟨A, hA⟩ : ∃ A : Fin n → ℝ, ∀ j, A j = alphaPoint p (lpSet p r) j (α j) := ⟨_, fun _ => rfl⟩
                  obtain ⟨A', hA'⟩ : ∃ A' : Fin m → ℝ, ∀ j, A' j = alphaPoint p' (lpSet p' r') j (α' j) := ⟨_, fun _ => rfl⟩
                  have hAiff : ∀ j, (r j:ℝ) ≤ t → ∀ s ≤ t, (A' (e j) ≤ s ↔ A j ≤ s) := by
                    intro j hj s hs
                    rw [hA, hA', (GEN m p' r' hp' (e j) _ (hα' _).1 (hα' _).2).2 s, (GEN n p r hp j _ (hα _).1 (hα _).2).2 s,
                      hset s hs j hj, (hagree j hj).1, (hagree j hj).2.2.2]
                  have hAr : ∀ j, (r j:ℝ) ≤ A j := fun j => by
                    rw [hA]; exact (GEN n p r hp j _ (hα _).1 (hα _).2).1
                  have hAr' : ∀ j, (r' j:ℝ) ≤ A' j := fun j => by
                    rw [hA']; exact (GEN m p' r' hp' j _ (hα' _).1 (hα' _).2).1
                  have hAe : ∀ j, A j ≤ t → A' (e j) = A j := by
                    intro j hj
                    have hr := (hAr j).trans hj
                    have h1 := (hAiff j hr (A j) hj).mpr le_rfl
                    exact le_antisymm h1 ((hAiff j hr (A' (e j)) (h1.trans hj)).mp le_rfl)
                  have hsurjA : ∀ k', A' k' ≤ t → ∃ k, A k ≤ t ∧ e k = k' := by
                    intro k' hk'
                    obtain ⟨k, h1, rfl⟩ := hsurj k' ((hAr' k').trans hk')
                    exact ⟨k, (hAiff k h1 t le_rfl).mp hk', rfl⟩
                  have hP : ∀ k j, precedes p r α k j ↔ (A k < A j ∨ (A k = A j ∧ k ≤ j)) := by
                    intro k j; unfold precedes; rw [hA, hA]
                  have hP' : ∀ k j, precedes p' r' α' k j ↔ (A' k < A' j ∨ (A' k = A' j ∧ k ≤ j)) := by
                    intro k j; unfold precedes; rw [hA', hA']
                  have hprec : ∀ k j, A k ≤ t → A j ≤ t → (precedes p' r' α' (e k) (e j) ↔ precedes p r α k j) := by
                    intro k j hk hj
                    rw [hP, hP', hAe k hk, hAe j hj, hle k j ((hAr k).trans hk) ((hAr j).trans hj)]
                  have hPle : ∀ k j, precedes p r α k j → A k ≤ A j := by
                    intro k j h; rw [hP] at h; rcases h with h | h
                    · exact h.le
                    · exact h.1.le
                  have hPle' : ∀ k j, precedes p' r' α' k j → A' k ≤ A' j := by
                    intro k j h; rw [hP'] at h; rcases h with h | h
                    · exact h.le
                    · exact h.1.le
                  intro j hj
                  obtain ⟨hpj, hrj, -, -⟩ := hagree j hj
                  have hlow : A j + p j ≤ onlineCompletion p r α j := by
                    have hjj : precedes p r α j j := Or.inr ⟨rfl, le_rfl⟩
                    have h := (hOC n p r α j _).mp le_rfl j hjj
                    rw [← hA] at h
                    have h2 := Finset.single_le_sum (f := fun i => (p i:ℝ)) (s := Finset.univ.filter (fun i => precedes p r α j i ∧ precedes p r α i j)) (fun i _ => by positivity) (a := j) (by simp [hjj])
                    have h3 := le_max_right (r j:ℝ) (A j)
                    linarith
                  have hlow' : A' (e j) + p' (e j) ≤ onlineCompletion p' r' α' (e j) := by
                    have hjj : precedes p' r' α' (e j) (e j) := Or.inr ⟨rfl, le_rfl⟩
                    have h := (hOC m p' r' α' (e j) _).mp le_rfl (e j) hjj
                    rw [← hA'] at h
                    have h2 := Finset.single_le_sum (f := fun i => (p' i:ℝ)) (s := Finset.univ.filter (fun i => precedes p' r' α' (e j) i ∧ precedes p' r' α' i (e j))) (fun i _ => by positivity) (a := e j) (by simp [hjj])
                    have h3 := le_max_right (r' (e j):ℝ) (A' (e j))
                    linarith
                  by_cases hjt : A j ≤ t
                  · have hterm : ∀ k, precedes p r α k j →
                        max (r' (e k) : ℝ) (A' (e k)) + ∑ i ∈ Finset.univ.filter (fun i => precedes p' r' α' (e k) i ∧ precedes p' r' α' i (e j)), (p' i : ℝ) =
                        max (r k : ℝ) (A k) + ∑ i ∈ Finset.univ.filter (fun i => precedes p r α k i ∧ precedes p r α i j), (p i : ℝ) := by
                      intro k hk
                      have hkt := (hPle k j hk).trans hjt
                      rw [hAe k hkt, (hagree k ((hAr k).trans hkt)).2.1]
                      congr 1
                      symm
                      refine Finset.sum_bij (fun i _ => e i) ?_ ?_ ?_ ?_
                      · intro i hi
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
                        have hit := (hPle i j hi.2).trans hjt
                        exact ⟨(hprec k i hkt hit).mpr hi.1, (hprec i j hit hjt).mpr hi.2⟩
                      · intro i hi i2 hi2 hee
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi2
                        have hit := (hAr i).trans ((hPle i j hi.2).trans hjt)
                        have hit2 := (hAr i2).trans ((hPle i2 j hi2.2).trans hjt)
                        exact le_antisymm ((hle i i2 hit hit2).mp hee.le) ((hle i2 i hit2 hit).mp hee.ge)
                      · intro i' hi'
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'
                        have h1 := hPle' i' (e j) hi'.2
                        rw [hAe j hjt] at h1
                        obtain ⟨i, hit, rfl⟩ := hsurjA i' (h1.trans hjt)
                        refine ⟨i, ?_, rfl⟩
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                        exact ⟨(hprec k i hkt hit).mp hi'.1, (hprec i j hit hjt).mp hi'.2⟩
                      · intro i hi
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                        rw [(hagree i ((hAr i).trans ((hPle i j hi.2).trans hjt))).1]
                    have heq : onlineCompletion p r α j = onlineCompletion p' r' α' (e j) := by
                      apply eq_of_forall_ge_iff
                      intro x
                      rw [hOC, hOC]
                      constructor
                      · intro h k' hk'
                        have h1 := hPle' k' (e j) hk'
                        rw [hAe j hjt] at h1
                        obtain ⟨k, hkt, rfl⟩ := hsurjA k' (h1.trans hjt)
                        have hk := (hprec k j hkt hjt).mp hk'
                        have := h k hk
                        rw [← hA] at this
                        rw [← hA', hterm k hk]
                        exact this
                      · intro h k hk
                        have hkt := (hPle k j hk).trans hjt
                        have := h (e k) ((hprec k j hkt hjt).mpr hk)
                        rw [← hA', hterm k hk] at this
                        rw [← hA]
                        exact this
                    rw [heq, hpj]
                    exact ⟨Iff.rfl, fun _ => rfl⟩
                  · have hjt' : ¬ A' (e j) ≤ t := fun h => hjt ((hAiff j hj t le_rfl).mp h)
                    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
                    · exfalso; linarith
                    · exfalso; linarith
                    · exfalso; linarith
                have hPACK : (∀ j, Measurable (fun x => alphaPoint p (lpSet p r) j x)) ∧
                    (∃ T : ℝ, ∀ j, (r j:ℝ) ≤ T ∧ ∀ x, 0 < x → x ≤ 1 → alphaPoint p (lpSet p r) j x ≤ T) ∧
                    (∑ j, w j * (mLP p r j + (p j:ℝ)/2) ≤ optValue p r w) ∧
                    (∑ j, w j * onlineCompletion p r (fun _ => 1 / Real.sqrt 2) j ≤ (1 + Real.sqrt 2) * optValue p r w) ∧
                    (∀ j, ∃ (σ : ℝ) (N1 N2 : Finset (Fin n)) (ν η : Fin n → ℝ),
                      (∀ k, 0 ≤ ν k ∧ ν k ≤ 1) ∧ (∀ k, 0 ≤ η k ∧ η k ≤ 1) ∧ (∀ k ∈ N2, j ≠ k) ∧
                      (∑ k ∈ N1, (p k:ℝ) * η k ≤ σ) ∧
                      (mLP p r j = σ + (p j:ℝ)/2 + ∑ k ∈ N2, (p k:ℝ) * (1 - ν k)) ∧
                      (∀ a : Fin n → ℝ, (∀ j, a j ∈ Set.Ioc (0:ℝ) 1) → onlineCompletion p r a j ≤
                        ((σ + p j) + p j * a j) + (∑ k ∈ N2, (p k:ℝ) * ((if ν k < a j then (1:ℝ) else 0) * (1 + a k)) +
                        ∑ k ∈ N1, (p k:ℝ) * (if a k ≤ η k then 1 + a k - η k else 0)))) := by
                  clear hGf hsqrt GEN hchar honline
                  have hrun_some : ∀ τ j, lpRun p r τ = some j → r j ≤ τ ∧ 0 < lpRemaining p r τ j ∧
                      ∀ k, r k ≤ τ → 0 < lpRemaining p r τ k → j ≤ k := by
                    intro τ j h
                    unfold lpRun lpPick at h
                    split_ifs at h with hne
                    have h' := Option.some.inj h
                    have hm := Finset.min'_mem _ hne
                    rw [h'] at hm
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
                    refine ⟨hm.1, hm.2, fun k h1 h2 => ?_⟩
                    rw [← h']
                    exact Finset.min'_le _ _ (by simp [h1, h2])
                  have hrun_none : ∀ τ, lpRun p r τ = none → ∀ k, r k ≤ τ → lpRemaining p r τ k = 0 := by
                    intro τ h k hk
                    unfold lpRun lpPick at h
                    split_ifs at h with hne
                    by_contra hc
                    exact hne ⟨k, by simp [hk]; omega⟩
                  have hsucc : ∀ τ j, lpRemaining p r (τ+1) j =
                      if lpRun p r τ = some j then lpRemaining p r τ j - 1 else lpRemaining p r τ j := by
                    intro τ j; rfl
                  have hcnt : ∀ b j, lpRemaining p r b j +
                      ∑ τ ∈ Finset.range b, (if lpRun p r τ = some j then 1 else 0) = p j := by
                    intro b j
                    induction b with
                    | zero => simp [lpRemaining]
                    | succ b ih =>
                      rw [Finset.sum_range_succ, hsucc]
                      split_ifs with h
                      · have := (hrun_some b j h).2.1
                        omega
                      · omega
                  have hnotrel : ∀ b j, b ≤ r j → lpRemaining p r b j = p j := by
                    intro b j
                    induction b with
                    | zero => simp [lpRemaining]
                    | succ b ih =>
                      intro hb
                      rw [hsucc, if_neg, ih (by omega)]
                      intro h
                      have := (hrun_some b j h).1
                      omega
                  have hmono : ∀ b c j, b ≤ c → lpRemaining p r c j ≤ lpRemaining p r b j := by
                    intro b c j hbc
                    induction hbc with
                    | refl => exact le_rfl
                    | step _ ih => 
                      refine le_trans ?_ ih
                      rw [hsucc]; split_ifs <;> omega
                  have hT : ∃ T, ∀ b, T ≤ b → ∀ j, lpRemaining p r b j = 0 := by
                    have key : ∀ s, ∑ j, lpRemaining p r ((∑ j, r j) + s) j ≤ (∑ j, p j) - s := by
                      intro s
                      induction s with
                      | zero =>
                        simp only [add_zero, Nat.sub_zero]
                        exact Finset.sum_le_sum fun j _ => by have := hcnt (∑ j, r j) j; omega
                      | succ s ih =>
                        rcases hc : lpRun p r ((∑ j, r j) + s) with _ | k
                        · have h0 : ∀ j, lpRemaining p r ((∑ j, r j) + (s+1)) j = 0 := by
                            intro j
                            rw [← add_assoc, hsucc, hc]
                            simp only [reduceCtorEq, if_false]
                            exact hrun_none _ hc j (by
                              have := Finset.single_le_sum (f := r) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
                              omega)
                          simp [h0]
                        · have hk := (hrun_some _ _ hc).2.1
                          have hlt : ∑ j, lpRemaining p r ((∑ j, r j) + (s+1)) j
                              < ∑ j, lpRemaining p r ((∑ j, r j) + s) j := by
                            apply Finset.sum_lt_sum
                            · intro j _; exact hmono _ _ _ (by omega)
                            · refine ⟨k, Finset.mem_univ _, ?_⟩
                              rw [← add_assoc, hsucc, hc, if_pos rfl]
                              omega
                          omega
                    refine ⟨(∑ j, r j) + ∑ j, p j, fun b hb j => ?_⟩
                    have h1 := key (∑ j, p j)
                    have h2 := Finset.single_le_sum (f := fun j => lpRemaining p r ((∑ j, r j) + ∑ j, p j) j) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
                    have h3 := hmono _ _ j hb
                    omega
                  have hblockG : ∀ (c : ℝ) (Φ : Fin n → ℝ) (i : Fin n),
                      (∀ a b : ℕ, a < b → (∀ j ≤ i, r j < a → lpRemaining p r a j = 0) →
                        (∀ j ≤ i, r j < b → lpRemaining p r b j = 0) →
                        (∀ τ, a ≤ τ → τ < b → ∃ j ≤ i, lpRun p r τ = some j) →
                        (∑ j ∈ Finset.univ.filter (fun j => j ≤ i ∧ a ≤ r j ∧ r j < b), p j = b - a) →
                        c * (((b:ℝ) - a) * (a + ((b:ℝ)-a)/2)) ≤
                          ∑ j ∈ Finset.univ.filter (fun j => j ≤ i ∧ a ≤ r j ∧ r j < b), Φ j) → ∀ b,
                      (∀ j ≤ i, r j < b → lpRemaining p r b j = 0) →
                      c * ∑ τ ∈ Finset.range b, (if (∃ j ≤ i, lpRun p r τ = some j) then ((τ:ℝ)+1/2) else 0) ≤
                        ∑ j ∈ Finset.univ.filter (fun j => j ≤ i ∧ r j < b), Φ j := by
                    intro c Φ i hH
                    -- work identity
                    have hW : ∀ b, (∀ j ≤ i, r j < b → lpRemaining p r b j = 0) →
                        ∑ j ∈ Finset.univ.filter (fun j => j ≤ i ∧ r j < b), p j =
                          ∑ τ ∈ Finset.range b, (if (∃ j ≤ i, lpRun p r τ = some j) then 1 else 0) := by
                      intro b hb
                      have h1 : ∀ j ∈ Finset.univ.filter (fun j => j ≤ i ∧ r j < b), p j =
                          ∑ τ ∈ Finset.range b, (if lpRun p r τ = some j then 1 else 0) := by
                        intro j hj
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                        have := hcnt b j
                        rw [hb j hj.1 hj.2] at this
                        omega
                      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
                      refine Finset.sum_congr rfl fun τ hτ => ?_
                      rw [Finset.mem_range] at hτ
                      rcases hc : lpRun p r τ with _ | k
                      · simp
                      · have hk := (hrun_some _ _ hc).1
                        simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
                        have hkb : r k < b := by omega
                        simp [hkb]
                    intro b
                    induction b using Nat.strong_induction_on with
                    | _ b IH =>
                    intro hb
                    rcases Nat.eq_zero_or_pos b with rfl | hbpos
                    · simp
                    -- greatest clear a < b
                    obtain ⟨a, ⟨hab, hac⟩, hamax⟩ : ∃ a, (a < b ∧ ∀ j ≤ i, r j < a → lpRemaining p r a j = 0) ∧
                        ∀ c, a < c → c < b → ¬ (∀ j ≤ i, r j < c → lpRemaining p r c j = 0) := by
                      have hex : ∃ a, a ≤ b - 1 ∧ (∀ j ≤ i, r j < a → lpRemaining p r a j = 0) := ⟨0, by omega, by simp⟩
                      have hP := Nat.findGreatest_spec (P := fun a => ∀ j ≤ i, r j < a → lpRemaining p r a j = 0)
                        (n := b - 1) (m := 0) (by omega) (by simp)
                      refine ⟨_, ⟨?_, hP⟩, ?_⟩
                      · have := Nat.findGreatest_le (P := fun a => ∀ j ≤ i, r j < a → lpRemaining p r a j = 0) (b-1)
                        omega
                      · intro c h1 h2
                        exact Nat.findGreatest_is_greatest h1 (by omega)
                    have ha := IH a hab hac
                    -- idle slot => clear
                    have hidle : ∀ τ, (¬ ∃ j ≤ i, lpRun p r τ = some j) → ∀ j ≤ i, r j ≤ τ → lpRemaining p r τ j = 0 := by
                      intro τ hτ j hj hrj
                      rcases hc : lpRun p r τ with _ | k
                      · exact hrun_none _ hc j hrj
                      · by_contra hne
                        have := (hrun_some _ _ hc).2.2 j hrj (by omega)
                        exact hτ ⟨k, le_trans this hj, hc⟩
                    by_cases hall : ∀ τ, a ≤ τ → τ < b → ∃ j ≤ i, lpRun p r τ = some j
                    · -- block
                      have hsplit : ∀ f : ℕ → ℝ, ∑ τ ∈ Finset.range b, f τ = ∑ τ ∈ Finset.range a, f τ + ∑ τ ∈ Finset.Ico a b, f τ := by
                        intro f; rw [Finset.sum_range_add_sum_Ico _ hab.le]
                      have hdiff : Finset.univ.filter (fun j => j ≤ i ∧ r j < b) =
                          (Finset.univ.filter (fun j => j ≤ i ∧ r j < a)) ∪ (Finset.univ.filter (fun j => j ≤ i ∧ a ≤ r j ∧ r j < b)) := by
                        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
                        constructor
                        · rintro ⟨h1, h2⟩
                          by_cases h3 : r j < a
                          · exact Or.inl ⟨h1, h3⟩
                          · exact Or.inr ⟨h1, by omega, h2⟩
                        · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
                          · exact ⟨h1, by omega⟩
                          · exact ⟨h1, h3⟩
                      have hdisj : Disjoint (Finset.univ.filter (fun j => j ≤ i ∧ r j < a)) (Finset.univ.filter (fun j => j ≤ i ∧ a ≤ r j ∧ r j < b)) := by
                        rw [Finset.disjoint_left]
                        intro j h1 h2
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
                        omega
                      set S := Finset.univ.filter (fun j => j ≤ i ∧ a ≤ r j ∧ r j < b) with hS
                      have hpS : ∑ j ∈ S, p j = b - a := by
                        have h1 := hW b hb
                        have h2 := hW a hac
                        rw [hdiff, Finset.sum_union hdisj, h2, ← Finset.sum_range_add_sum_Ico _ hab.le] at h1
                        have h3 : ∑ τ ∈ Finset.Ico a b, (if (∃ j ≤ i, lpRun p r τ = some j) then 1 else 0) = b - a := by
                          rw [Finset.sum_congr rfl (g := fun _ => 1)]
                          · simp
                          · intro τ hτ
                            rw [Finset.mem_Ico] at hτ
                            rw [if_pos (hall τ hτ.1 hτ.2)]
                        rw [h3] at h1
                        omega
                      have hba : (a:ℝ) < b := by exact_mod_cast hab
                      have hsumI : ∀ c, a ≤ c → ∑ τ ∈ Finset.Ico a c, ((τ:ℝ)+1/2) = ((c:ℝ) - a) * (a + ((c:ℝ)-a)/2) := by
                        intro c hc
                        induction c, hc using Nat.le_induction with
                        | base => simp
                        | succ c hc ih => rw [Finset.sum_Ico_succ_top hc, ih]; push_cast; ring
                      rw [hsplit, hdiff, Finset.sum_union hdisj, mul_add]
                      refine add_le_add ha ?_
                      rw [Finset.sum_congr rfl (g := fun τ : ℕ => ((τ:ℝ)+1/2))]
                      · rw [hsumI b hab.le]
                        exact hH a b hab hac hb hall hpS
                      · intro τ hτ
                        rw [Finset.mem_Ico] at hτ
                        rw [if_pos (hall τ hτ.1 hτ.2)]
                    · push Not at hall
                      obtain ⟨τ, h1, h2, h3⟩ := hall
                      have h3' : ¬ ∃ j ≤ i, lpRun p r τ = some j := by push Not; exact h3
                      have h4 := hidle τ h3'
                      have hτ : τ + 1 = b := by
                        by_contra hne
                        refine hamax (τ+1) (by omega) (by omega) ?_
                        intro j hj hrj
                        have := h4 j hj (by omega)
                        have := hmono τ (τ+1) j (by omega)
                        omega
                      have hτa : τ = a := by
                        by_contra hne
                        exact hamax τ (by omega) (by omega) (fun j hj hrj => h4 j hj hrj.le)
                      subst hτa
                      subst hτ
                      rw [Finset.sum_range_succ, if_neg h3', add_zero]
                      refine le_trans ha (le_of_eq ?_)
                      apply Finset.sum_congr _ (fun _ _ => rfl)
                      ext j
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                      refine and_congr_right fun hj => ⟨fun h => by omega, fun h => ?_⟩
                      by_contra hne
                      have e1 := h4 j hj (by omega)
                      have e2 := hnotrel τ j (by omega)
                      have := hp j
                      omega
                  have hblock : ∀ M : Fin n → ℝ, (∀ S : Finset (Fin n), S.Nonempty → ∀ ρ : ℝ, (∀ j ∈ S, ρ ≤ (r j:ℝ)) → (∑ j ∈ S, (p j:ℝ)) * (ρ + (∑ j ∈ S, (p j:ℝ))/2) ≤ ∑ j ∈ S, (p j:ℝ) * M j) → ∀ i : Fin n, ∀ b,
                      (∀ j ≤ i, r j < b → lpRemaining p r b j = 0) →
                      ∑ τ ∈ Finset.range b, (if (∃ j ≤ i, lpRun p r τ = some j) then ((τ:ℝ)+1/2) else 0) ≤
                        ∑ j ∈ Finset.univ.filter (fun j => j ≤ i ∧ r j < b), (p j : ℝ) * M j := by
                    intro M hM i b hb
                    have h := hblockG 1 (fun j => (p j : ℝ) * M j) i ?_ b hb
                    · rw [one_mul] at h; exact h
                    intro a b hab hac hb hall hpS
                    set S := Finset.univ.filter (fun j => j ≤ i ∧ a ≤ r j ∧ r j < b) with hS
                    have hSne : S.Nonempty := by
                      by_contra hne
                      rw [Finset.not_nonempty_iff_eq_empty] at hne
                      rw [hne] at hpS
                      simp at hpS
                      omega
                    have hpS' : ∑ j ∈ S, (p j : ℝ) = (b:ℝ) - a := by
                      rw [← Nat.cast_sub hab.le, ← hpS]; push_cast; rfl
                    have hrm : ∀ j ∈ S, (a:ℝ) ≤ r j := by
                      intro j hj
                      rw [hS] at hj
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                      exact_mod_cast hj.2.1
                    have hcon := hM S hSne a hrm
                    rw [hpS'] at hcon
                    rw [one_mul]
                    exact hcon
                  have habel : ∀ q y : Fin n → ℝ, (∀ j k : Fin n, j ≤ k → q k ≤ q j) → (∀ j, 0 ≤ q j) →
                      (∀ i : Fin n, 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), y j) → 0 ≤ ∑ j, q j * y j := by
                    intro q y hq hq0 hy
                    set q' : ℕ → ℝ := fun j => if h : j < n then q ⟨j, h⟩ else 0 with hq'
                    set y' : ℕ → ℝ := fun j => if h : j < n then y ⟨j, h⟩ else 0 with hy'
                    have hY : ∀ m, m < n → 0 ≤ ∑ j ∈ Finset.range (m+1), y' j := by
                      intro m hm
                      have e := hy ⟨m, hm⟩
                      refine le_trans e (le_of_eq ?_)
                      rw [Finset.sum_filter]
                      have : ∀ j : Fin n, (if j ≤ ⟨m, hm⟩ then y j else 0) = (fun k : ℕ => if k ≤ m then y' k else 0) j := by
                        intro j
                        simp [hy', Fin.le_def]
                      rw [Finset.sum_congr rfl (fun j _ => this j), Fin.sum_univ_eq_sum_range (fun k : ℕ => if k ≤ m then y' k else 0) n, ← Finset.sum_filter]
                      apply Finset.sum_congr _ (fun _ _ => rfl)
                      ext k; simp; omega
                    have main : ∀ m, m < n → q' m * ∑ j ∈ Finset.range (m+1), y' j ≤ ∑ j ∈ Finset.range (m+1), q' j * y' j := by
                      intro m
                      induction m with
                      | zero => intro h; simp
                      | succ m ih =>
                        intro h
                        have i1 := ih (by omega)
                        have i2 := hY m (by omega)
                        rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => q' j * y' j)]
                        have i3 : q' (m+1) ≤ q' m := by
                          simp only [hq', h, show m < n by omega, dif_pos]
                          exact hq _ _ (by simp [Fin.le_def])
                        linarith only [i1, mul_le_mul_of_nonneg_right i3 i2]
                    have hfin : ∑ j, q j * y j = ∑ j ∈ Finset.range n, q' j * y' j := by
                      rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => q' k * y' k) n]
                      exact Finset.sum_congr rfl fun j _ => by simp [hq', hy']
                    rw [hfin]
                    rcases Nat.eq_zero_or_pos n with h0 | h0
                    · rw [h0]; simp
                    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
                      refine le_trans (mul_nonneg ?_ (hY m (by omega))) (main m (by omega))
                      simp only [hq', show m < m + 1 by omega, dif_pos]
                      exact hq0 _
                  obtain ⟨T, hT⟩ := hT
                  have hAeq : ∀ j, lpSet p r j = ⋃ τ ∈ (Finset.range T).filter (fun τ => lpRun p r τ = some j),
                      Set.Ico (τ:ℝ) (τ+1) := by
                    intro j
                    ext x
                    simp only [lpSet, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
                    constructor
                    · rintro ⟨τ, h1, h2⟩
                      refine ⟨τ, ⟨?_, h1⟩, h2⟩
                      by_contra hc
                      have e1 := (hrun_some τ j h1).2.1
                      have e2 := hT τ (by omega) j
                      omega
                    · rintro ⟨τ, ⟨_, h1⟩, h2⟩
                      exact ⟨τ, h1, h2⟩
                  have hIco : ∀ a b : ℕ, a ≠ b → Disjoint (Set.Ico (a:ℝ) (a+1)) (Set.Ico (b:ℝ) (b+1)) := by
                    intro a b hab
                    rw [Set.disjoint_left]
                    rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
                    have e1 : (a:ℝ) < b + 1 := by linarith
                    have e2 : (b:ℝ) < a + 1 := by linarith
                    have e3 : a < b + 1 := by exact_mod_cast e1
                    have e4 : b < a + 1 := by exact_mod_cast e2
                    omega
                  have hAmeas : ∀ j, MeasurableSet (lpSet p r j) := by
                    intro j
                    rw [hAeq]
                    exact Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ico
                  have hAvol : ∀ j, volume (lpSet p r j) = (p j : ENNReal) := by
                    intro j
                    rw [hAeq, measure_biUnion_finset (fun a _ b _ hab => hIco a b hab) (fun _ _ => measurableSet_Ico)]
                    simp only [Real.volume_Ico, add_sub_cancel_left, ENNReal.ofReal_one]
                    have e := hcnt T j
                    rw [hT T le_rfl j, zero_add] at e
                    rw [← e, Finset.sum_filter]
                    push_cast
                    rfl
                  have hAintble : ∀ j, IntegrableOn (fun t : ℝ => t) (lpSet p r j) := by
                    intro j
                    rw [hAeq]
                    rw [integrableOn_finset_iUnion]
                    intro τ _
                    exact (continuous_id.integrableOn_Icc (a := (τ:ℝ)) (b := τ+1)).mono_set Set.Ico_subset_Icc_self
                  have hAint : ∀ j, ∫ t in lpSet p r j, t =
                      ∑ τ ∈ Finset.range T, (if lpRun p r τ = some j then ((τ:ℝ)+1/2) else 0) := by
                    intro j
                    rw [hAeq, integral_biUnion_finset _ (fun _ _ => measurableSet_Ico) (fun a _ b _ hab => hIco a b hab), Finset.sum_filter]
                    · refine Finset.sum_congr rfl fun τ _ => ?_
                      split_ifs
                      · rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_id]
                        ring
                      · rfl
                    · intro τ _
                      exact (continuous_id.integrableOn_Icc (a := (τ:ℝ)) (b := τ+1)).mono_set Set.Ico_subset_Icc_self
                  have hAr : ∀ j, ∀ x ∈ lpSet p r j, (r j : ℝ) ≤ x := by
                    intro j x hx
                    simp only [lpSet, Set.mem_iUnion, exists_prop] at hx
                    obtain ⟨τ, h1, h2⟩ := hx
                    have e : (r j : ℝ) ≤ τ := by exact_mod_cast (hrun_some τ j h1).1
                    exact e.trans h2.1
                  have hAT : ∀ j, ∀ x ∈ lpSet p r j, x ≤ T := by
                    intro j x hx
                    rw [hAeq] at hx
                    simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_range] at hx
                    obtain ⟨τ, h1, h2⟩ := hx
                    have e : ((τ:ℝ) + 1 ) ≤ T := by exact_mod_cast h1.1
                    exact h2.2.le.trans e
                  have hAdisj : ∀ j k, j ≠ k → Disjoint (lpSet p r j) (lpSet p r k) := by
                    intro j k hjk
                    rw [Set.disjoint_left]
                    intro x hx hy
                    simp only [lpSet, Set.mem_iUnion, exists_prop] at hx hy
                    obtain ⟨τ, h1, h2⟩ := hx
                    obtain ⟨σ, h3, h4⟩ := hy
                    by_cases hc : τ = σ
                    · subst hc
                      rw [h1] at h3
                      exact hjk (Option.some.inj h3)
                    · exact Set.disjoint_left.mp (hIco τ σ hc) h2 h4
                  clear hAeq hIco
                  -- F
                  obtain ⟨F, hF⟩ : ∃ F : Fin n → ℝ → ℝ, ∀ j t, F j t = (volume (lpSet p r j ∩ Set.Iic t)).toReal := ⟨_, fun _ _ => rfl⟩
                  have hfin : ∀ j (s : Set ℝ), volume (lpSet p r j ∩ s) ≠ ⊤ := by
                    intro j s
                    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_left)
                    rw [hAvol]; exact ENNReal.natCast_ne_top _
                  have hF0 : ∀ j t, 0 ≤ F j t := fun j t => by rw [hF]; exact ENNReal.toReal_nonneg
                  have hFvol : ∀ j t, volume (lpSet p r j ∩ Set.Iic t) = ENNReal.ofReal (F j t) := by
                    intro j t
                    rw [hF, ENNReal.ofReal_toReal (hfin _ _)]
                  have hFmono : ∀ j s t, s ≤ t → F j s ≤ F j t := by
                    intro j s t hst
                    rw [hF, hF]
                    exact ENNReal.toReal_mono (hfin _ _) (measure_mono (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr hst)))
                  have hFp : ∀ j t, F j t ≤ p j := by
                    intro j t
                    rw [hF]
                    have := ENNReal.toReal_mono (by rw [hAvol]; exact ENNReal.natCast_ne_top _) (measure_mono (μ := volume) (Set.inter_subset_left (s := lpSet p r j) (t := Set.Iic t)))
                    rw [hAvol] at this
                    simpa using this
                  have hFT : ∀ j, F j T = p j := by
                    intro j
                    rw [hF, Set.inter_eq_left.mpr (show lpSet p r j ⊆ Set.Iic (T:ℝ) from fun x hx => hAT j x hx), hAvol]
                    simp
                  have hFr : ∀ j (t : ℝ), t < r j → F j t = 0 := by
                    intro j t ht
                    rw [hF]
                    have : lpSet p r j ∩ Set.Iic t = ∅ := by
                      ext x
                      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_and, not_le]
                      intro hx
                      exact lt_of_lt_of_le ht (hAr j x hx)
                    rw [this]; simp
                  have hFcont : ∀ j, Continuous (F j) := by
                    intro j
                    refine (LipschitzWith.of_le_add (f := F j) fun x y => ?_).continuous
                    rw [hF, hF, Real.dist_eq]
                    have e1 : volume (lpSet p r j ∩ Set.Iic x) ≤ volume (lpSet p r j ∩ Set.Iic y) + ENNReal.ofReal |x - y| := by
                      refine (measure_mono (t := (lpSet p r j ∩ Set.Iic y) ∪ Set.Ioc y x) ?_).trans ((measure_union_le _ _).trans ?_)
                      · rintro z ⟨h1, h2⟩
                        by_cases h : z ≤ y
                        · exact Or.inl ⟨h1, h⟩
                        · exact Or.inr ⟨not_le.mp h, h2⟩
                      · rw [Real.volume_Ioc]
                        gcongr
                        exact le_abs_self _
                    have e2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _ _, ENNReal.ofReal_ne_top⟩) e1
                    rwa [ENNReal.toReal_add (hfin _ _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (abs_nonneg _)] at e2
                  have hFsum : ∀ t, 0 ≤ t → ∑ j, F j t ≤ t := by
                    intro t ht
                    simp only [hF]
                    rw [← ENNReal.toReal_sum (fun j _ => hfin _ _), ← measure_biUnion_finset]
                    · have e : volume (⋃ j ∈ (Finset.univ : Finset (Fin n)), lpSet p r j ∩ Set.Iic t) ≤ ENNReal.ofReal t := by
                        refine (measure_mono (t := Set.Icc 0 t) ?_).trans ?_
                        · intro x hx
                          simp only [Set.mem_iUnion, exists_prop] at hx
                          obtain ⟨j, _, h1, h2⟩ := hx
                          exact ⟨le_trans (Nat.cast_nonneg _) (hAr j x h1), h2⟩
                        · rw [Real.volume_Icc, sub_zero]
                      exact ENNReal.toReal_le_of_le_ofReal ht e
                    · intro a _ b _ hab
                      exact (hAdisj a b hab).mono Set.inter_subset_left Set.inter_subset_left
                    · intro j _
                      exact (hAmeas j).inter measurableSet_Iic
                  -- alpha points
                  obtain ⟨tt, htt⟩ : ∃ tt : Fin n → ℝ → ℝ, ∀ j x, tt j x = alphaPoint p (lpSet p r) j x := ⟨_, fun _ _ => rfl⟩
                  have htt' : ∀ j x, tt j x = sInf {t | x * (p j : ℝ) ≤ F j t} := by
                    intro j x
                    rw [htt]; unfold alphaPoint
                    simp only [hF]
                  have hpR : ∀ j, (0:ℝ) < p j := fun j => by exact_mod_cast hp j
                  have hEr : ∀ j x, 0 < x → ∀ t, x * (p j : ℝ) ≤ F j t → (r j : ℝ) ≤ t := by
                    intro j x hx t ht
                    by_contra hc
                    rw [hFr j t (not_le.mp hc)] at ht
                    have := mul_pos hx (hpR j)
                    linarith
                  have hG : ∀ j x, 0 < x → x ≤ 1 → ∀ s, tt j x ≤ s ↔ x * (p j : ℝ) ≤ F j s := by
                    intro j x hx0 hx1 s
                    have hbdd : BddBelow {t | x * (p j : ℝ) ≤ F j t} := ⟨r j, fun t ht => hEr j x hx0 t ht⟩
                    have hne : {t | x * (p j : ℝ) ≤ F j t}.Nonempty := ⟨T, by
                      simp only [Set.mem_ofPred_eq, hFT]
                      exact mul_le_of_le_one_left (hpR j).le hx1⟩
                    have hcl : IsClosed {t | x * (p j : ℝ) ≤ F j t} := isClosed_le continuous_const (hFcont j)
                    have hmem := hcl.csInf_mem hne hbdd
                    rw [htt']
                    constructor
                    · intro h
                      exact le_trans hmem (hFmono j _ _ h)
                    · intro h
                      exact csInf_le hbdd h
                  clear hFcont
                  have htr : ∀ j x, 0 < x → x ≤ 1 → (r j : ℝ) ≤ tt j x := by
                    intro j x h0 h1
                    exact hEr j x h0 _ ((hG j x h0 h1 _).mp le_rfl)
                  have htt0 : ∀ j x, 0 ≤ tt j x := by
                    intro j x
                    by_cases h0 : 0 < x
                    · by_cases h1 : x ≤ 1
                      · exact le_trans (Nat.cast_nonneg _) (htr j x h0 h1)
                      · rw [htt']
                        apply Real.sInf_nonneg
                        intro t ht
                        exact le_trans (Nat.cast_nonneg _) (hEr j x h0 t ht)
                    · rw [htt']
                      have : {t | x * (p j : ℝ) ≤ F j t} = Set.univ := by
                        ext t
                        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
                        have := hF0 j t
                        nlinarith [hpR j]
                      rw [this, Real.sInf_univ]
                  clear hEr
                  have htt_out : ∀ j x, x ∉ Set.Ioc (0:ℝ) 1 → tt j x = 0 := by
                    intro j x hx
                    rw [htt']
                    by_cases h0 : 0 < x
                    · have h1 : 1 < x := by
                        by_contra h; exact hx ⟨h0, not_lt.mp h⟩
                      have : {t | x * (p j : ℝ) ≤ F j t} = ∅ := by
                        ext t
                        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
                        have := hFp j t
                        nlinarith [hpR j]
                      rw [this, Real.sInf_empty]
                    · have : {t | x * (p j : ℝ) ≤ F j t} = Set.univ := by
                        ext t
                        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
                        have := hF0 j t
                        nlinarith [hpR j]
                      rw [this, Real.sInf_univ]
                  have httm : ∀ j, Measurable (tt j) := by
                    intro j
                    apply measurable_of_Iic
                    intro s
                    have : tt j ⁻¹' Set.Iic s = (Set.Ioc 0 1 ∩ {x | x * (p j : ℝ) ≤ F j s}) ∪ ((Set.Ioc 0 1)ᶜ ∩ {x | 0 ≤ s}) := by
                      ext x
                      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff]
                      by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
                      · simp [hx, hG j x hx.1 hx.2 s]
                      · simp [hx, htt_out j x hx]
                    rw [this]
                    refine (measurableSet_Ioc.inter (measurableSet_le (by fun_prop) measurable_const)).union (measurableSet_Ioc.compl.inter (MeasurableSet.const _))
                  clear htt_out htt'
                  have hM : ∀ j, (p j : ℝ) * mLP p r j = ∫ t in lpSet p r j, t := by
                    intro j
                    unfold mLP meanBusyTime
                    have := (hpR j).ne'
                    field_simp
                  have hM0 : ∀ j, 0 ≤ mLP p r j := by
                    intro j
                    unfold mLP meanBusyTime
                    refine mul_nonneg (by positivity) (setIntegral_nonneg (hAmeas j) fun x hx => le_trans (Nat.cast_nonneg _) (hAr j x hx))
                  have hEt : ∀ j, ∫⁻ x in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (tt j x) = ENNReal.ofReal (mLP p r j) := by
                    intro j
                    have e1 := lintegral_eq_lintegral_meas_lt (volume.restrict (Set.Ioc (0:ℝ) 1)) (f := tt j)
                      (Filter.Eventually.of_forall fun x => htt0 j x) (httm j).aemeasurable
                    have e2 := lintegral_eq_lintegral_meas_lt (volume.restrict (lpSet p r j)) (f := fun t => t)
                      ((ae_restrict_iff' (hAmeas j)).mpr (Filter.Eventually.of_forall fun x hx => le_trans (Nat.cast_nonneg _) (hAr j x hx))) measurable_id.aemeasurable
                    have e3 : ENNReal.ofReal (p j) * ∫⁻ x in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (tt j x) = ∫⁻ t in lpSet p r j, ENNReal.ofReal t := by
                      rw [e1, e2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                      apply lintegral_congr
                      intro s
                      rw [Measure.restrict_apply (measurableSet_lt measurable_const (httm j)),
                        Measure.restrict_apply (show MeasurableSet {a : ℝ | s < a} from measurableSet_Ioi)]
                      have s1 : {x | s < tt j x} ∩ Set.Ioc 0 1 = if 0 ≤ s then Set.Ioc (F j s / p j) 1 else Set.Ioc (F j s / p j) 1 := by
                        rw [ite_self]
                        ext x
                        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
                        constructor
                        · rintro ⟨h1, h2, h3⟩
                          refine ⟨?_, h3⟩
                          rw [div_lt_iff₀ (hpR j)]
                          by_contra hc
                          exact absurd ((hG j x h2 h3 s).mpr (not_lt.mp hc)) (not_le.mpr h1)
                        · rintro ⟨h1, h3⟩
                          have h2 : 0 < x := lt_of_le_of_lt (div_nonneg (hF0 j s) (hpR j).le) h1
                          refine ⟨?_, h2, h3⟩
                          rw [div_lt_iff₀ (hpR j)] at h1
                          by_contra hc
                          exact absurd ((hG j x h2 h3 s).mp (not_lt.mp hc)) (not_le.mpr h1)
                      rw [s1, ite_self, Real.volume_Ioc, ← ENNReal.ofReal_mul (hpR j).le]
                      have s2 : volume ({a | s < a} ∩ lpSet p r j) = ENNReal.ofReal (p j) - ENNReal.ofReal (F j s) := by
                        have : {a | s < a} ∩ lpSet p r j = lpSet p r j \ (lpSet p r j ∩ Set.Iic s) := by
                          ext x
                          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_Iic, not_and, not_le]
                          tauto
                        rw [this, measure_sdiff Set.inter_subset_left ((hAmeas j).inter measurableSet_Iic).nullMeasurableSet (hfin _ _), hAvol, hFvol]
                        simp
                      rw [s2, ← ENNReal.ofReal_sub _ (hF0 j s)]
                      congr 1
                      have := (hpR j).ne'
                      field_simp
                    have e4 : ∫⁻ t in lpSet p r j, ENNReal.ofReal t = ENNReal.ofReal (p j) * ENNReal.ofReal (mLP p r j) := by
                      rw [← ENNReal.ofReal_mul (hpR j).le, hM, ofReal_integral_eq_lintegral_ofReal (hAintble j)]
                      exact (ae_restrict_iff' (hAmeas j)).mpr (Filter.Eventually.of_forall fun x hx => le_trans (Nat.cast_nonneg _) (hAr j x hx))
                    rw [e4] at e3
                    exact (ENNReal.mul_right_inj (by simpa using (hp j).ne') ENNReal.ofReal_ne_top).mp e3
                  clear hAintble
                  have hrT : ∀ j, r j < T := by
                    intro j
                    by_contra hc
                    have e1 := hnotrel T j (by omega)
                    have e2 := hT T le_rfl j
                    have := hp j
                    omega
                  have hpre : ∀ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), (p j : ℝ) * mLP p r j =
                      ∑ τ ∈ Finset.range T, (if (∃ j ≤ i, lpRun p r τ = some j) then ((τ:ℝ)+1/2) else 0) := by
                    intro i
                    simp only [hM, hAint]
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun τ hτ => ?_
                    rcases hc : lpRun p r τ with _ | k
                    · simp
                    · simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and, exists_eq_right']
                  clear hAint hM hnotrel hsucc
                  have hLB : ∀ M : Fin n → ℝ, (∀ S : Finset (Fin n), S.Nonempty → ∀ ρ : ℝ, (∀ j ∈ S, ρ ≤ (r j:ℝ)) → (∑ j ∈ S, (p j:ℝ)) * (ρ + (∑ j ∈ S, (p j:ℝ))/2) ≤ ∑ j ∈ S, (p j:ℝ) * M j) → ∑ j, w j * mLP p r j ≤ ∑ j, w j * M j := by
                    intro M hMf
                    have h1 := habel (fun j => w j / p j) (fun j => (p j : ℝ) * (M j - mLP p r j)) hsort
                      (fun j => div_nonneg (hw j).le (hpR j).le) ?_
                    · have h2 : ∑ j, w j / p j * ((p j : ℝ) * (M j - mLP p r j)) = ∑ j, w j * M j - ∑ j, w j * mLP p r j := by
                        rw [← Finset.sum_sub_distrib]
                        refine Finset.sum_congr rfl fun j _ => ?_
                        have := (hpR j).ne'
                        field_simp
                      linarith
                    · intro i
                      have h2 := hblock M hMf i T (fun j _ _ => hT T le_rfl j)
                      have h3 : Finset.univ.filter (fun j => j ≤ i ∧ r j < T) = Finset.univ.filter (fun j => j ≤ i) := by
                        ext j; simp [hrT j]
                      rw [h3] at h2
                      have h4 := hpre i
                      simp only [mul_sub, Finset.sum_sub_distrib]
                      linarith

                  clear hblock
                  have hOPT : ∑ j, w j * (mLP p r j + (p j:ℝ)/2) ≤ optValue p r w := by
                    unfold optValue
                    apply le_csInf
                    · refine Set.Nonempty.image _ ⟨fun j => (∑ i, (r i : ℝ)) + ∑ i ∈ Finset.univ.filter (· < j), (p i : ℝ), ?_, ?_⟩
                      · intro j
                        have h1 : (r j : ℝ) ≤ ∑ i, (r i : ℝ) :=
                          Finset.single_le_sum (f := fun i => (r i : ℝ)) (fun i _ => by positivity) (Finset.mem_univ j)
                        have h3 : (0:ℝ) ≤ ∑ i ∈ Finset.univ.filter (· < j), (p i : ℝ) :=
                          Finset.sum_nonneg (fun i _ => by positivity)
                        simp only; linarith
                      · have key : ∀ j k : Fin n, j < k → ∑ i ∈ Finset.univ.filter (· < j), (p i : ℝ) + p j ≤
                            ∑ i ∈ Finset.univ.filter (· < k), (p i : ℝ) := by
                          intro j k hjk
                          have hsub : insert j (Finset.univ.filter (· < j)) ⊆ Finset.univ.filter (· < k) := by
                            intro x hx
                            simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
                            rcases hx with rfl | hx
                            · exact hjk
                            · exact lt_trans hx hjk
                          have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun i => (p i : ℝ))
                            (fun i _ _ => by positivity)
                          rw [Finset.sum_insert (by simp)] at this
                          linarith
                        intro j k hjk
                        rcases lt_or_gt_of_ne hjk with h | h
                        · left; have := key j k h; simp only; linarith
                        · right; have := key k j h; simp only; linarith
                    · rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩
                      have hfe : ∀ ρ : ℝ, ∀ S : Finset (Fin n), (∀ j ∈ S, ρ ≤ (r j:ℝ)) →
                          ((∑ j ∈ S, (p j:ℝ)) * (ρ + (∑ j ∈ S, (p j:ℝ))/2) ≤ ∑ j ∈ S, (p j:ℝ) * (s j + (p j:ℝ)/2)) ∧
                          (∀ x, ρ ≤ x → (∀ j ∈ S, s j + p j ≤ x) → ρ + ∑ j ∈ S, (p j:ℝ) ≤ x) := by
                        intro ρ S
                        induction S using Finset.induction_on_max_value s with
                        | empty => intro _; simp
                        | insert j S hjS hmax ih =>
                          intro hρ
                          obtain ⟨i1, i2⟩ := ih (fun k hk => hρ k (Finset.mem_insert_of_mem hk))
                          have h1 : ρ + ∑ k ∈ S, (p k:ℝ) ≤ s j := by
                            apply i2
                            · exact (hρ j (Finset.mem_insert_self _ _)).trans (hs1 j)
                            · intro k hk
                              rcases hs2 k j (by rintro rfl; exact hjS hk) with h | h
                              · exact h
                              · have := hmax k hk
                                have := hpR j
                                linarith
                          constructor
                          · rw [Finset.sum_insert hjS, Finset.sum_insert hjS]
                            have := mul_le_mul_of_nonneg_left h1 (hpR j).le
                            linarith only [this, i1]
                          · intro x _ hx2
                            have := hx2 j (Finset.mem_insert_self _ _)
                            rw [Finset.sum_insert hjS]
                            linarith
                      have h := hLB (fun j => s j + (p j:ℝ)/2) (fun S _ ρ hρ => (hfe ρ S hρ).1)
                      have e1 : ∑ j, w j * (mLP p r j + (p j:ℝ)/2) = ∑ j, w j * mLP p r j + ∑ j, w j * ((p j:ℝ)/2) := by
                        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
                      have e2 : ∑ j, w j * (s j + (p j:ℝ)) = ∑ j, w j * (s j + (p j:ℝ)/2) + ∑ j, w j * ((p j:ℝ)/2) := by
                        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
                      simp only
                      rw [e1, e2]
                      linarith
                  clear hLB
                  have hFdiff : ∀ (X : Finset (Fin n)) (s t : ℝ), s ≤ t → ∑ i ∈ X, (F i t - F i s) ≤ t - s := by
                    intro X s t hst
                    have h1 : ∀ i, F i t - F i s ≤ (volume (lpSet p r i ∩ Set.Ioc s t)).toReal := by
                      intro i
                      have e1 : volume (lpSet p r i ∩ Set.Iic t) ≤ volume (lpSet p r i ∩ Set.Iic s) + volume (lpSet p r i ∩ Set.Ioc s t) := by
                        refine (measure_mono ?_).trans (measure_union_le _ _)
                        rintro z ⟨h1, h2⟩
                        by_cases h : z ≤ s
                        · exact Or.inl ⟨h1, h⟩
                        · exact Or.inr ⟨h1, not_le.mp h, h2⟩
                      have e2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _ _, hfin _ _⟩) e1
                      rw [ENNReal.toReal_add (hfin _ _) (hfin _ _), ← hF, ← hF] at e2
                      linarith
                    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
                    rw [← ENNReal.toReal_sum (fun j _ => hfin _ _), ← measure_biUnion_finset]
                    · have e : volume (⋃ j ∈ X, lpSet p r j ∩ Set.Ioc s t) ≤ ENNReal.ofReal (t - s) := by
                        refine (measure_mono (t := Set.Ioc s t) ?_).trans ?_
                        · intro x hx
                          simp only [Set.mem_iUnion, exists_prop] at hx
                          obtain ⟨j, _, h1, h2⟩ := hx
                          exact h2
                        · rw [Real.volume_Ioc]
                      exact ENNReal.toReal_le_of_le_ofReal (by linarith) e
                    · intro a _ b _ hab
                      exact (hAdisj a b hab).mono Set.inter_subset_left Set.inter_subset_left
                    · intro j _
                      exact (hAmeas j).inter measurableSet_Ioc
                  have hcover : ∀ (X : Finset (Fin n)) (a t : ℝ), (∀ x, a ≤ x → x < t → ∃ k ∈ X, x ∈ lpSet p r k) →
                      t - a ≤ ∑ k ∈ X, F k t := by
                    intro X a t h
                    have e : ENNReal.ofReal (t - a) ≤ ∑ k ∈ X, volume (lpSet p r k ∩ Set.Iic t) := by
                      rw [← Real.volume_Ico]
                      refine (measure_mono ?_).trans (measure_biUnion_finset_le X _)
                      intro x hx
                      obtain ⟨k, hk, hk2⟩ := h x hx.1 hx.2
                      simp only [Set.mem_iUnion, exists_prop]
                      exact ⟨k, hk, hk2, hx.2.le⟩
                    simp only [hFvol] at e
                    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hF0 k t)] at e
                    exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun k _ => hF0 k t)).mp e
                  have hFeq : ∀ j x, 0 < x → x ≤ 1 → F j (tt j x) = x * p j := by
                    intro j x h0 h1
                    apply le_antisymm _ ((hG j x h0 h1 _).mp le_rfl)
                    apply le_of_forall_pos_le_add
                    intro ε hε
                    have e1 := hFdiff {j} (tt j x - ε) (tt j x) (by linarith)
                    rw [Finset.sum_singleton] at e1
                    have e2 : ¬ x * (p j:ℝ) ≤ F j (tt j x - ε) := by
                      rw [← hG j x h0 h1]; linarith
                    linarith
                  clear hFvol
                  have hFint : ∀ j (b : ℕ), lpRemaining p r b j = 0 → F j b = p j := by
                    intro j b hb
                    rw [hF, Set.inter_eq_left.mpr, hAvol]
                    · simp
                    · intro x hx
                      simp only [lpSet, Set.mem_iUnion, exists_prop] at hx
                      obtain ⟨τ, h1, h2⟩ := hx
                      have e : τ < b := by
                        by_contra hc
                        have := hmono b τ j (by omega)
                        have := (hrun_some τ j h1).2.1
                        omega
                      have e' : ((τ:ℝ) + 1) ≤ b := by exact_mod_cast e
                      exact h2.2.le.trans e'
                  clear hAvol
                  have hfloor : ∀ j x, x ∈ lpSet p r j ↔ (0 ≤ x ∧ lpRun p r ⌊x⌋₊ = some j) := by
                    intro j x
                    simp only [lpSet, Set.mem_iUnion, exists_prop]
                    constructor
                    · rintro ⟨τ, h1, h2, h3⟩
                      have h0 : (0:ℝ) ≤ x := le_trans (Nat.cast_nonneg _) h2
                      refine ⟨h0, ?_⟩
                      rw [(Nat.floor_eq_iff h0).mpr ⟨h2, h3⟩]; exact h1
                    · rintro ⟨h0, h⟩
                      exact ⟨⌊x⌋₊, h, Nat.floor_le h0, Nat.lt_floor_add_one x⟩
                  have hPle : ∀ a k i, precedes p r a k i → tt k (a k) ≤ tt i (a i) := by
                    intro a k i h
                    unfold precedes at h
                    rw [← htt, ← htt] at h
                    rcases h with h | h
                    · exact h.le
                    · exact h.1.le
                  have hPnot : ∀ a k i, ¬ precedes p r a k i → tt i (a i) ≤ tt k (a k) := by
                    intro a k i h
                    unfold precedes at h
                    rw [← htt, ← htt] at h
                    push Not at h
                    exact h.1
                  have hCgen : ∀ a : Fin n → ℝ, (∀ j, a j ∈ Set.Ioc (0:ℝ) 1) → ∀ j,
                      onlineCompletion p r a j ≤ tt j (a j) +
                        ∑ k ∈ Finset.univ.filter (fun k => precedes p r a k j), ((1 + a k) * p k - F k (tt j (a j))) := by
                    intro a ha j
                    rw [hOC]
                    intro k hk
                    rw [← htt, max_eq_right (htr k _ (ha k).1 (ha k).2)]
                    have h1 := hFdiff (Finset.univ.filter (fun i => precedes p r a k i ∧ precedes p r a i j)) _ _ (hPle a k j hk)
                    have h2 : ∑ i ∈ Finset.univ.filter (fun i => precedes p r a k i ∧ precedes p r a i j), (F i (tt j (a j)) - a i * p i) ≤
                        ∑ i ∈ Finset.univ.filter (fun i => precedes p r a k i ∧ precedes p r a i j), (F i (tt j (a j)) - F i (tt k (a k))) := by
                      refine Finset.sum_le_sum fun i hi => ?_
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                      have := hFmono i _ _ (hPle a k i hi.1)
                      rw [hFeq i _ (ha i).1 (ha i).2] at this
                      linarith
                    have h3 : ∑ i ∈ Finset.univ.filter (fun i => precedes p r a k i ∧ precedes p r a i j), ((1 + a i) * p i - F i (tt j (a j))) ≤
                        ∑ i ∈ Finset.univ.filter (fun i => precedes p r a i j), ((1 + a i) * p i - F i (tt j (a j))) := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg
                      · intro i hi
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
                        exact hi.2
                      · intro i _ _
                        have := hFp i (tt j (a j))
                        have := mul_pos (ha i).1 (hpR i)
                        linarith
                    have h4 : ∑ i ∈ Finset.univ.filter (fun i => precedes p r a k i ∧ precedes p r a i j), ((1 + a i) * p i - F i (tt j (a j))) =
                        ∑ i ∈ Finset.univ.filter (fun i => precedes p r a k i ∧ precedes p r a i j), (p i:ℝ) -
                        ∑ i ∈ Finset.univ.filter (fun i => precedes p r a k i ∧ precedes p r a i j), (F i (tt j (a j)) - a i * p i) := by
                      rw [← Finset.sum_sub_distrib]
                      exact Finset.sum_congr rfl fun i _ => by ring
                    linarith
                  have hdet : ∑ j, w j * onlineCompletion p r (fun _ => 1 / Real.sqrt 2) j ≤
                        (1 + Real.sqrt 2) * optValue p r w := by
                    clear hrun_none hcnt hAr hAdisj hAT hAmeas hF hfin hFT hFr htt htt0 httm hM0 hEt hFdiff hOC hFp
                    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.sqrt 2 := ⟨_, rfl⟩
                    have hq0 : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr (by norm_num)
                    have hqq : q * q = 2 := by rw [hq]; exact Real.mul_self_sqrt (by norm_num)
                    have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_sqrt.mpr (by norm_num)
                    rw [← hq]
                    obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 / q := ⟨_, rfl⟩
                    rw [← hα]
                    have hαq : α * q = 1 := by rw [hα]; field_simp
                    have hα0 : 0 < α := by rw [hα]; exact one_div_pos.mpr hq0
                    have hα1 : α ≤ 1 := by rw [hα]; exact (div_le_one hq0).mpr hq1
                    have hα2 : 2 * α = q := by linear_combination α * hqq * (-1) + q * hαq
                    obtain ⟨C, hCdef⟩ : ∃ C : Fin n → ℝ, ∀ j, C j = onlineCompletion p r (fun _ => α) j := ⟨_, fun _ => rfl⟩
                    simp only [← hCdef]
                    have hC1 := hCgen (fun _ => α) (fun _ => ⟨hα0, hα1⟩)
                    simp only [← hCdef] at hC1
                    have hblk : ∀ i : Fin n, ∀ a b : ℕ, a < b → (∀ j ≤ i, r j < a → lpRemaining p r a j = 0) →
                        (∀ j ≤ i, r j < b → lpRemaining p r b j = 0) →
                        (∀ τ, a ≤ τ → τ < b → ∃ j ≤ i, lpRun p r τ = some j) →
                        (∑ j ∈ Finset.univ.filter (fun j => j ≤ i ∧ a ≤ r j ∧ r j < b), p j = b - a) →
                        (-(1 + q)) * (((b:ℝ) - a) * (a + ((b:ℝ)-a)/2)) ≤
                          ∑ j ∈ Finset.univ.filter (fun j => j ≤ i ∧ a ≤ r j ∧ r j < b),
                            ((1 + q) * ((p j:ℝ)^2/2) - p j * C j) := by
                      intro i a b hab hac hb hall hpS
                      set S := Finset.univ.filter (fun j => j ≤ i ∧ a ≤ r j ∧ r j < b) with hS
                      have hpS' : ∑ j ∈ S, (p j : ℝ) = (b:ℝ) - a := by
                        rw [← Nat.cast_sub hab.le, ← hpS]; push_cast; rfl
                      have hSmem : ∀ j, j ∈ S ↔ (j ≤ i ∧ a ≤ r j ∧ r j < b) := by
                        intro j; rw [hS]; simp
                      have hCj : ∀ j ∈ S, C j ≤ (1 + q) * a + α * ((b:ℝ) - a) +
                          ∑ k ∈ S, (if precedes p r (fun _ => α) k j then (p k:ℝ) else 0) := by
                        intro j hj
                        obtain ⟨hj1, hj2, hj3⟩ := (hSmem j).mp hj
                        obtain ⟨t, ht⟩ : ∃ t, t = tt j α := ⟨_, rfl⟩
                        have htb : t ≤ b := by
                          rw [ht, hG j α hα0 hα1, hFint j b (hb j hj1 hj3)]
                          exact mul_le_of_le_one_left (hpR j).le hα1
                        have hat : (a:ℝ) ≤ t := by
                          rw [ht]; exact le_trans (by exact_mod_cast hj2) (htr j α hα0 hα1)
                        have hcov : t - a ≤ ∑ k ∈ S, F k t := by
                          apply hcover
                          intro x hx1 hx2
                          have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx1
                          have f1 : a ≤ ⌊x⌋₊ := Nat.le_floor hx1
                          have f2 : ⌊x⌋₊ < b := (Nat.floor_lt hx0).mpr (lt_of_lt_of_le hx2 htb)
                          obtain ⟨k, hk1, hk2⟩ := hall _ f1 f2
                          refine ⟨k, (hSmem k).mpr ⟨hk1, ?_, ?_⟩, (hfloor k x).mpr ⟨hx0, hk2⟩⟩
                          · by_contra hc
                            have e1 := hac k hk1 (by omega)
                            have e2 := hmono a ⌊x⌋₊ k f1
                            have e3 := (hrun_some _ _ hk2).2.1
                            omega
                          · have := (hrun_some _ _ hk2).1; omega
                        have hsum := hFsum t (le_trans (Nat.cast_nonneg _) hat)
                        rw [← Finset.sum_add_sum_compl S] at hsum
                        have h1 := hC1 j
                        simp only [← ht] at h1
                        rw [Finset.sum_filter, ← Finset.sum_add_sum_compl S] at h1
                        have h2 : ∑ k ∈ S, (if precedes p r (fun _ => α) k j then ((1 + α) * p k - F k t) else 0) ≤
                            ∑ k ∈ S, ((if precedes p r (fun _ => α) k j then (p k:ℝ) else 0) + (α * p k - F k t)) := by
                          refine Finset.sum_le_sum fun k _ => ?_
                          split_ifs with hk
                          · linarith
                          · have e1 := hPnot (fun _ => α) k j hk
                            simp only [← ht] at e1
                            have e2 := hFmono k _ _ e1
                            rw [hFeq k α hα0 hα1] at e2
                            linarith
                        have h3 : ∑ k ∈ Sᶜ, (if precedes p r (fun _ => α) k j then ((1 + α) * p k - F k t) else 0) ≤
                            ∑ k ∈ Sᶜ, q * F k t := by
                          refine Finset.sum_le_sum fun k _ => ?_
                          split_ifs with hk
                          · have e1 := hPle (fun _ => α) k j hk
                            simp only [← ht] at e1
                            rw [hG k α hα0 hα1] at e1
                            have e2 := mul_le_mul_of_nonneg_left e1 hq0.le
                            have e3 : q * (α * p k) = p k := by rw [← mul_assoc, mul_comm q α, hαq, one_mul]
                            linarith
                          · exact mul_nonneg hq0.le (hF0 k t)
                        rw [← Finset.mul_sum] at h3
                        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hpS'] at h2
                        have h4 : q * ∑ k ∈ Sᶜ, F k t ≤ q * a := mul_le_mul_of_nonneg_left (by linarith) hq0.le
                        linarith only [h1, h2, h3, h4, hcov, hsum]
                      have hsym : 2 * ∑ j ∈ S, (p j:ℝ) * ∑ k ∈ S, (if precedes p r (fun _ => α) k j then (p k:ℝ) else 0) =
                          ((b:ℝ) - a)^2 + ∑ j ∈ S, (p j:ℝ)^2 := by
                        have e1 : ∑ j ∈ S, (p j:ℝ) * ∑ k ∈ S, (if precedes p r (fun _ => α) k j then (p k:ℝ) else 0) =
                            ∑ j ∈ S, ∑ k ∈ S, (if precedes p r (fun _ => α) k j then (p j:ℝ) * p k else 0) := by
                          refine Finset.sum_congr rfl fun j _ => ?_
                          rw [Finset.mul_sum]
                          refine Finset.sum_congr rfl fun k _ => ?_
                          rw [mul_ite, mul_zero]
                        have e2 : ∑ j ∈ S, ∑ k ∈ S, (if precedes p r (fun _ => α) k j then (p j:ℝ) * p k else 0) =
                            ∑ j ∈ S, ∑ k ∈ S, (if precedes p r (fun _ => α) j k then (p j:ℝ) * p k else 0) := by
                          rw [Finset.sum_comm]
                          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
                          rw [mul_comm]
                        rw [two_mul, e1]
                        nth_rewrite 2 [e2]
                        rw [← Finset.sum_add_distrib, ← hpS', pow_two, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
                        refine Finset.sum_congr rfl fun j hj => ?_
                        have e3 : (p j:ℝ)^2 = ∑ k ∈ S, if j = k then (p j:ℝ) * p k else 0 := by
                          rw [Finset.sum_ite_eq, if_pos hj, pow_two]
                        rw [e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                        refine Finset.sum_congr rfl fun k _ => ?_
                        unfold precedes
                        simp only
                        rcases lt_trichotomy (alphaPoint p (lpSet p r) k α) (alphaPoint p (lpSet p r) j α) with h | h | h
                        · have hne : j ≠ k := by rintro rfl; exact lt_irrefl _ h
                          simp [h, hne, not_lt.mpr h.le, h.ne']
                        · rcases lt_trichotomy j k with h' | h' | h'
                          · simp [h, h'.ne, h'.le, not_le.mpr h']
                          · subst h'; simp
                          · simp [h, h'.ne', h'.le, not_le.mpr h']
                        · have hne : j ≠ k := by rintro rfl; exact lt_irrefl _ h
                          simp [h, hne, not_lt.mpr h.le, h.ne']
                      have hmain : ∑ j ∈ S, (p j:ℝ) * C j ≤ ∑ j ∈ S, (p j:ℝ) * ((1 + q) * a + α * ((b:ℝ) - a) +
                          ∑ k ∈ S, (if precedes p r (fun _ => α) k j then (p k:ℝ) else 0)) :=
                        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hCj j hj) (hpR j).le
                      simp only [mul_add (_ : ℝ) (_ + _ : ℝ) _] at hmain
                      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hpS'] at hmain
                      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
                      have hsq : 0 ≤ ∑ j ∈ S, (p j:ℝ)^2 := Finset.sum_nonneg fun j _ => by positivity
                      have hα3 : α = q / 2 := by linarith
                      rw [hα3] at hmain
                      have hba : (0:ℝ) ≤ (b:ℝ) - a := by
                        have : (a:ℝ) < b := by exact_mod_cast hab
                        linarith
                      rw [hα3] at hsym
                      linarith only [mul_nonneg hq0.le hsq, hmain, hsym]
                    have hpref : ∀ i : Fin n, 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => j ≤ i),
                        (p j:ℝ) * ((1 + q) * (mLP p r j + (p j:ℝ)/2) - C j) := by
                      intro i
                      have h2 := hblockG _ _ i (hblk i) T (fun j _ _ => hT T le_rfl j)
                      have h3 : Finset.univ.filter (fun j => j ≤ i ∧ r j < T) = Finset.univ.filter (fun j => j ≤ i) := by
                        ext j; simp [hrT j]
                      rw [h3, ← hpre i] at h2
                      have h4 : ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), (p j:ℝ) * ((1 + q) * (mLP p r j + (p j:ℝ)/2) - C j) =
                          (1 + q) * ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), (p j : ℝ) * mLP p r j +
                          ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), ((1 + q) * ((p j:ℝ)^2/2) - p j * C j) := by
                        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                        exact Finset.sum_congr rfl fun j _ => by ring
                      rw [h4]
                      linarith
                    have h1 := habel (fun j => w j / p j) _ hsort (fun j => div_nonneg (hw j).le (hpR j).le) hpref
                    have h2 : ∑ j, w j / p j * ((p j:ℝ) * ((1 + q) * (mLP p r j + (p j:ℝ)/2) - C j)) =
                        (1 + q) * ∑ j, w j * (mLP p r j + (p j:ℝ)/2) - ∑ j, w j * C j := by
                      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                      refine Finset.sum_congr rfl fun j _ => ?_
                      have := (hpR j).ne'
                      field_simp
                    have h3 := mul_le_mul_of_nonneg_left hOPT (show (0:ℝ) ≤ 1 + q by linarith only [hq0])
                    linarith only [h1, h2, h3]
                  have hcore : (∀ j, ∃ (σ : ℝ) (N1 N2 : Finset (Fin n)) (ν η : Fin n → ℝ),
                        (∀ k, 0 ≤ ν k ∧ ν k ≤ 1) ∧ (∀ k, 0 ≤ η k ∧ η k ≤ 1) ∧ (∀ k ∈ N2, j ≠ k) ∧
                        (∑ k ∈ N1, (p k:ℝ) * η k ≤ σ) ∧
                        (mLP p r j = σ + (p j:ℝ)/2 + ∑ k ∈ N2, (p k:ℝ) * (1 - ν k)) ∧
                        (∀ a : Fin n → ℝ, (∀ j, a j ∈ Set.Ioc (0:ℝ) 1) → onlineCompletion p r a j ≤
                          ((σ + p j) + p j * a j) + (∑ k ∈ N2, (p k:ℝ) * ((if ν k < a j then (1:ℝ) else 0) * (1 + a k)) +
                          ∑ k ∈ N1, (p k:ℝ) * (if a k ≤ η k then 1 + a k - η k else 0)))) := by
                    clear hdet hOPT hsort hw hblockG habel hrT hpre hPnot hAdisj hAT hAmeas hFT htt htr hOC
                    intro j
                    have hexσ : ∃ σ, lpRun p r σ = some j := by
                      by_contra hc
                      push Not at hc
                      have e := hcnt T j
                      rw [hT T le_rfl j] at e
                      simp only [hc] at e
                      have := hp j
                      simp at e
                      omega
                    obtain ⟨σ, hσr, hσm⟩ : ∃ σ, lpRun p r σ = some j ∧ ∀ τ, lpRun p r τ = some j → σ ≤ τ :=
                      ⟨Nat.find hexσ, Nat.find_spec hexσ, fun τ hτ => Nat.find_min' hexσ hτ⟩
                    obtain ⟨hσ1, hσ2, hσ3⟩ := hrun_some σ j hσr
                    have hconst : ∀ k (s t : ℝ), (∀ x, s < x → x < t → x ∉ lpSet p r k) → F k t ≤ F k s := by
                      intro k s t h
                      rw [hF, hF]
                      apply ENNReal.toReal_mono (hfin _ _)
                      have hsub : lpSet p r k ∩ Set.Iic t ⊆ (lpSet p r k ∩ Set.Iic s) ∪ {t} := by
                        rintro x ⟨h1, h2⟩
                        by_cases hs : x ≤ s
                        · exact Or.inl ⟨h1, hs⟩
                        · right
                          by_contra hne
                          exact h x (not_le.mp hs) (lt_of_le_of_ne h2 hne) h1
                      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
                      simp
                    have hFr0 : ∀ k (s : ℝ), s ≤ r k → F k s = 0 := by
                      intro k s hs
                      apply le_antisymm _ (hF0 k s)
                      have h1 := hconst k (s - 1) s (fun x _ hx2 hx => by have := hAr k x hx; linarith)
                      rw [hFr k (s - 1) (by linarith)] at h1
                      exact h1
                    have hFσ : F j σ = 0 := by
                      apply le_antisymm _ (hF0 j _)
                      have h1 := hconst j (-1) σ (fun x _ hx2 hx => by
                        rw [hfloor] at hx
                        have e1 := hσm _ hx.2
                        have e2 : (σ:ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast e1
                        have e3 := Nat.floor_le hx.1
                        linarith)
                      rw [hFr j (-1) (by have : (0:ℝ) ≤ r j := by positivity
                                         linarith)] at h1
                      exact h1
                    obtain ⟨N2, hN2⟩ : ∃ N2, N2 = (Finset.univ.erase j).filter (fun k => k < j ∧ σ ≤ r k) := ⟨_, rfl⟩
                    obtain ⟨N1, hN1⟩ : ∃ N1, N1 = (Finset.univ.erase j).filter (fun k => ¬ (k < j ∧ σ ≤ r k)) := ⟨_, rfl⟩
                    have hN2m : ∀ k, k ∈ N2 ↔ (k < j ∧ σ ≤ r k) := by
                      intro k; rw [hN2]; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
                      exact ⟨fun h => h.2, fun h => ⟨h.1.ne, h⟩⟩
                    have hN1m : ∀ k, k ∈ N1 ↔ (k ≠ j ∧ ¬ (k < j ∧ σ ≤ r k)) := by
                      intro k; rw [hN1]; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
                    have hjN2 : j ∉ N2 := by rw [hN2m]; simp
                    have hsplitN : ∀ f : Fin n → ℝ, ∑ k, f k = f j + (∑ k ∈ N2, f k + ∑ k ∈ N1, f k) := by
                      intro f
                      rw [hN1, hN2, Finset.sum_filter_add_sum_filter_not, Finset.add_sum_erase _ _ (Finset.mem_univ j)]
                    obtain ⟨ν, hν⟩ : ∃ ν : Fin n → ℝ, ∀ k, ν k = F j (r k) / p j := ⟨_, fun _ => rfl⟩
                    have hν0 : ∀ k, 0 ≤ ν k := fun k => by rw [hν]; exact div_nonneg (hF0 _ _) (hpR j).le
                    have hν1 : ∀ k, ν k ≤ 1 := fun k => by rw [hν]; exact div_le_one_of_le₀ (hFp _ _) (hpR j).le
                    have hstruct : ∀ x, 0 < x → x ≤ 1 →
                        (∀ k ∈ N2, F k (tt j x) = if ν k < x then (p k:ℝ) else 0) ∧
                        (tt j x = σ + x * p j + ∑ k ∈ N2, F k (tt j x)) ∧
                        (∀ k ∈ N1, F k (tt j x) = F k σ) := by
                      intro x hx0 hx1
                      obtain ⟨t, ht⟩ : ∃ t, t = tt j x := ⟨_, rfl⟩
                      have hGt : ∀ s, t ≤ s ↔ x * p j ≤ F j s := fun s => by rw [ht]; exact hG j x hx0 hx1 s
                      have hFt : F j t = x * p j := by rw [ht]; exact hFeq j x hx0 hx1
                      have hxp := mul_pos hx0 (hpR j)
                      have hσt : (σ:ℝ) < t := by
                        rw [← not_le, hGt, hFσ]; linarith
                      rw [← ht]
                      have ht0 : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg _) hσt
                      obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : ℕ, (τ:ℝ) < t ∧ t ≤ τ + 1 := by
                        have h1 : 0 < ⌈t⌉₊ := Nat.ceil_pos.mpr ht0
                        refine ⟨⌈t⌉₊ - 1, Nat.lt_ceil.mp (by omega), ?_⟩
                        have h2 := Nat.le_ceil t
                        have h3 : ((⌈t⌉₊ - 1 : ℕ):ℝ) + 1 = ⌈t⌉₊ := by exact_mod_cast Nat.sub_add_cancel h1
                        rw [h3]; exact h2
                      have hτr : lpRun p r τ = some j := by
                        by_contra hc
                        have h1 := hconst j τ t (fun y hy1 hy2 hy => by
                          rw [hfloor] at hy
                          rw [(Nat.floor_eq_iff hy.1).mpr ⟨hy1.le, by linarith⟩] at hy
                          exact hc hy.2)
                        rw [hFt, ← hGt] at h1
                        linarith
                      obtain ⟨hτ3, hτ4, hτ5⟩ := hrun_some τ j hτr
                      have hστ := hσm τ hτr
                      have hslot : ∀ τ', σ ≤ τ' → τ' ≤ τ → ∃ k, lpRun p r τ' = some k ∧ (k = j ∨ k ∈ N2) := by
                        intro τ' h1 h2
                        have h3 := hmono τ' τ j h2
                        rcases hc : lpRun p r τ' with _ | k
                        · have := hrun_none _ hc j (by omega)
                          omega
                        · refine ⟨k, rfl, ?_⟩
                          obtain ⟨g1, g2, g3⟩ := hrun_some _ _ hc
                          have g4 := g3 j (by omega) (by omega)
                          rcases eq_or_lt_of_le g4 with h | h
                          · exact Or.inl h
                          · right
                            rw [hN2m]
                            refine ⟨h, ?_⟩
                            by_contra hcc
                            have g5 := hmono σ τ' k h1
                            have g6 := hσ3 k (by omega) (by omega)
                            exact absurd h (not_lt.mpr g6)
                      have hfl : ∀ y, (σ:ℝ) ≤ y → y < t → σ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ ≤ τ ∧ 0 ≤ y := by
                        intro y h1 h2
                        have h0 : (0:ℝ) ≤ y := le_trans (Nat.cast_nonneg _) h1
                        refine ⟨Nat.le_floor h1, ?_, h0⟩
                        have : ⌊y⌋₊ < τ + 1 := (Nat.floor_lt h0).mpr (by push_cast; linarith)
                        omega
                      have hlow : ∀ k, k < j → ((r k:ℝ) < t → F k t = p k) ∧ (t ≤ r k → F k t = 0) := by
                        intro k hk
                        refine ⟨fun h => ?_, fun h => hFr0 k t h⟩
                        have h1 : r k ≤ τ := by
                          have : (r k:ℝ) < ((τ + 1 : ℕ):ℝ) := by push_cast; linarith
                          have : r k < τ + 1 := by exact_mod_cast this
                          omega
                        have h2 : lpRemaining p r τ k = 0 := by
                          by_contra hc
                          exact absurd hk (not_lt.mpr (hτ5 k h1 (by omega)))
                        have h3 := hFint k τ h2
                        have h4 := hFmono k _ _ hτ1.le
                        exact le_antisymm (hFp k t) (by linarith)
                      refine ⟨?_, ?_, ?_⟩
                      · intro k hk
                        have hkj := ((hN2m k).mp hk).1
                        have hiff : ν k < x ↔ (r k:ℝ) < t := by
                          rw [← not_le, ← not_le, hGt, hν, le_div_iff₀ (hpR j)]
                        by_cases hc : ν k < x
                        · rw [if_pos hc, (hlow k hkj).1 (hiff.mp hc)]
                        · rw [if_neg hc, (hlow k hkj).2 (not_lt.mp (fun h => hc (hiff.mpr h)))]
                      · apply le_antisymm
                        · have h1 := hcover (insert j N2) σ t (fun y h1 h2 => by
                            obtain ⟨e1, e2, e3⟩ := hfl y h1 h2
                            obtain ⟨k, hk1, hk2⟩ := hslot _ e1 e2
                            exact ⟨k, Finset.mem_insert.mpr hk2, (hfloor k y).mpr ⟨e3, hk1⟩⟩)
                          rw [Finset.sum_insert hjN2, hFt] at h1
                          linarith
                        · have h1 := hFdiff (insert j N2) σ t hσt.le
                          rw [Finset.sum_insert hjN2, hFt, hFσ] at h1
                          have h2 : ∑ k ∈ N2, (F k t - F k σ) = ∑ k ∈ N2, F k t := by
                            refine Finset.sum_congr rfl fun k hk => ?_
                            rw [hFr0 k σ (by exact_mod_cast ((hN2m k).mp hk).2), sub_zero]
                          rw [h2] at h1
                          linarith
                      · intro k hk
                        apply le_antisymm _ (hFmono k _ _ hσt.le)
                        apply hconst
                        intro y h1 h2 hy
                        obtain ⟨e1, e2, e3⟩ := hfl y h1.le h2
                        obtain ⟨k', hk1, hk2⟩ := hslot _ e1 e2
                        have := ((hfloor k y).mp hy).2
                        rw [hk1] at this
                        have hkk := Option.some.inj this
                        rw [hkk] at hk2
                        obtain ⟨g1, g2⟩ := (hN1m k).mp hk
                        rcases hk2 with h | h
                        · exact g1 h
                        · exact g2 ((hN2m k).mp h)
                    have hMform : mLP p r j = σ + (p j:ℝ)/2 + ∑ k ∈ N2, (p k:ℝ) * (1 - ν k) := by
                      have e1 : ∫ x in Set.Ioc (0:ℝ) 1, tt j x = mLP p r j := by
                        rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => htt0 j x) (httm j).aestronglyMeasurable,
                          hEt j, ENNReal.toReal_ofReal (hM0 j)]
                      have hite : ∀ u : ℝ, Measurable (fun x : ℝ => if u < x then (1:ℝ) else 0) := fun u =>
                        Measurable.ite measurableSet_Ioi measurable_const measurable_const
                      have e2 : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∫ x in Set.Ioc (0:ℝ) 1, (if u < x then (1:ℝ) else 0) = 1 - u := by
                        intro u h0 h1
                        rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc (Set.Ioc_subset_Ioc_left h0) (s := Set.Ioc u 1),
                          setIntegral_congr_fun (g := fun _ => (1:ℝ)) measurableSet_Ioc]
                        · simp [h1]
                        · intro x hx; simp [hx.1]
                        · rintro x ⟨hx1, hx2⟩
                          rw [if_neg]
                          intro h; exact hx2 ⟨h, hx1.2⟩
                      have hi1 : ∀ u : ℝ, IntegrableOn (fun x : ℝ => if u < x then (1:ℝ) else 0) (Set.Ioc 0 1) := by
                        intro u
                        refine Integrable.of_bound (hite u).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
                        split_ifs <;> simp
                      have hi2 : IntegrableOn (fun x : ℝ => (σ:ℝ) + x * p j) (Set.Ioc 0 1) := by
                        have : Continuous (fun x : ℝ => (σ:ℝ) + x * p j) := by fun_prop
                        exact (this.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ioc_subset_Icc_self
                      have hi3 : ∀ k, IntegrableOn (fun x : ℝ => (p k:ℝ) * (if ν k < x then (1:ℝ) else 0)) (Set.Ioc 0 1) :=
                        fun k => (hi1 (ν k)).const_mul _
                      rw [← e1, setIntegral_congr_fun (g := fun x => ((σ:ℝ) + x * p j) + ∑ k ∈ N2, (p k:ℝ) * (if ν k < x then (1:ℝ) else 0)) measurableSet_Ioc]
                      · rw [integral_add hi2 (integrable_finsetSum _ fun k _ => hi3 k), integral_finsetSum _ fun k _ => hi3 k]
                        simp only [integral_const_mul]
                        congr 1
                        · rw [← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_add (by simp) (by apply Continuous.intervalIntegrable; fun_prop),
                            intervalIntegral.integral_mul_const, integral_id]
                          simp
                          ring
                        · exact Finset.sum_congr rfl fun k _ => by rw [e2 _ (hν0 k) (hν1 k)]
                      · intro x hx
                        obtain ⟨g1, g2, -⟩ := hstruct x hx.1 hx.2
                        have g3 : ∑ k ∈ N2, F k (tt j x) = ∑ k ∈ N2, (p k:ℝ) * (if ν k < x then (1:ℝ) else 0) := by
                          refine Finset.sum_congr rfl fun k hk => ?_
                          rw [g1 k hk, mul_ite, mul_one, mul_zero]
                        rw [g3] at g2
                        exact g2
                    obtain ⟨η, hη⟩ : ∃ η : Fin n → ℝ, ∀ k, η k = F k σ / p k := ⟨_, fun _ => rfl⟩
                    have hη0 : ∀ k, 0 ≤ η k := fun k => by rw [hη]; exact div_nonneg (hF0 _ _) (hpR k).le
                    have hη1 : ∀ k, η k ≤ 1 := fun k => by rw [hη]; exact div_le_one_of_le₀ (hFp _ _) (hpR k).le
                    have hηp : ∀ k, (p k:ℝ) * η k = F k σ := fun k => by rw [hη]; have := (hpR k).ne'; field_simp
                    have hCr : ∀ a : Fin n → ℝ, (∀ j, a j ∈ Set.Ioc (0:ℝ) 1) → onlineCompletion p r a j ≤
                        (((σ:ℝ) + p j) + p j * a j) + (∑ k ∈ N2, (p k:ℝ) * ((if ν k < a j then (1:ℝ) else 0) * (1 + a k)) +
                        ∑ k ∈ N1, (p k:ℝ) * (if a k ≤ η k then 1 + a k - η k else 0)) := by
                      intro a ha
                      have h1 := hCgen a ha j
                      obtain ⟨g1, g2, g3⟩ := hstruct (a j) (ha j).1 (ha j).2
                      have hFj := hFeq j _ (ha j).1 (ha j).2
                      obtain ⟨t, ht⟩ : ∃ t, t = tt j (a j) := ⟨_, rfl⟩
                      have hpk : ∀ k, precedes p r a k j → a k * p k ≤ F k t := by
                        intro k hk
                        rw [← hG k _ (ha k).1 (ha k).2, ht]; exact hPle a k j hk
                      rw [← ht] at h1 g1 g2 g3 hFj
                      rw [Finset.sum_filter, hsplitN] at h1
                      have hjj : precedes p r a j j := Or.inr ⟨rfl, le_rfl⟩
                      rw [if_pos hjj, hFj] at h1
                      have h2 : ∑ k ∈ N2, (if precedes p r a k j then (1 + a k) * (p k:ℝ) - F k t else 0) ≤
                          ∑ k ∈ N2, ((p k:ℝ) * ((if ν k < a j then (1:ℝ) else 0) * (1 + a k)) - F k t) := by
                        refine Finset.sum_le_sum fun k hk => ?_
                        have hk0 := mul_pos (ha k).1 (hpR k)
                        have e1 := hpk k
                        rw [g1 k hk] at e1 ⊢
                        by_cases hc : ν k < a j
                        · simp only [hc, if_true]
                          split_ifs <;> linarith
                        · simp only [hc, if_false] at e1 ⊢
                          rw [if_neg]
                          · simp
                          · intro h; linarith [e1 h]
                      have h3 : ∑ k ∈ N1, (if precedes p r a k j then (1 + a k) * (p k:ℝ) - F k t else 0) ≤
                          ∑ k ∈ N1, (p k:ℝ) * (if a k ≤ η k then 1 + a k - η k else 0) := by
                        refine Finset.sum_le_sum fun k hk => ?_
                        have e1 := hpk k
                        rw [g3 k hk] at e1 ⊢
                        by_cases hc : precedes p r a k j
                        · have e2 : a k ≤ η k := by
                            rw [hη, le_div_iff₀ (hpR k)]; exact e1 hc
                          rw [if_pos hc, if_pos e2, ← hηp k]
                          apply le_of_eq; ring
                        · rw [if_neg hc]
                          split_ifs
                          · apply mul_nonneg (hpR k).le
                            linarith [(ha k).1, hη1 k]
                          · simp
                      rw [Finset.sum_sub_distrib] at h2
                      linarith
                    refine ⟨σ, N1, N2, ν, η, fun k => ⟨hν0 k, hν1 k⟩, fun k => ⟨hη0 k, hη1 k⟩, ?_, ?_, hMform, hCr⟩
                    · intro k hk; exact ((hN2m k).mp hk).1.ne'
                    · rw [Finset.sum_congr rfl fun k _ => hηp k]
                      refine le_trans ?_ (hFsum σ (Nat.cast_nonneg _))
                      exact Finset.sum_le_univ_sum_of_nonneg fun i => hF0 _ _
                  refine ⟨?_, ⟨T, fun j => ⟨?_, ?_⟩⟩, hOPT, hdet, hcore⟩
                  · intro j
                    have : (fun x => alphaPoint p (lpSet p r) j x) = tt j := funext fun x => (htt j x).symm
                    rw [this]; exact httm j
                  · exact_mod_cast (hrT j).le
                  · intro x h0 h1
                    rw [← htt, hG j x h0 h1, hFT]
                    exact mul_le_of_le_one_left (hpR j).le h1
                have hrand : ∀ γ : ℝ, (0 < γ ∧ γ < 1 ∧
                      γ + Real.log (2 - γ) = Real.exp (-γ) * ((2 - γ) * Real.exp γ - 1)) →
                    cConst γ < 1.6853 ∧
                      ∀ μ : Measure (Fin n → ℝ), IsProbabilityMeasure μ →
                        (∀ j, μ.map (fun a => a j) = gMeasure γ) →
                        (∀ j k, j ≠ k → IndepFun (fun a => a j) (fun a => a k) μ) →
                        Integrable (fun a => ∑ j, w j * onlineCompletion p r a j) μ ∧
                          ∫ a, ∑ j, w j * onlineCompletion p r a j ∂μ ≤
                            cConst γ * optValue p r w := by
                  clear GEN hchar honline hsqrt hsort
                  intro γ hγ
                  obtain ⟨hc, K, hKpos, hcK, hγK, haeG, hLi, hE, hLii⟩ := hGf γ hγ
                  clear hGf hγ
                  refine ⟨hc, ?_⟩
                  obtain ⟨httm, ⟨T, hT⟩, hOPT, -, hcore⟩ := hPACK
                  clear hc
                  have hpR : ∀ j, (0:ℝ) < p j := fun j => Nat.cast_pos.mpr (hp j)
                  obtain ⟨tt, htt⟩ : ∃ tt : Fin n → ℝ → ℝ, ∀ j x, tt j x = alphaPoint p (lpSet p r) j x := ⟨_, fun _ _ => rfl⟩
                  simp only [← htt] at httm hT
                  intro P hPr hmarg hind
                  have hmeasE : ∀ j : Fin n, Measurable (fun a : Fin n → ℝ => a j) := fun j => measurable_pi_apply j
                  have hae : ∀ᵐ a ∂P, ∀ j, a j ∈ Set.Ioc (0:ℝ) 1 := by
                    rw [ae_all_iff]
                    intro j
                    have h1 : ∀ᵐ x ∂(P.map (fun a => a j)), x ∈ Set.Ioc (0:ℝ) 1 := by
                      rw [hmarg j]
                      exact haeG
                    exact ae_of_ae_map (hmeasE j).aemeasurable h1
                  have hPm : ∀ k i, MeasurableSet {a : Fin n → ℝ | precedes p r a k i} := by
                    intro k i
                    have m1 : Measurable (fun a : Fin n → ℝ => tt k (a k)) := (httm k).comp (hmeasE k)
                    have m2 : Measurable (fun a : Fin n → ℝ => tt i (a i)) := (httm i).comp (hmeasE i)
                    have : {a : Fin n → ℝ | precedes p r a k i} =
                        {a | tt k (a k) < tt i (a i)} ∪ ({a | tt k (a k) = tt i (a i)} ∩ {a | k ≤ i}) := by
                      ext a
                      simp only [precedes, ← htt]
                      rfl
                    rw [this]
                    exact (measurableSet_lt m1 m2).union ((measurableSet_eq_fun m1 m2).inter (MeasurableSet.const _))
                  have hCm : ∀ j, Measurable (fun a : Fin n → ℝ => onlineCompletion p r a j) := by
                    intro j
                    apply measurable_of_Iic
                    intro x
                    have : (fun a : Fin n → ℝ => onlineCompletion p r a j) ⁻¹' Set.Iic x =
                        ⋂ k, ({a | precedes p r a k j}ᶜ ∪ {a | max (r k : ℝ) (tt k (a k)) +
                          ∑ i, (if (precedes p r a k i ∧ precedes p r a i j) then (p i : ℝ) else 0) ≤ x}) := by
                      ext a
                      simp only [Set.mem_preimage, Set.mem_Iic, hOC, ← htt, Set.mem_iInter, Set.mem_union,
                        Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.sum_filter]
                      exact forall_congr' fun k => imp_iff_not_or
                    rw [this]
                    refine MeasurableSet.iInter fun k => (hPm k j).compl.union (measurableSet_le ?_ measurable_const)
                    refine Measurable.add (measurable_const.max ((httm k).comp (hmeasE k))) ?_
                    refine Finset.measurable_sum _ fun i _ => ?_
                    exact Measurable.ite ((hPm k i).inter (hPm i j)) measurable_const measurable_const
                  have hIntg : ∀ g : (Fin n → ℝ) → ℝ, Measurable g → ∀ B : ℝ,
                      (∀ a, (∀ j, a j ∈ Set.Ioc (0:ℝ) 1) → |g a| ≤ B) → Integrable g P := by
                    intro g hg B hB
                    refine Integrable.of_bound hg.aestronglyMeasurable B ?_
                    filter_upwards [hae] with a ha
                    exact hB a ha
                  have hCint : ∀ j, Integrable (fun a : Fin n → ℝ => onlineCompletion p r a j) P := by
                    intro j
                    apply hIntg _ (hCm j) (T + ∑ i, (p i:ℝ))
                    intro a ha
                    rw [abs_le]
                    have hTT : ∀ k, tt k (a k) ≤ T := fun k => (hT k).2 _ (ha k).1 (ha k).2
                    have hT0 : 0 ≤ T := le_trans (Nat.cast_nonneg _) (hT j).1
                    have hP0 : 0 ≤ ∑ i, (p i:ℝ) := Finset.sum_nonneg fun i _ => (hpR i).le
                    constructor
                    · have hjj : precedes p r a j j := Or.inr ⟨rfl, le_rfl⟩
                      have h := (hOC n p r a j _).mp le_rfl j hjj
                      have h2 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => precedes p r a j i ∧ precedes p r a i j), (p i:ℝ) :=
                        Finset.sum_nonneg fun i _ => (hpR i).le
                      have h3 := le_max_left (r j:ℝ) (alphaPoint p (lpSet p r) j (a j))
                      have h4 : (0:ℝ) ≤ r j := by positivity
                      linarith
                    · rw [hOC]
                      intro k hk
                      rw [← htt]
                      have h1 : max (r k:ℝ) (tt k (a k)) ≤ T := max_le (hT k).1 (hTT k)
                      have h2 : ∑ i ∈ Finset.univ.filter (fun i => precedes p r a k i ∧ precedes p r a i j), (p i:ℝ) ≤ ∑ i, (p i:ℝ) :=
                        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => (hpR i).le)
                      linarith
                  have hmap : ∀ j, ∀ f : ℝ → ℝ, Measurable f → ∫ a, f (a j) ∂P = ∫ x, f x ∂(gMeasure γ) := by
                    intro j f hf
                    rw [← hmarg j, integral_map (hmeasE j).aemeasurable hf.aestronglyMeasurable]
                  have hEC : ∀ j, ∫ a, onlineCompletion p r a j ∂P ≤ (1 + K) * (mLP p r j + (p j:ℝ)/2) := by
                    intro j
                    obtain ⟨σ, N1, N2, ν, η, hν, hη, hN2, hN1, hMform, hCr⟩ := hcore j
                    have hη0 := fun k => (hη k).1
                    have hη1 := fun k => (hη k).2
                    have hν0 := fun k => (hν k).1
                    have hν1 := fun k => (hν k).2
                    clear hη hν hcore hOPT hOC httm hT htt hPm
                    have m1 : ∀ k, Measurable (fun x : ℝ => if ν k < x then (1:ℝ) else 0) := fun k =>
                      Measurable.ite measurableSet_Ioi measurable_const measurable_const
                    have m2 : ∀ k, Measurable (fun x : ℝ => if x ≤ η k then 1 + x - η k else 0) := fun k =>
                      Measurable.ite measurableSet_Iic (by fun_prop) measurable_const
                    have m3 : Measurable (fun x : ℝ => 1 + x) := by fun_prop
                    have i0 : Integrable (fun a : Fin n → ℝ => a j) P := by
                      apply hIntg _ (hmeasE j) 1
                      intro a ha
                      rw [abs_of_pos (ha j).1]; exact (ha j).2
                    have i0' : ∀ k, Integrable (fun a : Fin n → ℝ => a k) P := by
                      intro k
                      apply hIntg _ (hmeasE k) 1
                      intro a ha
                      rw [abs_of_pos (ha k).1]; exact (ha k).2
                    have i1 : ∀ k, Integrable (fun a : Fin n → ℝ => (p k:ℝ) * ((if ν k < a j then (1:ℝ) else 0) * (1 + a k))) P := by
                      intro k
                      apply Integrable.const_mul
                      apply hIntg _ (((m1 k).comp (hmeasE j)).mul (m3.comp (hmeasE k))) 2
                      intro a ha
                      change |(if ν k < a j then (1:ℝ) else 0) * (1 + a k)| ≤ 2
                      have := ha k
                      split_ifs
                      · rw [one_mul, abs_of_pos (by linarith [this.1])]; linarith [this.2]
                      · simp
                    have i2 : ∀ k, Integrable (fun a : Fin n → ℝ => (p k:ℝ) * (if a k ≤ η k then 1 + a k - η k else 0)) P := by
                      intro k
                      apply Integrable.const_mul
                      apply hIntg _ ((m2 k).comp (hmeasE k)) 2
                      intro a ha
                      try simp only [Function.comp]
                      have h1 := ha k
                      have h2 := hη0 k
                      have h3 := hη1 k
                      split_ifs
                      · rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
                      · simp
                    have i3 : Integrable (fun a : Fin n → ℝ => (σ + p j) + p j * a j) P :=
                      (integrable_const _).add (i0.const_mul _)
                    have i4 : Integrable (fun a : Fin n → ℝ => ∑ k ∈ N2, (p k:ℝ) * ((if ν k < a j then (1:ℝ) else 0) * (1 + a k))) P :=
                      integrable_finsetSum _ fun k _ => i1 k
                    have i5 : Integrable (fun a : Fin n → ℝ => ∑ k ∈ N1, (p k:ℝ) * (if a k ≤ η k then 1 + a k - η k else 0)) P :=
                      integrable_finsetSum _ fun k _ => i2 k
                    have hEj : ∀ k, ∫ a, a k ∂P = 1 - γ := fun k => by
                      rw [hmap k (fun x => x) measurable_id, hE]
                    have s1 : ∫ a, onlineCompletion p r a j ∂P ≤ ∫ a, (((σ + p j) + p j * a j) + (∑ k ∈ N2, (p k:ℝ) * ((if ν k < a j then (1:ℝ) else 0) * (1 + a k)) +
                        ∑ k ∈ N1, (p k:ℝ) * (if a k ≤ η k then 1 + a k - η k else 0))) ∂P := by
                      apply integral_mono_ae (hCint j) (i3.add (i4.add i5))
                      filter_upwards [hae] with a ha
                      exact hCr a ha
                    have s1a := integral_add i3 (i4.add i5)
                    have s1b := integral_add i4 i5
                    simp only [Pi.add_apply] at s1a s1b
                    rw [s1a, s1b, integral_add (integrable_const _) (i0.const_mul _),
                      integral_finsetSum _ fun k _ => i1 k, integral_finsetSum _ fun k _ => i2 k] at s1
                    simp only [integral_const_mul, hEj] at s1
                    have s0 : ∫ a : Fin n → ℝ, (σ + p j) ∂P = σ + p j := by simp
                    rw [s0] at s1
                    have s2 : ∑ k ∈ N2, (p k:ℝ) * ∫ a, (if ν k < a j then (1:ℝ) else 0) * (1 + a k) ∂P ≤
                        ∑ k ∈ N2, (p k:ℝ) * ((1 + K) * (1 - ν k)) := by
                      refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hpR k).le
                      have hjk : j ≠ k := hN2 k hk
                      have hi := (hind j k hjk).comp (m1 k) m3
                      have e1 := hi.integral_fun_mul_eq_mul_integral ((m1 k).comp (hmeasE j)).aestronglyMeasurable (m3.comp (hmeasE k)).aestronglyMeasurable
                      simp only [Function.comp] at e1
                      rw [e1, hmap j _ (m1 k), integral_add (integrable_const _) (i0' k), hEj]
                      have e2 := hLii (ν k) (hν0 k) (hν1 k)
                      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
                      linarith
                    have s3 : ∑ k ∈ N1, (p k:ℝ) * ∫ a, (if a k ≤ η k then 1 + a k - η k else 0) ∂P ≤ K * σ := by
                      have e1 : ∑ k ∈ N1, (p k:ℝ) * ∫ a, (if a k ≤ η k then 1 + a k - η k else 0) ∂P ≤ ∑ k ∈ N1, (p k:ℝ) * (K * η k) := by
                        refine Finset.sum_le_sum fun k hk => ?_
                        rw [hmap k _ (m2 k)]
                        exact mul_le_mul_of_nonneg_left (hLi (η k) (hη0 k) (hη1 k)) (hpR k).le
                      refine e1.trans ?_
                      have e2 : ∑ k ∈ N1, (p k:ℝ) * (K * η k) = K * ∑ k ∈ N1, (p k:ℝ) * η k := by
                        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
                      rw [e2]
                      exact mul_le_mul_of_nonneg_left hN1 hKpos.le
                    have s4 : ∑ k ∈ N2, (p k:ℝ) * ((1 + K) * (1 - ν k)) = (1 + K) * ∑ k ∈ N2, (p k:ℝ) * (1 - ν k) := by
                      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
                    have s5 : (2 - γ) * (p j:ℝ) ≤ (1 + K) * p j := mul_le_mul_of_nonneg_right hγK (hpR j).le
                    rw [hMform]
                    rw [s4] at s2
                    linarith
                  refine ⟨integrable_finsetSum _ fun j _ => (hCint j).const_mul _, ?_⟩
                  rw [integral_finsetSum _ fun j _ => (hCint j).const_mul _, hcK]
                  simp only [integral_const_mul]
                  have f1 : ∑ j, w j * ∫ a, onlineCompletion p r a j ∂P ≤ ∑ j, w j * ((1 + K) * (mLP p r j + (p j:ℝ)/2)) :=
                    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hEC j) (hw j).le
                  have f2 : ∑ j, w j * ((1 + K) * (mLP p r j + (p j:ℝ)/2)) = (1 + K) * ∑ j, w j * (mLP p r j + (p j:ℝ)/2) := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun j _ => by ring
                  rw [f2] at f1
                  have f3 := mul_le_mul_of_nonneg_left hOPT (show (0:ℝ) ≤ 1 + K by linarith)
                  linarith
                exact ⟨⟨hsqrt, hPACK.2.2.2.1⟩, hrand, honline⟩
