-- Prove2me | solution 1 for SigRoute.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T08:48:47.072947+00:00
-- url     : https://prove2.me/submissions/772871e9-7479-442e-92ba-e97e33fedeaa

import Mathlib
open MeasureTheory

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m) (N : ℕ) (Y : ℕ → Ω → ℝ)
    (hY_nonneg : ∀ j < N, ∀ ω, 0 ≤ Y j ω)
    (hY_meas : ∀ j < N, Measurable[F (j + 1)] (Y j))
    (lam Λ : ℝ) (hlam : 0 < lam) (hΛ : 1 ≤ Λ)
    (hint : ∀ j < N, Integrable (fun ω => Real.exp (lam * Y j ω)) μ)
    (hmgf : ∀ j < N, condExp (F j) μ (fun ω => Real.exp (lam * Y j ω)) ≤ᵐ[μ] fun _ => Λ)
    (τ : ℝ) :
    μ.real {ω | τ ≤ ∑ j ∈ Finset.range N, Y j ω} ≤ Real.exp (-lam * τ) * Λ ^ N := by
  set Z : ℕ → Ω → ℝ := fun j ω => Real.exp (lam * Y j ω) with hZ
  set S : Ω → ℝ := fun ω => ∑ j ∈ Finset.range N, Y j ω with hS
  have hZ_nonneg : ∀ j ω, 0 ≤ Z j ω := fun j ω => (Real.exp_pos _).le
  have hZ_meas : ∀ j, j < N → Measurable[F (j + 1)] (Z j) := by
    intro j hj
    rw [hZ]
    exact Real.measurable_exp.comp ((hY_meas j hj).const_mul lam)
  -- Truncations
  set ZM : ℕ → ℕ → Ω → ℝ := fun M j ω => min (Z j ω) (M : ℝ) with hZM
  set PM : ℕ → ℕ → Ω → ℝ := fun M n ω => ∏ j ∈ Finset.range n, ZM M j ω with hPM
  have hZM_nonneg : ∀ M j ω, 0 ≤ ZM M j ω := by
    intro M j ω
    rw [hZM]
    exact le_min (hZ_nonneg j ω) (Nat.cast_nonneg M)
  have hZM_le_Z : ∀ M j ω, ZM M j ω ≤ Z j ω := by
    intro M j ω; rw [hZM]; exact min_le_left _ _
  have hZM_le_M : ∀ M j ω, ZM M j ω ≤ (M : ℝ) := by
    intro M j ω; rw [hZM]; exact min_le_right _ _
  have hPM_nonneg : ∀ M n ω, 0 ≤ PM M n ω := by
    intro M n ω
    rw [hPM]
    exact Finset.prod_nonneg (fun j _ => hZM_nonneg M j ω)
  have hZM_meas : ∀ M (j : ℕ), j < N → Measurable[F (j + 1)] (ZM M j) := by
    intro M j hj
    rw [hZM]
    exact (hZ_meas j hj).min measurable_const
  have hPM_sm : ∀ M n, n ≤ N → StronglyMeasurable[F n] (PM M n) := by
    intro M n hn
    rw [hPM]
    change StronglyMeasurable[F n] (fun ω => ∏ j ∈ Finset.range n, ZM M j ω)
    have h := Finset.stronglyMeasurable_prod (s := Finset.range n)
      (f := fun j => ZM M j) (fun j hj => by
        have hjn : j < n := Finset.mem_range.mp hj
        have hjN : j < N := lt_of_lt_of_le hjn hn
        exact StronglyMeasurable.mono ((hZM_meas M j hjN).stronglyMeasurable)
          (F.mono (by omega : j + 1 ≤ n)))
    have hfun : (∏ j ∈ Finset.range n, ZM M j) =
        fun ω => ∏ j ∈ Finset.range n, ZM M j ω := by
      funext ω
      rw [Finset.prod_apply]
    rwa [hfun] at h
  have hZM_int : ∀ M (j : ℕ), j < N → Integrable (ZM M j) μ := by
    intro M j hj
    refine Integrable.of_bound
      ((hZM_meas M j hj).mono (F.le (j + 1)) (le_refl _)).aestronglyMeasurable (M : ℝ) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (hZM_nonneg M j ω)]
    exact hZM_le_M M j ω
  have hPM_le_pow : ∀ M n ω, PM M n ω ≤ (M : ℝ) ^ n := by
    intro M n ω
    rw [hPM]
    calc ∏ j ∈ Finset.range n, ZM M j ω ≤ ∏ _j ∈ Finset.range n, (M : ℝ) := by
          apply Finset.prod_le_prod
          · intro j _; exact hZM_nonneg M j ω
          · intro j _; exact hZM_le_M M j ω
      _ = (M : ℝ) ^ n := by simp [Finset.prod_const, Finset.card_range]
  have hPM_int : ∀ M n, n ≤ N → Integrable (PM M n) μ := by
    intro M n hn
    refine Integrable.of_bound
      ((hPM_sm M n hn).mono (F.le n)).aestronglyMeasurable ((M : ℝ) ^ n) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (hPM_nonneg M n ω)]
    exact hPM_le_pow M n ω
  -- Base case
  have hbase : ∀ M, ∫ ω, PM M 0 ω ∂μ = 1 := by
    intro M
    have h : PM M 0 = fun _ => (1 : ℝ) := by
      funext ω
      rw [hPM]
      simp
    rw [h]
    simp [integral_const, probReal_univ]
  -- Induction step
  have hstep : ∀ M n, n < N → ∫ ω, PM M (n + 1) ω ∂μ ≤ Λ * ∫ ω, PM M n ω ∂μ := by
    intro M n hn
    have hprod : (fun ω => PM M (n + 1) ω) = fun ω => PM M n ω * ZM M n ω := by
      funext ω
      rw [hPM]
      simp [Finset.prod_range_succ]
    rw [hprod, ← integral_condExp (F.le n)]
    rw [show (fun ω => PM M n ω * ZM M n ω) = PM M n * ZM M n from funext fun ω => rfl]
    have hsm : StronglyMeasurable[F n] (PM M n) := hPM_sm M n (by omega)
    have hfg : Integrable (PM M n * ZM M n) μ := by
      refine Integrable.of_bound ?_ ((M : ℝ) ^ (n + 1)) ?_
      · exact (((hPM_sm M n (by omega)).mono (F.le n)).aestronglyMeasurable).mul
          (hZM_int M n hn).aestronglyMeasurable
      · filter_upwards with ω
        rw [Pi.mul_apply,
          Real.norm_of_nonneg (mul_nonneg (hPM_nonneg M n ω) (hZM_nonneg M n ω))]
        calc PM M n ω * ZM M n ω ≤ (M : ℝ) ^ n * (M : ℝ) :=
              mul_le_mul (hPM_le_pow M n ω) (hZM_le_M M n ω) (hZM_nonneg M n ω) (by positivity)
          _ = (M : ℝ) ^ (n + 1) := by ring
    have hg : Integrable (ZM M n) μ := hZM_int M n hn
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := F n) hsm hfg hg
    rw [integral_congr_ae hpull]
    have hcond_le : condExp (F n) μ (ZM M n) ≤ᵐ[μ] fun _ => Λ := by
      have h1 : condExp (F n) μ (ZM M n) ≤ᵐ[μ] condExp (F n) μ (Z n) := by
        refine condExp_mono (hZM_int M n hn) (hint n hn) ?_
        exact ae_of_all _ (fun ω => hZM_le_Z M n ω)
      have h2 : condExp (F n) μ (Z n) ≤ᵐ[μ] fun _ => Λ := by
        simpa [hZ] using hmgf n hn
      exact h1.trans h2
    have hcond_nonneg : 0 ≤ᵐ[μ] condExp (F n) μ (ZM M n) :=
      condExp_nonneg (ae_of_all _ (fun ω => hZM_nonneg M n ω))
    have hint_prod : Integrable (PM M n * condExp (F n) μ (ZM M n)) μ := by
      refine Integrable.of_bound ?_ ((M : ℝ) ^ n * Λ) ?_
      · exact (((hPM_sm M n (by omega)).mono (F.le n)).aestronglyMeasurable).mul
          ((stronglyMeasurable_condExp (m := F n) (f := ZM M n)).mono (F.le n)).aestronglyMeasurable
      · filter_upwards [hcond_nonneg, hcond_le] with ω h1 h2
        rw [Pi.mul_apply, Real.norm_of_nonneg (mul_nonneg (hPM_nonneg M n ω) h1)]
        calc PM M n ω * condExp (F n) μ (ZM M n) ω ≤ (M : ℝ) ^ n * Λ :=
              mul_le_mul (hPM_le_pow M n ω) h2 h1 (by positivity)
          _ = (M : ℝ) ^ n * Λ := rfl
    let K : Ω → ℝ := fun _ => Λ
    have hmono : (PM M n * condExp (F n) μ (ZM M n)) ≤ᵐ[μ] (PM M n * K) := by
      filter_upwards [hcond_le] with ω hω
      rw [Pi.mul_apply, Pi.mul_apply]
      exact mul_le_mul_of_nonneg_left hω (hPM_nonneg M n ω)
    calc ∫ ω, (PM M n * condExp (F n) μ (ZM M n)) ω ∂μ
        ≤ ∫ ω, (PM M n * K) ω ∂μ :=
          integral_mono_ae hint_prod
            (show Integrable (PM M n * K) μ from (hPM_int M n (by omega)).mul_const Λ) hmono
      _ = Λ * ∫ ω, PM M n ω ∂μ := by
          rw [show (fun ω => (PM M n * K) ω) = fun ω => PM M n ω * Λ from
            funext fun ω => rfl]
          rw [integral_mul_const]; ring
  -- Product bound for the truncated variables
  have hbound : ∀ n, n ≤ N → ∀ M, ∫ ω, PM M n ω ∂μ ≤ Λ ^ n := by
    intro n
    induction n with
    | zero =>
        intro _ M
        simp [hbase M]
    | succ n ih =>
        intro hn M
        have hnN : n < N := by omega
        calc ∫ ω, PM M (n + 1) ω ∂μ ≤ Λ * ∫ ω, PM M n ω ∂μ := hstep M n hnN
          _ ≤ Λ * Λ ^ n := by
              apply mul_le_mul_of_nonneg_left (ih (by omega) M)
              linarith
          _ = Λ ^ (n + 1) := by rw [pow_succ]; ring
  -- The full product
  set P : Ω → ℝ := fun ω => ∏ j ∈ Finset.range N, Z j ω with hP
  have hP_nonneg : ∀ ω, 0 ≤ P ω := fun ω =>
    Finset.prod_nonneg (fun j _ => hZ_nonneg j ω)
  have hP_exp : ∀ ω, P ω = Real.exp (lam * S ω) := by
    intro ω
    rw [hP, hS, hZ, Finset.mul_sum, Real.exp_sum]
  have hP_meas : Measurable P := by
    rw [hP]
    exact Finset.measurable_prod _ (fun j hj =>
      (hZ_meas j (Finset.mem_range.mp hj)).mono (F.le (j + 1)) (le_refl _))
  have hPM_le_P : ∀ M ω, PM M N ω ≤ P ω := by
    intro M ω
    rw [hPM, hP]
    apply Finset.prod_le_prod
    · intro j _; exact hZM_nonneg M j ω
    · intro j _; exact hZM_le_Z M j ω
  -- Sup over truncations
  have hsup_eq : ∀ ω, (⨆ M, ENNReal.ofReal (PM M N ω)) = ENNReal.ofReal (P ω) := by
    intro ω
    refine le_antisymm (iSup_le (fun M => ENNReal.ofReal_le_ofReal (hPM_le_P M ω))) ?_
    set M₀ : ℕ := ⌈∑ j ∈ Finset.range N, Z j ω⌉₊
    have hlarge : PM M₀ N ω = P ω := by
      rw [hPM, hP]
      apply Finset.prod_congr rfl
      intro j hj
      show min (Z j ω) (M₀ : ℝ) = Z j ω
      rw [min_eq_left]
      exact (Finset.single_le_sum (fun k _ => hZ_nonneg k ω) hj).trans (Nat.le_ceil _)
    calc ENNReal.ofReal (P ω) = ENNReal.ofReal (PM M₀ N ω) := by rw [hlarge]
      _ ≤ ⨆ M, ENNReal.ofReal (PM M N ω) :=
          le_iSup (fun M : ℕ => ENNReal.ofReal (PM M N ω)) M₀
  have hmono_ofReal : Monotone (fun M : ℕ => fun ω => ENNReal.ofReal (PM M N ω)) := by
    intro M M' hMM' ω
    apply ENNReal.ofReal_le_ofReal
    show (∏ j ∈ Finset.range N, ZM M j ω) ≤ (∏ j ∈ Finset.range N, ZM M' j ω)
    apply Finset.prod_le_prod
    · intro j _; exact hZM_nonneg M j ω
    · intro j _
      exact min_le_min_left _ (by exact_mod_cast hMM')
  have hmeas_ofReal : ∀ M, Measurable (fun ω => ENNReal.ofReal (PM M N ω)) := by
    intro M
    exact ENNReal.measurable_ofReal.comp
      ((hPM_sm M N le_rfl).mono (F.le N)).measurable
  have hlin_eq : ∫⁻ ω, ENNReal.ofReal (P ω) ∂μ =
      ⨆ M, ∫⁻ ω, ENNReal.ofReal (PM M N ω) ∂μ := by
    have hcongr : (fun ω => ENNReal.ofReal (P ω)) =
        fun ω => ⨆ M, ENNReal.ofReal (PM M N ω) := by
      funext ω
      exact (hsup_eq ω).symm
    rw [hcongr]
    exact lintegral_iSup hmeas_ofReal hmono_ofReal
  have hlin_le : ∫⁻ ω, ENNReal.ofReal (P ω) ∂μ ≤ ENNReal.ofReal (Λ ^ N) := by
    rw [hlin_eq]
    apply iSup_le
    intro M
    rw [← ofReal_integral_eq_lintegral_ofReal (hPM_int M N le_rfl)
      (ae_of_all _ (fun ω => hPM_nonneg M N ω))]
    exact ENNReal.ofReal_le_ofReal (hbound N le_rfl M)
  -- Markov's inequality in lintegral form
  have hMarkov : ENNReal.ofReal (Real.exp (lam * τ)) * μ {ω | τ ≤ S ω} ≤
      ∫⁻ ω, ENNReal.ofReal (P ω) ∂μ := by
    have hf : Measurable (fun ω => ENNReal.ofReal (P ω)) :=
      ENNReal.measurable_ofReal.comp hP_meas
    have h := mul_meas_ge_le_lintegral (μ := μ) hf (ENNReal.ofReal (Real.exp (lam * τ)))
    rw [show {x | ENNReal.ofReal (Real.exp (lam * τ)) ≤ ENNReal.ofReal (P x)} =
        {ω | τ ≤ S ω} from by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ENNReal.ofReal_le_ofReal_iff (hP_nonneg ω)]
      constructor
      · intro hle
        have h2 : Real.exp (lam * τ) ≤ Real.exp (lam * S ω) := by rwa [hP_exp ω] at hle
        have h3 : lam * τ ≤ lam * S ω := Real.exp_le_exp.mp h2
        exact (mul_le_mul_iff_of_pos_left hlam).mp h3
      · intro hle
        have h3 : lam * τ ≤ lam * S ω := (mul_le_mul_iff_of_pos_left hlam).mpr hle
        have h2 : Real.exp (lam * τ) ≤ Real.exp (lam * S ω) := Real.exp_le_exp.mpr h3
        rwa [hP_exp ω]] at h
    exact h
  -- Conclude
  have hmu_le : μ {ω | τ ≤ S ω} ≤
      ENNReal.ofReal (Λ ^ N) / ENNReal.ofReal (Real.exp (lam * τ)) := by
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
      (Or.inl ENNReal.ofReal_ne_top)]
    rw [mul_comm]
    exact hMarkov.trans hlin_le
  have hmu_le' : μ {ω | τ ≤ S ω} ≤ ENNReal.ofReal (Real.exp (-lam * τ) * Λ ^ N) := by
    have hdiv : ENNReal.ofReal (Λ ^ N) / ENNReal.ofReal (Real.exp (lam * τ)) =
        ENNReal.ofReal (Real.exp (-lam * τ) * Λ ^ N) := by
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
      congr 1
      rw [show -lam * τ = -(lam * τ) by ring, Real.exp_neg, div_eq_mul_inv, mul_comm]
    rwa [hdiv] at hmu_le
  have hfinal := ENNReal.toReal_le_of_le_ofReal
    (by positivity : (0 : ℝ) ≤ Real.exp (-lam * τ) * Λ ^ N) hmu_le'
  rwa [Measure.real_def]
