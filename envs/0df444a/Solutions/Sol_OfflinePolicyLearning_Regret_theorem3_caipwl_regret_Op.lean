-- Prove2me | solution 1 for OfflinePolicyLearning.Regret.theorem3_caipwl_regret_Op
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:35:48.02732+00:00
-- url     : https://prove2.me/submissions/36e48509-9355-4bae-b889-d4198e0b1875
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Theorems.Thm_OfflinePolicyLearning_Regret_eq18_regret_le_sup_diff
import Theorems.Thm_OfflinePolicyLearning_Regret_lemma3_crossfit_uniform_op
import Theorems.Thm_OfflinePolicyLearning_Regret_oracle_uniform_concentration_Op

open MeasureTheory ProbabilityTheory Filter Topology
open OfflinePolicyLearning.Regret
/-- Under the polynomial-entropy bound of Assumption 3 the entropy integral is finite. -/
theorem opl_entropyIntegral_ne_top {X : Type*} {d : ℕ} (Pol : Set (X → Fin d))
    (Cc Dc ω : ℝ) (hCc : 0 < Cc) (hDc : 0 < Dc) (hω : 0 < ω) (hω' : ω < 1 / 2)
    (h3 : ∀ ε : ℝ, 0 < ε → ε < 1 → hammingCoverNum ε Pol ≠ ⊤ ∧
      ((hammingCoverNum ε Pol).toNat : ℝ) ≤ Cc * Real.exp (Dc * (1 / ε) ^ ω)) :
    entropyIntegral Pol ≠ ⊤ := by
  set A : ℝ := 1 + |Real.log Cc| with hA
  set g : ℝ → ℝ := fun ε => A + Dc * ε ^ (-(2 * ω)) with hg
  have hgint : IntegrableOn g (Set.Ioo (0 : ℝ) 1) := by
    have h1 : IntegrableOn (fun ε : ℝ => ε ^ (-(2 * ω))) (Set.Ioo (0 : ℝ) 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
    have h2 : IntegrableOn (fun _ : ℝ => A) (Set.Ioo (0 : ℝ) 1) := by
      refine integrableOn_const ?_
      simp
    exact h2.add (h1.const_mul Dc)
  have hbound : ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      (if hammingCoverNum (ε ^ 2) Pol = ⊤ then (⊤ : ENNReal)
        else ENNReal.ofReal (Real.sqrt (Real.log ((hammingCoverNum (ε ^ 2) Pol).toNat : ℝ))))
        ≤ ENNReal.ofReal (g ε) := by
    rintro ε ⟨hε0, hε1⟩
    have hε2 : 0 < ε ^ 2 := by positivity
    have hε2' : ε ^ 2 < 1 := by nlinarith
    obtain ⟨hne, hle⟩ := h3 (ε ^ 2) hε2 hε2'
    rw [if_neg hne]
    apply ENNReal.ofReal_le_ofReal
    set N : ℝ := ((hammingCoverNum (ε ^ 2) Pol).toNat : ℝ)
    have hN0 : 0 ≤ N := by positivity
    have ht : Dc * (1 / ε ^ 2) ^ ω = Dc * ε ^ (-(2 * ω)) := by
      congr 1
      rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg hε0.le, Real.rpow_mul hε0.le]
      norm_num
    have htnn : 0 ≤ Dc * ε ^ (-(2 * ω)) := by positivity
    have hlog : Real.log N ≤ |Real.log Cc| + Dc * ε ^ (-(2 * ω)) := by
      rcases hN0.eq_or_lt with h | h
      · rw [← h, Real.log_zero]; positivity
      · calc Real.log N ≤ Real.log (Cc * Real.exp (Dc * (1 / ε ^ 2) ^ ω)) :=
              Real.log_le_log h hle
          _ = Real.log Cc + Dc * (1 / ε ^ 2) ^ ω := by
              rw [Real.log_mul hCc.ne' (Real.exp_pos _).ne', Real.log_exp]
          _ ≤ |Real.log Cc| + Dc * ε ^ (-(2 * ω)) := by rw [ht]; linarith [le_abs_self (Real.log Cc)]
    have hsq : ∀ u : ℝ, 0 ≤ u → Real.sqrt u ≤ 1 + u := by
      intro u hu
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    calc Real.sqrt (Real.log N) ≤ 1 + max (Real.log N) 0 := by
          rcases le_total (Real.log N) 0 with h | h
          · rw [Real.sqrt_eq_zero'.2 h]; positivity
          · rw [max_eq_left h]; exact hsq _ h
      _ ≤ g ε := by
          simp only [hg, hA]
          have := abs_nonneg (Real.log Cc)
          rcases le_total (Real.log N) 0 with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
  unfold entropyIntegral
  rw [← lt_top_iff_ne_top]
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 1)).symm]
  calc _ ≤ ∫⁻ ε in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (g ε) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
          (Filter.Eventually.of_forall hbound))
    _ < ⊤ := hgint.lintegral_lt_top

/-- If two policies of `Pol` disagree somewhere, the entropy integral is positive. -/
theorem opl_entropyIntegral_ne_zero {X : Type*} {d : ℕ} (Pol : Set (X → Fin d))
    (π₁ π₂ : X → Fin d) (h₁ : π₁ ∈ Pol) (h₂ : π₂ ∈ Pol) (x₀ : X) (hx : π₁ x₀ ≠ π₂ x₀) :
    entropyIntegral Pol ≠ 0 := by
  classical
  set x : Fin 1 → X := fun _ => x₀
  -- the Hamming distance on one point
  have hdist : ∀ π π' : X → Fin d, π x₀ ≠ π' x₀ → OfflinePolicyLearning.Regret.hammingDist x π π' = 1 := by
    intro π π' h
    unfold OfflinePolicyLearning.Regret.hammingDist
    simp [x, h]
  have hdist0 : ∀ π π' : X → Fin d, π x₀ = π' x₀ → OfflinePolicyLearning.Regret.hammingDist x π π' = 0 := by
    intro π π' h
    unfold OfflinePolicyLearning.Regret.hammingDist
    simp [x, h]
  have hon : ∀ ε : ℝ, 0 ≤ ε → ε < 1 → 2 ≤ hammingCoverNumOn ε Pol x := by
    intro ε hε0 hε1
    unfold hammingCoverNumOn
    apply le_csInf
    · refine ⟨d, fun a => if h : ∃ π ∈ Pol, π x₀ = a then h.choose else π₁, ?_, ?_⟩
      · intro a
        dsimp only
        split_ifs with h
        · exact h.choose_spec.1
        · exact h₁
      · intro π hπ
        refine ⟨π x₀, ?_⟩
        have h : ∃ π' ∈ Pol, π' x₀ = π x₀ := ⟨π, hπ, rfl⟩
        dsimp only
        rw [dif_pos h, hdist0 _ _ h.choose_spec.2.symm]
        exact hε0
    · rintro K ⟨c, -, hc⟩
      by_contra hK
      push Not at hK
      obtain ⟨i, hi⟩ := hc π₁ h₁
      obtain ⟨j, hj⟩ := hc π₂ h₂
      have hij : i = j := by
        have : K ≤ 1 := by omega
        exact Fin.ext (by omega)
      subst hij
      have e1 : π₁ x₀ = c i x₀ := by
        by_contra h; rw [hdist _ _ h] at hi; linarith
      have e2 : π₂ x₀ = c i x₀ := by
        by_contra h; rw [hdist _ _ h] at hj; linarith
      exact hx (e1.trans e2.symm)
  have hcov : ∀ ε : ℝ, 0 ≤ ε → ε < 1 → (2 : ℕ∞) ≤ hammingCoverNum ε Pol := by
    intro ε hε0 hε1
    unfold hammingCoverNum
    refine le_trans ?_ (le_iSup_of_le 1 (le_iSup_of_le le_rfl (le_iSup_of_le x le_rfl)))
    exact_mod_cast hon ε hε0 hε1
  set c : ENNReal := ENNReal.ofReal (Real.sqrt (Real.log 2)) with hc
  have hcpos : 0 < c := by
    rw [hc, ENNReal.ofReal_pos]
    exact Real.sqrt_pos.2 (Real.log_pos (by norm_num))
  have hlow : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, c ≤
      (if hammingCoverNum (ε ^ 2) Pol = ⊤ then (⊤ : ENNReal)
        else ENNReal.ofReal (Real.sqrt (Real.log ((hammingCoverNum (ε ^ 2) Pol).toNat : ℝ)))) := by
    rintro ε ⟨hε0, hε1⟩
    split_ifs with htop
    · exact le_top
    · have h2 := hcov (ε ^ 2) (by positivity) (by nlinarith)
      have h2' : (2 : ℝ) ≤ ((hammingCoverNum (ε ^ 2) Pol).toNat : ℝ) := by
        have : 2 ≤ (hammingCoverNum (ε ^ 2) Pol).toNat := by
          have := ENat.toNat_le_toNat h2 htop
          simpa using this
        exact_mod_cast this
      apply ENNReal.ofReal_le_ofReal
      exact Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) h2')
  unfold entropyIntegral
  apply ne_of_gt
  calc (0 : ENNReal) < c * volume (Set.Ioo (0 : ℝ) 1) := by
        simp [hcpos]
    _ = ∫⁻ _ in Set.Ioo (0 : ℝ) 1, c := by rw [setLIntegral_const]
    _ ≤ _ := lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
          (Filter.Eventually.of_forall hlow))
    _ ≤ _ := lintegral_mono_set Set.Ioo_subset_Ioc_self

theorem opl_law_prob {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d) :
    IsProbabilityMeasure M.law := by
  unfold Model.law; infer_instance

/-- The outcome vector is a.s. bounded by `|B|` under the joint law. -/
theorem opl_law_bound {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) :
    ∀ᵐ ω ∂M.law, ∀ a, |ω.2.1 a| ≤ |B| := by
  have hmeasS : MeasurableSet {ω : Draw X d | ∀ a, |ω.2.1 a| ≤ |B|} := by
    have : {ω : Draw X d | ∀ a, |ω.2.1 a| ≤ |B|} = ⋂ a, {ω : Draw X d | |ω.2.1 a| ≤ |B|} := by
      ext ω; simp
    rw [this]
    refine MeasurableSet.iInter fun a => measurableSet_le ?_ measurable_const
    exact ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)).abs
  unfold Model.law
  refine Measure.ae_compProd_of_ae_ae hmeasS (Filter.Eventually.of_forall fun x => ?_)
  rw [Kernel.prod_apply]
  exact (Measure.quasiMeasurePreserving_fst).ae
    ((hB x).mono fun y hy a => (hy a).trans (le_abs_self B))

theorem opl_mu_bound {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) (x : X) (a : Fin d) :
    |M.μ x a| ≤ |B| := by
  have := norm_integral_le_of_norm_le_const (μ := M.κY x) (C := |B|)
    (f := fun y : Fin d → ℝ => y a) ((hB x).mono fun y hy => by
      simpa using (hy a).trans (le_abs_self B))
  simpa [Model.μ, probReal_univ] using this

theorem opl_Gamma_measurable {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (π : X → Fin d) (hπ : Measurable π) :
    Measurable fun ω : Draw X d => M.Γ (obs ω) (π ω.1) := by
  have hμm : ∀ j, Measurable fun x => M.μ x j := fun j =>
    (StronglyMeasurable.integral_kernel (κ := M.κY) (f := fun y : Fin d → ℝ => y j)
      (measurable_pi_apply j).stronglyMeasurable).measurable
  have hem : ∀ j, Measurable fun x => M.e x j := fun j =>
    (M.κA.measurable_coe (measurableSet_singleton j)).ennreal_toReal
  let H : Draw X d × (Fin d × Fin d) → ℝ := fun p =>
    M.μ p.1.1 p.2.2 + if p.2.1 = p.2.2 then (p.1.2.1 p.2.1 - M.μ p.1.1 p.2.1) / M.e p.1.1 p.2.1
      else 0
  have hH : Measurable H := by
    refine measurable_from_prod_countable_left fun y => ?_
    dsimp only [H]
    by_cases h : y.1 = y.2
    · simp only [h, if_true]
      exact ((hμm _).comp measurable_fst).add
        ((((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)).sub
          ((hμm _).comp measurable_fst)).div ((hem _).comp measurable_fst))
    · simp only [h, if_false, add_zero]
      exact (hμm _).comp measurable_fst
  have : (fun ω : Draw X d => M.Γ (obs ω) (π ω.1)) =
      H ∘ fun ω => (ω, (ω.2.2, π ω.1)) := rfl
  rw [this]
  exact hH.comp (measurable_id.prodMk
    ((measurable_snd.comp measurable_snd).prodMk (hπ.comp measurable_fst)))

theorem opl_Gamma_bound {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (η : ℝ) (hη : 0 < η) (hover : ∀ x a, η ≤ M.e x a)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) :
    ∀ᵐ ω ∂M.law, ∀ j, |M.Γ (obs ω) j| ≤ |B| + 2 * |B| / η := by
  filter_upwards [opl_law_bound M B hB] with ω hω j
  change |M.μ ω.1 j + (if ω.2.2 = j then (ω.2.1 ω.2.2 - M.μ ω.1 ω.2.2) / M.e ω.1 ω.2.2 else 0)|
    ≤ |B| + 2 * |B| / η
  have h1 := opl_mu_bound M B hB ω.1 j
  by_cases h : ω.2.2 = j
  · rw [if_pos h]
    have h2 := opl_mu_bound M B hB ω.1 ω.2.2
    have h3 := hω ω.2.2
    have he := hover ω.1 ω.2.2
    have hepos : 0 < M.e ω.1 ω.2.2 := lt_of_lt_of_le hη he
    have hq : |(ω.2.1 ω.2.2 - M.μ ω.1 ω.2.2) / M.e ω.1 ω.2.2| ≤ 2 * |B| / η := by
      rw [abs_div, abs_of_pos hepos]
      have hnum : |ω.2.1 ω.2.2 - M.μ ω.1 ω.2.2| ≤ 2 * |B| := by
        calc _ ≤ |ω.2.1 ω.2.2| + |M.μ ω.1 ω.2.2| := abs_sub _ _
          _ ≤ 2 * |B| := by linarith
      calc _ ≤ 2 * |B| / M.e ω.1 ω.2.2 := by gcongr
        _ ≤ 2 * |B| / η := by gcongr
    calc _ ≤ |M.μ ω.1 j| + |(ω.2.1 ω.2.2 - M.μ ω.1 ω.2.2) / M.e ω.1 ω.2.2| := abs_add_le _ _
      _ ≤ _ := by linarith
  · rw [if_neg h, add_zero]
    have : 0 ≤ 2 * |B| / η := by positivity
    linarith

/-- If `V* = 0`, all policies of `Pol` have the same value. -/
theorem opl_Q_eq_of_Vstar_zero {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (η : ℝ) (hη : 0 < η) (hover : ∀ x a, η ≤ M.e x a)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B)
    (Pol : Set (X → Fin d)) (hPol : Pol.Nonempty) (hPmeas : ∀ π ∈ Pol, Measurable π)
    (hperm : ∀ (m : ℕ) (s : Fin m → Fin d),
      MeasurableSet {x : Fin m → X | ∃ π ∈ Pol, ∀ i, π (x i) = s i})
    (Cc Dc ω : ℝ) (hCc : 0 < Cc) (hDc : 0 < Dc) (hω : 0 < ω) (hω' : ω < 1 / 2)
    (h3 : ∀ ε : ℝ, 0 < ε → ε < 1 → hammingCoverNum ε Pol ≠ ⊤ ∧
      ((hammingCoverNum ε Pol).toNat : ℝ) ≤ Cc * Real.exp (Dc * (1 / ε) ^ ω))
    (hV : M.Vstar Pol = 0) :
    ∀ πa ∈ Pol, ∀ πb ∈ Pol, M.Q πa = M.Q πb := by
  have := opl_law_prob M
  set Gb : ℝ := |B| + 2 * |B| / η with hGb
  have hΓb := opl_Gamma_bound M η hη hover B hB
  -- integrand of `V*`
  set F : (X → Fin d) → (X → Fin d) → Draw X d → ℝ := fun πa πb ω =>
    (M.Γ (obs ω) (πa ω.1) - M.Γ (obs ω) (πb ω.1)) ^ 2 with hF
  have hFb : ∀ πa πb, ∀ᵐ ω ∂M.law, ‖F πa πb ω‖ ≤ (2 * Gb) ^ 2 := by
    intro πa πb
    filter_upwards [hΓb] with ω hω
    have h1 := hω (πa ω.1); have h2 := hω (πb ω.1)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : |M.Γ (obs ω) (πa ω.1) - M.Γ (obs ω) (πb ω.1)| ≤ 2 * Gb := by
      calc _ ≤ |M.Γ (obs ω) (πa ω.1)| + |M.Γ (obs ω) (πb ω.1)| := abs_sub _ _
        _ ≤ 2 * Gb := by linarith
    calc F πa πb ω = |M.Γ (obs ω) (πa ω.1) - M.Γ (obs ω) (πb ω.1)| ^ 2 := by
          simp only [hF, sq_abs]
      _ ≤ (2 * Gb) ^ 2 := by gcongr
  have hFint : ∀ πa πb, ∫ ω, F πa πb ω ∂M.law ≤ (2 * Gb) ^ 2 := by
    intro πa πb
    have := norm_integral_le_of_norm_le_const (hFb πa πb)
    rw [probReal_univ, mul_one] at this
    exact (le_abs_self _).trans (by simpa using this)
  obtain ⟨π₀, hπ₀⟩ := hPol
  have : Nonempty Pol := ⟨⟨π₀, hπ₀⟩⟩
  have hinner : ∀ πa : Pol, BddAbove (Set.range fun πb : Pol => ∫ ω, F πa.1 πb.1 ω ∂M.law) :=
    fun πa => ⟨(2 * Gb) ^ 2, by rintro _ ⟨πb, rfl⟩; exact hFint _ _⟩
  have houter : BddAbove (Set.range fun πa : Pol => ⨆ πb : Pol, ∫ ω, F πa.1 πb.1 ω ∂M.law) :=
    ⟨(2 * Gb) ^ 2, by rintro _ ⟨πa, rfl⟩; exact ciSup_le fun πb => hFint _ _⟩
  -- each pair has a.s. equal oracle scores
  have hzero : ∀ πa ∈ Pol, ∀ πb ∈ Pol,
      ∀ᵐ ω ∂M.law, M.Γ (obs ω) (πa ω.1) = M.Γ (obs ω) (πb ω.1) := by
    intro πa ha πb hb
    have hle : ∫ ω, F πa πb ω ∂M.law ≤ 0 := by
      rw [← hV]
      exact (le_ciSup (hinner ⟨πa, ha⟩) ⟨πb, hb⟩).trans (le_ciSup houter ⟨πa, ha⟩)
    have hmeas : Measurable (F πa πb) :=
      ((opl_Gamma_measurable M πa (hPmeas πa ha)).sub
        (opl_Gamma_measurable M πb (hPmeas πb hb))).pow_const 2
    have hint : Integrable (F πa πb) M.law :=
      Integrable.of_bound hmeas.aestronglyMeasurable _ (hFb πa πb)
    have hnn : 0 ≤ F πa πb := fun ω => sq_nonneg _
    have h0 : ∫ ω, F πa πb ω ∂M.law = 0 := le_antisymm hle (integral_nonneg hnn)
    rw [integral_eq_zero_iff_of_nonneg hnn hint] at h0
    filter_upwards [h0] with ω hω
    have : (M.Γ (obs ω) (πa ω.1) - M.Γ (obs ω) (πb ω.1)) ^ 2 = 0 := hω
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  intro πa ha πb hb
  by_contra hne
  have hΔ : 0 < |M.Δ πa πb| := by
    rw [abs_pos]; intro h; apply hne; unfold Model.Δ at h; linarith
  obtain ⟨Mc, hMc, N, hN⟩ := oracle_uniform_concentration_Op M η hη hover B hB Pol
    ⟨π₀, hπ₀⟩ hPmeas hperm Cc Dc ω hCc hDc hω hω' h3 (1 / 2) (by norm_num)
  set n : ℕ := N + ⌈(Mc / |M.Δ πa πb|) ^ 2⌉₊ + 1 with hn
  have hnN : n ≥ N := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hsq : Mc / Real.sqrt n < |M.Δ πa πb| := by
    have hs : Mc / |M.Δ πa πb| < Real.sqrt n := by
      rw [Real.lt_sqrt (by positivity)]
      have h1 : (Mc / |M.Δ πa πb|) ^ 2 ≤ (⌈(Mc / |M.Δ πa πb|) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈(Mc / |M.Δ πa πb|) ^ 2⌉₊ : ℕ) : ℝ) < n := by
        rw [hn]; push_cast; linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
      linarith
    rw [div_lt_iff₀ (Real.sqrt_pos.2 hnpos)]
    rw [div_lt_iff₀ hΔ] at hs
    linarith
  have hS := hN n hnN
  set S := {D : Fin n → Draw X d | ∃ πa ∈ Pol, ∃ πb ∈ Pol,
        Mc / Real.sqrt n < |M.Δtilde D πa πb - M.Δ πa πb|} with hSdef
  have hae : ∀ᵐ D ∂M.sample n, D ∈ S := by
    have hall : ∀ᵐ D ∂M.sample n, ∀ i : Fin n,
        M.Γ (obs (D i)) (πa (D i).1) = M.Γ (obs (D i)) (πb (D i).1) := by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval (fun _ : Fin n => M.law) i).quasiMeasurePreserving.ae
        (hzero πa ha πb hb)
    filter_upwards [hall] with D hD
    refine ⟨πa, ha, πb, hb, ?_⟩
    have : M.Δtilde D πa πb = 0 := by
      unfold Model.Δtilde Model.Qtilde
      rw [Finset.sum_congr rfl fun i _ => hD i, sub_self]
    rw [this, zero_sub, abs_neg]
    exact hsq
  have hcompl : M.sample n Sᶜ = 0 := by
    rw [ae_iff] at hae
    simpa [Set.compl_def] using hae
  have hprob : IsProbabilityMeasure (M.sample n) := by unfold Model.sample; infer_instance
  have h1 : (1 : ENNReal) ≤ M.sample n S := by
    calc (1 : ENNReal) = M.sample n (S ∪ Sᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ M.sample n S + M.sample n Sᶜ := measure_union_le _ _
      _ = M.sample n S := by rw [hcompl, add_zero]
  have h2 : M.sample n S ≤ ENNReal.ofReal (1 / 2) := hS
  have : (1 : ENNReal) ≤ ENNReal.ofReal (1 / 2) := h1.trans h2
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
  norm_num at this

theorem solution {X : Type*} [MeasurableSpace X] {d : ℕ}
    (M : Model X d)
    (η : ℝ) (hη : 0 < η) (hover : ∀ x a, η ≤ M.e x a)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B)
    (K : ℕ) (hK : 2 ≤ K) (C : CrossFit X d K)
    (hfold : ∀ (n : ℕ) (k : Fin K), n / K ≤ (Finset.univ.filter fun i : Fin n => C.fold n i = k).card)
    (h2 : ∀ (k : Fin K) (a : Fin d),
      Tendsto (fun n : ℕ => (n : ℝ) * (C.mseMu M n k a * C.mseE M n k a)) atTop (𝓝 0))
    (h2μ : ∀ (k : Fin K) (a : Fin d), Tendsto (fun n : ℕ => C.mseMu M n k a) atTop (𝓝 0))
    (h2e : ∀ (k : Fin K) (a : Fin d), Tendsto (fun n : ℕ => C.mseE M n k a) atTop (𝓝 0))
    (Bhat ηhat : ℝ) (hηhat : 0 < ηhat)
    (hμbdd : ∀ n k T x a, |C.μhat n k T x a| ≤ Bhat)
    (hebdd : ∀ n k T x a, ηhat ≤ C.ehat n k T x a)
    (hμmeas : ∀ (n : ℕ) (k : Fin K) (a : Fin d),
      Measurable fun p : ({i : Fin n // C.fold n i ≠ k} → Obs X d) × X => C.μhat n k p.1 p.2 a)
    (hemeas : ∀ (n : ℕ) (k : Fin K) (a : Fin d),
      Measurable fun p : ({i : Fin n // C.fold n i ≠ k} → Obs X d) × X => C.ehat n k p.1 p.2 a)
    (Pol : Set (X → Fin d)) (hPol : Pol.Nonempty) (hPmeas : ∀ π ∈ Pol, Measurable π)
    (hperm : ∀ (m : ℕ) (s : Fin m → Fin d),
      MeasurableSet {x : Fin m → X | ∃ π ∈ Pol, ∀ i, π (x i) = s i})
    (Cc Dc ω : ℝ) (hCc : 0 < Cc) (hDc : 0 < Dc) (hω : 0 < ω) (hω' : ω < 1 / 2)
    (h3 : ∀ ε : ℝ, 0 < ε → ε < 1 → hammingCoverNum ε Pol ≠ ⊤ ∧
      ((hammingCoverNum ε Pol).toNat : ℝ) ≤ Cc * Real.exp (Dc * (1 / ε) ^ ω))
    (πhat : (n : ℕ) → (Fin n → Draw X d) → X → Fin d)
    (hmem : ∀ n D, πhat n D ∈ Pol)
    (hmax : ∀ n D, ∀ π ∈ Pol, C.Qhat D π ≤ C.Qhat D (πhat n D)) :
    ∀ ε : ℝ, 0 < ε → ∃ Mc : ℝ, 0 < Mc ∧ ∃ N : ℕ, ∀ n ≥ N,
      M.sample n {D | Mc * (entropyIntegral Pol).toReal * Real.sqrt (M.Vstar Pol / n) <
        M.regret Pol (πhat n D)} ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hκfin := opl_entropyIntegral_ne_top Pol Cc Dc ω hCc hDc hω hω' h3
  obtain ⟨π₀, hπ₀⟩ := hPol
  have hne : Nonempty Pol := ⟨⟨π₀, hπ₀⟩⟩
  -- degenerate case: all policies of `Pol` have the same value, so the regret vanishes
  have hdeg : (∀ πa ∈ Pol, ∀ πb ∈ Pol, M.Q πa = M.Q πb) →
      ∀ n D, M.regret Pol (πhat n D) ≤ 0 := by
    intro hQ n D
    unfold Model.regret
    have := ciSup_le fun π' : Pol => (hQ π'.1 π'.2 (πhat n D) (hmem n D)).le
    linarith
  set κr := (entropyIntegral Pol).toReal with hκr
  have hκnn : 0 ≤ κr := ENNReal.toReal_nonneg
  have hVnn : 0 ≤ M.Vstar Pol := by
    unfold Model.Vstar
    exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  by_cases hdegen : κr = 0 ∨ M.Vstar Pol = 0
  · have hQ : ∀ πa ∈ Pol, ∀ πb ∈ Pol, M.Q πa = M.Q πb := by
      rcases hdegen with h | h
      · have h0 : entropyIntegral Pol = 0 := by
          rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
          · exact h
          · exact absurd h hκfin
        intro πa ha πb hb
        have : πa = πb := by
          funext x
          by_contra hx
          exact opl_entropyIntegral_ne_zero Pol πa πb ha hb x hx h0
        rw [this]
      · exact opl_Q_eq_of_Vstar_zero M η hη hover B hB Pol ⟨π₀, hπ₀⟩ hPmeas hperm
          Cc Dc ω hCc hDc hω hω' h3 h
    refine ⟨1, one_pos, 0, fun n _ => ?_⟩
    have hempty : {D : Fin n → Draw X d | 1 * κr * Real.sqrt (M.Vstar Pol / n) <
        M.regret Pol (πhat n D)} = ∅ := by
      ext D
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h1 := hdeg hQ n D
      have h2 : 1 * κr * Real.sqrt (M.Vstar Pol / n) = 0 := by
        rcases hdegen with h | h <;> simp [h]
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  push Not at hdegen
  obtain ⟨hκ0, hV0⟩ := hdegen
  have hκpos : 0 < κr := lt_of_le_of_ne hκnn (Ne.symm hκ0)
  have hVpos : 0 < M.Vstar Pol := lt_of_le_of_ne hVnn (Ne.symm hV0)
  obtain ⟨Mc, hMc, N1, hN1⟩ := oracle_uniform_concentration_Op M η hη hover B hB Pol
    ⟨π₀, hπ₀⟩ hPmeas hperm Cc Dc ω hCc hDc hω hω' h3 (ε / 2) (by positivity)
  have hL3 := lemma3_crossfit_uniform_op M η hη hover B hB K hK C hfold h2 h2μ h2e Bhat ηhat
    hηhat hμbdd hebdd hμmeas hemeas Pol ⟨π₀, hπ₀⟩ hPmeas hperm hκfin 1 one_pos
  have hev := (tendsto_order.1 hL3).2 (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hev
  have hsV : 0 < Real.sqrt (M.Vstar Pol) := Real.sqrt_pos.2 hVpos
  refine ⟨(1 + Mc) / (κr * Real.sqrt (M.Vstar Pol)), by positivity, max (max N1 N2) 1,
    fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : (0 : ℝ) < n := by
    have : 1 ≤ n := le_trans (le_max_right _ _) hn
    exact_mod_cast this
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  set S2 := {D : Fin n → Draw X d | ∃ πa ∈ Pol, ∃ πb ∈ Pol,
        Mc / Real.sqrt n < |M.Δtilde D πa πb - M.Δ πa πb|} with hS2
  set S3 := {D : Fin n → Draw X d | ∃ πa ∈ Pol, ∃ πb ∈ Pol,
        1 / Real.sqrt n ≤ |C.Δhat D πa πb - M.Δtilde D πa πb|} with hS3
  have hsub : {D : Fin n → Draw X d | (1 + Mc) / (κr * Real.sqrt (M.Vstar Pol)) * κr *
      Real.sqrt (M.Vstar Pol / n) < M.regret Pol (πhat n D)} ⊆ S2 ∪ S3 := by
    intro D hD
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    obtain ⟨hc2, hc3⟩ := hc
    have hbound : ∀ πa ∈ Pol, ∀ πb ∈ Pol,
        |C.Δhat D πa πb - M.Δ πa πb| ≤ (1 + Mc) / Real.sqrt n := by
      intro πa ha πb hb
      have e2 : |M.Δtilde D πa πb - M.Δ πa πb| ≤ Mc / Real.sqrt n :=
        not_lt.1 fun h => hc2 ⟨πa, ha, πb, hb, h⟩
      have e3 : |C.Δhat D πa πb - M.Δtilde D πa πb| < 1 / Real.sqrt n :=
        not_le.1 fun h => hc3 ⟨πa, ha, πb, hb, h⟩
      have := abs_sub_le (C.Δhat D πa πb) (M.Δtilde D πa πb) (M.Δ πa πb)
      rw [add_div]
      linarith
    have hreg := eq18_regret_le_sup_diff M B hB C Pol D (πhat n D) (hmem n D) (hmax n D)
    have hsup : (⨆ π₁ : Pol, ⨆ π₂ : Pol, |C.Δhat D π₁.1 π₂.1 - M.Δ π₁.1 π₂.1|) ≤
        (1 + Mc) / Real.sqrt n :=
      ciSup_le fun π₁ => ciSup_le fun π₂ => hbound _ π₁.2 _ π₂.2
    have heq : (1 + Mc) / (κr * Real.sqrt (M.Vstar Pol)) * κr * Real.sqrt (M.Vstar Pol / n) =
        (1 + Mc) / Real.sqrt n := by
      rw [Real.sqrt_div hVnn]
      field_simp
    have hD' : (1 + Mc) / (κr * Real.sqrt (M.Vstar Pol)) * κr * Real.sqrt (M.Vstar Pol / n) <
        M.regret Pol (πhat n D) := hD
    linarith
  calc _ ≤ M.sample n (S2 ∪ S3) := measure_mono hsub
    _ ≤ M.sample n S2 + M.sample n S3 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add (hN1 n hn1) (hN2 n hn2).le
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
