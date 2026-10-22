-- Prove2me | solution 1 for RedundancyStab.IID.emptying_time
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:15:16.851591+00:00
-- url     : https://prove2.me/submissions/915e4867-e7d2-48ee-9f1f-3e9e27d0d7d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RedundancyStab_IID_FluidModel
import Theorems.Thm_RedundancyStab_IID_lemma_1
import Theorems.Thm_RedundancyStab_IID_lemma_2
import Theorems.Thm_ProcessingNetworks_LyapunovCriteria_dini_extinction_criterion
import Theorems.Thm_ProcessingNetworks_LyapunovCriteria_max_derivative_at_active_index

open RedundancyStab.IID MeasureTheory ProbabilityTheory Filter

theorem solution {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ)
    (hρ : lam / (μ * K) < 1)
    (P : Primitives K d lam μ Ω) (pol : Policy) (n0 : JobType K d → ℝ) (hn0 : ∀ c, 0 ≤ n0 c) :
    ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ n τ : JobType K d → ℝ → ℝ, IsFluidLimitAt P pol n0 ω n τ →
      ∀ c, n c ((⨆ s : Fin K, fluidCopies K d (fun c' => n c' 0) s) /
        ((d : ℝ) * (μ - lam / K))) = 0 := by
  classical
  filter_upwards [lemma_1 K d hd hdK lam μ hlam hμ P pol n0 hn0,
    lemma_2 K d hd hdK lam μ hlam hμ P pol n0 hn0] with ω h1 h2
  intro n τ hfl c0
  obtain ⟨r, hrpos, hrtend, hconv⟩ := hfl
  obtain ⟨φ, hφ, n', τ', hconv', -, hrep, hnn, -, -, -, hlip⟩ := h1 r hrpos hrtend
  -- the fluid limit along `r` coincides with the one of Lemma 1 along the subsequence
  have hid : ∀ c t, 0 ≤ t → n c t = n' c t := by
    intro c t ht
    have A := ((hconv c t ht).1.tendsto_at (Set.mem_Icc.2 ⟨ht, le_rfl⟩))
    have B := ((hconv' c t ht).1.tendsto_at (Set.mem_Icc.2 ⟨ht, le_rfl⟩))
    exact tendsto_nhds_unique (A.comp hφ.tendsto_atTop) B
  have hK : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hlt : lam / K < μ := by
    rw [div_lt_iff₀ (by positivity)] at hρ
    rw [div_lt_iff₀ hKr]; linarith
  set ε : ℝ := (d : ℝ) * (μ - lam / K) with hεdef
  have hε : 0 < ε := mul_pos hdr (by linarith)
  have hC : 0 ≤ lam / (K.choose d : ℝ) := by positivity
  set L0 : ℝ := lam / (K.choose d : ℝ) + μ * d with hL0
  have hL0nn : 0 ≤ L0 := by positivity
  have hnn' : ∀ c t, 0 ≤ t → 0 ≤ n c t := fun c t ht => (hid c t ht).symm ▸ hnn c t ht
  -- Lipschitz bound for each `n_c` on `t ≥ 0`
  have hnl : ∀ c t u, 0 ≤ t → 0 ≤ u → |n c t - n c u| ≤ L0 * |t - u| := by
    intro c t u ht hu
    rw [hid c t ht, hid c u hu, hrep c t ht, hrep c u hu]
    have h := (hlip c).dist_le_mul t ht u hu
    rw [Real.dist_eq, Real.dist_eq] at h
    simp only [NNReal.coe_natCast] at h
    calc |n0 c + lam / ↑(K.choose d) * t - μ * τ' c t -
          (n0 c + lam / ↑(K.choose d) * u - μ * τ' c u)|
        = |lam / ↑(K.choose d) * (t - u) - μ * (τ' c t - τ' c u)| := by congr 1; ring
      _ ≤ |lam / ↑(K.choose d) * (t - u)| + |μ * (τ' c t - τ' c u)| := abs_sub _ _
      _ = lam / ↑(K.choose d) * |t - u| + μ * |τ' c t - τ' c u| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hC, abs_of_pos hμ]
      _ ≤ lam / ↑(K.choose d) * |t - u| + μ * (d * |t - u|) := by gcongr
      _ = L0 * |t - u| := by ring
  -- the fluid copies at each server, and their maximum
  set m : Fin K → ℝ → ℝ := fun s t => fluidCopies K d (fun c => n c t) s with hm
  set f : ℝ → ℝ := fun t => ⨆ s, m s t with hf
  set L : ℝ := (Fintype.card (JobType K d) : ℝ) * L0 with hL
  have hLnn : 0 ≤ L := by positivity
  have hml : ∀ s t u, 0 ≤ t → 0 ≤ u → |m s t - m s u| ≤ L * |t - u| := by
    intro s t u ht hu
    simp only [hm, fluidCopies]
    rw [← Finset.sum_sub_distrib]
    calc |∑ c ∈ typesAt K d s, (n c t - n c u)|
        ≤ ∑ c ∈ typesAt K d s, |n c t - n c u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c ∈ typesAt K d s, L0 * |t - u| := Finset.sum_le_sum fun c _ => hnl c t u ht hu
      _ = ((typesAt K d s).card : ℝ) * (L0 * |t - u|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card (JobType K d) : ℝ) * (L0 * |t - u|) := by
          gcongr
          exact_mod_cast Finset.card_le_univ _
      _ = L * |t - u| := by ring
  have hbdd : ∀ t, BddAbove (Set.range fun s => m s t) := fun t => (Set.finite_range _).bddAbove
  have hmf : ∀ s t, m s t ≤ f t := fun s t => le_ciSup (hbdd t) s
  have hfl : ∀ t u, 0 ≤ t → 0 ≤ u → |f t - f u| ≤ L * |t - u| := by
    have one : ∀ t u, 0 ≤ t → 0 ≤ u → f t ≤ f u + L * |t - u| := by
      intro t u ht hu
      apply ciSup_le
      intro s
      have := hml s t u ht hu
      have := hmf s u
      have := (abs_le.1 (hml s t u ht hu)).2
      linarith
    intro t u ht hu
    have a := one t u ht hu
    have b := one u t hu ht
    rw [abs_sub_comm u t] at b
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have hLf : LipschitzOnWith (Real.toNNReal L) f (Set.Ici 0) := by
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq]
    exact hfl x y hx hy
  have hLn : ∀ c, LipschitzOnWith (Real.toNNReal L0) (n c) (Set.Ici 0) := by
    intro c
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq]
    exact hnl c x y hx hy
  have hfnn : ∀ t, 0 ≤ t → 0 ≤ f t := by
    intro t ht
    obtain ⟨s⟩ := (inferInstance : Nonempty (Fin K))
    refine le_trans ?_ (hmf s t)
    simp only [hm, fluidCopies]
    exact Finset.sum_nonneg fun c _ => hnn' c t ht
  -- the Dini derivative of `f` is bounded by the Lipschitz constant
  have hdini_le : ∀ t, 0 ≤ t →
      ProcessingNetworks.LyapunovCriteria.diniUpperRight f t ≤ (L : EReal) := by
    intro t ht
    unfold ProcessingNetworks.LyapunovCriteria.diniUpperRight
    refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    rw [EReal.coe_le_coe_iff, div_le_iff₀ hh]
    have := hfl (t + h) t (by linarith) ht
    rw [show t + h - t = h by ring, abs_of_pos hh] at this
    exact (le_abs_self _).trans this
  have hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t →
      ProcessingNetworks.LyapunovCriteria.diniUpperRight f t ≤ ((-ε : ℝ) : EReal) := by
    have hdc : ∀ c, ∀ᵐ t, t ∈ Set.Ici (0 : ℝ) →
        DifferentiableWithinAt ℝ (n c) (Set.Ici 0) t := fun c =>
      (hLn c).locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem
    have hdf : ∀ᵐ t, t ∈ Set.Ici (0 : ℝ) → DifferentiableWithinAt ℝ f (Set.Ici 0) t :=
      hLf.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem
    filter_upwards [ae_all_iff.2 hdc, hdf, Measure.ae_ne volume (0 : ℝ)] with t hnc hft ht0
      htnn hfpos
    have htpos : 0 < t := lt_of_le_of_ne htnn (Ne.symm ht0)
    have hnd : ∀ c, DifferentiableAt ℝ (n c) t := fun c =>
      (hnc c htnn).differentiableAt (Ici_mem_nhds htpos)
    have hfd : DifferentiableAt ℝ f t := (hft htnn).differentiableAt (Ici_mem_nhds htpos)
    obtain ⟨s, hs⟩ := exists_eq_ciSup_of_finite (f := fun s => m s t)
    have hmax : ∀ l, m l t ≤ m s t := fun l => by
      have := hmf l t
      simp only [hf] at this
      rw [← hs] at this
      exact this
    have hspos : 0 < m s t := by
      have : m s t = f t := hs
      rw [this]; exact hfpos
    have hder := h2 n τ ⟨r, hrpos, hrtend, hconv⟩ s t htpos hnd hmax hspos
    have hmsd : DifferentiableAt ℝ (m s) t := by
      simp only [hm, fluidCopies]
      exact DifferentiableAt.fun_sum (fun c _ => hnd c)
    have heq := ProcessingNetworks.LyapunovCriteria.max_derivative_at_active_index m t htpos s
      hs hmsd hfd
    have hderf : deriv f t ≤ -ε := by
      have : deriv f t = deriv (m s) t := heq
      rw [this]
      have e2 : lam * d / K - μ * d = -ε := by rw [hεdef]; ring
      rw [← e2]
      exact hder
    have htend := hfd.hasDerivAt.tendsto_slope_zero_right
    have htend' : Tendsto (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((deriv f t : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      refine htend.congr (fun h => ?_)
      simp [smul_eq_mul, div_eq_inv_mul]
    unfold ProcessingNetworks.LyapunovCriteria.diniUpperRight
    rw [htend'.limsup_eq]
    exact_mod_cast hderf
  have hext := ProcessingNetworks.LyapunovCriteria.dini_extinction_criterion f hfnn
    (hLf.continuousOn.mono Set.Ioi_subset_Ici_self)
    (fun a b ha _ => ⟨L + 1, by linarith, fun t ht =>
      (hdini_le t (le_trans ha ht.1)).trans (by exact_mod_cast (by linarith : L ≤ L + 1))⟩)
    ε hε hdrift
  -- conclusion
  set T : ℝ := f 0 / ε with hT
  have hT0 : 0 ≤ T := div_nonneg (hfnn 0 le_rfl) hε.le
  have hfT : f T = 0 := hext T le_rfl
  have hne : c0.1.Nonempty := by
    rw [← Finset.card_pos, c0.2]; omega
  obtain ⟨s, hs⟩ := hne
  have hle : n c0 T ≤ m s T := by
    simp only [hm, fluidCopies]
    exact Finset.single_le_sum (f := fun c => n c T) (fun c _ => hnn' c T hT0)
      (by simp [typesAt, hs])
  have := hmf s T
  show n c0 T = 0
  linarith [hnn' c0 T hT0]
