-- Prove2me | solution 1 for RobustRegLasso.WorstCaseExp.corollary_3_worst_case_expectation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:15:01.081899+00:00
-- url     : https://prove2.me/submissions/d6088db0-c9cb-4327-8a0d-892f120d7632

import Mathlib
import Definitions.Def_RobustRegLasso_WorstCaseExp_Basic
import Theorems.Thm_RobustRegLasso_WorstCaseExp_appendix_d_robust_identity
import Theorems.Thm_RobustRegLasso_WorstCaseExp_appendix_d_box_decomposition

open MeasureTheory

namespace RobustRegLasso.WorstCaseExp

private lemma box_eq_pi {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b σ : Fin n → ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    box A b σ Δ i = Set.pi Set.univ
      (Fin.cons (Set.Icc (b i - σ i) (b i + σ i))
        (fun j => Set.Icc (A i j - Δ i j) (A i j + Δ i j))) := by
  ext z
  simp [box, Fin.forall_fin_succ]

private lemma isCompact_box {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b σ : Fin n → ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    IsCompact (box A b σ Δ i) := by
  rw [box_eq_pi]
  refine isCompact_univ_pi fun k => ?_
  refine Fin.cases ?_ (fun _ => ?_) k <;> exact isCompact_Icc

private lemma measurableSet_box {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b σ : Fin n → ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    MeasurableSet (box A b σ Δ i) :=
  (isCompact_box A b σ Δ i).isClosed.measurableSet

private lemma continuous_sqLoss {m : ℕ} (x : Fin m → ℝ) :
    Continuous (sqLoss x) := by
  unfold sqLoss
  exact (((continuous_apply 0).sub
    (continuous_finsetSum _ fun j _ => (continuous_apply j.succ).mul continuous_const)).pow 2)

private lemma risk_le_of_distClass {n m : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin m) ℝ) (b σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ)
    (x : Fin m → ℝ) {μ : Measure (Fin (m + 1) → ℝ)} (hμ : μ ∈ distClass A b σ Δ) :
    ∃ s : Fin n → ℝ, (∀ i, IsGreatest (sqLoss x '' box A b σ Δ i) (s i)) ∧
      rootScaledRisk n x μ ≤ ENNReal.ofReal (Real.sqrt (∑ i, s i)) := by
  classical
  have : IsProbabilityMeasure μ := hμ.1
  have hcov := hμ.2
  have hbox_ne : ∀ i : Fin n, (box A b σ Δ i).Nonempty := by
    intro i
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    have hle := hcov {i}
    simp [hemp] at hle
    exact hn.ne' hle
  have hex : ∀ i : Fin n, ∃ si : ℝ, IsGreatest (sqLoss x '' box A b σ Δ i) si := by
    intro i
    have hK : IsCompact (sqLoss x '' box A b σ Δ i) :=
      (isCompact_box A b σ Δ i).image (continuous_sqLoss x)
    obtain ⟨z₀, hz₀⟩ := hbox_ne i
    have hne : (sqLoss x '' box A b σ Δ i).Nonempty := ⟨sqLoss x z₀, z₀, hz₀, rfl⟩
    exact ⟨sSup (sqLoss x '' box A b σ Δ i), hK.sSup_mem hne,
      (isLUB_csSup hne hK.bddAbove).1⟩
  choose s hs using hex
  have hs_nn : ∀ i : Fin n, 0 ≤ s i := by
    intro i
    obtain ⟨z₀, hz₀⟩ := hbox_ne i
    have h0 : 0 ≤ sqLoss x z₀ := by unfold sqLoss; positivity
    exact h0.trans ((hs i).2 ⟨z₀, hz₀, rfl⟩)
  refine ⟨s, hs, ?_⟩
  let π : Equiv.Perm (Fin n) := Tuple.sort s
  have hmono : Monotone (s ∘ π) := Tuple.monotone_sort s
  let t : ℕ → ℝ := fun k =>
    match k with
    | 0 => 0
    | k + 1 => if hk : k < n then s (π ⟨k, hk⟩) else 0
  have ht_succ : ∀ (k : ℕ) (hk : k < n), t (k + 1) = s (π ⟨k, hk⟩) := by
    intro k hk
    simp [t, hk]
  have ht_diff_nn : ∀ k ∈ Finset.range n, 0 ≤ t (k + 1) - t k := by
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    cases k with
    | zero =>
      simp [t, hkn, hs_nn]
    | succ k' =>
      have hk' : k' < n := Nat.lt_of_succ_lt hkn
      rw [ht_succ (k' + 1) hkn, ht_succ k' hk', sub_nonneg]
      exact hmono (Fin.mk_le_mk.mpr (Nat.le_succ k'))
  let Sk : ℕ → Finset (Fin n) := fun k =>
    (Finset.univ.filter (fun j : Fin n => j.val < k)).map π.toEmbedding
  let Vk : ℕ → Set (Fin (m + 1) → ℝ) := fun k => ⋃ i ∈ Sk k, box A b σ Δ i
  have hVk_meas : ∀ k : ℕ, MeasurableSet (Vk k) := fun k =>
    Finset.measurableSet_biUnion (Sk k) (fun i _ => measurableSet_box A b σ Δ i)
  have hSk_card : ∀ {k : ℕ}, k ≤ n → (Sk k).card = k := by
    intro k hkn
    rw [Finset.card_map]
    have hbij : (Finset.univ.filter (fun j : Fin n => j.val < k)).card =
        (Finset.range k).card := by
      refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
      · intro j₁ _ j₂ _ h
        exact Fin.ext h
      · intro a ha
        have hak : a < k := Finset.mem_range.mp ha
        exact ⟨⟨a, lt_of_lt_of_le hak hkn⟩, by simp [hak], rfl⟩
    simpa using hbij
  have hVk_compl : ∀ {k : ℕ}, k ≤ n →
      μ (Vk k)ᶜ ≤ ENNReal.ofReal (1 - (k : ℝ) / n) := by
    intro k hkn
    have hmc : μ (Vk k)ᶜ = 1 - μ (Vk k) := by
      rw [measure_compl (hVk_meas k) (measure_ne_top μ _), measure_univ]
    have hcov_k : ENNReal.ofReal ((k : ℝ) / n) ≤ μ (Vk k) := by
      simpa [Vk, hSk_card hkn] using hcov (Sk k)
    rw [hmc]
    refine (tsub_le_tsub_left hcov_k 1).trans ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by positivity)]
  have hVn_null : μ (Vk n)ᶜ = 0 := by
    have hle := hVk_compl le_rfl
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [div_self hn0, sub_self, ENNReal.ofReal_zero] at hle
    exact nonpos_iff_eq_zero.mp hle
  have hae : ∀ᵐ z ∂μ, ENNReal.ofReal (sqLoss x z) ≤
      ∑ k ∈ Finset.range n,
        ENNReal.ofReal (t (k + 1) - t k) * (Vk k)ᶜ.indicator (fun _ => (1 : ENNReal)) z := by
    refine Filter.eventually_of_mem (mem_ae_iff.mpr hVn_null) ?_
    intro z hz
    have hz_mem_i : ∃ i : Fin n, z ∈ box A b σ Δ i := by
      simpa [Vk, Sk] using hz
    let F : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => z ∈ box A b σ Δ (π j))
    have hF_ne : F.Nonempty := by
      obtain ⟨i, hi⟩ := hz_mem_i
      exact ⟨π.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hi⟩⟩
    let j₀ : Fin n := F.min' hF_ne
    have hj₀_box : z ∈ box A b σ Δ (π j₀) :=
      (Finset.mem_filter.mp (F.min'_mem hF_ne)).2
    have hsq_le : sqLoss x z ≤ t (j₀.val + 1) - t 0 := by
      rw [ht_succ j₀.val j₀.isLt]
      simpa [t] using (hs (π j₀)).2 ⟨z, hj₀_box, rfl⟩
    have hsub_range : Finset.range (j₀.val + 1) ⊆ Finset.range n :=
      Finset.range_mono (Nat.succ_le_of_lt j₀.isLt)
    have hind_one : ∀ k ∈ Finset.range (j₀.val + 1),
        (Vk k)ᶜ.indicator (fun _ => (1 : ENNReal)) z = 1 := by
      intro k hk
      have hkle : k ≤ j₀.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hz_not : z ∈ (Vk k)ᶜ := by
        intro hzk
        have hex_i : ∃ i : Fin n, (π.symm i).val < k ∧ z ∈ box A b σ Δ i := by
          simpa [Vk, Sk] using hzk
        obtain ⟨i, hjk, hjbox⟩ := hex_i
        have hj_ge : j₀ ≤ π.symm i :=
          F.min'_le (π.symm i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hjbox⟩)
        exact absurd (lt_of_lt_of_le hjk hkle) (not_lt.mpr hj_ge)
      exact Set.indicator_of_mem hz_not _
    calc
      ENNReal.ofReal (sqLoss x z)
        ≤ ENNReal.ofReal (t (j₀.val + 1) - t 0) := ENNReal.ofReal_le_ofReal hsq_le
      _ = ENNReal.ofReal (∑ k ∈ Finset.range (j₀.val + 1), (t (k + 1) - t k)) := by
          rw [Finset.sum_range_sub]
      _ = ∑ k ∈ Finset.range (j₀.val + 1), ENNReal.ofReal (t (k + 1) - t k) :=
          ENNReal.ofReal_sum_of_nonneg fun k hk => ht_diff_nn k (hsub_range hk)
      _ = ∑ k ∈ Finset.range (j₀.val + 1),
            ENNReal.ofReal (t (k + 1) - t k) * (Vk k)ᶜ.indicator (fun _ => (1 : ENNReal)) z := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hind_one k hk, mul_one]
      _ ≤ ∑ k ∈ Finset.range n,
            ENNReal.ofReal (t (k + 1) - t k) * (Vk k)ᶜ.indicator (fun _ => (1 : ENNReal)) z :=
          Finset.sum_le_sum_of_subset hsub_range
  have hlint_le : ∫⁻ z, ENNReal.ofReal (sqLoss x z) ∂μ ≤
      ENNReal.ofReal (∑ k ∈ Finset.range n, (t (k + 1) - t k) * (1 - (k : ℝ) / n)) := by
    calc
      ∫⁻ z, ENNReal.ofReal (sqLoss x z) ∂μ
        ≤ ∫⁻ z, (∑ k ∈ Finset.range n,
            ENNReal.ofReal (t (k + 1) - t k) *
              (Vk k)ᶜ.indicator (fun _ => (1 : ENNReal)) z) ∂μ := lintegral_mono_ae hae
      _ = ∑ k ∈ Finset.range n,
            ENNReal.ofReal (t (k + 1) - t k) * μ (Vk k)ᶜ := by
          rw [lintegral_finsetSum]
          · refine Finset.sum_congr rfl fun k _ => ?_
            rw [lintegral_const_mul _ (measurable_const.indicator (hVk_meas k).compl),
              lintegral_indicator (hVk_meas k).compl, lintegral_const,
              Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul]
          · intro k _
            exact (measurable_const.indicator (hVk_meas k).compl).const_mul _
      _ ≤ ∑ k ∈ Finset.range n,
            ENNReal.ofReal (t (k + 1) - t k) * ENNReal.ofReal (1 - (k : ℝ) / n) := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact mul_le_mul_of_nonneg_left
            (hVk_compl (Nat.le_of_lt (Finset.mem_range.mp hk))) zero_le
      _ = ∑ k ∈ Finset.range n,
            ENNReal.ofReal ((t (k + 1) - t k) * (1 - (k : ℝ) / n)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [ENNReal.ofReal_mul (ht_diff_nn k hk)]
      _ = ENNReal.ofReal (∑ k ∈ Finset.range n, (t (k + 1) - t k) * (1 - (k : ℝ) / n)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro k hk
          have hkn : (k : ℝ) ≤ n := Nat.cast_le.mpr (Nat.le_of_lt (Finset.mem_range.mp hk))
          have h1 : 0 ≤ 1 - (k : ℝ) / n := by
            rw [sub_nonneg, div_le_one (Nat.cast_pos.mpr hn)]
            exact hkn
          exact mul_nonneg (ht_diff_nn k hk) h1
  have hsum_id : (n : ℝ) * ∑ k ∈ Finset.range n, (t (k + 1) - t k) * (1 - (k : ℝ) / n) =
      ∑ i : Fin n, s i := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [Finset.mul_sum]
    have h1 : ∑ k ∈ Finset.range n, (n : ℝ) * ((t (k + 1) - t k) * (1 - (k : ℝ) / n)) =
        ∑ k ∈ Finset.range n, (t (k + 1) - t k) * ((n : ℝ) - k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp [hn0]
    rw [h1]
    let g : ℕ → ℝ := fun k => t k * ((n : ℝ) - (k : ℝ))
    have h2 : ∀ k : ℕ, (t (k + 1) - t k) * ((n : ℝ) - k) =
        (g (k + 1) - g k) + t (k + 1) := by
      intro k
      dsimp [g]
      push_cast
      ring
    simp_rw [h2]
    rw [Finset.sum_add_distrib, Finset.sum_range_sub]
    have hg : g n - g 0 = 0 := by simp [g, t]
    rw [hg, zero_add]
    calc
      ∑ k ∈ Finset.range n, t (k + 1)
        = ∑ k : Fin n, t (k.val + 1) := (Fin.sum_univ_eq_sum_range (fun k => t (k + 1)) n).symm
      _ = ∑ k : Fin n, s (π k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact ht_succ k.val k.isLt
      _ = ∑ i : Fin n, s i := Equiv.sum_comp π s
  unfold rootScaledRisk
  have hmul_le : (n : ENNReal) * ∫⁻ z, ENNReal.ofReal (sqLoss x z) ∂μ ≤
      ENNReal.ofReal (∑ i : Fin n, s i) := by
    calc
      (n : ENNReal) * ∫⁻ z, ENNReal.ofReal (sqLoss x z) ∂μ
        ≤ ENNReal.ofReal (n : ℝ) *
            ENNReal.ofReal (∑ k ∈ Finset.range n, (t (k + 1) - t k) * (1 - (k : ℝ) / n)) := by
          rw [ENNReal.ofReal_natCast]
          exact mul_le_mul_of_nonneg_left hlint_le zero_le
      _ = ENNReal.ofReal ((n : ℝ) *
            ∑ k ∈ Finset.range n, (t (k + 1) - t k) * (1 - (k : ℝ) / n)) := by
          rw [← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      _ = ENNReal.ofReal (∑ i : Fin n, s i) := by rw [hsum_id]
  calc
    ((n : ENNReal) * ∫⁻ z, ENNReal.ofReal (sqLoss x z) ∂μ) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (∑ i : Fin n, s i)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hmul_le (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (∑ i : Fin n, s i)) := by
        rw [Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun i _ => hs_nn i) (by norm_num)]

private lemma diracMixture_mem_distClass_and_risk {n m : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin m) ℝ) (b σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ)
    (x : Fin m → ℝ) (p : Fin n → Fin (m + 1) → ℝ) (hp : ∀ i, p i ∈ box A b σ Δ i) :
    ∃ μ ∈ distClass A b σ Δ,
      rootScaledRisk n x μ = ENNReal.ofReal (Real.sqrt (∑ i, sqLoss x (p i))) := by
  let μ : Measure (Fin (m + 1) → ℝ) := (n : ENNReal)⁻¹ • ∑ i : Fin n, Measure.dirac (p i)
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn.ne') (ENNReal.natCast_ne_top n)
  refine ⟨μ, ⟨hprob, ?_⟩, ?_⟩
  · intro S
    simp only [μ, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    have hsub : (S.card : ENNReal) ≤
        ∑ i : Fin n, (Measure.dirac (p i)) (⋃ j ∈ S, box A b σ Δ j) := by
      calc
        (S.card : ENNReal) = ∑ _i ∈ S, (1 : ENNReal) := by simp
        _ ≤ ∑ i ∈ S, (Measure.dirac (p i)) (⋃ j ∈ S, box A b σ Δ j) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hmem : p i ∈ ⋃ j ∈ S, box A b σ Δ j := Set.mem_biUnion hi (hp i)
          rw [Measure.dirac_apply_of_mem hmem]
        _ ≤ ∑ i : Fin n, (Measure.dirac (p i)) (⋃ j ∈ S, box A b σ Δ j) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    have hcast : ENNReal.ofReal ((S.card : ℝ) / n) = (n : ENNReal)⁻¹ * (S.card : ENNReal) := by
      rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hn),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [hcast]
    exact mul_le_mul_of_nonneg_left hsub zero_le
  · unfold rootScaledRisk
    have hmeas : Measurable (fun z => ENNReal.ofReal (sqLoss x z)) :=
      ENNReal.measurable_ofReal.comp (continuous_sqLoss x).measurable
    have hlint : ∫⁻ z, ENNReal.ofReal (sqLoss x z) ∂μ =
        (n : ENNReal)⁻¹ * ∑ i : Fin n, ENNReal.ofReal (sqLoss x (p i)) := by
      simp only [μ, lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      exact lintegral_dirac' (p i) hmeas
    rw [hlint, ← mul_assoc,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hn.ne') (ENNReal.natCast_ne_top n), one_mul]
    have hsum_nn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ sqLoss x (p i) := by
      intro i _
      unfold sqLoss
      positivity
    rw [← ENNReal.ofReal_sum_of_nonneg hsum_nn, Real.sqrt_eq_rpow,
      ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg hsum_nn) (by norm_num)]

end RobustRegLasso.WorstCaseExp

open RobustRegLasso.WorstCaseExp in
theorem solution {n m : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (x : Fin m → ℝ) :
    IsLUB {v : ENNReal | ∃ μ ∈ hatP A b c, v = rootScaledRisk n x μ}
      (ENNReal.ofReal (regularizedLoss A b c x)) := by
  have hId := appendix_d_robust_identity hn A b c hc x
  have hDecomp := appendix_d_box_decomposition hn A b c hc x (regularizedLoss A b c x)
  have hLUB1 := hId.isLUB
  have hLUB2 := hDecomp.1.mp hLUB1
  have hLUB3 := hDecomp.2.mp hLUB2
  refine ⟨?_, ?_⟩
  · rintro v ⟨μ, ⟨σ, Δ, hAdm, hμ⟩, rfl⟩
    obtain ⟨s, hs, hle⟩ := risk_le_of_distClass hn A b σ Δ x hμ
    have hs_le : Real.sqrt (∑ i, s i) ≤ regularizedLoss A b c x :=
      hLUB3.1 ⟨σ, Δ, hAdm, s, hs, rfl⟩
    exact hle.trans (ENNReal.ofReal_le_ofReal hs_le)
  · intro w hw
    by_cases hw_top : w = ⊤
    · rw [hw_top]
      exact le_top
    · have hw_ub : w.toReal ∈ upperBounds
          {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
            Admissible c σ Δ ∧ ∃ p : Fin n → Fin (m + 1) → ℝ,
              (∀ i, p i ∈ box A b σ Δ i) ∧ v = Real.sqrt (∑ i, sqLoss x (p i))} := by
        rintro y ⟨σ, Δ, hAdm, p, hp, rfl⟩
        obtain ⟨μ, hμ, hrisk⟩ := diracMixture_mem_distClass_and_risk hn A b σ Δ x p hp
        have hle : ENNReal.ofReal (Real.sqrt (∑ i, sqLoss x (p i))) ≤ w :=
          hw ⟨μ, ⟨σ, Δ, hAdm, hμ⟩, hrisk.symm⟩
        exact (ENNReal.ofReal_le_iff_le_toReal hw_top).mp hle
      have hR_le : regularizedLoss A b c x ≤ w.toReal := hLUB2.2 hw_ub
      rw [← ENNReal.ofReal_toReal hw_top]
      exact ENNReal.ofReal_le_ofReal hR_le
