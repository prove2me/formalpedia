-- Prove2me | solution 1 for SpatialDemandEq.Optimal.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:48:17.63008+00:00
-- url     : https://prove2.me/submissions/22496319-94d5-46ab-a642-33cc531c32b9

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory Filter Topology
open SpatialDemandEq.Optimal

theorem solution {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (g : Fin K → E n → ℝ)
    (G : (Fin K → ℝ) → ℝ) (hset : GeneralSetting S ν g) (A : Fin K → Set (E n))
    (hopt : IsLocalOptPartition ν S G g A) (hG : DifferentiableAt ℝ G (areas ν A)) :
    ∀ k, ∀ᵐ x ∂ν, x ∈ A k → ∀ j, j ≠ k →
      g k x + fderiv ℝ G (areas ν A) (Pi.single k (1 : ℝ)) ≤
        g j x + fderiv ℝ G (areas ν A) (Pi.single j (1 : ℝ)) := by
  have hprob := hset.prob
  obtain ⟨hApart, ε, hε, hloc⟩ := hopt
  obtain ⟨hAm, hAS, hAU, hAN⟩ := hApart
  set a := areas ν A with ha_def
  set G' := fderiv ℝ G a with hG'_def
  set D : Fin K → ℝ := fun i => G' (Pi.single i 1) with hD_def
  intro k
  suffices H : ∀ j, j ≠ k → ν (A k ∩ {x | g j x + D j < g k x + D k}) = 0 by
    have h1 : ∀ j, ∀ᵐ x ∂ν, j ≠ k → x ∈ A k → g k x + D k ≤ g j x + D j := by
      intro j
      by_cases hjk : j = k
      · exact ae_of_all _ fun x h => absurd hjk h
      · have h0 := measure_eq_zero_iff_ae_notMem.mp (H j hjk)
        filter_upwards [h0] with x hx
        intro _ hxA
        by_contra hlt
        push_neg at hlt
        exact hx ⟨hxA, hlt⟩
    filter_upwards [ae_all_iff.mpr h1] with x hx
    intro hxA j hjk
    exact hx j hjk hxA
  intro j hjk
  by_contra hTpos
  have hcont : ∀ i, Continuous (g i) := hset.cont
  -- a level `δ` with a positive-measure piece
  set T : ℕ → Set (E n) := fun m =>
    A k ∩ {x | g j x + D j + 1 / ((m : ℝ) + 1) ≤ g k x + D k} with hT_def
  have hTsub : A k ∩ {x | g j x + D j < g k x + D k} ⊆ ⋃ m, T m := by
    rintro x ⟨hxA, hx⟩
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
    refine Set.mem_iUnion.mpr ⟨m, hxA, ?_⟩
    simp only [Set.mem_setOf_eq]
    linarith
  obtain ⟨m, hm⟩ : ∃ m, ν (T m) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hTpos (measure_mono_null hTsub (measure_iUnion_null hall))
  set δ : ℝ := 1 / ((m : ℝ) + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  set T' := T m with hT'_def
  have hT'm : MeasurableSet T' :=
    (hAm k).inter (measurableSet_le (((hcont j).add continuous_const).add
      continuous_const).measurable ((hcont k).add continuous_const).measurable)
  have hT'A : T' ⊆ A k := Set.inter_subset_left
  -- derivative estimate
  set v : Fin K → ℝ := Pi.single j 1 - Pi.single k 1 with hv_def
  set C : ℝ := ‖v‖ with hC_def
  have hC : 0 ≤ C := norm_nonneg _
  set η : ℝ := δ / (2 * (C + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hlo := hG.hasFDerivAt.isLittleO.def hη
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.mp hlo
  set ρ' : ℝ := min ε (ρ / (C + 1)) with hρ'_def
  have hρ' : 0 < ρ' := lt_min hε (by positivity)
  -- a small piece `P ⊆ T'` of positive measure
  obtain ⟨P, hPm, hPT, hPpos, hPsmall⟩ : ∃ P : Set (E n), MeasurableSet P ∧ P ⊆ T' ∧
      0 < ν P ∧ ν P < ENNReal.ofReal ρ' := by
    have hμr : ν.restrict T' ≠ 0 := by
      intro h0
      apply hm
      have := congrArg (fun μ : Measure (E n) => μ Set.univ) h0
      simpa [Measure.restrict_apply_univ] using this
    obtain ⟨x0, hx0⟩ := Measure.nonempty_support hμr
    have hballpos : ∀ r : ℝ, 0 < r → 0 < ν (T' ∩ Metric.ball x0 r) := by
      intro r hr
      have := (Measure.mem_support_iff_forall x0).mp hx0 (Metric.ball x0 r)
        (Metric.ball_mem_nhds x0 hr)
      rwa [Measure.restrict_apply Metric.isOpen_ball.measurableSet, Set.inter_comm] at this
    have hatom : ν {x0} = 0 := by
      set h : E n → ℝ := fun x => g j x - g k x
      have hhm : Measurable h := ((hcont j).sub (hcont k)).measurable
      apply measure_mono_null (show ({x0} : Set (E n)) ⊆ h ⁻¹' {h x0} by
        intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; rfl)
      rw [← Measure.map_apply hhm (measurableSet_singleton _)]
      exact hset.regular j k hjk Real.volume_singleton
    set s : ℕ → Set (E n) := fun N => T' ∩ Metric.ball x0 (1 / ((N : ℝ) + 1)) with hs_def
    have hanti : Antitone s := by
      intro N M hNM
      apply Set.inter_subset_inter_right
      apply Metric.ball_subset_ball
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ M := by exact_mod_cast hNM
      linarith
    have hlim := tendsto_measure_iInter_atTop (μ := ν)
      (fun N => (hT'm.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have hinter : ν (⋂ N, s N) = 0 := by
      apply measure_mono_null _ hatom
      intro y hy
      rw [Set.mem_iInter] at hy
      rw [Set.mem_singleton_iff]
      by_contra hne
      have hd : 0 < dist y x0 := dist_pos.mpr hne
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hd
      have := (hy N).2
      rw [Metric.mem_ball] at this
      linarith
    rw [hinter] at hlim
    obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hρ'))).exists
    exact ⟨s N, hT'm.inter Metric.isOpen_ball.measurableSet, Set.inter_subset_left,
      hballpos _ (by positivity), hN⟩
  have hPA : P ⊆ A k := hPT.trans hT'A
  set sP : ℝ := (ν P).toReal with hsP_def
  have hsPpos : 0 < sP := ENNReal.toReal_pos hPpos.ne' (measure_ne_top _ _)
  have hsPlt : sP < ρ' := ENNReal.toReal_lt_of_lt_ofReal hPsmall
  -- the modified partition: move `P` from `A k` to `A j`
  set A' : Fin K → Set (E n) := fun i =>
    if i = j then A j ∪ P else if i = k then A k \ P else A i with hA'_def
  have hA'j : A' j = A j ∪ P := by simp [A']
  have hA'k : A' k = A k \ P := by simp [A', Ne.symm hjk]
  have hA'o : ∀ i, i ≠ j → i ≠ k → A' i = A i := by
    intro i hij hik; simp [A', hij, hik]
  have hsub1 : ∀ i, A' i ⊆ A i ∪ P := by
    intro i
    by_cases hij : i = j
    · subst hij; rw [hA'j]
    · by_cases hik : i = k
      · subst hik; rw [hA'k]; exact Set.diff_subset.trans Set.subset_union_left
      · rw [hA'o i hij hik]; exact Set.subset_union_left
  have hsub2 : ∀ i, A i ⊆ A' i ∪ P := by
    intro i x hx
    by_cases hxP : x ∈ P
    · exact Or.inr hxP
    · left
      by_cases hij : i = j
      · subst hij; rw [hA'j]; exact Or.inl hx
      · by_cases hik : i = k
        · subst hik; rw [hA'k]; exact ⟨hx, hxP⟩
        · rw [hA'o i hij hik]; exact hx
  have hPi : ∀ i, i ≠ j → ν (P ∩ A' i) = 0 := by
    intro i hij
    by_cases hik : i = k
    · subst hik; rw [hA'k]
      have : P ∩ (A i \ P) = ∅ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false,
          iff_false, not_and, not_not]; intro h1 _; exact h1
      rw [this, measure_empty]
    · rw [hA'o i hij hik]
      exact measure_mono_null (Set.inter_subset_inter_left _ hPA) (hAN k i (Ne.symm hik))
  have hA'm : ∀ i, MeasurableSet (A' i) := by
    intro i
    by_cases hij : i = j
    · subst hij; rw [hA'j]; exact (hAm i).union hPm
    · by_cases hik : i = k
      · subst hik; rw [hA'k]; exact (hAm i).diff hPm
      · rw [hA'o i hij hik]; exact hAm i
  have hPS : P ⊆ S := hPA.trans (hAS k)
  have hA'part : IsPartition ν S A' := by
    refine ⟨hA'm, fun i => (hsub1 i).trans (Set.union_subset (hAS i) hPS), ?_, ?_⟩
    · apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun i => (hsub1 i).trans (Set.union_subset (hAS i) hPS)
      · intro x hx
        rw [← hAU] at hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        rcases hsub2 i hi with h | h
        · exact Set.mem_iUnion.mpr ⟨i, h⟩
        · exact Set.mem_iUnion.mpr ⟨j, by rw [hA'j]; exact Or.inr h⟩
    · intro i l hil
      by_cases hij : i = j
      · have hlj : l ≠ j := fun h => hil (hij.trans h.symm)
        apply measure_mono_null (t := (A i ∩ A l) ∪ (P ∩ A' l))
        · rintro x ⟨hxi, hxl⟩
          by_cases hxP : x ∈ P
          · exact Or.inr ⟨hxP, hxl⟩
          · left
            exact ⟨((hsub1 i) hxi).resolve_right hxP, ((hsub1 l) hxl).resolve_right hxP⟩
        · exact measure_union_null (hAN i l hil) (hPi l hlj)
      · apply measure_mono_null (t := (A i ∩ A l) ∪ (P ∩ A' i))
        · rintro x ⟨hxi, hxl⟩
          by_cases hxP : x ∈ P
          · exact Or.inr ⟨hxP, hxi⟩
          · left
            exact ⟨((hsub1 i) hxi).resolve_right hxP, ((hsub1 l) hxl).resolve_right hxP⟩
        · exact measure_union_null (hAN i l hil) (hPi i hij)
  have hsd : ∀ i, ν (symmDiff (A' i) (A i)) < ENNReal.ofReal ε := by
    intro i
    have hsub : symmDiff (A' i) (A i) ⊆ P := by
      intro x hx
      rcases Set.mem_symmDiff.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ((hsub1 i) h1).resolve_left h2
      · exact ((hsub2 i) h1).resolve_left h2
    calc ν (symmDiff (A' i) (A i)) ≤ ν P := measure_mono hsub
      _ < ENNReal.ofReal ρ' := hPsmall
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hle := hloc A' hA'part hsd
  -- areas of the modified partition
  have hAjP : ν (A j ∩ P) = 0 :=
    measure_mono_null (Set.inter_subset_inter_right _ hPA) (hAN j k hjk)
  have hareaj : area ν (A j ∪ P) = a j + sP := by
    have h := measure_union_add_inter (μ := ν) (A j) hPm
    rw [hAjP, add_zero] at h
    simp only [area]
    rw [h, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rfl
  have hareak : area ν (A k \ P) = a k - sP := by
    simp only [area]
    rw [measure_sdiff hPA hPm.nullMeasurableSet (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono hPA) (measure_ne_top _ _)]
    rfl
  have hb : areas ν A' = a + sP • v := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, v, Pi.sub_apply]
    by_cases hij : i = j
    · subst hij
      show area ν (A' i) = _
      rw [hA'j, hareaj, Pi.single_eq_same, Pi.single_eq_of_ne hjk]; ring
    · by_cases hik : i = k
      · subst hik
        show area ν (A' i) = _
        rw [hA'k, hareak, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjk)]; ring
      · show area ν (A' i) = _
        rw [hA'o i hij hik, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]
        simp [a, areas]
  -- linear cost of the modified partition
  have hint : ∀ i, Integrable (g i) ν := hset.integrable
  have hlin : linCost ν g A' = linCost ν g A + ((∫ x in P, g j x ∂ν) - ∫ x in P, g k x ∂ν) := by
    have hterm : ∀ i, ∫ x in A' i, g i x ∂ν = ∫ x in A i, g i x ∂ν +
        ((if i = j then ∫ x in P, g j x ∂ν else 0) - (if i = k then ∫ x in P, g k x ∂ν else 0)) := by
      intro i
      by_cases hij : i = j
      · subst hij
        rw [hA'j, if_pos rfl, if_neg hjk, setIntegral_union₀ hAjP hPm.nullMeasurableSet
          (hint i).integrableOn (hint i).integrableOn]
        ring
      · by_cases hik : i = k
        · subst hik
          rw [hA'k, if_neg hij, if_pos rfl, setIntegral_sdiff hPm (hint i).integrableOn hPA]
          ring
        · rw [hA'o i hij hik, if_neg hij, if_neg hik]; ring
    unfold linCost
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hPint : (∫ x in P, g j x ∂ν) - ∫ x in P, g k x ∂ν ≤ sP * (D k - D j - δ) := by
    rw [← integral_sub (hint j).integrableOn (hint k).integrableOn]
    have h1 : ∫ x in P, (g j x - g k x) ∂ν ≤ ∫ x in P, (D k - D j - δ) ∂ν := by
      apply setIntegral_mono_on (((hint j).sub (hint k)).integrableOn)
        (integrable_const _).integrableOn hPm
      intro x hx
      have := (hPT hx).2
      simp only [Set.mem_setOf_eq] at this
      have hδe : δ = 1 / ((m : ℝ) + 1) := rfl
      simp only [Pi.sub_apply]
      linarith
    rw [setIntegral_const, smul_eq_mul] at h1
    exact h1
  -- the derivative estimate at `b = a + sP • v`
  have hdist : dist (a + sP • v) a < ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hsPpos]
    have h1 : sP < ρ / (C + 1) := lt_of_lt_of_le hsPlt (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hest := hρball hdist
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hsPpos.le] at hest
  have hG'v : G' (sP • v) = sP * (D j - D k) := by
    simp only [v, map_smul, map_sub, smul_eq_mul, D]
  rw [hG'v] at hest
  have hest' : G (a + sP • v) - G a ≤ sP * (D j - D k) + η * (sP * C) := by
    have h2 := le_trans (Real.le_norm_self _) hest
    linarith
  -- combine
  unfold partitionObj at hle
  rw [hb, hlin] at hle
  have hηC : η * C < δ := by
    rw [hη_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have : 0 ≤ sP * (η * C - δ) := by nlinarith
  have : sP * (η * C - δ) < 0 := mul_neg_of_pos_of_neg hsPpos (by linarith)
  linarith
