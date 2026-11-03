-- Prove2me | solution 1 for StochLoadBal.Makespan.lemma_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:02:58.8629+00:00
-- url     : https://prove2.me/submissions/722f756f-9772-4966-9c26-5cbdebdaca82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model
import Theorems.Thm_StochLoadBal_Makespan_lemma_1
import Theorems.Thm_StochLoadBal_Makespan_lemma_4

open MeasureTheory ProbabilityTheory StochLoadBal.Makespan

lemma slb5_load_le_makespan {m n : ℕ} {Ω : Type} (X : Fin m → Fin n → Ω → ℝ)
    (σ : Fin n → Fin m) (i : Fin m) (ω : Ω) : load X σ i ω ≤ makespan X σ ω := by
  unfold makespan
  exact le_ciSup (f := fun i => load X σ i ω) (Set.finite_range _).bddAbove i

lemma slb5_makespan_integrable {m n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Fin m → Fin n → Ω → ℝ) (hmeas : ∀ i j, Measurable (X i j))
    (hnn : ∀ i j ω, 0 ≤ X i j ω) (hint : ∀ i j, Integrable (X i j) P)
    (σ : Fin n → Fin m) (hm : 1 ≤ m) : Integrable (makespan X σ) P := by
  have hne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hmeas' : Measurable (makespan X σ) := by
    unfold makespan load
    exact Measurable.iSup (fun i => Finset.measurable_sum _ (fun j _ => hmeas i j))
  refine Integrable.mono' (g := fun ω => ∑ i, ∑ j, X i j ω)
    (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j)))
    hmeas'.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
  have h0 : 0 ≤ makespan X σ ω :=
    le_trans (Finset.sum_nonneg (fun j _ => hnn _ j ω)) (slb5_load_le_makespan X σ ⟨0, hm⟩ ω)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  apply ciSup_le
  intro i
  unfold load
  calc ∑ j ∈ Finset.univ.filter (fun j => σ j = i), X i j ω ≤ ∑ j, X i j ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => hnn i j ω)
    _ ≤ ∑ i, ∑ j, X i j ω :=
        Finset.single_le_sum (f := fun i => ∑ j, X i j ω)
          (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j ω)) (Finset.mem_univ i)

lemma slb5_exc_meas : Measurable exc := by
  unfold exc
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_id
    measurable_const

lemma slb5_trunc_meas : Measurable trunc := by
  unfold trunc
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_id
    measurable_const

lemma slb5_effSize_zero {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) : effSize P k (fun _ => (0:ℝ)) = 0 := by
  unfold effSize
  split_ifs <;> simp

theorem solution :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (m n : ℕ), 1 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin m → Fin n → Ω → ℝ),
        (∀ i j, Measurable (X i j)) → (∀ i j ω, 0 ≤ X i j ω) →
        (∀ i j, Integrable (X i j) P) → iIndepFun (fun j ω i => X i j ω) P →
        ∀ σ : Fin n → Fin m, expMakespan P X σ ≤ c₀ →
          (∑ j, ∫ ω, exc (X (σ j) j ω) ∂P ≤ 2) ∧
          ∀ K : Finset (Fin m), K.Nonempty →
            ∑ i ∈ K, ∑ j ∈ Finset.univ.filter (fun j => σ j = i),
                effSize P K.card (fun ω => trunc (X i j ω)) ≤ 17 * (K.card : ℝ) := by
  obtain ⟨c₁, hc₁, h4⟩ := StochLoadBal.Makespan.lemma_4
  refine ⟨min (1/4) (c₁/2), lt_min (by norm_num) (by linarith), ?_⟩
  intro m n hm Ω _ P _ X hmeas hnn hint hind σ hσ
  have hc14 : expMakespan P X σ ≤ 1/4 := hσ.trans (min_le_left _ _)
  have hc1 : expMakespan P X σ ≤ c₁/2 := hσ.trans (min_le_right _ _)
  have hMint := slb5_makespan_integrable P X hmeas hnn hint σ hm
  refine ⟨?_, ?_⟩
  · -- inequality (3), via Lemma 1 with L = 1
    by_contra hgt
    push Not at hgt
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at hgt; linarith
    let Z : Fin n → Ω → ℝ := fun j ω => exc (X (σ j) j ω)
    have hZmeas : ∀ j, Measurable (Z j) := fun j => slb5_exc_meas.comp (hmeas _ _)
    have hZnn : ∀ j ω, 0 ≤ Z j ω := by
      intro j ω; simp only [Z, exc]; split_ifs <;> linarith [hnn (σ j) j ω]
    have hZle : ∀ j ω, Z j ω ≤ X (σ j) j ω := by
      intro j ω; simp only [Z, exc]; split_ifs <;> linarith [hnn (σ j) j ω]
    have hZint : ∀ j, Integrable (Z j) P := by
      intro j
      refine Integrable.mono' (hint (σ j) j) (hZmeas j).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (hZnn j ω)]
      exact hZle j ω
    have hZind : iIndepFun Z P :=
      hind.comp (fun j (v : Fin m → ℝ) => exc (v (σ j)))
        (fun j => slb5_exc_meas.comp (measurable_pi_apply _))
    have hval : ∀ j ω, Z j ω = 0 ∨ (1:ℝ) ≤ Z j ω := by
      intro j ω; simp only [Z, exc]; split_ifs with h
      · right; linarith
      · left; rfl
    have h1 := StochLoadBal.Makespan.lemma_1 P n hn 1 one_pos Z hZmeas hZint hZind hval
      (by linarith)
    have hmono : ∫ ω, (⨆ j, Z j ω) ∂P ≤ expMakespan P X σ := by
      unfold expMakespan
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => ?_)) hMint
        (Filter.Eventually.of_forall (fun ω => ?_))
      · exact le_ciSup_of_le (Set.finite_range _).bddAbove ⟨0, hn⟩ (hZnn _ ω)
      · have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        apply ciSup_le
        intro j
        refine (hZle j ω).trans (le_trans ?_ (slb5_load_le_makespan X σ (σ j) ω))
        unfold load
        exact Finset.single_le_sum (f := fun j' => X (σ j) j' ω)
          (fun j' _ => hnn _ j' ω) (by simp)
    linarith
  · -- inequality (4), via Lemma 4 on the machines of K
    intro K hK
    by_contra hgt
    push Not at hgt
    have hk : 1 ≤ K.card := Finset.card_pos.mpr hK
    let e : K ≃ Fin K.card := K.equivFin
    let Y : Fin n → Ω → ℝ := fun j ω => if σ j ∈ K then trunc (X (σ j) j ω) else 0
    let τ : Fin n → Fin K.card := fun j => if h : σ j ∈ K then e ⟨σ j, h⟩ else ⟨0, hk⟩
    have hYmeas : ∀ j, Measurable (Y j) := by
      intro j
      by_cases h : σ j ∈ K
      · simp only [Y, h, if_true]; exact slb5_trunc_meas.comp (hmeas _ _)
      · simp only [Y, h, if_false]; exact measurable_const
    have hYind : iIndepFun Y P := by
      refine hind.comp (fun j (v : Fin m → ℝ) => if σ j ∈ K then trunc (v (σ j)) else 0)
        (fun j => ?_)
      by_cases h : σ j ∈ K
      · simp only [h, if_true]; exact slb5_trunc_meas.comp (measurable_pi_apply _)
      · simp only [h, if_false]; exact measurable_const
    have htr : ∀ x : ℝ, 0 ≤ x → 0 ≤ trunc x ∧ trunc x ≤ 1 ∧ trunc x ≤ x := by
      intro x hx; unfold trunc; split_ifs with h
      · exact ⟨hx, h, le_rfl⟩
      · exact ⟨le_rfl, zero_le_one, hx⟩
    have hYbd : ∀ j ω, 0 ≤ Y j ω ∧ Y j ω ≤ 1 := by
      intro j ω
      by_cases h : σ j ∈ K
      · simp only [Y, h, if_true]; exact ⟨(htr _ (hnn _ _ _)).1, (htr _ (hnn _ _ _)).2.1⟩
      · simp only [Y, h, if_false]; norm_num
    have hsum : ∑ j, effSize P K.card (Y j) =
        ∑ i ∈ K, ∑ j ∈ Finset.univ.filter (fun j => σ j = i),
          effSize P K.card (fun ω => trunc (X i j ω)) := by
      have e1 : ∑ j, effSize P K.card (Y j) = ∑ j, (if σ j ∈ K then
          effSize P K.card (fun ω => trunc (X (σ j) j ω)) else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases h : σ j ∈ K
        · simp only [Y, h, if_true]
        · simp only [Y, h, if_false]; exact slb5_effSize_zero P _
      rw [e1]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_ite_eq]
    have hcY := h4 K.card n hk Ω P Y hYmeas hYind hYbd τ (by rw [hsum]; exact hgt.le)
    have hmono : expMakespan P (fun _ : Fin K.card => Y) τ ≤ expMakespan P X σ := by
      unfold expMakespan
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => ?_)) hMint
        (Filter.Eventually.of_forall (fun ω => ?_))
      · refine le_ciSup_of_le (Set.finite_range _).bddAbove ⟨0, hk⟩ ?_
        unfold load
        exact Finset.sum_nonneg (fun j _ => (hYbd j ω).1)
      · have hne : Nonempty (Fin K.card) := ⟨⟨0, hk⟩⟩
        apply ciSup_le
        intro r
        refine le_trans ?_ (slb5_load_le_makespan X σ (e.symm r : Fin m) ω)
        unfold load
        rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : σ j ∈ K
        · have hτ : τ j = e ⟨σ j, hj⟩ := dif_pos hj
          by_cases hr : τ j = r
          · have hs : σ j = (e.symm r : Fin m) := by
              rw [hτ] at hr
              rw [← hr, Equiv.symm_apply_apply]
            rw [if_pos hr, if_pos hs]
            simp only [Y, hj, if_true]
            rw [← hs]
            exact (htr _ (hnn _ _ _)).2.2
          · rw [if_neg hr]
            split_ifs
            · exact hnn _ _ _
            · exact le_rfl
        · have : Y j ω = 0 := by simp only [Y, hj, if_false]
          beta_reduce
          rw [this]
          split_ifs
          · exact hnn _ _ _
          · exact le_rfl
          · exact hnn _ _ _
          · exact le_rfl
    linarith
