-- Prove2me | solution 1 for SamuelCahnProphet.IID.upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:06:06.101211+00:00
-- url     : https://prove2.me/submissions/f4c3d5c6-223d-4772-bb0a-eea624a5e0bc

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting
import Theorems.Thm_SamuelCahnProphet_Median_theorem_1

open MeasureTheory Filter Topology

lemma scp2_exists_median {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hnn : ∀ᵐ ω ∂P, 0 ≤ Y ω) :
    ∃ m : ℝ, 0 ≤ m ∧ P {ω | Y ω < m} ≤ (1 / 2 : ENNReal) ∧ P {ω | m < Y ω} ≤ (1 / 2 : ENNReal) := by
  set S : Set ℝ := {t | (1 / 2 : ENNReal) ≤ P {ω | Y ω ≤ t}} with hS
  have hmeasLe : ∀ t : ℝ, MeasurableSet {ω | Y ω ≤ t} := fun t => measurableSet_le hY measurable_const
  -- upward closed
  have hup : ∀ s t, s ≤ t → s ∈ S → t ∈ S := by
    intro s t hst hs
    exact le_trans hs (measure_mono fun ω (h : Y ω ≤ s) => (show Y ω ≤ t from h.trans hst))
  -- negative numbers are not in S
  have hneg : ∀ t, t < 0 → t ∉ S := by
    intro t ht hmem
    have h0 : P {ω | Y ω ≤ t} = 0 := by
      apply measure_mono_null (t := {ω | ¬ (0 ≤ Y ω)})
      · intro ω (h : Y ω ≤ t); simp only [Set.mem_ofPred_eq, not_le]; linarith
      · exact ae_iff.1 hnn
    rw [Set.mem_ofPred_eq, h0] at hmem
    norm_num at hmem
  have hlb : ∀ s ∈ S, 0 ≤ s := fun s hs => by
    by_contra h; exact hneg s (lt_of_not_ge h) hs
  -- S is nonempty
  have hne : S.Nonempty := by
    have hmono : Monotone (fun k : ℕ => {ω | Y ω ≤ (k : ℝ)}) := by
      intro i j hij ω (h : Y ω ≤ i); exact (show Y ω ≤ j from h.trans (by exact_mod_cast hij))
    have hU : (⋃ k : ℕ, {ω | Y ω ≤ (k : ℝ)}) = Set.univ := by
      ext ω; simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      obtain ⟨k, hk⟩ := exists_nat_ge (Y ω); exact ⟨k, hk⟩
    have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
    rw [hU, measure_univ] at ht
    have : ∀ᶠ k : ℕ in atTop, (1 / 2 : ENNReal) < P {ω | Y ω ≤ (k : ℝ)} :=
      ht.eventually (lt_mem_nhds (by norm_num))
    obtain ⟨k, hk⟩ := this.exists
    exact ⟨k, hk.le⟩
  have hbdd : BddBelow S := ⟨0, fun s hs => hlb s hs⟩
  set m := sInf S
  have hm0 : 0 ≤ m := le_csInf hne hlb
  refine ⟨m, hm0, ?_, ?_⟩
  · -- P{Y < m} ≤ 1/2
    have hU : {ω | Y ω < m} = ⋃ k : ℕ, {ω | Y ω ≤ m - 1 / ((k : ℝ) + 1)} := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    have hmono : Monotone (fun k : ℕ => {ω | Y ω ≤ m - 1 / ((k : ℝ) + 1)}) := by
      intro i j hij ω (h : Y ω ≤ m - 1 / ((i : ℝ) + 1))
      show Y ω ≤ m - 1 / ((j : ℝ) + 1)
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity); exact_mod_cast (by omega : i + 1 ≤ j + 1)
      linarith
    rw [hU, hmono.measure_iUnion]
    refine iSup_le fun k => ?_
    have hnot : m - 1 / ((k : ℝ) + 1) ∉ S := by
      intro hmem
      have := csInf_le hbdd hmem
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    simp only [hS, Set.mem_ofPred_eq, not_le] at hnot
    exact hnot.le
  · -- P{Y > m} ≤ 1/2
    have hle : (1 / 2 : ENNReal) ≤ P {ω | Y ω ≤ m} := by
      have hI : {ω | Y ω ≤ m} = ⋂ k : ℕ, {ω | Y ω ≤ m + 1 / ((k : ℝ) + 1)} := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
        constructor
        · intro h k; have : 0 < 1 / ((k : ℝ) + 1) := by positivity
          linarith
        · intro h
          by_contra hc
          push Not at hc
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
          have := h k; linarith
      have hanti : Antitone (fun k : ℕ => {ω | Y ω ≤ m + 1 / ((k : ℝ) + 1)}) := by
        intro i j hij ω (h : Y ω ≤ m + 1 / ((j : ℝ) + 1))
        show Y ω ≤ m + 1 / ((i : ℝ) + 1)
        have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity); exact_mod_cast (by omega : i + 1 ≤ j + 1)
        linarith
      rw [hI, hanti.measure_iInter (fun k => (hmeasLe _).nullMeasurableSet)
        ⟨0, measure_ne_top _ _⟩]
      refine le_iInf fun k => ?_
      have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hne (show sInf S < m + 1 / ((k : ℝ) + 1) by linarith)
      exact hup s _ hslt.le hs
    have hc : {ω | m < Y ω} = {ω | Y ω ≤ m}ᶜ := by
      ext ω; simp
    rw [hc, prob_compl_eq_one_sub (hmeasLe m)]
    calc 1 - P {ω | Y ω ≤ m} ≤ 1 - 1 / 2 := tsub_le_tsub_left hle 1
      _ = 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]

theorem solution (n : ℕ) [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) :
    SamuelCahnProphet.IID.Emax μ n ≤ 2 * SamuelCahnProphet.IID.supEplus μ n := by
  classical
  set P : Measure (Fin n → ℝ) := SamuelCahnProphet.IID.iidLaw μ n with hP
  have : IsProbabilityMeasure P := by
    rw [hP]; unfold SamuelCahnProphet.IID.iidLaw; infer_instance
  set X : Fin n → (Fin n → ℝ) → ℝ := fun i x => x i with hX
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hμnn : ∀ᵐ y ∂μ, 0 ≤ y := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [this]; exact hμ
  have hXnn : ∀ i, ∀ᵐ x ∂P, 0 ≤ X i x := fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => μ) (i := i)).eventually hμnn
  have hind : ProbabilityTheory.iIndepFun X P := by
    have := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin n => μ)
      (X := fun _ (y : ℝ) => y) (fun _ => measurable_id.aemeasurable)
    exact this
  have hYm : Measurable (SamuelCahnProphet.Median.maxX X) := by
    have : SamuelCahnProphet.Median.maxX X = Finset.univ.sup' Finset.univ_nonempty X := by
      funext x; simp [SamuelCahnProphet.Median.maxX, Finset.sup'_apply]
    rw [this]; exact Finset.measurable_sup' _ (fun i _ => hXm i)
  have hYnn : ∀ᵐ x ∂P, 0 ≤ SamuelCahnProphet.Median.maxX X x := by
    have h0 := hXnn ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    filter_upwards [h0] with x hx
    exact le_trans hx (Finset.le_sup' (fun i => X i x) (Finset.mem_univ _))
  obtain ⟨m, hm0, hm1, hm2⟩ := scp2_exists_median P _ hYm hYnn
  have hmed : SamuelCahnProphet.Median.IsMedian P (SamuelCahnProphet.Median.maxX X) m := ⟨hm1, hm2⟩
  have hthm := SamuelCahnProphet.Median.theorem_1 P X hXm hXnn hind m hmed
  have hEmax : SamuelCahnProphet.IID.Emax μ n =
      ∫⁻ ω, ENNReal.ofReal (SamuelCahnProphet.Median.maxX X ω) ∂P := rfl
  have hT : SamuelCahnProphet.Median.EplusT P X m = SamuelCahnProphet.IID.EplusT μ n m := rfl
  have hS : SamuelCahnProphet.Median.EplusS P X m = SamuelCahnProphet.IID.EplusS μ n m := rfl
  have hTle : SamuelCahnProphet.IID.EplusT μ n m ≤ SamuelCahnProphet.IID.supEplus μ n :=
    le_trans (le_max_left _ _) (le_iSup₂_of_le (f := fun (c : ℝ) (_ : 0 ≤ c) =>
      max (SamuelCahnProphet.IID.EplusT μ n c) (SamuelCahnProphet.IID.EplusS μ n c)) m hm0 le_rfl)
  have hSle : SamuelCahnProphet.IID.EplusS μ n m ≤ SamuelCahnProphet.IID.supEplus μ n :=
    le_trans (le_max_right _ _) (le_iSup₂_of_le (f := fun (c : ℝ) (_ : 0 ≤ c) =>
      max (SamuelCahnProphet.IID.EplusT μ n c) (SamuelCahnProphet.IID.EplusS μ n c)) m hm0 le_rfl)
  rw [hEmax]
  rcases le_total (ENNReal.ofReal m) (SamuelCahnProphet.Median.beta P X m) with h | h
  · have := (hthm.1 h).1
    rw [hS] at this
    exact this.trans (by gcongr)
  · have := (hthm.2 h).1
    rw [hT] at this
    exact this.trans (by gcongr)
