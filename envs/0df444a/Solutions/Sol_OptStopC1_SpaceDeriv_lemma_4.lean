-- Prove2me | solution 1 for OptStopC1.SpaceDeriv.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:59:03.848243+00:00
-- url     : https://prove2.me/submissions/4d594e48-54d9-471f-aeec-b95f82f6f876

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

open OptStopC1.SpaceDeriv in
theorem solution
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (X : Flow d Ω)
    (hX : IsStandardMarkovFlow X P 𝔽)
    (D : Set (State d)) (hD : IsClosed D)
    (hcont : FlowContinuousAE X P) (ε : ℝ≥0) (hε : 0 < ε) :
    UpperSemicontinuous
      (fun x : State d => P {ω | (ε : ℝ≥0∞) ≤ hittingTime X x (interior D) ω}) := by
  set A := interior D with hAdef
  have hAo : IsOpen A := isOpen_interior
  -- a single null set outside which x ↦ X^x_q is continuous for every rational q
  have hgood : ∀ᵐ ω ∂P, ∀ q : ℚ, Continuous (fun x => X x (Real.toNNReal q) ω) :=
    ae_all_iff.2 fun q => hcont _
  -- pathwise upper semicontinuity of the hitting time, (3.7)
  have hpath : ∀ ω, (∀ q : ℚ, Continuous (fun x => X x (Real.toNNReal q) ω)) →
      ∀ x (s : ℝ≥0∞), hittingTime X x A ω < s →
        ∀ᶠ x' in 𝓝 x, hittingTime X x' A ω < s := by
    intro ω hω x s hs
    obtain ⟨_, ⟨t, ⟨ht0, htA⟩, rfl⟩, hts⟩ := sInf_lt_iff.1 hs
    obtain ⟨r, htr, hrs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hts
    have hrc := (hX.2.1 x ω).1 t
    have hev : ∀ᶠ t' in 𝓝[≥] t, X x t' ω ∈ A := hrc.eventually (hAo.mem_nhds htA)
    obtain ⟨u, hu, hIco⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
    have htr' : t < r := by simpa using htr
    have hu' : t < u := hu
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < min (u : ℝ) (r : ℝ) from
      lt_min (by exact_mod_cast hu') (by exact_mod_cast htr'))
    have hqpos : (0 : ℝ) < q := lt_of_le_of_lt t.2 hq1
    have hq'coe : ((Real.toNNReal q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hqpos.le
    have hq'mem : Real.toNNReal q ∈ Ico t u := by
      constructor
      · rw [← NNReal.coe_le_coe, hq'coe]; exact hq1.le
      · rw [← NNReal.coe_lt_coe, hq'coe]; exact lt_of_lt_of_le hq2 (min_le_left _ _)
    have hqr : Real.toNNReal q < r := by
      rw [← NNReal.coe_lt_coe, hq'coe]; exact lt_of_lt_of_le hq2 (min_le_right _ _)
    have hXq : X x (Real.toNNReal q) ω ∈ A := hIco hq'mem
    have hev2 : ∀ᶠ x' in 𝓝 x, X x' (Real.toNNReal q) ω ∈ A :=
      ((hω q).tendsto x).eventually (hAo.mem_nhds hXq)
    filter_upwards [hev2] with x' hx'
    have hle : hittingTime X x' A ω ≤ ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) :=
      sInf_le ⟨_, ⟨Real.toNNReal_pos.2 hqpos, hx'⟩, rfl⟩
    have hlt : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < s :=
      lt_trans (by exact_mod_cast hqr) hrs
    exact lt_of_le_of_lt hle hlt
  -- measurability of the events {σ ≥ ε}
  have hmeasA : ∀ x, MeasurableSet {ω | (ε : ℝ≥0∞) ≤ hittingTime X x A ω} := by
    intro x
    have hst := (hX.2.2.2.2.2.2.1 A (Or.inl hAo) x).2.1
    have hlt : MeasurableSet {ω | hittingTime X x A ω < ((ε : ℝ≥0) : WithTop ℝ≥0)} :=
      𝔽.le ε _ (hst.measurableSet_lt ε)
    have hset : {ω | (ε : ℝ≥0∞) ≤ hittingTime X x A ω} =
        {ω | hittingTime X x A ω < ((ε : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff]
      exact not_lt.symm
    rw [hset]
    exact hlt.compl
  -- Fatou's lemma for sets along sequences, (3.8)
  intro x y hy
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨xs, hxs, hge⟩ := exists_seq_forall_of_frequently hcon
  set B : ℕ → Set Ω := fun m => ⋃ n, ⋃ (_ : m ≤ n),
    {ω | (ε : ℝ≥0∞) ≤ hittingTime X (xs n) A ω} with hBdef
  have hBm : ∀ m, NullMeasurableSet (B m) P := fun m =>
    (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hmeasA (xs n)).nullMeasurableSet
  have hBanti : Antitone B := by
    intro m m' hmm' ω hω
    simp only [B, mem_iUnion] at hω ⊢
    obtain ⟨n, hn, h⟩ := hω
    exact ⟨n, le_trans hmm' hn, h⟩
  have hlim := tendsto_measure_iInter_atTop hBm hBanti ⟨0, measure_ne_top _ _⟩
  have hinter : P (⋂ m, B m) ≤ P {ω | (ε : ℝ≥0∞) ≤ hittingTime X x A ω} := by
    apply measure_mono_ae
    filter_upwards [hgood] with ω hω hωB
    by_contra hlt
    have hlt' : hittingTime X x A ω < ε := not_le.1 hlt
    have hev := hpath ω hω x ε hlt'
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually hev)
    have hωN := mem_iInter.1 hωB N
    simp only [B, mem_iUnion] at hωN
    obtain ⟨n, hn, hωn⟩ := hωN
    exact absurd hωn (not_le.2 (hN n hn))
  have hBge : ∀ m, y ≤ P (B m) := by
    intro m
    refine le_trans (not_lt.1 (hge m)) (measure_mono ?_)
    intro ω hω
    simp only [B, mem_iUnion]
    exact ⟨m, le_refl m, hω⟩
  have hyle : y ≤ P (⋂ m, B m) := ge_of_tendsto' hlim fun m => hBge m
  exact absurd (lt_of_le_of_lt (hyle.trans hinter) hy) (lt_irrefl _)
