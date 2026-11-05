-- Prove2me | solution 1 for OptStopC1.SpaceDeriv.corollary_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:00:08.820218+00:00
-- url     : https://prove2.me/submissions/61202b04-7327-4cfb-808b-676ca96c0bdb

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
    (z : State d) (hz : z ∈ frontier Dᶜ)
    (hPR : IsProbRegular X P (interior D) z)
    (hcont : FlowContinuousAE X P)
    (xs : ℕ → State d) (hxs : ∀ n, xs n ∈ Dᶜ)
    (hconv : Tendsto xs atTop (𝓝 z)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => entryTime X (xs n) (interior D) ω) atTop (𝓝 0) ∧
      Tendsto (fun n => entryTime X (xs n) D ω) atTop (𝓝 0) := by
  set A := interior D with hAdef
  have hAo : IsOpen A := isOpen_interior
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
  -- probabilistic regularity as an almost-sure statement
  have hmeas : MeasurableSet {ω | hittingTime X z A ω = 0} := by
    have hst := (hX.2.2.2.2.2.2.1 A (Or.inl hAo) z).2.1
    have h0 := 𝔽.le 0 _ (hst 0)
    have hset : {ω | hittingTime X z A ω = 0} =
        {ω | hittingTime X z A ω ≤ ((0 : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      simp
    rw [hset]
    exact h0
  have hreg : ∀ᵐ ω ∂P, hittingTime X z A ω = 0 := by
    rw [ae_iff]
    have hc : P {ω | hittingTime X z A ω = 0}ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hmeas]; exact hPR
    exact hc
  have hle : ∀ x (B : Set (State d)) ω, entryTime X x B ω ≤ hittingTime X x B ω := by
    intro x B ω
    apply sInf_le_sInf
    exact image_mono fun t ht => ht.2
  have hmono : ∀ x ω, entryTime X x D ω ≤ entryTime X x A ω := by
    intro x ω
    apply sInf_le_sInf
    exact image_mono fun t (ht : X x t ω ∈ interior D) => (interior_subset ht : X x t ω ∈ D)
  filter_upwards [hgood, hreg] with ω hω hω0
  -- σ^{x_n}_{D°} → 0
  have hsig : Tendsto (fun n => hittingTime X (xs n) A ω) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    have hev := hpath ω hω z δ (by rw [hω0]; exact hδ)
    filter_upwards [hconv.eventually hev] with n hn
    exact hn.le
  have h1 : Tendsto (fun n => entryTime X (xs n) A ω) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsig
      (fun n => zero_le) (fun n => hle (xs n) A ω)
  refine ⟨h1, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun n => zero_le) (fun n => hmono (xs n) ω)
