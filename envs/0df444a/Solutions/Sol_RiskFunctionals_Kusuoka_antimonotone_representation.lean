-- Prove2me | solution 1 for RiskFunctionals.Kusuoka.antimonotone_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:29:20.853978+00:00
-- url     : https://prove2.me/submissions/224e97c2-9b49-4528-82ed-82b7725827af

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
set_option linter.unusedSimpArgs false
open MeasureTheory

namespace KA83

noncomputable def g79q_F (μ : Measure ℝ) (u : ℝ) : ℝ := μ.real (Set.Iic u)

noncomputable def g79q_q (μ : Measure ℝ) (p : ℝ) : ℝ := sInf {u : ℝ | p ≤ g79q_F μ u}

theorem g79q_cdf_eq_real (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    ProbabilityTheory.cdf μ v = g79q_F μ v := ProbabilityTheory.cdf_eq_real μ v

theorem g79q_qle (μ : Measure ℝ) [IsProbabilityMeasure μ] (p u : ℝ)
    (hp : 0 < p) (hfin : ∃ v : ℝ, p ≤ g79q_F μ v) :
    g79q_q μ p ≤ u ↔ p ≤ g79q_F μ u := by
  have hF : ∀ v, g79q_F μ v = ProbabilityTheory.cdf μ v := fun v =>
    (g79q_cdf_eq_real μ v).symm
  set S := {u : ℝ | p ≤ g79q_F μ u} with hS
  have hne : S.Nonempty := hfin
  have hbdd : BddBelow S := by
    have h := (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (gt_mem_nhds hp)
    obtain ⟨L, hL⟩ := Filter.eventually_atBot.1 h
    refine ⟨L, fun v hv => ?_⟩
    by_contra hlt
    have := hL v (le_of_lt (lt_of_not_ge hlt))
    have hv' : p ≤ g79q_F μ v := hv
    rw [hF] at hv'
    linarith
  have hmono : Monotone (g79q_F μ) := fun a b hab => by
    rw [hF, hF]; exact (ProbabilityTheory.cdf μ).mono hab
  constructor
  · intro hq
    have hQ : p ≤ g79q_F μ (g79q_q μ p) := by
      have hev : ∀ᶠ v in nhdsWithin (g79q_q μ p) (Set.Ioi (g79q_q μ p)),
          p ≤ ProbabilityTheory.cdf μ v := by
        filter_upwards [self_mem_nhdsWithin] with v hv
        obtain ⟨w, hwS, hwv⟩ := exists_lt_of_csInf_lt hne hv
        have : p ≤ g79q_F μ w := hwS
        rw [← hF]; exact this.trans (hmono hwv.le)
      have ht : Filter.Tendsto (ProbabilityTheory.cdf μ)
          (nhdsWithin (g79q_q μ p) (Set.Ioi (g79q_q μ p)))
          (nhds (ProbabilityTheory.cdf μ (g79q_q μ p))) :=
        ((ProbabilityTheory.cdf μ).right_continuous _).tendsto.mono_left
          (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      rw [hF]
      exact ge_of_tendsto ht hev
    exact hQ.trans (hmono hq)
  · intro hu
    exact csInf_le hbdd hu

theorem g79q_q_nonpos (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : p ≤ 0) :
    g79q_q μ p = 0 := by
  unfold g79q_q
  have : {u : ℝ | p ≤ g79q_F μ u} = Set.univ := by
    ext u
    simp only [Set.mem_univ, iff_true]
    refine le_trans hp ?_
    unfold g79q_F; exact measureReal_nonneg
  rw [this]
  exact Real.sInf_of_not_bddBelow not_bddBelow_univ

theorem g79q_q_nowit (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ)
    (h : ¬ ∃ v, p ≤ g79q_F μ v) : g79q_q μ p = 0 := by
  unfold g79q_q
  have : {u : ℝ | p ≤ g79q_F μ u} = ∅ := by
    ext u; simp only [Set.mem_empty_iff_false, iff_false]; exact fun hu => h ⟨u, hu⟩
  rw [this, Real.sInf_empty]

theorem g79q_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] : Monotone (g79q_F μ) := by
  intro a b hab
  unfold g79q_F
  exact measureReal_mono (Set.Iic_subset_Iic.2 hab)

theorem g79q_meas (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (g79q_q μ) := by
  set A : Set ℝ := Set.Ioi 0 ∩ ⋃ n : ℕ, Set.Iic (g79q_F μ n) with hA
  have hAm : MeasurableSet A :=
    measurableSet_Ioi.inter (MeasurableSet.iUnion (fun _ => measurableSet_Iic))
  have hAiff : ∀ p, p ∈ A ↔ 0 < p ∧ ∃ v, p ≤ g79q_F μ v := by
    intro p
    simp only [hA, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · rintro ⟨h0, n, hn⟩; exact ⟨h0, n, hn⟩
    · rintro ⟨h0, v, hv⟩
      obtain ⟨n, hn⟩ := exists_nat_ge v
      exact ⟨h0, n, hv.trans (g79q_mono μ hn)⟩
  refine measurable_of_Iic (fun x => ?_)
  have : g79q_q μ ⁻¹' Set.Iic x =
      (A ∩ Set.Iic (g79q_F μ x)) ∪ (Aᶜ ∩ {_p | 0 ≤ x}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq]
    by_cases hp : p ∈ A
    · have := (hAiff p).1 hp
      rw [g79q_qle μ p x this.1 this.2]
      simp [hp]
    · have h0 : g79q_q μ p = 0 := by
        by_cases hp0 : p ≤ 0
        · exact g79q_q_nonpos μ p hp0
        · exact g79q_q_nowit μ p (fun hw => hp ((hAiff p).2 ⟨lt_of_not_ge hp0, hw⟩))
      simp [hp, h0]
  rw [this]
  exact (hAm.inter measurableSet_Iic).union (hAm.compl.inter (MeasurableSet.const _))

theorem g79q_transform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U) (hunif : P.map U = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    P.map (fun ω => g79q_q μ (U ω)) = μ := by
  have hf := g79q_meas μ
  have hcomp : P.map (fun ω => g79q_q μ (U ω)) =
      (P.map U).map (g79q_q μ) := by
    rw [Measure.map_map hf hU]; rfl
  rw [hcomp, hunif]
  have hrestr : (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  rw [hrestr]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    constructor; rw [Measure.restrict_apply_univ]; simp
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply hf measurableSet_Iic,
    Measure.restrict_apply (hf measurableSet_Iic)]
  set g := g79q_F μ x with hg
  have hset : g79q_q μ ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 = Set.Iic g ∩ Set.Ioo 0 1 := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h0, h1'⟩
      refine ⟨?_, h0, h1'⟩
      have hw : ∃ v, p ≤ g79q_F μ v := by
        have hlim : Filter.Tendsto (g79q_F μ) Filter.atTop (nhds 1) := by
          have := ProbabilityTheory.tendsto_cdf_atTop μ
          refine this.congr (fun v => ?_)
          exact g79q_cdf_eq_real μ v
        obtain ⟨v, hv⟩ := (hlim.eventually (lt_mem_nhds h1')).exists
        exact ⟨v, hv.le⟩
      exact (g79q_qle μ p x h0 hw).1 h1
    · rintro ⟨h1, h0, h1'⟩
      exact ⟨(g79q_qle μ p x h0 ⟨x, h1⟩).2 h1, h0, h1'⟩
  rw [hset]
  have hg0 : 0 ≤ g := measureReal_nonneg
  have hg1 : g ≤ 1 := by
    rw [hg]; unfold g79q_F; exact measureReal_le_one
  have hμx : μ (Set.Iic x) = ENNReal.ofReal g := by
    rw [hg]; unfold g79q_F
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hμx]
  apply le_antisymm
  · calc volume (Set.Iic g ∩ Set.Ioo 0 1) ≤ volume (Set.Ioc 0 g) := by
          apply measure_mono
          rintro p ⟨h1, h0, -⟩; exact ⟨h0, h1⟩
      _ = ENNReal.ofReal g := by simp
  · calc ENNReal.ofReal g = volume (Set.Ioo 0 g) := by simp
      _ ≤ volume (Set.Iic g ∩ Set.Ioo 0 1) := by
          apply measure_mono
          rintro p ⟨h0, h1⟩; exact ⟨h1.le, h0, lt_of_lt_of_le h1 hg1⟩

theorem g79q_wit (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : p < 1) :
    ∃ v, p ≤ g79q_F μ v := by
  have hlim : Filter.Tendsto (g79q_F μ) Filter.atTop (nhds 1) :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).congr (fun v => g79q_cdf_eq_real μ v)
  obtain ⟨v, hv⟩ := (hlim.eventually (lt_mem_nhds hp)).exists
  exact ⟨v, hv.le⟩

theorem g79q_qle' (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (u : ℝ) :
    g79q_q μ p ≤ u ↔ p ≤ g79q_F μ u := g79q_qle μ p u hp0 (g79q_wit μ hp1)


open MeasureTheory ProbabilityTheory Set Filter Topology


theorem cr_qint (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ) :
    IntegrableOn (g79q_q μ) (Ioc 0 1) := by
  have hP : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have htr' : (volume.restrict (Set.Icc (0 : ℝ) 1)).map (g79q_q μ) = μ :=
    g79q_transform μ (volume.restrict (Set.Icc (0 : ℝ) 1)) id measurable_id Measure.map_id
  have hmeas := g79q_meas μ
  rw [← htr'] at hμ
  have := (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).1 hμ
  exact (show IntegrableOn (g79q_q μ) (Icc 0 1) volume from this).mono_set Ioc_subset_Icc_self

theorem cr_qmono (μ : Measure ℝ) [IsProbabilityMeasure μ] : MonotoneOn (g79q_q μ) (Ioo 0 1) := by
  intro p hp p' hp' hpp
  rw [g79q_qle' μ hp.1 hp.2]
  have := (g79q_qle' μ hp'.1 hp'.2 (g79q_q μ p')).1 le_rfl
  linarith

end KA83


open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace KA83

variable {Q : Type*} [MeasurableSpace Q] (ρ : Measure Q) [IsProbabilityMeasure ρ]

/-- double layer cake for a product of two nonnegative parts -/
theorem lay (A B : ℝ → Set Q) (f g : Q → ℝ) (hg : Measurable g)
    (hA : ∀ ω, ENNReal.ofReal (f ω) = volume ({s | ω ∈ A s} ∩ Ioi 0))
    (hB : ∀ ω, ENNReal.ofReal (g ω) = volume ({s | ω ∈ B s} ∩ Ioi 0))
    (hAm : MeasurableSet {p : ℝ × Q | p.2 ∈ A p.1})
    (hBm : MeasurableSet {p : ℝ × Q | p.2 ∈ B p.1}) :
    ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω) ∂ρ =
      ∫⁻ s in Ioi 0, ∫⁻ t in Ioi 0, ρ (A s ∩ B t) := by
  set IA : ℝ × Q → ℝ≥0∞ := {p : ℝ × Q | p.2 ∈ A p.1}.indicator 1 with hIA
  set IB : ℝ × Q → ℝ≥0∞ := {p : ℝ × Q | p.2 ∈ B p.1}.indicator 1 with hIB
  have mIA : Measurable IA := measurable_one.indicator hAm
  have mIB : Measurable IB := measurable_one.indicator hBm
  have hsec : ∀ (C : ℝ → Set Q) (hC : MeasurableSet {p : ℝ × Q | p.2 ∈ C p.1}) (ω : Q),
      volume ({s | ω ∈ C s} ∩ Ioi 0) =
        ∫⁻ s in Ioi 0, ({p : ℝ × Q | p.2 ∈ C p.1}.indicator 1 : ℝ × Q → ℝ≥0∞) (s, ω) := by
    intro C hC ω
    have hm : MeasurableSet {s | ω ∈ C s} := measurable_prodMk_right hC
    rw [← Measure.restrict_apply hm, ← lintegral_indicator_one hm]
    congr 1
  have key1 : ∀ s t, ρ (A s ∩ B t) = ∫⁻ ω, IA (s, ω) * IB (t, ω) ∂ρ := by
    intro s t
    have hmA : MeasurableSet (A s) := measurable_prodMk_left hAm
    have hmB : MeasurableSet (B t) := measurable_prodMk_left hBm
    rw [← lintegral_indicator_one (hmA.inter hmB)]
    congr 1; funext ω
    simp only [IA, IB, indicator, mem_inter_iff, mem_setOf_eq, Pi.one_apply]
    split_ifs <;> simp_all
  have mg : Measurable fun ω => ENNReal.ofReal (g ω) := ENNReal.measurable_ofReal.comp hg
  calc ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω) ∂ρ
      = ∫⁻ ω, (∫⁻ s in Ioi 0, IA (s, ω) * ENNReal.ofReal (g ω)) ∂ρ := by
        refine lintegral_congr fun ω => ?_
        rw [hA ω, hsec A hAm ω]
        have h : Measurable fun s : ℝ => IA (s, ω) := mIA.comp (measurable_id.prodMk measurable_const)
        exact (lintegral_mul_const _ h).symm
    _ = ∫⁻ s in Ioi 0, ∫⁻ ω, IA (s, ω) * ENNReal.ofReal (g ω) ∂ρ := by
        apply lintegral_lintegral_swap
        exact (((mIA.comp (measurable_snd.prodMk measurable_fst))).mul
          (mg.comp measurable_fst)).aemeasurable
    _ = ∫⁻ s in Ioi 0, ∫⁻ ω, (∫⁻ t in Ioi 0, IA (s, ω) * IB (t, ω)) ∂ρ := by
        refine lintegral_congr fun s => lintegral_congr fun ω => ?_
        rw [hB ω, hsec B hBm ω]
        have h : Measurable fun t : ℝ => IB (t, ω) := mIB.comp (measurable_id.prodMk measurable_const)
        exact (lintegral_const_mul _ h).symm
    _ = ∫⁻ s in Ioi 0, ∫⁻ t in Ioi 0, ∫⁻ ω, IA (s, ω) * IB (t, ω) ∂ρ := by
        refine lintegral_congr fun s => ?_
        apply lintegral_lintegral_swap
        exact ((mIA.comp (measurable_const.prodMk measurable_fst)).mul
          (mIB.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
    _ = _ := by
        refine lintegral_congr fun s => lintegral_congr fun t => (key1 s t).symm

def Ap (Z : Q → ℝ) (s : ℝ) : Set Q := {ω | s < Z ω}
def Am (Z : Q → ℝ) (s : ℝ) : Set Q := {ω | Z ω ≤ -s}

theorem Ap_vol (Z : Q → ℝ) (ω : Q) :
    ENNReal.ofReal (Z ω) = volume ({s | ω ∈ Ap Z s} ∩ Ioi 0) := by
  have : {s | ω ∈ Ap Z s} ∩ Ioi 0 = Ioo 0 (Z ω) := by
    ext s; simp only [Ap, mem_setOf_eq, mem_inter_iff, mem_Ioi, mem_Ioo]; tauto
  rw [this, Real.volume_Ioo, sub_zero]

theorem Am_vol (Z : Q → ℝ) (ω : Q) :
    ENNReal.ofReal (-Z ω) = volume ({s | ω ∈ Am Z s} ∩ Ioi 0) := by
  have : {s | ω ∈ Am Z s} ∩ Ioi 0 = Ioc 0 (-Z ω) := by
    ext s; simp only [Am, mem_setOf_eq, mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
  rw [this, Real.volume_Ioc, sub_zero]

theorem Ap_meas {Z : Q → ℝ} (hZ : Measurable Z) : MeasurableSet {p : ℝ × Q | p.2 ∈ Ap Z p.1} :=
  measurableSet_lt measurable_fst (hZ.comp measurable_snd)

theorem Am_meas {Z : Q → ℝ} (hZ : Measurable Z) : MeasurableSet {p : ℝ × Q | p.2 ∈ Am Z p.1} :=
  measurableSet_le (hZ.comp measurable_snd) measurable_fst.neg

/-- the quadrant term -/
noncomputable def T (A B : ℝ → Set Q) : ℝ≥0∞ := ∫⁻ s in Ioi 0, ∫⁻ t in Ioi 0, ρ (A s ∩ B t)

theorem piece (a b : Q → ℝ) (A B : ℝ → Set Q) (ha : Measurable a) (hb : Measurable b)
    (hA : ∀ ω, ENNReal.ofReal (a ω) = volume ({s | ω ∈ A s} ∩ Ioi 0))
    (hB : ∀ ω, ENNReal.ofReal (b ω) = volume ({s | ω ∈ B s} ∩ Ioi 0))
    (hAm : MeasurableSet {p : ℝ × Q | p.2 ∈ A p.1})
    (hBm : MeasurableSet {p : ℝ × Q | p.2 ∈ B p.1})
    (hI : Integrable (fun ω => a ω * b ω) ρ) :
    Integrable (fun ω => max (a ω) 0 * max (b ω) 0) ρ ∧
    ∫ ω, max (a ω) 0 * max (b ω) 0 ∂ρ = (T ρ A B).toReal ∧ T ρ A B ≠ ⊤ := by
  have hm : Measurable fun ω => max (a ω) 0 * max (b ω) 0 :=
    (ha.max measurable_const).mul (hb.max measurable_const)
  have hI' : Integrable (fun ω => max (a ω) 0 * max (b ω) 0) ρ := by
    refine hI.norm.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)),
      Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (max_le (le_abs_self _) (abs_nonneg _)) (max_le (le_abs_self _) (abs_nonneg _))
      (le_max_right _ _) (abs_nonneg _)
  have hof : ∀ x : ℝ, ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
    intro x; rcases le_total x 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  have hL : ∫⁻ ω, ENNReal.ofReal (max (a ω) 0 * max (b ω) 0) ∂ρ = T ρ A B := by
    rw [T, ← lay ρ A B a b hb hA hB hAm hBm]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_mul (le_max_right _ _), hof, hof]
  refine ⟨hI', ?_, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun ω => mul_nonneg (le_max_right _ _) (le_max_right _ _))
      hm.aestronglyMeasurable, hL]
  · rw [← hL]; exact (hI'.lintegral_lt_top).ne

/-- E[Z₁Z₂] as a signed combination of four quadrant terms -/
theorem cov_quad (Z₁ Z₂ : Q → ℝ) (m₁ : Measurable Z₁) (m₂ : Measurable Z₂)
    (hI : Integrable (fun ω => Z₁ ω * Z₂ ω) ρ) :
    ∫ ω, Z₁ ω * Z₂ ω ∂ρ =
      (T ρ (Ap Z₁) (Ap Z₂)).toReal + (T ρ (Am Z₁) (Am Z₂)).toReal -
        (T ρ (Ap Z₁) (Am Z₂)).toReal - (T ρ (Am Z₁) (Ap Z₂)).toReal ∧
    T ρ (Ap Z₁) (Ap Z₂) ≠ ⊤ ∧ T ρ (Am Z₁) (Am Z₂) ≠ ⊤ ∧
    T ρ (Ap Z₁) (Am Z₂) ≠ ⊤ ∧ T ρ (Am Z₁) (Ap Z₂) ≠ ⊤ := by
  have hI2 : Integrable (fun ω => -Z₁ ω * -Z₂ ω) ρ := by simpa using hI
  have hI3 : Integrable (fun ω => Z₁ ω * -Z₂ ω) ρ := by simpa using hI.neg
  have hI4 : Integrable (fun ω => -Z₁ ω * Z₂ ω) ρ := by simpa using hI.neg
  obtain ⟨i1, e1, f1⟩ := piece ρ Z₁ Z₂ (Ap Z₁) (Ap Z₂) m₁ m₂ (Ap_vol Z₁) (Ap_vol Z₂)
    (Ap_meas m₁) (Ap_meas m₂) hI
  obtain ⟨i2, e2, f2⟩ := piece ρ (fun ω => -Z₁ ω) (fun ω => -Z₂ ω) (Am Z₁) (Am Z₂) m₁.neg m₂.neg
    (Am_vol Z₁) (Am_vol Z₂) (Am_meas m₁) (Am_meas m₂) hI2
  obtain ⟨i3, e3, f3⟩ := piece ρ Z₁ (fun ω => -Z₂ ω) (Ap Z₁) (Am Z₂) m₁ m₂.neg (Ap_vol Z₁)
    (Am_vol Z₂) (Ap_meas m₁) (Am_meas m₂) hI3
  obtain ⟨i4, e4, f4⟩ := piece ρ (fun ω => -Z₁ ω) Z₂ (Am Z₁) (Ap Z₂) m₁.neg m₂ (Am_vol Z₁)
    (Ap_vol Z₂) (Am_meas m₁) (Ap_meas m₂) hI4
  refine ⟨?_, f1, f2, f3, f4⟩
  have k3 : ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0 -
      max (Z₁ ω) 0 * max (-Z₂ ω) 0 - max (-Z₁ ω) 0 * max (Z₂ ω) 0) ∂ρ =
      ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0 -
      max (Z₁ ω) 0 * max (-Z₂ ω) 0) ∂ρ - ∫ ω, max (-Z₁ ω) 0 * max (Z₂ ω) 0 ∂ρ :=
    integral_sub ((i1.add i2).sub i3) i4
  have k2 : ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0 -
      max (Z₁ ω) 0 * max (-Z₂ ω) 0) ∂ρ =
      ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0) ∂ρ -
      ∫ ω, max (Z₁ ω) 0 * max (-Z₂ ω) 0 ∂ρ := integral_sub (i1.add i2) i3
  have k1 : ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0) ∂ρ =
      ∫ ω, max (Z₁ ω) 0 * max (Z₂ ω) 0 ∂ρ + ∫ ω, max (-Z₁ ω) 0 * max (-Z₂ ω) 0 ∂ρ :=
    integral_add i1 i2
  rw [← e1, ← e2, ← e3, ← e4, ← k1, ← k2, ← k3]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show Z₁ ω * Z₂ ω = max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0 - max (Z₁ ω) 0 * max (-Z₂ ω) 0 - max (-Z₁ ω) 0 * max (Z₂ ω) 0
  rcases le_total (Z₁ ω) 0 with h1 | h1 <;> rcases le_total (Z₂ ω) 0 with h2 | h2
  · rw [max_eq_right h1, max_eq_right h2, max_eq_left (neg_nonneg.2 h1),
      max_eq_left (neg_nonneg.2 h2)]; ring
  · rw [max_eq_right h1, max_eq_left h2, max_eq_left (neg_nonneg.2 h1),
      max_eq_right (neg_nonpos.2 h2)]; ring
  · rw [max_eq_left h1, max_eq_right h2, max_eq_right (neg_nonpos.2 h1),
      max_eq_left (neg_nonneg.2 h2)]; ring
  · rw [max_eq_left h1, max_eq_left h2, max_eq_right (neg_nonpos.2 h1),
      max_eq_right (neg_nonpos.2 h2)]; ring

theorem T_mono {Q Q' : Type*} [MeasurableSpace Q] [MeasurableSpace Q'] (ρ : Measure Q) (ρ' : Measure Q')
    [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'] (A B : ℝ → Set Q) (A' B' : ℝ → Set Q')
    (h : ∀ s t, ρ.real (A s ∩ B t) ≤ ρ'.real (A' s ∩ B' t)) : T ρ A B ≤ T ρ' A' B' := by
  refine lintegral_mono fun s => lintegral_mono fun t => ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _), ← ENNReal.ofReal_toReal (measure_ne_top ρ' _)]
  exact ENNReal.ofReal_le_ofReal (h s t)

variable {Q : Type*} [MeasurableSpace Q] (ρ : Measure Q) [IsProbabilityMeasure ρ]

theorem frechet_up {A B : Set Q} : ρ.real (A ∩ B) ≤ min (ρ.real A) (ρ.real B) :=
  le_min (measureReal_mono inter_subset_left) (measureReal_mono inter_subset_right)

theorem frechet_lo {A B : Set Q} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    max (ρ.real A + ρ.real B - 1) 0 ≤ ρ.real (A ∩ B) := by
  have h1 := measureReal_union_add_inter (μ := ρ) (s := A) hB
  have h2 : ρ.real (A ∪ B) ≤ 1 := measureReal_le_one
  exact max_le (by linarith) measureReal_nonneg

theorem Ap_eq (Z : Q → ℝ) (s : ℝ) : Ap Z s = {ω | Z ω ≤ s}ᶜ := by
  ext ω; simp [Ap]

theorem Am_eq (Z : Q → ℝ) (s : ℝ) : Am Z s = {ω | Z ω ≤ -s} := rfl

/-- the four quadrant probabilities in terms of the joint distribution function -/
theorem quad_formulas {A0 B0 : Set Q} (hA : MeasurableSet A0) (hB : MeasurableSet B0) :
    ρ.real (A0ᶜ ∩ B0ᶜ) = 1 - ρ.real A0 - ρ.real B0 + ρ.real (A0 ∩ B0) ∧
    ρ.real (A0ᶜ ∩ B0) = ρ.real B0 - ρ.real (A0 ∩ B0) ∧
    ρ.real (A0 ∩ B0ᶜ) = ρ.real A0 - ρ.real (A0 ∩ B0) := by
  have hc : ∀ {C : Set Q}, MeasurableSet C → ρ.real Cᶜ = 1 - ρ.real C := fun hC =>
    probReal_compl_eq_one_sub hC
  refine ⟨?_, ?_, ?_⟩
  · rw [← compl_union, hc (hA.union hB)]
    have := measureReal_union_add_inter (μ := ρ) (s := A0) hB
    linarith
  · have := measureReal_inter_add_diff (μ := ρ) (s := B0) hA
    rw [diff_eq, inter_comm B0 A0] at this
    rw [inter_comm]; linarith
  · have := measureReal_inter_add_diff (μ := ρ) (s := A0) hB
    rw [diff_eq] at this; linarith

section
variable {ρ}
variable (Y₁ Y₂ : Q → ℝ) (m₁ : Measurable Y₁) (m₂ : Measurable Y₂)

include m₁ m₂ in
theorem co_quads
    (hc : ∀ u v : ℝ, ρ.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
      min (ρ.real {ω | Y₁ ω ≤ u}) (ρ.real {ω | Y₂ ω ≤ v})) (s t : ℝ) :
    ρ.real (Ap Y₁ s ∩ Ap Y₂ t) = min (ρ.real (Ap Y₁ s)) (ρ.real (Ap Y₂ t)) ∧
    ρ.real (Am Y₁ s ∩ Am Y₂ t) = min (ρ.real (Am Y₁ s)) (ρ.real (Am Y₂ t)) ∧
    ρ.real (Ap Y₁ s ∩ Am Y₂ t) = max (ρ.real (Ap Y₁ s) + ρ.real (Am Y₂ t) - 1) 0 ∧
    ρ.real (Am Y₁ s ∩ Ap Y₂ t) = max (ρ.real (Am Y₁ s) + ρ.real (Ap Y₂ t) - 1) 0 := by
  have hm1 : ∀ u, MeasurableSet {ω | Y₁ ω ≤ u} := fun u => measurableSet_le m₁ measurable_const
  have hm2 : ∀ u, MeasurableSet {ω | Y₂ ω ≤ u} := fun u => measurableSet_le m₂ measurable_const
  have hcomp : ∀ C : Set Q, MeasurableSet C → ρ.real Cᶜ = 1 - ρ.real C := fun C hC =>
    probReal_compl_eq_one_sub hC
  have hc' : ∀ u v, ρ.real ({ω | Y₁ ω ≤ u} ∩ {ω | Y₂ ω ≤ v}) =
      min (ρ.real {ω | Y₁ ω ≤ u}) (ρ.real {ω | Y₂ ω ≤ v}) := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Ap_eq, Ap_eq, (quad_formulas ρ (hm1 s) (hm2 t)).1, hcomp _ (hm1 s), hcomp _ (hm2 t), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith
  · exact hc' (-s) (-t)
  · rw [Ap_eq, Am_eq, (quad_formulas ρ (hm1 s) (hm2 (-t))).2.1, hcomp _ (hm1 s), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith
  · rw [Am_eq, Ap_eq, (quad_formulas ρ (hm1 (-s)) (hm2 t)).2.2, hcomp _ (hm2 t), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith

include m₁ m₂ in
theorem anti_quads
    (hc : ∀ u v : ℝ, ρ.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
      max (ρ.real {ω | Y₁ ω ≤ u} + ρ.real {ω | Y₂ ω ≤ v} - 1) 0) (s t : ℝ) :
    ρ.real (Ap Y₁ s ∩ Ap Y₂ t) = max (ρ.real (Ap Y₁ s) + ρ.real (Ap Y₂ t) - 1) 0 ∧
    ρ.real (Am Y₁ s ∩ Am Y₂ t) = max (ρ.real (Am Y₁ s) + ρ.real (Am Y₂ t) - 1) 0 ∧
    ρ.real (Ap Y₁ s ∩ Am Y₂ t) = min (ρ.real (Ap Y₁ s)) (ρ.real (Am Y₂ t)) ∧
    ρ.real (Am Y₁ s ∩ Ap Y₂ t) = min (ρ.real (Am Y₁ s)) (ρ.real (Ap Y₂ t)) := by
  have hm1 : ∀ u, MeasurableSet {ω | Y₁ ω ≤ u} := fun u => measurableSet_le m₁ measurable_const
  have hm2 : ∀ u, MeasurableSet {ω | Y₂ ω ≤ u} := fun u => measurableSet_le m₂ measurable_const
  have hcomp : ∀ C : Set Q, MeasurableSet C → ρ.real Cᶜ = 1 - ρ.real C := fun C hC =>
    probReal_compl_eq_one_sub hC
  have hc' : ∀ u v, ρ.real ({ω | Y₁ ω ≤ u} ∩ {ω | Y₂ ω ≤ v}) =
      max (ρ.real {ω | Y₁ ω ≤ u} + ρ.real {ω | Y₂ ω ≤ v} - 1) 0 := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Ap_eq, Ap_eq, (quad_formulas ρ (hm1 s) (hm2 t)).1, hcomp _ (hm1 s), hcomp _ (hm2 t), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith
  · exact hc' (-s) (-t)
  · rw [Ap_eq, Am_eq, (quad_formulas ρ (hm1 s) (hm2 (-t))).2.1, hcomp _ (hm1 s), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith
  · rw [Am_eq, Ap_eq, (quad_formulas ρ (hm1 (-s)) (hm2 t)).2.2, hcomp _ (hm2 t), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith

end

theorem main_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P']
    (Y₁ Y₂ : Ω → ℝ) (hIY : Integrable (fun ω => Y₁ ω * Y₂ ω) P)
    (X₁ X₂ : Ω' → ℝ) (hIX : Integrable (fun ω => X₁ ω * X₂ ω) P') (h₁ : IdentDistrib X₁ Y₁ P' P) (h₂ : IdentDistrib X₂ Y₂ P' P)
    (mY₁ : Measurable Y₁) (mY₂ : Measurable Y₂) (mX₁ : Measurable X₁) (mX₂ : Measurable X₂) :
    ((∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
          min (P.real {ω | Y₁ ω ≤ u}) (P.real {ω | Y₂ ω ≤ v})) →
        ∫ ω, X₁ ω * X₂ ω ∂P' ≤ ∫ ω, Y₁ ω * Y₂ ω ∂P) ∧
    ((∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
          max (P.real {ω | Y₁ ω ≤ u} + P.real {ω | Y₂ ω ≤ v} - 1) 0) →
        ∫ ω, Y₁ ω * Y₂ ω ∂P ≤ ∫ ω, X₁ ω * X₂ ω ∂P') := by
  obtain ⟨eY, fY1, fY2, fY3, fY4⟩ := cov_quad P Y₁ Y₂ mY₁ mY₂ hIY
  obtain ⟨eX, fX1, fX2, fX3, fX4⟩ := cov_quad P' X₁ X₂ mX₁ mX₂ hIX
  have mp1 : ∀ s, P'.real (Ap X₁ s) = P.real (Ap Y₁ s) := fun s => by
    simp only [measureReal_def]; congr 1; exact h₁.measure_mem_eq measurableSet_Ioi
  have mp2 : ∀ s, P'.real (Ap X₂ s) = P.real (Ap Y₂ s) := fun s => by
    simp only [measureReal_def]; congr 1; exact h₂.measure_mem_eq measurableSet_Ioi
  have mm1 : ∀ s, P'.real (Am X₁ s) = P.real (Am Y₁ s) := fun s => by
    simp only [measureReal_def]; congr 1; exact h₁.measure_mem_eq measurableSet_Iic
  have mm2 : ∀ s, P'.real (Am X₂ s) = P.real (Am Y₂ s) := fun s => by
    simp only [measureReal_def]; congr 1; exact h₂.measure_mem_eq measurableSet_Iic
  have apm : ∀ (Z : Ω' → ℝ), Measurable Z → ∀ s, MeasurableSet (Ap Z s) := fun Z hZ s =>
    measurableSet_lt measurable_const hZ
  have amm : ∀ (Z : Ω' → ℝ), Measurable Z → ∀ s, MeasurableSet (Am Z s) := fun Z hZ s =>
    measurableSet_le hZ measurable_const
  constructor
  · intro hc
    have q := co_quads Y₁ Y₂ mY₁ mY₂ hc
    have t1 : T P' (Ap X₁) (Ap X₂) ≤ T P (Ap Y₁) (Ap Y₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).1, ← mp1, ← mp2]; exact frechet_up P'
    have t2 : T P' (Am X₁) (Am X₂) ≤ T P (Am Y₁) (Am Y₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.1, ← mm1, ← mm2]; exact frechet_up P'
    have t3 : T P (Ap Y₁) (Am Y₂) ≤ T P' (Ap X₁) (Am X₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.2.1, ← mp1, ← mm2]; exact frechet_lo P' (apm _ mX₁ s) (amm _ mX₂ t)
    have t4 : T P (Am Y₁) (Ap Y₂) ≤ T P' (Am X₁) (Ap X₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.2.2, ← mm1, ← mp2]; exact frechet_lo P' (amm _ mX₁ s) (apm _ mX₂ t)
    have r1 := ENNReal.toReal_mono fY1 t1
    have r2 := ENNReal.toReal_mono fY2 t2
    have r3 := ENNReal.toReal_mono fX3 t3
    have r4 := ENNReal.toReal_mono fX4 t4
    rw [eX, eY]; linarith
  · intro hc
    have q := anti_quads Y₁ Y₂ mY₁ mY₂ hc
    have t1 : T P (Ap Y₁) (Ap Y₂) ≤ T P' (Ap X₁) (Ap X₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).1, ← mp1, ← mp2]; exact frechet_lo P' (apm _ mX₁ s) (apm _ mX₂ t)
    have t2 : T P (Am Y₁) (Am Y₂) ≤ T P' (Am X₁) (Am X₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.1, ← mm1, ← mm2]; exact frechet_lo P' (amm _ mX₁ s) (amm _ mX₂ t)
    have t3 : T P' (Ap X₁) (Am X₂) ≤ T P (Ap Y₁) (Am Y₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.2.1, ← mp1, ← mm2]; exact frechet_up P'
    have t4 : T P' (Am X₁) (Ap X₂) ≤ T P (Am Y₁) (Ap Y₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.2.2, ← mm1, ← mp2]; exact frechet_up P'
    have r1 := ENNReal.toReal_mono fX1 t1
    have r2 := ENNReal.toReal_mono fX2 t2
    have r3 := ENNReal.toReal_mono fY3 t3
    have r4 := ENNReal.toReal_mono fY4 t4
    rw [eX, eY]; linarith

end KA83


open MeasureTheory ProbabilityTheory Set Filter Topology

namespace KA83

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- one halving step: a non-null set contains a non-null subset of at most half its mass -/
theorem half (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {A : Set Ω} (hA : MeasurableSet A)
    (hpos : 0 < P.real A) : ∃ B ⊆ A, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ P.real A / 2 := by
  have hna := hP A
  simp only [RiskFunctionals.Kusuoka.IsAtomOf, not_and, not_forall, not_or] at hna
  have hpos' : 0 < P A := by
    rw [measureReal_def] at hpos; exact pos_of_ne_zero (fun h => by simp [h] at hpos)
  obtain ⟨A', hA'A, hA'm, hne1, hne0⟩ := hna hA hpos'
  have hr1 : P.real A' ≠ P.real A := fun h => hne1 (by
    rw [measureReal_def, measureReal_def] at h
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h)
  have hr0 : P.real A' ≠ 0 := fun h => hne0 (by
    rw [measureReal_def] at h
    exact (ENNReal.toReal_eq_zero_iff _).1 h |>.resolve_right (measure_ne_top _ _))
  have hle : P.real A' ≤ P.real A := measureReal_mono hA'A
  have hlt : P.real A' < P.real A := lt_of_le_of_ne hle hr1
  have h0 : 0 < P.real A' := lt_of_le_of_ne measureReal_nonneg (Ne.symm hr0)
  have hdiff : P.real (A \ A') = P.real A - P.real A' := measureReal_diff hA'A hA'm
  rcases le_or_gt (P.real A') (P.real A / 2) with h | h
  · exact ⟨A', hA'A, hA'm, h0, h⟩
  · refine ⟨A \ A', diff_subset, hA.diff hA'm, ?_, ?_⟩ <;> rw [hdiff] <;> linarith

theorem small (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {A : Set Ω} (hA : MeasurableSet A)
    (hpos : 0 < P.real A) (n : ℕ) :
    ∃ B ⊆ A, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ P.real A / 2 ^ n := by
  induction n with
  | zero => exact ⟨A, subset_rfl, hA, hpos, by simp⟩
  | succ n ih =>
    obtain ⟨B, hBA, hBm, hB0, hBle⟩ := ih
    obtain ⟨C, hCB, hCm, hC0, hCle⟩ := half P hP hBm hB0
    refine ⟨C, hCB.trans hBA, hCm, hC0, ?_⟩
    rw [pow_succ]
    calc P.real C ≤ P.real B / 2 := hCle
      _ ≤ P.real A / 2 ^ n / 2 := by linarith
      _ = _ := by ring

theorem small_eps (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {A : Set Ω} (hA : MeasurableSet A)
    (hpos : 0 < P.real A) {ε : ℝ} (hε : 0 < ε) :
    ∃ B ⊆ A, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith [measureReal_le_one (μ := P) (s := A)] : (0:ℝ) < 2)) (by norm_num : (1/2:ℝ) < 1)
  obtain ⟨B, hBA, hBm, hB0, hBle⟩ := small P hP hA hpos n
  refine ⟨B, hBA, hBm, hB0, hBle.trans ?_⟩
  have h1 : P.real A ≤ 1 := measureReal_le_one
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ h2]
  have : (1/2:ℝ)^n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  nlinarith

/-- admissible increments -/
def Adm (A B : Set Ω) (t : ℝ) (C : Set Ω) : Prop :=
  C ⊆ A \ B ∧ MeasurableSet C ∧ P.real B + P.real C ≤ t

theorem exists_greedy (A B : Set Ω) (t : ℝ) (hB : P.real B ≤ t) :
    ∃ C, Adm P A B t C ∧ ∀ C', Adm P A B t C' → P.real C' ≤ 2 * P.real C := by
  set S := {x | ∃ C, Adm P A B t C ∧ x = P.real C}
  have hne : S.Nonempty := ⟨0, ∅, ⟨empty_subset _, MeasurableSet.empty, by simpa using hB⟩, by simp⟩
  have hbdd : BddAbove S := ⟨1, by rintro x ⟨C, -, rfl⟩; exact measureReal_le_one⟩
  rcases le_or_gt (sSup S) 0 with h0 | h0
  · refine ⟨∅, ⟨empty_subset _, MeasurableSet.empty, by simpa using hB⟩, fun C' hC' => ?_⟩
    have := le_csSup hbdd ⟨C', hC', rfl⟩
    simp only [measureReal_empty, mul_zero]; linarith
  · obtain ⟨x, ⟨C, hC, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hne (half_lt_self h0)
    refine ⟨C, hC, fun C' hC' => ?_⟩
    have := le_csSup hbdd ⟨C', hC', rfl⟩
    linarith

open scoped Classical in
/-- the greedy step -/
noncomputable def nxt (A : Set Ω) (t : ℝ) (B : Set Ω) : Set Ω :=
  B ∪ (if h : ∃ C, Adm P A B t C ∧ ∀ C', Adm P A B t C' → P.real C' ≤ 2 * P.real C
    then h.choose else ∅)

noncomputable def gseq (A : Set Ω) (t : ℝ) : ℕ → Set Ω
  | 0 => ∅
  | n + 1 => nxt P A t (gseq A t n)

theorem seq_inv (A : Set Ω) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    gseq P A t n ⊆ A ∧ MeasurableSet (gseq P A t n) ∧ P.real (gseq P A t n) ≤ t := by
  induction n with
  | zero => exact ⟨empty_subset _, MeasurableSet.empty, by simpa [gseq] using ht⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hex := exists_greedy P A (gseq P A t n) t h3
    simp only [gseq, nxt, dif_pos hex]
    obtain ⟨⟨hCs, hCm, hCt⟩, -⟩ := hex.choose_spec
    refine ⟨union_subset h1 (hCs.trans diff_subset), h2.union hCm, ?_⟩
    exact (measureReal_union_le _ _).trans hCt

theorem seq_step (A : Set Ω) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    ∃ C, gseq P A t (n + 1) = gseq P A t n ∪ C ∧ Adm P A (gseq P A t n) t C ∧
      ∀ C', Adm P A (gseq P A t n) t C' → P.real C' ≤ 2 * P.real C := by
  have hex := exists_greedy P A (gseq P A t n) t (seq_inv P A t ht n).2.2
  refine ⟨hex.choose, ?_, hex.choose_spec⟩
  simp only [gseq, nxt, dif_pos hex]

/-- Sierpiński: a non-atomic probability takes every intermediate value on subsets. -/
theorem sierpinski (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {A : Set Ω} (hA : MeasurableSet A)
    {t : ℝ} (ht0 : 0 ≤ t) (htA : t ≤ P.real A) :
    ∃ B ⊆ A, MeasurableSet B ∧ P.real B = t := by
  set Bn := gseq P A t
  have hinv := seq_inv P A t ht0
  have hmono : Monotone Bn := monotone_nat_of_le_succ fun n => by
    obtain ⟨C, hC, -⟩ := seq_step P A t ht0 n
    show gseq P A t n ⊆ gseq P A t (n+1)
    rw [hC]; exact subset_union_left
  set B := ⋃ n, Bn n
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun n => (hinv n).2.1
  have hBA : B ⊆ A := iUnion_subset fun n => (hinv n).1
  have hlim : Tendsto (fun n => P.real (Bn n)) atTop (𝓝 (P.real B)) := by
    have := tendsto_measure_iUnion_atTop (μ := P) hmono
    have h2 := (ENNReal.tendsto_toReal (measure_ne_top P B)).comp this
    simpa [measureReal_def, Function.comp_def] using h2
  have hBt : P.real B ≤ t := le_of_tendsto' hlim fun n => (hinv n).2.2
  refine ⟨B, hBA, hBm, le_antisymm hBt ?_⟩
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hD : 0 < P.real (A \ B) := by
    rw [measureReal_diff hBA hBm]; linarith
  obtain ⟨C, hCD, hCm, hC0, hCle⟩ := small_eps P hP (hA.diff hBm) hD (sub_pos.2 hlt)
  -- increments tend to zero
  have hinc : ∀ n, ∃ Cn, P.real (Bn (n+1)) = P.real (Bn n) + P.real Cn ∧ P.real C ≤ 2 * P.real Cn := by
    intro n
    obtain ⟨Cn, hCn, ⟨hCs, hCnm, -⟩, hgr⟩ := seq_step P A t ht0 n
    refine ⟨Cn, ?_, hgr C ⟨fun x hx => ⟨(hCD hx).1, fun hxB => (hCD hx).2
      (mem_iUnion.2 ⟨n, hxB⟩)⟩, hCm, ?_⟩⟩
    · show P.real (gseq P A t (n+1)) = P.real (gseq P A t n) + _
      rw [hCn, measureReal_union (disjoint_left.2 fun x hx hx' => (hCs hx').2 hx) hCnm]
    · have : P.real (Bn n) ≤ P.real B := measureReal_mono (subset_iUnion Bn n)
      linarith
  have hdiff : Tendsto (fun n => P.real (Bn (n+1)) - P.real (Bn n)) atTop (𝓝 0) := by
    have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    simpa using this
  have hev := (hdiff.eventually (gt_mem_nhds (half_pos hC0))).exists
  obtain ⟨n, hn⟩ := hev
  obtain ⟨Cn, h1, h2⟩ := hinc n
  linarith

end KA83


open MeasureTheory ProbabilityTheory Set Filter Topology

namespace KA83

variable {Q : Type*} [MeasurableSpace Q] (ρ : Measure Q) [IsProbabilityMeasure ρ]

theorem real_inter_conull {S E : Set Q} (h : ρ Eᶜ = 0) : ρ.real (S ∩ E) = ρ.real S := by
  simp only [measureReal_def, measure_inter_conull h]

theorem F_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) : 0 ≤ g79q_F μ x :=
  measureReal_nonneg

theorem F_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) : g79q_F μ x ≤ 1 :=
  measureReal_le_one

/-- generic antimonotone coupling -/
theorem anti (μY μZ : Measure ℝ) [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    (V W : Q → ℝ) (hV : Measurable V) (hW : Measurable W)
    (hV01 : ρ {ω | 0 < V ω ∧ V ω < 1}ᶜ = 0)
    (hVa : ∀ a, 0 ≤ a → a ≤ 1 → ρ.real {ω | V ω < a} = a)
    (hVW : ∀ a, 0 ≤ a → a ≤ 1 → ∀ x,
      ρ.real ({ω | V ω < a} ∩ {ω | W ω ≤ x}) = min a (g79q_F μZ x)) :
    (∀ s, ρ.real {ω | g79q_q μY (1 - V ω) ≤ s} = g79q_F μY s) ∧
    (∀ t, ρ.real {ω | W ω ≤ t} = g79q_F μZ t) ∧
    (∀ s t, ρ.real {ω | g79q_q μY (1 - V ω) ≤ s ∧ W ω ≤ t} =
      max (g79q_F μY s + g79q_F μZ t - 1) 0) := by
  set E := {ω | 0 < V ω ∧ V ω < 1} with hE
  have key : ∀ s (C : Set Q), ρ.real ({ω | g79q_q μY (1 - V ω) ≤ s} ∩ C) =
      ρ.real ({ω | V ω < 1 - g79q_F μY s}ᶜ ∩ C) := by
    intro s C
    rw [← real_inter_conull ρ (S := {ω | g79q_q μY (1 - V ω) ≤ s} ∩ C) hV01,
      ← real_inter_conull ρ (S := {ω | V ω < 1 - g79q_F μY s}ᶜ ∩ C) hV01]
    congr 1
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, mem_compl_iff, not_lt, hE]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨?_, h2⟩, h3, h4⟩
      have := (g79q_qle' μY (p := 1 - V ω) (by linarith) (by linarith) s).1 h1
      linarith
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨?_, h2⟩, h3, h4⟩
      exact (g79q_qle' μY (p := 1 - V ω) (by linarith) (by linarith) s).2 (by linarith)
  have mVa : ∀ a, MeasurableSet {ω | V ω < a} := fun a => measurableSet_lt hV measurable_const
  have hWt : ∀ t, ρ.real {ω | W ω ≤ t} = g79q_F μZ t := by
    intro t
    have h := hVW 1 zero_le_one le_rfl t
    rw [min_eq_right (F_le_one μZ t), inter_comm,
      real_inter_conull ρ (E := {ω | V ω < 1})] at h
    · exact h
    · exact measure_mono_null (compl_subset_compl.2 fun ω hω => hω.2) hV01
  have ha0 : ∀ s, 0 ≤ 1 - g79q_F μY s := fun s => by linarith [F_le_one μY s]
  have ha1 : ∀ s, 1 - g79q_F μY s ≤ 1 := fun s => by linarith [F_nonneg μY s]
  refine ⟨fun s => ?_, hWt, fun s t => ?_⟩
  · have h := key s univ
    rw [inter_univ, inter_univ, probReal_compl_eq_one_sub (mVa _), hVa _ (ha0 s) (ha1 s)] at h
    rw [h]; ring
  · have h := key s {ω | W ω ≤ t}
    have hs : {ω | g79q_q μY (1 - V ω) ≤ s ∧ W ω ≤ t} =
        {ω | g79q_q μY (1 - V ω) ≤ s} ∩ {ω | W ω ≤ t} := rfl
    rw [hs, h]
    have hd := measureReal_inter_add_diff (μ := ρ) (s := {ω | W ω ≤ t}) (mVa (1 - g79q_F μY s))
    rw [diff_eq, inter_comm {ω | W ω ≤ t} {ω | V ω < 1 - g79q_F μY s},
      hVW _ (ha0 s) (ha1 s), hWt, inter_comm] at hd
    have e : ρ.real ({ω | V ω < 1 - g79q_F μY s}ᶜ ∩ {ω | W ω ≤ t}) =
        g79q_F μZ t - min (1 - g79q_F μY s) (g79q_F μZ t) := by linarith
    rw [e]
    simp only [min_def, max_def]; split_ifs <;> linarith

/-- the law from the distribution function -/
theorem law_eq (f : Q → ℝ) (hf : Measurable f) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ s, ρ.real {ω | f ω ≤ s} = g79q_F μ s) : ρ.map f = μ := by
  haveI : IsProbabilityMeasure (ρ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  refine Measure.ext_of_Iic _ _ fun s => ?_
  rw [Measure.map_apply hf measurableSet_Iic]
  have h2 := h s
  simp only [g79q_F, measureReal_def] at h2
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h2

end KA83


open MeasureTheory ProbabilityTheory Set Filter Topology

namespace KA83

instance ioo_prob : IsProbabilityMeasure (volume.restrict (Ioo (0:ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ]; simp⟩

theorem ioo_real (S : Set ℝ) :
    (volume.restrict (Ioo (0:ℝ) 1)).real S = (volume (S ∩ Ioo 0 1)).toReal := by
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Ioo]

theorem vol_sandwich {S : Set ℝ} {m : ℝ} (hm : m ≤ 1) (h1 : Ioo m 1 ⊆ S) (h2 : S ⊆ Icc m 1) :
    (volume S).toReal = 1 - m := by
  have e1 : volume (Ioo m 1) = ENNReal.ofReal (1 - m) := Real.volume_Ioo
  have e2 : volume (Icc m 1) = ENNReal.ofReal (1 - m) := Real.volume_Icc
  have : volume S = ENNReal.ofReal (1 - m) :=
    le_antisymm (e2 ▸ measure_mono h2) (e1 ▸ measure_mono h1)
  rw [this, ENNReal.toReal_ofReal (by linarith)]

theorem instA (μY μZ : Measure ℝ) [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    Measurable (fun u : ℝ => g79q_q μY u) ∧ Measurable (fun u : ℝ => g79q_q μZ (1 - u)) ∧
    (volume.restrict (Ioo (0:ℝ) 1)).map (fun u => g79q_q μY u) = μY ∧
    (volume.restrict (Ioo (0:ℝ) 1)).map (fun u => g79q_q μZ (1 - u)) = μZ ∧
    (∀ s t, (volume.restrict (Ioo (0:ℝ) 1)).real {u | g79q_q μY u ≤ s ∧ g79q_q μZ (1 - u) ≤ t} =
      max ((volume.restrict (Ioo (0:ℝ) 1)).real {u | g79q_q μY u ≤ s} +
        (volume.restrict (Ioo (0:ℝ) 1)).real {u | g79q_q μZ (1 - u) ≤ t} - 1) 0) := by
  set ν := volume.restrict (Ioo (0:ℝ) 1)
  have mW : Measurable (fun u : ℝ => g79q_q μZ (1 - u)) :=
    (g79q_meas μZ).comp (measurable_const.sub measurable_id)
  have mY : Measurable (fun u : ℝ => g79q_q μY u) := g79q_meas μY
  have h01 : ν {u : ℝ | 0 < 1 - u ∧ 1 - u < 1}ᶜ = 0 := by
    rw [Measure.restrict_apply' measurableSet_Ioo]
    convert measure_empty (μ := (volume : Measure ℝ))
    ext u; simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq, mem_Ioo, mem_empty_iff_false,
      iff_false]
    rintro ⟨h, h1, h2⟩; exact h ⟨by linarith, by linarith⟩
  have hVa : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ν.real {u : ℝ | 1 - u < a} = a := by
    intro a ha0 ha1
    rw [ioo_real, vol_sandwich (m := 1 - a) (by linarith)]
    · ring
    · intro u ⟨h1, h2⟩; exact ⟨show 1 - u < a by linarith, by linarith, h2⟩
    · intro u ⟨h1, h2, h3⟩
      simp only [mem_setOf_eq] at h1
      exact ⟨by linarith, h3.le⟩
  have hVW : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ x, ν.real ({u : ℝ | 1 - u < a} ∩
      {u | g79q_q μZ (1 - u) ≤ x}) = min a (g79q_F μZ x) := by
    intro a ha0 ha1 x
    have hG0 := F_nonneg μZ x
    have hG1 := F_le_one μZ x
    have key : ∀ u ∈ Ioo (0:ℝ) 1, g79q_q μZ (1 - u) ≤ x ↔ 1 - u ≤ g79q_F μZ x := fun u hu =>
      g79q_qle' μZ (by linarith [hu.2]) (by linarith [hu.1]) x
    rw [ioo_real, vol_sandwich (m := max (1 - a) (1 - g79q_F μZ x)) (max_le (by linarith) (by linarith))]
    · simp only [min_def, max_def]; split_ifs <;> linarith
    · intro u ⟨h1, h2⟩
      have hu : u ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_lt (le_max_of_le_left (by linarith)) h1, h2⟩
      have ha := (max_lt_iff.1 h1).1
      have hb := (max_lt_iff.1 h1).2
      exact ⟨⟨show 1 - u < a by linarith, (key u hu).2 (by linarith)⟩, hu⟩
    · intro u ⟨⟨h1, h2⟩, hu⟩
      simp only [mem_setOf_eq] at h1 h2
      have := (key u hu).1 h2
      exact ⟨max_le (by linarith) (by linarith), hu.2.le⟩
  obtain ⟨h1, h2, h3⟩ := anti ν μY μZ (fun u => 1 - u) (fun u => g79q_q μZ (1 - u))
    (measurable_const.sub measurable_id) mW h01 hVa hVW
  simp only [sub_sub_cancel] at h1 h3
  refine ⟨mY, mW, law_eq ν _ mY μY h1, law_eq ν _ mW μZ h2, fun s t => ?_⟩
  rw [h3, h1, h2]

end KA83


open MeasureTheory ProbabilityTheory Set Filter Topology

namespace KA83

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

open scoped Classical in
noncomputable def between (B C : Set Ω) (t : ℝ) : Set Ω :=
  if h : ∃ D, B ⊆ D ∧ D ⊆ C ∧ MeasurableSet D ∧ P.real D = t then h.choose else ∅

theorem between_spec (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) {B C : Set Ω}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : B ⊆ C) {t : ℝ}
    (h1 : P.real B ≤ t) (h2 : t ≤ P.real C) :
    B ⊆ between P B C t ∧ between P B C t ⊆ C ∧ MeasurableSet (between P B C t) ∧
      P.real (between P B C t) = t := by
  have hex : ∃ D, B ⊆ D ∧ D ⊆ C ∧ MeasurableSet D ∧ P.real D = t := by
    obtain ⟨E, hE, hEm, hEt⟩ := sierpinski P hP (hC.diff hB) (t := t - P.real B) (by linarith)
      (by rw [measureReal_diff hBC hB]; linarith)
    refine ⟨B ∪ E, subset_union_left, union_subset hBC (hE.trans diff_subset), hB.union hEm, ?_⟩
    rw [measureReal_union (disjoint_left.2 fun x hx hx' => (hE hx').2 hx) hEm, hEt]; ring
  simp only [between, dif_pos hex]; exact hex.choose_spec

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (Z : Ω → ℝ)

/-- dyadic family adapted to the level sets of `Z` -/
noncomputable def dz : ℕ → ℕ → Set Ω
  | 0, k => if k = 0 then ∅ else univ
  | n + 1, k => if k % 2 = 0 then dz n (k / 2) else if 2 ^ (n + 1) ≤ k then univ else
      between P (dz n (k / 2) ∪ {ω | Z ω < g79q_q μ ((k : ℝ) / 2 ^ (n + 1))})
        (dz n (k / 2 + 1) ∩ {ω | Z ω ≤ g79q_q μ ((k : ℝ) / 2 ^ (n + 1))}) ((k : ℝ) / 2 ^ (n + 1))

theorem dy_even (n j : ℕ) : dz P μ Z (n + 1) (2 * j) = dz P μ Z n j := by
  simp only [dz, show 2 * j % 2 = 0 by omega, if_true, show 2 * j / 2 = j by omega]

theorem dz_odd_big (n j : ℕ) (h : 2 ^ (n + 1) ≤ 2 * j + 1) : dz P μ Z (n + 1) (2 * j + 1) = univ := by
  simp only [dz, show (2 * j + 1) % 2 = 1 by omega, if_pos h]
  rfl

theorem dz_odd (n j : ℕ) (h : 2 * j + 1 < 2 ^ (n + 1)) : dz P μ Z (n + 1) (2 * j + 1) =
    between P (dz P μ Z n j ∪ {ω | Z ω < g79q_q μ (((2 * j + 1 : ℕ) : ℝ) / 2 ^ (n + 1))})
      (dz P μ Z n (j + 1) ∩ {ω | Z ω ≤ g79q_q μ (((2 * j + 1 : ℕ) : ℝ) / 2 ^ (n + 1))})
      (((2 * j + 1 : ℕ) : ℝ) / 2 ^ (n + 1)) := by
  simp only [dz, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega,
    if_neg (not_le.2 h)]
  rfl

theorem q_lt_le (hZ : Measurable Z) (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : P.real {ω | Z ω < g79q_q μ t} ≤ t := by
  by_contra hlt
  push_neg at hlt
  set x := g79q_q μ t
  have hU : {ω | Z ω < x} = ⋃ m : ℕ, {ω | Z ω ≤ x - 1 / (m + 1)} := by
    ext ω; simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      exact ⟨m, by linarith⟩
    · rintro ⟨m, hm⟩
      have : (0:ℝ) < 1 / (m + 1) := by positivity
      linarith
  have hmono : Monotone fun m : ℕ => {ω | Z ω ≤ x - 1 / (m + 1)} := by
    intro a b hab ω hω
    simp only [mem_setOf_eq] at hω ⊢
    have : (1:ℝ) / (b + 1) ≤ 1 / (a + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    linarith
  have hlim : Tendsto (fun m : ℕ => P.real {ω | Z ω ≤ x - 1 / (m + 1)}) atTop
      (𝓝 (P.real {ω | Z ω < x})) := by
    rw [hU]
    have := tendsto_measure_iUnion_atTop (μ := P) hmono
    have h2 := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp this
    simpa [measureReal_def, Function.comp_def] using h2
  obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
  rw [hμ] at hm
  have := (g79q_qle' μ ht0 ht1 _).2 hm.le
  have : (0:ℝ) < 1 / (m + 1) := by positivity
  linarith

theorem le_q_le (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : t ≤ P.real {ω | Z ω ≤ g79q_q μ t} := by
  rw [hμ]; exact (g79q_qle' μ ht0 ht1 _).1 le_rfl

theorem dz_full (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) (n : ℕ) :
    ((∀ k : ℕ, MeasurableSet (dz P μ Z n k) ∧ P.real (dz P μ Z n k) = min ((k : ℝ) / 2 ^ n) 1) ∧
      ∀ k : ℕ, dz P μ Z n k ⊆ dz P μ Z n (k + 1)) ∧
    (∀ k : ℕ, 0 < k → k < 2 ^ n → {ω | Z ω < g79q_q μ ((k : ℝ) / 2 ^ n)} ⊆ dz P μ Z n k ∧
        dz P μ Z n k ⊆ {ω | Z ω ≤ g79q_q μ ((k : ℝ) / 2 ^ n)}) ∧
    (∀ k : ℕ, 2 ^ n ≤ k → dz P μ Z n k = univ) ∧ dz P μ Z n 0 = ∅ := by
  have qm := cr_qmono μ
  induction n with
  | zero =>
    refine ⟨⟨fun k => ?_, fun k => ?_⟩, fun k hk hk' => by simp at hk'; omega, fun k hk => ?_,
      by simp [dz]⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [dz]
      · simp only [dz, Nat.pos_iff_ne_zero.1 hk, if_false, MeasurableSet.univ, true_and,
          probReal_univ, pow_zero, div_one]
        have : (1:ℝ) ≤ k := by exact_mod_cast hk
        rw [min_eq_right this]
    · simp only [dz, Nat.succ_ne_zero, if_false]; split_ifs <;> simp
    · simp only [pow_zero] at hk
      simp only [dz, show k ≠ 0 by omega, if_false]
  | succ n ih =>
    obtain ⟨⟨ih1, ih2⟩, ih3, ih4, ih5⟩ := ih
    have hpow : (2:ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hp : (0:ℝ) < 2 ^ n := by positivity
    have hpN : (2:ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
    -- the odd step
    have hodd : ∀ j, 2 * j + 1 < 2 ^ (n + 1) →
        dz P μ Z n j ⊆ dz P μ Z (n + 1) (2 * j + 1) ∧
        dz P μ Z (n + 1) (2 * j + 1) ⊆ dz P μ Z n (j + 1) ∧
        MeasurableSet (dz P μ Z (n + 1) (2 * j + 1)) ∧
        P.real (dz P μ Z (n + 1) (2 * j + 1)) = (((2 * j + 1 : ℕ)) : ℝ) / 2 ^ (n + 1) ∧
        {ω | Z ω < g79q_q μ ((((2 * j + 1 : ℕ)) : ℝ) / 2 ^ (n + 1))} ⊆ dz P μ Z (n + 1) (2 * j + 1) ∧
        dz P μ Z (n + 1) (2 * j + 1) ⊆ {ω | Z ω ≤ g79q_q μ ((((2 * j + 1 : ℕ)) : ℝ) / 2 ^ (n + 1))} := by
      intro j hj
      rw [dz_odd P μ Z n j hj]
      set t : ℝ := (((2 * j + 1 : ℕ)) : ℝ) / 2 ^ (n + 1) with ht
      have hj' : j < 2 ^ n := by omega
      have hjr : (j : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hj'
      have ht0 : 0 < t := by positivity
      have ht1 : t < 1 := by
        rw [ht, div_lt_one (by positivity)]; exact_mod_cast hj
      have htl : (j : ℝ) / 2 ^ n < t := by
        rw [ht, hpow, div_lt_div_iff₀ hp (by positivity)]; push_cast; nlinarith
      have htr : t < ((j + 1 : ℕ) : ℝ) / 2 ^ n := by
        rw [ht, hpow, div_lt_div_iff₀ (by positivity) hp]; push_cast; nlinarith
      have mlt : MeasurableSet {ω | Z ω < g79q_q μ t} := measurableSet_lt hZ measurable_const
      have mle : MeasurableSet {ω | Z ω ≤ g79q_q μ t} := measurableSet_le hZ measurable_const
      -- lower set facts
      have hL : dz P μ Z n j ⊆ {ω | Z ω ≤ g79q_q μ t} ∧
          (dz P μ Z n j ∪ {ω | Z ω < g79q_q μ t} ⊆ dz P μ Z n j ∨
            dz P μ Z n j ∪ {ω | Z ω < g79q_q μ t} ⊆ {ω | Z ω < g79q_q μ t}) := by
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · rw [ih5]; simp
        have hjr1 : (j : ℝ) / 2 ^ n < 1 := by rw [div_lt_one hp]; linarith
        have hj0' : (0:ℝ) < (j : ℝ) / 2 ^ n := by
          have : (0:ℝ) < j := by exact_mod_cast hj0
          positivity
        have hqle : g79q_q μ ((j : ℝ) / 2 ^ n) ≤ g79q_q μ t :=
          qm ⟨hj0', hjr1⟩ ⟨ht0, ht1⟩ htl.le
        obtain ⟨i3a, i3b⟩ := ih3 j hj0 hj'
        refine ⟨fun ω hω => le_trans (i3b hω) hqle, ?_⟩
        rcases hqle.lt_or_eq with hlt | heq
        · right
          exact union_subset (fun ω hω => lt_of_le_of_lt (i3b hω) hlt) subset_rfl
        · left
          refine union_subset subset_rfl ?_
          rw [← heq]; exact i3a
      have hR : {ω | Z ω < g79q_q μ t} ⊆ dz P μ Z n (j + 1) ∧
          (dz P μ Z n (j + 1) ⊆ dz P μ Z n (j + 1) ∩ {ω | Z ω ≤ g79q_q μ t} ∨
            {ω | Z ω ≤ g79q_q μ t} ⊆ dz P μ Z n (j + 1) ∩ {ω | Z ω ≤ g79q_q μ t}) := by
        rcases (show j + 1 = 2 ^ n ∨ j + 1 < 2 ^ n by omega) with he | hlt'
        · rw [ih4 (j + 1) he.ge]; simp
        have hjr1 : ((j + 1 : ℕ) : ℝ) / 2 ^ n < 1 := by
          rw [div_lt_one hp]; exact_mod_cast hlt'
        have hqle : g79q_q μ t ≤ g79q_q μ (((j + 1 : ℕ) : ℝ) / 2 ^ n) :=
          qm ⟨ht0, ht1⟩ ⟨ht0.trans htr, hjr1⟩ htr.le
        obtain ⟨i3a, i3b⟩ := ih3 (j + 1) (by omega) hlt'
        refine ⟨fun ω (hω : Z ω < _) => i3a (show Z ω < _ from lt_of_lt_of_le hω hqle), ?_⟩
        rcases hqle.lt_or_eq with hlt | heq
        · right
          exact subset_inter (fun ω (hω : Z ω ≤ _) => i3a (show Z ω < _ from
            lt_of_le_of_lt hω hlt)) subset_rfl
        · left
          refine subset_inter subset_rfl ?_
          rw [heq]; exact i3b
      have hsub : dz P μ Z n j ∪ {ω | Z ω < g79q_q μ t} ⊆
          dz P μ Z n (j + 1) ∩ {ω | Z ω ≤ g79q_q μ t} :=
        union_subset (subset_inter (ih2 j) hL.1)
          (subset_inter hR.1 fun ω (hω : Z ω < _) => show Z ω ≤ _ from hω.le)
      have hm1 : P.real (dz P μ Z n j ∪ {ω | Z ω < g79q_q μ t}) ≤ t := by
        rcases hL.2 with h | h
        · refine (measureReal_mono h).trans ?_
          rw [(ih1 j).2]; exact (min_le_left _ _).trans htl.le
        · exact (measureReal_mono h).trans (q_lt_le P μ Z hZ hμ ht0 ht1)
      have hm2 : t ≤ P.real (dz P μ Z n (j + 1) ∩ {ω | Z ω ≤ g79q_q μ t}) := by
        rcases hR.2 with h | h
        · refine le_trans ?_ (measureReal_mono h)
          rw [(ih1 (j + 1)).2]
          refine le_min htr.le ht1.le
        · exact (le_q_le P μ Z hμ ht0 ht1).trans (measureReal_mono h)
      obtain ⟨b1, b2, b3, b4⟩ := between_spec P hP ((ih1 j).1.union mlt) ((ih1 (j+1)).1.inter mle)
        hsub hm1 hm2
      refine ⟨subset_union_left.trans b1, b2.trans inter_subset_left, b3, b4,
        subset_union_right.trans b1, b2.trans inter_subset_right⟩
    refine ⟨⟨fun k => ?_, fun k => ?_⟩, fun k hk hk' => ?_, fun k hk => ?_, ?_⟩
    · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [dy_even]; refine ⟨(ih1 j).1, ?_⟩
        rw [(ih1 j).2, hpow]; push_cast
        rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
      · rcases lt_or_ge (2 * j + 1) (2 ^ (n + 1)) with hj | hj
        · obtain ⟨-, -, h3, h4, -⟩ := hodd j hj
          refine ⟨h3, ?_⟩
          rw [h4, min_eq_left]
          rw [div_le_one (by positivity)]; exact_mod_cast hj.le
        · rw [dz_odd_big P μ Z n j hj]
          refine ⟨MeasurableSet.univ, ?_⟩
          rw [probReal_univ, min_eq_right]
          rw [le_div_iff₀ (by positivity), one_mul]; exact_mod_cast hj
    · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [dy_even]
        rcases lt_or_ge (2 * j + 1) (2 ^ (n + 1)) with hj | hj
        · exact (hodd j hj).1
        · rw [dz_odd_big P μ Z n j hj]; exact subset_univ _
      · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, dy_even]
        rcases lt_or_ge (2 * j + 1) (2 ^ (n + 1)) with hj | hj
        · exact (hodd j hj).2.1
        · rw [ih4 (j + 1) (by omega)]; exact subset_univ _
    · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [dy_even]
        have e : ((2 * j : ℕ) : ℝ) / 2 ^ (n + 1) = (j : ℝ) / 2 ^ n := by
          rw [hpow]; push_cast
          rw [mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
        rw [e]; exact ih3 j (by omega) (by omega)
      · obtain ⟨-, -, -, -, h5, h6⟩ := hodd j hk'
        exact ⟨h5, h6⟩
    · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [dy_even]; exact ih4 j (by omega)
      · exact dz_odd_big P μ Z n j hk
    · rw [show (0:ℕ) = 2 * 0 by rfl, dy_even]; exact ih5

end KA83


open MeasureTheory ProbabilityTheory Set Filter Topology

namespace KA83

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (Z : Ω → ℝ)

theorem dy_inv (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) (n : ℕ) :
    (∀ k : ℕ, MeasurableSet (dz P μ Z n k) ∧ P.real (dz P μ Z n k) = min ((k : ℝ) / 2 ^ n) 1) ∧
      ∀ k : ℕ, dz P μ Z n k ⊆ dz P μ Z n (k + 1) := (dz_full P μ Z hP hZ hμ n).1

theorem dy_lift (n k i : ℕ) : dz P μ Z (n + i) (k * 2 ^ i) = dz P μ Z n k := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc, show k * 2 ^ (i + 1) = 2 * (k * 2 ^ i) by ring, dy_even, ih]

theorem dy_sub (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) {n m k k' : ℕ}
    (h : (k : ℝ) / 2 ^ n ≤ (k' : ℝ) / 2 ^ m) : dz P μ Z n k ⊆ dz P μ Z m k' := by
  have hmono : Monotone (dz P μ Z (n + m)) := monotone_nat_of_le_succ (dy_inv P μ Z hP hZ hμ (n + m)).2
  have hle : k * 2 ^ m ≤ k' * 2 ^ n := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
    exact_mod_cast h
  rw [← dy_lift P μ Z n k m, ← dy_lift P μ Z m k' n, add_comm m n]
  exact hmono hle

/-- the uniform variable -/
noncomputable def V (ω : Ω) : ℝ := sInf {x | ∃ n k, ω ∈ dz P μ Z n k ∧ x = (k : ℝ) / 2 ^ n}

theorem U_lt (ω : Ω) (x : ℝ) : V P μ Z ω < x ↔ ∃ n k, ω ∈ dz P μ Z n k ∧ (k : ℝ) / 2 ^ n < x := by
  have hne : {x | ∃ n k, ω ∈ dz P μ Z n k ∧ x = (k : ℝ) / 2 ^ n}.Nonempty :=
    ⟨1, 0, 1, by simp [dz], by norm_num⟩
  have hbdd : BddBelow {x | ∃ n k, ω ∈ dz P μ Z n k ∧ x = (k : ℝ) / 2 ^ n} :=
    ⟨0, by rintro _ ⟨n, k, -, rfl⟩; positivity⟩
  rw [V, csInf_lt_iff hbdd hne]
  constructor
  · rintro ⟨_, ⟨n, k, h, rfl⟩, hlt⟩; exact ⟨n, k, h, hlt⟩
  · rintro ⟨n, k, h, hlt⟩; exact ⟨_, ⟨n, k, h, rfl⟩, hlt⟩

theorem U_set (x : ℝ) : {ω | V P μ Z ω < x} =
    ⋃ n, ⋃ k, dz P μ Z n k ∩ {_ω | (k : ℝ) / 2 ^ n < x} := by
  ext ω; simp only [mem_setOf_eq, U_lt, mem_iUnion, mem_inter_iff]

theorem U_meas (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) : Measurable (V P μ Z) := by
  refine measurable_of_Iio fun x => ?_
  change MeasurableSet {ω | V P μ Z ω < x}
  rw [U_set]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k =>
    ((dy_inv P μ Z hP hZ hμ n).1 k).1.inter (MeasurableSet.const _)

theorem U_lo (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) {x : ℝ} {n k : ℕ}
    (h : (k : ℝ) / 2 ^ n < x) : dz P μ Z n k ⊆ {ω | V P μ Z ω < x} :=
  fun ω hω => (U_lt P μ Z ω x).2 ⟨n, k, hω, h⟩

theorem U_hi (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) {x : ℝ} {N k : ℕ}
    (h : x ≤ (k : ℝ) / 2 ^ N) : {ω | V P μ Z ω < x} ⊆ dz P μ Z N k := by
  intro ω hω
  obtain ⟨n, k', hω', hlt⟩ := (U_lt P μ Z ω x).1 hω
  exact dy_sub P μ Z hP hZ hμ (hlt.le.trans h) hω'

theorem U_prob_lt (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) (x : ℝ) :
    P.real {ω | V P μ Z ω < x} = max 0 (min x 1) := by
  rcases le_or_gt x 0 with hx0 | hx0
  · have : {ω | V P μ Z ω < x} = ∅ := by
      apply subset_eq_empty (U_hi P μ Z hP hZ hμ (N := 0) (k := 0) (by simpa using hx0))
      simp [dz]
    rw [this, measureReal_empty, max_eq_left (min_le_of_left_le hx0)]
  rcases lt_or_ge 1 x with hx1 | hx1
  · have : {ω | V P μ Z ω < x} = univ :=
      univ_subset_iff.1 (by
        have := U_lo P μ Z hP hZ hμ (n := 0) (k := 1) (x := x) (by simpa using hx1)
        simpa [dz] using this)
    rw [this, probReal_univ, min_eq_right hx1.le, max_eq_right zero_le_one]
  rw [min_eq_left hx1, max_eq_right hx0.le]
  have hinv := dy_inv P μ Z hP hZ hμ
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ) < 1)
    have hy : 0 ≤ x * 2 ^ N := by positivity
    have hk := Nat.ceil_lt_add_one hy
    have hk' := Nat.le_ceil (x * 2 ^ N)
    have h2 : (0:ℝ) < 2 ^ N := by positivity
    have hinvN : (1/2:ℝ) ^ N = 1 / 2 ^ N := by rw [div_pow, one_pow]
    calc P.real {ω | V P μ Z ω < x} ≤ P.real (dz P μ Z N ⌈x * 2 ^ N⌉₊) :=
          measureReal_mono (U_hi P μ Z hP hZ hμ (by rw [le_div_iff₀ h2]; exact hk'))
      _ = min ((⌈x * 2 ^ N⌉₊ : ℝ) / 2 ^ N) 1 := ((hinv N).1 _).2
      _ ≤ (⌈x * 2 ^ N⌉₊ : ℝ) / 2 ^ N := min_le_left _ _
      _ ≤ x + ε := by
          rw [div_le_iff₀ h2]
          have : 1 < ε * 2 ^ N := by
            rw [hinvN, div_lt_iff₀ h2] at hN; linarith
          nlinarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ) < 1)
    have h2 : (0:ℝ) < 2 ^ N := by positivity
    have hy : 0 < x * 2 ^ N := by positivity
    have hk := Nat.ceil_lt_add_one hy.le
    have hk' := Nat.le_ceil (x * 2 ^ N)
    have hk1 : 1 ≤ ⌈x * 2 ^ N⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hy).ne'
    have hinvN : (1/2:ℝ) ^ N = 1 / 2 ^ N := by rw [div_pow, one_pow]
    have hcast : ((⌈x * 2 ^ N⌉₊ - 1 : ℕ) : ℝ) = (⌈x * 2 ^ N⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hk1, Nat.cast_one]
    have hlt : ((⌈x * 2 ^ N⌉₊ - 1 : ℕ) : ℝ) / 2 ^ N < x := by
      rw [div_lt_iff₀ h2, hcast]; linarith
    have hmeas := ((hinv N).1 (⌈x * 2 ^ N⌉₊ - 1)).2
    have hle1 : ((⌈x * 2 ^ N⌉₊ - 1 : ℕ) : ℝ) / 2 ^ N ≤ 1 := hlt.le.trans hx1
    have := measureReal_mono (μ := P) (U_lo P μ Z hP hZ hμ hlt)
    rw [hmeas, min_eq_left hle1] at this
    have : 1 < ε * 2 ^ N := by
      rw [hinvN, div_lt_iff₀ h2] at hN; linarith
    have h3 : x ≤ ((⌈x * 2 ^ N⌉₊ - 1 : ℕ) : ℝ) / 2 ^ N + ε := by
      rw [hcast, div_add' _ _ _ h2.ne', le_div_iff₀ h2]; nlinarith
    linarith

theorem U_unif (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) :
    P.map (V P μ Z) = volume.restrict (Icc (0:ℝ) 1) := by
  have hm := U_meas P μ Z hP hZ hμ
  set Φ : ℝ → ℝ := fun x => max 0 (min x 1)
  have hΦ : ∀ x, P.real {ω | V P μ Z ω < x} = Φ x := U_prob_lt P μ Z hP hZ hμ
  have hΦle : ∀ x, P.real {ω | V P μ Z ω ≤ x} = Φ x := by
    intro x
    apply le_antisymm
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      calc P.real {ω | V P μ Z ω ≤ x} ≤ P.real {ω | V P μ Z ω < x + ε} :=
            measureReal_mono fun ω (h : V P μ Z ω ≤ x) => show V P μ Z ω < x + ε by linarith
        _ = Φ (x + ε) := hΦ _
        _ ≤ Φ x + ε := by
            simp only [Φ]
            have h1 : min (x + ε) 1 ≤ min x 1 + ε := by
              rcases le_total x 1 with h | h
              · rw [min_eq_left h]; exact min_le_left _ _
              · rw [min_eq_right h]; linarith [min_le_right (x + ε) 1]
            exact max_le (by linarith [le_max_left 0 (min x 1)])
              (by linarith [le_max_right 0 (min x 1)])
    · rw [← hΦ]; exact measureReal_mono fun ω (h : V P μ Z ω < x) => show V P μ Z ω ≤ x from h.le
  haveI : IsProbabilityMeasure (P.map (V P μ Z)) := Measure.isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  have hL : P (V P μ Z ⁻¹' Iic x) = ENNReal.ofReal (Φ x) := by
    rw [← hΦle x, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]; rfl
  rw [hL]
  rcases lt_or_ge x 0 with hx | hx
  · have : Iic x ∩ Icc (0:ℝ) 1 = ∅ := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩; linarith
    rw [this, measure_empty]; simp only [Φ]
    rw [min_eq_left (by linarith), max_eq_left hx.le, ENNReal.ofReal_zero]
  rcases le_or_gt x 1 with hx1 | hx1
  · have : Iic x ∩ Icc (0:ℝ) 1 = Icc 0 x := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [this, Real.volume_Icc, sub_zero]; simp only [Φ]
    rw [min_eq_left hx1, max_eq_right hx]
  · have : Iic x ∩ Icc (0:ℝ) 1 = Icc 0 1 := by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨h1', h2⟩; exact ⟨by linarith, h1', h2⟩
    rw [this, Real.volume_Icc]; simp only [Φ]
    rw [min_eq_right hx1.le, max_eq_right zero_le_one]; simp

end KA83


open MeasureTheory ProbabilityTheory Set Filter Topology

namespace KA83

theorem dyadic_between {b c : ℝ} (hb : 0 ≤ b) (hbc : b < c) (hc : c ≤ 1) :
    ∃ N k : ℕ, b < (k : ℝ) / 2 ^ N ∧ (k : ℝ) / 2 ^ N < c ∧ 0 < k ∧ k < 2 ^ N := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (sub_pos.2 hbc) (by norm_num : (1/2:ℝ) < 1)
  have h2 : (0:ℝ) < 2 ^ N := by positivity
  have hinvN : (1/2:ℝ) ^ N = 1 / 2 ^ N := by rw [div_pow, one_pow]
  rw [hinvN, div_lt_iff₀ h2] at hN
  set k := ⌊b * 2 ^ N⌋₊ + 1 with hk
  have hk1 : b * 2 ^ N < (k : ℝ) := by rw [hk]; push_cast; exact Nat.lt_floor_add_one _
  have hk2 : (k : ℝ) ≤ b * 2 ^ N + 1 := by
    rw [hk]; push_cast; linarith [Nat.floor_le (show 0 ≤ b * 2 ^ N by positivity)]
  have hkc : (k : ℝ) / 2 ^ N < c := by rw [div_lt_iff₀ h2]; nlinarith
  refine ⟨N, k, by rw [lt_div_iff₀ h2]; exact hk1, hkc, by omega, ?_⟩
  have : (k : ℝ) < 2 ^ N := by
    have := (div_lt_iff₀ h2).1 (hkc.trans_le hc); linarith
  exact_mod_cast this

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (Z : Ω → ℝ)

theorem V_W (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x : ℝ) :
    P.real ({ω | V P μ Z ω < a} ∩ {ω | Z ω ≤ x}) = min a (g79q_F μ x) := by
  obtain ⟨-, -, h4, h5⟩ := dz_full P μ Z hP hZ hμ 0
  have hfull := dz_full P μ Z hP hZ hμ
  have hVa : P.real {ω | V P μ Z ω < a} = a := by
    rw [U_prob_lt P μ Z hP hZ hμ, min_eq_left ha1, max_eq_right ha0]
  rcases le_or_gt a (g79q_F μ x) with hle | hlt
  · rw [min_eq_left hle, inter_eq_left.2, hVa]
    intro ω hω
    obtain ⟨n, k, hωk, hk⟩ := (U_lt P μ Z ω a).1 hω
    obtain ⟨-, h3, h4, h5⟩ := hfull n
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h5] at hωk; exact absurd hωk (notMem_empty ω)
    rcases lt_or_ge k (2 ^ n) with hkn | hkn
    · have hp : (0:ℝ) < 2 ^ n := by positivity
      have hr0 : (0:ℝ) < (k : ℝ) / 2 ^ n := by
        have : (0:ℝ) < k := by exact_mod_cast hk0
        positivity
      have hr1 : (k : ℝ) / 2 ^ n < 1 := by rw [div_lt_one hp]; exact_mod_cast hkn
      have := (h3 k hk0 hkn).2 hωk
      exact le_trans this ((g79q_qle' μ hr0 hr1 x).2 (hk.le.trans hle))
    · exfalso
      have hp : (0:ℝ) < 2 ^ n := by positivity
      have : (1:ℝ) ≤ (k : ℝ) / 2 ^ n := by
        rw [le_div_iff₀ hp, one_mul]; exact_mod_cast hkn
      linarith
  · rw [min_eq_right hlt.le, inter_eq_right.2, hμ]
    obtain ⟨N, k, h1, h2, hk0, hkN⟩ := dyadic_between (measureReal_nonneg) hlt ha1
    obtain ⟨-, h3, -, -⟩ := hfull N
    intro ω (hω : Z ω ≤ x)
    have hp : (0:ℝ) < 2 ^ N := by positivity
    have hr0 : (0:ℝ) < (k : ℝ) / 2 ^ N := lt_of_le_of_lt measureReal_nonneg h1
    have hr1 : (k : ℝ) / 2 ^ N < 1 := h2.trans_le ha1
    have hq : x < g79q_q μ ((k : ℝ) / 2 ^ N) := by
      by_contra hc; push_neg at hc
      exact (not_lt.2 ((g79q_qle' μ hr0 hr1 x).1 hc)) h1
    exact U_lo P μ Z hP hZ hμ h2 ((h3 k hk0 hkN).1 (show Z ω < _ from lt_of_le_of_lt hω hq))

theorem V_01 (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) :
    P {ω | 0 < V P μ Z ω ∧ V P μ Z ω < 1}ᶜ = 0 := by
  have hm := U_meas P μ Z hP hZ hμ
  have e : {ω | 0 < V P μ Z ω ∧ V P μ Z ω < 1}ᶜ = V P μ Z ⁻¹' (Ioo 0 1)ᶜ := rfl
  rw [e, ← Measure.map_apply hm measurableSet_Ioo.compl, U_unif P μ Z hP hZ hμ,
    Measure.restrict_apply measurableSet_Ioo.compl]
  refine measure_mono_null (t := {0, 1}) ?_ ?_
  · intro u ⟨h1, h2, h3⟩
    simp only [mem_compl_iff, mem_Ioo, not_and, not_lt] at h1
    rcases h2.lt_or_eq with h | h
    · have := h1 h; right; simp only [mem_singleton_iff]; linarith
    · left; exact h.symm
  · exact (toFinite _).measure_zero _

/-- instance on the non-atomic space -/
theorem instB (hP : RiskFunctionals.Kusuoka.IsNonAtomic P) (hZ : Measurable Z)
    (hμ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F μ x) (μY : Measure ℝ) [IsProbabilityMeasure μY] :
    Measurable (fun ω => g79q_q μY (1 - V P μ Z ω)) ∧
    P.map (fun ω => g79q_q μY (1 - V P μ Z ω)) = μY ∧
    (∀ s t, P.real {ω | g79q_q μY (1 - V P μ Z ω) ≤ s ∧ Z ω ≤ t} =
      max (P.real {ω | g79q_q μY (1 - V P μ Z ω) ≤ s} + P.real {ω | Z ω ≤ t} - 1) 0) := by
  have hm := U_meas P μ Z hP hZ hμ
  have hmY : Measurable (fun ω => g79q_q μY (1 - V P μ Z ω)) :=
    (g79q_meas μY).comp (measurable_const.sub hm)
  obtain ⟨h1, h2, h3⟩ := anti P μY μ (V P μ Z) Z hm hZ (V_01 P μ Z hP hZ hμ)
    (fun a ha0 ha1 => by rw [U_prob_lt P μ Z hP hZ hμ, min_eq_left ha1, max_eq_right ha0])
    (V_W P μ Z hP hZ hμ)
  refine ⟨hmY, law_eq P _ hmY μY h1, fun s t => ?_⟩
  rw [h3, h1, h2]

end KA83


open MeasureTheory ProbabilityTheory Set

namespace KA83

theorem two_sides {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : RiskFunctionals.Kusuoka.IsNonAtomic P)
    {p q : ENNReal} (hpq : p.HolderConjugate q) (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    (∫ u in Ioo 0 1, RiskFunctionals.Kusuoka.quantileFunction (P.map Y) u *
        RiskFunctionals.Kusuoka.quantileFunction (P.map Z) (1 - u)) ≤ ∫ ω, Y ω * Z ω ∂P ∧
    ∃ Y' : Lp ℝ p P, IdentDistrib (Y : Ω → ℝ) (Y' : Ω → ℝ) P P ∧
      (∫ ω, Y' ω * Z ω ∂P) ≤ ∫ u in Ioo 0 1, RiskFunctionals.Kusuoka.quantileFunction (P.map Y) u *
        RiskFunctionals.Kusuoka.quantileFunction (P.map Z) (1 - u) := by
  haveI : p.HolderTriple q 1 := hpq
  have mY : Measurable (Y : Ω → ℝ) := (Lp.stronglyMeasurable Y).measurable
  have mZ : Measurable (Z : Ω → ℝ) := (Lp.stronglyMeasurable Z).measurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map mY.aemeasurable
  haveI : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map mZ.aemeasurable
  set ν := volume.restrict (Ioo (0:ℝ) 1)
  obtain ⟨mA1, mA2, lA1, lA2, jA⟩ := instA (P.map Y) (P.map Z)
  have hμZ : ∀ x, P.real {ω | Z ω ≤ x} = g79q_F (P.map Z) x := fun x => by
    rw [g79q_F, map_measureReal_apply mZ measurableSet_Iic]; rfl
  obtain ⟨mB, lB, jB⟩ := instB P (P.map Z) Z hP mZ hμZ (P.map Y)
  have iA1 : IdentDistrib (fun u => g79q_q (P.map Y) u) Y ν P :=
    ⟨mA1.aemeasurable, mY.aemeasurable, lA1⟩
  have iA2 : IdentDistrib (fun u => g79q_q (P.map Z) (1 - u)) Z ν P :=
    ⟨mA2.aemeasurable, mZ.aemeasurable, lA2⟩
  have iB1 : IdentDistrib (fun ω => g79q_q (P.map Y) (1 - V P (P.map Z) Z ω)) Y P P :=
    ⟨mB.aemeasurable, mY.aemeasurable, lB⟩
  have memA1 := iA1.memLp_iff.2 (Lp.memLp Y)
  have memA2 := iA2.memLp_iff.2 (Lp.memLp Z)
  have memB := iB1.memLp_iff.2 (Lp.memLp Y)
  have intA : Integrable (fun u => g79q_q (P.map Y) u * g79q_q (P.map Z) (1 - u)) ν :=
    memA1.integrable_mul memA2
  have intP : Integrable (fun ω => Y ω * Z ω) P := (Lp.memLp Y).integrable_mul (Lp.memLp Z)
  have intB : Integrable (fun ω => g79q_q (P.map Y) (1 - V P (P.map Z) Z ω) * Z ω) P :=
    memB.integrable_mul (Lp.memLp Z)
  refine ⟨?_, ?_⟩
  · exact (main_meas ν P _ _ intA _ _ intP iA1.symm iA2.symm mA1 mA2 mY mZ).2 jA
  · refine ⟨memB.toLp _, iB1.symm.trans (IdentDistrib.of_ae_eq mB.aemeasurable
      memB.coeFn_toLp.symm), ?_⟩
    have e : (∫ ω, (memB.toLp _ : Ω → ℝ) ω * Z ω ∂P) =
        ∫ ω, g79q_q (P.map Y) (1 - V P (P.map Z) Z ω) * Z ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [memB.coeFn_toLp] with ω h
      rw [h]
    rw [e]
    exact (main_meas P ν _ _ intB _ _ intA (iA1.trans iB1.symm) iA2 mB mZ mA1 mA2).2 jB

end KA83

open RiskFunctionals.Kusuoka

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P)
    {p q : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hpq : p.HolderConjugate q)
    (𝒜 : Lp ℝ p P → ℝ) (h𝒜 : IsAcceptabilityFunctional P 𝒜)
    (h𝒜vi : IsVersionIndependent P 𝒜)
    (𝒵𝒜 : Set (Lp ℝ q P)) (A : Lp ℝ q P → ℝ)
    (hrep : HasDualRepresentation P 𝒜 𝒵𝒜 A) (hAvi : IsVersionIndependentDual P 𝒵𝒜 A)
    (hC1 : ∀ Z ∈ 𝒵𝒜, A Z = 0) :
    ∀ Y : Lp ℝ p P,
      IsGLB {x : ℝ | ∃ Z ∈ 𝒵𝒜, x = ∫ u in Set.Ioo 0 1,
        quantileFunction (P.map Y) u * quantileFunction (P.map Z) (1 - u)} (𝒜 Y) := by
  intro Y
  constructor
  · rintro x ⟨Z, hZ, rfl⟩
    obtain ⟨-, Y', hid, hle⟩ := KA83.two_sides P hP hpq Y Z
    have h1 := (hrep Y').1 ⟨Z, hZ, rfl⟩
    rw [hC1 Z hZ, sub_zero] at h1
    rw [h𝒜vi Y Y' hid]
    linarith
  · intro b hb
    apply (hrep Y).2
    rintro x ⟨Z, hZ, rfl⟩
    have h1 := hb ⟨Z, hZ, rfl⟩
    rw [hC1 Z hZ, sub_zero]
    linarith [(KA83.two_sides P hP hpq Y Z).1]

