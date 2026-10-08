-- Prove2me | solution 1 for PoissonDirichlet.MaxDensity.eq_92
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:18:27.943974+00:00
-- url     : https://prove2.me/submissions/9defc359-4d30-4d2a-b253-2643c3d675fc

import Mathlib
import Definitions.Def_PoissonDirichlet_MaxDensity_Setting
open MeasureTheory ProbabilityTheory Filter Topology


namespace PoissonDirichlet.MaxDensity

open PoissonDirichlet.Ratio in
lemma e92_measurable_stick : Measurable (stick : (ℕ → ℝ) → ℕ → ℝ) := by
  refine measurable_pi_lambda _ (fun k => ?_)
  unfold stick
  exact (Finset.measurable_prod _ (fun i _ => measurable_const.sub (measurable_pi_apply i))).mul
    (measurable_pi_apply k)

open PoissonDirichlet.Ratio in
lemma e92_measurable_stick_k (k : ℕ) : Measurable (fun y : ℕ → ℝ => stick y k) :=
  (measurable_pi_apply k).comp e92_measurable_stick

open PoissonDirichlet.Ratio in
lemma e92_stick_succ (y : ℕ → ℝ) (k : ℕ) :
    stick y (k + 1) = (1 - y 0) * stick (fun i => y (i + 1)) k := by
  unfold stick
  rw [Finset.prod_range_succ', mul_comm]
  ring

open PoissonDirichlet.Ratio in
lemma e92_stick_zero (y : ℕ → ℝ) : stick y 0 = y 0 := by
  simp [stick]

open PoissonDirichlet.Ratio in
lemma e92_stick_mem (y : ℕ → ℝ) (hy : ∀ i, 0 < y i ∧ y i < 1) (k : ℕ) :
    0 < stick y k ∧ stick y k < 1 := by
  unfold stick
  have hp : 0 < ∏ i ∈ Finset.range k, (1 - y i) :=
    Finset.prod_pos (fun i _ => by linarith [(hy i).2])
  have hp1 : ∏ i ∈ Finset.range k, (1 - y i) ≤ 1 :=
    Finset.prod_le_one (fun i _ => by linarith [(hy i).2]) (fun i _ => by linarith [(hy i).1])
  constructor
  · exact mul_pos hp (hy k).1
  · calc (∏ i ∈ Finset.range k, (1 - y i)) * y k ≤ 1 * y k :=
          mul_le_mul_of_nonneg_right hp1 (hy k).1.le
      _ < 1 := by linarith [(hy k).2]

open PoissonDirichlet.Ratio in
/-- The top ranked value of a bounded nonnegative sequence is its supremum. -/
lemma e92_ranked_zero (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ranked x 0 = ⨆ i, x i := by
  unfold ranked
  have hbdd : BddAbove (Set.range x) := ⟨1, by rintro _ ⟨i, rfl⟩; exact (hx i).2⟩
  have hS : {t : ℝ | 0 ≤ t ∧ {i | t < x i}.encard ≤ (0 : ℕ)} = Set.Ici (⨆ i, x i) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ici, Nat.cast_zero, nonpos_iff_eq_zero,
      Set.encard_eq_zero]
    constructor
    · rintro ⟨_, h⟩
      apply ciSup_le
      intro i
      by_contra hlt
      push_neg at hlt
      have : i ∈ ({i | t < x i} : Set ℕ) := hlt
      rw [h] at this
      exact this
    · intro h
      refine ⟨le_trans (le_trans (hx 0).1 (le_ciSup hbdd 0)) h, ?_⟩
      apply Set.eq_empty_of_forall_notMem
      intro i hi
      have : x i ≤ ⨆ j, x j := le_ciSup hbdd i
      simp only [Set.mem_setOf_eq] at hi
      linarith
  rw [hS, csInf_Ici]

open PoissonDirichlet.Ratio in
lemma e92_sup_le_iff (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (c : ℝ) :
    (⨆ i, x i) ≤ c ↔ ∀ i, x i ≤ c := by
  have hbdd : BddAbove (Set.range x) := ⟨1, by rintro _ ⟨i, rfl⟩; exact (hx i).2⟩
  exact ciSup_le_iff hbdd

open PoissonDirichlet.Ratio in
/-- Characterization of `V₁ = Ṽ₁` in terms of the normalized tail. -/
lemma e92_max_eq_first (y : ℕ → ℝ) (hy : ∀ i, 0 < y i ∧ y i < 1) :
    ranked (stick y) 0 = y 0 ↔
      ∀ k, stick (fun i => y (i + 1)) k ≤ y 0 / (1 - y 0) := by
  have hx : ∀ i, 0 ≤ stick y i ∧ stick y i ≤ 1 :=
    fun i => ⟨(e92_stick_mem y hy i).1.le, (e92_stick_mem y hy i).2.le⟩
  have hbdd : BddAbove (Set.range (stick y)) := ⟨1, by rintro _ ⟨i, rfl⟩; exact (hx i).2⟩
  rw [e92_ranked_zero _ hx]
  have h0 : stick y 0 ≤ ⨆ i, stick y i := le_ciSup hbdd 0
  rw [e92_stick_zero] at h0
  have h1 : (1 : ℝ) - y 0 > 0 := by linarith [(hy 0).2]
  constructor
  · intro h k
    have : stick y (k + 1) ≤ y 0 := h ▸ le_ciSup hbdd (k + 1)
    rw [e92_stick_succ] at this
    rw [le_div_iff₀ h1]
    linarith
  · intro h
    apply le_antisymm _ h0
    rw [e92_sup_le_iff _ hx]
    intro i
    cases i with
    | zero => rw [e92_stick_zero]
    | succ k =>
      rw [e92_stick_succ]
      have := h k
      rw [le_div_iff₀ h1] at this
      linarith

lemma e92_beta_compl (a b : ℝ) : betaMeasure a b (Set.Ioo 0 1)ᶜ = 0 := by
  unfold betaMeasure
  rw [withDensity_apply _ measurableSet_Ioo.compl]
  rw [setLIntegral_congr_fun measurableSet_Ioo.compl (g := fun _ => 0) ?_]
  · simp
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with h | h
    · exact betaPDF_eq_zero_of_nonpos h
    · exact betaPDF_eq_zero_of_one_le h

lemma e92_stickLaw_unique (α θ : ℝ) (ν : Measure (ℕ → ℝ))
    (hν : PoissonDirichlet.Ratio.IsStickLaw α θ ν) :
    ν = Measure.infinitePi (fun k : ℕ => betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) := by
  have := hν.2.1.map_fun_eq_infinitePi_map (fun k => measurable_pi_apply k)
  have h1 : ν.map (fun (y : ℕ → ℝ) (i : ℕ) => y i) = ν := by
    have : (fun (y : ℕ → ℝ) (i : ℕ) => y i) = id := rfl
    rw [this, Measure.map_id]
  rw [h1] at this
  rw [this]
  congr 1
  funext k
  exact (hν.2.2 k).map_eq

lemma e92_measurable_betaPDF (a b : ℝ) : Measurable (betaPDF a b) :=
  ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)

open PoissonDirichlet.Ratio in
theorem eq_92_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P)
    (V' : Ω' → ℕ → ℝ) (hV' : PoissonDirichlet.Ratio.HasPD α (α + θ) P' V')
    (s : Set ℝ) (hs : MeasurableSet s) :
    P {ω | PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 ∈ s ∧
        PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 = PoissonDirichlet.Ratio.stick (fun k => Ytil k ω) 0} =
      ∫⁻ x in s ∩ Set.Ioo (0 : ℝ) 1, ENNReal.ofReal
        (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
          * x ^ (-α) * (1 - x) ^ (α + θ - 1)
          * (P' {ω' | V' ω' 0 < x / (1 - x)}).toReal) := by
  -- the shifted sequence and its law
  set Z : Ω → ℕ → ℝ := fun ω k => Ytil (k + 1) ω with hZ
  have hZm : Measurable Z := measurable_pi_lambda _ (fun k => hYm (k + 1))
  set μ : Measure (ℕ → ℝ) :=
    Measure.infinitePi (fun k : ℕ => betaMeasure (1 - α) ((α + θ) + ((k : ℝ) + 1) * α)) with hμ
  have hprob : ∀ k : ℕ, IsProbabilityMeasure
      (betaMeasure (1 - α) ((α + θ) + ((k : ℝ) + 1) * α)) := by
    intro k
    have h := Measure.isProbabilityMeasure_map (μ := P) (f := Ytil (k + 1)) (hYm (k + 1)).aemeasurable
    rw [(hYlaw (k + 1)).map_eq] at h
    have e : θ + (((k + 1 : ℕ) : ℝ) + 1) * α = (α + θ) + ((k : ℝ) + 1) * α := by push_cast; ring
    rw [e] at h
    exact h
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hZind' : iIndepFun (fun k => Ytil (k + 1)) P :=
    hYind.precomp (g := fun k : ℕ => k + 1) (fun a b h => by simpa using h)
  have hZlaw : P.map Z = μ := by
    have := hZind'.map_fun_eq_infinitePi_map (fun k => hYm (k + 1))
    show P.map (fun ω k => Ytil (k + 1) ω) = _
    rw [this, hμ]
    congr 1
    funext k
    rw [(hYlaw (k + 1)).map_eq]
    have e : θ + (((k + 1 : ℕ) : ℝ) + 1) * α = (α + θ) + ((k : ℝ) + 1) * α := by push_cast; ring
    rw [e]
  have hZind : IndepFun (Ytil 0) Z P := by
    rw [IndepFun_iff_Indep]
    have hmeas : ∀ k, MeasurableSpace.comap (Ytil k) inferInstance ≤ ‹MeasurableSpace Ω› :=
      fun k => (hYm k).comap_le
    have hS := indep_iSup_of_disjoint hmeas hYind.iIndep
      (S := {0}) (T := {k : ℕ | k ≠ 0}) (by
        rw [Set.disjoint_left]; intro k hk hk'; simp at hk hk'; exact hk' hk)
    refine indep_of_indep_of_le hS ?_ ?_
    · exact le_iSup₂ (f := fun i (_ : i ∈ ({0} : Set ℕ)) =>
        MeasurableSpace.comap (Ytil i) inferInstance) 0 rfl
    · have : Measurable[⨆ i ∈ {k : ℕ | k ≠ 0}, MeasurableSpace.comap (Ytil i) inferInstance] Z := by
        refine @measurable_pi_lambda Ω ℕ (fun _ => ℝ)
          (⨆ i ∈ {k : ℕ | k ≠ 0}, MeasurableSpace.comap (Ytil i) inferInstance) _ Z (fun k => ?_)
        have hk : k + 1 ∈ {k : ℕ | k ≠ 0} := by simp
        refine measurable_iff_comap_le.mpr ?_
        exact le_iSup₂ (f := fun i (_ : i ∈ {k : ℕ | k ≠ 0}) =>
          MeasurableSpace.comap (Ytil i) inferInstance) (k + 1) hk
      exact this.comap_le
  -- law of Y₀
  have hβ0 : P.map (Ytil 0) = betaMeasure (1 - α) (θ + α) := by
    rw [(hYlaw 0).map_eq]
    have e : θ + (((0 : ℕ) : ℝ) + 1) * α = θ + α := by push_cast; ring
    rw [e]
  haveI hβprob : IsProbabilityMeasure (betaMeasure (1 - α) (θ + α)) := by
    rw [← hβ0]; exact Measure.isProbabilityMeasure_map (hYm 0).aemeasurable
  -- almost surely all coordinates lie in (0,1)
  have hE : ∀ᵐ ω ∂P, ∀ i, 0 < Ytil i ω ∧ Ytil i ω < 1 := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have : {ω | ¬(0 < Ytil i ω ∧ Ytil i ω < 1)} = Ytil i ⁻¹' (Set.Ioo 0 1)ᶜ := by ext; simp
    rw [this, ← Measure.map_apply (hYm i) measurableSet_Ioo.compl, (hYlaw i).map_eq,
      e92_beta_compl]
  have hE' : ∀ᵐ y ∂μ, ∀ i, 0 < y i ∧ y i < 1 := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have : {y : ℕ → ℝ | ¬(0 < y i ∧ y i < 1)} = (fun y : ℕ → ℝ => y i) ⁻¹' (Set.Ioo 0 1)ᶜ := by
      ext; simp
    rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Ioo.compl, hμ,
      Measure.infinitePi_map_eval, e92_beta_compl]
  -- the supremum of the stick lengths
  set T : (ℕ → ℝ) → ℝ := fun y => ⨆ k, stick y k with hT
  have hTm : Measurable T := Measurable.iSup (fun k => e92_measurable_stick_k k)
  -- the event in the product space
  set A : Set (ℝ × (ℕ → ℝ)) := {p | p.1 ∈ s ∧ ∀ k, stick p.2 k ≤ p.1 / (1 - p.1)} with hA
  have hAm : MeasurableSet A := by
    have : A = (Prod.fst ⁻¹' s) ∩ ⋂ k, {p : ℝ × (ℕ → ℝ) | stick p.2 k ≤ p.1 / (1 - p.1)} := by
      ext p; simp [hA]
    rw [this]
    apply (hs.preimage measurable_fst).inter
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_le ((e92_measurable_stick_k k).comp measurable_snd)
      (measurable_fst.div (measurable_const.sub measurable_fst))
  have hLHS : P {ω | ranked (stick fun k => Ytil k ω) 0 ∈ s ∧
        ranked (stick fun k => Ytil k ω) 0 = stick (fun k => Ytil k ω) 0} =
      P ((fun ω => (Ytil 0 ω, Z ω)) ⁻¹' A) := by
    apply measure_congr
    filter_upwards [hE] with ω hω
    show (ranked (stick fun k => Ytil k ω) 0 ∈ s ∧
        ranked (stick fun k => Ytil k ω) 0 = stick (fun k => Ytil k ω) 0) = ((Ytil 0 ω, Z ω) ∈ A)
    simp only [hA, Set.mem_setOf_eq]
    rw [e92_stick_zero]
    have key := e92_max_eq_first (fun k => Ytil k ω) hω
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2 ▸ h1, ?_⟩
      exact key.1 h2
    · rintro ⟨h1, h2⟩
      have h3 : ranked (stick fun k => Ytil k ω) 0 = Ytil 0 ω := key.2 h2
      exact ⟨h3 ▸ h1, h3⟩
  have hjoint : P.map (fun ω => (Ytil 0 ω, Z ω)) = (betaMeasure (1 - α) (θ + α)).prod μ := by
    rw [hZind.map_prod_eq_prod_map_map (hYm 0).aemeasurable hZm.aemeasurable, hβ0, hZlaw]
  rw [hLHS, ← Measure.map_apply ((hYm 0).prodMk hZm) hAm, hjoint, Measure.prod_apply hAm]
  have hsec : ∀ x, μ (Prod.mk x ⁻¹' A) =
      s.indicator (fun x => μ {y | ∀ k, stick y k ≤ x / (1 - x)}) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      congr 1
      ext y
      simp [hA, hx]
    · rw [Set.indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' A = ∅ := by
        ext y
        simp [hA, hx]
      rw [this, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator hs]
  have hg : ∀ c, μ {y | ∀ k, stick y k ≤ c} = μ {y | T y ≤ c} := by
    intro c
    apply measure_congr
    filter_upwards [hE'] with y hy
    show (∀ k, stick y k ≤ c) = (T y ≤ c)
    simp only [hT]
    rw [e92_sup_le_iff _ (fun i => ⟨(e92_stick_mem y hy i).1.le, (e92_stick_mem y hy i).2.le⟩)]
  have hh : ∀ c, P' {ω' | V' ω' 0 < c} = μ {y | T y < c} := by
    intro c
    obtain ⟨hV'm, μ', hμ', hlaw⟩ := hV'
    have e1 : {ω' | V' ω' 0 < c} = V' ⁻¹' {v : ℕ → ℝ | v 0 < c} := by ext; simp
    rw [e1, hlaw _ (measurableSet_lt (measurable_pi_apply 0) measurable_const),
      e92_stickLaw_unique α (α + θ) μ' hμ']
    apply measure_congr
    filter_upwards [hE'] with y hy
    show (ranked (stick y) 0 < c) = (T y < c)
    simp only [hT]
    rw [e92_ranked_zero _ (fun i => ⟨(e92_stick_mem y hy i).1.le, (e92_stick_mem y hy i).2.le⟩)]
  simp_rw [hg, hh]
  -- atoms: the two sets differ only for countably many x
  have hcount : Set.Countable
      {x : ℝ | μ {y | T y ≤ x / (1 - x)} ≠ μ {y | T y < x / (1 - x)}} := by
    have hC := Measure.countable_meas_level_set_pos (μ := μ) hTm
    apply Set.Countable.mono _ ((hC.image (fun c => c / (1 + c))).insert 1)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_cases hx1 : x = 1
    · exact Set.mem_insert_iff.2 (Or.inl hx1)
    · apply Set.mem_insert_iff.2
      right
      refine ⟨x / (1 - x), ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]
        by_contra hzero
        have h0 : μ {y | T y = x / (1 - x)} = 0 := by
          by_contra hne
          exact hzero (pos_iff_ne_zero.mpr hne)
        apply hx
        have hU : {y | T y ≤ x / (1 - x)} = {y | T y < x / (1 - x)} ∪ {y | T y = x / (1 - x)} := by
          ext y
          simp only [Set.mem_setOf_eq, Set.mem_union]
          exact le_iff_lt_or_eq
        rw [hU]
        apply le_antisymm
        · calc μ ({y | T y < x / (1 - x)} ∪ {y | T y = x / (1 - x)})
              ≤ μ {y | T y < x / (1 - x)} + μ {y | T y = x / (1 - x)} := measure_union_le _ _
            _ = μ {y | T y < x / (1 - x)} := by rw [h0, add_zero]
        · exact measure_mono Set.subset_union_left
      · have h1x : (1 : ℝ) - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx1)
        have : 1 + x / (1 - x) = 1 / (1 - x) := by
          rw [eq_div_iff h1x, add_mul, one_mul, div_mul_cancel₀ _ h1x]; ring
        show x / (1 - x) / (1 + x / (1 - x)) = x
        rw [this, div_div_div_cancel_right₀ h1x, div_one]
  have hae : ∀ᵐ x ∂((betaMeasure (1 - α) (θ + α)).restrict s),
      μ {y | T y ≤ x / (1 - x)} = μ {y | T y < x / (1 - x)} := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    have : {x : ℝ | ¬ μ {y | T y ≤ x / (1 - x)} = μ {y | T y < x / (1 - x)}} =
      {x : ℝ | μ {y | T y ≤ x / (1 - x)} ≠ μ {y | T y < x / (1 - x)}} := rfl
    rw [this]
    exact (withDensity_absolutelyContinuous volume _) (hcount.measure_zero volume)
  rw [lintegral_congr_ae hae]
  -- measurability of the integrand
  have hBm : MeasurableSet {p : ℝ × (ℕ → ℝ) | T p.2 < p.1 / (1 - p.1)} :=
    measurableSet_lt (hTm.comp measurable_snd)
      (measurable_fst.div (measurable_const.sub measurable_fst))
  have hFm : Measurable (fun x : ℝ => μ {y | T y < x / (1 - x)}) :=
    measurable_measure_prodMk_left (ν := μ) hBm
  -- unfold the beta measure
  rw [betaMeasure, restrict_withDensity hs,
    lintegral_withDensity_eq_lintegral_mul _ (e92_measurable_betaPDF _ _) hFm]
  rw [← lintegral_inter_add_sdiff _ _ (measurableSet_Ioo (a := (0:ℝ)) (b := 1))]
  have hzero : ∫⁻ x in s \ Set.Ioo 0 1,
      (betaPDF (1 - α) (θ + α) * fun x => μ {y | T y < x / (1 - x)}) x = 0 := by
    rw [setLIntegral_congr_fun (hs.diff measurableSet_Ioo) (g := fun _ => 0)]
    · simp
    · intro x hx
      simp only [Set.mem_diff, Set.mem_Ioo, not_and_or, not_lt] at hx
      simp only [Pi.mul_apply]
      rcases hx.2 with h | h
      · rw [betaPDF_eq_zero_of_nonpos h, zero_mul]
      · rw [betaPDF_eq_zero_of_one_le h, zero_mul]
  rw [hzero, add_zero]
  apply setLIntegral_congr_fun (hs.inter measurableSet_Ioo)
  intro x hx
  have hx0 : 0 < x := hx.2.1
  have hx1 : x < 1 := hx.2.2
  simp only [Pi.mul_apply]
  rw [betaPDF_of_pos_lt_one hx0 hx1]
  conv_lhs => rw [← ENNReal.ofReal_toReal (measure_ne_top μ {y | T y < x / (1 - x)})]
  rw [← ENNReal.ofReal_mul]
  · congr 1
    have e1 : (1 : ℝ) - α - 1 = -α := by ring
    have e2 : θ + α - 1 = α + θ - 1 := by ring
    rw [e1, e2]
    unfold beta
    have e3 : 1 - α + (θ + α) = θ + 1 := by ring
    rw [e3, one_div_div]
    ring
  · have hb : 0 < beta (1 - α) (θ + α) := beta_pos (by linarith) (by linarith)
    exact mul_nonneg (mul_nonneg (div_nonneg zero_le_one hb.le) (Real.rpow_nonneg hx0.le _))
      (Real.rpow_nonneg (by linarith) _)

end PoissonDirichlet.MaxDensity

open PoissonDirichlet.MaxDensity


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (α θ : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (Ytil : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable (Ytil k)) (hYind : iIndepFun Ytil P)
    (hYlaw : ∀ k : ℕ, HasLaw (Ytil k) (betaMeasure (1 - α) (θ + ((k : ℝ) + 1) * α)) P)
    (V' : Ω' → ℕ → ℝ) (hV' : PoissonDirichlet.Ratio.HasPD α (α + θ) P' V')
    (s : Set ℝ) (hs : MeasurableSet s) :
    P {ω | PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 ∈ s ∧
        PoissonDirichlet.Ratio.ranked (PoissonDirichlet.Ratio.stick fun k => Ytil k ω) 0 = PoissonDirichlet.Ratio.stick (fun k => Ytil k ω) 0} =
      ∫⁻ x in s ∩ Set.Ioo (0 : ℝ) 1, ENNReal.ofReal
        (Real.Gamma (θ + 1) / (Real.Gamma (θ + α) * Real.Gamma (1 - α))
          * x ^ (-α) * (1 - x) ^ (α + θ - 1)
          * (P' {ω' | V' ω' 0 < x / (1 - x)}).toReal) := by
  exact eq_92_core P P' α θ hα hα1 hθ Ytil hYm hYind hYlaw V' hV' s hs
