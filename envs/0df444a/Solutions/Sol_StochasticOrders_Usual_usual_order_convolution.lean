-- Prove2me | solution 1 for StochasticOrders.Usual.usual_order_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T11:15:41.693989+00:00
-- url     : https://prove2.me/submissions/7014831d-e0c6-4a0b-a8da-9d3525586407

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Quantile function (left-continuous inverse of the cdf) of a measure on `ℝ`. -/
noncomputable def soUsConv_Q (P : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf P x}

theorem soUsConv_bdd (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf P x} := by
  have h := (tendsto_cdf_atBot P).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

theorem soUsConv_nonempty (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf P x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop P).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

theorem soUsConv_le_cdf_Q (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    u ≤ cdf P (soUsConv_Q P u) := by
  have hcont : ContinuousWithinAt (cdf P) (Ici (soUsConv_Q P u)) (soUsConv_Q P u) :=
    (cdf P).right_continuous _
  have ht : Tendsto (cdf P) (𝓝[>] (soUsConv_Q P u)) (𝓝 (cdf P (soUsConv_Q P u))) :=
    hcont.mono Ioi_subset_Ici_self
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (soUsConv_nonempty P hu1) hx
  exact le_trans hs (monotone_cdf P hsx.le)

theorem soUsConv_Q_le_iff (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) (x : ℝ) : soUsConv_Q P u ≤ x ↔ u ≤ cdf P x := by
  constructor
  · intro h
    exact le_trans (soUsConv_le_cdf_Q P hu1) (monotone_cdf P h)
  · intro h
    exact csInf_le (soUsConv_bdd P hu0) h

theorem soUsConv_Q_mono (P : Measure ℝ) [IsProbabilityMeasure P] :
    MonotoneOn (soUsConv_Q P) (Ioo 0 1) := by
  intro u hu v hv huv
  rw [soUsConv_Q_le_iff P hu.1 hu.2]
  exact le_trans huv (soUsConv_le_cdf_Q P hv.2)

instance soUsConv_U_prob : IsProbabilityMeasure (volume.restrict (Ioo (0:ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; simp⟩

theorem soUsConv_Q_ae (P : Measure ℝ) [IsProbabilityMeasure P] :
    AEMeasurable (soUsConv_Q P) (volume.restrict (Ioo (0:ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (soUsConv_Q_mono P)

theorem soUsConv_map_Q (P : Measure ℝ) [IsProbabilityMeasure P] :
    (volume.restrict (Ioo (0:ℝ) 1)).map (soUsConv_Q P) = P := by
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply_of_aemeasurable (soUsConv_Q_ae P) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf P x]
  have hset : soUsConv_Q P ⁻¹' Iic x ∩ Ioo 0 1 = {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (soUsConv_Q_le_iff P h2.1 h2.2 x).mp h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(soUsConv_Q_le_iff P h2.1 h2.2 x).mpr h1, h2⟩
  rw [hset]
  apply le_antisymm
  · calc volume {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} ≤ volume (Icc 0 (cdf P x)) :=
          measure_mono (fun u hu => ⟨hu.1.1.le, hu.2⟩)
      _ = ENNReal.ofReal (cdf P x) := by rw [Real.volume_Icc, sub_zero]
  · calc ENNReal.ofReal (cdf P x) = volume (Ioo 0 (cdf P x)) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ volume {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
          apply measure_mono
          intro u hu
          exact ⟨⟨hu.1, lt_of_lt_of_le hu.2 (cdf_le_one P x)⟩, hu.2.le⟩

theorem soUsConv_cdf_le {P R : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (h : ∀ x, P (Ioi x) ≤ R (Ioi x)) (x : ℝ) : cdf R x ≤ cdf P x := by
  have hP := prob_compl_eq_one_sub (μ := P) (measurableSet_Ioi (a := x))
  have hR := prob_compl_eq_one_sub (μ := R) (measurableSet_Ioi (a := x))
  rw [compl_Ioi] at hP hR
  have key : R (Iic x) ≤ P (Iic x) := by
    rw [hP, hR]
    exact tsub_le_tsub_left (h x) 1
  rw [← ofReal_cdf, ← ofReal_cdf] at key
  exact (ENNReal.ofReal_le_ofReal_iff (cdf_nonneg P x)).mp key

theorem soUsConv_Q_le_Q {P R : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (h : ∀ x, P (Ioi x) ≤ R (Ioi x)) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    soUsConv_Q P u ≤ soUsConv_Q R u := by
  rw [soUsConv_Q_le_iff P hu.1 hu.2]
  exact le_trans (soUsConv_le_cdf_Q R hu.2) (soUsConv_cdf_le h _)

theorem soUsConv_exists_rat_ge {m : ℕ} {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    {v : Fin m → ℝ} (hv : v ∈ U) :
    ∃ q : Fin m → ℚ, (fun i => (q i : ℝ)) ∈ U ∧ v ≤ (fun i => (q i : ℝ)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU v hv
  have hq : ∀ i, ∃ r : ℚ, v i < r ∧ (r : ℝ) < v i + ε := fun i => exists_rat_btwn (by linarith)
  choose q hq1 hq2 using hq
  refine ⟨q, hball ?_, fun i => (hq1 i).le⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hq1 i, hq2 i]

theorem soUsConv_exists_rat_le {m : ℕ} {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    {v : Fin m → ℝ} (hv : v ∈ U) :
    ∃ q : Fin m → ℚ, (fun i => (q i : ℝ)) ∈ U ∧ (fun i => (q i : ℝ)) ≤ v := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU v hv
  have hq : ∀ i, ∃ r : ℚ, v i - ε < r ∧ (r : ℝ) < v i := fun i => exists_rat_btwn (by linarith)
  choose q hq1 hq2 using hq
  refine ⟨q, hball ?_, fun i => (hq2 i).le⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hq1 i, hq2 i]

theorem soUsConv_core {m : ℕ} (PX PY : Fin m → Measure ℝ) [∀ i, IsProbabilityMeasure (PX i)]
    [∀ i, IsProbabilityMeasure (PY i)] (hord : ∀ i x, PX i (Ioi x) ≤ PY i (Ioi x))
    (A : Set (Fin m → ℝ)) (hA : IsUpperSet A) :
    ∃ B2 B1 : Set (Fin m → ℝ), MeasurableSet B2 ∧ MeasurableSet B1 ∧ A ⊆ B2 ∧ B1 ⊆ A ∧
      Measure.pi PX B2 ≤ Measure.pi PY B1 := by
  classical
  set I : Set (Fin m → ℝ) := Set.univ.pi (fun _ => Ioo (0:ℝ) 1) with hIdef
  have hIopen : IsOpen I := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have hImeas : MeasurableSet I := MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
  set L : Measure (Fin m → ℝ) :=
    Measure.pi (fun _ : Fin m => volume.restrict (Ioo (0:ℝ) 1)) with hLdef
  have hLvol : L = volume.restrict I := by
    rw [hLdef, hIdef, volume_pi, Measure.restrict_pi_pi]
  have hLIc : L Iᶜ = 0 := by
    rw [hLvol, Measure.restrict_apply' hImeas, compl_inter_self, measure_empty]
  have hLnull : ∀ S, volume S = 0 → L S = 0 := by
    intro S hS
    rw [hLvol]
    exact nonpos_iff_eq_zero.mp (le_trans (Measure.restrict_apply_le _ _) hS.le)
  set g : (Fin m → ℝ) → (Fin m → ℝ) := fun u i => soUsConv_Q (PX i) (u i) with hgdef
  set h : (Fin m → ℝ) → (Fin m → ℝ) := fun u i => soUsConv_Q (PY i) (u i) with hhdef
  have hgmap : L.map g = Measure.pi PX := by
    rw [hLdef, hgdef, Measure.pi_map_pi (fun i => soUsConv_Q_ae (PX i))]
    congr 1
    funext i
    exact soUsConv_map_Q (PX i)
  have hhmap : L.map h = Measure.pi PY := by
    rw [hLdef, hhdef, Measure.pi_map_pi (fun i => soUsConv_Q_ae (PY i))]
    congr 1
    funext i
    exact soUsConv_map_Q (PY i)
  have hgae : AEMeasurable g L := by
    rw [hLdef]
    exact aemeasurable_pi_lambda _ fun i =>
      (soUsConv_Q_ae (PX i)).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
  have hhae : AEMeasurable h L := by
    rw [hLdef]
    exact aemeasurable_pi_lambda _ fun i =>
      (soUsConv_Q_ae (PY i)).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
  have hgmono : ∀ v w, v ∈ I → w ∈ I → v ≤ w → g v ≤ g w := fun v w hv hw hvw i =>
    soUsConv_Q_mono (PX i) (hv i (mem_univ i)) (hw i (mem_univ i)) (hvw i)
  have hhmono : ∀ v w, v ∈ I → w ∈ I → v ≤ w → h v ≤ h w := fun v w hv hw hvw i =>
    soUsConv_Q_mono (PY i) (hv i (mem_univ i)) (hw i (mem_univ i)) (hvw i)
  have hgh : ∀ v, v ∈ I → g v ≤ h v := fun v hv i =>
    soUsConv_Q_le_Q (hord i) (hv i (mem_univ i))
  set C : Set (Fin m → ℝ) := {u | ∃ v ∈ I, v ≤ u ∧ g v ∈ A} with hCdef
  set D : Set (Fin m → ℝ) := {u | ∃ v ∈ I, v ≤ u ∧ h v ∈ A} with hDdef
  have hCD : C ⊆ D := fun u ⟨v, hv, hvu, hgv⟩ => ⟨v, hv, hvu, hA (hgh v hv) hgv⟩
  have hDup : IsUpperSet D := fun a b hab ⟨v, hv, hva, hhv⟩ => ⟨v, hv, hva.trans hab, hhv⟩
  set qr : (Fin m → ℚ) → (Fin m → ℝ) := fun q i => (q i : ℝ) with hqrdef
  set S2 : Set (Fin m → ℚ) := {q | qr q ∈ I ∧ g (qr q) ∉ A} with hS2def
  set S1 : Set (Fin m → ℚ) := {q | qr q ∈ I ∧ h (qr q) ∈ A} with hS1def
  have hB2meas : MeasurableSet (⋃ q ∈ S2, Iic (g (qr q)))ᶜ :=
    (MeasurableSet.biUnion S2.to_countable (fun q _ => isClosed_Iic.measurableSet)).compl
  have hB1meas : MeasurableSet (⋃ q ∈ S1, Ici (h (qr q))) :=
    MeasurableSet.biUnion S1.to_countable (fun q _ => isClosed_Ici.measurableSet)
  refine ⟨(⋃ q ∈ S2, Iic (g (qr q)))ᶜ, ⋃ q ∈ S1, Ici (h (qr q)), hB2meas, hB1meas, ?_, ?_, ?_⟩
  · intro x hx hmem
    simp only [mem_iUnion] at hmem
    obtain ⟨q, hq, hxq⟩ := hmem
    exact hq.2 (hA hxq hx)
  · intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨q, hq, hxq⟩ := hx
    exact hA hxq hq.2
  · have hsub2 : g ⁻¹' (⋃ q ∈ S2, Iic (g (qr q)))ᶜ ⊆ closure C ∪ Iᶜ := by
      intro v hv
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
      obtain ⟨hvC, hvI⟩ := hcon
      obtain ⟨q, hqU, hvq⟩ :=
        soUsConv_exists_rat_ge (hIopen.inter isClosed_closure.isOpen_compl) ⟨hvI, hvC⟩
      apply hv
      simp only [mem_iUnion]
      exact ⟨q, ⟨hqU.1, fun hgq => hqU.2 (subset_closure ⟨qr q, hqU.1, le_rfl, hgq⟩)⟩,
        hgmono v (qr q) hvI hqU.1 hvq⟩
    have hsub1 : interior D ⊆ h ⁻¹' (⋃ q ∈ S1, Ici (h (qr q))) ∪ Iᶜ := by
      intro v hv
      by_cases hvI : v ∈ I
      · left
        obtain ⟨q, hqU, hqv⟩ := soUsConv_exists_rat_le (isOpen_interior.inter hIopen) ⟨hv, hvI⟩
        obtain ⟨w, hw, hwq, hhw⟩ := interior_subset hqU.1
        simp only [mem_preimage, mem_iUnion]
        exact ⟨q, ⟨hqU.2, hA (hhmono w (qr q) hw hqU.2 hwq) hhw⟩, hhmono (qr q) v hqU.2 hvI hqv⟩
      · right
        exact hvI
    have hfr : L (frontier D) = 0 := hLnull _ hDup.null_frontier
    calc Measure.pi PX (⋃ q ∈ S2, Iic (g (qr q)))ᶜ
        = L (g ⁻¹' (⋃ q ∈ S2, Iic (g (qr q)))ᶜ) := by
          rw [← hgmap, Measure.map_apply_of_aemeasurable hgae hB2meas]
      _ ≤ L (closure C ∪ Iᶜ) := measure_mono hsub2
      _ ≤ L (closure C) + L Iᶜ := measure_union_le _ _
      _ = L (closure C) := by rw [hLIc, add_zero]
      _ ≤ L (closure D) := measure_mono (closure_mono hCD)
      _ ≤ L (interior D ∪ frontier D) := by
          apply measure_mono
          intro x hx
          by_cases hxi : x ∈ interior D
          · exact Or.inl hxi
          · exact Or.inr ⟨hx, hxi⟩
      _ ≤ L (interior D) + L (frontier D) := measure_union_le _ _
      _ = L (interior D) := by rw [hfr, add_zero]
      _ ≤ L (h ⁻¹' (⋃ q ∈ S1, Ici (h (qr q))) ∪ Iᶜ) := measure_mono hsub1
      _ ≤ L (h ⁻¹' (⋃ q ∈ S1, Ici (h (qr q)))) + L Iᶜ := measure_union_le _ _
      _ = Measure.pi PY (⋃ q ∈ S1, Ici (h (qr q))) := by
          rw [hLIc, add_zero, ← hhmap, Measure.map_apply_of_aemeasurable hhae hB1meas]

open MeasureTheory ProbabilityTheory StochasticOrders.Usual in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, UsualOrder μ ν (X i) (Y i)) (ψ : (Fin m → ℝ) → ℝ) (hψ : Monotone ψ) :
    UsualOrder μ ν (fun ω => ψ (fun i => X i ω)) (fun ω => ψ (fun i => Y i ω)) := by
  intro t
  have : ∀ i, IsProbabilityMeasure (μ.map (X i)) := fun i =>
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have : ∀ i, IsProbabilityMeasure (ν.map (Y i)) := fun i =>
    Measure.isProbabilityMeasure_map (hY i).aemeasurable
  have hordP : ∀ i x, μ.map (X i) (Set.Ioi x) ≤ ν.map (Y i) (Set.Ioi x) := by
    intro i x
    rw [Measure.map_apply (hX i) measurableSet_Ioi, Measure.map_apply (hY i) measurableSet_Ioi]
    exact hord i x
  have hAup : IsUpperSet {x : Fin m → ℝ | t < ψ x} := fun a b hab ha =>
    lt_of_lt_of_le ha (hψ hab)
  obtain ⟨B2, B1, hB2, hB1, hAB2, hB1A, hle⟩ :=
    soUsConv_core (fun i => μ.map (X i)) (fun i => ν.map (Y i)) hordP _ hAup
  have hXm : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ hX
  have hYm : Measurable (fun ω i => Y i ω) := measurable_pi_lambda _ hY
  calc μ {ω | t < ψ (fun i => X i ω)} ≤ μ ((fun ω i => X i ω) ⁻¹' B2) :=
        measure_mono (fun ω hω => hAB2 hω)
    _ = Measure.pi (fun i => μ.map (X i)) B2 := by
        rw [← hXindep.map_fun_eq_pi_map (fun i => (hX i).aemeasurable), Measure.map_apply hXm hB2]
    _ ≤ Measure.pi (fun i => ν.map (Y i)) B1 := hle
    _ = ν ((fun ω i => Y i ω) ⁻¹' B1) := by
        rw [← hYindep.map_fun_eq_pi_map (fun i => (hY i).aemeasurable), Measure.map_apply hYm hB1]
    _ ≤ ν {ω | t < ψ (fun i => Y i ω)} := measure_mono (fun ω hω => hB1A hω)

