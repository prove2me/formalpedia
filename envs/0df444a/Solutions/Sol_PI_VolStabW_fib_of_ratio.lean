-- Prove2me | solution 1 for PI.VolStabW.fib_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:52.731731+00:00
-- url     : https://prove2.me/submissions/ccbfe75d-e238-43c4-a286-3749de8f79c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCountHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
namespace PI.VolStabW
theorem _root_.solution (μ : Measure V) (ν : Measure X) [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (hNbU : ∀ x, G x ∈ Nb → x ∈ U) (Q : Set V) (hQo : IsOpen Q) (hQcl : IsClosed Q)
    (hQc : IsCompact Q) (H : ℕ → AddSubgroup X) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (κ : ℝ) (hratio : ∀ n, μ.real (Q ∩ G ⁻¹' {z | z - T ∈ H n}) = κ * ν.real (H n)) :
    ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) = (κ : ℂ) := by
  obtain ⟨hconc, hdis, hcont⟩ := hfib
  have hpre : ∀ b, f ⁻¹' {ι b} = G ⁻¹' {b} := by
    intro b
    ext x
    simp [hfG, hι.eq_iff]
  set S : ℕ → Set X := fun n => {z | z - T ∈ H n} with hSdef
  set P : ℕ → Set V := fun n => Q ∩ G ⁻¹' S n with hPdef
  have hSo : ∀ n, IsOpen (S n) := fun n => (hHo n).preimage (continuous_id.sub continuous_const)
  have hScl : ∀ n, IsClosed (S n) := fun n =>
    (AddSubgroup.isClosed_of_isOpen _ (hHo n)).preimage (continuous_id.sub continuous_const)
  have hSeq : ∀ n, S n = (fun w => w + -T) ⁻¹' (H n : Set X) := by
    intro n
    ext z
    simp [hSdef, sub_eq_add_neg]
  have hSc : ∀ n, IsCompact (S n) := by
    intro n
    have : S n = (fun w => w + T) '' (H n : Set X) := by
      ext z
      simp only [hSdef, mem_setOf_eq, mem_image, SetLike.mem_coe]
      constructor
      · intro hz
        exact ⟨z - T, hz, by abel⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [this]
    exact (hHc n).image (continuous_id.add continuous_const)
  have hνS : ∀ n, ν (S n) = ν (H n) := by
    intro n
    rw [hSeq, measure_preimage_add_right]
  have hPcl : ∀ n, IsClosed (P n) := fun n => hQcl.inter ((hScl n).preimage hGc)
  have hPo : ∀ n, IsOpen (P n) := fun n => hQo.inter ((hSo n).preimage hGc)
  have hPc : ∀ n, IsCompact (P n) := fun n => hQc.of_isClosed_subset (hPcl n) inter_subset_left
  have hPm : ∀ n, MeasurableSet (P n) := fun n => (hPo n).measurableSet

  have hO : (fun w : X => T + w) ⁻¹' (Nb ∩ B) ∈ 𝓝 (0 : X) := by
    have hc : Continuous fun w : X => T + w := continuous_const.add continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using inter_mem hNb hB)
  obtain ⟨k, hk⟩ := hHb _ hO
  have hSk : ∀ z ∈ S k, z ∈ Nb ∩ B := by
    intro z hz
    have := hk hz
    simpa using this
  have hPkU : P k ⊆ U := fun x hx => hNbU x (hSk _ hx.2).1
  set φ : V → ℝ := (P k).indicator (fun _ => (1 : ℝ)) with hφdef
  have hφc : Continuous φ :=
    (LocallyConstant.indicator (LocallyConstant.const V (1 : ℝ))
      ⟨hPcl k, hPo k⟩).isLocallyConstant.continuous
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro' (hPc k) (hPcl k) fun x hx => indicator_of_notMem hx _
  have hφU : tsupport φ ⊆ U :=
    (closure_minimal Set.support_indicator_subset (hPcl k)).trans hPkU
  obtain ⟨hint, hΦc⟩ := hcont φ hφc hφs hφU
  set Φ : X → ℝ := fun b => ∫ x, φ x ∂(fib b) with hΦdef
  have hΦval : ∀ b, Φ b = (fib b).real (P k) := fun b => integral_indicator_one (hPm k)
  have hfin : ∀ b ∈ B, fib b (P k) ≠ ⊤ := by
    intro b hb
    have h := hint b hb
    rw [hφdef, integrable_indicator_iff (hPm k)] at h
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne

  have hcon : ∀ b (A : Set V), fib b A = fib b (A ∩ (G ⁻¹' {b} ∩ U)) := by
    intro b A
    rw [measure_inter_conull]
    rw [← hpre]
    exact hconc b
  have hPn : ∀ n, (H n : Set X) ⊆ H k → ∀ b, fib b (P n) = (S n).indicator (fun b => fib b (P k)) b := by
    intro n hn b
    by_cases hb : b ∈ S n
    · rw [indicator_of_mem hb, hcon b (P n), hcon b (P k)]
      congr 1
      ext x
      constructor
      · rintro ⟨⟨hxQ, _⟩, hxb, hxU⟩
        have hxb' : G x = b := hxb
        refine ⟨⟨hxQ, ?_⟩, hxb, hxU⟩
        show G x ∈ S k
        rw [hxb']
        exact hn hb
      · rintro ⟨⟨hxQ, _⟩, hxb, hxU⟩
        have hxb' : G x = b := hxb
        refine ⟨⟨hxQ, ?_⟩, hxb, hxU⟩
        show G x ∈ S n
        rw [hxb']
        exact hb
    · rw [indicator_of_notMem hb, hcon b (P n)]
      convert measure_empty (μ := fib b)
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      obtain ⟨⟨_, hxS⟩, hxb, _⟩ := hx
      have hxb' : G x = b := hxb
      have hxS' : G x ∈ S n := hxS
      rw [hxb'] at hxS'
      exact hb hxS'

  have hstep : ∀ n, (H n : Set X) ⊆ H k → μ.real (P n) = ∫ b in S n, Φ b ∂ν := by
    intro n hn
    have hSnk : S n ⊆ S k := fun z hz => hn hz
    have hΦon : ContinuousOn Φ (S n) := hΦc.mono fun z hz => (hSk z (hSnk hz)).2
    have hΦint : IntegrableOn Φ (S n) ν := hΦon.integrableOn_compact (hSc n)
    have hΦnn : ∀ b, 0 ≤ Φ b := fun b => integral_nonneg fun x => by
      simp only [hφdef]
      exact indicator_nonneg (fun _ _ => zero_le_one) x
    have h1 : μ (P n) = ∫⁻ b in S n, ENNReal.ofReal (Φ b) ∂ν := by
      have hU : μ (P n) = ∫⁻ x in U, (P n).indicator 1 x ∂μ := by
        rw [lintegral_indicator_one (hPm n), Measure.restrict_apply (hPm n),
          inter_eq_left.2 (fun x hx => hPkU ⟨hx.1, hn hx.2⟩)]
      rw [hU, hdis ((P n).indicator 1) (measurable_one.indicator (hPm n))]
      simp_rw [lintegral_indicator_one (hPm n)]
      rw [← lintegral_indicator (hSo n).measurableSet]
      refine lintegral_congr fun b => ?_
      rw [hPn n hn b]
      by_cases hb : b ∈ S n
      · rw [indicator_of_mem hb, indicator_of_mem hb, hΦval, measureReal_def,
          ENNReal.ofReal_toReal (hfin b (hSk b (hSnk hb)).2)]
      · rw [indicator_of_notMem hb, indicator_of_notMem hb]
    rw [measureReal_def, h1, ← ofReal_integral_eq_lintegral_ofReal hΦint
      (Eventually.of_forall hΦnn), ENNReal.toReal_ofReal (setIntegral_nonneg
        (hSo n).measurableSet fun b _ => hΦnn b)]

  have hνpos : ∀ n, 0 < ν.real (H n) := by
    intro n
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo n).measure_pos ν ⟨0, (H n).zero_mem⟩).ne'
      (hHc n).measure_lt_top.ne
  have hκ : κ = Φ T := by
    have hΦT : ContinuousAt Φ T := hΦc.continuousAt hB
    refine eq_of_forall_dist_le fun ε hε => ?_
    have hev : ∀ᶠ b in 𝓝 T, dist (Φ b) (Φ T) < ε := hΦT.eventually (Metric.ball_mem_nhds _ hε)
    have hO' : (fun w : X => T + w) ⁻¹' {b | dist (Φ b) (Φ T) < ε} ∩ (H k : Set X) ∈ 𝓝 (0 : X) := by
      have hc : Continuous fun w : X => T + w := continuous_const.add continuous_id
      refine inter_mem (hc.continuousAt.preimage_mem_nhds (by show _ ∈ 𝓝 (T + 0); rw [add_zero]; exact hev)) ?_
      exact (hHo k).mem_nhds (H k).zero_mem
    obtain ⟨n, hn⟩ := hHb _ hO'
    have hnk : (H n : Set X) ⊆ H k := fun z hz => (hn hz).2
    have hclose : ∀ b ∈ S n, ‖Φ b - Φ T‖ ≤ ε := by
      intro b hb
      have := (hn hb).1
      simp only [mem_preimage, mem_setOf_eq, add_sub_cancel] at this
      rw [← dist_eq_norm]
      exact this.le
    have hΦint : IntegrableOn Φ (S n) ν :=
      (hΦc.mono fun z hz => (hSk z (hnk hz)).2).integrableOn_compact (hSc n)
    have hbound := norm_setIntegral_le_of_norm_le_const (μ := ν) (hSc n).measure_lt_top hclose
    rw [integral_sub hΦint (integrableOn_const (hSc n).measure_lt_top.ne), setIntegral_const,
      ← hstep n hnk, hratio n, smul_eq_mul] at hbound
    have hνSn : ν.real (S n) = ν.real (H n) := by rw [measureReal_def, measureReal_def, hνS]
    rw [hνSn, mul_comm (ν.real (H n : Set X)) (Φ T), ← sub_mul, norm_mul,
      Real.norm_of_nonneg (hνpos n).le] at hbound
    rw [Real.dist_eq, ← Real.norm_eq_abs]
    exact le_of_mul_le_mul_right hbound (hνpos n)

  have hT : T ∈ S k := by simp [hSdef, (H k).zero_mem]
  have hae : ∀ᵐ x ∂(fib T), Q.indicator (1 : V → ℂ) x = ((φ x : ℝ) : ℂ) := by
    have hm : G ⁻¹' {T} ∩ U ∈ ae (fib T) := by
      rw [mem_ae_iff, ← hpre]
      exact hconc T
    filter_upwards [hm] with x hx
    have hxT : G x = T := hx.1
    by_cases hxQ : x ∈ Q
    · have hxP : x ∈ P k := ⟨hxQ, by simp only [mem_preimage, hxT]; exact hT⟩
      simp [hφdef, indicator_of_mem hxQ, indicator_of_mem hxP]
    · have hxP : x ∉ P k := fun h => hxQ h.1
      simp [hφdef, indicator_of_notMem hxQ, indicator_of_notMem hxP]
  rw [integral_congr_ae hae, integral_complex_ofReal, hκ]
end PI.VolStabW
