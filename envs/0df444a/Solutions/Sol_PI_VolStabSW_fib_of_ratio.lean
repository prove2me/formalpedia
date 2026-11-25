-- Prove2me | solution 1 for PI.VolStabSW.fib_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:36.838821+00:00
-- url     : https://prove2.me/submissions/d2953314-9d3d-43a2-b7e5-debadc04b649

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HenselCountHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabSW
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Core
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
private lemma module_finite_F_E {W : Type} [MeasurableSpace W] (m : Measure W) (s : Set W)
    (hs : MeasurableSet s) (h : Integrable (s.indicator (1 : W → ℝ)) m) : m s ≠ ⊤ := by
  have h1 := h.lintegral_lt_top
  have e : (fun x => ENNReal.ofReal (s.indicator (1 : W → ℝ) x)) = s.indicator 1 := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [e, lintegral_indicator_one hs] at h1
  exact h1.ne
end Core
section Lat
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
end Lat
section Fin
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
end Fin
end PI.VolStabSW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
namespace PI.VolStabSW
theorem _root_.solution (μ : Measure V) (ν : Measure X) [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (hNbU : ∀ x, G x ∈ Nb → x ∈ U) (Q : Set V) (hQo : IsOpen Q) (hQcl : IsClosed Q)
    (hQc : IsCompact Q) (H : ℕ → AddSubgroup X) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (κ : ℝ) (hratio : ∀ n, μ.real (Q ∩ G ⁻¹' {z | z - T ∈ H n}) = κ * ν.real (H n)) :
    ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) = (κ : ℂ) := by
  classical
  obtain ⟨hconc, hdis, hcont⟩ := hfib
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Set X, S = fun n => {z | z - T ∈ H n} := ⟨_, rfl⟩
  have hmemS : ∀ n z, z ∈ S n ↔ z - T ∈ H n := by
    intro n z
    rw [hSdef]
    rfl
  have hSo : ∀ n, IsOpen (S n) := by
    intro n
    rw [hSdef]
    exact (hHo n).preimage (continuous_id.sub continuous_const)
  have hScl : ∀ n, IsClosed (S n) := by
    intro n
    rw [hSdef]
    exact (AddSubgroup.isClosed_of_isOpen (H n) (hHo n)).preimage
      (continuous_id.sub continuous_const)
  have hSm : ∀ n, MeasurableSet (S n) := fun n => (hSo n).measurableSet
  have hSc : ∀ n, IsCompact (S n) := by
    intro n
    have e : S n = (fun z => z + T) '' (H n : Set X) := by
      ext z
      constructor
      · intro hz
        exact ⟨z - T, (hmemS n z).1 hz, sub_add_cancel z T⟩
      · rintro ⟨w, hw, rfl⟩
        rw [hmemS]
        simpa using hw
    rw [e]
    exact (hHc n).image (continuous_add_right T)
  have hνS : ∀ n, ν (S n) = ν (H n) := by
    intro n
    have e : S n = (fun z => -T + z) ⁻¹' (H n : Set X) := by
      ext z
      rw [hmemS]
      simp [neg_add_eq_sub]
    rw [e]
    exact measure_preimage_add ν (-T) (H n : Set X)
  have hTS : ∀ n, T ∈ S n := fun n => (hmemS n T).2 (by rw [sub_self]; exact (H n).zero_mem)
  have hsmall : ∀ N ∈ 𝓝 T, ∃ n, S n ⊆ N := by
    intro N hN
    have h0 : (fun x : X => T + x) ⁻¹' N ∈ 𝓝 (0 : X) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
    obtain ⟨n, hn⟩ := hHb _ h0
    refine ⟨n, fun z hz => ?_⟩
    have h := hn ((hmemS n z).1 hz)
    simpa using h
  obtain ⟨n₀, hn₀⟩ := hsmall (Nb ∩ B) (Filter.inter_mem hNb hB)
  have hQ'o : IsOpen (Q ∩ G ⁻¹' S n₀) := hQo.inter ((hSo n₀).preimage hGc)
  have hQ'cl : IsClosed (Q ∩ G ⁻¹' S n₀) := hQcl.inter ((hScl n₀).preimage hGc)
  have hQ'c : IsCompact (Q ∩ G ⁻¹' S n₀) := hQc.of_isClosed_subset hQ'cl Set.inter_subset_left
  have hQ'm : MeasurableSet (Q ∩ G ⁻¹' S n₀) := hQ'o.measurableSet
  have hQ'U : Q ∩ G ⁻¹' S n₀ ⊆ U := fun x hx => hNbU x (hn₀ hx.2).1
  have hS0B : S n₀ ⊆ B := fun z hz => (hn₀ hz).2
  have hfr : frontier (Q ∩ G ⁻¹' S n₀) = ∅ := by
    rw [frontier, hQ'cl.closure_eq, hQ'o.interior_eq, Set.diff_self]
  have hφc : Continuous ((Q ∩ G ⁻¹' S n₀).indicator (1 : V → ℝ)) := by
    rw [← Set.piecewise_eq_indicator]
    exact continuous_one.piecewise (fun a ha => by rw [hfr] at ha; simp at ha) continuous_zero
  have hts : tsupport ((Q ∩ G ⁻¹' S n₀).indicator (1 : V → ℝ)) ⊆ Q ∩ G ⁻¹' S n₀ :=
    closure_minimal Set.support_indicator_subset hQ'cl
  have hφcs : HasCompactSupport ((Q ∩ G ⁻¹' S n₀).indicator (1 : V → ℝ)) :=
    hQ'c.of_isClosed_subset (isClosed_tsupport _) hts
  obtain ⟨hint, hFc0⟩ := hcont _ hφc hφcs (hts.trans hQ'U)
  obtain ⟨F, hFdef⟩ : ∃ F : X → ℝ,
      F = fun b => ∫ v, (Q ∩ G ⁻¹' S n₀).indicator (1 : V → ℝ) v ∂(fib b) := ⟨_, rfl⟩
  have hFc : ContinuousOn F B := by
    rw [hFdef]
    exact hFc0
  have hFval : ∀ b, F b = (fib b (Q ∩ G ⁻¹' S n₀)).toReal := by
    intro b
    simp only [hFdef]
    rw [integral_indicator_one hQ'm, measureReal_def]
  have hF0 : ∀ b, 0 ≤ F b := fun b => by
    rw [hFval]
    exact ENNReal.toReal_nonneg
  have hGb : ∀ b x, x ∈ f ⁻¹' {ι b} ∩ U → G x = b := fun b x hx =>
    hι ((hfG x).symm.trans (Set.mem_singleton_iff.1 hx.1))
  have hfibS : ∀ b (R : Set V), fib b R = fib b (R ∩ (f ⁻¹' {ι b} ∩ U)) :=
    fun b R => (measure_inter_conull (hconc b)).symm
  have hcut : ∀ b m, b ∈ S m →
      (Q ∩ G ⁻¹' S m) ∩ (f ⁻¹' {ι b} ∩ U) = Q ∩ (f ⁻¹' {ι b} ∩ U) := by
    intro b m hb
    ext x
    constructor
    · rintro ⟨⟨hxQ, _⟩, hxA⟩
      exact ⟨hxQ, hxA⟩
    · rintro ⟨hxQ, hxA⟩
      refine ⟨⟨hxQ, ?_⟩, hxA⟩
      show G x ∈ S m
      rw [hGb b x hxA]
      exact hb
  have hfin : ∀ b ∈ B, fib b (Q ∩ G ⁻¹' S n₀) ≠ ⊤ := fun b hb => module_finite_F_E (fib b) _ hQ'm (hint b hb)
  have hmain : ∀ n, S n ⊆ S n₀ → ∫ b in S n, F b ∂ν = κ * ν.real (H n) := by
    intro n hn
    have hSvm : MeasurableSet (Q ∩ G ⁻¹' S n) := (hQo.inter ((hSo n).preimage hGc)).measurableSet
    have hSvU : Q ∩ G ⁻¹' S n ⊆ U := fun x hx => hQ'U ⟨hx.1, hn hx.2⟩
    have h1 := hdis ((Q ∩ G ⁻¹' S n).indicator 1) (measurable_one.indicator hSvm)
    rw [lintegral_indicator_one hSvm, Measure.restrict_apply hSvm, Set.inter_eq_left.2 hSvU] at h1
    simp_rw [lintegral_indicator_one hSvm] at h1
    have hpt : ∀ b, fib b (Q ∩ G ⁻¹' S n) =
        (S n).indicator (fun b => ENNReal.ofReal (F b)) b := by
      intro b
      simp only [Set.indicator_apply]
      split_ifs with hb
      · rw [hfibS b, hcut b n hb, ← hcut b n₀ (hn hb), ← hfibS b, hFval,
          ENNReal.ofReal_toReal (hfin b (hS0B (hn hb)))]
      · rw [hfibS b]
        have e : (Q ∩ G ⁻¹' S n) ∩ (f ⁻¹' {ι b} ∩ U) = ∅ := Set.subset_empty_iff.1 fun x hx =>
          hb (by rw [← hGb b x hx.2]; exact hx.1.2)
        rw [e, measure_empty]
    have h2 : μ (Q ∩ G ⁻¹' S n) = ∫⁻ b in S n, ENNReal.ofReal (F b) ∂ν := by
      rw [h1, lintegral_congr hpt, lintegral_indicator (hSm n)]
    have hFint : IntegrableOn F (S n) ν :=
      (hFc.mono fun z hz => hS0B (hn hz)).integrableOn_compact (hSc n)
    rw [← ofReal_integral_eq_lintegral_ofReal hFint (ae_of_all _ hF0)] at h2
    have hr : μ.real (Q ∩ G ⁻¹' S n) = κ * ν.real (H n) := by
      rw [hSdef]
      exact hratio n
    rw [measureReal_def, h2, ENNReal.toReal_ofReal (integral_nonneg hF0)] at hr
    exact hr
  have hcT : ContinuousAt F T := hFc.continuousAt hB
  have hrpos : ∀ n, 0 < ν.real (H n) := by
    intro n
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo n).measure_ne_zero ν ⟨0, (H n).zero_mem⟩)
      (hHc n).measure_lt_top.ne
  have key : ∀ ε > 0, |κ - F T| ≤ ε := by
    intro ε hε
    have hW : F ⁻¹' Metric.ball (F T) ε ∈ 𝓝 T := hcT (Metric.ball_mem_nhds _ hε)
    obtain ⟨n, hnW⟩ := hsmall _ (Filter.inter_mem hW ((hSo n₀).mem_nhds (hTS n₀)))
    have hsub : S n ⊆ S n₀ := fun z hz => (hnW hz).2
    have hI := hmain n hsub
    have hFint : IntegrableOn F (S n) ν :=
      (hFc.mono fun z hz => hS0B (hsub hz)).integrableOn_compact (hSc n)
    have hclose : ∀ b ∈ S n, |F b - F T| < ε := fun b hb => by
      have h := (hnW hb).1
      rwa [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at h
    have hup : ∫ b in S n, F b ∂ν ≤ ∫ b in S n, (F T + ε) ∂ν :=
      setIntegral_mono_on hFint (continuousOn_const.integrableOn_compact (hSc n)) (hSm n)
        fun b hb => by linarith [(abs_sub_lt_iff.1 (hclose b hb)).1]
    have hlo : ∫ b in S n, (F T - ε) ∂ν ≤ ∫ b in S n, F b ∂ν :=
      setIntegral_mono_on (continuousOn_const.integrableOn_compact (hSc n)) hFint (hSm n)
        fun b hb => by linarith [(abs_sub_lt_iff.1 (hclose b hb)).2]
    rw [setIntegral_const, hI] at hup
    rw [setIntegral_const, hI] at hlo
    simp only [smul_eq_mul, measureReal_def, hνS n] at hup hlo
    have hr := hrpos n
    rw [measureReal_def] at hr
    rw [abs_le]
    constructor <;> nlinarith
  have hk : κ = F T := by
    by_contra hne
    have hpos : 0 < |κ - F T| := abs_pos.2 (sub_ne_zero.2 hne)
    have := key (|κ - F T| / 2) (half_pos hpos)
    linarith
  have hQQ : fib T Q = fib T (Q ∩ G ⁻¹' S n₀) := by
    rw [hfibS T (Q ∩ G ⁻¹' S n₀), hcut T n₀ (hTS n₀), ← hfibS T Q]
  have hint' : ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) =
      ∫ x, ((Q.indicator (1 : V → ℝ) x : ℝ) : ℂ) ∂(fib T) :=
    integral_congr_ae (ae_of_all _ fun x => by by_cases hx : x ∈ Q <;> simp [hx])
  rw [hint', integral_complex_ofReal, integral_indicator_one hQo.measurableSet, measureReal_def, hQQ,
    ← hFval, ← hk]
end PI.VolStabSW
