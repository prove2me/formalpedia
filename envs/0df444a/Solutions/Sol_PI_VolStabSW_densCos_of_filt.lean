-- Prove2me | solution 1 for PI.VolStabSW.densCos_of_filt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:43:28.008908+00:00
-- url     : https://prove2.me/submissions/6e79c4b0-7a67-4d7e-92b3-0865394a1ca7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HenselCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGlue
import Theorems.Thm_PI_VolStabSW_HasDens_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology Set
namespace PI.VolStabSW
theorem _root_.solution (hP1 : HenselCount) (hP2 : CosDens) {V X Y : Type} [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X)
    (hG : Continuous G) (hfG : ∀ v, f v = ι (G v)) (y : V) (Λ : ℕ → AddSubgroup V)
    (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V)) (hΛc : ∀ n, IsCompact (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (hHb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n)
    (hyp : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ 0}.indicator (fun _ => (1 : ℝ)) v ∂μ =
        ∫ b in S, g b ∂ν := by
  classical
  have hHa : Antitone H := by
    intro a b hab
    rw [← hD a, ← hD b]
    exact AddSubgroup.map_mono (hΛa hab)
  have hΦ : Continuous (fun Z : V => G (y + Z)) := hG.comp (continuous_const.add continuous_id)
  have hΦm : Measurable (fun Z : V => G (y + Z)) := hΦ.measurable
  have hΛ0m : MeasurableSet (Λ 0 : Set V) := (hΛo 0).measurableSet
  set m : Measure X := (μ.restrict (Λ 0 : Set V)).map (fun Z : V => G (y + Z)) with hm
  haveI : IsFiniteMeasure (μ.restrict (Λ 0 : Set V)) :=
    isFiniteMeasure_restrict.mpr (hΛc 0).measure_lt_top.ne
  haveI : IsFiniteMeasure m := by rw [hm]; infer_instance
  have hmT : ∀ T : Set X, MeasurableSet T → m T = μ {Z | Z ∈ Λ 0 ∧ G (y + Z) ∈ T} := by
    intro T hT
    rw [hm, Measure.map_apply hΦm hT, Measure.restrict_apply' hΛ0m]
    congr 1
    ext Z
    simp [and_comm]
  have hopen : ∀ (h : X) (k : ℕ), IsOpen {z : X | z - h ∈ H k} := fun h k =>
    (hHo k).preimage (continuous_sub_right h)
  have hν0 : ν (H 0 : Set X) ≠ 0 := ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
  have hνt : ν (H 0 : Set X) ≠ ⊤ := (hHc 0).measure_lt_top.ne
  have htrans : ∀ (h : X) (k : ℕ), ν {z : X | z - h ∈ H k} = ν (H k : Set X) := by
    intro h k
    have he : {z : X | z - h ∈ H k} = (fun z => -h + z) ⁻¹' (H k : Set X) := by
      ext z
      simp [sub_eq_neg_add]
    rw [he, measure_preimage_add]
  set κ : ENNReal := μ (Λ 0 : Set V) / ν (H 0 : Set X) with hκ
  have hdens : ∀ k (h : X), h - G y ∈ H 0 →
      m {z | z - h ∈ H k} = κ * ν {z | z - h ∈ H k} := by
    intro k h hh
    have hH := hP1 V X μ ν inferInstance inferInstance Λ H hΛo hΛc hΛa hHo hHc D hD G y hyp k h hh
    rw [hmT _ (hopen h k).measurableSet, htrans, hκ, div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv, ENNReal.eq_div_iff hν0 hνt, mul_comm]
    exact hH
  have hcompl : m {z | z - G y ∈ H 0}ᶜ = 0 := by
    rw [hmT _ (hopen (G y) 0).measurableSet.compl]
    convert measure_empty (μ := μ)
    ext Z
    constructor
    · rintro ⟨hZ, hZ'⟩
      have h1 := hyp 0 0 (Λ 0).zero_mem Z hZ
      simp only [add_zero, zero_add] at h1
      have h2 : D Z ∈ H 0 := by
        rw [← hD 0]
        exact AddSubgroup.mem_map_of_mem D hZ
      have hmem : G (y + Z) - G y ∈ H 0 := by
        simpa using (H 0).add_mem (hHa (Nat.zero_le 1) h1) h2
      exact hZ' hmem
    · intro hZ
      exact False.elim hZ
  have hcos := hP2 X ν m inferInstance H hHo hHc hHa hHb (G y) κ hcompl hdens
  set C : Set X := {z | z - G y ∈ H 0} with hC
  have hCo : IsOpen C := hopen (G y) 0
  have hCc : IsClosed C := (hHc 0).isClosed.preimage (continuous_sub_right (G y))
  refine ⟨C.indicator (fun _ => κ.toReal), ?_, ?_⟩
  · refine continuous_indicator ?_ continuousOn_const
    intro a ha
    rw [hCc.frontier_eq, hCo.interior_eq, Set.diff_self] at ha
    simp at ha
  · intro S hS
    have hSm : MeasurableSet S := hS.isClosed.measurableSet
    have hpre : f ⁻¹' (ι '' S) = G ⁻¹' S := by
      ext v
      simp [hfG, hι.mem_set_image]
    have hCV : MeasurableSet {z : V | z - y ∈ Λ 0} :=
      ((hΛo 0).preimage (continuous_sub_right y)).measurableSet
    have key : m S = μ ({z : V | z - y ∈ Λ 0} ∩ G ⁻¹' S) := by
      rw [hmT S hSm, ← measure_preimage_add μ y ({z : V | z - y ∈ Λ 0} ∩ G ⁻¹' S)]
      congr 1
      ext Z
      simp
    rw [hpre, integral_indicator_const _ hCV, integral_indicator_const _ hCo.measurableSet]
    simp only [Measure.real, smul_eq_mul, mul_one]
    rw [Measure.restrict_apply hCV, Measure.restrict_apply hCo.measurableSet, ← key, hcos S hS,
      ENNReal.toReal_mul, Set.inter_comm, mul_comm]
end PI.VolStabSW
