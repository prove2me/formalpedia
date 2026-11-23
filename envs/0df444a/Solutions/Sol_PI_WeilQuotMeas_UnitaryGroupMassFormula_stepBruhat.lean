-- Prove2me | solution 1 for PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:55.978134+00:00
-- url     : https://prove2.me/submissions/1859da3d-d22d-4d42-b9b2-00411e071ae8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_Bruhat
import Theorems.Thm_PI_WeilQuotMeas_UnitaryGroupMassFormula_avg_mul_right
import Theorems.Thm_PI_WeilQuotMeas_UnitaryGroupMassFormula_measurable_avg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
open PI PI.WeilQuotMeas PI.WeilQuotMeas.UnitaryGroupMassFormula
namespace PI.WeilQuotMeas.UnitaryGroupMassFormula
theorem _root_.solution : StepBruhat := by
  intro G _ _ _ _ _ _ _ _ H hH ν hν
  classical
  have : LocallyCompactSpace H := hH.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  obtain ⟨K0, hK0, h1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨d, hd⟩ : ∃ d : ℕ → G, DenseRange d := TopologicalSpace.exists_dense_seq G
  obtain ⟨U, hU⟩ : ∃ U : ℕ → Set G, U = fun n => (fun x => d n * x) '' interior K0 := ⟨_, rfl⟩
  have hUo : ∀ n, IsOpen (U n) := fun n => by
    rw [hU]; exact isOpenMap_mul_left (d n) _ isOpen_interior
  have hUK : ∀ n, U n ⊆ (fun x => d n * x) '' K0 := fun n => by
    rw [hU]; exact Set.image_mono interior_subset
  have hcov : ∀ g : G, ∃ n, g ∈ U n := by
    intro g
    have ho : IsOpen ((fun x => g * x) '' (interior K0)⁻¹) :=
      isOpenMap_mul_left g _ isOpen_interior.inv
    have h1' : (1 : G) ∈ (interior K0)⁻¹ := by
      rw [Set.mem_inv, inv_one]; exact mem_interior_iff_mem_nhds.2 h1
    obtain ⟨n, hn⟩ := hd.exists_mem_open ho ⟨g, 1, h1', mul_one g⟩
    obtain ⟨z, hz, hzn⟩ := hn
    simp only at hzn
    refine ⟨n, ?_⟩
    rw [hU]
    show g ∈ (fun x => d n * x) '' interior K0
    exact ⟨z⁻¹, Set.mem_inv.1 hz, by simp only; rw [← hzn, mul_inv_cancel_right]⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → G → ℝ≥0∞,
      A = fun n g => ∫⁻ h, (U n).indicator 1 (g * (h : G)) ∂ν := ⟨_, rfl⟩
  have hAm : ∀ n, Measurable (A n) := fun n => by
    rw [hA]; exact measurable_avg ν (measurable_one.indicator (hUo n).measurableSet)
  have hAinv : ∀ n g (k : H), A n (g * k) = A n g := fun n g k => by
    rw [hA]; exact avg_mul_right ν _ g k
  have hAeq : ∀ n g, A n g = ν {h : H | g * (h : G) ∈ U n} := fun n g => by
    have hS : MeasurableSet {h : H | g * (h : G) ∈ U n} :=
      (continuous_const.mul continuous_subtype_val).measurable (hUo n).measurableSet
    rw [← lintegral_indicator_one hS, hA]
    rfl
  have hApos : ∀ n g, g ∈ U n → 0 < A n g := fun n g hg => by
    rw [hAeq]
    refine IsOpen.measure_pos ν ((hUo n).preimage (continuous_const.mul continuous_subtype_val))
      ⟨1, ?_⟩
    show g * ((1 : H) : G) ∈ U n
    rw [OneMemClass.coe_one, mul_one]; exact hg
  have hAfin : ∀ n g, A n g < ⊤ := fun n g => by
    rw [hAeq]
    have hKc : IsCompact ((fun x => d n * x) '' K0) := hK0.image (continuous_const_mul (d n))
    have hpre : ∀ S : Set G, (fun x => g * x) ⁻¹' S = (fun x => g⁻¹ * x) '' S := fun S => by
      rw [Set.image_mul_left, inv_inv]
    have hc2 : IsCompact ((fun x => g * x) ⁻¹' ((fun x => d n * x) '' K0)) := by
      rw [hpre]; exact hKc.image (continuous_const_mul g⁻¹)
    have hc3 : IsCompact (Subtype.val ⁻¹' ((fun x => g * x) ⁻¹' ((fun x => d n * x) '' K0)) :
        Set H) := hH.isClosedEmbedding_subtypeVal.isCompact_preimage hc2
    refine lt_of_le_of_lt (measure_mono ?_) hc3.measure_lt_top
    intro h hh
    exact hUK n hh
  have hex : ∀ g, ∃ n, 0 < A n g := fun g => (hcov g).imp fun n hn => hApos n g hn
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : G → ℕ, n₀ = fun g => Nat.find (hex g) := ⟨_, rfl⟩
  have hspec : ∀ g, 0 < A (n₀ g) g := fun g => by rw [hn₀]; exact Nat.find_spec (hex g)
  have hmin : ∀ g m, 0 < A m g → n₀ g ≤ m := fun g m hm => by rw [hn₀]; exact Nat.find_min' _ hm
  have hn₀inv : ∀ g (k : H), n₀ (g * k) = n₀ g := fun g k =>
    le_antisymm (hmin _ _ (by rw [hAinv]; exact hspec g))
      (hmin _ _ (by rw [← hAinv _ g k]; exact hspec _))
  have hn₀m : Measurable n₀ := by
    rw [hn₀]
    exact measurable_find hex fun k => measurableSet_lt measurable_const (hAm k)
  obtain ⟨b, hb⟩ : ∃ b : G → ℝ≥0∞, b = fun g => (U (n₀ g)).indicator 1 g := ⟨_, rfl⟩
  have hbm : Measurable b := by
    intro t ht
    have e : b ⁻¹' t = ⋃ n, (n₀ ⁻¹' {n}) ∩ ((U n).indicator (1 : G → ℝ≥0∞)) ⁻¹' t := by
      ext g
      simp only [hb, Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff,
        exists_eq_left']
    rw [e]
    exact MeasurableSet.iUnion fun n => (hn₀m (measurableSet_singleton n)).inter
      ((measurable_one.indicator (hUo n).measurableSet) ht)
  obtain ⟨a, ha⟩ : ∃ a : G → ℝ≥0∞, a = fun g => ∫⁻ h, b (g * (h : G)) ∂ν := ⟨_, rfl⟩
  have ham : Measurable a := by rw [ha]; exact measurable_avg ν hbm
  have hainv : ∀ g (k : H), a (g * k) = a g := fun g k => by rw [ha]; exact avg_mul_right ν b g k
  have haA : ∀ g, a g = A (n₀ g) g := fun g => by
    rw [ha, hA]
    refine lintegral_congr fun h => ?_
    rw [hb]
    simp only [hn₀inv]
  have ha0 : ∀ g, a g ≠ 0 := fun g => by rw [haA]; exact (hspec g).ne'
  have hat : ∀ g, a g ≠ ⊤ := fun g => by rw [haA]; exact (hAfin _ g).ne
  refine ⟨fun g => b g * (a g)⁻¹, hbm.mul ham.inv, fun g => ?_⟩
  have hbg : Measurable (fun h : H => b (g * (h : G))) :=
    hbm.comp (continuous_const.mul continuous_subtype_val).measurable
  calc ∫⁻ h, b (g * (h : G)) * (a (g * (h : G)))⁻¹ ∂ν
      = ∫⁻ h, b (g * (h : G)) * (a g)⁻¹ ∂ν := by
        refine lintegral_congr fun h => ?_
        rw [hainv]
    _ = a g * (a g)⁻¹ := by rw [lintegral_mul_const _ hbg, ha]
    _ = 1 := ENNReal.mul_inv_cancel (ha0 g) (hat g)
end PI.WeilQuotMeas.UnitaryGroupMassFormula
