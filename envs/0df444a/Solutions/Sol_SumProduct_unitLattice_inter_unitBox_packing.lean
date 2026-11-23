-- Prove2me | solution 1 for SumProduct.unitLattice_inter_unitBox_packing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:34:07.179736+00:00
-- url     : https://prove2.me/submissions/7d4ab8c2-aae8-4887-b610-fbbab386cafc

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount
import Theorems.Thm_SumProduct_unitLattice_inter_unitBox_finite
import Theorems.Thm_SumProduct_unitLattice_unitBox_eq_zero
import Theorems.Thm_SumProduct_add_mem_unitBox
import Theorems.Thm_SumProduct_hensley_unitBox_volume
import Theorems.Thm_SumProduct_measurableSet_unitBox
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
import Theorems.Thm_SumProduct_sub_mem_unitBox
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Metric
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {d : ℕ} (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    ((↑(unitLattice K) ∩ unitBox K Y).ncard : ℝ) ≤ 5 * (5 * Y + 1) ^ (d - 1) := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hdpos : 0 < Real.sqrt (d : ℝ) := by
    rw [Real.sqrt_pos]; have : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hd] at this; exact_mod_cast this
  have hfin := unitLattice_inter_unitBox_finite (K := K) (Y := Y) hY0
  set P := hfin.toFinset with hP
  set C : logSpace K → Set (logSpace K) := fun p => (fun y => y - p) ⁻¹' (unitBox K (1 / 5)) with hC
  have hvolfin : ∀ r : ℝ, 0 ≤ r → volume (unitBox K r) ≠ ⊤ := by
    intro r hr
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
      (isCompact_closedBall (0 : logSpace K) r).measure_lt_top)
    intro x hx
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr]
    intro w; rw [Real.norm_eq_abs]; exact hx.1 w
  have hmeasC : ∀ p, MeasurableSet (C p) :=
    fun p => (measurableSet_unitBox (1 / 5)).preimage (by fun_prop)
  have hvolC : ∀ p, volume (C p) = volume (unitBox K (1 / 5)) := by
    intro p
    have hmp : MeasurePreserving (fun y : logSpace K => y - p) volume volume := by
      simpa [sub_eq_add_neg] using measurePreserving_add_right volume (-p)
    change volume ((fun y => y - p) ⁻¹' unitBox K (1 / 5)) = volume (unitBox K (1 / 5))
    exact hmp.measure_preimage (measurableSet_unitBox (1 / 5)).nullMeasurableSet
  have hdisj : (↑P : Set (logSpace K)).PairwiseDisjoint C := by
    intro p hp p' hp' hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    simp only [hC, Set.mem_preimage] at hz hz'
    simp only [hP, Finset.mem_coe, Set.Finite.mem_toFinset] at hp hp'
    have hdiff : p' - p ∈ unitBox K (2 / 5) := by
      have h := sub_mem_unitBox hz hz'
      rw [show (1 : ℝ) / 5 + 1 / 5 = 2 / 5 by norm_num,
        show (z - p) - (z - p') = p' - p by abel] at h
      exact h
    have hlat : p' - p ∈ unitLattice K := (unitLattice K).sub_mem hp'.1 hp.1
    exact hne (sub_eq_zero.mp (unitLattice_unitBox_eq_zero hlat hdiff)).symm
  have hsub : (⋃ p ∈ P, C p) ⊆ unitBox K (Y + 1 / 5) := by
    intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    simp only [hC, Set.mem_preimage] at hzp
    simp only [hP, Set.Finite.mem_toFinset] at hp
    have h := add_mem_unitBox hp.2 hzp
    rwa [show p + (z - p) = z by abel] at h
  have hpack : (P.card : ENNReal) * volume (unitBox K (1 / 5))
      ≤ volume (unitBox K (Y + 1 / 5)) := by
    calc (P.card : ENNReal) * volume (unitBox K (1 / 5))
        = ∑ p ∈ P, volume (C p) := by
          rw [Finset.sum_congr rfl (fun p _ => hvolC p), Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ p ∈ P, C p) := (measure_biUnion_finset hdisj (fun p _ => hmeasC p)).symm
      _ ≤ volume (unitBox K (Y + 1 / 5)) := measure_mono hsub
  -- convert to reals via eq (3.1)
  have hreal := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hvolfin _ (by norm_num)))
    (hvolfin _ (by positivity))).mpr hpack
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  obtain ⟨hlo, -⟩ := hensley_unitBox_volume K (1 / 5) (by norm_num)
  obtain ⟨-, hhi⟩ := hensley_unitBox_volume K (Y + 1 / 5) (by positivity)
  rw [hd, show (2 : ℝ) * (1 / 5) = 2 / 5 by norm_num] at hlo
  rw [hd] at hhi
  have hncard : ((↑(unitLattice K) ∩ unitBox K Y).ncard : ℝ) = (P.card : ℝ) := by
    rw [hP]; congr 1; exact Set.ncard_eq_toFinset_card _ hfin
  have hc : (0 : ℝ) < (2 / 5) ^ (d - 1) / Real.sqrt d := by positivity
  rw [hncard]
  refine le_of_mul_le_mul_right ?_ hc
  calc (P.card : ℝ) * ((2 / 5) ^ (d - 1) / Real.sqrt d)
      ≤ (P.card : ℝ) * (volume (unitBox K (1 / 5))).toReal := by gcongr
    _ ≤ (volume (unitBox K (Y + 1 / 5))).toReal := hreal
    _ ≤ 5 * (2 * (Y + 1 / 5)) ^ (d - 1) / Real.sqrt d := hhi
    _ = 5 * (5 * Y + 1) ^ (d - 1) * ((2 / 5) ^ (d - 1) / Real.sqrt d) := by
        rw [show (2 : ℝ) * (Y + 1 / 5) = (5 * Y + 1) * (2 / 5) by ring, mul_pow]; ring
end SumProduct
