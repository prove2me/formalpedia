-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.lattice_packLem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:29.469463+00:00
-- url     : https://prove2.me/submissions/6e736eb5-96f8-4c3b-af02-1428eec4c6dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_PackLem
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_norm_matVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_matVec_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_finrank_matSpace
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Module
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : PackLem := by
  intro ι _ N R ρ hρ hR T hT hsep
  classical
  let W := EuclideanSpace ℂ (Fin N × Fin N)
  let μ : Measure W := Measure.addHaar
  let ν : Measure (ι → W) := Measure.pi fun _ => μ
  let B : (ι → Matrix (Fin N) (Fin N) ℂ) → Set (ι → W) :=
    fun p => Set.univ.pi fun v => ball (matVec (p v)) (ρ v / 2)
  let Big : Set (ι → W) := Set.univ.pi fun v => ball (0 : W) (R v + ρ v / 2)
  have hdisj : (T : Set (ι → Matrix (Fin N) (Fin N) ℂ)).PairwiseDisjoint B := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    obtain ⟨v, hv⟩ := hsep p hp q hq hpq
    have h1 := (Set.mem_univ_pi.1 hzp) v
    have h2 := (Set.mem_univ_pi.1 hzq) v
    rw [mem_ball] at h1 h2
    have h3 : dist (matVec (p v)) (matVec (q v)) < ρ v := by
      calc dist (matVec (p v)) (matVec (q v)) ≤ dist (matVec (p v)) (z v) + dist (z v) (matVec (q v)) :=
            dist_triangle _ _ _
        _ < ρ v / 2 + ρ v / 2 := by rw [dist_comm] at h1; exact add_lt_add h1 h2
        _ = ρ v := by ring
    rw [dist_eq_norm, ← matVec_sub, norm_matVec] at h3
    linarith
  have hmeas : ∀ p ∈ T, MeasurableSet (B p) := fun p _ =>
    MeasurableSet.univ_pi fun v => measurableSet_ball
  have hsub : (⋃ p ∈ T, B p) ⊆ Big := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    refine Set.mem_univ_pi.2 fun v => ?_
    have h1 := (Set.mem_univ_pi.1 hz) v
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_ball_zero_iff]
    have h2 : ‖matVec (p v)‖ ≤ R v := by rw [norm_matVec]; exact hT p hp v
    calc ‖z v‖ = ‖(z v - matVec (p v)) + matVec (p v)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z v - matVec (p v)‖ + ‖matVec (p v)‖ := norm_add_le _ _
      _ < ρ v / 2 + R v := by linarith
      _ = R v + ρ v / 2 := by ring
  have key : ∑ p ∈ T, ν (B p) ≤ ν Big := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact measure_mono hsub
  set d := finrank ℝ W with hd
  set c := μ (ball (0 : W) 1) with hc
  have hc0 : c ≠ 0 := (measure_ball_pos μ (0 : W) one_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  have hB : ∀ p, ν (B p) = ∏ v, ENNReal.ofReal ((ρ v / 2) ^ d) * c := by
    intro p
    simp only [ν, B, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v])
  have hBig : ν Big = ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c := by
    simp only [ν, Big, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v, hR v])
  simp only [hB, Finset.sum_const, nsmul_eq_mul] at key
  rw [hBig] at key
  have hfin : ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c ≠ ⊤ :=
    ENNReal.prod_ne_top fun v _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  have key' := ENNReal.toReal_mono hfin key
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod, ENNReal.toReal_prod] at key'
  simp only [ENNReal.toReal_mul] at key'
  have hc' : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hpos : ∀ v, 0 < ρ v / 2 := fun v => by linarith [hρ v]
  simp only [fun v => ENNReal.toReal_ofReal (pow_nonneg (hpos v).le d),
    fun v => ENNReal.toReal_ofReal (pow_nonneg (add_pos_of_nonneg_of_pos (hR v) (hpos v)).le d)] at key'
  have hprodpos : 0 < ∏ v, (ρ v / 2) ^ d * c.toReal :=
    Finset.prod_pos fun v _ => mul_pos (pow_pos (hpos v) d) hc'
  rw [← le_div_iff₀ hprodpos, ← Finset.prod_div_distrib] at key'
  have hdN : d = 2 * N ^ 2 := finrank_matSpace N
  calc (T.card : ℝ) ≤ ∏ v, (R v + ρ v / 2) ^ d * c.toReal / ((ρ v / 2) ^ d * c.toReal) := key'
    _ = ∏ v, ((2 * R v + ρ v) / ρ v) ^ (2 * N ^ 2) := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [mul_div_mul_right _ _ hc'.ne', ← div_pow, hdN]
      congr 1
      have := hρ v
      field_simp
end PI.UnitaryGroupMassFormula.LCG
