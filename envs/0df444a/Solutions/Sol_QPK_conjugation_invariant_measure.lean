-- Prove2me | solution 1 for QPK.conjugation_invariant_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:27.752043+00:00
-- url     : https://prove2.me/submissions/72e486b0-b09c-4d57-b358-1e838f13d50b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ConjugationInvariantMeasure
import Theorems.Thm_QPK_ennreal_eq_one_of_mul
import Theorems.Thm_QPK_ennreal_le_one_of_pow_le
import Theorems.Thm_QPK_measurable_conj
import Theorems.Thm_QPK_conj_comp
import Theorems.Thm_QPK_invOn_map_conj
import Theorems.Thm_QPK_haar_measure_uniqueness


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
open QPK
namespace QPK
theorem _root_.solution : ConjInv := by
  intro G _ _ _ _ _ _ _ _ N H hN hH hGN hGH hnorm μ hμ hfin hpos h hh
  haveI := hfin
  have hinvH : ∀ g ∈ H, g⁻¹ ∈ H := hGH.2.2
  have hinv : ∀ g ∈ H, InvOn (μ.map (fun x => g * x * g⁻¹)) N := fun g hg =>
    invOn_map_conj hN g (hnorm g hg) (hnorm g⁻¹ (hinvH g hg)) hμ
  have hd : ∀ g ∈ H, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map (fun x => g * x * g⁻¹) = c • μ :=
    fun g hg => haar_measure_uniqueness G N hN hGN _ _ (hinv g hg) hμ
  choose d hd0 hdt hdmap using hd
  obtain ⟨K0, hK0c, hK0n⟩ := exists_compact_mem_nhds (1 : G)
  have hAi : μ (interior K0) ≠ 0 :=
    hpos _ isOpen_interior ⟨1, mem_interior_iff_mem_nhds.mpr hK0n, hGN.1⟩
  have hK0pos : μ K0 ≠ 0 := fun h0 => hAi (measure_mono_null interior_subset h0)
  have hK0fin : μ K0 ≠ ⊤ := hK0c.measure_lt_top.ne
  have hK0m : MeasurableSet K0 := hK0c.isClosed.measurableSet
  let Bc : Set G := (fun p : G × G × G => p.1 * p.2.1 * p.2.2) '' (H ×ˢ (K0 ×ˢ H))
  have hBc : IsCompact Bc :=
    (hH.prod (hK0c.prod hH)).image (by fun_prop)
  have hBcfin : μ Bc ≠ ⊤ := hBc.measure_lt_top.ne

  have hle : ∀ g (hg : g ∈ H), d g hg ≤ 1 := by
    intro g hg
    have hpowmem : ∀ k : ℕ, g ^ k ∈ H := by
      intro k
      induction k with
      | zero => simpa using hGH.1
      | succ k ih => rw [pow_succ]; exact hGH.2.1 _ ih _ hg
    have hpow : ∀ k : ℕ, μ.map (fun x => g ^ k * x * (g ^ k)⁻¹) = d g hg ^ k • μ := by
      intro k
      induction k with
      | zero => simp [Measure.map_id']
      | succ k ih =>
        have e := conj_comp g (g ^ k)
        rw [← pow_succ'] at e
        rw [← e, ← Measure.map_map (measurable_conj g) (measurable_conj (g ^ k)), ih, Measure.map_smul,
          hdmap g hg, smul_smul, pow_succ]
    have hbd : ∀ k : ℕ, d g hg ^ k ≤ μ Bc / μ K0 := by
      intro k
      rw [ENNReal.le_div_iff_mul_le (Or.inl hK0pos) (Or.inl hK0fin)]
      have h1 : (μ.map (fun x => g ^ k * x * (g ^ k)⁻¹)) K0 = d g hg ^ k * μ K0 := by
        rw [hpow k]
        rfl
      rw [← h1, Measure.map_apply (measurable_conj _) hK0m]
      apply measure_mono
      intro x hx
      refine ⟨((g ^ k)⁻¹, (g ^ k * x * (g ^ k)⁻¹, g ^ k)), ⟨hinvH _ (hpowmem k), hx, hpowmem k⟩, ?_⟩
      simp only
      group
    exact ennreal_le_one_of_pow_le (hdt g hg) (ENNReal.div_ne_top hBcfin hK0pos) hbd

  have hprod : d h hh * d h⁻¹ (hinvH h hh) = 1 := by
    have e := conj_comp h⁻¹ h
    have e2 : (fun x : G => (h⁻¹ * h) * x * (h⁻¹ * h)⁻¹) = id := by
      funext x
      simp
    rw [e2] at e
    have h1 : μ = (d h⁻¹ (hinvH h hh) * d h hh) • μ := by
      conv_lhs => rw [← Measure.map_id (μ := μ), ← e, ← Measure.map_map (measurable_conj h⁻¹) (measurable_conj h)]
      rw [hdmap h hh, Measure.map_smul, hdmap h⁻¹ (hinvH h hh), smul_smul, mul_comm]
    have h2 := congrArg (fun ν : Measure G => ν K0) h1
    simp only [Measure.smul_apply, smul_eq_mul] at h2
    rw [mul_comm]
    exact ennreal_eq_one_of_mul hK0pos hK0fin h2.symm
  have hone : d h hh = 1 := by
    apply le_antisymm (hle h hh)
    calc (1 : ℝ≥0∞) = d h hh * d h⁻¹ (hinvH h hh) := hprod.symm
      _ ≤ d h hh * 1 := mul_le_mul_of_nonneg_left (hle h⁻¹ (hinvH h hh)) (by simp)
      _ = d h hh := mul_one _
  rw [hdmap h hh, hone, one_smul]
end QPK
