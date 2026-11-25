-- Prove2me | solution 1 for PI.RhsWLim.W.hypLF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:21:22.850436+00:00
-- url     : https://prove2.me/submissions/9b9b57c4-10b3-443f-984e-3d20c30a4f1b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Theorems.Thm_PI_RhsWLim_W_hypPar_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution : HypLF := by
  intro k T' hT'
  have hcont : Continuous (hypPar k T') := by
    unfold hypPar
    refine (continuous_pi (fun i => ?_)).prodMk ?_
    · exact (EuclideanSpace.proj i).continuous.comp continuous_fst
    · refine (Complex.continuous_ofReal.comp ?_).mul ?_
      · exact Real.continuous_sqrt.comp (((continuous_norm.comp continuous_fst).pow 2).add continuous_const)
      · exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hmeas : Measurable (hypPar k T') := hcont.measurable
  have hSc : IsClosed (hypS k T') := by
    have h1 : Continuous (fun p : (Fin k → ℂ) × ℂ => ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2) :=
      (continuous_finset_sum _ (fun i _ => Complex.continuous_normSq.comp ((continuous_apply i).comp continuous_fst))).sub
        (Complex.continuous_normSq.comp continuous_snd)
    exact isClosed_eq h1 continuous_const
  constructor
  · unfold hypM
    rw [Measure.smul_apply, Measure.map_apply hmeas hSc.measurableSet.compl]
    have h2 : hypPar k T' ⁻¹' (hypS k T')ᶜ = ∅ := by
      ext q
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      exact hypPar_mem k T' hT' q
    rw [h2, measure_empty, smul_zero]
  · intro C hC
    obtain ⟨R, hR⟩ := (hC.image continuous_fst).isBounded.exists_norm_le
    have hsub : hypPar k T' ⁻¹' C ⊆
        Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2)) ×ˢ Set.univ := by
      intro q hq
      refine ⟨?_, Set.mem_univ _⟩
      have h1 : ‖(hypPar k T' q).1‖ ≤ R := hR _ ⟨_, hq, rfl⟩
      have h2 : ∀ i, ‖q.1 i‖ ≤ R := fun i => le_trans (norm_le_pi_norm (hypPar k T' q).1 i) h1
      rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖q.1 i‖ ^ 2 ≤ ∑ i : Fin k, R ^ 2 :=
            Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h2 i) 2)
        _ = k * R ^ 2 := by simp
    unfold hypM
    rw [Measure.smul_apply, Measure.map_apply hmeas hC.isClosed.measurableSet, smul_eq_mul]
    refine ENNReal.mul_lt_top (ENNReal.div_lt_top ENNReal.one_ne_top two_ne_zero) ?_
    calc _ ≤ (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))
          (Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2)) ×ˢ Set.univ) :=
          measure_mono hsub
      _ = volume (Metric.closedBall (0 : EuclideanSpace ℂ (Fin k)) (Real.sqrt (k * R ^ 2))) *
          volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) Set.univ := Measure.prod_prod _ _
      _ < ⊤ := by
        apply ENNReal.mul_lt_top measure_closedBall_lt_top
        rw [Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top
end PI.RhsWLim.W
