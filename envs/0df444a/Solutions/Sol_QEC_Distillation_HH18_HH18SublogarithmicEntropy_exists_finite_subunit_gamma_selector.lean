-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.exists_finite_subunit_gamma_selector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:49:38.673584+00:00
-- url     : https://prove2.me/submissions/330cdf11-1ae9-48e9-b935-dcd0bf93f401

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_rat_num_den_in_window
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_parameter_sequence_admissible
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_tendsto_parameterGamma
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_exists_rat_mem_parameterInterval_hh18Gamma_lt
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_hh18GammaInf_lt_339_div_500
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_hh18GammaSet_bddBelow
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.bitstringWordEquiv_reducedLogicalBits
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.physicalCliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution (eta : ℝ) (heta : 0 < eta) :
    ∃ q : ℚ, ∃ A D j : Nat,
      (1 / 6 : ℚ) < q ∧ q < (1 / 3 : ℚ) ∧
        0 < A ∧ 0 < D ∧ 3 * A < D ∧ 0 < j ∧ q = (A : ℚ) / D ∧
        let r := parameterR D j
        let w := parameterW A j
        let m := parameterM D j
        let n := parameterLength A D j
        let k := parameterDimension A D j
        let d := parameterDistance A D j
        Admissible w r m ∧
          (w : ℚ) = 3 * (r : ℚ) * q ∧
          parameterGamma A D j = Real.log ((n : ℝ) / k) / Real.log d ∧
          |parameterGamma A D j - hh18GammaInf| < eta ∧
          parameterGamma A D j < (1339 / 1500 : ℝ) ∧
          parameterGamma A D j < 1 := by
  let epsilon : ℝ := min (eta / 3) (161 / 1500)
  have hepsilon_pos : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min (by linarith) (by norm_num)
  have hepsilon_eta : epsilon ≤ eta / 3 := by
    dsimp [epsilon]
    exact min_le_left _ _
  have hepsilon_fixed : epsilon ≤ 161 / 1500 := by
    dsimp [epsilon]
    exact min_le_right _ _
  rcases exists_rat_mem_parameterInterval_hh18Gamma_lt epsilon hepsilon_pos with
    ⟨q, hqI, hqGamma⟩
  have hqIReal : (1 / 6 : ℝ) < (q : ℝ) ∧ (q : ℝ) < (1 / 3 : ℝ) := by
    exact hqI
  have hqL : (1 / 6 : ℚ) < q := by
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num [Rat.cast_div]
    exact hqIReal.1
  have hqU : q < (1 / 3 : ℚ) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num [Rat.cast_div]
    exact hqIReal.2
  rcases rat_num_den_in_window hqL hqU with ⟨hA, hD, hwindow, hq⟩
  have hwindowL : q.den < 6 * q.num.natAbs := by
    have hqR : (1 / 6 : ℚ) < (q.num.natAbs : ℚ) / q.den := by
      rw [← hq]
      exact hqL
    have hdenR : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    have hcleared : (q.den : ℚ) < 6 * q.num.natAbs := by
      have := (lt_div_iff₀ hdenR).mp hqR
      nlinarith
    exact_mod_cast hcleared
  have hqR : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
    have hqcast := congrArg (fun x : ℚ => (x : ℝ)) hq
    simpa only [Rat.cast_div, Rat.cast_natCast] using hqcast
  have hgammaLimit := tendsto_parameterGamma q.num.natAbs q.den
    hA hD hwindowL hwindow
  have hgammaLimitQ : Tendsto (parameterGamma q.num.natAbs q.den) atTop
      (𝓝 (hh18Gamma (q : ℝ))) := by
    simpa only [hqR] using hgammaLimit
  have hnearBall : ∀ᶠ j in atTop,
      parameterGamma q.num.natAbs q.den j ∈
        Metric.ball (hh18Gamma (q : ℝ)) epsilon :=
    hgammaLimitQ.eventually (Metric.ball_mem_nhds _ hepsilon_pos)
  have hnear : ∀ᶠ j in atTop,
      |parameterGamma q.num.natAbs q.den j - hh18Gamma (q : ℝ)| < epsilon := by
    filter_upwards [hnearBall] with j hj
    simpa [Metric.mem_ball, Real.dist_eq] using hj
  rcases eventually_atTop.1 hnear with ⟨J, hJ⟩
  let j : Nat := max 1 J
  have hj : 0 < j := by
    dsimp [j]
    omega
  have hjlarge : J ≤ j := by
    dsimp [j]
    exact Nat.le_max_right _ _
  have hnear_j :
      |parameterGamma q.num.natAbs q.den j - hh18Gamma (q : ℝ)| < epsilon :=
    hJ j hjlarge
  have hqInf : hh18GammaInf ≤ hh18Gamma (q : ℝ) := by
    change sInf hh18GammaSet ≤ hh18Gamma (q : ℝ)
    apply csInf_le hh18GammaSet_bddBelow
    exact ⟨(q : ℝ), hqI, rfl⟩
  have hInfStrict : hh18GammaInf < (339 / 500 : ℝ) :=
    hh18GammaInf_lt_339_div_500
  have hqInfClose : |hh18Gamma (q : ℝ) - hh18GammaInf| < epsilon := by
    rw [abs_of_nonneg (sub_nonneg.mpr hqInf)]
    linarith
  have habs : |parameterGamma q.num.natAbs q.den j - hh18GammaInf| < eta := by
    calc
      |parameterGamma q.num.natAbs q.den j - hh18GammaInf| =
          |(parameterGamma q.num.natAbs q.den j - hh18Gamma (q : ℝ)) +
            (hh18Gamma (q : ℝ) - hh18GammaInf)| := by ring
      _ ≤ |parameterGamma q.num.natAbs q.den j - hh18Gamma (q : ℝ)| +
            |hh18Gamma (q : ℝ) - hh18GammaInf| := abs_add_le _ _
      _ < epsilon + epsilon := add_lt_add hnear_j hqInfClose
      _ < eta := by nlinarith
  have hgammaUpper : parameterGamma q.num.natAbs q.den j <
      hh18Gamma (q : ℝ) + epsilon := by
    have h := abs_lt.mp hnear_j
    linarith
  have hsubunit : parameterGamma q.num.natAbs q.den j <
      (1339 / 1500 : ℝ) := by
    linarith
  have hsubunit_one : parameterGamma q.num.natAbs q.den j < 1 := by
    calc
      parameterGamma q.num.natAbs q.den j < (1339 / 1500 : ℝ) := hsubunit
      _ < 1 := by norm_num
  rcases parameter_sequence_admissible q.num.natAbs q.den j hA hD hwindow hj
    with ⟨hm, hslope, hadmissible⟩
  have hslopeQ :
      (parameterW q.num.natAbs j : ℚ) =
        3 * (parameterR q.den j : ℚ) * q := by
    calc
      (parameterW q.num.natAbs j : ℚ) =
          3 * (parameterR q.den j : ℚ) *
            ((q.num.natAbs : ℚ) / q.den) := hslope
      _ = 3 * (parameterR q.den j : ℚ) * q := by rw [← hq]
  refine ⟨q, q.num.natAbs, q.den, j, hqL, hqU, hA, hD, hwindow, hj, hq, ?_⟩
  change
    Admissible (parameterW q.num.natAbs j) (parameterR q.den j)
        (parameterM q.den j) ∧
      (parameterW q.num.natAbs j : ℚ) =
        3 * (parameterR q.den j : ℚ) * q ∧
      parameterGamma q.num.natAbs q.den j =
        Real.log
          ((parameterLength q.num.natAbs q.den j : ℝ) /
            (parameterDimension q.num.natAbs q.den j : ℝ)) /
          Real.log (parameterDistance q.num.natAbs q.den j : ℝ) ∧
      |parameterGamma q.num.natAbs q.den j - hh18GammaInf| < eta ∧
      parameterGamma q.num.natAbs q.den j < (1339 / 1500 : ℝ) ∧
      parameterGamma q.num.natAbs q.den j < 1
  exact ⟨hadmissible, hslopeQ, rfl, habs, hsubunit, hsubunit_one⟩
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
