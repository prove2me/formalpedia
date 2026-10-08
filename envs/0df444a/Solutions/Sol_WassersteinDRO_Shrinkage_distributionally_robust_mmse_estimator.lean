-- Prove2me | solution 1 for WassersteinDRO.Shrinkage.distributionally_robust_mmse_estimator
-- status  : ACCEPTED   (disprove)
-- author  : @moona3k
-- created : 2026-10-06T18:16:33.885921+00:00
-- url     : https://prove2.me/submissions/f9861d82-0b96-4bb4-82e8-131aed455c12

import Definitions.Def_WassersteinDRO_Shrinkage_IsElliptical
import Definitions.Def_WassersteinDRO_Shrinkage_affineEstimator
import Definitions.Def_WassersteinDRO_Shrinkage_estimationLoss
import Definitions.Def_WassersteinDRO_Shrinkage_nominalRisk
import Definitions.Def_WassersteinDRO_Shrinkage_psdSqrt
import Definitions.Def_WassersteinDRO_Shrinkage_robustMMSEValue
import Definitions.Def_WassersteinDRO_Shrinkage_sdpValue
import Mathlib
import Mathlib.Analysis.Matrix.Order

-- Complete local proof: Solutions.Basic

open MeasureTheory
open scoped ENNReal
namespace ShrinkageCounterexample
abbrev V := EuclideanSpace ℝ (Fin 1 ⊕ Fin 1)
noncomputable def point (x y : ℝ) : V :=
  (EuclideanSpace.equiv (Fin 1 ⊕ Fin 1) ℝ).symm (Sum.elim (fun _ => x) (fun _ => y))
@[simp] theorem point_x (x y : ℝ) (i : Fin 1) : point x y (Sum.inl i) = x := rfl
@[simp] theorem point_y (x y : ℝ) (i : Fin 1) : point x y (Sum.inr i) = y := rfl
noncomputable def nominal : Measure V :=
  (1/2 : ℝ≥0∞) • Measure.dirac (point (-1/2) 0) +
  (1/4 : ℝ≥0∞) • Measure.dirac (point (1/2) (-1)) +
  (1/4 : ℝ≥0∞) • Measure.dirac (point (1/2) 1)
theorem nominal_probability : nominal Set.univ = 1 := by
  simp [nominal]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]
end ShrinkageCounterexample

-- Complete local proof: Solutions.Atomic
open MeasureTheory
open scoped ENNReal
namespace ShrinkageCounterexample
 theorem atomic_integrable {E : Type*} [NormedAddCommGroup E] (f : V → E) : Integrable f nominal := by
  have hd (z : V) : Integrable f (Measure.dirac z) := integrable_dirac (by simp)
  have h2 : (1/2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h4 : (1/4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  exact ((hd _).smul_measure h2 |>.add_measure ((hd _).smul_measure h4)).add_measure ((hd _).smul_measure h4)
 theorem atomic_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : V → E) :
    (∫ z, f z ∂nominal) = (1/2 : ℝ) • f (point (-1/2) 0) +
      (1/4 : ℝ) • f (point (1/2) (-1)) + (1/4 : ℝ) • f (point (1/2) 1) := by
  have hd (z : V) : Integrable f (Measure.dirac z) := integrable_dirac (by simp)
  have h2 : (1/2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h4 : (1/4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  unfold nominal
  rw [integral_add_measure (((hd _).smul_measure h2).add_measure ((hd _).smul_measure h4)) ((hd _).smul_measure h4)]
  rw [integral_add_measure ((hd _).smul_measure h2) ((hd _).smul_measure h4)]
  simp only [integral_smul_measure, integral_dirac]
  norm_num
 theorem nominal_mean : WassersteinDRO.Shrinkage.meanVector nominal = 0 := by
  unfold WassersteinDRO.Shrinkage.meanVector
  rw [atomic_integral]
  ext i
  rcases i with i | i <;> simp
  all_goals norm_num
noncomputable def nominalCovariance : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.diagonal (Sum.elim (fun _ => 1/4) (fun _ => 1/2))
theorem nominal_covariance : WassersteinDRO.Shrinkage.covarianceMatrix nominal = nominalCovariance := by
  ext i j
  simp only [WassersteinDRO.Shrinkage.covarianceMatrix, Matrix.of_apply, nominal_mean, PiLp.zero_apply, sub_zero]
  rw [atomic_integral]
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i; fin_cases j; norm_num [nominalCovariance, Matrix.diagonal_apply] <;> simp
theorem nominal_elliptical (g : ℝ → ℝ) :
    WassersteinDRO.Shrinkage.IsElliptical nominal g 0 nominalCovariance :=
  ⟨nominal_probability, nominal_mean, nominal_covariance⟩
theorem nominal_covariance_posDef : nominalCovariance.PosDef := by
  rw [nominalCovariance, Matrix.posDef_diagonal_iff]
  intro i
  rcases i with i | i <;> norm_num
#print axioms nominal_elliptical
#print axioms nominal_covariance_posDef
end ShrinkageCounterexample

-- Complete local proof: Solutions.Estimator
open MeasureTheory
namespace ShrinkageCounterexample
abbrev Y := EuclideanSpace ℝ (Fin 1)
noncomputable def predictor (y : Y) : Y :=
  (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => |y 0| - 1/2)
theorem predictor_measurable : Measurable predictor := by
  unfold predictor
  fun_prop
theorem loss_scalar (z : V) : WassersteinDRO.Shrinkage.estimationLoss predictor z =
    (z (Sum.inl 0) - (|z (Sum.inr 0)| - 1/2)) ^ 2 := by
  simp [WassersteinDRO.Shrinkage.estimationLoss, EuclideanSpace.real_norm_sq_eq, predictor]
theorem point_loss_zero (x y : ℝ) (h : x = |y| - 1/2) :
    WassersteinDRO.Shrinkage.estimationLoss predictor (point x y) = 0 := by
  rw [loss_scalar]
  simp [h]
theorem loss_transport_bound (z : V) (x y : ℝ) (h : x = |y| - 1/2) :
    WassersteinDRO.Shrinkage.estimationLoss predictor z ≤ 2 * ‖z - point x y‖ ^ 2 := by
  rw [loss_scalar, EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, PiLp.sub_apply, point_x, point_y]
  have ha := abs_abs_sub_abs_le_abs_sub (z (Sum.inr 0)) y
  have hs : (|z (Sum.inr 0)| - |y|)^2 ≤ (z (Sum.inr 0) - y)^2 := by
    exact (sq_le_sq).2 ha
  rw [h]
  nlinarith [sq_nonneg ((z (Sum.inl 0) - (|y| - 1/2)) + (|z (Sum.inr 0)| - |y|))]
theorem nominal_predictor_risk_zero :
    WassersteinDRO.Shrinkage.nominalRisk nominal
      (WassersteinDRO.Shrinkage.estimationLoss predictor) = 0 := by
  unfold WassersteinDRO.Shrinkage.nominalRisk
  rw [atomic_integral]
  norm_num [loss_scalar]
#print axioms predictor_measurable
#print axioms loss_transport_bound
#print axioms nominal_predictor_risk_zero
end ShrinkageCounterexample

-- Complete local proof: Solutions.TransportRisk
open MeasureTheory
open scoped ENNReal
namespace ShrinkageCounterexample
open WassersteinDRO.Shrinkage
noncomputable abbrev loss (z : V) : ℝ := estimationLoss predictor z
theorem loss_nonneg (z : V) : 0 ≤ loss z := by change 0 ≤ estimationLoss predictor z; rw [loss_scalar]; positivity
theorem loss_measurable : Measurable loss := by
  have he : loss = fun z : V => (z (Sum.inl 0) - (|z (Sum.inr 0)| - 1/2))^2 := funext loss_scalar
  rw [he]
  fun_prop
abbrev atoms : Set V := {z | z = point (-1/2) 0 ∨ z = point (1/2) (-1) ∨ z = point (1/2) 1}
theorem nominal_supported : nominal atomsᶜ = 0 := by
  simp [nominal, atoms]
theorem coupling_loss_half_bound (Q : Measure V) (hi : Integrable loss Q)
    (π : Measure (V × V)) (hf : π.map Prod.fst = Q) (hs : π.map Prod.snd = nominal) :
    ENNReal.ofReal (nominalRisk Q loss / 2) ≤
      ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ (2 : ℝ)) ∂π := by
  have hy : ∀ᵐ z ∂π, z.2 ∈ atoms := by
    apply ae_iff.mpr
    change π (Prod.snd ⁻¹' atomsᶜ) = 0
    rw [← Measure.map_apply measurable_snd (by measurability : MeasurableSet atomsᶜ), hs]
    exact nominal_supported
  have hpoint : ∀ᵐ z ∂π, loss z.1 / 2 ≤ ‖z.1-z.2‖ ^ (2 : ℝ) := hy.mono fun z hz => by
    have hb (x y : ℝ) (hx : x = |y| - 1/2) : loss z.1 / 2 ≤ ‖z.1-point x y‖ ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      have hh := loss_transport_bound z.1 x y hx
      change loss z.1 ≤ _ at hh
      linarith
    rcases hz with hz | hz | hz
    · rw [hz]; exact hb (-1/2) 0 (by norm_num)
    · rw [hz]; exact hb (1/2) (-1) (by norm_num)
    · rw [hz]; exact hb (1/2) 1 (by norm_num)
  have hhalf : Integrable (fun z => loss z / 2) Q := hi.div_const 2
  have hnn : 0 ≤ᵐ[Q] (fun z => loss z / 2) := Filter.Eventually.of_forall fun z => div_nonneg (loss_nonneg z) (by norm_num)
  have he : ENNReal.ofReal (nominalRisk Q loss / 2) = ∫⁻ z, ENNReal.ofReal (loss z / 2) ∂Q := by
    unfold nominalRisk
    rw [← integral_div]
    exact ofReal_integral_eq_lintegral_ofReal hhalf hnn
  rw [he, ← hf, lintegral_map ((loss_measurable.div_const 2).ennreal_ofReal) measurable_fst]
  exact lintegral_mono_ae (hpoint.mono fun z hz => ENNReal.ofReal_le_ofReal hz)
theorem risk_half_le_transport_inf (Q : Measure V) (hi : Integrable loss Q) :
    ENNReal.ofReal (nominalRisk Q loss / 2) ≤
      ⨅ (π : Measure (V × V)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = nominal),
        ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ (2 : ℝ)) ∂π := by
  refine le_iInf fun π => le_iInf fun hπ => ?_
  exact coupling_loss_half_bound Q hi π hπ.1 hπ.2
theorem risk_ball_bound (ε : ℝ) (hε : 0 ≤ ε) (Q : Measure V)
    (hQ : Q ∈ ambiguitySet ε 2 Set.univ nominal) (hi : Integrable loss Q) :
    nominalRisk Q loss ≤ 2 * ε^2 := by
  have hw := ENNReal.rpow_le_rpow hQ.2.2 (by norm_num : 0 ≤ (2 : ℝ))
  rw [wassersteinDistance, ← ENNReal.rpow_mul] at hw
  have he : (1 / (2 : ℝ)) * 2 = 1 := by norm_num
  rw [he, ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg hε (by norm_num), Real.rpow_two] at hw
  have hb := (risk_half_le_transport_inf Q hi).trans hw
  have hr : nominalRisk Q loss / 2 ≤ ε^2 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ε)).mp hb
  linarith
 theorem robust_value_upper (ε : ℝ) (hε : 0 ≤ ε) :
    robustMMSEValue ε nominal ≤ (2 * ε^2 : ℝ) := by
  unfold robustMMSEValue
  refine iInf_le_of_le predictor (iInf_le_of_le predictor_measurable ?_)
  refine iSup_le fun Q => iSup_le fun hQ => iSup_le fun hi => ?_
  exact EReal.coe_le_coe_iff.mpr (risk_ball_bound ε hε Q hQ hi)
#print axioms risk_half_le_transport_inf
#print axioms robust_value_upper
end ShrinkageCounterexample

-- Complete local proof: Solutions.SquareRoot
open scoped MatrixOrder
namespace ShrinkageCounterexample
 theorem psdSqrt_eq_cfc {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    WassersteinDRO.Shrinkage.psdSqrt A = CFC.sqrt A := by
  have h : ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = A :=
    ⟨CFC.sqrt A, Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A), CFC.sqrt_mul_sqrt_self A hA.nonneg⟩
  unfold WassersteinDRO.Shrinkage.psdSqrt
  rw [dif_pos h]
  exact (CFC.sqrt_unique h.choose_spec.2 h.choose_spec.1.nonneg).symm
 theorem nominal_bures_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    WassersteinDRO.Shrinkage.psdSqrt
      (WassersteinDRO.Shrinkage.psdSqrt A * A * WassersteinDRO.Shrinkage.psdSqrt A) = A := by
  rw [psdSqrt_eq_cfc A hA]
  have hs : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have he : CFC.sqrt A * A * CFC.sqrt A = A * A := by
    calc
      _ = CFC.sqrt A * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt A := by rw [hs]
      _ = (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A * CFC.sqrt A) := by noncomm_ring
      _ = A * A := by rw [hs]
  rw [he]
  have haa : (A * A).PosSemidef := by
    simpa only [hA.1.eq] using Matrix.posSemidef_conjTranspose_mul_self A
  rw [psdSqrt_eq_cfc (A * A) haa]
  exact CFC.sqrt_mul_self A hA.nonneg
#print axioms psdSqrt_eq_cfc
#print axioms nominal_bures_zero
end ShrinkageCounterexample

-- Complete local proof: Solutions.SDP
open MeasureTheory
namespace ShrinkageCounterexample
open WassersteinDRO.Shrinkage
theorem nominal_eigenvalue_lower (i : Fin 1 ⊕ Fin 1) :
    (1/4 : ℝ) ≤ nominal_covariance_posDef.isHermitian.eigenvalues i := by
  have hi : nominal_covariance_posDef.isHermitian.eigenvalues i ∈ spectrum ℝ nominalCovariance := nominal_covariance_posDef.isHermitian.eigenvalues_mem_spectrum_real i
  change nominal_covariance_posDef.isHermitian.eigenvalues i ∈ spectrum ℝ
    (Matrix.diagonal (Sum.elim (fun _ : Fin 1 => (1/4 : ℝ)) (fun _ : Fin 1 => (1/2 : ℝ)))) at hi
  rw [spectrum_diagonal] at hi
  obtain ⟨j, hj⟩ := hi
  rw [← hj]
  rcases j with j | j <;> norm_num
theorem nominal_eigenvalue_attained :
    ∃ i, (1/4 : ℝ) = nominal_covariance_posDef.isHermitian.eigenvalues i := by
  have hm : (1/4 : ℝ) ∈ spectrum ℝ nominalCovariance := by
    rw [nominalCovariance, spectrum_diagonal]
    exact ⟨Sum.inl 0, rfl⟩
  rw [nominal_covariance_posDef.isHermitian.spectrum_real_eq_range_eigenvalues] at hm
  obtain ⟨i, hi⟩ := hm
  exact ⟨i, hi.symm⟩
theorem nominal_block_x : nominalCovariance.toBlocks₁₁ = Matrix.diagonal (fun _ : Fin 1 => (1/4 : ℝ)) := by
  ext i j
  simp [nominalCovariance, Matrix.toBlocks₁₁, Matrix.diagonal_apply]
theorem nominal_block_y : nominalCovariance.toBlocks₂₂ = Matrix.diagonal (fun _ : Fin 1 => (1/2 : ℝ)) := by
  ext i j
  simp [nominalCovariance, Matrix.toBlocks₂₂, Matrix.diagonal_apply]
theorem nominal_block_xy : nominalCovariance.toBlocks₁₂ = 0 := by
  ext i j
  simp [nominalCovariance, Matrix.toBlocks₁₂]
theorem nominal_loewner :
    (nominalCovariance - (1/4 : ℝ) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)).PosSemidef := by
  have he : nominalCovariance - (1/4 : ℝ) • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) =
      Matrix.diagonal (Sum.elim (fun _ => (0 : ℝ)) (fun _ => (1/4 : ℝ))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals fin_cases i; fin_cases j; norm_num [nominalCovariance, Matrix.diagonal_apply, Matrix.one_apply] <;> simp
  rw [he]
  exact Matrix.PosSemidef.diagonal (fun i => by rcases i with i | i <;> norm_num)
theorem nominal_sdp_feasible (ε : ℝ) : nominalCovariance ∈ sdpFeasibleSet ε nominalCovariance (1/4) := by
  refine ⟨nominal_covariance_posDef.posSemidef, ?_, ?_, ?_, nominal_loewner⟩
  · rw [nominal_block_x]
    exact Matrix.PosSemidef.diagonal (fun _ => by norm_num)
  · rw [nominal_block_y]
    exact Matrix.PosSemidef.diagonal (fun _ => by norm_num)
  · rw [nominal_bures_zero nominalCovariance nominal_covariance_posDef.posSemidef]
    have he : nominalCovariance + nominalCovariance - (2 : ℝ) • nominalCovariance = 0 := by simp [two_smul]
    rw [he]
    simp [sq_nonneg]
theorem nominal_sdp_objective : sdpObjective nominalCovariance = 1/4 := by
  simp [sdpObjective, nominal_block_xy, nominal_block_x, Matrix.trace]
theorem sdp_value_lower (ε : ℝ) : ((1/4 : ℝ) : EReal) ≤ sdpValue ε nominalCovariance (1/4) := by
  have h : (sdpObjective nominalCovariance : EReal) ≤ sdpValue ε nominalCovariance (1/4) := by
    unfold sdpValue
    exact le_iSup_of_le nominalCovariance (le_iSup_of_le (nominal_sdp_feasible ε) le_rfl)
  simpa only [nominal_sdp_objective] using h
#print axioms sdp_value_lower
end ShrinkageCounterexample

-- Complete local proof: Solutions.Dis_RobustMMSE
open MeasureTheory WassersteinDRO.Shrinkage ShrinkageCounterexample

theorem solution : ¬ (∀ {mx my : ℕ}
    (ε : ℝ) (hε : 0 < ε)
    (SigmaHat : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ)
    (hSigmaHatSymm : SigmaHat.IsHermitian) (hSigmaHatPD : SigmaHat.PosDef)
    (lambdaMin : ℝ) (hLambdaMinLB : ∀ i, lambdaMin ≤ hSigmaHatSymm.eigenvalues i)
    (hLambdaMinAttained : ∃ i, lambdaMin = hSigmaHatSymm.eigenvalues i)
    (muHatX : EuclideanSpace ℝ (Fin mx)) (muHatY : EuclideanSpace ℝ (Fin my))
    (muHat : EuclideanSpace ℝ (Fin mx ⊕ Fin my))
    (hmuHatX : ∀ i : Fin mx, muHat (Sum.inl i) = muHatX i)
    (hmuHatY : ∀ i : Fin my, muHat (Sum.inr i) = muHatY i)
    (g : ℝ → ℝ) (PN : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my)))
    (hElliptical : IsElliptical PN g muHat SigmaHat),
robustMMSEValue ε PN = sdpValue ε SigmaHat lambdaMin ∧
      ∀ S : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ,
        S ∈ sdpFeasibleSet ε SigmaHat lambdaMin →
        (sdpObjective S : EReal) = sdpValue ε SigmaHat lambdaMin →
        S.toBlocks₂₂.PosDef →
        ⨆ (Q : Measure (EuclideanSpace ℝ (Fin mx ⊕ Fin my)))
            (_ : Q ∈ ambiguitySet ε 2 Set.univ PN)
            (_ : Integrable
              (estimationLoss (affineEstimator S.toBlocks₁₂ S.toBlocks₂₂ muHatX muHatY)) Q),
          (nominalRisk Q
              (estimationLoss (affineEstimator S.toBlocks₁₂ S.toBlocks₂₂ muHatX muHatY)) :
              EReal) =
          robustMMSEValue ε PN) := by
  intro h
  have he := (h (mx := 1) (my := 1) (1/8) (by norm_num)
    nominalCovariance nominal_covariance_posDef.isHermitian nominal_covariance_posDef
    (1/4) nominal_eigenvalue_lower nominal_eigenvalue_attained
    0 0 0 (fun i => by simp) (fun i => by simp) (fun _ => 0) nominal
    (nominal_elliptical (fun _ => 0))).1
  have hu := robust_value_upper (1/8) (by norm_num)
  have hl := sdp_value_lower (1/8)
  rw [he] at hu
  have hc : (1/4 : ℝ) ≤ 2 * (1/8 : ℝ)^2 := EReal.coe_le_coe_iff.mp (hl.trans hu)
  norm_num at hc
#print axioms solution
