-- Prove2me | solution 1 for Real.poitouKernel_admissible_and_archBound
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bb9fc218-923a-5ba3-a4b4-eb5d0d799123

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Real_poitouKernel_admissible_and_archBound

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

namespace Complex
p2m_export "Complex" "abs_re_le_norm reCLM one_re sinh_two_mul continuous_re differentiable_exp re sqrt div_ofNat_im continuous_sinh ofReal_re hasDerivAt_exp add_re reCLM_apply cosh_sq_sub_sinh_sq log_one cosh hasDerivAt_cosh norm_real one_im add_im im arg sinh_zero log_inv conj_re I_sq Gamma sinh continuous_cosh exp_bound exists zero_re ofReal_mul exp_neg cosh_zero neg_re sub_re I_re div_ofNat_re continuous_exp exp norm_exp sub_im exp_re tanh_eq_sinh_div_cosh cosh_neg exp_zero tanh cos_neg ofReal_inj exp_log Gammaℂ ofReal_cpow continuous_ofReal contDiff_exp I_im mul_re log_mul ofReal_im log ofReal_exp digamma I exp_nat_mul conj_im mul_im zero_im cos continuous_cos hasDerivAt_log exp_add"
p2m_open "Complex"
end Complex
namespace FLT
namespace Gapsw48T2OdlyzkoDeg24PinCarrier
end FLT.Gapsw48T2OdlyzkoDeg24PinCarrier
namespace FLT
namespace Gapsw50T2ExplicitFormulaDecompositionPin
end FLT.Gapsw50T2ExplicitFormulaDecompositionPin
namespace FLT
namespace Gapsw52T2CarrierContentAtoms
end FLT.Gapsw52T2CarrierContentAtoms
namespace FLT
namespace Gapsw80T11ExplicitFormulaA34Decomp
end FLT.Gapsw80T11ExplicitFormulaA34Decomp
namespace FLT
namespace Gapsw80T13AffineArchTermA34Redecomp
end FLT.Gapsw80T13AffineArchTermA34Redecomp
namespace FLT
namespace Gapsw80T18ArchDerivedA34Redecomp
end FLT.Gapsw80T18ArchDerivedA34Redecomp
namespace FLT
namespace Gapsw80T19B2ppHadamardDecomp
end FLT.Gapsw80T19B2ppHadamardDecomp
namespace FLT
namespace Gapsw80T1OdlyzkoFoundationAtomDecomposition
end FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
namespace FLT
namespace Gapsw80T20LambdaLogDerivProductRule
end FLT.Gapsw80T20LambdaLogDerivProductRule
namespace FLT
namespace Gapsw80T21D2SubDecompWire
end FLT.Gapsw80T21D2SubDecompWire
namespace FLT
namespace Gapsw80T22AdmissibilityStripGapProbe
end FLT.Gapsw80T22AdmissibilityStripGapProbe
namespace FLT
namespace Gapsw80T23OdlyzkoKernelStripRemint
end FLT.Gapsw80T23OdlyzkoKernelStripRemint
namespace FLT
namespace Gapsw80T24StripMigrationChainStart
end FLT.Gapsw80T24StripMigrationChainStart
namespace FLT
namespace Gapsw80T25B4pppStripSinglePointAbsorption
end FLT.Gapsw80T25B4pppStripSinglePointAbsorption
namespace FLT
namespace Gapsw80T62ArchGammaKernelRemintWire
end FLT.Gapsw80T62ArchGammaKernelRemintWire
namespace FLT
namespace Gapsw80T64D2fGaussianMollificationProof
end FLT.Gapsw80T64D2fGaussianMollificationProof
namespace FLT
namespace Gapsw80T67D2bpPrimeSumFalseprobeRemint
end FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint
namespace FLT
namespace Gapsw80T68D2bppExplicitFormulaSubDecomp
end FLT.Gapsw80T68D2bppExplicitFormulaSubDecomp
namespace FLT
namespace Gapsw80T69AdmC2RemintZktSummable
end FLT.Gapsw80T69AdmC2RemintZktSummable
namespace FLT
namespace Gapsw80T70D2bpppZeroSideEvalSubDecomp
end FLT.Gapsw80T70D2bpppZeroSideEvalSubDecomp
namespace FLT
namespace Gapsw80T71D2bpppbAnalyticContinuationProof
end FLT.Gapsw80T71D2bpppbAnalyticContinuationProof
namespace FLT
namespace Gapsw80T73B4ppppFalseprobeMarcRemint
end FLT.Gapsw80T73B4ppppFalseprobeMarcRemint
namespace FLT
namespace Gapsw80T74B4vFloor24SubDecomp
end FLT.Gapsw80T74B4vFloor24SubDecomp
namespace FLT
namespace Gapsw80T75BourbakiKernelDef
end FLT.Gapsw80T75BourbakiKernelDef
namespace FLT
namespace Gapsw80T9ClassSumA1Closure
end FLT.Gapsw80T9ClassSumA1Closure
namespace Filter
p2m_export "Filter" "pi Tendsto.atTop_div_const Tendsto tendsto_neg_atTop_atBot atTop eventually_inf_principal comap principal tendsto_id Eventually.of_forall"
p2m_open "Filter"
end Filter
namespace MeasureTheory
p2m_export "MeasureTheory" "Ioi_ae_eq_Ici setIntegral_congr_fun integral_nonneg norm_integral_le_of_norm_le integral_comp_mul_left_Ioi IntegrableOn pdf Integrable.mono' ae_restrict_mem covolume integrableOn_Ioi_deriv_of_nonneg integral setIntegral_mono_on IntegrableOn.union integrableOn_univ Integrable integral_tsum_of_summable_integral_norm integral_Ioi_of_hasDerivAt_of_tendsto integral_add integral_const_mul AEStronglyMeasurable integral_neg_eq_self setIntegral_union"
p2m_open "MeasureTheory"
end MeasureTheory
namespace Module
p2m_export "Module" "reflection finrank"
p2m_open "Module"
end Module
namespace NumberField
p2m_export "NumberField" "IsTotallyComplex place InfinitePlace"
p2m_open "NumberField"
end NumberField
namespace NumberField
p2m_export "NumberField" "IsTotallyComplex place InfinitePlace"
namespace InfinitePlace
p2m_export "NumberField.InfinitePlace" "comap apply"
p2m_open "NumberField.InfinitePlace NumberField"
end NumberField.InfinitePlace
namespace Real
p2m_export "Real" "tendsto_exp_atBot sqrt_pos log_le_sub_one_of_pos sinh differentiable_exp sinh_eq continuous_cosh exp_zero sqrt_le_sqrt sinh_two_mul cosh_zero one_le_exp log_one contDiff_exp tendsto_exp_neg_atTop_nhds_zero cosh_eq sqrt_sq_eq_abs Gamma log_inv pi_lt_d6 log_lt_iff_lt_exp exp_nat_mul exp cos_neg abs_exp exp_pos exp_le_exp pi_gt_d6 eulerMascheroniConstant eulerMascheroniSeq hasDerivAt_cosh sqrt_lt_sqrt lt_log_iff_exp_lt cosh_sq_sub_sinh_sq continuous_cos abs_cos_le_one sqrt_eq_rpow cosh_pos tanh_eq_sinh_div_cosh cosh_neg cosh pi_lt_four continuous_exp continuousAt_log log norm_eq_abs exp_neg pi_pos sinh_zero exp_log lattice exp_le_one_iff exp_lt_exp log_mul tanh eulerMascheroniSeq_lt_eulerMascheroniConstant one_lt_exp_iff cos hasDerivAt_exp exp_bound hasDerivAt_log sum_le_exp_of_nonneg sign add_one_le_exp exp_add sqrt_sq log_two_lt_d9 log_pow continuous_sinh log_div sqrt"
p2m_open "Real"
end Real

section

namespace FLT
namespace Gapsw80T13AffineArchTermA34Redecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
p2m_open "NumberField P2MW.S_Real_poitouKernel_admissible_and_archBound.NumberField NumberField.InfinitePlace P2MW.S_Real_poitouKernel_admissible_and_archBound.NumberField.InfinitePlace Module P2MW.S_Real_poitouKernel_admissible_and_archBound.Module"

noncomputable def gapsw80_t13_poleTerm (F : ℝ → ℝ) : ℝ :=
  2 * ∫ x in Set.Ioi (0:ℝ), F x * (Real.exp (x / 2) + Real.exp (-(x / 2)))

end FLT.Gapsw80T13AffineArchTermA34Redecomp

end

section

namespace FLT
namespace Gapsw80T21D2SubDecompWire

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T20LambdaLogDerivProductRule
p2m_open "NumberField P2MW.S_Real_poitouKernel_admissible_and_archBound.NumberField NumberField.InfinitePlace P2MW.S_Real_poitouKernel_admissible_and_archBound.NumberField.InfinitePlace Module P2MW.S_Real_poitouKernel_admissible_and_archBound.Module Complex P2MW.S_Real_poitouKernel_admissible_and_archBound.Complex"

noncomputable def gapsw80_t21_zeroKernelTransform (F : ℝ → ℝ) (ρ : ℂ) : ℝ :=
  ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x)

end FLT.Gapsw80T21D2SubDecompWire

end

section

namespace FLT
namespace Gapsw80T18ArchDerivedA34Redecomp

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T11ExplicitFormulaA34Decomp
open FLT.Gapsw80T13AffineArchTermA34Redecomp
p2m_open "NumberField P2MW.S_Real_poitouKernel_admissible_and_archBound.NumberField NumberField.InfinitePlace P2MW.S_Real_poitouKernel_admissible_and_archBound.NumberField.InfinitePlace Module P2MW.S_Real_poitouKernel_admissible_and_archBound.Module"

noncomputable def gapsw80_t18_archDerived (F : ℝ → ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
    - ∫ x in Set.Ioi (0:ℝ), (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2)))

noncomputable def gapsw80_t18_archTermDerived (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * gapsw80_t18_archDerived F - gapsw80_t13_poleTerm F

end FLT.Gapsw80T18ArchDerivedA34Redecomp

end

section

namespace FLT
namespace Gapsw80T23OdlyzkoKernelStripRemint

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T22AdmissibilityStripGapProbe
p2m_open "Complex P2MW.S_Real_poitouKernel_admissible_and_archBound.Complex"

def gapsw80_t23_OdlyzkoAdmissibleKernelStrip (F : ℝ → ℝ) : Prop :=
  Differentiable ℝ F ∧ (∀ x : ℝ, F (-x) = F x) ∧ F 0 = 1 ∧ (∀ x : ℝ, 0 ≤ F x) ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → 0 ≤ gapsw80_t21_zeroKernelTransform F ρ

end FLT.Gapsw80T23OdlyzkoKernelStripRemint

end

section

namespace FLT
namespace Gapsw80T69AdmC2RemintZktSummable

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T9ClassSumA1Closure
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T19B2ppHadamardDecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T23OdlyzkoKernelStripRemint
open FLT.Gapsw80T24StripMigrationChainStart
open FLT.Gapsw80T25B4pppStripSinglePointAbsorption
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T64D2fGaussianMollificationProof
open FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint
open FLT.Gapsw80T68D2bppExplicitFormulaSubDecomp
p2m_open "NumberField P2MW.S_Real_poitouKernel_admissible_and_archBound.NumberField NumberField.InfinitePlace P2MW.S_Real_poitouKernel_admissible_and_archBound.NumberField.InfinitePlace Module P2MW.S_Real_poitouKernel_admissible_and_archBound.Module Complex P2MW.S_Real_poitouKernel_admissible_and_archBound.Complex MeasureTheory P2MW.S_Real_poitouKernel_admissible_and_archBound.MeasureTheory"

def gapsw80_t69_KernelC2Decay (F : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 F ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))

def gapsw80_t69_OdlyzkoAdmissibleKernelStripC2 (F : ℝ → ℝ) : Prop :=
  gapsw80_t23_OdlyzkoAdmissibleKernelStrip F ∧ gapsw80_t69_KernelC2Decay F

end FLT.Gapsw80T69AdmC2RemintZktSummable

end

section

namespace FLT
namespace Gapsw80T74B4vFloor24SubDecomp

open FLT.Gapsw48T2OdlyzkoDeg24PinCarrier
open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw52T2CarrierContentAtoms
open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T23OdlyzkoKernelStripRemint
open FLT.Gapsw80T24StripMigrationChainStart
open FLT.Gapsw80T62ArchGammaKernelRemintWire
open FLT.Gapsw80T67D2bpPrimeSumFalseprobeRemint
open FLT.Gapsw80T69AdmC2RemintZktSummable
open FLT.Gapsw80T70D2bpppZeroSideEvalSubDecomp
open FLT.Gapsw80T71D2bpppbAnalyticContinuationProof
open FLT.Gapsw80T73B4ppppFalseprobeMarcRemint
p2m_open "NumberField P2MW.S_Real_poitouKernel_admissible_and_archBound.NumberField Module P2MW.S_Real_poitouKernel_admissible_and_archBound.Module"

def gapsw80_t74_BourbakiFloorAtTwentyFourMarc : Prop :=
  ∃ F : ℝ → ℝ, gapsw80_t69_OdlyzkoAdmissibleKernelStripC2 F ∧
    (24 : ℝ) * Real.log (9805 / 1000)
      ≤ gapsw80_t18_archTermDerived F 24 + 24 * Real.log 2

end FLT.Gapsw80T74B4vFloor24SubDecomp

end

section

namespace FLT
namespace Gapsw80T75BourbakiKernelDef

open FLT.Gapsw50T2ExplicitFormulaDecompositionPin
open FLT.Gapsw80T13AffineArchTermA34Redecomp
open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T23OdlyzkoKernelStripRemint
open FLT.Gapsw80T69AdmC2RemintZktSummable
open FLT.Gapsw80T74B4vFloor24SubDecomp
p2m_open "Real P2MW.S_Real_poitouKernel_admissible_and_archBound.Real MeasureTheory P2MW.S_Real_poitouKernel_admissible_and_archBound.MeasureTheory"

noncomputable def gapsw80_t75_bourbakiKernel : ℝ → ℝ :=
  fun x => Real.exp (-(11/100) * x ^ 2) / Real.cosh (x / 2)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_pin (x : ℝ) :
    gapsw80_t75_bourbakiKernel x
      = Real.exp (-(11/100) * x ^ 2) / Real.cosh (x / 2) := by
  have _em := Classical.em
  rfl

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_exp_abs_le_two_cosh (x : ℝ) :
    Real.exp (|x| / 2) ≤ 2 * Real.cosh (x / 2) := by
  have _em := Classical.em
  rw [Real.cosh_eq (x / 2), mul_div_cancel₀ _ (two_ne_zero)]
  rcases abs_choice x with h | h
  · rw [h]; linarith [Real.exp_pos (-(x/2))]
  · rw [h, neg_div]; linarith [Real.exp_pos (x/2)]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_pos (x : ℝ) :
    0 < gapsw80_t75_bourbakiKernel x :=
  div_pos (Real.exp_pos _) (Real.cosh_pos _)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_raw_decay (x : ℝ) :
    gapsw80_t75_bourbakiKernel x
      ≤ 2 * Real.exp (-(11/100) * x ^ 2 - |x| / 2) := by
  have _em := Classical.em
  have hcosh := gapsw80_t75_exp_abs_le_two_cosh x
  rw [gapsw80_t75_bourbakiKernel, div_le_iff₀ (Real.cosh_pos _)]
  calc Real.exp (-(11/100)*x^2)
      = Real.exp (-(11/100)*x^2 - |x|/2) * Real.exp (|x|/2) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(11/100)*x^2 - |x|/2) * (2 * Real.cosh (x/2)) :=
        mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
    _ = 2 * Real.exp (-(11/100)*x^2 - |x|/2) * Real.cosh (x/2) := by ring

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_linear_sub_sq_le {a b t : ℝ} (hb : 0 < b) :
    a * t - b * t ^ 2 ≤ a ^ 2 / (4 * b) := by
  have _em := Classical.em
  have hsq : (0:ℝ) ≤ (a - 2*b*t)^2 := sq_nonneg _
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*b)]
  nlinarith [hsq]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_even (x : ℝ) :
    gapsw80_t75_bourbakiKernel (-x) = gapsw80_t75_bourbakiKernel x := by
  have _em := Classical.em
  simp only [gapsw80_t75_bourbakiKernel, neg_sq, neg_div, Real.cosh_neg]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_zero :
    gapsw80_t75_bourbakiKernel 0 = 1 := by
  have _em := Classical.em
  simp [gapsw80_t75_bourbakiKernel, Real.cosh_zero]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_nonneg (x : ℝ) :
    0 ≤ gapsw80_t75_bourbakiKernel x :=
  (gapsw80_t75_bourbakiKernel_pos x).le

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_decay :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ,
      |gapsw80_t75_bourbakiKernel x|
        ≤ c * Real.exp (-(1/2 + ε) * |x|) := by
  have _em := Classical.em
  refine ⟨2 * Real.exp (25/176), 1/4, by positivity, by norm_num, fun x => ?_⟩
  rw [abs_of_pos (gapsw80_t75_bourbakiKernel_pos x)]
  refine (gapsw80_t75_bourbakiKernel_raw_decay x).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  gcongr
  have hsq : (0:ℝ) ≤ (11/100) * (|x| - 25/22)^2 := by positivity
  nlinarith [sq_abs x, hsq]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_contDiff_cosh_half :
    ContDiff ℝ ⊤ (fun x : ℝ => Real.cosh (x / 2)) := by
  have _em := Classical.em
  have h : (fun x : ℝ => Real.cosh (x/2))
      = fun x => (Real.exp (x/2) + Real.exp (-(x/2))) / 2 :=
    funext (fun x => Real.cosh_eq (x / 2))
  rw [h]
  have hhalf : ContDiff ℝ ⊤ (fun x : ℝ => x / 2) := contDiff_id.div_const 2
  exact ((Real.contDiff_exp.comp hhalf).add
    (Real.contDiff_exp.comp hhalf.neg)).div_const 2

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_contDiff :
    ContDiff ℝ 2 gapsw80_t75_bourbakiKernel := by
  have _em := Classical.em
  have hexponent : ContDiff ℝ ⊤ (fun x : ℝ => -(11/100) * x^2) :=
    contDiff_const.mul (contDiff_id.pow 2)
  have hnum : ContDiff ℝ ⊤ (fun x : ℝ => Real.exp (-(11/100) * x^2)) :=
    Real.contDiff_exp.comp hexponent
  exact (hnum.div gapsw80_t75_contDiff_cosh_half
    (fun x => (Real.cosh_pos _).ne')).of_le le_top

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_differentiable :
    Differentiable ℝ gapsw80_t75_bourbakiKernel :=
  gapsw80_t75_bourbakiKernel_contDiff.differentiable (by norm_num)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_hasDerivAt_cosh_half (x : ℝ) :
    HasDerivAt (fun y => Real.cosh (y/2)) ((1/2) * Real.sinh (x/2)) x := by
  have _em := Classical.em
  have hch : (fun y : ℝ => Real.cosh (y/2))
      = fun y => (Real.exp (y/2) + Real.exp (-(y/2))) / 2 :=
    funext (fun y => Real.cosh_eq (y/2))
  rw [hch]
  have hD : HasDerivAt (fun y : ℝ => (Real.exp (y/2) + Real.exp (-(y/2))) / 2)
      ((Real.exp (x/2) * (1/2) + Real.exp (-(x/2)) * (-(1/2))) / 2) x := by
    apply HasDerivAt.div_const
    exact ((Real.hasDerivAt_exp (x/2)).comp x
        ((hasDerivAt_id x).div_const 2)).add
      ((Real.hasDerivAt_exp (-(x/2))).comp x
        ((hasDerivAt_id x).div_const 2).neg)
  convert hD using 1 <;> try rfl
  rw [Real.sinh_eq]; ring

set_option maxHeartbeats 6400000 in

theorem gapsw80_t75_bourbakiKernel_hasDerivAt (x : ℝ) :
    HasDerivAt gapsw80_t75_bourbakiKernel
      (gapsw80_t75_bourbakiKernel x
        * (-(11/50) * x - (1/2) * (Real.sinh (x/2) / Real.cosh (x/2)))) x := by
  have _em := Classical.em
  have hN : HasDerivAt (fun y => Real.exp (-(11/100) * y^2))
      (Real.exp (-(11/100)*x^2) * (-(11/50)*x)) x := by
    have := (Real.hasDerivAt_exp (-(11/100)*x^2)).comp x
      ((hasDerivAt_pow 2 x).const_mul (-(11/100)))
    convert this using 1 <;> try rfl
    push_cast; ring
  have hD := gapsw80_t75_hasDerivAt_cosh_half x
  have hquot := hN.div hD (Real.cosh_pos _).ne'
  convert hquot using 1 <;> try rfl
  rw [gapsw80_t75_bourbakiKernel]
  have hne : Real.cosh (x/2) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiKernel_deriv :
    deriv gapsw80_t75_bourbakiKernel
      = fun x => gapsw80_t75_bourbakiKernel x
          * (-(11/50) * x - (1/2) * (Real.sinh (x/2) / Real.cosh (x/2))) :=
  funext (fun x => (gapsw80_t75_bourbakiKernel_hasDerivAt x).deriv)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_g1_bound (x : ℝ) :
    |-(11/50:ℝ) * x - (1/2) * (Real.sinh (x/2) / Real.cosh (x/2))|
      ≤ (11/50) * |x| + 1/2 := by
  have _em := Classical.em
  have htanh : |Real.sinh (x/2) / Real.cosh (x/2)| ≤ 1 := by
    rw [abs_div, abs_of_pos (Real.cosh_pos _), div_le_one (Real.cosh_pos _)]
    have hsq : Real.sinh (x/2)^2 ≤ Real.cosh (x/2)^2 := by
      linarith [Real.cosh_sq_sub_sinh_sq (x/2)]
    calc |Real.sinh (x/2)| = Real.sqrt (Real.sinh (x/2)^2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (Real.cosh (x/2)^2) := Real.sqrt_le_sqrt hsq
      _ = Real.cosh (x/2) := Real.sqrt_sq (Real.cosh_pos _).le
  have habs := abs_le.mp htanh
  rw [abs_le]
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; constructor <;> nlinarith [habs.1, habs.2]
  · rw [abs_of_neg hx]; constructor <;> nlinarith [habs.1, habs.2]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_abs_deriv_le (x : ℝ) :
    |deriv gapsw80_t75_bourbakiKernel x|
      ≤ gapsw80_t75_bourbakiKernel x * ((11/50) * |x| + 1/2) := by
  have _em := Classical.em
  rw [gapsw80_t75_bourbakiKernel_deriv, abs_mul,
    abs_of_pos (gapsw80_t75_bourbakiKernel_pos x)]
  exact mul_le_mul_of_nonneg_left (gapsw80_t75_g1_bound x)
    (gapsw80_t75_bourbakiKernel_pos x).le

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_affine_le_exp (x : ℝ) :
    (11/50) * |x| + 1/2 ≤ (1/2) * Real.exp ((11/25) * |x|) := by
  have _em := Classical.em
  have h := Real.add_one_le_exp ((11/25) * |x|)
  linarith [h]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t75_weighted_decay (a : ℝ) (x : ℝ) :
    gapsw80_t75_bourbakiKernel x * Real.exp (a * |x|)
      ≤ 2 * Real.exp ((25/11) * (a + 1/4)^2) * Real.exp (-(3/4) * |x|) := by
  have _em := Classical.em
  refine (mul_le_mul_of_nonneg_right (gapsw80_t75_bourbakiKernel_raw_decay x)
    (Real.exp_pos _).le).trans ?_
  rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)

  have hquad := gapsw80_t75_linear_sub_sq_le
    (a := a + 1/4) (b := 11/100) (t := |x|) (by norm_num)
  have hsq : |x|^2 = x^2 := sq_abs x
  have heq : (a + 1/4)^2 / (4*(11/100)) = (25/11) * (a + 1/4)^2 := by ring
  rw [heq] at hquad
  linarith [hquad, hsq ▸ (le_refl (x^2))]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_hasDerivAt_sinh_half (x : ℝ) :
    HasDerivAt (fun y => Real.sinh (y/2)) ((1/2) * Real.cosh (x/2)) x := by
  have _em := Classical.em
  have hsh : (fun y : ℝ => Real.sinh (y/2))
      = fun y => (Real.exp (y/2) - Real.exp (-(y/2))) / 2 :=
    funext (fun y => Real.sinh_eq (y/2))
  rw [hsh]
  have hD : HasDerivAt (fun y : ℝ => (Real.exp (y/2) - Real.exp (-(y/2))) / 2)
      ((Real.exp (x/2) * (1/2) - Real.exp (-(x/2)) * (-(1/2))) / 2) x := by
    apply HasDerivAt.div_const
    exact ((Real.hasDerivAt_exp (x/2)).comp x
        ((hasDerivAt_id x).div_const 2)).sub
      ((Real.hasDerivAt_exp (-(x/2))).comp x
        ((hasDerivAt_id x).div_const 2).neg)
  convert hD using 1 <;> try rfl
  rw [Real.cosh_eq]; ring

set_option maxHeartbeats 6400000 in

theorem gapsw80_t75_hasDerivAt_g1 (x : ℝ) :
    HasDerivAt
      (fun y => -(11/50:ℝ) * y - (1/2) * (Real.sinh (y/2) / Real.cosh (y/2)))
      (-(11/50) - (1/4) / (Real.cosh (x/2))^2) x := by
  have _em := Classical.em
  have hS := gapsw80_t75_hasDerivAt_sinh_half x
  have hC := gapsw80_t75_hasDerivAt_cosh_half x
  have hQ := hS.div hC (Real.cosh_pos _).ne'
  have hLin : HasDerivAt (fun y => -(11/50:ℝ) * y) (-(11/50)) x := by
    simpa using (hasDerivAt_id x).const_mul (-(11/50:ℝ))
  have hFull := hLin.sub (hQ.const_mul (1/2))
  convert hFull using 1 <;> try rfl
  have hne : Real.cosh (x/2) ≠ 0 := (Real.cosh_pos _).ne'
  have hid := Real.cosh_sq_sub_sinh_sq (x/2)
  rw [show (1 / 2 * Real.cosh (x / 2) * Real.cosh (x / 2) - Real.sinh (x / 2) * (1 / 2 * Real.sinh (x / 2)))
      = 1 / 2 * (Real.cosh (x / 2) ^ 2 - Real.sinh (x / 2) ^ 2) by ring, hid]
  ring

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_g1'_bound (x : ℝ) :
    |-(11/50:ℝ) - (1/4) / (Real.cosh (x/2))^2| ≤ 1 := by
  have _em := Classical.em
  have hc : (0:ℝ) < (Real.cosh (x/2))^2 := pow_pos (Real.cosh_pos _) 2
  have h1 : (1:ℝ) ≤ (Real.cosh (x/2))^2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (x/2), sq_nonneg (Real.sinh (x/2))]
  have hinv : (1/4:ℝ) / (Real.cosh (x/2))^2 ≤ 1/4 := by
    rw [div_le_iff₀ hc]; linarith
  have hpos : (0:ℝ) ≤ (1/4) / (Real.cosh (x/2))^2 := by positivity
  rw [abs_le]; constructor <;> linarith

set_option maxHeartbeats 6400000 in

theorem gapsw80_t75_abs_deriv2_le (x : ℝ) :
    |deriv (deriv gapsw80_t75_bourbakiKernel) x|
      ≤ gapsw80_t75_bourbakiKernel x * (((11/50)*|x| + 1/2)^2 + 1) := by
  have _em := Classical.em
  have hFg1 : deriv gapsw80_t75_bourbakiKernel
      = fun y => gapsw80_t75_bourbakiKernel y
          * (-(11/50) * y - (1/2) * (Real.sinh (y/2) / Real.cosh (y/2))) :=
    gapsw80_t75_bourbakiKernel_deriv
  rw [hFg1]
  have hD : HasDerivAt
      (fun y => gapsw80_t75_bourbakiKernel y
        * (-(11/50) * y - (1/2) * (Real.sinh (y/2) / Real.cosh (y/2))))
      (gapsw80_t75_bourbakiKernel x
          * (-(11/50)*x - (1/2)*(Real.sinh (x/2)/Real.cosh (x/2)))
          * (-(11/50)*x - (1/2)*(Real.sinh (x/2)/Real.cosh (x/2)))
        + gapsw80_t75_bourbakiKernel x
          * (-(11/50) - (1/4)/(Real.cosh (x/2))^2)) x :=
    (gapsw80_t75_bourbakiKernel_hasDerivAt x).mul (gapsw80_t75_hasDerivAt_g1 x)
  rw [hD.deriv]
  have hg1 := gapsw80_t75_g1_bound x
  have hg1' := gapsw80_t75_g1'_bound x
  have hF := (gapsw80_t75_bourbakiKernel_pos x).le
  set g1 := -(11/50:ℝ)*x - (1/2)*(Real.sinh (x/2)/Real.cosh (x/2))
  set g1' := -(11/50:ℝ) - (1/4)/(Real.cosh (x/2))^2
  have habs_sq : |g1| * |g1| ≤ ((11/50)*|x|+1/2) * ((11/50)*|x|+1/2) :=
    mul_le_mul hg1 hg1 (abs_nonneg _) (by positivity)
  calc |gapsw80_t75_bourbakiKernel x * g1 * g1 + gapsw80_t75_bourbakiKernel x * g1'|
      ≤ |gapsw80_t75_bourbakiKernel x * g1 * g1|
        + |gapsw80_t75_bourbakiKernel x * g1'| := abs_add_le _ _
    _ = gapsw80_t75_bourbakiKernel x * (|g1| * |g1|)
        + gapsw80_t75_bourbakiKernel x * |g1'| := by
        simp only [abs_mul, abs_of_nonneg hF]; ring
    _ ≤ gapsw80_t75_bourbakiKernel x * (((11/50)*|x|+1/2)*((11/50)*|x|+1/2))
        + gapsw80_t75_bourbakiKernel x * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left habs_sq hF)
          (mul_le_mul_of_nonneg_left hg1' hF)
    _ = gapsw80_t75_bourbakiKernel x * (((11/50)*|x|+1/2)^2 + 1) := by ring

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_abs_deriv2_decay (x : ℝ) :
    |deriv (deriv gapsw80_t75_bourbakiKernel) x|
      ≤ 2 * Real.exp (7/2) * Real.exp (-(3/4) * |x|) := by
  have _em := Classical.em
  have hD2 := gapsw80_t75_abs_deriv2_le x
  have hF := (gapsw80_t75_bourbakiKernel_pos x).le
  have haff := gapsw80_t75_affine_le_exp x
  have hsqb : ((11/50:ℝ)*|x| + 1/2)^2 + 1 ≤ (5/4) * Real.exp ((22/25)*|x|) := by
    have h1 : ((11/50:ℝ)*|x| + 1/2)^2 ≤ (1/4) * Real.exp ((22/25)*|x|) := by
      have := sq_le_sq' (by linarith [abs_nonneg x] :
        -((1/2:ℝ)*Real.exp ((11/25)*|x|)) ≤ (11/50)*|x| + 1/2) haff
      calc ((11/50:ℝ)*|x|+1/2)^2 ≤ ((1/2)*Real.exp ((11/25)*|x|))^2 := this
        _ = (1/4) * Real.exp ((22/25)*|x|) := by
            rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    have h2 : (1:ℝ) ≤ Real.exp ((22/25)*|x|) :=
      Real.one_le_exp (by positivity)
    linarith
  calc |deriv (deriv gapsw80_t75_bourbakiKernel) x|
      ≤ gapsw80_t75_bourbakiKernel x * (((11/50)*|x|+1/2)^2 + 1) := hD2
    _ ≤ gapsw80_t75_bourbakiKernel x * ((5/4) * Real.exp ((22/25)*|x|)) :=
        mul_le_mul_of_nonneg_left hsqb hF
    _ = (5/4) * (gapsw80_t75_bourbakiKernel x * Real.exp ((22/25)*|x|)) := by ring
    _ ≤ (5/4) * (2 * Real.exp ((25/11)*(22/25+1/4)^2) * Real.exp (-(3/4)*|x|)) :=
        mul_le_mul_of_nonneg_left (gapsw80_t75_weighted_decay (22/25) x)
          (by norm_num)
    _ ≤ 2 * Real.exp (7/2) * Real.exp (-(3/4)*|x|) := by
        have heq : (25/11:ℝ)*(22/25+1/4)^2 = 12769/4400 := by norm_num
        rw [heq]
        have hle : (5/4:ℝ) * (2 * Real.exp (12769/4400)) ≤ 2 * Real.exp (7/2) := by
          have hlog54 : Real.log (5/4:ℝ) ≤ 1/4 :=
            (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
          have h := Real.exp_le_exp.mpr
            (show (12769/4400:ℝ) + Real.log (5/4) ≤ 7/2 by linarith)
          rw [Real.exp_add, Real.exp_log (by norm_num)] at h
          linarith
        nlinarith [Real.exp_pos (-(3/4:ℝ)*|x|), hle]

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_abs_deriv_decay (x : ℝ) :
    |deriv gapsw80_t75_bourbakiKernel x|
      ≤ Real.exp (4761/4400) * Real.exp (-(3/4) * |x|) := by
  have _em := Classical.em
  have h1 := gapsw80_t75_abs_deriv_le x
  have h2 := gapsw80_t75_affine_le_exp x
  have h3 := gapsw80_t75_weighted_decay (11/25) x
  have hF := gapsw80_t75_bourbakiKernel_pos x
  calc |deriv gapsw80_t75_bourbakiKernel x|
      ≤ gapsw80_t75_bourbakiKernel x * ((11/50)*|x| + 1/2) := h1
    _ ≤ gapsw80_t75_bourbakiKernel x * ((1/2) * Real.exp ((11/25)*|x|)) :=
        mul_le_mul_of_nonneg_left h2 hF.le
    _ = (1/2) * (gapsw80_t75_bourbakiKernel x * Real.exp ((11/25)*|x|)) := by ring
    _ ≤ (1/2) * (2 * Real.exp ((25/11)*(11/25+1/4)^2) * Real.exp (-(3/4)*|x|)) :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = Real.exp (4761/4400) * Real.exp (-(3/4)*|x|) := by norm_num; ring_nf

set_option maxHeartbeats 6400000 in

theorem gapsw80_t75_bourbakiKernel_iterDeriv_decay :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k gapsw80_t75_bourbakiKernel x|
        ≤ c * Real.exp (-(1/2 + ε) * |x|) := by
  have _em := Classical.em
  refine ⟨2 * Real.exp (7/2), 1/4, by positivity, by norm_num, fun k x => ?_⟩
  have hrate : -((1:ℝ)/2 + 1/4) = -(3/4) := by norm_num
  rw [hrate]
  have hk3 : (k : ℕ) < 3 := k.isLt
  interval_cases (k : ℕ)
  ·
    rw [iteratedDeriv_zero, abs_of_pos (gapsw80_t75_bourbakiKernel_pos x)]
    have hwd := gapsw80_t75_weighted_decay 0 x
    rw [zero_mul, Real.exp_zero, mul_one] at hwd
    refine hwd.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num))
      (by norm_num)
  ·
    rw [iteratedDeriv_one]
    refine (gapsw80_t75_abs_deriv_decay x).trans
      (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    calc Real.exp (4761/4400) ≤ Real.exp (7/2) :=
          Real.exp_le_exp.mpr (by norm_num)
      _ ≤ 2 * Real.exp (7/2) := by linarith [Real.exp_pos (7/2:ℝ)]
  ·
    simp only [iteratedDeriv_succ, iteratedDeriv_one]
    exact gapsw80_t75_abs_deriv2_decay x

set_option maxHeartbeats 6400000 in

theorem gapsw80_t75_poleTerm_bourbakiKernel :
    gapsw80_t13_poleTerm gapsw80_t75_bourbakiKernel
      = 2 * Real.sqrt (100 * Real.pi / 11) := by
  have _em := Classical.em
  simp only [gapsw80_t13_poleTerm, gapsw80_t75_bourbakiKernel]
  have hcancel : ∀ x : ℝ,
      Real.exp (-(11/100) * x^2) / Real.cosh (x/2)
        * (Real.exp (x/2) + Real.exp (-(x/2)))
      = 2 * Real.exp (-(11/100) * x^2) := by
    intro x
    have hne : Real.exp (x/2) + Real.exp (-(x/2)) ≠ 0 := by positivity
    rw [Real.cosh_eq (x/2), div_div_eq_mul_div, div_mul_cancel₀ _ hne]
    ring
  simp_rw [hcancel]
  rw [MeasureTheory.integral_const_mul, integral_gaussian_Ioi,
    show (Real.pi / (11/100) : ℝ) = 100 * Real.pi / 11 by ring]
  ring

def gapsw80_t75_BourbakiArchDerivedLowerBound : Prop :=
  (24 : ℝ) * Real.log (9805 / 1000)
    ≤ gapsw80_t18_archTermDerived gapsw80_t75_bourbakiKernel 24 + 24 * Real.log 2

set_option maxHeartbeats 3200000 in

theorem gapsw80_t75_bourbakiArchDerivedLowerBound_iff :
    gapsw80_t75_BourbakiArchDerivedLowerBound
      ↔ Real.log (9805/2000) + (1/12) * Real.sqrt (100 * Real.pi / 11)
          ≤ gapsw80_t18_archDerived gapsw80_t75_bourbakiKernel := by
  have _em := Classical.em
  have hlog : Real.log ((9805:ℝ)/2000) = Real.log (9805/1000) - Real.log 2 := by
    rw [show ((9805:ℝ)/2000) = (9805/1000) / 2 by norm_num,
      Real.log_div (by norm_num) two_ne_zero]
  rw [gapsw80_t75_BourbakiArchDerivedLowerBound, gapsw80_t18_archTermDerived,
    gapsw80_t75_poleTerm_bourbakiKernel, hlog]
  push_cast
  constructor <;> intro h <;> linarith

def gapsw80_t75_BourbakiStripPositivity : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
    0 ≤ gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel ρ

set_option maxHeartbeats 6400000 in

theorem gapsw80_t75_B4vi_of_B4via_B4vib
    (ha : gapsw80_t75_BourbakiArchDerivedLowerBound)
    (hb : gapsw80_t75_BourbakiStripPositivity) :
    gapsw80_t74_BourbakiFloorAtTwentyFourMarc :=
  ⟨gapsw80_t75_bourbakiKernel,
    ⟨⟨gapsw80_t75_bourbakiKernel_differentiable,
      gapsw80_t75_bourbakiKernel_even,
      gapsw80_t75_bourbakiKernel_zero,
      gapsw80_t75_bourbakiKernel_nonneg,
      gapsw80_t75_bourbakiKernel_decay, hb⟩,
     gapsw80_t75_bourbakiKernel_contDiff,
     gapsw80_t75_bourbakiKernel_iterDeriv_decay⟩, ha⟩

end FLT.Gapsw80T75BourbakiKernelDef

end

section

set_option maxHeartbeats 3200000

namespace FLT
namespace Gapsw80T76BourbakiStripPositivityProof

open FLT.Gapsw80T21D2SubDecompWire
open FLT.Gapsw80T75BourbakiKernelDef
p2m_open "Complex P2MW.S_Real_poitouKernel_admissible_and_archBound.Complex MeasureTheory P2MW.S_Real_poitouKernel_admissible_and_archBound.MeasureTheory"

noncomputable def gapsw80_t76_bourbakiLaplace (ρ : ℂ) : ℂ :=
  ∫ x : ℝ, (gapsw80_t75_bourbakiKernel x : ℂ) * Complex.exp ((ρ - 1/2) * x)

set_option maxHeartbeats 3200000 in

theorem gapsw80_t76_integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
  have _em := Classical.em
  have hIci : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Ici 0) := by
    have h : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hc).congr_fun
        (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
    exact h.congr_set_ae Ioi_ae_eq_Ici.symm
  have hIic : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Set.Iic 0) := by
    have := hIci.comp_neg
    simp only [abs_neg] at this
    rwa [show -Set.Ici (0:ℝ) = Set.Iic 0 by rw [Set.neg_Ici, _root_.neg_zero]] at this
  rw [← integrableOn_univ, ← Set.Iic_union_Ici (a := (0:ℝ))]
  exact hIic.union hIci

set_option maxHeartbeats 3200000 in

theorem gapsw80_t76_integrand_continuous (ρ : ℂ) :
    Continuous (fun x : ℝ => (gapsw80_t75_bourbakiKernel x : ℂ)
      * Complex.exp ((ρ - 1/2) * x)) := by
  have _em := Classical.em
  exact (Complex.continuous_ofReal.comp
      gapsw80_t75_bourbakiKernel_contDiff.continuous).mul
    (Complex.continuous_exp.comp ((continuous_const).mul Complex.continuous_ofReal))

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_re_mul_ofReal (ρ : ℂ) (x : ℝ) :
    ((ρ - 1/2) * (x:ℂ)).re = (ρ.re - 1/2) * x := by
  have _em := Classical.em
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, mul_zero, sub_zero]
  congr 1
  simp [Complex.div_ofNat_re, Complex.one_re]

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_integrand_dom (ρ : ℂ) (hρ : |ρ.re - 1/2| ≤ 3/4) (x : ℝ) :
    ‖(gapsw80_t75_bourbakiKernel x : ℂ) * Complex.exp ((ρ - 1/2) * x)‖
      ≤ 2 * Real.exp (25/11) * Real.exp (-(3/4) * |x|) := by
  have _em := Classical.em
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    abs_of_pos (gapsw80_t75_bourbakiKernel_pos x), gapsw80_t76_re_mul_ofReal]
  have hle : (ρ.re - 1/2) * x ≤ (3/4) * |x| := by
    calc (ρ.re - 1/2) * x ≤ |(ρ.re - 1/2) * x| := le_abs_self _
      _ = |ρ.re - 1/2| * |x| := abs_mul _ _
      _ ≤ (3/4) * |x| := by gcongr
  calc gapsw80_t75_bourbakiKernel x * Real.exp ((ρ.re - 1/2) * x)
      ≤ gapsw80_t75_bourbakiKernel x * Real.exp ((3/4) * |x|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle)
          (gapsw80_t75_bourbakiKernel_pos x).le
    _ ≤ 2 * Real.exp ((25/11) * (3/4 + 1/4)^2) * Real.exp (-(3/4) * |x|) :=
        gapsw80_t75_weighted_decay (3/4) x
    _ = 2 * Real.exp (25/11) * Real.exp (-(3/4) * |x|) := by norm_num

set_option maxHeartbeats 3200000 in

theorem gapsw80_t76_dom_integrable :
    Integrable (fun x : ℝ => 2 * Real.exp (25/11) * Real.exp (-(3/4) * |x|)) := by
  have _em := Classical.em
  exact (gapsw80_t76_integrable_exp_neg_mul_abs
    (by norm_num : (0:ℝ) < 3/4)).const_mul _

set_option maxHeartbeats 3200000 in

theorem gapsw80_t76_integrand_integrable (ρ : ℂ) (hρ : |ρ.re - 1/2| ≤ 3/4) :
    Integrable (fun x : ℝ => (gapsw80_t75_bourbakiKernel x : ℂ)
      * Complex.exp ((ρ - 1/2) * x)) := by
  have _em := Classical.em
  exact (gapsw80_t76_dom_integrable.mono'
    (gapsw80_t76_integrand_continuous ρ).aestronglyMeasurable
    (Filter.Eventually.of_forall (gapsw80_t76_integrand_dom ρ hρ)))

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_zKT_eq_re_bourbakiLaplace (ρ : ℂ) (hρ : |ρ.re - 1/2| ≤ 3/4) :
    gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel ρ
      = (gapsw80_t76_bourbakiLaplace ρ).re := by
  have _em := Classical.em
  have hptwise : ∀ x : ℝ,
      gapsw80_t75_bourbakiKernel x * Real.exp ((ρ.re - 1/2) * x)
        * Real.cos (ρ.im * x)
        = ((gapsw80_t75_bourbakiKernel x : ℂ)
            * Complex.exp ((ρ - 1/2) * x)).re := by
    intro x
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_re, gapsw80_t76_re_mul_ofReal]
    have him : ((ρ - 1/2) * (x:ℂ)).im = ρ.im * x := by
      simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, add_zero]
      congr 1
      simp [Complex.div_ofNat_im, Complex.one_im]
    rw [him]; ring
  rw [gapsw80_t21_zeroKernelTransform, gapsw80_t76_bourbakiLaplace]
  simp_rw [hptwise]
  have hi := Complex.reCLM.integral_comp_comm (gapsw80_t76_integrand_integrable ρ hρ)
  simp only [Complex.reCLM_apply] at hi
  exact hi

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_deriv_integrand_dom (ρ : ℂ) (hρ : |ρ.re - 1/2| ≤ 3/4) (x : ℝ) :
    ‖(gapsw80_t75_bourbakiKernel x : ℂ) * Complex.exp ((ρ - 1/2) * x)
        * (x:ℂ)‖
      ≤ (4 * Real.exp (25/11)) * Real.exp (-(1/4) * |x|) := by
  have _em := Classical.em
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := gapsw80_t76_integrand_dom ρ hρ x
  have habs : |x| ≤ 2 * Real.exp (|x|/2) := by
    have h := Real.add_one_le_exp (|x|/2)
    linarith [Real.exp_pos (|x|/2)]
  calc ‖(gapsw80_t75_bourbakiKernel x : ℂ) * Complex.exp ((ρ-1/2) * x)‖ * |x|
      ≤ (2 * Real.exp (25/11) * Real.exp (-(3/4) * |x|)) * (2 * Real.exp (|x|/2)) :=
        mul_le_mul h1 habs (abs_nonneg _) (by positivity)
    _ = (4 * Real.exp (25/11)) * (Real.exp (-(3/4) * |x|) * Real.exp (|x|/2)) := by
        ring
    _ = (4 * Real.exp (25/11)) * Real.exp (-(1/4) * |x|) := by
        rw [← Real.exp_add]; ring_nf

set_option maxHeartbeats 3200000 in

theorem gapsw80_t76_dom_deriv_integrable :
    Integrable (fun x : ℝ => (4 * Real.exp (25/11))
      * Real.exp (-(1/4) * |x|)) := by
  have _em := Classical.em
  exact (gapsw80_t76_integrable_exp_neg_mul_abs
    (by norm_num : (0:ℝ) < 1/4)).const_mul _

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_integrand_hasDerivAt (x : ℝ) (ρ : ℂ) :
    HasDerivAt (fun ρ' => (gapsw80_t75_bourbakiKernel x : ℂ)
        * Complex.exp ((ρ' - 1/2) * x))
      ((gapsw80_t75_bourbakiKernel x : ℂ)
        * Complex.exp ((ρ - 1/2) * x) * (x:ℂ)) ρ := by
  have _em := Classical.em
  have h1 : HasDerivAt (fun ρ' : ℂ => (ρ' - 1/2) * (x:ℂ)) (x:ℂ) ρ := by
    have := (hasDerivAt_id ρ).sub_const (1/2:ℂ)
    simpa using this.mul_const (x:ℂ)
  have h2 := (Complex.hasDerivAt_exp ((ρ-1/2)*x)).comp ρ h1
  have h3 := h2.const_mul (gapsw80_t75_bourbakiKernel x : ℂ)
  convert h3 using 1 <;> try rfl
  ring

set_option maxHeartbeats 12800000 in

theorem gapsw80_t76_bourbakiLaplace_hasDerivAt (ρ : ℂ) (hρ : |ρ.re - 1/2| < 3/4) :
    HasDerivAt gapsw80_t76_bourbakiLaplace
      (∫ x : ℝ, (gapsw80_t75_bourbakiKernel x : ℂ)
        * Complex.exp ((ρ - 1/2) * x) * (x:ℂ)) ρ := by
  have _em := Classical.em
  set S := {z : ℂ | |z.re - 1/2| < 3/4}
  have hSopen : IsOpen S := isOpen_lt
    ((continuous_sub_right _).comp Complex.continuous_re).abs continuous_const
  have hSnhds : S ∈ nhds ρ := hSopen.mem_nhds hρ
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable
      (fun x : ℝ => (gapsw80_t75_bourbakiKernel x : ℂ)
        * Complex.exp ((z - 1/2) * x)) volume :=
    fun z => (gapsw80_t76_integrand_continuous z).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable
      (fun x : ℝ => (gapsw80_t75_bourbakiKernel x : ℂ)
        * Complex.exp ((ρ - 1/2) * x) * (x:ℂ)) volume :=
    ((gapsw80_t76_integrand_continuous ρ).mul Complex.continuous_ofReal).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hSnhds
    (Filter.Eventually.of_forall hmeas)
    (gapsw80_t76_integrand_integrable ρ hρ.le) hmeas'
    (Filter.Eventually.of_forall
      (fun x z hz => gapsw80_t76_deriv_integrand_dom z (le_of_lt hz) x))
    gapsw80_t76_dom_deriv_integrable
    (Filter.Eventually.of_forall
      (fun x z _ => gapsw80_t76_integrand_hasDerivAt x z))).2

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_bourbakiLaplace_diffContOnCl :
    DiffContOnCl ℂ gapsw80_t76_bourbakiLaplace (Complex.re ⁻¹' Set.Ioo 0 1) := by
  have _em := Classical.em
  set S := {z : ℂ | |z.re - 1/2| < 3/4}
  have hSopen : IsOpen S := isOpen_lt
    ((continuous_sub_right _).comp Complex.continuous_re).abs continuous_const
  have hdiffS : DifferentiableOn ℂ gapsw80_t76_bourbakiLaplace S := fun z hz =>
    (gapsw80_t76_bourbakiLaplace_hasDerivAt z hz).differentiableAt.differentiableWithinAt
  have hcl : closure (Complex.re ⁻¹' Set.Ioo 0 1) ⊆ S := by
    have h1 : closure (Complex.re ⁻¹' Set.Ioo 0 1)
        ⊆ Complex.re ⁻¹' (closure (Set.Ioo (0:ℝ) 1)) :=
      Complex.continuous_re.closure_preimage_subset _
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at h1
    intro z hz
    have : z.re ∈ Set.Icc (0:ℝ) 1 := h1 hz
    simp only [Set.mem_setOf_eq, S, abs_sub_lt_iff]
    constructor <;> linarith [this.1, this.2]
  exact (hdiffS.mono hcl).diffContOnCl

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_bourbakiLaplace_bound (ρ : ℂ) (hρ : ρ.re ∈ Set.Icc (0:ℝ) 1) :
    ‖gapsw80_t76_bourbakiLaplace ρ‖ ≤ 2 * Real.sqrt (100 * Real.pi / 11) := by
  have _em := Classical.em
  have hρ' : |ρ.re - 1/2| ≤ 1/2 := by
    rw [abs_sub_le_iff]; exact ⟨by linarith [hρ.2], by linarith [hρ.1]⟩
  have hdom : ∀ x, ‖(gapsw80_t75_bourbakiKernel x : ℂ)
      * Complex.exp ((ρ - 1/2) * x)‖ ≤ 2 * Real.exp (-(11/100) * x^2) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      abs_of_pos (gapsw80_t75_bourbakiKernel_pos x), gapsw80_t76_re_mul_ofReal]
    have hle : (ρ.re - 1/2) * x ≤ |x|/2 := by
      calc (ρ.re - 1/2) * x ≤ |ρ.re - 1/2| * |x| :=
            (le_abs_self _).trans (abs_mul _ _).le
        _ ≤ (1/2) * |x| := by gcongr
        _ = |x|/2 := by ring
    calc gapsw80_t75_bourbakiKernel x * Real.exp ((ρ.re - 1/2) * x)
        ≤ gapsw80_t75_bourbakiKernel x * Real.exp (|x|/2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle)
            (gapsw80_t75_bourbakiKernel_pos x).le
      _ ≤ 2 * Real.exp (-(11/100) * x^2 - |x|/2) * Real.exp (|x|/2) :=
          mul_le_mul_of_nonneg_right (gapsw80_t75_bourbakiKernel_raw_decay x)
            (Real.exp_pos _).le
      _ = 2 * Real.exp (-(11/100) * x^2) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hint : Integrable (fun x : ℝ => 2 * Real.exp (-(11/100) * x^2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 11/100)).const_mul 2
  calc ‖gapsw80_t76_bourbakiLaplace ρ‖
      ≤ ∫ x, 2 * Real.exp (-(11/100) * x^2) :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hdom)
    _ = 2 * ∫ x, Real.exp (-(11/100) * x^2) := integral_const_mul 2 _
    _ = 2 * Real.sqrt (Real.pi / (11/100)) := by rw [integral_gaussian (11/100)]
    _ = 2 * Real.sqrt (100 * Real.pi / 11) := by
        congr 1; congr 1; ring

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_zKT_even_symm (ρ : ℂ) :
    gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel ρ
      = gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel
          (1 - (starRingEnd ℂ) ρ) := by
  have _em := Classical.em
  rw [gapsw80_t21_zeroKernelTransform, gapsw80_t21_zeroKernelTransform]
  have hρ' : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.one_re, Complex.conj_re]
  have hρ'' : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by
    simp [Complex.sub_im, Complex.one_im, Complex.conj_im]
  rw [hρ', hρ'', ← integral_neg_eq_self
    (fun x => gapsw80_t75_bourbakiKernel x * Real.exp ((1 - ρ.re - 1/2) * x)
      * Real.cos (ρ.im * x)) volume]
  congr 1; funext x
  rw [gapsw80_t75_bourbakiKernel_even,
    show ρ.im * (-x) = -(ρ.im * x) by ring, Real.cos_neg,
    show (1 - ρ.re - 1/2) * (-x) = -((1 - ρ.re - 1/2) * x) by ring]
  congr 2
  ring

set_option maxHeartbeats 3200000 in

theorem gapsw80_t76_bourbaki_cosh_cancel (x : ℝ) :
    gapsw80_t75_bourbakiKernel x * (Real.exp (-(x/2)) + Real.exp (x/2))
      = 2 * Real.exp (-(11/100) * x^2) := by
  have _em := Classical.em
  have hne : Real.cosh (x/2) ≠ 0 := (Real.cosh_pos _).ne'
  rw [gapsw80_t75_bourbakiKernel_pin,
    show Real.exp (-(x/2)) + Real.exp (x/2) = 2 * Real.cosh (x/2) by
      rw [Real.cosh_eq]; ring]
  field_simp

set_option maxHeartbeats 3200000 in

theorem gapsw80_t76_zKT_integrand_integrable (σ t : ℝ) (hσ : σ = 0 ∨ σ = 1) :
    Integrable (fun x => gapsw80_t75_bourbakiKernel x
      * Real.exp ((σ - 1/2) * x) * Real.cos (t * x)) := by
  have _em := Classical.em
  refine (((integrable_exp_neg_mul_sq
    (by norm_num : (0:ℝ)<11/100)).const_mul 2).mono'
    ?_ (Filter.Eventually.of_forall (fun x => ?_)))
  · exact ((gapsw80_t75_bourbakiKernel_contDiff.continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (gapsw80_t75_bourbakiKernel_pos x),
      abs_of_pos (Real.exp_pos _)]
    have hcos : |Real.cos (t*x)| ≤ 1 := Real.abs_cos_le_one _
    have hσx : (σ - 1/2) * x ≤ |x|/2 := by
      have hσ' : |σ - 1/2| = 1/2 := by rcases hσ with h | h <;> rw [h] <;> norm_num
      calc (σ - 1/2) * x ≤ |(σ - 1/2) * x| := le_abs_self _
        _ = |σ - 1/2| * |x| := abs_mul _ _
        _ = (1/2) * |x| := by rw [hσ']
        _ = |x|/2 := by ring
    have hprod : gapsw80_t75_bourbakiKernel x * Real.exp ((σ-1/2)*x)
        ≤ 2 * Real.exp (-(11/100)*x^2) := by
      calc gapsw80_t75_bourbakiKernel x * Real.exp ((σ-1/2)*x)
          ≤ gapsw80_t75_bourbakiKernel x * Real.exp (|x|/2) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hσx)
              (gapsw80_t75_bourbakiKernel_pos x).le
        _ ≤ 2 * Real.exp (-(11/100)*x^2 - |x|/2) * Real.exp (|x|/2) :=
            mul_le_mul_of_nonneg_right (gapsw80_t75_bourbakiKernel_raw_decay x)
              (Real.exp_pos _).le
        _ = 2 * Real.exp (-(11/100)*x^2) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
    calc gapsw80_t75_bourbakiKernel x * Real.exp ((σ-1/2)*x) * |Real.cos (t*x)|
        ≤ 2 * Real.exp (-(11/100)*x^2) * 1 :=
          mul_le_mul hprod hcos (abs_nonneg _) (by positivity)
      _ = 2 * Real.exp (-(11/100)*x^2) := mul_one _

set_option maxHeartbeats 12800000 in

theorem gapsw80_t76_gaussian_cos_integral (t : ℝ) :
    ∫ x : ℝ, Real.exp (-(11/100) * x^2) * Real.cos (t * x)
      = Real.sqrt (100 * Real.pi / 11) * Real.exp (-(25/11) * t^2) := by
  have _em := Classical.em
  have hb : ((-11/100 : ℂ)).re < 0 := by norm_num
  have hptwise : ∀ x : ℝ,
      Real.exp (-(11/100) * x^2) * Real.cos (t * x)
        = (Complex.exp ((-11/100 : ℂ) * x^2 + (t:ℂ)*I * x + 0)).re := by
    intro x
    rw [Complex.exp_re]
    have hbre : (-11/100 : ℂ).re = -11/100 := by norm_num
    have hbim : (-11/100 : ℂ).im = 0 := by norm_num
    have hre : ((-11/100 : ℂ) * (x:ℂ)^2 + (t:ℂ)*I * x + 0).re
        = -(11/100) * x^2 := by
      rw [show ((x:ℂ)^2) = (((x^2:ℝ)):ℂ) by push_cast; ring]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one, hbre, hbim]
      ring
    have him : ((-11/100 : ℂ) * (x:ℂ)^2 + (t:ℂ)*I * x + 0).im = t * x := by
      rw [show ((x:ℂ)^2) = (((x^2:ℝ)):ℂ) by push_cast; ring]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_im,
        mul_zero, zero_mul, add_zero, zero_add, mul_one, hbre, hbim]
    rw [hre, him]
  simp_rw [hptwise]
  have hint := integrable_cexp_quadratic' hb ((t:ℂ)*I) 0
  have hi := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at hi
  rw [hi, integral_cexp_quadratic hb ((t:ℂ)*I) 0]
  have harg : (0 - ((t:ℂ)*I)^2 / (4*(-11/100:ℂ))) = ((-(25/11) * t^2 : ℝ) : ℂ) := by
    have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
    rw [mul_pow, hI2]; push_cast; ring
  have hbase : (Real.pi : ℂ) / -(-11/100 : ℂ) = ((100 * Real.pi / 11 : ℝ) : ℂ) := by
    push_cast; ring
  rw [harg, hbase,
    show ((((100*Real.pi/11 : ℝ):ℂ))^(1/2:ℂ))
      = ((Real.sqrt (100*Real.pi/11) : ℝ) : ℂ) by
      rw [show ((1:ℂ)/2) = (((1/2:ℝ)):ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (by positivity), Complex.ofReal_inj,
        ← Real.sqrt_eq_rpow],
    show Complex.exp (((-(25/11) * t^2 : ℝ) : ℂ))
      = ((Real.exp (-(25/11) * t^2) : ℝ) : ℂ) from (Complex.ofReal_exp _).symm]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

set_option maxHeartbeats 12800000 in

theorem gapsw80_t76_zKT_boundary_value (z : ℂ) (hz : z.re = 0 ∨ z.re = 1) :
    gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel z
      = Real.sqrt (100 * Real.pi / 11) * Real.exp (-(25/11) * z.im^2) := by
  have _em := Classical.em
  set t := z.im

  have heq0 : gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel z
      = gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel
          (⟨0, t⟩ : ℂ) := by
    rcases hz with h0 | h1
    · congr 1; exact Complex.ext_iff.mpr ⟨h0, rfl⟩
    · rw [gapsw80_t76_zKT_even_symm z]; congr 1
      exact Complex.ext_iff.mpr
        ⟨by simp [Complex.sub_re, Complex.one_re, Complex.conj_re, h1],
         by simp [Complex.sub_im, Complex.one_im, Complex.conj_im, t]⟩
  rw [heq0]

  have hre0 : (⟨0, t⟩ : ℂ).re = 0 := rfl
  have hre1 : (⟨1, t⟩ : ℂ).re = 1 := rfl
  have him0 : (⟨0, t⟩ : ℂ).im = t := rfl
  have him1 : (⟨1, t⟩ : ℂ).im = t := rfl
  have hint0 := gapsw80_t76_zKT_integrand_integrable 0 t (.inl rfl)
  have hint1 := gapsw80_t76_zKT_integrand_integrable 1 t (.inr rfl)
  have hsum : gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel ⟨0, t⟩
      + gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel ⟨1, t⟩
      = 2 * ∫ x, Real.exp (-(11/100) * x^2) * Real.cos (t * x) := by
    rw [gapsw80_t21_zeroKernelTransform, gapsw80_t21_zeroKernelTransform]
    simp only [hre0, hre1, him0, him1]
    rw [← integral_add hint0 hint1, ← integral_const_mul]
    congr 1; funext x
    have hcancel := gapsw80_t76_bourbaki_cosh_cancel x
    have heq : Real.exp ((0-1/2:ℝ)*x) + Real.exp ((1-1/2:ℝ)*x)
        = Real.exp (-(x/2)) + Real.exp (x/2) := by ring_nf
    calc gapsw80_t75_bourbakiKernel x * Real.exp ((0-1/2)*x) * Real.cos (t*x)
          + gapsw80_t75_bourbakiKernel x * Real.exp ((1-1/2)*x) * Real.cos (t*x)
        = gapsw80_t75_bourbakiKernel x
            * (Real.exp ((0-1/2)*x) + Real.exp ((1-1/2)*x)) * Real.cos (t*x) := by ring
      _ = gapsw80_t75_bourbakiKernel x
            * (Real.exp (-(x/2)) + Real.exp (x/2)) * Real.cos (t*x) := by rw [heq]
      _ = 2 * Real.exp (-(11/100)*x^2) * Real.cos (t*x) := by rw [hcancel]
      _ = 2 * (Real.exp (-(11/100)*x^2) * Real.cos (t*x)) := by ring

  have hsymm : gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel ⟨0, t⟩
      = gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel ⟨1, t⟩ := by
    have h := gapsw80_t76_zKT_even_symm (⟨0, t⟩ : ℂ)
    rw [h]; congr 1
    exact Complex.ext_iff.mpr
      ⟨by simp [Complex.sub_re, Complex.one_re, Complex.conj_re],
       by simp [Complex.sub_im, Complex.one_im, Complex.conj_im]⟩
  have h2x : 2 * gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel ⟨0,t⟩
      = 2 * ∫ x, Real.exp (-(11/100)*x^2) * Real.cos (t*x) := by linarith [hsum, hsymm]
  have := gapsw80_t76_gaussian_cos_integral t
  linarith

set_option maxHeartbeats 3200000 in

theorem gapsw80_t76_zKT_boundary_pos (z : ℂ) (hz : z.re = 0 ∨ z.re = 1) :
    0 < gapsw80_t21_zeroKernelTransform gapsw80_t75_bourbakiKernel z := by
  have _em := Classical.em
  rw [gapsw80_t76_zKT_boundary_value z hz]
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _)

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_expNegPhi_diffContOnCl :
    DiffContOnCl ℂ (fun ρ => Complex.exp (-gapsw80_t76_bourbakiLaplace ρ))
      (Complex.re ⁻¹' Set.Ioo 0 1) := by
  have _em := Classical.em
  exact Complex.differentiable_exp.diffContOnCl.comp
    gapsw80_t76_bourbakiLaplace_diffContOnCl.neg (Set.mapsTo_univ _ _)

set_option maxHeartbeats 6400000 in

theorem gapsw80_t76_expNegPhi_growth :
    ∃ c < Real.pi / (1 - 0), ∃ B,
      (fun ρ => Complex.exp (-gapsw80_t76_bourbakiLaplace ρ))
        =O[Filter.comap (abs ∘ Complex.im) Filter.atTop
            ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  have _em := Classical.em
  refine ⟨0, by simp [Real.pi_pos], 2 * Real.sqrt (100 * Real.pi / 11), ?_⟩
  refine Asymptotics.IsBigO.of_bound 1 ?_
  rw [Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall (fun z hz => ?_)
  simp only [zero_mul, Real.exp_zero, mul_one, Real.norm_eq_abs,
    Real.abs_exp, one_mul]
  rw [Complex.norm_exp, Complex.neg_re]
  have hb := gapsw80_t76_bourbakiLaplace_bound z ⟨hz.1.le, hz.2.le⟩
  calc Real.exp (-(gapsw80_t76_bourbakiLaplace z).re)
      ≤ Real.exp ‖gapsw80_t76_bourbakiLaplace z‖ :=
        Real.exp_le_exp.mpr ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
    _ ≤ Real.exp (2 * Real.sqrt (100 * Real.pi / 11)) := Real.exp_le_exp.mpr hb

set_option maxHeartbeats 12800000 in

theorem gapsw80_t76_bourbakiStripPositivity :
    gapsw80_t75_BourbakiStripPositivity := by
  have _em := Classical.em
  intro ρ hρ0 hρ1
  have hρ' : |ρ.re - 1/2| ≤ 3/4 := by
    rw [abs_sub_le_iff]; constructor <;> linarith
  have hbdry : ∀ z : ℂ, z.re = 0 ∨ z.re = 1
      → ‖Complex.exp (-gapsw80_t76_bourbakiLaplace z)‖ ≤ 1 := by
    intro z hz
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff, neg_nonpos]
    have hzρ : |z.re - 1/2| ≤ 3/4 := by
      rcases hz with h | h <;> rw [h] <;> norm_num
    rw [← gapsw80_t76_zKT_eq_re_bourbakiLaplace z hzρ]
    exact (gapsw80_t76_zKT_boundary_pos z hz).le
  have hPL := PhragmenLindelof.vertical_strip
    gapsw80_t76_expNegPhi_diffContOnCl gapsw80_t76_expNegPhi_growth
    (fun z hz => hbdry z (.inl hz)) (fun z hz => hbdry z (.inr hz))
    hρ0.le hρ1.le
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff, neg_nonpos] at hPL
  rw [gapsw80_t76_zKT_eq_re_bourbakiLaplace ρ hρ']
  exact hPL

end FLT.Gapsw80T76BourbakiStripPositivityProof

end

section

set_option maxHeartbeats 3200000

namespace FLT
namespace Gapsw80T77BourbakiArchDerivedLowerBoundProof

open FLT.Gapsw80T18ArchDerivedA34Redecomp
open FLT.Gapsw80T75BourbakiKernelDef
p2m_open "Real P2MW.S_Real_poitouKernel_admissible_and_archBound.Real MeasureTheory P2MW.S_Real_poitouKernel_admissible_and_archBound.MeasureTheory Filter P2MW.S_Real_poitouKernel_admissible_and_archBound.Filter"

set_option maxHeartbeats 3200000 in

theorem gapsw80_t77_sinh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  have _em := Classical.em
  rw [Real.sinh_eq]
  have := Real.exp_lt_exp.mpr (show -x < x by linarith)
  linarith

set_option maxHeartbeats 3200000 in

theorem gapsw80_t77_one_le_cosh (x : ℝ) : 1 ≤ Real.cosh x := by
  have _em := Classical.em
  rw [Real.cosh_eq]
  have h1 := Real.add_one_le_exp x
  have h2 := Real.add_one_le_exp (-x)
  linarith

set_option maxHeartbeats 3200000 in

theorem gapsw80_t77_hasDerivAt_cosh (x : ℝ) :
    HasDerivAt Real.cosh (Real.sinh x) x := by
  have _em := Classical.em
  have h : HasDerivAt (fun y => (Real.exp y + Real.exp (-y))/2)
      ((Real.exp x - Real.exp (-x))/2) x := by
    have h1 := Real.hasDerivAt_exp x
    have h2 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    convert (h1.add h2).div_const 2 using 1 <;> first | rfl | ring1 | (simp only [Pi.add_apply]; ring1)
  exact (Real.sinh_eq x) ▸ (funext Real.cosh_eq) ▸ h

set_option maxHeartbeats 3200000 in

theorem gapsw80_t77_hasDerivAt_sinh (x : ℝ) :
    HasDerivAt Real.sinh (Real.cosh x) x := by
  have _em := Classical.em
  have h : HasDerivAt (fun y => (Real.exp y - Real.exp (-y))/2)
      ((Real.exp x + Real.exp (-x))/2) x := by
    have h1 := Real.hasDerivAt_exp x
    have h2 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    convert (h1.sub h2).div_const 2 using 1 <;> first | rfl | ring1 | (simp only [Pi.sub_apply]; ring1)
  exact (Real.cosh_eq x) ▸ (funext Real.sinh_eq) ▸ h

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_nonneg_of_deriv_nonneg {P p : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hp : Continuous p) (hP : ∀ t, HasDerivAt P (p t) t) (hP0 : P 0 = 0)
    (hpnn : ∀ t ∈ Set.Icc (0:ℝ) x, 0 ≤ p t) : 0 ≤ P x := by
  have _em := Classical.em
  have heq : P x = ∫ t in (0:ℝ)..x, p t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hP t)
      (hp.intervalIntegrable _ _), hP0, sub_zero]
  rw [heq]
  exact intervalIntegral.integral_nonneg hx hpnn

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_sinh_ge_cubic {x : ℝ} (hx : 0 ≤ x) :
    x + x ^ 3 / 6 ≤ Real.sinh x := by
  have _em := Classical.em
  have hs1 : ∀ t, 0 ≤ t → t ≤ Real.sinh t := by
    intro t ht
    have h := gapsw80_t77_nonneg_of_deriv_nonneg (P := fun s => Real.sinh s - s)
      (p := fun s => Real.cosh s - 1) ht
      (Real.continuous_cosh.sub continuous_const)
      (fun s => ((gapsw80_t77_hasDerivAt_sinh s).sub (hasDerivAt_id s)))
      (by simp [Real.sinh_zero])
      (fun s _ => sub_nonneg.mpr (gapsw80_t77_one_le_cosh s))
    linarith
  have hs2 : ∀ t, 0 ≤ t → 1 + t^2/2 ≤ Real.cosh t := by
    intro t ht
    have hd : ∀ s, HasDerivAt (fun r => Real.cosh r - 1 - r^2/2) (Real.sinh s - s) s := by
      intro s
      have h := (gapsw80_t77_hasDerivAt_cosh s).sub
        ((hasDerivAt_const s (1:ℝ)).add ((hasDerivAt_pow 2 s).div_const 2))
      refine HasDerivAt.congr_of_eventuallyEq (f := fun r => Real.cosh r - (1 + r^2/2))
        ?_ (Filter.Eventually.of_forall (fun r => by ring))
      exact h.congr_deriv (by push_cast; ring)
    have h := gapsw80_t77_nonneg_of_deriv_nonneg
      (P := fun s => Real.cosh s - 1 - s^2/2) (p := fun s => Real.sinh s - s) ht
      (Real.continuous_sinh.sub continuous_id) hd
      (by simp [Real.cosh_zero])
      (fun s hs => sub_nonneg.mpr (hs1 s hs.1))
    linarith
  have hd3 : ∀ s, HasDerivAt (fun r => Real.sinh r - r - r^3/6)
      (Real.cosh s - 1 - s^2/2) s := by
    intro s
    have h := (gapsw80_t77_hasDerivAt_sinh s).sub
      ((hasDerivAt_id s).add ((hasDerivAt_pow 3 s).div_const 6))
    refine HasDerivAt.congr_of_eventuallyEq (f := fun r => Real.sinh r - (r + r^3/6))
      ?_ (Filter.Eventually.of_forall (fun r => by ring))
    exact h.congr_deriv (by push_cast; ring)
  have h := gapsw80_t77_nonneg_of_deriv_nonneg
    (P := fun s => Real.sinh s - s - s^3/6) (p := fun s => Real.cosh s - 1 - s^2/2) hx
    ((Real.continuous_cosh.sub continuous_const).sub ((continuous_pow 2).div_const 2)) hd3
    (by simp [Real.sinh_zero])
    (fun s hs => by linarith [hs2 s hs.1])
  linarith

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_one_sub_exp_neg_le_cubic {u : ℝ} (hu : 0 ≤ u) :
    1 - Real.exp (-u) ≤ u - u ^ 2 / 2 + u ^ 3 / 6 := by
  have _em := Classical.em
  have hdn : ∀ s, HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-s)) s := fun s => by
    have h := (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
    convert h using 1 <;> first | rfl | ring1
  have hs1 : ∀ t, 0 ≤ t → 0 ≤ Real.exp (-t) - 1 + t := fun t _ => by
    linarith [Real.add_one_le_exp (-t)]
  have hs2 : ∀ t, 0 ≤ t → 0 ≤ 1 - Real.exp (-t) - t + t^2/2 := by
    intro t ht
    exact gapsw80_t77_nonneg_of_deriv_nonneg
      (P := fun s => 1 - Real.exp (-s) - s + s^2/2)
      (p := fun s => Real.exp (-s) - 1 + s) ht
      (((Real.continuous_exp.comp continuous_neg).sub continuous_const).add continuous_id)
      (fun s => by
        have h := ((hasDerivAt_const s (1:ℝ)).sub (hdn s)).sub (hasDerivAt_id s)
          |>.add ((hasDerivAt_pow 2 s).div_const 2)
        convert h using 1 <;> first | rfl | (push_cast; ring1))
      (by simp)
      (fun s hs => hs1 s hs.1)
  have hs3 : 0 ≤ Real.exp (-u) - 1 + u - u^2/2 + u^3/6 :=
    gapsw80_t77_nonneg_of_deriv_nonneg
      (P := fun s => Real.exp (-s) - 1 + s - s^2/2 + s^3/6)
      (p := fun s => 1 - Real.exp (-s) - s + s^2/2) hu
      (((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).sub
        continuous_id).add ((continuous_pow 2).div_const 2))
      (fun s => by
        have h := (((hdn s).sub (hasDerivAt_const s (1:ℝ))).add (hasDerivAt_id s)).sub
          ((hasDerivAt_pow 2 s).div_const 2) |>.add ((hasDerivAt_pow 3 s).div_const 6)
        convert h using 1 <;> first | rfl | (push_cast; ring1))
      (by simp)
      (fun s hs => hs2 s hs.1)
  linarith

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_cosh_sub_one_div_sinh_eq {x : ℝ} (hx : 0 < x) :
    (Real.cosh (x / 2) - 1) / Real.sinh x
      = 1 / (Real.exp (x / 2) + 1) - 1 / (Real.exp x + 1) := by
  have _em := Classical.em
  set a := Real.exp (x / 2) with ha_def
  have ha_pos : 0 < a := Real.exp_pos _
  have ha_gt : 1 < a := Real.one_lt_exp_iff.mpr (by linarith)
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hex : Real.exp x = a ^ 2 := by
    rw [ha_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcosh : Real.cosh (x / 2) = (a + a⁻¹) / 2 := by
    rw [Real.cosh_eq, ha_def, Real.exp_neg]
  have hsinh : Real.sinh x = (a ^ 2 - a⁻¹ ^ 2) / 2 := by
    rw [Real.sinh_eq, hex, Real.exp_neg, hex]; ring
  rw [hcosh, hsinh, hex]
  have hden1 : (a + 1 : ℝ) ≠ 0 := by positivity
  have hden2 : (a ^ 2 + 1 : ℝ) ≠ 0 := by positivity
  have ha2 : (0:ℝ) < a ^ 2 - a⁻¹ ^ 2 := by
    have h1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha_gt
    nlinarith [sq_nonneg (a - a⁻¹), mul_pos ha_pos (inv_pos.mpr ha_pos)]
  have hden3 : (a ^ 2 - a⁻¹ ^ 2 : ℝ) ≠ 0 := ha2.ne'

  have hkey : ((a + a⁻¹)/2 - 1) * (2*a^2) = a*(a-1)^2 := by
    field_simp; ring
  have hkey2 : ((a^2 - a⁻¹^2)/2) * (2*a^2) = (a-1)*(a+1)*(a^2+1) := by
    field_simp; ring
  have ham1 : (0:ℝ) < a - 1 := by linarith
  have h2a2 : (0:ℝ) < 2*a^2 := by positivity
  calc ((a + a⁻¹)/2 - 1) / ((a^2 - a⁻¹^2)/2)
      = (((a + a⁻¹)/2 - 1)*(2*a^2)) / (((a^2 - a⁻¹^2)/2)*(2*a^2)) := by
        rw [mul_div_mul_right _ _ h2a2.ne']
    _ = (a*(a-1)^2) / ((a-1)*(a+1)*(a^2+1)) := by rw [hkey, hkey2]
    _ = (a*(a-1)) / ((a+1)*(a^2+1)) := by
        rw [show a*(a-1)^2 = (a*(a-1))*(a-1) by ring,
          show (a-1)*(a+1)*(a^2+1) = ((a+1)*(a^2+1))*(a-1) by ring,
          mul_div_mul_right _ _ ham1.ne']
    _ = 1/(a+1) - 1/(a^2+1) := by
        rw [div_sub_div _ _ hden1 hden2]; congr 1; ring

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_integrand_split {x : ℝ} (hx : 0 < x) :
    (1 - gapsw80_t75_bourbakiKernel x) / (Real.exp (x / 2) - Real.exp (-(x / 2)))
      = (1 / (Real.exp (x / 2) + 1) - 1 / (Real.exp x + 1))
        + (1 - Real.exp (-(11 / 100) * x ^ 2)) / Real.sinh x := by
  have _em := Classical.em
  have hcosh_pos : 0 < Real.cosh (x / 2) := Real.cosh_pos _
  have hsinh_pos : 0 < Real.sinh x := gapsw80_t77_sinh_pos hx
  have h2s : Real.exp (x / 2) - Real.exp (-(x / 2)) = 2 * Real.sinh (x / 2) := by
    rw [Real.sinh_eq]; ring
  have hsinh2 : 2 * Real.sinh (x / 2) * Real.cosh (x / 2) = Real.sinh x := by
    have h := Real.sinh_two_mul (x / 2)
    rw [show 2 * (x/2) = x by ring] at h; linarith
  rw [gapsw80_t75_bourbakiKernel, ← gapsw80_t77_cosh_sub_one_div_sinh_eq hx,
    show (1:ℝ) - Real.exp (-(11/100)*x^2) / Real.cosh (x/2)
        = (Real.cosh (x/2) - Real.exp (-(11/100)*x^2)) / Real.cosh (x/2) by
      field_simp,
    h2s, div_div,
    show Real.cosh (x/2) * (2 * Real.sinh (x/2))
        = 2 * Real.sinh (x/2) * Real.cosh (x/2) by ring,
    hsinh2, ← add_div]
  congr 1; ring

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_part1_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => Real.log (1 + Real.exp (-y)) - 2 * Real.log (1 + Real.exp (-(y/2))))
      (1 / (Real.exp (x/2) + 1) - 1 / (Real.exp x + 1)) x := by
  have _em := Classical.em
  have hp1 : (0:ℝ) < 1 + Real.exp (-x) := by positivity
  have hp2 : (0:ℝ) < 1 + Real.exp (-(x/2)) := by positivity
  have hd1 : HasDerivAt (fun y => Real.log (1 + Real.exp (-y)))
      (-(1 / (Real.exp x + 1))) x := by
    have h := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x))
    have h2 := (hasDerivAt_const x (1:ℝ)).add h
    have h3 := (Real.hasDerivAt_log hp1.ne').comp x h2
    convert h3 using 1 <;> try rfl
    rw [Real.exp_neg]; field_simp; ring
  have hd2 : HasDerivAt (fun y => 2 * Real.log (1 + Real.exp (-(y/2))))
      (-(1 / (Real.exp (x/2) + 1))) x := by
    have h := (Real.hasDerivAt_exp (-(x/2))).comp x
      (((hasDerivAt_id x).div_const 2).neg)
    have h2 := (hasDerivAt_const x (1:ℝ)).add h
    have h3 := ((Real.hasDerivAt_log hp2.ne').comp x h2).const_mul 2
    convert h3 using 1 <;> try rfl
    rw [Real.exp_neg]; field_simp; ring
  have := hd1.sub hd2
  convert this using 1 <;> first | rfl | ring1

set_option maxHeartbeats 3200000 in

theorem gapsw80_t77_part1_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 / (Real.exp (x/2) + 1) - 1 / (Real.exp x + 1) := by
  have _em := Classical.em
  have h : Real.exp (x/2) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
  have h1 : (0:ℝ) < Real.exp (x/2) + 1 := by positivity
  have h2 : (0:ℝ) < Real.exp x + 1 := by positivity
  rw [div_sub_div _ _ h1.ne' h2.ne', div_nonneg_iff]
  left; exact ⟨by nlinarith, by positivity⟩

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_integral_part1_eq_log_two :
    ∫ x in Set.Ioi (0:ℝ), (1 / (Real.exp (x/2) + 1) - 1 / (Real.exp x + 1))
      = Real.log 2 := by
  have _em := Classical.em
  set G : ℝ → ℝ :=
    fun y => Real.log (1 + Real.exp (-y)) - 2 * Real.log (1 + Real.exp (-(y/2)))
  have hG0 : G 0 = -Real.log 2 := by
    simp only [G, _root_.neg_zero, Real.exp_zero]
    rw [show -((0:ℝ)/2) = 0 by norm_num, Real.exp_zero,
      show (1:ℝ)+1 = 2 by norm_num]
    ring
  have htend : Tendsto G atTop (nhds 0) := by
    have h1 : Tendsto (fun y => (1:ℝ) + Real.exp (-y)) atTop (nhds (1+0)) :=
      tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero
    have h2 : Tendsto (fun y => (1:ℝ) + Real.exp (-(y/2))) atTop (nhds (1+0)) := by
      apply tendsto_const_nhds.add
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_neg_atTop_atBot.comp
        (Tendsto.atTop_div_const (by norm_num) tendsto_id)
    have hcL : ContinuousAt Real.log (1+0) :=
      Real.continuousAt_log (by norm_num)
    have := (hcL.tendsto.comp h1).sub ((hcL.tendsto.comp h2).const_mul 2)
    simpa [G, Real.log_one] using this
  have hcont : ContinuousWithinAt G (Set.Ici (0:ℝ)) 0 :=
    (gapsw80_t77_part1_hasDerivAt 0).continuousAt.continuousWithinAt
  have hint : IntegrableOn
      (fun x => 1 / (Real.exp (x/2) + 1) - 1 / (Real.exp x + 1)) (Set.Ioi (0:ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg hcont
      (fun x _ => gapsw80_t77_part1_hasDerivAt x)
      (fun x hx => gapsw80_t77_part1_nonneg hx) htend
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun x _ => gapsw80_t77_part1_hasDerivAt x) hint htend
  rw [this, hG0]; ring

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_exp_three_gt_twenty : (20:ℝ) < Real.exp 3 := by
  have _em := Classical.em
  have h := Real.sum_le_exp_of_nonneg (x := (3:ℝ)) (by norm_num) 12
  refine lt_of_lt_of_le ?_ h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

set_option maxHeartbeats 3200000 in

theorem gapsw80_t77_J_integrand_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ (1 - Real.exp (-(11/100) * x ^ 2)) / Real.sinh x := by
  have _em := Classical.em
  apply div_nonneg
  · have := Real.exp_le_one_iff.mpr (by nlinarith : -(11/100:ℝ)*x^2 ≤ 0); linarith
  · exact (gapsw80_t77_sinh_pos hx).le

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_J_integrand_bound {x : ℝ} (hx : 0 < x) :
    (1 - Real.exp (-(11/100) * x ^ 2)) / Real.sinh x
      ≤ (11/100) * (1 - (11/100)*x^2/2 + ((11/100)*x^2)^2/6) * (6*x/(6+x^2)) := by
  have _em := Classical.em
  have hsinh_pos : 0 < Real.sinh x := gapsw80_t77_sinh_pos hx
  have hsinh_ge : x + x^3/6 ≤ Real.sinh x := gapsw80_t77_sinh_ge_cubic hx.le
  have h1e : 1 - Real.exp (-(11/100)*x^2)
      ≤ (11/100)*x^2 - ((11/100)*x^2)^2/2 + ((11/100)*x^2)^3/6 := by
    have h := gapsw80_t77_one_sub_exp_neg_le_cubic (u := (11/100)*x^2) (by positivity)
    rw [show -(11/100:ℝ)*x^2 = -((11/100)*x^2) by ring]; exact h
  have hden : (0:ℝ) < 6 + x^2 := by positivity
  have hx3 : (0:ℝ) < x + x^3/6 := by positivity
  have hcnn : (0:ℝ) ≤ 1 - (11/100)*x^2/2 + ((11/100)*x^2)^2/6 := by
    nlinarith [sq_nonneg ((11/100:ℝ)*x^2 - 3/2), sq_nonneg x]
  have hrep : (6:ℝ)*x/(6+x^2)*(x+x^3/6) = x^2 := by
    rw [div_mul_eq_mul_div, div_eq_iff hden.ne']; ring
  rw [div_le_iff₀ hsinh_pos]
  calc 1 - Real.exp (-(11/100)*x^2)
      ≤ (11/100)*x^2 - ((11/100)*x^2)^2/2 + ((11/100)*x^2)^3/6 := h1e
    _ = (11/100)*(1-(11/100)*x^2/2+((11/100)*x^2)^2/6)*((6*x/(6+x^2))*(x+x^3/6)) := by
        rw [hrep]; ring
    _ ≤ (11/100)*(1-(11/100)*x^2/2+((11/100)*x^2)^2/6)*((6*x/(6+x^2))*Real.sinh x) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hsinh_ge (by positivity)
        · positivity
    _ = (11/100)*(1-(11/100)*x^2/2+((11/100)*x^2)^2/6)*(6*x/(6+x^2))*Real.sinh x := by
        ring

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_inv_sinh_Ioi_three :
    IntegrableOn (fun x => (1:ℝ)/Real.sinh x) (Set.Ioi (3:ℝ))
    ∧ ∫ x in Set.Ioi (3:ℝ), (1:ℝ)/Real.sinh x = -Real.log (Real.tanh (3/2)) := by
  have _em := Classical.em
  set G : ℝ → ℝ := fun t => Real.log (Real.tanh (t/2))
  have htanh_pos : ∀ t > (0:ℝ), 0 < Real.tanh (t/2) := fun t ht => by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (gapsw80_t77_sinh_pos (by linarith)) (Real.cosh_pos _)
  have hderiv : ∀ t ∈ Set.Ici (3:ℝ), HasDerivAt G (1/Real.sinh t) t := by
    intro t ht
    have ht3 := Set.mem_Ici.mp ht; have ht0 : 0 < t := by linarith
    have hsh := gapsw80_t77_sinh_pos (show (0:ℝ) < t/2 by linarith)
    have hch := Real.cosh_pos (t/2)
    have hs2 : Real.sinh t = 2*Real.sinh (t/2)*Real.cosh (t/2) := by
      rw [← Real.sinh_two_mul]; congr 1; ring
    have hdt : HasDerivAt (fun s => Real.tanh (s/2))
        (1/(2*Real.cosh (t/2)^2)) t := by
      have h1 := (gapsw80_t77_hasDerivAt_sinh (t/2)).comp t
        ((hasDerivAt_id t).div_const 2)
      have h2 := (gapsw80_t77_hasDerivAt_cosh (t/2)).comp t
        ((hasDerivAt_id t).div_const 2)
      have h := h1.div h2 hch.ne'
      refine (HasDerivAt.congr_of_eventuallyEq ?_
        (Filter.Eventually.of_forall (fun s => (Real.tanh_eq_sinh_div_cosh (s/2)))))
      refine h.congr_deriv ?_
      have hid := Real.cosh_sq_sub_sinh_sq (t/2)
      simp only [Function.comp_apply, id_eq]
      rw [div_eq_div_iff (by positivity) (by positivity)]; nlinarith [hid]
    have h := (Real.hasDerivAt_log (htanh_pos t ht0).ne').comp t hdt
    refine h.congr_deriv ?_
    rw [Real.tanh_eq_sinh_div_cosh, inv_div, hs2]
    field_simp
  have hform : ∀ t, Real.tanh (t/2)
      = (1 - Real.exp (-t))/(1 + Real.exp (-t)) := fun t => by
    have hea : Real.exp (-(t/2)) * Real.exp t = Real.exp (t/2) := by
      rw [← Real.exp_add]; ring_nf
    have h1 : Real.exp (t/2) - Real.exp (-(t/2))
        = Real.exp (-(t/2))*(Real.exp t - 1) := by rw [mul_sub, hea, mul_one]
    have h2 : Real.exp (t/2) + Real.exp (-(t/2))
        = Real.exp (-(t/2))*(Real.exp t + 1) := by rw [mul_add, hea, mul_one]
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq,
      div_div_div_cancel_right₀ (hc := two_ne_zero), h1, h2,
      mul_div_mul_left _ _ (Real.exp_pos _).ne', Real.exp_neg]
    have hne : Real.exp t ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  have htend : Tendsto G atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.tanh (t/2)) atTop (nhds 1) := by
      simp_rw [hform]
      have hnum : Tendsto (fun t : ℝ => (1:ℝ) - Real.exp (-t)) atTop (nhds (1-0)) :=
        tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
      have hden : Tendsto (fun t : ℝ => (1:ℝ) + Real.exp (-t)) atTop (nhds (1+0)) :=
        tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero
      have := hnum.div hden (by norm_num)
      simpa [Pi.div_def] using this
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    simpa [Real.log_one, G, Function.comp_def] using this
  have hcont : ContinuousWithinAt G (Set.Ici (3:ℝ)) 3 :=
    (hderiv 3 Set.self_mem_Ici).continuousAt.continuousWithinAt
  have hnn : ∀ x ∈ Set.Ioi (3:ℝ), (0:ℝ) ≤ 1/Real.sinh x := fun x hx => by
    have hx0 : (0:ℝ) < x := lt_trans (by norm_num) hx
    exact div_nonneg zero_le_one (gapsw80_t77_sinh_pos hx0).le
  have hint : IntegrableOn (fun x => (1:ℝ)/Real.sinh x) (Set.Ioi (3:ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg hcont
      (fun x hx => hderiv x (Set.mem_Ici_of_Ioi hx)) hnn htend
  refine ⟨hint, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun x hx => hderiv x (Set.mem_Ici_of_Ioi hx)) hint htend
  simp only [G] at h; linarith

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_J_dom_continuous :
    Continuous (fun t : ℝ =>
      (11/100)*(1-(11/100)*t^2/2+((11/100)*t^2)^2/6)*(6*t/(6+t^2))) := by
  have _em := Classical.em
  apply Continuous.mul (by continuity)
  exact (continuous_const.mul continuous_id).div
    (continuous_const.add (continuous_pow 2)) (fun t => by positivity)

set_option maxHeartbeats 12800000 in

theorem gapsw80_t77_J_integrableOn :
    IntegrableOn (fun x => (1 - Real.exp (-(11/100)*x^2)) / Real.sinh x)
      (Set.Ioi (0:ℝ)) := by
  have _em := Classical.em
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 3 ∪ Set.Ioi 3 from
    (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm]
  have hcontJ : ContinuousOn
      (fun x => (1 - Real.exp (-(11/100)*x^2)) / Real.sinh x) (Set.Ioi (0:ℝ)) := by
    apply ContinuousOn.div
    · apply Continuous.continuousOn
      exact continuous_const.sub (Real.continuous_exp.comp (by continuity))
    · exact Real.continuous_sinh.continuousOn
    · exact fun x hx => (gapsw80_t77_sinh_pos hx).ne'
  apply IntegrableOn.union
  · refine Integrable.mono' (g := fun t =>
        (11/100)*(1-(11/100)*t^2/2+((11/100)*t^2)^2/6)*(6*t/(6+t^2)))
      (gapsw80_t77_J_dom_continuous.integrableOn_Ioc) ?_ ?_
    · exact (hcontJ.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (gapsw80_t77_J_integrand_nonneg hx.1)]
      exact gapsw80_t77_J_integrand_bound hx.1
  · refine Integrable.mono' (g := fun x => (1:ℝ)/Real.sinh x)
      gapsw80_t77_inv_sinh_Ioi_three.1 ?_ ?_
    · exact (hcontJ.mono (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0:ℝ) < x := lt_trans (by norm_num) hx
      rw [Real.norm_eq_abs, abs_of_nonneg (gapsw80_t77_J_integrand_nonneg hx0)]
      apply div_le_div_of_nonneg_right ?_ (gapsw80_t77_sinh_pos hx0).le
      linarith [Real.exp_pos (-(11/100:ℝ)*x^2)]

set_option maxHeartbeats 12800000 in

theorem gapsw80_t77_J_head_integral :
    ∫ x in (0:ℝ)..3,
        (11/100)*(1-(11/100)*x^2/2+((11/100)*x^2)^2/6)*(6*x/(6+x^2))
      = (231429/500000 : ℝ) * Real.log (5/2) + (-689337/4000000) := by
  have _em := Classical.em
  set H : ℝ → ℝ := fun t => (231429/500000:ℝ) * Real.log (6 + t^2)
    + (-(3*(11/100)^2)*t^2/2 + (11/100)^3*t^4/4 - 3*(11/100)^3*t^2)
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 3, HasDerivAt H
      ((11/100)*(1-(11/100)*t^2/2+((11/100)*t^2)^2/6)*(6*t/(6+t^2))) t := by
    intro t _
    have hden : (0:ℝ) < 6 + t^2 := by positivity
    have hd1 : HasDerivAt (fun s => (231429/500000:ℝ) * Real.log (6 + s^2))
        ((231429/500000:ℝ)*(2*t/(6+t^2))) t := by
      have h := ((Real.hasDerivAt_log hden.ne').comp t
        ((hasDerivAt_const t (6:ℝ)).add (hasDerivAt_pow 2 t))).const_mul (231429/500000:ℝ)
      refine h.congr_deriv ?_; push_cast; field_simp; ring
    have hd2 : HasDerivAt
        (fun s => -(3*(11/100:ℝ)^2)*s^2/2 + (11/100)^3*s^4/4 - 3*(11/100)^3*s^2)
        (-(3*(11/100:ℝ)^2)*t + (11/100)^3*t^3 - 6*(11/100)^3*t) t := by
      have h := ((((hasDerivAt_pow 2 t).const_mul (-(3*(11/100:ℝ)^2))).div_const 2).add
        (((hasDerivAt_pow 4 t).const_mul ((11/100:ℝ)^3)).div_const 4)).sub
        ((hasDerivAt_pow 2 t).const_mul (3*(11/100:ℝ)^3))
      have hfeq : (fun (s:ℝ) => -(3*(11/100:ℝ)^2)*s^2/2 + (11/100)^3*s^4/4
            - 3*(11/100)^3*s^2)
          = (((fun x => -(3*(11/100:ℝ)^2) * x^2 / 2) + fun x => (11/100:ℝ)^3 * x^4 / 4)
            - fun y => 3*(11/100:ℝ)^3 * y^2) := by
        funext s; simp only [Pi.add_apply, Pi.sub_apply]
      rw [hfeq]; refine h.congr_deriv ?_; push_cast; ring
    have hH := hd1.add hd2
    have hHeq : H = ((fun s => (231429/500000:ℝ) * Real.log (6 + s^2))
        + fun s => -(3*(11/100:ℝ)^2)*s^2/2 + (11/100)^3*s^4/4 - 3*(11/100)^3*s^2) := by
      funext s; simp only [H, Pi.add_apply]
    rw [hHeq]; refine hH.congr_deriv ?_
    have hkey : ∀ (c:ℝ), c/(6+t^2)*(6+t^2) = c := fun c =>
      div_mul_cancel₀ c hden.ne'
    have hrhs : (11/100:ℝ)*(1-(11/100)*t^2/2+((11/100)*t^2)^2/6)*(6*t/(6+t^2))
        = (6*(11/100)*t - 3*(11/100)^2*t^3 + (11/100)^3*t^5)/(6+t^2) := by
      rw [eq_div_iff hden.ne', mul_assoc _ (_/_), hkey]; ring
    have hlhs : (231429/500000:ℝ)*(2*t/(6+t^2))
          + (-(3*(11/100)^2)*t + (11/100)^3*t^3 - 6*(11/100)^3*t)
        = (6*(11/100)*t - 3*(11/100)^2*t^3 + (11/100)^3*t^5)/(6+t^2) := by
      rw [eq_div_iff hden.ne', add_mul, mul_assoc _ (_/_), hkey]; ring
    rw [hlhs, hrhs]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (gapsw80_t77_J_dom_continuous.intervalIntegrable _ _)]
  simp only [H]
  rw [show Real.log (6+(3:ℝ)^2) = Real.log (5/2) + Real.log 6 by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num,
    show Real.log (6+(0:ℝ)^2) = Real.log 6 by norm_num]
  ring

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_J_tail_bound :
    ∫ x in Set.Ioi (3:ℝ), (1:ℝ) / Real.sinh x < 2/19 := by
  have _em := Classical.em
  rw [gapsw80_t77_inv_sinh_Ioi_three.2]
  have he3 := gapsw80_t77_exp_three_gt_twenty
  have hea : Real.exp (-((3:ℝ)/2)) * Real.exp 3 = Real.exp (3/2) := by
    rw [← Real.exp_add]; ring_nf
  have htanh : Real.tanh ((3:ℝ)/2) = (Real.exp 3 - 1)/(Real.exp 3 + 1) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq,
      div_div_div_cancel_right₀ (hc := two_ne_zero),
      show Real.exp ((3:ℝ)/2) - Real.exp (-(3/2))
        = Real.exp (-(3/2))*(Real.exp 3 - 1) by rw [mul_sub, hea, mul_one],
      show Real.exp ((3:ℝ)/2) + Real.exp (-(3/2))
        = Real.exp (-(3/2))*(Real.exp 3 + 1) by rw [mul_add, hea, mul_one],
      mul_div_mul_left _ _ (Real.exp_pos _).ne']
  have hp : (0:ℝ) < Real.exp 3 + 1 := by positivity
  have hm : (0:ℝ) < Real.exp 3 - 1 := by linarith
  rw [htanh, ← Real.log_inv, inv_div,
    show (Real.exp 3 + 1)/(Real.exp 3 - 1) = 1 + 2/(Real.exp 3 - 1) by
      field_simp; ring]
  calc Real.log (1 + 2/(Real.exp 3 - 1))
      ≤ 2/(Real.exp 3 - 1) := by
        have h := Real.log_le_sub_one_of_pos (x := 1 + 2/(Real.exp 3 - 1))
          (by positivity)
        linarith
    _ < 2/19 := by
        apply div_lt_div_of_pos_left (by norm_num) (by norm_num)
        linarith

set_option maxHeartbeats 12800000 in

theorem gapsw80_t77_J_lt :
    ∫ x in Set.Ioi (0:ℝ), (1 - Real.exp (-(11/100)*x^2)) / Real.sinh x
      < (231429/500000 : ℝ) * (917/1000) + (-689337/4000000) + 2/19 := by
  have _em := Classical.em
  have hhead : IntegrableOn (fun x => (1-Real.exp (-(11/100)*x^2))/Real.sinh x)
      (Set.Ioc (0:ℝ) 3) :=
    gapsw80_t77_J_integrableOn.mono_set Set.Ioc_subset_Ioi_self
  have htail := gapsw80_t77_J_integrableOn.mono_set
    (Set.Ioi_subset_Ioi (show (0:ℝ) ≤ 3 by norm_num))
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 3 ∪ Set.Ioi 3 from
      (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm,
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hhead htail]
  have hH : (∫ x in Set.Ioc (0:ℝ) 3, (1-Real.exp (-(11/100)*x^2))/Real.sinh x)
      ≤ (231429/500000:ℝ)*Real.log (5/2) + (-689337/4000000) := by
    rw [← gapsw80_t77_J_head_integral,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤3)]
    apply setIntegral_mono_on hhead
      (gapsw80_t77_J_dom_continuous.integrableOn_Ioc) measurableSet_Ioc
    intro x hx; exact gapsw80_t77_J_integrand_bound hx.1
  have hT : (∫ x in Set.Ioi (3:ℝ), (1-Real.exp (-(11/100)*x^2))/Real.sinh x)
      ≤ ∫ x in Set.Ioi (3:ℝ), (1:ℝ)/Real.sinh x := by
    apply setIntegral_mono_on htail gapsw80_t77_inv_sinh_Ioi_three.1 measurableSet_Ioi
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans (by norm_num) hx
    exact div_le_div_of_nonneg_right
      (by linarith [Real.exp_pos (-(11/100:ℝ)*x^2)]) (gapsw80_t77_sinh_pos hx0).le
  have hlog52 : Real.log ((5:ℝ)/2) < 917/1000 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h := Real.sum_le_exp_of_nonneg (x := (917:ℝ)/1000) (by norm_num) 8
    refine lt_of_lt_of_le ?_ h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num
  have htailb := gapsw80_t77_J_tail_bound
  nlinarith [hH, hT, hlog52, htailb]

set_option maxHeartbeats 12800000 in

theorem gapsw80_t77_gamma_gt :
    (290774257297357 : ℝ)/72201776446800 - 5 * Real.log 2
      < Real.eulerMascheroniConstant := by
  have _em := Classical.em
  have hseq : Real.eulerMascheroniSeq 31
      = (290774257297357 : ℝ)/72201776446800 - Real.log 32 := by
    rw [Real.eulerMascheroniSeq]; push_cast; norm_num
  have hlog32 : Real.log (32:ℝ) = 5 * Real.log 2 := by
    rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]; push_cast; ring
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  rw [hseq, hlog32] at h; exact h

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_sqrt_100pi_div_11_lt :
    Real.sqrt (100 * Real.pi / 11) < (5345:ℝ)/1000 := by
  have _em := Classical.em
  have hpi := Real.pi_lt_d6
  have h1 : 100 * Real.pi / 11 < (5345/1000:ℝ)^2 := by nlinarith
  calc Real.sqrt (100*Real.pi/11) < Real.sqrt ((5345/1000)^2) :=
        Real.sqrt_lt_sqrt (by positivity) h1
    _ = 5345/1000 := Real.sqrt_sq (by norm_num)

set_option maxHeartbeats 12800000 in

theorem gapsw80_t77_log_4000pi_div_9805_gt :
    (248:ℝ)/1000 < Real.log (4000 * Real.pi / 9805) := by
  have _em := Classical.em
  have hpi := Real.pi_gt_d6
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have hexp : Real.exp ((248:ℝ)/1000) < 12566368/9805000 := by
    have hb := Real.exp_bound (x := (248:ℝ)/1000) (by norm_num) (n := 6) (by norm_num)
    have habs : Real.exp ((248:ℝ)/1000)
        ≤ (∑ m ∈ Finset.range 6, ((248:ℝ)/1000)^m/m.factorial)
          + |((248:ℝ)/1000)|^6 * (7/(720*6)) := by
      have h1 := (abs_sub_le_iff.mp hb).1
      have h2 : ((6:ℕ).succ : ℝ) / ((6:ℕ).factorial * (6:ℕ)) = 7/(720*6) := by
        norm_num [Nat.factorial]
      linarith [h1, h2]
    refine lt_of_le_of_lt habs ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
      abs_of_nonneg (show (0:ℝ) ≤ 248/1000 by norm_num)]
    norm_num
  calc Real.exp ((248:ℝ)/1000) < 12566368/9805000 := hexp
    _ < 4000 * Real.pi / 9805 := by nlinarith

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_part1_integrableOn :
    IntegrableOn (fun x => 1/(Real.exp (x/2)+1) - 1/(Real.exp x+1))
      (Set.Ioi (0:ℝ)) := by
  have _em := Classical.em
  have hG0 := gapsw80_t77_part1_hasDerivAt 0
  exact integrableOn_Ioi_deriv_of_nonneg hG0.continuousAt.continuousWithinAt
    (fun x _ => gapsw80_t77_part1_hasDerivAt x)
    (fun x hx => gapsw80_t77_part1_nonneg hx)
    (by
      have h1 : Tendsto (fun y => (1:ℝ)+Real.exp (-y)) atTop (nhds (1+0)) :=
        tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero
      have h2 : Tendsto (fun y => (1:ℝ)+Real.exp (-(y/2))) atTop (nhds (1+0)) := by
        apply tendsto_const_nhds.add
        exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
          (Tendsto.atTop_div_const (by norm_num) tendsto_id))
      have hcL := (Real.continuousAt_log (show (1:ℝ)+0 ≠ 0 by norm_num)).tendsto
      have := (hcL.comp h1).sub ((hcL.comp h2).const_mul 2)
      simpa [Real.log_one] using this)

set_option maxHeartbeats 6400000 in

theorem gapsw80_t77_I_eq_log_two_add_J :
    (∫ x in Set.Ioi (0:ℝ),
        (1 - gapsw80_t75_bourbakiKernel x) / (Real.exp (x/2) - Real.exp (-(x/2))))
      = Real.log 2
        + ∫ x in Set.Ioi (0:ℝ), (1 - Real.exp (-(11/100)*x^2)) / Real.sinh x := by
  have _em := Classical.em
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => gapsw80_t77_integrand_split hx),
    integral_add gapsw80_t77_part1_integrableOn gapsw80_t77_J_integrableOn,
    gapsw80_t77_integral_part1_eq_log_two]

set_option maxHeartbeats 12800000 in

theorem gapsw80_t77_bourbakiArchDerivedLowerBound :
    gapsw80_t75_BourbakiArchDerivedLowerBound := by
  have _em := Classical.em
  rw [gapsw80_t75_bourbakiArchDerivedLowerBound_iff, gapsw80_t18_archDerived,
    gapsw80_t77_I_eq_log_two_add_J]
  have hrew : Real.log (4*Real.pi) - Real.log 2 - Real.log ((9805:ℝ)/2000)
      = Real.log (4000*Real.pi/9805) := by
    rw [← Real.log_div (by positivity) (by norm_num),
        ← Real.log_div (by positivity) (by norm_num)]
    congr 1; field_simp; ring
  have hγ := gapsw80_t77_gamma_gt
  have hL := gapsw80_t77_log_4000pi_div_9805_gt
  have hJ := gapsw80_t77_J_lt
  have hS := gapsw80_t77_sqrt_100pi_div_11_lt
  have hlog2 := Real.log_two_lt_d9
  have hnum : (290774257297357:ℝ)/72201776446800 - 5*(6931471808/10^10)
      + 248/1000 - ((231429/500000)*(917/1000) + (-689337/4000000) + 2/19)
      - (5345/1000)/12 > 0 := by norm_num
  nlinarith [hγ, hL, hJ, hS, hlog2, hrew, hnum]

end FLT.Gapsw80T77BourbakiArchDerivedLowerBoundProof

end

open FLT.Gapsw80T75BourbakiKernelDef FLT.Gapsw80T76BourbakiStripPositivityProof FLT.Gapsw80T77BourbakiArchDerivedLowerBoundProof FLT.Gapsw80T13AffineArchTermA34Redecomp FLT.Gapsw80T18ArchDerivedA34Redecomp FLT.Gapsw80T21D2SubDecompWire in

theorem solution :
    let F : ℝ → ℝ := fun x => Real.exp (-(11 / 100) * x ^ 2) / Real.cosh (x / 2)

    Differentiable ℝ F ∧ (∀ x : ℝ, F (-x) = F x) ∧ F 0 = 1 ∧ (∀ x : ℝ, 0 ≤ F x) ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧

    (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      0 ≤ ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x)) ∧

    ContDiff ℝ 2 F ∧
    (∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) ∧

    (2 * ∫ x in Set.Ioi (0 : ℝ), F x * (Real.exp (x / 2) + Real.exp (-(x / 2)))
        = 2 * Real.sqrt (100 * Real.pi / 11)) ∧

    (Real.log (9805 / 2000) + (1 / 12) * Real.sqrt (100 * Real.pi / 11)
      ≤ Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
          - ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2)))) := by
  intro F
  have hF : F = gapsw80_t75_bourbakiKernel := rfl
  refine ⟨gapsw80_t75_bourbakiKernel_differentiable, gapsw80_t75_bourbakiKernel_even,
    gapsw80_t75_bourbakiKernel_zero, gapsw80_t75_bourbakiKernel_nonneg,
    gapsw80_t75_bourbakiKernel_decay, ?_, gapsw80_t75_bourbakiKernel_contDiff,
    gapsw80_t75_bourbakiKernel_iterDeriv_decay, ?_, ?_⟩
  · exact gapsw80_t76_bourbakiStripPositivity
  · exact gapsw80_t75_poleTerm_bourbakiKernel
  · exact (gapsw80_t75_bourbakiArchDerivedLowerBound_iff).mp gapsw80_t77_bourbakiArchDerivedLowerBound

end S_Real_poitouKernel_admissible_and_archBound
end P2MW
export P2MW.S_Real_poitouKernel_admissible_and_archBound (solution)
