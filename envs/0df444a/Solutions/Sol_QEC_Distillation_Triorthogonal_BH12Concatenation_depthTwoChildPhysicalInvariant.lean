-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildPhysicalInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:31:37.472533+00:00
-- url     : https://prove2.me/submissions/2f3c8032-3021-4fe6-aa40-4f1f3dc8d445

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoChildRun_eq_bh12ActualRun
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoChildSelectedPortTransportedDensity_eq_selectedPortDensity

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat) (p : ErrorParameter)
    (firstPort secondPort : OddRow q)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1) :
    ∃ hfirst : 0 < rawSuccessMass q p,
      ∃ hsecond : 0 < rawSuccessMass q
          (bh12DecodedMarginalErrorParameter q p hfirst firstPort),
        0 < (depthTwoChildRun q p firstPort).successProbability ∧
          depthTwoChildSelectedPortTransportedDensity q p firstPort secondPort =
            OneQubit.diagonalAResource
              (bh12DecodedMarginalErrorParameter q
                (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
                hsecond secondPort) ∧
          (bh12DecodedMarginalErrorParameter q
            (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
            hsecond secondPort).rate ≤
              quadraticCoefficient q ^ 3 * p.rate ^ 4 := by
  obtain ⟨hfirst, hfirstActual, _hfirstDensity, hfirstQuadratic,
    _hfirstNonincrease, hfirstSmall, hfirstHalf, hfirstCoefficient⟩ :=
    bh12OneStepPhysicalInvariant q p firstPort hsmall hhalf hquadraticSmall
  obtain ⟨hsecond, hsecondActual, hsecondDensity, hsecondQuadratic,
    _hsecondNonincrease, _hsecondSmall, _hsecondHalf, _hsecondCoefficient⟩ :=
    bh12OneStepPhysicalInvariant q
      (bh12DecodedMarginalErrorParameter q p hfirst firstPort) secondPort
      hfirstSmall hfirstHalf hfirstCoefficient
  have hchildSuccess : 0 < (depthTwoChildRun q p firstPort).successProbability := by
    rw [depthTwoChildRun_eq_bh12ActualRun q p hfirst firstPort]
    exact hsecondActual
  have hchildDensity :
      depthTwoChildSelectedPortTransportedDensity q p firstPort secondPort =
        OneQubit.diagonalAResource
          (bh12DecodedMarginalErrorParameter q
            (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
            hsecond secondPort) := by
    rw [depthTwoChildSelectedPortTransportedDensity_eq_selectedPortDensity
      q p hfirst firstPort secondPort]
    exact hsecondDensity
  have hfirstRateNonneg :
      0 ≤ (bh12DecodedMarginalErrorParameter q p hfirst firstPort).rate :=
    (bh12DecodedMarginalErrorParameter q p hfirst firstPort).rate_nonneg
  have hquadraticUpperNonneg :
      0 ≤ quadraticCoefficient q * p.rate ^ 2 :=
    mul_nonneg (le_of_lt (quadraticCoefficient_pos q)) (sq_nonneg _)
  have hfirstSquare :
      (bh12DecodedMarginalErrorParameter q p hfirst firstPort).rate ^ 2 ≤
        (quadraticCoefficient q * p.rate ^ 2) ^ 2 :=
    (sq_le_sq₀ hfirstRateNonneg hquadraticUpperNonneg).mpr hfirstQuadratic
  have htwiceQuadratic :
      (bh12DecodedMarginalErrorParameter q
        (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
        hsecond secondPort).rate ≤
          quadraticCoefficient q * (quadraticCoefficient q * p.rate ^ 2) ^ 2 :=
    hsecondQuadratic.trans
      (mul_le_mul_of_nonneg_left hfirstSquare
        (le_of_lt (quadraticCoefficient_pos q)))
  refine ⟨hfirst, hsecond, hchildSuccess, hchildDensity, ?_⟩
  calc
    (bh12DecodedMarginalErrorParameter q
      (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
      hsecond secondPort).rate ≤
        quadraticCoefficient q * (quadraticCoefficient q * p.rate ^ 2) ^ 2 :=
      htwiceQuadratic
    _ = quadraticCoefficient q ^ 3 * p.rate ^ 4 := by ring
end QEC.Distillation.Triorthogonal.BH12Concatenation
