-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.exp_mulVec_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:16.335012+00:00
-- url     : https://prove2.me/submissions/6db61f8c-ad1d-491b-9e53-f10b10678ea6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
open PI.QnHermHaar.HermitianAdjointLemmas
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace PI.QnHermHaar.HermitianAdjointLemmas
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hv : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) X
  have hexp : NormedSpace.exp X = ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • X ^ m := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  let φ : Matrix (Fin n) (Fin n) ℂ →+ (Fin n → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_zero' := Matrix.zero_mulVec v
      map_add' := fun A B => Matrix.add_mulVec A B v }
  have hφ : Continuous φ := continuous_id.matrix_mulVec continuous_const
  have h1 := hs.hasSum.map φ hφ
  have h2 : HasSum (fun m : ℕ => φ (((m.factorial : ℂ)⁻¹) • X ^ m)) v := by
    have e : (fun m : ℕ => φ (((m.factorial : ℂ)⁻¹) • X ^ m)) = fun m => if m = 0 then v else 0 := by
      funext m
      rcases m with _ | m
      · simp [φ]
      · simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (Nat.succ_ne_zero m)]
        rw [Matrix.smul_mulVec, pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
          smul_zero]
    rw [e]
    exact hasSum_ite_eq 0 v
  rw [hexp]
  exact h1.unique h2
end PI.QnHermHaar.HermitianAdjointLemmas
