-- Prove2me | solution 1 for P2M_GlobalTheory_SerConj_bcEquiv___3b5f4a7a85e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:07.50837+00:00
-- url     : https://prove2.me/submissions/8aaff890-a080-49ce-afb1-04a4473281df

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
variable {Γ : Type} [Group Γ]
namespace GlobalTheory.SerConj
theorem _root_.solution (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ) (v : τ) :
    bcEquiv σ τ (τ.ρ γ v) = (bc σ τ).ρ γ (bcEquiv σ τ v) := by
  refine funext fun i => ?_
  change σ ((Module.finBasis ℂ τ).repr (τ.ρ γ v) i) =
    (((LinearMap.toMatrix (Module.finBasis ℂ τ) (Module.finBasis ℂ τ) (τ.ρ γ)).map σ).mulVec
      fun k => σ ((Module.finBasis ℂ τ).repr v k)) i
  rw [← LinearMap.toMatrix_mulVec_repr (Module.finBasis ℂ τ) (Module.finBasis ℂ τ)]
  simp [Matrix.mulVec, dotProduct]
end GlobalTheory.SerConj
