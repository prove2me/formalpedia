-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdInst.BR_cont_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:07.102904+00:00
-- url     : https://prove2.me/submissions/8ff25081-c24e-4006-994e-8ac6c6b83bb6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExInst
import Theorems.Thm_PI_VolStabSW_HasDens_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdInst
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.OmFibreUniq.W.SdInst
theorem _root_.solution (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (fun p : (Fin a → Fin n → Fv F v ⊗[F] E) × (Fin a → Fin n → Fv F v ⊗[F] E) =>
      BR (Fv F v) σ J p.1 p.2) := by
  have htr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) := by
    first
    | exact IsModuleTopology.continuous_of_linearMap _
    | exact LinearMap.continuous_of_finiteDimensional _
  let φ : (Fv F v ⊗[F] E) →ₐ[Fv F v] (Fv F v ⊗[F] E) :=
    Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ
  have hφ : ∀ z, sigR (Fv F v) σ z = φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsg : Continuous (sigR (Fv F v) σ) := by
    have h1 : ⇑(sigR (Fv F v) σ) = ⇑(φ.toLinearMap) := funext hφ
    rw [h1]
    first
    | exact IsModuleTopology.continuous_of_linearMap _
    | exact LinearMap.continuous_of_finiteDimensional _
  unfold BR hR Formalism.UG.hform
  fun_prop
end PI.OmFibreUniq.W.SdInst
