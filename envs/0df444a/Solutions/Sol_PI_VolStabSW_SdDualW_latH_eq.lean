-- Prove2me | solution 1 for PI.VolStabSW.SdDualW.latH_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:00.335434+00:00
-- url     : https://prove2.me/submissions/1ce2266d-df74-4ef5-9550-3e7258fe5ad4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E]
namespace PI.VolStabSW.SdDualW
theorem _root_.solution (σ : E →ₐ[F] E) (a : ℕ) :
    (latH v b σ a : Set (HermR (Fv F v) σ a)) = Subtype.val ⁻¹'
      ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latS v b σ : Set (Fv F v ⊗[F] E))) :
        Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) := by
  ext S
  exact ⟨fun h p _ q _ => h p q, fun h p q => h p (Set.mem_univ _) q (Set.mem_univ _)⟩
end PI.VolStabSW.SdDualW
