-- Prove2me | solution 1 for PI.VolStabSW.SdDualW.isCompact_latA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:38.378138+00:00
-- url     : https://prove2.me/submissions/038147e4-b35c-4089-b01f-5b4b04a7084c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isCompact_latV


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
theorem _root_.solution : IsCompact (latA v b : Set (Fv F v ⊗[F] E)) := by
  have e : (latA v b : Set (Fv F v ⊗[F] E)) =
      (fun Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E => Y 0 0) '' latV (M := 1) (n := 1) b v := by
    ext z
    constructor
    · intro hz
      exact ⟨fun _ _ => z, fun p i k => hz k, rfl⟩
    · rintro ⟨Y, hY, rfl⟩ k
      exact hY 0 0 k
  rw [e]
  exact (isCompact_latV b v 1 1).image ((continuous_apply 0).comp (continuous_apply 0))
end PI.VolStabSW.SdDualW
