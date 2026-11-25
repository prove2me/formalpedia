-- Prove2me | solution 1 for PI.VolStabSW.SdDualW.isCompact_latS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:31:03.180842+00:00
-- url     : https://prove2.me/submissions/726bab81-4694-4d31-9089-eed3aff9b825

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Theorems.Thm_PI_VolStabSW_SdDualW_isCompact_latA
import Theorems.Thm_PI_VolStabSW_SdDualW_mem_latS
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv


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
theorem _root_.solution (σ : E →ₐ[F] E) : IsCompact (latS v b σ : Set (Fv F v ⊗[F] E)) := by
  have e : (latS v b σ : Set (Fv F v ⊗[F] E)) =
      (fun p : (Fv F v ⊗[F] E) × (Fv F v ⊗[F] E) => p.1 + sigR (Fv F v) σ p.2) ''
        ((latA v b : Set (Fv F v ⊗[F] E)) ×ˢ (latA v b : Set (Fv F v ⊗[F] E))) := by
    ext z
    rw [SetLike.mem_coe, mem_latS]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  rw [e]
  have := locallyCompact_Fv F v
  exact ((isCompact_latA v b).prod (isCompact_latA v b)).image
    (continuous_fst.add ((continuous_sigR (Fv F v) σ).comp continuous_snd))
end PI.VolStabSW.SdDualW
