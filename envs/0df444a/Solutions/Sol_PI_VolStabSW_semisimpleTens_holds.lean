-- Prove2me | solution 1 for PI.VolStabSW.semisimpleTens_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:42.379394+00:00
-- url     : https://prove2.me/submissions/e5b12d5a-62c9-4434-9ad6-49578dff491a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfSS
import Theorems.Thm_PI_VolStabSW_isReduced_tens_field

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution : SemisimpleTens := by
  intro F E _ _ _ _ _ σ _
  classical
  have : IsArtinianRing (Ainf F) :=
    inferInstanceAs (IsArtinianRing ((v : InfinitePlace F) → v.Completion))
  have : IsArtinianRing (Ainf F ⊗[F] E) := IsArtinianRing.of_finite (Ainf F) (Ainf F ⊗[F] E)
  let e1 : Ainf F ⊗[F] E ≃ₐ[F] E ⊗[F] Ainf F := Algebra.TensorProduct.comm F (Ainf F) E
  let e2 : E ⊗[F] ((v : InfinitePlace F) → v.Completion) ≃ₐ[F]
      ((v : InfinitePlace F) → E ⊗[F] v.Completion) :=
    Algebra.TensorProduct.piRight F F E (fun v : InfinitePlace F => v.Completion)
  have : ∀ v : InfinitePlace F, IsReduced (E ⊗[F] v.Completion) := fun v =>
    have := isReduced_tens_field F E v.Completion
    isReduced_of_injective (Algebra.TensorProduct.comm F E v.Completion).toRingHom
      (Algebra.TensorProduct.comm F E v.Completion).injective
  have : IsReduced (Ainf F ⊗[F] E) :=
    isReduced_of_injective ((e2.toRingHom).comp e1.toRingHom) (e2.injective.comp e1.injective)
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _
end PI.VolStabSW
