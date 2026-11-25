-- Prove2me | solution 1 for PI.VolStabSW.CompGAux.eventually_struct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:51:15.326784+00:00
-- url     : https://prove2.me/submissions/e70a82c2-69fc-4ab9-b967-34a9520d6249

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallyStruct

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
open PI.VolStabSW.CompGAux
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabSW.FiniteThetaCoordinates
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabSW.CompGAux
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ p q k,
      algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro p q k
  first
  | exact (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((b.repr (b p * b q)) k)).2
  | exact RestrictedProduct.eventually (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((b.repr (b p * b q)) k))
  | exact ((algebraMap F (FiniteAdeleRing (𝓞 F) F) ((b.repr (b p * b q)) k)).2).mono
      fun v hv => by simpa [FiniteAdeleRing.algebraMap_apply] using hv
end PI.VolStabSW.CompGAux
