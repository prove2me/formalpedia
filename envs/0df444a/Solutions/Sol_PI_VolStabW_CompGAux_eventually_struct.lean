-- Prove2me | solution 1 for PI.VolStabW.CompGAux.eventually_struct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:10.648485+00:00
-- url     : https://prove2.me/submissions/351a9248-3e0a-4293-97c3-5027db27cbb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_EventuallyStruct
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_eventually_piV_le_one
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_norm_le_one_iff_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.CompGAux
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabW.FiniteThetaCoordinates
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW.CompGAux
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ p q k,
      algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro p q k
  refine (eventually_piV_le_one F (algebraMap F (AF F) (b.repr (b p * b q) k))).mono fun v hv => ?_
  rw [AlgHom.commutes] at hv
  exact (norm_le_one_iff_mem F v _).1 hv
end PI.VolStabW.CompGAux
