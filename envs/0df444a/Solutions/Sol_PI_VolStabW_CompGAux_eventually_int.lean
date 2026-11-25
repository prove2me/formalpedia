-- Prove2me | solution 1 for PI.VolStabW.CompGAux.eventually_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:57:08.639915+00:00
-- url     : https://prove2.me/submissions/f3a925f2-0e9e-4bd8-89de-1d5ef45b3623

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
theorem _root_.solution (g : HA (AF F) σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ i j p, piV F v (crd b (AF F)
      (((HA.mat (AF F) σ J g : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
        v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro i j p
  exact (eventually_piV_le_one F _).mono fun v hv => (norm_le_one_iff_mem F v _).1 hv
end PI.VolStabW.CompGAux
