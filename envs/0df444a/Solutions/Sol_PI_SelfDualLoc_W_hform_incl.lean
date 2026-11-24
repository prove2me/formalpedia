-- Prove2me | solution 1 for PI.SelfDualLoc.W.hform_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:42:49.923564+00:00
-- url     : https://prove2.me/submissions/ec37ef5d-e0b0-479f-87c7-f88c26ef1074

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_SelfDualLocOfDirs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Assembly
import Theorems.Thm_PI_SelfDualLoc_W_sigR_inclE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.SelfDualLoc.W
theorem _root_.solution {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (v : HeightOneSpectrum (𝓞 F)) (a b : Fin n → E) :
    hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
      (fun i => inclE (F := F) (v.adicCompletion F) (a i))
      (fun i => inclE (F := F) (v.adicCompletion F) (b i)) =
      inclE (F := F) (v.adicCompletion F) (hform (σ : E →+* E) J a b) := by
  simp only [hform, Matrix.map_apply, sigR_inclE, map_sum, map_mul]
  rfl
end PI.SelfDualLoc.W
