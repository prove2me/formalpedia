-- Prove2me | solution 1 for PI.VolStabW.CompGAux.crd_mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:45.745886+00:00
-- url     : https://prove2.me/submissions/fb123b0f-149a-43ab-8a5c-05c8f8cfe93b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_EventuallyStruct
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_crd_mulVec


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (y : Fin M → Fv F v ⊗[F] E)
    (hm : ∀ i j p, crd b (Fv F v) (m i j) p ∈ v.adicCompletionIntegers F)
    (hy : ∀ j q, crd b (Fv F v) (y j) q ∈ v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (i : Fin M) (k : Fin d) : crd b (Fv F v) ((m.mulVec y) i) k ∈ v.adicCompletionIntegers F := by
  rw [crd_mulVec]
  exact sum_mem fun j _ => sum_mem fun p _ => sum_mem fun q _ =>
    mul_mem (mul_mem (hm i j p) (hy j q)) (hc p q k)
end PI.VolStabW.CompGAux
