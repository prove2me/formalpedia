-- Prove2me | solution 1 for PI.VolStabSW.CompGAux.smul_mem_latV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:10.799326+00:00
-- url     : https://prove2.me/submissions/2678cc5f-b2d5-4c6f-a794-ef3488a9b893

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallyStruct
import Theorems.Thm_PI_VolStabSW_CompGAux_crd_mulVec_mem

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {d a : ℕ} (b : Module.Basis (Fin d) F E)
    (h : HA (Fv F v) σ J)
    (hm : ∀ i j p, crd b (Fv F v)
      (((HA.mat (Fv F v) σ J h : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p ∈
        v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (Y : Fin a → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV b v) : h • Y ∈ latV b v := by
  simp only [latV, Set.mem_ofPred_eq] at hY ⊢
  intro x i k
  exact crd_mulVec_mem v b _ (Y x) hm (fun j q => hY x j q) hc i k
end PI.VolStabSW.CompGAux
