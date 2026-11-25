-- Prove2me | solution 1 for PI.VolStabSW.CompGAux.map_smul_tup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:36.33455+00:00
-- url     : https://prove2.me/submissions/cb383c07-1174-437c-bf91-585bc7cb791f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallyStruct
import Theorems.Thm_PI_VolStabSW_CompGAux_mat_haMap_apply

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabSW.CompGAux
theorem _root_.solution (φ : R →ₐ[F] S) {n : ℕ} (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) ((h • X) x i)) =
      haMap σ J φ h • (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x i)) := by
  funext x i
  simp only [HSMul.hSMul, SMul.smul]
  unfold actTup
  simp [mat_haMap_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
end PI.VolStabSW.CompGAux
