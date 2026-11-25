-- Prove2me | solution 1 for PI.VolStabW.CompGAux.map_smul_tup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:30.953784+00:00
-- url     : https://prove2.me/submissions/67398e14-9adf-45b7-924d-0db4fbcea2ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_EventuallyStruct
import Theorems.Thm_PI_VolStabW_CompGAux_mat_haMap_apply

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW.CompGAux
theorem _root_.solution (φ : R →ₐ[F] S) {n : ℕ} (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) ((h • X) x i)) =
      haMap σ J φ h • (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x i)) := by
  funext x i
  show Algebra.TensorProduct.map φ (AlgHom.id F E)
      ((((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X x)) i) =
    (((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec
      (fun j => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x j))) i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, mat_haMap_apply]
end PI.VolStabW.CompGAux
