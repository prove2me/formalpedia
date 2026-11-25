-- Prove2me | solution 1 for PI.VolStabSW.CompGAux.tmap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:40.132867+00:00
-- url     : https://prove2.me/submissions/4a22223b-35e5-440a-9ad2-c470adf7b6af

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabSW.CompGAux
theorem _root_.solution {T : Type} [CommRing T] [Algebra F T] (f : R →ₐ[F] S) (g : S →ₐ[F] T)
    (y : R ⊗[F] E) :
    Algebra.TensorProduct.map g (AlgHom.id F E) (Algebra.TensorProduct.map f (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (g.comp f) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp
  | add x y hx hy => simp only [map_add, hx, hy]
end PI.VolStabSW.CompGAux
