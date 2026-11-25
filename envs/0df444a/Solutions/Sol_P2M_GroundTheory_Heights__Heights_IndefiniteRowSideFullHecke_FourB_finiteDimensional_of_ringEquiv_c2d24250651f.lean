-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_finiteDimensional_of_ringEquiv_c2d24250651f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:04.338988+00:00
-- url     : https://prove2.me/submissions/57362c04-115e-4c4e-987c-296033e262ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
theorem _root_.solution {E₁ E₂ L : Type*} [Field E₁] [Field E₂] [Field L]
    [Algebra E₁ L] [Algebra E₂ L] (e : E₂ ≃+* E₁)
    (he : algebraMap E₂ L = (algebraMap E₁ L).comp (e : E₂ →+* E₁)) [FiniteDimensional E₁ L] :
    FiniteDimensional E₂ L := by
  let : Algebra E₂ E₁ := (e : E₂ →+* E₁).toAlgebra
  have : IsScalarTower E₂ E₁ L := IsScalarTower.of_algebraMap_eq fun z => by rw [he]; rfl
  have : Module.Finite E₂ E₁ := Module.Finite.of_surjective (Algebra.linearMap E₂ E₁) e.surjective
  exact Module.Finite.trans E₁ L
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
