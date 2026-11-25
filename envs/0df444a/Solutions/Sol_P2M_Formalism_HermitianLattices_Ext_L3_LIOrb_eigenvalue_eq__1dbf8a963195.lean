-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_eigenvalue_eq__1dbf8a963195
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:11.713256+00:00
-- url     : https://prove2.me/submissions/c2a8351c-b569-4173-bb4d-7acddd865126

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NuGmapLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RepRatioEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution (T : Submodule (𝓞 K) V') (𝔭 : Ideal (𝓞 F)) :
    lamP h' T 𝔭 = alphaStd K 𝔭 (finrank K V') * (nu h' T 𝔭)⁻¹ := by
  unfold lamP nu
  rw [inv_div, mul_div_assoc]
end Formalism.HermitianLattices.Ext.L3.LIOrb
