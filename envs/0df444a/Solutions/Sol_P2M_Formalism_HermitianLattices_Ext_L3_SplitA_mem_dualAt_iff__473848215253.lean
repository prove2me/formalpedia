-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_SplitA_mem_dualAt_iff__473848215253
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:46.835804+00:00
-- url     : https://prove2.me/submissions/42e5dcc2-b9cc-4763-8fb0-2bf297c7f29d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.SplitA
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (g : W →ₗ⋆[K] W →ₗ[K] K) (p : Ideal (𝓞 K))
    (M : Submodule (𝓞 K) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.dualAt g p M ↔ ∀ y ∈ M, g y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  unfold Formalism.HermitianLatticesTheory.dualAt
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
end Formalism.HermitianLattices.Ext.L3.SplitA
