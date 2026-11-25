-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isUnimodularAt_adjoin_iff__b76ec24e3c29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:38.050833+00:00
-- url     : https://prove2.me/submissions/364a2ce5-fabd-400d-aa78-aac59d434036

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_mem_loc_adjoin_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_mem_dualAt_iff
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
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open Formalism.HermitianLattices.Ext.L3.VecSplit
variable (S : VecSplit h h')
namespace Formalism.HermitianLattices.Ext.L3.VecSplit
theorem _root_.solution (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1)
    (L' : Submodule (𝓞 K) V') (p : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L' := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  constructor
  · intro H
    ext a
    have h1' := S.comb_mem_dualAt_iff hs h1 p L' 0 a
    have h2' := S.comb_mem_loc_adjoin_iff p L' 0 a
    rw [H, h2'] at h1'
    simpa [Submodule.zero_mem] using h1'.symm
  · intro H
    ext v
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [S.comb_mem_dualAt_iff hs h1, S.comb_mem_loc_adjoin_iff, H]
end Formalism.HermitianLattices.Ext.L3.VecSplit
