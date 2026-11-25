-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_cut_adjoin__7176bb1c31ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:34.390736+00:00
-- url     : https://prove2.me/submissions/b4ff65f7-9d7e-442d-9fc4-3cc30ce8daea

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_eq_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_adjoin_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_mem_cut_iff
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
theorem _root_.solution (L' : Submodule (𝓞 K) V') : S.cut (S.adjoin L') = L' := by
  ext a
  rw [S.mem_cut_iff, S.mem_adjoin_iff]
  constructor
  · rintro ⟨r, b, hb, he⟩
    have h0 : (0 : K) • S.x₀ + S.ι a = (algebraMap (𝓞 K) K r) • S.x₀ + S.ι b := by
      rw [zero_smul, zero_add]
      exact he
    rw [(S.comb_eq_iff.mp h0).2]
    exact hb
  · intro ha
    exact ⟨0, a, ha, by simp⟩
end Formalism.HermitianLattices.Ext.L3.VecSplit
