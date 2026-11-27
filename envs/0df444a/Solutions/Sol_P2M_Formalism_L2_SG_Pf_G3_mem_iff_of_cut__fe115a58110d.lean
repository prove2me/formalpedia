-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G3_mem_iff_of_cut__fe115a58110d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:19.127124+00:00
-- url     : https://prove2.me/submissions/f1158a91-654f-4fc3-b80e-65731ba646ce

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanIffSpanS
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.G3
theorem _root_.solution {M N : AddSubgroup V} (hMs : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M)
    (hNs : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N) {x X : V} (hx : x ∈ M) (hX : X ∈ N)
    (hMx : ∀ m ∈ M, h x m * (h x x)⁻¹ ∈ S) (hNX : ∀ m ∈ N, h X m * (h X X)⁻¹ ∈ S)
    {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hgx : g x = X) (hxx : h x x ≠ 0)
    (hcut : ∀ v, v ∈ cutM h M x ↔ g v ∈ cutM h N X) : ∀ v, v ∈ M ↔ g v ∈ N := by
  have hcut' : ∀ v, (v ∈ M ∧ h x v = 0) ↔ (g v ∈ N ∧ h X (g v) = 0) := by
    intro v
    have := hcut v
    simp only [cutM, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker] at this
    exact this
  have hiso : ∀ u w, h (g u) (g w) = h u w := hg
  have hXX : h X X ≠ 0 := by
    rw [← hgx, hiso x x]
    exact hxx
  intro v
  constructor
  · intro hv
    have hαS : h x v * (h x x)⁻¹ ∈ S := hMx v hv
    have h1 : v - (h x v * (h x x)⁻¹) • x ∈ M := M.sub_mem hv (hMs _ hαS x hx)
    have h2 : h x (v - (h x v * (h x x)⁻¹) • x) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hxx, sub_self]
    obtain ⟨h3, -⟩ := (hcut' _).mp ⟨h1, h2⟩
    rw [map_sub, map_smul, hgx] at h3
    have := N.add_mem h3 (hNs _ hαS X hX)
    rwa [sub_add_cancel] at this
  · intro hv
    have hβS : h X (g v) * (h X X)⁻¹ ∈ S := hNX _ hv
    have h1 : g (v - (h X (g v) * (h X X)⁻¹) • x) ∈ N := by
      rw [map_sub, map_smul, hgx]
      exact N.sub_mem hv (hNs _ hβS X hX)
    have h2 : h X (g (v - (h X (g v) * (h X X)⁻¹) • x)) = 0 := by
      rw [map_sub, map_smul, hgx, map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hXX,
        sub_self]
    obtain ⟨h3, -⟩ := (hcut' _).mpr ⟨h1, h2⟩
    have := M.add_mem h3 (hMs _ hβS x hx)
    rwa [sub_add_cancel] at this
end Formalism.L2.SG.Pf.G3
