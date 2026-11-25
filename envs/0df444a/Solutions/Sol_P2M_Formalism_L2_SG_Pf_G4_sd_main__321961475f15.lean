-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G4_sd_main__321961475f15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:08.571843+00:00
-- url     : https://prove2.me/submissions/a4cb14c9-3589-4246-abd3-2a77e3f892d6

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsIsomScale
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_prep__c54da6000b34
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsASD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsLatIn_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_IsSD_cut
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_cutW
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_proj_mem
import Theorems.Thm_Formalism_L2_SG_Pf_G4_nondegOn_cut
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_IsSD_exists_norm__3019c7167a34
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_IsSD_exists_unit_norm__db471541043b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G4
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.G4
theorem _root_.solution [FiniteDimensional K V] (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (φ : V ≃ₗ[K] V), finrank K W₁ ≤ n →
      NondegOn h W₁ → IsSD S h W₁ M → IsSD S h W₂ N → φ ∈ Formalism.HermitianLatticesTheory.isom h →
      (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => by
    rw [← starRingEnd_apply]
    exact hs.eq u v
  induction n with
  | zero =>
    intro W₁ W₂ M N φ hr hnd hM hN hφ hW
    have hW0 : W₁ = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hr)
    refine ⟨φ, hφ, fun v _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · have h0 : v = 0 := by
        have := hM.le v hv
        rwa [hW0, Submodule.mem_bot] at this
      rw [h0, map_zero]
      exact N.zero_mem
    · have h0 : v = 0 := by
        have := (hW v).2 (hN.le _ hv)
        rwa [hW0, Submodule.mem_bot] at this
      rw [h0]
      exact M.zero_mem
  | succ n ih =>
    intro W₁ W₂ M N φ hr hnd hM hN hφ hW
    by_cases hW0 : W₁ = ⊥
    · refine ⟨φ, hφ, fun v _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
      · have h0 : v = 0 := by
          have := hM.le v hv
          rwa [hW0, Submodule.mem_bot] at this
        rw [h0, map_zero]
        exact N.zero_mem
      · have h0 : v = 0 := by
          have := (hW v).2 (hN.le _ hv)
          rwa [hW0, Submodule.mem_bot] at this
        rw [h0]
        exact M.zero_mem
    have hφ' : ∀ a c, h (φ a) (φ c) = h a c := hφ
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨x, hxM, hxu⟩ := IsSD.exists_unit_norm' hS hπ hs hnd hM hξ hξ0
    have hx : x ∈ W₁ := hM.le x hxM
    have hφx : φ x ∈ W₂ := (hW x).1 hx
    obtain ⟨X, hXN, hXx⟩ := IsSD.exists_norm' hS hπ hs hN hφx hxu (hφ' x x)
    have hx0 : h x x ≠ 0 := hxu.1
    have hXu : IsUnitIn S (h X X) := by
      rw [hXx]
      exact hxu
    obtain ⟨φ₁, hφ₁, hφ₁x, hφ₁W, hφ₁v⟩ := exists_prep' hs h2 hφ hW hx (hN.le X hXN) hXx.symm hx0
    have hr' : finrank K (cutW h W₁ x) ≤ n := by
      have hlt : finrank K (cutW h W₁ x) < finrank K W₁ := by
        apply Submodule.finrank_lt_finrank_of_lt
        rw [lt_iff_le_and_ne]
        refine ⟨fun v hv => (mem_cutW.1 hv).1, fun heq => ?_⟩
        have hxc : x ∈ cutW h W₁ x := by
          rw [heq]
          exact hx
        exact hx0 (mem_cutW.1 hxc).2
      omega
    obtain ⟨g, hg, hgv, hgM⟩ := ih (cutW h W₁ x) (cutW h W₂ X) (cutM h M x) (cutM h N X) φ₁ hr'
      (nondegOn_cut hnd hx hx0) (hM.cut hxM hxu) (hN.cut hXN hXu) hφ₁ hφ₁W
    have hg' : ∀ a c, h (g a) (g c) = h a c := hg
    have horth : ∀ w ∈ cutW h W₁ x, h w x = 0 := fun w hw => by
      rw [← hsym x w, (mem_cutW.1 hw).2, star_zero]
    have hgx : g x = X := by
      rw [hgv x horth, hφ₁x]
    have hdec : ∀ v : V, v = (v - (h x v * (h x x)⁻¹) • x) + (h x v * (h x x)⁻¹) • x :=
      fun v => by abel
    have hgdec : ∀ v, g v = g (v - (h x v * (h x x)⁻¹) • x) + (h x v * (h x x)⁻¹) • X := fun v => by
      conv_lhs => rw [hdec v]
      rw [map_add, map_smul, hgx]
    refine ⟨g, hg, fun v hv => ?_, fun v => ?_⟩
    · rw [hgv v (fun w hw => hv w (mem_cutW.1 hw).1), hφ₁v v hv]
    have hxvX : h X (g v) = h x v := by
      rw [← hgx, hg']
    have hxxinv : (h x x)⁻¹ ∈ S := hxu.2.2
    constructor
    · intro hv
      have ha : h x v * (h x x)⁻¹ ∈ S := S.mul_mem (hM.int x hxM v hv) hxxinv
      have hp := proj_mem hM.toIsLatIn hxM hxu hv
      have hgp := (hgM _).1 hp
      rw [hgdec v]
      exact N.add_mem (AddSubgroup.mem_inf.1 hgp).1 (hN.smul_mem _ ha X hXN)
    · intro hv
      have hiS : h x v ∈ S := by
        rw [← hxvX]
        exact hN.int X hXN (g v) hv
      have ha : h x v * (h x x)⁻¹ ∈ S := S.mul_mem hiS hxxinv
      have hq := proj_mem hN.toIsLatIn hXN hXu hv
      rw [hxvX, hXx] at hq
      have hq' : g (v - (h x v * (h x x)⁻¹) • x) ∈ cutM h N X := by
        rw [map_sub, map_smul, hgx]
        exact hq
      have hp := (hgM _).2 hq'
      rw [hdec v]
      exact M.add_mem (AddSubgroup.mem_inf.1 hp).1 (hM.smul_mem _ ha x hxM)
end Formalism.L2.SG.Pf.G4
