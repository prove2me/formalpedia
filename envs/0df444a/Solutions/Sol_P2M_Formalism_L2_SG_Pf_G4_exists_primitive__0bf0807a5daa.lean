-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_G4_exists_primitive__0bf0807a5daa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:55.830632+00:00
-- url     : https://prove2.me/submissions/e8348744-087e-4d92-992c-941240c9c337

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation

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
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.L2.SG.Pf.G4
theorem _root_.solution (hS : IsHermSemilocal S) (hM : IsLatIn S h W M) {ξ w : V} (hξ : ξ ∈ W)
    (hw : w ∈ W) (hn : h w ξ ≠ 0) :
    ∃ l : K, l ≠ 0 ∧ l • ξ ∈ M ∧ ∀ c : K, c • ξ ∈ M → c * l⁻¹ ∈ S := by
  obtain ⟨t, ht0, htM⟩ := hM.span w hw
  have hsp := hM.span ξ hξ
  let A : AddSubgroup K :=
    { carrier := {c | c • ξ ∈ M}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • ξ ∈ M
        rw [add_smul]
        exact M.add_mem ha hb
      zero_mem' := by
        show (0 : K) • ξ ∈ M
        rw [zero_smul]
        exact M.zero_mem
      neg_mem' := fun {a} ha => by
        show (-a) • ξ ∈ M
        rw [neg_smul]
        exact M.neg_mem ha }
  have hA : ∀ c, c ∈ A ↔ c • ξ ∈ M := fun c => Iff.rfl
  obtain ⟨α, hαA, hα0, hα⟩ := hS.principal A
    (fun s hs a ha => by
      rw [hA] at ha ⊢
      rw [mul_smul]
      exact hM.smul_mem s hs _ ha)
    (by
      obtain ⟨t', ht'0, ht'M⟩ := hsp
      exact ⟨t', (hA t').2 ht'M, ht'0⟩)
    ⟨star t * h w ξ, mul_ne_zero (star_ne_zero.2 ht0) hn, fun a ha => by
      rw [hA] at ha
      have hi := hM.int _ htM _ ha
      have e : h (t • w) (a • ξ) = star t * h w ξ * a := by
        rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
        ring
      rw [← e]
      exact hi⟩
  exact ⟨α, hα0, (hA α).1 hαA, fun c hc => hα c ((hA c).2 hc)⟩
end Formalism.L2.SG.Pf.G4
