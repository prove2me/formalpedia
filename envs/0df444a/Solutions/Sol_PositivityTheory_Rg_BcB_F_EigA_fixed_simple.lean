-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.fixed_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:10.118014+00:00
-- url     : https://prove2.me/submissions/ab4f917f-b009-4ae7-ab06-48e83878fc99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_finsum_refine
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_mem_fixed_iff
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_finiteIndex_stabK
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_hop_apply
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_term_inv
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_hop_mem_fixed
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution {K : Subgroup G} (hK : GelPair K) (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible)
    (W : Submodule ℂ (fixed ρ K)) (hW : W ≠ ⊥)
    (hst : ∀ g : G, ∀ w : fixed ρ K, w ∈ W → ∀ y : fixed ρ K, (y : V) = hop ρ K g w → y ∈ W) : W = ⊤ := by
  classical
  obtain ⟨-, hirr'⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hirr
  let W' : Submodule ℂ V := W.map (fixed ρ K).subtype
  let U : Submodule ℂ V := Submodule.span ℂ {y | ∃ g : G, ∃ w ∈ W', y = ρ g w}
  have hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U := by
    intro g v hv
    have : U ≤ U.comap (ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨g', w, hw, rfl⟩
      refine Submodule.subset_span ⟨g * g', w, hw, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    exact this hv
  obtain ⟨w0, hw0, hw0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hUne : U ≠ ⊥ := by
    intro hb
    have : ((w0 : fixed ρ K) : V) ∈ U :=
      Submodule.subset_span ⟨1, _, Submodule.mem_map_of_mem hw0, by simp⟩
    rw [hb, Submodule.mem_bot] at this
    exact hw0ne (Subtype.ext this)
  have hUtop : U = ⊤ := (hirr' U hU).resolve_left hUne
  rw [eq_top_iff]
  intro x _
  have hxU : (x : V) ∈ U := hUtop ▸ Submodule.mem_top
  obtain ⟨n, c, s, hs⟩ := Submodule.mem_span_set'.1 hxU
  have hch : ∀ i, ∃ g : G, ∃ w ∈ W', (s i : V) = ρ g w := fun i => (s i).2
  choose gs ws hws hgw using hch
  haveI : ∀ i, (stabK K (gs i)).FiniteIndex := fun i => finiteIndex_stabK (hK.1 (gs i))
  let K' : Subgroup K := ⨅ i, stabK K (gs i)
  haveI : K'.FiniteIndex := Subgroup.finiteIndex_iInf (fun i => inferInstance)
  letI := Fintype.ofFinite (K ⧸ K')
  let P : V →ₗ[ℂ] V := ∑ q : K ⧸ K', ρ ((q.out : K) : G)
  have hPx : P x = (Fintype.card (K ⧸ K')) • (x : V) := by
    simp only [P, LinearMap.sum_apply, (mem_fixed_iff.1 x.2) _ (Subtype.coe_prop _), Finset.sum_const,
      Finset.card_univ]
  have hPs : ∀ i, P (ρ (gs i) (ws i)) ∈ W' := by
    intro i
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hws i)
    have hwf : ws i ∈ fixed ρ K := hue ▸ u.2
    haveI : Finite (K ⧸ stabK K (gs i)) := inferInstance
    have hle : K' ≤ stabK K (gs i) := iInf_le _ i
    have h1 : P (ρ (gs i) (ws i)) = ∑ᶠ q : K ⧸ K', ρ ((q.out : K) : G) (ρ (gs i) (ws i)) := by
      rw [finsum_eq_sum_of_fintype]
      simp only [P, LinearMap.sum_apply]
    rw [h1, finsum_refine K' (stabK K (gs i)) hle (fun y : K => ρ (y : G) (ρ (gs i) (ws i))) (term_inv hwf),
      ← hop_apply]
    refine W'.smul_of_tower_mem _ ?_
    refine Submodule.mem_map.2 ⟨⟨hop ρ K (gs i) (ws i), hop_mem_fixed hwf⟩,
      hst (gs i) u hu _ (by show hop ρ K (gs i) (ws i) = hop ρ K (gs i) u; rw [← hue]; rfl), rfl⟩
  have hsum : P x ∈ W' := by
    rw [← hs, map_sum]
    refine W'.sum_mem fun i _ => ?_
    rw [map_smul, hgw i]
    exact W'.smul_mem _ (hPs i)
  rw [hPx] at hsum
  have hcard : (Fintype.card (K ⧸ K') : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hx' : (x : V) ∈ W' := by
    have := W'.smul_mem ((Fintype.card (K ⧸ K') : ℂ)⁻¹) hsum
    rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul] at this
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx'
  have : y = x := Subtype.ext hyx
  rwa [← this]
end PositivityTheory.Rg.BcB.F.EigA
