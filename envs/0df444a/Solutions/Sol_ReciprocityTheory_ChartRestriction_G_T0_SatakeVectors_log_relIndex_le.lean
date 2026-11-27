-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.log_relIndex_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:19:16.273409+00:00
-- url     : https://prove2.me/submissions/024dc857-451f-4575-b12a-e8f4b1159481

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_sum_smul_bG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_linInd_bG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_gauss_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_relIndex_pi_const
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_contId_ne_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_mem_inv_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_relIndex_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (G₀ : MvPolynomial κ (𝓞 K))
    (hG : G₀ ≠ 0) (S T : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S,
      (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial m 1).support ⊆ T) :
    Real.log ((Submodule.span (𝓞 K)
        (Set.range (bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e))).toAddSubgroup.relIndex
      (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r)
        (bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e)).toAddSubgroup : ℝ) ≤
      S.card * Real.log (Ideal.absNorm (contId G₀) : ℝ) := by
  set G := MvPolynomial.map (algebraMap (𝓞 K) K) G₀ with hGdef
  have hG' : G ≠ 0 := by
    intro h0; apply hG
    exact MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)
      (by rw [← hGdef, h0, map_zero])
  set b := bG G S e with hbdef
  set Φ := phiB b with hΦdef
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have hli := linInd_bG G hG' S T e hST
    rw [Fintype.linearIndependent_iff] at hli
    exact funext (hli p hp)
  set O1 := (1 : Submodule (𝓞 K) K).toAddSubgroup with hO1
  set I1 := ((((contId G₀ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) :
    Submodule (𝓞 K) K).toAddSubgroup with hI1
  have hspan : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup =
      (AddSubgroup.pi Set.univ fun _ : Fin S.card => O1).map Φ := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
      refine ⟨fun j => (c j : K), fun j _ => ?_, ?_⟩
      · change (c j : K) ∈ O1
        rw [hO1, Submodule.mem_toAddSubgroup, Submodule.mem_one]; exact ⟨c j, rfl⟩
      · rw [← hc]
        simp only [hΦdef, phiB, AddMonoidHom.mk'_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact algebraMap_smul K (c j) (b j)
    · rintro ⟨p, hp, rfl⟩
      have hc : ∀ j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = p j := fun j => by
        have : p j ∈ O1 := hp j (Set.mem_univ j)
        rwa [hO1, Submodule.mem_toAddSubgroup, Submodule.mem_one] at this
      choose c hc using hc
      refine (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mpr ⟨c, ?_⟩
      simp only [hΦdef, phiB, AddMonoidHom.mk'_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc j]
      exact (algebraMap_smul K (c j) (b j)).symm
  have hB : (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b).toAddSubgroup ≤
      (AddSubgroup.pi Set.univ fun _ : Fin S.card => I1).map Φ := by
    intro x hx
    rw [Submodule.mem_toAddSubgroup] at hx
    obtain ⟨hxL, hxK⟩ := hx
    obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxK
    refine AddSubgroup.mem_map.mpr ⟨p, fun j _ => ?_, ?_⟩
    · change p j ∈ I1
      rw [hI1, Submodule.mem_toAddSubgroup]
      refine mem_inv_of G₀ hG (p j) fun s => ?_
      refine gauss_int G₀ hG S T e hST p ?_ j s
      intro i
      have h1 := (Submodule.mem_pi.mp hxL) i (Set.mem_univ i)
      rw [Submodule.mem_one] at h1
      obtain ⟨y, hy⟩ := h1
      refine ⟨y, ?_⟩
      rw [← sum_smul_bG, hp]
      exact hy
    · simp only [hΦdef, phiB, AddMonoidHom.mk'_apply]
      exact hp
  have hidx : O1.relIndex I1 = Ideal.absNorm (contId G₀) := by
    have := relIndex_inv G₀ hG
    exact_mod_cast this
  have hN0 : Ideal.absNorm (contId G₀) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact contId_ne_bot G₀ hG
  have hpi := relIndex_pi_const O1 I1 S.card
  rw [hidx] at hpi
  have hmm : ((AddSubgroup.pi Set.univ fun _ : Fin S.card => O1).map Φ).relIndex
      ((AddSubgroup.pi Set.univ fun _ : Fin S.card => I1).map Φ) =
      Ideal.absNorm (contId G₀) ^ S.card := by
    rw [AddSubgroup.relIndex_map_map_of_injective _ _ hΦ, hpi]
  have hle := AddSubgroup.relIndex_le_of_le_right hB (by rw [hmm]; exact pow_ne_zero _ hN0)
  rw [hmm, ← hspan] at hle
  have hN1 : (1 : ℝ) ≤ (Ideal.absNorm (contId G₀) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0
  rcases Nat.eq_zero_or_pos ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b).toAddSubgroup) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hN1)
  · rw [← Real.log_pow]
    refine Real.log_le_log (by exact_mod_cast hpos) ?_
    exact_mod_cast hle
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
