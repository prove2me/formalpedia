-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_kerfam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:18.515238+00:00
-- url     : https://prove2.me/submissions/578b89da-1cf8-4730-9cfd-1f352c58991f

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactSecond_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_scale
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_li_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ b : Fin (finrank K (LinearMap.ker N.mulVecLin)) → Fin r → K,
      (∀ i, b i ∈ L) ∧ (∀ i, N *ᵥ b i = 0) ∧ LinearIndependent K b ∧
      ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b) := by
  set b0 := Module.finBasis K (LinearMap.ker N.mulVecLin)
  choose d hd0 hdL using fun i => sc_scale L hL (b0 i : Fin r → K)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ i, algebraMap (𝓞 K) K (d i) ≠ 0 := fun i h =>
    hd0 i (hinj (by rw [h, map_zero]))
  refine ⟨fun i => algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K), fun i => ?_, fun i => ?_, ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K) ∈ L
    rw [algebraMap_smul]; exact hdL i
  · have h := (b0 i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    rw [mulVec_smul, h, smul_zero]
  · exact sc_li_scale (b0.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
  · intro y hy
    have hy' : y ∈ LinearMap.ker N.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hy
    have hsum := b0.sum_repr ⟨y, hy'⟩
    have hsum' : y = ∑ i, b0.repr ⟨y, hy'⟩ i • (b0 i : Fin r → K) := by
      calc y = ((⟨y, hy'⟩ : LinearMap.ker N.mulVecLin) : Fin r → K) := rfl
        _ = ((∑ i, b0.repr ⟨y, hy'⟩ i • b0 i : LinearMap.ker N.mulVecLin) : Fin r → K) := by
          rw [hsum]
        _ = _ := by rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
    rw [hsum']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hb : (b0 i : Fin r → K) =
        (algebraMap (𝓞 K) K (d i))⁻¹ • (algebraMap (𝓞 K) K (d i) • (b0 i : Fin r → K)) := by
      rw [inv_smul_smul₀ (ha i)]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end ReciprocityTheory.MultiplicativeHeights
