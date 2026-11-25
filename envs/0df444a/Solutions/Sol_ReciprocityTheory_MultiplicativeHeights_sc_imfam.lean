-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_imfam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:12.467302+00:00
-- url     : https://prove2.me/submissions/6fd29ecd-caf1-4171-a7ee-31a7b2b38df3

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
    ∃ c : Fin (finrank K (LinearMap.range N.mulVecLin)) → Fin r → K,
      (∀ j, c j ∈ L) ∧ LinearIndependent K (fun j => N *ᵥ c j) := by
  set e := Module.finBasis K (LinearMap.range N.mulVecLin)
  have hex : ∀ j, ∃ y, N *ᵥ y = (e j : Fin r → K) := by
    intro j
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (e j).2
    exact ⟨y, by rw [← Matrix.mulVecLin_apply]; exact hy⟩
  choose y hy using hex
  choose d hd0 hdL using fun j => sc_scale L hL (y j)
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have ha : ∀ j, algebraMap (𝓞 K) K (d j) ≠ 0 := fun j h =>
    hd0 j (hinj (by rw [h, map_zero]))
  refine ⟨fun j => algebraMap (𝓞 K) K (d j) • y j, fun j => ?_, ?_⟩
  · show algebraMap (𝓞 K) K (d j) • y j ∈ L
    rw [algebraMap_smul]; exact hdL j
  · have := sc_li_scale (e.linearIndependent.map' _ (Submodule.ker_subtype _)) _ ha
    have heq : (fun j => N *ᵥ (algebraMap (𝓞 K) K (d j) • y j)) = fun j =>
        algebraMap (𝓞 K) K (d j) • ((LinearMap.range N.mulVecLin).subtype ∘ e) j := by
      funext j; simp [mulVec_smul, hy]
    rw [heq]; exact this
end ReciprocityTheory.MultiplicativeHeights
