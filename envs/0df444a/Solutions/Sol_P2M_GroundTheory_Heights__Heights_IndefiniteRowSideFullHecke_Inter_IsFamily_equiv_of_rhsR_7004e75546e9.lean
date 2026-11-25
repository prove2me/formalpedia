-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IsFamily_equiv_of_rhsR_7004e75546e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:18:00.074386+00:00
-- url     : https://prove2.me/submissions/a4595ba2-b857-4ccb-b717-0fd8423c0b3b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothHerm_tensor_0e83f230e265
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_update_6724d9a7040a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_snoc_70b1a9fae82c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_cc429de364eb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace IsFamily
theorem _root_.solution (I : Family ι)
    (hR : ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι),
      rhsR I P L A s = recR I P L A s) :
    IsFamily I ↔ IsIntersectionFamily I := by
  constructor
  · rintro ⟨hsym, hadd, hrec⟩
    refine ⟨fun P n L σ hP hL => hsym P n L σ trivial hP hL, ?_, ?_⟩
    · intro P n L A B hP hL hA hB
      have hLA : AllSmooth (Fin.snoc L A : Fin (n + 1) → HermLine ι) := allSmooth_snoc hL hA
      have h := hadd P (n + 1) (Fin.snoc L A) (Fin.last n) A B trivial hP hLA hA hB
      simpa only [Fin.update_snoc_last] using h
    · intro P n L A s a hP hL hA ha hs hsP
      have h := hrec P n (Fin.snoc L A) s trivial hP (allSmooth_snoc hL hA)
        (by simpa only [Fin.snoc_last] using (isSec_iff P A s).2 ⟨a, ha, hs, hsP⟩)
      rw [h, Fin.init_snoc, Fin.snoc_last, hR]
  · rintro ⟨hsym, hadd, hrec⟩
    refine ⟨fun P n L σ _ hP hL => hsym P n L σ hP hL, ?_, ?_⟩
    · intro P n L j A B _ hP hL hA hB
      cases n with
      | zero => exact j.elim0
      | succ m =>
        set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m) with hσ
        have key : ∀ X : HermLine ι, IsSmoothHerm X →
            I P (m + 1) (Function.update L j X) = I P (m + 1) (Fin.snoc (Fin.init (L ∘ σ)) X) := by
          intro X hX
          have e : Function.update L j X ∘ σ = Fin.snoc (Fin.init (L ∘ σ)) X := by
            rw [Function.update_comp_equiv, hσ, Equiv.symm_swap, Equiv.swap_apply_left]
            conv_lhs => rw [← Fin.snoc_init_self (L ∘ ⇑(Equiv.swap j (Fin.last m)))]
            exact Fin.update_snoc_last _ _ _
          rw [← e, hsym P (m + 1) _ σ hP (allSmooth_update hL j hX)]
        have hL' : ∀ i, IsSmoothHerm (Fin.init (L ∘ σ) i) := fun i => hL _
        rw [key _ (isSmoothHerm_tensor hA hB), key A hA, key B hB]
        exact hadd P m _ A B hP hL' hA hB
    · intro P n L s _ hP hL hs
      obtain ⟨a, ha, hsm, hsP⟩ := (isSec_iff P _ s).1 hs
      have h := hrec P n (Fin.init L) (L (Fin.last n)) s a hP (fun i => hL _) (hL _) ha hsm hsP
      rw [Fin.snoc_init_self] at h
      rw [h, hR]
end IsFamily
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
