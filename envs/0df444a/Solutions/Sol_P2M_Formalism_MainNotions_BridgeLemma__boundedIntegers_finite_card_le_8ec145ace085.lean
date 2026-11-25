-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__boundedIntegers_finite_card_le_8ec145ace085
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:14:37.216843+00:00
-- url     : https://prove2.me/submissions/812c4b23-c102-4026-9c1f-3e9f3b998fe9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__prod_norm_embeddings_eq_abs_norm_alt_a07d0a0fed57
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__one_le_abs_norm_of_ne_zero_alt_c6845006cab4
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LatticeSumBounds_boxCountO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory Module
variable (K : Type) [Field K] [NumberField K]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (B : ℝ) (hB : 0 < B) :
    (boundedIntegers K B).Finite ∧ ((boundedIntegers K B).ncard : ℝ) ≤ (1 + 2 * B) ^ (2 * finrank ℚ K) := by
  classical
  let emb : 𝓞 K →+ ((K →+* ℂ) → ℂ) :=
    { toFun := fun a φ => φ (a : K)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hinj : Function.Injective emb := by
    intro a b hab
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h1 : φ (a : K) = φ (b : K) := congrFun hab φ
    exact RingOfIntegers.ext (φ.injective h1)
  have hmin : ∀ x ∈ emb.range, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖ := by
    rintro x ⟨a, rfl⟩ hx
    have ha : a ≠ 0 := by rintro rfl; exact hx (map_zero _)
    show 1 ≤ ∏ v : K →+* ℂ, ‖v (a : K)‖
    rw [prod_norm_embeddings_eq_abs_norm_alt]; exact one_le_abs_norm_of_ne_zero_alt K a ha
  obtain ⟨hfin, hcard, -⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.boxCountO (K →+* ℂ) emb.range (fun _ => B) (fun _ => hB) hmin
  have himg : emb '' (boundedIntegers K B) = {x | x ∈ emb.range ∧ ∀ v, ‖x v‖ ≤ B} := by
    ext x; constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, rfl⟩, ha⟩
    · rintro ⟨⟨a, rfl⟩, ha⟩; exact ⟨a, ha, rfl⟩
  have hf : (boundedIntegers K B).Finite := Set.Finite.of_finite_image (himg ▸ hfin) hinj.injOn
  refine ⟨hf, ?_⟩
  rw [← Set.ncard_image_of_injective _ hinj, himg]
  refine hcard.trans (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card, ← pow_mul]
end Formalism.MainNotions.BridgeLemma₂
