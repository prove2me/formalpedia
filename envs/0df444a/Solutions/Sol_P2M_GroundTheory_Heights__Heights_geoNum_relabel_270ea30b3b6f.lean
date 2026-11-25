-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_geoNum_relabel_270ea30b3b6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:11.671781+00:00
-- url     : https://prove2.me/submissions/643db2df-8689-4956-b269-d8d9ace7246a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_ringEquiv_injective_a552ea8108be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_int_quotient_map_5647412ff0d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRelevant_map_relabel_iff_831acc433198
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_divSupp_map_relabel_c0ea796b5361
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_multAt_map_relabel_58c8783fc9c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabel_X_choose_90b307a92fed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (n : ℕ) : ∀ (V : Ideal (MRing ι)) (a : Fin n → K' → ℤ),
    geoNum n V (fun j => a j ∘ ε) = geoNum n (V.map (relabelRingEquiv ε h)) a := by
  induction n with
  | zero =>
    intro V a
    by_cases hV : IsRelevant V
    · have hV' := (isRelevant_map_relabel_iff ε h V).2 hV
      simp only [geoNum, dif_pos hV, dif_pos hV']
      have hrange : (Set.range fun k' => (X ⟨k', (hV' k').choose⟩ : MRing ι') - 1) =
          relabelRingEquiv ε h '' Set.range fun k => (X ⟨k, (hV k).choose⟩ : MRing ι) - 1 := by
        ext x
        simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
        constructor
        · rintro ⟨k', rfl⟩
          obtain ⟨k, rfl⟩ := ε.surjective k'
          exact ⟨k, by rw [map_sub, map_one, relabel_X_choose ε h V hV hV' k]⟩
        · rintro ⟨k, rfl⟩
          exact ⟨ε k, by rw [map_sub, map_one, relabel_X_choose ε h V hV hV' k]⟩
      rw [hrange, ← Ideal.map_span, ← Ideal.map_sup, length_int_quotient_map]
    · have hV' : ¬ IsRelevant (V.map (relabelRingEquiv ε h)) :=
        fun h' => hV ((isRelevant_map_relabel_iff ε h V).1 h')
      simp only [geoNum, dif_neg hV, dif_neg hV']
  | succ n ih =>
    intro V a
    by_cases hV : IsRelevant V
    · have hV' := (isRelevant_map_relabel_iff ε h V).2 hV
      simp only [geoNum, dif_pos hV, dif_pos hV']
      refine Fintype.sum_equiv ε _ _ fun k => ?_
      rw [← relabel_X_choose ε h V hV hV' k, divSupp_map_relabel,
        finsum_mem_image ((map_ringEquiv_injective (relabelRingEquiv ε h)).injOn)]
      have hsup : V.map (relabelRingEquiv ε h) ⊔
          Ideal.span {relabelRingEquiv ε h (X ⟨k, (hV k).choose⟩)} =
          (V ⊔ Ideal.span {(X ⟨k, (hV k).choose⟩ : MRing ι)}).map (relabelRingEquiv ε h) := by
        rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
      rw [hsup]
      congr 1
      refine finsum_mem_congr rfl fun W _ => ?_
      rw [multAt_map_relabel, ← ih W (Fin.init a)]
      rfl
    · have hV' : ¬ IsRelevant (V.map (relabelRingEquiv ε h)) :=
        fun h' => hV ((isRelevant_map_relabel_iff ε h V).1 h')
      simp only [geoNum, dif_neg hV, dif_neg hV']
end GroundTheory.Heights₂.Heights
