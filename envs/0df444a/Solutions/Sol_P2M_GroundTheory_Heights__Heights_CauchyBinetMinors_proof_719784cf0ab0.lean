-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetMinors_proof_719784cf0ab0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:52:46.695288+00:00
-- url     : https://prove2.me/submissions/b38b1987-10c2-4b12-a532-bb3f50e83a45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_det_one_add_eq_sum_64ef61237c7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_minor_reindex_26cf196fa7b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_finset_by_card_9f3e46f68106
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_strictMono_aeabc6a5e861
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_principal_minor_43c2d72f49f6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Finset
open CauchyBinetMinorsAlt
namespace GroundTheory.Heights₂.Heights
namespace CauchyBinetMinors
theorem _root_.solution : CauchyBinetMinors.Statement := by
  intro p q M
  let G : (k : ℕ) → {T : Finset (Fin p) // T.card = k} → {S : Finset (Fin q) // S.card = k} → ℂ :=
    fun k T S => ((‖(M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det‖ ^ 2 : ℝ) : ℂ)
  have hL : (1 + Mᴴ * M).det = ∑ k ∈ range (p + q + 1), ∑ T, ∑ S, G k T S := by
    rw [det_one_add_eq_sum, sum_finset_by_card]
    have hk : ∀ k, ∑ S : {S : Finset (Fin q) // S.card = k},
        ((Mᴴ * M).submatrix ((↑) : S.1 → Fin q) ((↑) : S.1 → Fin q)).det = ∑ T, ∑ S, G k T S := by
      intro k
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [minor_reindex _ S.1 S.2, principal_minor]
    simp only [hk]
    have hsub : range (q + 1) ⊆ range (p + q + 1) := range_subset_range.2 (by omega)
    exact Finset.sum_subset hsub (f := fun k => ∑ T, ∑ S, G k T S) (fun k _ hk => by
      have : IsEmpty {S : Finset (Fin q) // S.card = k} := ⟨fun S => by
        have := card_le_univ S.1
        rw [Fintype.card_fin, S.2] at this
        simp only [mem_range] at hk
        omega⟩
      exact Finset.sum_eq_zero fun T _ => Fintype.sum_empty _)
  have hR : ((∑ k ∈ range (p + 1),
        ∑ a ∈ univ.filter (fun a : Fin k → Fin p => StrictMono a),
          ∑ b ∈ univ.filter (fun b : Fin k → Fin q => StrictMono b),
            ‖(M.submatrix a b).det‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ range (p + q + 1), ∑ T, ∑ S, G k T S := by
    simp only [Complex.ofReal_sum]
    have hk : ∀ k, (∑ a ∈ univ.filter (fun a : Fin k → Fin p => StrictMono a),
          ∑ b ∈ univ.filter (fun b : Fin k → Fin q => StrictMono b),
            ((‖(M.submatrix a b).det‖ ^ 2 : ℝ) : ℂ)) = ∑ T, ∑ S, G k T S := by
      intro k
      rw [sum_strictMono]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [sum_strictMono]
    simp only [hk]
    have hsub : range (p + 1) ⊆ range (p + q + 1) := range_subset_range.2 (by omega)
    exact Finset.sum_subset hsub (f := fun k => ∑ T, ∑ S, G k T S) (fun k _ hk => by
      have : IsEmpty {T : Finset (Fin p) // T.card = k} := ⟨fun T => by
        have := card_le_univ T.1
        rw [Fintype.card_fin, T.2] at this
        simp only [mem_range] at hk
        omega⟩
      exact Fintype.sum_empty _)
  rw [hL, hR]
end CauchyBinetMinors
end GroundTheory.Heights₂.Heights
