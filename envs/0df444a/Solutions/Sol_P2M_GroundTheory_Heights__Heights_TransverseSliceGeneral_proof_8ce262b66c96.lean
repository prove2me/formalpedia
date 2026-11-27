-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_proof_8ce262b66c96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:10:54.313413+00:00
-- url     : https://prove2.me/submissions/148019b9-a57c-48e2-891d-407ba96cefa1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_apply_45cf6933810d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isTransverseSliceAt_iff_4bf6e33116db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isOpen_dense_sup_span_rows_093d7c676508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_jacobian_minor_not_mem_charZero_0ff55ba28423


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
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TransverseSliceGeneral
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.TransverseSliceGeneral
theorem _root_.solution : TransverseSliceGeneral.Statement := by
  intro n d W hW hdim
  have := hW
  obtain ⟨t, G, hG⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian W)
  obtain ⟨a, b, hab⟩ := IndefiniteRowSideFullHecke.Inter.exists_jacobian_minor_not_mem_charZero W G hG d hdim
  refine ⟨_, hab, fun q hq hfq => ?_⟩
  have hV : n ≤ Module.finrank ℂ (gradSpace W q) + d := by
    let w : Fin (Fintype.card (Fin n) - d) → Fin n → ℂ := fun i => gradAt q (G (a i))
    have hw : LinearIndependent ℂ w := by
      refine LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ b) ?_
      have hdet : IsUnit (Matrix.of fun i j => eval q (pderiv (b j) (G (a i)))) := by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        rw [RingHom.map_det] at hfq
        exact hfq
      have hfun : (⇑(LinearMap.funLeft ℂ ℂ b) ∘ w) =
          fun i => (Matrix.of fun i j => eval q (pderiv (b j) (G (a i)))) i := by
        ext i j
        simp [w, gradAt_apply, LinearMap.funLeft_apply]
      rw [hfun]
      exact Matrix.linearIndependent_rows_iff_isUnit.2 hdet
    have hle : Submodule.span ℂ (Set.range w) ≤ gradSpace W q := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨G (a i), hG ▸ Ideal.subset_span ⟨a i, rfl⟩, rfl⟩
    have := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hw, Fintype.card_fin, Fintype.card_fin] at this
    omega
  have hset : {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q} =
      {L | gradSpace W q ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} :=
    Set.ext fun L => isTransverseSliceAt_iff W L q hq
  rw [hset]
  exact isOpen_dense_sup_span_rows _ hV
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
