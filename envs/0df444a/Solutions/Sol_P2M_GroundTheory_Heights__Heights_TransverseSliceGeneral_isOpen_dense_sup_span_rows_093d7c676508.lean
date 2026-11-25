-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isOpen_dense_sup_span_rows_093d7c676508
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:45.967801+00:00
-- url     : https://prove2.me/submissions/93b64a67-1267-4545-bd77-c0c4379fb619

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_dense_linearIndependent_2e378db1f721

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
theorem _root_.solution (V : Submodule ℂ (Fin n → ℂ)) (hV : n ≤ Module.finrank ℂ V + d) :
    IsOpen {L : Matrix (Fin d) (Fin n) ℂ | V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} ∧
      Dense {L : Matrix (Fin d) (Fin n) ℂ | V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} := by
  set m := Module.finrank ℂ ((Fin n → ℂ) ⧸ V)
  have hm : m ≤ d := by
    have := Submodule.finrank_quotient_add_finrank V
    simp only [Module.finrank_fin_fun] at this
    omega
  let Ψ : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    (Module.finBasis ℂ ((Fin n → ℂ) ⧸ V)).equivFun.toLinearMap ∘ₗ V.mkQ
  have hΨs : Function.Surjective Ψ :=
    (Module.finBasis ℂ ((Fin n → ℂ) ⧸ V)).equivFun.surjective.comp V.mkQ_surjective
  have hΨk : LinearMap.ker Ψ = V := by
    simp [Ψ, LinearEquiv.ker_comp]
  let Φ : Matrix (Fin d) (Fin n) ℂ →ₗ[ℂ] (Fin m → Fin d → ℂ) :=
    { toFun := fun L k i => Ψ (L i) k
      map_add' := fun L L' => by
        ext k i
        show Ψ (L i + L' i) k = Ψ (L i) k + Ψ (L' i) k
        rw [map_add]
        rfl
      map_smul' := fun c L => by
        ext k i
        show Ψ (c • L i) k = c * Ψ (L i) k
        rw [map_smul]
        rfl }
  have hΦs : Function.Surjective Φ := by
    intro F
    refine ⟨Matrix.of fun i => Function.surjInv hΨs (fun k => F k i), ?_⟩
    ext k i
    show Ψ (Function.surjInv hΨs (fun k => F k i)) k = F k i
    rw [Function.surjInv_eq hΨs]
  have hset : {L : Matrix (Fin d) (Fin n) ℂ | V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} =
      Φ ⁻¹' {f | LinearIndependent ℂ f} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    let N : Matrix (Fin d) (Fin m) ℂ := Matrix.of fun i k => Ψ (L i) k
    have h1 : V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤ ↔
        Submodule.span ℂ (Set.range N.row) = ⊤ := by
      have hc : Submodule.comap Ψ (Submodule.span ℂ (Set.range N.row)) =
          V ⊔ Submodule.span ℂ (Set.range fun i => L i) := by
        have : Submodule.span ℂ (Set.range N.row) =
            (Submodule.span ℂ (Set.range fun i => L i)).map Ψ := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        rw [this, Submodule.comap_map_eq, hΨk, sup_comm]
      rw [← hc]
      constructor
      · intro htop
        rw [← Submodule.map_comap_eq_of_surjective hΨs (Submodule.span ℂ (Set.range N.row)),
          htop, Submodule.map_top, LinearMap.range_eq_top.2 hΨs]
      · intro htop
        rw [htop, Submodule.comap_top]
    have h2 : Submodule.span ℂ (Set.range N.row) = ⊤ ↔ N.rank = m := by
      rw [Matrix.rank_eq_finrank_span_row]
      constructor
      · intro htop
        rw [htop, finrank_top, Module.finrank_fin_fun]
      · intro hr
        exact Submodule.eq_top_of_finrank_eq (by rw [hr, Module.finrank_fin_fun])
    have h3 : LinearIndependent ℂ (Φ L) ↔ N.rank = m := by
      rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, ← Matrix.rank_transpose N,
        Matrix.rank_eq_finrank_span_row, eq_comm]
      rfl
    rw [h1, h2, h3]
  rw [hset]
  exact ⟨isOpen_setOfPred_linearIndependent.preimage (LinearMap.continuous_of_finiteDimensional Φ),
    (dense_linearIndependent hm).preimage (LinearMap.isOpenMap_of_finiteDimensional Φ hΦs)⟩
end GroundTheory.Heights₂.Heights.TransverseSliceGeneral
