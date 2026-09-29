-- Prove2me | solution 1 for ResidualGaloisRep.forall_indexTwo_stable_eq_bot_or_top_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bba5a0d1-ad02-552e-8b89-5dea238854c8

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_forall_indexTwo_stable_eq_bot_or_top_baseChangeAlong

set_option autoImplicit false

open scoped TensorProduct

namespace IDX2BCProof

theorem aux
    {k k' : Type} [Field k] [Field k'] [Algebra k k'] (ρ : ResidualGaloisRep k)
    (h : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρ.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρ.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (K' : Type) [Field K'] [Algebra k' K'] [Algebra k K'] [IsScalarTower k k' K']
    (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hG : G.index = 2)
    (V : Submodule K' ((ρ.baseChange k').baseChange K').V)
    (hV : ∀ σ ∈ G, ∀ x ∈ V, ((ρ.baseChange k').baseChange K').ρ σ x ∈ V) :
    V = ⊥ ∨ V = ⊤ := by
  classical
  let e : ((ρ.baseChange k').baseChange K').V ≃ₗ[K'] (ρ.baseChange K').V :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange k k' K' K' ρ.V
  have he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ((ρ.baseChange k').baseChange K').V),
      e (((ρ.baseChange k').baseChange K').ρ σ x) = (ρ.baseChange K').ρ σ (e x) := by
    intro σ x
    change TensorProduct.AlgebraTensorModule.cancelBaseChange k k' K' K' ρ.V
        (LinearMap.baseChange K' (LinearMap.baseChange k' (ρ.ρ σ)) x) =
      LinearMap.baseChange K' (ρ.ρ σ) (TensorProduct.AlgebraTensorModule.cancelBaseChange k k' K' K' ρ.V x)
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | tmul b v =>
        simp only [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  have hV' : ∀ σ ∈ G, ∀ x ∈ V.map (e : _ →ₗ[K'] _), (ρ.baseChange K').ρ σ x ∈ V.map (e : _ →ₗ[K'] _) := by
    rintro σ hσ _ ⟨y, hy, rfl⟩
    exact ⟨_, hV σ hσ y hy, he σ y⟩
  rcases h K' G hG (V.map (e : _ →ₗ[K'] _)) hV' with h0 | h1
  · left
    apply (Submodule.orderIsoMapComap e).injective
    rw [map_bot]
    exact h0
  · right
    apply (Submodule.orderIsoMapComap e).injective
    rw [map_top]
    exact h1

end IDX2BCProof

theorem solution
    {k k' : Type} [Field k] [Field k'] (ι : k →+* k') (ρ : ResidualGaloisRep k)
    (h : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρ.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρ.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (K' : Type) [Field K'] [Algebra k' K']
    (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hG : G.index = 2)
    (V : Submodule K' ((ρ.baseChangeAlong ι).baseChange K').V)
    (hV : ∀ σ ∈ G, ∀ x ∈ V, ((ρ.baseChangeAlong ι).baseChange K').ρ σ x ∈ V) :
    V = ⊥ ∨ V = ⊤ :=
  letI : Algebra k k' := ι.toAlgebra
  letI : Algebra k K' := ((algebraMap k' K').comp ι).toAlgebra
  haveI : IsScalarTower k k' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  IDX2BCProof.aux ρ h K' G hG V hV

end S_ResidualGaloisRep_forall_indexTwo_stable_eq_bot_or_top_baseChangeAlong
end P2MW
export P2MW.S_ResidualGaloisRep_forall_indexTwo_stable_eq_bot_or_top_baseChangeAlong (solution)
