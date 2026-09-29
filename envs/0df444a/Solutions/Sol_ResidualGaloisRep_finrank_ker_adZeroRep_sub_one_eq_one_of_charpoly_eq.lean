-- Prove2me | solution 1 for ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e0fa0750-5ef0-5bc8-8c10-ec111a2404c4

import Mathlib
import Definitions.Def_GaloisRep_AdZeroMatrixGlue
import Definitions.Def_Deformations_TaylorWilesLocal
import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq
import Theorems.Thm_TaylorWiles_finrank_inf_traceZero_of_hasDistinctRationalEigenvalues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq

open Module TaylorWiles

theorem solution
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {α β : k} (hαβ : α ≠ β)
    (hchar : LinearMap.charpoly (ρbar.ρ σ) = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) :
    Module.finrank k (LinearMap.ker (ρbar.adZeroRep σ - 1)) = 1 := by
  classical
  let b : Module.Basis (Fin 2) k ρbar.V := Module.finBasisOfFinrankEq k ρbar.V ρbar.finrank_eq
  set A : Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrix b b (ρbar.ρ σ) with hA
  have hpoly : (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)
      = Polynomial.X ^ 2 - Polynomial.C (α + β) * Polynomial.X + Polynomial.C (α * β) := by
    simp only [map_add, map_mul]; ring
  have hcharA : A.charpoly = Polynomial.X ^ 2 - Polynomial.C (α + β) * Polynomial.X + Polynomial.C (α * β) := by
    rw [hA, LinearMap.charpoly_toMatrix, hchar, hpoly]
  have hdist : A.HasDistinctRationalEigenvalues := by
    refine ⟨α, β, hαβ, ?_, ?_⟩
    · rw [Matrix.trace_eq_neg_charpoly_coeff, hcharA]
      simp
    · rw [Matrix.det_eq_sign_charpoly_coeff, hcharA]
      simp
  rw [ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq ρbar b σ]
  have hcomap : Module.finrank k ((LinearMap.ker (TaylorWiles.adAction A)).comap (TaylorWiles.traceZero k).subtype)
      = Module.finrank k (LinearMap.ker (TaylorWiles.adAction A) ⊓ TaylorWiles.traceZero k :
          Submodule k (Matrix (Fin 2) (Fin 2) k)) := by
    rw [← Submodule.finrank_map_subtype_eq (TaylorWiles.traceZero k)
      ((LinearMap.ker (TaylorWiles.adAction A)).comap (TaylorWiles.traceZero k).subtype),
      Submodule.map_comap_subtype, inf_comm]
  rw [hcomap]
  exact TaylorWiles.finrank_inf_traceZero_of_hasDistinctRationalEigenvalues h2 hdist

end S_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq
end P2MW
export P2MW.S_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq (solution)
