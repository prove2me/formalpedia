-- Prove2me | solution 1 for WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4a81e65f-993d-51c3-bada-e66224d375fc

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare
import Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero

set_option maxHeartbeats 6400000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [Fact n.Prime] :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    let W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by
  by_cases hsq : IsSquare c
  · obtain ⟨d, hd⟩ := hsq
    exact WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare
      K c hc n d hd.symm
  · exact WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare
      K c hc n hsq

end S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero
end P2MW
export P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero (solution)
