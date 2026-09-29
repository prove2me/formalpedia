-- Prove2me | solution 1 for ValuationSubring.nonempty_residueField_algEquiv_algebraicClosure_galoisField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/cbe3ae4c-a8d3-5e50-bd3d-b12523f5706d

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_nonempty_residueField_algEquiv_algebraicClosure_galoisField

set_option autoImplicit false

open IsLocalRing

private theorem isTorsionFree_of_field (K M : Type*) [Field K] [Field M] [Algebra K M] :
    Module.IsTorsionFree K M := by
  refine Module.IsTorsionFree.of_smul_eq_zero (fun r m h => ?_)
  rw [Algebra.smul_def] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact Or.inl ((map_eq_zero_iff _ (algebraMap K M).injective).mp h')
  · exact Or.inr h'

theorem solution (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField P) := ι.toAlgebra
    Nonempty (IsLocalRing.ResidueField P ≃ₐ[GaloisField q 2] AlgebraicClosure (GaloisField q 2)) := by
  letI iGF : Algebra (GaloisField q 2) (ResidueField P) := ι.toAlgebra
  letI iZ : Algebra (ZMod q) (ResidueField P) :=
    ((algebraMap (GaloisField q 2) (ResidueField P)).comp (algebraMap (ZMod q) (GaloisField q 2))).toAlgebra
  haveI : IsScalarTower (ZMod q) (GaloisField q 2) (ResidueField P) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := isTorsionFree_of_field (ZMod q) (ResidueField P)
  haveI := isTorsionFree_of_field (GaloisField q 2) (ResidueField P)
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI hZ : IsAlgClosure (ZMod q) (ResidueField P) := ValuationSubring.isAlgClosure_residueField P
  haveI : Algebra.IsAlgebraic (ZMod q) (ResidueField P) := hZ.isAlgebraic
  haveI : IsAlgClosure (GaloisField q 2) (ResidueField P) :=
    ⟨hZ.isAlgClosed, Algebra.IsAlgebraic.tower_top (K := ZMod q) (GaloisField q 2)⟩
  exact ⟨IsAlgClosure.equiv (GaloisField q 2) (ResidueField P) (AlgebraicClosure (GaloisField q 2))⟩

end S_ValuationSubring_nonempty_residueField_algEquiv_algebraicClosure_galoisField
end P2MW
export P2MW.S_ValuationSubring_nonempty_residueField_algEquiv_algebraicClosure_galoisField (solution)
