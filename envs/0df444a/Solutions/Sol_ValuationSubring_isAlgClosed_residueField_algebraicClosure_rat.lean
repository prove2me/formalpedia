-- Prove2me | solution 1 for ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/12a8bc7d-b180-5486-8fa1-e8f492b8679c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat

open IsLocalRing Polynomial

theorem solution (A : ValuationSubring (AlgebraicClosure ℚ)) :
    IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun f hfm hfi => ?_

  have hsurj : Function.Surjective (residue A) := Ideal.Quotient.mk_surjective
  obtain ⟨F0, hF0⟩ := Polynomial.map_surjective _ hsurj f
  obtain ⟨F, hFmap, -, hFm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts f).mpr ⟨F0, hF0⟩) hfm

  let G := F.map (algebraMap A (AlgebraicClosure ℚ))
  have hGdeg : G.degree ≠ 0 := by
    have : G.degree = f.degree := by
      rw [show G = F.map _ from rfl, hFm.degree_map, ← hFmap, hFm.degree_map]
    rw [this]; exact (Polynomial.degree_pos_of_irreducible hfi).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root G hGdeg

  have hint : IsIntegral A α := ⟨F, hFm, by rwa [← Polynomial.eval_map]⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint

  refine ⟨residue A a, ?_⟩
  have hFa : F.eval a = 0 := by
    apply IsFractionRing.injective A (AlgebraicClosure ℚ)
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ha]; exact hα
  rw [← hFmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hFa, map_zero]

end S_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
end P2MW
export P2MW.S_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat (solution)
