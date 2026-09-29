-- Prove2me | solution 1 for TaylorWiles.exists_isTaylorWilesPrime_of_statement
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8cca6727-0552-57d0-b9a2-952aba706043

import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_Matrix_hasDistinctRationalEigenvalues_pow
import Theorems.Thm_Matrix_hasDistinctRationalEigenvalues_of_isConj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TaylorWiles_exists_isTaylorWilesPrime_of_statement

open NumberField FrobeniusDensity

theorem solution {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜]
    (ρ : TaylorWiles.ResidualRep L 𝕜) (p n : ℕ) (hstmt : FrobeniusDensity.Statement L)
    {S : Finset ℕ} (seed : TaylorWiles.Seed ρ p n S) (T : Finset ℕ) :
    ∃ q : ℕ, q ∉ S ∧ q ∉ T ∧ TaylorWiles.IsTaylorWilesPrime ρ p n q := by
  obtain ⟨q, hqmem, hreal⟩ := hstmt seed.σ (S ∪ T)
  rw [Finset.mem_union, not_or] at hqmem
  obtain ⟨hqS, hqT⟩ := hqmem
  obtain ⟨hq, hQ⟩ := hreal
  refine ⟨q, hqS, hqT, hq, seed.congruent q hqS ⟨hq, hQ⟩, ?_⟩
  intro Q hQp hQl hQf
  obtain ⟨k, hk, hconj⟩ := hQ Q hQp hQl hQf
  have hpow : (ρ seed.σ) ^ (orderOf seed.σ) = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h1 : ((ρ seed.σ) ^ k).HasDistinctRationalEigenvalues :=
    Matrix.hasDistinctRationalEigenvalues_pow (orderOf_pos seed.σ) hpow seed.regular hk
  have h2 : IsConj ((ρ seed.σ) ^ k) (ρ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) := by
    have h3 := ρ.map_isConj hconj
    rwa [map_pow] at h3
  exact Matrix.hasDistinctRationalEigenvalues_of_isConj h2 h1

end S_TaylorWiles_exists_isTaylorWilesPrime_of_statement
end P2MW
export P2MW.S_TaylorWiles_exists_isTaylorWilesPrime_of_statement (solution)
