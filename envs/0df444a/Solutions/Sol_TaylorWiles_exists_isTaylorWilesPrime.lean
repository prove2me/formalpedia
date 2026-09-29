-- Prove2me | solution 1 for TaylorWiles.exists_isTaylorWilesPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/817ec6a8-2e8f-5c86-8b1c-b4a1dbb74f58

import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_TaylorWiles_exists_isTaylorWilesPrime_of_statement
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TaylorWiles_exists_isTaylorWilesPrime
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow"

open NumberField FrobeniusDensity

theorem solution {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜]
    (ρ : TaylorWiles.ResidualRep L 𝕜) (p n : ℕ)
    {S : Finset ℕ} (seed : TaylorWiles.Seed ρ p n S) (T : Finset ℕ) :
    ∃ q : ℕ, q ∉ S ∧ q ∉ T ∧ TaylorWiles.IsTaylorWilesPrime ρ p n q :=
  TaylorWiles.exists_isTaylorWilesPrime_of_statement ρ p n (FrobeniusDensity.statement L) seed T

end S_TaylorWiles_exists_isTaylorWilesPrime
end P2MW
export P2MW.S_TaylorWiles_exists_isTaylorWilesPrime (solution)
