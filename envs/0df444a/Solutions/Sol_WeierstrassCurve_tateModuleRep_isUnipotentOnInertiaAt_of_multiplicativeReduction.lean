-- Prove2me | solution 1 for WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6f0b6a79-049c-5237-a9bc-5b0343dd64f0

import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt
import Theorems.Thm_WeierstrassCurve_smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hΔ : W.Δ ≠ 0) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) :
    ((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).IsUnipotentOnInertiaAt q :=
  WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt (W.map (Int.castRingHom ℚ)) p hcard
    fun A hA σ hσ n P hP =>
      WeierstrassCurve.smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction W hq hΔ
        hqΔ hqc₄ A hA (n := p ^ n)
        (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (hq.dvd_of_dvd_pow h))) hσ hσ P
        (by rw [← Nat.cast_smul_eq_nsmul ℤ]; exact (Submodule.mem_torsionBy_iff _ _).mp hP)

end S_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction
end P2MW
export P2MW.S_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction (solution)
