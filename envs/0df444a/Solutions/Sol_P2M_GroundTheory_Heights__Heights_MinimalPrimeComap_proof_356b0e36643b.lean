-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimeComap_proof_356b0e36643b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:04:37.969802+00:00
-- url     : https://prove2.me/submissions/24185473-9f8f-4b21-a62c-c0aca44e4e22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMinimalPrimeComap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimeComap_flat_d8b37256755b

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace MinimalPrimeComap
theorem _root_.solution : MinimalPrimeComap.Statement := by
  intro K L _ _ σ ι I hI P hP
  let := σ.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have := MinimalPrimeComap.flat K L σ ι
  have halg : algebraMap (MvPolynomial ι K) (MvPolynomial ι L) = MvPolynomial.map σ := rfl
  have : P.IsPrime := hP.1.1
  have hle : I ≤ P.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hP.1.2
  by_contra hne
  have hlt : I < P.under (MvPolynomial ι K) := lt_of_le_of_ne hle (fun h => hne h.symm)
  have : (P.under (MvPolynomial ι K)).IsPrime := Ideal.IsPrime.under _ _
  have : P.LiesOver (P.under (MvPolynomial ι K)) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQI⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := I) P hlt
  have hIQ : I.map (MvPolynomial.map σ) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, ← halg, ← Ideal.under_def, ← hQI.over]
  exact (not_le_of_gt hQP) (hP.2 ⟨hQ, hIQ⟩ hQP.le)
end MinimalPrimeComap
end GroundTheory.Heights₂.Heights
