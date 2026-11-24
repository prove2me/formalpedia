-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComplexMinimalPrimesContract_proof_3ede0676b13c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:56.93824+00:00
-- url     : https://prove2.me/submissions/473b8e29-2f9f-4380-b98b-56751470da75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexMinimalPrimesContract
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComplexMinimalPrimesContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_mvPolynomial_int_complex_flat_9507931c25a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_algebraMap_mvPolynomial_int_complex_a208a4dfdd5b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace ComplexMinimalPrimesContract
theorem _root_.solution : ComplexMinimalPrimesContract.Statement := by
  intro σ _ P hP Q hQ
  have := hP
  have hflat := mvPolynomial_int_complex_flat σ
  have hAlg := algebraMap_mvPolynomial_int_complex σ
  have : Q.IsPrime := hQ.1.1
  have hPQ : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q := hQ.1.2
  have hle : P ≤ Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
    Ideal.map_le_iff_le_comap.mp hPQ
  have : (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have : Q.LiesOver (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) :=
    ⟨by rw [Ideal.under, Ideal.comap, hAlg]; rfl⟩
  obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (R := MvPolynomial σ ℤ) (p := P)
      (q := Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) Q hle
  have hQ'P : Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
    have := hQ'over.over
    rw [Ideal.under, hAlg] at this
    exact this.symm
  have hmapQ' : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q' :=
    Ideal.map_le_iff_le_comap.mpr hQ'P.ge
  have hQQ' : Q ≤ Q' := hQ.2 ⟨hQ'prime, hmapQ'⟩ hQ'Q
  rw [← le_antisymm hQ'Q hQQ']
  exact hQ'P
end ComplexMinimalPrimesContract
end GroundTheory.Heights₂.Heights.HilbertSamuel
