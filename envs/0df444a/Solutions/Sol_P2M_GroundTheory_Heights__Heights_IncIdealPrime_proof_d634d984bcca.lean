-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncIdealPrime_proof_d634d984bcca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:13.026597+00:00
-- url     : https://prove2.me/submissions/b13d5528-ccda-4e65-8272-6f5fe7ced62c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncIdealPrime

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
namespace IncIdealPrime
theorem _root_.solution (h₁ : IncidenceGeneric.Statement) : IncIdealPrime.Statement := by
  intro F _ n k P hP hrel
  have := hP
  obtain ⟨j, hj⟩ := hrel
  have hξ : genPt P j ≠ 0 := by
    unfold genPt
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  set c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P) := Pi.single j (genPt P j)⁻¹ with hc
  have hsum : ∑ l, c l * genPt P l = 1 := by
    rw [Finset.sum_eq_single j]
    · simp [hc, inv_mul_cancel₀ hξ]
    · intro b _ hb
      simp [hc, Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hker : incIdeal P k =
      RingHom.ker (aeval (genSubst (k := k) (genPt P) c) :
        MvPolynomial (Fin k × Fin n) F →ₐ[F]
          MvPolynomial (Fin k × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ P))) := by
    ext g
    rw [RingHom.mem_ker]
    exact h₁ F n k P c hsum g
  rw [hker]
  exact RingHom.ker_isPrime _
end IncIdealPrime
end GroundTheory.Heights₂.Heights
