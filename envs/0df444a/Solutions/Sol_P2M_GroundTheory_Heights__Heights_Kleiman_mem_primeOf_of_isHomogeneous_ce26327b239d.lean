-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:44.646091+00:00
-- url     : https://prove2.me/submissions/553ef59e-e965-47e8-8257-6dc1014a8431

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cone_of_isHomogeneous_046c5887f5b7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω]
variable {N : ℕ} (x : Fin (N + 1) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {f : Poly S N} {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ primeOf x ↔ aeval x f = 0 := by
  rw [primeOf_eq, RingHom.mem_ker, cone_of_isHomogeneous x hf]
  constructor
  · intro h
    have := congrArg (fun p => Polynomial.coeff p d) h
    simpa only [Polynomial.coeff_C_mul_X_pow, if_true, Polynomial.coeff_zero] using this
  · intro h; rw [h, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.Kleiman
