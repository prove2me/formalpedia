-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_coeff_psi_mul_single_32b62343d37b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:22:04.655916+00:00
-- url     : https://prove2.me/submissions/248d7c93-87a0-4ccb-b94b-b8171120309f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_of_isHomogeneous_43e37c81185f


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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
variable (M0 : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution (c : Sy S r) (b' b : ℕ) (s' : Ω) :
    (psi η S c * single ((0 : ℤ), (b' : ℤ)) s').coeff ((0 : ℤ), (b : ℤ)) =
      ∑ d ∈ Finset.range (c.totalDegree + 1),
        if d + b' = b then aeval η (homogeneousComponent d c) * s' else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent c]
  rw [map_sum, Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [psi_of_isHomogeneous η S (homogeneousComponent_isHomogeneous d c), single_mul_single, coeff_single,
    Finsupp.single_apply]
  by_cases hdb : d + b' = b
  · rw [if_pos hdb, if_pos (by ext <;> simp; omega)]
  · rw [if_neg hdb, if_neg (by intro h; apply hdb; have := congrArg Prod.snd h; simp at this; omega)]
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
