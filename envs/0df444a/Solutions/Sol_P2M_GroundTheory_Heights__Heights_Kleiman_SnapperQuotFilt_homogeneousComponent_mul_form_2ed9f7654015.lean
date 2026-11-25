-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_homogeneousComponent_mul_form_2ed9f7654015
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:18:49.242639+00:00
-- url     : https://prove2.me/submissions/edbe58ac-f473-42fe-9c6e-90a42c841f81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm

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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
theorem _root_.solution (c h : Poly S N) {d : ℕ} (hh : h.IsHomogeneous d) (n : ℕ) :
    homogeneousComponent n (c * h) = if d ≤ n then homogeneousComponent (n - d) c * h else 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent c, Finset.sum_mul, map_sum]
  have each : ∀ i, homogeneousComponent n (homogeneousComponent i c * h) =
      if i + d = n then homogeneousComponent i c * h else 0 := fun i => by
    rw [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous i c).mul hh)]
    by_cases hi : i + d = n
    · rw [if_pos hi.symm, if_pos hi]
    · rw [if_neg (Ne.symm hi), if_neg hi]
  simp_rw [each]
  rw [Finset.sum_eq_single (n - d)]
  · by_cases hdn : d ≤ n
    · rw [if_pos (by omega), if_pos hdn]
    · rw [if_neg hdn]
      by_cases h0 : n - d + d = n
      · exfalso; omega
      · rw [if_neg h0]
  · intro i _ hi
    rw [if_neg (by omega)]
  · intro hn
    by_cases h0 : n - d + d = n
    · rw [if_pos h0, homogeneousComponent_eq_zero _ _ (by simp at hn; omega), zero_mul]
    · rw [if_neg h0]
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
