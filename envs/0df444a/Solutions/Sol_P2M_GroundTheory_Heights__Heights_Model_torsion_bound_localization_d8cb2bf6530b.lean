-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_torsion_bound_localization_d8cb2bf6530b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:43.806419+00:00
-- url     : https://prove2.me/submissions/6a4f77c3-d61a-4278-91aa-922787802da3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B] {N : ℕ}
    (hN : ∀ (n : ℤ) (a : A), n ≠ 0 → (n : A) * a = 0 → (N : A) * a = 0)
    (n : ℤ) (b : B) (hn : n ≠ 0) (hb : (n : B) * b = 0) : (N : B) * b = 0 := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S b
  have key : ∀ z : ℤ, (z : B) * IsLocalization.mk' B a s = IsLocalization.mk' B ((z : A) * a) s := by
    intro z
    rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_intCast]
  rw [key, IsLocalization.mk'_eq_zero_iff] at hb
  obtain ⟨c, hc⟩ := hb
  have h := hN n ((c : A) * a) hn (by rw [← hc]; ring)
  have key' := key (N : ℤ)
  push_cast at key'
  rw [key', IsLocalization.mk'_eq_zero_iff]
  exact ⟨c, by rw [← h]; ring⟩
end GroundTheory.Heights₂.Heights.Model
