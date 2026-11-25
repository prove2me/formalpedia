-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_intCast_mul_eq_zero_44d637363897
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:25:31.633866+00:00
-- url     : https://prove2.me/submissions/55ead7fb-853f-4851-b096-27f93978484d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_torsion_bound_localization_d8cb2bf6530b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isUnit_intCast_of_le_invOpen_ebaf15bce7bb

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
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ)
    (hcov : ∀ x : X, ∃ (U : X.affineOpens) (N : ℕ), x ∈ (U : X.Opens) ∧ (N : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N : Γ(X, U)) * a = 0)
    {W : X.Opens} (hW : W ≤ invOpen f k) (n : ℤ) (hn : n ≠ 0) (s : Γ(X, W))
    (hs : (n : Γ(X, W)) * s = 0) : s = 0 := by
  refine X.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨U, N, hxU, hNk, hN⟩ := hcov x
  obtain ⟨a, haW, hxa⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ hxU
  refine ⟨X.basicOpen a, haW, hxa, ?_⟩
  have := U.2.isLocalization_basicOpen a
  set t := X.presheaf.map (homOfLE haW).op s with ht_def
  have ht : (n : Γ(X, X.basicOpen a)) * t = 0 := by
    rw [ht_def, ← map_intCast (X.presheaf.map (homOfLE haW).op).hom n, ← map_mul, hs, map_zero]
  have hNt := torsion_bound_localization (Submonoid.powers a) hN n t hn ht
  have hk := isUnit_intCast_of_le_invOpen f k (haW.trans hW)
  have hNu : IsUnit (N : Γ(X, X.basicOpen a)) := by
    obtain ⟨c, hc⟩ := hNk
    have hkc : ((k : ℤ) : Γ(X, X.basicOpen a)) =
        ((N : ℤ) : Γ(X, X.basicOpen a)) * (c : Γ(X, X.basicOpen a)) := by
      rw [hc]; push_cast; ring
    rw [hkc] at hk
    exact_mod_cast isUnit_of_mul_isUnit_left hk
  rw [map_zero]
  exact hNu.mul_right_eq_zero.mp hNt
end GroundTheory.Heights₂.Heights.Model
