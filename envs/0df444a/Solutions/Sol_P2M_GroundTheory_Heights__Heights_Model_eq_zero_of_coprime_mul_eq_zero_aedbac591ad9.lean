-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_coprime_mul_eq_zero_aedbac591ad9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:25:30.063447+00:00
-- url     : https://prove2.me/submissions/2e3d49a9-87cf-4dd2-b080-b97f2e858085

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLocSectionsInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_mul_of_coprime_16bf724ac7de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isUnit_intCast_of_le_invOpen_ebaf15bce7bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_torsion_bound_localization_d8cb2bf6530b


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
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : ℕ) (hp : p.Prime) (k : ℤ)
    (hcov : ∀ x : X, ∃ (U : X.affineOpens) (N : ℕ), x ∈ (U : X.Opens) ∧ ((ordCompl[p] N : ℕ) : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N : Γ(X, U)) * a = 0)
    {W : X.Opens} (hW : W ≤ invOpen f k) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (s : Γ(X, W))
    (hs : (u : Γ(X, W)) * s = 0) : s = 0 := by
  refine X.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨U, N, hxU, hNk, hN⟩ := hcov x
  obtain ⟨a, haW, hxa⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ hxU
  refine ⟨X.basicOpen a, haW, hxa, ?_⟩
  have := U.2.isLocalization_basicOpen a
  set t := X.presheaf.map (homOfLE haW).op s with ht_def
  have ht : (u : Γ(X, X.basicOpen a)) * t = 0 := by
    rw [ht_def, ← map_intCast (X.presheaf.map (homOfLE haW).op).hom u, ← map_mul, hs, map_zero]
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  have hNt := torsion_bound_localization (Submonoid.powers a) hN u t hu0 ht
  have hk := isUnit_intCast_of_le_invOpen f k (haW.trans hW)
  obtain ⟨c, hc⟩ := hNk
  rw [hc, Int.cast_mul, Int.cast_natCast] at hk
  rw [map_zero]
  refine eq_zero_of_mul_of_coprime p hp (N.factorization p) (ordCompl[p] N) u hu
    (isUnit_of_mul_isUnit_left hk) t ?_ ht
  rwa [Nat.ordProj_mul_ordCompl_eq_self]
end GroundTheory.Heights₂.Heights.Model
