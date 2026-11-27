-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ReadsMul_proof_58b9d991dba4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:41.604352+00:00
-- url     : https://prove2.me/submissions/13cb8088-40c9-467a-8d1c-4156d9575506

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PReadsMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReadsMul_mem_mCoordIdeal_a1b8fcafa902
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ReadsMul
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ReadsMul
theorem _root_.solution : ReadsMul.Statement := by
  intro ι _ _ n Ω _ y P a b s s' t t' hP ⟨f, q, δf, δq, hf, hq, hfq, hqP, ht⟩ _ hR hR'
  subst ht
  have hqy : aeval y q ≠ 0 := fun h0 ↦ hqP (hP ▸ mem_mCoordIdeal y hq h0)
  have hqF : P.mkF q ≠ 0 := fun h0 ↦ hqP ((P.mkF_eq_zero_iff q).mp h0)
  have hfy : aeval y f = s * aeval y q :=
    (hR f q δf δq hf hq (fun k ↦ by have := hfq k; omega)).mpr (div_mul_cancel₀ _ hqF).symm
  intro g h δg δh hg hh hd
  have key := hR' (g * q) (f * h) (δg + δq) (δf + δh) (hg.mul hq) (hf.mul hh) (fun k ↦ by
    have h1 := hfq k
    have h2 := hd k
    simp only [Pi.add_apply, Nat.cast_add] at h1 h2 ⊢
    omega)
  rw [map_mul, map_mul, map_mul, map_mul] at key
  have e1 : (aeval y g = s * s' * aeval y h) ↔
      (aeval y g * aeval y q = s' * (aeval y f * aeval y h)) := by
    rw [← mul_left_inj' hqy, hfy, show s * s' * aeval y h * aeval y q =
      s' * (s * aeval y q * aeval y h) by ring]
  have e2 : (P.mkF g = P.mkF f / P.mkF q * t' * P.mkF h) ↔
      (P.mkF g * P.mkF q = t' * (P.mkF f * P.mkF h)) := by
    rw [← mul_left_inj' hqF, show P.mkF f / P.mkF q * t' * P.mkF h * P.mkF q =
      t' * (P.mkF f * P.mkF h) by field_simp]
  exact e1.trans (key.trans e2.symm)
end GroundTheory.Heights₂.Heights.ReadsMul
