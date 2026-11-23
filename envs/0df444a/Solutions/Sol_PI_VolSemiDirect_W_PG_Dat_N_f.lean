-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.N_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:36.382803+00:00
-- url     : https://prove2.me/submissions/65ab6c6f-9c4b-4aa8-a2e1-7010e5ddd7e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_symm
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pXv_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pz_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable (D : Dat A n r)
variable {D}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (b : Fin r) :
    S (D.f b) = D.f b + D.pW (S (D.f b)) + ∑ a, D.h (D.f a) (S (D.f b)) • D.e a := by
  have hpW : D.pW (S (D.f b)) = S (D.f b) - D.pU (S (D.f b)) := by simp [pW]
  have hXv : D.pXv (S (D.f b)) = D.f b := by
    rw [pXv_apply]
    have he : ∀ a, D.h (D.e a) (S (D.f b)) = if a = b then 1 else 0 := fun a => by
      rw [← hS.1 a, hU, H.ef]
    simp [he]
  have hz0 : D.h D.z (S (D.f b)) = 0 := by
    rw [← hS.2, hU, h_symm H, H.fz, map_zero]
  have hz : D.pz (S (D.f b)) = 0 := by
    rw [pz_apply, hz0, mul_zero, zero_smul]
  rw [hpW, pU_apply, hXv, hz, pX_apply]
  abel
end PI.VolSemiDirect.W.PG.Dat
