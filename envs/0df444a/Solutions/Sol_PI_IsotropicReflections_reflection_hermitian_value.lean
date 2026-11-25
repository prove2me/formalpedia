-- Prove2me | solution 1 for PI.IsotropicReflections.reflection_hermitian_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:52:56.497151+00:00
-- url     : https://prove2.me/submissions/1854c411-0839-4206-977f-43a13f8ae237

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic
import Theorems.Thm_PI_IsotropicReflections_sw_e
import Theorems.Thm_PI_IsotropicReflections_al_e
import Theorems.Thm_PI_IsotropicReflections_weyl_lift_eq_pair
import Theorems.Thm_PI_IsotropicReflections_hpk_e_row
import Theorems.Thm_PI_IsotropicReflections_mulVec_bvec
import Theorems.Thm_PI_IsotropicReflections_herm_bvec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsotropicReflections
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {k r : ℕ}
variable (l : Fin r) (g : Mx k r) (hg : g ∈ Glev k r l.succ)
include hg
namespace PI.IsotropicReflections
theorem _root_.solution (c : ℂ) :
    herm (Hpk k r) ((w1 k r l c * g) *ᵥ bvec (eI k r l)) (bvec (eI k r l)) = c := by
  have h := hg
  simp only [Glev, Set.mem_setOf_eq] at h
  have hge : g *ᵥ bvec (eI k r l) = bvec (eI k r l) := (h.2 l (by simp)).1
  rw [herm_bvec, ← Matrix.mulVec_mulVec, hge, mulVec_bvec]
  simp only [Matrix.mulVec, dotProduct, hpk_e_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [weyl_lift_eq_pair, sw_e, al_e]
  simp
end PI.IsotropicReflections
