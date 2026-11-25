-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_coneEq_irreducible_5f02fbd10eb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:52:15.597368+00:00
-- url     : https://prove2.me/submissions/a7e9d0e4-9854-4deb-99e1-5d87101adb55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : Irreducible coneEq := by
  rw [← MulEquiv.irreducible_iff (finSuccEquiv ℂ 2).toMulEquiv]
  change Irreducible (finSuccEquiv ℂ 2 coneEq)
  rw [finSuccEquiv_coneEq]
  have hm : (Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1 : MvPolynomial (Fin 2) ℂ)).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hd : (Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1 : MvPolynomial (Fin 2) ℂ)).natDegree = 2 :=
    Polynomial.natDegree_X_pow_sub_C
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hd]) (by rw [hd]; norm_num),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  rw [Polynomial.mem_roots hm.ne_zero, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hr
  have hx : (X 0 * X 1 : MvPolynomial (Fin 2) ℂ) ≠ 0 := mul_ne_zero (X_ne_zero _) (X_ne_zero _)
  have r0 : r ≠ 0 := by
    rintro rfl
    exact hx (by rw [← hr]; simp)
  have h := congrArg (degreeOf 0) hr
  rw [degreeOf_pow_eq 0 r 2 r0, degreeOf_mul_eq (X_ne_zero _) (X_ne_zero _), degreeOf_X,
    degreeOf_X] at h
  simp at h
end GroundTheory.Heights₂.Heights.ComplexSets
