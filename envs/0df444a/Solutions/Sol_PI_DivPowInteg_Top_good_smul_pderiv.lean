-- Prove2me | solution 1 for PI.DivPowInteg.Top.good_smul_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:51.296197+00:00
-- url     : https://prove2.me/submissions/ec4bf35a-d3ce-4149-90a4-c50100eb5559

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_NatMulFactorialBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Top
open PI.DivPowInteg.Gen
variable {A K I J : Type} [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
  [Fintype I] [Fintype J]
namespace PI.DivPowInteg.Top
theorem _root_.solution (L : Submodule A K) (k : ℕ) (c : K) (hc : c ∈ L) (s : I ⊕ J)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) (m : (I ⊕ J) →₀ ℕ) :
    c * (coeff (m + Finsupp.single s 1) Q * ((m s : K) + 1)) ∈ L ^ (k + 1) := by
  have hy : coeff (m + Finsupp.single s 1) Q * ((m s : K) + 1) ∈ L ^ k := by
    have e : coeff (m + Finsupp.single s 1) Q * ((m s : K) + 1) =
        (m s + 1) • coeff (m + Finsupp.single s 1) Q := by
      rw [nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    exact nsmul_mem (hQ _) _
  rw [pow_succ']
  exact Submodule.mul_mem_mul hc hy
end PI.DivPowInteg.Top
