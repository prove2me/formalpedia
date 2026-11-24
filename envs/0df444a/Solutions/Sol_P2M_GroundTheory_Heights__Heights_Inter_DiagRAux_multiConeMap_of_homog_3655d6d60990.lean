-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_multiConeMap_of_homog_3655d6d60990
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:08.436032+00:00
-- url     : https://prove2.me/submissions/6623fb1e-3b48-4951-aa40-247117281282

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    T.multiConeMap c s = C (aeval c s) * ∏ k, X k ^ β k := by
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : (m.prod fun p e => (X p.1 : MvPolynomial K Φ) ^ e) = ∏ k, X k ^ β k := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, (X k : MvPolynomial K Φ) ^ m ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  simp only [T.multiConeMap, coe_eval₂Hom, eval₂_monomial, aeval_monomial, mul_pow, Finsupp.prod_mul,
    ← hX, map_mul, eq_intCast, algebraMap_int_eq, map_intCast]
  rw [show (m.prod fun p e => (C (c p) : MvPolynomial K Φ) ^ e) = C (m.prod fun p e => c p ^ e) by
    simp [Finsupp.prod, map_prod, map_pow]]
  ring
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
