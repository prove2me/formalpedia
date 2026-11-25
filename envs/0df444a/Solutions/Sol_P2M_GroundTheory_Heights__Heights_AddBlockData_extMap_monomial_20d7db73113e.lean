-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_monomial_20d7db73113e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:37.915753+00:00
-- url     : https://prove2.me/submissions/6fc7f227-1653-449c-8f34-4f11bf6df2bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightEqMapDomain

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
theorem _root_.solution (s : Coord D.extSizes →₀ ℕ) (a : ℤ) :
    D.extMap (monomial s a) =
      monomial (s.mapDomain Sigma.fst) ((a : P.FunField) * s.prod fun v e ↦ D.extVal v ^ e) := by
  have hX : (s.prod fun v e ↦ (X v.1 : MvPolynomial (Option ι) P.FunField) ^ e) =
      monomial (s.mapDomain Sigma.fst) 1 := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_mapDomain_index (fun _ ↦ pow_zero _)
      (fun _ _ _ ↦ pow_add _ _ _)]
  rw [extMap, coe_eval₂Hom, eval₂_monomial]
  simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
  rw [hX, ← map_finsuppProd, eq_intCast, ← map_intCast (C : P.FunField →+* MvPolynomial (Option ι) P.FunField),
    ← mul_assoc, ← C_mul, C_mul_monomial, mul_one]
end GroundTheory.Heights₂.Heights.AddBlockData
