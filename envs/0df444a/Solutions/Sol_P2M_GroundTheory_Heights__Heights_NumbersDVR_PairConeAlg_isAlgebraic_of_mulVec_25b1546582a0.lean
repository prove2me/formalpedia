-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_isAlgebraic_of_mulVec_25b1546582a0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:43.987988+00:00
-- url     : https://prove2.me/submissions/946ea7fd-d887-4014-8947-dd57fcb0c76b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg
theorem _root_.solution {R L : Type*} [CommRing R] [IsDomain R] [CommRing L] [IsDomain L]
    [Algebra R L] {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n L) (w : n → L)
    (hG : ∀ i j, IsAlgebraic R (G i j)) (hGw : ∀ i, IsAlgebraic R ((G.mulVec w) i)) (hdet : G.det ≠ 0)
    (q : n) : IsAlgebraic R (w q) := by
  let AC := Subalgebra.algebraicClosure R L
  let GA : Matrix n n AC := fun i j => ⟨G i j, hG i j⟩
  let f : AC →+* L := AC.val.toRingHom
  have hmap : f.mapMatrix GA = G := by ext i j; rfl
  have hadj : ∀ i j, G.adjugate i j ∈ AC := by
    intro i j
    rw [← hmap, ← RingHom.map_adjugate]
    exact (GA.adjugate i j).2
  have hdetA : G.det ∈ AC := by
    rw [← hmap, ← RingHom.map_det]
    exact (GA.det).2
  have key : G.det * w q = (G.adjugate.mulVec (G.mulVec w)) q := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hdet) hdetA ?_
  rw [key]
  exact Subalgebra.sum_mem AC fun j _ => AC.mul_mem (hadj q j) (hGw j)
end GroundTheory.Heights₂.Heights.NumbersDVR.PairConeAlg
