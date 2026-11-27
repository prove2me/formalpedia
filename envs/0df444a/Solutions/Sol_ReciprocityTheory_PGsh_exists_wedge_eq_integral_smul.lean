-- Prove2me | solution 1 for ReciprocityTheory.PGsh.exists_wedge_eq_integral_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:30:36.317886+00:00
-- url     : https://prove2.me/submissions/e1329d36-c7e0-4121-9e0d-1697fb788652

import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Theorems.Thm_ReciprocityTheory_PGsh_wedge_eq_det_smul_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open ReciprocityTheory ReciprocityTheory.PGsh
attribute [local instance] extModR
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {R : Type*} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
    {k : ℕ} {b w : Fin k → V} (hb : LinearIndependent K b)
    (hw : ∀ j, w j ∈ span R (Set.range b)) :
    ∃ r : R, ExteriorAlgebra.ιMulti K k w = algebraMap R K r • ExteriorAlgebra.ιMulti K k b := by
  have hw' : ∀ j, w j ∈ span K (Set.range b) := fun j => span_le_restrictScalars R K _ (hw j)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun R).mp (hw j)
  let bW := Basis.span hb
  let w' : Fin k → span K (Set.range b) := fun j => ⟨w j, hw' j⟩
  have hw'eq : ∀ j, w' j = ∑ i, algebraMap R K (c j i) • bW i := by
    intro j; ext
    simp only [w', bW, Submodule.coe_sum, Submodule.coe_smul, Basis.span_apply, ← hc j]
    simp [algebraMap_smul]
  have hrepr : ∀ j i, bW.repr (w' j) i = algebraMap R K (c j i) := by
    intro j i
    rw [hw'eq j, map_sum]
    simp only [map_smul, Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  refine ⟨(Matrix.of fun i j => c j i).det, ?_⟩
  have h1 := wedge_eq_det_smul_basis bW w'
  have hdet : bW.det w' = algebraMap R K (Matrix.of fun i j => c j i).det := by
    rw [Basis.det_apply, RingHom.map_det]
    congr 1; ext i j; simp [Basis.toMatrix_apply, hrepr]
  simpa [w', bW, Basis.span_apply, hdet] using h1
end ReciprocityTheory.PGsh
