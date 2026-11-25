-- Prove2me | solution 1 for ReciprocityTheory.PGsh.wedge_eq_det_smul_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:45:30.743157+00:00
-- url     : https://prove2.me/submissions/111da296-f43e-40f8-8bab-26049d17b0c2

import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent

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
theorem _root_.solution {k : ℕ} {W : Submodule K V} (bW : Basis (Fin k) K W) (w : Fin k → W) :
    ExteriorAlgebra.ιMulti K k (fun j => (w j : V)) =
      bW.det w • ExteriorAlgebra.ιMulti K k (fun j => (bW j : V)) := by
  let f := (ExteriorAlgebra.ιMulti K k).compLinearMap W.subtype
  have key : ∀ ψ : Module.Dual K (ExteriorAlgebra K V), ψ (f w) = ψ (bW.det w • f bW) := by
    intro ψ
    have h := AlternatingMap.eq_smul_basis_det bW (ψ.compAlternatingMap f)
    have := congrArg (fun g => g w) h
    simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at this
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have : f w - bW.det w • f bW = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro ψ; rw [map_sub, key, sub_self]
  exact sub_eq_zero.mp this
end ReciprocityTheory.PGsh
