-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.tor_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:11.112367+00:00
-- url     : https://prove2.me/submissions/1a121895-1076-4984-bb11-802cc730df9a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {σ : R →+* R}
  {J : Matrix ι ι R}
variable (σ J)
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (e f : ι → R) (l m : R) (x : ι → R) :
    tor σ J e f l m *ᵥ x = x + ((l - 1) * hf σ J x f) • e + ((m - 1) * hf σ J x e) • f := by
  have vmvs : ∀ (s : R) (a w z : ι → R), (s • vecMulVec a w) *ᵥ z = (s * (w ⬝ᵥ z)) • a := by
    intro s a w z
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  unfold tor
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, vmvs, vmvs, ← hf_eq, ← hf_eq]
end ReciprocityTheory.ChartRestriction.G.SA
