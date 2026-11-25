-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.inhab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:16:23.981818+00:00
-- url     : https://prove2.me/submissions/cb89464b-3de7-4c0c-96a1-604bf537a04e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_lattice_zeroTorus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_hermFormPi_zeroTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 NumberField Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (q n : ℕ) (_hq : 1 ≤ q) :
    IsPi X0 q LinearMap.id ∧ (fun _ : Fin 1 → Vsp X0.dim => (1 : ℂ)) ∈ X0.Sec 1 1 ∧ (fun _ : Fin 1 → Vsp X0.dim => (1 : ℂ)) ≠ 0 ∧
      IsReps X0 q n LinearMap.id {0} := by
  refine ⟨⟨fun _ _ => Subsingleton.elim _ _, fun x _ => mem_lattice_zeroTorus x, fun v w => ?_, fun x _ => ?_⟩,
    ⟨differentiable_const _, fun γ _ v => ?_⟩, fun h => one_ne_zero (congrFun h 0),
    ⟨fun b _ k => mem_lattice_zeroTorus _, fun b _ => ⟨0, ⟨Finset.mem_singleton_self _, fun k => mem_lattice_zeroTorus _⟩,
      fun y hy => Finset.mem_singleton.mp hy.1⟩⟩⟩
  · simp [Hf]
  · simp [X0]
  · rw [hermFormPi_zeroTorus, hermFormPi_zeroTorus]; simp [X0]
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
