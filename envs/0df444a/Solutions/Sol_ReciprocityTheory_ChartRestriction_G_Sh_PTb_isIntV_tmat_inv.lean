-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.isIntV_tmat_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:08.477052+00:00
-- url     : https://prove2.me/submissions/b3996a35-6e97-4a47-b491-3f1eea67eb0e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_tmat_det_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a))
    (hdet : v (tmat γ).det = 0) (i j : Fin d) : IsIntV v ((tmat γ)⁻¹ i j) := by
  let S : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
        exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }
  have hent : ∀ a b, tmat γ a b ∈ S := fun a b => by
    show 0 ≤ v (tmat γ a b)
    exact (hγ a b).2 1
  let M' : Matrix (Fin d) (Fin d) S := fun a b => ⟨tmat γ a b, hent a b⟩
  have hM : tmat γ = S.subtype.mapMatrix M' := by
    ext a b
    rfl
  have hadj : ∀ i j, (tmat γ).adjugate i j ∈ S := by
    intro i j
    rw [hM, ← RingHom.map_adjugate]
    first
    | exact (M'.adjugate i j).2
    | simp
  have hdet_inv : v ((tmat γ).det⁻¹) = 0 := by
    have h1 : v ((tmat γ).det⁻¹ * (tmat γ).det) = 0 := by
      rw [inv_mul_cancel₀ (tmat_det_ne_zero hdet), AddValuation.map_one]
    rwa [AddValuation.map_mul, hdet, add_zero] at h1
  show 0 ≤ v ((tmat γ)⁻¹ i j)
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, AddValuation.map_mul,
    hdet_inv, zero_add]
  exact hadj i j
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
