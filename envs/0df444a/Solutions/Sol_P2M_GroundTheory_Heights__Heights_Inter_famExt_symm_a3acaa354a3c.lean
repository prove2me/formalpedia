-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_famExt_symm_a3acaa354a3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:59:06.848675+00:00
-- url     : https://prove2.me/submissions/df1e36ee-6c5d-4cba-8915-e462d7b38c90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_famExt_apply_175dede7bc86

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (hI : IsIntersectionFamily I) (hP : IsArithVar P n) (e : Fin 2 → HermLine ι)
    (he : ∀ i, IsSmoothHerm (e i)) : IsSymmForm (famExt I P n e) := by
  intro σ v
  rw [famExt_apply, famExt_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_
  have h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm := rfl
  have h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j) := by
    refine (Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_
    simp
  rw [h1, h2, hI.1 P n (e ∘ s) σ.symm hP fun j => he _]
end GroundTheory.Heights₂.Heights.Inter
