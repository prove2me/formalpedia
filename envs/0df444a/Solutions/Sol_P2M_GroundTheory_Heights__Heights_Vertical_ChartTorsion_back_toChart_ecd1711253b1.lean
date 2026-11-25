-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_back_toChart_ecd1711253b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:25.306161+00:00
-- url     : https://prove2.me/submissions/d121d527-8bf5-4e22-9a83-5c69a7a3cd47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartTorsion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_baseToLoc_toBase_7faf5b7bd565

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
variable {D : Type} [CommRing D] {n : ℕ} (k : ℕ) (P : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
namespace GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
theorem _root_.solution (g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D) :
    back k P j (toChart k P j g) = toLoc k P j g := by
  suffices h : (back k P j).comp (toChart k P j) = toLoc k P j from congrArg (· g) h
  apply MvPolynomial.ringHom_ext
  · intro d
    have := baseToLoc_toBase k P j (C d)
    simpa [back, toChart] using this
  · rintro (m | ⟨i, m⟩)
    · have := baseToLoc_toBase k P j (X m)
      simpa [back, toChart] using this
    · by_cases hm : m = j
      · subst hm
        have hinc : toLoc k P m (∑ l, X (Sum.inr (i, l)) * X (Sum.inl l)) = 0 :=
          toLoc_mem k P m (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), map_add, map_sum] at hinc
        have hinv : baseToLoc k P m (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X m))) *
            toLoc k P m (X (Sum.inl m)) = 1 := by
          have e := baseToLoc_toBase k P m (X m)
          rw [rename_X] at e
          rw [← e, toBase, RingHom.comp_apply, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf,
            map_one]
        simp only [RingHom.comp_apply, toChart, eval₂Hom_X', Sum.elim_inr, solve, ↓reduceIte,
          back, map_neg, map_mul, map_sum, eval₂Hom_C, eval₂Hom_X', baseToLoc_toBase, rename_X]
        simp only [map_mul] at hinc
        set u := toLoc k P m (X (Sum.inr (i, m)))
        set xm := toLoc k P m (X (Sum.inl m))
        set inv := baseToLoc k P m (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X m)))
        have hS : ∑ l ∈ Finset.univ.erase m, toLoc k P m (X (Sum.inl l)) *
              toLoc k P m (X (Sum.inr (i, l))) =
            ∑ l ∈ Finset.univ.erase m, toLoc k P m (X (Sum.inr (i, l))) *
              toLoc k P m (X (Sum.inl l)) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        rw [hS]
        linear_combination (-inv) * hinc + u * hinv
      · simp [back, toChart, solve, hm]
end GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
