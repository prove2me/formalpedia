-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isSheetAt_space_951c6534d672
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:12:11.801537+00:00
-- url     : https://prove2.me/submissions/6e943907-3215-4687-b2ab-45bf789c1fab

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (x : Fin n → ℂ) :
    IsSheetAt (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) x id := by
  have hZ : ∀ y : Fin n → ℂ, y ∈ zeroSet (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) := by
    intro y q hq
    rw [Ideal.mem_bot] at hq
    simp [hq]
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, differentiableOn_id, by simp,
    fun y _ => ⟨by simp, hZ y⟩, Set.univ, Filter.univ_mem, fun x' _ _ => by simp⟩
end GroundTheory.Heights₂.Heights
