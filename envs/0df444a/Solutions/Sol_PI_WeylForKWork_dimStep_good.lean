-- Prove2me | solution 1 for PI.WeylForKWork.dimStep_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:28:02.028871+00:00
-- url     : https://prove2.me/submissions/e41f29af-e035-4987-b9e8-6c6c8fd144ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStep
import Theorems.Thm_PI_WeylForKWork_dimStep_one_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix DimensionInduction
namespace PI.WeylForKWork
theorem _root_.solution {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (Kset (allPos n)) σ) :
    Good (fun g : Kset (allPos n) => σ g.1) where
  isom := fun g v => hσ.2.1 g.1 g.2 v
  inv := fun g => ⟨⟨star g.1, Kset_star _ g.2⟩, fun v => by
    show σ g.1 (σ (star g.1) v) = v
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ g.2 _ (Kset_star _ g.2),
      Unitary.mul_star_self_of_mem g.2.1, hσ.1.1]
    rfl⟩
  mul := fun g g' => ⟨⟨g.1 * g'.1, Kset_mul _ g.2 g'.2⟩, fun v => by
    show σ g.1 (σ g'.1 v) = σ (g.1 * g'.1) v
    rw [hσ.1.2 _ g.2 _ g'.2]
    rfl⟩
  one := ⟨⟨1, dimStep_one_mem _⟩, fun v => by
    show σ 1 v = v
    rw [hσ.1.1]
    rfl⟩
end PI.WeylForKWork
