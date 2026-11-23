-- Prove2me | solution 1 for PI.WGL.XiU.sum_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:45.714793+00:00
-- url     : https://prove2.me/submissions/df3e7709-6345-4e20-bd4b-400af61d9391

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiU
open Matrix
namespace PI.WGL.XiU
theorem _root_.solution {N s : ℕ} {M : Type*} [AddCommMonoid M] (I : Fin s → Fin N) (hI : Function.Injective I)
    (f : Fin N → M) (hf : ∀ b, b ∉ Set.range I → f b = 0) : ∑ b, f b = ∑ p, f (I p) := by
  rw [← Finset.sum_image (fun p _ q _ h => hI h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  apply hf
  rintro ⟨p, rfl⟩
  exact hb (Finset.mem_image_of_mem _ (Finset.mem_univ p))
end PI.WGL.XiU
