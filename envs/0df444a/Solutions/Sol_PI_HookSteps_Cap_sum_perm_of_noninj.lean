-- Prove2me | solution 1 for PI.HookSteps.Cap.sum_perm_of_noninj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:42:36.587868+00:00
-- url     : https://prove2.me/submissions/f4d119d9-6451-4089-81e5-60568bdd265d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open MvPolynomial Finset
namespace PI.HookSteps.Cap
theorem _root_.solution {M : Type} [AddCommMonoid M] (N : ℕ) (F : (Fin N → Fin N) → M)
    (hF : ∀ s, ¬ Function.Injective s → F s = 0) :
    ∑ s, F s = ∑ π : Equiv.Perm (Fin N), F π := by
  classical
  have himg : ∑ π : Equiv.Perm (Fin N), F π =
      ∑ s ∈ Finset.univ.image (fun π : Equiv.Perm (Fin N) => (π : Fin N → Fin N)), F s :=
    (Finset.sum_image fun π _ σ _ h => Equiv.ext (congrFun h)).symm
  rw [himg]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hF s fun hinj => hs ?_
  exact Finset.mem_image.2
    ⟨Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩
end PI.HookSteps.Cap
