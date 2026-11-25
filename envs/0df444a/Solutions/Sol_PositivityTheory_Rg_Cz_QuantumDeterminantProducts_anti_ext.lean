-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.anti_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:35.77481+00:00
-- url     : https://prove2.me/submissions/86ee48a3-6a21-4373-a1a4-0fc06138179e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_anti_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_anti_zero
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.QuantumDeterminantProducts
theorem _root_.solution {g : TV n M (Fin n)} (hg : IsAnti g) (h0 : g id = 0) : g = 0 := by
  funext I
  by_cases hI : Function.Injective I
  · have hb : Function.Bijective I := Finite.injective_iff_bijective.mp hI
    have h := anti_apply hg (Equiv.ofBijective I hb) id
    have hc : (id ∘ ⇑(Equiv.ofBijective I hb)) = I := by
      funext k
      rfl
    rw [hc, h0, smul_zero] at h
    simpa using h
  · simpa using anti_zero hg hI
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts
