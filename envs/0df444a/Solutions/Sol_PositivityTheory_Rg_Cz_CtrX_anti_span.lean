-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.anti_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:30:49.999876+00:00
-- url     : https://prove2.me/submissions/a02eb8c9-4cbe-4c91-8aaa-657f29c28b33

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_antisymmetric_eq_zero_of_not_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution (f : TV n M (Fin n))
    (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) (J : Fin n → Fin n) :
    ∃ c : ℂ, f J = c • f id := by
  by_cases hJ : Function.Injective J
  · have hb : Function.Bijective J := Finite.injective_iff_bijective.mp hJ
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective J hb) : ℤ) : ℂ), ?_⟩
    have h1 := congrFun (hf (Equiv.ofBijective J hb)) id
    have h3 : pm (Equiv.ofBijective J hb) f id = f J := rfl
    rw [h3, Pi.smul_apply] at h1
    exact h1
  · exact ⟨0, by rw [antisymmetric_eq_zero_of_not_injective f hf J hJ, zero_smul]⟩
end PositivityTheory.Rg.Cz.CtrX
