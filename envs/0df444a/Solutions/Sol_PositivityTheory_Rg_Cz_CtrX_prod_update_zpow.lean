-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.prod_update_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:25.594616+00:00
-- url     : https://prove2.me/submissions/85cca478-809b-45e9-b9db-4d0e441cd9b1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractB

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (c : ι → ℤ) (τ0 : ι) (hd : d τ0 ≠ 0) :
    ∏ τ, d τ ^ (Function.update c τ0 (c τ0 - 1)) τ = (d τ0)⁻¹ * ∏ τ, d τ ^ c τ := by
  have hsplit : ∀ f : ι → ℂ, ∏ τ, f τ = f τ0 * ∏ τ ∈ Finset.univ.erase τ0, f τ := by
    intro f
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ τ0)]
  rw [hsplit, hsplit (fun τ => d τ ^ c τ)]
  have hrest : ∏ τ ∈ Finset.univ.erase τ0, d τ ^ (Function.update c τ0 (c τ0 - 1)) τ = ∏ τ ∈ Finset.univ.erase τ0, d τ ^ c τ := by
    refine Finset.prod_congr rfl (fun τ hτ => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]
  rw [hrest, Function.update_self, zpow_sub_one₀ hd]
  ring
end PositivityTheory.Rg.Cz.CtrX
