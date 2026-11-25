-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.sf_renameL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:51.609222+00:00
-- url     : https://prove2.me/submissions/e4b8e41d-d93d-41ca-a85b-dbbffcd4e366

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_mulL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
variable (ε : Fin m → Bool)
namespace PositivityTheory.Rg.Sw.LC.B1
theorem _root_.solution (p : PX m n) (hp : p ∈ F1 ε) {s : Sym m n} (h : SymbolInFirstFamily ε s) : SymbolInFirstFamily ε (rename Sum.inl p * s) := by
  rw [p.as_sum, map_sum, Finset.sum_mul]
  refine sf_sum ε _ _ fun μ hμ => ?_
  rw [rename_monomial]
  refine sf_mulL ε μ (fun k hk => ?_) h _
  have hv : k ∈ p.vars := (MvPolynomial.mem_vars k).mpr ⟨μ, hμ, hk⟩
  exact (MvPolynomial.mem_supported.mp hp) hv
end PositivityTheory.Rg.Sw.LC.B1
