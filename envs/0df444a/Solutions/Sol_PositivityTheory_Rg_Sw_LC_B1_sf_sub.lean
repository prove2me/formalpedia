-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.sf_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:58.374455+00:00
-- url     : https://prove2.me/submissions/3a9d4a7e-3b3b-4e0f-9607-9b4d4e6659c1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_smul

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
theorem _root_.solution {s₁ s₂ : Sym m n} (h₁ : SymbolInFirstFamily ε s₁) (h₂ : SymbolInFirstFamily ε s₂) : SymbolInFirstFamily ε (s₁ - s₂) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ s₂]; exact sf_add ε h₁ (sf_smul ε _ h₂)
end PositivityTheory.Rg.Sw.LC.B1
