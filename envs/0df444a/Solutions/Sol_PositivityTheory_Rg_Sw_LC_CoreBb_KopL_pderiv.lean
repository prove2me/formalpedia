-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.KopL_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:19.640349+00:00
-- url     : https://prove2.me/submissions/f46d9a08-8619-42ca-961c-b00d3be95e59

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_KopL

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreBb
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) (f : PX m n) :
    KopL ε i j (pderiv k f) - pderiv k (KopL ε i j f) =
      if ε k.1 then (if k.2.2 = false ∧ k.2.1 = i then -pderiv (k.1, j, false) f else 0)
      else (if k.2.2 = true ∧ k.2.1 = j then pderiv (k.1, i, true) f else 0) := by
  rw [pderiv_KopL]
  obtain ⟨a, c, b⟩ := k
  cases hε : ε a <;> cases b <;> by_cases hcj : c = j <;> by_cases hci : c = i <;> simp [hε, hcj, hci] <;>
    split_ifs <;> simp
end PositivityTheory.Rg.Sw.LC.CoreBb
