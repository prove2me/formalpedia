-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.etaLt_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:40:58.209806+00:00
-- url     : https://prove2.me/submissions/0d5a72ef-5fde-4b22-83a6-cb09f35aeb02

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.B3
theorem _root_.solution {u v : Sym m n} {d₁ d₂ : ℕ} (hu : EtaLe u d₁) (hv : EtaLt v d₂) : EtaLt (u * v) (d₁ + d₂) := by
  classical
  intro t ht
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul u v ht)
  have h1 := hu a ha
  have h2 := hv b hb
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  omega
end PositivityTheory.Rg.Sw.LC.B3
