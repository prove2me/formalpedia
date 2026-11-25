-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.DegLT.X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:43:08.290311+00:00
-- url     : https://prove2.me/submissions/e907ccd8-0c13-4ae5-85ac-9332d097747b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_Basic_degree_add__88e784869794

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
namespace DegLT
theorem _root_.solution {d : ℕ} {P : PX m n} (j : Ix m n) (hP : DegLT d P) : DegLT (d + 1) (X j * P) := by
  intro t ht
  rw [MvPolynomial.support_X_mul] at ht
  obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
  simp only [addLeftEmbedding_apply, degree_add', Finsupp.degree_single]
  have := hP t' ht'
  omega
end DegLT
end PositivityTheory.Rg.Sw.LC.Basic
