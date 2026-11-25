-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.mom_fock_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:44.020527+00:00
-- url     : https://prove2.me/submissions/329f0cc9-4d74-4ad5-a14b-51a3bc68e6e3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FockMomOfBasic
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_pderiv_fock
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_cr_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_pderiv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_smul


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hB : FockBasic)
variable (hM : OneMom)
include hB hM
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    mom c (fock c (X k * p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
  obtain ⟨hL, -, hX⟩ := hB m n c hc
  have e1 := mom_pderiv hM c hc k (fock c p)
  have e2 : mom c (pderiv k (fock c p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
    rw [pderiv_fock hB c hc, mom_smul]
  rw [hX, cr_apply, mom_add hM c hc, ← neg_one_smul ℂ (pderiv k (fock c p)), mom_smul, mom_smul, ← e2, e1]
  ring
end PositivityTheory.Rg.Sw.LC
