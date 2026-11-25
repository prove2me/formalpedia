-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_SP_Mi_opE_C_mul__198277c1a297
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:25.09266+00:00
-- url     : https://prove2.me/submissions/47ad2f02-c2b6-4438-b7fd-4d19c28acfa8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_del_C_mul

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R] {ρ : ℕ}
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution (α : R) (p q : Fin ρ) (r : R) (g : Pm R ρ) : opE α p q (C r * g) = C r * opE α p q g := by
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, del_C_mul]
  ring
end PositivityTheory.Rg.Sw.SP.Mi
