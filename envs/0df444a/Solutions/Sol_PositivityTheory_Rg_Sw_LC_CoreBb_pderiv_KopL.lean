-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.pderiv_KopL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:20.339015+00:00
-- url     : https://prove2.me/submissions/b211f2ce-fc5f-4778-9750-9fe7d6d4f45e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_comm__c7d947a11a2b
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_KopL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_collapse

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
    pderiv k (KopL ε i j f) = KopL ε i j (pderiv k f) +
      ((if ε k.1 = true ∧ k.2.1 = i ∧ k.2.2 = false then pderiv (k.1, j, false) f else 0) -
        (if ε k.1 = false ∧ k.2.1 = j ∧ k.2.2 = true then pderiv (k.1, i, true) f else 0)) := by
  classical
  rw [KopL_apply, KopL_apply, map_sub, map_sum, map_sum]
  have e1 : ∀ (a : Fin m) (c : Fin n) (b : Bool) (q : Fin m × Fin n × Bool),
      pderiv k (X (a, c, b) * pderiv q f) =
        (if k = (a, c, b) then pderiv q f else 0) + X (a, c, b) * pderiv q (pderiv k f) := by
    intro a c b q
    rw [pderiv_mul, pderiv_X, Pi.single_apply, pderiv_comm' k q f]
    by_cases h : (a, c, b) = k
    · subst h; simp
    · have h' : ¬ k = (a, c, b) := fun e => h e.symm
      simp [h, h']
  simp only [e1, Finset.sum_add_distrib]
  rw [collapse (fun a => ε a = true) i false (fun a => pderiv (a, j, false) f) k,
    collapse (fun a => ε a = false) j true (fun a => pderiv (a, i, true) f) k]
  ring
end PositivityTheory.Rg.Sw.LC.CoreBb
