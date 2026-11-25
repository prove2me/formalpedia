-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.sf_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:48:59.097087+00:00
-- url     : https://prove2.me/submissions/cb17ba22-a9a5-483e-91ae-eb0323ac560b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_add

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
theorem _root_.solution {ι : Type*} (S : Finset ι) (g : ι → Sym m n) (h : ∀ i ∈ S, SymbolInFirstFamily ε (g i)) : SymbolInFirstFamily ε (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using sf_zero ε
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact sf_add ε (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end PositivityTheory.Rg.Sw.LC.B1
