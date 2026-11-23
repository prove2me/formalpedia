-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_L4_cartan_comm_erase__7d4a3ad236fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:38.144328+00:00
-- url     : https://prove2.me/submissions/e6f36588-e71e-490a-9332-af62cf2473b2

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (ρ : Fin r) (a : Fin r) (ha : a ∈ univ.erase ρ) (b : Fin r)
    (hb : b ∈ univ.erase ρ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j ρ ρ (glAct p LL j a b x) = glAct p LL j a b (glAct p LL j ρ ρ x) := by
  have h := glAct_comm (p := p) LL j ρ ρ a b x
  have hda : ¬ (ρ = a) := fun h => (Finset.mem_erase.mp ha).1 h.symm
  have hbc : ¬ (b = ρ) := (Finset.mem_erase.mp hb).1
  rw [if_neg hda, if_neg hbc, sub_zero, sub_eq_zero] at h
  exact h
end Formalism.InvariantFactorPaths.L4
