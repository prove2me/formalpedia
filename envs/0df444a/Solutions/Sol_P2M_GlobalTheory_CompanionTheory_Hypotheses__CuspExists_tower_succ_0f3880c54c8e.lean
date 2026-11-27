-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_tower_succ_0f3880c54c8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:01:17.560503+00:00
-- url     : https://prove2.me/submissions/2407a88e-0a4f-4811-ad66-c20273b19308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIrreducibleTransportRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
variable (K : Type) [Field K] [Fintype K]
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
theorem _root_.solution (k : ℕ) :
    (tower K (k + 1)).1 ^ ((Fintype.card K ^ (k + 1).factorial - 1) / (Fintype.card K ^ k.factorial - 1)) =
      (tower K k).1 :=
  (exists_root_over (lev_pos K (Nat.factorial_pos (k + 1)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ k))) (tower K k).2
      (exists_prim K (Nat.factorial_pos (k + 1))).choose_spec).choose_spec.2
end GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
