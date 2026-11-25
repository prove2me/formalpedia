-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_LocAinf_isUnit_inclW___dfbc296eb1fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:13.228031+00:00
-- url     : https://prove2.me/submissions/4523943c-a7bb-4f16-a976-b900581078f0

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementPC
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Theorems.Thm_P2M_Formalism_BasicNotions_LocAinf___ne_one_c5617a838e7d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open Loc
open Formalism.BasicNotions.LocAinf
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
namespace Formalism.BasicNotions.LocAinf
theorem _root_.solution : IsUnit (inclW l AI.ξ) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [inclW, WittVector.map_coeff]
  have h0 : AI.ξ.coeff 0 = ∑ i ∈ Finset.range l, AI.ε1 ^ i := by
    have := congrArg (fun x => WittVector.constantCoeff x) (show AI.ξ = AI.ξ from rfl)
    simp only [ξ, map_sum, map_pow] at this ⊢
    change WittVector.constantCoeff (∑ i ∈ Finset.range l, (WittVector.teichmuller l AI.ε1) ^ i) = _
    simp [map_sum, map_pow, WittVector.teichmuller_coeff_zero]
  rw [h0]
  intro hz
  have hz' : ∑ i ∈ Finset.range l, AI.ε1 ^ i = 0 :=
    (IsFractionRing.injective (OCb l) (Cb l)) (by rw [hz, map_zero])
  apply AI.ε_ne_one
  have hg := geom_sum_mul AI.ε1 l
  rw [hz', zero_mul, ε1, frobeniusEquiv_symm_pow_p] at hg
  exact (sub_eq_zero.mp hg.symm)
end Formalism.BasicNotions.LocAinf
