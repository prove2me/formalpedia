-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_inv_mem_df30a667553b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:05.086973+00:00
-- url     : https://prove2.me/submissions/d0b4d4af-46fc-4721-8bd8-3e69032d53ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
set_option synthInstance.maxHeartbeats 400000
open GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
variable {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
local notation "fr" Q:max h:max =>
  algebraMap (_ ⧸ Q) (FractionRing (_ ⧸ Q)) (Ideal.Quotient.mk Q h)
variable {P W : Ideal (MRing ι F)} [P.IsPrime] [W.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
theorem _root_.solution (hPW : P ≤ W) {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) (hfW : f ∉ W) : fr P g / fr P f ∈ degZeroLoc P {W} :=
  div_mem_degZeroLoc P {W} hg hf (fun h => hfW (hPW h)) (by rintro _ rfl; exact hfW)
end GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
