-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_pow__5a8a11fb4ddf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:44.687875+00:00
-- url     : https://prove2.me/submissions/62d4beeb-e53f-46b9-ad51-d3efdbe02548

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIUnique
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_one__474efa1ab231
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIUnique_isMultiHomog_mul__07988fa1a14d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIUnique
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIUnique
theorem _root_.solution {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (isMultiHomog_one' (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul' ih hf
end GroundTheory.Heights₂.Heights.Inter.ThmIUnique
