-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_of_isChowForm_129f76209172
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:39.804811+00:00
-- url     : https://prove2.me/submissions/97d274bb-6fb3-4ff3-a4ab-768d467fb5bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_iff_0f52654b96e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultihomog_map_iff_cd1cd76dd983

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {e δ : ℕ} {P : Ideal (MRing (PBlk n))}
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f)) : IsMultiHomog δ f :=
  (isMultiHomog_iff f).mpr ((isMultihomog_map_iff (Rat.castHom ℂ).injective f).mp hf.1)
end GroundTheory.Heights₂.Heights.ObjectsChow
