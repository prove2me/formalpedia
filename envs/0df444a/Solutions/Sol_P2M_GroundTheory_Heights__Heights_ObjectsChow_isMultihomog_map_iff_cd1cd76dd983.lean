-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultihomog_map_iff_cd1cd76dd983
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:46.058625+00:00
-- url     : https://prove2.me/submissions/f2fcb713-3c51-41b2-a289-7c6d9ef2a9f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm

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
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) {e δ : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R) :
    IsMultihomog (map φ f) δ ↔ IsMultihomog f δ := by
  simp only [IsMultihomog, support_map_of_injective _ hφ]
end GroundTheory.Heights₂.Heights.ObjectsChow
