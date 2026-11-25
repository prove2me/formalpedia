-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.constSec_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:25.456924+00:00
-- url     : https://prove2.me/submissions/79ed0b07-fe12-4205-bb7c-e23e9b54dbc2

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (U : S.Opens) (c : ℂ) :
    constSec s U c = S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (constSec s ⊤ c) := by
  simp only [constSec, RingHom.comp_apply]
  rw [← s.appLE_map (U := ⊤) (V := ⊤) le_top (homOfLE (le_top : U ≤ ⊤)).op]
  rfl
end ReciprocityTheory.AnForm.R
