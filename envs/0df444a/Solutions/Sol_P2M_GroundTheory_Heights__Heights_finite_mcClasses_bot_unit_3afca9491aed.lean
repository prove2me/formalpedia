-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finite_mcClasses_bot_unit_3afca9491aed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:10:59.475255+00:00
-- url     : https://prove2.me/submissions/d4f215f0-fd71-424f-911d-03fc383c2311

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : Finite (McClasses (⊥ : Ideal (MRing (fun _ : Unit => Unit)))) := by
  haveI : Subsingleton (McClasses (⊥ : Ideal (MRing (fun _ : Unit => Unit)))) := by
    constructor
    intro x y
    induction x using Quot.ind with | mk z => ?_
    induction y using Quot.ind with | mk z' => ?_
    apply Quot.sound
    obtain ⟨⟨⟩, hz⟩ := z.2.1 ()
    obtain ⟨⟨⟩, hz'⟩ := z'.2.1 ()
    refine ⟨fun _ => z'.1 ⟨(), ()⟩ / z.1 ⟨(), ()⟩, fun _ => div_ne_zero hz' hz, ?_⟩
    funext p
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    field_simp
  exact Finite.of_subsingleton
end GroundTheory.Heights₂.Heights
