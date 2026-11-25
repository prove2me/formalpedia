-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.slice2_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:14:39.27813+00:00
-- url     : https://prove2.me/submissions/931088f7-f7cd-4f53-9c79-5c4ad285833f

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
theorem _root_.solution {X : Type} (E : (X → C) →ₗ[C] (X → C)) (g h : X → C) :
    slice2 E (fun p => g p.1 * h p.2) = fun p => E g p.1 * E h p.2 := by
  funext p
  show E (fun a => E (fun b => g a * h b) p.2) p.1 = E g p.1 * E h p.2
  have h1 : (fun a => E (fun b => g a * h b) p.2) = E h p.2 • g := by
    funext a
    rw [show (fun b => g a * h b) = g a • h from rfl, map_smul]
    simp [mul_comm]
  rw [h1, map_smul]
  simp [mul_comm]
end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
