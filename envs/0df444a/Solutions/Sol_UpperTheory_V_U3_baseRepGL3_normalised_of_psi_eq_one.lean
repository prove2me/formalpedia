-- Prove2me | solution 1 for UpperTheory.V.U3.baseRepGL3_normalised_of_psi_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:58.935796+00:00
-- url     : https://prove2.me/submissions/269ec947-0dbb-4f13-8d9c-f9a989e4da3d

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_UnitaryThreeReflectionRight
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_BaseRepGL3NormalisedOfPsiEqOne
import Theorems.Thm_UpperTheory_V_U3_unitaryThreeReflection_left
import Theorems.Thm_UpperTheory_V_U3_unitaryThreeReflection_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] UpperTheory.V.U3.unitaryThreeReflection_left
attribute [local simp] UpperTheory.V.U3.unitaryThreeReflection_right



set_option autoImplicit false
open UpperTheory UpperTheory.V UpperTheory.V.U3
open Matrix
namespace UpperTheory.V.U3
theorem _root_.solution {G : Type*} [Group G] {R : Type*} [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ)
    {c : G} (g₁ : G) (hc : Ψ c = 1) : Normalised c g₁ (r0 η Ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · show Matrix.diagonal (fun i => ((Ψ c ^ wt1 i : Rˣ) : R)) = 1
    rw [hc]
    simp
  · show Matrix.diagonal _ 0 1 - Matrix.diagonal _ 0 1 = (0 : R)
    simp
  · show Matrix.diagonal _ 1 0 - Matrix.diagonal _ 1 0 = (0 : R)
    simp
end UpperTheory.V.U3
