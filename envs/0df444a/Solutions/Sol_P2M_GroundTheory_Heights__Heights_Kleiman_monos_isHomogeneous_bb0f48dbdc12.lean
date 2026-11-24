-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:56.760362+00:00
-- url     : https://prove2.me/submissions/5b460c86-99a6-4087-9ed6-3c667248be99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable (S : Type u) [CommRing S] (N : ℕ)
variable {S N}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    ∃ e : ℕ, s.IsHomogeneous e := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := hx
    exact ⟨1, isHomogeneous_X S i⟩
  | one => exact ⟨0, isHomogeneous_one _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, ha.mul hb⟩
end GroundTheory.Heights₂.Heights.Kleiman
