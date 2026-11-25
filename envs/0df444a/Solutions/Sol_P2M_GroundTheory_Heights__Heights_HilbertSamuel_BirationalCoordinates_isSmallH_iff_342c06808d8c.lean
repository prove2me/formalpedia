-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_isSmallH_iff_342c06808d8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:13:33.903484+00:00
-- url     : https://prove2.me/submissions/14ce7de7-2a9d-49ed-9687-08d1129aad6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_rep_iff_6121dedef159

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution (P : Ideal (MRing (GlobalTheory κ))) (A : HermLine (GlobalTheory κ)) (τ : ℕ) (s' : Ω'') :
    IsSmallH P x A τ (μ ^ ((τ : ℤ) * A.a ()) * j s') ↔ IsSmallH P y A τ s' := by
  constructor
  · intro H dg dh g h z hg hh hd he hz
    exact H dg dh g h z hg hh hd ((rep_iff j hμ hx A τ s' hg hh hd).2 he) hz
  · intro H dg dh g h z hg hh hd he hz
    exact H dg dh g h z hg hh hd ((rep_iff j hμ hx A τ s' hg hh hd).1 he) hz
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
