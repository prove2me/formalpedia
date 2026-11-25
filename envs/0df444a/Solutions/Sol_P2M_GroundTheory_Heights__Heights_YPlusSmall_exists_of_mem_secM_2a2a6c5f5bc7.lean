-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSmall_exists_of_mem_secM_2a2a6c5f5bc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:13.611208+00:00
-- url     : https://prove2.me/submissions/4b13b851-75ff-4c5f-ad14-76fc374bddb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.YPlusSmall
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] {n' : κ → ℕ} {Ω : Type} [Field Ω]
    (y : Coord n' → Ω) (e : κ → ℕ) {s : Ω} (hs : s ∈ Geo.secM (ι := blockIdx n') y e) :
    ∃ f : MvPolynomial (Coord n') ℤ, Geo.IsMultiHomog (ι := blockIdx n') f e ∧ aeval y f = s := by
  have hle : Submodule.span ℤ {s | ∃ g : MvPolynomial (Coord n') ℤ,
      Geo.IsMultiHomog (ι := blockIdx n') g e ∧ aeval y g = s} ≤
      Submodule.map (aeval y : MvPolynomial (Coord n') ℤ →ₐ[ℤ] Ω).toLinearMap
        (weightedHomogeneousSubmodule ℤ (coordDeg n') e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((geoMultiHomog_iff g e).mp hg), rfl⟩
  obtain ⟨f, hf, hfs⟩ := hle hs
  exact ⟨f, (geoMultiHomog_iff f e).mpr ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf), hfs⟩
end GroundTheory.Heights₂.Heights.YPlusSmall
