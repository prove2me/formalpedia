-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosureTrdeg_sum_flagCoord_842bc55e9286
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:00.446919+00:00
-- url     : https://prove2.me/submissions/24519d91-0f0e-4733-b50c-7924320b339d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeLinesIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg
theorem _root_.solution {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (a : Fin N → Φ) :
    ∑ j, flagCoord w e t k j * a j =
      ∑ j : Fin k, flagCoord w e t k (Fin.castLE hkN j) * a (Fin.castLE hkN j) := by
  calc ∑ j, flagCoord w e t k j * a j
      = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hkN), flagCoord w e t k j * a j :=
        (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    _ = _ := Finset.sum_map _ _ _
  intro j _ hj
  have hjk : ¬ (j : ℕ) < k := fun h => hj (Finset.mem_map.2 ⟨⟨j, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  simp [flagCoord, hjk]
end GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureTrdeg
