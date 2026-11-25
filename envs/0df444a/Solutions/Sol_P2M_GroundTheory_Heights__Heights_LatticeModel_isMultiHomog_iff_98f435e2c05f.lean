-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_isMultiHomog_iff_98f435e2c05f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:02:30.024911+00:00
-- url     : https://prove2.me/submissions/a5f7b639-5cda-4381-9427-9e7abeb0a40e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_weight_one_eq_degree_27ee5a5b405e


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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (g : Geo.MRing (blockIdx fun _ : Unit ↦ N)) (d : Unit → ℕ) :
    Geo.IsMultiHomog g d ↔ g.IsHomogeneous (d ()) := by
  have hdeg : ∀ s : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ, ∑ i : Fin (N + 1), s ⟨(), i⟩ = s.degree := by
    intro s
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp
  constructor
  · intro h s hs
    rw [weight_one_eq_degree, ← hdeg]
    exact h s (mem_support_iff.mpr hs) ()
  · intro h s hs k
    have := h (mem_support_iff.mp hs)
    rw [weight_one_eq_degree, ← hdeg] at this
    exact this
end GroundTheory.Heights₂.Heights.LatticeModel
