-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_ne_zero_d609092c2fe8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:02:22.493442+00:00
-- url     : https://prove2.me/submissions/0510893b-dee2-432b-a32b-bb8530e91d20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_882e60645eed


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
theorem _root_.solution {u : Fin (r + 1) → K} (hu : u ≠ 0) : dehom K r (latticeForm u) ≠ 0 := by
  rw [dehom_latticeForm]
  intro h
  apply hu
  have h' := IsFractionRing.injective (MvPolynomial (Fin r) K) (LatticeField K r) (h.trans (map_zero _).symm)
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · have := congrArg (coeff 0) h'
    simpa [coeff_sum, coeff_C_mul, coeff_X, coeff_C] using this
  · have := congrArg (coeff (Finsupp.single i 1)) h'
    have h0 : (0 : Fin r →₀ ℕ) ≠ Finsupp.single i 1 := (Finsupp.single_ne_zero.mpr one_ne_zero).symm
    simpa [coeff_sum, coeff_C_mul, coeff_X, coeff_C, Finsupp.single_left_inj, h0] using this
end GroundTheory.Heights₂.Heights.LatticeModel
