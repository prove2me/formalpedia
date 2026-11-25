-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_latticeMap_intComb_ac9dfce53bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:28.976796+00:00
-- url     : https://prove2.me/submissions/375d9eaf-aceb-4ba4-ad25-d40c39114d56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeForm_add_e2e620659c05

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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (φ : Fin (N + 1) → Fin (r + 1) → K) (c : Fin (N + 1) → ℤ) :
    latticeMap φ (∑ b, (c b : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * X ⟨(), b⟩) =
      latticeForm (∑ b, c b • φ b) := by
  let Lf : (Fin (r + 1) → K) →+ MvPolynomial (Fin (r + 1)) K := AddMonoidHom.mk' latticeForm latticeForm_add
  have h : latticeForm (∑ b, c b • φ b) = ∑ b, c b • latticeForm (φ b) := by
    change Lf _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ ↦ map_zsmul Lf (c b) (φ b)
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [map_mul, map_intCast, zsmul_eq_mul]
  simp [latticeMap]
end GroundTheory.Heights₂.Heights
