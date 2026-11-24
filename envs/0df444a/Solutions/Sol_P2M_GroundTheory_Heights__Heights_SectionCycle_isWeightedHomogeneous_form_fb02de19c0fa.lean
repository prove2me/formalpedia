-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_isWeightedHomogeneous_form_fb02de19c0fa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:34.22709+00:00
-- url     : https://prove2.me/submissions/554635f4-c1db-491a-87fd-1104a8f4539c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution (hg : D.IsFormSystem d g) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (D.size + 1)) :
    IsWeightedHomogeneous (coordDeg n) (g c j) (fun k ↦ ((d k : ℤ) + D.deg k).toNat) := by
  obtain ⟨δ, hδ, hδk⟩ := hg.homog c j
  convert hδ using 1
  funext k
  rw [← hδk k]
  simp
end GroundTheory.Heights₂.Heights.SectionCycle
