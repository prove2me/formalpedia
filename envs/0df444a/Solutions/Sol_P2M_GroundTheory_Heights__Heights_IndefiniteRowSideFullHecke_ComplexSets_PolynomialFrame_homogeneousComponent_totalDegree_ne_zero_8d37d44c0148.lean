-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_homogeneousComponent_totalDegree_ne_zero_8d37d44c0148
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:57:26.24263+00:00
-- url     : https://prove2.me/submissions/3f69fc81-5a7d-41a7-b28a-3924fe7beefd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PolynomialFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame
theorem _root_.solution {k : ℕ} {P : MvPolynomial (Fin k) ℂ} (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  have hne : P.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hP)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup P.support hne (fun s => s.sum fun _ e => e)
  intro h0
  have h1 := congrArg (coeff m) h0
  rw [coeff_homogeneousComponent, coeff_zero, if_pos] at h1
  · exact (mem_support_iff.mp hm) h1
  · rw [totalDegree, hmax]
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame
