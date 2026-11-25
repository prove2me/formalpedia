-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_proof_28dc9e797b4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:30.995886+00:00
-- url     : https://prove2.me/submissions/45313795-dd2c-47a0-8e24-97576983dc6d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_ringKrullDim_eq_62996ccb0278
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
open MvPolynomial Algebra Cardinal
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace DimTie
theorem _root_.solution : DimTie.Statement := by
  intro k _ Ω _ _ N y hy e
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hi₀ : y i₀ ≠ 0 := hi₀
  have hdim := DimTie.ringKrullDim_eq (k := k) y hy
  constructor
  · intro h
    have h' := h.dim
    rw [hdim] at h'
    have h3 : (trdeg k (funField (k := k) y)).toENat + 1 = (e : ℕ∞) + 1 := by exact_mod_cast h'
    exact Cardinal.toENat_eq_natCast.mp ((ENat.add_left_injective_of_ne_top ENat.one_ne_top) h3)
  · intro h
    have h' : trdeg k (funField (k := k) y) = e := h
    refine ⟨inferInstance, fun p hp d => homogeneousComponent_mem_primeOf y hp d, le_rfl, ⟨i₀, ?_⟩, ?_⟩
    · rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k i₀), aeval_X]
      exact hi₀
    · rw [hdim, Cardinal.toENat_eq_natCast.mpr h']
      push_cast
      rfl
end DimTie
end GroundTheory.Heights₂.Heights.Kleiman
