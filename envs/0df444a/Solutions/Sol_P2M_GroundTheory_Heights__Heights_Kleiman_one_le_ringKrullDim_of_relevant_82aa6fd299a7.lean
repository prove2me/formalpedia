-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_one_le_ringKrullDim_of_relevant_82aa6fd299a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:59.456471+00:00
-- url     : https://prove2.me/submissions/84276cff-77c9-43c1-9775-8af24f55ffd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quotient_succ_le_of_lt_6f6a573dbbda

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
variable {k : Type u} [Field k] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (pp : Ideal (Poly k N)) [pp.IsPrime]
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    1 ≤ ringKrullDim (Poly k N ⧸ pp) := by
  obtain ⟨i, hi⟩ := hrel
  have hle : pp ≤ RingHom.ker (constantCoeff : Poly k N →+* k) := by
    intro f hf
    rw [RingHom.mem_ker]
    by_contra h0
    have h1 := hh f hf 0
    rw [homogeneousComponent_zero] at h1
    have h0' : coeff 0 f ≠ 0 := by rwa [← constantCoeff_eq]
    have hu : IsUnit (C (coeff 0 f) : Poly k N) := (isUnit_iff_ne_zero.mpr h0').map C
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ h1 hu)
  have hlt : pp < RingHom.ker (constantCoeff : Poly k N →+* k) :=
    lt_of_le_of_ne hle fun h => hi (h ▸ by simp [RingHom.mem_ker])
  have hnt : Nontrivial (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) :=
    Ideal.Quotient.nontrivial_iff.mpr (RingHom.ker_ne_top _)
  calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
    _ ≤ ringKrullDim (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) + 1 :=
        by gcongr; exact ringKrullDim_nonneg_of_nontrivial
    _ ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_quotient_succ_le_of_lt hlt
end GroundTheory.Heights₂.Heights.Kleiman
