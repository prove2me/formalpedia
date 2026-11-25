-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_pairToLattice_bijective_0c88b201f33f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:15.04174+00:00
-- url     : https://prove2.me/submissions/2f1ea4b7-87a5-46ed-a8e5-9168bd8625c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_coord_unique_a2cc2d0ceb8a
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_mem_latticeOf_8c9b33b78633


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (τ : ℍ) : Function.Bijective (pairToLattice τ) := by
  constructor
  · intro p r h
    have h2 := congrArg (fun z : NzLattice τ => (z : ℂ)) h
    simp only [pairToLattice] at h2
    have := coord_unique (τ := τ) (m := p.1.2) (n := p.1.1) (m' := r.1.2) (n' := r.1.1)
      (by linear_combination h2)
    exact Subtype.ext (Prod.ext this.2 this.1)
  · rintro ⟨z, hz, hz0⟩
    obtain ⟨m, n, rfl⟩ := mem_latticeOf.mp hz
    refine ⟨⟨(n, m), fun h => hz0 ?_⟩, Subtype.ext ?_⟩
    · rw [Prod.mk_eq_zero] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · simp only [pairToLattice]
      ring
end GroundTheory.Heights₂.Theta.projectiveLineClassData
