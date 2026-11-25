-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_HeightOneIntersection_proof_f7da7b6d131d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:25.98087+00:00
-- url     : https://prove2.me/submissions/17a1cdf1-88b1-4742-af1d-096bf2217de7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_KrullDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneIntersection
import Theorems.Thm_GroundTheory_Arith_Toric_mem_range_of_forall_height_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
namespace HeightOneIntersection
theorem _root_.solution : HeightOneIntersection.Statement := by
  intro A _ _ _ _ K _ _ _
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf]
    intro p _
    exact ⟨1, (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top, by rwa [one_smul]⟩
  · intro x hx
    simp only [Submodule.mem_iInf] at hx
    change x ∈ (⊥ : Subalgebra A K)
    rw [Algebra.mem_bot]
    obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := A) (K := K) x
      (fun p hp h1 => by
        obtain ⟨s, hs, hsx⟩ := hx ⟨p, hp⟩ h1
        change s • x ∈ (⊥ : Subalgebra A K) at hsx
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hsx
        refine ⟨a, s, hs, ?_⟩
        rw [Algebra.smul_def] at ha
        rw [ha, mul_comm])
    exact ⟨y, hy⟩
end HeightOneIntersection
end GroundTheory.Heights₂.Heights.Model
