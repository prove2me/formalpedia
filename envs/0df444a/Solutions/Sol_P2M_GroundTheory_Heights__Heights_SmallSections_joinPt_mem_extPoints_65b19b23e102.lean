-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_joinPt_mem_extPoints_65b19b23e102
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:40.513558+00:00
-- url     : https://prove2.me/submissions/e8fa037f-e446-4613-a421-2db19570f5e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_aeval_8800237edca7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_isLive_of_mem_points_f34985632ea7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_exists_evalCone_ne_zero_d1e48d88ea05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_aeval_formSubst_mem_14b5e93265d5

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
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) :
    D.joinPt z (fun j ↦ evalCone z (g c j)) ∈ D.extPoints := by
  have hc : P.IsLive c := isLive_of_mem_points hz hzc
  refine ⟨fun o ↦ ?_, fun f hf ↦ ?_⟩
  · cases o with
    | none =>
      obtain ⟨j, hj⟩ := exists_evalCone_ne_zero hg hz hzc
      exact fun h ↦ hj (congrFun h j)
    | some k => exact hz.1 k
  · have h := hz.2 _ (aeval_formSubst_mem hg hc hf)
    rw [evalCone_aeval] at h
    rw [← h, evalCone]
    congr 1
    funext v
    obtain ⟨o, i⟩ := v
    cases o with
    | none => rfl
    | some k => simp [formSubst, evalCone, AddBlockData.joinPt]
end GroundTheory.Heights₂.Heights.SmallSections
