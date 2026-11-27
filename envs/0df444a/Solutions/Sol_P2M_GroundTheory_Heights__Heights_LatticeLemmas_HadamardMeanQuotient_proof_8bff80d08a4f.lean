-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardMeanQuotient_proof_8bff80d08a4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:10:47.084895+00:00
-- url     : https://prove2.me/submissions/56cf29b7-55e7-476f-8aaf-6f7166d4e0f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMeanQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_normAt_mkQ_le_d6bddfecc781
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_exists_linearIndependent_mkQ_cf11d1f1864d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField GroundTheory.Heights₂.Heights Submodule Cardinal TensorProduct
universe u v w
noncomputable section
variable {K : Type u} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace HadamardMeanQuotient
theorem _root_.solution (h1 : HadamardMean.Statement.{u, v, 0}) :
    HadamardMeanQuotient.Statement.{u, v, w} := by
  intro K _ _ M F hF ι x hx
  obtain ⟨s, hs⟩ := exists_linearIndependent_mkQ M F x hx
  refine ⟨s, hs, le_trans ?_ (h1 K (M.quot F hF) (fun j ↦ F.mkQ (x (s j))) hs
    (by rw [Fintype.card_fin]; rfl))⟩
  gcongr with j _ σ _
  have hne : HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j))) ≠ 0 := by
    have := (linearIndependent_fibreVec (M.quot F hF).metric σ hs).ne_zero j
    exact norm_ne_zero_iff.mpr this
  have hpos : 0 < HermitianBundle.normAt (M.quot F hF) σ (F.mkQ (x (s j))) :=
    (norm_nonneg _).lt_of_ne' hne
  all_goals first
    | exact hpos
    | exact normAt_mkQ_le M F hF σ _
end HadamardMeanQuotient
end GroundTheory.Heights₂.Heights.LatticeLemmas
