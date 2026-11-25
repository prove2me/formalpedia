-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_baseChange_968fd6092864
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:11.232742+00:00
-- url     : https://prove2.me/submissions/bd8995eb-f96b-46b5-b70a-22de83f10b5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_baseChangeCoord_one_tmul_01fd286ad6c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreSpace_inner_equiv_9aa4479f01dc


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
open NumberField TensorProduct ComplexAt GroundTheory.Heights₂.Heights
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (h : HermitianMetric K E) (τ : L →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → E) :
    gramDet (h.baseChange L) τ (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) =
      gramDet h (τ.comp (algebraMap K L)) s := by
  have hv : ∀ i j, inner ℂ (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s i))
      (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s j)) =
      inner ℂ (fibreVec h (τ.comp (algebraMap K L)) (s i))
        (fibreVec h (τ.comp (algebraMap K L)) (s j)) := by
    intro i j
    rw [fibreVec, fibreVec, FibreSpace.inner_equiv]
    change inner ℂ (FibreSpace.equiv h _ (baseChangeCoord τ _))
      (FibreSpace.equiv h _ (baseChangeCoord τ _)) = _
    rw [baseChangeCoord_one_tmul, baseChangeCoord_one_tmul]
    rfl
  simp only [gramDet]
  congr 2
  ext i j
  simp only [Matrix.gram_apply, hv]
end GroundTheory.Heights₂.Heights.LatticeLemmas
