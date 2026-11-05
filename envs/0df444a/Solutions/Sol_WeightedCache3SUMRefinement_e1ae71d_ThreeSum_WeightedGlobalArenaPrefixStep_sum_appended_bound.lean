-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixStep.sum_appended_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:30:55.499086+00:00
-- url     : https://prove2.me/submissions/e8cd7e39-fbd7-45a5-8131-52005407be02

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPotential
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixStep
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixStep_appended_next
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_TernaryPairedContraction_sum_nextPotential_bound
import Theorems.Thm_ThreeSum_TernaryPairedPotential_minor_small_of_entry_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixStep
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaPrefixGroups WeightedGlobalArenaPrefixPairs WeightedGlobalArenaPrefixPotential
open WeightedGlobalNativePrefixLineage TernaryPairedPotential TernaryPairedContraction TernaryOriginalRowMenu
open TernaryExtensionEncoding
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixStep
theorem _root_.solution (ℓ : E→ₗ[ZMod p] ZMod p) (hℓ : ℓ≠0)
    (V : Submodule (ZMod p) (Fin Λ→ZMod p)) (hV : V≠⊤) (hp : 3≤p)
    (newroot : E×E→ℕ→ZMod p) (r K b : ℕ)
    (hL : ∀ i j, (L i j).natAbs≤b) (hR : ∀ i j, (R i j).natAbs≤b)
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*Λ*p^2≤Fintype.card E) (hsize : 8*Λ*p^(2*(K+K))≤Fintype.card E) :
    p^(K+K)*(∑ seed∈admissible Λ ℓ V,
      value maps τ cap I L R (Function.update row r (TernaryOriginalRowMenu.row Λ ℓ seed))
        (fun o => Function.update (root o) r (newroot seed o)) Q (r+1) K)≤
      3*(admissible Λ ℓ V).card*F*(vertices (fixedLength m) (fixedPi m)).card*
        (2^(fixedPi m 1)*3^(fixedPi m 2))^K*value maps τ cap I L R row root Q r K := by
  have hsmall : ∀ (x : Index maps τ cap I L R row root Q r K) f,
      ((matrix maps τ cap I L R row root Q x).submatrix id f).det.natAbs<p := by
    intro x
    apply minor_small_of_entry_bound _ b ?_ hdet
    intro i j
    unfold matrix
    cases finSumFinEquiv.symm i with
    | inl k => exact hL _ _
    | inr k => exact hR _ _
  have hh := sum_nextPotential_bound (α := fixedAlpha m) (π := fixedPi m) ℓ hℓ V hV hp
    (matrix maps τ cap I L R row root Q (r := r) (K := K)) hsmall maps hsize1 hsize
  apply le_trans (Nat.mul_le_mul_left _ (sum_le_sum (fun seed hs =>
    appended_next maps τ cap I L R row root Q ℓ seed (newroot seed) r K))) hh
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixStep
