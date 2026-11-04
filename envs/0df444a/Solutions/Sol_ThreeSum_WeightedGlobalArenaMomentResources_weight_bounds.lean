-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaMomentResources.weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:48:28.724872+00:00
-- url     : https://prove2.me/submissions/7b34635f-1d98-4000-81bf-a41c30316eb0

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_bound
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound
import Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_left_bound
import Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_right_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaMomentResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPairMass
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeMomentBounds
open WeightedGlobalMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaMomentResources
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (B C : ℕ→ℤ) (U K : ℕ)
    (hB : ∀ i<I.nB, |B i|≤(U : ℤ)) (hC : ∀ i<I.nC, |C i|≤(U : ℤ))
    (hcap : leftBound U K≤I.weightCap) :
    ∀ k<K+1, ∀ j≤k,
      (∀ i<(setup (r := r) maps τ cap Q I).left.NL,
        |LightWeightedGlobalMomentChannelFactory.leftWeights k j B i|≤
          ((setup (r := r) maps τ cap Q I).left.weightU : ℤ)) ∧
      (∀ i<(setup (r := r) maps τ cap Q I).right.NL,
        |LightWeightedGlobalMomentChannelFactory.rightWeights k j C i|≤
          ((setup (r := r) maps τ cap Q I).right.weightU : ℤ)) := by
  intro k hk j hj
  have hright : rightBound U K≤I.weightCap := by
    apply le_trans _ hcap
    unfold leftBound rightBound
    exact Nat.le_mul_of_pos_left _ (by positivity)
  constructor
  · intro i hi
    exact (left_bound (B i) (hB i hi) (by omega) hj).trans (Int.ofNat_le.mpr hcap)
  · intro i hi
    exact (right_bound (C i) (hC i hi) (by omega)).trans (Int.ofNat_le.mpr hright)
end ThreeSum.WeightedGlobalArenaMomentResources
