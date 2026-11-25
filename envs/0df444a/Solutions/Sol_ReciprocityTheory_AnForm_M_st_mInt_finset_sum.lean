-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_mInt_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:36.778371+00:00
-- url     : https://prove2.me/submissions/114ce284-cb3d-4598-aede-b255c263a437

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_mInt_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntLinear
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntegrableCont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type*} (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ m, Continuous (f m)) :
    mInt A Φ (fun x => ∑ m ∈ s, f m x) = ∑ m ∈ s, mInt A Φ (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_mInt_zero A Φ
  | insert a s ha ih =>
    have hc : Continuous (fun x => ∑ m ∈ s, f m x) := continuous_finsetSum _ fun m _ => hf m
    have := mIntLinear A Φ hΦ 1 (f a) (fun x => ∑ m ∈ s, f m x)
      (mIntegrableCont A Φ hΦ _ (hf a)) (mIntegrableCont A Φ hΦ _ hc)
    simp only [one_mul] at this
    simp only [Finset.sum_insert ha, this, ih]
end ReciprocityTheory.AnForm.M
