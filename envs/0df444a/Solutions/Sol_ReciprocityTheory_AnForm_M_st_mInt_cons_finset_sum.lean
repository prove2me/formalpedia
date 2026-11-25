-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_mInt_cons_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:09:45.102375+00:00
-- url     : https://prove2.me/submissions/7ce535a9-b1cf-47ed-b51b-0cb50007d1e8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_sum
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_mInt_congr_phi
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_mIntConstPot
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_isPotential_cons
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntAdd
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
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {ι : Type*} (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ m, A.Smooth (f m)) (g : X → ℝ) (hg : Continuous g) :
    mInt A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) g =
      ∑ m ∈ s, mInt A (Fin.cons (LocPot.ofFun (f m)) Φ) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_mIntConstPot A 0 Φ g
  | insert a s ha ih =>
    have hS : A.Smooth (fun x => ∑ m ∈ s, f m x) := st_smooth_sum A s hf
    have hcongr : mInt A (Fin.cons (LocPot.ofFun fun x => ∑ m ∈ insert a s, f m x) Φ) g =
        mInt A (Fin.cons (LocPot.ofFun (f a) + LocPot.ofFun fun x => ∑ m ∈ s, f m x) Φ) g := by
      apply st_mInt_congr_phi
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · funext x y
        simp [Finset.sum_insert ha, LocPot.ofFun]
        rfl
      · rfl
    rw [hcongr, mIntAdd A _ _ Φ (isPotential_ofFun A _ (hf a)) (isPotential_ofFun A _ hS) hΦ g
      (mIntegrableCont A _ (st_isPotential_cons A (hf a) hΦ) g hg)
      (mIntegrableCont A _ (st_isPotential_cons A hS hΦ) g hg), ih, Finset.sum_insert ha]
end ReciprocityTheory.AnForm.M
