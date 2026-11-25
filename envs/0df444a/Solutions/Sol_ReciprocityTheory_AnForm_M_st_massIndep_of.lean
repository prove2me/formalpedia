-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_massIndep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:14.054276+00:00
-- url     : https://prove2.me/submissions/25f9d374-bcb4-4ac9-baab-1ba06a199ebc

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_mass_step
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialAdd
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (hP : PartsStatement) : MassIndepStatement := by
  intro e X _ _ _ A Φ u hΦ hu
  cases e with
  | zero =>
    congr 1
    funext i
    exact i.elim0
  | succ n =>
    classical
    have key : ∀ s : Finset (Fin (n + 1)),
        mInt A (fun i => if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i) (fun _ => 1) =
          mInt A Φ (fun _ => 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have hpot : ∀ i, IsPotential A (if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i) := by
          intro i
          split_ifs
          · exact isPotentialAdd A _ _ (hΦ i) (isPotential_ofFun A _ (hu i))
          · exact hΦ i
        have hupd : (fun i => if i ∈ insert a s then Φ i + LocPot.ofFun (u i) else Φ i) =
            Function.update (fun i => if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i) a
              (Φ a + LocPot.ofFun (u a)) := by
          funext i
          by_cases hi : i = a
          · subst hi
            simp
          · simp [hi, Finset.mem_insert]
        have hstep := st_mass_step hP A (fun i => if i ∈ s then Φ i + LocPot.ofFun (u i) else Φ i)
          hpot a (u a) (hu a)
        simp only [ha, if_false] at hstep
        rw [hupd, hstep, ih]
    simpa using key Finset.univ
end ReciprocityTheory.AnForm.M
