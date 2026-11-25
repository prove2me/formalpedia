-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_sec_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:23:12.719855+00:00
-- url     : https://prove2.me/submissions/15a152e1-a24b-4745-b7f0-410fcf7e3684

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_nonzeroLocus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_basicOpen_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sameSum_iff_fsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_transport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {Y : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (f : Y ⟶ X) (n : ℕ) (hn : 1 ≤ n)
    (s : LB.Sec (LB.LinComb L (fun _ : Fin n => f) (fun _ => 1))) :
    ∃ s' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => f) (fun _ => (n : ℤ))), nonzeroLocus s ≤ nonzeroLocus s' := by
  classical
  have hsame : LB.SameSum (fun _ : Fin n => f) (fun _ => (1 : ℤ)) (fun _ : Fin 1 => f) (fun _ => (n : ℤ)) := by
    rw [sameSum_iff_fsum]
    simp [fsum, Finset.sum_const, Finsupp.smul_single]
  obtain ⟨s', hs'⟩ := sec_transport (L := L) (φ := fun _ : Fin n => f) (ε := fun _ => 1) (φ' := fun _ : Fin 1 => f)
    (ε' := fun _ => (n : ℤ)) hL hsame s
  refine ⟨s', fun y hy => ?_⟩
  obtain ⟨d, hd⟩ := (mem_nonzeroLocus s y).1 hy
  have hyd : y ∈ LB.wchart L (fun _ : Fin n => f) d := Y.basicOpen_le _ hd
  set i := d ⟨0, hn⟩
  have hi : f y ∈ L.U i := Set.mem_iInter.1 hyd ⟨0, hn⟩
  have hj : y ∈ LB.wchart L (fun _ : Fin n => f) (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have hj' : y ∈ LB.wchart L (fun _ : Fin 1 => f) (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have hyj := mem_basicOpen_chart s hd hj
  have e := congrArg Y.basicOpen (hs' (fun _ => i) (fun _ => i) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl))
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hmem : y ∈ (LB.wchart L (fun _ : Fin n => f) (fun _ => i) ⊓ LB.wchart L (fun _ : Fin 1 => f) (fun _ => i)) ⊓
      Y.basicOpen (s.f (fun _ => i)) := ⟨⟨hj, hj'⟩, hyj⟩
  have hmem2 := e ▸ hmem
  exact (mem_nonzeroLocus s' y).2 ⟨_, hmem2.2⟩
end ReciprocityTheory.ChartRestriction.G.DVR
