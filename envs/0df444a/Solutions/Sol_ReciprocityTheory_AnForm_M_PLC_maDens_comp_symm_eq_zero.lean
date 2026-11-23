-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.maDens_comp_symm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:13.756822+00:00
-- url     : https://prove2.me/submissions/319812ac-2569-4919-ad6f-fae6bd6b9dcc

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_maDens_one_eq_zero

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
open ReciprocityTheory.AnForm.M.PLC
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLC
theorem _root_.solution (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ)) (v : X → ℝ)
    {y : Fin 1 → ℂ} (hy : y ∈ ψ.target) (hv : ψ.symm y ∉ tsupport v) :
    ReciprocityTheory.AnForm.maDens ![v ∘ ψ.symm] y = 0 := by
  apply maDens_one_eq_zero
  have ho : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (tsupport v)ᶜ) :=
    ψ.isOpen_inter_preimage_symm (isClosed_tsupport v).isOpen_compl
  filter_upwards [ho.mem_nhds ⟨hy, hv⟩] with w hw
  show v (ψ.symm w) = 0
  exact image_eq_zero_of_notMem_tsupport hw.2
end ReciprocityTheory.AnForm.M.PLC
