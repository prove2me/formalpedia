-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_isAnalyticSubset_D_e54d8c491106
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:40.780849+00:00
-- url     : https://prove2.me/submissions/57d6a6e4-c3eb-4ea8-8aba-df0cc8103db9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullFlat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_pt_mem_D_iff_4133d8fe572e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_isGoodAtlas_7b36ff3bea7c
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
theorem _root_.solution :
    R.atlas.IsAnalyticSubset {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} := by
  intro x
  set i := R.idx x
  obtain ⟨n, g, hg⟩ :=
    (Submodule.fg_iff_exists_fin_generating_family).mp (IsNoetherian.noetherian (R.R.bd i))
  refine ⟨R.R.src i, R.R.isOpen_alt_bis i, R.mem_src_idx x, n, fun l y => eval (R.R.coord i y) (g l),
    fun l => R.isGoodAtlas.1 i (g l), ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyD, hy⟩
    refine ⟨hy, fun l => ?_⟩
    have hz := (R.R.zero_bd i y hy).mpr ((pt_mem_D_iff R hy).mp hyD)
    have hgl : g l ∈ R.R.bd i := by
      rw [← hg]
      exact Submodule.subset_span ⟨l, rfl⟩
    exact hz _ hgl
  · rintro ⟨hy, hz⟩
    refine ⟨(pt_mem_D_iff R hy).mpr ((R.R.zero_bd i y hy).mp fun h hh => ?_), hy⟩
    rw [← hg] at hh
    induction hh using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, rfl⟩ := ha
      exact hz l
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [smul_eq_mul, hb]
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
