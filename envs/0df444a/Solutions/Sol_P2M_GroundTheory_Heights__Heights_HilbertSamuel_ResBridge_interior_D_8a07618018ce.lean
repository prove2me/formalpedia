-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_interior_D_8a07618018ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:03:17.755639+00:00
-- url     : https://prove2.me/submissions/95c770f9-4f29-487f-a724-34403479832b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullFlat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_pt_mem_D_iff_4133d8fe572e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_isGoodAtlas_7b36ff3bea7c
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
theorem _root_.solution : interior {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  set i := R.idx x
  have hxi : x ∈ R.R.src i := R.mem_src_idx x
  set sd := R.R.sncAt i x hxi
  have hcont : ContinuousOn (fun y => eval (R.R.coord i y) sd.h) (R.R.src i) :=
    (MvPolynomial.continuous_eval sd.h).comp_continuousOn
      (continuousOn_iff_continuous_domRestrict.mpr (R.R.isEmbedding i).continuous)
  set O := interior {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} ∩
    (R.R.src i ∩ (fun y => eval (R.R.coord i y) sd.h) ⁻¹' {0}ᶜ) with hOdef
  have hO : IsOpen O :=
    isOpen_interior.inter (hcont.isOpen_inter_preimage (R.R.isOpen_alt_bis i) isOpen_compl_singleton)
  have hxO : x ∈ O := ⟨hx, hxi, sd.eval_h⟩
  obtain ⟨ψ, -, hxψ, hsub, hform⟩ := R.isGoodAtlas.2 i x hxi sd.r sd.span_eq O hO hxO
  have hnull : volume ψ.target = 0 := by
    refine measure_mono_null (t := ⋃ l : Fin e, {u : Fin e → ℂ | u l = 0}) ?_
      (measure_iUnion_null fun l => ?_)
    · intro u hu
      have hy : ψ.symm u ∈ ψ.source := ψ.map_target hu
      have hyO := hsub hy
      have hyD : R.pt (ψ.symm u) ∈ ReciprocityTheory.AnForm.R.conePts R.D :=
        (interior_subset (s := {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D}) hyO.1.1 :)
      have hbd := (R.R.zero_bd i (ψ.symm u) hyO.2).mpr ((pt_mem_D_iff R (x := x) hyO.2).mp hyD)
      have h0 := hbd _ sd.mem_bd
      rw [map_mul, map_prod] at h0
      have hprod := (mul_eq_zero.mp h0).resolve_left hyO.1.2.2
      obtain ⟨l, -, hl0⟩ := Finset.prod_eq_zero_iff.mp hprod
      have hu' : u = ReciprocityTheory.AnForm.R.evalFam sd.r (R.R.coord i (ψ.symm u)) :=
        (ψ.right_inv hu).symm.trans (hform _ hy)
      exact Set.mem_iUnion.mpr ⟨l, (congrFun hu' l).trans hl0⟩
    · rw [MeasureTheory.volume_pi]
      exact Measure.pi_hyperplane _ l 0
  exact (ψ.open_target.measure_pos volume ⟨ψ x, ψ.map_source hxψ⟩).ne' hnull
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
