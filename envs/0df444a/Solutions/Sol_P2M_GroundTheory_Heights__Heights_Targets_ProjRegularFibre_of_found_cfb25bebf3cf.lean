-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegularFibre_of_found_cfb25bebf3cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:38.951271+00:00
-- url     : https://prove2.me/submissions/24dae1ec-206d-4aa9-8ce2-592c26dbc88e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_isClosed_projFibre_e496eb342b27
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_restrictScalars_real
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_locInj


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjRegularFibre
theorem _root_.solution (hReg : ProjRegular.Statement) : ProjRegularFibre.Statement := by
  intro K _ ι _ P J n R Ψ V BV hBV hV hΨ
  have hAn := (hReg K ι P J n R Ψ V BV hBV).2.1
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  set q : V → Fin n → ℂ := projCoord R Ψ ∘ Subtype.val with hqdef
  set f : Fin BV.n → (Fin n → ℂ) → Fin n → ℂ := fun j => q ∘ (BV.chart j).symm with hfdef

  set C : Fin BV.n → Set (Fin n → ℂ) := fun j => {u | u ∈ (BV.chart j).target ∧
      Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1)) 0 ≠ 0 ∧
      LinearMap.det (fderiv ℂ (f j) u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0} with hCdef
  have hnull : ∀ j, volume (f j '' C j) = 0 := fun j => by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (f j) u).restrictScalars ℝ) (fun u hu => ?_) (fun u hu => ?_)
    · have ha := hAn _ hu.2.1 j ((BV.chart j).map_target hu.1)
      rw [(BV.chart j).right_inv hu.1] at ha
      exact (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · show LinearMap.det ((fderiv ℂ (f j) u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) = 0
      rw [ReciprocityTheory.AnForm.A.det_restrictScalars_real, hu.2.2, map_zero]
  filter_upwards [compl_mem_ae_iff.mpr (measure_iUnion_null hnull)] with y hy
  set F : Set V := Subtype.val ⁻¹'
    {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} with hFdef
  have hFc : IsCompact F :=
    ((isClosed_projFibre R Ψ hV hΨ y).preimage continuous_subtype_val).isCompact

  have hFreg : ∀ x ∈ F, x ∈ projRegular R Ψ BV := by
    intro x hx
    refine ⟨hx.2.1, fun j hj hd => hy (Set.mem_iUnion.mpr ⟨j, BV.chart j x,
      ⟨(BV.chart j).map_source hj, ?_, hd⟩, ?_⟩)⟩
    · rw [(BV.chart j).left_inv hj]; exact hx.2.1
    · show projCoord R Ψ ((BV.chart j).symm (BV.chart j x)).1 = y
      rw [(BV.chart j).left_inv hj]; exact hx.2.2

  have hloc : ∀ x ∈ F, ∃ N ∈ 𝓝 x, Set.InjOn q N := by
    intro x hx
    obtain ⟨j, hj⟩ := BV.cover x
    obtain ⟨W, hWo, hxW, hinj⟩ :=
      pushA_locInj (hAn x (hFreg x hx).1 j hj) ((hFreg x hx).2 j hj)
    refine ⟨(BV.chart j).source ∩ BV.chart j ⁻¹' W,
      ((BV.chart j).isOpen_inter_preimage hWo).mem_nhds ⟨hj, hxW⟩, fun a ha b hb hab => ?_⟩
    refine (BV.chart j).injOn ha.1 hb.1 (hinj ha.2 hb.2 ?_)
    show projCoord R Ψ ((BV.chart j).symm (BV.chart j a)).1 =
      projCoord R Ψ ((BV.chart j).symm (BV.chart j b)).1
    rw [(BV.chart j).left_inv ha.1, (BV.chart j).left_inv hb.1]
    exact hab
  choose! N hN hNinj using hloc
  obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover N hN
  refine t.finite_toSet.subset fun z hz => ?_
  have hzy : projCoord R Ψ z.1 = y := hz.1
  have hzF : z ∈ F := ⟨z.2, hz.2.1, hzy⟩
  obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp (hcov hzF)
  have hxF := htF x hxt
  have : z = x := hNinj x hxF hzx (mem_of_mem_nhds (hN x hxF)) (hzy.trans hxF.2.2.symm)
  exact this ▸ hxt
end ProjRegularFibre
end GroundTheory.Heights₂.Heights.Targets
