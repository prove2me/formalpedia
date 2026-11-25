-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_injective_fderiv_affLift_d9609d0f5e9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:35:38.323456+00:00
-- url     : https://prove2.me/submissions/5c671741-2d98-407c-8a4c-145744c65e40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDens
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_affLift_analyticAt_1c5c7977c09d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X} {BV : FinHolAtlas n V}
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotDens
theorem _root_.solution (hB : HoloMap BV R.A Subtype.val) (x : V) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) {j j' : Fin BV.n} (hj : x ∈ (BV.chart j).source)
    (hj' : x ∈ (BV.chart j').source)
    (hr : Module.finrank ℂ (LinearMap.range (fderiv ℂ
      (fun u => affCoord p (R.lift x.1 ((BV.chart j').symm u).1)) (BV.chart j' x) :
        (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) = n) :
    Function.Injective (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1))
      (BV.chart j x)) := by
  set F : Fin BV.n → (Fin n → ℂ) → ((Σ k, ι k) → ℂ) :=
    fun i u => affCoord p (R.lift x.1 ((BV.chart i).symm u).1) with hF
  have hinj' : Function.Injective (fderiv ℂ (F j') (BV.chart j' x)) := by
    have hk := LinearMap.finrank_range_add_finrank_ker
      (fderiv ℂ (F j') (BV.chart j' x) : (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))
    rw [hr, Module.finrank_fin_fun] at hk
    have h0 : LinearMap.ker (fderiv ℂ (F j') (BV.chart j' x) :
        (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ)) = ⊥ :=
      Submodule.finrank_eq_zero.1 (by omega)
    exact LinearMap.ker_eq_bot.1 h0
  have hu0 : BV.chart j x ∈ (BV.chart j).target := (BV.chart j).map_source hj
  have hv0 : BV.chart j' x ∈ (BV.chart j').target := (BV.chart j').map_source hj'
  have hsj : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hj
  have hsk : (BV.chart j').symm (BV.chart j' x) = x := (BV.chart j').left_inv hj'
  have hτu : (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x) = BV.chart j' x := by simp [hsj]
  have hτ : AnalyticAt ℂ (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x) :=
    BV.holo j j' _ ⟨hu0, by
      show (BV.chart j).symm (BV.chart j x) ∈ (BV.chart j').source; rw [hsj]; exact hj'⟩
  have hσ : AnalyticAt ℂ (BV.chart j ∘ (BV.chart j').symm)
      ((BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    rw [hτu]
    exact BV.holo j' j _ ⟨hv0, by
      show (BV.chart j').symm (BV.chart j' x) ∈ (BV.chart j).source; rw [hsk]; exact hj⟩
  have hev : ∀ᶠ u in 𝓝 (BV.chart j x), (BV.chart j).symm u ∈ (BV.chart j').source :=
    ((BV.chart j).continuousAt_symm hu0).preimage_mem_nhds (by
      show (BV.chart j').source ∈ 𝓝 ((BV.chart j).symm (BV.chart j x))
      rw [hsj]; exact (BV.chart j').open_source.mem_nhds hj')
  have hid : (BV.chart j ∘ (BV.chart j').symm) ∘ (BV.chart j' ∘ (BV.chart j).symm)
      =ᶠ[𝓝 (BV.chart j x)] id := by
    filter_upwards [hev, (BV.chart j).open_target.mem_nhds hu0] with u hu hut
    simp [(BV.chart j').left_inv hu, (BV.chart j).right_inv hut]
  have hq : F j =ᶠ[𝓝 (BV.chart j x)] F j' ∘ (BV.chart j' ∘ (BV.chart j).symm) := by
    filter_upwards [hev] with u hu
    simp [hF, (BV.chart j').left_inv hu]
  have hFa : AnalyticAt ℂ (F j') ((BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    rw [hτu]; exact (affLift_analyticAt hB x hj' p hp).1
  have hD : fderiv ℂ (F j) (BV.chart j x) = (fderiv ℂ (F j') (BV.chart j' x)).comp
      (fderiv ℂ (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    rw [hq.fderiv_eq, fderiv_comp _ hFa.differentiableAt hτ.differentiableAt, hτu]
  have hT : Function.LeftInverse (fderiv ℂ (BV.chart j ∘ (BV.chart j').symm) (BV.chart j' x))
      (fderiv ℂ (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    intro w
    have h1 := hid.fderiv_eq (𝕜 := ℂ)
    rw [fderiv_comp _ hσ.differentiableAt hτ.differentiableAt, fderiv_id, hτu] at h1
    simpa using congrArg (fun L => L w) h1
  show Function.Injective (fderiv ℂ (F j) (BV.chart j x))
  rw [hD]
  exact hinj'.comp hT.injective
end GroundTheory.Heights₂.Heights.Targets.ProjPotDens
