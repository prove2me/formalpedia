-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_isClosed_projFibre_e496eb342b27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:44.504951+00:00
-- url     : https://prove2.me/submissions/3b3eb9ec-d5cb-4d25-881a-9ea505deeb7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_segre_lift_eq_smul_efc1b61b0f6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_continuousOn_segre_lift_63fa5bef8928
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


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
theorem _root_.solution {n : ℕ} (R : AnLogRes P J (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (hV : IsClosed V)
    (hΨ : ∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) (y : Fin n → ℂ) :
    IsClosed {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  set F := {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} with hFdef
  have hxV : x ∈ V := closure_minimal (fun z hz => hz.1) hV hx
  set w : R.X → Fin (n + 1) → ℂ := fun z => Ψ (segre (R.lift x z)) with hwdef
  have hw : ContinuousAt w x :=
    (continuousOn_segre_lift R Ψ x).continuousAt ((R.isOpen_U x).mem_nhds (R.mem_U x))
  set h : R.X → Fin n → ℂ := fun z i => w z i.succ - y i * w z 0 with hhdef
  have hh : ContinuousAt h x := continuousAt_pi.mpr fun i =>
    ((continuous_apply _).continuousAt.comp hw).sub
      (continuousAt_const.mul ((continuous_apply _).continuousAt.comp hw))

  have hev : ∀ᶠ z in 𝓝[F] x, h z = 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((R.isOpen_U x).mem_nhds (R.mem_U x))] with z hz hzU
    obtain ⟨c, hc, hcz⟩ := segre_lift_eq_smul R x hzU
    have h0 : Ψ (segre (R.lift z z)) = c • w z := by simp [w, hcz]
    have hw0 : w z 0 ≠ 0 := fun h' => hz.2.1 (by rw [h0]; simp [h'])
    funext i
    have hi := congrFun hz.2.2 i
    simp only [projCoord, h0, Pi.smul_apply, smul_eq_mul] at hi
    rw [mul_div_mul_left _ _ hc, div_eq_iff hw0] at hi
    simp [h, hi]
  have : (𝓝[F] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hlim : h x = 0 :=
    tendsto_nhds_unique (hh.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm))
  have hi : ∀ i : Fin n, w x i.succ = y i * w x 0 := fun i => by
    have := congrFun hlim i
    simpa [h, sub_eq_zero] using this
  have hw0 : w x 0 ≠ 0 := by
    intro h0
    apply hΨ x hxV
    funext i
    cases i using Fin.cases with
    | zero => simpa [w] using h0
    | succ i => simpa [w, h0] using hi i
  refine ⟨hxV, hw0, funext fun i => ?_⟩
  show w x i.succ / w x 0 = y i
  rw [div_eq_iff hw0]
  exact hi i
end GroundTheory.Heights₂.Heights.Targets
