-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_continuousAt_levi_self_0e89eed5c63b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:41:31.823602+00:00
-- url     : https://prove2.me/submissions/288ce952-9140-474b-a42c-5d9de500208f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StChartLeviThGe
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartLeviThGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartLeviThGe_levi_base_indep_c0ed9c553384
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_analyticAt_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (contDiffOn_compat analyticAt_compat)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
variable {om : LocPot X}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
theorem _root_.solution (hpot : IsPotential A om) {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}
    (hψ : IsCompatChart A ψ) {p0 : X} (hp0 : p0 ∈ ψ.source) (v0 : Fin D → ℂ) :
    ContinuousAt (fun q : X × (Fin D → ℂ) => levi (om.φ q.1 ∘ ψ.symm) (ψ q.1) q.2) (p0, v0) := by
  have hV : IsOpen (ψ.target ∩ ψ.symm ⁻¹' om.U p0) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (om.isOpen_U p0)
  have hcd : ContDiffOn ℝ 2 (om.φ p0 ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' om.U p0) :=
    (contDiffOn_compat hψ (om.isOpen_U p0) (hpot.1 p0)).of_le (WithTop.coe_le_coe.2 le_top)
  have hc := continuousOn_levi hV hcd
  have hmem : (ψ p0, v0) ∈ (ψ.target ∩ ψ.symm ⁻¹' om.U p0) ×ˢ (Set.univ : Set (Fin D → ℂ)) :=
    ⟨⟨ψ.map_source hp0, by simpa [ψ.left_inv hp0] using om.mem_U p0⟩, trivial⟩
  have h1 : ContinuousAt (fun r : (Fin D → ℂ) × (Fin D → ℂ) => levi (om.φ p0 ∘ ψ.symm) r.1 r.2)
      (ψ p0, v0) := hc.continuousAt ((hV.prod isOpen_univ).mem_nhds hmem)
  have h2 : ContinuousAt (fun q : X × (Fin D → ℂ) => (ψ q.1, q.2)) (p0, v0) :=
    ((ψ.continuousAt hp0).comp continuousAt_fst).prodMk continuousAt_snd
  refine (ContinuousAt.comp (g := fun r : (Fin D → ℂ) × (Fin D → ℂ) => levi (om.φ p0 ∘ ψ.symm) r.1 r.2)
    (f := fun q : X × (Fin D → ℂ) => (ψ q.1, q.2)) h1 h2).congr ?_
  have hN : (om.U p0 ∩ ψ.source) ×ˢ (Set.univ : Set (Fin D → ℂ)) ∈ 𝓝 (p0, v0) :=
    (((om.isOpen_U p0).inter ψ.open_source).prod isOpen_univ).mem_nhds ⟨⟨om.mem_U p0, hp0⟩, trivial⟩
  filter_upwards [hN] with q hq
  exact (levi_base_indep hpot hψ (om.mem_U q.1) hq.1.1 hq.1.2 q.2).symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
