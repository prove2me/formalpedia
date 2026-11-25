-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_sheetDensity_eq_f776bfe0d7d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:21.395729+00:00
-- url     : https://prove2.me/submissions/b45c8eea-bbfe-4535-864c-aaf1ba1dc0fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_continuous_segre_de56826dede7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_analyticOnNhd_of_diffOn_dfa8683cecfc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_apply_eq_of_segre_eq_0b2426e6d1f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_eq_of_segre_f6435d9f6971
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sheet_analyticAt


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
namespace GroundTheory.Heights₂.Heights.PtsPosPartLocal
theorem _root_.solution {P : Ideal (MRing ι)} {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {G : ((Σ k, ι k) → ℂ) → ℝ}
    (hG : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → G (fun p => c p.1 * z p) = G z)
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {U : Set (Fin e → ℂ)}
    {N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hU : IsOpen U)
    (hγ : ∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (hN : IsOpen N) (hNp : ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hq : (y, w) ∈ N) (hw : w ∈ fibre P Ψ y) :
    sheetDensity P Ψ (pot L) G y w = G (γ y) * maDensity (fun j y' => pot L j (γ y')) y := by
  obtain ⟨hyU, hw'⟩ := hNp _ hq
  have hw1 : w = segre (γ y) := hw' hw
  have hsh : IsSheet P Ψ y w γ := ⟨hw1.symm, Filter.eventually_of_mem (hU.mem_nhds hyU) hγ⟩
  have hex : ∃ γ', IsSheet P Ψ y w γ' := ⟨γ, hsh⟩
  have han : AnalyticOnNhd ℂ γ U := analyticOnNhd_of_diffOn hU fun y hy => (hγ y hy).1
  unfold sheetDensity
  rw [dif_pos hex]
  have hc := hex.choose_spec
  set γc := hex.choose
  have hcont : ContinuousAt (fun y' => (y', segre (γc y'))) y :=
    continuousAt_id.prodMk (continuous_segre.continuousAt.comp hc.2.self_of_nhds.1.continuousAt)
  have hN' : ∀ᶠ y' in 𝓝 y, (y', segre (γc y')) ∈ N :=
    hcont.eventually (hN.mem_nhds (by show (y, segre (γc y)) ∈ N; rw [hc.1]; exact hq))
  have hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γc y') := by
    filter_upwards [hN', hc.2] with y' h1 h2
    exact ((hNp _ h1).2 ⟨γc y', h2.2.1, rfl, h2.2.2⟩).symm
  have hblk : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := (hγ y hyU).2.1.1
  rw [apply_eq_of_segre_eq hG hblk (hc.1.trans hw1).symm,
    maDensity_eq_of_segre hL (han y hyU) (sheet_analyticAt osgood hc) hblk hseg]
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
