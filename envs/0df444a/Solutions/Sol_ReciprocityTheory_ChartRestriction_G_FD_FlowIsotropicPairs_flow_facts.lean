-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.flow_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:02.289243+00:00
-- url     : https://prove2.me/submissions/06ea91e2-b556-427e-b798-f8d20e178955

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_Hf_flag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_hpe_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_maj_flag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_maj_flowV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_flowDomainCriterion_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
theorem _root_.solution (X : Data E r) {ξ : Fin r → E} {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.FramesOverBasis ξ)
    (e : X.Ψ → Fin r → ℂ) (hiso : X.IsIsoV e)
    (heξ : ∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0)
    (hHe : ∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) (hce : ∀ τ, X.c τ * X.maj z0 τ (e τ) = 1)
    {z : Frame X.Ψ r} (hz : z ∈ X.dom) (hf : X.SameFlag z0 z) :
    (∀ τ, X.ttV e z τ = 1) ∧ X.flowV e (fun _ => -(I / 2)) z ∈ X.FramesOverBasis ξ := by
  have httv : ∀ τ, X.ttV e z τ = 1 := by
    intro τ
    rw [Data.ttV, maj_flag X hz0.1 hz hf, hce τ, div_one]
  have hTz : X.flowV e (fun _ => -(I / 2)) z ∈ X.dom := by
    refine (flowDomainCriterion_holds r X e hiso z hz (fun _ => -(I / 2))).1.mpr fun τ => ?_
    rw [httv τ]
    norm_num
  refine ⟨httv, hTz, fun τ => ?_⟩
  have hve : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (e τ) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm, heξ τ, map_zero]
  have hpe : hermC τ.1 X.Gm (X.ppos z τ (Data.emb τ.1 ξ)) (e τ) = 0 :=
    hpe_of X hz τ (Data.emb τ.1 ξ) (e τ) (by rw [Hf_flag X hz0.1 hz hf]; exact hHe τ) (heξ τ)
  rw [maj_flowV X e _ hz hTz τ _ hve hpe, maj_flag X hz0.1 hz hf, hz0.2 τ]
end ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
