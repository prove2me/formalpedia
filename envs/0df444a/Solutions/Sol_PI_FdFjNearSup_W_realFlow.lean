-- Prove2me | solution 1 for PI.FdFjNearSup.W.realFlow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:26.860894+00:00
-- url     : https://prove2.me/submissions/944a3370-c4bf-469e-b207-ea74421e368a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf
import Theorems.Thm_PI_FdFjNearSup_W_isIsoV_embV
import Theorems.Thm_PI_FdFjNearSup_W_nfac_pos
import Theorems.Thm_PI_FdFjNearSup_W_flow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FdFjNearSup PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace PI.FdFjNearSup.W
theorem _root_.solution {r : ℕ} (X : Data E r) (h1 : FlowDomainCriterion (E := E))
    (h2 : FlowNormRatio (E := E)) {ξ : Fin r → E} (hξ : X.IsIso ξ) (la : Wt X.Ψ r)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) (s : X.Ψ → ℝ) :
    X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom ∧
      X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x := by
  rw [flow_eq]
  have he := isIsoV_embV X hξ
  have hd : X.flowV (X.embV ξ) (fun τ => (s τ : ℂ)) x ∈ X.dom :=
    (h1 r X _ he x hx _).1.2 fun τ => by simp
  refine ⟨hd, ?_⟩
  obtain ⟨hlo, hhi⟩ := h2 r X _ he la x hx _ hd
  simp only [Complex.ofReal_im, zero_div, add_zero, inv_one, min_self, max_self,
    Real.one_rpow, Finset.prod_const_one] at hlo hhi
  have hn := nfac_pos X la hd
  have heq := le_antisymm hhi hlo
  rw [div_eq_one_iff_eq hn.ne'] at heq
  exact heq.symm
end PI.FdFjNearSup.W
