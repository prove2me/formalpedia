-- Prove2me | solution 1 for P2M_CompanionTheory_D_gk_FinalFormK_SmOn_smul__7902115b4004
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:43.91745+00:00
-- url     : https://prove2.me/submissions/4ed3216e-dd04-4171-b71f-2f120f0457c5

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.FinalFormK
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Mat n → (H →L[ℂ] H)} {τ : Mat n → (H' →L[ℂ] H')}
variable {L : Mat n → Prop}
namespace CompanionTheory.D.gk.FinalFormK
namespace SmOn
theorem _root_.solution {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    {A : Set E} {c : E → ℂ} {f : E → V} (hc : SmOn A c) (hf : SmOn A f) : SmOn A fun a => c a • f a := fun a ha => by
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hc a ha
  obtain ⟨U', F', hU', haU', hF', hfF'⟩ := hf a ha
  exact ⟨U ∩ U', fun x => F x • F' x, hU.inter hU', ⟨haU, haU'⟩,
    (hF.mono inter_subset_left).smul (hF'.mono inter_subset_right),
    fun g hg hgA => by simp only [hfF g hg.1 hgA, hfF' g hg.2 hgA]⟩
end SmOn
end CompanionTheory.D.gk.FinalFormK
