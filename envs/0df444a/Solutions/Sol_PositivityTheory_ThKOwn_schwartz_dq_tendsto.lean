-- Prove2me | solution 1 for PositivityTheory.ThKOwn.schwartz_dq_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:22.654854+00:00
-- url     : https://prove2.me/submissions/2144ebe8-e4b3-40ba-bc29-8e6147017914

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_SchwartzDqTendsto
import Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_bound_mul_translate
import Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_seminorm_remainder


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open Filter Topology GlobalTheory.CompanionTheory.OM.SchDiff
open scoped SchwartzMap LineDeriv ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKOwn
theorem _root_.solution (g : 𝓢(V, ℂ)) (a : V) :
    Tendsto (fun t : ℝ => t⁻¹ • (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g - g)) (𝓝[≠] 0) (𝓝 (∂_{a} g)) := by
  let l : ℝ →L[ℝ] V := ContinuousLinearMap.toSpanSingleton ℝ a
  let M : ℝ × V →L[ℝ] V := ContinuousLinearMap.snd ℝ ℝ V + l ∘L ContinuousLinearMap.fst ℝ ℝ V
  have hM : ∀ q : ℝ × V, M q = q.2 + q.1 • a := fun q => rfl
  have hF : ContDiff ℝ ∞ (fun q : ℝ × V => (1 : ℂ) * g (q.2 + l q.1)) :=
    contDiff_const.mul ((g.smooth ⊤).comp M.contDiff)
  have hb := bound_mul_translate (A := fun _ : ℝ × V => (1 : ℂ)) (Function.HasTemperateGrowth.const _) g l 0
  have hrem := seminorm_remainder hF 0 hb (fun t => SchwartzMap.compSubConstCLM ℂ (-(t • a)) g) (fun t => t • ∂_{a} g)
    (fun p => by
      funext x
      rw [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, one_mul]
      rfl)
    (fun v => by
      funext x
      have e : (fun q : ℝ × V => (1 : ℂ) * g (q.2 + l q.1)) = ⇑g ∘ M := by
        funext q
        rw [one_mul]
        rfl
      rw [e, ((g.hasFDerivAt (M (0, x))).comp (0, x) M.hasFDerivAt).fderiv]
      simp [hM, SchwartzMap.lineDerivOp_apply_eq_fderiv])
  rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨C, hC⟩ := hrem k n
  have h1 : Tendsto (fun t : ℝ => C * ‖t‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℝ)).const_mul C
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h1.eventually (gt_mem_nhds hε)),
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with t ht h2 h3
  have ht0 : t ≠ 0 := ht
  have h4 := hC t (mem_closedBall_zero_iff.1 h3)
  have e : t⁻¹ • (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g - g) - ∂_{a} g =
      ((t⁻¹ : ℝ) : ℂ) • (SchwartzMap.compSubConstCLM ℂ (-((0 + t) • a)) g -
        SchwartzMap.compSubConstCLM ℂ (-((0 : ℝ) • a)) g - t • ∂_{a} g) := by
    ext x
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.compSubConstCLM_apply, zero_add, zero_smul,
      neg_zero, sub_zero, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
    field_simp
  rw [SchwartzMap.schwartzSeminormFamily_apply, e, map_smul_eq_mul, Complex.norm_real, norm_inv]
  refine lt_of_le_of_lt ?_ h2
  have hn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  calc _ ≤ ‖t‖⁻¹ * (C * ‖t‖ ^ 2) := by gcongr
    _ = _ := by field_simp
end PositivityTheory.ThKOwn
