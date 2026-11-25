-- Prove2me | solution 1 for PI.GGMatBoundW.eigBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:30.030347+00:00
-- url     : https://prove2.me/submissions/7295e036-e381-4d1b-b713-379bf45c8f1b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GamOneReal
import Theorems.Thm_PI_GGMatBoundW_gam_one_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
namespace PI.GGMatBoundW
theorem _root_.solution (hP : PlaceBound) (hJ : JointEig) (hF : ProdFormula) : EigBound := by
  intro hC hR ι _ Fq _ _ k ψ hψ hq V _ _ _ π w μ hw he
  obtain ⟨W, hW0, hWinv, hWeig, hv⟩ := hJ ι Fq k ψ V π w μ hw he
  choose μv hμv using hv
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hpl : ∀ v, ∃ c : ℝ, μv v = gam (ψ v) (1 : GL (Fin k) (Fq v)) * (c : ℂ) ∧ 0 ≤ c ∧
      c ≤ 1 + 3 / (Fintype.card (Fq v) : ℝ) := by
    intro v
    refine hP hC hR (Fq v) k (ψ v) (hψ v) (hq v) V
      (π.comp (MonoidHom.mulSingle (fun v => GL (Fin k) (Fq v)) v)) W (μv v) hW0 ?_ ?_
    · intro g y hy; exact hWinv _ y hy
    · intro y hy
      rw [← hμv v y hy]
      simp [repGam, placeOp, LinearMap.sum_apply]
  choose c hc using hpl
  have h1 : totOp ψ π x = (∏ v, μv v) • x := hF ι Fq k ψ V π μv x (fun v => hμv v x hxW)
  have h2 : μ = ∏ v, μv v := by
    have h3 := hWeig x hxW
    rw [h1] at h3
    exact (smul_left_injective ℂ hx0 h3).symm
  set g : ι → ℝ := fun v => (Fintype.card (GL (Fin k) (Fq v)) : ℝ) / (cardU (Fq v) k : ℝ) with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hG1 : gamProd ψ (1 : ∀ v, GL (Fin k) (Fq v)) = ((∏ v, g v : ℝ) : ℂ) := by
    unfold gamProd
    push_cast
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Pi.one_apply, gam_one_real]
  refine ⟨(∏ v, g v) * ∏ v, c v, ?_, ?_, ?_⟩
  · rw [h2]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hc v).1, gam_one_real]
  · exact mul_nonneg (Finset.prod_nonneg fun v _ => hg0 v) (Finset.prod_nonneg fun v _ => (hc v).2.1)
  · rw [hG1, Complex.ofReal_re, mul_comm (∏ v, (1 + 3 / (Fintype.card (Fq v) : ℝ)))]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun v _ => (hc v).2.1) (fun v _ => (hc v).2.2))
      (Finset.prod_nonneg fun v _ => hg0 v)
end PI.GGMatBoundW
