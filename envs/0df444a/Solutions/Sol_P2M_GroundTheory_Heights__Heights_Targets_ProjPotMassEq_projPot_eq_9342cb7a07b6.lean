-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_projPot_eq_9342cb7a07b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:42:25.440553+00:00
-- url     : https://prove2.me/submissions/d7363a86-9a97-44ff-8990-ada096962354

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_blockSum_pos_f3a6ed830dc6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_sqSum_pos_28c025ccad4a
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
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
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)}
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
theorem _root_.solution (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (b z : V)
    (hzb : z.1 ∈ R.U b.1) (hz : Ψ (segre (R.lift z.1 z.1)) ≠ 0) :
    (projPot R Ψ V).φ b z = (multiprojPot R V).φ b z + uFun R Ψ V z := by
  obtain ⟨c, hc, hcz⟩ := R.compat b.1 z.1 z.1 ⟨hzb, R.mem_U z.1⟩
  have hm := (R.mem z.1 z.1 (R.mem_U z.1)).1
  have hc2 : ∀ k, ‖c k‖ ^ 2 ≠ 0 := fun k => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  have hS : ∀ k, ∑ i, ‖R.lift b.1 z.1 ⟨k, i⟩‖ ^ 2 =
      ‖c k‖ ^ 2 * ∑ i, ‖R.lift z.1 z.1 ⟨k, i⟩‖ ^ 2 := by
    intro k
    rw [hcz]
    simp [mul_pow, Finset.mul_sum]
  have hseg : segre (R.lift b.1 z.1) = (∏ k, c k) • segre (R.lift z.1 z.1) := by
    rw [hcz]
    funext i
    simp only [segre, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  have hN : ∑ l, ‖Ψ (segre (R.lift b.1 z.1)) l‖ ^ 2 =
      ‖∏ k, c k‖ ^ 2 * ∑ l, ‖Ψ (segre (R.lift z.1 z.1)) l‖ ^ 2 := by
    rw [hseg, map_smul]
    simp [mul_pow, Finset.mul_sum]
  have hsum : ∑ k, Real.log (∑ i, ‖R.lift b.1 z.1 ⟨k, i⟩‖ ^ 2) =
      ∑ k, Real.log (‖c k‖ ^ 2) + ∑ k, Real.log (∑ i, ‖R.lift z.1 z.1 ⟨k, i⟩‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      rw [hS k, Real.log_mul (hc2 k) (blockSum_pos hm k).ne']
  have hprod : Real.log (‖∏ k, c k‖ ^ 2) = ∑ k, Real.log (‖c k‖ ^ 2) := by
    rw [norm_prod, ← Finset.prod_pow, Real.log_prod fun k _ => hc2 k]
  simp only [uFun, projPot, multiprojPot]
  rw [hN, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2
    (Finset.prod_ne_zero_iff.2 fun k _ => hc k))) (sqSum_pos hz).ne', hsum, hprod]
  ring
end GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
