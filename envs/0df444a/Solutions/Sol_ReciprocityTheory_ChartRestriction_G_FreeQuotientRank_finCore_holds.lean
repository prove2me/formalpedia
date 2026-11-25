-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finCore_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:03:23.693723+00:00
-- url     : https://prove2.me/submissions/7f5249a7-57e0-4078-9784-c493dbd6dadf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCoreSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DiscPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_UnitPointLiftBall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_UnitPointLiftBall_exists_unit_point
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_disc_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution : FinCoreStatement := by
  unfold FinCoreStatement
  intro K _ _ _ K₀ hK₀ S hS hSr hSu ι _ δ hδ hδ1 P b hPb hconv

  have step1 : ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 →
      ∀ n, ‖MvPolynomial.eval x (P n)‖ ≤ 1 ∧ (n < 0 → MvPolynomial.eval x (P n) = 0) := by
    intro x hx hxδ
    have hd := disc_holds
    unfold DiscStatement at hd
    refine hd K K₀ hK₀ S hS hSr (fun n => MvPolynomial.eval x (P n)) b ?_ ?_
    · intro n hn
      show MvPolynomial.eval x (P n) = 0
      rw [hPb n hn, map_zero]
    · intro t ht
      refine ⟨(hconv t ht x hx hxδ).1, ?_⟩
      intro τ hτ hτ1
      exact (hconv (t * τ) (hSu t ht τ hτ hτ1) x hx hxδ).2

  have key : ∀ p : MvPolynomial ι K, p ≠ 0 → ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) ∧
      ‖MvPolynomial.eval x δ‖ = 1 ∧ ∃ μ, ‖MvPolynomial.eval x p‖ = ‖MvPolynomial.coeff μ p‖ ∧
        MvPolynomial.coeff μ p ≠ 0 ∧ ∀ ν, ‖MvPolynomial.coeff ν p‖ ≤ ‖MvPolynomial.coeff μ p‖ := by
    intro p hp
    have hne : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact hp (MvPolynomial.support_eq_empty.mp h)
    obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image p.support
      (fun ν => ‖MvPolynomial.coeff ν p‖) hne
    have hc : MvPolynomial.coeff μ p ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
    have hmax' : ∀ ν, ‖MvPolynomial.coeff ν p‖ ≤ ‖MvPolynomial.coeff μ p‖ := by
      intro ν
      by_cases hν : ν ∈ p.support
      · exact hmax ν hν
      · have h0 : MvPolynomial.coeff ν p = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hν
        rw [h0, norm_zero]
        exact norm_nonneg _
    have hcpos : 0 < ‖MvPolynomial.coeff μ p‖ := norm_pos_iff.mpr hc
    have hQ : ∀ ν, ‖MvPolynomial.coeff ν
        (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p)‖ ≤ 1 := by
      intro ν
      rw [MvPolynomial.coeff_C_mul, norm_mul, norm_inv]
      calc ‖MvPolynomial.coeff μ p‖⁻¹ * ‖MvPolynomial.coeff ν p‖
          ≤ ‖MvPolynomial.coeff μ p‖⁻¹ * ‖MvPolynomial.coeff μ p‖ := by
            gcongr
            exact hmax' ν
        _ = 1 := inv_mul_cancel₀ hcpos.ne'
    have hQ1 : ∃ ν, ‖MvPolynomial.coeff ν
        (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p)‖ = 1 := by
      refine ⟨μ, ?_⟩
      rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, norm_one]
    obtain ⟨x, hx, hxQ, hxδ⟩ := UnitPointLiftBall.exists_unit_point K₀ hK₀
      (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p) δ hQ hQ1 hδ hδ1
    refine ⟨x, fun i => ⟨(hx i).1, (hx i).2.le⟩, hxδ, μ, ?_, hc, hmax'⟩
    have he : MvPolynomial.eval x p = MvPolynomial.coeff μ p *
        MvPolynomial.eval x (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p) := by
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_inv_cancel_left₀ hc]
    rw [he, norm_mul, hxQ, mul_one]
  intro n
  constructor
  · intro μ
    by_contra hlt
    push_neg at hlt
    have hp : P n ≠ 0 := by
      intro h
      rw [h, MvPolynomial.coeff_zero, norm_zero] at hlt
      linarith
    obtain ⟨x, hx, hxδ, ν, hev, -, hmax⟩ := key (P n) hp
    have h1 := (step1 x hx hxδ n).1
    rw [hev] at h1
    linarith [hmax μ]
  · intro hn
    by_contra hp
    obtain ⟨x, hx, hxδ, ν, hev, hc, -⟩ := key (P n) hp
    have h0 := (step1 x hx hxδ n).2 hn
    rw [h0, norm_zero] at hev
    exact hc (norm_eq_zero.mp hev.symm)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
