-- Prove2me | solution 1 for PI.DvRows.norm_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:11.334833+00:00
-- url     : https://prove2.me/submissions/f394137c-b971-40f9-b9c6-802c9b14071c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_norm_embedding_eq_zpow
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
namespace PI.DvRows
theorem _root_.solution : NormFinsum := by
  intro K _ _ x hx
  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun v => ‖FinitePlace.embedding v x‖ with hf
  have hprod : ∏ᶠ v, f v = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹ := by
    have h := FinitePlace.prod_eq_inv_abs_norm (K := K) hx
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply] at h
    rw [hf, h]
    push_cast
    rfl
  have hfin : (Function.mulSupport f).Finite := by
    have h := FinitePlace.hasFiniteMulSupport (K := K) hx
    have e : Function.mulSupport f = FinitePlace.equivHeightOneSpectrum.symm ⁻¹'
        Function.mulSupport (fun w : FinitePlace K => w x) := by
      ext v
      simp only [f, Function.mem_mulSupport, Set.mem_preimage,
        FinitePlace.equivHeightOneSpectrum_symm_apply]
    rw [e]
    exact Set.Finite.preimage (Equiv.injective _).injOn h
  set s := hfin.toFinset with hs
  have hN : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := fun v => by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hfs : ∀ v, v ∉ s → vAdd v x = 0 := by
    intro v hv
    rw [hs, Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not, hf] at hv
    dsimp only at hv
    rw [norm_embedding_eq_zpow v hx] at hv
    have h2 := congrArg Real.log hv
    rw [Real.log_zpow, Real.log_one] at h2
    have hl : 0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) := Real.log_pos (hN v)
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact_mod_cast neg_eq_zero.1 (by exact_mod_cast h3)
    · exact absurd h3 hl.ne'
  have hlog : ∑ v ∈ s, Real.log (Ideal.absNorm v.asIdeal : ℝ) * (-(vAdd v x : ℝ)) =
      -Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    have h := congrArg Real.log hprod
    rw [finprod_eq_prod_of_mulSupport_subset f (s := s) (by
      intro v hv; rw [hs, Finset.mem_coe, Set.Finite.mem_toFinset]; exact hv)] at h
    rw [Real.log_prod (fun v _ => by
      rw [hf]; dsimp only; rw [norm_embedding_eq_zpow v hx]
      exact (zpow_pos (by linarith [hN v]) _).ne'), Real.log_inv] at h
    rw [← h]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hf]; dsimp only
    rw [norm_embedding_eq_zpow v hx, Real.log_zpow]
    push_cast
    ring
  rw [finsum_eq_sum_of_support_subset (s := s)]
  · unfold lw
    have e : ∑ v ∈ s, Real.log (Ideal.absNorm v.asIdeal : ℝ) / (Module.finrank ℚ K : ℝ) *
        (vAdd v x : ℝ) = (∑ v ∈ s, Real.log (Ideal.absNorm v.asIdeal : ℝ) * (-(vAdd v x : ℝ))) *
          (-1) / (Module.finrank ℚ K : ℝ) := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [e, hlog]
    ring
  · intro v hv
    rw [Function.mem_support] at hv
    by_contra hc
    apply hv
    rw [hfs v hc]
    simp
end PI.DvRows
