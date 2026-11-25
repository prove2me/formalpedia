-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.centre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:55.051134+00:00
-- url     : https://prove2.me/submissions/74be4c9a-0c62-4f3c-9678-292e66ccf4f5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContractionFirstOperatorAdjoint
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_X_pderiv_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_apply
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_pE



set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k) (hu : ∀ k ∈ u.support, ¬ inF1 ε k)
    (hr : rdeg ε s ≠ rdeg ε (u.mapDomain pE)) : Λ (monomial s 1 * monomial u 1) = 0 := by
  have hs0 : ∀ k, ¬ inF1 ε k → s k = 0 := fun k hk => by
    by_contra h; exact hk (hs k (Finsupp.mem_support_iff.mpr h))
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hr
  rw [monomial_mul, one_mul]
  have hD : Dop ε c a a (monomial (s + u) (1 : ℂ)) =
      ((∑ i, ((s + u) (a, i, true) : ℂ)) - ∑ i, ((s + u) (a, i, false) : ℂ)) • monomial (s + u) 1 := by
    unfold Dop
    rw [if_pos rfl]
    simp only [X_pderiv_mono, ← Finset.sum_sub_distrib, Finset.sum_smul, sub_smul]
  have h0 := hΛ a a (monomial (s + u) 1)
  rw [hD, map_smul, smul_eq_mul] at h0
  refine (mul_eq_zero.mp h0).resolve_left ?_
  simp only [rdeg, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_not] at ha
  rw [← ne_eq, sub_ne_zero]
  simp only [Finsupp.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  cases hεa : ε a
  · have e1 : ∀ i, u (a, i, true) = 0 := fun i => hu0 _ (by simp [inF1, hεa])
    have e2 : ∀ i, s (a, i, false) = 0 := fun i => hs0 _ (by simp [inF1, hεa])
    simp only [e1, e2, Nat.cast_zero, Finset.sum_const_zero, add_zero, zero_add]
    rw [hεa] at ha
    simp only [Bool.not_false] at ha
    intro h; apply ha; exact_mod_cast h
  · have e1 : ∀ i, u (a, i, false) = 0 := fun i => hu0 _ (by simp [inF1, hεa])
    have e2 : ∀ i, s (a, i, true) = 0 := fun i => hs0 _ (by simp [inF1, hεa])
    simp only [e1, e2, Nat.cast_zero, Finset.sum_const_zero, add_zero, zero_add]
    rw [hεa] at ha
    simp only [Bool.not_true] at ha
    intro h; apply ha; exact_mod_cast h.symm
end PositivityTheory.Rg.Sw.LC.CoreC
