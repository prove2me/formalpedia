-- Prove2me | solution 1 for PI.OpWords.vanish_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:26.516815+00:00
-- url     : https://prove2.me/submissions/acdbc5ff-5886-4281-9b44-33801535f73d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishMain
import Theorems.Thm_PI_OpWords_eval_base
import Theorems.Thm_PI_OpWords_iter_mem
import Theorems.Thm_PI_OpWords_expFormula
import Theorems.Thm_PI_OpWords_rop_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords
theorem _root_.solution {d c : ℕ} (W : Submodule K (Pol K k)) (hW : W ≤ Bihom K k d)
    (hst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) (hwt : ∀ f ∈ W, WtLe K k c f) (hcd : c < d)
    (i0 : Fin k) (S : Finset (Fin k)) :
    ∀ p : Fin k ⊕ Fin k → K, p (Sum.inl i0) ≠ 0 → (∀ b, b ≠ i0 → p (Sum.inl b) ≠ 0 → b ∈ S) →
      ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → ∀ g ∈ W, eval p g = 0 := by
  classical
  induction S using Finset.induction_on
  next =>
    intro p hp0 hS hq g hg
    have hx : ∀ b, b ≠ i0 → p (Sum.inl b) = 0 := by
      intro b hb
      by_contra h
      exact absurd (hS b hb h) (by simp)
    have hxi : p (Sum.inr i0) = 0 := by
      rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [hx b hb, zero_mul])
        (fun h => absurd (Finset.mem_univ i0) h)] at hq
      exact (mul_eq_zero.1 hq).resolve_left hp0
    exact eval_base hcd i0 (hW hg) (hwt g hg) p hx hxi
  next b S hbS ih =>
    intro p hp0 hS hq g hg
    by_cases hpb : p (Sum.inl b) = 0
    · refine ih p hp0 ?_ hq g hg
      intro b' hb' hne
      rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
      · subst h
        exact absurd hpb hne
      · exact h
    by_cases hbi : b = i0
    · refine ih p hp0 ?_ hq g hg
      intro b' hb' hne
      rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
      · exact absurd (h.trans hbi) hb'
      · exact h
    have hib : i0 ≠ b := Ne.symm hbi
    have hshl : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k),
        shiftPt i0 b t y (Sum.inl j) = y (Sum.inl j) + t * (if j = b then y (Sum.inl i0) else 0) := by
      intro t y j
      by_cases h : j = b <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring
    have hshr : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k),
        shiftPt i0 b t y (Sum.inr j) = y (Sum.inr j) - t * (if j = i0 then y (Sum.inr b) else 0) := by
      intro t y j
      by_cases h : j = i0 <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring
    obtain ⟨s, hs⟩ : ∃ s : K, s = -(p (Sum.inl b) / p (Sum.inl i0)) := ⟨_, rfl⟩
    have hq0 : shiftPt i0 b s p (Sum.inl i0) = p (Sum.inl i0) := by
      rw [hshl, if_neg hib, mul_zero, add_zero]
    have hqb : shiftPt i0 b s p (Sum.inl b) = 0 := by
      rw [hshl, if_pos rfl, hs, neg_mul, div_mul_cancel₀ _ hp0]
      ring
    have hqj : ∀ j, j ≠ b → shiftPt i0 b s p (Sum.inl j) = p (Sum.inl j) := by
      intro j hj
      rw [hshl, if_neg hj, mul_zero, add_zero]
    have hquad : ∑ i, shiftPt i0 b s p (Sum.inl i) * shiftPt i0 b s p (Sum.inr i) = 0 := by
      simp only [hshl, hshr, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hbi, hib, if_false, hq]
      ring
    have ihq : ∀ g ∈ W, eval (shiftPt i0 b s p) g = 0 := by
      refine ih _ (by rw [hq0]; exact hp0) ?_ hquad
      intro b' hb' hne
      by_cases hbb : b' = b
      · subst hbb
        exact absurd hqb hne
      · rw [hqj b' hbb] at hne
        rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
        · exact absurd h hbb
        · exact h
    have hback : shiftPt i0 b (-s) (shiftPt i0 b s p) = p := by
      funext v
      rcases v with j | j
      · by_cases h : j = b <;> simp [hshl, h, hib] <;> ring
      · by_cases h : j = i0 <;> simp [hshr, h, hbi] <;> ring
    have hE := expFormula i0 b hib (-s) g
    unfold ExpFormula at hE
    obtain ⟨N, _, hsum⟩ := hE
    rw [← hback, hsum N le_rfl]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [ihq _ (iter_mem W hst i0 b hg n), mul_zero]
end PI.OpWords
