-- Prove2me | solution 1 for PI.Dv.Tr.real_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:46.066498+00:00
-- url     : https://prove2.me/submissions/f4c6143f-3bae-4460-b517-685ccf567956

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open Formalism.HN
variable {ι : Type} [Fintype ι] {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace PI.Dv.Tr
theorem _root_.solution (v : ι → E) (w : ι → F) (C : ℝ)
    (h : ∀ a : ι → ℤ, ‖∑ i, (a i : ℝ) • w i‖ ≤ C * ‖∑ i, (a i : ℝ) • v i‖) :
    ∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖ := by
  classical
  have hq : ∀ q : ι → ℚ, ‖∑ i, ((q i : ℝ)) • w i‖ ≤ C * ‖∑ i, ((q i : ℝ)) • v i‖ := by
    intro q
    set N : ℕ := ∏ i, (q i).den with hN
    have hNpos : (0 : ℝ) < N := by
      rw [hN]
      exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
    have hint : ∀ i, ∃ a : ℤ, (a : ℝ) = (N : ℝ) * (q i : ℝ) := by
      intro i
      obtain ⟨k, hk⟩ : (q i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(q i).num * k, ?_⟩
      have h1 := Rat.mul_den_eq_num (q i)
      have h2 : ((N : ℚ) * q i) = (((q i).num * k : ℤ) : ℚ) := by
        rw [hk]
        push_cast
        rw [show ((q i).den : ℚ) * (k : ℚ) * q i = (q i * (q i).den) * k by ring, h1]
      have h3 : (((N : ℚ) * q i : ℚ) : ℝ) = ((((q i).num * k : ℤ) : ℚ) : ℝ) := by rw [h2]
      push_cast at h3
      rw [h3]
      push_cast
      ring
    choose a ha using hint
    have hw : ∑ i, (a i : ℝ) • w i = (N : ℝ) • ∑ i, (q i : ℝ) • w i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ha i, mul_smul]
    have hv : ∑ i, (a i : ℝ) • v i = (N : ℝ) • ∑ i, (q i : ℝ) • v i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ha i, mul_smul]
    have := h a
    rw [hw, hv, norm_smul, norm_smul, Real.norm_of_nonneg hNpos.le] at this
    have h' : (N : ℝ) * ‖∑ i, (q i : ℝ) • w i‖ ≤ (N : ℝ) * (C * ‖∑ i, (q i : ℝ) • v i‖) := by
      linarith
    exact le_of_mul_le_mul_left h' hNpos
  have hd : DenseRange (Pi.map fun _ : ι => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hcl : IsClosed {c : ι → ℝ | ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  intro c
  have hc : c ∈ closure (Set.range (Pi.map fun _ : ι => (Rat.cast : ℚ → ℝ))) := by
    rw [hd.closure_range]
    trivial
  exact (closure_minimal (by rintro _ ⟨q, rfl⟩; exact hq q) hcl) hc
end PI.Dv.Tr
