-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:05.689404+00:00
-- url     : https://prove2.me/submissions/557362b3-8846-4d24-a262-a4e3731485fa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (A : Mc n) (f : Fin n → ℝ) (K : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ K / (f i * f j)) : ‖A.det‖ ≤ (Nat.factorial n : ℝ) * (K ^ n / (∏ i, f i) ^ 2) := by
  rw [Matrix.det_apply']
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖ ≤ K ^ n / (∏ i, f i) ^ 2 := by
    intro σ
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [norm_mul, hs, one_mul, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ i, K / (f (σ i) * f i) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hA _ _)
      _ = K ^ n / (∏ i, f i) ^ 2 := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_mul_distrib, Equiv.prod_comp σ f, sq]
  calc ‖∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), K ^ n / (∏ i, f i) ^ 2 := Finset.sum_le_sum fun σ _ => hterm σ
    _ = (Nat.factorial n : ℝ) * (K ^ n / (∏ i, f i) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
end PositivityTheory.Rg.Sw.WR.K.GB
