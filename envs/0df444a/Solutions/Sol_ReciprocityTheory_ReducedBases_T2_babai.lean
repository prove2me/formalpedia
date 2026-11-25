-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.babai
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:49.888989+00:00
-- url     : https://prove2.me/submissions/2fcd06b7-df63-41d5-9885-b9bf33785776

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_sub
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_eq_zero_of
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) {N : ℝ} (hN : 0 < N)
    (t : ℕ) (ht : t ≤ d) : ∃ w : Fin d → ℤ, (∀ l : Fin d, t ≤ l.val → w l = 0) ∧
      ∀ j : Fin d, j.val < t → |nu b (fun l => c l - N * (w l : ℝ)) j| ≤ N / 2 := by
  induction t generalizing c with
  | zero =>
    exact ⟨0, fun l _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ t ih =>
    have htd : t < d := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round (nu b c ⟨t, htd⟩ / N) := ⟨_, rfl⟩
    obtain ⟨w, hw0, hw⟩ := ih (fun l => c l - N * (if l = ⟨t, htd⟩ then (k : ℝ) else 0)) (by omega)
    refine ⟨fun l => w l + if l = ⟨t, htd⟩ then k else 0, ?_, ?_⟩
    · intro l hl
      have hne : l ≠ ⟨t, htd⟩ := by
        intro h
        rw [h] at hl
        simp at hl
      simp [hw0 l (by omega), hne]
    · intro j hj
      have hnu : nu b (fun l => c l - N * ((w l + if l = ⟨t, htd⟩ then k else 0 : ℤ) : ℝ)) j =
          nu b (fun l => (c l - N * (if l = ⟨t, htd⟩ then (k : ℝ) else 0)) - N * (w l : ℝ)) j := by
        congr 1
        funext l
        split_ifs <;> push_cast <;> ring
      by_cases hjt : j.val < t
      · exact (le_of_eq (congrArg abs hnu)).trans (hw j hjt)
      · obtain rfl : j = ⟨t, htd⟩ := Fin.ext (by simp; omega)
        have hval : nu b (fun l => c l - N * ((w l + if l = ⟨t, htd⟩ then k else 0 : ℤ) : ℝ)) ⟨t, htd⟩ =
            nu b c ⟨t, htd⟩ - N * (k : ℝ) := by
          rw [hnu, nu_sub, nu_eq_zero_of b (fun l => ((w l : ℤ) : ℝ)) ⟨t, htd⟩
            (fun l hl => by simp [hw0 l hl]), mul_zero, sub_zero, nu_sub,
            nu_top b hb (fun l => if l = ⟨t, htd⟩ then (k : ℝ) else 0) ⟨t, htd⟩
              (fun l hl => if_neg (ne_of_gt hl))]
          simp
        have hN0 : N ≠ 0 := hN.ne'
        have hr := abs_sub_round (nu b c ⟨t, htd⟩ / N)
        have e3 : N * (nu b c ⟨t, htd⟩ / N) = nu b c ⟨t, htd⟩ := by field_simp
        have e2 : nu b c ⟨t, htd⟩ - N * (k : ℝ) =
            N * (nu b c ⟨t, htd⟩ / N - (round (nu b c ⟨t, htd⟩ / N) : ℝ)) := by
          rw [hk, mul_sub, e3]
        rw [hval, e2, abs_mul, abs_of_pos hN]
        calc N * |nu b c ⟨t, htd⟩ / N - (round (nu b c ⟨t, htd⟩ / N) : ℝ)| ≤ N * (1 / 2) :=
              mul_le_mul_of_nonneg_left hr hN.le
          _ = N / 2 := by ring
end ReciprocityTheory.ReducedBases.T2
