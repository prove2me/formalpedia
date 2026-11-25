-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_abs_sub_le_of_unit_steps_95b851164d45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:54:40.707099+00:00
-- url     : https://prove2.me/submissions/3f06134b-2e29-4471-b866-ea9b04f33004

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_sum_add_pi_single_one_3a9c5801f689

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (G : (K → ℕ) → ℤ) (A : ℕ) (D : ℝ) (hD : 0 ≤ D) (s : ℕ) :
    ∀ a : K → ℕ, ∑ k, a k = s → (∀ k, A ≤ a k) →
      (∀ (m : K → ℕ) (k : K), (∀ j, A ≤ m j) → ∑ j, m j + 1 ≤ s →
        |((G (m + Pi.single k 1) : ℝ) - G m)| ≤ D) →
      |((G a : ℝ) - G (fun _ => A))| ≤ D * s := by
  induction s with
  | zero =>
    intro a hs ha _
    have : a = fun _ => A := by
      funext k
      have h0 := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
      have := ha k
      omega
    subst this
    simp
  | succ s ih =>
    intro a hs ha hstep
    by_cases hall : ∀ k, a k = A
    · have : a = fun _ => A := funext hall
      subst this
      simp only [sub_self, abs_zero]
      positivity
    · push Not at hall
      obtain ⟨k, hk⟩ := hall
      have hk' : A < a k := lt_of_le_of_ne (ha k) (Ne.symm hk)
      set m : K → ℕ := a - Pi.single k 1 with hm_def
      have hma : m + Pi.single k 1 = a := by
        funext j
        by_cases h : j = k
        · subst h; simp [m]; omega
        · simp [m, h]
      have hmA : ∀ j, A ≤ m j := by
        intro j
        by_cases h : j = k
        · subst h; simp [m]; omega
        · simp [m, h]; exact ha j
      have hms : ∑ j, m j = s := by
        have := sum_add_pi_single_one m k
        rw [hma, hs] at this
        omega
      have h1 := ih m hms hmA (fun m' k' hm' hs' => hstep m' k' hm' (by omega))
      have h2 := hstep m k hmA (by omega)
      rw [hma] at h2
      calc |((G a : ℝ) - G (fun _ => A))|
          = |((G a : ℝ) - G m) + ((G m : ℝ) - G (fun _ => A))| := by ring_nf
        _ ≤ |((G a : ℝ) - G m)| + |((G m : ℝ) - G (fun _ => A))| := abs_add_le _ _
        _ ≤ D + D * s := add_le_add h2 h1
        _ = D * ((s + 1 : ℕ) : ℝ) := by push_cast; ring
end GroundTheory.Heights₂.Heights.HilbertSamuel
