-- Prove2me | solution 1 for QualityEncroach.NoCommit.stage3_no_uniform
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:01:32.238362+00:00
-- url     : https://prove2.me/submissions/48875ebc-c2c3-40f9-8505-02c60cedf8af

import Definitions.Def_QualityEncroach_NoCommit_Game
open QualityEncroach.NoCommit
theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w uR qR uM qM : ℝ)
    (huR : 0 < uR) (hqR : 0 < qR) (huM : 0 < uM) (hqM : 0 ≤ qM)
    (hopt : ∀ uM' qM' : ℝ, 0 < uM' → 0 ≤ qM' →
      mfrPayoff k c ⟨w, uR, qR, uM', qM'⟩ ≤ mfrPayoff k c ⟨w, uR, qR, uM, qM⟩) :
    ¬ (uM = uR ∧ 0 < qM) := by
  rintro ⟨heq, hqpos⟩
  subst uM
  let e := min (uR / 2) (qR / (4*k))
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have heu : e ≤ uR/2 := min_le_left _ _
  have heq : e ≤ qR/(4*k) := min_le_right _ _
  have hek : 4*k*e ≤ qR := by
    have := (le_div_iff₀ (by positivity : 0 < 4*k)).mp heq
    nlinarith
  have hp : 0 < uR + e := by linarith
  have hm : 0 < uR - e := by linarith
  have hplus := hopt (uR+e) qM hp hqM
  have hminus := hopt (uR-e) qM hm hqM
  have hi : mfrPayoff k c ⟨w,uR,qR,uR+e,qM⟩ +
      mfrPayoff k c ⟨w,uR,qR,uR-e,qM⟩ -
      2 * mfrPayoff k c ⟨w,uR,qR,uR,qM⟩ = qM*e*(qR-2*k*e) := by
    simp only [mfrPayoff, priceM, if_pos (show uR ≤ uR+e by linarith),
      if_neg (show ¬uR ≤ uR-e by linarith), if_pos (le_refl uR)]
    ring
  have hz : 0 < qM*e*(qR-2*k*e) := mul_pos (mul_pos hqpos he) (by nlinarith)
  linarith
