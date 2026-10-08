-- Prove2me | solution 1 for RevShareCoord.Wholesale.qstar_lt_qI
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:21:46.807468+00:00
-- url     : https://prove2.me/submissions/f358c4f8-166f-45c4-ab99-0c05bd0f4998

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

set_option autoImplicit false

namespace QsLtAuxD25a
open RevShareCoord.Wholesale

/-- `R'` is strictly decreasing on `[0, ∞)` (from strict concavity of `R`). -/
theorem R'_lt (M : Model) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : M.R' y < M.R' x := by
  have hy : (0:ℝ) ≤ y := le_trans hx hxy.le
  have h1 := M.strictConcave.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 hx)
    (Set.mem_Ici.2 hy) hxy (M.hasDeriv y hy)
  have h2 := M.strictConcave.slope_lt_of_hasDerivWithinAt (Set.mem_Ici.2 hx)
    (Set.mem_Ici.2 hy) hxy (M.hasDeriv x hx)
  linarith

theorem qI_pos (M : Model) (qI : ℝ) (hqI0 : 0 ≤ qI)
    (hqI : IsMaxOn (chainProfit M.R M.c) (Set.Ici 0) qI) : 0 < qI := by
  rcases hqI0.lt_or_eq with h | h
  · exact h
  exfalso
  subst h
  have hd : HasDerivWithinAt M.R (M.R' 0) (Set.Ioi 0) 0 :=
    (M.hasDeriv 0 le_rfl).mono Set.Ioi_subset_Ici_self
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hd
  have hev : ∀ᶠ q in nhdsWithin (0:ℝ) (Set.Ioi 0), M.c < slope M.R 0 q :=
    hd.eventually (lt_mem_nhds M.viable)
  have hev2 : ∀ᶠ q in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < q := self_mem_nhdsWithin
  obtain ⟨q, hq1, hq2⟩ := (hev.and hev2).exists
  have hmax := isMaxOn_iff.1 hqI q (Set.mem_Ici.2 hq2.le)
  simp only [chainProfit, M.R_zero, zero_mul, sub_zero] at hmax
  rw [slope_def_field, M.R_zero, sub_zero, sub_zero, lt_div_iff₀ hq2] at hq1
  linarith

theorem qI_foc (M : Model) (qI : ℝ) (hqI0 : 0 ≤ qI)
    (hqI : IsMaxOn (chainProfit M.R M.c) (Set.Ici 0) qI) : M.R' qI = M.c := by
  have hpos := qI_pos M qI hqI0 hqI
  have hd : HasDerivAt (fun q => M.R q - q * M.c) (M.R' qI - 1 * M.c) qI :=
    ((M.hasDeriv qI hqI0).hasDerivAt (Ici_mem_nhds hpos)).sub
      ((hasDerivAt_id qI).mul_const M.c)
  have hlm : IsLocalMax (fun q => M.R q - q * M.c) qI :=
    hqI.isLocalMax (Ici_mem_nhds hpos)
  have := hlm.hasDerivAt_eq_zero hd
  linarith

theorem qs_pos (M : Model) (qs qI : ℝ) (hqs0 : 0 ≤ qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs)
    (hqI0 : 0 ≤ qI) (hqI : IsMaxOn (chainProfit M.R M.c) (Set.Ici 0) qI) : 0 < qs := by
  have hpos := qI_pos M qI hqI0 hqI
  have hfoc := qI_foc M qI hqI0 hqI
  have hlt := R'_lt M (x := qI / 2) (y := qI) (by linarith) (by linarith)
  have hmax := isMaxOn_iff.1 hqs (qI / 2) (Set.mem_Ici.2 (by linarith))
  simp only [supplierProfit, inducingPrice] at hmax
  have hp : 0 < qI / 2 * (M.R' (qI / 2) - M.c) := mul_pos (by linarith) (by linarith)
  rcases hqs0.lt_or_eq with h | h
  · exact h
  · subst h
    simp at hmax
    linarith

end QsLtAuxD25a

open RevShareCoord.Wholesale in
theorem solution (M : Model) (qs qI : ℝ) (hqs0 : 0 ≤ qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs)
    (hqI0 : 0 ≤ qI) (hqI : IsMaxOn (chainProfit M.R M.c) (Set.Ici 0) qI) :
    0 < qs ∧ qs < qI := by
  have hpos := QsLtAuxD25a.qs_pos M qs qI hqs0 hqs hqI0 hqI
  have hIpos := QsLtAuxD25a.qI_pos M qI hqI0 hqI
  have hfI := QsLtAuxD25a.qI_foc M qI hqI0 hqI
  have hlt := QsLtAuxD25a.R'_lt M (x := qI / 2) (y := qI) (by linarith) (by linarith)
  have hmax := isMaxOn_iff.1 hqs (qI / 2) (Set.mem_Ici.2 (by linarith))
  simp only [supplierProfit, inducingPrice] at hmax
  have hp : 0 < qI / 2 * (M.R' (qI / 2) - M.c) := mul_pos (by linarith) (by linarith)
  have hR : M.c < M.R' qs := by
    by_contra hc
    push_neg at hc
    have : qs * (M.R' qs - M.c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hqs0 (by linarith)
    linarith
  refine ⟨hpos, ?_⟩
  by_contra hc
  push_neg at hc
  rcases hc.lt_or_eq with h | h
  · have := QsLtAuxD25a.R'_lt M hqI0 h
    linarith
  · rw [h] at hfI
    linarith
