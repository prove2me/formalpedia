-- Prove2me | solution 1 for RevShareCoord.Wholesale.qstar_vs_half_qI
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:46:48.517142+00:00
-- url     : https://prove2.me/submissions/8dd3ff32-5b13-4ad0-b46c-52b58330fbb8

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

set_option autoImplicit false

namespace QsHalfAux27c0
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

theorem qs_foc (M : Model) (qs : ℝ) (hpos : 0 < qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs) :
    M.R' qs - M.c + qs * M.R'' qs = 0 := by
  have hd : HasDerivAt (fun q => q * (M.R' q - M.c)) (1 * (M.R' qs - M.c) + qs * M.R'' qs) qs :=
    (hasDerivAt_id qs).mul ((M.hasDeriv2 qs hpos).sub_const M.c)
  have hlm : IsLocalMax (fun q => q * (M.R' q - M.c)) qs :=
    hqs.isLocalMax (Ici_mem_nhds hpos)
  have := hlm.hasDerivAt_eq_zero hd
  linarith

end QsHalfAux27c0

open RevShareCoord.Wholesale in
theorem solution (M : Model) (qs qI : ℝ) (hqs0 : 0 ≤ qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs)
    (hqI0 : 0 ≤ qI) (hqI : IsMaxOn (chainProfit M.R M.c) (Set.Ici 0) qI) :
    (ConvexOn ℝ (Set.Ici 0) M.R' → 2 * qs ≤ qI) ∧
      (ConcaveOn ℝ (Set.Ici 0) M.R' → qI ≤ 2 * qs) ∧
      (StrictConvexOn ℝ (Set.Ici 0) M.R' → 2 * qs < qI) ∧
      (StrictConcaveOn ℝ (Set.Ici 0) M.R' → qI < 2 * qs) := by
  have hpos := QsHalfAux27c0.qs_pos M qs qI hqs0 hqs hqI0 hqI
  have hfI := QsHalfAux27c0.qI_foc M qI hqI0 hqI
  have hfs := QsHalfAux27c0.qs_foc M qs hpos hqs
  have hm1 : qs ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 hqs0
  have hm2 : 2 * qs ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith)
  have hlt : qs < 2 * qs := by linarith
  have hd := M.hasDeriv2 qs hpos
  have e : 2 * qs - qs = qs := by ring
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hs := h.le_slope_of_hasDerivAt hm1 hm2 hlt hd
    rw [slope_def_field, e, le_div_iff₀ hpos] at hs
    by_contra hc
    have := QsHalfAux27c0.R'_lt M hqI0 (not_le.mp hc)
    nlinarith
  · have hs := h.slope_le_of_hasDerivAt hm1 hm2 hlt hd
    rw [slope_def_field, e, div_le_iff₀ hpos] at hs
    by_contra hc
    have := QsHalfAux27c0.R'_lt M (by linarith) (not_le.mp hc)
    nlinarith
  · have hs := h.lt_slope_of_hasDerivAt hm1 hm2 hlt hd
    rw [slope_def_field, e, lt_div_iff₀ hpos] at hs
    by_contra hc
    rcases (not_lt.mp hc).lt_or_eq with h' | h'
    · have := QsHalfAux27c0.R'_lt M hqI0 h'
      nlinarith
    · rw [← h'] at hs
      nlinarith
  · have hs := h.slope_lt_of_hasDerivAt hm1 hm2 hlt hd
    rw [slope_def_field, e, div_lt_iff₀ hpos] at hs
    by_contra hc
    rcases (not_lt.mp hc).lt_or_eq with h' | h'
    · have := QsHalfAux27c0.R'_lt M (by linarith) h'
      nlinarith
    · rw [h'] at hs
      nlinarith
