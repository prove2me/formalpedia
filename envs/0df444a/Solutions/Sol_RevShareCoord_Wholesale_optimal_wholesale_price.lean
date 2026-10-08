-- Prove2me | solution 1 for RevShareCoord.Wholesale.optimal_wholesale_price
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:05:08.927455+00:00
-- url     : https://prove2.me/submissions/9f1060b7-5401-4492-adfa-7511f484d589

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

set_option autoImplicit false

open RevShareCoord.Wholesale in
theorem ce083d6b_exists_pos (M : Model) : ∃ q : ℝ, 0 < q ∧ M.c < M.R' q := by
  by_contra hcon
  push Not at hcon
  set g : ℝ → ℝ := fun q => M.R q - M.c * q with hg
  have hgd : ∀ q : ℝ, 0 ≤ q → HasDerivWithinAt g (M.R' q - M.c) (Set.Ici 0) q := by
    intro q hq
    have h1 := M.hasDeriv q hq
    have h2 : HasDerivWithinAt (fun q : ℝ => M.c * q) (M.c * 1) (Set.Ici 0) q :=
      ((hasDerivAt_id q).const_mul M.c).hasDerivWithinAt
    have h3 := h1.sub h2
    rw [mul_one] at h3
    exact h3
  have hcont : ContinuousOn g (Set.Ici 0) := fun q hq => (hgd q hq).continuousWithinAt
  have hanti : AntitoneOn g (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont
    · intro q hq
      rw [interior_Ici] at hq
      have hq' : (0:ℝ) < q := hq
      exact ((hgd q hq'.le).hasDerivAt (Ici_mem_nhds hq')).differentiableAt.differentiableWithinAt
    · intro q hq
      rw [interior_Ici] at hq
      have hq' : (0:ℝ) < q := hq
      rw [((hgd q hq'.le).hasDerivAt (Ici_mem_nhds hq')).deriv]
      linarith [hcon q hq']
  have h0 : HasDerivWithinAt g (M.R' 0 - M.c) (Set.Ioi 0) 0 :=
    (hgd 0 le_rfl).mono Set.Ioi_subset_Ici_self
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at h0
  have hle : M.R' 0 - M.c ≤ 0 := by
    apply le_of_tendsto h0
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : (0:ℝ) < q := hq
    rw [slope_def_field]
    apply div_nonpos_of_nonpos_of_nonneg
    · have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hq'.le) hq'.le
      linarith
    · linarith
  linarith [M.viable]

open RevShareCoord.Wholesale in
theorem solution (M : Model) (qs : ℝ) (hqs0 : 0 ≤ qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs) :
    inducingPrice M.R' qs = M.c - qs * M.R'' qs ∧
      M.c < inducingPrice M.R' qs := by
  obtain ⟨q, hq, hcq⟩ := ce083d6b_exists_pos M
  have hmax : supplierProfit M.R' M.c q ≤ supplierProfit M.R' M.c qs :=
    hqs (Set.mem_Ici.mpr hq.le)
  have hpos : 0 < supplierProfit M.R' M.c q := by
    unfold supplierProfit inducingPrice
    exact mul_pos hq (by linarith)
  have hspos : 0 < qs * (M.R' qs - M.c) := by
    have := lt_of_lt_of_le hpos hmax
    simpa [supplierProfit, inducingPrice] using this
  have hqs_pos : 0 < qs := by
    rcases hqs0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hspos; simp at hspos
  have hgt : M.c < M.R' qs := by
    by_contra hc
    push Not at hc
    have : qs * (M.R' qs - M.c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hqs0 (by linarith)
    linarith
  have hloc : IsLocalMax (supplierProfit M.R' M.c) qs :=
    hqs.isLocalMax (Ici_mem_nhds hqs_pos)
  have hd : HasDerivAt (supplierProfit M.R' M.c)
      (1 * (M.R' qs - M.c) + qs * M.R'' qs) qs := by
    have h1 : HasDerivAt (fun x : ℝ => x * (M.R' x - M.c))
        (1 * (M.R' qs - M.c) + qs * M.R'' qs) qs :=
      (hasDerivAt_id' qs).mul ((M.hasDeriv2 qs hqs_pos).sub_const M.c)
    exact h1
  have hz := hloc.hasDerivAt_eq_zero hd
  refine ⟨?_, ?_⟩
  · unfold inducingPrice
    linarith
  · unfold inducingPrice
    exact hgt
