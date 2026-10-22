-- Prove2me | solution 1 for YeIPA.Asymptotic.proposition_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:10:13.459687+00:00
-- url     : https://prove2.me/submissions/b06852aa-68e2-44d2-95fa-b1eedb8a2b68

import Mathlib
import Definitions.Def_YeIPA_Asymptotic_Order
open YeIPA.Asymptotic

theorem g69w_mem (r : ℕ → ℝ) (hpos : ∀ k, 0 < r k) (p : ℝ) (hp : 0 ≤ p)
    (hev : ∀ᶠ k in Filter.atTop, r (k + 1) ≤ r k ^ p) :
    (p : EReal) ∈ {q : EReal | ∃ p : ℝ, 0 ≤ p ∧ q = (p : EReal) ∧ 0 ≤ ratioLimsup r p ∧
      ratioLimsup r p < ⊤} := by
  refine ⟨p, hp, rfl, ?_, ?_⟩
  · unfold ratioLimsup
    apply Filter.le_limsup_of_frequently_le'
    refine Filter.Frequently.of_forall fun k => ?_
    have := hpos k; have := hpos (k + 1)
    exact_mod_cast (by positivity : (0 : ℝ) ≤ |r (k + 1)| / |r k| ^ p)
  · unfold ratioLimsup
    refine lt_of_le_of_lt (Filter.limsup_le_of_le (a := ((1 : ℝ) : EReal)) (by isBoundedDefault) ?_)
      (EReal.coe_lt_top 1)
    filter_upwards [hev] with k hk
    have h0 := hpos k; have h1 := hpos (k + 1)
    rw [abs_of_pos h0, abs_of_pos h1]
    have : r (k + 1) / r k ^ p ≤ 1 := by
      rw [div_le_one (Real.rpow_pos_of_pos h0 p)]; exact hk
    exact_mod_cast this

theorem solution (r : ℕ → ℝ) (hpos : ∀ k, 0 < r k)
    (hlim : Filter.Tendsto r Filter.atTop (nhds 0)) :
    orderOfConvergence r =
      Filter.liminf (fun k => ((Real.log (r (k + 1)) / Real.log (r k) : ℝ) : EReal))
        Filter.atTop := by
  set L := Filter.liminf (fun k => ((Real.log (r (k + 1)) / Real.log (r k) : ℝ) : EReal))
    Filter.atTop with hL
  have hlt1 : ∀ᶠ k in Filter.atTop, r k < 1 := hlim.eventually (gt_mem_nhds one_pos)
  have hneg : ∀ᶠ k in Filter.atTop, Real.log (r k) < 0 := by
    filter_upwards [hlt1] with k hk
    exact Real.log_neg (hpos k) hk
  have hlogeq : ∀ k, Real.log (r k) < 0 →
      Real.log (r (k + 1)) = Real.log (r (k + 1)) / Real.log (r k) * Real.log (r k) := by
    intro k hk; rw [div_mul_cancel₀ _ hk.ne]
  have hrpow : ∀ k (q : ℝ), r k ^ q = Real.exp (Real.log (r k) * q) := fun k q =>
    Real.rpow_def_of_pos (hpos k) q
  unfold orderOfConvergence
  apply le_antisymm
  · refine sSup_le fun x hx => ?_
    obtain ⟨p, hp0, rfl, _, hfin⟩ := hx
    by_contra hcon
    push Not at hcon
    obtain ⟨q, hLq, hqp⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hqp' : q < p := by exact_mod_cast hqp
    have hfreq : ∃ᶠ k in Filter.atTop,
        ((Real.log (r (k + 1)) / Real.log (r k) : ℝ) : EReal) < q :=
      Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hLq
    apply (lt_irrefl (⊤ : EReal))
    have htop : ratioLimsup r p = ⊤ := by
      rw [EReal.eq_top_iff_forall_lt]
      intro M
      set M' := max M 0 + 1 with hM'
      have hM'pos : 0 < M' := by positivity
      have hT : ∀ᶠ k in Filter.atTop, r k < Real.exp (Real.log M' / (q - p)) :=
        hlim.eventually (gt_mem_nhds (Real.exp_pos _))
      have hfr : ∃ᶠ k in Filter.atTop, (M' : EReal) ≤ ((|r (k + 1)| / |r k| ^ p : ℝ) : EReal) := by
        refine (hfreq.and_eventually (hneg.and hT)).mono fun k ⟨hk, hk2, hk3⟩ => ?_
        have hk' : Real.log (r (k + 1)) / Real.log (r k) < q := by exact_mod_cast hk
        have h0 := hpos k; have h1 := hpos (k + 1)
        rw [abs_of_pos h0, abs_of_pos h1]
        -- log r(k+1) > q log r k
        have hl1 : q * Real.log (r k) < Real.log (r (k + 1)) := by
          rw [hlogeq k hk2]; exact mul_lt_mul_of_neg_right hk' hk2
        have hlk : Real.log (r k) < Real.log M' / (q - p) := by
          have := Real.log_lt_log h0 hk3; rwa [Real.log_exp] at this
        have hqp0 : q - p < 0 := by linarith
        have hl2 : Real.log M' < (q - p) * Real.log (r k) := by
          rw [lt_div_iff_of_neg hqp0] at hlk; linarith
        have : M' ≤ r (k + 1) / r k ^ p := by
          rw [le_div_iff₀ (Real.rpow_pos_of_pos h0 p), hrpow k p]
          rw [← Real.exp_log hM'pos, ← Real.exp_log h1, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith
        exact_mod_cast this
      have := Filter.le_limsup_of_frequently_le' hfr
      refine lt_of_lt_of_le ?_ this
      have : M < M' := by rw [hM']; have := le_max_left M 0; linarith
      exact_mod_cast this
    rw [htop] at hfin
    exact (lt_irrefl _ hfin).elim
  · have hlt1' : ∀ᶠ k in Filter.atTop, r (k + 1) < 1 :=
      (Filter.tendsto_add_atTop_nat 1).eventually hlt1
    have h0mem : ((0 : ℝ) : EReal) ∈ {q : EReal | ∃ p : ℝ, 0 ≤ p ∧ q = (p : EReal) ∧
        0 ≤ ratioLimsup r p ∧ ratioLimsup r p < ⊤} := by
      apply g69w_mem r hpos 0 le_rfl
      filter_upwards [hlt1'] with k hk
      rw [Real.rpow_zero]; exact hk.le
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨q, hcq, hqL⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    rcases le_or_gt q 0 with hq0 | hq0
    · calc c < q := hcq
        _ ≤ ((0 : ℝ) : EReal) := by exact_mod_cast hq0
        _ ≤ _ := le_sSup h0mem
    · have hev : ∀ᶠ k in Filter.atTop,
          (q : EReal) < ((Real.log (r (k + 1)) / Real.log (r k) : ℝ) : EReal) :=
        Filter.eventually_lt_of_lt_liminf hqL (by isBoundedDefault)
      have hqmem := g69w_mem r hpos q hq0.le (by
        filter_upwards [hev, hneg] with k hk hk2
        have hk' : q < Real.log (r (k + 1)) / Real.log (r k) := by exact_mod_cast hk
        have hl1 : Real.log (r (k + 1)) < q * Real.log (r k) := by
          rw [hlogeq k hk2]; exact mul_lt_mul_of_neg_right hk' hk2
        rw [hrpow k q, ← Real.exp_log (hpos (k + 1))]
        apply Real.exp_le_exp.mpr
        linarith)
      exact lt_of_lt_of_le hcq (le_sSup hqmem)
