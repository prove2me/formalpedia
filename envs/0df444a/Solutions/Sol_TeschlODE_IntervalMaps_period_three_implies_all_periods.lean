-- Prove2me | solution 1 for TeschlODE.IntervalMaps.period_three_implies_all_periods
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:25:27.412013+00:00
-- url     : https://prove2.me/submissions/d36d069d-ac53-433f-815e-7786d339f514

import Mathlib

open Set Function

lemma p3_ivt_core (F : ℝ → ℝ) (hF : Continuous F) (a b y : ℝ) (hab : a ≤ b)
    (hy : y ∈ uIcc (F a) (F b)) : ∃ z ∈ Icc a b, F z = y := by
  have := intermediate_value_uIcc (a := a) (b := b) hF.continuousOn hy
  rw [uIcc_of_le hab] at this
  exact this

lemma p3_exact_core (F : ℝ → ℝ) (hF : Continuous F) (p q r s : ℝ) (hrs : r ≤ s)
    (hcov : Icc r s ⊆ F '' Icc p q) :
    ∃ c d, c ≤ d ∧ Icc c d ⊆ Icc p q ∧ F '' Icc c d = Icc r s := by
  obtain ⟨u, hu, hFu⟩ := hcov ⟨le_rfl, hrs⟩
  obtain ⟨v, hv, hFv⟩ := hcov ⟨hrs, le_rfl⟩
  have hclosed : ∀ (a b y : ℝ), IsCompact {x | x ∈ Icc a b ∧ F x = y} := fun a b y =>
    isCompact_Icc.inter_right (isClosed_eq hF continuous_const)
  rcases le_total u v with huv | hvu
  · obtain ⟨u', ⟨hu'I, hFu'⟩, hu'max⟩ := (hclosed u v r).exists_isGreatest ⟨u, ⟨le_rfl, huv⟩, hFu⟩
    obtain ⟨v', ⟨hv'I, hFv'⟩, hv'min⟩ := (hclosed u' v s).exists_isLeast
      ⟨v, ⟨hu'I.2, le_rfl⟩, hFv⟩
    refine ⟨u', v', hv'I.1, fun x hx => ⟨by linarith [hu.1, hu'I.1, hx.1],
      by linarith [hv.2, hv'I.2, hx.2]⟩, ?_⟩
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      constructor
      · by_contra hlt
        push Not at hlt
        obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF x v' r hx.2
          (by rw [hFv', mem_uIcc]; left; exact ⟨hlt.le, hrs⟩)
        have hzA := hu'max ⟨⟨by linarith [hu'I.1, hx.1, hz.1], by linarith [hz.2, hv'I.2]⟩, hFz⟩
        have hxu : x ≠ u' := by rintro rfl; linarith
        have : u' < x := lt_of_le_of_ne hx.1 (Ne.symm hxu)
        linarith [hz.1]
      · by_contra hlt
        push Not at hlt
        obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF u' x s hx.1
          (by rw [hFu', mem_uIcc]; left; exact ⟨hrs, hlt.le⟩)
        have hzB := hv'min ⟨⟨hz.1, by linarith [hz.2, hx.2, hv'I.2]⟩, hFz⟩
        have : x = v' := le_antisymm hx.2 (by linarith [hz.2])
        rw [this] at hlt; linarith
    · have := p3_ivt_core F hF u' v' (F u') hv'I.1 left_mem_uIcc
      intro y hy
      obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF u' v' y hv'I.1
        (by rw [hFu', hFv', mem_uIcc]; left; exact hy)
      exact ⟨z, hz, hFz⟩
  · obtain ⟨v', ⟨hv'I, hFv'⟩, hv'max⟩ := (hclosed v u s).exists_isGreatest ⟨v, ⟨le_rfl, hvu⟩, hFv⟩
    obtain ⟨u', ⟨hu'I, hFu'⟩, hu'min⟩ := (hclosed v' u r).exists_isLeast
      ⟨u, ⟨hv'I.2, le_rfl⟩, hFu⟩
    refine ⟨v', u', hu'I.1, fun x hx => ⟨by linarith [hv.1, hv'I.1, hx.1],
      by linarith [hu.2, hu'I.2, hx.2]⟩, ?_⟩
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      constructor
      · by_contra hlt
        push Not at hlt
        obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF v' x r hx.1
          (by rw [hFv', mem_uIcc]; right; exact ⟨hlt.le, hrs⟩)
        have hzB := hu'min ⟨⟨hz.1, by linarith [hz.2, hx.2, hu'I.2]⟩, hFz⟩
        have : x = u' := le_antisymm hx.2 (by linarith [hz.2])
        rw [this] at hlt; linarith
      · by_contra hlt
        push Not at hlt
        obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF x u' s hx.2
          (by rw [hFu', mem_uIcc]; right; exact ⟨hrs, hlt.le⟩)
        have hzA := hv'max ⟨⟨by linarith [hv'I.1, hx.1, hz.1], by linarith [hz.2, hu'I.2]⟩, hFz⟩
        have hxv : x ≠ v' := by rintro rfl; linarith
        have : v' < x := lt_of_le_of_ne hx.1 (Ne.symm hxv)
        linarith [hz.1]
    · intro y hy
      obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF v' u' y hu'I.1
        (by rw [hFu', hFv', mem_uIcc]; right; exact hy)
      exact ⟨z, hz, hFz⟩

lemma p3_chain_core (F : ℝ → ℝ) (hF : Continuous F) :
    ∀ (n : ℕ) (p q : ℕ → ℝ), (∀ k, p k ≤ q k) →
      (∀ k < n, Icc (p (k + 1)) (q (k + 1)) ⊆ F '' Icc (p k) (q k)) →
      ∃ c d, c ≤ d ∧ (∀ k ≤ n, F^[k] '' Icc c d ⊆ Icc (p k) (q k)) ∧
        F^[n] '' Icc c d = Icc (p n) (q n) := by
  intro n
  induction n with
  | zero =>
    intro p q hpq _
    refine ⟨p 0, q 0, hpq 0, fun k hk => ?_, by simp⟩
    rw [Nat.le_zero.mp hk]; simp
  | succ n ih =>
    intro p q hpq hcov
    obtain ⟨c', d', hcd', hsub', himg'⟩ := ih (fun k => p (k + 1)) (fun k => q (k + 1))
      (fun k => hpq (k + 1)) (fun k hk => hcov (k + 1) (by omega))
    have h1 : Icc c' d' ⊆ F '' Icc (p 0) (q 0) := by
      have := hsub' 0 (by omega)
      simp only [iterate_zero, image_id] at this
      exact this.trans (hcov 0 (by omega))
    obtain ⟨c, d, hcd, hsub, himg⟩ := p3_exact_core F hF (p 0) (q 0) c' d' hcd' h1
    refine ⟨c, d, hcd, fun k hk => ?_, ?_⟩
    · rcases k with _ | k
      · simpa using hsub
      · rw [iterate_succ, image_comp, himg]
        exact hsub' k (by omega)
    · rw [iterate_succ, image_comp, himg]
      exact himg'

lemma p3_fixed_core (F : ℝ → ℝ) (hF : Continuous F) (n : ℕ) (c d : ℝ) (hcd : c ≤ d)
    (hcov : Icc c d ⊆ F^[n] '' Icc c d) : ∃ x ∈ Icc c d, F^[n] x = x := by
  obtain ⟨x1, hx1, hF1⟩ := hcov ⟨le_rfl, hcd⟩
  obtain ⟨x2, hx2, hF2⟩ := hcov ⟨hcd, le_rfl⟩
  have hG : Continuous fun x => F^[n] x - x := (hF.iterate n).sub continuous_id
  have h0 : (0 : ℝ) ∈ uIcc (F^[n] x1 - x1) (F^[n] x2 - x2) := by
    rw [mem_uIcc]; left; constructor <;> linarith [hx1.1, hx2.2]
  rcases le_total x1 x2 with h12 | h21
  · obtain ⟨z, hz, hGz⟩ := p3_ivt_core _ hG x1 x2 0 h12 h0
    exact ⟨z, ⟨by linarith [hx1.1, hz.1], by linarith [hx2.2, hz.2]⟩, by linarith⟩
  · obtain ⟨z, hz, hGz⟩ := p3_ivt_core _ hG x2 x1 0 h21 (by rw [uIcc_comm]; exact h0)
    exact ⟨z, ⟨by linarith [hx2.1, hz.1], by linarith [hx1.2, hz.2]⟩, by linarith⟩

lemma p3_cycle_core (F : ℝ → ℝ) (y0 y1 y2 : ℝ) (h01 : y0 ≠ y1) (h02 : y0 ≠ y2)
    (h12 : y1 ≠ y2) (hF0 : F y0 = y1) (hF1 : F y1 = y2) (hF2 : F y2 = y0) :
    ∃ lo m hi : ℝ, lo < m ∧ m < hi ∧
      ((F lo = m ∧ F m = hi ∧ F hi = lo) ∨ (F lo = hi ∧ F hi = m ∧ F m = lo)) := by
  rcases lt_or_gt_of_ne h01 with a | a <;> rcases lt_or_gt_of_ne h02 with b | b <;>
    rcases lt_or_gt_of_ne h12 with c | c
  · exact ⟨y0, y1, y2, a, c, Or.inl ⟨hF0, hF1, hF2⟩⟩
  · exact ⟨y0, y2, y1, b, c, Or.inr ⟨hF0, hF1, hF2⟩⟩
  · exact absurd (lt_trans a c) (not_lt.mpr b.le)
  · exact ⟨y2, y0, y1, b, a, Or.inl ⟨hF2, hF0, hF1⟩⟩
  · exact ⟨y1, y0, y2, a, b, Or.inr ⟨hF1, hF2, hF0⟩⟩
  · exact absurd (lt_trans c a) (not_lt.mpr b.le)
  · exact ⟨y1, y2, y0, c, b, Or.inl ⟨hF1, hF2, hF0⟩⟩
  · exact ⟨y2, y1, y0, c, a, Or.inr ⟨hF2, hF0, hF1⟩⟩

/-- the real-line version -/
lemma p3_real_core (F : ℝ → ℝ) (hF : Continuous F) (y0 : ℝ) (hy0 : minimalPeriod F y0 = 3) :
    ∀ n : ℕ, 1 ≤ n → ∃ x : ℝ, minimalPeriod F x = n := by
  have hper : IsPeriodicPt F 3 y0 := by rw [← hy0]; exact isPeriodicPt_minimalPeriod F y0
  have hnot : ∀ k, 0 < k → k < 3 → F^[k] y0 ≠ y0 := fun k hk1 hk2 h =>
    absurd (IsPeriodicPt.minimalPeriod_le hk1 h) (by omega)
  have h01 : y0 ≠ F y0 := fun h => hnot 1 (by omega) (by omega) h.symm
  have h02 : y0 ≠ F (F y0) := fun h => hnot 2 (by omega) (by omega) (by simpa using h.symm)
  have h3 : F (F (F y0)) = y0 := by simpa [iterate_succ_apply'] using hper.eq
  have h12 : F y0 ≠ F (F y0) := by
    intro h
    apply h01
    calc y0 = F (F (F y0)) := h3.symm
      _ = F (F y0) := congrArg F h.symm
      _ = F y0 := h.symm
  obtain ⟨lo, m, hi, hlm, hmh, hcase⟩ := p3_cycle_core F y0 (F y0) (F (F y0)) h01 h02 h12 rfl rfl h3
  -- the two intervals `L` and `R`
  obtain ⟨pL, qL, pR, qR, hL, hR, hLR, hcovL, hcovLR, hcovR, hFFm, hFm⟩ :
      ∃ pL qL pR qR : ℝ, pL ≤ qL ∧ pR ≤ qR ∧
        (∀ x, x ∈ Icc pL qL → x ∈ Icc pR qR → x = m) ∧
        Icc pL qL ⊆ F '' Icc pL qL ∧ Icc pR qR ⊆ F '' Icc pL qL ∧
        Icc pL qL ⊆ F '' Icc pR qR ∧ F (F m) ∉ Icc pL qL ∧ F m ≠ m := by
    rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hLimg : Icc lo hi ⊆ F '' Icc m hi := fun y hy => by
        obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF m hi y hmh.le
          (by rw [h2, h3, mem_uIcc]; right; exact hy)
        exact ⟨z, hz, hFz⟩
      have hRimg : Icc m hi ⊆ F '' Icc lo m := fun y hy => by
        obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF lo m y hlm.le
          (by rw [h1, h2, mem_uIcc]; left; exact hy)
        exact ⟨z, hz, hFz⟩
      refine ⟨m, hi, lo, m, hmh.le, hlm.le, fun x hx1 hx2 => le_antisymm hx2.2 hx1.1,
        fun y hy => hLimg ⟨by linarith [hy.1], hy.2⟩,
        fun y hy => hLimg ⟨hy.1, by linarith [hy.2]⟩, hRimg, ?_, ?_⟩
      · rw [h2, h3]; intro h; linarith [h.1]
      · rw [h2]; exact hmh.ne'
    · have hLimg : Icc lo hi ⊆ F '' Icc lo m := fun y hy => by
        obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF lo m y hlm.le
          (by rw [h1, h3, mem_uIcc]; right; exact hy)
        exact ⟨z, hz, hFz⟩
      have hRimg : Icc lo m ⊆ F '' Icc m hi := fun y hy => by
        obtain ⟨z, hz, hFz⟩ := p3_ivt_core F hF m hi y hmh.le
          (by rw [h3, h2, mem_uIcc]; left; exact hy)
        exact ⟨z, hz, hFz⟩
      refine ⟨lo, m, m, hi, hlm.le, hmh.le, fun x hx1 hx2 => le_antisymm hx1.2 hx2.1,
        fun y hy => hLimg ⟨hy.1, by linarith [hy.2]⟩,
        fun y hy => hLimg ⟨by linarith [hy.1], hy.2⟩, hRimg, ?_, ?_⟩
      · rw [h3, h1]; intro h; linarith [h.2]
      · rw [h3]; exact hlm.ne
  intro n hn
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · -- a fixed point
    have hn1' : n = 1 := by omega
    subst hn1'
    obtain ⟨c, d, hcd, hsub, himg⟩ := p3_chain_core F hF 1 (fun _ => pL) (fun _ => qL)
      (fun _ => hL) (fun k _ => hcovL)
    have h0 := hsub 0 (by omega)
    simp only [iterate_zero, image_id] at h0
    obtain ⟨x, -, hfx⟩ := p3_fixed_core F hF 1 c d hcd (by rw [himg]; exact h0)
    exact ⟨x, minimalPeriod_eq_one_iff_isFixedPt.mpr hfx⟩
  · let p : ℕ → ℝ := fun k => if k = n - 1 then pR else pL
    let q : ℕ → ℝ := fun k => if k = n - 1 then qR else qL
    have hpq : ∀ k, p k ≤ q k := fun k => by
      simp only [p, q]; split_ifs <;> assumption
    have hpL : ∀ k, k ≠ n - 1 → p k = pL ∧ q k = qL := fun k hk => by
      simp [p, q, if_neg hk]
    have hpR : p (n - 1) = pR ∧ q (n - 1) = qR := by
      simp [p, q]
    have hcov : ∀ k < n, Icc (p (k + 1)) (q (k + 1)) ⊆ F '' Icc (p k) (q k) := by
      intro k hk
      by_cases hk1 : k = n - 1
      · rw [(hpL (k + 1) (by omega)).1, (hpL (k + 1) (by omega)).2, hk1, hpR.1, hpR.2]
        exact hcovR
      · rw [(hpL k hk1).1, (hpL k hk1).2]
        by_cases hk2 : k + 1 = n - 1
        · rw [hk2, hpR.1, hpR.2]; exact hcovLR
        · rw [(hpL (k + 1) hk2).1, (hpL (k + 1) hk2).2]; exact hcovL
    obtain ⟨c, d, hcd, hsub, himg⟩ := p3_chain_core F hF n p q hpq hcov
    have h0 := hsub 0 (by omega)
    simp only [iterate_zero, image_id, p, q, if_neg (show 0 ≠ n - 1 by omega)] at h0
    have hn' : p n = pL ∧ q n = qL := by
      exact hpL n (by omega)
    rw [hn'.1, hn'.2] at himg
    obtain ⟨x, hx, hfx⟩ := p3_fixed_core F hF n c d hcd (by rw [himg]; exact h0)
    have horb : ∀ k ≤ n, F^[k] x ∈ Icc (p k) (q k) := fun k hk => hsub k hk (Set.mem_image_of_mem _ hx)
    have horbL : ∀ k ≤ n, k ≠ n - 1 → F^[k] x ∈ Icc pL qL := by
      intro k hk hk'
      have := horb k hk
      simpa [p, q, hk'] using this
    have horbR : F^[n - 1] x ∈ Icc pR qR := by
      have := horb (n - 1) (by omega)
      simpa [p, q] using this
    have hpx : IsPeriodicPt F n x := hfx
    refine ⟨x, ?_⟩
    have hdvd := hpx.minimalPeriod_dvd
    have hpos := hpx.minimalPeriod_pos (by omega)
    by_contra hne
    have hlt : minimalPeriod F x < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) hne
    have hmp : F^[minimalPeriod F x] x = x := (isPeriodicPt_minimalPeriod F x).eq
    rcases Nat.lt_or_ge n 3 with h2 | h3
    · have hn2 : n = 2 := by omega
      subst hn2
      have h1 : minimalPeriod F x = 1 := by omega
      rw [h1, iterate_one] at hmp
      have hxL := horbL 0 (by omega) (by omega)
      have hxR := horbR
      simp only [iterate_zero, id, show 2 - 1 = 1 from rfl, iterate_one] at hxL hxR
      rw [hmp] at hxR
      have := hLR x hxL hxR
      rw [this] at hmp
      exact hFm (by simpa using hmp)
    · set k := n - 1 - minimalPeriod F x with hk
      have hsplit : F^[n - 1] x = F^[k] x := by
        rw [show n - 1 = k + minimalPeriod F x by omega, iterate_add_apply, hmp]
      have hkL := horbL k (by omega) (by omega)
      rw [← hsplit] at hkL
      have hm := hLR _ hkL horbR
      have hF1 := horbL 1 (by omega) (by omega)
      have : F^[n + 1] x = F (F (F^[n - 1] x)) := by
        rw [show n + 1 = 2 + (n - 1) by omega, iterate_add_apply]; rfl
      rw [hm] at this
      have hF1' : F^[n + 1] x = F^[1] x := by
        rw [show n + 1 = 1 + n by omega, iterate_add_apply, hfx]
      rw [← hF1', this] at hF1
      exact hFFm hF1

theorem solution (a b : ℝ) (hab : a ≤ b)
    (f : Set.Icc a b → Set.Icc a b) (hf : Continuous f)
    (h3 : ∃ x : Set.Icc a b, Function.minimalPeriod f x = 3) :
    ∀ n : ℕ, 1 ≤ n → ∃ x : Set.Icc a b, Function.minimalPeriod f x = n := by
  set F : ℝ → ℝ := fun y => (f (Set.projIcc a b hab y) : ℝ) with hFdef
  have hF : Continuous F := continuous_subtype_val.comp (hf.comp continuous_projIcc)
  have hiter : ∀ (k : ℕ) (x : Set.Icc a b), F^[k] (x : ℝ) = ((f^[k] x : Set.Icc a b) : ℝ) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [iterate_succ_apply', ih, iterate_succ_apply']
      simp only [hFdef, Set.projIcc_val]
  have hmin : ∀ x : Set.Icc a b, minimalPeriod F (x : ℝ) = minimalPeriod f x := by
    intro x
    rw [minimalPeriod_eq_minimalPeriod_iff]
    intro k
    simp only [IsPeriodicPt, IsFixedPt, hiter]
    exact Subtype.val_injective.eq_iff
  obtain ⟨x0, hx0⟩ := h3
  intro n hn
  obtain ⟨y, hy⟩ := p3_real_core F hF x0 (by rw [hmin, hx0]) n hn
  have hyper : IsPeriodicPt F n y := by rw [← hy]; exact isPeriodicPt_minimalPeriod F y
  have hyI : y ∈ Set.Icc a b := by
    have : F^[n] y = y := hyper.eq
    rw [← this, show n = (n - 1) + 1 by omega, iterate_succ_apply']
    exact (f _).2
  refine ⟨⟨y, hyI⟩, ?_⟩
  rw [← hmin]
  exact hy

#print axioms solution
