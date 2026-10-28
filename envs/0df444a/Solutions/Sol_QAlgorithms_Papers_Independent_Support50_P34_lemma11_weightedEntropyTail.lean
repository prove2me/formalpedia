-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P34.lemma11_weightedEntropyTail
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:39:14.496989+00:00
-- url     : https://prove2.me/submissions/0b27af46-d815-4c7f-b2b6-ad6e085754b0

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators

open QAlgorithms.Papers.Independent.Support50.P34

open QAlgorithms.Papers.Independent.Dependency50.P13 (entropyWeight)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Pointwise Legendre-type bound: `η(t)/h ≤ λ t + e^{-1-λh}/h` for `t ≥ 0`, `h > 0`, `λ ≥ 0`. -/
lemma eta_div_le_aux (t h lam : ℝ) (ht : 0 ≤ t) (hh : 0 < h) (hl : 0 ≤ lam) :
    entropyWeight t / h ≤ lam * t + Real.exp (-1 - lam * h) / h := by
  have key : entropyWeight t ≤ lam * h * t + Real.exp (-1 - lam * h) := by
    rcases ht.eq_or_lt with rfl | ht
    · simp only [entropyWeight, neg_zero, zero_mul, mul_zero, zero_add]
      exact (Real.exp_pos _).le
    · have h1 := Real.add_one_le_exp (-1 - lam * h - Real.log t)
      rw [Real.exp_sub, Real.exp_log ht, le_div_iff₀ ht] at h1
      unfold entropyWeight
      nlinarith [h1]
  rw [div_le_iff₀ hh]
  calc entropyWeight t ≤ lam * h * t + Real.exp (-1 - lam * h) := key
    _ = (lam * t + Real.exp (-1 - lam * h) / h) * h := by field_simp

theorem solution (h : ℕ → ℝ) (hmono : Monotone h)
    (hpos : ∀ j, 0 < h j) (hfinite : convergenceExponent h < ⊤) :
    Tendsto (weightedEntropyTail h) atTop (nhds (convergenceExponent h)) := by
  unfold convergenceExponent at hfinite ⊢
  set S := {r : ℝ≥0∞ | ∃ lam : ℝ, 0 < lam ∧
    Summable (fun j : ℕ => Real.exp (-lam * h j)) ∧ r = ENNReal.ofReal lam} with hS
  -- some exponent is admissible
  obtain ⟨lam₁, hlam₁, hsum₁⟩ : ∃ lam : ℝ, 0 < lam ∧
      Summable (fun j : ℕ => Real.exp (-lam * h j)) := by
    rw [sInf_lt_iff] at hfinite
    obtain ⟨r, ⟨lam, hl, hs, rfl⟩, _⟩ := hfinite
    exact ⟨lam, hl, hs⟩
  -- hence `h` tends to infinity
  have hinf : Tendsto h atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro B
    have := hsum₁.tendsto_atTop_zero.eventually_lt_const (Real.exp_pos (-lam₁ * B))
    filter_upwards [this] with j hj
    rw [Real.exp_lt_exp] at hj
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hlam₁ (sub_pos.2 hc)]
  rw [tendsto_order]
  constructor
  · -- lower bound: for every `a < sInf S`, eventually `a < W m`
    intro a ha
    obtain ⟨lam, hlam0, halam, hlamL⟩ := ENNReal.lt_iff_exists_real_btwn.1 ha
    have hlam : 0 < lam := by
      rcases hlam0.eq_or_lt with rfl | hl
      · simp at halam
      · exact hl
    have hns : ¬ Summable (fun j : ℕ => Real.exp (-lam * h j)) := by
      intro hs
      have hmem : ENNReal.ofReal lam ∈ S := ⟨lam, hlam, hs, rfl⟩
      exact absurd (sInf_le hmem) (not_le.2 hlamL)
    obtain ⟨r, hr0, har, hrlam⟩ := ENNReal.lt_iff_exists_real_btwn.1 halam
    have hr : 0 < r := by
      rcases hr0.eq_or_lt with rfl | hl
      · simp at har
      · exact hl
    have hrlam' : r < lam := (ENNReal.ofReal_lt_ofReal_iff hlam).1 hrlam
    have hδpos : 0 < 1 - r / lam := by
      have : r / lam < 1 := (div_lt_one hlam).2 hrlam'
      linarith
    -- the candidate weights
    set t : ℕ → ℝ := fun j => Real.exp (-1 - lam * h j) with ht
    have ht0 : ∀ j, 0 ≤ t j := fun j => (Real.exp_pos _).le
    have htlim : Tendsto t atTop (nhds 0) := by
      have hin : Tendsto (fun j => -1 - lam * h j) atTop atBot := by
        rw [Filter.tendsto_atBot]
        intro B
        filter_upwards [hinf.eventually_ge_atTop ((-1 - B) / lam)] with j hj
        rw [div_le_iff₀ hlam] at hj
        linarith
      exact Real.tendsto_exp_atBot.comp hin
    have htns : ¬ Summable t := by
      intro hs
      apply hns
      have : (fun j : ℕ => Real.exp (-lam * h j)) = fun j => Real.exp 1 * t j := by
        ext j
        simp only [ht]
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this]
      exact hs.mul_left _
    have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg ht0).1 htns
    obtain ⟨N, hN⟩ := eventually_atTop.1 (htlim.eventually_lt_const hδpos)
    rw [eventually_atTop]
    refine ⟨N, fun m hm => ?_⟩
    have hex : ∃ M, r / lam ≤ ∑ j ∈ Finset.Ico m M, t j := by
      obtain ⟨M, hM1, hM2⟩ := ((hdiv.eventually_ge_atTop
        (r / lam + ∑ j ∈ Finset.range m, t j)).and (eventually_ge_atTop m)).exists
      refine ⟨M, ?_⟩
      rw [Finset.sum_Ico_eq_sub _ hM2]
      linarith
    obtain ⟨M, hM, hMmin⟩ : ∃ M, r / lam ≤ ∑ j ∈ Finset.Ico m M, t j ∧
        ∀ M' < M, ¬ (r / lam ≤ ∑ j ∈ Finset.Ico m M', t j) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun M' hM' => Nat.find_min hex hM'⟩
    have hMm : m < M := by
      by_contra hcon
      push Not at hcon
      have : ∑ j ∈ Finset.Ico m M, t j = 0 := by
        rw [Finset.Ico_eq_empty_of_le hcon]
        simp
      rw [this] at hM
      exact absurd hM (not_le.2 (div_pos hr hlam))
    have hM1 : ∑ j ∈ Finset.Ico m M, t j < 1 := by
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      rw [Finset.sum_Ico_succ_top (by omega : m ≤ M')]
      have h1 : ¬ (r / lam ≤ ∑ j ∈ Finset.Ico m M', t j) := hMmin M' (Nat.lt_succ_self _)
      push Not at h1
      have h2 : t M' < 1 - r / lam := hN M' (by omega)
      linarith
    let x : ℕ → ℝ := fun j => if m ≤ j ∧ j < M then t j else 0
    have hxsupp : ∀ j ∉ Finset.Ico m M, x j = 0 := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp [x, hj]
    have hxeq : ∀ j ∈ Finset.Ico m M, x j = t j := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp [x, hj]
    have hx0 : ∀ j, 0 ≤ x j := by
      intro j
      simp only [x]
      split_ifs
      · exact ht0 j
      · exact le_rfl
    have hxball : x ∈ PositiveL1Ball := by
      refine ⟨hx0, ?_⟩
      rw [tsum_eq_sum (s := Finset.Ico m M) (fun j hj => by rw [hxsupp j hj]; simp)]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hx0 j)]
      calc ENNReal.ofReal (∑ j ∈ Finset.Ico m M, x j)
          = ENNReal.ofReal (∑ j ∈ Finset.Ico m M, t j) := by
            rw [Finset.sum_congr rfl hxeq]
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hM1.le
        _ = 1 := ENNReal.ofReal_one
    have hval : ENNReal.ofReal r ≤
        ∑' j, if m ≤ j then ENNReal.ofReal (scalarEta (x j) / h j) else 0 := by
      rw [tsum_eq_sum (s := Finset.Ico m M) ?_]
      · calc ENNReal.ofReal r = ENNReal.ofReal (lam * (r / lam)) := by
              rw [mul_div_cancel₀ _ hlam.ne']
          _ ≤ ENNReal.ofReal (lam * ∑ j ∈ Finset.Ico m M, t j) :=
              ENNReal.ofReal_le_ofReal (by gcongr)
          _ = ENNReal.ofReal (∑ j ∈ Finset.Ico m M, lam * t j) := by rw [Finset.mul_sum]
          _ = ∑ j ∈ Finset.Ico m M, ENNReal.ofReal (lam * t j) :=
              ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hlam.le (ht0 j))
          _ ≤ ∑ j ∈ Finset.Ico m M,
                (if m ≤ j then ENNReal.ofReal (scalarEta (x j) / h j) else 0) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hj' := Finset.mem_Ico.1 hj
              rw [if_pos hj'.1, hxeq j hj]
              apply ENNReal.ofReal_le_ofReal
              have heta : scalarEta (t j) = t j * (1 + lam * h j) := by
                simp only [scalarEta, entropyWeight, ht, Real.log_exp]
                ring
              rw [heta, le_div_iff₀ (hpos j)]
              have := ht0 j
              nlinarith
      · intro j hj
        simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hj
        rcases hj with hj | hj
        · rw [if_neg (not_le.2 hj)]
        · rw [hxsupp j (by simp only [Finset.mem_Ico]; omega)]
          simp [scalarEta, entropyWeight]
    calc a < ENNReal.ofReal r := har
      _ ≤ _ := hval
      _ ≤ weightedEntropyTail h m := by
        unfold weightedEntropyTail
        exact le_iSup (fun x : PositiveL1Ball =>
          ∑' j, if m ≤ j then ENNReal.ofReal (scalarEta (x.val j) / h j) else 0) ⟨x, hxball⟩
  · -- upper bound: for every `a > sInf S`, eventually `W m < a`
    intro a ha
    rw [gt_iff_lt, sInf_lt_iff] at ha
    obtain ⟨r, ⟨lam, hlam, hsum, rfl⟩, hra⟩ := ha
    have hg_nonneg : ∀ j, 0 ≤ Real.exp (-1 - lam * h j) / h j :=
      fun j => div_nonneg (Real.exp_pos _).le (hpos j).le
    have hg_sum : Summable (fun j => Real.exp (-1 - lam * h j) / h j) := by
      refine Summable.of_nonneg_of_le hg_nonneg (fun j => ?_)
        (hsum.mul_left (Real.exp (-1) / h 0))
      have h0j : h 0 ≤ h j := hmono (Nat.zero_le j)
      calc Real.exp (-1 - lam * h j) / h j ≤ Real.exp (-1 - lam * h j) / h 0 :=
            div_le_div_of_nonneg_left (Real.exp_pos _).le (hpos 0) h0j
        _ = Real.exp (-1) / h 0 * Real.exp (-lam * h j) := by
            rw [show -1 - lam * h j = -1 + (-lam * h j) by ring, Real.exp_add]
            ring
    set G : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (Real.exp (-1 - lam * h j) / h j) with hG
    have hGtop : ∑' j, G j ≠ ⊤ := by
      rw [hG, ← ENNReal.ofReal_tsum_of_nonneg hg_nonneg hg_sum]
      exact ENNReal.ofReal_ne_top
    have htail : Tendsto (fun m => ∑' j, if m ≤ j then G j else 0) atTop (nhds 0) := by
      refine (ENNReal.tendsto_sum_nat_add G hGtop).congr (fun m => ?_)
      have hinj : Function.Injective (fun k : ℕ => k + m) := add_left_injective m
      have key := hinj.tsum_eq (f := fun j => if m ≤ j then G j else 0) ?_
      · rw [← key]
        refine tsum_congr fun k => ?_
        simp
      · intro j hj
        rw [Function.mem_support] at hj
        by_cases hmj : m ≤ j
        · exact ⟨j - m, by simp only; omega⟩
        · simp [hmj] at hj
    have hbound : ∀ m, weightedEntropyTail h m ≤
        ENNReal.ofReal lam + ∑' j, if m ≤ j then G j else 0 := by
      intro m
      unfold weightedEntropyTail
      refine iSup_le fun x => ?_
      obtain ⟨hx0, hx1⟩ := x.2
      calc (∑' j, if m ≤ j then ENNReal.ofReal (scalarEta (x.val j) / h j) else 0)
          ≤ ∑' j, ((if m ≤ j then ENNReal.ofReal (lam * x.val j) else 0) +
              (if m ≤ j then G j else 0)) := by
            refine ENNReal.tsum_le_tsum fun j => ?_
            split_ifs with hmj
            · calc ENNReal.ofReal (scalarEta (x.val j) / h j)
                  ≤ ENNReal.ofReal (lam * x.val j + Real.exp (-1 - lam * h j) / h j) :=
                    ENNReal.ofReal_le_ofReal
                      (eta_div_le_aux _ _ _ (hx0 j) (hpos j) hlam.le)
                _ ≤ _ := ENNReal.ofReal_add_le
            · simp
        _ = (∑' j, if m ≤ j then ENNReal.ofReal (lam * x.val j) else 0) +
              ∑' j, if m ≤ j then G j else 0 := ENNReal.tsum_add
        _ ≤ ENNReal.ofReal lam * (∑' j, ENNReal.ofReal (x.val j)) +
              ∑' j, if m ≤ j then G j else 0 := by
            gcongr
            calc (∑' j, if m ≤ j then ENNReal.ofReal (lam * x.val j) else 0)
                ≤ ∑' j, ENNReal.ofReal lam * ENNReal.ofReal (x.val j) := by
                  refine ENNReal.tsum_le_tsum fun j => ?_
                  split_ifs
                  · rw [ENNReal.ofReal_mul hlam.le]
                  · exact zero_le'
              _ = _ := ENNReal.tsum_mul_left
        _ ≤ ENNReal.ofReal lam * 1 + ∑' j, if m ≤ j then G j else 0 := by gcongr
        _ = _ := by rw [mul_one]
    have hlim : Tendsto (fun m => ENNReal.ofReal lam + ∑' j, if m ≤ j then G j else 0)
        atTop (nhds (ENNReal.ofReal lam + 0)) := tendsto_const_nhds.add htail
    rw [add_zero] at hlim
    filter_upwards [hlim.eventually_lt_const hra] with m hm
    exact lt_of_le_of_lt (hbound m) hm

end
