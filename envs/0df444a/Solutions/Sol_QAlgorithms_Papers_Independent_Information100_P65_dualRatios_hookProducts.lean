-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P65.dualRatios_hookProducts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:46:51.565813+00:00
-- url     : https://prove2.me/submissions/7a092776-6b50-42a7-9611-e1967f61978c

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P65

noncomputable section

namespace X4P65

open QAlgorithms.Papers.Independent.Information100.P65

def fac (r : ℕ → ℕ) (a b : ℕ) : ℝ :=
  (((r a : ℝ) - (a : ℝ)) - ((r b : ℝ) - (b : ℝ))) / ((b : ℝ) - (a : ℝ))

lemma wd_succ (r : ℕ → ℕ) (n : ℕ) :
    weylDimension r (n + 1) = weylDimension r n * ∏ a ∈ Finset.range n, fac r a n := by
  unfold weylDimension
  rw [Finset.prod_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [Finset.prod_Ico_succ_top (by omega)]
  rfl

lemma comp_le (μ : YoungDiagram) (R d a b : ℕ) (hab : a ≤ b) (hb : b < d) :
    complementRows μ R d b ≤ complementRows μ R d a := by
  unfold complementRows
  rw [if_pos (by omega), if_pos (by omega)]
  exact Nat.sub_le_sub_left (μ.rowLen_anti _ _ (by omega)) R

lemma wd_ne (μ : YoungDiagram) (R d n : ℕ) (hn : n ≤ d) :
    weylDimension (complementRows μ R d) n ≠ 0 := by
  unfold weylDimension
  refine Finset.prod_ne_zero_iff.2 fun a ha => Finset.prod_ne_zero_iff.2 fun b hb => ?_
  simp only [Finset.mem_range, Finset.mem_Ico] at ha hb
  have hc : (complementRows μ R d b : ℝ) ≤ complementRows μ R d a := by
    exact_mod_cast comp_le μ R d a b (by omega) (by omega)
  have hab' : a < b := by omega
  have hab : (a : ℝ) < b := by exact_mod_cast hab'
  exact div_ne_zero (ne_of_gt (by linarith)) (ne_of_gt (by linarith))

lemma added_eq (d : ℕ) (lower upper : YoungDiagram) (j R : ℕ)
    (hpair : IsBoxPair d lower upper j) (hR : upper.rowLen 0 ≤ R) :
    addedRows (complementRows upper R d) (d - 1 - j) = complementRows lower R d := by
  obtain ⟨hd, -, -, hj, hu⟩ := hpair
  have hle : upper.rowLen j ≤ R := (upper.rowLen_anti 0 j (Nat.zero_le _)).trans hR
  have hj1 : upper.rowLen j = lower.rowLen j + 1 := by
    have := hu j; simpa [addedRows] using this
  funext a
  have hua := hu (d - 1 - a)
  have hlR : lower.rowLen (d - 1 - a) ≤ R := by
    have h1 : lower.rowLen (d - 1 - a) ≤ upper.rowLen (d - 1 - a) := by
      rw [hu]; exact Nat.le_add_right _ _
    exact h1.trans ((upper.rowLen_anti 0 (d - 1 - a) (Nat.zero_le _)).trans hR)
  have huR : upper.rowLen (d - 1 - a) ≤ R := (upper.rowLen_anti 0 _ (Nat.zero_le _)).trans hR
  simp only [addedRows, complementRows] at hua ⊢
  split_ifs at hua ⊢ <;> omega

/-- one step of the ratio recursion -/
lemma step (c : ℕ → ℕ) (j' n : ℕ) (hn : j' < n)
    (hW : weylDimension c n ≠ 0)
    (hf : ∀ a < n, fac c a n ≠ 0)
    (hx : ((c j' : ℝ) - j') - ((c n : ℝ) - n) ≠ 0) :
    dimensionRatio c j' (n + 1) = dimensionRatio c j' n *
      (((((c j' : ℝ) - j') - ((c n : ℝ) - n)) + 1) / (((c j' : ℝ) - j') - ((c n : ℝ) - n))) := by
  set x := ((c j' : ℝ) - j') - ((c n : ℝ) - n) with hxdef
  unfold dimensionRatio
  rw [wd_succ, wd_succ]
  have hP : ∏ a ∈ Finset.range n, fac (addedRows c j') a n =
      (∏ a ∈ Finset.range n, fac c a n) * ((x + 1) / x) := by
    have : ∀ a ∈ Finset.range n, fac (addedRows c j') a n =
        fac c a n * (if a = j' then (x + 1) / x else 1) := by
      intro a ha
      rw [Finset.mem_range] at ha
      have hnj : n ≠ j' := by omega
      by_cases haj : a = j'
      · subst haj
        rw [if_pos rfl]
        have hden : (n : ℝ) - a ≠ 0 := by
          have : (a : ℝ) < n := by exact_mod_cast ha
          linarith
        simp only [fac, addedRows, if_pos rfl, if_neg hnj]
        push_cast
        field_simp
        ring
      · rw [if_neg haj, mul_one]
        simp only [fac, addedRows, if_neg haj, if_neg hnj, add_zero]
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_ite_eq']
    rw [if_pos (Finset.mem_range.2 hn)]
  rw [hP]
  have hPn : ∏ a ∈ Finset.range n, fac c a n ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a ha => hf a (Finset.mem_range.1 ha)
  field_simp

end X4P65

open QAlgorithms.Papers.Independent.Information100.P65 in
theorem solution {d j R k : ℕ} (lower upper : YoungDiagram)
    (hpair : IsBoxPair d lower upper j) (hR : upper.rowLen 0 ≤ R)
    (hk : 1 ≤ k) (hkj : k ≤ j + 1) :
    dimensionRatio (complementRows upper R d) (d - 1 - j) (d - 1 - j + k) /
      dimensionRatio (complementRows upper R d) (d - 1 - j) d =
      ∏ a ∈ Finset.range (j + 1 - k),
        (1 - 1 / (hookLength upper a (upper.rowLen j - 1) : ℝ)) := by
  classical
  have hpair' := hpair
  obtain ⟨hd, hl0, hu0, hj, hu⟩ := hpair'
  set c := complementRows upper R d with hc
  set j' := d - 1 - j with hj'
  have hadd := X4P65.added_eq d lower upper j R hpair hR
  -- nonvanishing
  have hW : ∀ n ≤ d, weylDimension c n ≠ 0 := fun n hn => X4P65.wd_ne upper R d n hn
  have hW' : ∀ n ≤ d, weylDimension (addedRows c j') n ≠ 0 := by
    intro n hn; rw [hadd]; exact X4P65.wd_ne lower R d n hn
  have hκ : ∀ n ≤ d, dimensionRatio c j' n ≠ 0 := fun n hn =>
    div_ne_zero (hW' n hn) (hW n hn)
  have hf : ∀ n < d, ∀ a < n, X4P65.fac c a n ≠ 0 := by
    intro n hn a ha
    have h1 : (c n : ℝ) ≤ c a := by exact_mod_cast X4P65.comp_le upper R d a n (by omega) hn
    have h2 : (a : ℝ) < n := by exact_mod_cast ha
    exact div_ne_zero (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
  have hxpos : ∀ n < d, j' < n → 0 < ((c j' : ℝ) - j') - ((c n : ℝ) - n) := by
    intro n hn hjn
    have h1 : (c n : ℝ) ≤ c j' := by exact_mod_cast X4P65.comp_le upper R d j' n (by omega) hn
    have h2 : (j' : ℝ) < n := by exact_mod_cast hjn
    linarith
  -- ratio of consecutive terms
  have hq : ∀ n < d, j' < n → dimensionRatio c j' n / dimensionRatio c j' (n + 1) =
      1 - 1 / ((((c j' : ℝ) - j') - ((c n : ℝ) - n)) + 1) := by
    intro n hn hjn
    have hx := hxpos n hn hjn
    rw [X4P65.step c j' n hjn (hW n hn.le) (hf n hn) hx.ne']
    have := hκ n hn.le
    field_simp
    ring
  -- telescoping
  have htel : ∀ m, j' + k + m ≤ d → dimensionRatio c j' (j' + k) / dimensionRatio c j' (j' + k + m) =
      ∏ i ∈ Finset.range m, (1 - 1 / ((((c j' : ℝ) - j') - ((c (j' + k + i) : ℝ) - (j' + k + i : ℕ))) + 1)) := by
    intro m
    induction m with
    | zero => intro _; rw [add_zero, Finset.prod_range_zero, div_self (hκ _ (by omega))]
    | succ m ih =>
      intro hm
      rw [Finset.prod_range_succ, ← ih (by omega), ← hq (j' + k + m) (by omega) (by omega),
        ← add_assoc]
      have := hκ (j' + k + m) (by omega)
      field_simp
  have hd' : j' + k + (j + 1 - k) = d := by omega
  rw [← hd', htel (j + 1 - k) hd'.le, ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  congr 2
  -- identify the hook length
  set a := i with ha
  set n := j' + k + (j + 1 - k - 1 - i) with hn
  have hna : n = d - 1 - a := by omega
  have hlj : lower.rowLen (j + 1) ≤ lower.rowLen j := lower.rowLen_anti _ _ (by omega)
  have hj1 : upper.rowLen j = lower.rowLen j + 1 := by
    have := hu j; simpa [X4P65.added_eq, addedRows] using this
  have hj2 : upper.rowLen (j + 1) = lower.rowLen (j + 1) := by
    have := hu (j + 1); simpa [addedRows] using this
  have hcol : upper.colLen (upper.rowLen j - 1) = j + 1 := by
    apply le_antisymm
    · by_contra h
      push_neg at h
      have hm : (j + 1, upper.rowLen j - 1) ∈ upper := YoungDiagram.mem_iff_lt_colLen.2 (by omega)
      have := YoungDiagram.mem_iff_lt_rowLen.1 hm
      omega
    · have hm : (j, upper.rowLen j - 1) ∈ upper := YoungDiagram.mem_iff_lt_rowLen.2 (by omega)
      exact YoungDiagram.mem_iff_lt_colLen.1 hm
  have haj : upper.rowLen j ≤ upper.rowLen a := upper.rowLen_anti _ _ (by omega)
  have haR : upper.rowLen a ≤ R := (upper.rowLen_anti 0 a (Nat.zero_le _)).trans hR
  have hcj : c j' = R - upper.rowLen j := by
    simp only [hc, complementRows]; rw [if_pos (by omega)]; congr 2; omega
  have hcn : c n = R - upper.rowLen a := by
    simp only [hc, complementRows]; rw [if_pos (by omega)]; congr 2; omega
  have E : c j' + n + 1 = hookLength upper a (upper.rowLen j - 1) + c n + j' := by
    rw [hcj, hcn]
    unfold hookLength
    rw [hcol]
    omega
  have E' := congrArg (Nat.cast : ℕ → ℝ) E
  push_cast at E'
  linarith
