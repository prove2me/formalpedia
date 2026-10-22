-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.majority_weight_strict_decrease
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:19:07.378343+00:00
-- url     : https://prove2.me/submissions/6de76850-9e51-4dba-9f22-cb4e9db863ac

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)


def g74f_c (n k : ℕ) : ℝ := (Nat.choose n k : ℝ)
def g74f_D (n k : ℕ) : ℝ := g74f_c n k - if k = 0 then 0 else g74f_c n (k-1)
def g74f_S (n h : ℕ) : ℝ := ∑ k ∈ Finset.range (h+1), g74f_D n k * (((n:ℝ) - h - k) / ((n:ℝ) - 2*k))
def g74f_T (n h : ℕ) : ℝ := ∑ k ∈ Finset.range (h+1), g74f_D n k / ((n:ℝ) - 2*k)
def g74f_E (n m : ℕ) : ℝ := recurrenceB n (m+1) * g74f_c n (m+1) - g74f_D n (m+1)

lemma g74f_ne (n k : ℕ) (hodd : Odd n) : ((n:ℝ) - 2*k) ≠ 0 := by
  intro h
  obtain ⟨r, rfl⟩ := hodd
  push_cast at h
  have : ((2*r+1 : ℕ) : ℝ) = ((2*k : ℕ) : ℝ) := by push_cast; linarith
  have := Nat.cast_injective this
  omega

lemma g74f_mwf (n h : ℕ) : majorityWeightFidelity n h = g74f_S n h / g74f_c n h := by
  unfold majorityWeightFidelity g74f_S schurWeightProbability g74f_D g74f_c
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma g74f_Sstep (n m : ℕ) (hodd : Odd n) :
    g74f_S n (m+1) = g74f_S n m - g74f_T n m + g74f_D n (m+1) := by
  unfold g74f_S g74f_T
  rw [Finset.sum_range_succ (n := m+1)]
  have h1 : g74f_D n (m+1) * (((n:ℝ) - ((m+1:ℕ):ℝ) - ((m+1:ℕ):ℝ)) / ((n:ℝ) - 2*((m+1:ℕ):ℝ))) = g74f_D n (m+1) := by
    have := g74f_ne n (m+1) hodd
    rw [show ((n:ℝ) - ((m+1:ℕ):ℝ) - ((m+1:ℕ):ℝ)) = ((n:ℝ) - 2*((m+1:ℕ):ℝ)) by ring, div_self this, mul_one]
  rw [h1, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

lemma g74f_Tstep (n m : ℕ) :
    g74f_T n (m+1) = g74f_T n m + g74f_D n (m+1) / ((n:ℝ) - 2*((m+1 : ℕ) : ℝ)) := by
  unfold g74f_T
  rw [Finset.sum_range_succ]

lemma g74f_crel (n m : ℕ) (hm : m ≤ n) :
    g74f_c n (m+1) * ((m:ℝ)+1) = g74f_c n m * ((n:ℝ) - m) := by
  unfold g74f_c
  have := Nat.choose_succ_right_eq n m
  have h2 : ((n.choose (m+1) * (m+1) : ℕ) : ℝ) = ((n.choose m * (n-m) : ℕ) : ℝ) := by rw [this]
  push_cast [Nat.cast_sub hm] at h2
  linarith

lemma g74f_cpos (n m : ℕ) (hm : m ≤ n) : 0 < g74f_c n m := by
  unfold g74f_c; exact_mod_cast Nat.choose_pos hm

lemma g74f_BI (n m : ℕ) (hodd : Odd n) (hm : 2*m+5 ≤ n) :
    ((n:ℝ) - 2*m) * g74f_E n m + g74f_D n (m+1) = ((n:ℝ) - 2*m - 2) * g74f_E n (m+1) := by
  have r1 := g74f_crel n m (by omega)
  have r2 := g74f_crel n (m+1) (by omega)
  have hnm : ((m:ℝ) + 5) ≤ n - m := by
    have : ((2*m+5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hm
    push_cast at this; linarith
  have hm0 : (0:ℝ) ≤ m := by positivity
  unfold g74f_E g74f_D recurrenceB
  simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
    show m + 1 + 1 = m + 2 from rfl, show m + 2 - 1 = m + 1 from rfl]
  push_cast at r2 ⊢
  have d5 : ((n:ℝ) - m) ≠ 0 := by intro h; linarith
  have hc0 : g74f_c n m = g74f_c n (m+1) * ((m:ℝ)+1) / ((n:ℝ) - m) := by
    rw [r1, mul_div_assoc, div_self d5, mul_one]
  have hc2 : g74f_c n (m+2) = g74f_c n (m+1) * ((n:ℝ) - (m+1)) / ((m:ℝ)+1+1) := by
    rw [eq_div_iff (by positivity), r2]
  rw [hc0, hc2]
  have d1 : ((n:ℝ) - 2*((m:ℝ)+1) + 2) ≠ 0 := by intro h; linarith
  have d2 : ((n:ℝ) - ((m:ℝ)+1) + 1) ≠ 0 := by intro h; linarith
  have d3 : ((n:ℝ) - 2*((m:ℝ)+2) + 2) ≠ 0 := by intro h; linarith
  have d4 : ((n:ℝ) - ((m:ℝ)+2) + 1) ≠ 0 := by intro h; linarith
  have d6 : ((m:ℝ)+1+1) ≠ 0 := by positivity
  simp only [and_false, ↓reduceIte]
  field_simp
  ring

lemma g74f_L (n : ℕ) (hodd : Odd n) : ∀ m, 2*m+3 ≤ n →
    2 * g74f_S n m = ((n:ℝ) - 2*m) * (g74f_T n m + g74f_E n m) := by
  intro m
  induction m with
  | zero =>
    intro hn
    have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n:ℝ) ≠ 0 := by intro h; linarith
    unfold g74f_S g74f_T g74f_E g74f_D recurrenceB g74f_c
    simp
    field_simp
    ring
  | succ m ih =>
    intro hn
    have := ih (by omega)
    rw [g74f_Sstep n m hodd, g74f_Tstep n m]
    have hb := g74f_BI n m hodd (by omega)
    have hne := g74f_ne n (m+1) hodd
    push_cast at hne ⊢
    have hne' : ((n:ℝ) - 2*m - 2) ≠ 0 := by intro h; apply hne; linarith
    have key : ((n:ℝ) - 2*((m:ℝ)+1)) * (g74f_D n (m+1) / ((n:ℝ) - 2*((m:ℝ)+1))) = g74f_D n (m+1) := by
      field_simp
    linear_combination this + hb - key

lemma g74f_rec (n : ℕ) (hodd : Odd n) (m : ℕ) (hm : 2*m+3 ≤ n) :
    majorityWeightFidelity n (m+1) = recurrenceA n (m+1) * majorityWeightFidelity n m + recurrenceB n (m+1) := by
  rw [g74f_mwf, g74f_mwf]
  have hL := g74f_L n hodd m hm
  have hs := g74f_Sstep n m hodd
  have r1 := g74f_crel n m (by omega)
  have p0 := g74f_cpos n m (by omega)
  have p1 := g74f_cpos n (m+1) (by omega)
  have hnm : ((m:ℝ) + 3) ≤ n - m := by
    have : ((2*m+3 : ℕ) : ℝ) ≤ n := by exact_mod_cast hm
    push_cast at this; linarith
  have hm0 : (0:ℝ) ≤ m := by positivity
  have d5 : ((n:ℝ) - 2*m) ≠ 0 := by intro h; linarith
  have hT : g74f_T n m = 2 * g74f_S n m / ((n:ℝ) - 2*m) - g74f_E n m := by
    rw [hL]; field_simp; ring
  rw [hs, hT]
  unfold g74f_E recurrenceA
  push_cast
  have d1 : ((n:ℝ) - 2*((m:ℝ)+1) + 2) ≠ 0 := by intro h; linarith
  have d2 : ((n:ℝ) - ((m:ℝ)+1) + 1) ≠ 0 := by intro h; linarith
  have d6 : ((n:ℝ) - m) ≠ 0 := by intro h; linarith
  have hc0 : g74f_c n m = g74f_c n (m+1) * ((m:ℝ)+1) / ((n:ℝ) - m) := by
    rw [r1, mul_div_assoc, div_self d6, mul_one]
  rw [hc0]
  have d7 : g74f_c n (m+1) ≠ 0 := p1.ne'
  field_simp
  ring

lemma g74f_dstep (N M x y : ℝ) (hM : 0 ≤ M) (hN : 2*M+3 ≤ N)
    (hy : y = ((N - 2*(M+1)) * (M+1)) / ((N - 2*(M+1) + 2) * (N - (M+1) + 1)) * x +
      (4 * (M+1)^2 - (4 * N + 5) * (M+1) + (N + 1) * (N + 2)) / ((N - 2*(M+1) + 2) * (N - (M+1) + 1)))
    (hx : (N^2 - 4*N*(M+1) + 3*N + 4*(M+1)^2 - 4*(M+1) + 2) * (1 - x) < M + 1) :
    y < x ∧ (2*M+5 ≤ N → (N^2 - 4*N*(M+2) + 3*N + 4*(M+2)^2 - 4*(M+2) + 2) * (1 - y) < M + 2) := by
  have hden : 0 < (N - 2*(M+1) + 2) * (N - (M+1) + 1) := by
    apply mul_pos <;> linarith
  have e : y * ((N - 2*(M+1) + 2) * (N - (M+1) + 1)) =
      ((N - 2*(M+1)) * (M+1)) * x + (4 * (M+1)^2 - (4 * N + 5) * (M+1) + (N + 1) * (N + 2)) := by
    have := hden.ne'
    rw [hy, div_mul_eq_mul_div, ← add_div, div_mul_cancel₀ _ this]
  set den := (N - 2*(M+1) + 2) * (N - (M+1) + 1) with hd
  set q1 := N^2 - 4*N*(M+1) + 3*N + 4*(M+1)^2 - 4*(M+1) + 2 with hq1
  have ha : 0 < (N - 2*(M+1)) * (M+1) := by apply mul_pos <;> linarith
  have e1 : (x - y) * den = (M+1) - q1 * (1 - x) := by
    rw [hd, hq1]; linear_combination -e
  have hxy : 0 < (x - y) * den := by rw [e1]; linarith
  refine ⟨by nlinarith [pos_of_mul_pos_left hxy hden.le], fun h5 => ?_⟩
  have hq1p : 0 < q1 := by rw [hq1]; nlinarith
  have e2 : (1 - y) * den = ((N - 2*(M+1)) * (M+1)) * (1 - x) + (M+1) := by
    rw [hd]; linear_combination -e
  -- q1 (1-y) < M+1
  have h3 : q1 * (1 - y) * den < (M+1) * den := by
    have : q1 * (1 - y) * den = ((N - 2*(M+1)) * (M+1)) * (q1 * (1 - x)) + (M+1) * q1 := by
      rw [mul_assoc, e2]; ring
    rw [this]
    have hden' : den = ((N - 2*(M+1)) * (M+1)) + q1 := by rw [hd, hq1]; ring
    rw [hden']
    nlinarith
  have h4 : q1 * (1 - y) < M + 1 := lt_of_mul_lt_mul_right h3 hden.le
  have hq12 : (N^2 - 4*N*(M+2) + 3*N + 4*(M+2)^2 - 4*(M+2) + 2) ≤ q1 := by rw [hq1]; nlinarith
  by_cases hy1 : 1 - y ≤ 0
  · have : 0 ≤ (N^2 - 4*N*(M+2) + 3*N + 4*(M+2)^2 - 4*(M+2) + 2) := by nlinarith
    nlinarith
  · push Not at hy1
    nlinarith

lemma g74f_inv (n : ℕ) (hodd : Odd n) : ∀ m : ℕ, 2*m+3 ≤ n →
    ((n:ℝ)^2 - 4*n*((m:ℝ)+1) + 3*n + 4*((m:ℝ)+1)^2 - 4*((m:ℝ)+1) + 2) * (1 - majorityWeightFidelity n m) < (m:ℝ) + 1 ∧
    majorityWeightFidelity n (m+1) < majorityWeightFidelity n m := by
  intro m
  induction m with
  | zero =>
    intro hn
    have h0 : majorityWeightFidelity n 0 = 1 := by
      have h1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hn' : (n:ℝ) ≠ 0 := by intro h; linarith
      simp [majorityWeightFidelity, schurWeightProbability, hn']
    have hx : ((n:ℝ)^2 - 4*n*(((0:ℕ):ℝ)+1) + 3*n + 4*(((0:ℕ):ℝ)+1)^2 - 4*(((0:ℕ):ℝ)+1) + 2) * (1 - majorityWeightFidelity n 0) < ((0:ℕ):ℝ) + 1 := by
      rw [h0]; norm_num
    refine ⟨hx, ?_⟩
    have hr := g74f_rec n hodd 0 hn
    unfold recurrenceA recurrenceB at hr
    push_cast at hr hx
    have hN : (2*(0:ℝ)+3) ≤ n := by exact_mod_cast hn
    exact (g74f_dstep n 0 _ _ le_rfl hN (by simpa using hr) (by simpa using hx)).1
  | succ m ih =>
    intro hn
    obtain ⟨hx, -⟩ := ih (by omega)
    have hr := g74f_rec n hodd m (by omega)
    unfold recurrenceA recurrenceB at hr
    push_cast at hr
    have hN : (2*(m:ℝ)+3) ≤ n := by exact_mod_cast (show 2*m+3 ≤ n by omega)
    have hN5 : (2*(m:ℝ)+5) ≤ n := by exact_mod_cast (show 2*m+5 ≤ n by omega)
    have hm0 : (0:ℝ) ≤ m := by positivity
    have st := (g74f_dstep n m _ _ hm0 hN hr hx).2 hN5
    refine ⟨?_, ?_⟩
    · push_cast
      convert st using 1 <;> ring
    · have hr2 := g74f_rec n hodd (m+1) hn
      unfold recurrenceA recurrenceB at hr2
      push_cast at hr2
      have hm1 : (0:ℝ) ≤ (m:ℝ)+1 := by positivity
      have hN' : (2*((m:ℝ)+1)+3) ≤ n := by
        have : ((2*(m+1)+3 : ℕ):ℝ) ≤ n := by exact_mod_cast hn
        push_cast at this; linarith
      refine (g74f_dstep n ((m:ℝ)+1) _ _ hm1 hN' ?_ ?_).1
      · first | exact hr2 | (rw [hr2]; ring)
      · convert st using 1 <;> ring

theorem solution (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ∀ h j : ℕ, h < j → j ≤ (n-1)/2 → majorityWeightFidelity n j < majorityWeightFidelity n h := by
  intro h j hhj hj
  induction j with
  | zero => omega
  | succ j ih =>
    have step := (g74f_inv n hodd j (by omega)).2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hhj with hlt | heq
    · exact step.trans (ih hlt (by omega))
    · subst heq; exact step

end
