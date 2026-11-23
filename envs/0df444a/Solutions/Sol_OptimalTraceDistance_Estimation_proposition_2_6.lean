-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.proposition_2_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T08:54:01.593987+00:00
-- url     : https://prove2.me/submissions/8a705c10-f2fb-4d89-b032-c6e8af831011
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_A_1
import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_B_2
import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_3
import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_5
import Theorems.Thm_MatrixSpectral_eigenvalue_count_le_add_rank

noncomputable section
namespace OTDDyadic
lemma exists_pow_ge {x : ℝ} (hx : 0 < x) (c : ℝ) : ∃ l : ℕ, c ≤ (2:ℝ)^l * x := by
  obtain ⟨l, hl⟩ := pow_unbounded_of_one_lt (c / x) (by norm_num : (1:ℝ) < 2)
  exact ⟨l, by rw [div_lt_iff₀ hx] at hl; linarith⟩

/-- `∑ 2^{-l}` over the dyadic scales with `2^l x ≥ 1` is at most `2x`. -/
lemma D1 {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∑ l ∈ Finset.range N, (if 1 ≤ (2:ℝ)^l * x then ((2:ℝ)^l)⁻¹ else 0) ≤ 2 * x := by
  classical
  have hex := exists_pow_ge hx 1
  set n0 := Nat.find hex with hn0
  have hspec : 1 ≤ (2:ℝ)^n0 * x := Nat.find_spec hex
  have hle : ∀ l ∈ Finset.range N, (if 1 ≤ (2:ℝ)^l * x then ((2:ℝ)^l)⁻¹ else 0) ≤
      (if n0 ≤ l then (1/2:ℝ)^l else 0) := by
    intro l _
    split_ifs with h1 h2
    · rw [one_div, inv_pow]
    · exact absurd (Nat.find_min' hex h1) h2
    · positivity
    · exact le_rfl
  refine (Finset.sum_le_sum hle).trans ?_
  rw [← Finset.sum_filter]
  have hf : (Finset.range N).filter (fun l => n0 ≤ l) ⊆ Finset.Ico n0 (max N n0) := by
    intro l hl; simp only [Finset.mem_filter, Finset.mem_range] at hl
    simp only [Finset.mem_Ico]; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hf (fun _ _ _ => by positivity)).trans ?_
  refine (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans ?_
  have : (1/2:ℝ)^n0 ≤ x := by
    rw [one_div, inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]; linarith
  have e : (1/2:ℝ)^n0 / (1 - 1/2) = 2 * (1/2)^n0 := by ring
  linarith

/-- `∑ 2^l x` over the scales with `2^l x < c` is at most `2c`. -/
lemma D2 {x : ℝ} (hx : 0 ≤ x) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∑ l ∈ Finset.range N, (if (2:ℝ)^l * x < c then (2:ℝ)^l * x else 0) ≤ 2 * c := by
  classical
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0; simp; linarith
  have hex := exists_pow_ge hpos c
  set n1 := Nat.find hex with hn1
  have hspec : c ≤ (2:ℝ)^n1 * x := Nat.find_spec hex
  have hle : ∀ l ∈ Finset.range N, (if (2:ℝ)^l * x < c then (2:ℝ)^l * x else 0) ≤
      (if l < n1 then (2:ℝ)^l * x else 0) := by
    intro l _
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; push_neg at h2
      have : (2:ℝ)^n1 * x ≤ (2:ℝ)^l * x :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h2) hx
      linarith
    · positivity
    · exact le_rfl
  refine (Finset.sum_le_sum hle).trans ?_
  rw [← Finset.sum_filter]
  have hf : (Finset.range N).filter (fun l => l < n1) ⊆ Finset.range n1 := by
    intro l hl; simp only [Finset.mem_filter, Finset.mem_range] at hl
    simp only [Finset.mem_range]; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hf (fun _ _ _ => by positivity)).trans ?_
  rw [← Finset.sum_mul]
  have hg : ∑ i ∈ Finset.range n1, (2:ℝ)^i = 2^n1 - 1 := by
    have := geom_sum_eq (x := (2:ℝ)) (by norm_num) n1
    rw [this]; ring
  rw [hg]
  rcases Nat.eq_zero_or_pos n1 with h | h
  · rw [h]; simp; linarith
  · have hmin : ¬ (c ≤ (2:ℝ)^(n1 - 1) * x) := Nat.find_min hex (by omega)
    push_neg at hmin
    have e : (2:ℝ)^n1 = 2 * 2^(n1-1) := by
      rw [← pow_succ']; congr 1; omega
    nlinarith

/-- `∑ (2^l x)^{-1/2}` over the scales with `2^l x ≥ 1` is at most `4`. -/
lemma D4 {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∑ l ∈ Finset.range N, (if 1 ≤ (2:ℝ)^l * x then Real.sqrt ((2:ℝ)^l * x)⁻¹ else 0) ≤ 4 := by
  classical
  have hex := exists_pow_ge hx 1
  set n0 := Nat.find hex with hn0
  have hspec : 1 ≤ (2:ℝ)^n0 * x := Nat.find_spec hex
  set r := Real.sqrt (1/2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 3/4 := by
    rw [hr, Real.sqrt_le_left (by norm_num)]; norm_num
  have hrpos : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hle : ∀ l ∈ Finset.range N, (if 1 ≤ (2:ℝ)^l * x then Real.sqrt ((2:ℝ)^l * x)⁻¹ else 0) ≤
      (if n0 ≤ l then r^l / r^n0 else 0) := by
    intro l _
    split_ifs with h1 h2
    · have hl := Nat.find_min' hex h1
      have hk : r^l / r^n0 = r^(l - n0) := by
        rw [div_eq_iff (pow_pos hrpos _).ne', ← pow_add]; congr 1; omega
      have hsq : r^(l - n0) = Real.sqrt ((1/2:ℝ)^(l - n0)) := by
        have : (1/2:ℝ)^(l - n0) = (r^(l - n0))^2 := by
          rw [← pow_mul, mul_comm, pow_mul, hr, Real.sq_sqrt (by norm_num)]
        rw [this, Real.sqrt_sq (pow_nonneg hr0 _)]
      rw [hk, hsq]
      refine Real.sqrt_le_sqrt ?_
      have e : (2:ℝ)^l * x = 2^(l - n0) * (2^n0 * x) := by
        rw [← mul_assoc, ← pow_add]; congr 2; omega
      rw [e, one_div, inv_pow]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (l - n0)]
    · exact absurd (Nat.find_min' hex h1) h2
    · positivity
    · exact le_rfl
  refine (Finset.sum_le_sum hle).trans ?_
  rw [← Finset.sum_filter]
  have hf : (Finset.range N).filter (fun l => n0 ≤ l) ⊆ Finset.Ico n0 (max N n0) := by
    intro l hl; simp only [Finset.mem_filter, Finset.mem_range] at hl
    simp only [Finset.mem_Ico]; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hf (fun _ _ _ => by positivity)).trans ?_
  rw [← Finset.sum_div]
  have hg := geom_sum_Ico_le_of_lt_one (m := n0) (n := max N n0) hr0 (by linarith)
  rw [div_le_iff₀ (pow_pos hrpos _)]
  refine hg.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_pos hrpos n0]

/-- number of scales with `2^l < d` -/
lemma Dlog {d : ℕ} (hd : 1 ≤ d) (N : ℕ) :
    ∑ l ∈ Finset.range N, (if (2:ℝ)^l < d then (1:ℝ) else 0) ≤ Real.log d / Real.log 2 + 1 := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : (Finset.range N).filter (fun l => (2:ℝ)^l < d) ⊆ Finset.range (Nat.log 2 d + 1) := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl
    have h2 : 2^l < d := by exact_mod_cast hl.2
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) h2.le
    simp only [Finset.mem_range]; omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_range] at hc
  have hlog : (Nat.log 2 d : ℝ) ≤ Real.log d / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    have hp : ((2^(Nat.log 2 d) : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have := Real.log_le_log (by positivity) hp
    rw [Nat.cast_pow, Real.log_pow] at this
    push_cast at this; linarith
  calc ((Finset.range N).filter (fun l => (2:ℝ)^l < d)).card ≤ ((Nat.log 2 d + 1 : ℕ) : ℝ) := by
        exact_mod_cast hc
    _ ≤ _ := by push_cast; linarith


/-- the fixed-scale bound of Lemma B.2 -/
def MB (j : ℕ) (K b : ℝ) : ℝ := 2^10 * K * b * (2^16 * K^2 / b)^j / ((2*j).factorial : ℝ)

lemma term_bound (j : ℕ) {K a m : ℝ} (l : ℕ) (hK0 : 0 ≤ K) (ha : 0 ≤ a) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hK : K ≤ 2 * a * Real.sqrt m) :
    MB j K (2 * ((2:ℝ)^l)⁻¹) + MB j K ((2:ℝ)^l)⁻¹ ≤
      2^13 * a * (2^18 * a^2)^j * (m^j * ((2:ℝ)^l)^j / 2^l) / ((2*j).factorial : ℝ) := by
  set p := (2:ℝ)^l with hp
  have hp0 : 0 < p := by positivity
  set F := ((2*j).factorial : ℝ) with hF
  have hF0 : 0 < F := by positivity
  have hsq : Real.sqrt m ≤ 1 := Real.sqrt_le_one.mpr hm1
  have hK2a : K ≤ 2 * a := by nlinarith [Real.sqrt_nonneg m]
  have hKsq : K^2 ≤ 4 * a^2 * m := by
    have h1 : K^2 ≤ (2 * a * Real.sqrt m)^2 := pow_le_pow_left₀ hK0 hK 2
    rw [mul_pow, Real.sq_sqrt hm0] at h1; nlinarith
  have hpow1 : (2^16 * K^2 / (2 * p⁻¹))^j ≤ (2^16 * K^2 * p)^j := by
    refine pow_le_pow_left₀ (by positivity) ?_ j
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ 2^16 * K^2 * p := by positivity
    have e : 2^16 * K^2 * p * (2 * p⁻¹) = 2 * (2^16 * K^2) := by field_simp
    nlinarith [sq_nonneg K]
  have hpow2 : (2^16 * K^2 / p⁻¹) = 2^16 * K^2 * p := by field_simp
  have hpow3 : (2^16 * K^2 * p)^j ≤ (2^18 * a^2)^j * (m^j * p^j) := by
    rw [← mul_pow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ j
    nlinarith
  have hX : 0 ≤ (2^16 * K^2 * p)^j := by positivity
  unfold MB
  rw [hpow2]
  calc 2^10 * K * (2 * p⁻¹) * (2^16 * K^2 / (2 * p⁻¹))^j / F + 2^10 * K * p⁻¹ * (2^16 * K^2 * p)^j / F
      ≤ 2^10 * K * (2 * p⁻¹) * (2^16 * K^2 * p)^j / F + 2^10 * K * p⁻¹ * (2^16 * K^2 * p)^j / F := by
        gcongr
    _ = 3 * 2^10 * K * p⁻¹ * (2^16 * K^2 * p)^j / F := by ring
    _ ≤ 3 * 2^10 * (2 * a) * p⁻¹ * ((2^18 * a^2)^j * (m^j * p^j)) / F := by gcongr
    _ ≤ 2^13 * a * (2^18 * a^2)^j * (m^j * p^j / p) / F := by
        rw [div_le_div_iff_of_pos_right hF0]
        have : 0 ≤ a * p⁻¹ * ((2^18 * a^2)^j * (m^j * p^j)) := by positivity
        rw [div_eq_mul_inv]
        nlinarith

def Sl (d j l : ℕ) : ℝ :=
  if (2:ℝ)^l < d then ((2:ℝ)^l * (1/(d:ℝ)))^(j-1) else d * ((2:ℝ)^l)⁻¹

lemma T_bound {d : ℕ} (hd : 1 ≤ d) {j : ℕ} (hj : 1 ≤ j) (l : ℕ) :
    (min 1 ((d:ℝ) * ((2:ℝ)^l)⁻¹))^j * ((2:ℝ)^l)^j / 2^l ≤ (d:ℝ)^(j-1) * Sl d j l := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hp : (0:ℝ) < 2^l := by positivity
  unfold Sl
  split_ifs with h
  · have hm : min 1 ((d:ℝ) * ((2:ℝ)^l)⁻¹) = 1 := by
      apply min_eq_left
      rw [← div_eq_mul_inv, le_div_iff₀ hp]; linarith
    rw [hm, one_pow, one_mul, ← mul_pow, show (d:ℝ) * ((2:ℝ)^l * (1/(d:ℝ))) = 2^l by field_simp]
    rw [div_le_iff₀ hp, ← pow_succ, show j - 1 + 1 = j by omega]
  · push_neg at h
    have hm : min 1 ((d:ℝ) * ((2:ℝ)^l)⁻¹) = (d:ℝ) * ((2:ℝ)^l)⁻¹ := by
      apply min_eq_right
      rw [← div_eq_mul_inv, div_le_iff₀ hp]; linarith
    rw [hm, mul_pow, inv_pow]
    have e : (d:ℝ)^j = d^(j-1) * d := by rw [← pow_succ]; congr 1; omega
    rw [e]
    field_simp
    rfl

lemma S_sum {d : ℕ} (hd : 2 ≤ d) {j : ℕ} (hj : 1 ≤ j) (N : ℕ) :
    ∑ l ∈ Finset.range N, Sl d j l ≤ (if j = 1 then Real.log d / Real.log 2 + 3 else 4) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hx : (0:ℝ) < 1/(d:ℝ) := by positivity
  have h1 := D1 hx N
  have hsplit : ∀ l ∈ Finset.range N, Sl d j l ≤
      (if j = 1 then (if (2:ℝ)^l < d then (1:ℝ) else 0)
        else (if (2:ℝ)^l * (1/(d:ℝ)) < 1 then (2:ℝ)^l * (1/(d:ℝ)) else 0)) +
      d * (if 1 ≤ (2:ℝ)^l * (1/(d:ℝ)) then ((2:ℝ)^l)⁻¹ else 0) := by
    intro l _
    have hlt : ((2:ℝ)^l < d) ↔ (2:ℝ)^l * (1/(d:ℝ)) < 1 := by
      rw [mul_one_div, div_lt_one hdr]
    have hx0 : 0 ≤ (2:ℝ)^l * (1/(d:ℝ)) := by positivity
    unfold Sl
    by_cases h : (2:ℝ)^l < d
    · have h' := hlt.1 h
      have hB : ¬ (1 ≤ (2:ℝ)^l * (1/(d:ℝ))) := not_le.2 h'
      rw [if_pos h, if_neg hB, mul_zero, add_zero]
      rcases eq_or_ne j 1 with hj1 | hj1
      · rw [if_pos hj1, if_pos h, hj1, Nat.sub_self, pow_zero]
      · rw [if_neg hj1, if_pos h']
        exact pow_le_of_le_one hx0 h'.le (by omega)
    · have hB : 1 ≤ (2:ℝ)^l * (1/(d:ℝ)) := not_lt.1 (fun h' => h (hlt.2 h'))
      rw [if_neg h, if_pos hB]
      have : 0 ≤ (if j = 1 then (if (2:ℝ)^l < d then (1:ℝ) else 0)
        else (if (2:ℝ)^l * (1/(d:ℝ)) < 1 then (2:ℝ)^l * (1/(d:ℝ)) else 0)) := by
        split_ifs <;> positivity
      linarith
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hB : (d:ℝ) * ∑ l ∈ Finset.range N, (if 1 ≤ (2:ℝ)^l * (1/(d:ℝ)) then ((2:ℝ)^l)⁻¹ else 0) ≤ 2 := by
    calc (d:ℝ) * ∑ l ∈ Finset.range N, (if 1 ≤ (2:ℝ)^l * (1/(d:ℝ)) then ((2:ℝ)^l)⁻¹ else 0)
        ≤ d * (2 * (1/(d:ℝ))) := mul_le_mul_of_nonneg_left h1 hdr.le
      _ = 2 := by field_simp
  rcases eq_or_ne j 1 with hj1 | hj1
  · simp only [if_pos hj1]
    have := Dlog (d := d) (by omega) N
    linarith
  · simp only [if_neg hj1]
    have := D2 (le_of_lt hx) one_pos N
    linarith

lemma taylor_numeric {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (J : ℕ)
    (K : ℕ → ℝ)
    (hK : ∀ l, 1 ≤ l → l ≤ J → 0 ≤ K l ∧
      K l ≤ 2 * (2^30/ε) * Real.sqrt (min 1 ((d:ℝ) * ((2:ℝ)^l)⁻¹)))
    {j : ℕ} (hj : 1 ≤ j) :
    ∑ i ∈ Finset.range J, (MB j (K (i+1)) (2 * ((2:ℝ)^(i+1))⁻¹) + MB j (K (i+1)) ((2:ℝ)^(i+1))⁻¹) ≤
      (if j = 1 then 2^123 * Real.log d / ε^3 else
        (2^123 * d / ε^2)^j / ((d:ℝ) * ε * ((2*j).factorial : ℝ))) := by
  set a := (2:ℝ)^30/ε with ha
  have ha0 : 0 < a := by positivity
  set F := ((2*j).factorial : ℝ) with hF
  have hF0 : 0 < F := by positivity
  have hdr : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hterm : ∀ i ∈ Finset.range J,
      MB j (K (i+1)) (2 * ((2:ℝ)^(i+1))⁻¹) + MB j (K (i+1)) ((2:ℝ)^(i+1))⁻¹ ≤
        2^13 * a * (2^18 * a^2)^j * ((d:ℝ)^(j-1) * Sl d j (i+1)) / F := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    obtain ⟨hK0, hK1⟩ := hK (i+1) (by omega) (by omega)
    set m := min 1 ((d:ℝ) * ((2:ℝ)^(i+1))⁻¹)
    have hm0 : 0 ≤ m := le_min zero_le_one (by positivity)
    have hm1 : m ≤ 1 := min_le_left _ _
    refine (term_bound j (i+1) hK0 ha0.le hm0 hm1 hK1).trans ?_
    gcongr
    exact T_bound (by omega) hj (i+1)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS : ∑ i ∈ Finset.range J, Sl d j (i+1) ≤ ∑ l ∈ Finset.range (J+1), Sl d j l := by
    rw [Finset.sum_range_succ' (fun l => Sl d j l)]
    have : 0 ≤ Sl d j 0 := by unfold Sl; split_ifs <;> positivity
    linarith
  have hS2 := (hS.trans (S_sum hd hj (J+1)))
  have hc0 : 0 ≤ 2^13 * a * (2^18 * a^2)^j * (d:ℝ)^(j-1) := by positivity
  have hlog2 : (1/2:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogd : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) (by exact_mod_cast hd)
  rcases eq_or_ne j 1 with hj1 | hj1
  · subst hj1
    rw [if_pos rfl] at hS2 ⊢
    simp only [Nat.sub_self, pow_zero, mul_one, pow_one] at hS2 ⊢
    have hq : Real.log d / Real.log 2 + 3 ≤ 8 * Real.log d := by
      rw [div_add' _ _ _ (by linarith), div_le_iff₀ (by linarith)]
      nlinarith
    have hF2 : F = 2 := by rw [hF]; norm_num
    rw [hF2]
    calc 2^13 * a * (2^18 * a^2) * (1 * ∑ i ∈ Finset.range J, Sl d 1 (i+1)) / 2
        ≤ 2^13 * a * (2^18 * a^2) * (8 * Real.log d) / 2 := by
          rw [one_mul]; gcongr; linarith
      _ = 2^123 * Real.log d / ε^3 := by rw [ha]; field_simp; ring
  · rw [if_neg hj1] at hS2 ⊢
    have hj2 : 2 ≤ j := by omega
    calc 2^13 * a * (2^18 * a^2)^j * ((d:ℝ)^(j-1) * ∑ i ∈ Finset.range J, Sl d j (i+1)) / F
        ≤ 2^13 * a * (2^18 * a^2)^j * ((d:ℝ)^(j-1) * 4) / F := by gcongr
      _ = 2^15 * a * (2^18 * a^2)^j * (d:ℝ)^(j-1) / F := by ring
      _ ≤ (2^123 * d / ε^2)^j / ((d:ℝ) * ε * F) := by
        rw [div_le_div_iff₀ hF0 (by positivity)]
        have e1 : (2^123 * (d:ℝ) / ε^2)^j = (2^45)^j * (2^78 / ε^2)^j * (d:ℝ)^j := by
          rw [← mul_pow, ← mul_pow]; congr 1; field_simp
        have e2 : (2^18 * a^2)^j = (2^78/ε^2)^j := by rw [ha]; congr 1; field_simp
        have e3 : (d:ℝ)^j = d^(j-1) * d := by rw [← pow_succ]; congr 1; omega
        have h45 : (2:ℝ)^45 ≤ (2^45)^j := by
          calc (2:ℝ)^45 = (2^45)^1 := by ring
            _ ≤ (2^45)^j := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [e1, e2, e3, ha]
        have hpos : 0 < (2^78/ε^2 : ℝ)^j * (d:ℝ)^(j-1) * F * d := by positivity
        have : 2^15 * (2^30/ε) * ((d:ℝ) * ε) = 2^45 * d := by field_simp
        nlinarith [mul_le_mul_of_nonneg_right h45 hpos.le]

end OTDDyadic

open scoped BigOperators Matrix ComplexOrder
namespace OTDP26
open Matrix OptimalTraceDistance.Estimation

variable {d : ℕ}

/-! ### Taylor coefficients are determined by evaluations -/

def trP (P : Polynomial (Mat d)) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff k).trace * Polynomial.X ^ k

lemma trP_coeff (P : Polynomial (Mat d)) (j : ℕ) : (trP P).coeff j = (P.coeff j).trace := by
  unfold trP
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Matrix.trace_zero]

lemma eval_central_mul (P Q : Polynomial (Mat d)) (z : ℂ) :
    (P * Q).eval (z • (1 : Mat d)) = P.eval (z • 1) * Q.eval (z • 1) :=
  Polynomial.eval₂_mul_noncomm _ _ (fun k => (Commute.one_right _).smul_right z)

lemma eval_central_list (l : List (Polynomial (Mat d))) (z : ℂ) :
    l.prod.eval (z • (1 : Mat d)) = (l.map (fun P => P.eval (z • 1))).prod := by
  induction l with
  | nil => simp
  | cons P l ih => rw [List.prod_cons, eval_central_mul, ih]; simp

lemma trP_eval (P : Polynomial (Mat d)) (z : ℂ) :
    (trP P).eval z = (P.eval (z • (1 : Mat d))).trace := by
  conv_rhs => rw [Polynomial.eval_eq_sum_range, Matrix.trace_sum]
  unfold trP
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, smul_pow,
    one_pow, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, mul_comm]

lemma wordLine_eval (w : Word d) (X Y E₀ E₁ : Mat d) (z : ℂ) :
    (wordLine w X Y E₀ E₁).eval (z • (1 : Mat d)) = wordEval w (X + z • E₀) (Y + z • E₁) := by
  unfold wordLine wordEval
  rw [eval_central_mul, eval_central_list, List.map_map, Polynomial.eval_C]
  congr 2
  refine List.map_congr_left (fun At _ => ?_)
  simp only [Function.comp_apply, eval_central_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X]
  rw [Matrix.smul_mul, Matrix.one_mul]
  cases At.2 <;> simp

def tpoly (f : TraceExpression d) (X Y E₀ E₁ : Mat d) : Polynomial ℂ :=
  Polynomial.C f.constant + (f.words.map (fun w => trP (wordLine w X Y E₀ E₁))).sum

lemma tpoly_coeff (f : TraceExpression d) (X Y E₀ E₁ : Mat d) (j : ℕ) :
    (tpoly f X Y E₀ E₁).coeff j = taylor f X Y j E₀ E₁ := by
  unfold tpoly taylor
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_list_sum, List.map_map]
  congr 2
  refine List.map_congr_left (fun w _ => ?_)
  simp [trP_coeff]

lemma tpoly_eval (f : TraceExpression d) (X Y E₀ E₁ : Mat d) (z : ℂ) :
    (tpoly f X Y E₀ E₁).eval z = evaluate f (X + z • E₀) (Y + z • E₁) := by
  unfold tpoly evaluate
  rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_listSum, List.map_map]
  congr 2
  refine List.map_congr_left (fun w _ => ?_)
  simp [trP_eval, wordLine_eval]

theorem taylor_lin {ι : Type*} (S : Finset ι) (f : TraceExpression d) (g : ι → TraceExpression d)
    (c : ι → ℂ) (h : ∀ X Y, evaluate f X Y = ∑ i ∈ S, c i * evaluate (g i) X Y)
    (X Y : Mat d) (j : ℕ) (E₀ E₁ : Mat d) :
    taylor f X Y j E₀ E₁ = ∑ i ∈ S, c i * taylor (g i) X Y j E₀ E₁ := by
  have hp : tpoly f X Y E₀ E₁ = ∑ i ∈ S, Polynomial.C (c i) * tpoly (g i) X Y E₀ E₁ := by
    refine Polynomial.funext (fun z => ?_)
    rw [tpoly_eval, h, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, tpoly_eval]
  rw [← tpoly_coeff, hp, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_C_mul, tpoly_coeff]

/-! ### algebra of ordered bounds -/

lemma hob_congr {j : ℕ} {Φ Ψ : Mat d → Mat d → ℂ} {M : ℝ} (h : ∀ E₀ E₁, Φ E₀ E₁ = Ψ E₀ E₁)
    (hΦ : HasOrderedBound j Φ M) : HasOrderedBound j Ψ M := by
  obtain ⟨L, c, A, t, hid, hb⟩ := hΦ
  exact ⟨L, c, A, t, fun E₀ E₁ => (h E₀ E₁).symm.trans (hid E₀ E₁), hb⟩

lemma hob_mono {j : ℕ} {Φ : Mat d → Mat d → ℂ} {M M' : ℝ} (hΦ : HasOrderedBound j Φ M)
    (h : M ≤ M') : HasOrderedBound j Φ M' := by
  obtain ⟨L, c, A, t, hid, hb⟩ := hΦ
  exact ⟨L, c, A, t, hid, hb.trans h⟩

lemma hob_zero (j : ℕ) : HasOrderedBound j (fun _ _ : Mat d => (0:ℂ)) 0 :=
  ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun _ _ => by simp, by simp⟩

lemma hob_add {j : ℕ} {Φ₁ Φ₂ : Mat d → Mat d → ℂ} {M₁ M₂ : ℝ}
    (h₁ : HasOrderedBound j Φ₁ M₁) (h₂ : HasOrderedBound j Φ₂ M₂) :
    HasOrderedBound j (fun E₀ E₁ => Φ₁ E₀ E₁ + Φ₂ E₀ E₁) (M₁ + M₂) := by
  obtain ⟨L₁, c₁, A₁, t₁, hid₁, hb₁⟩ := h₁
  obtain ⟨L₂, c₂, A₂, t₂, hid₂, hb₂⟩ := h₂
  refine ⟨L₁ + L₂, Fin.append c₁ c₂, Fin.append A₁ A₂, Fin.append t₁ t₂, fun E₀ E₁ => ?_, ?_⟩
  · dsimp only
    rw [hid₁, hid₂, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact add_le_add hb₁ hb₂

lemma hob_smul {j : ℕ} {Φ : Mat d → Mat d → ℂ} {M : ℝ} (a : ℂ) (h : HasOrderedBound j Φ M) :
    HasOrderedBound j (fun E₀ E₁ => a * Φ E₀ E₁) (‖a‖ * M) := by
  obtain ⟨L, c, A, t, hid, hb⟩ := h
  refine ⟨L, fun α => a * c α, A, t, fun E₀ E₁ => ?_, ?_⟩
  · dsimp only
    rw [hid, Finset.mul_sum]; simp only [mul_assoc]
  · simp only [norm_mul, mul_assoc]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

lemma hob_sum {j : ℕ} {ι : Type*} (S : Finset ι) {Φ : ι → Mat d → Mat d → ℂ} {M : ι → ℝ}
    (h : ∀ i ∈ S, HasOrderedBound j (Φ i) (M i)) :
    HasOrderedBound j (fun E₀ E₁ => ∑ i ∈ S, Φ i E₀ E₁) (∑ i ∈ S, M i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hob_zero (d := d) j
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := hob_add h1 h2
    refine hob_congr (fun E₀ E₁ => ?_) (hob_mono this (le_of_eq ?_))
    · rw [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha]


/-! ### evaluation of expressions -/

def varOf (X Y : Mat d) (t : Bool) : Mat d := if t then Y else X

def exprEval (u : MatrixExpression d) (X Y : Mat d) : Mat d :=
  (u.map (fun w => wordEval w X Y)).sum

lemma wordEval_mul (u v : Word d) (X Y : Mat d) :
    wordEval (wordMul u v) X Y = wordEval u X Y * wordEval v X Y := by
  unfold wordMul
  rcases v with ⟨vf, vt⟩
  cases vf with
  | nil => simp [wordEval, Matrix.mul_assoc]
  | cons At xs =>
    rcases At with ⟨A, t⟩
    simp only [wordEval, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    simp only [Matrix.mul_assoc]

lemma exprEval_append (u v : MatrixExpression d) (X Y : Mat d) :
    exprEval (u ++ v) X Y = exprEval u X Y + exprEval v X Y := by
  simp [exprEval]

lemma exprEval_mul (u v : MatrixExpression d) (X Y : Mat d) :
    exprEval (exprMul u v) X Y = exprEval u X Y * exprEval v X Y := by
  unfold exprMul exprEval
  induction u with
  | nil => simp
  | cons a u ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      Matrix.add_mul]
    rw [ih]; congr 1
    rw [List.map_map]
    simp only [Function.comp_def, wordEval_mul]
    rw [← List.sum_map_mul_left]

lemma exprEval_const (A : Mat d) (X Y : Mat d) : exprEval (exprConst A) X Y = A := by
  simp [exprEval, exprConst, wordEval]

lemma exprEval_var (t : Bool) (X Y : Mat d) : exprEval (exprVar d t) X Y = varOf X Y t := by
  simp [exprEval, exprVar, wordEval, varOf]

lemma exprEval_scale (c : ℝ) (u : MatrixExpression d) (X Y : Mat d) :
    exprEval (exprScale c u) X Y = (c : ℂ) • exprEval u X Y := by
  unfold exprScale exprEval
  induction u with
  | nil => simp
  | cons a u ih =>
    simp only [List.map_cons, List.sum_cons, List.map_map, smul_add] at ih ⊢
    rw [← ih]
    simp [wordEval, Function.comp_def]

lemma exprEval_pow (u : MatrixExpression d) (X Y : Mat d) (k : ℕ) :
    exprEval (exprPow u k) X Y = exprEval u X Y ^ k := by
  induction k with
  | zero => simp [exprPow, exprEval_const]
  | succ k ih => rw [exprPow, exprEval_mul, ih, pow_succ]

lemma exprEval_flatMap {α : Type*} (l : List α) (g : α → MatrixExpression d) (X Y : Mat d) :
    exprEval (l.flatMap g) X Y = (l.map (fun k => exprEval (g k) X Y)).sum := by
  induction l with
  | nil => simp [exprEval]
  | cons k l ih => simp only [List.flatMap_cons, List.map_cons, List.sum_cons, exprEval_append, ih]

lemma exprEval_poly (p : Polynomial ℝ) (u : MatrixExpression d) (X Y : Mat d) :
    exprEval (exprPoly p u) X Y = matrixEval p (exprEval u X Y) := by
  unfold exprPoly matrixEval
  rw [exprEval_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [exprEval_scale, exprEval_pow]

lemma evaluate_traceExpr (u : MatrixExpression d) (X Y : Mat d) :
    evaluate (traceExpr u) X Y = (exprEval u X Y).trace := by
  simp only [evaluate, traceExpr, exprEval, zero_add]
  rw [Matrix.trace_list_sum, List.map_map]; rfl


lemma list_range_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma matrixEval_eq_aeval (p : Polynomial ℝ) (B : Mat d) : matrixEval p B = Polynomial.aeval B p := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, matrixEval, Polynomial.sum_def]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [show ((p.coeff k : ℝ) : ℂ) • B ^ k = (p.coeff k : ℝ) • B ^ k from
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm]

lemma matrixEval_qScaled (K : ℕ) {w : ℝ} (A : Mat d) :
    matrixEval (qScaled K w) A = (w : ℂ) • matrixEval (q K) ((w⁻¹ : ℂ) • A) := by
  rw [matrixEval_eq_aeval, matrixEval_eq_aeval, qScaled, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_comp, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_mul_assoc, one_mul]
  rw [show (w⁻¹ : ℝ) • A = ((w⁻¹ : ℝ) : ℂ) • A from (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm,
    show w • Polynomial.aeval (((w⁻¹ : ℝ) : ℂ) • A) (q K) =
      (w : ℂ) • Polynomial.aeval (((w⁻¹ : ℝ) : ℂ) • A) (q K) from
      (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm]
  push_cast; rfl

lemma matrixEval_one (A : Mat d) : matrixEval (1 : Polynomial ℝ) A = 1 := by
  rw [matrixEval_eq_aeval, map_one]

/-- the fixed-scale expression of Lemma B.2 -/
def G (K : ℕ) (b s : ℝ) : TraceExpression d :=
  let r := exprPoly (filter b) (exprVar d false)
  traceExpr (exprPoly (qScaled K s) (exprMul (exprMul r (exprVar d true)) r))

lemma filter_one : filter 1 = 1 := by unfold filter; rw [if_pos (by norm_num)]

lemma eval_G (K : ℕ) (b s : ℝ) (X Y : Mat d) :
    evaluate (G K b s) X Y = (matrixEval (qScaled K s)
      (matrixEval (filter b) X * Y * matrixEval (filter b) X)).trace := by
  simp only [G, evaluate_traceExpr, exprEval_poly, exprEval_mul, exprEval_var, varOf]
  rfl

lemma filteredY_eval (l : ℕ) (X Y : Mat d) :
    exprEval (filteredY d l) X Y =
      matrixEval (filter ((2:ℝ)^(-(l:ℤ)))) X * Y * matrixEval (filter ((2:ℝ)^(-(l:ℤ)))) X := by
  unfold filteredY
  split_ifs with h
  · subst h; simp [exprEval_var, varOf, filter_one, matrixEval_one]
  · simp only [exprEval_mul, exprEval_poly, exprEval_var, varOf]; rfl

lemma eval_F (A : ℝ) (ε : ℝ) (X Y : Mat d) :
    evaluate (multiscale A d ε) X Y = ∑ i ∈ Finset.range (scales d ε),
      (evaluate (G (d := d) (scaleDegree A d ε (i+1)) ((2:ℝ)^(-(i:ℤ))) ((2:ℝ)^(((i+1:ℕ):ℤ)-9))⁻¹) X Y -
       evaluate (G (d := d) (scaleDegree A d ε (i+1)) ((2:ℝ)^(-((i+1:ℕ):ℤ)))
        ((2:ℝ)^(((i+1:ℕ):ℤ)-9))⁻¹) X Y) := by
  unfold multiscale
  rw [evaluate_traceExpr, exprEval_flatMap, list_range_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [eval_G]
  rw [exprEval_scale, exprEval_append, exprEval_scale, exprEval_poly, exprEval_poly, exprEval_scale,
    exprEval_scale, filteredY_eval, filteredY_eval, matrixEval_qScaled, matrixEval_qScaled]
  simp only [Nat.add_sub_cancel, inv_inv, Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_one]
  simp only [smul_add, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring


section cfcsec
variable {d : ℕ}
lemma quad_conj (U : Mat d) (B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((U * B * star U) *ᵥ x) = star (star U *ᵥ x) ⬝ᵥ (B *ᵥ (star U *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  simp [Matrix.star_eq_conjTranspose]

lemma quad_diag (w : Fin d → ℂ) (y : Fin d → ℂ) :
    star y ⬝ᵥ (diagonal w *ᵥ y) = ∑ i, w i * (star (y i) * y i) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => by ring)

lemma quad_cfc {A : Mat d} (hA : A.IsHermitian) (f : ℝ → ℝ) (x : Fin d → ℂ) :
    star x ⬝ᵥ (cfc f A *ᵥ x) =
      ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) *
        (star ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i) *
          ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i)) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, quad_conj, quad_diag]
  rfl

lemma unitary_norm (U : Mat d) (hU : U ∈ unitary (Mat d)) (x : Fin d → ℂ) :
    star (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) = star x ⬝ᵥ x := by
  have := quad_conj U 1 x
  rw [mul_one, Unitary.mul_star_self_of_mem hU, one_mulVec, one_mulVec] at this
  exact this.symm

lemma sum_normsq (y : Fin d → ℂ) : star y ⬝ᵥ y = ∑ i, ((‖y i‖^2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  show y i * (starRingEnd ℂ) (y i) = _
  rw [Complex.mul_conj', Complex.ofReal_pow]


lemma inner_eq' (A : Mat d) (x : EuclideanSpace ℂ (Fin d)) :
    RCLike.re (inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) A x) x) =
      (star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  simp only [dotProduct, Pi.star_apply, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma normsq_eq (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖^2 = (star (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma opNorm_le_of_quad {A : Mat d} (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin d → ℂ, |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ c * (star x ⬝ᵥ x).re) :
    opNorm A ≤ c := by
  unfold opNorm
  have hT : (Matrix.toEuclideanCLM (𝕜 := ℂ) A : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hT]
  refine ciSup_le (fun x => ?_)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf]
  rw [inner_eq', normsq_eq]
  rcases eq_or_lt_of_le (sq_nonneg ‖x‖) with h0 | hpos
  · rw [normsq_eq] at h0; rw [← h0]; simp [hc]
  · rw [normsq_eq] at hpos
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact h _


section spec
variable {A : Mat d} (hA : A.IsHermitian)
include hA

lemma U_mem : (hA.eigenvectorUnitary : Mat d) ∈ unitary (Mat d) := (hA.eigenvectorUnitary).2

lemma cfc_explicit (f : ℝ → ℝ) : cfc f A =
    (hA.eigenvectorUnitary : Mat d) * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Mat d) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

lemma cfc_herm (f : ℝ → ℝ) : (cfc f A).IsHermitian := by
  rw [cfc_explicit hA]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp [Complex.conj_ofReal]))

lemma trace_cfc (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [cfc_explicit hA, Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem (U_mem hA),
    Matrix.one_mul, trace_diagonal]

lemma cfc_congr' {f g : ℝ → ℝ} (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    cfc f A = cfc g A := by
  rw [cfc_explicit hA, cfc_explicit hA]; simp only [h]

lemma cfc_mul' (f g : ℝ → ℝ) : cfc f A * cfc g A = cfc (fun t => f t * g t) A := by
  rw [cfc_explicit hA, cfc_explicit hA, cfc_explicit hA]
  set U := (hA.eigenvectorUnitary : Mat d)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (U_mem hA)
  calc U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * star U *
        (U * diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ)) * star U)
      = U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * (star U * U) *
          diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; push_cast; rfl

end spec

lemma opNorm_cfc_le {Y : Mat d} (hY : Y.IsHermitian) (g : ℝ → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hb : ∀ a, |g (hY.eigenvalues a)| ≤ B) : opNorm (cfc g Y) ≤ B := by
  refine opNorm_le_of_quad (cfc_herm hY g) hB0 (fun x => ?_)
  rw [quad_cfc hY g x]
  set y := star (hY.eigenvectorUnitary : Mat d) *ᵥ x
  have hyy : (star x ⬝ᵥ x) = star y ⬝ᵥ y := (unitary_norm _ (U_mem hY) x).symm
  rw [hyy, sum_normsq y]
  simp only [Complex.re_sum, Complex.ofReal_re]
  have h1 : ∀ i, (((g (hY.eigenvalues i) : ℝ) : ℂ) * (star (y i) * y i)).re = g (hY.eigenvalues i) * ‖y i‖^2 := by
    intro i
    have : star (y i) * y i = ((‖y i‖^2 : ℝ) : ℂ) := by
      rw [mul_comm]; show y i * (starRingEnd ℂ) (y i) = _
      rw [Complex.mul_conj', Complex.ofReal_pow]
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [h1]
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖y i‖)]
  exact mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)

end cfcsec

lemma opNorm_nonneg' {d : ℕ} (A : Mat d) : 0 ≤ opNorm A := norm_nonneg _

section extras
variable {d : ℕ}
lemma quad_le_opNorm (A : Mat d) (x : Fin d → ℂ) :
    |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ opNorm A * (star x ⬝ᵥ x).re := by
  have := ContinuousLinearMap.rayleighQuotient_le_norm (Matrix.toEuclideanCLM (𝕜 := ℂ) A)
    (WithLp.toLp 2 x)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] at this
  rw [inner_eq', normsq_eq] at this
  simp only [WithLp.ofLp_toLp] at this
  rcases eq_or_lt_of_le (show 0 ≤ (star x ⬝ᵥ x).re from by
      rw [sum_normsq]; simp only [Complex.re_sum, Complex.ofReal_re]; positivity) with h0 | hpos
  · have hx : x = 0 := by
      have := (h0.symm)
      rw [sum_normsq] at this
      simp only [Complex.re_sum, Complex.ofReal_re] at this
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖)).mp this
      funext i; have := h2 i (Finset.mem_univ i); simpa using this
    subst hx; simp
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at this
    exact this


lemma re_nonneg_of_psd {A : Mat d} (hA : A.PosSemidef) (x : Fin d → ℂ) :
    0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

/-- sandwich: |quad Y| ≤ quad X -/
lemma opNorm_mul_le (A B : Mat d) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm; rw [map_mul]; exact norm_mul_le _ _

lemma eig_abs_le {Y : Mat d} (hY : Y.IsHermitian) (a : Fin d) : |hY.eigenvalues a| ≤ opNorm Y := by
  set v := hY.eigenvectorBasis a
  have hv := hY.mulVec_eigenvectorBasis a
  have h1 := quad_le_opNorm Y (⇑v)
  have hn : (star (⇑v) ⬝ᵥ (⇑v : Fin d → ℂ)).re = 1 := by
    have := normsq_eq v
    rw [hY.eigenvectorBasis.orthonormal.1 a] at this
    simpa using this.symm
  rw [hv, dotProduct_smul, hn, mul_one] at h1
  have : (hY.eigenvalues a • (star (⇑v) ⬝ᵥ (⇑v : Fin d → ℂ))).re = hY.eigenvalues a := by
    rw [Complex.real_smul, Complex.re_ofReal_mul, hn, mul_one]
  rwa [this] at h1

lemma opNorm_le_trace {S : Mat d} (hS : S.PosSemidef) : opNorm S ≤ (S.trace).re := by
  have hH := hS.1
  have htr0 : 0 ≤ (S.trace).re := (Complex.nonneg_iff.1 hS.trace_nonneg).1
  refine opNorm_le_of_quad hH htr0 (fun x => ?_)
  have hid : cfc (fun t : ℝ => t) S = S := cfc_id' ℝ S hH.isSelfAdjoint
  have hq := quad_cfc hH (fun t => t) x
  rw [hid] at hq
  rw [hq]
  set y := star (hH.eigenvectorUnitary : Mat d) *ᵥ x
  have hyy : (star x ⬝ᵥ x) = star y ⬝ᵥ y := (unitary_norm _ (U_mem hH) x).symm
  rw [hyy, sum_normsq y]
  simp only [Complex.re_sum, Complex.ofReal_re]
  have h1 : ∀ i, (((hH.eigenvalues i : ℝ) : ℂ) * (star (y i) * y i)).re = hH.eigenvalues i * ‖y i‖^2 := by
    intro i
    have : star (y i) * y i = ((‖y i‖^2 : ℝ) : ℂ) := by
      rw [mul_comm]; show y i * (starRingEnd ℂ) (y i) = _
      rw [Complex.mul_conj', Complex.ofReal_pow]
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [h1]
  have hl0 : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hS.eigenvalues_nonneg i
  have htr : (S.trace).re = ∑ i, hH.eigenvalues i := by rw [hH.trace_eq_sum_eigenvalues]; simp
  have hle : ∀ i, hH.eigenvalues i ≤ (S.trace).re := fun i => by
    rw [htr]; exact Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ i)
  rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hl0 i) (sq_nonneg _))), Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _))

end extras

/-! ### scale bookkeeping -/

lemma zpow_neg_nat (l : ℕ) : (2:ℝ)^(-(l:ℤ)) = ((2:ℝ)^l)⁻¹ := by rw [_root_.zpow_neg, zpow_natCast]

lemma width_eq (i : ℕ) : ((2:ℝ)^(((i+1:ℕ):ℤ)-9))⁻¹ = 2^9 * ((2:ℝ)^(i+1))⁻¹ := by
  rw [← _root_.zpow_neg, neg_sub, zpow_sub₀ two_ne_zero, zpow_natCast, div_eq_mul_inv]; norm_num

lemma scales_facts {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2^9 * (d:ℝ) / ε ≤ (2:ℝ)^(scales d ε) ∧ (2:ℝ)^(scales d ε) < 2^10 * (d:ℝ) / ε := by
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  set z := 2^9 * (d:ℝ) / ε with hz
  have hz1 : 1 < z := by
    rw [hz, lt_div_iff₀ hε]; nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set y := Real.log z / Real.log 2 with hy
  have hy0 : 0 ≤ y := div_nonneg (Real.log_nonneg hz1.le) hl2.le
  have h2y : (2:ℝ)^y = z := by
    rw [Real.rpow_def_of_pos (by norm_num), hy, mul_div_cancel₀ _ hl2.ne', Real.exp_log (by linarith)]
  have hJ : scales d ε = ⌈y⌉₊ := rfl
  have e : (2:ℝ)^(scales d ε) = (2:ℝ)^((scales d ε : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
  constructor
  · rw [e, ← h2y]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hJ]; exact Nat.le_ceil y)
  · rw [e]
    have h1 : ((scales d ε : ℕ) : ℝ) < y + 1 := by rw [hJ]; exact Nat.ceil_lt_add_one hy0
    calc (2:ℝ)^((scales d ε : ℕ) : ℝ) < (2:ℝ)^(y+1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
      _ = 2 * z := by rw [Real.rpow_add (by norm_num), h2y, Real.rpow_one]; ring
      _ = 2^10 * (d:ℝ) / ε := by rw [hz]; ring

lemma K_facts {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (l : ℕ) (hl : l ≤ scales d ε) :
    2 ≤ scaleDegree constructionA d ε l ∧
    (scaleDegree constructionA d ε l : ℝ) ≤
      2 * (2^30/ε) * Real.sqrt (min 1 ((d:ℝ) * ((2:ℝ)^l)⁻¹)) ∧
    (2^30/ε) * Real.sqrt (min 1 ((d:ℝ) * ((2:ℝ)^l)⁻¹)) ≤ (scaleDegree constructionA d ε l : ℝ) := by
  obtain ⟨-, hJ2⟩ := scales_facts hd hε hε1
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  set m := min 1 ((d:ℝ) * ((2:ℝ)^l)⁻¹) with hm
  have hpl : (2:ℝ)^l ≤ (2:ℝ)^(scales d ε) := pow_le_pow_right₀ (by norm_num) hl
  have hm0 : ε / 2^10 ≤ m := by
    rw [hm]
    refine le_min (by rw [div_le_one (by norm_num)]; linarith) ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have : (2:ℝ)^l < 2^10 * d / ε := lt_of_le_of_lt hpl hJ2
    rw [lt_div_iff₀ hε] at this
    nlinarith
  set v := (2^30/ε) * Real.sqrt m with hv
  have hv0 : 0 ≤ v := by positivity
  have hv2 : 2 ≤ v := by
    have hsq : v^2 = (2^30/ε)^2 * m := by
      rw [hv, mul_pow, Real.sq_sqrt (le_trans (by positivity) hm0)]
    have : (4:ℝ) ≤ v^2 := by
      rw [hsq]
      calc (4:ℝ) ≤ (2^30/ε)^2 * (ε / 2^10) := by
            rw [div_pow]; field_simp
            nlinarith
        _ ≤ (2^30/ε)^2 * m := by gcongr
    nlinarith
  have hK : scaleDegree constructionA d ε l = ⌈v⌉₊ := by
    unfold scaleDegree constructionA
    rw [hv, hm, zpow_neg_nat]
  rw [hK]
  refine ⟨?_, ?_, Nat.le_ceil v⟩
  · have : (2:ℝ) ≤ ⌈v⌉₊ := hv2.trans (Nat.le_ceil v)
    exact_mod_cast this
  · have := Nat.ceil_lt_add_one hv0
    linarith

/-! ### the Taylor clause -/

lemma psd_cfc {A : Mat d} (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (cfc f A).PosSemidef := by
  rw [cfc_explicit hA]
  have hD : (diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))).PosSemidef :=
    PosSemidef.diagonal (fun i => by simpa using hf i)
  have := hD.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Mat d)
  rwa [← Matrix.star_eq_conjTranspose] at this

lemma eig_le_tr {X : Mat d} (hX : X.PosSemidef) (htr : tr X ≤ 1) (i : Fin d) :
    hX.1.eigenvalues i ≤ 1 := by
  have h0 : ∀ j, 0 ≤ hX.1.eigenvalues j := fun j => hX.eigenvalues_nonneg j
  have htr' : tr X = ∑ j, hX.1.eigenvalues j := by
    unfold tr; rw [hX.1.trace_eq_sum_eigenvalues]; simp
  have := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  linarith

lemma le_one_of_tr {X : Mat d} (hX : X.PosSemidef) (htr : tr X ≤ 1) : lePSD X 1 := by
  unfold lePSD
  have e : (1 : Mat d) - X = cfc (fun x : ℝ => 1 - x) X := by
    rw [cfc_sub (fun _ => (1:ℝ)) (fun x => x) X,
      cfc_const_one ℝ X (ha := hX.1.isSelfAdjoint), cfc_id' ℝ X hX.1.isSelfAdjoint]
  rw [e]
  exact psd_cfc hX.1 _ (fun i => by linarith [eig_le_tr hX htr i])

theorem taylor_clause {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) {X Y : Mat d}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hX0 : X.PosSemidef) (htr : tr X ≤ 1)
    (hlo : lePSD (-X) Y) (hhi : lePSD Y X) {j : ℕ} (hj : 1 ≤ j) :
    HasOrderedBound j (taylor (F d ε) X Y j)
      (if j = 1 then 2^123 * Real.log d / ε^3 else
        (2^123 * d / ε^2)^j / ((d:ℝ) * ε * ((2*j).factorial : ℝ))) := by
  set J := scales d ε with hJ
  have hd1 : 1 ≤ d := by omega
  have hε1' : ε ≤ 1 := by linarith
  have hXI := le_one_of_tr hX0 htr
  set Kn : ℕ → ℕ := fun l => scaleDegree constructionA d ε l with hKn
  set g : ℕ × Bool → TraceExpression d := fun ib => if ib.2 then
      G (d := d) (Kn (ib.1+1)) ((2:ℝ)^(-(ib.1:ℤ))) ((2:ℝ)^(((ib.1+1:ℕ):ℤ)-9))⁻¹ else
      G (d := d) (Kn (ib.1+1)) ((2:ℝ)^(-((ib.1+1:ℕ):ℤ))) ((2:ℝ)^(((ib.1+1:ℕ):ℤ)-9))⁻¹ with hg
  set c : ℕ × Bool → ℂ := fun ib => if ib.2 then 1 else -1 with hc
  set S := Finset.range J ×ˢ (Finset.univ : Finset Bool) with hS
  have hev : ∀ X Y : Mat d, evaluate (F d ε) X Y = ∑ ib ∈ S, c ib * evaluate (g ib) X Y := by
    intro X Y
    rw [show F d ε = multiscale constructionA d ε from rfl, eval_F, hS, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_bool]
    simp only [hc, hg, if_true, Bool.false_eq_true, if_false]
    ring
  have hTl := taylor_lin S (F d ε) g c hev X Y j
  -- bounds for each piece
  set MBf : ℕ × Bool → ℝ := fun ib => if ib.2 then
      OTDDyadic.MB j (Kn (ib.1+1)) (2 * ((2:ℝ)^(ib.1+1))⁻¹) else
      OTDDyadic.MB j (Kn (ib.1+1)) ((2:ℝ)^(ib.1+1))⁻¹ with hMBf
  have hpiece : ∀ ib ∈ S, HasOrderedBound j (fun E₀ E₁ => c ib * taylor (g ib) X Y j E₀ E₁) (MBf ib) := by
    intro ib hib
    obtain ⟨i, b⟩ := ib
    have hi : i < J := Finset.mem_range.1 (Finset.mem_product.1 hib).1
    obtain ⟨hK2, -, -⟩ := K_facts hd1 hε hε1' (i+1) (by omega)
    have hw := width_eq i
    have hnorm : ∀ b : Bool, ‖c (i, b)‖ = 1 := by intro b; cases b <;> simp [hc]
    cases b
    · -- fine scale b = 2^{-(i+1)}
      have hB := lemma_B_2 d (Kn (i+1)) (by omega) hK2 ((2:ℝ)^(-((i+1:ℕ):ℤ)))
        ((2:ℝ)^(((i+1:ℕ):ℤ)-9))⁻¹ (by positivity)
        (by rw [zpow_neg_nat]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
        (by rw [hw, zpow_neg_nat]; have : (0:ℝ) < ((2:ℝ)^(i+1))⁻¹ := by positivity
            nlinarith)
        (by rw [hw, zpow_neg_nat])
        X Y hX hY hX0 hXI hlo hhi j hj
      have := hob_smul (c (i, false)) hB
      rw [hnorm] at this
      refine hob_mono this (le_of_eq ?_)
      simp only [hMBf, Bool.false_eq_true, if_false, one_mul, OTDDyadic.MB, zpow_neg_nat]
    · -- coarse scale b = 2^{-i}
      have hb : (2:ℝ)^(-(i:ℤ)) = 2 * ((2:ℝ)^(i+1))⁻¹ := by
        rw [zpow_neg_nat, pow_succ, mul_inv]; field_simp
      have hB := lemma_B_2 d (Kn (i+1)) (by omega) hK2 ((2:ℝ)^(-(i:ℤ)))
        ((2:ℝ)^(((i+1:ℕ):ℤ)-9))⁻¹ (by positivity)
        (by rw [zpow_neg_nat]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
        (by rw [hw, hb]; ring_nf; rfl)
        (by rw [hw, hb]; have : (0:ℝ) < ((2:ℝ)^(i+1))⁻¹ := by positivity
            nlinarith)
        X Y hX hY hX0 hXI hlo hhi j hj
      have := hob_smul (c (i, true)) hB
      rw [hnorm] at this
      refine hob_mono this (le_of_eq ?_)
      simp only [hMBf, if_true, one_mul, OTDDyadic.MB, hb]
  have hsum := hob_sum S hpiece
  have hsum' : HasOrderedBound j (taylor (F d ε) X Y j) (∑ ib ∈ S, MBf ib) :=
    hob_congr (fun E₀ E₁ => (hTl E₀ E₁).symm) hsum
  refine hob_mono hsum' ?_
  rw [hS, Finset.sum_product]
  simp only [Fintype.sum_bool, hMBf, if_true, Bool.false_eq_true, if_false]
  refine OTDDyadic.taylor_numeric hd hε hε1' J (fun l => (Kn l : ℝ)) (fun l hl1 hlJ => ?_) hj
  obtain ⟨-, h2, -⟩ := K_facts hd1 hε hε1' l hlJ
  exact ⟨Nat.cast_nonneg _, h2⟩

lemma foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => by simp
  | (b :: l), a => by
    have ih := foldl_max_ge l (max a b)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨le_trans (le_max_left a b) ih.1, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact le_trans (le_max_right a x) ih.1
    · exact ih.2 x hx

lemma foldl_max_le : ∀ (l : List ℕ) (a b : ℕ), a ≤ b → (∀ x ∈ l, x ≤ b) → l.foldl max a ≤ b
  | [], a, b, h, _ => by simpa using h
  | (c :: l), a, b, h, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le l _ b (max_le h (hl c (by simp))) (fun x hx => hl x (by simp [hx]))

lemma len_le_deg (g : TraceExpression d) (w : Word d) (hw : w ∈ g.words) :
    w.factors.length ≤ expressionDegree g :=
  (foldl_max_ge _ 0).2 _ (List.mem_map.mpr ⟨w, hw, rfl⟩)

lemma deg_le_of (g : TraceExpression d) (b : ℕ) (h : ∀ w ∈ g.words, w.factors.length ≤ b) :
    expressionDegree g ≤ b := by
  unfold expressionDegree
  refine foldl_max_le _ 0 b (Nat.zero_le b) (fun x hx => ?_)
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact h w hw


/-! ### the degree clause -/

def LenLe (u : MatrixExpression d) (B : ℕ) : Prop := ∀ w ∈ u, w.factors.length ≤ B

lemma len_scale {u : MatrixExpression d} {B : ℕ} (c : ℝ) (h : LenLe u B) : LenLe (exprScale c u) B := by
  intro w hw
  unfold exprScale at hw
  obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
  exact h w' hw'

lemma len_mono {u : MatrixExpression d} {B B' : ℕ} (h : LenLe u B) (hB : B ≤ B') : LenLe u B' :=
  fun w hw => (h w hw).trans hB

lemma len_append {u v : MatrixExpression d} {B : ℕ} (hu : LenLe u B) (hv : LenLe v B) :
    LenLe (u ++ v) B := by
  intro w hw
  rcases List.mem_append.1 hw with h | h
  · exact hu w h
  · exact hv w h

lemma len_wordMul (a b : Word d) : (wordMul a b).factors.length = a.factors.length + b.factors.length := by
  unfold wordMul
  rcases b with ⟨bf, bt⟩
  cases bf with
  | nil => simp
  | cons At xs => simp

lemma len_mul {u v : MatrixExpression d} {B B' : ℕ} (hu : LenLe u B) (hv : LenLe v B') :
    LenLe (exprMul u v) (B + B') := by
  intro w hw
  unfold exprMul at hw
  obtain ⟨a, ha, hw⟩ := List.mem_flatMap.1 hw
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hw
  rw [len_wordMul]; exact Nat.add_le_add (hu a ha) (hv b hb)

lemma len_pow {u : MatrixExpression d} {B : ℕ} (h : LenLe u B) : ∀ k, LenLe (exprPow u k) (k * B)
  | 0 => by intro w hw; simp [exprPow, exprConst] at hw; subst hw; simp
  | k+1 => by
    have := len_mul (len_pow h k) h
    intro w hw
    have := this w hw
    rw [Nat.succ_mul]; exact this

lemma len_poly {u : MatrixExpression d} {B : ℕ} (p : Polynomial ℝ) (h : LenLe u B) :
    LenLe (exprPoly p u) (p.natDegree * B) := by
  intro w hw
  unfold exprPoly at hw
  obtain ⟨k, hk, hw⟩ := List.mem_flatMap.1 hw
  have hk' : k ∈ p.support := Finset.mem_toList.1 hk
  have := len_scale (p.coeff k) (len_pow h k) w hw
  exact this.trans (Nat.mul_le_mul_right _ (Polynomial.le_natDegree_of_mem_supp k hk'))

lemma len_var (t : Bool) : LenLe (exprVar d t) 1 := by
  intro w hw; simp [exprVar] at hw; subst hw; simp

lemma len_filteredY (l : ℕ) :
    LenLe (filteredY d l) (2 * (filter ((2:ℝ)^(-(l:ℤ)))).natDegree + 1) := by
  unfold filteredY
  split_ifs
  · intro w hw; exact (len_var true w hw).trans (by omega)
  · have h1 := len_poly (filter ((2:ℝ)^(-(l:ℤ)))) (len_var (d := d) false)
    have h2 := len_mul (len_mul h1 (len_var (d := d) true)) h1
    intro w hw; have := h2 w hw; simp only [mul_one] at this; omega

lemma natDeg_filter_sq (l : ℕ) :
    ((filter ((2:ℝ)^(-(l:ℤ)))).natDegree : ℝ)^2 ≤ 2^l := by
  set b := (2:ℝ)^(-(l:ℤ)) with hbdef
  have hb : (0:ℝ) < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hbdef, zpow_neg_nat]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h := (lemma_2_5 b hb hb1).1
  have h0 : (0:ℝ) ≤ (filter b).natDegree := Nat.cast_nonneg _
  have h2 := pow_le_pow_left₀ h0 h 2
  have e : (b ^ (-(1/2:ℝ)))^2 = b⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]; norm_num; exact Real.rpow_neg_one b
  have e2 : b⁻¹ = 2^l := by rw [hbdef, zpow_neg_nat, inv_inv]
  rw [e, e2] at h2
  exact h2

theorem degree_clause {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) :
    (expressionDegree (F d ε) : ℝ) ≤ 6 * 2^30 * Real.sqrt d / ε := by
  have hd1 : 1 ≤ d := by omega
  have hε1' : ε ≤ 1 := by linarith
  set R := 6 * 2^30 * Real.sqrt d / ε with hR
  have hR0 : 0 ≤ R := by positivity
  have hdsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (by exact_mod_cast hd1)
  -- each scale's words are short
  have key : ∀ i < scales d ε, ∀ l ∈ ({i, i+1} : Finset ℕ),
      ((scaleDegree constructionA d ε (i+1) : ℕ) : ℝ) *
        (2 * (filter ((2:ℝ)^(-(l:ℤ)))).natDegree + 1) ≤ R := by
    intro i hi l hl
    have hl' : l ≤ i + 1 := by simp at hl; omega
    obtain ⟨-, hK, -⟩ := K_facts hd1 hε hε1' (i+1) (by omega)
    set m := min 1 ((d:ℝ) * ((2:ℝ)^(i+1))⁻¹) with hm
    have hm0 : 0 ≤ m := le_min zero_le_one (by positivity)
    have hm1 : m ≤ 1 := min_le_left _ _
    set D : ℝ := ((filter ((2:ℝ)^(-(l:ℤ)))).natDegree : ℝ) with hD
    have hD0 : 0 ≤ D := Nat.cast_nonneg _
    have hD2 : D^2 ≤ 2^(i+1) := (natDeg_filter_sq l).trans (pow_le_pow_right₀ (by norm_num) hl')
    have hmd : m * 2^(i+1) ≤ d := by
      have : m ≤ (d:ℝ) * ((2:ℝ)^(i+1))⁻¹ := min_le_right _ _
      calc m * 2^(i+1) ≤ (d:ℝ) * ((2:ℝ)^(i+1))⁻¹ * 2^(i+1) := by gcongr
        _ = d := by field_simp
    have hsD : Real.sqrt m * D ≤ Real.sqrt d := by
      rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, Real.sq_sqrt hm0]
      calc m * D^2 ≤ m * 2^(i+1) := by gcongr
        _ ≤ d := hmd
    have hsm : Real.sqrt m ≤ 1 := Real.sqrt_le_one.mpr hm1
    set K : ℝ := ((scaleDegree constructionA d ε (i+1) : ℕ) : ℝ)
    have ha : 0 ≤ (2:ℝ)^30/ε := by positivity
    calc K * (2 * D + 1) = 2 * (K * D) + K := by ring
      _ ≤ 2 * (2 * (2^30/ε) * Real.sqrt m * D) + 2 * (2^30/ε) * Real.sqrt m := by gcongr
      _ = 4 * (2^30/ε) * (Real.sqrt m * D) + 2 * (2^30/ε) * Real.sqrt m := by ring
      _ ≤ 4 * (2^30/ε) * Real.sqrt d + 2 * (2^30/ε) * Real.sqrt d := by
          have h1 := mul_le_mul_of_nonneg_left hsD (by positivity : (0:ℝ) ≤ 4 * (2^30/ε))
          have h2 := mul_le_mul_of_nonneg_left (hsm.trans hdsq) (by positivity : (0:ℝ) ≤ 2 * (2^30/ε))
          linarith
      _ = R := by rw [hR]; ring
  set b := ⌊R⌋₊
  have hdeg : expressionDegree (F d ε) ≤ b := by
    refine deg_le_of _ b (fun w hw => ?_)
    have hw' : w ∈ (multiscale constructionA d ε).words := hw
    unfold multiscale traceExpr at hw'
    simp only at hw'
    obtain ⟨i, hi, hw2⟩ := List.mem_flatMap.1 hw'
    have hi' : i < scales d ε := List.mem_range.1 hi
    set K := scaleDegree constructionA d ε (i+1)
    have hqK : (q K).natDegree ≤ K := (lemma_2_3 K (K_facts hd1 hε hε1' (i+1) (by omega)).1).1
    set Bm := max (K * (2 * (filter ((2:ℝ)^(-(i:ℤ)))).natDegree + 1))
      (K * (2 * (filter ((2:ℝ)^(-((i+1:ℕ):ℤ)))).natDegree + 1)) with hBm
    have hA := len_mono (B' := Bm) (len_poly (q K) (len_scale ((2:ℝ)^(((i+1:ℕ):ℤ)-9)) (len_filteredY (d := d) i)))
      ((Nat.mul_le_mul_right _ hqK).trans (le_max_left _ _))
    have hB := len_mono (B' := Bm) (len_poly (q K) (len_scale ((2:ℝ)^(((i+1:ℕ):ℤ)-9))
      (len_filteredY (d := d) (i+1)))) ((Nat.mul_le_mul_right _ hqK).trans (le_max_right _ _))
    have hAB := len_scale ((2:ℝ)^(((i+1:ℕ):ℤ)-9))⁻¹ (len_append hA (len_scale (-1) hB))
    have hlen := hAB w hw2
    refine hlen.trans (Nat.le_floor ?_)
    rw [hBm, Nat.cast_max]
    refine max_le ?_ ?_
    · have := key i hi' i (by simp); push_cast at this ⊢; exact this
    · have := key i hi' (i+1) (by simp); push_cast at this ⊢; exact this
  have : (b : ℝ) ≤ R := Nat.floor_le hR0
  exact (Nat.cast_le.2 hdeg).trans this

open MeasureTheory

lemma traceError_eq (K : ℕ) (s : ℝ) {A : Mat d} (hA : A.IsHermitian) :
    traceError K s A = ∑ k, (|hA.eigenvalues k| - (qScaled K s).eval (hA.eigenvalues k)) := by
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have e : Aᴴ * A = cfc (fun t : ℝ => t * t) A := by
    rw [hA.eq, ← cfc_mul' hA, cfc_id' ℝ A hA.isSelfAdjoint]
  unfold traceError tr absMat
  rw [trace_sub, Complex.sub_re, e, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) A hA.isSelfAdjoint
    ((hfin.image _).continuousOn _) (hfin.continuousOn _), trace_cfc hA, matrixEval_eq_aeval,
    ← cfc_polynomial (qScaled K s) A hA.isSelfAdjoint, trace_cfc hA, Complex.re_sum, Complex.re_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Function.comp, Complex.ofReal_re]
  rw [← sq, Real.sqrt_sq_eq_abs]


lemma sign_monotone : Monotone sign := by
  intro a b hab
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have : sign a = -1 := by simp [sign, ha]
    rw [this]; unfold sign; split_ifs <;> norm_num
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · linarith
    · exact le_rfl
    · simp [sign, hb, not_lt.mpr hb.le, hb.ne']
  · have hb : 0 < b := lt_of_lt_of_le ha hab
    simp [sign, not_lt.mpr ha.le, ha.ne', not_lt.mpr hb.le, hb.ne']

lemma sign_intInt (a b : ℝ) : IntervalIntegrable sign volume a b :=
  sign_monotone.intervalIntegrable

lemma int_sign (x : ℝ) : ∫ t in (0:ℝ)..x, sign t = |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx (f := fun t => t)
      continuousOn_id (fun t ht => ?_) (sign_intInt 0 x)]
    · simp [abs_of_nonneg hx]
    · have : sign t = 1 := by unfold sign; simp [not_lt.mpr ht.1.le, ht.1.ne']
      rw [this]; exact hasDerivAt_id t
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.le
      (f := fun t => -t) continuousOn_neg (fun t ht => ?_) (sign_intInt x 0)]
    · simp [abs_of_neg hx]
    · have : sign t = -1 := by unfold sign; simp [ht.2]
      rw [this]; exact (hasDerivAt_id t).neg

lemma qScaled_deriv (K : ℕ) {s : ℝ} (hs : s ≠ 0) (t : ℝ) :
    (qScaled K s).derivative.eval t = (q K).derivative.eval (t/s) := by
  simp only [qScaled, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.derivative_X, mul_one, Polynomial.eval_X]
  rw [div_eq_inv_mul]; field_simp

lemma int_qprime (K : ℕ) {s : ℝ} (hs : s ≠ 0) (hq0 : (q K).eval 0 = 0) (x : ℝ) :
    ∫ t in (0:ℝ)..x, (q K).derivative.eval (t/s) = (qScaled K s).eval x := by
  have : (fun t => (q K).derivative.eval (t/s)) = fun t => (qScaled K s).derivative.eval t := by
    funext t; rw [qScaled_deriv K hs]
  rw [this, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => Polynomial.hasDerivAt (qScaled K s) t)]
  · simp [qScaled, Polynomial.eval_comp, hq0]
  · exact (Polynomial.continuous _).intervalIntegrable _ _

def gfun (K : ℕ) (s : ℝ) (t : ℝ) : ℝ := sign t - (q K).derivative.eval (t/s)

lemma gfun_intInt (K : ℕ) (s : ℝ) (a b : ℝ) : IntervalIntegrable (gfun K s) volume a b :=
  (sign_intInt a b).sub
    ((by fun_prop : Continuous fun t => (q K).derivative.eval (t/s)).intervalIntegrable _ _)

lemma e_eq (K : ℕ) {s : ℝ} (hs : s ≠ 0) (hq0 : (q K).eval 0 = 0) (x : ℝ) :
    |x| - (qScaled K s).eval x =
      (∫ t in (-s)..x, gfun K s t) - ∫ t in (-s)..0, gfun K s t := by
  rw [intervalIntegral.integral_interval_sub_left (gfun_intInt K s _ _) (gfun_intInt K s _ _)]
  unfold gfun
  rw [intervalIntegral.integral_sub (sign_intInt 0 x)
    ((by fun_prop : Continuous fun t => (q K).derivative.eval (t/s)).intervalIntegrable _ _),
    int_sign, int_qprime K hs hq0]

lemma F_indicator (K : ℕ) {s x : ℝ} (hx : x ∈ Set.Icc (-s) s) :
    ∫ t in (-s)..x, gfun K s t = ∫ t in (-s)..s, Set.indicator {t | t ≤ x} (gfun K s) t :=
  (intervalIntegral.integral_indicator hx).symm


lemma ind_intInt (K : ℕ) (s a b x : ℝ) :
    IntervalIntegrable (Set.indicator {t | t ≤ x} (gfun K s)) volume a b := by
  have h := gfun_intInt K s a b
  exact ⟨h.1.indicator measurableSet_Iic, h.2.indicator measurableSet_Iic⟩

lemma sum_intInt {a b : ℝ} (f : Fin d → ℝ → ℝ)
    (hf : ∀ k, IntervalIntegrable (f k) volume a b) :
    IntervalIntegrable (fun t => ∑ k, f k t) volume a b := by
  suffices h : ∀ S : Finset (Fin d), IntervalIntegrable (fun t => ∑ k ∈ S, f k t) volume a b from
    h Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hf k).add ih

lemma sum_ind (K : ℕ) (s : ℝ) (lam : Fin d → ℝ) (t : ℝ) :
    ∑ k, Set.indicator {t | t ≤ lam k} (gfun K s) t =
      gfun K s t * ((Finset.univ.filter (fun k => t ≤ lam k)).card : ℝ) := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma sumF (K : ℕ) {s : ℝ} (lam : Fin d → ℝ) (hlam : ∀ k, lam k ∈ Set.Icc (-s) s) :
    ∑ k, ∫ t in (-s)..(lam k), gfun K s t =
      ∫ t in (-s)..s, gfun K s t * ((Finset.univ.filter (fun k => t ≤ lam k)).card : ℝ) := by
  simp only [F_indicator K (hlam _)]
  rw [← intervalIntegral.integral_finsetSum (fun k _ => ind_intInt K s _ _ _)]
  simp only [sum_ind]

lemma sign_mul_pos {s : ℝ} (hs : 0 < s) (x : ℝ) : sign (s * x) = sign x := by
  unfold sign
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [h, mul_neg_of_pos_of_neg hs h]
  · simp
  · simp [not_lt.mpr h.le, h.ne', not_lt.mpr (mul_pos hs h).le, (mul_pos hs h).ne']

lemma int_abs_g (K : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ t in (-s)..s, |gfun K s t| = s * ∫ x in (-1:ℝ)..1, |sign x - (q K).derivative.eval x| := by
  have h := intervalIntegral.integral_comp_mul_left (fun t => |gfun K s t|) (a := -1) (b := 1)
    hs.ne'
  simp only [mul_neg, mul_one, smul_eq_mul] at h
  have e : (fun x => |gfun K s (s * x)|) = fun x => |sign x - (q K).derivative.eval x| := by
    funext x; unfold gfun; rw [sign_mul_pos hs, mul_div_cancel_left₀ _ hs.ne']
  rw [e] at h
  rw [h]; field_simp


theorem l24_explicit (d K : ℕ) (hK : 2 ≤ K) (s : ℝ) (hs : 0 < s) (U V : Mat d)
    (hU : U.IsHermitian) (hV : V.IsHermitian) (hUs : opNorm U ≤ s) (hVs : opNorm V ≤ s) :
    |traceError K s U - traceError K s V| ≤ 64*s/(K : ℝ) * (U-V).rank := by
  obtain ⟨-, -, hq0, -, -, hint, hle, -⟩ := lemma_2_3 K hK
  have hsne : s ≠ 0 := hs.ne'
  have hmemU : ∀ k, hU.eigenvalues k ∈ Set.Icc (-s) s := fun k => by
    have := (eig_abs_le hU k).trans hUs; rw [abs_le] at this; exact this
  have hmemV : ∀ k, hV.eigenvalues k ∈ Set.Icc (-s) s := fun k => by
    have := (eig_abs_le hV k).trans hVs; rw [abs_le] at this; exact this
  set F0 := ∫ t in (-s)..0, gfun K s t
  have hTU : traceError K s U = (∑ k, ∫ t in (-s)..(hU.eigenvalues k), gfun K s t) - d * F0 := by
    rw [traceError_eq K s hU]
    simp only [e_eq K hsne hq0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rfl
  have hTV : traceError K s V = (∑ k, ∫ t in (-s)..(hV.eigenvalues k), gfun K s t) - d * F0 := by
    rw [traceError_eq K s hV]
    simp only [e_eq K hsne hq0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rfl
  set cU : ℝ → ℝ := fun t => ((Finset.univ.filter (fun k => t ≤ hU.eigenvalues k)).card : ℝ)
  set cV : ℝ → ℝ := fun t => ((Finset.univ.filter (fun k => t ≤ hV.eigenvalues k)).card : ℝ)
  set r : ℝ := ((U - V).rank : ℝ)
  have hc : ∀ t, |cU t - cV t| ≤ r := by
    intro t
    have h1 := (MatrixSpectral.eigenvalue_count_le_add_rank U V hU hV t).2
    have h2 := (MatrixSpectral.eigenvalue_count_le_add_rank V U hV hU t).2
    have hr : (V - U).rank = (U - V).rank := by
      rw [show V - U = (-1 : ℂ) • (U - V) by rw [neg_one_smul]; abel]
      exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (by norm_num))
    rw [hr] at h2
    rw [abs_le]; constructor
    · have : (cV t) ≤ cU t + r := by simp only [cU, cV, r]; exact_mod_cast h2
      linarith
    · have : (cU t) ≤ cV t + r := by simp only [cU, cV, r]; exact_mod_cast h1
      linarith
  have hIU : IntervalIntegrable (fun t => gfun K s t * cU t) volume (-s) s := by
    have hsum : IntervalIntegrable (fun t => ∑ k, Set.indicator {t | t ≤ hU.eigenvalues k}
        (gfun K s) t) volume (-s) s :=
      sum_intInt _ (fun k => ind_intInt K s (-s) s (hU.eigenvalues k))
    simpa only [sum_ind] using hsum
  have hIV : IntervalIntegrable (fun t => gfun K s t * cV t) volume (-s) s := by
    have hsum : IntervalIntegrable (fun t => ∑ k, Set.indicator {t | t ≤ hV.eigenvalues k}
        (gfun K s) t) volume (-s) s :=
      sum_intInt _ (fun k => ind_intInt K s (-s) s (hV.eigenvalues k))
    simpa only [sum_ind] using hsum
  have hdiff : traceError K s U - traceError K s V =
      ∫ t in (-s)..s, (gfun K s t * cU t - gfun K s t * cV t) := by
    rw [hTU, hTV, sumF K _ hmemU, sumF K _ hmemV, intervalIntegral.integral_sub hIU hIV]
    ring
  have hgabs : IntervalIntegrable (fun t => |gfun K s t|) volume (-s) s :=
    (gfun_intInt K s (-s) s).abs
  rw [hdiff]
  have hss : -s ≤ s := by linarith
  calc |∫ t in (-s)..s, (gfun K s t * cU t - gfun K s t * cV t)|
      ≤ ∫ t in (-s)..s, |gfun K s t * cU t - gfun K s t * cV t| :=
        intervalIntegral.abs_integral_le_integral_abs hss
    _ ≤ ∫ t in (-s)..s, r * |gfun K s t| := by
        refine intervalIntegral.integral_mono_on hss (hIU.sub hIV).abs (hgabs.const_mul r)
          (fun t _ => ?_)
        rw [← mul_sub, abs_mul, mul_comm r]
        exact mul_le_mul_of_nonneg_left (hc t) (abs_nonneg _)
    _ = r * (s * ∫ x in (-1:ℝ)..1, |sign x - (q K).derivative.eval x|) := by
        rw [intervalIntegral.integral_const_mul, int_abs_g K hs]
    _ ≤ r * (s * (64 / K)) := by
        gcongr
    _ = 64 * s / K * r := by ring


/-! ### functional-calculus facts for the approximation clause -/

section approx
variable {X : Mat d} (hX : X.IsHermitian)
include hX

lemma posdef_cfc (f : ℝ → ℝ) (hf : ∀ i, 0 < f (hX.eigenvalues i)) : (cfc f X).PosDef := by
  rw [cfc_explicit hX]
  set U := (hX.eigenvectorUnitary : Mat d)
  have hD : (diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ))).PosDef :=
    Matrix.posDef_diagonal_iff.2 (fun i => by simpa using hf i)
  have hinj : Function.Injective U.vecMul := by
    intro v w h
    have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem (U_mem hX)
    have := congrArg (fun z => z ᵥ* star U) h
    simp only [Matrix.vecMul_vecMul, hUU, Matrix.vecMul_one] at this
    exact this
  have := hD.mul_mul_conjTranspose_same hinj
  rwa [← Matrix.star_eq_conjTranspose] at this

lemma cfc_le_one (f : ℝ → ℝ) (hf : ∀ i, f (hX.eigenvalues i) ≤ 1) : lePSD (cfc f X) 1 := by
  unfold lePSD
  have e : (1 : Mat d) - cfc f X = cfc (fun x : ℝ => 1 - f x) X := by
    rw [cfc_sub (fun _ => (1:ℝ)) f X (hg := (Matrix.finite_real_spectrum).continuousOn _),
      cfc_const_one ℝ X (ha := hX.isSelfAdjoint)]
  rw [e]
  exact psd_cfc hX _ (fun i => by linarith [hf i])

lemma traceNorm_cfc (h : ℝ → ℝ) :
    QAlgorithms.traceNorm (cfc h X) = ∑ i, |h (hX.eigenvalues i)| := by
  have hfin : (spectrum ℝ X).Finite := Matrix.finite_real_spectrum
  have hH := cfc_herm hX h
  have e : (cfc h X)ᴴ * cfc h X = cfc (fun t => h t * h t) X := by
    rw [hH.eq, cfc_mul' hX]
  unfold QAlgorithms.traceNorm
  rw [e, ← cfc_comp Real.sqrt (fun t => h t * h t) X hX.isSelfAdjoint
    ((hfin.image _).continuousOn _) (hfin.continuousOn _), trace_cfc hX, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Function.comp, Complex.ofReal_re]
  rw [← sq, Real.sqrt_sq_eq_abs]

lemma rank_cfc_le (h : ℝ → ℝ) :
    (cfc h X).rank ≤ ((Finset.univ.filter (fun i => h (hX.eigenvalues i) ≠ 0)).card) := by
  classical
  rw [cfc_explicit hX]
  refine (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans ?_)
  rw [rank_diagonal]
  rw [Fintype.card_subtype]
  apply le_of_eq
  congr 1
  ext i; simp

/-- sandwich bound `‖g(X) Y g(X)‖ ≤ max x g(x)²` under `-X ≤ Y ≤ X` -/
lemma opNorm_sandwich {Y : Mat d} (hY : Y.IsHermitian) (hlo : lePSD (-X) Y) (hhi : lePSD Y X)
    (g : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) (hg : ∀ i, hX.eigenvalues i * g (hX.eigenvalues i)^2 ≤ c) :
    opNorm (cfc g X * Y * cfc g X) ≤ c := by
  set G := cfc g X with hG
  have hGH : G.IsHermitian := cfc_herm hX g
  have hZH : (G * Y * G).IsHermitian := by
    show (G * Y * G)ᴴ = G * Y * G
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGH.eq, hY.eq, Matrix.mul_assoc]
  refine opNorm_le_of_quad hZH hc (fun v => ?_)
  set u := G *ᵥ v with hu
  have hq : ∀ M : Mat d, star v ⬝ᵥ ((G * M * G) *ᵥ v) = star u ⬝ᵥ (M *ᵥ u) := by
    intro M
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hu,
      Matrix.star_mulVec, hGH.eq]
  rw [hq Y]
  have h1 := re_nonneg_of_psd hlo u
  have h2 := re_nonneg_of_psd hhi u
  rw [sub_neg_eq_add, Matrix.add_mulVec, dotProduct_add, Complex.add_re] at h1
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at h2
  have hX' : (star u ⬝ᵥ (X *ᵥ u)).re ≤ c * (star v ⬝ᵥ v).re := by
    rw [← hq X]
    have e : G * X * G = cfc (fun x => x * g x ^ 2) X := by
      have h1 : cfc g X * cfc (fun x : ℝ => x) X * cfc g X = cfc (fun x => x * g x ^ 2) X := by
        rw [cfc_mul' hX, cfc_mul' hX]; congr 1; funext x; ring
      rwa [cfc_id' ℝ X hX.isSelfAdjoint] at h1
    rw [e, quad_cfc hX]
    set y := star (hX.eigenvectorUnitary : Mat d) *ᵥ v
    have hyy : (star v ⬝ᵥ v) = star y ⬝ᵥ y := (unitary_norm _ (U_mem hX) v).symm
    rw [hyy, sum_normsq y]
    simp only [Complex.re_sum, Complex.ofReal_re]
    have h1 : ∀ i, ((((hX.eigenvalues i * g (hX.eigenvalues i) ^ 2 : ℝ)) : ℂ) * (star (y i) * y i)).re =
        (hX.eigenvalues i * g (hX.eigenvalues i) ^ 2) * ‖y i‖^2 := by
      intro i
      have : star (y i) * y i = ((‖y i‖^2 : ℝ) : ℂ) := by
        rw [mul_comm]; show y i * (starRingEnd ℂ) (y i) = _
        rw [Complex.mul_conj', Complex.ofReal_pow]
      rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp only [h1]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hg i) (sq_nonneg _))
  rw [abs_le]; constructor <;> linarith

lemma matrixEval_cfc (p : Polynomial ℝ) : matrixEval p X = cfc (fun x => p.eval x) X := by
  rw [matrixEval_eq_aeval, cfc_polynomial p X hX.isSelfAdjoint]

def Rf (c : ℝ) (x : ℝ) : ℝ := if x < c then 1 else (filter c).eval x
def Lf (c : ℝ) (x : ℝ) : ℝ := if x < c then (filter c).eval x else 1

omit hX in
lemma filter_facts {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (filter c).eval x ∧ (filter c).eval x ≤ 1 ∧ x * ((filter c).eval x)^2 ≤ 2^7 * c ∧
    (x < c → 0 < (filter c).eval x ∧ -Real.log ((filter c).eval x) ≤ (x/c)^2) := by
  obtain ⟨-, -, h3, h4⟩ := lemma_2_5 c hc0 hc1
  obtain ⟨a1, a2, a3⟩ := h3 x ⟨hx0, hx1⟩
  exact ⟨a1, a2, a3, fun hxc => h4 x ⟨hx0, hxc.le⟩⟩

lemma Ytil_facts {Y : Mat d} (hY : Y.IsHermitian) (hlo : lePSD (-X) Y) (hhi : lePSD Y X)
    (hx0 : ∀ i, 0 ≤ hX.eigenvalues i) (hx1 : ∀ i, hX.eigenvalues i ≤ 1)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (cfc (Rf c) X * Y * cfc (Rf c) X).IsHermitian ∧
    opNorm (cfc (Rf c) X * Y * cfc (Rf c) X) ≤ 2^7 * c := by
  have hGH : (cfc (Rf c) X).IsHermitian := cfc_herm hX _
  refine ⟨?_, ?_⟩
  · show (cfc (Rf c) X * Y * cfc (Rf c) X)ᴴ = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGH.eq, hY.eq, Matrix.mul_assoc]
  · refine opNorm_sandwich hX hY hlo hhi (Rf c) (by positivity) (fun i => ?_)
    obtain ⟨-, -, h3, -⟩ := filter_facts hc0 hc1 (hx0 i) (hx1 i)
    unfold Rf; split_ifs with h
    · nlinarith
    · exact h3

lemma side_A1 {Y : Mat d} (hd : 0 < d) (hY : Y.IsHermitian) (hlo : lePSD (-X) Y) (hhi : lePSD Y X)
    (hx0 : ∀ i, 0 ≤ hX.eigenvalues i) (hx1 : ∀ i, hX.eigenvalues i ≤ 1)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (K : ℕ) (hK : 2 ≤ K) {w : ℝ} (hw : 2^7 * c ≤ w) :
    |traceError K w (matrixEval (filter c) X * Y * matrixEval (filter c) X) -
      traceError K w (cfc (Rf c) X * Y * cfc (Rf c) X)| ≤
      2^5 * w / K * ∑ k, (if hX.eigenvalues k < c then (hX.eigenvalues k / c)^2 else 0) := by
  obtain ⟨hYH, hYn⟩ := Ytil_facts hX hY hlo hhi hx0 hx1 hc0 hc1
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  set Λ := cfc (Lf c) X with hΛ
  have hpos : ∀ i, 0 < Lf c (hX.eigenvalues i) := by
    intro i; obtain ⟨-, -, -, h4⟩ := filter_facts hc0 hc1 (hx0 i) (hx1 i)
    unfold Lf; split_ifs with h
    · exact (h4 h).1
    · exact one_pos
  have hΛpd : Λ.PosDef := posdef_cfc hX _ hpos
  have hΛ1 : lePSD Λ 1 := cfc_le_one hX _ (fun i => by
    obtain ⟨-, h2, -, -⟩ := filter_facts hc0 hc1 (hx0 i) (hx1 i)
    unfold Lf; split_ifs <;> linarith)
  have hr : matrixEval (filter c) X = Λ * cfc (Rf c) X := by
    rw [matrixEval_cfc hX, hΛ, cfc_mul' hX]
    congr 1; funext x; unfold Lf Rf; split_ifs <;> ring
  have hr' : matrixEval (filter c) X = cfc (Rf c) X * Λ := by
    rw [matrixEval_cfc hX, hΛ, cfc_mul' hX]
    congr 1; funext x; unfold Lf Rf; split_ifs <;> ring
  have he : matrixEval (filter c) X * Y * matrixEval (filter c) X =
      Λ * (cfc (Rf c) X * Y * cfc (Rf c) X) * Λ := by
    calc matrixEval (filter c) X * Y * matrixEval (filter c) X
        = (Λ * cfc (Rf c) X) * Y * (cfc (Rf c) X * Λ) := by rw [← hr, ← hr']
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [he]
  have hA := lemma_A_1 d K hd hK w hw0 _ Λ hYH (hYn.trans hw) hΛpd hΛ1
  refine hA.trans ?_
  have hfin : (spectrum ℝ X).Finite := Matrix.finite_real_spectrum
  have hlog : logMat Λ = cfc (fun x => Real.log (Lf c x)) X := by
    rw [logMat, hΛ, ← cfc_comp Real.log (Lf c) X hX.isSelfAdjoint
      ((hfin.image _).continuousOn _) (hfin.continuousOn _)]
    rfl
  rw [hlog, traceNorm_cfc hX]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => ?_)) (by positivity)
  obtain ⟨-, h2, -, h4⟩ := filter_facts hc0 hc1 (hx0 k) (hx1 k)
  unfold Lf; split_ifs with h
  · obtain ⟨hp, hl⟩ := h4 h
    rw [abs_of_nonpos (Real.log_nonpos hp.le h2)]; exact hl
  · simp

omit hX in
lemma rank_add_le' (A B : Mat d) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma rank_Ytil {Y : Mat d} {a b : ℝ} (hab : b ≤ a) :
    ((cfc (Rf a) X * Y * cfc (Rf a) X) - (cfc (Rf b) X * Y * cfc (Rf b) X)).rank ≤
      2 * (Finset.univ.filter (fun k => b ≤ hX.eigenvalues k)).card := by
  have hfin : (spectrum ℝ X).Finite := Matrix.finite_real_spectrum
  set D := cfc (fun x => Rf a x - Rf b x) X with hD
  have hDe : cfc (Rf a) X - cfc (Rf b) X = D := by
    rw [hD, cfc_sub (Rf a) (Rf b) X (hf := hfin.continuousOn _) (hg := hfin.continuousOn _)]
  have e : (cfc (Rf a) X * Y * cfc (Rf a) X) - (cfc (Rf b) X * Y * cfc (Rf b) X) =
      D * Y * cfc (Rf a) X + cfc (Rf b) X * Y * D := by
    rw [← hDe]; simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [e]
  have hDr : D.rank ≤ (Finset.univ.filter (fun k => b ≤ hX.eigenvalues k)).card := by
    refine (rank_cfc_le hX _).trans (Finset.card_le_card (fun k hk => ?_))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    by_contra hlt; push_neg at hlt
    apply hk; unfold Rf; rw [if_pos hlt, if_pos (lt_of_lt_of_le hlt hab)]; ring
  have h1 := rank_mul_le_left (D * Y) (cfc (Rf a) X)
  have h1' := rank_mul_le_left D Y
  have h2 := rank_mul_le_right (cfc (Rf b) X * Y) D
  have := rank_add_le' (D * Y * cfc (Rf a) X) (cfc (Rf b) X * Y * D)
  omega

omit hX in
lemma per_k {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    2^5 * (2^9 * p⁻¹) * (if x < 2 * p⁻¹ then (x / (2 * p⁻¹))^2 else 0) +
      64 * (2^9 * p⁻¹) * (2 * (if p⁻¹ ≤ x then (1:ℝ) else 0)) +
      2^5 * (2^9 * p⁻¹) * (if x < p⁻¹ then (x / p⁻¹)^2 else 0) ≤
    2^16 * ((if 1 ≤ p * x then p⁻¹ else 0) + (if p * x < 2 then p * x else 0) * x) := by
  have c1 : x < 2 * p⁻¹ ↔ p * x < 2 := by
    rw [← div_eq_mul_inv, lt_div_iff₀ hp, mul_comm]
  have c2 : p⁻¹ ≤ x ↔ 1 ≤ p * x := by
    rw [inv_le_iff_one_le_mul₀ hp, mul_comm]
  have c3 : x < p⁻¹ ↔ p * x < 1 := by
    rw [← one_div, lt_div_iff₀ hp, mul_comm]
  have e1 : (x / (2 * p⁻¹))^2 = p^2 * x^2 / 4 := by field_simp; ring
  have e3 : (x / p⁻¹)^2 = p^2 * x^2 := by field_simp
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have hpi0 : 0 < p⁻¹ := inv_pos.2 hp
  rw [e1, e3]
  simp only [c1, c2, c3]
  have hA : 2^5 * (2^9 * p⁻¹) * (p^2 * x^2 / 4) = 2^12 * (p * x) * x := by
    field_simp; ring
  have hB : 2^5 * (2^9 * p⁻¹) * (p^2 * x^2) = 2^14 * (p * x) * x := by
    field_simp
  have hpx : 0 ≤ p * x := by positivity
  split_ifs with h1 h2 h3 <;> nlinarith [mul_nonneg hpx hx]

lemma scale_err {Y : Mat d} (hd : 0 < d) (hY : Y.IsHermitian) (hlo : lePSD (-X) Y) (hhi : lePSD Y X)
    (hx0 : ∀ i, 0 ≤ hX.eigenvalues i) (hx1 : ∀ i, hX.eigenvalues i ≤ 1)
    (K : ℕ) (hK : 2 ≤ K) (l : ℕ) (hl : 1 ≤ l) :
    |traceError K (2^9 * ((2:ℝ)^l)⁻¹)
        (matrixEval (filter (2 * ((2:ℝ)^l)⁻¹)) X * Y * matrixEval (filter (2 * ((2:ℝ)^l)⁻¹)) X) -
      traceError K (2^9 * ((2:ℝ)^l)⁻¹)
        (matrixEval (filter ((2:ℝ)^l)⁻¹) X * Y * matrixEval (filter ((2:ℝ)^l)⁻¹) X)| ≤
      2^16 / K * ∑ k, ((if 1 ≤ (2:ℝ)^l * hX.eigenvalues k then ((2:ℝ)^l)⁻¹ else 0) +
        (if (2:ℝ)^l * hX.eigenvalues k < 2 then (2:ℝ)^l * hX.eigenvalues k else 0) *
          hX.eigenvalues k) := by
  set p := (2:ℝ)^l with hp
  have hp0 : 0 < p := by positivity
  have hp1 : 1 ≤ p := one_le_pow₀ (by norm_num)
  set a := 2 * p⁻¹ with ha
  set b := p⁻¹ with hb
  set w := 2^9 * p⁻¹ with hw
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 1 := inv_le_one_of_one_le₀ hp1
  have hKr : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hw0 : 0 < w := by positivity
  have hp2 : 2 ≤ p := by
    calc (2:ℝ) = 2^1 := by norm_num
      _ ≤ p := pow_le_pow_right₀ (by norm_num) hl
  have ha1 : a ≤ 1 := by
    rw [ha, ← div_eq_mul_inv, div_le_one hp0]; exact hp2
  · have ha0 : 0 < a := by positivity
    have hA := side_A1 hX hd hY hlo hhi hx0 hx1 ha0 ha1 K hK (w := w) (by rw [ha, hw]; nlinarith)
    have hB := side_A1 hX hd hY hlo hhi hx0 hx1 hb0 hb1 K hK (w := w) (by rw [hb, hw]; nlinarith)
    obtain ⟨hYa, hYan⟩ := Ytil_facts hX hY hlo hhi hx0 hx1 ha0 ha1
    obtain ⟨hYb, hYbn⟩ := Ytil_facts hX hY hlo hhi hx0 hx1 hb0 hb1
    have hL := l24_explicit d K hK w hw0 _ _ hYa hYb (hYan.trans (by rw [ha, hw]; nlinarith))
      (hYbn.trans (by rw [hb, hw]; nlinarith))
    have hR := rank_Ytil hX (Y := Y) (show b ≤ a by rw [ha, hb]; linarith)
    have hcard : ((Finset.univ.filter (fun k => b ≤ hX.eigenvalues k)).card : ℝ) =
        ∑ k, (if b ≤ hX.eigenvalues k then (1:ℝ) else 0) := by
      rw [Finset.sum_boole]
    have hR' : (((cfc (Rf a) X * Y * cfc (Rf a) X) - (cfc (Rf b) X * Y * cfc (Rf b) X)).rank : ℝ) ≤
        2 * ∑ k, (if b ≤ hX.eigenvalues k then (1:ℝ) else 0) := by
      rw [← hcard]; exact_mod_cast hR
    have htri : |traceError K w (matrixEval (filter a) X * Y * matrixEval (filter a) X) -
        traceError K w (matrixEval (filter b) X * Y * matrixEval (filter b) X)| ≤
        2^5 * w / K * ∑ k, (if hX.eigenvalues k < a then (hX.eigenvalues k / a)^2 else 0) +
        64 * w / K * (2 * ∑ k, (if b ≤ hX.eigenvalues k then (1:ℝ) else 0)) +
        2^5 * w / K * ∑ k, (if hX.eigenvalues k < b then (hX.eigenvalues k / b)^2 else 0) := by
      have h3 : 64 * w / K * (((cfc (Rf a) X * Y * cfc (Rf a) X) -
          (cfc (Rf b) X * Y * cfc (Rf b) X)).rank : ℝ) ≤
          64 * w / K * (2 * ∑ k, (if b ≤ hX.eigenvalues k then (1:ℝ) else 0)) :=
        mul_le_mul_of_nonneg_left hR' (by positivity)
      have := abs_sub_le (G := ℝ) (traceError K w (matrixEval (filter a) X * Y * matrixEval (filter a) X))
        (traceError K w (cfc (Rf a) X * Y * cfc (Rf a) X))
        (traceError K w (matrixEval (filter b) X * Y * matrixEval (filter b) X))
      have := abs_sub_le (G := ℝ) (traceError K w (cfc (Rf a) X * Y * cfc (Rf a) X))
        (traceError K w (cfc (Rf b) X * Y * cfc (Rf b) X))
        (traceError K w (matrixEval (filter b) X * Y * matrixEval (filter b) X))
      rw [abs_sub_comm] at hB
      linarith
    refine htri.trans ?_
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hpk := per_k hp0 (hx0 k)
    rw [← ha, ← hb, ← hw] at hpk
    have e : ∀ z : ℝ, 2^5 * w / K * z = (2^5 * w * z) / K := fun z => by ring
    have e2 : ∀ z : ℝ, 64 * w / K * z = (64 * w * z) / K := fun z => by ring
    have e3 : ∀ z : ℝ, 2^16 / K * z = (2^16 * z) / K := fun z => by ring
    rw [e, e2, e, e3, ← add_div, ← add_div]
    exact div_le_div_of_nonneg_right hpk hKr.le

end approx


/-! ### numerics of the approximation clause -/

def hfun (l : ℕ) (x : ℝ) : ℝ :=
  (if 1 ≤ (2:ℝ)^l * x then ((2:ℝ)^l)⁻¹ else 0) + (if (2:ℝ)^l * x < 2 then (2:ℝ)^l * x else 0) * x

lemma hfun_nonneg (l : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ hfun l x := by
  unfold hfun; split_ifs <;> positivity

lemma hfun_sum {x : ℝ} (hx : 0 ≤ x) (N : ℕ) : ∑ l ∈ Finset.range N, hfun l x ≤ 6 * x := by
  unfold hfun
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0; norm_num
  have h1 := OTDDyadic.D1 hpos N
  have h2 := OTDDyadic.D2 hx (by norm_num : (0:ℝ) < 2) N
  nlinarith

lemma hfun_le (l : ℕ) {x : ℝ} (hx : 0 ≤ x) : hfun l x ≤ 5 * ((2:ℝ)^l)⁻¹ := by
  unfold hfun
  have hp : (0:ℝ) < 2^l := by positivity
  have hpi : (2:ℝ)^l * ((2:ℝ)^l)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  split_ifs with h1 h2 h2
  · have : (2:ℝ)^l * x * x ≤ 4 * ((2:ℝ)^l)⁻¹ := by
      have hx2 : x < 2 * ((2:ℝ)^l)⁻¹ := by
        rw [← div_eq_mul_inv, lt_div_iff₀ hp]; linarith
      nlinarith
    linarith
  · have : 0 ≤ ((2:ℝ)^l)⁻¹ := by positivity
    linarith
  · have : (2:ℝ)^l * x * x ≤ 4 * ((2:ℝ)^l)⁻¹ := by
      have hx2 : x < 2 * ((2:ℝ)^l)⁻¹ := by
        rw [← div_eq_mul_inv, lt_div_iff₀ hp]; linarith
      nlinarith
    have : 0 ≤ ((2:ℝ)^l)⁻¹ := by positivity
    linarith
  · have : 0 ≤ ((2:ℝ)^l)⁻¹ := by positivity
    linarith

lemma approx_numeric {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ)
    (hx0 : ∀ k, 0 ≤ x k) (hxs : ∑ k, x k ≤ 1) (J : ℕ) (K : ℕ → ℝ)
    (hK : ∀ l, 1 ≤ l → l ≤ J →
      (2^30/ε) * Real.sqrt (min 1 ((d:ℝ) * ((2:ℝ)^l)⁻¹)) ≤ K l) :
    ∑ i ∈ Finset.range J, 2^16 / K (i+1) * ∑ k, hfun (i+1) (x k) ≤ ε / 4 := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  set H : ℕ → ℝ := fun l => ∑ k, hfun l (x k) with hH
  have hH0 : ∀ l, 0 ≤ H l := fun l => Finset.sum_nonneg (fun k _ => hfun_nonneg l (hx0 k))
  set g : ℕ → ℝ := fun l => (if (2:ℝ)^l < d then H l else 0) +
    5 * (if 1 ≤ (2:ℝ)^l * (1/(d:ℝ)) then Real.sqrt ((2:ℝ)^l * (1/(d:ℝ)))⁻¹ else 0) with hg
  have hg0 : ∀ l, 0 ≤ g l := fun l => by
    simp only [hg]; have := hH0 l; split_ifs <;> positivity
  have hterm : ∀ i ∈ Finset.range J, 2^16 / K (i+1) * H (i+1) ≤ 2^16 * (ε / 2^30) * g (i+1) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hKl := hK (i+1) (by omega) (by omega)
    set l := i + 1
    set p := (2:ℝ)^l with hp
    have hp0 : 0 < p := by positivity
    set m := min 1 ((d:ℝ) * p⁻¹) with hm
    by_cases hlt : p < d
    · have hm1 : m = 1 := by
        rw [hm]; apply min_eq_left; rw [← div_eq_mul_inv, le_div_iff₀ hp0]; linarith
      rw [hm1, Real.sqrt_one, mul_one] at hKl
      have hK0 : 0 < K l := lt_of_lt_of_le (by positivity) hKl
      have : 2^16 / K l ≤ 2^16 * (ε / 2^30) := by
        rw [div_le_iff₀ hK0]
        calc (2:ℝ)^16 = 2^16 * (ε / 2^30) * (2^30/ε) := by field_simp
          _ ≤ 2^16 * (ε / 2^30) * K l := by gcongr
      have hgl : H l ≤ g l := by
        simp only [hg]; rw [if_pos hlt]
        have : 0 ≤ 5 * (if 1 ≤ p * (1/(d:ℝ)) then Real.sqrt (p * (1/(d:ℝ)))⁻¹ else 0) := by
          split_ifs <;> positivity
        linarith
      calc 2^16 / K l * H l ≤ 2^16 * (ε / 2^30) * H l := by gcongr; exact hH0 l
        _ ≤ 2^16 * (ε / 2^30) * g l := by gcongr
    · push_neg at hlt
      have hm1 : m = d * p⁻¹ := by
        rw [hm]; apply min_eq_right; rw [← div_eq_mul_inv, div_le_iff₀ hp0]; linarith
      have hm0 : 0 < m := by rw [hm1]; positivity
      have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
      have hK0 : 0 < K l := lt_of_lt_of_le (by positivity) hKl
      have hcond : 1 ≤ p * (1/(d:ℝ)) := by rw [mul_one_div, le_div_iff₀ hdr]; linarith
      have hgl : g l = 5 * Real.sqrt (p * (1/(d:ℝ)))⁻¹ := by
        simp only [hg]; rw [if_neg (not_lt.2 hlt), if_pos hcond, zero_add]
      have hHl : H l ≤ 5 * d * p⁻¹ := by
        calc H l ≤ ∑ k : Fin d, 5 * p⁻¹ := Finset.sum_le_sum (fun k _ => hfun_le l (hx0 k))
          _ = 5 * d * p⁻¹ := by simp; ring
      have hsq : Real.sqrt (p * (1/(d:ℝ)))⁻¹ = Real.sqrt m := by
        rw [hm1]; congr 1; field_simp
      rw [hgl, hsq]
      -- 2^16/K * H ≤ 2^16 * (ε/2^30) * (5 * sqrt m)
      have h1 : 2^16 / K l ≤ 2^16 * (ε / 2^30) / Real.sqrt m := by
        rw [div_le_div_iff₀ hK0 hsm]
        calc (2:ℝ)^16 * Real.sqrt m = 2^16 * (ε / 2^30) * ((2^30/ε) * Real.sqrt m) := by
              field_simp
          _ ≤ 2^16 * (ε / 2^30) * K l := by gcongr
      have h2 : H l / Real.sqrt m ≤ 5 * Real.sqrt m := by
        rw [div_le_iff₀ hsm]
        have : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
        rw [mul_assoc, this, hm1]; linarith
      calc 2^16 / K l * H l ≤ 2^16 * (ε / 2^30) / Real.sqrt m * H l := by gcongr; exact hH0 l
        _ = 2^16 * (ε / 2^30) * (H l / Real.sqrt m) := by ring
        _ ≤ 2^16 * (ε / 2^30) * (5 * Real.sqrt m) := by gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hs : ∑ i ∈ Finset.range J, g (i+1) ≤ ∑ l ∈ Finset.range (J+1), g l := by
    rw [Finset.sum_range_succ' (fun l => g l)]; linarith [hg0 0]
  have hsum : ∑ l ∈ Finset.range (J+1), g l ≤ 26 := by
    simp only [hg, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h4 := OTDDyadic.D4 (by positivity : (0:ℝ) < 1/(d:ℝ)) (J+1)
    have h6 : ∑ l ∈ Finset.range (J+1), (if (2:ℝ)^l < d then H l else 0) ≤ 6 := by
      calc ∑ l ∈ Finset.range (J+1), (if (2:ℝ)^l < d then H l else 0)
          ≤ ∑ l ∈ Finset.range (J+1), H l :=
            Finset.sum_le_sum (fun l _ => by split_ifs; exact le_rfl; exact hH0 l)
        _ = ∑ k, ∑ l ∈ Finset.range (J+1), hfun l (x k) := by rw [Finset.sum_comm]
        _ ≤ ∑ k, 6 * x k := Finset.sum_le_sum (fun k _ => hfun_sum (hx0 k) _)
        _ ≤ 6 := by rw [← Finset.mul_sum]; linarith
    linarith
  have := hs.trans hsum
  calc 2^16 * (ε / 2^30) * ∑ i ∈ Finset.range J, g (i+1) ≤ 2^16 * (ε / 2^30) * 26 := by gcongr
    _ ≤ ε / 4 := by nlinarith

lemma traceNorm_eq {A : Mat d} (hA : A.IsHermitian) :
    QAlgorithms.traceNorm A = ∑ i, |hA.eigenvalues i| := by
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have e : Aᴴ * A = cfc (fun t : ℝ => t * t) A := by
    rw [hA.eq, ← cfc_mul' hA, cfc_id' ℝ A hA.isSelfAdjoint]
  unfold QAlgorithms.traceNorm
  rw [e, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) A hA.isSelfAdjoint
    ((hfin.image _).continuousOn _) (hfin.continuousOn _), trace_cfc hA, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Function.comp, Complex.ofReal_re]
  rw [← sq, Real.sqrt_sq_eq_abs]

lemma traceNorm_le_opNorm {Z : Mat d} (hZ : Z.IsHermitian) :
    QAlgorithms.traceNorm Z ≤ d * opNorm Z := by
  rw [traceNorm_eq hZ]
  calc ∑ i, |hZ.eigenvalues i| ≤ ∑ _i : Fin d, opNorm Z := Finset.sum_le_sum (fun i _ => eig_abs_le hZ i)
    _ = d * opNorm Z := by simp

theorem approx_clause {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/32) {X Y : Mat d}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hX0 : X.PosSemidef) (htr : tr X ≤ 1)
    (hlo : lePSD (-X) Y) (hhi : lePSD Y X) :
    |(evaluate (F d ε) X Y).re - QAlgorithms.traceNorm Y| ≤ ε := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have hε1' : ε ≤ 1 := by linarith
  have hx0 : ∀ i, 0 ≤ hX.eigenvalues i := fun i => hX0.eigenvalues_nonneg i
  have hx1 : ∀ i, hX.eigenvalues i ≤ 1 := fun i => eig_le_tr hX0 htr i
  have hxs : ∑ k, hX.eigenvalues k ≤ 1 := by
    have : tr X = ∑ j, hX.eigenvalues j := by
      unfold tr; rw [hX.trace_eq_sum_eigenvalues]; simp
    linarith
  set J := scales d ε with hJ
  set Kn : ℕ → ℕ := fun l => scaleDegree constructionA d ε l with hKn
  set M : ℝ → Mat d := fun c => matrixEval (filter c) X with hM
  set Yb : ℝ → Mat d := fun c => M c * Y * M c with hYb
  set T : ℕ → ℝ := fun i => QAlgorithms.traceNorm (Yb ((2:ℝ)^i)⁻¹) with hT
  set E : ℕ → Mat d → ℝ := fun i A => traceError (Kn (i+1)) (2^9 * ((2:ℝ)^(i+1))⁻¹) A with hE
  have hGre : ∀ (K : ℕ) (b w : ℝ), (evaluate (G (d := d) K b w) X Y).re =
      QAlgorithms.traceNorm (Yb b) - traceError K w (Yb b) := by
    intro K b w
    rw [eval_G]
    have : traceError K w (Yb b) = QAlgorithms.traceNorm (Yb b) -
        (matrixEval (qScaled K w) (Yb b)).trace.re := by
      unfold traceError tr absMat QAlgorithms.traceNorm
      rw [Matrix.trace_sub, Complex.sub_re]
    rw [this]; simp only [hYb, hM]; ring
  have hF : (evaluate (F d ε) X Y).re =
      ∑ i ∈ Finset.range J, (T i - T (i+1)) +
      ∑ i ∈ Finset.range J, (E i (Yb ((2:ℝ)^(i+1))⁻¹) - E i (Yb ((2:ℝ)^i)⁻¹)) := by
    rw [show F d ε = multiscale constructionA d ε from rfl, eval_F, Complex.re_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.sub_re, hGre, hGre, width_eq, zpow_neg_nat, zpow_neg_nat]
    simp only [hT, hE]
    ring
  have hT0 : T 0 = QAlgorithms.traceNorm Y := by
    simp only [hT, hYb, hM, pow_zero, inv_one, filter_one, matrixEval_one, Matrix.one_mul,
      Matrix.mul_one]
  have htel : ∑ i ∈ Finset.range J, (T i - T (i+1)) = T 0 - T J := Finset.sum_range_sub' T J
  rw [hF, htel, hT0]
  -- the tail
  obtain ⟨hJ1, -⟩ := scales_facts hd1 hε hε1'
  have hbJ0 : 0 < ((2:ℝ)^J)⁻¹ := by positivity
  have hbJ1 : ((2:ℝ)^J)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hYJH : (Yb ((2:ℝ)^J)⁻¹).IsHermitian := by
    have hMH : (M ((2:ℝ)^J)⁻¹).IsHermitian := by
      simp only [hM]; rw [matrixEval_cfc hX]; exact cfc_herm hX _
    have : (M ((2:ℝ)^J)⁻¹ * Y * M ((2:ℝ)^J)⁻¹)ᴴ = M ((2:ℝ)^J)⁻¹ * Y * M ((2:ℝ)^J)⁻¹ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hMH.eq, hY.eq, Matrix.mul_assoc]
    exact this
  have hYJn : opNorm (Yb ((2:ℝ)^J)⁻¹) ≤ 2^7 * ((2:ℝ)^J)⁻¹ := by
    simp only [hYb, hM]; rw [matrixEval_cfc hX]
    refine opNorm_sandwich hX hY hlo hhi _ (by positivity) (fun i => ?_)
    exact (filter_facts hbJ0 hbJ1 (hx0 i) (hx1 i)).2.2.1
  have htail : T J ≤ ε / 4 := by
    have h1 := traceNorm_le_opNorm hYJH
    have hdr : (0:ℝ) < d := by exact_mod_cast hd0
    calc T J ≤ d * opNorm (Yb ((2:ℝ)^J)⁻¹) := h1
      _ ≤ d * (2^7 * ((2:ℝ)^J)⁻¹) := by gcongr
      _ ≤ ε / 4 := by
          rw [← div_eq_mul_inv, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          rw [div_le_iff₀ hε] at hJ1
          nlinarith
  -- the scales
  have hsc : ∀ i ∈ Finset.range J, |E i (Yb ((2:ℝ)^i)⁻¹) - E i (Yb ((2:ℝ)^(i+1))⁻¹)| ≤
      2^16 / (Kn (i+1) : ℝ) * ∑ k, hfun (i+1) (hX.eigenvalues k) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    obtain ⟨hK2, -, -⟩ := K_facts hd1 hε hε1' (i+1) (by omega)
    have h := scale_err hX hd0 hY hlo hhi hx0 hx1 (Kn (i+1)) hK2 (i+1) (by omega)
    have e : ((2:ℝ)^i)⁻¹ = 2 * ((2:ℝ)^(i+1))⁻¹ := by rw [pow_succ, mul_inv]; field_simp
    simp only [hE, hYb, hM, e]
    exact h
  have hnum := approx_numeric hd1 hε (fun k => hX.eigenvalues k) hx0 hxs J (fun l => (Kn l : ℝ))
    (fun l hl1 hlJ => (K_facts hd1 hε hε1' l hlJ).2.2)
  have hsum : |∑ i ∈ Finset.range J, (E i (Yb ((2:ℝ)^(i+1))⁻¹) - E i (Yb ((2:ℝ)^i)⁻¹))| ≤ ε / 4 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (fun i hi => ?_)) hnum
    rw [abs_sub_comm]; exact hsc i hi
  have hTJ0 : 0 ≤ T J := by
    simp only [hT]; rw [traceNorm_eq hYJH]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have := abs_add_le (-(T J)) (∑ i ∈ Finset.range J, (E i (Yb ((2:ℝ)^(i+1))⁻¹) - E i (Yb ((2:ℝ)^i)⁻¹)))
  rw [abs_neg, abs_of_nonneg hTJ0] at this
  calc |QAlgorithms.traceNorm Y - T J + ∑ i ∈ Finset.range J, (E i (Yb ((2:ℝ)^(i+1))⁻¹) - E i (Yb ((2:ℝ)^i)⁻¹)) -
        QAlgorithms.traceNorm Y|
      = |-(T J) + ∑ i ∈ Finset.range J, (E i (Yb ((2:ℝ)^(i+1))⁻¹) - E i (Yb ((2:ℝ)^i)⁻¹))| := by ring_nf
    _ ≤ ε := by linarith

end OTDP26

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
open OptimalTraceDistance.Estimation in
theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
  ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 → ∀ X Y : Mat d,
  X.IsHermitian → Y.IsHermitian → X.PosSemidef → tr X ≤ 1 →
  lePSD (-X) Y → lePSD Y X →
    (expressionDegree (F d ε) : ℝ) ≤ C*Real.sqrt d/ε ∧
    |(evaluate (F d ε) X Y).re - QAlgorithms.traceNorm Y| ≤ ε ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ expressionDegree (F d ε) →
      HasOrderedBound j (taylor (F d ε) X Y j)
        (if j = 1 then C*Real.log d/ε^3 else
          (C*d/ε^2)^j / ((d : ℝ)*ε*((2*j).factorial : ℝ))) := by
  refine ⟨2^123, by positivity, fun d hd ε hε hε1 X Y hX hY hX0 htr hlo hhi => ⟨?_, ?_, ?_⟩⟩
  · refine (OTDP26.degree_clause hd hε hε1).trans ?_
    gcongr
    norm_num
  · exact OTDP26.approx_clause hd hε hε1 hX hY hX0 htr hlo hhi
  · intro j hj _
    exact OTDP26.taylor_clause hd hε hε1 hX hY hX0 htr hlo hhi hj
