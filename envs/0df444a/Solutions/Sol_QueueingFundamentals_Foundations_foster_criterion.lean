-- Prove2me | solution 1 for QueueingFundamentals.Foundations.foster_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T08:16:12.656496+00:00
-- url     : https://prove2.me/submissions/64a0ada4-aa22-413f-8dd6-e713298243c9

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain

open scoped ENNReal
open QueueingFundamentals.Foundations

set_option autoImplicit false

namespace FC9A

variable (P : TransitionMatrix)

lemma p_le_one (i j : ℕ) : P.p i j ≤ 1 :=
  le_hasSum (P.row_sum i) j (fun k _ => P.nonneg i k)

lemma fp_two (n i j : ℕ) : P.firstPassage (n + 2) i j =
    ∑' l, if l = j then 0 else P.p i l * P.firstPassage (n + 1) l j := rfl

lemma fp_bound : ∀ n i j, 0 ≤ P.firstPassage n i j ∧ P.firstPassage n i j ≤ 1 := by
  intro n
  induction n with
  | zero => intro i j; simp [TransitionMatrix.firstPassage]
  | succ n ih =>
    intro i j
    cases n with
    | zero => exact ⟨P.nonneg i j, p_le_one P i j⟩
    | succ m =>
      rw [fp_two]
      have h0 : ∀ l, 0 ≤ (if l = j then 0 else P.p i l * P.firstPassage (m + 1) l j) := by
        intro l; split_ifs
        · exact le_rfl
        · exact mul_nonneg (P.nonneg i l) (ih l j).1
      have h1 : ∀ l, (if l = j then 0 else P.p i l * P.firstPassage (m + 1) l j) ≤ P.p i l := by
        intro l; split_ifs
        · exact P.nonneg i l
        · exact mul_le_of_le_one_right (P.nonneg i l) (ih l j).2
      have hs := Summable.of_nonneg_of_le h0 h1 (P.row_sum i).summable
      refine ⟨tsum_nonneg h0, ?_⟩
      calc _ ≤ ∑' l, P.p i l := hs.tsum_le_tsum h1 (P.row_sum i).summable
        _ = 1 := (P.row_sum i).tsum_eq

lemma fp_two_enn (n i j : ℕ) : ENNReal.ofReal (P.firstPassage (n + 2) i j) =
    ∑' l, if l = j then 0 else
      ENNReal.ofReal (P.p i l) * ENNReal.ofReal (P.firstPassage (n + 1) l j) := by
  have h0 : ∀ l, 0 ≤ (if l = j then 0 else P.p i l * P.firstPassage (n + 1) l j) := by
    intro l; split_ifs
    · exact le_rfl
    · exact mul_nonneg (P.nonneg i l) (fp_bound P (n + 1) l j).1
  have h1 : ∀ l, (if l = j then 0 else P.p i l * P.firstPassage (n + 1) l j) ≤ P.p i l := by
    intro l; split_ifs
    · exact P.nonneg i l
    · exact mul_le_of_le_one_right (P.nonneg i l) (fp_bound P (n + 1) l j).2
  have hs := Summable.of_nonneg_of_le h0 h1 (P.row_sum i).summable
  rw [fp_two, ENNReal.ofReal_tsum_of_nonneg h0 hs]
  congr 1; funext l
  split_ifs
  · simp
  · rw [ENNReal.ofReal_mul (P.nonneg _ _)]

lemma row_enn (i : ℕ) : ∑' l, ENNReal.ofReal (P.p i l) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (P.nonneg i) (P.row_sum i).summable,
    (P.row_sum i).tsum_eq, ENNReal.ofReal_one]

/-- killed one-step weights for target `j` -/
noncomputable def cc (j i k : ℕ) : ℝ≥0∞ := if k = j then 0 else ENNReal.ofReal (P.p i k)

lemma c_split (j i : ℕ) : ENNReal.ofReal (P.p i j) + ∑' k, cc P j i k = 1 := by
  have h : ∀ l, ENNReal.ofReal (P.p i l) =
      (if l = j then ENNReal.ofReal (P.p i j) else 0) + cc P j i l := by
    intro l; unfold cc; split_ifs with hl
    · subst hl; simp
    · simp
  rw [← row_enn P i]
  conv_rhs => rw [show (fun l => ENNReal.ofReal (P.p i l)) =
    fun l => (if l = j then ENNReal.ofReal (P.p i j) else 0) + cc P j i l from funext h]
  rw [ENNReal.tsum_add, tsum_ite_eq]

lemma a_rec (n i j : ℕ) : ENNReal.ofReal (P.firstPassage (n + 2) i j) =
    ∑' k, cc P j i k * ENNReal.ofReal (P.firstPassage (n + 1) k j) := by
  rw [fp_two_enn]
  congr 1; funext l
  unfold cc; split_ifs <;> simp

/-- survival (not yet hit `j`) mass after `n` steps -/
noncomputable def sv (j : ℕ) : ℕ → ℕ → ℝ≥0∞
  | 0, _ => 1
  | n + 1, i => ∑' k, cc P j i k * sv j n k

lemma sF (j : ℕ) : ∀ n i, sv P j n i +
    ∑ m ∈ Finset.range (n + 1), ENNReal.ofReal (P.firstPassage m i j) = 1 := by
  intro n
  induction n with
  | zero => intro i; simp [sv, TransitionMatrix.firstPassage]
  | succ n ih =>
    intro i
    have key : ∀ k, sv P j n k +
        ∑ m ∈ Finset.range n, ENNReal.ofReal (P.firstPassage (m + 1) k j) = 1 := by
      intro k
      have := ih k
      rw [Finset.sum_range_succ'] at this
      simpa [TransitionMatrix.firstPassage] using this
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [a_rec]
    have h1 : P.firstPassage (0 + 1) i j = P.p i j := rfl
    have h0 : P.firstPassage 0 i j = 0 := rfl
    rw [h1, h0, ENNReal.ofReal_zero, add_zero]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [← Finset.mul_sum]
    change ∑' k, cc P j i k * sv P j n k + _ = 1
    rw [← add_assoc, ← ENNReal.tsum_add]
    simp_rw [← mul_add, key, mul_one]
    rw [add_comm]; exact c_split P j i

/-- Lyapunov (supersolution) witness for target `j` -/
def Good (j : ℕ) : Prop :=
  ∃ h : ℕ → ℝ≥0∞, (∀ i, h i ≠ ⊤) ∧ ∀ i, 1 + ∑' k, cc P j i k * h k ≤ h i

lemma sum_sv_le (j : ℕ) (h : ℕ → ℝ≥0∞) (hsup : ∀ i, 1 + ∑' k, cc P j i k * h k ≤ h i) :
    ∀ N i, ∑ n ∈ Finset.range N, sv P j n i ≤ h i := by
  intro N
  induction N with
  | zero => intro i; simp
  | succ N ih =>
    intro i
    rw [Finset.sum_range_succ']
    change ∑ n ∈ Finset.range N, (∑' k, cc P j i k * sv P j n k) + 1 ≤ h i
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [← Finset.mul_sum]
    calc _ ≤ ∑' k, cc P j i k * h k + 1 := by
          gcongr with k; exact ih k
      _ = 1 + ∑' k, cc P j i k * h k := add_comm _ _
      _ ≤ h i := hsup i

lemma tail_le (j m i : ℕ) :
    ∑' n, (if m < n then ENNReal.ofReal (P.firstPassage n i j) else 0) ≤ sv P j m i := by
  set a : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (P.firstPassage n i j) with ha
  set B := ∑ n ∈ Finset.range (m + 1), a n
  have hB : B ≠ ⊤ := ENNReal.sum_ne_top.2 (fun _ _ => ENNReal.ofReal_ne_top)
  have hsplit : ∑' n, a n = ∑' n, (if m < n then a n else 0) + B := by
    have : ∀ n, a n = (if m < n then a n else 0) + (if m < n then 0 else a n) := by
      intro n; split_ifs <;> simp
    conv_lhs => rw [show a = fun n => (if m < n then a n else 0) + (if m < n then 0 else a n)
      from funext this]
    rw [ENNReal.tsum_add]
    congr 1
    rw [tsum_eq_sum (s := Finset.range (m + 1))]
    · apply Finset.sum_congr rfl
      intro n hn
      have : ¬ m < n := by simp [Finset.mem_range] at hn; omega
      simp [this]
    · intro n hn
      have : m < n := by simp [Finset.mem_range] at hn; omega
      simp [this]
  have hle : ∑' n, a n ≤ 1 := by
    apply ENNReal.tsum_le_of_sum_range_le
    intro n
    calc ∑ k ∈ Finset.range n, a k ≤ ∑ k ∈ Finset.range (n + 1), a k :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ n))
      _ ≤ sv P j n i + ∑ k ∈ Finset.range (n + 1), a k := le_add_self
      _ = 1 := sF P j n i
  have h1 : ∑' n, (if m < n then a n else 0) + B ≤ sv P j m i + B := by
    rw [← hsplit, sF P j m i]; exact hle
  exact (ENNReal.add_le_add_iff_right hB).1 h1

lemma posrec_of_good (j : ℕ) (hg : Good P j) : P.PositiveRecurrentState j := by
  obtain ⟨h, hfin, hsup⟩ := hg
  set a : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (P.firstPassage n j j) with ha
  have hsv : ∑' n, sv P j n j ≤ h j :=
    ENNReal.tsum_le_of_sum_range_le (fun N => sum_sv_le P j h hsup N j)
  have hsvt : ∑' n, sv P j n j ≠ ⊤ := ne_top_of_le_ne_top (hfin j) hsv
  refine ⟨?_, ?_⟩
  · -- returnProb = 1
    have hle : ∑' n, a n ≤ 1 := by
      apply ENNReal.tsum_le_of_sum_range_le
      intro n
      calc ∑ k ∈ Finset.range n, a k ≤ ∑ k ∈ Finset.range (n + 1), a k :=
            Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ n))
        _ ≤ sv P j n j + ∑ k ∈ Finset.range (n + 1), a k := le_add_self
        _ = 1 := sF P j n j
    have hge : 1 ≤ ∑' n, a n := by
      have ht := (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsvt).add_const (∑' n, a n)
      rw [zero_add] at ht
      refine ge_of_tendsto' ht (fun n => ?_)
      calc (1 : ℝ≥0∞) = sv P j n j + ∑ k ∈ Finset.range (n + 1), a k := (sF P j n j).symm
        _ ≤ sv P j n j + ∑' k, a k := by gcongr; exact ENNReal.sum_le_tsum _
    exact le_antisymm hle hge
  · -- mean recurrence time finite
    have hm : ∀ n : ℕ, (n : ℝ≥0∞) * a n = ∑' m : ℕ, (if m < n then a n else 0) := by
      intro n
      rw [tsum_eq_sum (s := Finset.range n)]
      · rw [Finset.sum_congr rfl (fun m hm => if_pos (Finset.mem_range.1 hm))]
        simp
      · intro m hm
        rw [if_neg (by simpa [Finset.mem_range] using hm)]
    change ∑' n : ℕ, (n : ℝ≥0∞) * a n < ⊤
    simp_rw [hm]
    rw [ENNReal.tsum_comm]
    calc _ ≤ ∑' m, sv P j m j := ENNReal.tsum_le_tsum (fun m => tail_le P j m j)
      _ ≤ h j := hsv
      _ < ⊤ := lt_top_iff_ne_top.2 (hfin j)

lemma good_step (s t : ℕ) (hs : Good P s) (hp : 0 < P.p s t) : Good P t := by
  by_cases hst : t = s
  · subst hst; exact hs
  obtain ⟨h, hfin, hsup⟩ := hs
  set q := ENNReal.ofReal (P.p s t) with hq
  have hq0 : q ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  set K := h s / q with hKdef
  have hK : K ≠ ⊤ := ENNReal.div_ne_top (hfin s) hq0
  have hKq : K * q = h s := ENNReal.div_mul_cancel hq0 hqt
  let y : ℕ → ℝ≥0∞ := fun i => if i = s then K else h i + K
  refine ⟨y, ?_, ?_⟩
  · intro i
    simp only [y]
    split_ifs
    · exact hK
    · exact ENNReal.add_ne_top.2 ⟨hfin i, hK⟩
  · intro i
    have hterm : ∀ k, cc P t i k * y k ≤ cc P s i k * h k + cc P t i k * K := by
      intro k
      simp only [y, cc]
      by_cases hkt : k = t
      · simp [hkt]
      · by_cases hks : k = s
        · subst hks; simp [hkt]
        · simp [hkt, hks, mul_add]
    have hA := c_split P t i
    set A := ∑' k, cc P t i k
    have hA1 : A ≤ 1 := by rw [← hA]; exact le_add_self
    have hbound : 1 + ∑' k, cc P t i k * y k ≤ h i + A * K := by
      calc 1 + ∑' k, cc P t i k * y k
          ≤ 1 + ∑' k, (cc P s i k * h k + cc P t i k * K) := by
            gcongr with k; exact hterm k
        _ = (1 + ∑' k, cc P s i k * h k) + A * K := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, add_assoc]
        _ ≤ h i + A * K := by gcongr; exact hsup i
    refine hbound.trans ?_
    by_cases his : i = s
    · subst his
      simp only [y, if_true]
      have : K = (q + A) * K := by rw [hA, one_mul]
      refine le_of_eq ?_
      calc h i + A * K = K * q + A * K := by rw [hKq]
        _ = (q + A) * K := by ring
        _ = K := this.symm
    · simp only [y, if_neg his]
      gcongr
      exact mul_le_of_le_one_left (by simp) hA1

lemma good_zero (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hsum : ∀ i, Summable (fun j => P.p i j * x j))
    (hdrift : ∀ i, i ≠ 0 → ∑' j, P.p i j * x j ≤ x i - 1) : Good P 0 := by
  let D : ℕ → ℝ≥0∞ := fun i => ∑' k, cc P 0 i k * ENNReal.ofReal (x k)
  have hD : ∀ i, D i ≤ ENNReal.ofReal (∑' k, P.p i k * x k) := by
    intro i
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (P.nonneg i k) (hx k)) (hsum i)]
    apply ENNReal.tsum_le_tsum
    intro k
    rw [ENNReal.ofReal_mul (P.nonneg i k)]
    unfold cc; split_ifs
    · simp
    · exact le_rfl
  let h : ℕ → ℝ≥0∞ := fun i => if i = 0 then 1 + D 0 else ENNReal.ofReal (x i)
  have hc : ∀ i, ∑' k, cc P 0 i k * h k = D i := by
    intro i
    simp only [D]
    congr 1; funext k
    simp only [h, cc]
    split_ifs <;> simp_all
  refine ⟨h, ?_, ?_⟩
  · intro i
    simp only [h]
    split_ifs
    · exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hD 0)⟩
    · exact ENNReal.ofReal_ne_top
  · intro i
    rw [hc]
    by_cases hi : i = 0
    · subst hi; simp [h]
    · simp only [h, if_neg hi]
      have hd := hdrift i hi
      have hnn : 0 ≤ ∑' k, P.p i k * x k :=
        tsum_nonneg (fun k => mul_nonneg (P.nonneg i k) (hx k))
      calc 1 + D i ≤ 1 + ENNReal.ofReal (∑' k, P.p i k * x k) := by gcongr; exact hD i
        _ ≤ 1 + ENNReal.ofReal (x i - 1) := by gcongr
        _ = ENNReal.ofReal (x i) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
          congr 1; ring

lemma propagate (Q : ℕ → Prop) (hQ : ∀ i l, Q i → 0 < P.p i l → Q l) :
    ∀ n i j, Q i → 0 < P.stepProb n i j → Q j := by
  intro n
  induction n with
  | zero =>
    intro i j hi hs
    change 0 < (if i = j then (1 : ℝ) else 0) at hs
    split_ifs at hs with h
    · subst h; exact hi
    · exact absurd hs (lt_irrefl 0)
  | succ n ih =>
    intro i j hi hs
    change 0 < ∑' k, P.p i k * P.stepProb n k j at hs
    obtain ⟨k, hk⟩ : ∃ k, 0 < P.p i k * P.stepProb n k j := by
      by_contra hc
      push Not at hc
      exact absurd (tsum_nonpos hc) (not_le.2 hs)
    have hboth := (pos_and_pos_or_neg_and_neg_of_mul_pos hk).resolve_right
      (fun h => absurd h.1 (not_lt.2 (P.nonneg i k)))
    exact ih k j (hQ i k hi hboth.1) hboth.2

end FC9A

open QueueingFundamentals.Foundations in
theorem solution (P : TransitionMatrix) (hirr : P.Irreducible) (hap : P.Aperiodic)
    (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hsum : ∀ i, Summable (fun j => P.p i j * x j))
    (hdrift : ∀ i, i ≠ 0 → ∑' j, P.p i j * x j ≤ x i - 1) :
    P.PositiveRecurrent := by
  intro j
  have g0 := FC9A.good_zero P x hx hsum hdrift
  obtain ⟨n, hn⟩ := hirr 0 j
  have gj : FC9A.Good P j :=
    FC9A.propagate P (FC9A.Good P) (fun i l hi hp => FC9A.good_step P i l hi hp) n 0 j g0 hn
  exact FC9A.posrec_of_good P j gj
