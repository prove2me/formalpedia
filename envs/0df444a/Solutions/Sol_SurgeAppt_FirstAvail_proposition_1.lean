-- Prove2me | solution 1 for SurgeAppt.FirstAvail.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T03:10:53.744067+00:00
-- url     : https://prove2.me/submissions/6fa40279-a467-4275-a15f-2e4e2d956d70

import Mathlib
import Definitions.Def_SurgeAppt_FirstAvail_Model

set_option autoImplicit false

namespace SurgeAppt.FirstAvail.Pf

open SurgeAppt.FirstAvail




/-! ## Part A: algebra of `phi` and condition (13) -/

lemma phi_zero (P : Params) : phi P 0 = P.cpost := by simp [phi]

lemma phi_succ (P : Params) (d : ℕ) :
    phi P (d + 1) = P.β * P.pF + P.β * P.pFbar * phi P d := by
  simp only [phi]
  rw [Finset.sum_range_succ']
  have h : ∀ l ∈ Finset.range d, P.β ^ (l + 1 + 1) * P.pF * P.pFbar ^ (l + 1)
      = P.β * P.pFbar * (P.β ^ (l + 1) * P.pF * P.pFbar ^ l) := by intro l _; ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  ring

lemma cpost_nonneg (P : Params) (hP : P.Standing) : 0 ≤ P.cpost := by
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4, h5, h6, -⟩ := hP
  unfold Params.cpost Params.pSbar
  have : 0 ≤ 1 - P.pS := by linarith
  positivity

lemma cpost_le_one (P : Params) (hP : P.Standing) : P.cpost ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4, h5, h6, -⟩ := hP
  unfold Params.cpost Params.pSbar
  nlinarith

lemma pFbar_pos (P : Params) (hP : P.Standing) : 0 < P.pFbar := by
  obtain ⟨-, -, -, -, -, h, -⟩ := hP
  unfold Params.pFbar; linarith

lemma pFbar_lt_one (P : Params) (hP : P.Standing) : P.pFbar < 1 := by
  obtain ⟨-, -, -, -, h, -⟩ := hP
  unfold Params.pFbar; linarith

lemma phi_nonneg (P : Params) (hP : P.Standing) (d : ℕ) : 0 ≤ phi P d := by
  induction d with
  | zero => rw [phi_zero]; exact cpost_nonneg P hP
  | succ d ih =>
    rw [phi_succ]
    have := pFbar_pos P hP
    obtain ⟨-, -, -, -, h1, -, -, -, -, -, -, -, -, hb, -⟩ := hP
    positivity

lemma phi_le_one (P : Params) (hP : P.Standing) (d : ℕ) : phi P d ≤ 1 := by
  induction d with
  | zero => rw [phi_zero]; exact cpost_le_one P hP
  | succ d ih =>
    rw [phi_succ]
    have h0 := phi_nonneg P hP d
    have hfb := pFbar_pos P hP
    obtain ⟨-, -, -, -, h1, h2, -, -, -, -, -, -, -, hb, hb1, -⟩ := hP
    have e : P.pFbar = 1 - P.pF := rfl
    have : P.β * P.pFbar * phi P d ≤ P.β * P.pFbar := by
      have := mul_le_mul_of_nonneg_left ih (le_of_lt (mul_pos hb hfb)); linarith
    nlinarith

/-- `rhs13 d d' * (pFbar^d β^d) = phi d' - phi d`. -/
lemma rhs13_mul (P : Params) (hP : P.Standing) (d d' : ℕ) (hdd : d ≤ d') :
    rhs13 P d d' * (P.pFbar ^ d * P.β ^ d) = phi P d' - phi P d := by
  have hfb := pFbar_pos P hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := hP
  have hne : P.pFbar ^ d * P.β ^ d ≠ 0 := by positivity
  unfold rhs13 phi
  rw [add_mul, div_mul_cancel₀ _ hne]
  have hsum : ∑ l ∈ Finset.range d', P.β ^ (l + 1) * P.pF * P.pFbar ^ l
      = ∑ l ∈ Finset.range d, P.β ^ (l + 1) * P.pF * P.pFbar ^ l
        + ∑ i ∈ Finset.Ico d d', P.β ^ (i + 1) * P.pF * P.pFbar ^ i :=
    (Finset.sum_range_add_sum_Ico _ hdd).symm
  rw [hsum]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdd
  rw [Nat.add_sub_cancel_left]
  ring

/-- Condition (13) in the shifted form used by the proof: for `c < c'` with `c' + 1 ≤ D`,
`cs (β pFbar)^c ≤ cF (phi c' - phi c)`. -/
lemma cond13_shift (P : Params) (hP : P.Standing) (h13 : Condition13 P) (c c' : ℕ)
    (hcc : c < c') (hc' : c' + 1 ≤ P.D) :
    P.cs * (P.β * P.pFbar) ^ c ≤ P.cF * (phi P c' - phi P c) := by
  have hfb := pFbar_pos P hP
  have hstd := hP
  obtain ⟨-, -, -, hcF, -, -, -, -, -, -, -, -, -, hb, -⟩ := hP
  have h := h13 (c + 1) (c' + 1) (by omega) (by omega) hc'
  rw [div_le_iff₀ hcF] at h
  have hpos : 0 < P.pFbar ^ (c + 1) * P.β ^ (c + 1) := by positivity
  have h2 : P.cs * (P.pFbar ^ (c + 1) * P.β ^ (c + 1))
      ≤ P.cF * (rhs13 P (c + 1) (c' + 1) * (P.pFbar ^ (c + 1) * P.β ^ (c + 1))) := by nlinarith
  rw [rhs13_mul P hstd _ _ (by omega), phi_succ, phi_succ] at h2
  have hbp : 0 < P.β * P.pFbar := mul_pos hb hfb
  have h3 : (P.β * P.pFbar) * (P.cs * (P.β * P.pFbar) ^ c)
      ≤ (P.β * P.pFbar) * (P.cF * (phi P c' - phi P c)) := by
    have e1 : P.pFbar ^ (c + 1) * P.β ^ (c + 1) = (P.β * P.pFbar) * (P.β * P.pFbar) ^ c := by ring
    rw [e1] at h2; nlinarith
  exact le_of_mul_le_mul_left h3 hbp

lemma phi_succ_sub (P : Params) (k : ℕ) :
    phi P (k + 1) - phi P k = (P.β * P.pFbar) ^ k * (phi P 1 - phi P 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 := phi_succ P (k + 1)
    have e2 := phi_succ P k
    rw [pow_succ]
    linear_combination e1 - e2 + (P.β * P.pFbar) * ih

/-- When `D ≥ 2`, condition (13) makes `phi` nondecreasing on all of `ℕ`. -/
lemma phi_mono (P : Params) (hP : P.Standing) (h13 : Condition13 P) (hD : 2 ≤ P.D) :
    Monotone (phi P) := by
  have h01 := cond13_shift P hP h13 0 1 (by omega) (by omega)
  have hcs : 0 ≤ P.cs := hP.2.2.1
  have hcF : 0 < P.cF := hP.2.2.2.1
  have hd : 0 ≤ phi P 1 - phi P 0 := by
    simp only [pow_zero, mul_one] at h01
    by_contra hneg; push Not at hneg
    have : P.cF * (phi P 1 - phi P 0) < 0 := mul_neg_of_pos_of_neg hcF hneg
    linarith
  have hfb := pFbar_pos P hP
  have hb : 0 < P.β := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply monotone_nat_of_le_succ
  intro k
  have := phi_succ_sub P k
  have : 0 ≤ (P.β * P.pFbar) ^ k * (phi P 1 - phi P 0) := by positivity
  linarith

/-- The key cost inequality: for `c < c' ≤ D - 1`, `cs (β pFbar)^c + cF phi c ≤ cF phi c'`. -/
lemma key_ineq (P : Params) (hP : P.Standing) (h13 : Condition13 P) (c c' : ℕ)
    (hcc : c < c') (hc' : c' + 1 ≤ P.D) :
    P.cs * (P.β * P.pFbar) ^ c + P.cF * phi P c ≤ P.cF * phi P c' := by
  have := cond13_shift P hP h13 c c' hcc hc'; nlinarith





/-! ## Part B: the transition kernel -/

lemma mem_validStates (P : Params) (s : Book P) :
    s ∈ validStates P ↔ (∀ d, s d ≤ P.K) ∧ s (Fin.last P.D) = 0 := by
  simp [validStates, Fintype.mem_piFinset]

/-- Pascal split of one binomial factor. -/
lemma binom_split (n k : ℕ) (p : ℝ) :
    ((n + 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n + 1 - k)
      = (1 - p) * ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
        + (if 1 ≤ k then p * ((n.choose (k - 1) : ℝ) * p ^ (k - 1) * (1 - p) ^ (n - (k - 1)))
           else 0) := by
  rcases k with _ | m
  · simp [pow_succ]; ring
  · simp only [Nat.choose_succ_succ, Nat.cast_add, le_add_iff_nonneg_left, zero_le,
      if_true, Nat.add_sub_cancel]
    rcases Nat.lt_or_ge n (m + 1) with h | h
    · rw [Nat.choose_eq_zero_of_lt h]
      have : n + 1 - (m + 1) = n - m := by omega
      rw [this]; simp; ring
    · have e1 : n + 1 - (m + 1) = n - (m + 1) + 1 := by omega
      have e2 : n - m = n - (m + 1) + 1 := by omega
      rw [e1, e2]; ring

lemma trans_ne_zero_le (P : Params) (T s' : Book P) (h : trans P T s' ≠ 0) (d : Fin P.D) :
    s' d.castSucc ≤ T d.succ := by
  unfold trans at h
  split_ifs at h with hl
  · rw [Finset.prod_ne_zero_iff] at h
    have := h d (Finset.mem_univ _)
    by_contra hlt; push Not at hlt
    apply this
    rw [Nat.choose_eq_zero_of_lt hlt]; simp
  · exact absurd rfl h

lemma trans_nonneg (P : Params) (hP : P.Standing) (T s' : Book P) : 0 ≤ trans P T s' := by
  unfold trans
  have h1 : 0 ≤ P.pFbar := by unfold Params.pFbar; linarith [hP.2.2.2.2.2.1]
  have h2 : 0 ≤ 1 - P.pFbar := by unfold Params.pFbar; linarith [hP.2.2.2.2.1]
  split_ifs
  · apply Finset.prod_nonneg; intro d _; positivity
  · exact le_refl _

/-- Pointwise split of the kernel when one appointment is added at slot `r.succ`. -/
lemma trans_add_single (P : Params) (T s' : Book P) (r : Fin P.D) :
    trans P (T + Pi.single r.succ 1 : Book P) s'
      = (1 - P.pFbar) * trans P T s'
        + (if 1 ≤ s' r.castSucc then P.pFbar * trans P T (s' - Pi.single r.castSucc 1 : Book P) else 0) := by
  have hlast : (s' - Pi.single r.castSucc 1 : Book P) (Fin.last P.D) = s' (Fin.last P.D) := by
    have : (Fin.last P.D) ≠ r.castSucc := (Fin.castSucc_ne_last r).symm
    simp [Pi.single_apply, this]
  unfold trans
  rw [hlast]
  split_ifs with hl hk
  · -- main case
    set f : Fin P.D → ℝ := fun d => ((T d.succ).choose (s' d.castSucc) : ℝ) * P.pFbar ^ (s' d.castSucc)
      * (1 - P.pFbar) ^ (T d.succ - s' d.castSucc) with hf
    have hrest : ∀ d ∈ ({r}ᶜ : Finset (Fin P.D)),
        (((T + Pi.single r.succ 1 : Book P) d.succ).choose (s' d.castSucc) : ℝ) * P.pFbar ^ (s' d.castSucc)
          * (1 - P.pFbar) ^ ((T + Pi.single r.succ 1 : Book P) d.succ - s' d.castSucc) = f d := by
      intro d hd
      have hdr : d ≠ r := by simpa using hd
      have : (T + Pi.single r.succ 1 : Book P) d.succ = T d.succ := by
        simp [Pi.single_apply, Fin.succ_inj, hdr]
      rw [this]
    have hrest2 : ∀ d ∈ ({r}ᶜ : Finset (Fin P.D)),
        ((T d.succ).choose ((s' - Pi.single r.castSucc 1 : Book P) d.castSucc) : ℝ)
          * P.pFbar ^ ((s' - Pi.single r.castSucc 1 : Book P) d.castSucc)
          * (1 - P.pFbar) ^ (T d.succ - (s' - Pi.single r.castSucc 1 : Book P) d.castSucc) = f d := by
      intro d hd
      have hdr : d ≠ r := by simpa using hd
      have : (s' - Pi.single r.castSucc 1 : Book P) d.castSucc = s' d.castSucc := by
        simp [Pi.single_apply, Fin.castSucc_inj, hdr]
      rw [this]
    rw [Fintype.prod_eq_mul_prod_compl r,
      Fintype.prod_eq_mul_prod_compl r,
      Fintype.prod_eq_mul_prod_compl r,
      Finset.prod_congr rfl hrest, Finset.prod_congr rfl hrest2]
    have e1 : (T + Pi.single r.succ 1 : Book P) r.succ = T r.succ + 1 := by simp
    have e2 : (s' - Pi.single r.castSucc 1 : Book P) r.castSucc = s' r.castSucc - 1 := by simp
    rw [e1, e2, binom_split, if_pos hk]
    ring
  · rw [Fintype.prod_eq_mul_prod_compl r,
      Fintype.prod_eq_mul_prod_compl r]
    have hk0 : s' r.castSucc = 0 := by omega
    have e1 : (T + Pi.single r.succ 1 : Book P) r.succ = T r.succ + 1 := by simp
    have hrest : ∀ d ∈ ({r}ᶜ : Finset (Fin P.D)),
        (((T + Pi.single r.succ 1 : Book P) d.succ).choose (s' d.castSucc) : ℝ) * P.pFbar ^ (s' d.castSucc)
          * (1 - P.pFbar) ^ ((T + Pi.single r.succ 1 : Book P) d.succ - s' d.castSucc)
        = ((T d.succ).choose (s' d.castSucc) : ℝ) * P.pFbar ^ (s' d.castSucc)
          * (1 - P.pFbar) ^ (T d.succ - s' d.castSucc) := by
      intro d hd
      have hdr : d ≠ r := by simpa using hd
      have : (T + Pi.single r.succ 1 : Book P) d.succ = T d.succ := by
        simp [Pi.single_apply, Fin.succ_inj, hdr]
      rw [this]
    rw [Finset.prod_congr rfl hrest, e1, hk0]
    simp [pow_succ]; ring
  all_goals simp

/-- Summed split: for `T r.succ < K`, `E_{T + e_{r+1}}[f] = (1-pFbar) E_T[f] + pFbar E_T[f(· + e_r)]`. -/
lemma sum_trans_add_single (P : Params) (T : Book P) (r : Fin P.D) (hT : T r.succ < P.K)
    (f : Book P → ℝ) :
    ∑ s' ∈ validStates P, trans P (T + Pi.single r.succ 1 : Book P) s' * f s'
      = (1 - P.pFbar) * ∑ s' ∈ validStates P, trans P T s' * f s'
        + P.pFbar * ∑ s' ∈ validStates P, trans P T s' * f (s' + Pi.single r.castSucc 1) := by
  simp_rw [trans_add_single, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro x _; ring
  · symm
    apply Finset.sum_bij_ne_zero (fun s'' _ _ => s'' + Pi.single r.castSucc 1)
    · intro s'' hs'' hne
      have hne' : trans P T s'' ≠ 0 := by
        intro h0; apply hne; rw [h0]; ring
      have hle := trans_ne_zero_le P T s'' hne' r
      rw [mem_validStates] at hs'' ⊢
      refine ⟨fun d => ?_, ?_⟩
      · by_cases hd : d = r.castSucc
        · subst hd; simp; omega
        · simp [Pi.single_apply, hd]; exact hs''.1 d
      · simp [Pi.single_apply, (Fin.castSucc_ne_last r).symm, hs''.2]
    · intro a _ _ b _ _ h
      funext i; have := congrFun h i; simp at this; exact this
    · intro s' hs' hne
      have hk : 1 ≤ s' r.castSucc := by
        by_contra hk; apply hne; rw [if_neg hk]; ring
      refine ⟨s' - Pi.single r.castSucc 1, ?_, ?_, ?_⟩
      · rw [mem_validStates] at hs' ⊢
        refine ⟨fun d => le_trans (Nat.sub_le _ _) (hs'.1 d), ?_⟩
        simp [Pi.single_apply, (Fin.castSucc_ne_last r).symm, hs'.2]
      · intro h0; apply hne; rw [if_pos hk]
        have hx : (s' - Pi.single r.castSucc 1 + Pi.single r.castSucc 1 : Book P) = s' := by
          funext i; by_cases hi : i = r.castSucc
          · subst hi; simp; omega
          · simp [Pi.single_apply, hi]
        rw [hx] at h0; rw [mul_assoc]; exact h0
      · funext i; by_cases hi : i = r.castSucc
        · subst hi; simp; omega
        · simp [Pi.single_apply, hi]
    · intro s'' _ _
      have hk : 1 ≤ (s'' + Pi.single r.castSucc 1 : Book P) r.castSucc := by simp
      rw [if_pos hk]
      have hx : (s'' + Pi.single r.castSucc 1 - Pi.single r.castSucc 1 : Book P) = s'' := by
        funext i; simp
      rw [hx]; ring

/-- Induction over post-action books by adding one appointment at a time to slots `≥ 1`. -/
lemma book_induction (P : Params) (Q : Book P → Prop)
    (h0 : ∀ T : Book P, (∀ d : Fin P.D, T d.succ = 0) → Q T)
    (hstep : ∀ (T : Book P) (r : Fin P.D), T r.succ < P.K → (∀ d : Fin P.D, T d.succ ≤ P.K) → Q T →
      Q (T + Pi.single r.succ 1)) :
    ∀ T : Book P, (∀ d : Fin P.D, T d.succ ≤ P.K) → Q T := by
  suffices H : ∀ n : ℕ, ∀ T : Book P, ∑ d : Fin P.D, T d.succ = n → (∀ d : Fin P.D, T d.succ ≤ P.K) → Q T by
    intro T hT; exact H _ T rfl hT
  intro n
  induction n with
  | zero =>
    intro T hs _
    apply h0; intro d
    exact (Finset.sum_eq_zero_iff.mp hs) d (Finset.mem_univ _)
  | succ n ih =>
    intro T hs hT
    have : ∃ r : Fin P.D, 1 ≤ T r.succ := by
      by_contra hno; push Not at hno
      have : ∑ d : Fin P.D, T d.succ = 0 := Finset.sum_eq_zero (fun d _ => by have := hno d; omega)
      omega
    obtain ⟨r, hr⟩ := this
    set T' : Book P := T - Pi.single r.succ 1 with hT'
    have hTT : T = T' + Pi.single r.succ 1 := by
      funext i; by_cases hi : i = r.succ
      · subst hi; simp [hT']; omega
      · simp [hT', Pi.single_apply, hi]
    have hT'le : ∀ d : Fin P.D, T' d.succ ≤ P.K := fun d => le_trans (Nat.sub_le _ _) (hT d)
    have hT'r : T' r.succ < P.K := by
      have := hT r; simp [hT']; omega
    have hsum : ∑ d : Fin P.D, T' d.succ = n := by
      have h1 : ∑ d : Fin P.D, T d.succ = ∑ d : Fin P.D, T' d.succ + 1 := by
        rw [hTT]
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single r]
        · simp
        · intro b _ hb; simp [Pi.single_apply, Fin.succ_inj, hb]
        · simp
      omega
    rw [hTT]
    exact hstep T' r hT'r hT'le (ih T' hsum hT'le)

lemma trans_base (P : Params) (T s' : Book P) (hT : ∀ d : Fin P.D, T d.succ = 0) :
    trans P T s' = if s' = 0 then 1 else 0 := by
  unfold trans
  by_cases hs : s' = 0
  · subst hs; simp [hT]
  · rw [if_neg hs]
    split_ifs with hl
    · have : ∃ d : Fin P.D, s' d.castSucc ≠ 0 := by
        by_contra hno; push Not at hno
        apply hs; funext i
        induction i using Fin.lastCases with
        | last => exact hl
        | cast d => exact hno d
      obtain ⟨d, hd⟩ := this
      apply Finset.prod_eq_zero (Finset.mem_univ d)
      rw [hT d, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hd)]; simp
    · rfl

lemma zero_mem_validStates (P : Params) : (0 : Book P) ∈ validStates P := by
  rw [mem_validStates]; simp

lemma mass_eq_one (P : Params) (T : Book P) (hT : ∀ d : Fin P.D, T d.succ ≤ P.K) :
    ∑ s' ∈ validStates P, trans P T s' = 1 := by
  refine book_induction P (fun T => ∑ s' ∈ validStates P, trans P T s' = 1) ?_ ?_ T hT
  · intro T h0
    simp_rw [trans_base P T _ h0]
    rw [Finset.sum_ite_eq' (validStates P) (0 : Book P) (fun _ => (1 : ℝ))]
    simp [zero_mem_validStates]
  · intro T r hr _ ih
    have := sum_trans_add_single P T r hr (fun _ => 1)
    simp only [mul_one] at this
    rw [this, ih]; ring

lemma sum_single_castSucc (P : Params) (r : Fin P.D) :
    ∑ d : Fin P.D, ((Pi.single r.castSucc 1 : Book P) d.castSucc : ℝ) = 1 := by
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hb; simp [Pi.single_apply, Fin.castSucc_inj, hb]
  · simp

lemma moment_eq (P : Params) (T : Book P) (hT : ∀ d : Fin P.D, T d.succ ≤ P.K) :
    ∑ s' ∈ validStates P, trans P T s' * (∑ d : Fin P.D, (s' d.castSucc : ℝ))
      = P.pFbar * ∑ d : Fin P.D, (T d.succ : ℝ) := by
  refine book_induction P (fun T => ∑ s' ∈ validStates P, trans P T s' * (∑ d : Fin P.D, (s' d.castSucc : ℝ))
      = P.pFbar * ∑ d : Fin P.D, (T d.succ : ℝ)) ?_ ?_ T hT
  · intro T h0
    simp_rw [trans_base P T _ h0]
    simp [h0]
  · intro T r hr hle ih
    rw [sum_trans_add_single P T r hr]
    have e : ∀ s' : Book P, ∑ d : Fin P.D, (((s' + Pi.single r.castSucc 1 : Book P) d.castSucc : ℕ) : ℝ)
        = ∑ d : Fin P.D, (s' d.castSucc : ℝ) + 1 := by
      intro s'
      simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
      rw [sum_single_castSucc]
    simp_rw [e, mul_add, mul_one, Finset.sum_add_distrib, mass_eq_one P T hle, ih]
    have e2 : ∑ d : Fin P.D, (((T + Pi.single r.succ 1 : Book P) d.succ : ℕ) : ℝ)
        = ∑ d : Fin P.D, (T d.succ : ℝ) + 1 := by
      simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single r]
      · simp
      · intro b _ hb; simp [Pi.single_apply, Fin.succ_inj, hb]
      · simp
    rw [e2]; ring

/-- Expected number of failures: `pF * ∑_{d ≥ 1} T_d`. -/
lemma expected_fail (P : Params) (hP : P.Standing) (T : Book P) (hT : ∀ d : Fin P.D, T d.succ ≤ P.K) :
    ∑ s' ∈ validStates P, trans P T s' * failCount P T s'
      = P.pF * ∑ d : Fin P.D, (T d.succ : ℝ) := by
  have h1 : ∀ s' ∈ validStates P, trans P T s' * failCount P T s'
      = trans P T s' * (∑ d : Fin P.D, (T d.succ : ℝ)) - trans P T s' * (∑ d : Fin P.D, (s' d.castSucc : ℝ)) := by
    intro s' _
    unfold failCount
    split_ifs with h
    · rw [Finset.sum_sub_distrib]; ring
    · have : trans P T s' = 0 := le_antisymm (not_lt.mp h) (trans_nonneg P hP T s')
      rw [this]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_mul, mass_eq_one P T hT,
    moment_eq P T hT]
  unfold Params.pFbar; ring





/-! ## Part C: Markov chain shift and the one-step decomposition of `discountedCost` -/

section Chain
variable {σ : Type*} [DecidableEq σ] (X : Finset σ) (k : ℕ → σ → σ → ℝ)

lemma chainLaw_shift (x₀ : σ) (hx₀ : x₀ ∈ X) (t : ℕ) :
    ∀ x' ∈ X, chainLaw X k x₀ (t + 1) x'
      = ∑ y ∈ X, k 0 x₀ y * chainLaw X (fun t => k (t + 1)) y t x' := by
  induction t with
  | zero =>
    intro x' hx'
    simp only [chainLaw]
    rw [Finset.sum_eq_single x₀]
    · rw [Finset.sum_eq_single x']
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd hx' h
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hx₀ h
  | succ t ih =>
    intro x' _
    show ∑ x ∈ X, chainLaw X k x₀ (t + 1) x * k (t + 1) x x'
      = ∑ y ∈ X, k 0 x₀ y * ∑ x ∈ X, chainLaw X (fun t => k (t + 1)) y t x * k (t + 1) x x'
    rw [Finset.sum_congr rfl (fun x hx => by rw [ih x hx])]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring

variable (hk0 : ∀ t, ∀ x ∈ X, ∀ x', 0 ≤ k t x x') (hk1 : ∀ t, ∀ x ∈ X, ∑ x' ∈ X, k t x x' = 1)
include hk0 hk1

lemma chainLaw_nonneg_mass (x₀ : σ) (hx₀ : x₀ ∈ X) (t : ℕ) :
    (∀ x, 0 ≤ chainLaw X k x₀ t x) ∧ ∑ x ∈ X, chainLaw X k x₀ t x = 1 := by
  induction t with
  | zero =>
    refine ⟨fun x => by simp only [chainLaw]; split_ifs <;> norm_num, ?_⟩
    simp only [chainLaw]
    rw [Finset.sum_ite_eq' X x₀ (fun _ => (1 : ℝ))]; simp [hx₀]
  | succ t ih =>
    refine ⟨fun x' => ?_, ?_⟩
    · show 0 ≤ ∑ x ∈ X, chainLaw X k x₀ t x * k t x x'
      exact Finset.sum_nonneg (fun x hx => mul_nonneg (ih.1 x) (hk0 t x hx x'))
    · show ∑ x' ∈ X, ∑ x ∈ X, chainLaw X k x₀ t x * k t x x' = 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun x hx => by rw [hk1 t x hx, mul_one])]
      exact ih.2

variable (c : ℕ → σ → ℝ) (C : ℝ) (hc : ∀ t, ∀ x ∈ X, 0 ≤ c t x ∧ c t x ≤ C)
  (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
include hc hβ0 hβ1

lemma dc_term_bounds (x₀ : σ) (hx₀ : x₀ ∈ X) (t : ℕ) :
    0 ≤ β ^ t * ∑ x ∈ X, chainLaw X k x₀ t x * c t x ∧
      β ^ t * ∑ x ∈ X, chainLaw X k x₀ t x * c t x ≤ C * β ^ t := by
  have hm := chainLaw_nonneg_mass X k hk0 hk1 x₀ hx₀ t
  have hs0 : 0 ≤ ∑ x ∈ X, chainLaw X k x₀ t x * c t x :=
    Finset.sum_nonneg (fun x hx => mul_nonneg (hm.1 x) (hc t x hx).1)
  have hs1 : ∑ x ∈ X, chainLaw X k x₀ t x * c t x ≤ C := by
    calc ∑ x ∈ X, chainLaw X k x₀ t x * c t x ≤ ∑ x ∈ X, chainLaw X k x₀ t x * C :=
          Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hc t x hx).2 (hm.1 x))
      _ = C := by rw [← Finset.sum_mul, hm.2, one_mul]
  have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
  exact ⟨mul_nonneg hb hs0, by nlinarith⟩

lemma dc_summable (x₀ : σ) (hx₀ : x₀ ∈ X) :
    Summable (fun t => β ^ t * ∑ x ∈ X, chainLaw X k x₀ t x * c t x) :=
  Summable.of_nonneg_of_le (fun t => (dc_term_bounds X k hk0 hk1 c C hc β hβ0 hβ1 x₀ hx₀ t).1)
    (fun t => (dc_term_bounds X k hk0 hk1 c C hc β hβ0 hβ1 x₀ hx₀ t).2)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left C)

lemma dc_bounds (x₀ : σ) (hx₀ : x₀ ∈ X) :
    0 ≤ discountedCost X k c β x₀ ∧ discountedCost X k c β x₀ ≤ C / (1 - β) := by
  unfold discountedCost
  refine ⟨tsum_nonneg (fun t => (dc_term_bounds X k hk0 hk1 c C hc β hβ0 hβ1 x₀ hx₀ t).1), ?_⟩
  calc ∑' t, β ^ t * ∑ x ∈ X, chainLaw X k x₀ t x * c t x ≤ ∑' t : ℕ, C * β ^ t :=
        Summable.tsum_le_tsum (fun t => (dc_term_bounds X k hk0 hk1 c C hc β hβ0 hβ1 x₀ hx₀ t).2)
          (dc_summable X k hk0 hk1 c C hc β hβ0 hβ1 x₀ hx₀)
          ((summable_geometric_of_lt_one hβ0 hβ1).mul_left C)
    _ = C / (1 - β) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1]; ring

/-- One-step decomposition: `V(x₀) = c 0 x₀ + β ∑_y k 0 x₀ y V'(y)` with `V'` the shifted value. -/
lemma dc_shift (x₀ : σ) (hx₀ : x₀ ∈ X) :
    discountedCost X k c β x₀
      = c 0 x₀ + β * ∑ y ∈ X, k 0 x₀ y *
          discountedCost X (fun t => k (t + 1)) (fun t => c (t + 1)) β y := by
  have hk0' : ∀ t, ∀ x ∈ X, ∀ x', 0 ≤ (fun t => k (t + 1)) t x x' := fun t => hk0 (t + 1)
  have hk1' : ∀ t, ∀ x ∈ X, ∑ x' ∈ X, (fun t => k (t + 1)) t x x' = 1 := fun t => hk1 (t + 1)
  have hc' : ∀ t, ∀ x ∈ X, 0 ≤ (fun t => c (t + 1)) t x ∧ (fun t => c (t + 1)) t x ≤ C :=
    fun t => hc (t + 1)
  unfold discountedCost
  rw [(dc_summable X k hk0 hk1 c C hc β hβ0 hβ1 x₀ hx₀).tsum_eq_zero_add]
  congr 1
  · simp only [pow_zero, one_mul, chainLaw]
    rw [Finset.sum_eq_single x₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hx₀ h
  · have hterm : ∀ t : ℕ, β ^ (t + 1) * ∑ x ∈ X, chainLaw X k x₀ (t + 1) x * c (t + 1) x
        = β * ∑ y ∈ X, k 0 x₀ y * (β ^ t * ∑ x ∈ X,
            chainLaw X (fun t => k (t + 1)) y t x * (fun t => c (t + 1)) t x) := by
      intro t
      rw [Finset.sum_congr rfl (fun x hx => by rw [chainLaw_shift X k x₀ hx₀ t x hx])]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl; intro x _; ring
    simp_rw [hterm]
    rw [tsum_mul_left]
    congr 1
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl; intro y _; rw [tsum_mul_left]
    · intro y hy
      exact (dc_summable X (fun t => k (t + 1)) hk0' hk1' (fun t => c (t + 1)) C hc' β hβ0 hβ1 y hy).mul_left _

end Chain





/-! ## Part G: cumulative sums of the First-Available action; FA is admissible -/

lemma fill_sum (f : ℕ → ℕ) (a : ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range n, min (f i) (a - ∑ j ∈ Finset.range i, f j)
      = min a (∑ i ∈ Finset.range n, f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    omega

/-- `free` as a function on `ℕ` (zero past the horizon). -/
def freeN (P : Params) (s : Book P) (i : ℕ) : ℕ :=
  if h : i < P.D + 1 then free P s ⟨i, h⟩ else 0

lemma sum_filter_lt_eq (P : Params) (s : Book P) (k : Fin (P.D + 1)) :
    ∑ d ∈ Finset.univ.filter (fun d' => d' < k), free P s d
      = ∑ i ∈ Finset.range k.val, freeN P s i := by
  rw [Finset.sum_filter]
  have h1 : ∀ d : Fin (P.D + 1), (if d < k then free P s d else 0)
      = (fun i : ℕ => if i < k.val then freeN P s i else 0) d.val := by
    intro d
    simp only [freeN, dif_pos d.isLt, Fin.lt_def]
  rw [Finset.sum_congr rfl (fun d _ => h1 d), Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if i < k.val then freeN P s i else 0) (P.D + 1)]
  rw [← Finset.sum_filter]
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_range]
  have := k.isLt; omega

lemma sum_univ_free_eq (P : Params) (s : Book P) :
    ∑ d, free P s d = ∑ i ∈ Finset.range (P.D + 1), freeN P s i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => freeN P s i) (P.D + 1)]
  apply Finset.sum_congr rfl; intro d _; rw [freeN, dif_pos d.isLt]

/-- Total booked by First-Available is `min a (total free)`. -/
lemma sum_faAction (P : Params) (s : Book P) (a : ℕ) :
    ∑ d, faAction P s a d = min a (∑ d, free P s d) := by
  have h1 : ∀ d : Fin (P.D + 1), faAction P s a d
      = (fun i : ℕ => min (freeN P s i) (a - ∑ j ∈ Finset.range i, freeN P s j)) d.val := by
    intro d
    simp only [faAction, sum_filter_lt_eq, freeN, dif_pos d.isLt]
  rw [Finset.sum_congr rfl (fun d _ => h1 d),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => min (freeN P s i) (a - ∑ j ∈ Finset.range i, freeN P s j)),
    fill_sum, sum_univ_free_eq]

lemma faAction_le_free (P : Params) (s : Book P) (a : ℕ) (d : Fin (P.D + 1)) :
    faAction P s a d ≤ free P s d := by
  unfold faAction; exact min_le_left _ _

lemma faAction_zero (P : Params) (s : Book P) (a : ℕ) : faAction P s a 0 = 0 := by
  simp [faAction, free]

lemma prefix_add_free_le (P : Params) (s : Book P) (d : Fin (P.D + 1)) :
    ∑ d' ∈ Finset.univ.filter (fun d' => d' < d), free P s d' + free P s d ≤ ∑ d', free P s d' := by
  have hnot : d ∉ Finset.univ.filter (fun d' => d' < d) := by simp
  rw [add_comm, ← Finset.sum_insert hnot]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma faAction_isAdmissible (P : Params) : IsAdmissible P (faPolicy P) := by
  intro t s a hs _
  refine ⟨faAction_zero P s a, ?_, ?_, ?_⟩
  · intro d hd
    have h1 := faAction_le_free P s a d
    have h2 := hs.1 d
    simp only [free, if_neg hd] at h1
    show faAction P s a d + s d ≤ P.K
    omega
  · intro hf
    show ∑ d, faAction P s a d = a
    rw [sum_faAction]; unfold Feasible at hf; omega
  · intro hf d hd
    show faAction P s a d + s d = P.K
    unfold Feasible at hf; push Not at hf
    have h1 := prefix_add_free_le P s d
    have h2 := hs.1 d
    have h3 : faAction P s a d = free P s d := by
      unfold faAction; apply min_eq_left; omega
    rw [h3]; simp only [free, if_neg hd]; omega


/-! ## Part H: one-step decomposition of `value`, and the core First-Available lemma -/

noncomputable def Cmax (P : Params) : ℝ :=
  P.cs * P.K + P.β * P.cF * (P.pF * (P.D * P.K)) + P.K * P.cF + P.cF * P.M

lemma post_le (P : Params) (s : Book P) (a : ℕ) (u : Book P) (hu : Admissible P s a u) :
    ∀ d : Fin P.D, (s + u) d.succ ≤ P.K := by
  intro d
  have := hu.2.1 d.succ (Fin.succ_ne_zero d)
  simp only [Pi.add_apply]; omega

lemma hcost_le (P : Params) (hP : P.Standing) (x : ℕ) : 0 ≤ hcost P x ∧ hcost P x ≤ P.cs * x := by
  have hcs : 0 ≤ P.cs := hP.2.2.1
  unfold hcost
  refine ⟨mul_nonneg hcs (le_max_right _ _), mul_le_mul_of_nonneg_left ?_ hcs⟩
  apply max_le
  · have : (0:ℝ) ≤ P.Kb := Nat.cast_nonneg _
    linarith
  · exact Nat.cast_nonneg _

lemma hcost_succ (P : Params) (hP : P.Standing) (x : ℕ) :
    0 ≤ hcost P (x + 1) - hcost P x ∧ hcost P (x + 1) - hcost P x ≤ P.cs := by
  have hcs : 0 ≤ P.cs := hP.2.2.1
  unfold hcost
  have hm : max ((x:ℝ) - P.Kb) 0 ≤ max (((x+1 : ℕ) : ℝ) - P.Kb) 0 :=
    max_le_max (by push_cast; linarith) le_rfl
  have ha := abs_max_sub_max_le_abs (((x+1 : ℕ) : ℝ) - P.Kb) ((x:ℝ) - P.Kb) 0
  rw [show (((x+1 : ℕ) : ℝ) - P.Kb) - ((x:ℝ) - P.Kb) = 1 by push_cast; ring, abs_one] at ha
  have hle := le_trans (le_abs_self (max (((x+1 : ℕ) : ℝ) - P.Kb) 0 - max ((x:ℝ) - P.Kb) 0)) ha
  constructor
  · rw [← mul_sub]; exact mul_nonneg hcs (by linarith)
  · rw [← mul_sub]; nlinarith [mul_nonneg hcs (sub_nonneg.2 hle)]

lemma failsum_le (P : Params) (T : Book P) (hT : ∀ d : Fin P.D, T d.succ ≤ P.K) :
    0 ≤ ∑ d : Fin P.D, (T d.succ : ℝ) ∧ ∑ d : Fin P.D, (T d.succ : ℝ) ≤ P.D * P.K := by
  constructor
  · exact Finset.sum_nonneg (fun d _ => Nat.cast_nonneg _)
  · calc ∑ d : Fin P.D, (T d.succ : ℝ) ≤ ∑ _d : Fin P.D, (P.K : ℝ) :=
          Finset.sum_le_sum (fun d _ => by exact_mod_cast hT d)
      _ = P.D * P.K := by simp

lemma cost_bounds (P : Params) (hP : P.Standing) (s : Book P) (hs : s ∈ validStates P) (a : ℕ)
    (ha : a ≤ P.M) (u : Book P) (hu : Admissible P s a u) :
    0 ≤ cost P s a u ∧ cost P s a u ≤ Cmax P := by
  have hcs : 0 ≤ P.cs := hP.2.2.1
  have hcF : 0 < P.cF := hP.2.2.2.1
  have hpF : 0 < P.pF := hP.2.2.2.2.1
  have hβ : 0 < P.β := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hT := post_le P s a u hu
  have hfs := failsum_le P (s + u) hT
  have hc0 := cpost_nonneg P hP
  have hc1 := cpost_le_one P hP
  have hh := hcost_le P hP (s 0)
  have hs0 : (s 0 : ℝ) ≤ P.K := by exact_mod_cast ((mem_validStates P s).1 hs).1 0
  have hov : (overflow a u : ℝ) ≤ P.M := by
    have : overflow a u ≤ P.M := by unfold overflow; omega
    exact_mod_cast this
  have hov0 : (0 : ℝ) ≤ overflow a u := Nat.cast_nonneg _
  have hs00 : (0:ℝ) ≤ s 0 := Nat.cast_nonneg _
  unfold cost
  rw [expected_fail P hP _ hT]
  have t1 : P.cs * (s 0 : ℝ) ≤ P.cs * P.K := mul_le_mul_of_nonneg_left hs0 hcs
  have t2 : P.β * P.cF * (P.pF * ∑ d : Fin P.D, ((s + u) d.succ : ℝ)) ≤ P.β * P.cF * (P.pF * (P.D * P.K)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfs.2 hpF.le) (by positivity)
  have t2' : 0 ≤ P.β * P.cF * (P.pF * ∑ d : Fin P.D, ((s + u) d.succ : ℝ)) :=
    mul_nonneg (by positivity) (mul_nonneg hpF.le hfs.1)
  have t3 : (s 0 : ℝ) * P.cF * P.cpost ≤ P.K * P.cF := by
    have : (s 0 : ℝ) * P.cF * P.cpost ≤ (s 0 : ℝ) * P.cF * 1 :=
      mul_le_mul_of_nonneg_left hc1 (mul_nonneg hs00 hcF.le)
    nlinarith
  have t3' : 0 ≤ (s 0 : ℝ) * P.cF * P.cpost := mul_nonneg (mul_nonneg hs00 hcF.le) hc0
  have t4 : P.cF * (overflow a u : ℝ) ≤ P.cF * P.M := mul_le_mul_of_nonneg_left hov hcF.le
  have t4' : 0 ≤ P.cF * (overflow a u : ℝ) := mul_nonneg hcF.le hov0
  unfold Cmax
  constructor <;> linarith [hh.1, hh.2]

lemma pA_facts (P : Params) (hP : P.Standing) :
    (∀ a, 0 ≤ P.pA a) ∧ ∑ a ∈ Finset.range (P.M + 1), P.pA a = 1 :=
  ⟨hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

lemma stageCost_bounds (P : Params) (hP : P.Standing) (r : Book P → ℕ → Book P) (s : Book P)
    (hs : s ∈ validStates P) (hr : ∀ a, a ≤ P.M → Admissible P s a (r s a)) :
    0 ≤ stageCost P r s ∧ stageCost P r s ≤ Cmax P := by
  obtain ⟨hpA, hpA1⟩ := pA_facts P hP
  unfold stageCost
  have hb : ∀ a ∈ Finset.range (P.M + 1), 0 ≤ cost P s a (r s a) ∧ cost P s a (r s a) ≤ Cmax P :=
    fun a ha => cost_bounds P hP s hs a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) _
      (hr a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
  constructor
  · exact Finset.sum_nonneg (fun a ha => mul_nonneg (hpA a) (hb a ha).1)
  · calc ∑ a ∈ Finset.range (P.M + 1), P.pA a * cost P s a (r s a)
          ≤ ∑ a ∈ Finset.range (P.M + 1), P.pA a * Cmax P :=
            Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hb a ha).2 (hpA a))
      _ = Cmax P := by rw [← Finset.sum_mul, hpA1, one_mul]

lemma stepKernel_nonneg (P : Params) (hP : P.Standing) (r : Book P → ℕ → Book P) (s s' : Book P) :
    0 ≤ stepKernel P r s s' :=
  Finset.sum_nonneg (fun a _ => mul_nonneg ((pA_facts P hP).1 a) (trans_nonneg P hP _ _))

lemma stepKernel_sum (P : Params) (hP : P.Standing) (r : Book P → ℕ → Book P) (s : Book P)
    (hr : ∀ a, a ≤ P.M → Admissible P s a (r s a)) :
    ∑ s' ∈ validStates P, stepKernel P r s s' = 1 := by
  unfold stepKernel
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a ha => by
    rw [← Finset.mul_sum, mass_eq_one P _ (post_le P s a _ (hr a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))),
      mul_one])]
  exact (pA_facts P hP).2

lemma value_shift (P : Params) (hP : P.Standing) (π : Policy P) (hπ : IsAdmissible P π) (s : Book P)
    (hs : s ∈ validStates P) :
    value P π s = stageCost P (π 0) s
      + P.β * ∑ y ∈ validStates P, stepKernel P (π 0) s y * value P (fun t => π (t + 1)) y := by
  have hβ0 : 0 < P.β := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hβ1 : P.β < 1 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold value
  exact dc_shift (validStates P) (fun t => stepKernel P (π t))
    (fun t x _ x' => stepKernel_nonneg P hP _ x x')
    (fun t x hx => stepKernel_sum P hP _ x (fun a ha => hπ t x a ((mem_validStates P x).1 hx) ha))
    (fun t => stageCost P (π t)) (Cmax P)
    (fun t x hx => stageCost_bounds P hP _ x hx (fun a ha => hπ t x a ((mem_validStates P x).1 hx) ha))
    P.β hβ0.le hβ1 s hs

lemma value_bounds (P : Params) (hP : P.Standing) (π : Policy P) (hπ : IsAdmissible P π) (s : Book P)
    (hs : s ∈ validStates P) :
    0 ≤ value P π s ∧ value P π s ≤ Cmax P / (1 - P.β) := by
  have hβ0 : 0 < P.β := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hβ1 : P.β < 1 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold value
  exact dc_bounds (validStates P) (fun t => stepKernel P (π t))
    (fun t x _ x' => stepKernel_nonneg P hP _ x x')
    (fun t x hx => stepKernel_sum P hP _ x (fun a ha => hπ t x a ((mem_validStates P x).1 hx) ha))
    (fun t => stageCost P (π t)) (Cmax P)
    (fun t x hx => stageCost_bounds P hP _ x hx (fun a ha => hπ t x a ((mem_validStates P x).1 hx) ha))
    P.β hβ0.le hβ1 s hs

lemma sum_qValue (P : Params) (V : Book P → ℝ) (r : Book P → ℕ → Book P) (s : Book P) :
    ∑ a ∈ Finset.range (P.M + 1), P.pA a * qValue P V s a (r s a)
      = stageCost P r s + P.β * ∑ y ∈ validStates P, stepKernel P r s y * V y := by
  unfold qValue stageCost stepKernel
  rw [show ∑ y ∈ validStates P, (∑ a ∈ Finset.range (P.M + 1), P.pA a * trans P (s + r s a) y) * V y
      = ∑ a ∈ Finset.range (P.M + 1), P.pA a * ∑ y ∈ validStates P, trans P (s + r s a) y * V y by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro y _; ring]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

lemma fa_bellman (P : Params) (hP : P.Standing) (s : Book P) (hs : s ∈ validStates P) :
    value P (faPolicy P) s = ∑ a ∈ Finset.range (P.M + 1),
      P.pA a * qValue P (value P (faPolicy P)) s a (faAction P s a) := by
  rw [sum_qValue P _ (faAction P) s]
  exact value_shift P hP (faPolicy P) (faAction_isAdmissible P) s hs

noncomputable def Gv (P : Params) (V : Book P → ℝ) (T : Book P) : ℝ :=
  P.β * P.cF * ∑ s' ∈ validStates P, trans P T s' * failCount P T s'
    + P.β * ∑ s' ∈ validStates P, trans P T s' * V s'

lemma qValue_eq (P : Params) (V : Book P → ℝ) (s : Book P) (a : ℕ) (u : Book P) :
    qValue P V s a u = hcost P (s 0) + (s 0 : ℝ) * P.cF * P.cpost + P.cF * overflow a u + Gv P V (s + u) := by
  unfold qValue cost Gv; ring

lemma Gv_congr (P : Params) (V : Book P → ℝ) (T T' : Book P) (h : ∀ d : Fin P.D, T d.succ = T' d.succ) :
    Gv P V T = Gv P V T' := by
  have ht : ∀ s', trans P T s' = trans P T' s' := by intro s'; simp only [trans, h]
  have hf : ∀ s', failCount P T s' = failCount P T' s' := by
    intro s'; unfold failCount; rw [ht]; simp only [h]
  unfold Gv; simp only [ht, hf]

lemma sum_succ_single (P : Params) (T : Book P) (r : Fin P.D) :
    ∑ d : Fin P.D, ((T + Pi.single r.succ 1 : Book P) d.succ : ℝ) = ∑ d : Fin P.D, (T d.succ : ℝ) + 1 := by
  simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hb; simp [Pi.single_apply, Fin.succ_inj, hb]
  · simp

lemma Gv_add_single (P : Params) (hP : P.Standing) (V : Book P → ℝ) (T : Book P) (r : Fin P.D)
    (hT : ∀ d : Fin P.D, T d.succ ≤ P.K) (hr : T r.succ < P.K) :
    Gv P V (T + Pi.single r.succ 1) = Gv P V T + P.β * P.cF * P.pF
      + P.β * P.pFbar * ∑ s' ∈ validStates P, trans P T s' * (V (s' + Pi.single r.castSucc 1) - V s') := by
  have hT' : ∀ d : Fin P.D, (T + Pi.single r.succ 1 : Book P) d.succ ≤ P.K := by
    intro d
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs with h
    · rw [h]; omega
    · have := hT d; omega
  unfold Gv
  rw [expected_fail P hP _ hT', expected_fail P hP _ hT, sum_succ_single, sum_trans_add_single P T r hr V]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-! ### The core First-Available lemma -/

lemma fin_max_val {n : ℕ} (a b : Fin n) : (max a b).val = max a.val b.val := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Fin.le_iff_val_le_val.1 h)]
  · rw [max_eq_left h, max_eq_left (Fin.le_iff_val_le_val.1 h)]

lemma free_add_single (P : Params) (z : Book P) (j : Fin (P.D + 1)) (hj : j ≠ 0) (hz : z j < P.K)
    (d : Fin (P.D + 1)) :
    free P (z + Pi.single j 1) d + (if d = j then 1 else 0) = free P z d := by
  unfold free
  by_cases h0 : d = 0
  · subst h0; simp [Ne.symm hj]
  · simp only [if_neg h0, Pi.add_apply, Pi.single_apply]
    split_ifs with h
    · subst h; omega
    · omega

lemma free_add_single_zero (P : Params) (z : Book P) (d : Fin (P.D + 1)) :
    free P (z + Pi.single 0 1) d = free P z d := by
  unfold free
  by_cases h0 : d = 0
  · simp [h0]
  · simp [h0, Pi.single_apply]

lemma prefix_add_single (P : Params) (z : Book P) (j : Fin (P.D + 1)) (hj : j ≠ 0) (hz : z j < P.K)
    (d : Fin (P.D + 1)) :
    ∑ d' ∈ Finset.univ.filter (fun d' => d' < d), free P (z + Pi.single j 1) d' + (if j < d then 1 else 0)
      = ∑ d' ∈ Finset.univ.filter (fun d' => d' < d), free P z d' := by
  rw [← Finset.sum_congr rfl (fun d' _ => free_add_single P z j hj hz d'), Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp

lemma total_add_single (P : Params) (z : Book P) (j : Fin (P.D + 1)) (hj : j ≠ 0) (hz : z j < P.K) :
    ∑ d, free P (z + Pi.single j 1) d + 1 = ∑ d, free P z d := by
  rw [← Finset.sum_congr rfl (fun d _ => free_add_single P z j hj hz d), Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp

lemma prefix_mono (P : Params) (f : Fin (P.D + 1) → ℕ) {d d'' : Fin (P.D + 1)} (h : d < d'') :
    ∑ x ∈ Finset.univ.filter (fun x => x < d), f x + f d
      ≤ ∑ x ∈ Finset.univ.filter (fun x => x < d''), f x := by
  have hnot : d ∉ Finset.univ.filter (fun x => x < d) := by simp
  rw [add_comm, ← Finset.sum_insert hnot]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with rfl | hx
  · exact h
  · exact lt_trans hx h

lemma exists_cross (f : ℕ → ℕ) (a : ℕ) : ∀ n, a < ∑ i ∈ Finset.range n, f i →
    ∃ k < n, ∑ i ∈ Finset.range k, f i ≤ a ∧ a < ∑ i ∈ Finset.range k, f i + f k := by
  intro n
  induction n with
  | zero => intro h; simp at h
  | succ n ih =>
    intro h
    by_cases h' : a < ∑ i ∈ Finset.range n, f i
    · obtain ⟨k, hk, h1, h2⟩ := ih h'
      exact ⟨k, by omega, h1, h2⟩
    · rw [Finset.sum_range_succ] at h
      exact ⟨n, by omega, by omega, h⟩

lemma exists_dstar (P : Params) (z : Book P) (a : ℕ) (ha : a < ∑ d, free P z d) :
    ∃ q : Fin (P.D + 1), ∑ x ∈ Finset.univ.filter (fun x => x < q), free P z x ≤ a ∧
      a < ∑ x ∈ Finset.univ.filter (fun x => x < q), free P z x + free P z q := by
  rw [sum_univ_free_eq] at ha
  obtain ⟨k, hk, h1, h2⟩ := exists_cross (freeN P z) a _ ha
  refine ⟨⟨k, hk⟩, ?_, ?_⟩
  · rw [sum_filter_lt_eq]; exact h1
  · rw [sum_filter_lt_eq]
    have : free P z ⟨k, hk⟩ = freeN P z k := by simp [freeN, hk]
    rw [this]; exact h2

lemma core_feasible (P : Params) (z : Book P) (j : Fin (P.D + 1)) (hj : j ≠ 0) (hz : z j < P.K) (a : ℕ)
    (q : Fin (P.D + 1)) (hq1 : ∑ x ∈ Finset.univ.filter (fun x => x < q), free P z x ≤ a)
    (hq2 : a < ∑ x ∈ Finset.univ.filter (fun x => x < q), free P z x + free P z q) :
    (z + Pi.single j 1 : Book P) + faAction P (z + Pi.single j 1) a
      = (z + faAction P z a) + Pi.single (max j q) 1 := by
  funext d
  have hf := free_add_single P z j hj hz d
  have hp := prefix_add_single P z j hj hz d
  have key : (d.val < q.val ∧ ∑ x ∈ Finset.univ.filter (fun x => x < d), free P z x + free P z d ≤ a) ∨
      (d.val = q.val ∧ ∑ x ∈ Finset.univ.filter (fun x => x < d), free P z x ≤ a ∧
        a < ∑ x ∈ Finset.univ.filter (fun x => x < d), free P z x + free P z d) ∨
      (q.val < d.val ∧ a < ∑ x ∈ Finset.univ.filter (fun x => x < d), free P z x) := by
    rcases lt_trichotomy d q with hdq | rfl | hdq
    · left; exact ⟨hdq, le_trans (prefix_mono P (free P z) hdq) hq1⟩
    · right; left; exact ⟨rfl, hq1, hq2⟩
    · right; right; exact ⟨hdq, lt_of_lt_of_le hq2 (prefix_mono P (free P z) hdq)⟩
  have e1 : (if d = j then 1 else 0 : ℕ) = if d.val = j.val then 1 else 0 := by simp [Fin.ext_iff]
  have e2 : (if j < d then 1 else 0 : ℕ) = if j.val < d.val then 1 else 0 := by
    by_cases h : j < d
    · rw [if_pos h, if_pos (Fin.lt_def.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (Fin.lt_def.2 h'))]
  have e3 : (if d = max j q then 1 else 0 : ℕ) = if d.val = max j.val q.val then 1 else 0 := by
    simp [Fin.ext_iff, fin_max_val]
  simp only [Pi.add_apply, faAction, Pi.single_apply]
  rw [e1] at hf ⊢
  rw [e2] at hp
  rw [e3]
  split_ifs at hf hp ⊢ <;> omega

lemma overflow_fa (P : Params) (z : Book P) (a : ℕ) :
    overflow a (faAction P z a) = a - ∑ d, free P z d := by
  unfold overflow; rw [sum_faAction]; omega

lemma core_infeasible (P : Params) (z : Book P) (j : Fin (P.D + 1)) (hj : j ≠ 0) (hz : z j < P.K)
    (a : ℕ) (ha : ∑ d, free P z d ≤ a) :
    (z + Pi.single j 1 : Book P) + faAction P (z + Pi.single j 1) a = z + faAction P z a ∧
      (overflow a (faAction P (z + Pi.single j 1) a) : ℝ) = overflow a (faAction P z a) + 1 := by
  have htot := total_add_single P z j hj hz
  refine ⟨?_, ?_⟩
  · funext d
    have hf := free_add_single P z j hj hz d
    have h1 : faAction P z a d = free P z d := by
      unfold faAction; apply min_eq_left; have := prefix_add_free_le P z d; omega
    have h2 : faAction P (z + Pi.single j 1) a d = free P (z + Pi.single j 1) d := by
      unfold faAction; apply min_eq_left; have := prefix_add_free_le P (z + Pi.single j 1) d; omega
    simp only [Pi.add_apply, h1, h2]
    simp only [Pi.single_apply] at hf ⊢
    omega
  · have e1 := overflow_fa P z a
    have e2 := overflow_fa P (z + Pi.single j 1) a
    have : overflow a (faAction P (z + Pi.single j 1) a) = overflow a (faAction P z a) + 1 := by
      rw [e1, e2]; omega
    rw [this]; push_cast; ring

lemma post_fa_le (P : Params) (z : Book P) (hz : ∀ d, z d ≤ P.K) (a : ℕ) :
    ∀ d : Fin P.D, (z + faAction P z a) d.succ ≤ P.K := by
  intro d
  have h1 := faAction_le_free P z a d.succ
  have h2 := hz d.succ
  simp only [free, if_neg (Fin.succ_ne_zero d)] at h1
  simp only [Pi.add_apply]; omega

/-! ### One-step differences of the FA Q-value -/

lemma add_single_le (P : Params) (z : Book P) (hz0 : ∀ d, z d ≤ P.K) (j : Fin (P.D + 1)) (hz : z j < P.K) :
    ∀ d, (z + Pi.single j 1 : Book P) d ≤ P.K := by
  intro d
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs with h
  · subst h; omega
  · have := hz0 d; omega

lemma qdiff_zero (P : Params) (V : Book P → ℝ) (S : Book P) (a : ℕ) :
    qValue P V (S + Pi.single 0 1) a (faAction P (S + Pi.single 0 1) a) - qValue P V S a (faAction P S a)
      = hcost P (S 0 + 1) - hcost P (S 0) + P.cF * P.cpost := by
  have hfa : faAction P (S + Pi.single 0 1) a = faAction P S a := by
    funext d; simp only [faAction, free_add_single_zero]
  rw [hfa, qValue_eq, qValue_eq,
    Gv_congr P V (S + Pi.single 0 1 + faAction P S a) (S + faAction P S a) (fun d => by
      simp [Pi.single_apply, Fin.succ_ne_zero])]
  simp only [Pi.add_apply, Pi.single_eq_same]
  push_cast; ring

lemma qdiff_feas (P : Params) (hP : P.Standing) (V : Book P → ℝ) (S : Book P) (hS : ∀ d, S d ≤ P.K)
    (k : Fin (P.D + 1)) (hk0 : k ≠ 0) (hSk : S k < P.K) (a : ℕ) (ha : a < ∑ d, free P S d)
    (q : Fin (P.D + 1)) (hq1 : ∑ x ∈ Finset.univ.filter (fun x => x < q), free P S x ≤ a)
    (hq2 : a < ∑ x ∈ Finset.univ.filter (fun x => x < q), free P S x + free P S q)
    (r : Fin P.D) (hr : r.succ = max k q) :
    qValue P V (S + Pi.single k 1) a (faAction P (S + Pi.single k 1) a) - qValue P V S a (faAction P S a)
      = P.β * P.cF * P.pF + P.β * P.pFbar * ∑ s' ∈ validStates P,
          trans P (S + faAction P S a) s' * (V (s' + Pi.single r.castSucc 1) - V s') := by
  have hcore := core_feasible P S k hk0 hSk a q hq1 hq2
  rw [← hr] at hcore
  have hT := post_fa_le P S hS a
  have hT2 := post_fa_le P (S + Pi.single k 1) (add_single_le P S hS k hSk) a r
  rw [hcore] at hT2
  have hr' : (S + faAction P S a) r.succ < P.K := by
    simp only [Pi.add_apply, Pi.single_eq_same] at hT2 ⊢; omega
  have htot := total_add_single P S k hk0 hSk
  have ho1 : overflow a (faAction P S a) = 0 := by rw [overflow_fa]; omega
  have ho2 : overflow a (faAction P (S + Pi.single k 1) a) = 0 := by rw [overflow_fa]; omega
  have h0 : (S + Pi.single k 1 : Book P) 0 = S 0 := by
    simp [Pi.single_apply, Ne.symm hk0]
  rw [qValue_eq, qValue_eq, hcore, Gv_add_single P hP V _ r hT hr', ho1, ho2, h0]
  push_cast; ring

lemma qdiff_infeas (P : Params) (V : Book P → ℝ) (S : Book P)
    (k : Fin (P.D + 1)) (hk0 : k ≠ 0) (hSk : S k < P.K) (a : ℕ) (ha : ∑ d, free P S d ≤ a) :
    qValue P V (S + Pi.single k 1) a (faAction P (S + Pi.single k 1) a) - qValue P V S a (faAction P S a)
      = P.cF := by
  obtain ⟨h1, h2⟩ := core_infeasible P S k hk0 hSk a ha
  have h0 : (S + Pi.single k 1 : Book P) 0 = S 0 := by
    simp [Pi.single_apply, Ne.symm hk0]
  rw [qValue_eq, qValue_eq, h1, h2, h0]; ring

/-! ## Part I: structural invariants of the FA value function -/

lemma core_slot (P : Params) (S : Book P) (hS : ∀ d, S d ≤ P.K)
    (k : Fin (P.D + 1)) (hk0 : k ≠ 0) (hSk : S k < P.K) (a : ℕ)
    (q : Fin (P.D + 1)) (hq1 : ∑ x ∈ Finset.univ.filter (fun x => x < q), free P S x ≤ a)
    (hq2 : a < ∑ x ∈ Finset.univ.filter (fun x => x < q), free P S x + free P S q)
    (r : Fin P.D) (hr : r.succ = max k q) :
    (S + faAction P S a) r.succ < P.K := by
  have hcore := core_feasible P S k hk0 hSk a q hq1 hq2
  rw [← hr] at hcore
  have hT2 := post_fa_le P (S + Pi.single k 1) (add_single_le P S hS k hSk) a r
  rw [hcore] at hT2
  simp only [Pi.add_apply, Pi.single_eq_same] at hT2 ⊢; omega

def Inv1 (P : Params) (V : Book P → ℝ) (e : ℝ) : Prop :=
  ∀ R : Book P, R ∈ validStates P → ∀ c c' : Fin (P.D + 1), c < c' → R c < P.K → R c' < P.K →
    c' ≠ Fin.last P.D → V (R + Pi.single c 1) ≤ V (R + Pi.single c' 1) + e

def Inv3 (P : Params) (V : Book P → ℝ) (e : ℝ) : Prop :=
  ∀ S : Book P, S ∈ validStates P → ∀ k : Fin (P.D + 1), S k < P.K → k ≠ Fin.last P.D →
    P.cF * phi P k.val ≤ V (S + Pi.single k 1) - V S + e

lemma add_single_mem (P : Params) (S : Book P) (hS : S ∈ validStates P) (k : Fin (P.D + 1))
    (hk : S k < P.K) (hkl : k ≠ Fin.last P.D) : S + Pi.single k 1 ∈ validStates P := by
  rw [mem_validStates] at hS ⊢
  refine ⟨add_single_le P S hS.1 k hk, ?_⟩
  simp [Pi.single_apply, Ne.symm hkl, hS.2]

lemma sum_trans_ge (P : Params) (hP : P.Standing) (T : Book P) (hT : ∀ d : Fin P.D, T d.succ ≤ P.K)
    (g : Book P → ℝ) (m : ℝ) (hg : ∀ s' ∈ validStates P, trans P T s' ≠ 0 → m ≤ g s') :
    m ≤ ∑ s' ∈ validStates P, trans P T s' * g s' := by
  calc m = ∑ s' ∈ validStates P, trans P T s' * m := by rw [← Finset.sum_mul, mass_eq_one P T hT, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun s' hs' => by
        by_cases h : trans P T s' = 0
        · rw [h]; simp
        · exact mul_le_mul_of_nonneg_left (hg s' hs' h) (trans_nonneg P hP T s'))

lemma sum_trans_le (P : Params) (hP : P.Standing) (T : Book P) (hT : ∀ d : Fin P.D, T d.succ ≤ P.K)
    (g : Book P → ℝ) (m : ℝ) (hg : ∀ s' ∈ validStates P, trans P T s' ≠ 0 → g s' ≤ m) :
    ∑ s' ∈ validStates P, trans P T s' * g s' ≤ m := by
  calc ∑ s' ∈ validStates P, trans P T s' * g s' ≤ ∑ s' ∈ validStates P, trans P T s' * m :=
        Finset.sum_le_sum (fun s' hs' => by
          by_cases h : trans P T s' = 0
          · rw [h]; simp
          · exact mul_le_mul_of_nonneg_left (hg s' hs' h) (trans_nonneg P hP T s'))
    _ = m := by rw [← Finset.sum_mul, mass_eq_one P T hT, one_mul]

lemma avg_ge (P : Params) (hP : P.Standing) (f : ℕ → ℝ) (m : ℝ) (h : ∀ a, m ≤ f a) :
    m ≤ ∑ a ∈ Finset.range (P.M + 1), P.pA a * f a := by
  obtain ⟨hpA, hpA1⟩ := pA_facts P hP
  calc m = ∑ a ∈ Finset.range (P.M + 1), P.pA a * m := by rw [← Finset.sum_mul, hpA1, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (hpA a))

lemma avg_le (P : Params) (hP : P.Standing) (f : ℕ → ℝ) (m : ℝ) (h : ∀ a, f a ≤ m) :
    ∑ a ∈ Finset.range (P.M + 1), P.pA a * f a ≤ m := by
  obtain ⟨hpA, hpA1⟩ := pA_facts P hP
  calc ∑ a ∈ Finset.range (P.M + 1), P.pA a * f a ≤ ∑ a ∈ Finset.range (P.M + 1), P.pA a * m :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (hpA a))
    _ = m := by rw [← Finset.sum_mul, hpA1, one_mul]

lemma vdiff (P : Params) (V : Book P → ℝ)
    (hB : ∀ s ∈ validStates P, V s = ∑ a ∈ Finset.range (P.M + 1),
      P.pA a * qValue P V s a (faAction P s a))
    (S S2 : Book P) (hS : S ∈ validStates P) (hS2 : S2 ∈ validStates P) :
    V S2 - V S = ∑ a ∈ Finset.range (P.M + 1), P.pA a *
      (qValue P V S2 a (faAction P S2 a) - qValue P V S a (faAction P S a)) := by
  rw [hB S2 hS2, hB S hS, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

lemma two_le_D (P : Params) (k : Fin (P.D + 1)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last P.D) :
    2 ≤ P.D ∧ 1 ≤ k.val ∧ k.val + 1 ≤ P.D := by
  have h1 : k.val ≠ 0 := by intro h; apply hk0; ext; simp [h]
  have h2 : k.val ≠ P.D := by intro h; apply hkl; ext; simp [h]
  have := k.isLt; omega

lemma beta_pFbar (P : Params) (hP : P.Standing) : 0 ≤ P.β * P.pFbar ∧ P.β * P.pFbar < 1 := by
  have hβ0 : 0 < P.β := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hβ1 : P.β < 1 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h1 := pFbar_pos P hP
  have h2 := pFbar_lt_one P hP
  exact ⟨mul_nonneg hβ0.le h1.le, by nlinarith⟩

lemma max_ne_zero' (P : Params) (k q : Fin (P.D + 1)) (hk0 : k ≠ 0) : max k q ≠ 0 := by
  intro h
  have : k ≤ max k q := le_max_left k q
  rw [h] at this
  exact hk0 (Fin.le_zero_iff.1 this)

lemma diff_lower (P : Params) (hP : P.Standing) (V : Book P → ℝ) (e : ℝ) (he : 0 ≤ e) (hI3 : Inv3 P V e)
    (S : Book P) (hS : S ∈ validStates P) (k : Fin (P.D + 1)) (hk0 : k ≠ 0) (hSk : S k < P.K)
    (a : ℕ) :
    ∃ m : ℕ, k.val ≤ m ∧ P.cF * phi P m - P.β * P.pFbar * e ≤
      qValue P V (S + Pi.single k 1) a (faAction P (S + Pi.single k 1) a) - qValue P V S a (faAction P S a) := by
  have hSv := (mem_validStates P S).1 hS
  have hρ := (beta_pFbar P hP).1
  by_cases ha : a < ∑ d, free P S d
  · obtain ⟨q, hq1, hq2⟩ := exists_dstar P S a ha
    obtain ⟨r, hr⟩ := Fin.exists_succ_eq.2 (max_ne_zero' P k q hk0)
    have hdiff := qdiff_feas P hP V S hSv.1 k hk0 hSk a ha q hq1 hq2 r hr
    have hTr := core_slot P S hSv.1 k hk0 hSk a q hq1 hq2 r hr
    have hT := post_fa_le P S hSv.1 a
    have hsum : P.cF * phi P r.val - e ≤ ∑ s' ∈ validStates P,
        trans P (S + faAction P S a) s' * (V (s' + Pi.single r.castSucc 1) - V s') := by
      apply sum_trans_ge P hP _ hT
      intro s' hs' htr
      have h1 := trans_ne_zero_le P _ s' htr r
      have h2 := hI3 s' hs' r.castSucc (by omega) (Fin.castSucc_lt_last r).ne
      simp only [Fin.coe_castSucc] at h2
      linarith
    have hmk : k.val ≤ r.val + 1 := by
      have := congrArg Fin.val hr
      rw [Fin.val_succ, fin_max_val] at this
      omega
    refine ⟨r.val + 1, hmk, ?_⟩
    rw [hdiff, phi_succ]
    nlinarith [mul_le_mul_of_nonneg_left hsum hρ]
  · push Not at ha
    refine ⟨k.val, le_rfl, ?_⟩
    rw [qdiff_infeas P V S k hk0 hSk a ha]
    have := phi_le_one P hP k.val
    have hcF : 0 < P.cF := hP.2.2.2.1
    have : 0 ≤ P.β * P.pFbar * e := mul_nonneg hρ he
    nlinarith

lemma step3 (P : Params) (hP : P.Standing) (h13 : Condition13 P) (V : Book P → ℝ)
    (hB : ∀ s ∈ validStates P, V s = ∑ a ∈ Finset.range (P.M + 1),
      P.pA a * qValue P V s a (faAction P s a))
    (e : ℝ) (he : 0 ≤ e) (hI3 : Inv3 P V e) : Inv3 P V (P.β * P.pFbar * e) := by
  intro S hS k hSk hkl
  have hS2 := add_single_mem P S hS k hSk hkl
  have hbe : 0 ≤ P.β * P.pFbar * e := mul_nonneg (beta_pFbar P hP).1 he
  have hd := vdiff P V hB S _ hS hS2
  have hcF : 0 < P.cF := hP.2.2.2.1
  suffices h : ∀ a, P.cF * phi P k.val - P.β * P.pFbar * e ≤
      qValue P V (S + Pi.single k 1) a (faAction P (S + Pi.single k 1) a) - qValue P V S a (faAction P S a) by
    have := avg_ge P hP _ _ h
    linarith
  intro a
  by_cases hk0 : k = 0
  · subst hk0
    rw [qdiff_zero]
    have := (hcost_succ P hP (S 0)).1
    simp only [Fin.val_zero, phi_zero]
    linarith
  · obtain ⟨m, hm, hle⟩ := diff_lower P hP V e he hI3 S hS k hk0 hSk a
    obtain ⟨hD, -, -⟩ := two_le_D P k hk0 hkl
    have := mul_le_mul_of_nonneg_left (phi_mono P hP h13 hD hm) hcF.le
    linarith

lemma step1 (P : Params) (hP : P.Standing) (h13 : Condition13 P) (V : Book P → ℝ)
    (hB : ∀ s ∈ validStates P, V s = ∑ a ∈ Finset.range (P.M + 1),
      P.pA a * qValue P V s a (faAction P s a))
    (e : ℝ) (he : 0 ≤ e) (hI1 : Inv1 P V e) (hI3 : Inv3 P V e) : Inv1 P V (P.β * P.pFbar * e) := by
  intro R hR c c' hcc hRc hRc' hcl
  have hc'0 : c' ≠ 0 := by intro h; rw [h] at hcc; exact absurd hcc (Fin.not_lt_zero c)
  have hcl' : c ≠ Fin.last P.D := ne_of_lt (lt_of_lt_of_le hcc (Fin.le_last c'))
  have hRv := (mem_validStates P R).1 hR
  have h1 := add_single_mem P R hR c hRc hcl'
  have h2 := add_single_mem P R hR c' hRc' hcl
  have hd := vdiff P V hB (R + Pi.single c' 1) (R + Pi.single c 1) h2 h1
  have hρ := (beta_pFbar P hP).1
  have hbe : 0 ≤ P.β * P.pFbar * e := mul_nonneg hρ he
  have hcF : 0 < P.cF := hP.2.2.2.1
  suffices h : ∀ a, qValue P V (R + Pi.single c 1) a (faAction P (R + Pi.single c 1) a)
      - qValue P V (R + Pi.single c' 1) a (faAction P (R + Pi.single c' 1) a) ≤ P.β * P.pFbar * e by
    have := avg_le P hP _ _ h
    linarith
  intro a
  obtain ⟨hD, hc'1, hc'D⟩ := two_le_D P c' hc'0 hcl
  by_cases hc0 : c = 0
  · subst hc0
    have hz := qdiff_zero P V R a
    have hh := (hcost_succ P hP (R 0)).2
    obtain ⟨m, hm, hle⟩ := diff_lower P hP V e he hI3 R hR c' hc'0 hRc' a
    have hk := key_ineq P hP h13 0 c'.val (by omega) hc'D
    rw [pow_zero, mul_one, phi_zero] at hk
    have hmono := mul_le_mul_of_nonneg_left (phi_mono P hP h13 hD hm) hcF.le
    linarith
  · by_cases ha : a < ∑ d, free P R d
    · obtain ⟨q, hq1, hq2⟩ := exists_dstar P R a ha
      obtain ⟨r, hr⟩ := Fin.exists_succ_eq.2 (max_ne_zero' P c q hc0)
      obtain ⟨r', hr'⟩ := Fin.exists_succ_eq.2 (max_ne_zero' P c' q hc'0)
      have hA := qdiff_feas P hP V R hRv.1 c hc0 hRc a ha q hq1 hq2 r hr
      have hA' := qdiff_feas P hP V R hRv.1 c' hc'0 hRc' a ha q hq1 hq2 r' hr'
      have hTr := core_slot P R hRv.1 c hc0 hRc a q hq1 hq2 r hr
      have hTr' := core_slot P R hRv.1 c' hc'0 hRc' a q hq1 hq2 r' hr'
      have hT := post_fa_le P R hRv.1 a
      have hrr : r ≤ r' := by
        have e1 := congrArg Fin.val hr
        have e2 := congrArg Fin.val hr'
        rw [Fin.val_succ, fin_max_val] at e1 e2
        have : c.val < c'.val := hcc
        rw [Fin.le_iff_val_le_val]; omega
      have hsplit : ∑ s' ∈ validStates P, trans P (R + faAction P R a) s' * (V (s' + Pi.single r.castSucc 1) - V s')
          - ∑ s' ∈ validStates P, trans P (R + faAction P R a) s' * (V (s' + Pi.single r'.castSucc 1) - V s')
          = ∑ s' ∈ validStates P, trans P (R + faAction P R a) s' *
              ((V (s' + Pi.single r.castSucc 1) - V s') - (V (s' + Pi.single r'.castSucc 1) - V s')) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro s' _; ring
      have hsum : ∑ s' ∈ validStates P, trans P (R + faAction P R a) s' *
              ((V (s' + Pi.single r.castSucc 1) - V s') - (V (s' + Pi.single r'.castSucc 1) - V s')) ≤ e := by
        apply sum_trans_le P hP _ hT
        intro s' hs' htr
        rcases eq_or_lt_of_le hrr with h | h
        · subst h; linarith
        · have g1 := trans_ne_zero_le P _ s' htr r
          have g2 := trans_ne_zero_le P _ s' htr r'
          have := hI1 s' hs' r.castSucc r'.castSucc (Fin.castSucc_lt_castSucc_iff.2 h) (by omega) (by omega)
            (Fin.castSucc_lt_last r').ne
          linarith
      rw [← hsplit] at hsum
      have := mul_le_mul_of_nonneg_left hsum hρ
      have e3 : qValue P V (R + Pi.single c 1) a (faAction P (R + Pi.single c 1) a)
          - qValue P V (R + Pi.single c' 1) a (faAction P (R + Pi.single c' 1) a)
          = (qValue P V (R + Pi.single c 1) a (faAction P (R + Pi.single c 1) a) - qValue P V R a (faAction P R a))
          - (qValue P V (R + Pi.single c' 1) a (faAction P (R + Pi.single c' 1) a) - qValue P V R a (faAction P R a)) := by
        ring
      rw [e3, hA, hA']
      nlinarith
    · push Not at ha
      have g1 := qdiff_infeas P V R c hc0 hRc a ha
      have g2 := qdiff_infeas P V R c' hc'0 hRc' a ha
      linarith

lemma inv_base (P : Params) (hP : P.Standing) (V : Book P → ℝ) (B : ℝ)
    (hV : ∀ s ∈ validStates P, 0 ≤ V s ∧ V s ≤ B) : Inv1 P V (B + P.cF) ∧ Inv3 P V (B + P.cF) := by
  have hcF : 0 < P.cF := hP.2.2.2.1
  constructor
  · intro R hR c c' hcc hRc hRc' hcl
    have h1 := hV _ (add_single_mem P R hR c hRc (ne_of_lt (lt_of_lt_of_le hcc (Fin.le_last c'))))
    have h2 := hV _ (add_single_mem P R hR c' hRc' hcl)
    linarith [h1.2, h2.1]
  · intro S hS k hSk hkl
    have h1 := hV _ (add_single_mem P S hS k hSk hkl)
    have h2 := hV S hS
    have := phi_le_one P hP k.val
    nlinarith [h1.1, h2.2]

lemma inv1_exact (P : Params) (hP : P.Standing) (h13 : Condition13 P) (V : Book P → ℝ)
    (hB : ∀ s ∈ validStates P, V s = ∑ a ∈ Finset.range (P.M + 1),
      P.pA a * qValue P V s a (faAction P s a))
    (B : ℝ) (hV : ∀ s ∈ validStates P, 0 ≤ V s ∧ V s ≤ B) : Inv1 P V 0 := by
  obtain ⟨hρ0, hρ1⟩ := beta_pFbar P hP
  have hcF : 0 < P.cF := hP.2.2.2.1
  have he0 : 0 ≤ B + P.cF := by
    have := hV 0 (zero_mem_validStates P); linarith [this.1, this.2]
  have hall : ∀ n : ℕ, Inv1 P V ((P.β * P.pFbar) ^ n * (B + P.cF)) ∧
      Inv3 P V ((P.β * P.pFbar) ^ n * (B + P.cF)) := by
    intro n
    induction n with
    | zero => simpa using inv_base P hP V B hV
    | succ n ih =>
      have he : 0 ≤ (P.β * P.pFbar) ^ n * (B + P.cF) := mul_nonneg (pow_nonneg hρ0 n) he0
      have e : (P.β * P.pFbar) ^ (n + 1) * (B + P.cF)
          = P.β * P.pFbar * ((P.β * P.pFbar) ^ n * (B + P.cF)) := by ring
      rw [e]
      exact ⟨step1 P hP h13 V hB _ he ih.1 ih.2, step3 P hP h13 V hB _ he ih.2⟩
  intro R hR c c' hcc hRc hRc' hcl
  have hlim : Filter.Tendsto (fun n : ℕ => (P.β * P.pFbar) ^ n * (B + P.cF)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (B + P.cF)
  have : V (R + Pi.single c 1) - V (R + Pi.single c' 1) ≤ 0 :=
    ge_of_tendsto' hlim (fun n => by have := (hall n).1 R hR c c' hcc hRc hRc' hcl; linarith)
  linarith

/-! ## Part J: greedy optimality of FA against V, and the comparison argument -/

lemma Gv_exchange (P : Params) (hP : P.Standing) (V : Book P → ℝ) (hI : Inv1 P V 0) (W : Book P)
    (hW : ∀ d : Fin P.D, W d.succ ≤ P.K) (x y : Fin (P.D + 1)) (hx0 : x ≠ 0) (hxy : x < y)
    (hWx : W x < P.K) (hWy : W y < P.K) :
    Gv P V (W + Pi.single x 1) ≤ Gv P V (W + Pi.single y 1) := by
  have hy0 : y ≠ 0 := by intro h; rw [h] at hxy; exact Fin.not_lt_zero x hxy
  obtain ⟨r, rfl⟩ := Fin.exists_succ_eq.2 hx0
  obtain ⟨r', rfl⟩ := Fin.exists_succ_eq.2 hy0
  rw [Gv_add_single P hP V W r hW hWx, Gv_add_single P hP V W r' hW hWy]
  have hrr : r.castSucc < r'.castSucc := Fin.castSucc_lt_castSucc_iff.2 (Fin.succ_lt_succ_iff.1 hxy)
  have hsum : ∑ s' ∈ validStates P, trans P W s' * (V (s' + Pi.single r.castSucc 1) - V s')
      ≤ ∑ s' ∈ validStates P, trans P W s' * (V (s' + Pi.single r'.castSucc 1) - V s') := by
    apply Finset.sum_le_sum
    intro s' hs'
    by_cases htr : trans P W s' = 0
    · rw [htr]; simp
    · have h1 := trans_ne_zero_le P W s' htr r
      have h2 := trans_ne_zero_le P W s' htr r'
      have := hI s' hs' r.castSucc r'.castSucc hrr (by omega) (by omega) (Fin.castSucc_lt_last r').ne
      exact mul_le_mul_of_nonneg_left (by linarith) (trans_nonneg P hP W s')
  have hρ := (beta_pFbar P hP).1
  nlinarith [mul_le_mul_of_nonneg_left hsum hρ]

lemma sum_filter_lt_eq' (P : Params) (g : Fin (P.D + 1) → ℕ) (k : Fin (P.D + 1)) :
    ∑ d ∈ Finset.univ.filter (fun d' => d' < k), g d
      = ∑ i ∈ Finset.range k.val, (if h : i < P.D + 1 then g ⟨i, h⟩ else 0) := by
  rw [Finset.sum_filter]
  have h1 : ∀ d : Fin (P.D + 1), (if d < k then g d else 0)
      = (fun i : ℕ => if i < k.val then (if h : i < P.D + 1 then g ⟨i, h⟩ else 0) else 0) d.val := by
    intro d
    simp only [dif_pos d.isLt, Fin.lt_def]
  rw [Finset.sum_congr rfl (fun d _ => h1 d), Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if i < k.val then (if h : i < P.D + 1 then g ⟨i, h⟩ else 0) else 0) (P.D + 1)]
  rw [← Finset.sum_filter]
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_range]
  have := k.isLt; omega

lemma prefix_fa (P : Params) (s : Book P) (a : ℕ) (k : Fin (P.D + 1)) :
    ∑ d ∈ Finset.univ.filter (fun d' => d' < k), faAction P s a d
      = min a (∑ d ∈ Finset.univ.filter (fun d' => d' < k), free P s d) := by
  rw [sum_filter_lt_eq', sum_filter_lt_eq, ← fill_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < P.D + 1 := by have := k.isLt; simp only [Finset.mem_range] at hi; omega
  rw [dif_pos hi']
  simp only [faAction, sum_filter_lt_eq, freeN, dif_pos hi']

set_option maxHeartbeats 1000000 in
lemma greedy (P : Params) (hP : P.Standing) (V : Book P → ℝ) (hI : Inv1 P V 0) (s : Book P)
    (hs : s ∈ validStates P) (a : ℕ) (ha : a ≤ P.M) (u : Book P) (hu : Admissible P s a u) :
    qValue P V s a (faAction P s a) ≤ qValue P V s a u := by
  have hsv := (mem_validStates P s).1 hs
  have hfa : Admissible P s a (faAction P s a) := faAction_isAdmissible P 0 s a hsv ha
  by_cases hf : Feasible P s a
  · suffices H : ∀ n, ∀ u : Book P, ∑ d, d.val * u d = n → u 0 = 0 →
        (∀ d, d ≠ 0 → u d + s d ≤ P.K) → ∑ d, u d = a →
        Gv P V (s + faAction P s a) ≤ Gv P V (s + u) by
      have h := H _ u rfl hu.1 hu.2.1 (hu.2.2.1 hf)
      rw [qValue_eq, qValue_eq]
      have ho : overflow a u = 0 := by unfold overflow; rw [hu.2.2.1 hf]; simp
      have ho' : overflow a (faAction P s a) = 0 := by unfold overflow; rw [hfa.2.2.1 hf]; simp
      rw [ho, ho']; linarith
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro u hn hu0 huK husum
    by_cases heq : u = faAction P s a
    · rw [heq]
    · have hne : ∃ d, u d ≠ faAction P s a d := by
        by_contra h; push Not at h; exact heq (funext h)
      have hSne : (Finset.univ.filter (fun d => u d ≠ faAction P s a d)).Nonempty := by
        obtain ⟨d, hd⟩ := hne; exact ⟨d, by simp [hd]⟩
      obtain ⟨d0, hd0mem, hd0min⟩ : ∃ d0 ∈ Finset.univ.filter (fun d => u d ≠ faAction P s a d),
          ∀ d ∈ Finset.univ.filter (fun d => u d ≠ faAction P s a d), d0 ≤ d :=
        ⟨_, Finset.min'_mem _ hSne, fun d hd => Finset.min'_le _ d hd⟩
      have hd0 : u d0 ≠ faAction P s a d0 := by simpa using hd0mem
      have hbefore : ∀ d, d < d0 → u d = faAction P s a d := by
        intro d hd; by_contra h
        exact absurd hd (not_lt.2 (hd0min d (by simp [h])))
      have hd00 : d0 ≠ 0 := by intro h; apply hd0; rw [h, hu0, hfa.1]
      have hpre : ∑ d ∈ Finset.univ.filter (fun d' => d' < d0), u d
          = ∑ d ∈ Finset.univ.filter (fun d' => d' < d0), faAction P s a d :=
        Finset.sum_congr rfl (fun d hd => hbefore d (by simpa using hd))
      have hpfa := prefix_fa P s a d0
      have hle : ∑ d ∈ Finset.univ.filter (fun d' => d' < d0), u d + u d0 ≤ a := by
        rw [← husum]
        have hnot : d0 ∉ Finset.univ.filter (fun d' => d' < d0) := by simp
        rw [add_comm, ← Finset.sum_insert hnot]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have hfree : u d0 + s d0 ≤ P.K := huK d0 hd00
      have hfd0 : free P s d0 = P.K - s d0 := by simp [free, hd00]
      have hlt : u d0 < faAction P s a d0 := by
        have hFA : faAction P s a d0 = min (free P s d0)
            (a - ∑ d ∈ Finset.univ.filter (fun d' => d' < d0), free P s d) := rfl
        have : u d0 ≤ faAction P s a d0 := by omega
        exact lt_of_le_of_ne this hd0
      have hex : ∃ d', d0 < d' ∧ faAction P s a d' < u d' := by
        by_contra h
        push Not at h
        have hall : ∀ d, u d ≤ faAction P s a d := by
          intro d
          rcases lt_trichotomy d d0 with h1 | h1 | h1
          · exact (hbefore d h1).le
          · rw [h1]; exact hlt.le
          · exact h d h1
        have := Finset.sum_lt_sum (fun d (_ : d ∈ Finset.univ) => hall d) ⟨d0, Finset.mem_univ _, hlt⟩
        rw [husum, hfa.2.2.1 hf] at this
        exact lt_irrefl _ this
      obtain ⟨d', hd'1, hd'2⟩ := hex
      have hd'0 : d' ≠ 0 := by intro h; rw [h] at hd'1; exact Fin.not_lt_zero d0 hd'1
      have hd0d' : d0 ≠ d' := ne_of_lt hd'1
      obtain ⟨u', hu'⟩ : ∃ u' : Book P, ∀ d,
          u' d = u d + (if d = d0 then 1 else 0) - (if d = d' then 1 else 0) := ⟨_, fun d => rfl⟩
      have hrel : ∀ d, u' d + (if d = d' then 1 else 0) = u d + (if d = d0 then 1 else 0) := by
        intro d
        rw [hu' d]
        by_cases h1 : d = d'
        · rw [h1]
          simp only [eq_self_iff_true, if_true, if_neg (Ne.symm hd0d')]
          omega
        · simp only [if_neg h1]; omega
      have hsum1 : ∑ d, u' d = ∑ d, u d := by
        have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin (P.D + 1)))) rfl (fun d _ => hrel d)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at h
        simp only [Finset.mem_univ, if_true] at h
        omega
      have hsum2 : ∑ d, d.val * u' d + d'.val = ∑ d, d.val * u d + d0.val := by
        have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin (P.D + 1)))) rfl
          (fun d _ => congrArg (fun x => d.val * x) (hrel d))
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true] at h
        exact h
      have hu'0 : u' 0 = 0 := by
        have := hrel 0
        rw [if_neg (Ne.symm hd'0), if_neg (Ne.symm hd00)] at this
        omega
      have hu'K : ∀ d, d ≠ 0 → u' d + s d ≤ P.K := by
        intro d hd
        have h1 := hrel d
        have h2 := huK d hd
        by_cases e1 : d = d0
        · rw [e1] at h1 ⊢
          simp only [eq_self_iff_true, if_true, if_neg hd0d'] at h1
          have h3 := faAction_le_free P s a d0
          omega
        · by_cases e2 : d = d'
          · rw [e2] at h1 h2 ⊢
            simp only [eq_self_iff_true, if_true, if_neg (Ne.symm hd0d')] at h1
            omega
          · rw [if_neg e1, if_neg e2] at h1; omega
      have hlt' : ∑ d, d.val * u' d < n := by
        have : d0.val < d'.val := hd'1
        omega
      have ih' := ih _ hlt' u' rfl hu'0 hu'K (by rw [hsum1, husum])
      obtain ⟨W, hW⟩ : ∃ W : Book P, ∀ d, W d = s d + u d - (if d = d' then 1 else 0) :=
        ⟨_, fun d => rfl⟩
      have hW1 : W + Pi.single d' 1 = s + u := by
        funext d
        simp only [Pi.add_apply, Pi.single_apply, hW]
        by_cases e1 : d = d'
        · rw [e1] at ⊢
          simp only [eq_self_iff_true, if_true]
          omega
        · simp only [if_neg e1]; omega
      have hW2 : W + Pi.single d0 1 = s + u' := by
        funext d
        have h1 := hrel d
        simp only [Pi.add_apply, Pi.single_apply, hW]
        by_cases e1 : d = d'
        · rw [e1] at h1 ⊢
          simp only [eq_self_iff_true, if_true, if_neg (Ne.symm hd0d')] at h1 ⊢
          omega
        · simp only [if_neg e1] at h1 ⊢
          omega
      have hWle : ∀ d : Fin P.D, W d.succ ≤ P.K := by
        intro d; have := huK d.succ (Fin.succ_ne_zero d); rw [hW]; omega
      have hWd0 : W d0 < P.K := by
        rw [hW, if_neg hd0d']
        have h3 := faAction_le_free P s a d0
        omega
      have hWd' : W d' < P.K := by
        rw [hW, if_pos rfl]; have := huK d' hd'0; omega
      have hx := Gv_exchange P hP V hI W hWle d0 d' hd00 hd'1 hWd0 hWd'
      rw [hW1, hW2] at hx
      linarith
  · have : u = faAction P s a := by
      funext d
      by_cases hd : d = 0
      · rw [hd, hu.1, hfa.1]
      · have h1 := hu.2.2.2 hf d hd
        have h2 := hfa.2.2.2 hf d hd
        omega
    rw [this]

lemma fa_compare (P : Params) (hP : P.Standing) (h13 : Condition13 P) :
    ∀ n : ℕ, ∀ π : Policy P, IsAdmissible P π → ∀ s ∈ validStates P,
      value P (faPolicy P) s - value P π s ≤ P.β ^ n * (Cmax P / (1 - P.β)) := by
  have hB : ∀ s ∈ validStates P, value P (faPolicy P) s = ∑ a ∈ Finset.range (P.M + 1),
      P.pA a * qValue P (value P (faPolicy P)) s a (faAction P s a) := fun s hs => fa_bellman P hP s hs
  have hVb : ∀ s ∈ validStates P, 0 ≤ value P (faPolicy P) s ∧
      value P (faPolicy P) s ≤ Cmax P / (1 - P.β) :=
    fun s hs => value_bounds P hP _ (faAction_isAdmissible P) s hs
  have hI := inv1_exact P hP h13 _ hB _ hVb
  obtain ⟨hpA, hpA1⟩ := pA_facts P hP
  have hβ0 : 0 < P.β := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro n
  induction n with
  | zero =>
    intro π hπ s hs
    have h1 := hVb s hs
    have h2 := (value_bounds P hP π hπ s hs).1
    simp only [pow_zero, one_mul]; linarith
  | succ n ih =>
    intro π hπ s hs
    have hπ' : IsAdmissible P (fun t => π (t + 1)) := fun t => hπ (t + 1)
    have hshift := value_shift P hP π hπ s hs
    have hsv := (mem_validStates P s).1 hs
    have hgreedy : value P (faPolicy P) s ≤ stageCost P (π 0) s
        + P.β * ∑ y ∈ validStates P, stepKernel P (π 0) s y * value P (faPolicy P) y := by
      rw [← sum_qValue P (value P (faPolicy P)) (π 0) s]
      calc value P (faPolicy P) s = ∑ a ∈ Finset.range (P.M + 1),
            P.pA a * qValue P (value P (faPolicy P)) s a (faAction P s a) := hB s hs
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro a ha
          have ha' : a ≤ P.M := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          exact mul_le_mul_of_nonneg_left (greedy P hP _ hI s hs a ha' _ (hπ 0 s a hsv ha')) (hpA a)
    have hstep : ∑ y ∈ validStates P, stepKernel P (π 0) s y * value P (faPolicy P) y
        - ∑ y ∈ validStates P, stepKernel P (π 0) s y * value P (fun t => π (t + 1)) y
        ≤ P.β ^ n * (Cmax P / (1 - P.β)) := by
      rw [← Finset.sum_sub_distrib]
      calc _ ≤ ∑ y ∈ validStates P, stepKernel P (π 0) s y * (P.β ^ n * (Cmax P / (1 - P.β))) := by
            apply Finset.sum_le_sum; intro y hy
            rw [← mul_sub]
            exact mul_le_mul_of_nonneg_left (ih _ hπ' y hy) (stepKernel_nonneg P hP _ s y)
        _ = _ := by rw [← Finset.sum_mul, stepKernel_sum P hP _ s (fun a ha => hπ 0 s a hsv ha), one_mul]
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hstep hβ0.le]

end SurgeAppt.FirstAvail.Pf

open SurgeAppt.FirstAvail.Pf

open SurgeAppt.FirstAvail in
theorem solution (P : Params) (hP : P.Standing) (h13 : Condition13 P) :
    IsAdmissible P (faPolicy P) ∧
      ∀ π : Policy P, IsAdmissible P π →
        ∀ s : Book P, Valid P s → value P (faPolicy P) s ≤ value P π s := by
  refine ⟨faAction_isAdmissible P, ?_⟩
  intro π hπ s hs
  have hs' : s ∈ validStates P := (mem_validStates P s).2 hs
  have hβ0 : 0 ≤ P.β := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1.le
  have hβ1 : P.β < 1 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlim : Filter.Tendsto (fun n : ℕ => P.β ^ n * (Cmax P / (1 - P.β))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (Cmax P / (1 - P.β))
  have : value P (faPolicy P) s - value P π s ≤ 0 :=
    ge_of_tendsto' hlim (fun n => fa_compare P hP h13 n π hπ s hs')
  linarith
