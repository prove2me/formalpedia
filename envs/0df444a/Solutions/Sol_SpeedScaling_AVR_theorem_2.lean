-- Prove2me | solution 1 for SpeedScaling.AVR.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T15:23:11.725156+00:00
-- url     : https://prove2.me/submissions/7a7536e7-674a-40f2-b7e2-5ed6224ff4c7

import Mathlib
import Definitions.Def_SpeedScaling_AVR_Model

set_option autoImplicit false



open Finset

namespace AVRMax

noncomputable def S (w α : ℕ → ℝ) (i j : ℕ) : ℝ := ∑ k ∈ Ico i j, w k * α k
noncomputable def W (w : ℕ → ℝ) (i j : ℕ) : ℝ := ∑ k ∈ Ico i j, w k
noncomputable def avg (w α : ℕ → ℝ) (i j : ℕ) : ℝ := S w α i j / W w i j

/-- right one-sided maximal average inside `[i, b)`; `0` when empty -/
noncomputable def G (w α : ℕ → ℝ) (b i : ℕ) : ℝ :=
  if h : i < b then (Ico i b).sup' (Finset.nonempty_Ico.mpr h) (fun j => avg w α i (j + 1)) else 0

variable {w α : ℕ → ℝ}

lemma S_split (w α : ℕ → ℝ) {i j k : ℕ} (h1 : i ≤ j) (h2 : j ≤ k) :
    S w α i k = S w α i j + S w α j k := by
  unfold S; rw [Finset.sum_Ico_consecutive _ h1 h2]

lemma W_split (w : ℕ → ℝ) {i j k : ℕ} (h1 : i ≤ j) (h2 : j ≤ k) :
    W w i k = W w i j + W w j k := by
  unfold W; rw [Finset.sum_Ico_consecutive _ h1 h2]

lemma W_pos (hw : ∀ k, 0 < w k) {i j : ℕ} (h : i < j) : 0 < W w i j := by
  unfold W; exact Finset.sum_pos (fun k _ => hw k) ⟨i, by simp [h]⟩

lemma W_nonneg (hw : ∀ k, 0 < w k) (i j : ℕ) : 0 ≤ W w i j := by
  unfold W; exact Finset.sum_nonneg (fun k _ => (hw k).le)

lemma W_zero_S (hw : ∀ k, 0 < w k) {i j : ℕ} (h : W w i j = 0) : S w α i j = 0 := by
  rcases lt_or_ge i j with hij | hij
  · exact absurd h (W_pos hw hij).ne'
  · unfold S; simp [Finset.Ico_eq_empty_of_le hij]

lemma le_G {b i j : ℕ} (hij : i ≤ j) (hjb : j < b) : avg w α i (j + 1) ≤ G w α b i := by
  unfold G; rw [dif_pos (lt_of_le_of_lt hij hjb)]
  exact Finset.le_sup' (fun j => avg w α i (j + 1)) (Finset.mem_Ico.mpr ⟨hij, hjb⟩)

lemma G_attained {b i : ℕ} (h : i < b) :
    ∃ j, i ≤ j ∧ j < b ∧ G w α b i = avg w α i (j + 1) := by
  unfold G; rw [dif_pos h]
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_Ico.mpr h) (fun j => avg w α i (j + 1))
  simp only [Finset.mem_Ico] at hj
  exact ⟨j, hj.1, hj.2, he⟩

lemma G_le_of {b i : ℕ} (h : i < b) {M : ℝ}
    (hM : ∀ j, i ≤ j → j < b → avg w α i (j + 1) ≤ M) : G w α b i ≤ M := by
  unfold G; rw [dif_pos h]
  exact Finset.sup'_le _ _ (fun j hj => by simp only [Finset.mem_Ico] at hj; exact hM j hj.1 hj.2)

lemma G_restrict (hw : ∀ k, 0 < w k) {a b c : ℕ} (hac : a < c) (hcb : c ≤ b)
    (hmax : ∀ j, a ≤ j → j < b → avg w α a (j + 1) ≤ avg w α a c) {i : ℕ}
    (hai : a < i) (hic : i < c) :
    G w α b i = G w α c i := by
  have hWac := W_pos hw hac
  have hWai := W_pos hw hai
  have hWic := W_pos hw hic
  have hSac : S w α a c = avg w α a c * W w a c := by
    unfold avg; rw [div_mul_cancel₀ _ hWac.ne']
  -- μ ≤ avg i c, in multiplied form
  have hleft : avg w α a c * W w i c ≤ S w α i c := by
    have h1 := hmax (i - 1) (by omega) (by omega)
    rw [show i - 1 + 1 = i by omega] at h1
    have h1' : S w α a i ≤ avg w α a c * W w a i := by rw [← div_le_iff₀ hWai]; exact h1
    have e1 := S_split w α (le_of_lt hai) (le_of_lt hic)
    have e2 := W_split w (le_of_lt hai) (le_of_lt hic)
    have e2' : avg w α a c * W w a c = avg w α a c * W w a i + avg w α a c * W w i c := by
      rw [e2]; ring
    linarith
  have hic_le : avg w α i c ≤ G w α c i := by
    have := le_G (w := w) (α := α) (b := c) (i := i) (j := c - 1) (by omega) (by omega)
    rwa [show c - 1 + 1 = c by omega] at this
  apply le_antisymm
  · apply G_le_of (lt_of_lt_of_le hic hcb)
    intro j hij hjb
    rcases lt_or_ge j c with hjc | hjc
    · exact le_G hij hjc
    · refine le_trans ?_ hic_le
      have hWcj := W_pos hw (show c < j + 1 by omega)
      have h1 := hmax j (by omega) hjb
      have h1' : S w α a (j + 1) ≤ avg w α a c * W w a (j + 1) := by
        rw [← div_le_iff₀ (W_pos hw (show a < j + 1 by omega))]; exact h1
      have e1 := S_split w α (le_of_lt hac) (show c ≤ j + 1 by omega)
      have e2 := W_split w (le_of_lt hac) (show c ≤ j + 1 by omega)
      have e2' : avg w α a c * W w a (j + 1) = avg w α a c * W w a c
          + avg w α a c * W w c (j + 1) := by rw [e2]; ring
      have hright : S w α c (j + 1) ≤ avg w α a c * W w c (j + 1) := by linarith
      have e3 := S_split w α (le_of_lt hic) (show c ≤ j + 1 by omega)
      have e4 := W_split w (le_of_lt hic) (show c ≤ j + 1 by omega)
      unfold avg
      rw [e3, e4, div_le_div_iff₀ (by linarith) hWic]
      nlinarith [mul_le_mul_of_nonneg_right hright hWic.le,
        mul_le_mul_of_nonneg_right hleft hWcj.le]
  · apply G_le_of hic
    intro j hij hjc
    exact le_G hij (lt_of_lt_of_le hjc hcb)

lemma block_alg {wa al S' W' μ : ℝ} (hwa : 0 < wa) (hW' : 0 ≤ W') (hS' : W' = 0 → S' = 0)
    (hμ : wa * al + S' = μ * (wa + W')) :
    wa * (μ ^ 2 - 2 * al * μ) - S' ^ 2 / W' + μ * (wa * al + S') ≤ 0 := by
  rcases hW'.eq_or_lt with h | h
  · have h0 := hS' h.symm
    rw [← h, h0] at hμ ⊢
    have hal : al = μ := by
      have : (al - μ) * wa = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · linarith
      · exact absurd h1 hwa.ne'
    subst hal
    simp only [div_zero]
    nlinarith
  · have h3 : S' ^ 2 / W' = (μ * W' - S') ^ 2 / W' + 2 * μ * S' - μ ^ 2 * W' := by
      field_simp; ring
    have h4 : 0 ≤ (μ * W' - S') ^ 2 / W' := div_nonneg (sq_nonneg _) h.le
    rw [h3]
    have e : wa * (μ ^ 2 - 2 * al * μ) - ((μ * W' - S') ^ 2 / W' + 2 * μ * S' - μ ^ 2 * W')
        + μ * (wa * al + S') = -((μ * W' - S') ^ 2 / W') := by
      linear_combination (-μ) * hμ
    linarith

lemma comb_alg {S1 S2 W1 W2 : ℝ} (hW1 : 0 < W1) (hW2 : 0 ≤ W2) (hS2 : W2 = 0 → S2 = 0) :
    (S1 + S2) ^ 2 / (W1 + W2) ≤ S1 ^ 2 / W1 + S2 ^ 2 / W2 := by
  rcases hW2.eq_or_lt with h | h
  · rw [← h, hS2 h.symm]; simp
  · rw [div_add_div _ _ hW1.ne' h.ne', div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith [sq_nonneg (S1 * W2 - S2 * W1)]

theorem Q (hw : ∀ k, 0 < w k) : ∀ d a b, b = a + d →
    ∑ i ∈ Ico a b, w i * (G w α b i ^ 2 - 2 * α i * G w α b i) + S w α a b ^ 2 / W w a b ≤ 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro a b hb
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp only [add_zero] at hb; subst hb; simp [S, W]
  · have hab : a < b := by omega
    obtain ⟨y, hay, hyb, hGy⟩ := G_attained (w := w) (α := α) hab
    have hac : a < y + 1 := by omega
    have hcb : y + 1 ≤ b := by omega
    have hmax : ∀ j, a ≤ j → j < b → avg w α a (j + 1) ≤ avg w α a (y + 1) :=
      fun j h1 h2 => hGy ▸ le_G h1 h2
    have IH1 := ih (y + 1 - (a + 1)) (by omega) (a + 1) (y + 1) (by omega)
    have IH2 := ih (b - (y + 1)) (by omega) (y + 1) b (by omega)
    rw [← Finset.sum_Ico_consecutive _ hac.le hcb, Finset.sum_eq_sum_Ico_succ_bot hac]
    have hmid : ∑ i ∈ Ico (a + 1) (y + 1), w i * (G w α b i ^ 2 - 2 * α i * G w α b i)
        = ∑ i ∈ Ico (a + 1) (y + 1), w i * (G w α (y + 1) i ^ 2 - 2 * α i * G w α (y + 1) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_Ico] at hi
      rw [G_restrict hw hac hcb hmax (by omega) (by omega)]
    rw [hmid]
    -- algebra
    have eS1 : S w α a (y + 1) = w a * α a + S w α (a + 1) (y + 1) := by
      rw [S_split w α (show a ≤ a + 1 by omega) (show a + 1 ≤ y + 1 by omega)]
      simp [S]
    have eW1 : W w a (y + 1) = w a + W w (a + 1) (y + 1) := by
      rw [W_split w (show a ≤ a + 1 by omega) (show a + 1 ≤ y + 1 by omega)]
      simp [W]
    have eS := S_split w α hac.le hcb
    have eW := W_split w hac.le hcb
    have hWB := W_pos hw hac
    set μ := G w α b a with hμdef
    have hμ : w a * α a + S w α (a + 1) (y + 1) = μ * (w a + W w (a + 1) (y + 1)) := by
      rw [← eS1, ← eW1, hGy]; unfold avg; rw [div_mul_cancel₀ _ hWB.ne']
    have hB := block_alg (hw a) (W_nonneg hw (a + 1) (y + 1)) (W_zero_S hw) hμ
    have hC := comb_alg (S1 := S w α a (y + 1)) (S2 := S w α (y + 1) b) hWB
      (W_nonneg hw (y + 1) b) (W_zero_S hw)
    have hSq : S w α a (y + 1) ^ 2 / W w a (y + 1) = μ * (w a * α a + S w α (a + 1) (y + 1)) := by
      rw [← eS1, hGy]; unfold avg; ring
    rw [eS, eW]
    linarith

theorem one_sided (hw : ∀ k, 0 < w k) (n : ℕ) :
    ∑ i ∈ range n, w i * G w α n i ^ 2 ≤ 4 * ∑ i ∈ range n, w i * α i ^ 2 := by
  have hQ := Q (α := α) hw n 0 n (by omega)
  have hnn : 0 ≤ S w α 0 n ^ 2 / W w 0 n := div_nonneg (sq_nonneg _) (W_nonneg hw 0 n)
  rw [← Finset.range_eq_Ico] at hQ
  have hpt : ∀ i ∈ range n, w i * (G w α n i ^ 2 / 2 - 2 * α i ^ 2)
      ≤ w i * (G w α n i ^ 2 - 2 * α i * G w α n i) := fun i _ =>
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (G w α n i - 2 * α i)]) (hw i).le
  have hs := Finset.sum_le_sum hpt
  have e : ∑ i ∈ range n, w i * (G w α n i ^ 2 / 2 - 2 * α i ^ 2)
      = (∑ i ∈ range n, w i * G w α n i ^ 2) / 2 - 2 * ∑ i ∈ range n, w i * α i ^ 2 := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  linarith



/-! ## D2: uncentered discrete maximal inequality, constant 8 -/

lemma mediant {S1 S2 W1 W2 : ℝ} (h1 : 0 < W1) (h2 : 0 < W2) :
    (S1 + S2) / (W1 + W2) ≤ max (S1 / W1) (S2 / W2) := by
  rw [div_le_iff₀ (by linarith)]
  have a1 : S1 ≤ max (S1 / W1) (S2 / W2) * W1 := by
    rw [← div_le_iff₀ h1]; exact le_max_left _ _
  have a2 : S2 ≤ max (S1 / W1) (S2 / W2) * W2 := by
    rw [← div_le_iff₀ h2]; exact le_max_right _ _
  linarith [mul_add (max (S1 / W1) (S2 / W2)) W1 W2]

lemma avg_nonneg (hw : ∀ k, 0 < w k) (hα : ∀ k, 0 ≤ α k) (i j : ℕ) : 0 ≤ avg w α i j :=
  div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (hw k).le (hα k)) (W_nonneg hw i j)

lemma blk (f : ℕ → ℝ) (K N : ℕ) :
    ∑ k ∈ range (K * N), f k = ∑ c ∈ range K, ∑ i ∈ range N, f (c * N + i) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma div_blk {c i N : ℕ} (hi : i < N) : (c * N + i) / N = c := by
  have hN : 0 < N := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hi, zero_add]

lemma cell_sum (g : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (u : ℕ) : ∀ d,
    ∑ k ∈ Ico (u * N) ((u + d) * N), g (k / N) = N * ∑ c ∈ Ico u (u + d), g c := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show u + (d + 1) = (u + d) + 1 by omega]
    have h1 : u * N ≤ (u + d) * N := Nat.mul_le_mul_right _ (by omega)
    have h2 : (u + d) * N ≤ ((u + d) + 1) * N := Nat.mul_le_mul_right _ (by omega)
    rw [← Finset.sum_Ico_consecutive _ h1 h2, ih, Finset.sum_Ico_succ_top (by omega : u ≤ u + d)]
    have : ∑ k ∈ Ico ((u + d) * N) ((u + d + 1) * N), g (k / N) = N * g (u + d) := by
      rw [show (u + d + 1) * N = (u + d) * N + N by ring, Finset.sum_Ico_eq_sum_range,
        Nat.add_sub_cancel_left]
      rw [Finset.sum_congr rfl (fun i hi => by rw [div_blk (Finset.mem_range.1 hi)])]
      simp
    rw [this]; ring

lemma S_reflect (f : ℕ → ℝ) {M u k : ℕ} (huk : u ≤ k) (hkM : k < M) :
    ∑ x ∈ Ico u (k + 1), f x = ∑ y ∈ Ico (M - 1 - k) (M - u), f (M - 1 - y) := by
  rw [Finset.sum_Ico_reflect f (M - 1 - k) (show M - u ≤ M - 1 + 1 by omega),
    show M - 1 + 1 - (M - u) = u by omega, show M - 1 + 1 - (M - 1 - k) = k + 1 by omega]

lemma left_le {M u k : ℕ} (huk : u ≤ k) (hkM : k < M) :
    avg w α u (k + 1) ≤ G (fun y => w (M - 1 - y)) (fun y => α (M - 1 - y)) M (M - 1 - k) := by
  have h := le_G (w := fun y => w (M - 1 - y)) (α := fun y => α (M - 1 - y)) (b := M)
    (i := M - 1 - k) (j := M - 1 - u) (by omega) (by omega)
  rw [show M - 1 - u + 1 = M - u by omega] at h
  refine le_of_eq_of_le ?_ h
  unfold avg S W
  rw [S_reflect (fun x => w x * α x) huk hkM, S_reflect w huk hkM]

lemma left_sum (hw : ∀ k, 0 < w k) (M : ℕ) :
    ∑ k ∈ range M, w k * G (fun y => w (M - 1 - y)) (fun y => α (M - 1 - y)) M (M - 1 - k) ^ 2
      ≤ 4 * ∑ k ∈ range M, w k * α k ^ 2 := by
  have h := one_sided (w := fun y => w (M - 1 - y)) (α := fun y => α (M - 1 - y))
    (fun k => hw _) M
  rw [← Finset.sum_range_reflect, ← Finset.sum_range_reflect (fun k => w k * α k ^ 2)]
  refine le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
  · apply Finset.sum_congr rfl; intro k hk
    have hk' := Finset.mem_range.1 hk
    simp only [show M - 1 - (M - 1 - k) = k by omega]
  · congr 1

lemma shift_sum (f : ℕ → ℝ) (M : ℕ) (h0 : 0 ≤ f 0) (hM : f M = 0) :
    ∑ k ∈ range M, f (k + 1) ≤ ∑ k ∈ range M, f k := by
  have e1 := Finset.sum_range_succ' f M
  have e2 := Finset.sum_range_succ f M
  linarith

theorem uncentered (ℓ α : ℕ → ℝ) (hℓ : ∀ c, 0 < ℓ c) (hα : ∀ c, 0 ≤ α c) (K : ℕ)
    (p q : ℕ → ℕ) (hp : ∀ c < K, p c ≤ c) (hq : ∀ c < K, c ≤ q c ∧ q c < K) :
    ∑ c ∈ range K, ℓ c * avg ℓ α (p c) (q c + 1) ^ 2 ≤ 8 * ∑ c ∈ range K, ℓ c * α c ^ 2 := by
  set X := ∑ c ∈ range K, ℓ c * avg ℓ α (p c) (q c + 1) ^ 2 with hX
  set Y := ∑ c ∈ range K, ℓ c * α c ^ 2 with hY
  set L := ∑ c ∈ range K, ℓ c with hL
  set B := ∑ c ∈ range K, α c with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun c _ => hα c
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun c _ => (hℓ c).le
  have key : ∀ N : ℕ, 0 < N → X ≤ 8 * Y + L * B ^ 2 / N := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    set M := K * N with hM
    set w' : ℕ → ℝ := fun k => ℓ (k / N) / N with hw'
    set a' : ℕ → ℝ := fun k => α (k / N) with ha'
    have hw'p : ∀ k, 0 < w' k := fun k => div_pos (hℓ _) hNr
    have ha'p : ∀ k, 0 ≤ a' k := fun k => hα _
    -- cell sums
    have hSc : ∀ u v, u ≤ v → S w' a' (u * N) (v * N) = S ℓ α u v := by
      intro u v huv
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huv
      unfold S
      rw [cell_sum (fun c => ℓ c / N * α c) hN u d, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro c _; field_simp
    have hWc : ∀ u v, u ≤ v → W w' (u * N) (v * N) = W ℓ u v := by
      intro u v huv
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huv
      unfold W
      rw [cell_sum (fun c => ℓ c / N) hN u d, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro c _; field_simp
    set Gp := G w' a' M with hGp
    set Gm : ℕ → ℝ := fun k => G (fun y => w' (M - 1 - y)) (fun y => a' (M - 1 - y)) M (M - 1 - k)
      with hGm
    have hGpM : Gp M = 0 := by simp only [hGp, G, lt_irrefl, dif_neg, not_false_eq_true]
    have hGp_bd : ∀ k, 0 ≤ Gp k ∧ Gp k ≤ B := by
      intro k
      rcases lt_or_ge k M with hk | hk
      · refine ⟨le_trans (avg_nonneg hw'p ha'p k (k + 1)) (le_G le_rfl hk), ?_⟩
        apply G_le_of hk
        intro j hkj hjM
        unfold avg
        rw [div_le_iff₀ (W_pos hw'p (by omega))]
        unfold S W
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        simp only [Finset.mem_Ico] at hx
        have hxK : x / N < K := (Nat.div_lt_iff_lt_mul hN).2 (by omega)
        have : a' x ≤ B := Finset.single_le_sum (fun c _ => hα c) (Finset.mem_range.2 hxK)
        nlinarith [hw'p x]
      · have : Gp k = 0 := by simp only [hGp, G, dif_neg (not_lt.2 hk)]
        rw [this]; exact ⟨le_rfl, hB0⟩
    -- pointwise bound
    have hpt : ∀ c < K, ∀ i < N,
        avg ℓ α (p c) (q c + 1) ^ 2 ≤ Gm (c * N + i) ^ 2 + Gp (c * N + i + 1) ^ 2 := by
      intro c hc i hi
      have hpc := hp c hc
      obtain ⟨hcq, hqK⟩ := hq c hc
      have hPk : p c * N ≤ c * N + i := le_trans (Nat.mul_le_mul_right _ hpc) (by omega)
      have hk1 : c * N + i + 1 ≤ (q c + 1) * N := by
        have : (c + 1) * N ≤ (q c + 1) * N := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      have hkM : c * N + i < M := by
        have : (c + 1) * N ≤ K * N := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      have hQM : (q c + 1) * N ≤ M := Nat.mul_le_mul_right _ (by omega)
      have hJ : avg ℓ α (p c) (q c + 1) = avg w' a' (p c * N) ((q c + 1) * N) := by
        unfold avg; rw [hSc _ _ (by omega), hWc _ _ (by omega)]
      have hx0 : 0 ≤ avg ℓ α (p c) (q c + 1) := avg_nonneg hℓ hα _ _
      have hLv : avg w' a' (p c * N) (c * N + i + 1) ≤ Gm (c * N + i) :=
        left_le hPk hkM
      have hsq : ∀ x g : ℝ, 0 ≤ x → x ≤ g → x ^ 2 ≤ g ^ 2 := fun x g h0 h1 => by nlinarith
      rcases hk1.eq_or_lt with heq | hlt
      · rw [hJ, ← heq]
        have := hsq _ _ (avg_nonneg hw'p ha'p _ _) hLv
        nlinarith [sq_nonneg (Gp (c * N + i + 1))]
      · have hRv : avg w' a' (c * N + i + 1) ((q c + 1) * N) ≤ Gp (c * N + i + 1) := by
          have h := le_G (w := w') (α := a') (b := M) (i := c * N + i + 1)
            (j := (q c + 1) * N - 1) (by omega) (by omega)
          rwa [show (q c + 1) * N - 1 + 1 = (q c + 1) * N by omega] at h
        have hmed : avg w' a' (p c * N) ((q c + 1) * N) ≤
            max (avg w' a' (p c * N) (c * N + i + 1)) (avg w' a' (c * N + i + 1) ((q c + 1) * N)) := by
          unfold avg
          rw [S_split w' a' (show p c * N ≤ c * N + i + 1 by omega) hlt.le,
            W_split w' (show p c * N ≤ c * N + i + 1 by omega) hlt.le]
          exact mediant (W_pos hw'p (by omega)) (W_pos hw'p hlt)
        rw [← hJ] at hmed
        rcases le_max_iff.1 hmed with h | h
        · have := hsq _ _ hx0 (le_trans h hLv)
          nlinarith [sq_nonneg (Gp (c * N + i + 1))]
        · have := hsq _ _ hx0 (le_trans h hRv)
          nlinarith [sq_nonneg (Gm (c * N + i))]
    -- per-cell sums
    have hcellN : ∀ (c : ℕ) (x : ℝ), ∑ i ∈ range N, ℓ c / N * x = ℓ c * x := by
      intro c x; simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    have hYk : ∑ k ∈ range M, w' k * a' k ^ 2 = Y := by
      rw [hM, blk]; apply Finset.sum_congr rfl; intro c _
      rw [← hcellN c (α c ^ 2)]; apply Finset.sum_congr rfl; intro i hi
      simp only [hw', ha', div_blk (Finset.mem_range.1 hi)]
    have hA : ∑ c ∈ range K, ∑ i ∈ range N, ℓ c / N * Gm (c * N + i) ^ 2 ≤ 4 * Y := by
      have h := left_sum (w := w') (α := a') hw'p M
      rw [hYk] at h
      have h' : ∑ k ∈ range M, w' k * Gm k ^ 2 ≤ 4 * Y := h
      have e := blk (fun k => w' k * Gm k ^ 2) K N
      rw [← hM] at e
      refine le_of_eq_of_le ?_ h'
      rw [e]; apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro i hi
      show _ = ℓ ((c * N + i) / N) / N * Gm (c * N + i) ^ 2
      rw [div_blk (Finset.mem_range.1 hi)]
    have hBsum : ∑ c ∈ range K, ∑ i ∈ range N, ℓ c / N * Gp (c * N + i + 1) ^ 2 ≤
        4 * Y + L * B ^ 2 / N := by
      have hterm : ∀ c ∈ range K, ∀ i ∈ range N, ℓ c / N * Gp (c * N + i + 1) ^ 2 ≤
          w' (c * N + i + 1) * Gp (c * N + i + 1) ^ 2 + (if i = N - 1 then ℓ c / N * B ^ 2 else 0) := by
        intro c _ i hi
        have hi' := Finset.mem_range.1 hi
        obtain ⟨g0, gB⟩ := hGp_bd (c * N + i + 1)
        by_cases h : i = N - 1
        · rw [if_pos h]
          have : Gp (c * N + i + 1) ^ 2 ≤ B ^ 2 := by nlinarith
          have h1 : 0 ≤ w' (c * N + i + 1) * Gp (c * N + i + 1) ^ 2 :=
            mul_nonneg (hw'p _).le (sq_nonneg _)
          have h2 := mul_le_mul_of_nonneg_left this (div_pos (hℓ c) hNr).le
          linarith
        · rw [if_neg h, add_zero]
          have : (c * N + i + 1) / N = c := by
            rw [show c * N + i + 1 = c * N + (i + 1) by ring]; exact div_blk (by omega)
          simp only [hw', this, le_refl]
      refine le_trans (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun i hi => hterm c hc i hi) ?_
      simp only [Finset.sum_add_distrib]
      have hshift : ∑ c ∈ range K, ∑ i ∈ range N, w' (c * N + i + 1) * Gp (c * N + i + 1) ^ 2 ≤ 4 * Y := by
        have e := blk (fun k => w' (k + 1) * Gp (k + 1) ^ 2) K N
        rw [← e, ← hM]
        refine le_trans (shift_sum (fun k => w' k * Gp k ^ 2) M
          (mul_nonneg (hw'p 0).le (sq_nonneg _)) (by simp [hGpM])) ?_
        have := one_sided (w := w') (α := a') hw'p M
        rw [hYk] at this; exact this
      have hite : ∑ c ∈ range K, ∑ i ∈ range N, (if i = N - 1 then ℓ c / N * B ^ 2 else 0)
          = L * B ^ 2 / N := by
        rw [hL, Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.sum_ite_eq' (range N) (N - 1), if_pos (Finset.mem_range.2 (by omega))]
        ring
      linarith
    have hXs : X = ∑ c ∈ range K, ∑ i ∈ range N, ℓ c / N * avg ℓ α (p c) (q c + 1) ^ 2 := by
      rw [hX]; apply Finset.sum_congr rfl; intro c _; rw [hcellN]
    have hXle : X ≤ ∑ c ∈ range K, ∑ i ∈ range N,
        (ℓ c / N * Gm (c * N + i) ^ 2 + ℓ c / N * Gp (c * N + i + 1) ^ 2) := by
      rw [hXs]
      apply Finset.sum_le_sum; intro c hc; apply Finset.sum_le_sum; intro i hi
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hpt c (Finset.mem_range.1 hc) i (Finset.mem_range.1 hi))
        (div_pos (hℓ c) hNr).le
    simp only [Finset.sum_add_distrib] at hXle
    linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN⟩ := exists_nat_gt (L * B ^ 2 / (X - 8 * Y))
  have hpos : 0 < X - 8 * Y := by linarith
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (by positivity) hpos.le) hN
  have h1 := key N (by exact_mod_cast hNpos)
  have h2 : L * B ^ 2 < (X - 8 * Y) * N := by rw [div_lt_iff₀ hpos] at hN; linarith
  have h3 : L * B ^ 2 / N < X - 8 * Y := by rw [div_lt_iff₀ hNpos]; linarith
  linarith



/-! ## Discrete core: AVR-cells <= 8 * energy-cells -/

theorem core {n : ℕ} (K : ℕ) (ℓ σ : ℕ → ℝ) (hℓ : ∀ c, 0 < ℓ c) (hσ : ∀ c, 0 ≤ σ c)
    (p q : Fin n → ℕ) (hpq : ∀ j, p j ≤ q j ∧ q j < K) (job : ℕ → Option (Fin n))
    (R : Fin n → ℝ)
    (hR : ∀ j, R j = ∑ c ∈ Ico (p j) (q j + 1), ℓ c * (σ c * if job c = some j then 1 else 0)) :
    ∑ c ∈ range K, ℓ c * (∑ j, if p j ≤ c ∧ c ≤ q j then R j / W ℓ (p j) (q j + 1) else 0) ^ 2
      ≤ 8 * ∑ c ∈ range K, ℓ c * σ c ^ 2 := by
  set α : ℕ → ℝ := fun c => ∑ j, if p j ≤ c ∧ c ≤ q j then R j / W ℓ (p j) (q j + 1) else 0
    with hαdef
  have hW : ∀ j, 0 < W ℓ (p j) (q j + 1) := fun j => W_pos hℓ (by have := hpq j; omega)
  have hRnn : ∀ j, 0 ≤ R j := by
    intro j; rw [hR j]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (hℓ c).le
      (mul_nonneg (hσ c) (by split_ifs <;> norm_num))
  have hα : ∀ c, 0 ≤ α c := fun c => Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact div_nonneg (hRnn j) (hW j).le
    · exact le_rfl
  have hfilt : ∀ j, (range K).filter (fun c => p j ≤ c ∧ c ≤ q j) = Ico (p j) (q j + 1) := by
    intro j; ext c; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have := hpq j; omega
  set av : Fin n → ℝ := fun j => avg ℓ α (p j) (q j + 1) with hav
  -- X = sum_j R_j av_j
  have hX1 : ∑ c ∈ range K, ℓ c * α c ^ 2 = ∑ j, R j * av j := by
    have e1 : ∀ c, ℓ c * α c ^ 2 = ∑ j, (if p j ≤ c ∧ c ≤ q j then
        ℓ c * α c * (R j / W ℓ (p j) (q j + 1)) else 0) := by
      intro c
      rw [sq, ← mul_assoc]
      rw [show ℓ c * α c * α c = ℓ c * α c * (∑ j, (if p j ≤ c ∧ c ≤ q j then
        R j / W ℓ (p j) (q j + 1) else 0)) from rfl, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> ring
    simp_rw [e1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_filter, hfilt j, ← Finset.sum_mul]
    simp only [hav, avg, S]
    ring
  -- sum_j R_j av_j = sum_c ℓ σ β
  set β : ℕ → ℝ := fun c => ∑ j, (if p j ≤ c ∧ c ≤ q j then
      (if job c = some j then av j else 0) else 0) with hβ
  have hX2 : ∑ j, R j * av j = ∑ c ∈ range K, ℓ c * σ c * β c := by
    have e2 : ∀ j, R j * av j = ∑ c ∈ range K, (if p j ≤ c ∧ c ≤ q j then
        ℓ c * σ c * (if job c = some j then av j else 0) else 0) := by
      intro j
      rw [← Finset.sum_filter, hfilt j, hR j, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro c _
      split_ifs <;> ring
    simp_rw [e2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    simp only [hβ, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> ring
  -- choice of intervals
  let P : ℕ → ℕ := fun c => match job c with
    | some j => if p j ≤ c ∧ c ≤ q j then p j else c
    | none => c
  let Q : ℕ → ℕ := fun c => match job c with
    | some j => if p j ≤ c ∧ c ≤ q j then q j else c
    | none => c
  have hβsq : ∀ c, β c ^ 2 ≤ avg ℓ α (P c) (Q c + 1) ^ 2 := by
    intro c
    simp only [hβ, P, Q]
    rcases hjc : job c with _ | j0
    · simp; positivity
    · simp only [Option.some.injEq]
      rw [Finset.sum_eq_single j0]
      · by_cases hc : p j0 ≤ c ∧ c ≤ q j0
        · simp [hc, hav]
        · simp only [hc, if_false, ite_false]; nlinarith [sq_nonneg (avg ℓ α c (c + 1))]
      · intro j _ hj; split_ifs with h1 h2
        · exact absurd h2.symm hj
        · rfl
        · rfl
      · simp
  have hPQ : ∀ c < K, P c ≤ c ∧ c ≤ Q c ∧ Q c < K := by
    intro c hc
    simp only [P, Q]
    rcases job c with _ | j0
    · simp; omega
    · simp only
      split_ifs with h
      · exact ⟨h.1, h.2, (hpq j0).2⟩
      · omega
  have hD2 := uncentered ℓ α hℓ hα K P Q (fun c hc => (hPQ c hc).1)
    (fun c hc => ⟨(hPQ c hc).2.1, (hPQ c hc).2.2⟩)
  have hβsum : ∑ c ∈ range K, ℓ c * β c ^ 2 ≤ ∑ c ∈ range K, ℓ c * avg ℓ α (P c) (Q c + 1) ^ 2 :=
    Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hβsq c) (hℓ c).le
  have hamgm : ∑ c ∈ range K, ℓ c * σ c * β c ≤
      4 * ∑ c ∈ range K, ℓ c * σ c ^ 2 + (∑ c ∈ range K, ℓ c * β c ^ 2) / 16 := by
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro c _
    have := mul_le_mul_of_nonneg_left
      (show σ c * β c ≤ 4 * σ c ^ 2 + β c ^ 2 / 16 by nlinarith [sq_nonneg (2 * σ c - β c / 4)])
      (hℓ c).le
    nlinarith
  have hXdef : (∑ c ∈ range K, ℓ c * α c ^ 2) =
      ∑ c ∈ range K, ℓ c * (∑ j, if p j ≤ c ∧ c ≤ q j then R j / W ℓ (p j) (q j + 1) else 0) ^ 2 :=
    rfl
  rw [← hXdef]
  linarith

end AVRMax



open Finset MeasureTheory

namespace AVRBridge

lemma cell_integral {f : ℝ → ℝ} {a b v : ℝ} (hab : a < b) (hf : ∀ t ∈ Set.Ioo a b, f t = v) :
    IntervalIntegrable f MeasureTheory.volume a b ∧ ∫ t in a..b, f t = (b - a) * v := by
  have hI : MeasureTheory.IntegrableOn f (Set.Ioo a b) := by
    have hc : MeasureTheory.IntegrableOn (fun _ : ℝ => v) (Set.Ioo a b) := by
      first
        | exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioo])
        | exact MeasureTheory.integrableOn_const.2 (Or.inr (by simp [Real.volume_Ioo]))
    exact hc.congr_fun (fun t ht => (hf t ht).symm) measurableSet_Ioo
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hI, ?_⟩
  rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hf, MeasureTheory.setIntegral_const]
  simp [MeasureTheory.Measure.real, Real.volume_Ioo, hab.le, smul_eq_mul]

lemma pw (x : ℕ → ℝ) (hx : StrictMono x) (f : ℝ → ℝ) (v : ℕ → ℝ) {u w : ℕ} (huw : u ≤ w)
    (hf : ∀ c ∈ Ico u w, ∀ t ∈ Set.Ioo (x c) (x (c + 1)), f t = v c) :
    ∫ t in x u..x w, f t = ∑ c ∈ Ico u w, (x (c + 1) - x c) * v c := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico (a := x) huw
    (fun c hc => (cell_integral (hx (Nat.lt_succ_self c))
      (hf c (Finset.mem_Ico.2 (Set.mem_Ico.1 hc)))).1)]
  exact Finset.sum_congr rfl fun c hc => (cell_integral (hx (Nat.lt_succ_self c)) (hf c hc)).2

lemma find_cell {m : ℕ} (τ : Fin (m + 1) → ℝ) {u v : ℝ} (huv : u < v)
    (h0 : τ 0 ≤ u) (hl : v ≤ τ (Fin.last m)) (hno : ∀ k, τ k ≤ u ∨ v ≤ τ k) :
    ∃ k : Fin m, τ k.castSucc ≤ u ∧ v ≤ τ k.succ := by
  classical
  let g : ℕ → ℝ := fun i => τ ⟨min i m, by omega⟩
  have hm : v ≤ g m := by
    have : (⟨min m m, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
    simp only [g, this]; exact hl
  have hex : ∃ i, v ≤ g i := ⟨m, hm⟩
  have hspec : v ≤ g (Nat.find hex) := Nat.find_spec hex
  have hle : Nat.find hex ≤ m := Nat.find_min' hex hm
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    have : (⟨min 0 m, by omega⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp)
    simp only [g, this] at hspec; linarith
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero hne
  have hkm : k < m := by omega
  have hlt : ¬ v ≤ g k := Nat.find_min hex (by omega)
  refine ⟨⟨k, hkm⟩, ?_, ?_⟩
  · have e : (⟨k, hkm⟩ : Fin m).castSucc = ⟨min k m, by omega⟩ := Fin.ext (by simp; omega)
    rw [e]
    rcases hno ⟨min k m, by omega⟩ with h | h
    · exact h
    · exact absurd h hlt
  · have e : (⟨k, hkm⟩ : Fin m).succ = ⟨min (Nat.find hex) m, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e]; exact hspec

end AVRBridge

open SpeedScaling.AVR in
theorem upper_of_core
    (hcore : ∀ {n : ℕ} (K : ℕ) (ℓ σ : ℕ → ℝ) (_ : ∀ c, 0 < ℓ c) (_ : ∀ c, 0 ≤ σ c)
      (p q : Fin n → ℕ) (_ : ∀ j, p j ≤ q j ∧ q j < K) (job : ℕ → Option (Fin n))
      (R : Fin n → ℝ)
      (_ : ∀ j, R j = ∑ c ∈ Ico (p j) (q j + 1), ℓ c * (σ c * if job c = some j then 1 else 0)),
      ∑ c ∈ range K, ℓ c * (∑ j, if p j ≤ c ∧ c ≤ q j then
          R j / (∑ k ∈ Ico (p j) (q j + 1), ℓ k) else 0) ^ 2
        ≤ 8 * ∑ c ∈ range K, ℓ c * σ c ^ 2)
    {n : ℕ} (J : Instance n) (S : Schedule n) (hS : IsSchedule J S) (hF : Feasible J S) :
    AVR J ≤ 8 * energy (fun x : ℝ => x ^ 2) J S := by
  classical
  obtain ⟨hs0, m, τ, _hm, hτ, hτ0, hτl, hcell⟩ := hS
  set P : Finset ℝ := univ.image τ ∪ univ.image J.a ∪ univ.image J.b with hP
  have hτP : ∀ k, τ k ∈ P := fun k => by simp [hP]
  have haP : ∀ j, J.a j ∈ P := fun j => by simp [hP]
  have hbP : ∀ j, J.b j ∈ P := fun j => by simp [hP]
  have hPb : ∀ z ∈ P, J.t0 ≤ z ∧ z ≤ J.t1 := by
    intro z hz
    simp only [hP, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with (⟨k, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩
    · constructor
      · rw [← hτ0]; exact hτ.monotone (Fin.zero_le k)
      · rw [← hτl]; exact hτ.monotone (Fin.le_last k)
    · exact ⟨J.ha j, (J.hab j).le.trans (J.hb j)⟩
    · exact ⟨(J.ha j).trans (J.hab j).le, J.hb j⟩
  have ht0P : J.t0 ∈ P := hτ0 ▸ hτP 0
  have ht1P : J.t1 ∈ P := hτl ▸ hτP (Fin.last m)
  obtain ⟨N, hN⟩ : ∃ N, P.card = N := ⟨_, rfl⟩
  set e := P.orderEmbOfFin hN with he
  set x : ℕ → ℝ := fun c => if h : c < N then e ⟨c, h⟩ else J.t1 + c with hxdef
  have hxmem : ∀ c (h : c < N), x c = e ⟨c, h⟩ := fun c h => by simp [hxdef, h]
  have heP : ∀ i, e i ∈ P := fun i => Finset.orderEmbOfFin_mem P hN i
  have hxsurj : ∀ z ∈ P, ∃ c, c < N ∧ x c = z := by
    intro z hz
    have hr := Finset.range_orderEmbOfFin P hN
    have : z ∈ Set.range e := by rw [he, hr]; exact hz
    obtain ⟨i, hi⟩ := this
    exact ⟨i.1, i.2, by rw [hxmem i.1 i.2]; exact hi⟩
  have hxmono : StrictMono x := by
    refine strictMono_nat_of_lt_succ fun c => ?_
    by_cases h1 : c + 1 < N
    · have h0 : c < N := by omega
      rw [hxmem c h0, hxmem (c + 1) h1]
      exact e.strictMono (Fin.mk_lt_mk.2 (by omega))
    · by_cases h0 : c < N
      · rw [hxmem c h0]
        have h2 : x (c + 1) = J.t1 + ((c + 1 : ℕ) : ℝ) := by simp [hxdef, h1]
        rw [h2]
        have := (hPb _ (heP ⟨c, h0⟩)).2
        have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
        push_cast; linarith
      · have h2 : x (c + 1) = J.t1 + ((c + 1 : ℕ) : ℝ) := by simp [hxdef, h1]
        have h3 : x c = J.t1 + (c : ℝ) := by simp [hxdef, h0]
        rw [h2, h3]; push_cast; linarith
  have hN2 : 1 < N := by
    rw [← hN]
    exact Finset.one_lt_card.2 ⟨J.t0, ht0P, J.t1, ht1P, J.ht.ne⟩
  set K := N - 1 with hK
  have hx0 : x 0 = J.t0 := by
    obtain ⟨d, hd, hxd⟩ := hxsurj _ ht0P
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [← hxd, h]
    · have h1 := hxmono h
      have h2 := (hPb _ (show x 0 ∈ P by rw [hxmem 0 (by omega)]; exact heP _)).1
      linarith
  have hxK : x K = J.t1 := by
    obtain ⟨d, hd, hxd⟩ := hxsurj _ ht1P
    rcases Nat.lt_or_ge d K with h | h
    · have h1 := hxmono h
      have h2 := (hPb _ (show x K ∈ P by rw [hxmem K (by omega)]; exact heP _)).2
      linarith
    · have : d = K := by omega
      rw [← this, hxd]
  have hgap : ∀ c, c < K → ∀ z ∈ P, z ≤ x c ∨ x (c + 1) ≤ z := by
    intro c _ z hz
    obtain ⟨d, _, rfl⟩ := hxsurj z hz
    rcases le_or_gt d c with h | h
    · exact Or.inl (hxmono.monotone h)
    · exact Or.inr (hxmono.monotone (by omega))
  set mid : ℕ → ℝ := fun c => (x c + x (c + 1)) / 2 with hmid
  have hmidI : ∀ c, x c < mid c ∧ mid c < x (c + 1) := fun c => by
    have := hxmono (Nat.lt_succ_self c); simp only [hmid]; constructor <;> linarith
  have hconst : ∀ c, c < K → ∀ t ∈ Set.Ioo (x c) (x (c + 1)),
      S.s t = S.s (mid c) ∧ S.job t = S.job (mid c) := by
    intro c hc t ht
    have hlt := hxmono (Nat.lt_succ_self c)
    obtain ⟨k, hk1, hk2⟩ := AVRBridge.find_cell τ hlt
      (by rw [hτ0, ← hx0]; exact hxmono.monotone (Nat.zero_le c))
      (by rw [hτl, ← hxK]; exact hxmono.monotone (by omega))
      (fun k => hgap c hc (τ k) (hτP k))
    obtain ⟨⟨v, hv⟩, ⟨q, hq⟩⟩ := hcell k
    have hm' : mid c ∈ Set.Ioo (τ k.castSucc) (τ k.succ) :=
      ⟨lt_of_le_of_lt hk1 (hmidI c).1, lt_of_lt_of_le (hmidI c).2 hk2⟩
    have ht' : t ∈ Set.Ioo (τ k.castSucc) (τ k.succ) :=
      ⟨lt_of_le_of_lt hk1 ht.1, lt_of_lt_of_le ht.2 hk2⟩
    exact ⟨(hv t ht').trans (hv _ hm').symm, (hq t ht').trans (hq _ hm').symm⟩
  have hpa : ∀ j, ∃ c, c < N ∧ x c = J.a j := fun j => hxsurj _ (haP j)
  have hqb : ∀ j, ∃ c, c < N ∧ x c = J.b j := fun j => hxsurj _ (hbP j)
  choose p hpN hpx using hpa
  choose q' hqN hqx using hqb
  have hpq' : ∀ j, p j < q' j := by
    intro j
    by_contra h
    have := hxmono.monotone (not_lt.1 h)
    rw [hpx, hqx] at this
    linarith [J.hab j]
  obtain ⟨q, hq1⟩ : ∃ q : Fin n → ℕ, ∀ j, q j + 1 = q' j :=
    ⟨fun j => q' j - 1, fun j => by show q' j - 1 + 1 = q' j; have := hpq' j; omega⟩
  have hpq : ∀ j, p j ≤ q j ∧ q j < K := fun j => by
    have := hpq' j; have := hqN j; have := hq1 j; omega
  set ℓ : ℕ → ℝ := fun c => x (c + 1) - x c with hℓdef
  have hℓ : ∀ c, 0 < ℓ c := fun c => sub_pos.2 (hxmono (Nat.lt_succ_self c))
  set σ : ℕ → ℝ := fun c => if c < K then S.s (mid c) else 0 with hσdef
  have hσ : ∀ c, 0 ≤ σ c := by
    intro c
    simp only [hσdef]
    split_ifs with h
    · apply hs0
      have a1 := hxmono.monotone (Nat.zero_le c)
      have a2 := hxmono.monotone (show c + 1 ≤ K by omega)
      have := hmidI c
      constructor <;> linarith
    · exact le_rfl
  set job' : ℕ → Option (Fin n) := fun c => S.job (mid c) with hjob
  have hσc : ∀ c, c < K → ∀ t ∈ Set.Ioo (x c) (x (c + 1)), S.s t = σ c := by
    intro c hc t ht
    rw [(hconst c hc t ht).1]; simp [hσdef, hc]
  have hR : ∀ j, J.R j = ∑ c ∈ Ico (p j) (q j + 1),
      ℓ c * (σ c * if job' c = some j then 1 else 0) := by
    intro j
    rw [← hF j, ← hpx j, ← hqx j, hq1 j]
    rw [AVRBridge.pw x hxmono _ (fun c => σ c * if job' c = some j then 1 else 0)
      (hpq' j).le]
    intro c hc t ht
    have hcK : c < K := by
      have := (Finset.mem_Ico.1 hc).2; have := hqN j; omega
    simp only [execSpeed]
    rw [hσc c hcK t ht, (hconst c hcK t ht).2]
  have hW : ∀ j, J.b j - J.a j = ∑ k ∈ Ico (p j) (q j + 1), ℓ k := by
    intro j
    have h := AVRBridge.pw x hxmono (fun _ => (1 : ℝ)) (fun _ => 1) (hpq' j).le
      (fun _ _ _ _ => rfl)
    rw [intervalIntegral.integral_const, hpx j, hqx j] at h
    rw [hq1 j]
    rw [smul_eq_mul, mul_one] at h
    exact h.trans (Finset.sum_congr rfl fun k _ => mul_one _)
  have hdens : ∀ c, c < K → ∀ t ∈ Set.Ioo (x c) (x (c + 1)), ∀ j,
      densityFun J j t = if p j ≤ c ∧ c ≤ q j then
        J.R j / (∑ k ∈ Ico (p j) (q j + 1), ℓ k) else 0 := by
    intro c _ t ht j
    simp only [densityFun]
    by_cases hc' : p j ≤ c ∧ c ≤ q j
    · rw [if_pos hc', if_pos, density, hW j]
      constructor
      · rw [← hpx j]; exact (hxmono.monotone hc'.1).trans ht.1.le
      · rw [← hqx j, ← hq1 j]; exact ht.2.le.trans (hxmono.monotone (by omega))
    · rw [if_neg hc', if_neg]
      intro hmem
      rcases Nat.lt_or_ge c (p j) with h | h
      · have := hxmono.monotone (show c + 1 ≤ p j by omega)
        rw [hpx j] at this
        linarith [hmem.1, ht.2]
      · have h' : q j + 1 ≤ c := by omega
        have := hxmono.monotone h'
        rw [hq1 j, hqx j] at this
        linarith [hmem.2, ht.1]
  have hE : energy (fun x : ℝ => x ^ 2) J S = ∑ c ∈ range K, ℓ c * σ c ^ 2 := by
    simp only [energy]
    rw [← hx0, ← hxK, AVRBridge.pw x hxmono _ (fun c => σ c ^ 2) (Nat.zero_le K),
      Finset.range_eq_Ico]
    intro c hc t ht
    rw [hσc c (Finset.mem_Ico.1 hc).2 t ht]
  have hA : AVR J = ∑ c ∈ range K, ℓ c * (∑ j, if p j ≤ c ∧ c ≤ q j then
          J.R j / (∑ k ∈ Ico (p j) (q j + 1), ℓ k) else 0) ^ 2 := by
    simp only [AVR]
    rw [← hx0, ← hxK, AVRBridge.pw x hxmono _ (fun c => (∑ j, if p j ≤ c ∧ c ≤ q j then
          J.R j / (∑ k ∈ Ico (p j) (q j + 1), ℓ k) else 0) ^ 2) (Nat.zero_le K),
      Finset.range_eq_Ico]
    intro c hc t ht
    rw [Finset.sum_congr rfl fun j _ => hdens c (Finset.mem_Ico.1 hc).2 t ht j]
  rw [hA, hE]
  exact hcore K ℓ σ hℓ hσ p q hpq job' J.R hR



open Finset MeasureTheory

namespace AVRLow

lemma cell_integral {f : ℝ → ℝ} {a b v : ℝ} (hab : a < b) (hf : ∀ t ∈ Set.Ioo a b, f t = v) :
    IntervalIntegrable f MeasureTheory.volume a b ∧ ∫ t in a..b, f t = (b - a) * v := by
  have hI : MeasureTheory.IntegrableOn f (Set.Ioo a b) := by
    have hc : MeasureTheory.IntegrableOn (fun _ : ℝ => v) (Set.Ioo a b) :=
      MeasureTheory.integrableOn_const (by simp [Real.volume_Ioo])
    exact hc.congr_fun (fun t ht => (hf t ht).symm) measurableSet_Ioo
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hI, ?_⟩
  rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hf, MeasureTheory.setIntegral_const]
  simp [MeasureTheory.Measure.real, Real.volume_Ioo, hab.le, smul_eq_mul]

lemma pw (x : ℕ → ℝ) (f : ℝ → ℝ) (v : ℕ → ℝ) {u w : ℕ} (huw : u ≤ w)
    (hx : ∀ c ∈ Ico u w, x c < x (c + 1))
    (hf : ∀ c ∈ Ico u w, ∀ t ∈ Set.Ioo (x c) (x (c + 1)), f t = v c) :
    IntervalIntegrable f volume (x u) (x w) ∧
    ∫ t in x u..x w, f t = ∑ c ∈ Ico u w, (x (c + 1) - x c) * v c := by
  have hint : ∀ c ∈ Set.Ico u w, IntervalIntegrable f volume (x c) (x (c + 1)) := fun c hc =>
    (cell_integral (hx c (Finset.mem_Ico.2 (Set.mem_Ico.1 hc)))
      (hf c (Finset.mem_Ico.2 (Set.mem_Ico.1 hc)))).1
  refine ⟨IntervalIntegrable.trans_iterate_Ico huw hint, ?_⟩
  rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico (a := x) huw hint]
  exact Finset.sum_congr rfl fun c hc => (cell_integral (hx c hc) (hf c hc)).2

lemma pw_idle (x : ℕ → ℝ) (f : ℝ → ℝ) (v : ℕ → ℝ) (w T : ℝ) {u M : ℕ} (huM : u ≤ M)
    (hx : ∀ c ∈ Ico u M, x c < x (c + 1)) (hT : x M < T)
    (hf : ∀ c ∈ Ico u M, ∀ t ∈ Set.Ioo (x c) (x (c + 1)), f t = v c)
    (hw : ∀ t ∈ Set.Ioo (x M) T, f t = w) :
    ∫ t in x u..T, f t = ∑ c ∈ Ico u M, (x (c + 1) - x c) * v c + (T - x M) * w := by
  obtain ⟨h1, h1'⟩ := pw x f v huM hx hf
  obtain ⟨h2, h2'⟩ := cell_integral hT hw
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, h1', h2']

noncomputable def xs (y : ℝ) (k : ℕ) : ℝ := 1 - y ^ (2 * k)

lemma xs_lt {y : ℝ} (h0 : 0 < y) (h1 : y < 1) {i j : ℕ} (hij : i < j) : xs y i < xs y j := by
  have : y ^ (2 * j) < y ^ (2 * i) := by
    first
      | exact pow_lt_pow_right_of_lt_one₀ h0 h1 (by omega)
      | exact pow_lt_pow_right_of_lt_one h0 h1 (by omega)
      | exact pow_right_strictAnti₀ h0 h1 (by omega)
  simp only [xs]; linarith

lemma xs_mono {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : StrictMono (xs y) :=
  fun _ _ h => xs_lt h0 h1 h

lemma xs_lt_one {y : ℝ} (h0 : 0 < y) (k : ℕ) : xs y k < 1 := by
  simp only [xs]; have := pow_pos h0 (2 * k); linarith

lemma xs_zero (y : ℝ) : xs y 0 = 0 := by simp [xs]

noncomputable def inst (y : ℝ) (h0 : 0 < y) (h1 : y < 1) (N : ℕ) :
    SpeedScaling.AVR.Instance N where
  t0 := 0
  t1 := 1
  ht := one_pos
  a := fun k => xs y k
  b := fun _ => 1
  R := fun k => y ^ (k : ℕ) * (1 - y ^ 2)
  ha := fun k => by
    show (0 : ℝ) ≤ xs y k
    rw [← xs_zero y]; exact (xs_mono h0 h1).monotone (Nat.zero_le _)
  hab := fun k => xs_lt_one h0 k
  hb := fun _ => le_rfl
  hR := fun k => mul_nonneg (pow_nonneg h0.le _) (by nlinarith)

noncomputable def sched (y : ℝ) (N : ℕ) : SpeedScaling.AVR.Schedule N where
  s := fun t => if h : ∃ k : Fin N, t ∈ Set.Ioo (xs y k) (xs y ((k : ℕ) + 1)) then
    (y ^ (h.choose : ℕ))⁻¹ else 0
  job := fun t => if h : ∃ k : Fin N, t ∈ Set.Ioo (xs y k) (xs y ((k : ℕ) + 1)) then
    some h.choose else none

lemma cell_unique {y : ℝ} (h0 : 0 < y) (h1 : y < 1) {N : ℕ} {t : ℝ} (c k : Fin N)
    (hc : t ∈ Set.Ioo (xs y c) (xs y ((c : ℕ) + 1)))
    (hk : t ∈ Set.Ioo (xs y k) (xs y ((k : ℕ) + 1))) : k = c := by
  have hm := (xs_mono h0 h1).monotone
  rcases lt_trichotomy (k : ℕ) c with h | h | h
  · have := hm (show (k : ℕ) + 1 ≤ c by omega); linarith [hk.2, hc.1]
  · exact Fin.ext h
  · have := hm (show (c : ℕ) + 1 ≤ k by omega); linarith [hk.1, hc.2]

lemma sched_on {y : ℝ} (h0 : 0 < y) (h1 : y < 1) {N : ℕ} (c : Fin N) {t : ℝ}
    (ht : t ∈ Set.Ioo (xs y c) (xs y ((c : ℕ) + 1))) :
    (sched y N).s t = (y ^ (c : ℕ))⁻¹ ∧ (sched y N).job t = some c := by
  have h : ∃ k : Fin N, t ∈ Set.Ioo (xs y k) (xs y ((k : ℕ) + 1)) := ⟨c, ht⟩
  have hc : h.choose = c := cell_unique h0 h1 c _ ht h.choose_spec
  simp only [sched, dif_pos h, hc, and_self]

lemma sched_off {y : ℝ} {N : ℕ} {t : ℝ} (ht : xs y N ≤ t) (h0 : 0 < y) (h1 : y < 1) :
    (sched y N).s t = 0 ∧ (sched y N).job t = none := by
  have h : ¬ ∃ k : Fin N, t ∈ Set.Ioo (xs y k) (xs y ((k : ℕ) + 1)) := by
    rintro ⟨k, hk⟩
    have := (xs_mono h0 h1).monotone (show (k : ℕ) + 1 ≤ N by omega)
    linarith [hk.2]
  simp only [sched, dif_neg h, and_self]

lemma sched_nonneg {y : ℝ} (h0 : 0 < y) {N : ℕ} (t : ℝ) : 0 ≤ (sched y N).s t := by
  simp only [sched]
  split_ifs
  · exact inv_nonneg.2 (pow_nonneg h0.le _)
  · exact le_rfl

open SpeedScaling.AVR in
lemma isSched {y : ℝ} (h0 : 0 < y) (h1 : y < 1) (N : ℕ) :
    IsSchedule (inst y h0 h1 N) (sched y N) := by
  refine ⟨fun t _ => sched_nonneg h0 t, N + 1,
    fun i => if (i : ℕ) ≤ N then xs y i else 1, by omega, ?_, ?_, ?_, ?_⟩
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hi := i.2
    rw [if_pos (by omega : (i : ℕ) ≤ N)]
    by_cases h : (i : ℕ) + 1 ≤ N
    · rw [if_pos h]; exact xs_lt h0 h1 (by omega)
    · rw [if_neg h]; exact xs_lt_one h0 _
  · simp [inst, xs_zero]
  · simp [inst]
  · intro k
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hk := k.2
    rw [if_pos (by omega : (k : ℕ) ≤ N)]
    by_cases h : (k : ℕ) + 1 ≤ N
    · rw [if_pos h]
      exact ⟨⟨(y ^ (k : ℕ))⁻¹, fun t ht => (sched_on (N := N) h0 h1 ⟨k, by omega⟩ ht).1⟩,
        ⟨some ⟨k, by omega⟩, fun t ht => (sched_on (N := N) h0 h1 ⟨k, by omega⟩ ht).2⟩⟩
    · rw [if_neg h]
      have hkN : (k : ℕ) = N := by omega
      rw [hkN]
      exact ⟨⟨0, fun t ht => (sched_off ht.1.le h0 h1).1⟩,
        ⟨none, fun t ht => (sched_off ht.1.le h0 h1).2⟩⟩

open SpeedScaling.AVR in
lemma feas {y : ℝ} (h0 : 0 < y) (h1 : y < 1) (N : ℕ) : Feasible (inst y h0 h1 N) (sched y N) := by
  intro j
  show ∫ t in xs y j..1, execSpeed (sched y N) j t = y ^ (j : ℕ) * (1 - y ^ 2)
  rw [pw_idle (xs y) _ (fun c => if c = (j : ℕ) then (y ^ c)⁻¹ else 0) 0 1 j.2.le
    (fun c _ => xs_lt h0 h1 (Nat.lt_succ_self c)) (xs_lt_one h0 N)]
  · beta_reduce
    rw [Finset.sum_eq_single_of_mem (j : ℕ) (Finset.mem_Ico.2 ⟨le_rfl, j.2⟩)]
    · simp only [↓reduceIte, mul_zero, add_zero, xs]
      have hy : y ^ (j : ℕ) ≠ 0 := pow_ne_zero _ h0.ne'
      have e1 : y ^ (2 * ((j : ℕ) + 1)) = (y ^ (j : ℕ)) ^ 2 * y ^ 2 := by ring
      have e2 : y ^ (2 * (j : ℕ)) = (y ^ (j : ℕ)) ^ 2 := by ring
      have e3 : 1 - (y ^ (j : ℕ)) ^ 2 * y ^ 2 - (1 - (y ^ (j : ℕ)) ^ 2)
          = y ^ (j : ℕ) * (y ^ (j : ℕ) * (1 - y ^ 2)) := by ring
      rw [e1, e2, e3, mul_comm _ (y ^ (j : ℕ))⁻¹, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]
    · intro c _ hc; simp [hc]
  · intro c hc t ht
    have hcN := (Finset.mem_Ico.1 hc).2
    obtain ⟨hs, hj⟩ := sched_on h0 h1 ⟨c, hcN⟩ ht
    simp only [execSpeed, hs, hj]
    by_cases h : c = (j : ℕ)
    · subst h; simp
    · have hne : (⟨c, hcN⟩ : Fin N) ≠ j := fun e => h (by rw [← e])
      simp [h, hne]
  · intro t ht
    obtain ⟨hs, _⟩ := sched_off ht.1.le h0 h1
    simp [execSpeed, hs]

open SpeedScaling.AVR in
lemma energy_eq {y : ℝ} (h0 : 0 < y) (h1 : y < 1) (N : ℕ) :
    energy (fun x : ℝ => x ^ 2) (inst y h0 h1 N) (sched y N) = N * (1 - y ^ 2) := by
  show ∫ t in (0:ℝ)..1, ((sched y N).s t) ^ 2 = _
  rw [← xs_zero y, pw_idle (xs y) _ (fun c => ((y ^ c)⁻¹) ^ 2) 0 1 (Nat.zero_le N)
    (fun c _ => xs_lt h0 h1 (Nat.lt_succ_self c)) (xs_lt_one h0 N)]
  · rw [mul_zero, add_zero, Finset.sum_congr rfl (g := fun _ => 1 - y ^ 2)]
    · simp; ring
    · intro c _
      simp only [xs]
      have hy : y ^ c ≠ 0 := pow_ne_zero _ h0.ne'
      have e1 : y ^ (2 * (c + 1)) = (y ^ c) ^ 2 * y ^ 2 := by ring
      have e2 : y ^ (2 * c) = (y ^ c) ^ 2 := by ring
      have e3 : 1 - (y ^ c) ^ 2 * y ^ 2 - (1 - (y ^ c) ^ 2) = (y ^ c) ^ 2 * (1 - y ^ 2) := by ring
      rw [e1, e2, e3, inv_pow, mul_comm _ ((y ^ c) ^ 2)⁻¹, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero 2 hy), one_mul]
  · intro c hc t ht
    rw [(sched_on h0 h1 ⟨c, (Finset.mem_Ico.1 hc).2⟩ ht).1]
  · intro t ht
    rw [(sched_off ht.1.le h0 h1).1]; norm_num

open SpeedScaling.AVR in
lemma dens_eq {y : ℝ} (h0 : 0 < y) (h1 : y < 1) (N : ℕ) (k : Fin N) :
    density (inst y h0 h1 N) k = (1 - y ^ 2) / y ^ (k : ℕ) := by
  show y ^ (k : ℕ) * (1 - y ^ 2) / (1 - xs y k) = _
  simp only [xs]
  have hy : y ^ (k : ℕ) ≠ 0 := pow_ne_zero _ h0.ne'
  have e2 : y ^ (2 * (k : ℕ)) = (y ^ (k : ℕ)) ^ 2 := by ring
  rw [sub_sub_cancel, e2, div_eq_div_iff (pow_ne_zero 2 hy) hy]
  ring

open SpeedScaling.AVR in
lemma dsum_cell {y : ℝ} (h0 : 0 < y) (h1 : y < 1) {N : ℕ} (c : ℕ) (hc : c < N) {t : ℝ}
    (ht : t ∈ Set.Ioo (xs y c) (xs y (c + 1))) :
    ∑ k : Fin N, densityFun (inst y h0 h1 N) k t = ∑ k ∈ range (c + 1), (1 - y ^ 2) / y ^ k := by
  have e : ∀ k : Fin N, densityFun (inst y h0 h1 N) k t =
      if (k : ℕ) ≤ c then (1 - y ^ 2) / y ^ (k : ℕ) else 0 := by
    intro k
    simp only [densityFun]
    rw [dens_eq h0 h1 N k]
    have hm := (xs_mono h0 h1).monotone
    by_cases hk : (k : ℕ) ≤ c
    · rw [if_pos hk, if_pos]
      exact ⟨(hm hk).trans ht.1.le, (ht.2.trans (xs_lt_one h0 _)).le⟩
    · rw [if_neg hk, if_neg]
      intro hmem
      have := hm (show c + 1 ≤ (k : ℕ) by omega)
      have h' : xs y k ≤ t := hmem.1
      linarith [ht.2]
  rw [Finset.sum_congr rfl fun k _ => e k]
  rw [show (∑ k : Fin N, if (k : ℕ) ≤ c then (1 - y ^ 2) / y ^ (k : ℕ) else 0)
      = ∑ k ∈ range N, if k ≤ c then (1 - y ^ 2) / y ^ k else 0 from
    Fin.sum_univ_eq_sum_range (fun k => if k ≤ c then (1 - y ^ 2) / y ^ k else 0) N]
  rw [← Finset.sum_filter]
  congr 1
  ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma geo (y : ℝ) (h0 : 0 < y) : ∀ c : ℕ,
    y ^ c * ∑ k ∈ range (c + 1), (1 - y ^ 2) / y ^ k = (1 + y) * (1 - y ^ (c + 1)) := by
  intro c
  induction c with
  | zero => simp only [pow_zero, one_mul, Finset.sum_range_one, div_one, zero_add, pow_one]; ring
  | succ c ih =>
    have hy : y ^ (c + 1) ≠ 0 := pow_ne_zero _ h0.ne'
    have e1 : y ^ (c + 1) * ((1 - y ^ 2) / y ^ (c + 1)) = 1 - y ^ 2 := by
      rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hy
    have e2 : y ^ (c + 1) * ∑ k ∈ range (c + 1), (1 - y ^ 2) / y ^ k
        = y * (y ^ c * ∑ k ∈ range (c + 1), (1 - y ^ 2) / y ^ k) := by ring
    rw [Finset.sum_range_succ, mul_add, e1, e2, ih]
    ring

open SpeedScaling.AVR in
lemma avr_ge {y : ℝ} (h0 : 0 < y) (h1 : y < 1) (N : ℕ) :
    ∑ c ∈ range N, (1 - y ^ 2) * ((1 + y) ^ 2 * (1 - y ^ (c + 1)) ^ 2) ≤ AVR (inst y h0 h1 N) := by
  show _ ≤ ∫ t in (0:ℝ)..1, (∑ k : Fin N, densityFun (inst y h0 h1 N) k t) ^ 2
  rw [← xs_zero y, pw_idle (xs y) _ (fun c => (∑ k ∈ range (c + 1), (1 - y ^ 2) / y ^ k) ^ 2)
    ((∑ k : Fin N, density (inst y h0 h1 N) k) ^ 2) 1 (Nat.zero_le N)
    (fun c _ => xs_lt h0 h1 (Nat.lt_succ_self c)) (xs_lt_one h0 N)]
  · have hidle : 0 ≤ (1 - xs y N) * ((∑ k : Fin N, density (inst y h0 h1 N) k) ^ 2) :=
      mul_nonneg (sub_nonneg.2 (xs_lt_one h0 N).le) (sq_nonneg _)
    rw [← Finset.range_eq_Ico]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_)) (le_add_of_nonneg_right hidle)
    have hg := geo y h0 c
    simp only [xs]
    have e1 : y ^ (2 * (c + 1)) = (y ^ c) ^ 2 * y ^ 2 := by ring
    have e2 : y ^ (2 * c) = (y ^ c) ^ 2 := by ring
    rw [e1, e2]
    have e3 : (1 - (y ^ c) ^ 2 * y ^ 2 - (1 - (y ^ c) ^ 2)) *
        (∑ k ∈ range (c + 1), (1 - y ^ 2) / y ^ k) ^ 2
        = (1 - y ^ 2) * (y ^ c * ∑ k ∈ range (c + 1), (1 - y ^ 2) / y ^ k) ^ 2 := by ring
    rw [e3, hg]; ring
  · intro c hc t ht
    beta_reduce
    rw [dsum_cell h0 h1 c (Finset.mem_Ico.1 hc).2 ht]
  · intro t ht
    beta_reduce
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [densityFun]
    rw [if_pos]
    exact ⟨((xs_mono h0 h1).monotone k.2.le).trans ht.1.le, ht.2.le⟩

end AVRLow

open SpeedScaling.AVR in
theorem lower_bound : ∀ c : ℝ, c < 4 → ∃ (n : ℕ) (J : Instance n) (S : Schedule n),
    IsSchedule J S ∧ Feasible J S ∧ c * energy (fun x : ℝ => x ^ 2) J S < AVR J := by
  intro c hc
  set ε := min ((4 - c) / 8) (1 / 2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hεc : ε ≤ (4 - c) / 8 := min_le_left _ _
  set y := 1 - ε with hy
  have h0 : 0 < y := by linarith
  have h1 : y < 1 := by linarith
  set D := (1 + y) ^ 2 with hD
  have hDc : c < D := by nlinarith
  have hDpos : 0 < D := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * D * y / ((1 - y) * (D - c)))
  refine ⟨N, AVRLow.inst y h0 h1 N, AVRLow.sched y N, AVRLow.isSched h0 h1 N,
    AVRLow.feas h0 h1 N, ?_⟩
  rw [AVRLow.energy_eq h0 h1 N]
  refine lt_of_lt_of_le ?_ (AVRLow.avr_ge h0 h1 N)
  set G := ∑ k ∈ range N, y ^ (k + 1) with hG
  have hGy : G * (1 - y) ≤ y := by
    have hgs := geom_sum_mul y N
    have : G = y * ∑ k ∈ range N, y ^ k := by
      show ∑ k ∈ range N, y ^ (k + 1) = _
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    have hyN : 0 ≤ y ^ N := pow_nonneg h0.le N
    nlinarith
  have hsum : (N : ℝ) - 2 * G ≤ ∑ k ∈ range N, (1 - y ^ (k + 1)) ^ 2 := by
    have : (N : ℝ) - 2 * G = ∑ k ∈ range N, (1 - 2 * y ^ (k + 1)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp; exact hG
    rw [this]
    exact Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (y ^ (k + 1))]
  have h1y : 0 < 1 - y := by linarith
  have hN' : 2 * D * y < N * ((1 - y) * (D - c)) := by
    rwa [div_lt_iff₀ (mul_pos h1y (by linarith))] at hN
  have h3 : 2 * D * G < N * (D - c) := by
    have : 2 * D * G * (1 - y) < N * (D - c) * (1 - y) := by nlinarith
    exact lt_of_mul_lt_mul_right this h1y.le
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h4 : c * N < D * ∑ k ∈ range N, (1 - y ^ (k + 1)) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsum hDpos.le]
  have h5 := mul_lt_mul_of_pos_left h4 hy2
  nlinarith


open SpeedScaling.AVR in
theorem solution :
    (∀ (n : ℕ) (J : Instance n) (S : Schedule n),
      IsSchedule J S → Feasible J S →
        AVR J ≤ 8 * energy (fun x : ℝ => x ^ 2) J S) ∧
    (∀ c : ℝ, c < 4 →
      ∃ (n : ℕ) (J : Instance n) (S : Schedule n),
        IsSchedule J S ∧ Feasible J S ∧
        c * energy (fun x : ℝ => x ^ 2) J S < AVR J) := by
  exact ⟨fun n J S hS hF => upper_of_core (fun K ℓ σ hℓ hσ p q hpq job R hR =>
    AVRMax.core K ℓ σ hℓ hσ p q hpq job R hR) J S hS hF, lower_bound⟩
