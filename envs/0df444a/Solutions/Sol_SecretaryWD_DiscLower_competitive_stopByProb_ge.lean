-- Prove2me | solution 1 for SecretaryWD.DiscLower.competitive_stopByProb_ge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T08:46:56.598812+00:00
-- url     : https://prove2.me/submissions/5903f549-351e-4fba-b02b-57e3e790f9f2

import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances



namespace SecretaryWD.DiscLower

open Finset

lemma sdl_stopProb_nonneg {n : ℕ} (A : StoppingRule n) (h : Fin n → ℝ) (t : Fin n) :
    0 ≤ stopProb A h t := by
  unfold stopProb
  exact mul_nonneg (A.stop_nonneg t h)
    (prod_nonneg fun s _ => sub_nonneg.mpr (A.stop_le_one s h))

lemma sdl_telescope {n : ℕ} (A : StoppingRule n) (h : Fin n → ℝ) (k : ℕ) :
    ∑ t ∈ univ.filter (fun t : Fin n => t.val < k), stopProb A h t
      + ∏ s ∈ univ.filter (fun s : Fin n => s.val < k), (1 - A.stop s h) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < n
    · have hset : univ.filter (fun t : Fin n => t.val < k + 1)
          = insert (⟨k, hk⟩ : Fin n) (univ.filter (fun t : Fin n => t.val < k)) := by
        ext x; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
      have hnot : (⟨k, hk⟩ : Fin n) ∉ univ.filter (fun t : Fin n => t.val < k) := by simp
      rw [hset, sum_insert hnot, prod_insert hnot]
      have hp : stopProb A h ⟨k, hk⟩ = A.stop ⟨k, hk⟩ h *
          ∏ s ∈ univ.filter (fun s : Fin n => s.val < k), (1 - A.stop s h) := by
        unfold stopProb
        congr 1
      rw [hp]; linarith
    · have hset : univ.filter (fun t : Fin n => t.val < k + 1)
          = univ.filter (fun t : Fin n => t.val < k) := by
        ext x; simp only [mem_filter, mem_univ, true_and]; have := x.2; omega
      rw [hset]; exact ih

lemma sdl_sum_stopProb_le_one {n : ℕ} (A : StoppingRule n) (h : Fin n → ℝ) (k : ℕ) :
    ∑ t ∈ univ.filter (fun t : Fin n => t.val < k), stopProb A h t ≤ 1 := by
  have := sdl_telescope A h k
  have : 0 ≤ ∏ s ∈ univ.filter (fun s : Fin n => s.val < k), (1 - A.stop s h) :=
    prod_nonneg fun s _ => sub_nonneg.mpr (A.stop_le_one s h)
  linarith

lemma sdl_sum_univ_stopProb_le_one {n : ℕ} (A : StoppingRule n) (h : Fin n → ℝ) :
    ∑ t, stopProb A h t ≤ 1 := by
  have := sdl_sum_stopProb_le_one A h n
  have hs : univ.filter (fun t : Fin n => t.val < n) = univ := by
    ext x; simp
  rwa [hs] at this

lemma sdl_swap_sum {n : ℕ} (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P]
    (j k : Fin n) (hP : ∀ π, P (π * Equiv.swap j k) ↔ P π) (f : Fin n → ℝ) :
    ∑ π ∈ univ.filter P, f (π j) = ∑ π ∈ univ.filter P, f (π k) := by
  rw [sum_filter, sum_filter]
  rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap j k))]
  apply sum_congr rfl
  intro π _
  simp only [Equiv.coe_mulRight, hP, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]

lemma sdl_perm_avg {n : ℕ} (j : Fin n) (f : Fin n → ℝ) :
    (n : ℝ) * ∑ π : Equiv.Perm (Fin n), f (π j) = (n.factorial : ℝ) * ∑ e, f e := by
  have h1 : ∀ k : Fin n, ∑ π : Equiv.Perm (Fin n), f (π k) = ∑ π : Equiv.Perm (Fin n), f (π j) := by
    intro k
    have := sdl_swap_sum (fun _ => True) k j (by simp) f
    simpa using this
  have h2 : ∑ k : Fin n, ∑ π : Equiv.Perm (Fin n), f (π k) = (n : ℝ) * ∑ π : Equiv.Perm (Fin n), f (π j) := by
    rw [sum_congr rfl (fun k _ => h1 k)]; simp
  rw [← h2, sum_comm]
  have h3 : ∀ π : Equiv.Perm (Fin n), ∑ k, f (π k) = ∑ e, f e := fun π => Equiv.sum_comp π f
  rw [sum_congr rfl (fun π _ => h3 π)]
  simp [Fintype.card_perm]


lemma sdl_valueLevel_le (c t e : ℕ) : valueLevel c t e ≤ t := by
  unfold valueLevel
  calc _ ≤ (Icc 1 t).card := card_filter_le _ _
    _ = t := by simp

lemma sdl_valueLevel_eq_of (c t e : ℕ) (hc : 1 ≤ c) (h : e * c ^ (2 * t) < horizon c) :
    valueLevel c t e = t := by
  unfold valueLevel
  rw [filter_true_of_mem]
  · simp
  intro s hs
  rw [mem_Icc] at hs
  calc e * c ^ (2 * s) ≤ e * c ^ (2 * t) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hc (by omega))
    _ < _ := h

lemma sdl_valueLevel_eq_imp (c t e : ℕ) (ht : 1 ≤ t) (h : valueLevel c t e = t) :
    e * c ^ (2 * t) < horizon c := by
  unfold valueLevel at h
  have h2 : (Icc 1 t).filter (fun s => e * c ^ (2 * s) < horizon c) = Icc 1 t := by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    rw [h]; simp
  have : t ∈ (Icc 1 t).filter (fun s => e * c ^ (2 * s) < horizon c) := by
    rw [h2]; simp [ht]
  exact (mem_filter.mp this).2

lemma sdl_valueLevel_succ (c t e : ℕ) (h : ¬ e * c ^ (2 * (t + 1)) < horizon c) :
    valueLevel c (t + 1) e = valueLevel c t e := by
  unfold valueLevel
  have : Icc 1 (t + 1) = insert (t + 1) (Icc 1 t) := by
    ext x; simp; omega
  rw [this, filter_insert, if_neg h]

/-- `n = n_t * c^(4c-2t)` -/
lemma sdl_horizon_split (c t : ℕ) (ht : t ≤ 2 * c) :
    horizon c = c ^ (2 * t) * c ^ (4 * c - 2 * t) := by
  unfold horizon; rw [← pow_add]; congr 1; omega

lemma sdl_top_iff (c t e : ℕ) (hc : 1 ≤ c) (ht : t ≤ 2 * c) :
    e * c ^ (2 * t) < horizon c ↔ e < c ^ (4 * c - 2 * t) := by
  rw [sdl_horizon_split c t ht, mul_comm (c ^ (2 * t))]
  exact Nat.mul_lt_mul_right (pow_pos hc _)

lemma sdl_horizon_pos (c : ℕ) (hc : 1 ≤ c) : 0 < horizon c := by
  unfold horizon; exact pow_pos hc _

lemma sdl_coupling_gen {n : ℕ} (hnpos : 0 < n) (A : StoppingRule n) (v w : Fin n → ℝ)
    (m' k : ℕ) (hm'n : m' ≤ n) (hsame : ∀ e : Fin n, ¬ e.val < m' → v e = w e) :
    stopByProb v A k - (k : ℝ) * m' / n ≤ stopByProb w A k := by
  unfold stopByProb
  set F := univ.filter (fun j : Fin n => j.val < k) with hF
  let g : Fin n → ℝ := fun e => if e.val < m' then 1 else 0
  -- per permutation bound
  have hper : ∀ π : Equiv.Perm (Fin n),
      ∑ j ∈ F, stopProb A (arrivalValues v π) j
        - ∑ j ∈ F, stopProb A (arrivalValues w π) j
        ≤ ∑ j ∈ F, g (π j) := by
    intro π
    by_cases hgood : ∀ j ∈ F, ¬ (π j).val < m'
    · have hrhs : ∑ j ∈ F, g (π j) = 0 := by
        apply sum_eq_zero; intro j hj; simp [g, hgood j hj]
      have heq : ∀ j ∈ F, stopProb A (arrivalValues v π) j
          = stopProb A (arrivalValues w π) j := by
        intro j hj
        have hag : ∀ s : Fin n, s ≤ j → arrivalValues v π s
            = arrivalValues w π s := by
          intro s hs
          apply hsame
          apply hgood
          simp only [hF, mem_filter, mem_univ, true_and] at hj ⊢
          exact lt_of_le_of_lt (Fin.le_def.mp hs) hj
        unfold stopProb
        rw [A.adapted j _ _ hag]
        congr 1
        apply prod_congr rfl
        intro s hs
        rw [A.adapted s _ _ (fun r hr => hag r (le_trans hr (le_of_lt (mem_filter.mp hs).2)))]
      rw [sum_congr rfl heq, hrhs]; simp
    · push_neg at hgood
      obtain ⟨j0, hj0, hj0'⟩ := hgood
      have h1 : ∑ j ∈ F, stopProb A (arrivalValues v π) j ≤ 1 :=
        sdl_sum_stopProb_le_one A _ _
      have h2 : 0 ≤ ∑ j ∈ F, stopProb A (arrivalValues w π) j :=
        sum_nonneg fun j _ => sdl_stopProb_nonneg A _ j
      have h3 : 1 ≤ ∑ j ∈ F, g (π j) := by
        have : g (π j0) = 1 := by simp [g, hj0']
        rw [← this]
        exact single_le_sum (f := fun j => g (π j)) (fun j _ => by simp only [g]; split_ifs <;> norm_num) hj0
      linarith
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have havg : ∀ j : Fin n, ∑ π : Equiv.Perm (Fin n), g (π j) = (n.factorial : ℝ) / n * m' := by
    intro j
    have := sdl_perm_avg j g
    have hsg : ∑ e, g e = (m' : ℝ) := by
      simp only [g, sum_boole]
      rw [Fin.card_filter_val_lt]
      simp [min_eq_right hm'n]
    rw [hsg] at this
    field_simp
    linarith
  have hcardF : (F.card : ℝ) ≤ k := by
    rw [hF, Fin.card_filter_val_lt]; exact_mod_cast min_le_right _ _
  have hsum : ∑ π : Equiv.Perm (Fin n), ∑ j ∈ F, stopProb A (arrivalValues v π) j
      - ∑ π : Equiv.Perm (Fin n), ∑ j ∈ F, stopProb A (arrivalValues w π) j
      ≤ (n.factorial : ℝ) * (k * m' / n) := by
    rw [← sum_sub_distrib]
    calc _ ≤ ∑ π : Equiv.Perm (Fin n), ∑ j ∈ F, g (π j) := sum_le_sum fun π _ => hper π
      _ = ∑ j ∈ F, (n.factorial : ℝ) / n * m' := by rw [sum_comm]; exact sum_congr rfl fun j _ => havg j
      _ = F.card * ((n.factorial : ℝ) / n * m') := by simp
      _ ≤ k * ((n.factorial : ℝ) / n * m') :=
          mul_le_mul_of_nonneg_right hcardF (by positivity)
      _ = _ := by field_simp
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h5 : 1 / (n.factorial : ℝ) * ((n.factorial : ℝ) * (k * m' / n)) = k * m' / n := by
    field_simp
  have := mul_le_mul_of_nonneg_left hsum (by positivity : (0:ℝ) ≤ 1 / (n.factorial : ℝ))
  rw [mul_sub, h5] at this
  linarith

lemma sdl_coupling_core (c t : ℕ) (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t < 2 * c)
    (A : StoppingRule (horizon c)) :
    stopByProb (hardInstance c t) A (blockEnd c t) - 1 / (c : ℝ) ^ 2 ≤
      stopByProb (hardInstance c (t + 1)) A (blockEnd c t) := by
  have hnpos := sdl_horizon_pos c hc
  have hm'n : c ^ (4 * c - 2 * (t + 1)) ≤ horizon c := by
    rw [sdl_horizon_split c (t+1) (by omega)]
    exact Nat.le_mul_of_pos_left _ (pow_pos hc _)
  have hsame : ∀ e : Fin (horizon c), ¬ e.val < c ^ (4 * c - 2 * (t + 1)) →
      hardInstance c t e = hardInstance c (t + 1) e := by
    intro e he
    have : ¬ e.val * c ^ (2 * (t + 1)) < horizon c := by
      rw [sdl_top_iff c (t+1) e hc (by omega)]; exact he
    unfold hardInstance; rw [sdl_valueLevel_succ c t e this]
  have := sdl_coupling_gen hnpos A (hardInstance c t) (hardInstance c (t + 1)) _ (blockEnd c t) hm'n hsame
  have hkey : (blockEnd c t : ℝ) * (c ^ (4 * c - 2 * (t + 1)) : ℕ) / (horizon c : ℕ) = 1 / (c : ℝ) ^ 2 := by
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
    rw [sdl_horizon_split c (t+1) (by omega), blockEnd]
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    rw [← pow_add, ← pow_add, ← pow_add]
    rw [one_mul]; congr 1; omega
  rw [hkey] at this
  exact this


lemma sdl_avoid_step {n : ℕ} (T : Finset (Fin n)) (k : ℕ) (hk : k < n) :
    (((univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => ∀ j : Fin n, j.val < k + 1 → π j ∉ T)).card : ℝ) ≤
      ((univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => ∀ j : Fin n, j.val < k → π j ∉ T)).card * (1 - (T.card : ℝ) / n) := by
  set S := (univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => ∀ j : Fin n, j.val < k → π j ∉ T) with hS
  set kk : Fin n := ⟨k, hk⟩
  have hsplit : (univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => ∀ j : Fin n, j.val < k + 1 → π j ∉ T) = S.filter (fun π => π kk ∉ T) := by
    ext π
    simp only [hS, mem_filter, mem_univ, true_and]
    constructor
    · intro h; exact ⟨fun j hj => h j (by omega), h kk (by simp [kk])⟩
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact h1 j h
      · have : j = kk := Fin.ext h
        rw [this]; exact h2
  let ind : Fin n → ℝ := fun e => if e ∈ T then 1 else 0
  set B := ∑ π ∈ S, ind (π kk) with hB
  have hcard1 : ((S.filter (fun π => π kk ∉ T)).card : ℝ) = S.card - B := by
    have := card_filter_add_card_filter_not (s := S) (fun π => π kk ∉ T)
    have hB' : B = ((S.filter (fun π => ¬ (π kk ∉ T))).card : ℝ) := by
      rw [hB]; simp only [ind, not_not]; rw [sum_boole]
    rw [hB']
    rw [← this]; push_cast; ring
  -- symmetry
  have hsym : ∀ j : Fin n, k ≤ j.val → ∑ π ∈ S, ind (π j) = B := by
    intro j hj
    rw [hS, hB, hS]
    apply sdl_swap_sum
    intro π
    constructor
    · intro h i hi
      have := h i hi
      have hne1 : i ≠ j := by intro e; rw [e] at hi; omega
      have hne2 : i ≠ kk := by intro e; rw [e] at hi; simp [kk] at hi
      simpa [Equiv.swap_apply_of_ne_of_ne hne1 hne2] using this
    · intro h i hi
      have hne1 : i ≠ j := by intro e; rw [e] at hi; omega
      have hne2 : i ≠ kk := by intro e; rw [e] at hi; simp [kk] at hi
      simpa [Equiv.swap_apply_of_ne_of_ne hne1 hne2] using h i hi
  have hdouble : ∑ j ∈ univ.filter (fun j : Fin n => k ≤ j.val), ∑ π ∈ S, ind (π j)
      = S.card * (T.card : ℝ) := by
    rw [sum_comm]
    have : ∀ π ∈ S, ∑ j ∈ univ.filter (fun j : Fin n => k ≤ j.val), ind (π j) = T.card := by
      intro π hπ
      rw [hS, mem_filter] at hπ
      rw [sum_filter]
      have : ∀ j : Fin n, (if k ≤ j.val then ind (π j) else 0) = ind (π j) := by
        intro j
        split_ifs with h
        · rfl
        · have := hπ.2 j (by omega); simp [ind, this]
      rw [sum_congr rfl (fun j _ => this j)]
      rw [Equiv.sum_comp π ind]
      simp [ind, sum_boole]
    rw [sum_congr rfl this]; simp
  have hcount : ((univ.filter (fun j : Fin n => k ≤ j.val)).card : ℝ) = n - k := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun j : Fin n => j.val < k)
    have h2 : (univ.filter (fun j : Fin n => ¬ j.val < k)) = univ.filter (fun j : Fin n => k ≤ j.val) := by
      ext j; simp
    rw [h2, Fin.card_filter_val_lt, card_univ, Fintype.card_fin, min_eq_right hk.le] at h1
    have : (univ.filter (fun j : Fin n => k ≤ j.val)).card = n - k := by omega
    rw [this]; push_cast [hk.le]; ring
  rw [sum_congr rfl (fun j hj => hsym j (by simpa using hj)), sum_const, nsmul_eq_mul, hcount] at hdouble
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hBnn : 0 ≤ B := sum_nonneg fun π _ => by simp only [ind]; split_ifs <;> norm_num
  have hkn : (k : ℝ) < n := by exact_mod_cast hk
  have hkey : (S.card : ℝ) * T.card / n ≤ B := by
    rw [div_le_iff₀ hnpos]
    have hk0 : (0:ℝ) ≤ k := by positivity
    nlinarith
  rw [hsplit, hcard1]
  have : (S.card : ℝ) * (1 - (T.card : ℝ) / n) = S.card - S.card * T.card / n := by ring
  rw [this]; linarith

lemma sdl_avoid_card {n : ℕ} (T : Finset (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (((univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => ∀ j : Fin n, j.val < k → π j ∉ T)).card : ℝ) ≤
      (n.factorial : ℝ) * (1 - (T.card : ℝ) / n) ^ k := by
  induction k with
  | zero =>
    simp [Fintype.card_perm]
  | succ k ih =>
    have hx : 0 ≤ 1 - (T.card : ℝ) / n := by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have : (T.card : ℝ) ≤ n := by
        have := card_le_univ T; simp at this; exact_mod_cast this
      rw [sub_nonneg, div_le_one hnpos]; exact this
    calc _ ≤ _ := sdl_avoid_step T k (by omega)
      _ ≤ (n.factorial : ℝ) * (1 - (T.card : ℝ) / n) ^ k * (1 - (T.card : ℝ) / n) :=
          mul_le_mul_of_nonneg_right (ih (by omega)) hx
      _ = _ := by ring

lemma sdl_discountClass_le (c t j : ℕ) (hc : 1 ≤ c) (ht : 1 ≤ t) (hj : j < c ^ (2 * t)) :
    discountClass c j ≤ t := by
  unfold discountClass
  have : ((Icc 1 (2 * c)).filter (fun s => c ^ (2 * s) < j + 1)) ⊆ Icc 1 (t - 1) := by
    intro s hs
    simp only [mem_filter, mem_Icc] at hs ⊢
    refine ⟨hs.1.1, ?_⟩
    by_contra hcon
    have : c ^ (2 * t) ≤ c ^ (2 * s) := Nat.pow_le_pow_right hc (by omega)
    omega
  have := card_le_card this
  simp only [Nat.card_Icc] at this; omega

lemma sdl_discountClass_ge (c u j : ℕ) (hc : 1 ≤ c) (hu : u ≤ 2 * c) (hj : c ^ (2 * u) ≤ j) :
    u + 1 ≤ discountClass c j := by
  unfold discountClass
  have : Icc 1 u ⊆ ((Icc 1 (2 * c)).filter (fun s => c ^ (2 * s) < j + 1)) := by
    intro s hs
    simp only [mem_filter, mem_Icc] at hs ⊢
    refine ⟨⟨hs.1, by omega⟩, ?_⟩
    have : c ^ (2 * s) ≤ c ^ (2 * u) := Nat.pow_le_pow_right hc (by omega)
    omega
  have := card_le_card this
  simp only [Nat.card_Icc] at this; omega

lemma sdl_discount_nonneg (c : ℕ) (j : Fin (horizon c)) : 0 ≤ discount c j := by
  unfold discount; positivity

lemma sdl_hardInstance_nonneg (c t : ℕ) (e : Fin (horizon c)) : 0 ≤ hardInstance c t e := by
  unfold hardInstance; split_ifs <;> positivity

lemma sdl_opt_core (c t : ℕ) (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c) :
    (1 - 1 / Real.exp 1) * (bigK c : ℝ) ^ t * ((c : ℝ) ^ t)⁻¹ ≤
      expectedOPT (discount c) (hardInstance c t) := by
  have hnpos := sdl_horizon_pos c hc
  set m := c ^ (4 * c - 2 * t) with hm
  have hmn : m ≤ horizon c := by
    rw [sdl_horizon_split c t ht2]; exact Nat.le_mul_of_pos_left _ (pow_pos hc _)
  set T : Finset (Fin (horizon c)) := univ.filter (fun e => e.val < m) with hT
  have hTcard : T.card = m := by rw [hT, Fin.card_filter_val_lt, min_eq_right hmn]
  set k := blockEnd c t with hk
  have hkn : k ≤ horizon c := by
    rw [sdl_horizon_split c t ht2, hk, blockEnd]; exact Nat.le_mul_of_pos_right _ (pow_pos hc _)
  have hav := sdl_avoid_card T k hkn
  set V : ℝ := (bigK c : ℝ) ^ t * ((c : ℝ) ^ t)⁻¹ with hV
  have hVnn : 0 ≤ V := by positivity
  -- pointwise
  have hpt : ∀ π : Equiv.Perm (Fin (horizon c)),
      (if ∀ j : Fin (horizon c), j.val < k → π j ∉ T then (0:ℝ) else V) ≤
        ⨆ j : Fin (horizon c), discount c j * hardInstance c t (π j) := by
    intro π
    have hbdd : BddAbove (Set.range fun j : Fin (horizon c) => discount c j * hardInstance c t (π j)) :=
      (Set.finite_range _).bddAbove
    split_ifs with h
    · exact le_ciSup_of_le hbdd ⟨0, hnpos⟩
        (mul_nonneg (sdl_discount_nonneg c _) (sdl_hardInstance_nonneg c t _))
    · push_neg at h
      obtain ⟨j, hj, hjT⟩ := h
      refine le_ciSup_of_le hbdd j ?_
      have hlev : valueLevel c t (π j).val = t := by
        apply sdl_valueLevel_eq_of c t _ hc
        rw [sdl_top_iff c t _ hc ht2]
        simpa [hT] using hjT
      have hval : hardInstance c t (π j) = (bigK c : ℝ) ^ t := by
        unfold hardInstance; rw [hlev]; simp; omega
      rw [hval, hV, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold discount
      have hcl := sdl_discountClass_le c t j.val hc ht1 hj
      have hcpos : (0:ℝ) < c := by exact_mod_cast hc
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ (by exact_mod_cast hc) hcl
  have hsum := sum_le_sum (fun π (_ : π ∈ (univ : Finset (Equiv.Perm (Fin (horizon c))))) => hpt π)
  rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul] at hsum
  have hc2 := card_filter_add_card_filter_not (s := (univ : Finset (Equiv.Perm (Fin (horizon c)))))
    (fun π => ∀ j : Fin (horizon c), j.val < k → π j ∉ T)
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at hc2
  have hc2' : (((univ : Finset (Equiv.Perm (Fin (horizon c)))).filter
      (fun π => ¬ ∀ j : Fin (horizon c), j.val < k → π j ∉ T)).card : ℝ) =
      (horizon c).factorial - ((univ : Finset (Equiv.Perm (Fin (horizon c)))).filter
      (fun π => ∀ j : Fin (horizon c), j.val < k → π j ∉ T)).card := by
    rw [← hc2]; push_cast; ring
  rw [hc2'] at hsum
  -- exponential bound
  have hxk : (1 - (T.card : ℝ) / (horizon c)) ^ k ≤ 1 / Real.exp 1 := by
    have hx0 : 0 ≤ 1 - (T.card : ℝ) / (horizon c) := by
      rw [hTcard, sub_nonneg, div_le_one (by exact_mod_cast hnpos)]; exact_mod_cast hmn
    have h1 : 1 - (T.card : ℝ) / (horizon c) ≤ Real.exp (-((T.card : ℝ) / (horizon c))) := by
      have := Real.add_one_le_exp (-((T.card : ℝ) / (horizon c))); linarith
    calc _ ≤ Real.exp (-((T.card : ℝ) / (horizon c))) ^ k := pow_le_pow_left₀ hx0 h1 k
      _ = Real.exp (-1) := by
          rw [← Real.exp_nat_mul]; congr 1
          rw [hTcard, sdl_horizon_split c t ht2, hk, blockEnd]
          have : (0:ℝ) < (c:ℝ) ^ (4 * c - 2 * t) := by positivity
          have : (0:ℝ) < (c:ℝ) ^ (2 * t) := by positivity
          push_cast; field_simp; rw [hm]; push_cast; ring
      _ = 1 / Real.exp 1 := by rw [Real.exp_neg]; ring
  have hfpos : (0:ℝ) < (horizon c).factorial := by exact_mod_cast Nat.factorial_pos _
  have hSle : (((univ : Finset (Equiv.Perm (Fin (horizon c)))).filter
      (fun π => ∀ j : Fin (horizon c), j.val < k → π j ∉ T)).card : ℝ) ≤
      (horizon c).factorial * (1 / Real.exp 1) :=
    hav.trans (mul_le_mul_of_nonneg_left hxk hfpos.le)
  unfold expectedOPT
  rw [show (1 - 1 / Real.exp 1) * (bigK c : ℝ) ^ t * ((c : ℝ) ^ t)⁻¹ = (1 - 1 / Real.exp 1) * V by
    rw [hV]; ring]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hfpos]
  nlinarith


lemma sdl_bigK_ge_one (c : ℕ) (hc : 1 ≤ c) : (1 : ℝ) ≤ bigK c := by
  have : 1 ≤ bigK c := by
    unfold bigK; exact Nat.one_le_pow _ _ (sdl_horizon_pos c hc)
  exact_mod_cast this

lemma sdl_discount_le (c : ℕ) (hc : 1 ≤ c) (j : Fin (horizon c)) (u : ℕ) (hu : u ≤ 2 * c)
    (hj : c ^ (2 * u) ≤ j.val) : discount c j ≤ ((c : ℝ) ^ (u + 1))⁻¹ := by
  unfold discount
  have hcl := sdl_discountClass_ge c u j.val hc hu hj
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ (by exact_mod_cast hc) hcl

lemma sdl_discount_le_one (c : ℕ) (hc : 1 ≤ c) (j : Fin (horizon c)) : discount c j ≤ 1 := by
  unfold discount
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by exact_mod_cast hc)

lemma sdl_stopProb_le_one {n : ℕ} (A : StoppingRule n) (h : Fin n → ℝ) (t : Fin n) :
    stopProb A h t ≤ 1 :=
  (single_le_sum (fun j _ => sdl_stopProb_nonneg A h j) (mem_univ t)).trans
    (sdl_sum_univ_stopProb_le_one A h)

lemma sdl_S_bound (c u : ℕ) (hc : 1 ≤ c) (hu : u ≤ 2 * c) :
    ∑ j ∈ univ.filter (fun j : Fin (horizon c) => j.val < c ^ (2 * u)), discount c j
      ≤ 2 * (c : ℝ) ^ u := by
  by_cases hc1 : c = 1
  · subst hc1
    calc _ ≤ ∑ j ∈ univ.filter (fun j : Fin (horizon 1) => j.val < 1 ^ (2 * u)), (1 : ℝ) :=
          sum_le_sum fun j _ => sdl_discount_le_one 1 le_rfl j
      _ ≤ ((univ : Finset (Fin (horizon 1))).card : ℝ) := by
          rw [sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast card_le_univ _
      _ ≤ _ := by rw [card_univ, Fintype.card_fin]; norm_num [horizon]
  have hc2 : 2 ≤ c := by omega
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc
  induction u with
  | zero =>
    calc _ ≤ ∑ j ∈ univ.filter (fun j : Fin (horizon c) => j.val < c ^ (2 * 0)), (1 : ℝ) := by
          apply sum_le_sum; intro j _
          exact sdl_discount_le_one c hc j
      _ ≤ _ := by
          simp only [sum_const, nsmul_eq_mul, mul_one, pow_zero]
          have : ((univ.filter (fun j : Fin (horizon c) => j.val < c ^ (2 * 0))).card : ℝ) ≤ 1 := by
            rw [Fin.card_filter_val_lt]; simp
          linarith
  | succ u ih =>
    have ih := ih (by omega)
    rw [← sum_filter_add_sum_filter_not _ (fun j : Fin (horizon c) => j.val < c ^ (2 * u))]
    rw [filter_filter]
    have hset : univ.filter (fun j : Fin (horizon c) => j.val < c ^ (2 * (u + 1)) ∧ j.val < c ^ (2 * u))
        = univ.filter (fun j : Fin (horizon c) => j.val < c ^ (2 * u)) := by
      ext j; simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; refine ⟨lt_of_lt_of_le h (Nat.pow_le_pow_right hc (by omega)), h⟩
    rw [hset]
    have h2 : ∑ j ∈ (univ.filter (fun j : Fin (horizon c) => j.val < c ^ (2 * (u + 1)))).filter
        (fun j => ¬ j.val < c ^ (2 * u)), discount c j ≤ (c : ℝ) ^ (u + 1) := by
      calc _ ≤ ∑ j ∈ (univ.filter (fun j : Fin (horizon c) => j.val < c ^ (2 * (u + 1)))).filter
            (fun j => ¬ j.val < c ^ (2 * u)), ((c:ℝ) ^ (u + 1))⁻¹ := by
            apply sum_le_sum; intro j hj
            rw [mem_filter] at hj
            exact sdl_discount_le c hc j u (by omega) (by omega)
        _ ≤ ∑ j ∈ (univ.filter (fun j : Fin (horizon c) => j.val < c ^ (2 * (u + 1)))),
              ((c:ℝ) ^ (u + 1))⁻¹ :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
        _ ≤ (c ^ (2 * (u + 1)) : ℕ) * ((c:ℝ) ^ (u + 1))⁻¹ := by
            rw [sum_const, nsmul_eq_mul]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [Fin.card_filter_val_lt]; exact_mod_cast min_le_right _ _
        _ = _ := by
            push_cast
            rw [show 2 * (u + 1) = (u + 1) + (u + 1) by ring, pow_add]
            field_simp
    have h3 : 2 * (c : ℝ) ^ u + (c : ℝ) ^ (u + 1) ≤ 2 * (c : ℝ) ^ (u + 1) := by
      have : (2 : ℝ) ≤ c := by exact_mod_cast hc2
      have : (0:ℝ) < (c:ℝ) ^ u := by positivity
      rw [pow_succ]; nlinarith
    linarith


lemma sdl_discount_le_inv (c : ℕ) (hc : 1 ≤ c) (j : Fin (horizon c)) :
    discount c j ≤ (c : ℝ)⁻¹ := by
  unfold discount
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc
  apply inv_anti₀ hcpos
  have : 1 ≤ discountClass c j.val := by unfold discountClass; omega
  calc (c:ℝ) = (c:ℝ) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hc) this

lemma sdl_blockEnd_mono (c t : ℕ) (hc : 1 ≤ c) : blockEnd c (t - 1) ≤ blockEnd c t := by
  unfold blockEnd; exact Nat.pow_le_pow_right hc (by omega)

lemma sdl_ev_point (c t : ℕ) (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c)
    (j e : Fin (horizon c)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    discount c j * hardInstance c t e * p ≤
      (c:ℝ)⁻¹ * (bigK c : ℝ) ^ (t - 1) * p + (bigK c : ℝ) ^ t *
        ((if j.val < blockEnd c (t - 1) then
            discount c j * (if e.val < c ^ (4 * c - 2 * t) then 1 else 0) else 0)
         + ((c:ℝ) ^ t)⁻¹ * ((if j.val < blockEnd c t then p else 0)
              - (if j.val < blockEnd c (t - 1) then p else 0))
         + ((c:ℝ) ^ (t + 1))⁻¹ * p) := by
  have hK := sdl_bigK_ge_one c hc
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc
  have hd0 := sdl_discount_nonneg c j
  have hmono := sdl_blockEnd_mono c t hc
  have hdiff : 0 ≤ (if j.val < blockEnd c t then p else 0)
              - (if j.val < blockEnd c (t - 1) then p else 0) := by
    split_ifs <;> first | linarith | omega
  have hA0 : 0 ≤ (if j.val < blockEnd c (t - 1) then
            discount c j * (if e.val < c ^ (4 * c - 2 * t) then 1 else 0) else 0) := by
    split_ifs <;> positivity
  have hKpos : (0:ℝ) < (bigK c : ℝ) ^ t := by positivity
  have hKpos' : (0:ℝ) < (bigK c : ℝ) ^ (t - 1) := by positivity
  by_cases htop : e.val < c ^ (4 * c - 2 * t)
  · have hlev : valueLevel c t e.val = t := by
      apply sdl_valueLevel_eq_of c t _ hc
      rw [sdl_top_iff c t _ hc ht2]; exact htop
    have hval : hardInstance c t e = (bigK c : ℝ) ^ t := by
      unfold hardInstance; rw [hlev]; simp; omega
    rw [hval]
    have hfirst : 0 ≤ (c:ℝ)⁻¹ * (bigK c : ℝ) ^ (t - 1) * p := by positivity
    suffices hs : discount c j * p ≤
        ((if j.val < blockEnd c (t - 1) then
            discount c j * (if e.val < c ^ (4 * c - 2 * t) then 1 else 0) else 0)
         + ((c:ℝ) ^ t)⁻¹ * ((if j.val < blockEnd c t then p else 0)
              - (if j.val < blockEnd c (t - 1) then p else 0))
         + ((c:ℝ) ^ (t + 1))⁻¹ * p) by
      have := mul_le_mul_of_nonneg_left hs hKpos.le
      nlinarith
    rw [if_pos htop, mul_one]
    by_cases h1 : j.val < blockEnd c (t - 1)
    · have h2 : j.val < blockEnd c t := lt_of_lt_of_le h1 hmono
      rw [if_pos h1, if_pos h1, if_pos h2, sub_self, mul_zero, add_zero]
      have : discount c j * p ≤ discount c j := by nlinarith
      have : 0 ≤ ((c:ℝ) ^ (t + 1))⁻¹ * p := by positivity
      linarith
    · rw [if_neg h1, if_neg h1, sub_zero, zero_add]
      by_cases h2 : j.val < blockEnd c t
      · rw [if_pos h2]
        have hd : discount c j ≤ ((c:ℝ) ^ (t - 1 + 1))⁻¹ :=
          sdl_discount_le c hc j (t - 1) (by omega) (by unfold blockEnd at h1; omega)
        rw [show t - 1 + 1 = t by omega] at hd
        have : discount c j * p ≤ ((c:ℝ) ^ t)⁻¹ * p := mul_le_mul_of_nonneg_right hd hp0
        have : 0 ≤ ((c:ℝ) ^ (t + 1))⁻¹ * p := by positivity
        linarith
      · rw [if_neg h2, mul_zero, zero_add]
        have hd : discount c j ≤ ((c:ℝ) ^ (t + 1))⁻¹ :=
          sdl_discount_le c hc j t ht2 (by unfold blockEnd at h2; omega)
        exact mul_le_mul_of_nonneg_right hd hp0
  · have hlev : valueLevel c t e.val < t := by
      rcases lt_or_eq_of_le (sdl_valueLevel_le c t e.val) with h | h
      · exact h
      · exfalso; apply htop
        rw [← sdl_top_iff c t _ hc ht2]; exact sdl_valueLevel_eq_imp c t _ ht1 h
    have hv : hardInstance c t e ≤ (bigK c : ℝ) ^ (t - 1) := by
      unfold hardInstance
      split_ifs
      · positivity
      · exact pow_le_pow_right₀ hK (by omega)
    have hv0 := sdl_hardInstance_nonneg c t e
    have hdinv := sdl_discount_le_inv c hc j
    have h1 : discount c j * hardInstance c t e * p ≤ (c:ℝ)⁻¹ * (bigK c : ℝ) ^ (t - 1) * p := by
      apply mul_le_mul_of_nonneg_right _ hp0
      exact mul_le_mul hdinv hv hv0 (by positivity)
    have h2 : 0 ≤ (bigK c : ℝ) ^ t *
        ((if j.val < blockEnd c (t - 1) then
            discount c j * (if e.val < c ^ (4 * c - 2 * t) then 1 else 0) else 0)
         + ((c:ℝ) ^ t)⁻¹ * ((if j.val < blockEnd c t then p else 0)
              - (if j.val < blockEnd c (t - 1) then p else 0))
         + ((c:ℝ) ^ (t + 1))⁻¹ * p) := by
      have : 0 ≤ ((c:ℝ) ^ t)⁻¹ * ((if j.val < blockEnd c t then p else 0)
              - (if j.val < blockEnd c (t - 1) then p else 0)) := mul_nonneg (by positivity) hdiff
      have : 0 ≤ ((c:ℝ) ^ (t + 1))⁻¹ * p := by positivity
      positivity
    linarith


lemma sdl_ev_perm (c t : ℕ) (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c)
    (A : StoppingRule (horizon c)) (π : Equiv.Perm (Fin (horizon c))) :
    ∑ j : Fin (horizon c), discount c j * hardInstance c t (π j) *
        stopProb A (arrivalValues (hardInstance c t) π) j ≤
      (c:ℝ)⁻¹ * (bigK c : ℝ) ^ (t - 1) + (bigK c : ℝ) ^ t *
        (∑ j ∈ univ.filter (fun j : Fin (horizon c) => j.val < blockEnd c (t - 1)),
            discount c j * (if (π j).val < c ^ (4 * c - 2 * t) then 1 else 0)
         + ((c:ℝ) ^ t)⁻¹ *
            (∑ j ∈ univ.filter (fun j : Fin (horizon c) => j.val < blockEnd c t),
                stopProb A (arrivalValues (hardInstance c t) π) j
             - ∑ j ∈ univ.filter (fun j : Fin (horizon c) => j.val < blockEnd c (t - 1)),
                stopProb A (arrivalValues (hardInstance c t) π) j)
         + ((c:ℝ) ^ (t + 1))⁻¹) := by
  set h := arrivalValues (hardInstance c t) π
  have hsum1 := sdl_sum_univ_stopProb_le_one A h
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc
  have hK := sdl_bigK_ge_one c hc
  calc _ ≤ ∑ j : Fin (horizon c), ((c:ℝ)⁻¹ * (bigK c : ℝ) ^ (t - 1) * stopProb A h j + (bigK c : ℝ) ^ t *
        ((if j.val < blockEnd c (t - 1) then
            discount c j * (if (π j).val < c ^ (4 * c - 2 * t) then 1 else 0) else 0)
         + ((c:ℝ) ^ t)⁻¹ * ((if j.val < blockEnd c t then stopProb A h j else 0)
              - (if j.val < blockEnd c (t - 1) then stopProb A h j else 0))
         + ((c:ℝ) ^ (t + 1))⁻¹ * stopProb A h j)) := by
        apply sum_le_sum; intro j _
        exact sdl_ev_point c t hc ht1 ht2 j (π j) _ (sdl_stopProb_nonneg A h j)
          (sdl_stopProb_le_one A h j)
    _ = (c:ℝ)⁻¹ * (bigK c : ℝ) ^ (t - 1) * ∑ j, stopProb A h j + (bigK c : ℝ) ^ t *
        (∑ j ∈ univ.filter (fun j : Fin (horizon c) => j.val < blockEnd c (t - 1)),
            discount c j * (if (π j).val < c ^ (4 * c - 2 * t) then 1 else 0)
         + ((c:ℝ) ^ t)⁻¹ *
            (∑ j ∈ univ.filter (fun j : Fin (horizon c) => j.val < blockEnd c t), stopProb A h j
             - ∑ j ∈ univ.filter (fun j : Fin (horizon c) => j.val < blockEnd c (t - 1)),
                stopProb A h j)
         + ((c:ℝ) ^ (t + 1))⁻¹ * ∑ j, stopProb A h j) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, sum_add_distrib,
          ← mul_sum, ← mul_sum, sum_sub_distrib, sum_filter, sum_filter, sum_filter]
    _ ≤ _ := by
        have hp0 : 0 ≤ ∑ j, stopProb A h j := sum_nonneg fun j _ => sdl_stopProb_nonneg A h j
        have e1 : (c:ℝ)⁻¹ * (bigK c : ℝ) ^ (t - 1) * ∑ j, stopProb A h j ≤
            (c:ℝ)⁻¹ * (bigK c : ℝ) ^ (t - 1) :=
          mul_le_of_le_one_right (by positivity) hsum1
        have e2 : ((c:ℝ) ^ (t + 1))⁻¹ * ∑ j, stopProb A h j ≤ ((c:ℝ) ^ (t + 1))⁻¹ :=
          mul_le_of_le_one_right (by positivity) hsum1
        have hKt : (0:ℝ) ≤ (bigK c : ℝ) ^ t := by positivity
        have := mul_le_mul_of_nonneg_left e2 hKt
        nlinarith


lemma sdl_ev_bound (c t : ℕ) (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c)
    (A : StoppingRule (horizon c)) :
    expectedValue (discount c) (hardInstance c t) A ≤
      (bigK c : ℝ) ^ t * ((c:ℝ) ^ t)⁻¹ *
        (stopByProb (hardInstance c t) A (blockEnd c t)
          - stopByProb (hardInstance c t) A (blockEnd c (t - 1)) + 4 / c) := by
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc
  have hK := sdl_bigK_ge_one c hc
  have hnpos := sdl_horizon_pos c hc
  have hn' : (0:ℝ) < (horizon c : ℝ) := by exact_mod_cast hnpos
  have hN : (0:ℝ) < ((horizon c).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  set N : ℝ := ((horizon c).factorial : ℝ) with hNdef
  set F1 := univ.filter (fun j : Fin (horizon c) => j.val < blockEnd c (t - 1)) with hF1
  set Ft := univ.filter (fun j : Fin (horizon c) => j.val < blockEnd c t) with hFt
  set m := c ^ (4 * c - 2 * t) with hm
  set K : ℝ := (bigK c : ℝ) with hKdef
  let ind : Fin (horizon c) → ℝ := fun e => if e.val < m then 1 else 0
  have H1 := sum_le_sum (fun π (_ : π ∈ (univ : Finset (Equiv.Perm (Fin (horizon c)))))
    => sdl_ev_perm c t hc ht1 ht2 A π)
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    ← mul_sum, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const,
    card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at H1
  -- Z bound
  have hmn : m ≤ horizon c := by
    rw [sdl_horizon_split c t ht2]; exact Nat.le_mul_of_pos_left _ (pow_pos hc _)
  have havg : ∀ j : Fin (horizon c), ∑ π : Equiv.Perm (Fin (horizon c)), ind (π j)
      = N * ((c:ℝ) ^ (2 * t))⁻¹ := by
    intro j
    have := sdl_perm_avg j ind
    have hsg : ∑ e, ind e = (m : ℝ) := by
      simp only [ind, sum_boole]
      rw [Fin.card_filter_val_lt]
      simp [min_eq_right hmn]
    rw [hsg] at this
    have hsplit : (horizon c : ℝ) = (c:ℝ) ^ (2 * t) * m := by
      rw [sdl_horizon_split c t ht2, hm]; push_cast; ring
    rw [hsplit] at this
    have : (0:ℝ) < m := by exact_mod_cast pow_pos hc _
    have : (0:ℝ) < (c:ℝ) ^ (2 * t) := by positivity
    field_simp
    nlinarith
  have hZ : ∑ π : Equiv.Perm (Fin (horizon c)), ∑ j ∈ F1, discount c j * ind (π j)
      ≤ N * ((c:ℝ) ^ (2 * t))⁻¹ * (2 * (c:ℝ) ^ (t - 1)) := by
    rw [sum_comm]
    simp_rw [← mul_sum]
    rw [sum_congr rfl (fun j _ => by rw [havg j]), ← sum_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := sdl_S_bound c (t - 1) hc (by omega)
    rw [hF1]; unfold blockEnd; exact this
  -- arithmetic facts
  have f1 : (c:ℝ)⁻¹ * K ^ (t - 1) ≤ K ^ t * ((c:ℝ) ^ (t + 1))⁻¹ := by
    have hct : (c:ℝ) ^ t ≤ K := by
      rw [hKdef, bigK, horizon]; push_cast
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by exact_mod_cast hc) (by omega)
    have hKt : K ^ t = K ^ (t - 1) * K := by rw [← pow_succ]; congr 1; omega
    rw [hKt, pow_succ]
    have : (0:ℝ) < K ^ (t - 1) := by positivity
    rw [mul_inv, show (c:ℝ)⁻¹ * K ^ (t - 1) = K ^ (t - 1) * (c:ℝ)⁻¹ * 1 by ring,
      show K ^ (t - 1) * K * (((c:ℝ) ^ t)⁻¹ * (c:ℝ)⁻¹) = K ^ (t - 1) * (c:ℝ)⁻¹ * (K * ((c:ℝ) ^ t)⁻¹) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [le_mul_inv_iff₀ (by positivity)]; linarith
  have f2 : ((c:ℝ) ^ (2 * t))⁻¹ * (2 * (c:ℝ) ^ (t - 1)) = 2 * ((c:ℝ) ^ (t + 1))⁻¹ := by
    have : (c:ℝ) ^ (2 * t) = (c:ℝ) ^ (t - 1) * (c:ℝ) ^ (t + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  have f3 : ((c:ℝ) ^ (t + 1))⁻¹ = ((c:ℝ) ^ t)⁻¹ * (c:ℝ)⁻¹ := by rw [pow_succ, mul_inv]
  unfold expectedValue stopByProb
  simp only [one_div] at *
  rw [← hNdef] at *
  -- goal: N⁻¹ * ΣE ≤ K^t (c^t)⁻¹ (N⁻¹ ΣSt - N⁻¹ ΣS1 + 4/c)
  have hZ' := hZ
  rw [mul_assoc, f2] at hZ'
  have hKt0 : (0:ℝ) ≤ K ^ t := by positivity
  have key : ∑ π : Equiv.Perm (Fin (horizon c)), ∑ j, discount c j * hardInstance c t (π j) *
        stopProb A (arrivalValues (hardInstance c t) π) j ≤
      N * (K ^ t * ((c:ℝ) ^ t)⁻¹ * (4 / c)) + K ^ t * ((c:ℝ) ^ t)⁻¹ *
        (∑ π : Equiv.Perm (Fin (horizon c)), ∑ j ∈ Ft, stopProb A (arrivalValues (hardInstance c t) π) j
          - ∑ π : Equiv.Perm (Fin (horizon c)), ∑ j ∈ F1, stopProb A (arrivalValues (hardInstance c t) π) j) := by
    refine H1.trans ?_
    have g1 := mul_le_mul_of_nonneg_left f1 hN.le
    have g2 := mul_le_mul_of_nonneg_left hZ' hKt0
    rw [f3] at g1 g2 ⊢
    have : N * (K ^ t * ((c:ℝ) ^ t)⁻¹ * (4 / c)) = 4 * (N * (K ^ t * (((c:ℝ) ^ t)⁻¹ * (c:ℝ)⁻¹))) := by
      field_simp
    rw [this]
    nlinarith
  have hNinv : 0 < N⁻¹ := inv_pos.mpr hN
  have := mul_le_mul_of_nonneg_left key hNinv.le
  calc _ ≤ _ := this
    _ = _ := by field_simp; rw [hFt, hF1]; ring


lemma sdl_gain (c : ℕ) (hc : 1 ≤ c) (A : StoppingRule (horizon c))
    (hA : ∀ s : ℕ, 1 ≤ s → s ≤ 2 * c →
      expectedOPT (discount c) (hardInstance c s) ≤
        (c : ℝ) / 10 * expectedValue (discount c) (hardInstance c s) A)
    (t : ℕ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c) :
    2 / (c : ℝ) ≤ stopByProb (hardInstance c t) A (blockEnd c t)
          - stopByProb (hardInstance c t) A (blockEnd c (t - 1)) := by
  have h1 := sdl_opt_core c t hc ht1 ht2
  have h2 := hA t ht1 ht2
  have h3 := sdl_ev_bound c t hc ht1 ht2 A
  set D := stopByProb (hardInstance c t) A (blockEnd c t)
          - stopByProb (hardInstance c t) A (blockEnd c (t - 1))
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc
  have hK := sdl_bigK_ge_one c hc
  set V := (bigK c : ℝ) ^ t * ((c:ℝ) ^ t)⁻¹ with hV
  have hVpos : 0 < V := by positivity
  have he : Real.exp 1 > 2.7182818283 := Real.exp_one_gt_d9
  have hinv : 1 / Real.exp 1 < 0.37 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  have h4 : (1 - 1 / Real.exp 1) * V ≤ (c:ℝ) / 10 * (V * (D + 4 / c)) := by
    have : (c:ℝ) / 10 * expectedValue (discount c) (hardInstance c t) A ≤ (c:ℝ) / 10 * (V * (D + 4 / c)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h1' : (1 - 1 / Real.exp 1) * V = (1 - 1 / Real.exp 1) * (bigK c : ℝ) ^ t * ((c : ℝ) ^ t)⁻¹ := by
      rw [hV]; ring
    linarith
  have h5 : (1 - 1 / Real.exp 1) ≤ (c:ℝ) / 10 * (D + 4 / c) := by
    have : (c:ℝ) / 10 * (V * (D + 4 / c)) = V * ((c:ℝ) / 10 * (D + 4 / c)) := by ring
    rw [this, mul_comm (1 - 1 / Real.exp 1)] at h4
    exact le_of_mul_le_mul_left h4 hVpos
  have h6 : (c:ℝ) / 10 * (D + 4 / c) = c * D / 10 + 2 / 5 := by field_simp; ring
  rw [h6] at h5
  rw [div_le_iff₀ hcpos]
  nlinarith

lemma sdl_comp_core (c : ℕ) (hc : 1 ≤ c) (A : StoppingRule (horizon c))
    (hA : ∀ s : ℕ, 1 ≤ s → s ≤ 2 * c →
      expectedOPT (discount c) (hardInstance c s) ≤
        (c : ℝ) / 10 * expectedValue (discount c) (hardInstance c s) A)
    (t : ℕ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c) :
    (t : ℝ) / c ≤ stopByProb (hardInstance c t) A (blockEnd c t) := by
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc
  induction t with
  | zero => omega
  | succ t ih =>
    have hg := sdl_gain c hc A hA (t + 1) (by omega) ht2
    simp only [Nat.add_sub_cancel] at hg
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      have : 0 ≤ stopByProb (hardInstance c (0 + 1)) A (blockEnd c 0) := by
        unfold stopByProb
        apply mul_nonneg (by positivity)
        exact sum_nonneg fun π _ => sum_nonneg fun j _ => sdl_stopProb_nonneg A _ j
      have h2 : (((0 + 1 : ℕ) : ℝ)) / c ≤ 2 / c := by
        apply div_le_div_of_nonneg_right _ hcpos.le; norm_num
      linarith
    · have ih' := ih hpos (by omega)
      have hcp := sdl_coupling_core c t hc hpos (by omega) A
      have : (1:ℝ) / (c:ℝ) ^ 2 ≤ 1 / c := by
        apply one_div_le_one_div_of_le hcpos
        have : (1:ℝ) ≤ c := by exact_mod_cast hc
        nlinarith
      have h3 : ((t + 1 : ℕ) : ℝ) / c = t / c + 1 / c := by push_cast; ring
      have h4 : (2:ℝ) / c = 1 / c + 1 / c := by ring
      linarith

end SecretaryWD.DiscLower

open SecretaryWD.DiscLower


theorem solution (c : ℕ) (hc : 1 ≤ c) (A : StoppingRule (horizon c))
    (hA : ∀ s : ℕ, 1 ≤ s → s ≤ 2 * c →
      expectedOPT (discount c) (hardInstance c s) ≤
        (c : ℝ) / 10 * expectedValue (discount c) (hardInstance c s) A)
    (t : ℕ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c) :
    (t : ℝ) / c ≤ stopByProb (hardInstance c t) A (blockEnd c t) := by
  exact sdl_comp_core c hc A hA t ht1 ht2
