-- Prove2me | solution 1 for SecretaryAdvice.Samples.theorem_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T01:31:01.470509+00:00
-- url     : https://prove2.me/submissions/6b682b78-ad4a-457a-971d-c3a7d1e2ccc2

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting


set_option autoImplicit false

open Finset

namespace SS16

/-! ## Part A: the analytic (dynamic-programming) part -/

/-- `fr n k i s = P(top | T_i, s_i = s)` (0-based round `i`). -/
noncomputable def fr (n k i s : ℕ) : ℝ := ∏ l ∈ Ioo i n, ((s:ℝ) + l) / ((k:ℝ) + l + 1)

noncomputable def rr (n j s' s : ℕ) : ℝ := ∏ l ∈ Ioo j n, ((s':ℝ) + l) / ((s:ℝ) + l)

noncomputable def cc (n k j s : ℕ) : ℝ := (1 / ((s:ℝ) + j)) * ∑ s' ∈ Icc s k, rr n j s' s

noncomputable def hh (n k i s : ℕ) : ℝ := ∑ j ∈ Ioo i n, cc n k j s

noncomputable def gg (n k i s : ℕ) : ℝ := fr n k i s * hh n k i s

/-- The Bellman continuation value after round `i` when the best online secretary so far has
`m` samples below it. -/
noncomputable def WW (n k : ℕ) (i m : ℕ) : ℝ :=
  if i + 1 < n then
    (((m:ℝ) + i + 1) * WW n k (i+1) m +
      ∑ s' ∈ Icc m k, max (fr n k (i+1) s') (WW n k (i+1) s')) / ((k:ℝ) + i + 2)
  else 0
termination_by n - i

lemma WW_succ (n k i m : ℕ) (h : i + 1 < n) :
    WW n k i m = (((m:ℝ) + i + 1) * WW n k (i+1) m +
      ∑ s' ∈ Icc m k, max (fr n k (i+1) s') (WW n k (i+1) s')) / ((k:ℝ) + i + 2) := by
  rw [WW, if_pos h]

lemma WW_last (n k i m : ℕ) (h : ¬ i + 1 < n) : WW n k i m = 0 := by
  rw [WW, if_neg h]

lemma back_ind (n : ℕ) (P : ℕ → Prop) (hlast : ∀ i, ¬ i + 1 < n → P i)
    (hstep : ∀ i, i + 1 < n → P (i+1) → P i) : ∀ i, P i := by
  have : ∀ d i, n - i ≤ d → P i := by
    intro d
    induction d with
    | zero => intro i hi; exact hlast i (by omega)
    | succ d ih =>
      intro i hi
      by_cases h : i + 1 < n
      · exact hstep i h (ih (i+1) (by omega))
      · exact hlast i h
  intro i; exact this _ i le_rfl

lemma Ioo_succ (i n : ℕ) (h : i + 1 < n) : Ioo i n = insert (i+1) (Ioo (i+1) n) := by
  ext x; simp only [mem_Ioo, mem_insert]; omega

lemma Ioo_empty (i n : ℕ) (h : ¬ i + 1 < n) : Ioo i n = ∅ := by
  ext x; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega

lemma fr_succ (n k i s : ℕ) (h : i + 1 < n) :
    fr n k i s = (((s:ℝ) + i + 1) / ((k:ℝ) + i + 2)) * fr n k (i+1) s := by
  unfold fr
  rw [Ioo_succ i n h, prod_insert (by simp)]
  congr 1
  push_cast; ring_nf

lemma fr_last (n k i s : ℕ) (h : ¬ i + 1 < n) : fr n k i s = 1 := by
  unfold fr; rw [Ioo_empty i n h]; simp

lemma fr_pos (n k i s : ℕ) : 0 < fr n k i s := by
  unfold fr
  apply prod_pos
  intro l hl
  have : 1 ≤ l := by simp at hl; omega
  have : (1:ℝ) ≤ l := by exact_mod_cast this
  apply div_pos <;> positivity

lemma rr_nonneg (n j s' s : ℕ) : 0 ≤ rr n j s' s := by
  unfold rr; apply prod_nonneg; intro l _; positivity

lemma cc_nonneg (n k j s : ℕ) : 0 ≤ cc n k j s := by
  unfold cc
  apply mul_nonneg
  · positivity
  · exact sum_nonneg (fun _ _ => rr_nonneg _ _ _ _)

lemma hh_succ (n k i s : ℕ) (h : i + 1 < n) : hh n k i s = cc n k (i+1) s + hh n k (i+1) s := by
  unfold hh; rw [Ioo_succ i n h, sum_insert (by simp)]

lemma hh_last (n k i s : ℕ) (h : ¬ i + 1 < n) : hh n k i s = 0 := by
  unfold hh; rw [Ioo_empty i n h]; simp

lemma hh_nonneg (n k i s : ℕ) : 0 ≤ hh n k i s := by
  unfold hh; exact sum_nonneg (fun _ _ => cc_nonneg _ _ _ _)

lemma hh_anti_i (n k i s : ℕ) : hh n k (i+1) s ≤ hh n k i s := by
  by_cases h : i + 1 < n
  · rw [hh_succ n k i s h]; linarith [cc_nonneg n k (i+1) s]
  · rw [hh_last n k i s h, hh_last n k (i+1) s (by omega)]

lemma rr_anti (n j s' s : ℕ) (hj : 0 ≤ j) : rr n j s' (s+1) ≤ rr n j s' s := by
  unfold rr
  apply prod_le_prod
  · intro l _; positivity
  · intro l hl
    have : 1 ≤ l := by simp at hl; omega
    have hl1 : (1:ℝ) ≤ l := by exact_mod_cast this
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    push_cast; linarith

lemma cc_anti (n k j s : ℕ) (hj : 1 ≤ j) : cc n k j (s+1) ≤ cc n k j s := by
  unfold cc
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj
  have h1 : ∑ s' ∈ Icc (s+1) k, rr n j s' (s+1) ≤ ∑ s' ∈ Icc s k, rr n j s' s := by
    calc ∑ s' ∈ Icc (s+1) k, rr n j s' (s+1) ≤ ∑ s' ∈ Icc (s+1) k, rr n j s' s :=
          sum_le_sum (fun s' _ => rr_anti n j s' s (Nat.zero_le _))
      _ ≤ ∑ s' ∈ Icc s k, rr n j s' s := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx; simp at hx ⊢; omega
          · intro _ _ _; exact rr_nonneg _ _ _ _
  apply mul_le_mul _ h1 (sum_nonneg (fun _ _ => rr_nonneg _ _ _ _)) (by positivity)
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  push_cast; linarith

lemma hh_anti_s1 (n k i s : ℕ) : hh n k i (s+1) ≤ hh n k i s := by
  unfold hh
  apply sum_le_sum
  intro j hj
  simp at hj
  exact cc_anti n k j s (by omega)

lemma hh_anti_s (n k i : ℕ) : ∀ s t, s ≤ t → hh n k i t ≤ hh n k i s := by
  intro s t hst
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact le_trans (hh_anti_s1 n k i t) ih

lemma fr_rr (n k j s s' : ℕ) : fr n k j s * rr n j s' s = fr n k j s' := by
  unfold fr rr
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro l hl
  have : 1 ≤ l := by simp at hl; omega
  have hl1 : (1:ℝ) ≤ l := by exact_mod_cast this
  have h1 : (0:ℝ) < (s:ℝ) + l := by positivity
  have h2 : (0:ℝ) < (k:ℝ) + l + 1 := by positivity
  field_simp

lemma gg_succ (n k i m : ℕ) (h : i + 1 < n) :
    gg n k i m = (((m:ℝ) + i + 1) * gg n k (i+1) m +
      ∑ s' ∈ Icc m k, fr n k (i+1) s') / ((k:ℝ) + i + 2) := by
  unfold gg
  rw [hh_succ n k i m h, fr_succ n k i m h]
  unfold cc
  have hpos : (0:ℝ) < (m:ℝ) + ((i+1 : ℕ) : ℝ) := by push_cast; positivity
  have hk : (0:ℝ) < (k:ℝ) + i + 2 := by positivity
  have e : ∑ s' ∈ Icc m k, fr n k (i+1) s' = fr n k (i+1) m * ∑ s' ∈ Icc m k, rr n (i+1) s' m := by
    rw [mul_sum]; apply sum_congr rfl; intro s' _; rw [fr_rr]
  rw [e]
  have : ((m:ℝ) + ((i+1:ℕ):ℝ)) = (m:ℝ) + i + 1 := by push_cast; ring
  rw [this] at hpos ⊢
  field_simp
  ring

lemma gg_last (n k i m : ℕ) (h : ¬ i + 1 < n) : gg n k i m = 0 := by
  unfold gg; rw [hh_last n k i m h]; simp

lemma WW_nonneg (n k : ℕ) : ∀ i m, 0 ≤ WW n k i m := by
  intro i
  induction i using back_ind n with
  | hlast i h => intro m; rw [WW_last n k i m h]
  | hstep i h ih =>
    intro m
    rw [WW_succ n k i m h]
    apply div_nonneg _ (by positivity)
    apply add_nonneg
    · exact mul_nonneg (by positivity) (ih m)
    · exact sum_nonneg (fun s' _ => le_trans (ih s') (le_max_right _ _))

lemma gg_le_WW (n k : ℕ) : ∀ i m, gg n k i m ≤ WW n k i m := by
  intro i
  induction i using back_ind n with
  | hlast i h => intro m; rw [WW_last n k i m h, gg_last n k i m h]
  | hstep i h ih =>
    intro m
    rw [WW_succ n k i m h, gg_succ n k i m h]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (ih m) (by positivity)
    · exact sum_le_sum (fun s' _ => le_max_left _ _)

lemma WW_eq_gg (n k : ℕ) : ∀ i m, hh n k i m ≤ 1 → WW n k i m = gg n k i m := by
  intro i
  induction i using back_ind n with
  | hlast i h => intro m _; rw [WW_last n k i m h, gg_last n k i m h]
  | hstep i h ih =>
    intro m hm
    rw [WW_succ n k i m h, gg_succ n k i m h]
    have h1 : hh n k (i+1) m ≤ 1 := le_trans (hh_anti_i n k i m) hm
    rw [ih m h1]
    congr 2
    apply sum_congr rfl
    intro s' hs'
    simp at hs'
    have h2 : hh n k (i+1) s' ≤ 1 := le_trans (hh_anti_s n k (i+1) m s' hs'.1) h1
    rw [ih s' h2]
    apply max_eq_left
    unfold gg
    have := fr_pos n k (i+1) s'
    nlinarith

lemma stop_iff (n k i s : ℕ) : WW n k i s ≤ fr n k i s ↔ hh n k i s ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h1 := gg_le_WW n k i s
    unfold gg at h1
    have := fr_pos n k i s
    nlinarith
  · intro h
    rw [WW_eq_gg n k i s h]
    unfold gg
    have := fr_pos n k i s
    nlinarith

lemma stop_mono (n k s : ℕ) : ∀ i j, i ≤ j → WW n k i s ≤ fr n k i s → WW n k j s ≤ fr n k j s := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact id
  | succ j _ ih =>
    intro h
    have h2 := ih h
    rw [stop_iff] at h2 ⊢
    exact le_trans (hh_anti_i n k j s) h2

lemma stop_exists (n k s : ℕ) (hn : 1 ≤ n) : ∃ i, WW n k i s ≤ fr n k i s := by
  refine ⟨n - 1, ?_⟩
  rw [WW_last n k (n-1) s (by omega)]
  exact le_of_lt (fr_pos _ _ _ _)

open Classical in
/-- The optimal thresholds (1-based). -/
noncomputable def thr (n k : ℕ) (s : ℕ) : ℕ :=
  if h : ∃ i, WW n k i s ≤ fr n k i s then Nat.find h + 1 else 1

lemma thr_iff (n k : ℕ) (hn : 1 ≤ n) (s i : ℕ) :
    thr n k s ≤ i + 1 ↔ WW n k i s ≤ fr n k i s := by
  classical
  have hex := stop_exists n k s hn
  unfold thr
  rw [dif_pos hex]
  constructor
  · intro h
    exact stop_mono n k s _ _ (by omega) (Nat.find_spec hex)
  · intro h
    have := Nat.find_min' hex h
    omega

lemma thr_valid (n k : ℕ) (hn : 1 ≤ n) (s : ℕ) : 1 ≤ thr n k s ∧ thr n k s ≤ n := by
  classical
  have hex := stop_exists n k s hn
  constructor
  · unfold thr; rw [dif_pos hex]; omega
  · have h : WW n k (n-1) s ≤ fr n k (n-1) s := by
      rw [WW_last n k (n-1) s (by omega)]; exact le_of_lt (fr_pos _ _ _ _)
    have := (thr_iff n k hn s (n-1)).2 h
    omega

end SS16


set_option autoImplicit false

open Finset
open SecretaryAdvice.Samples

namespace SS16

/-! ## Part B: permutations, insertion, information -/

/-- the value (rank) of position `p` as a natural number -/
def vv {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : ℕ) : ℕ := if h : p < N then (σ ⟨p, h⟩).val else 0

lemma vv_lt {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : ℕ) (hp : p < N) : vv σ p < N := by
  unfold vv; rw [dif_pos hp]; exact (σ _).isLt

lemma vv_inj {N : ℕ} (σ : Equiv.Perm (Fin N)) (p p' : ℕ) (hp : p < N) (hp' : p' < N)
    (h : vv σ p = vv σ p') : p = p' := by
  unfold vv at h; rw [dif_pos hp, dif_pos hp'] at h
  have := σ.injective (Fin.ext h)
  simpa using this

/-- insert value `v` at the last position -/
def insFun {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) : Fin (m+1) → Fin (m+1) :=
  Fin.lastCases v (fun k => v.succAbove (σ k))

@[simp] lemma insFun_last {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) :
    insFun v σ (Fin.last m) = v := by simp [insFun]

@[simp] lemma insFun_castSucc {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    insFun v σ (Fin.castSucc k) = v.succAbove (σ k) := by simp [insFun]

lemma insFun_inj {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) :
    Function.Injective (insFun v σ) := by
  intro x y hxy
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast k =>
      simp at hxy
  | cast k =>
    induction y using Fin.lastCases with
    | last =>
      simp at hxy
    | cast l =>
      simp at hxy
      rw [hxy]

noncomputable def ins {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m+1)) :=
  Equiv.ofBijective (insFun v σ) ((Finite.injective_iff_bijective).1 (insFun_inj v σ))

@[simp] lemma ins_apply {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) (x : Fin (m+1)) :
    ins v σ x = insFun v σ x := rfl

lemma ins_bij (m : ℕ) : Function.Bijective (fun x : Fin (m+1) × Equiv.Perm (Fin m) => ins x.1 x.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨v, σ⟩ ⟨v', σ'⟩ h
    simp only at h
    have hv : v = v' := by
      have := congrArg (fun π : Equiv.Perm (Fin (m+1)) => π (Fin.last m)) h
      simpa using this
    subst hv
    have hσ : σ = σ' := by
      ext k
      have := congrArg (fun π : Equiv.Perm (Fin (m+1)) => π (Fin.castSucc k)) h
      simp only [ins_apply, insFun_castSucc] at this
      rw [Fin.succAbove_right_inj] at this
      rw [this]
    rw [hσ]
  · simp [Fintype.card_perm, Nat.factorial_succ]

lemma sum_perm_succ {m : ℕ} (F : Equiv.Perm (Fin (m+1)) → ℝ) :
    ∑ π, F π = ∑ v : Fin (m+1), ∑ σ : Equiv.Perm (Fin m), F (ins v σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (ins_bij m) _ _ (fun x => rfl)).symm

lemma vv_ins {m : ℕ} (v : Fin (m+1)) (ρ : Equiv.Perm (Fin m)) (p : ℕ) (hp : p < m) :
    vv (ins v ρ) p = (v.succAbove (ρ ⟨p, hp⟩)).val := by
  unfold vv
  rw [dif_pos (by omega)]
  have : (⟨p, by omega⟩ : Fin (m+1)) = Fin.castSucc ⟨p, hp⟩ := rfl
  rw [this, ins_apply, insFun_castSucc]

lemma vv_ins_last {m : ℕ} (v : Fin (m+1)) (ρ : Equiv.Perm (Fin m)) :
    vv (ins v ρ) m = v.val := by
  unfold vv
  rw [dif_pos (by omega)]
  have : (⟨m, by omega⟩ : Fin (m+1)) = Fin.last m := rfl
  rw [this, ins_apply, insFun_last]

lemma vv_ins_lt_iff {m : ℕ} (v : Fin (m+1)) (ρ : Equiv.Perm (Fin m)) (p p' : ℕ)
    (hp : p < m) (hp' : p' < m) : vv (ins v ρ) p < vv (ins v ρ) p' ↔ vv ρ p < vv ρ p' := by
  rw [vv_ins v ρ p hp, vv_ins v ρ p' hp']
  unfold vv; rw [dif_pos hp, dif_pos hp']
  rw [← Fin.lt_def, Fin.succAbove_lt_succAbove_iff, Fin.lt_def]

lemma vv_ins_le_iff {m : ℕ} (v : Fin (m+1)) (ρ : Equiv.Perm (Fin m)) (p p' : ℕ)
    (hp : p < m) (hp' : p' < m) : vv (ins v ρ) p ≤ vv (ins v ρ) p' ↔ vv ρ p ≤ vv ρ p' := by
  rw [← not_lt, ← not_lt, vv_ins_lt_iff v ρ p' p hp' hp]

lemma succAbove_lt_iff' {m : ℕ} (v : Fin (m+1)) (y : Fin m) :
    (v.succAbove y).val < v.val ↔ y.val < v.val := by
  rcases lt_or_ge (Fin.castSucc y) v with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    simp only [Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ h]
    have : v.val ≤ y.val := h
    simp only [Fin.val_succ]
    omega

lemma vv_ins_lt_new {m : ℕ} (v : Fin (m+1)) (ρ : Equiv.Perm (Fin m)) (p : ℕ) (hp : p < m) :
    vv (ins v ρ) p < v.val ↔ vv ρ p < v.val := by
  rw [vv_ins v ρ p hp, succAbove_lt_iff' v]
  unfold vv; rw [dif_pos hp]

lemma vv_ins_new_le {m : ℕ} (v : Fin (m+1)) (ρ : Equiv.Perm (Fin m)) (p : ℕ) (hp : p < m) :
    v.val ≤ vv (ins v ρ) p ↔ v.val ≤ vv ρ p := by
  rw [← not_lt, ← not_lt, vv_ins_lt_new v ρ p hp]

/-- information at round `i` (relative order of the first `k + i + 1` positions) -/
def infoN {N : ℕ} (k i : ℕ) (σ : Equiv.Perm (Fin N)) : Info k i :=
  fun a b => decide (vv σ a.val < vv σ b.val)

lemma infoN_ins {m : ℕ} (k i : ℕ) (h : k + i + 1 ≤ m) (v : Fin (m+1)) (ρ : Equiv.Perm (Fin m)) :
    infoN k i (ins v ρ) = infoN k i ρ := by
  funext a b
  unfold infoN
  rw [decide_eq_decide]
  exact vv_ins_lt_iff v ρ _ _ (by omega) (by omega)

/-- the number of samples below the best online secretary so far -/
def infoMax {k i : ℕ} (x : Info k i) : ℕ :=
  (univ.filter fun a : Fin k => ∃ b : Fin (k + i + 1), k ≤ b.val ∧
    x (Fin.castLE (by omega) a) b = true).card

/-! ### counting lemmas -/

lemma card_fin_filter (L : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter (fun p : Fin L => P p.val)).card = ((range L).filter P).card := by
  rw [← card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
  · rintro ⟨hx, hP⟩; exact ⟨⟨x, hx⟩, hP, rfl⟩

lemma cnt_lt {L : ℕ} (σ : Equiv.Perm (Fin L)) (t : ℕ) (ht : t ≤ L) :
    ((range L).filter (fun p => vv σ p < t)).card = t := by
  have e : (range L).filter (fun p => vv σ p < t) =
      (range L).filter (fun p => if h : p < L then (σ ⟨p, h⟩).val < t else False) := by
    apply filter_congr
    intro p hp
    simp at hp
    unfold vv; rw [dif_pos hp, dif_pos hp]
  rw [e]
  rw [← card_fin_filter L (fun p => if h : p < L then (σ ⟨p, h⟩).val < t else False)]
  have e2 : (univ.filter (fun p : Fin L => if h : p.val < L then (σ ⟨p.val, h⟩).val < t else False))
      = univ.filter (fun p : Fin L => (σ p).val < t) := by
    apply filter_congr; intro p _; rw [dif_pos p.isLt]
  rw [e2]
  have e3 : univ.filter (fun p : Fin L => (σ p).val < t) =
      (univ.filter (fun y : Fin L => y.val < t)).map σ.symm.toEmbedding := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply]
    constructor
    · intro h; exact ⟨σ p, h, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [e3, card_map, card_fin_filter L (fun y => y < t)]
  have : (range L).filter (fun y => y < t) = range t := by
    ext y; simp; omega
  rw [this, card_range]

lemma cnt_split {L : ℕ} (k : ℕ) (hk : k ≤ L) (P : ℕ → Prop) [DecidablePred P] :
    ((range L).filter P).card = ((range k).filter P).card + ((Ico k L).filter P).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext x
    simp only [mem_union, mem_filter, mem_range, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hx : x < k
      · left; exact ⟨hx, h2⟩
      · right; exact ⟨⟨by omega, h1⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h3⟩, h2⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨h3, h2⟩
  · rw [disjoint_left]; intro x hx hx'; simp at hx hx'; omega

lemma card_Ico_erase (k L c : ℕ) (hc : k ≤ c) (hcL : c < L) : ((Ico k L).erase c).card = L - k - 1 := by
  rw [card_erase_of_mem (by simp; omega), Nat.card_Ico]

/-! ### statistics in terms of `vv` -/

lemma bsf_iff {N : ℕ} (k i : ℕ) (σ : Equiv.Perm (Fin N)) :
    infoBestSoFar (infoN k i σ) = true ↔ ∀ p, k ≤ p → p < k + i → vv σ p < vv σ (k + i) := by
  unfold infoBestSoFar infoN infoCur
  simp only [decide_eq_true_eq, Fin.val_last]
  constructor
  · intro h p hp1 hp2
    exact h ⟨p, by omega⟩ hp1 hp2
  · intro h b hb1 hb2
    exact h b.val hb1 hb2

lemma sig_eq {N : ℕ} (k i : ℕ) (σ : Equiv.Perm (Fin N)) :
    infoSignal (infoN k i σ) = ((range k).filter (fun a => vv σ a < vv σ (k + i))).card := by
  unfold infoSignal infoN infoCur
  simp only [decide_eq_true_eq, Fin.val_last, Fin.val_castLE]
  exact card_fin_filter k (fun a => vv σ a < vv σ (k + i))

lemma max_eq {N : ℕ} (k i : ℕ) (σ : Equiv.Perm (Fin N)) :
    infoMax (infoN k i σ) =
      ((range k).filter (fun a => ∃ p ∈ Icc k (k + i), vv σ a < vv σ p)).card := by
  unfold infoMax infoN
  simp only [decide_eq_true_eq, Fin.val_castLE]
  rw [← card_fin_filter k (fun a => ∃ p ∈ Icc k (k + i), vv σ a < vv σ p)]
  congr 1
  apply filter_congr
  intro a _
  simp only [mem_Icc]
  constructor
  · rintro ⟨b, hb1, hb2⟩; exact ⟨b.val, ⟨hb1, by omega⟩, hb2⟩
  · rintro ⟨p, ⟨hp1, hp2⟩, hp3⟩; exact ⟨⟨p, by omega⟩, hp1, hp3⟩

lemma max_eq_sig {N : ℕ} (k i : ℕ) (σ : Equiv.Perm (Fin N))
    (h : infoBestSoFar (infoN k i σ) = true) :
    infoMax (infoN k i σ) = infoSignal (infoN k i σ) := by
  rw [max_eq, sig_eq]
  rw [bsf_iff] at h
  congr 1
  apply filter_congr
  intro a _
  simp only [mem_Icc]
  constructor
  · rintro ⟨p, ⟨hp1, hp2⟩, hp3⟩
    rcases lt_or_eq_of_le hp2 with hp | hp
    · exact lt_trans hp3 (h p hp1 hp)
    · rw [hp] at hp3; exact hp3
  · intro ha; exact ⟨k + i, ⟨by omega, le_rfl⟩, ha⟩

end SS16


set_option autoImplicit false

open Finset
open SecretaryAdvice.Samples

namespace SS16

/-! ## Part C: the two conditioning identities -/

lemma map_fin_filter (L : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter (fun p : Fin L => P p.val)).map Fin.valEmbedding = (range L).filter P := by
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
  · rintro ⟨hx, hP⟩; exact ⟨⟨x, hx⟩, hP, rfl⟩

lemma sum_fin_filter (L : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ) :
    ∑ v ∈ univ.filter (fun v : Fin L => P v.val), f v.val = ∑ x ∈ (range L).filter P, f x := by
  rw [← map_fin_filter, sum_map]; rfl

lemma card_fin_le (m c : ℕ) (hc : c < m) :
    (univ.filter (fun v : Fin m => v.val ≤ c)).card = c + 1 := by
  rw [card_fin_filter m (fun v => v ≤ c)]
  have : (range m).filter (fun v => v ≤ c) = range (c+1) := by ext x; simp; omega
  rw [this, card_range]

/-- `top` for a general number of positions -/
def topN {N : ℕ} (k i : ℕ) (σ : Equiv.Perm (Fin N)) : Prop :=
  ∀ p ∈ Ico k N, vv σ p ≤ vv σ (k + i)

instance {N : ℕ} (k i : ℕ) (σ : Equiv.Perm (Fin N)) : Decidable (topN k i σ) := by
  unfold topN; infer_instance

lemma topN_ins {m : ℕ} (k i : ℕ) (h : k + i < m) (v : Fin (m+1)) (ρ : Equiv.Perm (Fin m)) :
    topN k i (ins v ρ) ↔ topN k i ρ ∧ v.val ≤ vv ρ (k + i) := by
  unfold topN
  simp only [mem_Ico]
  constructor
  · intro H
    refine ⟨fun p hp => ?_, ?_⟩
    · have := H p ⟨hp.1, by omega⟩
      rwa [vv_ins_le_iff v ρ p (k+i) hp.2 h] at this
    · have := H m ⟨by omega, by omega⟩
      rw [vv_ins_last] at this
      rwa [vv_ins_new_le v ρ (k+i) h] at this
  · rintro ⟨H, hv⟩ p ⟨hp1, hp2⟩
    by_cases hp : p < m
    · rw [vv_ins_le_iff v ρ p (k+i) hp h]; exact H p ⟨hp1, hp⟩
    · have e : p = m := by omega
      rw [e, vv_ins_last, vv_ins_new_le v ρ (k+i) h]; exact hv

lemma top_count {m : ℕ} (k i : ℕ) (h : k + i < m) (ρ : Equiv.Perm (Fin m)) (htop : topN k i ρ) :
    vv ρ (k + i) = infoSignal (infoN k i ρ) + (m - k - 1) := by
  have h1 := cnt_lt ρ (vv ρ (k+i)) (le_of_lt (vv_lt ρ _ h))
  rw [cnt_split k (by omega)] at h1
  rw [sig_eq]
  have h2 : (Ico k m).filter (fun p => vv ρ p < vv ρ (k+i)) = (Ico k m).erase (k+i) := by
    ext p
    simp only [mem_filter, mem_Ico, mem_erase]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, h1, h2⟩
      rintro rfl; exact lt_irrefl _ h3
    · rintro ⟨hne, h1, h2⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      have := htop p (by simp; omega)
      rcases lt_or_eq_of_le this with h' | h'
      · exact h'
      · exact absurd (vv_inj ρ _ _ h2 h h') hne
  rw [h2, card_Ico_erase k m (k+i) (by omega) h] at h1
  omega

lemma fr_succN (k i m s : ℕ) (h : k + i + 1 ≤ m) :
    ((m:ℝ) + 1) * fr (m + 1 - k) k i s = fr (m - k) k i s * ((s:ℝ) + ((m - k : ℕ) : ℝ)) := by
  unfold fr
  have e : Ioo i (m + 1 - k) = insert (m - k) (Ioo i (m - k)) := by
    ext x; simp only [mem_Ioo, mem_insert]; omega
  rw [e, prod_insert (by simp)]
  have hk : ((m - k : ℕ) : ℝ) = (m:ℝ) - k := by rw [Nat.cast_sub (by omega)]
  rw [hk]
  have : (k:ℝ) + ((m:ℝ) - k) + 1 = (m:ℝ) + 1 := by ring
  rw [this]
  have hm : (0:ℝ) < (m:ℝ) + 1 := by positivity
  field_simp

/-- Conditioning identity (T1): `P(top | info at round i) = [T_i] · f(i, s_i)`. -/
lemma T1 (k i : ℕ) : ∀ N, k + i + 1 ≤ N → ∀ G : Info k i → ℝ,
    ∑ σ : Equiv.Perm (Fin N), G (infoN k i σ) * (if topN k i σ then 1 else 0) =
    ∑ σ : Equiv.Perm (Fin N), G (infoN k i σ) *
      (if infoBestSoFar (infoN k i σ) = true then fr (N - k) k i (infoSignal (infoN k i σ)) else 0) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    intro G
    apply sum_congr rfl
    intro σ _
    have hiff : topN k i σ ↔ infoBestSoFar (infoN k i σ) = true := by
      rw [bsf_iff]
      unfold topN
      simp only [mem_Ico]
      constructor
      · intro H p hp1 hp2
        have := H p ⟨hp1, by omega⟩
        rcases lt_or_eq_of_le this with h' | h'
        · exact h'
        · have := vv_inj σ _ _ (by omega) (by omega) h'; omega
      · rintro H p ⟨hp1, hp2⟩
        by_cases hp : p < k + i
        · exact le_of_lt (H p hp1 hp)
        · have : p = k + i := by omega
          rw [this]
    rw [fr_last _ k i _ (by omega)]
    by_cases hb : infoBestSoFar (infoN k i σ) = true
    · rw [if_pos (hiff.2 hb), if_pos hb]
    · rw [if_neg (fun h => hb (hiff.1 h)), if_neg hb]
  | succ m hm ih =>
    intro G
    rw [sum_perm_succ, sum_perm_succ]
    have hL : ∀ v : Fin (m+1), ∀ ρ : Equiv.Perm (Fin m),
        G (infoN k i (ins v ρ)) * (if topN k i (ins v ρ) then 1 else 0) =
        G (infoN k i ρ) * (if topN k i ρ ∧ v.val ≤ vv ρ (k + i) then 1 else 0) := by
      intro v ρ
      rw [infoN_ins k i hm v ρ]
      congr 1
      exact if_congr (topN_ins k i (by omega) v ρ) rfl rfl
    simp only [hL]
    rw [sum_comm]
    have hR : ∀ v : Fin (m+1), ∀ ρ : Equiv.Perm (Fin m),
        G (infoN k i (ins v ρ)) * (if infoBestSoFar (infoN k i (ins v ρ)) = true then
          fr (m + 1 - k) k i (infoSignal (infoN k i (ins v ρ))) else 0) =
        G (infoN k i ρ) * (if infoBestSoFar (infoN k i ρ) = true then
          fr (m + 1 - k) k i (infoSignal (infoN k i ρ)) else 0) := by
      intro v ρ
      rw [infoN_ins k i hm v ρ]
    simp only [hR, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcount : ∀ ρ : Equiv.Perm (Fin m),
        ∑ v : Fin (m+1), G (infoN k i ρ) * (if topN k i ρ ∧ v.val ≤ vv ρ (k + i) then (1:ℝ) else 0) =
        (G (infoN k i ρ) * ((infoSignal (infoN k i ρ) : ℝ) + ((m - k : ℕ) : ℝ))) *
          (if topN k i ρ then 1 else 0) := by
      intro ρ
      rw [← mul_sum]
      by_cases ht : topN k i ρ
      · simp only [ht, true_and, if_true, mul_one]
        rw [sum_boole, card_fin_le (m+1) (vv ρ (k+i)) (by have := vv_lt ρ (k+i) (by omega); omega)]
        rw [top_count k i (by omega) ρ ht]
        congr 1
        rw [show infoSignal (infoN k i ρ) + (m - k - 1) + 1 = infoSignal (infoN k i ρ) + (m - k) by
          omega]
        push_cast
        ring
      · simp [ht]
    simp only [hcount]
    rw [ih (fun x => G x * ((infoSignal x : ℝ) + ((m - k : ℕ) : ℝ)))]
    rw [mul_sum]
    apply sum_congr rfl
    intro ρ _
    by_cases hb : infoBestSoFar (infoN k i ρ) = true
    · simp only [hb, if_true]
      have := fr_succN k i m (infoSignal (infoN k i ρ)) hm
      push_cast at this ⊢
      rw [show ((m:ℝ) + 1) * (G (infoN k i ρ) * fr (m + 1 - k) k i (infoSignal (infoN k i ρ))) =
        G (infoN k i ρ) * (((m:ℝ) + 1) * fr (m + 1 - k) k i (infoSignal (infoN k i ρ))) by ring]
      rw [this]
      ring
    · simp [hb]

/-! ### the one-step transition identity -/

lemma ins_core (k i : ℕ) (ρ : Equiv.Perm (Fin (k+i+1))) (H : Bool → ℕ → ℝ) :
    ∑ v : Fin (k+i+1+1), H (infoBestSoFar (infoN k (i+1) (ins v ρ)))
      (if infoBestSoFar (infoN k (i+1) (ins v ρ)) = true then infoSignal (infoN k (i+1) (ins v ρ))
        else infoMax (infoN k (i+1) (ins v ρ))) =
    (((infoMax (infoN k i ρ) : ℕ) : ℝ) + i + 1) * H false (infoMax (infoN k i ρ)) +
      ∑ s' ∈ Icc (infoMax (infoN k i ρ)) k, H true s' := by
  have hne : (Icc k (k+i)).Nonempty := ⟨k, by simp⟩
  obtain ⟨pst, hpst, hmax⟩ := exists_max_image (Icc k (k+i)) (vv ρ) hne
  have hpst' : k ≤ pst ∧ pst ≤ k + i := by simpa using hpst
  set μ := vv ρ pst with hμdef
  have hμL : μ < k + i + 1 := vv_lt ρ pst (by omega)
  -- (a)
  have hbsf : ∀ v : Fin (k+i+1+1), infoBestSoFar (infoN k (i+1) (ins v ρ)) = true ↔ μ < v.val := by
    intro v
    rw [bsf_iff]
    have e : k + (i + 1) = k + i + 1 := by omega
    rw [e, vv_ins_last]
    constructor
    · intro H
      have := H pst hpst'.1 (by omega)
      rwa [vv_ins_lt_new v ρ pst (by omega)] at this
    · intro hv p hp1 hp2
      rw [vv_ins_lt_new v ρ p hp2]
      exact lt_of_le_of_lt (hmax p (by simp; omega)) hv
  -- (b)
  have hsig : ∀ v : Fin (k+i+1+1), μ < v.val →
      infoSignal (infoN k (i+1) (ins v ρ)) = v.val - (i+1) := by
    intro v hv
    rw [sig_eq]
    have e : k + (i + 1) = k + i + 1 := by omega
    rw [e, vv_ins_last]
    have hf : (range k).filter (fun a => vv (ins v ρ) a < v.val) =
        (range k).filter (fun a => vv ρ a < v.val) := by
      apply filter_congr; intro a ha; simp at ha
      exact vv_ins_lt_new v ρ a (by omega)
    rw [hf]
    have h1 := cnt_lt ρ v.val (by have := v.isLt; omega)
    rw [cnt_split k (by omega)] at h1
    have h2 : (Ico k (k+i+1)).filter (fun p => vv ρ p < v.val) = Ico k (k+i+1) := by
      apply filter_true_of_mem
      intro p hp; simp at hp
      exact lt_of_le_of_lt (hmax p (by simp; omega)) hv
    rw [h2, Nat.card_Ico] at h1
    omega
  -- (c)
  have hmx : ∀ v : Fin (k+i+1+1), ¬ μ < v.val →
      infoMax (infoN k (i+1) (ins v ρ)) = infoMax (infoN k i ρ) := by
    intro v hv
    rw [max_eq, max_eq]
    congr 1
    apply filter_congr
    intro a ha
    simp only [mem_range] at ha
    simp only [mem_Icc]
    constructor
    · rintro ⟨p, ⟨hp1, hp2⟩, hp3⟩
      by_cases hp : p < k + i + 1
      · rw [vv_ins_lt_iff v ρ a p (by omega) hp] at hp3
        exact ⟨p, ⟨hp1, by omega⟩, hp3⟩
      · have e : p = k + i + 1 := by omega
        rw [e, vv_ins_last, vv_ins_lt_new v ρ a (by omega)] at hp3
        exact ⟨pst, hpst', by omega⟩
    · rintro ⟨p, ⟨hp1, hp2⟩, hp3⟩
      refine ⟨p, ⟨hp1, by omega⟩, ?_⟩
      rw [vv_ins_lt_iff v ρ a p (by omega) (by omega)]
      exact hp3
  -- (d)
  have hmu : μ = infoMax (infoN k i ρ) + i := by
    have h1 := cnt_lt ρ μ (by omega)
    rw [cnt_split k (by omega)] at h1
    have h2 : (Ico k (k+i+1)).filter (fun p => vv ρ p < μ) = (Ico k (k+i+1)).erase pst := by
      ext p
      simp only [mem_filter, mem_Ico, mem_erase]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨?_, h1, h2⟩
        rintro rfl; exact lt_irrefl _ h3
      · rintro ⟨hne, h1, h2⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        have := hmax p (by simp; omega)
        rcases lt_or_eq_of_le this with h' | h'
        · exact h'
        · exact absurd (vv_inj ρ _ _ h2 (by omega) h') hne
    rw [h2, card_Ico_erase k (k+i+1) pst hpst'.1 (by omega)] at h1
    have h3 : (range k).filter (fun a => vv ρ a < μ) =
        (range k).filter (fun a => ∃ p ∈ Icc k (k + i), vv ρ a < vv ρ p) := by
      apply filter_congr
      intro a _
      constructor
      · intro h; exact ⟨pst, hpst, h⟩
      · rintro ⟨p, hp, h⟩; exact lt_of_lt_of_le h (hmax p hp)
    rw [h3, ← max_eq] at h1
    omega
  -- assemble
  have hsum : ∀ v : Fin (k+i+1+1),
      H (infoBestSoFar (infoN k (i+1) (ins v ρ)))
        (if infoBestSoFar (infoN k (i+1) (ins v ρ)) = true then infoSignal (infoN k (i+1) (ins v ρ))
          else infoMax (infoN k (i+1) (ins v ρ))) =
      if μ < v.val then H true (v.val - (i+1)) else H false (infoMax (infoN k i ρ)) := by
    intro v
    by_cases hv : μ < v.val
    · have hb := (hbsf v).2 hv
      rw [if_pos hv, hb, if_pos rfl, hsig v hv]
    · have hb : infoBestSoFar (infoN k (i+1) (ins v ρ)) = false := by
        rw [← Bool.not_eq_true, hbsf v]; exact hv
      rw [if_neg hv, hb, if_neg (by simp), hmx v hv]
  simp only [hsum]
  rw [sum_ite]
  rw [sum_const]
  have hc : (univ.filter (fun v : Fin (k+i+1+1) => ¬ μ < v.val)).card = μ + 1 := by
    have : (univ.filter (fun v : Fin (k+i+1+1) => ¬ μ < v.val)) =
        univ.filter (fun v : Fin (k+i+1+1) => v.val ≤ μ) := by
      apply filter_congr; intro v _; omega
    rw [this, card_fin_le _ μ (by omega)]
  rw [hc, nsmul_eq_mul]
  rw [sum_fin_filter (k+i+1+1) (fun x => μ < x) (fun x => H true (x - (i+1)))]
  have hset : (range (k+i+1+1)).filter (fun x => μ < x) =
      (Icc (infoMax (infoN k i ρ)) k).map (addRightEmbedding (i+1)) := by
    ext x
    simp only [mem_filter, mem_range, mem_map, mem_Icc, addRightEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - (i+1), ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩; omega
  rw [hset, sum_map]
  simp only [addRightEmbedding_apply, Nat.add_sub_cancel]
  rw [hmu]
  push_cast
  ring

/-- Transition identity (T2). -/
lemma T2 (k i : ℕ) : ∀ N, k + i + 1 + 1 ≤ N → ∀ (G : Info k i → ℝ) (H : Bool → ℕ → ℝ),
    ∑ σ : Equiv.Perm (Fin N), G (infoN k i σ) * H (infoBestSoFar (infoN k (i+1) σ))
      (if infoBestSoFar (infoN k (i+1) σ) = true then infoSignal (infoN k (i+1) σ)
        else infoMax (infoN k (i+1) σ)) =
    ∑ σ : Equiv.Perm (Fin N), G (infoN k i σ) *
      (((((infoMax (infoN k i σ) : ℕ) : ℝ) + i + 1) * H false (infoMax (infoN k i σ)) +
        ∑ s' ∈ Icc (infoMax (infoN k i σ)) k, H true s') / ((k:ℝ) + i + 2)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    intro G H
    rw [sum_perm_succ, sum_perm_succ]
    simp only [infoN_ins k i (le_refl _)]
    rw [sum_comm]
    simp only [← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [ins_core k i _ H]
    rw [mul_sum]
    apply sum_congr rfl
    intro ρ _
    have : ((k + i + 1 + 1 : ℕ) : ℝ) = (k:ℝ) + i + 2 := by push_cast; ring
    rw [this]
    have hpos : (0:ℝ) < (k:ℝ) + i + 2 := by positivity
    field_simp
  | succ m hm ih =>
    intro G H
    rw [sum_perm_succ, sum_perm_succ]
    have h1 : k + i + 1 ≤ m := by omega
    have h2 : k + (i + 1) + 1 ≤ m := by omega
    simp only [infoN_ins k i h1, infoN_ins k (i+1) h2, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [ih G H]

end SS16



set_option autoImplicit false

open Finset
open SecretaryAdvice.Samples

namespace SS16

/-! ## Part D: the verification (telescoping) argument -/

lemma info_eq {n k : ℕ} (σ : Outcome n k) (i : Fin n) : info σ i = infoN k i.val σ := by
  funext a b
  unfold info infoN prefixPos
  have ha : a.val < k + n := by have := a.isLt; have := i.isLt; omega
  have hb : b.val < k + n := by have := b.isLt; have := i.isLt; omega
  unfold vv
  rw [dif_pos ha, dif_pos hb, decide_eq_decide]
  exact Fin.lt_def

lemma top_iff {n k : ℕ} (σ : Outcome n k) (i : Fin n) : top σ i ↔ topN k i.val σ := by
  unfold top topN onlinePos
  simp only [mem_Ico]
  have hi : k + i.val < k + n := by have := i.isLt; omega
  constructor
  · intro H p ⟨hp1, hp2⟩
    have := H ⟨p - k, by omega⟩
    unfold vv
    rw [dif_pos hp2, dif_pos hi]
    have e1 : Fin.natAdd k (⟨p - k, by omega⟩ : Fin n) = ⟨p, hp2⟩ := by
      ext; simp; omega
    have e2 : Fin.natAdd k i = ⟨k + i.val, hi⟩ := by ext; simp
    rw [e1, e2] at this
    exact this
  · intro H j
    have := H (k + j.val) ⟨by omega, by omega⟩
    unfold vv at this
    rw [dif_pos (by omega), dif_pos hi] at this
    have e1 : Fin.natAdd k j = ⟨k + j.val, by omega⟩ := by ext; simp
    have e2 : Fin.natAdd k i = ⟨k + i.val, hi⟩ := by ext; simp
    rw [e1, e2]
    exact this

def restr {k i : ℕ} (x : Info k i) (j : ℕ) (h : j ≤ i) : Info k j :=
  fun a b => x (Fin.castLE (by omega) a) (Fin.castLE (by omega) b)

lemma infoN_restr {N : ℕ} (k i j : ℕ) (h : j ≤ i) (σ : Equiv.Perm (Fin N)) :
    infoN k j σ = restr (infoN k i σ) j h := by
  funext a b; rfl

variable {n k : ℕ}

noncomputable def PI (q : Policy n k) (i : ℕ) (x : Info k i) : ℝ :=
  ∏ j : Fin n, if h : j.val < i then (1 - q j (restr x j.val (le_of_lt h))) else 1

noncomputable def Pq (q : Policy n k) (i : ℕ) (σ : Outcome n k) : ℝ :=
  ∏ j ∈ univ.filter (fun j : Fin n => j.val < i), (1 - q j (info σ j))

lemma Pq_eq (q : Policy n k) (i : ℕ) (σ : Outcome n k) : Pq q i σ = PI q i (infoN k i σ) := by
  unfold Pq PI
  rw [prod_filter]
  apply prod_congr rfl
  intro j _
  by_cases h : j.val < i
  · rw [if_pos h, dif_pos h, info_eq, infoN_restr k i j.val (le_of_lt h)]
  · rw [if_neg h, dif_neg h]

lemma Pq_succ (q : Policy n k) (i : Fin n) (σ : Outcome n k) :
    Pq q (i.val + 1) σ = Pq q i.val σ * (1 - q i (info σ i)) := by
  unfold Pq
  have e : univ.filter (fun j : Fin n => j.val < i.val + 1) =
      insert i (univ.filter (fun j : Fin n => j.val < i.val)) := by
    ext j; simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h; by_cases hj : j.val < i.val
      · right; exact hj
      · left; exact Fin.ext (by omega)
    · rintro (rfl | h) <;> omega
  rw [e, prod_insert (by simp), mul_comm]

lemma Pq_zero (q : Policy n k) (σ : Outcome n k) : Pq q 0 σ = 1 := by
  unfold Pq
  rw [filter_false_of_mem (by intro j _; omega)]
  simp

lemma Pq_nonneg (q : Policy n k) (hq : ValidPolicy q) (i : ℕ) (σ : Outcome n k) :
    0 ≤ Pq q i σ := by
  unfold Pq
  apply prod_nonneg
  intro j _
  linarith [(hq j (info σ j)).2]

lemma pickProb_eq (q : Policy n k) (σ : Outcome n k) (i : Fin n) :
    pickProb q σ i = q i (info σ i) * Pq q i.val σ := by
  unfold pickProb Pq
  congr 1

noncomputable def Vfun (n k i : ℕ) (x : Info k i) : ℝ :=
  if infoBestSoFar x = true then max (fr n k i (infoSignal x)) (WW n k i (infoSignal x))
  else WW n k i (infoMax x)

noncomputable def Rfun (n k i : ℕ) (x : Info k i) : ℝ :=
  if infoBestSoFar x = true then fr n k i (infoSignal x) else 0

noncomputable def Vat (n k i : ℕ) (σ : Outcome n k) : ℝ :=
  if i < n then Vfun n k i (infoN k i σ) else 0

noncomputable def Tot (q : Policy n k) (i : ℕ) : ℝ :=
  ∑ σ : Outcome n k, ∑ j ∈ univ.filter (fun j : Fin n => j.val < i),
      (if top σ j then pickProb q σ j else 0) +
    ∑ σ : Outcome n k, Pq q i σ * Vat n k i σ

noncomputable def Delta (q : Policy n k) (i : Fin n) (σ : Outcome n k) : ℝ :=
  Pq q i.val σ * (Vfun n k i.val (infoN k i.val σ) -
    q i (infoN k i.val σ) * Rfun n k i.val (infoN k i.val σ) -
    (1 - q i (infoN k i.val σ)) * WW n k i.val (infoMax (infoN k i.val σ)))

lemma stepA (q : Policy n k) (i : Fin n) :
    ∑ σ : Outcome n k, (if top σ i then pickProb q σ i else 0) =
    ∑ σ : Outcome n k, Pq q i.val σ * (q i (infoN k i.val σ) * Rfun n k i.val (infoN k i.val σ)) := by
  have h1 : ∀ σ : Outcome n k, (if top σ i then pickProb q σ i else 0) =
      (fun x => q i x * PI q i.val x) (infoN k i.val σ) * (if topN k i.val σ then 1 else 0) := by
    intro σ
    rw [pickProb_eq, Pq_eq, info_eq]
    by_cases h : top σ i
    · rw [if_pos h, if_pos ((top_iff σ i).1 h), mul_one]
    · rw [if_neg h, if_neg (fun h' => h ((top_iff σ i).2 h')), mul_zero]
  simp only [h1]
  rw [T1 k i.val (k + n) (by have := i.isLt; omega) (fun x => q i x * PI q i.val x)]
  apply sum_congr rfl
  intro σ _
  rw [Pq_eq, Nat.add_sub_cancel_left]
  unfold Rfun
  ring

lemma stepB (q : Policy n k) (i : Fin n) :
    ∑ σ : Outcome n k, Pq q (i.val + 1) σ * Vat n k (i.val + 1) σ =
    ∑ σ : Outcome n k, Pq q i.val σ * ((1 - q i (infoN k i.val σ)) *
      WW n k i.val (infoMax (infoN k i.val σ))) := by
  by_cases hi : i.val + 1 < n
  · have h1 : ∀ σ : Outcome n k, Pq q (i.val + 1) σ * Vat n k (i.val + 1) σ =
        (fun x => PI q i.val x * (1 - q i x)) (infoN k i.val σ) *
        (fun (b : Bool) (m : ℕ) => if b = true then max (fr n k (i.val+1) m) (WW n k (i.val+1) m)
            else WW n k (i.val+1) m) (infoBestSoFar (infoN k (i.val+1) σ))
          (if infoBestSoFar (infoN k (i.val+1) σ) = true then infoSignal (infoN k (i.val+1) σ)
            else infoMax (infoN k (i.val+1) σ)) := by
      intro σ
      rw [Pq_succ, Pq_eq, info_eq]
      unfold Vat Vfun
      rw [if_pos hi]
      by_cases hb : infoBestSoFar (infoN k (i.val+1) σ) = true
      · simp only [hb, if_true]
      · simp [hb]
    simp only [h1]
    rw [T2 k i.val (k + n) (by omega) (fun x => PI q i.val x * (1 - q i x))
      (fun (b : Bool) (m : ℕ) => if b = true then max (fr n k (i.val+1) m) (WW n k (i.val+1) m)
            else WW n k (i.val+1) m)]
    apply sum_congr rfl
    intro σ _
    rw [Pq_eq, WW_succ n k i.val _ hi]
    simp only [Bool.false_eq_true, if_false, if_true]
    ring
  · have h1 : ∀ σ : Outcome n k, Vat n k (i.val + 1) σ = 0 := by
      intro σ; unfold Vat; rw [if_neg (by omega)]
    have h2 : ∀ m, WW n k i.val m = 0 := fun m => WW_last n k i.val m hi
    simp [h1, h2]

lemma step (q : Policy n k) (i : Fin n) :
    Tot q (i.val + 1) = Tot q i.val - ∑ σ : Outcome n k, Delta q i σ := by
  unfold Tot
  have e : univ.filter (fun j : Fin n => j.val < i.val + 1) =
      insert i (univ.filter (fun j : Fin n => j.val < i.val)) := by
    ext j; simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h; by_cases hj : j.val < i.val
      · right; exact hj
      · left; exact Fin.ext (by omega)
    · rintro (rfl | h) <;> omega
  rw [e]
  simp only [sum_insert (show i ∉ univ.filter (fun j : Fin n => j.val < i.val) by simp)]
  rw [sum_add_distrib, stepA, stepB]
  have hV : ∀ σ : Outcome n k, Vat n k i.val σ = Vfun n k i.val (infoN k i.val σ) := by
    intro σ; unfold Vat; rw [if_pos i.isLt]
  simp only [hV]
  have hD : ∑ σ : Outcome n k, Delta q i σ =
      ∑ σ : Outcome n k, Pq q i.val σ * Vfun n k i.val (infoN k i.val σ) -
      ∑ σ : Outcome n k, Pq q i.val σ * (q i (infoN k i.val σ) * Rfun n k i.val (infoN k i.val σ)) -
      ∑ σ : Outcome n k, Pq q i.val σ * ((1 - q i (infoN k i.val σ)) *
        WW n k i.val (infoMax (infoN k i.val σ))) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro σ _
    unfold Delta
    ring
  rw [hD]
  ring

lemma tele (q : Policy n k) : ∀ m, m ≤ n →
    Tot q m = Tot q 0 - ∑ i ∈ univ.filter (fun i : Fin n => i.val < m), ∑ σ : Outcome n k, Delta q i σ := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [filter_false_of_mem (by intro j _; omega)]
    simp
  | succ m ih =>
    intro hm
    have := step q ⟨m, by omega⟩
    simp only at this
    rw [this, ih (by omega)]
    have e : univ.filter (fun j : Fin n => j.val < m + 1) =
        insert ⟨m, by omega⟩ (univ.filter (fun j : Fin n => j.val < m)) := by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro h; by_cases hj : j.val < m
        · right; exact hj
        · left; exact Fin.ext (by simp; omega)
      · rintro (rfl | h)
        · simp
        · omega
    rw [e, sum_insert (by simp)]
    ring

lemma Tot_n (q : Policy n k) : Tot q n = ((k + n).factorial : ℝ) * win q := by
  unfold Tot win
  have h1 : ∀ σ : Outcome n k, Vat n k n σ = 0 := by
    intro σ; unfold Vat; rw [if_neg (lt_irrefl _)]
  simp only [h1, mul_zero, sum_const_zero, add_zero]
  rw [filter_true_of_mem (by intro j _; exact j.isLt)]
  have : ((k + n).factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma Tot_zero (q q' : Policy n k) : Tot q 0 = Tot q' 0 := by
  unfold Tot
  simp only [Pq_zero]
  rw [filter_false_of_mem (by intro j _; omega)]
  simp

lemma Delta_nonneg (q : Policy n k) (hq : ValidPolicy q) (i : Fin n) (σ : Outcome n k) :
    0 ≤ Delta q i σ := by
  unfold Delta
  apply mul_nonneg (Pq_nonneg q hq _ σ)
  have hq0 := (hq i (infoN k i.val σ)).1
  have hq1 := (hq i (infoN k i.val σ)).2
  unfold Vfun Rfun
  by_cases hb : infoBestSoFar (infoN k i.val σ) = true
  · rw [if_pos hb, if_pos hb, max_eq_sig k i.val σ hb]
    have h1 := le_max_left (fr n k i.val (infoSignal (infoN k i.val σ)))
      (WW n k i.val (infoSignal (infoN k i.val σ)))
    have h2 := le_max_right (fr n k i.val (infoSignal (infoN k i.val σ)))
      (WW n k i.val (infoSignal (infoN k i.val σ)))
    nlinarith
  · rw [if_neg hb, if_neg hb]
    have := WW_nonneg n k i.val (infoMax (infoN k i.val σ))
    nlinarith

lemma Delta_thr (hn : 1 ≤ n) (i : Fin n) (σ : Outcome n k) :
    Delta (thresholdPolicy (n := n) (k := k) (thr n k)) i σ = 0 := by
  unfold Delta
  apply mul_eq_zero_of_right
  unfold Vfun Rfun thresholdPolicy
  by_cases hb : infoBestSoFar (infoN k i.val σ) = true
  · simp only [hb, true_and, if_true]
    rw [max_eq_sig k i.val σ hb]
    by_cases ht : thr n k (infoSignal (infoN k i.val σ)) ≤ i.val + 1
    · have hs := (thr_iff n k hn _ i.val).1 ht
      rw [if_pos ht, max_eq_left hs]
      ring
    · have hs : ¬ WW n k i.val (infoSignal (infoN k i.val σ)) ≤ fr n k i.val (infoSignal (infoN k i.val σ)) :=
        fun h => ht ((thr_iff n k hn _ i.val).2 h)
      push Not at hs
      rw [if_neg ht, max_eq_right (le_of_lt hs)]
      ring
  · simp only [hb, Bool.false_eq_true, false_and, if_false]
    ring

end SS16

open SS16 in
theorem solution (n k : ℕ) (hn : 1 ≤ n) :
    ∃ t : ℕ → ℕ, SecretaryAdvice.Samples.ValidThreshold n k t ∧
      ∀ q : SecretaryAdvice.Samples.Policy n k, SecretaryAdvice.Samples.ValidPolicy q →
        SecretaryAdvice.Samples.win q ≤
          SecretaryAdvice.Samples.win (SecretaryAdvice.Samples.thresholdPolicy (n := n) (k := k) t) := by
  refine ⟨thr n k, fun s _ => thr_valid n k hn s, ?_⟩
  intro q hq
  set τ := SecretaryAdvice.Samples.thresholdPolicy (n := n) (k := k) (thr n k)
  have hq' := tele q n le_rfl
  have hτ := tele τ n le_rfl
  rw [Tot_n] at hq' hτ
  have hz : ∑ i ∈ univ.filter (fun i : Fin n => i.val < n), ∑ σ : SecretaryAdvice.Samples.Outcome n k,
      Delta τ i σ = 0 := by
    apply sum_eq_zero; intro i _; apply sum_eq_zero; intro σ _; exact Delta_thr hn i σ
  have hpos : ∑ i ∈ univ.filter (fun i : Fin n => i.val < n), ∑ σ : SecretaryAdvice.Samples.Outcome n k,
      Delta q i σ ≥ 0 := by
    apply sum_nonneg; intro i _; apply sum_nonneg; intro σ _; exact Delta_nonneg q hq i σ
  rw [hz, sub_zero] at hτ
  rw [Tot_zero q τ] at hq'
  have hf : (0:ℝ) < ((k + n).factorial : ℝ) := by positivity
  have : ((k + n).factorial : ℝ) * SecretaryAdvice.Samples.win q ≤
      ((k + n).factorial : ℝ) * SecretaryAdvice.Samples.win τ := by linarith
  exact le_of_mul_le_mul_left this hf

