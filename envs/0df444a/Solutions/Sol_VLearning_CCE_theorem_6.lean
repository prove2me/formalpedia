-- Prove2me | solution 1 for VLearning.CCE.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T00:57:25.783921+00:00
-- url     : https://prove2.me/submissions/9a2fc7ec-9823-422b-8576-acd453eaf25c

import Mathlib
import Definitions.Def_VLearning_CCE_Model
/-! Generic causal-kernel sums on flat sequences `Fin N → X` (hR coupling toolkit for faa2f7e7). -/

namespace FaaSeq
open Finset Classical

/-- `e` agrees with `x` on the first `m` coordinates. -/
def Agree {X : Type*} {N : ℕ} (m : ℕ) (x e : Fin N → X) : Prop :=
  ∀ j : Fin N, j.val < m → e j = x j

/-- Tail normalisation: summing the kernels from position `m` on over all continuations of a
fixed prefix gives one. -/
lemma tail_sum {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (g : Fin N → (Fin N → X) → X → ℝ)
    (hdep : ∀ i e e', (∀ j : Fin N, j < i → e j = e' j) → g i e = g i e')
    (hsum : ∀ i e, ∑ y, g i e y = 1) :
    ∀ (d m : ℕ), m + d = N → ∀ x : Fin N → X,
      ∑ e ∈ univ.filter (fun e : Fin N → X => Agree m x e),
        ∏ i ∈ univ.filter (fun i : Fin N => m ≤ i.val), g i e (e i) = 1 := by
  classical
  intro d
  induction d with
  | zero =>
    intro m hm x
    have hA : univ.filter (fun e : Fin N → X => Agree m x e) = {x} := by
      ext e
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h; funext j; exact h.2 j (by omega)
      · rintro rfl; exact ⟨mem_univ _, fun j _ => rfl⟩
    have hP : univ.filter (fun i : Fin N => m ≤ i.val) = ∅ := by
      ext i; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
    rw [hA, hP]; simp
  | succ d ih =>
    intro m hm x
    have hmN : m < N := by omega
    set p : Fin N := ⟨m, hmN⟩ with hp
    have hsplit : univ.filter (fun i : Fin N => m ≤ i.val) =
        insert p (univ.filter (fun i : Fin N => m + 1 ≤ i.val)) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert, hp, Fin.ext_iff]
      omega
    have hpn : p ∉ univ.filter (fun i : Fin N => m + 1 ≤ i.val) := by simp [hp]
    rw [hsplit]
    simp_rw [prod_insert hpn]
    rw [← sum_fiberwise (univ.filter (fun e : Fin N → X => Agree m x e)) (fun e => e p)]
    have hfib : ∀ v : X, ∀ e : Fin N → X,
        (Agree m x e ∧ e p = v) ↔ Agree (m + 1) (Function.update x p v) e := by
      intro v e
      simp only [Agree]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        by_cases hjp : j = p
        · rw [hjp, h2]; simp
        · rw [Function.update_of_ne hjp]
          apply h1
          have : j.val ≠ m := fun h => hjp (Fin.ext h)
          omega
      · intro h
        refine ⟨fun j hj => ?_, ?_⟩
        · have hjp : j ≠ p := fun hjp => by rw [hjp] at hj; simp [hp] at hj
          rw [h j (by omega), Function.update_of_ne hjp]
        · rw [h p (by simp [hp])]; simp
    have hterm : ∀ v : X,
        ∑ e ∈ (univ.filter (fun e : Fin N → X => Agree m x e)).filter (fun e => e p = v),
          g p e (e p) * ∏ i ∈ univ.filter (fun i : Fin N => m + 1 ≤ i.val), g i e (e i) =
        g p x v := by
      intro v
      have hset : (univ.filter (fun e : Fin N → X => Agree m x e)).filter (fun e => e p = v) =
          univ.filter (fun e : Fin N → X => Agree (m + 1) (Function.update x p v) e) := by
        ext e
        simp only [mem_filter, mem_univ, true_and]
        exact hfib v e
      rw [hset]
      have hg : ∀ e ∈ univ.filter (fun e : Fin N → X => Agree (m + 1) (Function.update x p v) e),
          g p e (e p) * ∏ i ∈ univ.filter (fun i : Fin N => m + 1 ≤ i.val), g i e (e i) =
          g p x v * ∏ i ∈ univ.filter (fun i : Fin N => m + 1 ≤ i.val), g i e (e i) := by
        intro e he
        have he' := (hfib v e).2 (Finset.mem_filter.mp he).2
        rw [he'.2, hdep p e x (fun j hj => he'.1 j (by have := Fin.lt_def.mp hj; simpa [hp] using this))]
      rw [sum_congr rfl hg, ← mul_sum, ih (m + 1) (by omega) (Function.update x p v), mul_one]
    calc _ = ∑ v : X, g p x v := sum_congr rfl (fun v _ => hterm v)
      _ = 1 := hsum p x

/-- Cylinder marginal: the total weight of all sequences with a fixed prefix of length `m` is
the product of the kernels along that prefix. -/
lemma cyl_sum {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (g : Fin N → (Fin N → X) → X → ℝ)
    (hdep : ∀ i e e', (∀ j : Fin N, j < i → e j = e' j) → g i e = g i e')
    (hsum : ∀ i e, ∑ y, g i e y = 1) (m : ℕ) (hm : m ≤ N) (x : Fin N → X) :
    ∑ e ∈ univ.filter (fun e : Fin N → X => Agree m x e), ∏ i : Fin N, g i e (e i) =
      ∏ i ∈ univ.filter (fun i : Fin N => i.val < m), g i x (x i) := by
  classical
  have hsplit : ∀ e : Fin N → X, ∏ i : Fin N, g i e (e i) =
      (∏ i ∈ univ.filter (fun i : Fin N => i.val < m), g i e (e i)) *
        ∏ i ∈ univ.filter (fun i : Fin N => m ≤ i.val), g i e (e i) := by
    intro e
    rw [← prod_filter_mul_prod_filter_not univ (fun i : Fin N => i.val < m)]
    congr 1
    apply prod_congr _ (fun _ _ => rfl)
    ext i; simp
  have hpre : ∀ e ∈ univ.filter (fun e : Fin N → X => Agree m x e),
      ∏ i ∈ univ.filter (fun i : Fin N => i.val < m), g i e (e i) =
        ∏ i ∈ univ.filter (fun i : Fin N => i.val < m), g i x (x i) := by
    intro e he
    replace he : Agree m x e := (Finset.mem_filter.mp he).2
    apply prod_congr rfl
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    rw [he i hi, hdep i e x (fun j hj => he j (by have := Fin.lt_def.mp hj; omega))]
  rw [sum_congr rfl (fun e he => by rw [hsplit e, hpre e he]), ← mul_sum,
    tail_sum g hdep hsum (N - m) m (by omega) x, mul_one]

/-- Flattening a double product over episodes and steps (episode-major order). -/
lemma flat_prod {M : Type*} [CommMonoid M] {K H : ℕ} (F : Fin K → Fin H → M) :
    ∏ k, ∏ h, F k h =
      ∏ n : Fin (K * H), F (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2 := by
  rw [← Fintype.prod_prod_type']
  exact Fintype.prod_equiv finProdFinEquiv _ _ (fun x => by simp)

lemma flat_val {K H : ℕ} (a : Fin K × Fin H) :
    (finProdFinEquiv a).val = a.2.val + H * a.1.val := rfl

/-- The flat rank order is the lexicographic (episode, step) order. -/
lemma flat_rank_lt {K H : ℕ} (a b : Fin K × Fin H) :
    (finProdFinEquiv a).val < (finProdFinEquiv b).val ↔
      a.1.val < b.1.val ∨ (a.1 = b.1 ∧ a.2.val < b.2.val) := by
  rw [flat_val, flat_val]
  obtain ⟨⟨k, hk⟩, ⟨h, hh⟩⟩ := a
  obtain ⟨⟨k', hk'⟩, ⟨h', hh'⟩⟩ := b
  simp only [Fin.mk.injEq]
  constructor
  · intro hlt
    rcases lt_trichotomy k k' with c | c | c
    · left; exact c
    · right; subst c; exact ⟨rfl, by omega⟩
    · exfalso
      have : H * (k' + 1) ≤ H * k := Nat.mul_le_mul_left _ c
      nlinarith
  · rintro (c | ⟨rfl, c⟩)
    · have : H * (k + 1) ≤ H * k' := Nat.mul_le_mul_left _ c
      nlinarith
    · omega

end FaaSeq

set_option autoImplicit false

/-! faa2f7e7 VLearning.CCE.theorem_6 -- foundation layer (learning-rate weights).
See scratch/decomp/faa2f7e7.plan.md for the overall plan. -/

namespace VLearning.CCE.Aux
open VLearning.CCE

lemma lr_one (H : ℕ) : lr H 1 = 1 := by
  unfold lr; rw [Nat.cast_one]; exact div_self (by positivity)

lemma lr_nonneg (H t : ℕ) : 0 ≤ lr H t := by
  unfold lr; positivity

lemma lr_le_one (H t : ℕ) (ht : 1 ≤ t) : lr H t ≤ 1 := by
  unfold lr
  have h1 : (1:ℝ) ≤ t := by exact_mod_cast ht
  have h0 : (0:ℝ) ≤ H := Nat.cast_nonneg H
  rw [div_le_one (by linarith)]; linarith

lemma one_sub_lr_nonneg (H t : ℕ) (ht : 1 ≤ t) : 0 ≤ 1 - lr H t := by
  linarith [lr_le_one H t ht]

lemma one_sub_lr_succ (H t : ℕ) : 1 - lr H (t + 1) = (t : ℝ) / ((H : ℝ) + t + 1) := by
  unfold lr
  have h0 : (0:ℝ) ≤ H := Nat.cast_nonneg H
  have h1 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  have hne : (H : ℝ) + ((t + 1 : ℕ) : ℝ) ≠ 0 := by push_cast; linarith
  have hne' : (H : ℝ) + t + 1 ≠ 0 := by linarith
  rw [eq_div_iff hne', sub_mul, div_mul_eq_mul_div, one_mul]
  push_cast
  field_simp
  ring

lemma lrW_nonneg (H t i : ℕ) : 0 ≤ lrW H t i := by
  unfold lrW
  split_ifs with hi
  · apply Finset.prod_nonneg
    intro j hj
    exact one_sub_lr_nonneg H j (Finset.mem_Icc.mp hj).1
  · apply mul_nonneg (lr_nonneg H i)
    apply Finset.prod_nonneg
    intro j hj
    exact one_sub_lr_nonneg H j (by have := (Finset.mem_Ioc.mp hj).1; omega)

lemma lrW_zero_zero (H : ℕ) : lrW H 0 0 = 1 := by
  simp [lrW]

lemma lrW_zero_of_pos (H t : ℕ) (ht : 1 ≤ t) : lrW H t 0 = 0 := by
  unfold lrW
  rw [if_pos rfl]
  apply Finset.prod_eq_zero (i := 1) (Finset.mem_Icc.mpr ⟨le_refl 1, ht⟩)
  rw [lr_one]; ring

lemma lrW_self (H t : ℕ) (ht : 1 ≤ t) : lrW H t t = lr H t := by
  unfold lrW
  rw [if_neg (by omega)]
  simp

lemma lrW_succ_of_le (H t i : ℕ) (hi : 1 ≤ i) (hit : i ≤ t) :
    lrW H (t + 1) i = (1 - lr H (t + 1)) * lrW H t i := by
  unfold lrW
  rw [if_neg (by omega), if_neg (by omega), Finset.prod_Ioc_succ_top hit]
  ring

lemma lrW_zero_succ (H t : ℕ) : lrW H (t + 1) 0 = (1 - lr H (t + 1)) * lrW H t 0 := by
  unfold lrW
  rw [if_pos rfl, if_pos rfl, Finset.prod_Icc_succ_top (by omega)]
  ring

/-- The learning-rate weights sum to one: `α^0_t + ∑_{i=1}^t α^i_t = 1`. -/
lemma lrW_sum (H t : ℕ) : lrW H t 0 + ∑ i ∈ Finset.Icc 1 t, lrW H t i = 1 := by
  induction t with
  | zero => simp [lrW_zero_zero]
  | succ t ih =>
    rw [Finset.sum_Icc_succ_top (by omega), lrW_zero_succ, lrW_self H (t + 1) (by omega)]
    have hs : ∑ i ∈ Finset.Icc 1 t, lrW H (t + 1) i =
        (1 - lr H (t + 1)) * ∑ i ∈ Finset.Icc 1 t, lrW H t i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have := Finset.mem_Icc.mp hi
      exact lrW_succ_of_le H t i this.1 this.2
    rw [hs]
    linear_combination (1 - lr H (t + 1)) * ih

lemma sum_Icc_eq_sum_fin (f : ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ Finset.Icc 1 t, f i = ∑ i : Fin t, f (i.val + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Fin.sum_univ_castSucc, ih]
    simp

/-- Fin-indexed form, as used by `outVal`, `brW` and `weightedRegret`. -/
lemma lrW_sum_fin (H t : ℕ) : lrW H t 0 + ∑ i : Fin t, lrW H t (i.val + 1) = 1 := by
  rw [← sum_Icc_eq_sum_fin (fun i => lrW H t i) t]
  exact lrW_sum H t

/-- Telescoping identity behind `∑_{t ≥ i} α^i_t ≤ 1 + 1/H`. -/
lemma sum_tailProd (H i : ℕ) (hH : 1 ≤ H) (T : ℕ) (hT : i ≤ T) :
    ∑ t ∈ Finset.Icc i T, ∏ j ∈ Finset.Ioc i t, (1 - lr H j) =
      ((i : ℝ) + H) / H - (∏ j ∈ Finset.Ioc i T, (1 - lr H j)) * T / H := by
  have hH' : (0:ℝ) < H := by exact_mod_cast hH
  induction T, hT using Nat.le_induction with
  | base =>
    simp
    field_simp
    ring
  | succ T hT ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.prod_Ioc_succ_top hT, one_sub_lr_succ]
    have h1 : (0:ℝ) ≤ T := Nat.cast_nonneg T
    have hne : (H : ℝ) + T + 1 ≠ 0 := by linarith
    push_cast
    field_simp
    ring

/-- `∑_{t=i}^T α^i_t ≤ 1 + 1/H` for `i ≥ 1` (Jin et al. 2018, Lemma 4.1(c)). -/
lemma lrW_tail_sum (H i : ℕ) (hH : 1 ≤ H) (hi : 1 ≤ i) (T : ℕ) :
    ∑ t ∈ Finset.Icc i T, lrW H t i ≤ 1 + 1 / (H : ℝ) := by
  have hH' : (0:ℝ) < H := by exact_mod_cast hH
  rcases lt_or_ge T i with hTi | hTi
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
  have hrw : ∑ t ∈ Finset.Icc i T, lrW H t i =
      lr H i * ∑ t ∈ Finset.Icc i T, ∏ j ∈ Finset.Ioc i t, (1 - lr H j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    unfold lrW
    rw [if_neg (by omega)]
  rw [hrw, sum_tailProd H i hH T hTi]
  have hP : 0 ≤ (∏ j ∈ Finset.Ioc i T, (1 - lr H j)) * T / H := by
    apply div_nonneg _ hH'.le
    apply mul_nonneg _ (Nat.cast_nonneg T)
    apply Finset.prod_nonneg
    intro j hj
    exact one_sub_lr_nonneg H j (by have := (Finset.mem_Ioc.mp hj).1; omega)
  have hle : lr H i * (((i : ℝ) + H) / H - (∏ j ∈ Finset.Ioc i T, (1 - lr H j)) * T / H) ≤
      lr H i * (((i : ℝ) + H) / H) := by
    apply mul_le_mul_of_nonneg_left _ (lr_nonneg H i); linarith
  refine hle.trans (le_of_eq ?_)
  unfold lr
  have hi' : (1:ℝ) ≤ i := by exact_mod_cast hi
  have hne : (H : ℝ) + i ≠ 0 := by linarith
  field_simp
  ring

/-! ## Layer B: probability vectors -/

lemma wsum_le {ι : Type*} [Fintype ι] (p f : ι → ℝ) (hi : ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hf : ∀ i, f i ≤ hi) : ∑ i, p i * f i ≤ hi := by
  calc ∑ i, p i * f i ≤ ∑ i, p i * hi :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hp0 i))
    _ = hi := by rw [← Finset.sum_mul, hp1, one_mul]

lemma le_wsum {ι : Type*} [Fintype ι] (p f : ι → ℝ) (lo : ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hf : ∀ i, lo ≤ f i) : lo ≤ ∑ i, p i * f i := by
  calc lo = ∑ i, p i * lo := by rw [← Finset.sum_mul, hp1, one_mul]
    _ ≤ ∑ i, p i * f i :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hp0 i))

/-- A learning-rate combination `α^0_t F k + ∑ α^i_t F(k^i)` stays in `[lo, hi]`. -/
lemma comb_bounds (H t K : ℕ) (F : Fin K → ℝ) (k : Fin K) (vis : Fin t → Fin K) (lo hi : ℝ)
    (hF : ∀ k', lo ≤ F k' ∧ F k' ≤ hi) :
    lo ≤ lrW H t 0 * F k + ∑ i : Fin t, lrW H t (i.val + 1) * F (vis i) ∧
      lrW H t 0 * F k + ∑ i : Fin t, lrW H t (i.val + 1) * F (vis i) ≤ hi := by
  have hs := lrW_sum_fin H t
  constructor
  · calc lo = lrW H t 0 * lo + ∑ i : Fin t, lrW H t (i.val + 1) * lo := by
          rw [← Finset.sum_mul, ← add_mul, hs, one_mul]
      _ ≤ _ := by
          apply add_le_add (mul_le_mul_of_nonneg_left (hF k).1 (lrW_nonneg _ _ _))
          exact Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (hF _).1 (lrW_nonneg _ _ _))
  · calc _ ≤ lrW H t 0 * hi + ∑ i : Fin t, lrW H t (i.val + 1) * hi := by
          apply add_le_add (mul_le_mul_of_nonneg_left (hF k).2 (lrW_nonneg _ _ _))
          exact Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (hF _).2 (lrW_nonneg _ _ _))
      _ = hi := by rw [← Finset.sum_mul, ← add_mul, hs, one_mul]

section probs
variable {G : Game} {K : ℕ} (alg : ∀ j, BanditRule (G.A j)) (σ : RunState G K)

lemma policy_nonneg (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S)
    (b : Fin (G.A j)) : 0 ≤ RunState.policy alg σ j h s b :=
  (halg j).1 _ _

lemma policy_sum (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) :
    ∑ b, RunState.policy alg σ j h s b = 1 :=
  (halg j).2.1 _

lemma jointProb_nonneg (halg : ∀ j, (alg j).Valid) (h : Fin G.H) (s : Fin G.S)
    (a : G.JointAct) : 0 ≤ RunState.jointProb alg σ h s a :=
  Finset.prod_nonneg (fun j _ => policy_nonneg alg σ halg j h s (a j))

lemma jointProb_sum (halg : ∀ j, (alg j).Valid) (h : Fin G.H) (s : Fin G.S) :
    ∑ a : G.JointAct, RunState.jointProb alg σ h s a = 1 := by
  unfold RunState.jointProb
  rw [← Fintype.prod_sum (fun j b => RunState.policy alg σ j h s b)]
  exact Finset.prod_eq_one (fun j _ => policy_sum alg σ halg j h s)

lemma devProb_nonneg (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (b : Fin (G.A j))
    (h : Fin G.H) (s : Fin G.S) (a : G.JointAct) : 0 ≤ RunState.devProb alg σ j b h s a := by
  unfold RunState.devProb
  apply Finset.prod_nonneg
  intro j' _
  split_ifs
  · exact le_refl _ |>.trans' zero_le_one
  · exact le_refl 0
  · exact policy_nonneg alg σ halg j' h s (a j')

/-- The factor of player `j''` in `devProb`, as a function of its own action. -/
noncomputable def devFactor (j : Fin G.m) (b : Fin (G.A j)) (h : Fin G.H) (s : Fin G.S) :
    (j'' : Fin G.m) → Fin (G.A j'') → ℝ := fun j'' c =>
  if hj : j'' = j then (if (hj ▸ c : Fin (G.A j)) = b then (1:ℝ) else 0)
  else RunState.policy alg σ j'' h s c

lemma devProb_eq_prod (j : Fin G.m) (b : Fin (G.A j)) (h : Fin G.H) (s : Fin G.S)
    (a : G.JointAct) :
    RunState.devProb alg σ j b h s a = ∏ j', devFactor alg σ j b h s j' (a j') := by
  unfold RunState.devProb devFactor
  apply Finset.prod_congr rfl
  intro j' _
  by_cases hj : j' = j
  · subst hj; simp
  · simp [hj]

lemma devProb_sum (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (b : Fin (G.A j))
    (h : Fin G.H) (s : Fin G.S) : ∑ a : G.JointAct, RunState.devProb alg σ j b h s a = 1 := by
  rw [Finset.sum_congr rfl (fun a _ => devProb_eq_prod alg σ j b h s a),
    ← Fintype.prod_sum (devFactor alg σ j b h s)]
  apply Finset.prod_eq_one
  intro j' _
  unfold devFactor
  by_cases hj : j' = j
  · subst hj; simp
  · simp only [hj, dif_neg, not_false_eq_true]
    exact policy_sum alg σ halg j' h s

end probs

/-! ## Layer C: value bounds -/

lemma natsub_succ (H h : ℕ) (hh : h < H) : ((H - h : ℕ) : ℝ) = ((H - (h+1) : ℕ) : ℝ) + 1 := by
  rw [show H - h = (H - (h+1)) + 1 by omega]; push_cast; ring

section values
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}
  (τ : Fin K → Episode G)

lemma outVal_bounds (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) :
    ∀ d h, G.H - h ≤ d → ∀ (k : Fin K) (s : Fin G.S),
      0 ≤ outVal G alg β τ j h k s ∧ outVal G alg β τ j h k s ≤ ((G.H - h : ℕ) : ℝ) := by
  intro d
  induction d with
  | zero =>
    intro h hd k s
    have hh : ¬ h < G.H := by omega
    rw [outVal, dif_neg hh]; simp
  | succ d ih =>
    intro h hd k s
    by_cases hh : h < G.H
    · rw [outVal, dif_pos hh]
      refine comb_bounds G.H _ K (fun k' : Fin K => ∑ a : G.JointAct,
          RunState.jointProb alg (runState G β τ k'.val) ⟨h, hh⟩ s a *
            (G.r j ⟨h, hh⟩ s a + ∑ s', G.P ⟨h, hh⟩ s a s' * outVal G alg β τ j (h + 1) k' s'))
        k ((runState G β τ k.val).visits ⟨h, hh⟩ s).get 0 _ ?_
      intro k'
      have hnext : ∀ s', 0 ≤ outVal G alg β τ j (h+1) k' s' ∧
          outVal G alg β τ j (h+1) k' s' ≤ ((G.H - (h+1) : ℕ) : ℝ) :=
        fun s' => ih (h+1) (by omega) k' s'
      rw [natsub_succ G.H h hh]
      constructor
      · apply le_wsum _ _ _ (jointProb_nonneg alg _ halg _ _) (jointProb_sum alg _ halg _ _)
        intro a
        have hr := (hG.r_mem j ⟨h, hh⟩ s a).1
        have := le_wsum (G.P ⟨h, hh⟩ s a) _ 0 (hG.P_nonneg _ _ _) (hG.P_sum _ _ _)
          (fun s' => (hnext s').1)
        linarith
      · apply wsum_le _ _ _ (jointProb_nonneg alg _ halg _ _) (jointProb_sum alg _ halg _ _)
        intro a
        have hr := (hG.r_mem j ⟨h, hh⟩ s a).2
        have := wsum_le (G.P ⟨h, hh⟩ s a) _ _ (hG.P_nonneg _ _ _) (hG.P_sum _ _ _)
          (fun s' => (hnext s').2)
        linarith
    · rw [outVal, dif_neg hh]; simp

lemma brW_bounds (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m)
    (μ : DevPolicy G j) :
    ∀ d h, G.H - h ≤ d → ∀ (k : Fin K) (hist : List (Fin G.S × G.JointAct)) (s : Fin G.S),
      0 ≤ brW G alg β τ j μ h k hist s ∧
        brW G alg β τ j μ h k hist s ≤ ((G.H - h : ℕ) : ℝ) := by
  intro d
  induction d with
  | zero =>
    intro h hd k hist s
    have hh : ¬ h < G.H := by omega
    rw [brW, dif_neg hh]; simp
  | succ d ih =>
    intro h hd k hist s
    by_cases hh : h < G.H
    · rw [brW, dif_pos hh]
      refine comb_bounds G.H _ K (fun k' : Fin K => ∑ a : G.JointAct,
          RunState.devProb alg (runState G β τ k'.val) j (μ hist s) ⟨h, hh⟩ s a *
            (G.r j ⟨h, hh⟩ s a + ∑ s', G.P ⟨h, hh⟩ s a s' *
              brW G alg β τ j μ (h + 1) k' (hist ++ [(s, a)]) s'))
        k ((runState G β τ k.val).visits ⟨h, hh⟩ s).get 0 _ ?_
      intro k'
      rw [natsub_succ G.H h hh]
      constructor
      · apply le_wsum _ _ _ (devProb_nonneg alg _ halg j _ _ _)
          (devProb_sum alg _ halg j _ _ _)
        intro a
        have hr := (hG.r_mem j ⟨h, hh⟩ s a).1
        have := le_wsum (G.P ⟨h, hh⟩ s a) _ 0 (hG.P_nonneg _ _ _) (hG.P_sum _ _ _)
          (fun s' => (ih (h+1) (by omega) k' (hist ++ [(s, a)]) s').1)
        linarith
      · apply wsum_le _ _ _ (devProb_nonneg alg _ halg j _ _ _)
          (devProb_sum alg _ halg j _ _ _)
        intro a
        have hr := (hG.r_mem j ⟨h, hh⟩ s a).2
        have := wsum_le (G.P ⟨h, hh⟩ s a) _ _ (hG.P_nonneg _ _ _) (hG.P_sum _ _ _)
          (fun s' => (ih (h+1) (by omega) k' (hist ++ [(s, a)]) s').2)
        linarith
    · rw [brW, dif_neg hh]; simp

end values

/-! ## Layer D (in progress): run-state invariants -/

lemma sum_fin_append {α : Type*} (l : List α) (x : α) (f : ℕ → α → ℝ) :
    ∑ i : Fin (l ++ [x]).length, f i.val ((l ++ [x]).get i) =
      ∑ i : Fin l.length, f i.val (l.get i) + f l.length x := by
  have hl : l.length + 1 = (l ++ [x]).length := by simp
  rw [← Fin.sum_congr' _ hl, Fin.sum_univ_castSucc]
  simp [List.getElem_append_left, List.getElem_append_right]

section gap
variable {G : Game} (β : Fin G.m → ℕ → ℝ) {K : ℕ} (τ : Fin K → Episode G)

/-- `V ≤ Ṽ` and `Ṽ̲ ≤ V̲` in every run state (clipping only shrinks the gap). -/
lemma clip_inv (k : ℕ) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ k).vUp j h s ≤ (runState G β τ k).vTildeUp j h s ∧
      (runState G β τ k).vTildeLow j h s ≤ (runState G β τ k).vLow j h s := by
  induction k with
  | zero => simp [runState, RunState.init]
  | succ k ih =>
    simp only [runState]
    split_ifs with hk
    · simp only [episodeUpdate]
      split_ifs with he
      · exact ⟨min_le_right _ _, le_max_right _ _⟩
      · exact ih
    · exact ih

/-- The weighted-sum form of `Ṽ − Ṽ̲` for the visit list `l` of `(h, s)`. -/
noncomputable def gapSum (j : Fin G.m) (h : Fin G.H) (l : List (Fin K)) : ℝ :=
  lrW G.H l.length 0 * ((G.H : ℝ) - h.val) +
    ∑ i : Fin l.length, lrW G.H l.length (i.val + 1) *
      ((runState G β τ (l.get i).val).vUpAfter j (τ (l.get i)) h -
        (runState G β τ (l.get i).val).vLowAfter j (τ (l.get i)) h + 2 * β j (i.val + 1))

lemma gapSum_append (j : Fin G.m) (h : Fin G.H) (l : List (Fin K)) (x : Fin K) :
    gapSum β τ j h (l ++ [x]) = (1 - lr G.H (l.length + 1)) * gapSum β τ j h l +
      lr G.H (l.length + 1) * ((runState G β τ x.val).vUpAfter j (τ x) h -
        (runState G β τ x.val).vLowAfter j (τ x) h + 2 * β j (l.length + 1)) := by
  unfold gapSum
  have key := sum_fin_append l x (fun (i : ℕ) (k' : Fin K) =>
    lrW G.H (l ++ [x]).length (i + 1) *
      ((runState G β τ k'.val).vUpAfter j (τ k') h -
        (runState G β τ k'.val).vLowAfter j (τ k') h + 2 * β j (i + 1)))
  beta_reduce at key
  rw [key]
  simp only [List.length_append, List.length_singleton]
  rw [lrW_zero_succ, lrW_self G.H (l.length + 1) (by omega)]
  have hs : ∑ i : Fin l.length, lrW G.H (l.length + 1) (i.val + 1) *
      ((runState G β τ (l.get i).val).vUpAfter j (τ (l.get i)) h -
        (runState G β τ (l.get i).val).vLowAfter j (τ (l.get i)) h + 2 * β j (i.val + 1)) =
      (1 - lr G.H (l.length + 1)) * ∑ i : Fin l.length, lrW G.H l.length (i.val + 1) *
      ((runState G β τ (l.get i).val).vUpAfter j (τ (l.get i)) h -
        (runState G β τ (l.get i).val).vLowAfter j (τ (l.get i)) h + 2 * β j (i.val + 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [lrW_succ_of_le G.H l.length (i.val + 1) (by omega) (by omega)]; ring)
  rw [hs]
  ring

/-- `Ṽ − Ṽ̲ = α^0_t (H − h) + ∑_i α^i_t (V_{h+1} − V̲_{h+1} + 2β_i)` (exact, every run state). -/
lemma tilde_gap (k : ℕ) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ k).vTildeUp j h s - (runState G β τ k).vTildeLow j h s =
      gapSum β τ j h ((runState G β τ k).visits h s) := by
  induction k with
  | zero =>
    simp [runState, RunState.init, gapSum, lrW_zero_zero]
    exact Finset.sum_eq_zero (fun i _ => absurd i.isLt (by simp))
  | succ k ih =>
    by_cases hk : k < K
    · have hrs : runState G β τ (k + 1) =
          episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩) := by
        simp [runState, hk]
      rw [hrs]
      by_cases he : (τ ⟨k, hk⟩ h).1 = s
      · have hv : (episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩)).visits h s =
            (runState G β τ k).visits h s ++ [⟨k, hk⟩] := by
          simp [episodeUpdate, he]
        rw [hv, gapSum_append, ← ih]
        simp only [episodeUpdate, he, if_true, RunState.N]
        ring
      · have hv : (episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩)).visits h s =
            (runState G β τ k).visits h s := by
          simp [episodeUpdate, he]
        rw [hv, ← ih]
        simp [episodeUpdate, he]
    · have hrs : runState G β τ (k + 1) = runState G β τ k := by simp [runState, hk]
      rw [hrs]; exact ih

lemma vgap_le (k : ℕ) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ k).vUp j h s - (runState G β τ k).vLow j h s ≤
      gapSum β τ j h ((runState G β τ k).visits h s) := by
  have h1 := clip_inv β τ k j h s
  have h2 := tilde_gap β τ k j h s
  linarith [h1.1, h1.2]

lemma after_le_gapAt (k' : Fin K) (j : Fin G.m) (h : Fin G.H) :
    (runState G β τ k'.val).vUpAfter j (τ k') h -
        (runState G β τ k'.val).vLowAfter j (τ k') h ≤ gapAt G β τ k' (h.val + 1) := by
  unfold RunState.vUpAfter RunState.vLowAfter gapAt
  split_ifs with hh
  · exact le_ciSup (f := fun j : Fin G.m =>
      (runState G β τ k'.val).vUp j ⟨h.val + 1, hh⟩ (τ k' ⟨h.val + 1, hh⟩).1 -
        (runState G β τ k'.val).vLow j ⟨h.val + 1, hh⟩ (τ k' ⟨h.val + 1, hh⟩).1)
      (Set.finite_range _).bddAbove j
  · simp

/-- The gap recursion (proof of Thm 6, p. 22): with `l` the earlier visits of `(h, s^k_h)` and
`b` any bound on the weighted bonus sums of all players. -/
lemma gapAt_le (hm : 0 < G.m) (k : Fin K) (h : Fin G.H) (b : ℝ)
    (hb : ∀ j, ∑ i : Fin ((runState G β τ k.val).visits h (τ k h).1).length,
      lrW G.H ((runState G β τ k.val).visits h (τ k h).1).length (i.val + 1) * β j (i.val + 1) ≤ b) :
    gapAt G β τ k h.val ≤
      lrW G.H ((runState G β τ k.val).visits h (τ k h).1).length 0 * ((G.H : ℝ) - h.val) +
      ∑ i : Fin ((runState G β τ k.val).visits h (τ k h).1).length,
        lrW G.H ((runState G β τ k.val).visits h (τ k h).1).length (i.val + 1) *
          gapAt G β τ (((runState G β τ k.val).visits h (τ k h).1).get i) (h.val + 1) + 2 * b := by
  have : Nonempty (Fin G.m) := ⟨⟨0, hm⟩⟩
  unfold gapAt
  rw [dif_pos h.isLt]
  simp only [Fin.eta]
  apply ciSup_le
  intro j
  refine (vgap_le β τ k.val j h _).trans ?_
  unfold gapSum
  have h1 : ∑ i : Fin ((runState G β τ k.val).visits h (τ k h).1).length,
      lrW G.H ((runState G β τ k.val).visits h (τ k h).1).length (i.val + 1) *
        ((runState G β τ (((runState G β τ k.val).visits h (τ k h).1).get i).val).vUpAfter j
            (τ (((runState G β τ k.val).visits h (τ k h).1).get i)) h -
          (runState G β τ (((runState G β τ k.val).visits h (τ k h).1).get i).val).vLowAfter j
            (τ (((runState G β τ k.val).visits h (τ k h).1).get i)) h + 2 * β j (i.val + 1)) ≤
      ∑ i : Fin ((runState G β τ k.val).visits h (τ k h).1).length,
        lrW G.H ((runState G β τ k.val).visits h (τ k h).1).length (i.val + 1) *
          (if hh : h.val + 1 < G.H then ⨆ j : Fin G.m,
            ((runState G β τ (((runState G β τ k.val).visits h (τ k h).1).get i).val).vUp j
                ⟨h.val + 1, hh⟩ (τ (((runState G β τ k.val).visits h (τ k h).1).get i)
                  ⟨h.val + 1, hh⟩).1 -
              (runState G β τ (((runState G β τ k.val).visits h (τ k h).1).get i).val).vLow j
                ⟨h.val + 1, hh⟩ (τ (((runState G β τ k.val).visits h (τ k h).1).get i)
                  ⟨h.val + 1, hh⟩).1) else 0) +
        2 * ∑ i : Fin ((runState G β τ k.val).visits h (τ k h).1).length,
          lrW G.H ((runState G β τ k.val).visits h (τ k h).1).length (i.val + 1) *
            β j (i.val + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hg := after_le_gapAt β τ (((runState G β τ k.val).visits h (τ k h).1).get i) j h
    unfold gapAt at hg
    have hw := lrW_nonneg G.H ((runState G β τ k.val).visits h (τ k h).1).length (i.val + 1)
    have := mul_le_mul_of_nonneg_left hg hw
    linarith
  linarith [hb j]

end gap


/-! ## Layer E (in progress): visit lists and the summation -/

section visit
variable {K : ℕ} {α : Type*} [DecidableEq α] (c : Fin K → α)

/-- The visit list of class `s` before episode `k` (same recursion as `RunState.visits`). -/
def visList (s : α) : ℕ → List (Fin K)
  | 0 => []
  | k + 1 => if hk : k < K then
      (if c ⟨k, hk⟩ = s then visList s k ++ [⟨k, hk⟩] else visList s k) else visList s k

lemma visList_succ (s : α) (k : ℕ) : visList c s (k + 1) = if hk : k < K then
      (if c ⟨k, hk⟩ = s then visList c s k ++ [⟨k, hk⟩] else visList c s k) else
        visList c s k := rfl

lemma mem_visList (s : α) (k : ℕ) (k' : Fin K) :
    k' ∈ visList c s k ↔ k'.val < k ∧ c k' = s := by
  have hk'K := k'.isLt
  induction k with
  | zero => simp [visList]
  | succ k ih =>
    rw [visList_succ]
    split_ifs with hk hc
    · simp only [List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨by omega, h2⟩
        · exact ⟨by simp, hc⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Fin.ext h1)
    · simp only [ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
        · exact ⟨h1, h2⟩
        · have hkk : (⟨k, hk⟩ : Fin K) = k' := Fin.ext h1.symm
          exact (hc (by rw [hkk]; exact h2)).elim
    · simp only [ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma visList_nodup (s : α) (k : ℕ) : (visList c s k).Nodup := by
  induction k with
  | zero => simp [visList]
  | succ k ih =>
    rw [visList_succ]
    split_ifs with hk hc
    · rw [List.nodup_append_comm]
      refine List.Nodup.cons ?_ ih
      intro hm
      have := ((mem_visList c s k _).mp hm).1
      simp at this
    · exact ih
    · exact ih

lemma visList_prefix (s : α) (k d : ℕ) : visList c s k <+: visList c s (k + d) := by
  induction d with
  | zero => exact List.prefix_refl _
  | succ d ih =>
    refine ih.trans ?_
    rw [show k + (d + 1) = (k + d) + 1 by omega, visList_succ]
    split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
    · exact List.prefix_refl _

lemma visList_split (s : α) (k' : Fin K) (hc : c k' = s) :
    ∃ rest, visList c s K = visList c s k'.val ++ k' :: rest := by
  obtain ⟨rest, hr⟩ := visList_prefix c s (k'.val + 1) (K - (k'.val + 1))
  refine ⟨rest, ?_⟩
  rw [show k'.val + 1 + (K - (k'.val + 1)) = K by omega] at hr
  rw [← hr, visList_succ, dif_pos k'.isLt]
  simp [hc]

lemma idx_of_split {β : Type*} (L rest : List β) (x : β) (hnd : (L ++ x :: rest).Nodup)
    (t : Fin (L ++ x :: rest).length) (ht : (L ++ x :: rest).get t = x) :
    (L ++ x :: rest).take t.val = L := by
  have h1 : (L ++ x :: rest)[L.length]'(by simp) = x := by simp
  rw [List.get_eq_getElem] at ht
  have h2 : t.val = L.length := (List.Nodup.getElem_inj_iff hnd).mp (ht.trans h1.symm)
  rw [h2]
  simp

lemma visList_take_get (s : α) (t : Fin (visList c s K).length) :
    (visList c s K).take t.val = visList c s ((visList c s K).get t).val := by
  have key : ∀ (V : List (Fin K)), V = visList c s K → ∀ (t : Fin V.length),
      V.take t.val = visList c s (V.get t).val := by
    intro V hV t
    have hmem : V.get t ∈ visList c s K := by rw [← hV]; exact List.get_mem _ _
    have hc : c (V.get t) = s := ((mem_visList c s K _).mp hmem).2
    obtain ⟨rest, hr⟩ := visList_split c s _ hc
    have hnd := visList_nodup c s K
    generalize hx : V.get t = x at hr hc ⊢
    rw [hr] at hV hnd
    subst hV
    exact idx_of_split _ rest x hnd t hx
  exact key _ rfl t

lemma sum_class (s : α) (Φ : List (Fin K) → Fin K → ℝ) :
    ∑ k ∈ Finset.univ.filter (fun k => c k = s), Φ (visList c s k.val) k =
      ∑ t : Fin (visList c s K).length,
        Φ ((visList c s K).take t.val) ((visList c s K).get t) := by
  symm
  refine Finset.sum_bij (fun t _ => (visList c s K).get t) ?_ ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ((mem_visList c s K _).mp (List.get_mem _ _)).2
  · intro t₁ _ t₂ _ h
    exact (visList_nodup c s K).get_inj_iff.mp h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨t, ht⟩ := List.mem_iff_get.mp ((mem_visList c s K k).mpr ⟨k.isLt, hk⟩)
    exact ⟨t, Finset.mem_univ _, ht⟩
  · intro t _
    rw [visList_take_get]

end visit

lemma sum_fin_list {β : Type*} (l : List β) (g : ℕ → β → ℝ) :
    ∑ i : Fin l.length, g i.val (l.get i) =
      ∑ i ∈ Finset.range l.length, (l[i]?).elim 0 (g i) := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

lemma swap_bound (H N : ℕ) (hH : 1 ≤ H) (F : ℕ → ℝ) (hF : ∀ i, 0 ≤ F i) :
    ∑ t ∈ Finset.range N, ∑ i ∈ Finset.range t, lrW H t (i + 1) * F i ≤
      (1 + 1 / (H : ℝ)) * ∑ i ∈ Finset.range N, F i := by
  rw [Finset.sum_comm' (t' := Finset.range N) (s' := fun i => Finset.Ioo i N)]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    have hs : ∑ t ∈ Finset.Ioo i N, lrW H t (i + 1) ≤ 1 + 1 / (H : ℝ) := by
      calc ∑ t ∈ Finset.Ioo i N, lrW H t (i + 1)
            ≤ ∑ t ∈ Finset.Icc (i + 1) N, lrW H t (i + 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun t ht => by simp only [Finset.mem_Ioo, Finset.mem_Icc] at ht ⊢; omega)
              (fun t _ _ => lrW_nonneg _ _ _)
        _ ≤ 1 + 1 / (H : ℝ) := lrW_tail_sum H (i + 1) hH (by omega) N
    exact mul_le_mul_of_nonneg_right hs (hF i)
  · intro t i
    simp only [Finset.mem_range, Finset.mem_Ioo]
    omega


section visit2
variable {K : ℕ} {α : Type*} [DecidableEq α] (c : Fin K → α)

lemma visList_length_le (s : α) (k : ℕ) : (visList c s k).length ≤ k := by
  induction k with
  | zero => simp [visList]
  | succ k ih =>
    rw [visList_succ]
    split_ifs
    · simp only [List.length_append, List.length_singleton]; omega
    · omega
    · omega

lemma sum_lrW_zero (H N : ℕ) : ∑ t ∈ Finset.range N, lrW H t 0 ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [lrW_zero_zero]
    · rw [lrW_zero_of_pos H N hN]; linarith

/-- In each class only the first visit carries the initial weight `α^0`. -/
lemma class_first_bound (H : ℕ) (s : α) :
    ∑ k ∈ Finset.univ.filter (fun k => c k = s), lrW H (visList c s k.val).length 0 ≤ 1 := by
  have e := sum_class c s (fun l _ => lrW H l.length 0)
  beta_reduce at e
  rw [e]
  calc ∑ t : Fin (visList c s K).length, lrW H ((visList c s K).take t.val).length 0
        = ∑ t : Fin (visList c s K).length, lrW H t.val 0 :=
          Finset.sum_congr rfl (fun t _ => by simp [t.isLt.le])
    _ ≤ 1 := (Fin.sum_univ_eq_sum_range (fun t => lrW H t 0) _).trans_le (sum_lrW_zero H _)

/-- Per-class summation of the propagated gaps (Jin et al. 2018, proof of Thm 1). -/
lemma class_sum_bound (H : ℕ) (hH : 1 ≤ H) (s : α) (f : Fin K → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ k ∈ Finset.univ.filter (fun k => c k = s),
      ∑ i : Fin (visList c s k.val).length,
        lrW H (visList c s k.val).length (i.val + 1) * f ((visList c s k.val).get i) ≤
      (1 + 1 / (H : ℝ)) * ∑ k ∈ Finset.univ.filter (fun k => c k = s), f k := by
  have e1 := sum_class c s
    (fun l _ => ∑ i : Fin l.length, lrW H l.length (i.val + 1) * f (l.get i))
  have e2 := sum_class c s (fun _ k => f k)
  beta_reduce at e1 e2
  rw [e1, e2]
  set V := visList c s K with hV
  have h1 : ∀ t : Fin V.length, ∑ i : Fin (V.take t.val).length,
      lrW H (V.take t.val).length (i.val + 1) * f ((V.take t.val).get i) =
      ∑ i ∈ Finset.range t.val, lrW H t.val (i + 1) * (V[i]?).elim 0 f := by
    intro t
    have e3 := sum_fin_list (V.take t.val) (fun i k' => lrW H (V.take t.val).length (i + 1) * f k')
    beta_reduce at e3
    rw [e3]
    have hlen : (V.take t.val).length = t.val := by simp [t.isLt.le]
    rw [hlen]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have htk : (V.take t.val)[i]? = V[i]? := by simp [hi]
    rw [htk]
    cases V[i]? <;> simp
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => h1 t)]
  have e4 := Fin.sum_univ_eq_sum_range
    (fun t => ∑ i ∈ Finset.range t, lrW H t (i + 1) * (V[i]?).elim 0 f) V.length
  beta_reduce at e4
  rw [e4]
  have e5 : ∑ t : Fin V.length, f (V.get t) = ∑ i ∈ Finset.range V.length, (V[i]?).elim 0 f :=
    sum_fin_list V (fun _ k' => f k')
  rw [e5]
  exact swap_bound H V.length hH _ (fun i => by cases V[i]? <;> simp [hf])

end visit2

section gapsum
variable {G : Game} (β : Fin G.m → ℕ → ℝ) {K : ℕ} (τ : Fin K → Episode G)

lemma visits_eq (k : ℕ) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ k).visits h s = visList (fun k' => (τ k' h).1) s k := by
  induction k with
  | zero => simp [runState, RunState.init, visList]
  | succ k ih =>
    rw [visList_succ]
    by_cases hk : k < K
    · rw [dif_pos hk]
      simp only [runState, dif_pos hk, episodeUpdate, ih]
    · rw [dif_neg hk]
      simp only [runState, dif_neg hk, ih]

end gapsum


lemma class_len_sum {K : ℕ} {α : Type*} [DecidableEq α] (c : Fin K → α) (s : α) (bb : ℕ → ℝ) :
    ∑ k ∈ Finset.univ.filter (fun k => c k = s), bb (visList c s k.val).length =
      ∑ t ∈ Finset.range (visList c s K).length, bb t := by
  have e := sum_class c s (fun l _ => bb l.length)
  beta_reduce at e
  rw [e, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun t _ => by simp [t.isLt.le])

section gapsum2
variable {G : Game} (β : Fin G.m → ℕ → ℝ) {K : ℕ} (τ : Fin K → Episode G)

/-- `max(δ^k_h, 0)`: the gap recursion holds for it and it is nonnegative. -/
noncomputable def gplus (k : Fin K) (h : ℕ) : ℝ := max (gapAt G β τ k h) 0

lemma gplus_nonneg (k : Fin K) (h : ℕ) : 0 ≤ gplus β τ k h := le_max_right _ _

/-- The bound of the gap recursion as a function of the visit list. -/
noncomputable def recT (h : Fin G.H) (bb : ℕ → ℝ) (l : List (Fin K)) : ℝ :=
  lrW G.H l.length 0 * ((G.H : ℝ) - h.val) +
    ∑ i : Fin l.length, lrW G.H l.length (i.val + 1) * gplus β τ (l.get i) (h.val + 1) +
    2 * bb l.length

lemma gplus_le_recT (hm : 0 < G.m) (k : Fin K) (h : Fin G.H) (bb : ℕ → ℝ)
    (hbb0 : ∀ n, 0 ≤ bb n)
    (hbb : ∀ j (n : ℕ), n < K → ∑ i : Fin n, lrW G.H n (i.val + 1) * β j (i.val + 1) ≤ bb n) :
    gplus β τ k h.val ≤ recT β τ h bb (visList (fun k' => (τ k' h).1) (τ k h).1 k.val) := by
  rw [← visits_eq β τ k.val h (τ k h).1]
  have hn : ((runState G β τ k.val).visits h (τ k h).1).length < K := by
    rw [visits_eq]; exact (visList_length_le _ _ _).trans_lt k.isLt
  have hg := gapAt_le β τ hm k h (bb _) (fun j => hbb j _ hn)
  unfold recT gplus
  have hHh : (0:ℝ) ≤ (G.H : ℝ) - h.val := by
    have := h.isLt; rw [sub_nonneg]; exact_mod_cast this.le
  apply max_le
  · refine hg.trans ?_
    have : ∑ i : Fin ((runState G β τ k.val).visits h (τ k h).1).length,
        lrW G.H ((runState G β τ k.val).visits h (τ k h).1).length (i.val + 1) *
          gapAt G β τ (((runState G β τ k.val).visits h (τ k h).1).get i) (h.val + 1) ≤
        ∑ i : Fin ((runState G β τ k.val).visits h (τ k h).1).length,
        lrW G.H ((runState G β τ k.val).visits h (τ k h).1).length (i.val + 1) *
          max (gapAt G β τ (((runState G β τ k.val).visits h (τ k h).1).get i) (h.val + 1)) 0 :=
      Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (le_max_left _ _) (lrW_nonneg _ _ _))
    linarith
  · have h1 := mul_nonneg (lrW_nonneg G.H ((runState G β τ k.val).visits h (τ k h).1).length 0) hHh
    have h2 : 0 ≤ ∑ i : Fin ((runState G β τ k.val).visits h (τ k h).1).length,
        lrW G.H ((runState G β τ k.val).visits h (τ k h).1).length (i.val + 1) *
          max (gapAt G β τ (((runState G β τ k.val).visits h (τ k h).1).get i) (h.val + 1)) 0 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (lrW_nonneg _ _ _) (le_max_right _ _))
    linarith [hbb0 ((runState G β τ k.val).visits h (τ k h).1).length]

/-- One step of the summation: `∑_k δ⁺_h ≤ S(H − h) + (1 + 1/H) ∑_k δ⁺_{h+1} + 2 ∑_s ∑_{t < N_s} b_t`. -/
lemma sum_gplus_le (hm : 0 < G.m) (hH : 1 ≤ G.H) (h : Fin G.H) (bb : ℕ → ℝ)
    (hbb0 : ∀ n, 0 ≤ bb n)
    (hbb : ∀ j (n : ℕ), n < K → ∑ i : Fin n, lrW G.H n (i.val + 1) * β j (i.val + 1) ≤ bb n) :
    ∑ k : Fin K, gplus β τ k h.val ≤ (G.S : ℝ) * ((G.H : ℝ) - h.val) +
      (1 + 1 / (G.H : ℝ)) * ∑ k : Fin K, gplus β τ k (h.val + 1) +
      2 * ∑ s : Fin G.S, ∑ t ∈ Finset.range (visList (fun k' => (τ k' h).1) s K).length, bb t := by
  set c : Fin K → Fin G.S := fun k' => (τ k' h).1 with hc
  calc ∑ k : Fin K, gplus β τ k h.val ≤ ∑ k : Fin K, recT β τ h bb (visList c (c k) k.val) :=
        Finset.sum_le_sum (fun k _ => gplus_le_recT β τ hm k h bb hbb0 hbb)
    _ = ∑ s : Fin G.S, ∑ k ∈ Finset.univ.filter (fun k => c k = s),
          recT β τ h bb (visList c s k.val) := by
        rw [← Finset.sum_fiberwise Finset.univ c]
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun k hk => ?_))
        rw [(Finset.mem_filter.mp hk).2]
    _ ≤ ∑ s : Fin G.S, (((G.H : ℝ) - h.val) + (1 + 1 / (G.H : ℝ)) *
          ∑ k ∈ Finset.univ.filter (fun k => c k = s), gplus β τ k (h.val + 1) +
          2 * ∑ t ∈ Finset.range (visList c s K).length, bb t) := by
        apply Finset.sum_le_sum
        intro s _
        unfold recT
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
          class_len_sum]
        have hHh : (0:ℝ) ≤ (G.H : ℝ) - h.val := by
          have := h.isLt; rw [sub_nonneg]; exact_mod_cast this.le
        have h1 := class_first_bound c G.H s
        have h2 := class_sum_bound c G.H hH s (fun k => gplus β τ k (h.val + 1))
          (fun k => gplus_nonneg β τ k _)
        nlinarith
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_fiberwise]

end gapsum2


/-- Unrolling `x_h ≤ a_h + q x_{h+1}` from `h = H − d` to `H` (with `x_H ≤ 0`). -/
lemma unroll (H : ℕ) (q : ℝ) (hq : 1 ≤ q) (x a : ℕ → ℝ) (ha : ∀ h, 0 ≤ a h) (hxH : x H ≤ 0)
    (hx : ∀ h, h < H → x h ≤ a h + q * x (h + 1)) :
    ∀ d, d ≤ H → x (H - d) ≤ q ^ d * ∑ i ∈ Finset.Ico (H - d) H, a i := by
  intro d
  induction d with
  | zero => intro _; simpa using hxH
  | succ d ih =>
    intro hd
    have h1 := hx (H - (d + 1)) (by omega)
    rw [show H - (d + 1) + 1 = H - d by omega] at h1
    have h2 := ih (by omega)
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : H - (d + 1) < H),
      show H - (d + 1) + 1 = H - d by omega]
    have hq0 : 0 ≤ q := by linarith
    calc x (H - (d + 1)) ≤ a (H - (d + 1)) + q * (q ^ d * ∑ i ∈ Finset.Ico (H - d) H, a i) := by
          have := mul_le_mul_of_nonneg_left h2 hq0; linarith
      _ ≤ q ^ (d + 1) * (a (H - (d + 1)) + ∑ i ∈ Finset.Ico (H - d) H, a i) := by
          have hqd1 : 1 ≤ q ^ (d + 1) := one_le_pow₀ hq
          have h3 := mul_le_mul_of_nonneg_right hqd1 (ha (H - (d + 1)))
          have h4 : q * (q ^ d * ∑ i ∈ Finset.Ico (H - d) H, a i) =
              q ^ (d + 1) * ∑ i ∈ Finset.Ico (H - d) H, a i := by ring
          rw [h4, mul_add]; linarith

lemma one_add_inv_pow_le (H : ℕ) (hH : 1 ≤ H) : (1 + 1 / (H : ℝ)) ^ H ≤ Real.exp 1 := by
  have hH' : (0:ℝ) < H := by exact_mod_cast hH
  calc (1 + 1 / (H : ℝ)) ^ H ≤ (Real.exp (1 / H)) ^ H :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (H:ℝ))]) H
    _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp


section total
variable {G : Game} (β : Fin G.m → ℕ → ℝ) {K : ℕ} (τ : Fin K → Episode G)

lemma gplus_top (k : Fin K) : gplus β τ k G.H = 0 := by
  unfold gplus gapAt; simp

/-- Number of visits of state `s` at step `h` over all `K` episodes. -/
noncomputable def nvis (h : Fin G.H) (s : Fin G.S) : ℕ :=
  (visList (fun k' => (τ k' h).1) s K).length

/-- Per-step additive term of the summation recursion. -/
noncomputable def aStep (bb : ℕ → ℝ) (h : ℕ) : ℝ :=
  if hh : h < G.H then (G.S : ℝ) * ((G.H : ℝ) - h) +
    2 * ∑ s : Fin G.S, ∑ t ∈ Finset.range (nvis τ ⟨h, hh⟩ s), bb t else 0

lemma aStep_nonneg (bb : ℕ → ℝ) (hbb0 : ∀ n, 0 ≤ bb n) (h : ℕ) : 0 ≤ aStep τ bb h := by
  unfold aStep
  split_ifs with hh
  · have h1 : (0:ℝ) ≤ (G.H : ℝ) - h := by rw [sub_nonneg]; exact_mod_cast hh.le
    have h2 : 0 ≤ ∑ s : Fin G.S, ∑ t ∈ Finset.range (nvis τ ⟨h, hh⟩ s), bb t :=
      Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun t _ => hbb0 t))
    have h3 := mul_nonneg (Nat.cast_nonneg G.S : (0:ℝ) ≤ G.S) h1
    linarith
  · exact le_rfl

/-- Summation over all steps: `∑_k δ⁺_0 ≤ e ∑_{h<H} a_h`. -/
lemma sum_gplus_total (hm : 0 < G.m) (hH : 1 ≤ G.H) (bb : ℕ → ℝ) (hbb0 : ∀ n, 0 ≤ bb n)
    (hbb : ∀ j (n : ℕ), n < K → ∑ i : Fin n, lrW G.H n (i.val + 1) * β j (i.val + 1) ≤ bb n) :
    ∑ k : Fin K, gplus β τ k 0 ≤ Real.exp 1 * ∑ h ∈ Finset.range G.H, aStep τ bb h := by
  have hq : (1:ℝ) ≤ 1 + 1 / (G.H : ℝ) := by
    have : (0:ℝ) ≤ 1 / (G.H:ℝ) := by positivity
    linarith
  have hx : ∀ h, h < G.H → ∑ k : Fin K, gplus β τ k h ≤
      aStep τ bb h + (1 + 1 / (G.H:ℝ)) * ∑ k : Fin K, gplus β τ k (h + 1) := by
    intro h hh
    have := sum_gplus_le β τ hm hH ⟨h, hh⟩ bb hbb0 hbb
    dsimp only at this
    simp only [aStep, dif_pos hh]
    unfold nvis
    linarith
  have hu := unroll G.H (1 + 1 / (G.H : ℝ)) hq
    (fun h => ∑ k : Fin K, gplus β τ k h) (aStep τ bb) (aStep_nonneg τ bb hbb0)
    (by simp [gplus_top]) hx G.H le_rfl
  simp only [Nat.sub_self, ← Finset.range_eq_Ico] at hu
  refine hu.trans ?_
  apply mul_le_mul_of_nonneg_right (one_add_inv_pow_le G.H hH)
  exact Finset.sum_nonneg (fun h _ => aStep_nonneg τ bb hbb0 h)

end total

lemma visList_length_eq_card {K : ℕ} {α : Type*} [DecidableEq α] (c : Fin K → α) (s : α) :
    (visList c s K).length = (Finset.univ.filter (fun k => c k = s)).card := by
  have e := class_len_sum c s (fun _ => (1:ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range] at e
  exact_mod_cast e.symm

lemma sum_nvis {G : Game} {K : ℕ} (τ : Fin K → Episode G) (h : Fin G.H) :
    ∑ s : Fin G.S, nvis τ h s = K := by
  unfold nvis
  simp only [visList_length_eq_card]
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := fun k : Fin K => (τ k h).1) (fun k _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

lemma range_succ_eq (f : ℕ → ℝ) (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), f t = f 0 + ∑ t ∈ Finset.Icc 1 N, f t := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]; ring

lemma sum_inv_sqrt_le (N : ℕ) : ∑ t ∈ Finset.Icc 1 N, 1 / Real.sqrt t ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha := Real.sqrt_nonneg (n : ℝ)
    have hb : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hsa := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hsb : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have key : 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((n + 1 : ℕ) : ℝ) - 2 * Real.sqrt n := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n)]
    linarith

/-- `∑_{t<N} b_t ≤ c (H Ξ + 2 √(X N))` when `b_t ≤ c (H ξ_t + √(X/t))` for `1 ≤ t ≤ N`, `b_0 = 0`. -/
lemma bonus_sum (H X c Ξ' : ℝ) (hc : 0 ≤ c) (hX : 0 ≤ X) (hH : 0 ≤ H) (ξ' : ℕ → ℝ) (N : ℕ)
    (hΞ : ∑ t ∈ Finset.Icc 1 N, ξ' t ≤ Ξ') (bb : ℕ → ℝ) (hbb0 : ∀ t, 0 ≤ bb t) (hb0 : bb 0 = 0)
    (hbb : ∀ t, 1 ≤ t → t ≤ N → bb t ≤ c * (H * ξ' t + Real.sqrt (X / t))) :
    ∑ t ∈ Finset.range N, bb t ≤ c * (H * Ξ' + 2 * Real.sqrt (X * N)) := by
  have e1 : ∑ t ∈ Finset.range N, bb t ≤ ∑ t ∈ Finset.range (N + 1), bb t := by
    rw [Finset.sum_range_succ]; linarith [hbb0 N]
  rw [range_succ_eq, hb0, zero_add] at e1
  have e2 : ∑ t ∈ Finset.Icc 1 N, bb t ≤
      ∑ t ∈ Finset.Icc 1 N, c * (H * ξ' t + Real.sqrt X * (1 / Real.sqrt t)) := by
    apply Finset.sum_le_sum; intro t ht
    rw [Finset.mem_Icc] at ht
    have := hbb t ht.1 ht.2
    rwa [Real.sqrt_div hX, div_eq_mul_one_div] at this
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at e2
  have e3 := sum_inv_sqrt_le N
  rw [Real.sqrt_mul hX]
  have hsX := Real.sqrt_nonneg X
  have e4 : H * ∑ t ∈ Finset.Icc 1 N, ξ' t + Real.sqrt X * ∑ t ∈ Finset.Icc 1 N, 1 / Real.sqrt t
      ≤ H * Ξ' + 2 * (Real.sqrt X * Real.sqrt N) := by
    linarith [mul_le_mul_of_nonneg_left hΞ hH, mul_le_mul_of_nonneg_left e3 hsX]
  linarith [mul_le_mul_of_nonneg_left e4 hc]

/-- Jensen over `S` classes with uniform weights. -/
lemma jensen_fin (S : ℕ) (hS : 1 ≤ S) (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f) (N : Fin S → ℕ) :
    ∑ s : Fin S, f (N s) ≤ S * f ((∑ s : Fin S, (N s : ℝ)) / S) := by
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  have := hf.le_map_sum (t := Finset.univ) (w := fun _ => 1 / (S:ℝ)) (p := fun s => (N s : ℝ))
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_one_div_cancel hS'.ne')
    (fun s _ => Set.mem_Ici.mpr (Nat.cast_nonneg _))
  simp only [smul_eq_mul, ← Finset.mul_sum] at this
  rw [show (∑ s : Fin S, (N s : ℝ)) / S = 1 / S * ∑ s : Fin S, (N s : ℝ) by ring]
  have h2 := mul_le_mul_of_nonneg_left this hS'.le
  rwa [← mul_assoc, mul_one_div_cancel hS'.ne', one_mul] at h2

lemma sum_sqrt_le (S : ℕ) (hS : 1 ≤ S) (N : Fin S → ℕ) :
    ∑ s : Fin S, Real.sqrt (N s) ≤ Real.sqrt (S * ∑ s : Fin S, (N s : ℝ)) := by
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  have := jensen_fin S hS Real.sqrt Real.strictConcaveOn_sqrt.concaveOn N
  refine this.trans (le_of_eq ?_)
  have hsum : 0 ≤ ∑ s : Fin S, (N s : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  rw [Real.sqrt_div' _ hS'.le]
  have hsS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS'.le
  have hpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS'
  rw [Real.sqrt_mul hS'.le]
  field_simp
  rw [hsS]; ring

/-- Deterministic summation bound (layer E): `∑_k δ⁺_0 ≤ e H (S H + 2c(H S Ξ(K/S) + 2√X √(SK)))`. -/
lemma det_bound {G : Game} (β : Fin G.m → ℕ → ℝ) {K : ℕ} (τ : Fin K → Episode G)
    (hm : 0 < G.m) (hH : 1 ≤ G.H) (hS : 1 ≤ G.S) (c X : ℝ) (hc : 0 ≤ c) (hX : 0 ≤ X)
    (ξ' : ℕ → ℝ) (Ξ' : ℝ → ℝ) (hΞc : ConcaveOn ℝ (Set.Ici 0) Ξ')
    (hΞ : ∀ N : ℕ, ∑ t ∈ Finset.Icc 1 N, ξ' t ≤ Ξ' N)
    (bb : ℕ → ℝ) (hbb0 : ∀ t, 0 ≤ bb t) (hb0 : bb 0 = 0)
    (hbbc : ∀ t, 1 ≤ t → t ≤ K → bb t ≤ c * ((G.H:ℝ) * ξ' t + Real.sqrt (X / t)))
    (hbb : ∀ j (n : ℕ), n < K → ∑ i : Fin n, lrW G.H n (i.val + 1) * β j (i.val + 1) ≤ bb n) :
    ∑ k : Fin K, gplus β τ k 0 ≤ Real.exp 1 * ((G.H:ℝ) * ((G.S:ℝ) * G.H +
      2 * (c * ((G.H:ℝ) * (G.S * Ξ' ((K:ℝ) / G.S)) +
        2 * Real.sqrt X * Real.sqrt (G.S * K))))) := by
  refine (sum_gplus_total β τ hm hH bb hbb0 hbb).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
  have hstep : ∀ h ∈ Finset.range G.H, aStep τ bb h ≤ (G.S:ℝ) * G.H +
      2 * (c * ((G.H:ℝ) * (G.S * Ξ' ((K:ℝ) / G.S)) +
        2 * Real.sqrt X * Real.sqrt (G.S * K))) := by
    intro h hh
    have hh' : h < G.H := Finset.mem_range.mp hh
    simp only [aStep, dif_pos hh']
    have hsumN : ∑ s : Fin G.S, ((nvis τ ⟨h, hh'⟩ s : ℕ) : ℝ) = K := by
      rw [← Nat.cast_sum, sum_nvis]
    have hb : ∀ s : Fin G.S, ∑ t ∈ Finset.range (nvis τ ⟨h, hh'⟩ s), bb t ≤
        c * ((G.H:ℝ) * Ξ' (nvis τ ⟨h, hh'⟩ s) +
          2 * (Real.sqrt X * Real.sqrt (nvis τ ⟨h, hh'⟩ s))) := by
      intro s
      have hle : nvis τ ⟨h, hh'⟩ s ≤ K := visList_length_le _ _ _
      have := bonus_sum G.H X c (Ξ' (nvis τ ⟨h, hh'⟩ s)) hc hX (Nat.cast_nonneg _) ξ'
        (nvis τ ⟨h, hh'⟩ s) (hΞ _) bb hbb0 hb0 (fun t h1 h2 => hbbc t h1 (h2.trans hle))
      rwa [Real.sqrt_mul hX] at this
    have hJ := jensen_fin G.S hS Ξ' hΞc (nvis τ ⟨h, hh'⟩)
    have hQ := sum_sqrt_le G.S hS (nvis τ ⟨h, hh'⟩)
    rw [hsumN] at hJ hQ
    have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hb s)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
    have hHh : (G.S:ℝ) * ((G.H:ℝ) - h) ≤ G.S * G.H := by
      linarith [mul_nonneg (Nat.cast_nonneg G.S : (0:ℝ) ≤ G.S) (Nat.cast_nonneg h : (0:ℝ) ≤ h)]
    have hsX := Real.sqrt_nonneg X
    have hH0 : (0:ℝ) ≤ G.H := Nat.cast_nonneg _
    have k1 := mul_le_mul_of_nonneg_left hJ hH0
    have k2 := mul_le_mul_of_nonneg_left hQ hsX
    have k3 : (G.H:ℝ) * ∑ s : Fin G.S, Ξ' (nvis τ ⟨h, hh'⟩ s) +
        2 * (Real.sqrt X * ∑ s : Fin G.S, Real.sqrt (nvis τ ⟨h, hh'⟩ s)) ≤
        (G.H:ℝ) * (G.S * Ξ' ((K:ℝ) / G.S)) + 2 * Real.sqrt X * Real.sqrt (G.S * K) := by
      linarith
    have k4 := mul_le_mul_of_nonneg_left k3 hc
    linarith
  calc ∑ h ∈ Finset.range G.H, aStep τ bb h ≤ ∑ h ∈ Finset.range G.H, ((G.S:ℝ) * G.H +
      2 * (c * ((G.H:ℝ) * (G.S * Ξ' ((K:ℝ) / G.S)) +
        2 * Real.sqrt X * Real.sqrt (G.S * K)))) := Finset.sum_le_sum hstep
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- History-dependent kernels on `Fin n` normalise: `∑_e ∏_i g_i(e_{<i}, e_i) = 1`. -/
lemma hist_sum {X : Type*} [Fintype X] (x0 : X) : ∀ (n : ℕ) (g : Fin n → (Fin n → X) → X → ℝ),
    (∀ i e e', (∀ j : Fin n, j < i → e j = e' j) → g i e = g i e') →
    (∀ i e, ∑ y, g i e y = 1) →
    ∑ e : Fin n → X, ∏ i : Fin n, g i e (e i) = 1
  | 0, g, _, _ => by simp
  | n + 1, g, hdep, hsum => by
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => X)).sum_comp, Fintype.sum_prod_type]
    have h0 : ∀ x (e' : Fin n → X), g 0 (Fin.cons x e') = g 0 (fun _ => x0) :=
      fun x e' => hdep 0 _ _ (fun j hj => absurd hj (Fin.not_lt_zero j))
    have step : ∀ x : X, ∑ e' : Fin n → X, ∏ i : Fin (n+1),
        g i (Fin.cons x e') ((Fin.cons x e' : Fin (n+1) → X) i) = g 0 (fun _ => x0) x := by
      intro x
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, h0]
      rw [← Finset.mul_sum]
      have hrec : ∑ e' : Fin n → X, ∏ j : Fin n, g j.succ (Fin.cons x e') (e' j) = 1 := by
        refine hist_sum x0 n (fun j e' y => g j.succ (Fin.cons x e') y) ?_ (fun j e' => hsum _ _)
        intro j e' e'' hj
        apply hdep
        intro i hi
        cases i using Fin.cases with
        | zero => simp
        | succ i' => simp only [Fin.cons_succ]; exact hj i' (Fin.succ_lt_succ_iff.mp hi)
      rw [hrec, mul_one]
    exact (Finset.sum_congr rfl (fun x _ => step x)).trans (hsum 0 _)

section mass
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ}

/-- One step of an episode's path kernel under the policy of state `σ`. -/
noncomputable def pathKer (σ : RunState G K) (h : Fin G.H) (e : Episode G)
    (y : Fin G.S × G.JointAct) : ℝ :=
  (if hh : h.val = 0 then (if y.1 = G.s1 then 1 else 0)
   else G.P ⟨h.val - 1, by omega⟩ (e ⟨h.val - 1, by omega⟩).1 (e ⟨h.val - 1, by omega⟩).2 y.1) *
  RunState.jointProb alg σ h y.1 y.2

lemma pathKer_sum (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (σ : RunState G K) (h : Fin G.H)
    (e : Episode G) : ∑ y, pathKer alg σ h e y = 1 := by
  unfold pathKer
  rw [Fintype.sum_prod_type]
  by_cases hh : h.val = 0
  · simp [hh]; exact jointProb_sum alg σ halg h G.s1
  · simp only [dif_neg hh]
    calc _ = ∑ s, G.P ⟨h.val - 1, by omega⟩ (e ⟨h.val - 1, by omega⟩).1
          (e ⟨h.val - 1, by omega⟩).2 s :=
          Finset.sum_congr rfl (fun s _ => by rw [← Finset.mul_sum, jointProb_sum alg σ halg, mul_one])
      _ = 1 := hG.P_sum _ _ _

lemma pathKer_dep (σ : RunState G K) (h : Fin G.H) (e e' : Episode G)
    (he : ∀ j : Fin G.H, j < h → e j = e' j) : pathKer alg σ h e = pathKer alg σ h e' := by
  funext y; unfold pathKer
  by_cases hh : h.val = 0
  · simp only [dif_pos hh]
  · simp only [dif_neg hh]; rw [he ⟨h.val - 1, by omega⟩ (show h.val - 1 < h.val by omega)]

lemma runState_congr (β : Fin G.m → ℕ → ℝ) (τ τ' : Fin K → Episode G) : ∀ k : ℕ,
    (∀ i : Fin K, i.val < k → τ i = τ' i) → runState G β τ k = runState G β τ' k
  | 0, _ => rfl
  | k + 1, hτ => by
    simp only [runState]
    split_ifs with hk
    · rw [runState_congr β τ τ' k (fun i hi => hτ i (by omega)), hτ ⟨k, hk⟩ (by simp)]
    · exact runState_congr β τ τ' k (fun i hi => hτ i (by omega))

lemma traceWeight_eq (β : Fin G.m → ℕ → ℝ) (τ : Fin K → Episode G) :
    traceWeight G alg β τ =
      ∏ k : Fin K, ∏ h : Fin G.H, pathKer alg (runState G β τ k.val) h (τ k) (τ k h) := rfl

/-- Layer F: the training-run weights sum to one. -/
lemma traceWeight_sum (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (β : Fin G.m → ℕ → ℝ) :
    ∑ τ : Fin K → Episode G, traceWeight G alg β τ = 1 := by
  have y0 : Fin G.S × G.JointAct := (G.s1, fun j => ⟨0, hG.A_pos j⟩)
  simp only [traceWeight_eq]
  refine hist_sum (fun _ => y0) K
    (fun k τ e => ∏ h : Fin G.H, pathKer alg (runState G β τ k.val) h e (e h)) ?_ ?_
  · intro k τ τ' hk
    rw [runState_congr β τ τ' k.val (fun i hi => hk i hi)]
  · intro k τ
    exact hist_sum y0 G.H (fun h e y => pathKer alg (runState G β τ k.val) h e y)
      (fun h e e' he => pathKer_dep alg _ h e e' he)
      (fun h e => pathKer_sum alg hG halg _ h e)

end mass

section mass2
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

lemma traceWeight_nonneg (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (τ : Fin K → Episode G) :
    0 ≤ traceWeight G alg β τ := by
  rw [traceWeight_eq]
  apply Finset.prod_nonneg; intro k _
  apply Finset.prod_nonneg; intro h _
  unfold pathKer
  apply mul_nonneg
  · split_ifs <;> first | exact hG.P_nonneg _ _ _ _ | norm_num
  · exact jointProb_nonneg alg _ halg h _ _

lemma trainProb_mono (hG : G.Standing) (halg : ∀ j, (alg j).Valid)
    (E E' : (Fin K → Episode G) → Prop) (hEE : ∀ τ, E τ → E' τ) :
    trainProb G alg β K E ≤ trainProb G alg β K E' := by
  unfold trainProb
  apply Finset.sum_le_sum; intro τ _
  apply mul_le_mul_of_nonneg_left _ (traceWeight_nonneg alg β hG halg τ)
  by_cases h1 : E τ
  · have h2 := hEE τ h1; simp [h1, h2]
  · rw [if_neg h1]; split_ifs <;> norm_num

lemma trainProb_compl (hG : G.Standing) (halg : ∀ j, (alg j).Valid)
    (E : (Fin K → Episode G) → Prop) :
    trainProb G alg β K E = 1 - trainProb G alg β K (fun τ => ¬ E τ) := by
  rw [eq_sub_iff_add_eq, ← traceWeight_sum alg hG halg β]
  unfold trainProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  by_cases h1 : E τ
  · rw [if_pos h1, if_neg (not_not.mpr h1)]; ring
  · rw [if_neg h1, if_pos h1]; ring

/-- Union bound. -/
lemma trainProb_union (hG : G.Standing) (halg : ∀ j, (alg j).Valid) {ι : Type*} (s : Finset ι)
    (B : ι → (Fin K → Episode G) → Prop) :
    trainProb G alg β K (fun τ => ∃ i ∈ s, B i τ) ≤ ∑ i ∈ s, trainProb G alg β K (B i) := by
  unfold trainProb
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro τ _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (traceWeight_nonneg alg β hG halg τ)
  by_cases hex : ∃ i ∈ s, B i τ
  · obtain ⟨i, hi, hB⟩ := hex
    rw [if_pos ⟨i, hi, hB⟩]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum ?_ hi)
    · simp [hB]
    · intro j _; split_ifs <;> norm_num
  · rw [if_neg hex]; exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

/-- Good-event form: if `E` fails only on a union of events of total mass `≤ δ`, `trainProb E ≥ 1 - δ`. -/
lemma trainProb_ge (hG : G.Standing) (halg : ∀ j, (alg j).Valid) {ι : Type*} (s : Finset ι)
    (B : ι → (Fin K → Episode G) → Prop) (E : (Fin K → Episode G) → Prop)
    (hE : ∀ τ, ¬ E τ → ∃ i ∈ s, B i τ) (δ : ℝ) (hδ : ∑ i ∈ s, trainProb G alg β K (B i) ≤ δ) :
    1 - δ ≤ trainProb G alg β K E := by
  rw [trainProb_compl alg β hG halg E]
  have h1 := trainProb_mono alg β hG halg _ _ hE
  have h2 := trainProb_union alg β hG halg s B
  linarith

end mass2

section xi_lower
open AdaptiveEnv

lemma take_ofFn_congr {X : Type*} {t : ℕ} (ω ω' : Fin t → X) (i : ℕ)
    (h : ∀ j : Fin t, j.val < i → ω j = ω' j) : (List.ofFn ω).take i = (List.ofFn ω').take i := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h
    simp only [List.length_take, List.length_ofFn] at h1
    show n < i
    omega

/-- The deterministic adversary: loss `0` on arm `0`, `1` elsewhere; no private randomness. -/
def advEnv (B : ℕ) : AdaptiveEnv B Unit where
  init := fun _ => 1
  loss := fun _ _ b => if b.val = 0 then 0 else 1
  kernel := fun _ _ _ _ => 1
  fb := fun _ _ b _ => if b.val = 0 then 0 else 1

@[simp] lemma advEnv_init (B : ℕ) (z : Unit) : (advEnv B).init z = 1 := rfl
@[simp] lemma advEnv_loss (B : ℕ) (z : Unit) (p : List (Fin B × Unit)) (b : Fin B) :
    (advEnv B).loss z p b = if b.val = 0 then 0 else 1 := rfl
@[simp] lemma advEnv_kernel (B : ℕ) (z : Unit) (p : List (Fin B × Unit)) (b : Fin B) (z' : Unit) :
    (advEnv B).kernel z p b z' = 1 := rfl
@[simp] lemma advEnv_fb (B : ℕ) (z : Unit) (p : List (Fin B × Unit)) (b : Fin B) (z' : Unit) :
    (advEnv B).fb z p b z' = if b.val = 0 then 0 else 1 := rfl

lemma advEnv_valid (B : ℕ) : (advEnv B).Valid := by
  refine ⟨fun _ => by simp, by simp, fun _ _ _ _ => by simp, fun _ _ _ => by simp,
    fun _ _ b => ?_, fun _ _ b _ => ?_, fun _ _ b => by simp⟩
  all_goals (simp only [advEnv_loss, advEnv_fb]; split_ifs <;> simp)

lemma advEnv_theta_congr {B : ℕ} (alg : BanditRule B) {t : ℕ} (ω ω' : Fin t → Fin B × Unit) (i : ℕ)
    (h : ∀ j : Fin t, j.val < i → ω j = ω' j) :
    (advEnv B).theta alg () ω i = (advEnv B).theta alg () ω' i := by
  unfold theta fbList
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp only [List.length_take, List.length_ofFn] at h1
    have hn : n < i := by omega
    have e1 := h ⟨n, by omega⟩ hn
    have e2 : past ω n = past ω' n := take_ofFn_congr ω ω' n (fun j hj => h j (by omega))
    rw [e1, e2]

lemma advEnv_weight_sum {B : ℕ} (alg : BanditRule B) (halg : alg.Valid) (hB : 0 < B) (t : ℕ) :
    ∑ z₀ : Unit, ∑ ω : Fin t → Fin B × Unit, (advEnv B).weight alg z₀ ω = 1 := by
  rw [Fintype.sum_unique]
  refine (Finset.sum_congr rfl (fun ω _ => ?_)).trans (hist_sum ((⟨0, hB⟩ : Fin B), ()) t
    (fun i ω y => (advEnv B).theta alg () ω i.val y.1 * 1) ?_ ?_)
  · simp [AdaptiveEnv.weight]
  · intro i ω ω' h; funext y; rw [advEnv_theta_congr alg ω ω' i.val (fun j hj => h j hj)]
  · intro i ω; rw [Fintype.sum_prod_type]; simp [AdaptiveEnv.theta, halg.2.1]

lemma advEnv_regret_nonneg (H : ℕ) {B : ℕ} (alg : BanditRule B) (halg : alg.Valid) (hB : 0 < B)
    {t : ℕ} (ω : Fin t → Fin B × Unit) : 0 ≤ (advEnv B).weightedRegret alg H () ω := by
  unfold weightedRegret
  refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) ⟨0, hB⟩)
  apply Finset.sum_nonneg; intro i _
  apply mul_nonneg (lrW_nonneg _ _ _)
  rw [advEnv_loss, if_pos rfl, sub_zero]
  apply Finset.sum_nonneg; intro b _
  apply mul_nonneg (halg.1 _ _)
  rw [advEnv_loss]; split_ifs <;> norm_num

lemma advEnv_regret_one (H : ℕ) {B : ℕ} (alg : BanditRule B) (halg : alg.Valid) (hB : 0 < B)
    (ω : Fin 1 → Fin B × Unit) : ((B:ℝ) - 1) / B ≤ (advEnv B).weightedRegret alg H () ω := by
  unfold weightedRegret
  refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) ⟨0, hB⟩)
  rw [Fin.sum_univ_one]
  have hθ : (advEnv B).theta alg () ω (0 : Fin 1).val = alg [] := by
    unfold theta fbList; simp
  rw [hθ, show (0 : Fin 1).val + 1 = 1 from rfl, lrW_self H 1 le_rfl, lr_one, advEnv_loss,
    if_pos rfl, sub_zero, one_mul]
  have hs : ∑ b' : Fin B, alg [] b' * (advEnv B).loss () (past ω (0 : Fin 1).val) b' =
      ((B:ℝ) - 1) / B := by
    simp only [advEnv_loss, halg.2.2]
    rw [← Finset.mul_sum]
    have : ∑ b' : Fin B, (if b'.val = 0 then (0:ℝ) else 1) =
        ∑ b' : Fin B, (1 - if b' = ⟨0, hB⟩ then 1 else 0) :=
      Finset.sum_congr rfl (fun b' _ => by by_cases hb : b'.val = 0 <;> simp [hb, Fin.ext_iff])
    rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Finset.mem_univ, if_true]
    ring
  rw [hs]

/-- If the adversary forces regret `≥ L` on every history, Assumption 1 forces `ξ(B,t,x) ≥ L`. -/
lemma xi_ge_of_regret (H : ℕ) {B : ℕ} (alg : BanditRule B) (halg : alg.Valid)
    (ξ : ℕ → ℕ → ℝ → ℝ) (hA : Assumption1 H alg ξ) (hB : 0 < B) (t : ℕ) (x : ℝ) (hx : 0 < x)
    (L : ℝ) (hL : ∀ ω : Fin t → Fin B × Unit, L ≤ (advEnv B).weightedRegret alg H () ω) :
    L ≤ ξ B t x := by
  by_contra hlt; push Not at hlt
  have hδ0 : 0 < Real.exp (-x) := Real.exp_pos _
  have hδ1 : Real.exp (-x) < 1 := by
    have := Real.exp_lt_exp.mpr (show -x < 0 by linarith)
    simpa using this
  have hlog : Real.log (1 / Real.exp (-x)) = x := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hP := hA Unit (advEnv B) (advEnv_valid B) t _ hδ0 hδ1
  rw [hlog] at hP
  have hone : (advEnv B).regretExceedProb alg H t (ξ B t x) = 1 := by
    unfold regretExceedProb
    refine Eq.trans ?_ (advEnv_weight_sum alg halg hB t)
    refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun ω _ => ?_))
    rcases z with ⟨⟩
    rw [if_pos (lt_of_lt_of_le hlt (hL ω)), mul_one]
  linarith

lemma xi_nonneg (H : ℕ) {B : ℕ} (alg : BanditRule B) (halg : alg.Valid)
    (ξ : ℕ → ℕ → ℝ → ℝ) (hA : Assumption1 H alg ξ) (hB : 0 < B) (t : ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ ξ B t x :=
  xi_ge_of_regret H alg halg ξ hA hB t x hx 0 (fun ω => advEnv_regret_nonneg H alg halg hB ω)

lemma xi_one_ge (H : ℕ) {B : ℕ} (alg : BanditRule B) (halg : alg.Valid)
    (ξ : ℕ → ℕ → ℝ → ℝ) (hA : Assumption1 H alg ξ) (hB : 0 < B) (x : ℝ) (hx : 0 < x) :
    ((B:ℝ) - 1) / B ≤ ξ B 1 x :=
  xi_ge_of_regret H alg halg ξ hA hB 1 x hx _ (fun ω => advEnv_regret_one H alg halg hB ω)

end xi_lower

section final
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}

/-- The good event at the top: start state, optimism and pessimism at step 0. -/
def GoodTop (hH : 0 < G.H) (τ : Fin K → Episode G) : Prop :=
  (∀ k : Fin K, (τ k ⟨0, hH⟩).1 = G.s1) ∧
  (∀ (k : Fin K) (j : Fin G.m) (μ : DevPolicy G j),
      brW G alg β τ j μ 0 k [] G.s1 ≤ (runState G β τ k.val).vUp j ⟨0, hH⟩ G.s1) ∧
  (∀ (k : Fin K) (j : Fin G.m),
      (runState G β τ k.val).vLow j ⟨0, hH⟩ G.s1 ≤ outVal G alg β τ j 0 k G.s1)

lemma top_gap (hG : G.Standing) (hK : 1 ≤ K) (τ : Fin K → Episode G)
    (hgood : GoodTop alg β hG.H_pos τ) (j : Fin G.m) :
    brValTop G alg β τ j - outValTop G alg β τ j ≤
      (1 / (K:ℝ)) * ∑ k : Fin K, gplus β τ k 0 := by
  obtain ⟨hs, hopt, hpes⟩ := hgood
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  haveI : Nonempty (Fin (G.A j)) := ⟨⟨0, hG.A_pos j⟩⟩
  have hgap : ∀ k : Fin K, (runState G β τ k.val).vUp j ⟨0, hG.H_pos⟩ G.s1 -
      (runState G β τ k.val).vLow j ⟨0, hG.H_pos⟩ G.s1 ≤ gplus β τ k 0 := by
    intro k
    refine le_trans ?_ (le_max_left _ _)
    unfold gapAt
    rw [dif_pos hG.H_pos]
    have hk := hs k
    refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) j)
    simp only [hk]
    exact le_rfl
  have hbr : brValTop G alg β τ j ≤ (1 / (K:ℝ)) * ∑ k : Fin K,
      (runState G β τ k.val).vUp j ⟨0, hG.H_pos⟩ G.s1 := by
    unfold brValTop
    apply ciSup_le
    intro μ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun k _ => hopt k j μ)
  have hout : (1 / (K:ℝ)) * ∑ k : Fin K, (runState G β τ k.val).vLow j ⟨0, hG.H_pos⟩ G.s1
      ≤ outValTop G alg β τ j := by
    unfold outValTop
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun k _ => hpes k j)
  have h3 : (1 / (K:ℝ)) * ∑ k : Fin K, ((runState G β τ k.val).vUp j ⟨0, hG.H_pos⟩ G.s1 -
      (runState G β τ k.val).vLow j ⟨0, hG.H_pos⟩ G.s1) ≤
        (1 / (K:ℝ)) * ∑ k : Fin K, gplus β τ k 0 :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hgap k)) (by positivity)
  rw [Finset.sum_sub_distrib, mul_sub] at h3
  linarith

lemma gap_le_H (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (hK : 1 ≤ K)
    (τ : Fin K → Episode G) (j : Fin G.m) :
    brValTop G alg β τ j - outValTop G alg β τ j ≤ G.H := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  haveI : Nonempty (Fin (G.A j)) := ⟨⟨0, hG.A_pos j⟩⟩
  have hbr : brValTop G alg β τ j ≤ G.H := by
    unfold brValTop
    apply ciSup_le
    intro μ
    have : ∑ k : Fin K, brW G alg β τ j μ 0 k [] G.s1 ≤ ∑ _k : Fin K, (G.H : ℝ) := by
      apply Finset.sum_le_sum; intro k _
      have := (brW_bounds alg β τ hG halg j μ G.H 0 (by omega) k [] G.s1).2
      simpa using this
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc (1 / (K:ℝ)) * ∑ k : Fin K, brW G alg β τ j μ 0 k [] G.s1
        ≤ (1 / (K:ℝ)) * (K * G.H) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = G.H := by field_simp
  have hout : 0 ≤ outValTop G alg β τ j := by
    unfold outValTop
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun k _ => (outVal_bounds alg β τ hG halg j G.H 0 (by omega) k G.s1).1)
  linarith

end final

lemma concave_seg (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f) (n : ℕ) (u : ℝ)
    (h1 : (n:ℝ) ≤ u) (h2 : u ≤ n + 1) :
    ((n:ℝ) + 1 - u) * f n + (u - n) * f (n + 1) ≤ f u := by
  have hx : (n:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (Nat.cast_nonneg n)
  have hy : ((n:ℝ) + 1) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (by positivity)
  have := hf.2 hx hy (by linarith : (0:ℝ) ≤ (n:ℝ) + 1 - u) (by linarith : (0:ℝ) ≤ u - n)
    (by ring)
  simp only [smul_eq_mul] at this
  have e : ((n:ℝ) + 1 - u) * n + (u - n) * (n + 1) = u := by ring
  rw [e] at this
  exact this

lemma Xi_lower (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f) (a : ℝ) (ha : 0 ≤ a)
    (h0 : ∀ N : ℕ, 0 ≤ f N) (h1 : ∀ N : ℕ, 1 ≤ N → a ≤ f N) (u : ℝ) (hu : 0 ≤ u) :
    a * min u 1 ≤ f u := by
  rcases lt_or_ge u 1 with hlt | hge
  · rw [min_eq_left hlt.le]
    have hs := concave_seg f hf 0 u (by simpa using hu) (by simp; linarith)
    simp only [Nat.cast_zero, zero_add, sub_zero] at hs
    have hf0 : 0 ≤ f 0 := by simpa using h0 0
    have hf1 : a ≤ f 1 := by simpa using h1 1 le_rfl
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - u) hf0, mul_le_mul_of_nonneg_left hf1 hu]
  · rw [min_eq_right hge, mul_one]
    have hnu : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le hu
    have hun : u < ((⌊u⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one u
    have hn1 : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by simpa using hge)
    have hs := concave_seg f hf ⌊u⌋₊ u hnu hun.le
    have hfa : a ≤ f (⌊u⌋₊ : ℕ) := h1 _ hn1
    have hfb : a ≤ f ((⌊u⌋₊ : ℕ) + 1 : ℝ) := by
      have := h1 (⌊u⌋₊ + 1) (by omega); push_cast at this; exact this
    nlinarith [mul_le_mul_of_nonneg_left hfa (by linarith : (0:ℝ) ≤ (⌊u⌋₊ : ℝ) + 1 - u),
      mul_le_mul_of_nonneg_left hfb (by linarith : (0:ℝ) ≤ u - (⌊u⌋₊ : ℝ))]

lemma iota_pos {G : Game} (hG : G.Standing) {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hA : 1 ≤ G.Amax) : 0 < iota G K δ := by
  unfold iota
  apply Real.log_pos
  rw [lt_div_iff₀ hδ0, one_mul]
  have hN : 0 < G.m * G.H * G.S * G.Amax * K :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hG.m_pos hG.H_pos) hG.S_pos) hA) hK
  have h1 : (1:ℝ) ≤ ((G.m * G.H * G.S * G.Amax * K : ℕ) : ℝ) := by exact_mod_cast hN
  push_cast at h1
  linarith

lemma A_le_Amax (G : Game) (j : Fin G.m) : G.A j ≤ G.Amax :=
  Finset.le_sup (f := G.A) (Finset.mem_univ j)

section final2
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}

lemma c1_ge (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (ξ : ℕ → ℕ → ℝ → ℝ)
    (hA : ∀ j, Assumption1 G.H (alg j) ξ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hK : 1 ≤ K)
    (c₀ c₁ : ℝ)
    (hβ : ∀ j t, 1 ≤ t → t ≤ K →
          c₀ * bonusScale G ξ (G.A j) (iota G K δ) t ≤
              ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ∧
            ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ≤
              c₁ * bonusScale G ξ (G.A j) (iota G K δ) t) :
    c₀ ≤ c₁ := by
  have j0 : Fin G.m := ⟨0, hG.m_pos⟩
  have hι := iota_pos hG hK hδ0 hδ1 (le_trans (hG.A_pos j0) (A_le_Amax G j0))
  have hbs : 0 < bonusScale G ξ (G.A j0) (iota G K δ) 1 := by
    unfold bonusScale
    have hx := xi_nonneg G.H (alg j0) (halg j0) ξ (hA j0) (hG.A_pos j0) 1 _ hι
    have hH : (0:ℝ) < G.H := by exact_mod_cast hG.H_pos
    have : 0 < Real.sqrt ((G.H:ℝ) ^ 3 * iota G K δ / ((1:ℕ):ℝ)) :=
      Real.sqrt_pos.mpr (div_pos (mul_pos (pow_pos hH 3) hι) (by norm_num))
    nlinarith [mul_nonneg hH.le hx]
  have := hβ j0 1 le_rfl hK
  exact le_of_mul_le_mul_right (this.1.trans this.2) hbs

lemma det_final (hG : G.Standing) (halg : ∀ j, (alg j).Valid)
    (ξ : ℕ → ℕ → ℝ → ℝ) (Ξ : ℕ → ℝ → ℝ → ℝ)
    (hA : ∀ j, Assumption1 G.H (alg j) ξ)
    (hmono : ∀ B B' t x, 0 < x → B ≤ B' → ξ B t x ≤ ξ B' t x)
    (hsum : ∀ B (t : ℕ) x, 0 < x → ∑ t' ∈ Finset.Icc 1 t, ξ B t' x ≤ Ξ B t x)
    (hconc : ∀ B x, 0 < x → ConcaveOn ℝ (Set.Ici 0) (fun t => Ξ B t x))
    (hβ0 : ∀ j t, 0 ≤ β j t) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hK : 1 ≤ K)
    (c₀ c₁ : ℝ) (hc₀ : 0 < c₀)
    (hβ : ∀ j t, 1 ≤ t → t ≤ K →
          c₀ * bonusScale G ξ (G.A j) (iota G K δ) t ≤
              ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ∧
            ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ≤
              c₁ * bonusScale G ξ (G.A j) (iota G K δ) t)
    (hA2 : 2 ≤ G.Amax)
    (τ : Fin K → Episode G) (hgood : GoodTop alg β hG.H_pos τ) (j : Fin G.m) :
    brValTop G alg β τ j - outValTop G alg β τ j ≤
      (Real.exp 1 * (2 + 4 * max c₁ 0) + 2) *
        ((G.H : ℝ) ^ 2 * G.S / K * Ξ G.Amax ((K : ℝ) / G.S) (iota G K δ) +
          Real.sqrt ((G.H : ℝ) ^ 5 * G.S * iota G K δ / K)) := by
  have hm := hG.m_pos
  have j0 : Fin G.m := ⟨0, hm⟩
  haveI : Nonempty (Fin G.m) := ⟨j0⟩
  have hc : c₀ ≤ c₁ := c1_ge alg β hG halg ξ hA δ hδ0 hδ1 hK c₀ c₁ hβ
  have hc1 : 0 ≤ c₁ := hc₀.le.trans hc
  rw [max_eq_left hc1]
  have hι := iota_pos hG hK hδ0 hδ1 (by omega)
  set ι := iota G K δ with hιdef
  have hHr : (0:ℝ) < G.H := by exact_mod_cast hG.H_pos
  have hH1r : (1:ℝ) ≤ G.H := by exact_mod_cast hG.H_pos
  have hSr : (0:ℝ) < G.S := by exact_mod_cast hG.S_pos
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  obtain ⟨jstar, -, hjs⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin G.m))
    Finset.univ_nonempty G.A
  have hjs' : G.A jstar = G.Amax := hjs.symm
  have hxi0 : ∀ t : ℕ, 0 ≤ ξ G.Amax t ι := by
    intro t
    have := xi_nonneg G.H (alg jstar) (halg jstar) ξ (hA jstar) (hG.A_pos jstar) t ι hι
    rwa [hjs'] at this
  have hxi1 : (1:ℝ) / 2 ≤ ξ G.Amax 1 ι := by
    have := xi_one_ge G.H (alg jstar) (halg jstar) ξ (hA jstar) (hG.A_pos jstar) ι hι
    rw [hjs'] at this
    refine le_trans ?_ this
    have h2 : (2:ℝ) ≤ G.Amax := by exact_mod_cast hA2
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hΞ0 : ∀ N : ℕ, 0 ≤ Ξ G.Amax N ι := fun N =>
    (Finset.sum_nonneg (fun t _ => hxi0 t)).trans (hsum _ N ι hι)
  have hΞ1 : ∀ N : ℕ, 1 ≤ N → (1:ℝ) / 2 ≤ Ξ G.Amax N ι := by
    intro N hN
    refine le_trans hxi1 (le_trans ?_ (hsum _ N ι hι))
    exact Finset.single_le_sum (f := fun t => ξ G.Amax t ι) (fun t _ => hxi0 t)
      (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
  have hXl : (1/2:ℝ) * min ((K:ℝ) / G.S) 1 ≤ Ξ G.Amax ((K:ℝ) / G.S) ι :=
    Xi_lower (fun u => Ξ G.Amax u ι) (hconc _ ι hι) (1/2) (by norm_num) hΞ0 hΞ1
      ((K:ℝ) / G.S) (by positivity)
  set Ξv := Ξ G.Amax ((K:ℝ) / G.S) ι with hΞv
  set R2 := Real.sqrt ((G.H : ℝ) ^ 5 * G.S * ι / K) with hR2
  have hR2n : 0 ≤ R2 := Real.sqrt_nonneg _
  have hΞvn : 0 ≤ Ξv :=
    le_trans (mul_nonneg (by norm_num) (le_min (by positivity) zero_le_one)) hXl
  set P := (G.H : ℝ) ^ 2 * G.S / K with hP
  have hPn : 0 ≤ P := by positivity
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  rcases lt_or_ge (K:ℝ) G.S with hKS | hKS
  · have hmin : min ((K:ℝ) / G.S) 1 = (K:ℝ) / G.S := min_eq_left ((div_le_one hSr).mpr hKS.le)
    rw [hmin] at hXl
    have hPX : (G.H:ℝ) ≤ 2 * (P * Ξv) := by
      have e1 : P * ((1/2) * ((K:ℝ) / G.S)) = (G.H:ℝ)^2 / 2 := by
        rw [hP]; first | (field_simp; ring) | field_simp
      have h2 : P * ((1/2) * ((K:ℝ) / G.S)) ≤ P * Ξv := mul_le_mul_of_nonneg_left hXl hPn
      nlinarith
    have hg := gap_le_H alg β hG halg hK τ j
    nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ Real.exp 1 * (2 + 4 * c₁) + 2 - 2)
      (add_nonneg (mul_nonneg hPn hΞvn) hR2n)]
  · have hmin : min ((K:ℝ) / G.S) 1 = 1 := min_eq_right ((le_div_iff₀ hSr).mpr (by linarith))
    rw [hmin, mul_one] at hXl
    let bb : ℕ → ℝ := fun t => if t = 0 then 0 else
      ⨆ j' : Fin G.m, ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j' i
    have hbb0 : ∀ t, 0 ≤ bb t := by
      intro t
      by_cases ht : t = 0
      · simp [bb, ht]
      · simp only [bb, if_neg ht]
        refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) j0)
        exact Finset.sum_nonneg (fun i _ => mul_nonneg (lrW_nonneg _ _ _) (hβ0 _ _))
    have hb0 : bb 0 = 0 := by simp [bb]
    have hbbc : ∀ t, 1 ≤ t → t ≤ K → bb t ≤ c₁ * ((G.H:ℝ) * ξ G.Amax t ι +
        Real.sqrt ((G.H:ℝ) ^ 3 * ι / t)) := by
      intro t ht1 htK
      simp only [bb, if_neg (by omega : t ≠ 0)]
      apply ciSup_le
      intro j'
      refine ((hβ j' t ht1 htK).2).trans ?_
      unfold bonusScale
      apply mul_le_mul_of_nonneg_left _ hc1
      have := hmono (G.A j') G.Amax t ι hι (A_le_Amax G j')
      linarith [mul_le_mul_of_nonneg_left this hHr.le]
    have hbb : ∀ j' (n : ℕ), n < K →
        ∑ i : Fin n, lrW G.H n (i.val + 1) * β j' (i.val + 1) ≤ bb n := by
      intro j' n _
      by_cases hn : n = 0
      · subst hn; simp [bb]
      · simp only [bb, if_neg hn]
        rw [← sum_Icc_eq_sum_fin (fun i => lrW G.H n i * β j' i) n]
        exact le_ciSup (Finite.bddAbove_range (fun j'' : Fin G.m =>
          ∑ i ∈ Finset.Icc 1 n, lrW G.H n i * β j'' i)) j'
    have hX0 : 0 ≤ (G.H:ℝ) ^ 3 * ι := mul_nonneg (by positivity) hι.le
    have hdet := det_bound β τ hm hG.H_pos hG.S_pos c₁ ((G.H:ℝ) ^ 3 * ι) hc1 hX0
      (fun t => ξ G.Amax t ι) (fun u => Ξ G.Amax u ι) (hconc _ ι hι)
      (fun N => hsum _ N ι hι) bb hbb0 hb0 hbbc hbb
    have htop := top_gap alg β hG hK τ hgood j
    have hsq : (G.H:ℝ) * Real.sqrt ((G.H:ℝ) ^ 3 * ι) * Real.sqrt (G.S * K) / K = R2 := by
      have e1 : (G.H:ℝ) ^ 5 * G.S * ι / K =
          ((G.H:ℝ) / K) ^ 2 * ((G.H:ℝ) ^ 3 * ι * (G.S * K)) := by
        first | (field_simp; ring) | field_simp
      rw [hR2, e1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
        Real.sqrt_mul hX0]
      first | (field_simp; ring) | field_simp | ring
    have hexp : (1 / (K:ℝ)) * (Real.exp 1 * ((G.H:ℝ) * ((G.S:ℝ) * G.H +
        2 * (c₁ * ((G.H:ℝ) * (G.S * Ξv) +
          2 * Real.sqrt ((G.H:ℝ) ^ 3 * ι) * Real.sqrt (G.S * K)))))) =
        Real.exp 1 * (P + 2 * c₁ * (P * Ξv) + 4 * c₁ * R2) := by
      rw [← hsq, hP]; first | (field_simp; ring) | field_simp | ring
    have hgp : brValTop G alg β τ j - outValTop G alg β τ j ≤
        Real.exp 1 * (P + 2 * c₁ * (P * Ξv) + 4 * c₁ * R2) := by
      rw [← hexp]
      exact htop.trans (mul_le_mul_of_nonneg_left hdet (by positivity))
    have hPX : P ≤ 2 * (P * Ξv) := by nlinarith [mul_le_mul_of_nonneg_left hXl hPn]
    have hA0 : 0 ≤ P * Ξv := mul_nonneg hPn hΞvn
    refine hgp.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hPX he.le, mul_nonneg he.le (mul_nonneg hc1 hA0),
      mul_nonneg he.le hR2n, mul_nonneg he.le (mul_nonneg hc1 hR2n)]

end final2

section amax1
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}
  (τ : Fin K → Episode G)

lemma devProb_eq_joint_of_one (halg : ∀ j, (alg j).Valid) (h1 : ∀ j, G.A j = 1)
    (σ : RunState G K) (j : Fin G.m) (b : Fin (G.A j)) (h : Fin G.H) (s : Fin G.S)
    (a : G.JointAct) :
    RunState.devProb alg σ j b h s a = RunState.jointProb alg σ h s a := by
  unfold RunState.devProb RunState.jointProb
  apply Finset.prod_congr rfl
  intro j' _
  have hsub : ∀ j'', Subsingleton (Fin (G.A j'')) := fun j'' => by
    rw [h1 j'']; infer_instance
  split_ifs with hj hab
  · subst hj
    haveI := hsub j'
    have hs := (halg j').2.1 (σ.hist j' h s)
    rw [Fintype.sum_subsingleton _ (a j')] at hs
    exact hs.symm
  · subst hj
    haveI := hsub j'
    exact absurd (Subsingleton.elim _ _) hab
  · rfl

lemma brW_eq_outVal (halg : ∀ j, (alg j).Valid) (h1 : ∀ j, G.A j = 1) (j : Fin G.m)
    (μ : DevPolicy G j) :
    ∀ d h, G.H - h ≤ d → ∀ (k : Fin K) (hist : List (Fin G.S × G.JointAct)) (s : Fin G.S),
      brW G alg β τ j μ h k hist s = outVal G alg β τ j h k s := by
  intro d
  induction d with
  | zero =>
    intro h hd k hist s
    have hh : ¬ h < G.H := by omega
    rw [brW, dif_neg hh, outVal, dif_neg hh]
  | succ d ih =>
    intro h hd k hist s
    by_cases hh : h < G.H
    · rw [brW, dif_pos hh, outVal, dif_pos hh]
      have hF : ∀ k' : Fin K, (∑ a : G.JointAct,
          RunState.devProb alg (runState G β τ k'.val) j (μ hist s) ⟨h, hh⟩ s a *
            (G.r j ⟨h, hh⟩ s a + ∑ s', G.P ⟨h, hh⟩ s a s' *
              brW G alg β τ j μ (h + 1) k' (hist ++ [(s, a)]) s')) =
          ∑ a : G.JointAct, RunState.jointProb alg (runState G β τ k'.val) ⟨h, hh⟩ s a *
            (G.r j ⟨h, hh⟩ s a + ∑ s', G.P ⟨h, hh⟩ s a s' *
              outVal G alg β τ j (h + 1) k' s') := by
        intro k'
        apply Finset.sum_congr rfl; intro a _
        rw [devProb_eq_joint_of_one alg halg h1]
        congr 2
        apply Finset.sum_congr rfl; intro s' _
        rw [ih (h+1) (by omega) k' _ s']
      simp only [hF]
    · rw [brW, dif_neg hh, outVal, dif_neg hh]

lemma gap_zero_of_one (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (h1 : ∀ j, G.A j = 1)
    (j : Fin G.m) :
    brValTop G alg β τ j - outValTop G alg β τ j = 0 := by
  haveI : Nonempty (Fin (G.A j)) := ⟨⟨0, hG.A_pos j⟩⟩
  have hc : ∀ μ : DevPolicy G j, (1 / (K:ℝ)) * ∑ k : Fin K, brW G alg β τ j μ 0 k [] G.s1 =
      outValTop G alg β τ j := by
    intro μ; unfold outValTop
    congr 1; apply Finset.sum_congr rfl; intro k _
    exact brW_eq_outVal alg β τ halg h1 j μ G.H 0 (by omega) k [] G.s1
  unfold brValTop
  simp only [hc, ciSup_const, sub_self]

end amax1

/-- The one remaining probabilistic claim: the good event has probability at least `1 - δ`
(only the lower bonus bound is needed). -/
def GoodProbClaim (c₀ : ℝ) : Prop :=
  ∀ (G : Game) (hG : G.Standing) (alg : ∀ j, BanditRule (G.A j)), (∀ j, (alg j).Valid) →
    ∀ (ξ : ℕ → ℕ → ℝ → ℝ), (∀ j, Assumption1 G.H (alg j) ξ) →
    ∀ (β : Fin G.m → ℕ → ℝ), (∀ j t, 0 ≤ β j t) →
    ∀ (δ : ℝ), 0 < δ → δ < 1 → ∀ K : ℕ, 1 ≤ K → 2 ≤ G.Amax →
      (∀ j t, 1 ≤ t → t ≤ K →
          c₀ * bonusScale G ξ (G.A j) (iota G K δ) t ≤
              ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i) →
      1 - δ ≤ trainProb G alg β K (GoodTop alg β hG.H_pos)

lemma solution_of_good (c₀ : ℝ) (hc₀ : 0 < c₀) (hclaim : GoodProbClaim c₀) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, ∃ C : ℝ, ∀ (G : Game), G.Standing →
      ∀ (alg : ∀ j, BanditRule (G.A j)), (∀ j, (alg j).Valid) →
      ∀ (ξ : ℕ → ℕ → ℝ → ℝ) (Ξ : ℕ → ℝ → ℝ → ℝ),
        (∀ j, Assumption1 G.H (alg j) ξ) →
        (∀ B B' t x, 0 < x → B ≤ B' → ξ B t x ≤ ξ B' t x) →
        (∀ B (t : ℕ) x, 0 < x → ∑ t' ∈ Finset.Icc 1 t, ξ B t' x ≤ Ξ B t x) →
        (∀ B x, 0 < x → ConcaveOn ℝ (Set.Ici 0) (fun t => Ξ B t x)) →
      ∀ (β : Fin G.m → ℕ → ℝ), (∀ j t, 0 ≤ β j t) →
      ∀ (δ : ℝ), 0 < δ → δ < 1 → ∀ K : ℕ, 1 ≤ K →
        (∀ j t, 1 ≤ t → t ≤ K →
          c₀ * bonusScale G ξ (G.A j) (iota G K δ) t ≤
              ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ∧
            ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ≤
              c₁ * bonusScale G ξ (G.A j) (iota G K δ) t) →
        1 - δ ≤ trainProb G alg β K (fun τ => ∀ j : Fin G.m,
          brValTop G alg β τ j - outValTop G alg β τ j ≤
            C * ((G.H : ℝ) ^ 2 * G.S / K * Ξ G.Amax ((K : ℝ) / G.S) (iota G K δ) +
              Real.sqrt ((G.H : ℝ) ^ 5 * G.S * iota G K δ / K))) := by
  refine ⟨c₀, hc₀, fun c₁ => ⟨Real.exp 1 * (2 + 4 * max c₁ 0) + 2, ?_⟩⟩
  intro G hG alg halg ξ Ξ hA hmono hsum hconc β hβ0 δ hδ0 hδ1 K hK hβ
  have hm := hG.m_pos
  have j0 : Fin G.m := ⟨0, hm⟩
  have hAmax1 : 1 ≤ G.Amax := le_trans (hG.A_pos j0) (A_le_Amax G j0)
  rcases lt_or_ge G.Amax 2 with hA1 | hA2
  · -- every player has a single action: the gap is zero
    have h1 : ∀ j, G.A j = 1 := fun j => by
      have := A_le_Amax G j; have := hG.A_pos j; omega
    have hι := iota_pos hG hK hδ0 hδ1 hAmax1
    have hjA : G.A j0 = G.Amax := by rw [h1 j0]; omega
    have hxi0 : ∀ t : ℕ, 0 ≤ ξ G.Amax t (iota G K δ) := by
      intro t
      have := xi_nonneg G.H (alg j0) (halg j0) ξ (hA j0) (hG.A_pos j0) t _ hι
      rwa [hjA] at this
    have hΞ0 : ∀ N : ℕ, 0 ≤ Ξ G.Amax N (iota G K δ) := fun N =>
      (Finset.sum_nonneg (fun t _ => hxi0 t)).trans (hsum _ N _ hι)
    have hXl : (0:ℝ) * min ((K:ℝ) / G.S) 1 ≤ Ξ G.Amax ((K:ℝ) / G.S) (iota G K δ) :=
      Xi_lower (fun u => Ξ G.Amax u (iota G K δ)) (hconc _ _ hι) 0 le_rfl hΞ0
        (fun N _ => hΞ0 N) ((K:ℝ) / G.S) (by positivity)
    rw [zero_mul] at hXl
    have hC : 0 ≤ Real.exp 1 * (2 + 4 * max c₁ 0) + 2 := by
      have := Real.exp_pos 1
      have := le_max_right c₁ 0
      positivity
    have hR : 0 ≤ (G.H : ℝ) ^ 2 * G.S / K * Ξ G.Amax ((K : ℝ) / G.S) (iota G K δ) +
        Real.sqrt ((G.H : ℝ) ^ 5 * G.S * iota G K δ / K) :=
      add_nonneg (mul_nonneg (by positivity) hXl) (Real.sqrt_nonneg _)
    refine trainProb_ge alg β hG halg (∅ : Finset Unit) (fun _ _ => False) _ ?_ δ
      (by simp; linarith)
    intro τ hn
    exact absurd (fun j => by
      rw [gap_zero_of_one alg β τ hG halg h1 j]; exact mul_nonneg hC hR) hn
  · have hP := hclaim G hG alg halg ξ hA β hβ0 δ hδ0 hδ1 K hK hA2
      (fun j t h1 h2 => (hβ j t h1 h2).1)
    refine hP.trans (trainProb_mono alg β hG halg _ _ ?_)
    intro τ hgood j
    exact det_final alg β hG halg ξ Ξ hA hmono hsum hconc hβ0 δ hδ0 hδ1 hK c₀ c₁ hc₀ hβ hA2
      τ hgood j

section ae
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

lemma start_of_weight_ne (hH : 0 < G.H) (τ : Fin K → Episode G)
    (hw : traceWeight G alg β τ ≠ 0) (k : Fin K) : (τ k ⟨0, hH⟩).1 = G.s1 := by
  unfold traceWeight at hw
  have h1 := (Finset.prod_ne_zero_iff.mp hw) k (Finset.mem_univ _)
  have h2 := (Finset.prod_ne_zero_iff.mp h1) ⟨0, hH⟩ (Finset.mem_univ _)
  have h3 : stepProb G τ k ⟨0, hH⟩ ≠ 0 := left_ne_zero_of_mul h2
  by_contra hc
  apply h3
  simp [stepProb, hc]

/-- Union bound where the exceptions only need to cover traces of nonzero weight. -/
lemma trainProb_ge_ae (hG : G.Standing) (halg : ∀ j, (alg j).Valid) {ι : Type*}
    (s : Finset ι) (B : ι → (Fin K → Episode G) → Prop) (E : (Fin K → Episode G) → Prop)
    (hE : ∀ τ, traceWeight G alg β τ ≠ 0 → ¬ E τ → ∃ i ∈ s, B i τ) (δ : ℝ)
    (hδ : ∑ i ∈ s, trainProb G alg β K (B i) ≤ δ) :
    1 - δ ≤ trainProb G alg β K E := by
  have := trainProb_ge alg β hG halg s B (fun τ => E τ ∨ traceWeight G alg β τ = 0)
    (fun τ hn => hE τ (fun h0 => hn (Or.inr h0)) (fun he => hn (Or.inl he))) δ hδ
  refine this.trans (le_of_eq ?_)
  unfold trainProb
  apply Finset.sum_congr rfl; intro τ _
  by_cases h0 : traceWeight G alg β τ = 0
  · simp [h0]
  · by_cases hEt : E τ
    · simp [hEt]
    · simp only [hEt, h0, or_self, if_false]

end ae


/-! ## Layer I: optimism / pessimism on the good event (deterministic given OptHyp / PesHyp) -/
section layerI
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}
  (τ : Fin K → Episode G)

/-- The `i`-th (0-based) target of the optimistic update at `(h, s)`, from visit episode `k'`. -/
noncomputable def upTerm (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (i : ℕ) (k' : Fin K) : ℝ :=
  G.r j h s (τ k' h).2 + (runState G β τ k'.val).vUpAfter j (τ k') h + β j (i + 1)

/-- The `i`-th (0-based) target of the pessimistic update at `(h, s)`, from visit episode `k'`. -/
noncomputable def lowTerm (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (i : ℕ) (k' : Fin K) : ℝ :=
  G.r j h s (τ k' h).2 + (runState G β τ k'.val).vLowAfter j (τ k') h - β j (i + 1)

noncomputable def upSum (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (l : List (Fin K)) : ℝ :=
  lrW G.H l.length 0 * ((G.H : ℝ) - h.val) +
    ∑ i : Fin l.length, lrW G.H l.length (i.val + 1) * upTerm β τ j h s i.val (l.get i)

noncomputable def lowSum (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (l : List (Fin K)) : ℝ :=
  ∑ i : Fin l.length, lrW G.H l.length (i.val + 1) * lowTerm β τ j h s i.val (l.get i)

lemma upSum_append (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (l : List (Fin K)) (x : Fin K) :
    upSum β τ j h s (l ++ [x]) = (1 - lr G.H (l.length + 1)) * upSum β τ j h s l +
      lr G.H (l.length + 1) * upTerm β τ j h s l.length x := by
  unfold upSum
  have key := sum_fin_append l x (fun (i : ℕ) (k' : Fin K) =>
    lrW G.H (l ++ [x]).length (i + 1) * upTerm β τ j h s i k')
  beta_reduce at key
  rw [key]
  simp only [List.length_append, List.length_singleton]
  rw [lrW_zero_succ, lrW_self G.H (l.length + 1) (by omega)]
  have hs : ∑ i : Fin l.length, lrW G.H (l.length + 1) (i.val + 1) *
      upTerm β τ j h s i.val (l.get i) =
      (1 - lr G.H (l.length + 1)) * ∑ i : Fin l.length, lrW G.H l.length (i.val + 1) *
      upTerm β τ j h s i.val (l.get i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [lrW_succ_of_le G.H l.length (i.val + 1) (by omega) (by omega)]; ring)
  rw [hs]
  ring

lemma lowSum_append (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (l : List (Fin K)) (x : Fin K) :
    lowSum β τ j h s (l ++ [x]) = (1 - lr G.H (l.length + 1)) * lowSum β τ j h s l +
      lr G.H (l.length + 1) * lowTerm β τ j h s l.length x := by
  unfold lowSum
  have key := sum_fin_append l x (fun (i : ℕ) (k' : Fin K) =>
    lrW G.H (l ++ [x]).length (i + 1) * lowTerm β τ j h s i k')
  beta_reduce at key
  rw [key]
  simp only [List.length_append, List.length_singleton]
  rw [lrW_self G.H (l.length + 1) (by omega)]
  have hs : ∑ i : Fin l.length, lrW G.H (l.length + 1) (i.val + 1) *
      lowTerm β τ j h s i.val (l.get i) =
      (1 - lr G.H (l.length + 1)) * ∑ i : Fin l.length, lrW G.H l.length (i.val + 1) *
      lowTerm β τ j h s i.val (l.get i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [lrW_succ_of_le G.H l.length (i.val + 1) (by omega) (by omega)]; ring)
  rw [hs]

/-- `Ṽ` in unrolled form (every run state). -/
lemma tilde_up (k : ℕ) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ k).vTildeUp j h s = upSum β τ j h s ((runState G β τ k).visits h s) := by
  induction k with
  | zero =>
    simp [runState, RunState.init, upSum, lrW_zero_zero]
    all_goals exact Finset.sum_eq_zero (fun i _ => absurd i.isLt (by simp))
  | succ k ih =>
    by_cases hk : k < K
    · have hrs : runState G β τ (k + 1) =
          episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩) := by
        simp [runState, hk]
      rw [hrs]
      by_cases he : (τ ⟨k, hk⟩ h).1 = s
      · have hv : (episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩)).visits h s =
            (runState G β τ k).visits h s ++ [⟨k, hk⟩] := by
          simp [episodeUpdate, he]
        rw [hv, upSum_append, ← ih]
        simp only [episodeUpdate, he, if_true, RunState.N, upTerm]
      · have hv : (episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩)).visits h s =
            (runState G β τ k).visits h s := by
          simp [episodeUpdate, he]
        rw [hv, ← ih]
        simp [episodeUpdate, he]
    · have hrs : runState G β τ (k + 1) = runState G β τ k := by simp [runState, hk]
      rw [hrs]; exact ih

/-- `Ṽ̲` in unrolled form (every run state). -/
lemma tilde_low (k : ℕ) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ k).vTildeLow j h s = lowSum β τ j h s ((runState G β τ k).visits h s) := by
  induction k with
  | zero =>
    simp [runState, RunState.init, lowSum]
    all_goals exact (Finset.sum_eq_zero (fun i _ => absurd i.isLt (by simp))).symm
  | succ k ih =>
    by_cases hk : k < K
    · have hrs : runState G β τ (k + 1) =
          episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩) := by
        simp [runState, hk]
      rw [hrs]
      by_cases he : (τ ⟨k, hk⟩ h).1 = s
      · have hv : (episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩)).visits h s =
            (runState G β τ k).visits h s ++ [⟨k, hk⟩] := by
          simp [episodeUpdate, he]
        rw [hv, lowSum_append, ← ih]
        simp only [episodeUpdate, he, if_true, RunState.N, lowTerm]
      · have hv : (episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩)).visits h s =
            (runState G β τ k).visits h s := by
          simp [episodeUpdate, he]
        rw [hv, ← ih]
        simp [episodeUpdate, he]
    · have hrs : runState G β τ (k + 1) = runState G β τ k := by simp [runState, hk]
      rw [hrs]; exact ih

lemma vUp_eq_min (k : ℕ) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ k).vUp j h s = min ((G.H : ℝ) - h.val) ((runState G β τ k).vTildeUp j h s) := by
  induction k with
  | zero => simp [runState, RunState.init]
  | succ k ih =>
    by_cases hk : k < K
    · have hrs : runState G β τ (k + 1) =
          episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩) := by
        simp [runState, hk]
      rw [hrs]
      by_cases he : (τ ⟨k, hk⟩ h).1 = s
      · simp only [episodeUpdate, he, if_true]
      · simp only [episodeUpdate, he, ↓reduceIte]; exact ih
    · have hrs : runState G β τ (k + 1) = runState G β τ k := by simp [runState, hk]
      rw [hrs]; exact ih

lemma vLow_eq_max (k : ℕ) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ k).vLow j h s = max 0 ((runState G β τ k).vTildeLow j h s) := by
  induction k with
  | zero => simp [runState, RunState.init]
  | succ k ih =>
    by_cases hk : k < K
    · have hrs : runState G β τ (k + 1) =
          episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩) := by
        simp [runState, hk]
      rw [hrs]
      by_cases he : (τ ⟨k, hk⟩ h).1 = s
      · simp only [episodeUpdate, he, if_true]
      · simp only [episodeUpdate, he, ↓reduceIte]; exact ih
    · have hrs : runState G β τ (k + 1) = runState G β τ k := by simp [runState, hk]
      rw [hrs]; exact ih

/-- `𝔼_{π^{k'}}[r + ℙ V̲^{k'}_{h+1}](s)`. -/
noncomputable def lowExp (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (k' : Fin K) : ℝ :=
  ∑ a : G.JointAct, RunState.jointProb alg (runState G β τ k'.val) h s a *
    (G.r j h s a + ∑ s', G.P h s a s' * (runState G β τ k'.val).vLowNext j h s')

/-- `𝔼_{b × π^{k'}_{−j}}[r + ℙ V^{k'}_{h+1}](s)`. -/
noncomputable def devExp (j : Fin G.m) (b : Fin (G.A j)) (h : Fin G.H) (s : Fin G.S)
    (k' : Fin K) : ℝ :=
  ∑ a : G.JointAct, RunState.devProb alg (runState G β τ k'.val) j b h s a *
    (G.r j h s a + ∑ s', G.P h s a s' * (runState G β τ k'.val).vUpNext j h s')

/-- Pessimism hypothesis (Azuma event for `V̲`): at every `(k, j, h, s)`. -/
def PesHyp : Prop := ∀ (k : Fin K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S),
  ∑ i : Fin ((runState G β τ k.val).visits h s).length,
    lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
      (lowTerm β τ j h s i.val (((runState G β τ k.val).visits h s).get i) -
        lowExp alg β τ j h s (((runState G β τ k.val).visits h s).get i)) ≤ 0

/-- Optimism hypothesis (regret + Azuma event for `V`): at every `(k, j, h, s, b)`. -/
def OptHyp : Prop := ∀ (k : Fin K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (b : Fin (G.A j)),
  ∑ i : Fin ((runState G β τ k.val).visits h s).length,
    lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
      (devExp alg β τ j b h s (((runState G β τ k.val).visits h s).get i) -
        upTerm β τ j h s i.val (((runState G β τ k.val).visits h s).get i)) ≤ 0

lemma pes_ind (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (hP : PesHyp alg β τ)
    (j : Fin G.m) :
    ∀ d h, G.H - h ≤ d → ∀ (hh : h < G.H) (k : Fin K) (s : Fin G.S),
      (runState G β τ k.val).vLow j ⟨h, hh⟩ s ≤ outVal G alg β τ j h k s := by
  intro d
  induction d with
  | zero => intro h hd hh; omega
  | succ d ih =>
    intro h hd hh k s
    have hnext : ∀ (k' : Fin K) (s' : Fin G.S),
        (runState G β τ k'.val).vLowNext j ⟨h, hh⟩ s' ≤ outVal G alg β τ j (h + 1) k' s' := by
      intro k' s'
      unfold RunState.vLowNext
      split_ifs with hh1
      · exact ih (h + 1) (by omega) hh1 k' s'
      · exact (outVal_bounds alg β τ hG halg j _ (h + 1) le_rfl k' s').1
    have hF : ∀ k' : Fin K, lowExp alg β τ j ⟨h, hh⟩ s k' ≤
        ∑ a : G.JointAct, RunState.jointProb alg (runState G β τ k'.val) ⟨h, hh⟩ s a *
          (G.r j ⟨h, hh⟩ s a + ∑ s', G.P ⟨h, hh⟩ s a s' * outVal G alg β τ j (h + 1) k' s') := by
      intro k'
      unfold lowExp
      apply Finset.sum_le_sum; intro a _
      apply mul_le_mul_of_nonneg_left _ (jointProb_nonneg alg _ halg _ _ a)
      apply add_le_add le_rfl
      apply Finset.sum_le_sum; intro s' _
      exact mul_le_mul_of_nonneg_left (hnext k' s') (hG.P_nonneg _ _ _ s')
    have hF0 : ∀ k' : Fin K, 0 ≤
        ∑ a : G.JointAct, RunState.jointProb alg (runState G β τ k'.val) ⟨h, hh⟩ s a *
          (G.r j ⟨h, hh⟩ s a + ∑ s', G.P ⟨h, hh⟩ s a s' * outVal G alg β τ j (h + 1) k' s') := by
      intro k'
      apply le_wsum _ _ _ (jointProb_nonneg alg _ halg _ _) (jointProb_sum alg _ halg _ _)
      intro a
      have hr := (hG.r_mem j ⟨h, hh⟩ s a).1
      have := le_wsum (G.P ⟨h, hh⟩ s a) _ 0 (hG.P_nonneg _ _ _) (hG.P_sum _ _ _)
        (fun s' => (outVal_bounds alg β τ hG halg j _ (h + 1) le_rfl k' s').1)
      linarith
    have hp := hP k j ⟨h, hh⟩ s
    rw [vLow_eq_max, tilde_low, outVal, dif_pos hh]
    dsimp only
    apply max_le
    · exact add_nonneg (mul_nonneg (lrW_nonneg _ _ _) (hF0 k))
        (Finset.sum_nonneg fun i _ => mul_nonneg (lrW_nonneg _ _ _) (hF0 _))
    · unfold lowSum
      refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg (lrW_nonneg _ _ _) (hF0 k)))
      refine le_trans ?_ (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hF _) (lrW_nonneg _ _ _))
      rw [← sub_nonpos, ← Finset.sum_sub_distrib]
      exact le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => by ring)) hp

lemma opt_ind (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (hO : OptHyp alg β τ)
    (j : Fin G.m) (μ : DevPolicy G j) :
    ∀ d h, G.H - h ≤ d → ∀ (hh : h < G.H) (k : Fin K) (hist : List (Fin G.S × G.JointAct))
      (s : Fin G.S), brW G alg β τ j μ h k hist s ≤ (runState G β τ k.val).vUp j ⟨h, hh⟩ s := by
  intro d
  induction d with
  | zero => intro h hd hh; omega
  | succ d ih =>
    intro h hd hh k hist s
    have hnext : ∀ (k' : Fin K) (hist' : List (Fin G.S × G.JointAct)) (s' : Fin G.S),
        brW G alg β τ j μ (h + 1) k' hist' s' ≤ (runState G β τ k'.val).vUpNext j ⟨h, hh⟩ s' := by
      intro k' hist' s'
      unfold RunState.vUpNext
      split_ifs with hh1
      · exact ih (h + 1) (by omega) hh1 k' hist' s'
      · rw [brW, dif_neg hh1]
    have hF : ∀ k' : Fin K, (∑ a : G.JointAct,
        RunState.devProb alg (runState G β τ k'.val) j (μ hist s) ⟨h, hh⟩ s a *
          (G.r j ⟨h, hh⟩ s a + ∑ s', G.P ⟨h, hh⟩ s a s' *
            brW G alg β τ j μ (h + 1) k' (hist ++ [(s, a)]) s')) ≤
        devExp alg β τ j (μ hist s) ⟨h, hh⟩ s k' := by
      intro k'
      unfold devExp
      apply Finset.sum_le_sum; intro a _
      apply mul_le_mul_of_nonneg_left _ (devProb_nonneg alg _ halg j _ _ _ a)
      apply add_le_add le_rfl
      apply Finset.sum_le_sum; intro s' _
      exact mul_le_mul_of_nonneg_left (hnext k' _ s') (hG.P_nonneg _ _ _ s')
    have hFk : ∀ k' : Fin K, (∑ a : G.JointAct,
        RunState.devProb alg (runState G β τ k'.val) j (μ hist s) ⟨h, hh⟩ s a *
          (G.r j ⟨h, hh⟩ s a + ∑ s', G.P ⟨h, hh⟩ s a s' *
            brW G alg β τ j μ (h + 1) k' (hist ++ [(s, a)]) s')) ≤ (G.H : ℝ) - h := by
      intro k'
      have hc : (G.H : ℝ) - h = 1 + ((G.H - (h + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : h + 1 ≤ G.H)]; push_cast; ring
      rw [hc]
      apply wsum_le _ _ _ (devProb_nonneg alg _ halg j _ _ _) (devProb_sum alg _ halg j _ _ _)
      intro a
      have hr := (hG.r_mem j ⟨h, hh⟩ s a).2
      have := wsum_le (G.P ⟨h, hh⟩ s a) _ _ (hG.P_nonneg _ _ _) (hG.P_sum _ _ _)
        (fun s' => (brW_bounds alg β τ hG halg j μ _ (h + 1) le_rfl k' (hist ++ [(s, a)]) s').2)
      linarith
    have hp := hO k j ⟨h, hh⟩ s (μ hist s)
    rw [vUp_eq_min, tilde_up]
    apply le_min
    · have hb := (brW_bounds alg β τ hG halg j μ (G.H - h) h le_rfl k hist s).2
      rw [Nat.cast_sub hh.le] at hb
      exact hb
    · rw [brW, dif_pos hh]
      dsimp only
      unfold upSum
      apply add_le_add (mul_le_mul_of_nonneg_left (hFk k) (lrW_nonneg _ _ _))
      refine le_trans (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hF _) (lrW_nonneg _ _ _)) ?_
      rw [← sub_nonpos, ← Finset.sum_sub_distrib]
      exact le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => by ring)) hp

/-- Layer I conclusion: the good top event follows from the start condition and the
per-`(k, j, h, s)` optimism/pessimism inequalities. -/
lemma goodTop_of_hyps (hG : G.Standing) (halg : ∀ j, (alg j).Valid)
    (hO : OptHyp alg β τ) (hP : PesHyp alg β τ)
    (hs : ∀ k : Fin K, (τ k ⟨0, hG.H_pos⟩).1 = G.s1) : GoodTop alg β hG.H_pos τ := by
  refine ⟨hs, fun k j μ => ?_, fun k j => ?_⟩
  · exact opt_ind alg β τ hG halg hO j μ _ 0 le_rfl hG.H_pos k [] G.s1
  · exact pes_ind alg β τ hG halg hP j _ 0 le_rfl hG.H_pos k G.s1

end layerI

/-! ## Layer J: split of the optimism/pessimism sums into regret, martingale and bonus parts -/
section layerJ
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}
  (τ : Fin K → Episode G)

lemma policy_devProb_sum (σ : RunState G K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S)
    (a : G.JointAct) :
    ∑ b, σ.policy alg j h s b * RunState.devProb alg σ j b h s a =
      RunState.jointProb alg σ h s a := by
  unfold RunState.devProb RunState.jointProb
  have hd : ∀ b : Fin (G.A j), (∏ j', if j' = j then (if a j = b then (1:ℝ) else 0)
      else σ.policy alg j' h s (a j')) =
      (if a j = b then 1 else 0) * ∏ j' ∈ ({j}ᶜ : Finset (Fin G.m)), σ.policy alg j' h s (a j') := by
    intro b
    rw [Fintype.prod_eq_mul_prod_compl j, if_pos rfl]
    congr 1
    exact Finset.prod_congr rfl (fun j' hj' => if_neg (by simpa using hj'))
  simp_rw [hd]
  rw [Fintype.prod_eq_mul_prod_compl j, Finset.sum_eq_single (a j)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/-- `𝔼_{π^{k'}}[r + ℙ V^{k'}_{h+1}](s)`. -/
noncomputable def jExpUp (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (k' : Fin K) : ℝ :=
  ∑ a : G.JointAct, RunState.jointProb alg (runState G β τ k'.val) h s a *
    (G.r j h s a + ∑ s', G.P h s a s' * (runState G β τ k'.val).vUpNext j h s')

/-- `⟨θ, 𝔼_{· × π_{−j}}[…]⟩ = 𝔼_π[…]`: the learner's expected payoff is the joint expectation. -/
lemma devExp_avg (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (k' : Fin K) :
    ∑ b, (runState G β τ k'.val).policy alg j h s b * devExp alg β τ j b h s k' =
      jExpUp alg β τ j h s k' := by
  unfold devExp jExpUp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← policy_devProb_sum alg (runState G β τ k'.val) j h s a, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun b _ => by ring)

lemma visits_len_le (k : Fin K) (h : Fin G.H) (s : Fin G.S) :
    ((runState G β τ k.val).visits h s).length ≤ K := by
  rw [visits_eq]
  exact (visList_length_le _ s k.val).trans k.isLt.le

/-- Deterministic split: regret bound `Y`, martingale bound `X` and the bonus lower bound give
`OptHyp` and `PesHyp`. -/
lemma hyps_of_bounds (X : ℕ → ℝ) (Y : Fin G.m → ℕ → ℝ)
    (hreg : ∀ (k : Fin K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (b : Fin (G.A j)),
      ∑ i : Fin ((runState G β τ k.val).visits h s).length,
        lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
          (devExp alg β τ j b h s (((runState G β τ k.val).visits h s).get i) -
            jExpUp alg β τ j h s (((runState G β τ k.val).visits h s).get i)) ≤
        Y j ((runState G β τ k.val).visits h s).length)
    (hup : ∀ (k : Fin K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S),
      ∑ i : Fin ((runState G β τ k.val).visits h s).length,
        lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
          (jExpUp alg β τ j h s (((runState G β τ k.val).visits h s).get i) -
            (G.r j h s (τ (((runState G β τ k.val).visits h s).get i) h).2 +
              (runState G β τ (((runState G β τ k.val).visits h s).get i).val).vUpAfter j
                (τ (((runState G β τ k.val).visits h s).get i)) h)) ≤
        X ((runState G β τ k.val).visits h s).length)
    (hlow : ∀ (k : Fin K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S),
      ∑ i : Fin ((runState G β τ k.val).visits h s).length,
        lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
          ((G.r j h s (τ (((runState G β τ k.val).visits h s).get i) h).2 +
              (runState G β τ (((runState G β τ k.val).visits h s).get i).val).vLowAfter j
                (τ (((runState G β τ k.val).visits h s).get i)) h) -
            lowExp alg β τ j h s (((runState G β τ k.val).visits h s).get i)) ≤
        X ((runState G β τ k.val).visits h s).length)
    (hbon : ∀ (j : Fin G.m) (t : ℕ), 1 ≤ t → t ≤ K →
      Y j t + X t ≤ ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ∧
        X t ≤ ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i) :
    OptHyp alg β τ ∧ PesHyp alg β τ := by
  constructor
  · intro k j h s b
    by_cases hl : ((runState G β τ k.val).visits h s).length = 0
    · exact le_of_eq (Finset.sum_eq_zero (fun i _ => absurd i.isLt (by omega)))
    · have hb := hbon j _ (by omega) (visits_len_le β τ k h s)
      rw [sum_Icc_eq_sum_fin] at hb
      have hu := hup k j h s
      have hr := hreg k j h s b
      have e : ∑ i : Fin ((runState G β τ k.val).visits h s).length, lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
            (devExp alg β τ j b h s (((runState G β τ k.val).visits h s).get i) - upTerm β τ j h s i.val (((runState G β τ k.val).visits h s).get i)) =
          ∑ i : Fin ((runState G β τ k.val).visits h s).length, lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
            (devExp alg β τ j b h s (((runState G β τ k.val).visits h s).get i) - jExpUp alg β τ j h s (((runState G β τ k.val).visits h s).get i)) +
          ∑ i : Fin ((runState G β τ k.val).visits h s).length, lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
            (jExpUp alg β τ j h s (((runState G β τ k.val).visits h s).get i) -
              (G.r j h s (τ (((runState G β τ k.val).visits h s).get i) h).2 +
                (runState G β τ (((runState G β τ k.val).visits h s).get i).val).vUpAfter j (τ (((runState G β τ k.val).visits h s).get i)) h)) -
          ∑ i : Fin ((runState G β τ k.val).visits h s).length, lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) * β j (i.val + 1) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by unfold upTerm; ring)
      rw [e]
      linarith [hb.1]
  · intro k j h s
    by_cases hl : ((runState G β τ k.val).visits h s).length = 0
    · exact le_of_eq (Finset.sum_eq_zero (fun i _ => absurd i.isLt (by omega)))
    · have hb := hbon j _ (by omega) (visits_len_le β τ k h s)
      rw [sum_Icc_eq_sum_fin] at hb
      have hl2 := hlow k j h s
      have e : ∑ i : Fin ((runState G β τ k.val).visits h s).length,
          lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
            (lowTerm β τ j h s i.val (((runState G β τ k.val).visits h s).get i) -
              lowExp alg β τ j h s (((runState G β τ k.val).visits h s).get i)) =
          ∑ i : Fin ((runState G β τ k.val).visits h s).length,
            lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
              ((G.r j h s (τ (((runState G β τ k.val).visits h s).get i) h).2 +
                (runState G β τ (((runState G β τ k.val).visits h s).get i).val).vLowAfter j
                  (τ (((runState G β τ k.val).visits h s).get i)) h) -
              lowExp alg β τ j h s (((runState G β τ k.val).visits h s).get i)) -
          ∑ i : Fin ((runState G β τ k.val).visits h s).length,
            lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) * β j (i.val + 1) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by unfold lowTerm; ring)
      rw [e]
      linarith [hb.2]

end layerJ

/-! ## Layer K: GoodProbClaim from two probability bounds (regret event, Azuma event) -/
section layerK
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}

/-- Regret event: every weighted regret of every bandit is at most `H ξ(A_j, t, ι)`. -/
def RegOK (ξ : ℕ → ℕ → ℝ → ℝ) (ι : ℝ) (τ : Fin K → Episode G) : Prop :=
  ∀ (k : Fin K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (b : Fin (G.A j)),
    ∑ i : Fin ((runState G β τ k.val).visits h s).length,
      lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
        (devExp alg β τ j b h s (((runState G β τ k.val).visits h s).get i) -
          jExpUp alg β τ j h s (((runState G β τ k.val).visits h s).get i)) ≤
      (G.H : ℝ) * ξ (G.A j) ((runState G β τ k.val).visits h s).length ι

/-- Azuma event for both martingales, deviation `2 √(H³ι/t)`. -/
def MOK (ι : ℝ) (τ : Fin K → Episode G) : Prop :=
  (∀ (k : Fin K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S),
    ∑ i : Fin ((runState G β τ k.val).visits h s).length,
      lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
        (jExpUp alg β τ j h s (((runState G β τ k.val).visits h s).get i) -
          (G.r j h s (τ (((runState G β τ k.val).visits h s).get i) h).2 +
            (runState G β τ (((runState G β τ k.val).visits h s).get i).val).vUpAfter j
              (τ (((runState G β τ k.val).visits h s).get i)) h)) ≤
      2 * Real.sqrt ((G.H : ℝ) ^ 3 * ι / ((runState G β τ k.val).visits h s).length)) ∧
  (∀ (k : Fin K) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S),
    ∑ i : Fin ((runState G β τ k.val).visits h s).length,
      lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
        ((G.r j h s (τ (((runState G β τ k.val).visits h s).get i) h).2 +
            (runState G β τ (((runState G β τ k.val).visits h s).get i).val).vLowAfter j
              (τ (((runState G β τ k.val).visits h s).get i)) h) -
          lowExp alg β τ j h s (((runState G β τ k.val).visits h s).get i)) ≤
      2 * Real.sqrt ((G.H : ℝ) ^ 3 * ι / ((runState G β τ k.val).visits h s).length))

lemma goodProb_of_bounds (hG : G.Standing) (halg : ∀ j, (alg j).Valid)
    (ξ : ℕ → ℕ → ℝ → ℝ) (hA : ∀ j, Assumption1 G.H (alg j) ξ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hK : 1 ≤ K)
    (hβ : ∀ j t, 1 ≤ t → t ≤ K →
      2 * bonusScale G ξ (G.A j) (iota G K δ) t ≤ ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i)
    (hR : trainProb G alg β K (fun τ => ¬ RegOK alg β ξ (iota G K δ) τ) ≤ δ / 2)
    (hM : trainProb G alg β K (fun τ => ¬ MOK alg β (iota G K δ) τ) ≤ δ / 2) :
    1 - δ ≤ trainProb G alg β K (GoodTop alg β hG.H_pos) := by
  have hm := hG.m_pos
  have j0 : Fin G.m := ⟨0, hm⟩
  have hAmax1 : 1 ≤ G.Amax := le_trans (hG.A_pos j0) (A_le_Amax G j0)
  have hι := iota_pos hG hK hδ0 hδ1 hAmax1
  refine trainProb_ge_ae alg β hG halg (Finset.univ : Finset Bool)
    (fun i τ => if i then ¬ RegOK alg β ξ (iota G K δ) τ else ¬ MOK alg β (iota G K δ) τ)
    _ ?_ δ ?_
  · intro τ hw hnot
    by_contra hcon
    push_neg at hcon
    have h1 := hcon true (Finset.mem_univ _)
    have h2 := hcon false (Finset.mem_univ _)
    simp only [if_true, Bool.false_eq_true, if_false, not_not] at h1 h2
    apply hnot
    refine goodTop_of_hyps alg β τ hG halg ?_ ?_ (fun k => start_of_weight_ne alg β hG.H_pos τ hw k)
    all_goals
      have hh := hyps_of_bounds alg β τ
        (fun t => 2 * Real.sqrt ((G.H : ℝ) ^ 3 * iota G K δ / t))
        (fun j t => (G.H : ℝ) * ξ (G.A j) t (iota G K δ)) h1 h2.1 h2.2 (by
          intro j t ht1 htK
          have hb := hβ j t ht1 htK
          have hx := xi_nonneg G.H (alg j) (halg j) ξ (hA j) (hG.A_pos j) t _ hι
          have hH0 : (0 : ℝ) ≤ G.H := Nat.cast_nonneg _
          have hsq := Real.sqrt_nonneg ((G.H : ℝ) ^ 3 * iota G K δ / t)
          unfold bonusScale at hb
          constructor <;> nlinarith [mul_nonneg hH0 hx])
    · exact hh.1
    · exact hh.2
  · simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    linarith

end layerK
section layerL

/-- Supermartingale form of `hist_sum`: sub-stochastic history kernels have total mass `≤ 1`. -/
lemma hist_sum_le {X : Type*} [Fintype X] (x0 : X) : ∀ (n : ℕ) (g : Fin n → (Fin n → X) → X → ℝ),
    (∀ i e e', (∀ j : Fin n, j < i → e j = e' j) → g i e = g i e') →
    (∀ i e y, 0 ≤ g i e y) →
    (∀ i e, ∑ y, g i e y ≤ 1) →
    ∑ e : Fin n → X, ∏ i : Fin n, g i e (e i) ≤ 1
  | 0, g, _, _, _ => by simp
  | n + 1, g, hdep, hnn, hsum => by
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => X)).sum_comp, Fintype.sum_prod_type]
    have h0 : ∀ x (e' : Fin n → X), g 0 (Fin.cons x e') = g 0 (fun _ => x0) :=
      fun x e' => hdep 0 _ _ (fun j hj => absurd hj (Fin.not_lt_zero j))
    have step : ∀ x : X, ∑ e' : Fin n → X, ∏ i : Fin (n+1),
        g i (Fin.cons x e') ((Fin.cons x e' : Fin (n+1) → X) i) ≤ g 0 (fun _ => x0) x := by
      intro x
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, h0]
      rw [← Finset.mul_sum]
      have hrec : ∑ e' : Fin n → X, ∏ j : Fin n, g j.succ (Fin.cons x e') (e' j) ≤ 1 := by
        refine hist_sum_le x0 n (fun j e' y => g j.succ (Fin.cons x e') y) ?_
          (fun j e' y => hnn _ _ _) (fun j e' => hsum _ _)
        intro j e' e'' hj
        apply hdep
        intro i hi
        cases i using Fin.cases with
        | zero => simp
        | succ i' => simp only [Fin.cons_succ]; exact hj i' (Fin.succ_lt_succ_iff.mp hi)
      calc _ ≤ g 0 (fun _ => x0) x * 1 :=
            mul_le_mul_of_nonneg_left hrec (hnn _ _ _)
        _ = _ := mul_one _
    exact (Finset.sum_le_sum (fun x _ => step x)).trans (hsum 0 _)

/-- Discrete Hoeffding lemma for a finite probability vector. -/
lemma hoeff_fin {X : Type*} [Fintype X] (q f : X → ℝ) (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) (a b : ℝ) (hf : ∀ x, f x ∈ Set.Icc a b) (l : ℝ) :
    ∑ x, q x * Real.exp (l * (f x - ∑ y, q y * f y)) ≤ Real.exp (l ^ 2 * (b - a) ^ 2 / 8) := by
  classical
  let _ : MeasurableSpace X := ⊤
  have : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  let μ : MeasureTheory.Measure X := ∑ x, ENNReal.ofReal (q x) • MeasureTheory.Measure.dirac x
  have hμu : μ Set.univ = 1 := by
    simp only [μ, MeasureTheory.Measure.coe_finsetSum, Finset.sum_apply,
      MeasureTheory.Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hq0 x), hq1, ENNReal.ofReal_one]
  have : MeasureTheory.IsProbabilityMeasure μ := ⟨hμu⟩
  have hint : ∀ g : X → ℝ, ∫ x, g x ∂μ = ∑ x, q x * g x := by
    intro g
    rw [MeasureTheory.integral_finsetSum_measure
      (fun x _ => (MeasureTheory.Integrable.of_finite (μ := MeasureTheory.Measure.dirac x)).smul_measure
        ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
      ENNReal.toReal_ofReal (hq0 x), smul_eq_mul]
  set m := ∑ y, q y * f y with hm
  have hY := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := μ) (X := fun x => f x - m) (a := a - m) (b := b - m)
    (Measurable.of_discrete).aemeasurable
    (MeasureTheory.ae_of_all _ (fun x => ⟨by linarith [(hf x).1], by linarith [(hf x).2]⟩))
    (by rw [hint]; simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1, one_mul,
          hm, sub_self])
  have h1 := hY.mgf_le l
  have h2 : ProbabilityTheory.mgf (fun x => f x - m) μ l =
      ∑ x, q x * Real.exp (l * (f x - m)) := by
    unfold ProbabilityTheory.mgf; rw [hint]
  rw [h2] at h1
  refine h1.trans (le_of_eq ?_)
  congr 1
  have : ((‖b - m - (a - m)‖₊ / 2) ^ 2 : NNReal) = ((b - a) / 2) ^ 2 := by
    rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
    simp only [sub_sub_sub_cancel_right, NNReal.coe_ofNat]
    rw [div_pow, div_pow, sq_abs]
  rw [this]; ring

/-- `∑_{i=1}^t (α^i_t)^2 ≤ 2H/t` (Jin et al. 2018, Lemma 4.1). -/
lemma lrW_sq_sum (H : ℕ) (hH : 1 ≤ H) : ∀ t : ℕ, 1 ≤ t →
    ∑ i ∈ Finset.Icc 1 t, lrW H t i ^ 2 ≤ 2 * H / t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton, lrW_self H 1 le_rfl, lr_one]
    have : (1 : ℝ) ≤ H := by exact_mod_cast hH
    norm_num; linarith
  | succ t ht ih =>
    rw [Finset.sum_Icc_succ_top (by omega), lrW_self H (t+1) (by omega)]
    have hs : ∑ i ∈ Finset.Icc 1 t, lrW H (t+1) i ^ 2 =
        (1 - lr H (t+1)) ^ 2 * ∑ i ∈ Finset.Icc 1 t, lrW H t i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_Icc] at hi
      rw [lrW_succ_of_le H t i hi.1 hi.2]; ring
    rw [hs, one_sub_lr_succ]
    have hl : lr H (t+1) = ((H : ℝ) + 1) / ((H : ℝ) + t + 1) := by
      unfold lr; push_cast; ring_nf
    rw [hl]
    have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hD : (0 : ℝ) < H + t + 1 := by linarith
    calc ((t : ℝ) / (H + t + 1)) ^ 2 * ∑ i ∈ Finset.Icc 1 t, lrW H t i ^ 2 +
          (((H : ℝ) + 1) / (H + t + 1)) ^ 2
        ≤ ((t : ℝ) / (H + t + 1)) ^ 2 * (2 * H / t) + (((H : ℝ) + 1) / (H + t + 1)) ^ 2 := by
          gcongr
      _ ≤ 2 * (H : ℝ) / ((t + 1 : ℕ) : ℝ) := by
          push_cast
          rw [show ((t : ℝ) / (H + t + 1)) ^ 2 * (2 * H / t) + (((H : ℝ) + 1) / (H + t + 1)) ^ 2
            = (2 * H * t + (H + 1) ^ 2) / (H + t + 1) ^ 2 by field_simp <;> ring]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_pos (by linarith : (0:ℝ) < H) (by linarith : (0:ℝ) < t),
            sq_nonneg (H : ℝ), mul_pos (mul_pos (by linarith : (0:ℝ) < H) (by linarith : (0:ℝ) < H))
              (by linarith : (0:ℝ) < H)]

/-- Value ranges along the run: `V, V̲ ∈ [0, H-h]`, `Ṽ ≥ 0`, `Ṽ̲ ≤ H-h` (needs `β ≥ 0`). -/
lemma vrange {G : Game} {K : ℕ} (hG : G.Standing) (β : Fin G.m → ℕ → ℝ)
    (hβ0 : ∀ j t, 0 ≤ β j t) (τ : Fin K → Episode G) :
    ∀ (k : ℕ) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S),
    0 ≤ (runState G β τ k).vTildeUp j h s ∧ 0 ≤ (runState G β τ k).vUp j h s ∧
    (runState G β τ k).vUp j h s ≤ (G.H : ℝ) - h.val ∧
    (runState G β τ k).vTildeLow j h s ≤ (G.H : ℝ) - h.val ∧
    0 ≤ (runState G β τ k).vLow j h s ∧ (runState G β τ k).vLow j h s ≤ (G.H : ℝ) - h.val := by
  intro k
  induction k with
  | zero =>
    intro j h s
    have : (h.val : ℝ) < G.H := by exact_mod_cast h.isLt
    simp only [runState, RunState.init]
    refine ⟨by linarith, by linarith, le_rfl, by linarith, le_rfl, by linarith⟩
  | succ k ih =>
    intro j h s
    by_cases hk : k < K
    · have hrs : runState G β τ (k + 1) =
          episodeUpdate G β (runState G β τ k) ⟨k, hk⟩ (τ ⟨k, hk⟩) := by
        simp [runState, hk]
      rw [hrs]
      have hhR : (h.val : ℝ) + 1 ≤ G.H := by exact_mod_cast h.isLt
      have hA : 0 ≤ (runState G β τ k).vUpAfter j (τ ⟨k, hk⟩) h ∧
          (runState G β τ k).vUpAfter j (τ ⟨k, hk⟩) h ≤ (G.H : ℝ) - h.val - 1 := by
        unfold RunState.vUpAfter
        split_ifs with hh
        · obtain ⟨_, h2, h3, _⟩ := ih j ⟨h.val + 1, hh⟩ ((τ ⟨k, hk⟩) ⟨h.val + 1, hh⟩).1
          simp only at h3; push_cast at h3
          exact ⟨h2, by linarith⟩
        · have : (G.H : ℝ) ≤ h.val + 1 := by exact_mod_cast (not_lt.mp hh)
          exact ⟨le_rfl, by linarith⟩
      have hLA : 0 ≤ (runState G β τ k).vLowAfter j (τ ⟨k, hk⟩) h ∧
          (runState G β τ k).vLowAfter j (τ ⟨k, hk⟩) h ≤ (G.H : ℝ) - h.val - 1 := by
        unfold RunState.vLowAfter
        split_ifs with hh
        · obtain ⟨_, _, _, _, h5, h6⟩ := ih j ⟨h.val + 1, hh⟩ ((τ ⟨k, hk⟩) ⟨h.val + 1, hh⟩).1
          simp only at h6; push_cast at h6
          exact ⟨h5, by linarith⟩
        · have : (G.H : ℝ) ≤ h.val + 1 := by exact_mod_cast (not_lt.mp hh)
          exact ⟨le_rfl, by linarith⟩
      have hr := hG.r_mem j h s ((τ ⟨k, hk⟩) h).2
      have hlr0 := lr_nonneg G.H ((runState G β τ k).N h s + 1)
      have hlr1 := lr_le_one G.H ((runState G β τ k).N h s + 1) (by omega)
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih j h s
      have hb := hβ0 j ((runState G β τ k).N h s + 1)
      have hHh : (0 : ℝ) ≤ G.H - h.val := by linarith
      simp only [episodeUpdate]
      split_ifs with he
      · have p1 := mul_nonneg (sub_nonneg.2 hlr1) i1
        have p2 := mul_nonneg hlr0 (add_nonneg (add_nonneg hr.1 hA.1) hb)
        have p3 := mul_le_mul_of_nonneg_left i4 (sub_nonneg.2 hlr1)
        have p4 : lr G.H ((runState G β τ k).N h s + 1) *
            (G.r j h s ((τ ⟨k, hk⟩) h).2 + (runState G β τ k).vLowAfter j (τ ⟨k, hk⟩) h -
              β j ((runState G β τ k).N h s + 1)) ≤
            lr G.H ((runState G β τ k).N h s + 1) * ((G.H : ℝ) - h.val) :=
          mul_le_mul_of_nonneg_left (by linarith [hr.2, hLA.2]) hlr0
        have p5 : (1 - lr G.H ((runState G β τ k).N h s + 1)) * ((G.H : ℝ) - h.val) +
            lr G.H ((runState G β τ k).N h s + 1) * ((G.H : ℝ) - h.val) = (G.H : ℝ) - h.val := by
          ring
        refine ⟨by linarith, le_min hHh (by linarith), min_le_left _ _, by linarith,
          le_max_left _ _, max_le hHh (by linarith)⟩
      · exact ⟨i1, i2, i3, i4, i5, i6⟩
    · have hrs : runState G β τ (k + 1) = runState G β τ k := by simp [runState, hk]
      rw [hrs]; exact ih j h s

/-- One Azuma step: a centred bounded increment has normalised exponential moment `≤ 1`. -/
lemma hoeff_step {X : Type*} [Fintype X] (q f : X → ℝ) (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) (B Bm : ℝ) (hf : ∀ x, f x ∈ Set.Icc 0 B) (hB : 0 ≤ B) (hBm : B ≤ Bm)
    (l : ℝ) :
    ∑ x, q x * Real.exp (l * ((∑ y, q y * f y) - f x) - l ^ 2 * Bm ^ 2 / 8) ≤ 1 := by
  have h1 := hoeff_fin q f hq0 hq1 0 B hf (-l)
  have h2 : ∀ x, q x * Real.exp (l * ((∑ y, q y * f y) - f x) - l ^ 2 * Bm ^ 2 / 8) =
      Real.exp (-(l ^ 2 * Bm ^ 2 / 8)) *
        (q x * Real.exp (-l * (f x - ∑ y, q y * f y))) := by
    intro x
    rw [show l * ((∑ y, q y * f y) - f x) - l ^ 2 * Bm ^ 2 / 8 =
      -(l ^ 2 * Bm ^ 2 / 8) + -l * (f x - ∑ y, q y * f y) by ring, Real.exp_add]; ring
  simp only [h2, ← Finset.mul_sum]
  have h3 : Real.exp ((-l) ^ 2 * (B - 0) ^ 2 / 8) ≤ Real.exp (l ^ 2 * Bm ^ 2 / 8) := by
    apply Real.exp_le_exp.mpr
    have : B ^ 2 ≤ Bm ^ 2 := pow_le_pow_left₀ hB hBm 2
    have : 0 ≤ l ^ 2 := sq_nonneg l
    nlinarith
  calc Real.exp (-(l ^ 2 * Bm ^ 2 / 8)) * ∑ x, q x * Real.exp (-l * (f x - ∑ y, q y * f y))
      ≤ Real.exp (-(l ^ 2 * Bm ^ 2 / 8)) * Real.exp (l ^ 2 * Bm ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left (h1.trans h3) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- Two-stage kernels: a factor whose inner conditional average is sub-stochastic. -/
lemma sum_split_le {S A : Type*} [Fintype S] [Fintype A] (T : S → ℝ) (Q φ : S → A → ℝ)
    (hT : ∀ s, 0 ≤ T s) (hb : ∀ s, ∑ a, Q s a * φ s a ≤ ∑ a, Q s a) :
    ∑ y : S × A, T y.1 * Q y.1 y.2 * φ y.1 y.2 ≤ ∑ y : S × A, T y.1 * Q y.1 y.2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_le_sum (fun s _ => ?_)
  simp only [mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hb s) (hT s)

end layerL


/-! ## Layer M: Azuma-Hoeffding on the trace process (supermartingale) -/
section layerM
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ}

noncomputable def nextV (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (σ : RunState G K)
    (h : Fin G.H) (s' : Fin G.S) : ℝ :=
  if hh : h.val + 1 < G.H then vs σ ⟨h.val + 1, hh⟩ s' else 0

noncomputable def gV (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (σ : RunState G K)
    (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (a : G.JointAct) : ℝ :=
  G.r j h s a + ∑ s', G.P h s a s' * nextV vs σ h s'

noncomputable def mV (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (σ : RunState G K)
    (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) : ℝ :=
  ∑ a, RunState.jointProb alg σ h s a * gV vs σ j h s a

noncomputable def fV (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (σ : RunState G K)
    (j : Fin G.m) (s : Fin G.S) (e : Episode G) (h : Fin G.H) : ℝ :=
  G.r j h s (e h).2 +
    (if hh : h.val + 1 < G.H then vs σ ⟨h.val + 1, hh⟩ (e ⟨h.val + 1, hh⟩).1 else 0)

noncomputable def epF (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (σ : RunState G K) (e : Episode G) : ℝ :=
  if (e h).1 = s ∧ (σ.visits h s).length < t then
    Real.exp (l * lrW G.H t ((σ.visits h s).length + 1) * (mV alg vs σ j h s - fV vs σ j s e h) -
      l ^ 2 * lrW G.H t ((σ.visits h s).length + 1) ^ 2 * (G.H : ℝ) ^ 2 / 4)
  else 1

noncomputable def psi1 (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (σ : RunState G K) (y : Fin G.S × G.JointAct) : ℝ :=
  if y.1 = s then
    Real.exp (l * lrW G.H t ((σ.visits h s).length + 1) * (mV alg vs σ j h s - gV vs σ j h s y.2) -
      l ^ 2 * lrW G.H t ((σ.visits h s).length + 1) ^ 2 * (G.H : ℝ) ^ 2 / 8)
  else 1

noncomputable def psi2 (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (σ : RunState G K) (eh y : Fin G.S × G.JointAct) : ℝ :=
  if eh.1 = s then
    Real.exp (l * lrW G.H t ((σ.visits h s).length + 1) *
      ((∑ s', G.P h s eh.2 s' * nextV vs σ h s') - nextV vs σ h y.1) -
      l ^ 2 * lrW G.H t ((σ.visits h s).length + 1) ^ 2 * (G.H : ℝ) ^ 2 / 8)
  else 1

noncomputable def psi (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (σ : RunState G K) (h' : Fin G.H) (e : Episode G)
    (y : Fin G.S × G.JointAct) : ℝ :=
  if (σ.visits h s).length < t then
    (if h' = h then psi1 alg vs j h s t l σ y
     else if h'.val = h.val + 1 then psi2 vs h s t l σ (e h) y else 1)
  else 1

lemma prod_ite2 {n : ℕ} (h : Fin n) (A B : Fin n → ℝ) :
    ∏ h' : Fin n, (if h' = h then A h' else if h'.val = h.val + 1 then B h' else 1) =
      A h * (if hh : h.val + 1 < n then B ⟨h.val + 1, hh⟩ else 1) := by
  rw [Fintype.prod_eq_mul_prod_compl h, if_pos rfl]
  congr 1
  split_ifs with hh
  · rw [Finset.prod_eq_single (⟨h.val + 1, hh⟩ : Fin n)]
    · rw [if_neg (by simp [Fin.ext_iff]), if_pos rfl]
    · intro b hb hb2
      have hbh : b ≠ h := by simpa using hb
      rw [if_neg hbh, if_neg (fun hv => hb2 (Fin.ext hv))]
    · intro hn; exfalso; apply hn; simp [Fin.ext_iff]
  · apply Finset.prod_eq_one
    intro b hb
    have hbh : b ≠ h := by simpa using hb
    rw [if_neg hbh, if_neg (by intro hv; have := b.isLt; omega)]

lemma epF_nonneg (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (σ : RunState G K) (e : Episode G) :
    0 ≤ epF alg vs j h s t l σ e := by
  unfold epF; split_ifs <;> positivity

lemma psi_nonneg (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (σ : RunState G K) (h' : Fin G.H) (e : Episode G) (y) :
    0 ≤ psi alg vs j h s t l σ h' e y := by
  unfold psi psi1 psi2; split_ifs <;> positivity

lemma psi_dep (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (σ : RunState G K) (h' : Fin G.H) (e e' : Episode G)
    (he : ∀ i : Fin G.H, i < h' → e i = e' i) :
    psi alg vs j h s t l σ h' e = psi alg vs j h s t l σ h' e' := by
  by_cases hlt : h < h'
  · funext y; unfold psi; rw [he h hlt]
  · have hne : ¬ h'.val = h.val + 1 := by
      intro hv; exact hlt (by rw [Fin.lt_def]; omega)
    funext y
    simp only [psi, hne, if_false]

lemma epF_le (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (σ : RunState G K) (e : Episode G) :
    epF alg vs j h s t l σ e ≤ ∏ h' : Fin G.H, psi alg vs j h s t l σ h' e (e h') := by
  by_cases hlt : (σ.visits h s).length < t
  swap
  · simp [epF, psi, hlt]
  simp only [psi, hlt, if_true]
  rw [prod_ite2 h (fun h' => psi1 alg vs j h s t l σ (e h'))
    (fun h' => psi2 vs h s t l σ (e h) (e h'))]
  by_cases hs : (e h).1 = s
  · simp only [epF, psi1, psi2, hs, hlt, and_self, if_true]
    have hP : 0 ≤ l ^ 2 * lrW G.H t ((σ.visits h s).length + 1) ^ 2 * (G.H : ℝ) ^ 2 := by
      positivity
    split_ifs with hh
    · rw [← Real.exp_add]; apply le_of_eq; congr 1
      simp only [fV, gV, nextV, dif_pos hh]; ring
    · rw [mul_one]; apply Real.exp_le_exp.mpr
      simp only [fV, gV, nextV, dif_neg hh, mul_zero, Finset.sum_const_zero, add_zero]
      linarith
  · simp [epF, psi1, psi2, hs]

lemma pathKer_nonneg (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (σ : RunState G K)
    (h : Fin G.H) (e : Episode G) (y : Fin G.S × G.JointAct) : 0 ≤ pathKer alg σ h e y := by
  unfold pathKer
  apply mul_nonneg
  · split_ifs <;> first | exact hG.P_nonneg _ _ _ _ | norm_num
  · exact jointProb_nonneg alg _ halg h _ _

lemma pathKer_next (σ : RunState G K) (h h' : Fin G.H) (hv : h'.val = h.val + 1) (e : Episode G)
    (y : Fin G.S × G.JointAct) :
    pathKer alg σ h' e y = G.P h (e h).1 (e h).2 y.1 * RunState.jointProb alg σ h' y.1 y.2 := by
  unfold pathKer
  rw [dif_neg (by omega)]
  have hidx : ∀ (p : h'.val - 1 < G.H), (⟨h'.val - 1, p⟩ : Fin G.H) = h :=
    fun p => Fin.ext (by simp only; omega)
  rw [hidx]

lemma ker_psi (hG : G.Standing) (halg : ∀ j, (alg j).Valid)
    (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (σ : RunState G K)
    (hvs : ∀ h' s', 0 ≤ vs σ h' s' ∧ vs σ h' s' ≤ (G.H : ℝ) - h'.val)
    (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (t : ℕ) (l : ℝ) (h' : Fin G.H) (e : Episode G) :
    ∑ y, pathKer alg σ h' e y * psi alg vs j h s t l σ h' e y ≤ 1 := by
  have hH0 : (0 : ℝ) ≤ G.H := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ h.val := Nat.cast_nonneg _
  have hhH : (h.val : ℝ) + 1 ≤ G.H := by exact_mod_cast h.isLt
  have hnv : ∀ s', 0 ≤ nextV vs σ h s' ∧ nextV vs σ h s' ≤ (G.H : ℝ) - h.val - 1 := by
    intro s'; unfold nextV; split_ifs with hh
    · have := hvs ⟨h.val + 1, hh⟩ s'
      simp only [Nat.cast_add, Nat.cast_one] at this
      constructor <;> linarith [this.1, this.2]
    · constructor <;> linarith
  have hg : ∀ a, gV vs σ j h s a ∈ Set.Icc 0 (G.H : ℝ) := by
    intro a; unfold gV
    have hr := hG.r_mem j h s a
    have hP : ∑ s', G.P h s a s' * nextV vs σ h s' ≤ (G.H : ℝ) - h.val - 1 := by
      calc _ ≤ ∑ s', G.P h s a s' * ((G.H : ℝ) - h.val - 1) :=
            Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hnv s').2 (hG.P_nonneg _ _ _ _))
        _ = _ := by rw [← Finset.sum_mul, hG.P_sum, one_mul]
    have hP0 : 0 ≤ ∑ s', G.P h s a s' * nextV vs σ h s' :=
      Finset.sum_nonneg (fun s' _ => mul_nonneg (hG.P_nonneg _ _ _ _) (hnv s').1)
    constructor <;> linarith [hr.1, hr.2]
  have hpk1 := pathKer_sum alg hG halg σ h' e
  by_cases hlt : (σ.visits h s).length < t
  swap
  · simp only [psi, hlt, if_false, mul_one]; exact hpk1.le
  by_cases hh' : h' = h
  · subst hh'
    simp only [psi, hlt, if_true]
    calc ∑ y, pathKer alg σ h' e y * psi1 alg vs j h' s t l σ y ≤ ∑ y, pathKer alg σ h' e y := ?_
      _ = 1 := hpk1
    unfold pathKer
    refine sum_split_le (fun s0 => (if hh : h'.val = 0 then (if s0 = G.s1 then (1 : ℝ) else 0)
        else G.P ⟨h'.val - 1, by omega⟩ (e ⟨h'.val - 1, by omega⟩).1 (e ⟨h'.val - 1, by omega⟩).2 s0))
      (fun s0 a => RunState.jointProb alg σ h' s0 a) (fun s0 a => psi1 alg vs j h' s t l σ (s0, a))
      ?_ ?_
    · intro s0; split_ifs <;> first | exact hG.P_nonneg _ _ _ _ | norm_num
    · intro s0
      by_cases hs0 : s0 = s
      · subst hs0
        simp only [psi1, if_true]
        rw [jointProb_sum alg σ halg h' s0]
        have hst := hoeff_step (fun a => RunState.jointProb alg σ h' s0 a) (gV vs σ j h' s0)
          (fun a => jointProb_nonneg alg σ halg h' s0 a) (jointProb_sum alg σ halg h' s0)
          (G.H : ℝ) (G.H : ℝ) hg hH0 le_rfl (l * lrW G.H t ((σ.visits h' s0).length + 1))
        refine le_trans (le_of_eq (Finset.sum_congr rfl (fun a _ => ?_))) hst
        congr 1; congr 1; unfold mV; ring
      · simp only [psi1, if_neg hs0, mul_one]; exact le_rfl
  by_cases hv : h'.val = h.val + 1
  swap
  · simp only [psi, hlt, hh', hv, if_true, if_false, mul_one]; exact hpk1.le
  simp only [psi, hlt, hh', hv, if_true, if_false]
  by_cases hs : (e h).1 = s
  swap
  · simp only [psi2, hs, if_false, mul_one]; exact hpk1.le
  simp only [pathKer_next alg σ h h' hv e, psi2, hs, if_true]
  rw [Fintype.sum_prod_type]
  have hst := hoeff_step (fun s' => G.P h s (e h).2 s') (nextV vs σ h)
    (fun s' => hG.P_nonneg _ _ _ _) (hG.P_sum _ _ _) (G.H : ℝ) (G.H : ℝ)
    (fun s' => ⟨(hnv s').1, by linarith [(hnv s').2]⟩) hH0 le_rfl
    (l * lrW G.H t ((σ.visits h s).length + 1))
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun s' _ => ?_))) hst
  dsimp only
  have hsum : ∀ c : ℝ, ∑ a, G.P h s (e h).2 s' * RunState.jointProb alg σ h' s' a * c =
      G.P h s (e h).2 s' * c := by
    intro c
    rw [← Finset.sum_mul, ← Finset.mul_sum, jointProb_sum alg σ halg h' s', mul_one]
  rw [hsum]
  congr 1; congr 1; ring

lemma supermart (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (β : Fin G.m → ℕ → ℝ)
    (vs : RunState G K → Fin G.H → Fin G.S → ℝ)
    (hvs : ∀ (τ : Fin K → Episode G) (k : ℕ) h' s', 0 ≤ vs (runState G β τ k) h' s' ∧
      vs (runState G β τ k) h' s' ≤ (G.H : ℝ) - h'.val)
    (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (t : ℕ) (l : ℝ) :
    ∑ τ : Fin K → Episode G, traceWeight G alg β τ *
      ∏ k : Fin K, epF alg vs j h s t l (runState G β τ k.val) (τ k) ≤ 1 := by
  have y0 : Fin G.S × G.JointAct := (G.s1, fun j => ⟨0, hG.A_pos j⟩)
  calc _ ≤ ∑ τ : Fin K → Episode G, ∏ k : Fin K, ∏ h' : Fin G.H,
        (pathKer alg (runState G β τ k.val) h' (τ k) (τ k h') *
          psi alg vs j h s t l (runState G β τ k.val) h' (τ k) (τ k h')) := by
        apply Finset.sum_le_sum; intro τ _
        rw [traceWeight_eq, ← Finset.prod_mul_distrib]
        apply Finset.prod_le_prod
        · intro k _
          exact mul_nonneg (Finset.prod_nonneg (fun h' _ => pathKer_nonneg alg hG halg _ _ _ _))
            (epF_nonneg alg _ _ _ _ _ _ _ _)
        · intro k _
          rw [Finset.prod_mul_distrib]
          exact mul_le_mul_of_nonneg_left (epF_le alg _ _ _ _ _ _ _ _)
            (Finset.prod_nonneg (fun h' _ => pathKer_nonneg alg hG halg _ _ _ _))
    _ ≤ 1 := by
        refine hist_sum_le (fun _ => y0) K (fun k τ e => ∏ h' : Fin G.H,
          pathKer alg (runState G β τ k.val) h' e (e h') *
            psi alg vs j h s t l (runState G β τ k.val) h' e (e h')) ?_ ?_ ?_
        · intro k τ τ' hk
          rw [runState_congr β τ τ' k.val (fun i hi => hk i hi)]
        · intro k τ e
          exact Finset.prod_nonneg (fun h' _ =>
            mul_nonneg (pathKer_nonneg alg hG halg _ _ _ _) (psi_nonneg alg _ _ _ _ _ _ _ _ _ _))
        · intro k τ
          exact hist_sum_le y0 G.H (fun h' e y => pathKer alg (runState G β τ k.val) h' e y *
              psi alg vs j h s t l (runState G β τ k.val) h' e y)
            (fun h' e e' he => by
              funext y
              rw [pathKer_dep alg _ h' e e' he, psi_dep alg vs j h s t l _ h' e e' he])
            (fun h' e y => mul_nonneg (pathKer_nonneg alg hG halg _ _ _ _)
              (psi_nonneg alg _ _ _ _ _ _ _ _ _ _))
            (fun h' e => ker_psi alg hG halg vs _ (hvs τ k.val) j h s t l h' e)

end layerM

/-! ## Layer M2: the exponential process along one run, and the Chernoff bound -/
section layerM2
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}
  (τ : Fin K → Episode G)

noncomputable def Xv (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (k' : Fin K) : ℝ :=
  mV alg vs (runState G β τ k'.val) j h s - fV vs (runState G β τ k'.val) j s (τ k') h

noncomputable def sTerm (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (n : ℕ) (x : Fin K) : ℝ :=
  if n < t then l * lrW G.H t (n + 1) * Xv alg β τ vs j h s x -
    l ^ 2 * lrW G.H t (n + 1) ^ 2 * (G.H : ℝ) ^ 2 / 4 else 0

noncomputable def listSum (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (L : List (Fin K)) : ℝ :=
  ∑ i : Fin L.length, sTerm alg β τ vs j h s t l i.val (L.get i)

lemma listSum_append (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (L : List (Fin K)) (x : Fin K) :
    listSum alg β τ vs j h s t l (L ++ [x]) =
      listSum alg β τ vs j h s t l L + sTerm alg β τ vs j h s t l L.length x := by
  unfold listSum
  exact sum_fin_append L x (fun n y => sTerm alg β τ vs j h s t l n y)

lemma visits_succ (k : ℕ) (hk : k < K) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ (k + 1)).visits h s = if (τ ⟨k, hk⟩ h).1 = s then
      (runState G β τ k).visits h s ++ [⟨k, hk⟩] else (runState G β τ k).visits h s := by
  rw [visits_eq β τ (k + 1) h s, visits_eq β τ k h s, visList_succ, dif_pos hk]

lemma visits_succ_ge (k : ℕ) (hk : ¬ k < K) (h : Fin G.H) (s : Fin G.S) :
    (runState G β τ (k + 1)).visits h s = (runState G β τ k).visits h s := by
  rw [visits_eq β τ (k + 1) h s, visits_eq β τ k h s, visList_succ, dif_neg hk]

lemma prod_lt_succ (f : Fin K → ℝ) (k : ℕ) (hk : k < K) :
    ∏ k' : Fin K, (if k'.val < k + 1 then f k' else 1) =
      (∏ k' : Fin K, (if k'.val < k then f k' else 1)) * f ⟨k, hk⟩ := by
  have hsp : ∀ k' : Fin K, (if k'.val < k + 1 then f k' else 1) =
      (if k'.val < k then f k' else 1) * (if k' = ⟨k, hk⟩ then f k' else 1) := by
    intro k'
    by_cases h1 : k'.val < k
    · have hne : k' ≠ ⟨k, hk⟩ := fun he => by rw [he] at h1; exact lt_irrefl _ h1
      rw [if_pos (by omega), if_pos h1, if_neg hne, mul_one]
    · by_cases h2 : k' = ⟨k, hk⟩
      · subst h2; simp
      · have h3 : ¬ k'.val < k + 1 := fun h3 => h2 (Fin.ext (by simp only; omega))
        rw [if_neg h3, if_neg h1, if_neg h2, mul_one]
  rw [Finset.prod_congr rfl (fun k' _ => hsp k'), Finset.prod_mul_distrib]
  simp

lemma prod_epF_eq (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) : ∀ k : ℕ, k ≤ K →
    ∏ k' : Fin K, (if k'.val < k then epF alg vs j h s t l (runState G β τ k'.val) (τ k') else 1) =
      Real.exp (listSum alg β τ vs j h s t l ((runState G β τ k).visits h s)) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : listSum alg β τ vs j h s t l ((runState G β τ 0).visits h s) = 0 := by
      unfold listSum
      exact Finset.sum_eq_zero (fun i _ => absurd i.isLt (by simp [runState, RunState.init]))
    rw [h0, Real.exp_zero]; simp
  | succ k ih =>
    intro hk1
    have hk : k < K := by omega
    rw [prod_lt_succ _ k hk, ih (by omega), visits_succ β τ k hk h s]
    by_cases hv : (τ ⟨k, hk⟩ h).1 = s
    · rw [if_pos hv, listSum_append, Real.exp_add]
      congr 1
      unfold epF sTerm Xv
      by_cases hl : ((runState G β τ k).visits h s).length < t
      · simp only [Fin.val_mk, hv, hl, and_self, if_true]
      · simp only [Fin.val_mk, hl, and_false, if_false, Real.exp_zero]
    · rw [if_neg hv]
      unfold epF
      simp only [hv, false_and, if_false, mul_one]

lemma listSum_frozen (vs : RunState G K → Fin G.H → Fin G.S → ℝ) (j : Fin G.m) (h : Fin G.H)
    (s : Fin G.S) (t : ℕ) (l : ℝ) (k0 : ℕ) (ht : t ≤ ((runState G β τ k0).visits h s).length) :
    ∀ k, k0 ≤ k → listSum alg β τ vs j h s t l ((runState G β τ k).visits h s) =
      listSum alg β τ vs j h s t l ((runState G β τ k0).visits h s) ∧
      t ≤ ((runState G β τ k).visits h s).length := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨rfl, ht⟩
  | succ k _ ih =>
    by_cases hk : k < K
    · rw [visits_succ β τ k hk h s]
      split_ifs
      · have hz : sTerm alg β τ vs j h s t l ((runState G β τ k).visits h s).length ⟨k, hk⟩ = 0 := by
          unfold sTerm; rw [if_neg (not_lt.mpr ih.2)]
        refine ⟨by rw [listSum_append, hz, add_zero, ih.1], ?_⟩
        simp only [List.length_append, List.length_singleton]; omega
      · exact ih
    · rw [visits_succ_ge β τ k hk h s]; exact ih

end layerM2

section layerM3
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}

lemma markov_bound (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (E : (Fin K → Episode G) → Prop)
    (F : (Fin K → Episode G) → ℝ) (hF0 : ∀ τ, 0 ≤ F τ)
    (hsum : ∑ τ, traceWeight G alg β τ * F τ ≤ 1) (a : ℝ) (hE : ∀ τ, E τ → Real.exp a ≤ F τ) :
    trainProb G alg β K E ≤ Real.exp (-a) := by
  classical
  unfold trainProb
  calc ∑ τ, traceWeight G alg β τ * (if E τ then 1 else 0)
      ≤ ∑ τ, traceWeight G alg β τ * (F τ * Real.exp (-a)) := by
        apply Finset.sum_le_sum; intro τ _
        apply mul_le_mul_of_nonneg_left _ (traceWeight_nonneg alg β hG halg τ)
        split_ifs with hEt
        · have h1 := hE τ hEt
          have h2 : (1 : ℝ) = Real.exp a * Real.exp (-a) := by rw [← Real.exp_add]; simp
          rw [h2]; exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        · exact mul_nonneg (hF0 τ) (Real.exp_pos _).le
    _ = (∑ τ, traceWeight G alg β τ * F τ) * Real.exp (-a) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun τ _ => by ring)
    _ ≤ 1 * Real.exp (-a) := mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
    _ = _ := one_mul _

lemma sum_fin_len_eq (f : ℕ → ℝ) : ∀ (n t : ℕ), n = t →
    ∑ i : Fin n, f i.val = ∑ i : Fin t, f i.val := by
  rintro n t rfl; rfl

/-- Chernoff bound for one (vs, sign, j, h, s, t): failure probability `≤ exp(-2ι)`. -/
lemma badE_prob (hG : G.Standing) (halg : ∀ j, (alg j).Valid)
    (vs : RunState G K → Fin G.H → Fin G.S → ℝ)
    (hvs : ∀ (τ : Fin K → Episode G) (k : ℕ) h' s', 0 ≤ vs (runState G β τ k) h' s' ∧
      vs (runState G β τ k) h' s' ≤ (G.H : ℝ) - h'.val)
    (ε : ℝ) (hε : ε ^ 2 = 1) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) (t : ℕ) (ht : 1 ≤ t)
    (ι : ℝ) (hι : 0 ≤ ι) :
    trainProb G alg β K (fun τ => ∃ k0 : Fin K, ((runState G β τ k0.val).visits h s).length = t ∧
      2 * Real.sqrt ((G.H : ℝ) ^ 3 * ι / t) <
        ε * ∑ i : Fin ((runState G β τ k0.val).visits h s).length,
          lrW G.H ((runState G β τ k0.val).visits h s).length (i.val + 1) *
            Xv alg β τ vs j h s (((runState G β τ k0.val).visits h s).get i)) ≤
      Real.exp (-(2 * ι)) := by
  have hH1 : (1 : ℝ) ≤ G.H := by exact_mod_cast hG.H_pos
  have hL : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hc0 : 0 ≤ 2 * Real.sqrt ((G.H : ℝ) ^ 3 * ι / t) := by positivity
  have hc2 : (2 * Real.sqrt ((G.H : ℝ) ^ 3 * ι / t)) ^ 2 = 4 * ((G.H : ℝ) ^ 3 * ι / t) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have hlam0 : 0 ≤ 2 * Real.sqrt ((G.H : ℝ) ^ 3 * ι / t) * t / (G.H : ℝ) ^ 3 := by positivity
  apply markov_bound alg β hG halg _ (fun τ => ∏ k : Fin K, epF alg vs j h s t
      (ε * (2 * Real.sqrt ((G.H : ℝ) ^ 3 * ι / t) * t / (G.H : ℝ) ^ 3)) (runState G β τ k.val) (τ k))
    (fun τ => Finset.prod_nonneg (fun k _ => epF_nonneg alg _ _ _ _ _ _ _ _))
    (supermart alg hG halg β vs hvs j h s t _) (2 * ι)
  rintro τ ⟨k0, hlen, hS⟩
  generalize 2 * Real.sqrt ((G.H : ℝ) ^ 3 * ι / t) = c at hc0 hc2 hlam0 hS ⊢
  generalize hlam : c * t / (G.H : ℝ) ^ 3 = lam at hlam0 ⊢
  have h1 : ∏ k : Fin K, epF alg vs j h s t (ε * lam) (runState G β τ k.val) (τ k) =
      Real.exp (listSum alg β τ vs j h s t (ε * lam) ((runState G β τ K).visits h s)) := by
    rw [← prod_epF_eq alg β τ vs j h s t (ε * lam) K le_rfl]
    exact Finset.prod_congr rfl (fun k _ => by rw [if_pos k.isLt])
  have h2 := (listSum_frozen alg β τ vs j h s t (ε * lam) k0.val hlen.ge K k0.isLt.le).1
  rw [h1, h2]
  apply Real.exp_le_exp.mpr
  have hsT : ∀ i : Fin ((runState G β τ k0.val).visits h s).length,
      sTerm alg β τ vs j h s t (ε * lam) i.val (((runState G β τ k0.val).visits h s).get i) =
        ε * lam * lrW G.H t (i.val + 1) * Xv alg β τ vs j h s (((runState G β τ k0.val).visits h s).get i) -
          (ε * lam) ^ 2 * lrW G.H t (i.val + 1) ^ 2 * (G.H : ℝ) ^ 2 / 4 := by
    intro i; unfold sTerm; rw [if_pos (hlen ▸ i.isLt)]
  have hS' : c < ε * ∑ i : Fin ((runState G β τ k0.val).visits h s).length,
      lrW G.H t (i.val + 1) * Xv alg β τ vs j h s (((runState G β τ k0.val).visits h s).get i) := by
    have he : ∑ i : Fin ((runState G β τ k0.val).visits h s).length,
        lrW G.H ((runState G β τ k0.val).visits h s).length (i.val + 1) *
          Xv alg β τ vs j h s (((runState G β τ k0.val).visits h s).get i) =
        ∑ i : Fin ((runState G β τ k0.val).visits h s).length,
        lrW G.H t (i.val + 1) * Xv alg β τ vs j h s (((runState G β τ k0.val).visits h s).get i) :=
      Finset.sum_congr rfl (fun i _ => by rw [congrArg (fun n => lrW G.H n (i.val + 1)) hlen])
    rw [← he]; exact hS
  have hQ : ∑ i : Fin ((runState G β τ k0.val).visits h s).length, lrW G.H t (i.val + 1) ^ 2 ≤
      2 * G.H / t := by
    rw [sum_fin_len_eq (fun n => lrW G.H t (n + 1) ^ 2) _ t hlen,
      ← sum_Icc_eq_sum_fin (fun i => lrW G.H t i ^ 2) t]
    exact lrW_sq_sum G.H hG.H_pos t ht
  unfold listSum
  rw [Finset.sum_congr rfl (fun i _ => hsT i)]
  have hsplit : ∀ (a b C : ℝ) (w X : Fin ((runState G β τ k0.val).visits h s).length → ℝ),
      ∑ i, (a * w i * X i - b * w i ^ 2 * C / 4) = a * ∑ i, w i * X i - b * C / 4 * ∑ i, w i ^ 2 := by
    intro a b C w X
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit (ε * lam) ((ε * lam) ^ 2) ((G.H : ℝ) ^ 2) (fun i => lrW G.H t (i.val + 1))
    (fun i => Xv alg β τ vs j h s (((runState G β τ k0.val).visits h s).get i))]
  have ha2 : (ε * lam) ^ 2 = lam ^ 2 := by rw [mul_pow, hε, one_mul]
  rw [ha2]
  have e2 := mul_le_mul_of_nonneg_left hS'.le hlam0
  have e3 := mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ lam ^ 2 * (G.H : ℝ) ^ 2 / 4)
  have hH0 : (G.H : ℝ) ≠ 0 := by positivity
  have ht0 : (t : ℝ) ≠ 0 := by positivity
  have e4 : lam * c - lam ^ 2 * (G.H : ℝ) ^ 2 / 4 * (2 * G.H / t) = 2 * ι := by
    rw [← hlam]
    have : c * t / (G.H : ℝ) ^ 3 * c - (c * t / (G.H : ℝ) ^ 3) ^ 2 * (G.H : ℝ) ^ 2 / 4 * (2 * G.H / t)
        = c ^ 2 * t / (2 * (G.H : ℝ) ^ 3) := by field_simp; ring
    rw [this, hc2]; field_simp; ring
  have e5 : ε * lam * ∑ i : Fin ((runState G β τ k0.val).visits h s).length,
      lrW G.H t (i.val + 1) * Xv alg β τ vs j h s (((runState G β τ k0.val).visits h s).get i) =
      lam * (ε * ∑ i : Fin ((runState G β τ k0.val).visits h s).length,
      lrW G.H t (i.val + 1) * Xv alg β τ vs j h s (((runState G β τ k0.val).visits h s).get i)) := by
    ring
  linarith

end layerM3

/-! ## Layer M4: hM, union over (up/low, j, h, s, t) -/
section layerM4
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) (β : Fin G.m → ℕ → ℝ) {K : ℕ}

def vsel (b : Bool) (j : Fin G.m) : RunState G K → Fin G.H → Fin G.S → ℝ :=
  fun σ h s => cond b (σ.vUp j h s) (σ.vLow j h s)

lemma vsel_range (hG : G.Standing) (hβ0 : ∀ j t, 0 ≤ β j t) (b : Bool) (j : Fin G.m) :
    ∀ (τ : Fin K → Episode G) (k : ℕ) h' s', 0 ≤ vsel b j (runState G β τ k) h' s' ∧
      vsel b j (runState G β τ k) h' s' ≤ (G.H : ℝ) - h'.val := by
  intro τ k h' s'
  obtain ⟨-, i2, i3, -, i5, i6⟩ := vrange hG β hβ0 τ k j h' s'
  cases b
  · exact ⟨i5, i6⟩
  · exact ⟨i2, i3⟩

lemma final_count (m H S A K d : ℝ) (hm : 1 ≤ m) (hH : 1 ≤ H) (hS : 1 ≤ S) (hA : 2 ≤ A)
    (hK : 1 ≤ K) (hd0 : 0 < d) (hd1 : d < 1) :
    2 * (m * (H * (S * K))) * ((m * H * S * A * K / d) ^ 2)⁻¹ ≤ d / 2 := by
  have h1 : 1 ≤ S * K := one_le_mul_of_one_le_of_one_le hS hK
  have h2 : 1 ≤ H * (S * K) := one_le_mul_of_one_le_of_one_le hH h1
  have hM1 : 1 ≤ m * (H * (S * K)) := one_le_mul_of_one_le_of_one_le hm h2
  have hM0 : m * (H * (S * K)) ≠ 0 := by positivity
  have hA0 : A ≠ 0 := by positivity
  have hd0' : d ≠ 0 := hd0.ne'
  have heq : 2 * (m * (H * (S * K))) * ((m * H * S * A * K / d) ^ 2)⁻¹ =
      2 * d ^ 2 / (m * (H * (S * K)) * A ^ 2) := by
    field_simp
  rw [heq, div_le_div_iff₀ (by positivity) (by norm_num)]
  have h4 : 4 ≤ m * (H * (S * K)) * A ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hd0.le]

lemma hM_bound (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (hβ0 : ∀ j t, 0 ≤ β j t)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hK : 1 ≤ K) (hA2 : 2 ≤ G.Amax) :
    trainProb G alg β K (fun τ => ¬ MOK alg β (iota G K δ) τ) ≤ δ / 2 := by
  have hAmax1 : 1 ≤ G.Amax := by omega
  have hι : 0 ≤ iota G K δ := by have := iota_pos hG hK hδ0 hδ1 hAmax1; linarith
  let B : Bool × Fin G.m × Fin G.H × Fin G.S × Fin K → (Fin K → Episode G) → Prop :=
    fun i τ => ∃ k0 : Fin K,
      ((runState G β τ k0.val).visits i.2.2.1 i.2.2.2.1).length = i.2.2.2.2.val + 1 ∧
      2 * Real.sqrt ((G.H : ℝ) ^ 3 * iota G K δ / ((i.2.2.2.2.val + 1 : ℕ) : ℝ)) <
        cond i.1 1 (-1) * ∑ q : Fin ((runState G β τ k0.val).visits i.2.2.1 i.2.2.2.1).length,
          lrW G.H ((runState G β τ k0.val).visits i.2.2.1 i.2.2.2.1).length (q.val + 1) *
            Xv alg β τ (vsel i.1 i.2.1) i.2.1 i.2.2.1 i.2.2.2.1
              (((runState G β τ k0.val).visits i.2.2.1 i.2.2.2.1).get q)
  have hB : ∀ i, trainProb G alg β K (B i) ≤ Real.exp (-(2 * iota G K δ)) := by
    rintro ⟨b, j, h, s, k⟩
    exact badE_prob alg β hG halg (vsel b j) (vsel_range β hG hβ0 b j) (cond b 1 (-1))
      (by cases b <;> norm_num) j h s (k.val + 1) (by omega) _ hι
  have hcover : ∀ τ, ¬ MOK alg β (iota G K δ) τ →
      ∃ i ∈ (Finset.univ : Finset (Bool × Fin G.m × Fin G.H × Fin G.S × Fin K)), B i τ := by
    intro τ hnot
    unfold MOK at hnot
    rw [not_and_or] at hnot
    rcases hnot with hU | hU
    all_goals
      push_neg at hU
      obtain ⟨k, j, h, s, hlt⟩ := hU
      have hlen := visits_len_le (β := β) (τ := τ) k h s
      have hpos : 0 < ((runState G β τ k.val).visits h s).length := by
        by_contra h0
        have hz : ((runState G β τ k.val).visits h s).length = 0 := by omega
        have hs0 := Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin
          ((runState G β τ k.val).visits h s).length)))
          (f := fun q => lrW G.H ((runState G β τ k.val).visits h s).length (q.val + 1) *
            (0 : ℝ)) (fun q _ => absurd q.isLt (by omega))
        have hs1 : ∀ (F : Fin ((runState G β τ k.val).visits h s).length → ℝ), ∑ q, F q = 0 :=
          fun F => Finset.sum_eq_zero (fun q _ => absurd q.isLt (by omega))
        rw [hs1] at hlt
        have hc : (((runState G β τ k.val).visits h s).length : ℝ) = 0 := by exact_mod_cast hz
        rw [hc, div_zero, Real.sqrt_zero, mul_zero] at hlt
        exact lt_irrefl _ hlt
      obtain ⟨t', ht'⟩ : ∃ t', ((runState G β τ k.val).visits h s).length = t' + 1 :=
        ⟨((runState G β τ k.val).visits h s).length - 1, by omega⟩
      have hc : ((t' + 1 : ℕ) : ℝ) = (((runState G β τ k.val).visits h s).length : ℝ) := by
        rw [ht']
    · refine ⟨(true, j, h, s, ⟨t', by omega⟩), Finset.mem_univ _, k, ht', ?_⟩
      show _ < 1 * _
      rw [hc, one_mul]
      exact hlt
    · refine ⟨(false, j, h, s, ⟨t', by omega⟩), Finset.mem_univ _, k, ht', ?_⟩
      show _ < (-1) * _
      rw [hc, neg_one_mul, ← Finset.sum_neg_distrib]
      refine lt_of_lt_of_eq hlt (Finset.sum_congr rfl (fun q _ => ?_))
      have hXL : ∀ k' : Fin K, Xv alg β τ (vsel false j) j h s k' =
          lowExp alg β τ j h s k' - (G.r j h s (τ k' h).2 +
            (runState G β τ k'.val).vLowAfter j (τ k') h) := fun k' => rfl
      rw [hXL]; ring
  have hm : (1 : ℝ) ≤ G.m := by exact_mod_cast hG.m_pos
  have hH : (1 : ℝ) ≤ G.H := by exact_mod_cast hG.H_pos
  have hS : (1 : ℝ) ≤ G.S := by exact_mod_cast Fin.pos G.s1
  have hA : (2 : ℝ) ≤ G.Amax := by exact_mod_cast hA2
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hN : 0 < (G.m : ℝ) * G.H * G.S * G.Amax * K / δ := by
    apply div_pos _ hδ0
    have : (0 : ℝ) < G.m := by linarith
    have : (0 : ℝ) < G.H := by linarith
    have : (0 : ℝ) < G.S := by linarith
    have : (0 : ℝ) < G.Amax := by linarith
    have : (0 : ℝ) < K := by linarith
    positivity
  have hei : Real.exp (iota G K δ) = (G.m : ℝ) * G.H * G.S * G.Amax * K / δ := by
    unfold iota; exact Real.exp_log hN
  have hexp : Real.exp (-(2 * iota G K δ)) = (Real.exp (iota G K δ) ^ 2)⁻¹ := by
    rw [Real.exp_neg, show 2 * iota G K δ = iota G K δ + iota G K δ by ring, Real.exp_add, sq]
  calc trainProb G alg β K (fun τ => ¬ MOK alg β (iota G K δ) τ)
      ≤ trainProb G alg β K (fun τ => ∃ i ∈ (Finset.univ :
          Finset (Bool × Fin G.m × Fin G.H × Fin G.S × Fin K)), B i τ) :=
        trainProb_mono alg β hG halg _ _ hcover
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Bool × Fin G.m × Fin G.H × Fin G.S × Fin K)),
          trainProb G alg β K (B i) := trainProb_union alg β hG halg _ B
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Bool × Fin G.m × Fin G.H × Fin G.S × Fin K)),
          Real.exp (-(2 * iota G K δ)) := Finset.sum_le_sum (fun i _ => hB i)
    _ ≤ δ / 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hexp, hei]
        simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
        push_cast
        have := final_count (G.m : ℝ) G.H G.S G.Amax K δ hm hH hS hA hKr hδ0 hδ1
        convert this using 1

end layerM4

/-! ## hR step 1: flat (rank-indexed) view of the training trace. -/
section flat
open FaaSeq
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

/-- Rebuild the episode list from its flat rank-indexed sequence (rank of `(k, h)` = `h + H k`). -/
def unflat (x : Fin (K * G.H) → Fin G.S × G.JointAct) : Fin K → Episode G :=
  fun k h => x (finProdFinEquiv (k, h))

def flatOf (τ : Fin K → Episode G) : Fin (K * G.H) → Fin G.S × G.JointAct :=
  fun n => τ (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2

lemma unflat_flatOf (τ : Fin K → Episode G) : unflat (flatOf τ) = τ := by
  funext k h; simp [unflat, flatOf]

lemma flatOf_unflat (x : Fin (K * G.H) → Fin G.S × G.JointAct) : flatOf (unflat x) = x := by
  funext n; simp only [unflat, flatOf, Prod.mk.eta, Equiv.apply_symm_apply]

def flatEquiv : (Fin K → Episode G) ≃ (Fin (K * G.H) → Fin G.S × G.JointAct) :=
  ⟨flatOf, unflat, unflat_flatOf, flatOf_unflat⟩

lemma sum_flat (f : (Fin K → Episode G) → ℝ) : ∑ τ, f τ = ∑ x, f (unflat x) :=
  ((flatEquiv (G := G) (K := K)).symm.sum_comp f).symm

/-- The path kernel at flat rank `n`. -/
noncomputable def flatKer (n : Fin (K * G.H)) (x : Fin (K * G.H) → Fin G.S × G.JointAct)
    (y : Fin G.S × G.JointAct) : ℝ :=
  pathKer alg (runState G β (unflat x) (finProdFinEquiv.symm n).1.val)
    (finProdFinEquiv.symm n).2 (unflat x (finProdFinEquiv.symm n).1) y

lemma traceWeight_flat (x : Fin (K * G.H) → Fin G.S × G.JointAct) :
    traceWeight G alg β (unflat x) = ∏ n, flatKer alg β n x (x n) := by
  rw [traceWeight_eq, flat_prod (fun k h => pathKer alg (runState G β (unflat x) k.val) h
    (unflat x k) (unflat x k h))]
  apply Finset.prod_congr rfl; intro n _
  unfold flatKer; congr 1
  simp only [unflat, Prod.mk.eta, Equiv.apply_symm_apply]

lemma flatKer_dep (n : Fin (K * G.H)) (x x' : Fin (K * G.H) → Fin G.S × G.JointAct)
    (hx : ∀ m : Fin (K * G.H), m < n → x m = x' m) : flatKer alg β n x = flatKer alg β n x' := by
  unfold flatKer
  set p := finProdFinEquiv.symm n with hp
  have hn : n = finProdFinEquiv p := by rw [hp, Equiv.apply_symm_apply]
  have hlt : ∀ a : Fin K × Fin G.H, (a.1.val < p.1.val ∨ (a.1 = p.1 ∧ a.2.val < p.2.val)) →
      x (finProdFinEquiv a) = x' (finProdFinEquiv a) := by
    intro a ha; apply hx; rw [hn, Fin.lt_def]; exact (flat_rank_lt a p).2 ha
  rw [runState_congr β (unflat x) (unflat x') p.1.val
    (fun i hi => funext fun h => hlt (i, h) (Or.inl hi))]
  rw [pathKer_dep alg _ p.2 (unflat x p.1) (unflat x' p.1)
    (fun h hh => hlt (p.1, h) (Or.inr ⟨rfl, hh⟩))]

lemma flatKer_sum (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (n : Fin (K * G.H))
    (x : Fin (K * G.H) → Fin G.S × G.JointAct) : ∑ y, flatKer alg β n x y = 1 :=
  pathKer_sum alg hG halg _ _ _

lemma flatKer_nonneg (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (n : Fin (K * G.H))
    (x : Fin (K * G.H) → Fin G.S × G.JointAct) (y : Fin G.S × G.JointAct) :
    0 ≤ flatKer alg β n x y := by
  unfold flatKer pathKer
  apply mul_nonneg
  · split_ifs <;> first | exact hG.P_nonneg _ _ _ _ | norm_num
  · exact jointProb_nonneg alg _ halg _ _ _

open Classical in
lemma trainProb_flat (E : (Fin K → Episode G) → Prop) :
    trainProb G alg β K E =
      ∑ x, (∏ n, flatKer alg β n x (x n)) * (if E (unflat x) then 1 else 0) := by
  unfold trainProb
  rw [sum_flat (fun τ => traceWeight G alg β τ * (if E τ then 1 else 0))]
  simp only [traceWeight_flat]

end flat

/-! ## hR step 2: the coupling environment (Z = flat traces). -/
section env
open FaaSeq Classical
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

abbrev FSeq (G : Game) (K : ℕ) : Type := Fin (K * G.H) → Fin G.S × G.JointAct

/-- The current trace: the last private draw, or `z₀` before the first round. -/
def curZ {B : ℕ} (z0 : FSeq G K) (past : List (Fin B × FSeq G K)) : FSeq G K :=
  (past.getLast?.map Prod.snd).getD z0

/-- The full visit list of `(h₀, s₀)` in a flat trace. -/
noncomputable def fullVis (h0 : Fin G.H) (s0 : Fin G.S) (z : FSeq G K) : List (Fin K) :=
  (runState G β (unflat z) K).visits h0 s0

/-- Flat rank of step `h₀` of episode `k`. -/
abbrev slot (h0 : Fin G.H) (k : Fin K) : Fin (K * G.H) := finProdFinEquiv (k, h0)

noncomputable def tailW (r : ℕ) (z : FSeq G K) : ℝ :=
  ∏ n ∈ Finset.univ.filter (fun n : Fin (K * G.H) => r < n.val), flatKer alg β n z (z n)

/-- Coupling kernel at visit episode `k`: keep the prefix before slot `(k, h₀)`, force state `s₀`
and player `j`'s action `b` there, draw the others' actions and the rest of the run afresh. -/
noncomputable def visKer (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (k : Fin K) (zp : FSeq G K)
    (b : Fin (G.A j)) (z : FSeq G K) : ℝ :=
  (if Agree (slot h0 k).val zp z then 1 else 0) * (if (z (slot h0 k)).1 = s0 then 1 else 0) *
    RunState.devProb alg (runState G β (unflat z) k.val) j b h0 s0 (z (slot h0 k)).2 *
    tailW alg β (slot h0 k).val z

/-- The bandit feedback the V-learning player `j` records at visit episode `k` (episodeUpdate). -/
noncomputable def visFb (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (k : Fin K) (z : FSeq G K) : ℝ :=
  ((G.H : ℝ) - G.r j h0 s0 (z (slot h0 k)).2 -
    (runState G β (unflat z) k.val).vUpAfter j (unflat z k) h0) / G.H

noncomputable def cKer (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (z0 : FSeq G K)
    (past : List (Fin (G.A j) × FSeq G K)) (b : Fin (G.A j)) (z : FSeq G K) : ℝ :=
  if hi : past.length < (fullVis β h0 s0 (curZ z0 past)).length then
    visKer alg β j h0 s0 ((fullVis β h0 s0 (curZ z0 past)).get ⟨past.length, hi⟩) (curZ z0 past) b z
  else if z = curZ z0 past then 1 else 0

noncomputable def cFb (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (z0 : FSeq G K)
    (past : List (Fin (G.A j) × FSeq G K)) (_b : Fin (G.A j)) (z : FSeq G K) : ℝ :=
  if hi : past.length < (fullVis β h0 s0 (curZ z0 past)).length then
    visFb β j h0 s0 ((fullVis β h0 s0 (curZ z0 past)).get ⟨past.length, hi⟩) z
  else 0

/-- The coupling environment for player `j` at `(h₀, s₀)`. -/
noncomputable def cEnv (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) :
    AdaptiveEnv (G.A j) (FSeq G K) where
  init z0 := ∏ n, flatKer alg β n z0 (z0 n)
  kernel := cKer alg β j h0 s0
  fb := cFb β j h0 s0
  loss z0 past b := ∑ z, cKer alg β j h0 s0 z0 past b z * cFb β j h0 s0 z0 past b z

lemma runState_unflat_dep (h0 : Fin G.H) (k : Fin K) (e e' : FSeq G K)
    (he : ∀ m : Fin (K * G.H), m < slot h0 k → e m = e' m) :
    runState G β (unflat e) k.val = runState G β (unflat e') k.val :=
  runState_congr β _ _ k.val (fun i hi => funext fun h => he _ (by
    rw [Fin.lt_def]; exact (flat_rank_lt (i, h) (k, h0)).2 (Or.inl hi)))

/-- The kernel sequence of `visKer`: `flatKer` except at the forced slot. -/
noncomputable def modKer (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (k : Fin K) (b : Fin (G.A j))
    (n : Fin (K * G.H)) (e : FSeq G K) (y : Fin G.S × G.JointAct) : ℝ :=
  if n = slot h0 k then
    (if y.1 = s0 then 1 else 0) * RunState.devProb alg (runState G β (unflat e) k.val) j b h0 s0 y.2
  else flatKer alg β n e y

lemma modKer_dep (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (k : Fin K) (b : Fin (G.A j))
    (n : Fin (K * G.H)) (e e' : FSeq G K) (he : ∀ m : Fin (K * G.H), m < n → e m = e' m) :
    modKer alg β j h0 s0 k b n e = modKer alg β j h0 s0 k b n e' := by
  funext y
  by_cases hn : n = slot h0 k
  · subst hn; simp only [modKer, if_true]; rw [runState_unflat_dep β h0 k e e' he]
  · simp only [modKer, hn, if_false]; rw [flatKer_dep alg β n e e' he]

lemma modKer_sum (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (k : Fin K) (b : Fin (G.A j)) (n : Fin (K * G.H)) (e : FSeq G K) :
    ∑ y, modKer alg β j h0 s0 k b n e y = 1 := by
  by_cases hn : n = slot h0 k
  · simp only [modKer, hn, if_true]
    rw [Fintype.sum_prod_type]
    have hs : ∀ s : Fin G.S, ∑ a : G.JointAct, (if s = s0 then (1:ℝ) else 0) *
        RunState.devProb alg (runState G β (unflat e) k.val) j b h0 s0 a = if s = s0 then 1 else 0 := by
      intro s; rw [← Finset.mul_sum, devProb_sum alg _ halg, mul_one]
    simp only [hs, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [modKer, hn, if_false]; exact flatKer_sum alg β hG halg n e

lemma visKer_nonneg (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (k : Fin K) (zp : FSeq G K) (b : Fin (G.A j)) (z : FSeq G K) :
    0 ≤ visKer alg β j h0 s0 k zp b z := by
  unfold visKer tailW
  refine mul_nonneg (mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num))
    (devProb_nonneg alg _ halg _ _ _ _ _)) (Finset.prod_nonneg fun n _ => flatKer_nonneg alg β hG halg _ _ _)

lemma visKer_sum (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (k : Fin K) (zp : FSeq G K) (b : Fin (G.A j)) :
    ∑ z, visKer alg β j h0 s0 k zp b z = 1 := by
  have ht := tail_sum (modKer alg β j h0 s0 k b)
    (fun i e e' he => modKer_dep alg β j h0 s0 k b i e e' he)
    (fun i e => modKer_sum alg β hG halg j h0 s0 k b i e)
    (K * G.H - (slot h0 k).val) (slot h0 k).val (by have := (slot h0 k).isLt; omega) zp
  have hset : Finset.univ.filter (fun i : Fin (K * G.H) => (slot h0 k).val ≤ i.val) =
      insert (slot h0 k) (Finset.univ.filter (fun i : Fin (K * G.H) => (slot h0 k).val < i.val)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi; rcases Nat.lt_or_eq_of_le hi with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h.symm)
    · rintro (rfl | h)
      · exact le_refl _
      · exact h.le
  have htail : ∀ z : FSeq G K, ∏ i ∈ Finset.univ.filter (fun i : Fin (K * G.H) => (slot h0 k).val < i.val),
      modKer alg β j h0 s0 k b i z (z i) = tailW alg β (slot h0 k).val z := by
    intro z; unfold tailW; apply Finset.prod_congr rfl; intro i hi
    rw [Finset.mem_filter] at hi
    have : i ≠ slot h0 k := fun h => by rw [h] at hi; exact lt_irrefl _ hi.2
    simp only [modKer, this, if_false]
  refine Eq.trans ?_ ht
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro z _
  by_cases hz : Agree (slot h0 k).val zp z
  · rw [if_pos hz, hset, Finset.prod_insert (by simp), htail z]
    simp only [visKer, modKer, hz, if_true, one_mul, mul_assoc]
  · rw [if_neg hz]; simp only [visKer, hz, if_false, zero_mul]

lemma cKer_nonneg (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (z0 : FSeq G K) (past : List (Fin (G.A j) × FSeq G K)) (b : Fin (G.A j))
    (z : FSeq G K) : 0 ≤ cKer alg β j h0 s0 z0 past b z := by
  unfold cKer; split_ifs
  · exact visKer_nonneg alg β hG halg _ _ _ _ _ _ _
  · norm_num
  · norm_num

lemma cKer_sum (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (z0 : FSeq G K) (past : List (Fin (G.A j) × FSeq G K)) (b : Fin (G.A j)) :
    ∑ z, cKer alg β j h0 s0 z0 past b z = 1 := by
  unfold cKer
  by_cases hi : past.length < (fullVis β h0 s0 (curZ z0 past)).length
  · simp only [dif_pos hi]; exact visKer_sum alg β hG halg _ _ _ _ _ _
  · simp only [dif_neg hi, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma cEnv_valid (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (hfb : ∀ (k : Fin K) (z : FSeq G K), visFb β j h0 s0 k z ∈ Set.Icc (0 : ℝ) 1) :
    (cEnv alg β (K := K) j h0 s0).Valid := by
  have y0 : Fin G.S × G.JointAct := (G.s1, fun j => ⟨0, hG.A_pos j⟩)
  have hfb' : ∀ z0 (past : List (Fin (G.A j) × FSeq G K)) b z,
      cFb β j h0 s0 z0 past b z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z0 past b z; unfold cFb; split_ifs
    · exact hfb _ _
    · exact ⟨le_refl 0, zero_le_one⟩
  refine ⟨fun z => by
      show 0 ≤ ∏ n, flatKer alg β n z (z n)
      exact Finset.prod_nonneg fun n _ => flatKer_nonneg alg β hG halg _ _ _, ?_,
    fun z0 past b z => cKer_nonneg alg β hG halg j h0 s0 z0 past b z,
    fun z0 past b => cKer_sum alg β hG halg j h0 s0 z0 past b, ?_, fun z0 past b z => hfb' z0 past b z,
    fun z0 past b => rfl⟩
  · show ∑ z : FSeq G K, ∏ n, flatKer alg β n z (z n) = 1
    exact hist_sum y0 (K * G.H) (flatKer alg β) (fun i e e' he => flatKer_dep alg β i e e' he)
      (fun i e => flatKer_sum alg β hG halg i e)
  · intro z0 past b
    show ∑ z, _ ∈ _
    constructor
    · exact Finset.sum_nonneg fun z _ => mul_nonneg (cKer_nonneg alg β hG halg j h0 s0 z0 past b z)
        (hfb' z0 past b z).1
    · calc _ ≤ ∑ z, cKer alg β j h0 s0 z0 past b z * 1 :=
            Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hfb' z0 past b z).2
              (cKer_nonneg alg β hG halg j h0 s0 z0 past b z)
        _ = 1 := by simp only [mul_one]; exact cKer_sum alg β hG halg j h0 s0 z0 past b

end env

/-! ## hR step 3a: the i-th visit in terms of the prefix. -/
section visitc
variable {K : ℕ} {α : Type*} [DecidableEq α]

lemma visList_congr (c c' : Fin K → α) (s : α) : ∀ k : ℕ,
    (∀ k' : Fin K, k'.val < k → c k' = c' k') → visList c s k = visList c' s k
  | 0, _ => rfl
  | k + 1, hc => by
    have ih := visList_congr c c' s k (fun k' hk' => hc k' (by omega))
    rw [visList_succ, visList_succ, ih]
    by_cases hk : k < K
    · rw [dif_pos hk, dif_pos hk, hc ⟨k, hk⟩ (by simp)]
    · rw [dif_neg hk, dif_neg hk]

lemma visList_get_iff (c : Fin K → α) (s : α) (i : ℕ) (k : Fin K) :
    (∃ hi : i < (visList c s K).length, (visList c s K).get ⟨i, hi⟩ = k) ↔
      c k = s ∧ (visList c s k.val).length = i := by
  constructor
  · rintro ⟨hi, hget⟩
    have ht := visList_take_get c s ⟨i, hi⟩
    rw [hget] at ht
    refine ⟨?_, ?_⟩
    · have hm : k ∈ visList c s K := hget ▸ List.get_mem _ _
      exact ((mem_visList c s K k).1 hm).2
    · rw [← ht, List.length_take]; exact min_eq_left hi.le
  · rintro ⟨hc, hlen⟩
    obtain ⟨rest, hrest⟩ := visList_split c s k hc
    have hi : i < (visList c s K).length := by rw [hrest]; simp; omega
    refine ⟨hi, ?_⟩
    have key : ∀ (l : List (Fin K)) (h : i < l.length), l = visList c s k.val ++ k :: rest →
        l.get ⟨i, h⟩ = k := by
      rintro l h rfl; subst hlen; simp
    exact key _ hi hrest

end visitc

section visitf
open FaaSeq
variable {G : Game} {K : ℕ} (β : Fin G.m → ℕ → ℝ)

/-- Visits of `(h₀, s₀)` before episode `k` of a flat trace. -/
noncomputable def preVis (h0 : Fin G.H) (s0 : Fin G.S) (x : FSeq G K) (k : ℕ) : List (Fin K) :=
  visList (fun k' => (unflat x k' h0).1) s0 k

lemma fullVis_get_iff (h0 : Fin G.H) (s0 : Fin G.S) (x : FSeq G K) (i : ℕ) (k : Fin K) :
    (∃ hi : i < (fullVis β h0 s0 x).length, (fullVis β h0 s0 x).get ⟨i, hi⟩ = k) ↔
      (x (slot h0 k)).1 = s0 ∧ (preVis h0 s0 x k.val).length = i := by
  unfold fullVis preVis
  rw [visits_eq β (unflat x) K h0 s0]
  exact visList_get_iff _ s0 i k

lemma preVis_congr (h0 : Fin G.H) (s0 : Fin G.S) (x z : FSeq G K) (k : Fin K)
    (hxz : Agree (slot h0 k).val x z) : preVis h0 s0 x k.val = preVis h0 s0 z k.val := by
  unfold preVis
  refine visList_congr _ _ s0 k.val (fun k' hk' => ?_)
  show (x (finProdFinEquiv (k', h0))).1 = (z (finProdFinEquiv (k', h0))).1
  rw [hxz _ ((flat_rank_lt (k', h0) (k, h0)).2 (Or.inl hk'))]

/-- Two traces agreeing before slot `(k, h₀)`, both in state `s₀` there, have their `i`-th
visit of `(h₀, s₀)` at `k` simultaneously. -/
lemma visit_at_congr (h0 : Fin G.H) (s0 : Fin G.S) (x z : FSeq G K) (k : Fin K) (i : ℕ)
    (hxz : Agree (slot h0 k).val x z) (hz : (z (slot h0 k)).1 = s0) (hx : (x (slot h0 k)).1 = s0) :
    (∃ hi : i < (fullVis β h0 s0 x).length, (fullVis β h0 s0 x).get ⟨i, hi⟩ = k) ↔
      (∃ hi : i < (fullVis β h0 s0 z).length, (fullVis β h0 s0 z).get ⟨i, hi⟩ = k) := by
  rw [fullVis_get_iff, fullVis_get_iff, preVis_congr h0 s0 x z k hxz]
  simp only [hz, hx]

end visitf


/-! ## hR step 3b: cylinder sums with a constrained slot, and the resampling invariance (Lemma C). -/
section resample
open FaaSeq Classical

/-- Cylinder mass with the value at slot `m` constrained to a predicate. -/
lemma cyl_sum_pred {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (g : Fin N → (Fin N → X) → X → ℝ)
    (hdep : ∀ i e e', (∀ j : Fin N, j < i → e j = e' j) → g i e = g i e')
    (hsum : ∀ i e, ∑ y, g i e y = 1) (m : Fin N) (x : Fin N → X) (p : X → Prop)
    [DecidablePred p] :
    ∑ e ∈ Finset.univ.filter (fun e : Fin N → X => Agree m.val x e ∧ p (e m)), ∏ i : Fin N, g i e (e i) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin N => i.val < m.val), g i x (x i)) *
        ∑ y ∈ Finset.univ.filter p, g m x y := by
  have hagree : ∀ y : X, ∀ j : Fin N, j < m → Function.update x m y j = x j :=
    fun y j hj => Function.update_of_ne (ne_of_lt hj) _ _
  have hfib : ∀ y : X, ∑ e ∈ Finset.univ.filter (fun e : Fin N → X =>
      Agree (m.val + 1) (Function.update x m y) e), ∏ i, g i e (e i) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin N => i.val < m.val), g i x (x i)) * g m x y := by
    intro y
    rw [cyl_sum g hdep hsum (m.val + 1) (by omega) (Function.update x m y)]
    have hs : Finset.univ.filter (fun i : Fin N => i.val < m.val + 1) =
        insert m (Finset.univ.filter (fun i : Fin N => i.val < m.val)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hs, Finset.prod_insert (by simp), mul_comm]
    congr 1
    · apply Finset.prod_congr rfl; intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hi' : i < m := Fin.lt_def.mpr hi
      rw [hagree y i hi', hdep i _ x (fun j hj => hagree y j (lt_trans hj hi'))]
    · rw [Function.update_self, hdep m _ x (hagree y)]
  have hind : ∀ e : Fin N → X, (if Agree m.val x e ∧ p (e m) then ∏ i, g i e (e i) else 0) =
      ∑ y ∈ Finset.univ.filter p,
        (if Agree (m.val + 1) (Function.update x m y) e then ∏ i, g i e (e i) else 0) := by
    intro e
    have key : ∀ y, Agree (m.val + 1) (Function.update x m y) e ↔ Agree m.val x e ∧ e m = y := by
      intro y; constructor
      · intro h
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [h j (by omega)]; exact hagree y j (Fin.lt_def.mpr hj)
        · rw [h m (by omega), Function.update_self]
      · rintro ⟨h, rfl⟩ j hj
        by_cases hjm : j = m
        · subst hjm; rw [Function.update_self]
        · rw [Function.update_of_ne hjm]
          exact h j (by have : j.val ≠ m.val := fun h' => hjm (Fin.ext h'); omega)
    simp_rw [key]
    by_cases hA : Agree m.val x e
    · by_cases hp : p (e m)
      · rw [if_pos ⟨hA, hp⟩, Finset.sum_eq_single (e m)]
        · rw [if_pos ⟨hA, rfl⟩]
        · intro y _ hy; rw [if_neg (fun h => hy h.2.symm)]
        · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩) h
      · rw [if_neg (fun h => hp h.2)]
        symm; apply Finset.sum_eq_zero; intro y hy
        rw [if_neg]; rintro ⟨_, rfl⟩; exact hp (Finset.mem_filter.mp hy).2
    · rw [if_neg (fun h => hA h.1)]
      symm; apply Finset.sum_eq_zero; intro y _
      rw [if_neg (fun h => hA h.1)]
  rw [Finset.sum_filter, Finset.sum_congr rfl (fun e _ => hind e), Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro y _
  rw [← Finset.sum_filter, hfib y]

variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

/-- Averaging the forced action over player `j`'s own policy restores the joint law at the slot. -/
lemma visKer_avg (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (k : Fin K) (x z : FSeq G K) :
    ∑ b, (runState G β (unflat x) k.val).policy alg j h0 s0 b * visKer alg β j h0 s0 k x b z =
      (if Agree (slot h0 k).val x z then 1 else 0) * (if (z (slot h0 k)).1 = s0 then 1 else 0) *
        RunState.jointProb alg (runState G β (unflat z) k.val) h0 s0 (z (slot h0 k)).2 *
        tailW alg β (slot h0 k).val z := by
  by_cases hA : Agree (slot h0 k).val x z
  · have hrs : runState G β (unflat x) k.val = runState G β (unflat z) k.val :=
      runState_unflat_dep β h0 k x z (fun m hm => (hA m hm).symm)
    calc ∑ b, (runState G β (unflat x) k.val).policy alg j h0 s0 b * visKer alg β j h0 s0 k x b z
        = ∑ b, ((if (z (slot h0 k)).1 = s0 then 1 else 0) * tailW alg β (slot h0 k).val z) *
            ((runState G β (unflat z) k.val).policy alg j h0 s0 b *
              RunState.devProb alg (runState G β (unflat z) k.val) j b h0 s0 (z (slot h0 k)).2) :=
          Finset.sum_congr rfl (fun b _ => by simp only [visKer, hA, if_true, one_mul, hrs]; ring)
      _ = ((if (z (slot h0 k)).1 = s0 then 1 else 0) * tailW alg β (slot h0 k).val z) *
            RunState.jointProb alg (runState G β (unflat z) k.val) h0 s0 (z (slot h0 k)).2 := by
          rw [← Finset.mul_sum, policy_devProb_sum]
      _ = _ := by simp only [hA, if_true, one_mul]; ring
  · simp only [visKer, if_neg hA, zero_mul, mul_zero, Finset.sum_const_zero]

/-- The slot kernel factors as (state factor) × (joint action law at that state). -/
lemma flatKer_slot (h0 : Fin G.H) (k : Fin K) (z : FSeq G K) (s : Fin G.S) (a : G.JointAct) :
    flatKer alg β (slot h0 k) z (s, a) =
      (if hh : h0.val = 0 then (if s = G.s1 then 1 else 0)
        else G.P ⟨h0.val - 1, by omega⟩ (unflat z k ⟨h0.val - 1, by omega⟩).1
          (unflat z k ⟨h0.val - 1, by omega⟩).2 s) *
      RunState.jointProb alg (runState G β (unflat z) k.val) h0 s a := by
  simp only [flatKer, pathKer, slot, Equiv.symm_apply_apply]

lemma prod_split3 {N : ℕ} (f : Fin N → ℝ) (r : Fin N) :
    ∏ n, f n = (∏ n ∈ Finset.univ.filter (fun n : Fin N => n.val < r.val), f n) * f r *
      ∏ n ∈ Finset.univ.filter (fun n : Fin N => r.val < n.val), f n := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun n : Fin N => n.val < r.val), mul_assoc]
  congr 1
  have hset : Finset.univ.filter (fun n : Fin N => ¬ n.val < r.val) =
      insert r (Finset.univ.filter (fun n : Fin N => r.val < n.val)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hset, Finset.prod_insert (by simp)]

/-- **Lemma C** (resampling invariance): drawing the trace, then (on the event `D` fixed before
slot `(k, h₀)` and state `s₀` there) re-drawing player `j`'s action from its policy and everything
after the slot afresh, leaves the trace law unchanged. -/
lemma resample (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (k : Fin K) (D : FSeq G K → Prop)
    (hD : ∀ x z, Agree (slot h0 k).val x z → (D x ↔ D z)) (Ψ : FSeq G K → ℝ) :
    ∑ x, (∏ n, flatKer alg β n x (x n)) * (if (x (slot h0 k)).1 = s0 ∧ D x then 1 else 0) *
        ∑ b, (runState G β (unflat x) k.val).policy alg j h0 s0 b *
          ∑ z, visKer alg β j h0 s0 k x b z * Ψ z =
      ∑ z, (∏ n, flatKer alg β n z (z n)) * (if (z (slot h0 k)).1 = s0 ∧ D z then 1 else 0) * Ψ z := by
  set r := slot h0 k with hr
  set W : FSeq G K → ℝ := fun x => ∏ n, flatKer alg β n x (x n) with hW
  set pre : FSeq G K → ℝ := fun z =>
    ∏ n ∈ Finset.univ.filter (fun n : Fin (K * G.H) => n.val < r.val), flatKer alg β n z (z n) with hpre
  set c : FSeq G K → ℝ := fun z =>
    (if hh : h0.val = 0 then (if s0 = G.s1 then 1 else 0)
        else G.P ⟨h0.val - 1, by omega⟩ (unflat z k ⟨h0.val - 1, by omega⟩).1
          (unflat z k ⟨h0.val - 1, by omega⟩).2 s0) with hc
  set jp : FSeq G K → ℝ := fun z =>
    RunState.jointProb alg (runState G β (unflat z) k.val) h0 s0 (z r).2 with hjp
  -- the trace weight at a trace in state `s₀` at the slot
  have hWz : ∀ z : FSeq G K, (z r).1 = s0 → W z = pre z * c z * jp z * tailW alg β r.val z := by
    intro z hz
    simp only [hW, hpre, tailW]
    rw [prod_split3 (fun n => flatKer alg β n z (z n)) r]
    have : z r = (s0, (z r).2) := by rw [← hz]
    rw [this, flatKer_slot]
    simp only [hc, hjp, ← this]
    ring
  -- the slot mass with the state constrained
  have hslot : ∀ z : FSeq G K,
      ∑ y ∈ Finset.univ.filter (fun y : Fin G.S × G.JointAct => y.1 = s0), flatKer alg β r z y = c z := by
    intro z
    rw [hc, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single s0]
    · simp only [eq_self_iff_true, if_true, hr, flatKer_slot, ← Finset.mul_sum, jointProb_sum alg _ halg,
        mul_one]
    · intro s _ hs; exact Finset.sum_eq_zero (fun a _ => by simp [hs])
    · intro h; exact absurd (Finset.mem_univ _) h
  -- inner sum over the original trace
  have hinner : ∀ z : FSeq G K, ∑ x, W x * (if (x r).1 = s0 ∧ D x then 1 else 0) *
      (if Agree r.val x z then 1 else 0) = (if D z then 1 else 0) * (pre z * c z) := by
    intro z
    have h1 : ∀ x, W x * (if (x r).1 = s0 ∧ D x then 1 else 0) * (if Agree r.val x z then 1 else 0) =
        (if D z then 1 else 0) *
          (if Agree r.val z x ∧ (x r).1 = s0 then W x else 0) := by
      intro x
      by_cases hA : Agree r.val x z
      · have hA' : Agree r.val z x := fun j hj => (hA j hj).symm
        rw [hD x z hA]
        by_cases hs : (x r).1 = s0 <;> by_cases hd : D z <;> simp [hA, hA', hs, hd]
      · have hA' : ¬ Agree r.val z x := fun h => hA (fun j hj => (h j hj).symm)
        simp [hA, hA']
    rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum, ← Finset.sum_filter]
    simp only [hW, hpre]
    have hcs := cyl_sum_pred (flatKer alg β) (fun i e e' he => flatKer_dep alg β i e e' he)
      (fun i e => flatKer_sum alg β hG halg i e) r z (fun y => y.1 = s0)
    rw [hslot z] at hcs
    rw [← hcs]
    all_goals (congr 1; exact Finset.sum_congr (by ext x; simp only [Finset.mem_filter]) (fun _ _ => rfl))
  -- assemble
  have hstep : ∀ x z : FSeq G K, W x * (if (x r).1 = s0 ∧ D x then 1 else 0) *
      (∑ b, (runState G β (unflat x) k.val).policy alg j h0 s0 b * visKer alg β j h0 s0 k x b z) * Ψ z =
      (W x * (if (x r).1 = s0 ∧ D x then 1 else 0) * (if Agree r.val x z then 1 else 0)) *
        ((if (z r).1 = s0 then 1 else 0) * jp z * tailW alg β r.val z * Ψ z) := by
    intro x z; rw [visKer_avg]; simp only [hjp, hr]; ring
  calc _ = ∑ x, ∑ z, W x * (if (x r).1 = s0 ∧ D x then 1 else 0) *
          (∑ b, (runState G β (unflat x) k.val).policy alg j h0 s0 b * visKer alg β j h0 s0 k x b z) *
            Ψ z := by
        apply Finset.sum_congr rfl; intro x _
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro z _
        apply Finset.sum_congr rfl; intro b _
        simp only [hW]; ring
    _ = ∑ z, (∑ x, W x * (if (x r).1 = s0 ∧ D x then 1 else 0) * (if Agree r.val x z then 1 else 0)) *
          ((if (z r).1 = s0 then 1 else 0) * jp z * tailW alg β r.val z * Ψ z) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro z _
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => hstep x z)
    _ = _ := by
        apply Finset.sum_congr rfl; intro z _
        rw [hinner z]
        by_cases hz : (z r).1 = s0
        · rw [show (∏ n, flatKer alg β n z (z n)) = W z from rfl, hWz z hz]
          by_cases hd : D z <;>
            simp only [hz, hd, eq_self_iff_true, true_and, and_true, and_false, if_true, if_false] <;> ring
        · simp [hz]

end resample


/-! ## hR step 3: peeling one slot, one/two-step tail expectations, the bandit loss formula. -/
section peel
open FaaSeq Classical

lemma peel {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (g : Fin N → (Fin N → X) → X → ℝ)
    (hdep : ∀ i e e', (∀ j : Fin N, j < i → e j = e' j) → g i e = g i e')
    (r : Fin N) (x : Fin N → X) (Φ : (Fin N → X) → ℝ) :
    ∑ e ∈ Finset.univ.filter (fun e : Fin N → X => Agree r.val x e),
        (∏ i ∈ Finset.univ.filter (fun i : Fin N => r.val ≤ i.val), g i e (e i)) * Φ e =
      ∑ y, g r x y * ∑ e ∈ Finset.univ.filter
          (fun e : Fin N → X => Agree (r.val + 1) (Function.update x r y) e),
        (∏ i ∈ Finset.univ.filter (fun i : Fin N => r.val + 1 ≤ i.val), g i e (e i)) * Φ e := by
  rw [← Finset.sum_fiberwise (Finset.univ.filter (fun e : Fin N → X => Agree r.val x e))
    (fun e => e r)]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.mul_sum, Finset.filter_filter]
  have hset : Finset.univ.filter (fun e : Fin N → X => Agree r.val x e ∧ e r = y) =
      Finset.univ.filter (fun e : Fin N → X => Agree (r.val + 1) (Function.update x r y) e) := by
    apply Finset.filter_congr; intro e _; simp only [Agree]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      by_cases hjr : j = r
      · rw [hjr, Function.update_self]; exact h2
      · rw [Function.update_of_ne hjr]
        exact h1 j (by have : j.val ≠ r.val := fun h => hjr (Fin.ext h); omega)
    · intro h
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [h j (by omega), Function.update_of_ne (fun h' => by rw [h'] at hj; exact lt_irrefl _ hj)]
      · rw [h r (by omega), Function.update_self]
  rw [hset]
  apply Finset.sum_congr rfl; intro e he
  rw [Finset.mem_filter] at he
  have hsplit : Finset.univ.filter (fun i : Fin N => r.val ≤ i.val) =
      insert r (Finset.univ.filter (fun i : Fin N => r.val + 1 ≤ i.val)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hsplit, Finset.prod_insert (by simp)]
  have h1 : e r = y := by rw [he.2 r (by omega), Function.update_self]
  have hg : g r e (e r) = g r x y := by
    rw [h1, hdep r e x (fun j hj => by
      rw [he.2 j (by have : j.val < r.val := hj; omega), Function.update_of_ne (ne_of_lt hj)])]
  rw [hg]; ring

lemma tail_exp1 {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (g : Fin N → (Fin N → X) → X → ℝ)
    (hdep : ∀ i e e', (∀ j : Fin N, j < i → e j = e' j) → g i e = g i e')
    (hsum : ∀ i e, ∑ y, g i e y = 1) (r : Fin N) (x : Fin N → X) (F : X → ℝ) :
    ∑ e ∈ Finset.univ.filter (fun e : Fin N → X => Agree r.val x e),
        (∏ i ∈ Finset.univ.filter (fun i : Fin N => r.val ≤ i.val), g i e (e i)) * F (e r) =
      ∑ y, g r x y * F y := by
  rw [peel g hdep r x]
  apply Finset.sum_congr rfl; intro y _
  congr 1
  calc _ = ∑ e ∈ Finset.univ.filter (fun e : Fin N → X => Agree (r.val + 1) (Function.update x r y) e),
          (∏ i ∈ Finset.univ.filter (fun i : Fin N => r.val + 1 ≤ i.val), g i e (e i)) * F y := by
        apply Finset.sum_congr rfl; intro e he
        rw [Finset.mem_filter] at he
        rw [he.2 r (by omega), Function.update_self]
    _ = F y := by
        rw [← Finset.sum_mul, tail_sum g hdep hsum (N - (r.val + 1)) (r.val + 1)
          (by have := r.isLt; omega) (Function.update x r y), one_mul]

lemma tail_exp2 {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}
    (g : Fin N → (Fin N → X) → X → ℝ)
    (hdep : ∀ i e e', (∀ j : Fin N, j < i → e j = e' j) → g i e = g i e')
    (hsum : ∀ i e, ∑ y, g i e y = 1) (r r' : Fin N) (hr' : r'.val = r.val + 1)
    (x : Fin N → X) (F : X → X → ℝ) :
    ∑ e ∈ Finset.univ.filter (fun e : Fin N → X => Agree r.val x e),
        (∏ i ∈ Finset.univ.filter (fun i : Fin N => r.val ≤ i.val), g i e (e i)) * F (e r) (e r') =
      ∑ y, g r x y * ∑ y', g r' (Function.update x r y) y' * F y y' := by
  rw [peel g hdep r x]
  apply Finset.sum_congr rfl; intro y _
  congr 1
  rw [← hr']
  calc _ = ∑ e ∈ Finset.univ.filter (fun e : Fin N → X => Agree r'.val (Function.update x r y) e),
          (∏ i ∈ Finset.univ.filter (fun i : Fin N => r'.val ≤ i.val), g i e (e i)) * F y (e r') := by
        apply Finset.sum_congr rfl; intro e he
        rw [Finset.mem_filter] at he
        rw [he.2 r (by omega), Function.update_self]
    _ = _ := tail_exp1 g hdep hsum r' (Function.update x r y) (F y)

end peel

section loss
open FaaSeq Classical
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

lemma visKer_eq_tail (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (k : Fin K) (zp : FSeq G K)
    (b : Fin (G.A j)) (Ψ : FSeq G K → ℝ) :
    ∑ z, visKer alg β j h0 s0 k zp b z * Ψ z =
      ∑ z ∈ Finset.univ.filter (fun z : FSeq G K => Agree (slot h0 k).val zp z),
        (∏ i ∈ Finset.univ.filter (fun i : Fin (K * G.H) => (slot h0 k).val ≤ i.val),
          modKer alg β j h0 s0 k b i z (z i)) * Ψ z := by
  have hset : Finset.univ.filter (fun i : Fin (K * G.H) => (slot h0 k).val ≤ i.val) =
      insert (slot h0 k) (Finset.univ.filter (fun i : Fin (K * G.H) => (slot h0 k).val < i.val)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have htail : ∀ z : FSeq G K, ∏ i ∈ Finset.univ.filter (fun i : Fin (K * G.H) => (slot h0 k).val < i.val),
      modKer alg β j h0 s0 k b i z (z i) = tailW alg β (slot h0 k).val z := by
    intro z; unfold tailW; apply Finset.prod_congr rfl; intro i hi
    rw [Finset.mem_filter] at hi
    have : i ≠ slot h0 k := fun h => by rw [h] at hi; exact lt_irrefl _ hi.2
    simp only [modKer, this, if_false]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro z _
  by_cases hz : Agree (slot h0 k).val zp z
  · rw [if_pos hz, hset, Finset.prod_insert (by simp), htail z]
    simp only [visKer, modKer, hz, if_true, one_mul, mul_assoc]
  · rw [if_neg hz]; simp only [visKer, hz, if_false, zero_mul]

lemma sum_s0 (s0 : Fin G.S) (p : G.JointAct → ℝ) (Gf : Fin G.S → G.JointAct → ℝ) :
    ∑ y : Fin G.S × G.JointAct, (if y.1 = s0 then (1:ℝ) else 0) * p y.2 * Gf y.1 y.2 =
      ∑ a, p a * Gf s0 a := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s0 (fun s _ hs => by simp [hs]) (by simp)]
  simp

/-- **Loss formula**: the conditional mean of the recorded feedback is the bandit loss
`(H - devExp b)/H` at the visit episode. -/
lemma visKer_loss (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (k : Fin K) (zp : FSeq G K) (b : Fin (G.A j)) :
    ∑ z, visKer alg β j h0 s0 k zp b z * visFb β j h0 s0 k z =
      ((G.H : ℝ) - ∑ a : G.JointAct, RunState.devProb alg (runState G β (unflat zp) k.val) j b h0 s0 a *
        (G.r j h0 s0 a + ∑ s', G.P h0 s0 a s' * (runState G β (unflat zp) k.val).vUpNext j h0 s')) /
        G.H := by
  set σ := runState G β (unflat zp) k.val with hσ
  set r := slot h0 k with hr
  have hdep := fun i e e' he => modKer_dep alg β j h0 s0 k b i e e' he
  have hsum := fun i e => modKer_sum alg β hG halg j h0 s0 k b i e
  have hmr : ∀ y, modKer alg β j h0 s0 k b r zp y =
      (if y.1 = s0 then 1 else 0) * RunState.devProb alg σ j b h0 s0 y.2 := by
    intro y; simp only [hr, modKer, if_true, hσ]
  have hσz : ∀ z ∈ Finset.univ.filter (fun z : FSeq G K => Agree r.val zp z),
      runState G β (unflat z) k.val = σ := by
    intro z hz; rw [Finset.mem_filter] at hz
    exact runState_unflat_dep β h0 k z zp (fun m hm => hz.2 m hm)
  have hP : ∀ (a : G.JointAct) (v : Fin G.S → ℝ) (c : ℝ),
      ∑ s', G.P h0 s0 a s' * ((c - v s') / G.H) = (c - ∑ s', G.P h0 s0 a s' * v s') / G.H := by
    intro a v c
    have e1 : ∀ s', G.P h0 s0 a s' * ((c - v s') / G.H) =
        (G.P h0 s0 a s' * c - G.P h0 s0 a s' * v s') / G.H := fun s' => by ring
    rw [Finset.sum_congr rfl (fun s' _ => e1 s'), ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hG.P_sum, one_mul]
  have hD : ∀ (c : G.JointAct → ℝ),
      ∑ a, RunState.devProb alg σ j b h0 s0 a * (((G.H : ℝ) - c a) / G.H) =
        ((G.H : ℝ) - ∑ a, RunState.devProb alg σ j b h0 s0 a * c a) / G.H := by
    intro c
    have e1 : ∀ a, RunState.devProb alg σ j b h0 s0 a * (((G.H : ℝ) - c a) / G.H) =
        (RunState.devProb alg σ j b h0 s0 a * G.H - RunState.devProb alg σ j b h0 s0 a * c a) / G.H :=
      fun a => by ring
    rw [Finset.sum_congr rfl (fun a _ => e1 a), ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.sum_mul, devProb_sum alg σ halg, one_mul]
  rw [visKer_eq_tail]
  by_cases hh : h0.val + 1 < G.H
  · set h1 : Fin G.H := ⟨h0.val + 1, hh⟩ with hh1
    set r' := slot h1 k with hr'
    have hrr : r'.val = r.val + 1 := by
      simp only [hr', hr, slot, flat_val, hh1]; omega
    have hne : r' ≠ r := fun h => by rw [h] at hrr; omega
    set F : Fin G.S × G.JointAct → Fin G.S × G.JointAct → ℝ := fun y y' =>
      ((G.H : ℝ) - G.r j h0 s0 y.2 - σ.vUp j h1 y'.1) / G.H with hF
    rw [Finset.sum_congr rfl (fun z hz => by
      rw [show visFb β j h0 s0 k z = F (z r) (z r') by
        simp only [visFb, hσz z hz, RunState.vUpAfter, dif_pos hh, hF]; rfl])]
    rw [tail_exp2 _ hdep hsum r r' hrr zp F]
    have hin : ∀ y : Fin G.S × G.JointAct, ∑ y', modKer alg β j h0 s0 k b r'
        (Function.update zp r y) y' * F y y' =
        ∑ s', G.P h0 y.1 y.2 s' * (((G.H : ℝ) - G.r j h0 s0 y.2 - σ.vUp j h1 s') / G.H) := by
      intro y
      have hu : unflat (Function.update zp r y) k h0 = y := by
        simp only [unflat, hr, slot, Function.update_self]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro s' _
      have hne2 : slot h1 k ≠ slot h0 k := hne
      simp only [modKer, hr', hne2, if_false, flatKer_slot, hF]
      rw [dif_neg (by simp [hh1])]
      have e2 : (⟨h1.val - 1, by have := h1.isLt; omega⟩ : Fin G.H) = h0 := Fin.ext (by simp [hh1])
      simp only [e2, hu]
      rw [← Finset.sum_mul, ← Finset.mul_sum, jointProb_sum alg _ halg, mul_one]
    simp only [hin, hmr]
    rw [sum_s0 s0 (RunState.devProb alg σ j b h0 s0)
      (fun s a => ∑ s', G.P h0 s a s' * (((G.H : ℝ) - G.r j h0 s0 a - σ.vUp j h1 s') / G.H))]
    simp only [hP]
    simp only [sub_sub]
    have hD' := hD (fun a => G.r j h0 s0 a + ∑ s', G.P h0 s0 a s' * σ.vUp j h1 s')
    rw [hD']
    congr 2
    apply Finset.sum_congr rfl; intro a _
    simp only [RunState.vUpNext, dif_pos hh, ← hσ]
    ring
  · set F : Fin G.S × G.JointAct → ℝ := fun y => ((G.H : ℝ) - G.r j h0 s0 y.2) / G.H with hF
    rw [Finset.sum_congr rfl (fun z hz => by
      rw [show visFb β j h0 s0 k z = F (z r) by
        simp only [visFb, hσz z hz, RunState.vUpAfter, dif_neg hh, hF, sub_zero]; rfl])]
    rw [tail_exp1 _ hdep hsum r zp F]
    simp only [hmr]
    rw [sum_s0 s0 (RunState.devProb alg σ j b h0 s0) (fun _ a => ((G.H : ℝ) - G.r j h0 s0 a) / G.H)]
    have hD' := hD (fun a => G.r j h0 s0 a)
    rw [hD']
    congr 2
    apply Finset.sum_congr rfl; intro a _
    simp only [RunState.vUpNext, dif_neg hh, mul_zero, Finset.sum_const_zero, add_zero]

end loss

section histA
variable {G : Game} {K : ℕ} (β : Fin G.m → ℕ → ℝ)

/-- The bandit feedback a visit episode `k'` records at `(h, s)` for player `j`. -/
noncomputable def recFb (τ : Fin K → Episode G) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S)
    (k' : Fin K) : Fin (G.A j) × ℝ :=
  ((τ k' h).2 j, ((G.H : ℝ) - G.r j h s (τ k' h).2 - (runState G β τ k'.val).vUpAfter j (τ k') h) / G.H)

/-- **Lemma A0**: the bandit history is the feedback of the visit list, oldest first. -/
lemma hist_eq (τ : Fin K → Episode G) (j : Fin G.m) (h : Fin G.H) (s : Fin G.S) :
    ∀ k : ℕ, (runState G β τ k).hist j h s =
      ((runState G β τ k).visits h s).map (recFb β τ j h s)
  | 0 => rfl
  | k + 1 => by
    simp only [runState]
    by_cases hk : k < K
    · rw [dif_pos hk]
      simp only [episodeUpdate]
      by_cases he : (τ ⟨k, hk⟩ h).1 = s
      · rw [if_pos he, if_pos he, List.map_append, ← hist_eq τ j h s k]
        simp only [List.map_cons, List.map_nil, recFb, he]
      · rw [if_neg he, if_neg he]; exact hist_eq τ j h s k
    · rw [dif_neg hk]; exact hist_eq τ j h s k

end histA


/-! ## hR step 4: snoc calculus for adaptive histories, and the law of the coupled trace (B). -/
section snocA
variable {B : ℕ} {Z : Type} [Fintype Z]

lemma sum_snoc {X : Type*} [Fintype X] {t : ℕ} (f : (Fin (t + 1) → X) → ℝ) :
    ∑ ω, f ω = ∑ ω' : Fin t → X, ∑ p : X, f (Fin.snoc (α := fun _ => X) ω' p) := by
  let e : (Fin t → X) × X ≃ (Fin (t + 1) → X) :=
    { toFun := fun q => Fin.snoc (α := fun _ => X) q.1 q.2
      invFun := fun ω => (Fin.init ω, ω (Fin.last t))
      left_inv := fun q => by simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun ω => Fin.snoc_init_self ω }
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  rfl

lemma past_snoc {t : ℕ} (ω : Fin t → Fin B × Z) (p : Fin B × Z) (i : ℕ) (hi : i ≤ t) :
    AdaptiveEnv.past (Fin.snoc (α := fun _ => Fin B × Z) ω p) i = AdaptiveEnv.past ω i := by
  unfold AdaptiveEnv.past
  simp only [List.ofFn_succ', Fin.snoc_castSucc, List.concat_eq_append]
  rw [List.take_append_of_le_length (by simpa using hi)]

lemma past_full {t : ℕ} (ω : Fin t → Fin B × Z) : AdaptiveEnv.past ω t = List.ofFn ω := by
  unfold AdaptiveEnv.past
  exact List.take_of_length_le (by simp)

lemma fbList_snoc (env : AdaptiveEnv B Z) (z0 : Z) {t : ℕ} (ω : Fin t → Fin B × Z)
    (p : Fin B × Z) (i : ℕ) (hi : i ≤ t) :
    env.fbList z0 (Fin.snoc (α := fun _ => Fin B × Z) ω p) i = env.fbList z0 ω i := by
  have hf : ∀ i' : Fin t, AdaptiveEnv.past (Fin.snoc (α := fun _ => Fin B × Z) ω p) i'.val =
      AdaptiveEnv.past ω i'.val := fun i' => past_snoc ω p i'.val i'.isLt.le
  unfold AdaptiveEnv.fbList
  simp only [List.ofFn_succ', Fin.snoc_castSucc, Fin.coe_castSucc, hf, List.concat_eq_append]
  rw [List.take_append_of_le_length (by simpa using hi)]

lemma theta_snoc (env : AdaptiveEnv B Z) (alg : BanditRule B) (z0 : Z) {t : ℕ}
    (ω : Fin t → Fin B × Z) (p : Fin B × Z) (i : ℕ) (hi : i ≤ t) :
    env.theta alg z0 (Fin.snoc (α := fun _ => Fin B × Z) ω p) i = env.theta alg z0 ω i := by
  unfold AdaptiveEnv.theta
  rw [fbList_snoc env z0 ω p i hi]

lemma weight_snoc (env : AdaptiveEnv B Z) (alg : BanditRule B) (z0 : Z) {t : ℕ}
    (ω : Fin t → Fin B × Z) (p : Fin B × Z) :
    env.weight alg z0 (Fin.snoc (α := fun _ => Fin B × Z) ω p) =
      env.weight alg z0 ω * (env.theta alg z0 ω t p.1 * env.kernel z0 (List.ofFn ω) p.1 p.2) := by
  have h1 : ∀ i : Fin t, env.theta alg z0 (Fin.snoc (α := fun _ => Fin B × Z) ω p) i.val =
      env.theta alg z0 ω i.val := fun i => theta_snoc env alg z0 ω p _ i.isLt.le
  have h2 : ∀ i : Fin t, AdaptiveEnv.past (Fin.snoc (α := fun _ => Fin B × Z) ω p) i.val =
      AdaptiveEnv.past ω i.val := fun i => past_snoc ω p _ i.isLt.le
  unfold AdaptiveEnv.weight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last, h1, h2,
    theta_snoc env alg z0 ω p t le_rfl, past_snoc ω p t le_rfl, past_full]
  ring

end snocA

section lawB
open FaaSeq Classical
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

lemma cKer_of_lt (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (z0 : FSeq G K)
    (past : List (Fin (G.A j) × FSeq G K)) (t : ℕ) (hlen : past.length = t)
    (hi : t < (fullVis β h0 s0 (curZ z0 past)).length) (b : Fin (G.A j)) (z : FSeq G K) :
    cKer alg β j h0 s0 z0 past b z =
      visKer alg β j h0 s0 ((fullVis β h0 s0 (curZ z0 past)).get ⟨t, hi⟩) (curZ z0 past) b z := by
  subst hlen; unfold cKer; rw [dif_pos hi]

lemma cKer_of_ge (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (z0 : FSeq G K)
    (past : List (Fin (G.A j) × FSeq G K)) (t : ℕ) (hlen : past.length = t)
    (hi : ¬ t < (fullVis β h0 s0 (curZ z0 past)).length) (b : Fin (G.A j)) (z : FSeq G K) :
    cKer alg β j h0 s0 z0 past b z = if z = curZ z0 past then 1 else 0 := by
  subst hlen; unfold cKer; rw [dif_neg hi]

lemma sum_visit_sel (h0 : Fin G.H) (s0 : Fin G.S) (x : FSeq G K) (t : ℕ) (g : Fin K → ℝ) :
    ∑ k : Fin K, (if (x (slot h0 k)).1 = s0 ∧ (preVis h0 s0 x k.val).length = t then 1 else 0) * g k =
      if hi : t < (fullVis β h0 s0 x).length then g ((fullVis β h0 s0 x).get ⟨t, hi⟩) else 0 := by
  have hc : ∀ k : Fin K, ((x (slot h0 k)).1 = s0 ∧ (preVis h0 s0 x k.val).length = t) ↔
      (∃ hi : t < (fullVis β h0 s0 x).length, (fullVis β h0 s0 x).get ⟨t, hi⟩ = k) :=
    fun k => (fullVis_get_iff (β := β) h0 s0 x t k).symm
  by_cases hi : t < (fullVis β h0 s0 x).length
  · rw [dif_pos hi]
    have h' : ∀ k : Fin K, ((x (slot h0 k)).1 = s0 ∧ (preVis h0 s0 x k.val).length = t) ↔
        (fullVis β h0 s0 x).get ⟨t, hi⟩ = k :=
      fun k => (hc k).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨hi, h⟩⟩
    simp only [h', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · rw [dif_neg hi]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [if_neg (fun h => hi ((hc k).1 h).1), zero_mul]

/-- **Lemma B (law)**: given the support invariant `hθ` (the learner's strategy at round `t` is the
V-learning policy at the `t`-th visit), the coupled environment's last private draw has the law of
the training trace. -/
lemma law (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S)
    (hθ : ∀ (t : ℕ) (z0 : FSeq G K) (ω : Fin t → Fin (G.A j) × FSeq G K),
      (cEnv alg β j h0 s0).weight (alg j) z0 ω ≠ 0 →
      ∀ hi : t < (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).length,
        (cEnv alg β j h0 s0).theta (alg j) z0 ω t =
          (runState G β (unflat (curZ z0 (List.ofFn ω)))
            ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨t, hi⟩).val).policy alg j h0 s0) :
    ∀ (t : ℕ) (Ψ : FSeq G K → ℝ),
      ∑ z0, ∑ ω : Fin t → Fin (G.A j) × FSeq G K,
          (cEnv alg β j h0 s0).weight (alg j) z0 ω * Ψ (curZ z0 (List.ofFn ω)) =
        ∑ z, (∏ n, flatKer alg β n z (z n)) * Ψ z := by
  intro t
  induction t with
  | zero =>
    intro Ψ
    refine Finset.sum_congr rfl (fun z0 _ => ?_)
    rw [Fintype.sum_unique]
    simp [AdaptiveEnv.weight, curZ, cEnv]
  | succ t ih =>
    intro Ψ
    let F : FSeq G K → ℝ := fun x =>
      if hi : t < (fullVis β h0 s0 x).length then
        ∑ b, (runState G β (unflat x) ((fullVis β h0 s0 x).get ⟨t, hi⟩).val).policy alg j h0 s0 b *
          ∑ z, visKer alg β j h0 s0 ((fullVis β h0 s0 x).get ⟨t, hi⟩) x b z * Ψ z
      else Ψ x
    have hstep : ∀ (z0 : FSeq G K) (ω : Fin t → Fin (G.A j) × FSeq G K),
        ∑ p : Fin (G.A j) × FSeq G K,
            (cEnv alg β j h0 s0).weight (alg j) z0
              (Fin.snoc (α := fun _ => Fin (G.A j) × FSeq G K) ω p) *
            Ψ (curZ z0 (List.ofFn (Fin.snoc (α := fun _ => Fin (G.A j) × FSeq G K) ω p))) =
          (cEnv alg β j h0 s0).weight (alg j) z0 ω * F (curZ z0 (List.ofFn ω)) := by
      intro z0 ω
      have hc : ∀ p : Fin (G.A j) × FSeq G K,
          curZ z0 (List.ofFn (Fin.snoc (α := fun _ => Fin (G.A j) × FSeq G K) ω p)) = p.2 := by
        intro p; rw [List.ofFn_succ', List.concat_eq_append]; simp [curZ, Fin.snoc_last]
      simp only [weight_snoc, hc]
      by_cases hw : (cEnv alg β j h0 s0).weight (alg j) z0 ω = 0
      · simp [hw]
      rw [Fintype.sum_prod_type]
      have hre : ∀ (b : Fin (G.A j)) (z : FSeq G K),
          (cEnv alg β j h0 s0).weight (alg j) z0 ω *
              ((cEnv alg β j h0 s0).theta (alg j) z0 ω t b *
                (cEnv alg β j h0 s0).kernel z0 (List.ofFn ω) b z) * Ψ z =
            (cEnv alg β j h0 s0).weight (alg j) z0 ω *
              ((cEnv alg β j h0 s0).theta (alg j) z0 ω t b *
                ((cEnv alg β j h0 s0).kernel z0 (List.ofFn ω) b z * Ψ z)) := by
        intros; ring
      simp only [hre, ← Finset.mul_sum]
      congr 1
      have hlen : (List.ofFn ω).length = t := List.length_ofFn
      by_cases hi : t < (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).length
      · have hk : ∀ b z, (cEnv alg β j h0 s0).kernel z0 (List.ofFn ω) b z =
            visKer alg β j h0 s0 ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨t, hi⟩)
              (curZ z0 (List.ofFn ω)) b z := fun b z =>
          cKer_of_lt (alg := alg) (β := β) j h0 s0 z0 (List.ofFn ω) t hlen hi b z
        simp only [F, dif_pos hi, hk]
        rw [hθ t z0 ω hw hi]
      · have hk : ∀ b z, (cEnv alg β j h0 s0).kernel z0 (List.ofFn ω) b z =
            if z = curZ z0 (List.ofFn ω) then 1 else 0 := fun b z =>
          cKer_of_ge (alg := alg) (β := β) j h0 s0 z0 (List.ofFn ω) t hlen hi b z
        simp only [F, dif_neg hi, hk, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        simp only [AdaptiveEnv.theta]
        rw [← Finset.sum_mul, (halg j).2.1, one_mul]
    have hF : ∀ x : FSeq G K, (∏ n, flatKer alg β n x (x n)) * F x =
        (∏ n, flatKer alg β n x (x n)) * (if t < (fullVis β h0 s0 x).length then 0 else Ψ x) +
        ∑ k : Fin K, (∏ n, flatKer alg β n x (x n)) *
          ((if (x (slot h0 k)).1 = s0 ∧ (preVis h0 s0 x k.val).length = t then 1 else 0) *
            ∑ b, (runState G β (unflat x) k.val).policy alg j h0 s0 b *
              ∑ z, visKer alg β j h0 s0 k x b z * Ψ z) := by
      intro x
      rw [← Finset.mul_sum, ← mul_add]
      congr 1
      rw [sum_visit_sel (β := β) h0 s0 x t (fun k => ∑ b, (runState G β (unflat x) k.val).policy
        alg j h0 s0 b * ∑ z, visKer alg β j h0 s0 k x b z * Ψ z)]
      by_cases hi : t < (fullVis β h0 s0 x).length
      · simp only [F, dif_pos hi, if_pos hi, zero_add]
      · simp only [F, dif_neg hi, if_neg hi, add_zero]
    have hR : ∀ k : Fin K, ∑ x : FSeq G K, (∏ n, flatKer alg β n x (x n)) *
          ((if (x (slot h0 k)).1 = s0 ∧ (preVis h0 s0 x k.val).length = t then 1 else 0) *
            ∑ b, (runState G β (unflat x) k.val).policy alg j h0 s0 b *
              ∑ z, visKer alg β j h0 s0 k x b z * Ψ z) =
        ∑ z : FSeq G K, (∏ n, flatKer alg β n z (z n)) *
          ((if (z (slot h0 k)).1 = s0 ∧ (preVis h0 s0 z k.val).length = t then 1 else 0) * Ψ z) := by
      intro k
      have := resample (alg := alg) (β := β) hG halg j h0 s0 k
        (fun x => (preVis h0 s0 x k.val).length = t)
        (fun x z hxz => by
          show (preVis h0 s0 x k.val).length = t ↔ (preVis h0 s0 z k.val).length = t
          rw [preVis_congr h0 s0 x z k hxz]) Ψ
      simp only [mul_assoc] at this ⊢
      convert this
    have hsel : ∀ z : FSeq G K, ∑ k : Fin K,
        (if (z (slot h0 k)).1 = s0 ∧ (preVis h0 s0 z k.val).length = t then (1 : ℝ) else 0) * 1 =
          if t < (fullVis β h0 s0 z).length then 1 else 0 := by
      intro z
      rw [sum_visit_sel (β := β) h0 s0 z t (fun _ => 1)]
      by_cases hi : t < (fullVis β h0 s0 z).length
      · rw [dif_pos hi, if_pos hi]
      · rw [dif_neg hi, if_neg hi]
    calc ∑ z0, ∑ ω : Fin (t + 1) → Fin (G.A j) × FSeq G K,
          (cEnv alg β j h0 s0).weight (alg j) z0 ω * Ψ (curZ z0 (List.ofFn ω))
        = ∑ z0, ∑ ω : Fin t → Fin (G.A j) × FSeq G K,
            (cEnv alg β j h0 s0).weight (alg j) z0 ω * F (curZ z0 (List.ofFn ω)) := by
          refine Finset.sum_congr rfl (fun z0 _ => ?_)
          rw [sum_snoc]
          exact Finset.sum_congr rfl (fun ω _ => hstep z0 ω)
      _ = ∑ x, (∏ n, flatKer alg β n x (x n)) * F x := ih F
      _ = ∑ z, (∏ n, flatKer alg β n z (z n)) * Ψ z := by
          simp only [hF, Finset.sum_add_distrib]
          rw [Finset.sum_comm, Finset.sum_congr rfl (fun k _ => hR k), Finset.sum_comm,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [← Finset.mul_sum, ← mul_add]
          congr 1
          have e3 : ∑ k : Fin K,
              (if (z (slot h0 k)).1 = s0 ∧ (preVis h0 s0 z k.val).length = t then (1 : ℝ) else 0) * Ψ z =
                (∑ k : Fin K, (if (z (slot h0 k)).1 = s0 ∧ (preVis h0 s0 z k.val).length = t
                  then (1 : ℝ) else 0) * 1) * Ψ z := by
            rw [Finset.sum_mul]; simp only [mul_one]
          rw [e3, hsel z]
          by_cases hi : t < (fullVis β h0 s0 z).length
          · simp [hi]
          · simp [hi]

end lawB


/-! ## hR step 5: the support invariant (A) and the law with `hθ` discharged. -/
section snocB
variable {B : ℕ} {Z : Type} [Fintype Z]

lemma fbList_last (env : AdaptiveEnv B Z) (z0 : Z) {t : ℕ} (ω : Fin t → Fin B × Z)
    (p : Fin B × Z) :
    env.fbList z0 (Fin.snoc (α := fun _ => Fin B × Z) ω p) (t + 1) =
      env.fbList z0 ω t ++ [(p.1, env.fb z0 (List.ofFn ω) p.1 p.2)] := by
  have hf : ∀ i' : Fin t, AdaptiveEnv.past (Fin.snoc (α := fun _ => Fin B × Z) ω p) i'.val =
      AdaptiveEnv.past ω i'.val := fun i' => past_snoc ω p i'.val i'.isLt.le
  have e1 : ∀ (L : List (Fin B × ℝ)) (a : Fin B × ℝ), L.length = t → (L ++ [a]).take (t + 1) = L ++ [a] :=
    fun L a hL => List.take_of_length_le (by simp [hL])
  have e2 : ∀ L : List (Fin B × ℝ), L.length = t → L.take t = L :=
    fun L hL => List.take_of_length_le (by simp [hL])
  unfold AdaptiveEnv.fbList
  simp only [List.ofFn_succ', Fin.snoc_castSucc, Fin.coe_castSucc, hf, Fin.snoc_last, Fin.val_last,
    past_snoc ω p t le_rfl, past_full, List.concat_eq_append]
  rw [e1 _ _ (by simp), e2 _ (by simp)]

end snocB

section invA
open FaaSeq Classical
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

lemma curZ_snoc {B : ℕ} (z0 : FSeq G K) {t : ℕ} (ω : Fin t → Fin B × FSeq G K) (p : Fin B × FSeq G K) :
    curZ z0 (List.ofFn (Fin.snoc (α := fun _ => Fin B × FSeq G K) ω p)) = p.2 := by
  rw [List.ofFn_succ', List.concat_eq_append]; simp [curZ, Fin.snoc_last]

lemma fullVis_eq (h0 : Fin G.H) (s0 : Fin G.S) (x : FSeq G K) :
    fullVis β h0 s0 x = preVis h0 s0 x K := by
  unfold fullVis preVis; rw [visits_eq β (unflat x) K h0 s0]

lemma preVis_take (h0 : Fin G.H) (s0 : Fin G.S) (x : FSeq G K) (t : ℕ) (k : Fin K)
    (hk : (x (slot h0 k)).1 = s0 ∧ (preVis h0 s0 x k.val).length = t) :
    preVis h0 s0 x k.val = (fullVis β h0 s0 x).take t := by
  have hp : preVis h0 s0 x k.val <+: fullVis β h0 s0 x := by
    rw [fullVis_eq β h0 s0 x]
    unfold preVis
    have := visList_prefix (fun k' : Fin K => (unflat x k' h0).1) s0 k.val (K - k.val)
    rwa [Nat.add_sub_of_le k.isLt.le] at this
  have := List.prefix_iff_eq_take.1 hp
  rw [hk.2] at this
  exact this

lemma cFb_of_lt (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (z0 : FSeq G K)
    (past : List (Fin (G.A j) × FSeq G K)) (t : ℕ) (hlen : past.length = t)
    (hi : t < (fullVis β h0 s0 (curZ z0 past)).length) (b : Fin (G.A j)) (z : FSeq G K) :
    cFb β j h0 s0 z0 past b z = visFb β j h0 s0 ((fullVis β h0 s0 (curZ z0 past)).get ⟨t, hi⟩) z := by
  subst hlen; unfold cFb; rw [dif_pos hi]

/-- **Lemma A (support invariant)**: on a history of positive weight that has not run out of
visits, the learner's feedback list is the V-learning bandit history of the current trace. -/
lemma inv_A (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) :
    ∀ (t : ℕ) (z0 : FSeq G K) (ω : Fin t → Fin (G.A j) × FSeq G K),
      (cEnv alg β j h0 s0).weight (alg j) z0 ω ≠ 0 →
      t ≤ (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).length →
      (cEnv alg β j h0 s0).fbList z0 ω t =
        ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).take t).map
          (recFb β (unflat (curZ z0 (List.ofFn ω))) j h0 s0) := by
  intro t
  induction t with
  | zero => intro z0 ω _ _; simp [AdaptiveEnv.fbList]
  | succ t ih =>
    intro z0 ω hw hle
    obtain ⟨ω', p, rfl⟩ : ∃ ω' p, ω = Fin.snoc (α := fun _ => Fin (G.A j) × FSeq G K) ω' p :=
      ⟨Fin.init ω, ω (Fin.last t), (Fin.snoc_init_self ω).symm⟩
    rw [curZ_snoc] at hle ⊢
    rw [weight_snoc] at hw
    have hw' : (cEnv alg β j h0 s0).weight (alg j) z0 ω' ≠ 0 := fun h => hw (by rw [h, zero_mul])
    have hκ : (cEnv alg β j h0 s0).kernel z0 (List.ofFn ω') p.1 p.2 ≠ 0 :=
      fun h => hw (by rw [h, mul_zero, mul_zero])
    rw [fbList_last]
    have hlen : (List.ofFn ω').length = t := List.length_ofFn
    by_cases hi : t < (fullVis β h0 s0 (curZ z0 (List.ofFn ω'))).length
    · have ih' := ih z0 ω' hw' hi.le
      set x := curZ z0 (List.ofFn ω') with hx
      set k := (fullVis β h0 s0 x).get ⟨t, hi⟩ with hk
      have hκ' : visKer alg β j h0 s0 k x p.1 p.2 ≠ 0 := by
        have e : (cEnv alg β j h0 s0).kernel z0 (List.ofFn ω') p.1 p.2 = visKer alg β j h0 s0 k x p.1 p.2 :=
          cKer_of_lt (alg := alg) (β := β) j h0 s0 z0 (List.ofFn ω') t hlen hi p.1 p.2
        rwa [e] at hκ
      have hA : Agree (slot h0 k).val x p.2 := by
        by_contra h; apply hκ'; simp only [visKer, if_neg h, zero_mul]
      have hS : (p.2 (slot h0 k)).1 = s0 := by
        by_contra h; apply hκ'; simp only [visKer, if_neg h, mul_zero, zero_mul]
      have hB : (p.2 (slot h0 k)).2 j = p.1 := by
        by_contra h; apply hκ'
        have h0' : RunState.devProb alg (runState G β (unflat p.2) k.val) j p.1 h0 s0
            (p.2 (slot h0 k)).2 = 0 := by
          unfold RunState.devProb
          exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [h])
        simp only [visKer, h0', mul_zero, zero_mul]
      have hkx : (x (slot h0 k)).1 = s0 ∧ (preVis h0 s0 x k.val).length = t :=
        (fullVis_get_iff (β := β) h0 s0 x t k).1 ⟨hi, rfl⟩
      have hpre : preVis h0 s0 p.2 k.val = preVis h0 s0 x k.val := (preVis_congr h0 s0 x p.2 k hA).symm
      have hkz : (p.2 (slot h0 k)).1 = s0 ∧ (preVis h0 s0 p.2 k.val).length = t := ⟨hS, hpre ▸ hkx.2⟩
      obtain ⟨hiz, hgz⟩ := (fullVis_get_iff (β := β) h0 s0 p.2 t k).2 hkz
      have htx : (fullVis β h0 s0 x).take t = preVis h0 s0 x k.val := (preVis_take β h0 s0 x t k hkx).symm
      have htz : (fullVis β h0 s0 p.2).take t = preVis h0 s0 x k.val := by
        rw [← hpre]; exact (preVis_take β h0 s0 p.2 t k hkz).symm
      simp only [List.get_eq_getElem] at hgz
      have htake : (fullVis β h0 s0 p.2).take (t + 1) = preVis h0 s0 x k.val ++ [k] := by
        rw [List.take_succ, htz, List.getElem?_eq_getElem hiz, hgz, Option.toList_some]
      rw [htake, ih', htx, List.map_append, List.map_singleton]
      congr 1
      · refine List.map_congr_left (fun k' hk' => ?_)
        have hlt : k'.val < k.val :=
          ((mem_visList (fun k'' : Fin K => (unflat x k'' h0).1) s0 k.val k').1 hk').1
        have hep : unflat p.2 k' = unflat x k' :=
          funext fun h => hA (finProdFinEquiv (k', h)) ((flat_rank_lt (k', h) (k, h0)).2 (Or.inl hlt))
        have hrs : runState G β (unflat p.2) k'.val = runState G β (unflat x) k'.val :=
          runState_unflat_dep β h0 k' p.2 x (fun m hm => hA m (lt_trans (show m.val < (slot h0 k').val from hm)
            ((flat_rank_lt (k', h0) (k, h0)).2 (Or.inl hlt))))
        simp only [recFb, hep, hrs]
      · have e : (cEnv alg β j h0 s0).fb z0 (List.ofFn ω') p.1 p.2 = visFb β j h0 s0 k p.2 :=
          cFb_of_lt (β := β) j h0 s0 z0 (List.ofFn ω') t hlen hi p.1 p.2
        rw [e]
        refine congrArg (fun q => [q]) (Prod.ext ?_ ?_)
        · exact hB.symm
        · rfl
    · exfalso
      have e : (cEnv alg β j h0 s0).kernel z0 (List.ofFn ω') p.1 p.2 =
          if p.2 = curZ z0 (List.ofFn ω') then 1 else 0 :=
        cKer_of_ge (alg := alg) (β := β) j h0 s0 z0 (List.ofFn ω') t hlen hi p.1 p.2
      rw [e] at hκ
      have hz : p.2 = curZ z0 (List.ofFn ω') := by
        by_contra h; exact hκ (if_neg h)
      rw [hz] at hle
      omega

/-- `hθ` of Lemma B, from Lemma A and Lemma A0. -/
lemma hθ_A (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (t : ℕ) (z0 : FSeq G K)
    (ω : Fin t → Fin (G.A j) × FSeq G K) (hw : (cEnv alg β j h0 s0).weight (alg j) z0 ω ≠ 0)
    (hi : t < (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).length) :
    (cEnv alg β j h0 s0).theta (alg j) z0 ω t =
      (runState G β (unflat (curZ z0 (List.ofFn ω)))
        ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨t, hi⟩).val).policy alg j h0 s0 := by
  have hI := inv_A alg β j h0 s0 t z0 ω hw hi.le
  unfold AdaptiveEnv.theta RunState.policy
  rw [hI]
  set c := curZ z0 (List.ofFn ω) with hc
  set k := (fullVis β h0 s0 c).get ⟨t, hi⟩ with hk
  have hkc : (c (slot h0 k)).1 = s0 ∧ (preVis h0 s0 c k.val).length = t :=
    (fullVis_get_iff (β := β) h0 s0 c t k).1 ⟨hi, rfl⟩
  rw [hist_eq β (unflat c) j h0 s0 k.val, visits_eq β (unflat c) k.val h0 s0]
  have hv : visList (fun k' : Fin K => (unflat c k' h0).1) s0 k.val = (fullVis β h0 s0 c).take t :=
    preVis_take β h0 s0 c t k hkc
  rw [hv]

/-- **Lemma B, unconditional**: the coupled environment's last draw has the training-trace law. -/
lemma law_A (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S)
    (t : ℕ) (Ψ : FSeq G K → ℝ) :
    ∑ z0, ∑ ω : Fin t → Fin (G.A j) × FSeq G K,
        (cEnv alg β j h0 s0).weight (alg j) z0 ω * Ψ (curZ z0 (List.ofFn ω)) =
      ∑ z, (∏ n, flatKer alg β n z (z n)) * Ψ z :=
  law (alg := alg) (β := β) hG halg j h0 s0
    (fun t z0 ω hw hi => hθ_A alg β j h0 s0 t z0 ω hw hi) t Ψ

end invA


/-! ## hR step 6: every earlier round's trace agrees with the final trace before its visit slot. -/
section invP
open FaaSeq Classical
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

/-- `k` is the `i`-th (0-based) visit of `(h₀, s₀)` in the flat trace `x`. -/
abbrev IsVis (h0 : Fin G.H) (s0 : Fin G.S) (x : FSeq G K) (i : ℕ) (k : Fin K) : Prop :=
  (x (slot h0 k)).1 = s0 ∧ (preVis h0 s0 x k.val).length = i

lemma isVis_lt (h0 : Fin G.H) (s0 : Fin G.S) (x : FSeq G K) (i t : ℕ) (k kt : Fin K)
    (hk : IsVis h0 s0 x i k) (hkt : IsVis h0 s0 x t kt) (hit : i < t) : k.val < kt.val := by
  by_contra h
  push_neg at h
  have hp := visList_prefix (fun k'' : Fin K => (unflat x k'' h0).1) s0 kt.val (k.val - kt.val)
  rw [Nat.add_sub_of_le h] at hp
  have hl := hp.length_le
  have e1 : (preVis h0 s0 x kt.val).length = t := hkt.2
  have e2 : (preVis h0 s0 x k.val).length = i := hk.2
  unfold preVis at e1 e2
  omega

lemma inv_P (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) :
    ∀ (t : ℕ) (z0 : FSeq G K) (ω : Fin t → Fin (G.A j) × FSeq G K),
      (cEnv alg β j h0 s0).weight (alg j) z0 ω ≠ 0 →
      t ≤ (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).length →
      ∀ i < t, ∃ k : Fin K, IsVis h0 s0 (curZ z0 (AdaptiveEnv.past ω i)) i k ∧
        IsVis h0 s0 (curZ z0 (List.ofFn ω)) i k ∧
        Agree (slot h0 k).val (curZ z0 (AdaptiveEnv.past ω i)) (curZ z0 (List.ofFn ω)) := by
  intro t
  induction t with
  | zero => intro z0 ω _ _ i hi; omega
  | succ t ih =>
    intro z0 ω hw hle i hi
    obtain ⟨ω', p, rfl⟩ : ∃ ω' p, ω = Fin.snoc (α := fun _ => Fin (G.A j) × FSeq G K) ω' p :=
      ⟨Fin.init ω, ω (Fin.last t), (Fin.snoc_init_self ω).symm⟩
    rw [curZ_snoc] at hle ⊢
    rw [past_snoc ω' p i (by omega)]
    rw [weight_snoc] at hw
    have hw' : (cEnv alg β j h0 s0).weight (alg j) z0 ω' ≠ 0 := fun h => hw (by rw [h, zero_mul])
    have hκ : (cEnv alg β j h0 s0).kernel z0 (List.ofFn ω') p.1 p.2 ≠ 0 :=
      fun h => hw (by rw [h, mul_zero, mul_zero])
    have hlen : (List.ofFn ω').length = t := List.length_ofFn
    by_cases ht : t < (fullVis β h0 s0 (curZ z0 (List.ofFn ω'))).length
    · have ih' := ih z0 ω' hw' ht.le
      set x := curZ z0 (List.ofFn ω') with hx
      set k := (fullVis β h0 s0 x).get ⟨t, ht⟩ with hk
      have hκ' : visKer alg β j h0 s0 k x p.1 p.2 ≠ 0 := by
        have e : (cEnv alg β j h0 s0).kernel z0 (List.ofFn ω') p.1 p.2 = visKer alg β j h0 s0 k x p.1 p.2 :=
          cKer_of_lt (alg := alg) (β := β) j h0 s0 z0 (List.ofFn ω') t hlen ht p.1 p.2
        rwa [e] at hκ
      have hA : Agree (slot h0 k).val x p.2 := by
        by_contra h; apply hκ'; simp only [visKer, if_neg h, zero_mul]
      have hS : (p.2 (slot h0 k)).1 = s0 := by
        by_contra h; apply hκ'; simp only [visKer, if_neg h, mul_zero, zero_mul]
      have hkx : IsVis h0 s0 x t k := (fullVis_get_iff (β := β) h0 s0 x t k).1 ⟨ht, rfl⟩
      have hkz : IsVis h0 s0 p.2 t k := ⟨hS, (preVis_congr h0 s0 x p.2 k hA) ▸ hkx.2⟩
      have htr : ∀ (i' : ℕ) (k' : Fin K), i' < t → IsVis h0 s0 x i' k' →
          IsVis h0 s0 p.2 i' k' ∧ Agree (slot h0 k').val x p.2 := by
        intro i' k' hi' hv
        have hlt := isVis_lt h0 s0 x i' t k' k hv hkx hi'
        have hsl : (slot h0 k').val < (slot h0 k).val := (flat_rank_lt (k', h0) (k, h0)).2 (Or.inl hlt)
        have hA' : Agree (slot h0 k').val x p.2 := fun m hm => hA m (lt_trans hm hsl)
        refine ⟨⟨?_, ?_⟩, hA'⟩
        · rw [hA (slot h0 k') hsl]; exact hv.1
        · rw [← preVis_congr h0 s0 x p.2 k' hA']; exact hv.2
      rcases Nat.lt_or_ge i t with hi' | hge
      · obtain ⟨k', h1, h2, h3⟩ := ih' i hi'
        obtain ⟨h4, h5⟩ := htr i k' hi' h2
        exact ⟨k', h1, h4, fun m hm => (h5 m hm).trans (h3 m hm)⟩
      · have hit : i = t := by omega
        rw [hit, past_full]
        exact ⟨k, hkx, hkz, hA⟩
    · exfalso
      have e : (cEnv alg β j h0 s0).kernel z0 (List.ofFn ω') p.1 p.2 =
          if p.2 = curZ z0 (List.ofFn ω') then 1 else 0 :=
        cKer_of_ge (alg := alg) (β := β) j h0 s0 z0 (List.ofFn ω') t hlen ht p.1 p.2
      rw [e] at hκ
      have hz : p.2 = curZ z0 (List.ofFn ω') := by
        by_contra h; exact hκ (if_neg h)
      rw [hz] at hle
      omega

end invP



/-! ## hR step 7 (C): per-round identification of the coupled bandit's strategy and losses. -/
section roundC
open FaaSeq Classical
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

/-- `devExp` written on a flat trace. -/
noncomputable def flatDev (c : FSeq G K) (j : Fin G.m) (b : Fin (G.A j)) (h0 : Fin G.H)
    (s0 : Fin G.S) (k : Fin K) : ℝ :=
  ∑ a : G.JointAct, RunState.devProb alg (runState G β (unflat c) k.val) j b h0 s0 a *
    (G.r j h0 s0 a + ∑ s', G.P h0 s0 a s' * (runState G β (unflat c) k.val).vUpNext j h0 s')

lemma round_id (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (t : ℕ) (z0 : FSeq G K) (ω : Fin t → Fin (G.A j) × FSeq G K)
    (hw : (cEnv alg β j h0 s0).weight (alg j) z0 ω ≠ 0)
    (ht : t ≤ (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).length) (i : ℕ) (hi : i < t) :
    (cEnv alg β j h0 s0).theta (alg j) z0 ω i =
        (runState G β (unflat (curZ z0 (List.ofFn ω)))
          ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨i, lt_of_lt_of_le hi ht⟩).val).policy
            alg j h0 s0 ∧
      ∀ b, (cEnv alg β j h0 s0).loss z0 (AdaptiveEnv.past ω i) b =
        ((G.H : ℝ) - flatDev alg β (curZ z0 (List.ofFn ω)) j b h0 s0
          ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨i, lt_of_lt_of_le hi ht⟩)) / G.H := by
  obtain ⟨k, hk1, hk2, hag⟩ := inv_P alg β j h0 s0 t z0 ω hw ht i hi
  obtain ⟨_, hget⟩ := (fullVis_get_iff (β := β) h0 s0 (curZ z0 (List.ofFn ω)) i k).2 hk2
  obtain ⟨hi', hgeti⟩ := (fullVis_get_iff (β := β) h0 s0 (curZ z0 (AdaptiveEnv.past ω i)) i k).2 hk1
  rw [hget]
  constructor
  · have hI := inv_A alg β j h0 s0 t z0 ω hw ht
    have hfb : (cEnv alg β j h0 s0).fbList z0 ω i =
        ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).take i).map
          (recFb β (unflat (curZ z0 (List.ofFn ω))) j h0 s0) := by
      have h1 : (cEnv alg β j h0 s0).fbList z0 ω i =
          ((cEnv alg β j h0 s0).fbList z0 ω t).take i := by
        unfold AdaptiveEnv.fbList
        rw [List.take_take]; congr 1; omega
      rw [h1, hI, ← List.map_take, List.take_take]; congr 2; omega
    unfold AdaptiveEnv.theta RunState.policy
    rw [hfb, hist_eq β (unflat (curZ z0 (List.ofFn ω))) j h0 s0 k.val,
      visits_eq β (unflat (curZ z0 (List.ofFn ω))) k.val h0 s0]
    have hv : visList (fun k' : Fin K => (unflat (curZ z0 (List.ofFn ω)) k' h0).1) s0 k.val =
        (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).take i :=
      preVis_take β h0 s0 (curZ z0 (List.ofFn ω)) i k hk2
    rw [hv]
  · intro b
    have hlen : (AdaptiveEnv.past ω i).length = i := by
      unfold AdaptiveEnv.past; rw [List.length_take, List.length_ofFn]; omega
    have hrs : runState G β (unflat (curZ z0 (AdaptiveEnv.past ω i))) k.val =
        runState G β (unflat (curZ z0 (List.ofFn ω))) k.val :=
      runState_unflat_dep β h0 k _ _ (fun m hm => (hag m hm).symm)
    show ∑ z, cKer alg β j h0 s0 z0 (AdaptiveEnv.past ω i) b z *
        cFb β j h0 s0 z0 (AdaptiveEnv.past ω i) b z = _
    simp_rw [cKer_of_lt alg β j h0 s0 z0 _ i hlen hi' b, cFb_of_lt β j h0 s0 z0 _ i hlen hi' b]
    rw [hgeti, visKer_loss alg β hG halg j h0 s0 k (curZ z0 (AdaptiveEnv.past ω i)) b]
    unfold flatDev
    rw [hrs]

lemma round_regret (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (j : Fin G.m) (h0 : Fin G.H)
    (s0 : Fin G.S) (t : ℕ) (z0 : FSeq G K) (ω : Fin t → Fin (G.A j) × FSeq G K)
    (hw : (cEnv alg β j h0 s0).weight (alg j) z0 ω ≠ 0)
    (ht : t ≤ (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).length) (i : ℕ) (hi : i < t)
    (b : Fin (G.A j)) :
    (∑ b', (cEnv alg β j h0 s0).theta (alg j) z0 ω i b' *
        (cEnv alg β j h0 s0).loss z0 (AdaptiveEnv.past ω i) b') -
      (cEnv alg β j h0 s0).loss z0 (AdaptiveEnv.past ω i) b =
    (flatDev alg β (curZ z0 (List.ofFn ω)) j b h0 s0
        ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨i, lt_of_lt_of_le hi ht⟩) -
      ∑ b', (runState G β (unflat (curZ z0 (List.ofFn ω)))
          ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨i, lt_of_lt_of_le hi ht⟩).val).policy
            alg j h0 s0 b' *
        flatDev alg β (curZ z0 (List.ofFn ω)) j b' h0 s0
          ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨i, lt_of_lt_of_le hi ht⟩)) / G.H := by
  obtain ⟨hθ, hl⟩ := round_id alg β hG halg j h0 s0 t z0 ω hw ht i hi
  rw [hθ]
  simp only [hl]
  have hs := policy_sum alg (runState G β (unflat (curZ z0 (List.ofFn ω)))
      ((fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨i, lt_of_lt_of_le hi ht⟩).val) halg j h0 s0
  have hH : (G.H : ℝ) ≠ 0 := by have := hG.H_pos; positivity
  have e0 : ∀ (p D : Fin (G.A j) → ℝ), ∑ b', p b' = 1 →
      ∑ b', p b' * (((G.H : ℝ) - D b') / G.H) = ((G.H : ℝ) - ∑ b', p b' * D b') / G.H := by
    intro p D hp
    have : ∑ b', p b' * ((G.H : ℝ) - D b') = (G.H : ℝ) - ∑ b', p b' * D b' := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]
    rw [← this, Finset.sum_div]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [e0 _ _ hs]
  field_simp
  ring

/-- Visits before episode `k` are a prefix of the full visit list. -/
lemma visits_get (z : FSeq G K) (h0 : Fin G.H) (s0 : Fin G.S) (k : Fin K) (i : ℕ)
    (hi : i < ((runState G β (unflat z) k.val).visits h0 s0).length) :
    ∃ hi2 : i < (fullVis β h0 s0 z).length,
      ((runState G β (unflat z) k.val).visits h0 s0).get ⟨i, hi⟩ =
        (fullVis β h0 s0 z).get ⟨i, hi2⟩ := by
  have hp : (runState G β (unflat z) k.val).visits h0 s0 <+: fullVis β h0 s0 z := by
    rw [fullVis_eq β h0 s0 z, visits_eq β (unflat z) k.val h0 s0]
    unfold preVis
    have := visList_prefix (fun k' : Fin K => (unflat z k' h0).1) s0 k.val (K - k.val)
    rwa [Nat.add_sub_of_le k.isLt.le] at this
  refine ⟨lt_of_lt_of_le hi hp.length_le, ?_⟩
  simp only [List.get_eq_getElem]
  exact hp.getElem hi

end roundC


/-! ## hR step 8 (D): regret event bound via Assumption 1 on the coupled environment. -/
section layerR
open FaaSeq Classical
variable {G : Game} (alg : ∀ j, BanditRule (G.A j)) {K : ℕ} (β : Fin G.m → ℕ → ℝ)

lemma visits_prefix_full (z : FSeq G K) (h0 : Fin G.H) (s0 : Fin G.S) (k : Fin K) :
    (runState G β (unflat z) k.val).visits h0 s0 <+: fullVis β h0 s0 z := by
  rw [fullVis_eq β h0 s0 z, visits_eq β (unflat z) k.val h0 s0]
  unfold preVis
  have := visList_prefix (fun k' : Fin K => (unflat z k' h0).1) s0 k.val (K - k.val)
  rwa [Nat.add_sub_of_le k.isLt.le] at this

lemma reg_point (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (ξ : ℕ → ℕ → ℝ → ℝ) (ι : ℝ)
    (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (t : ℕ) (z0 : FSeq G K)
    (ω : Fin t → Fin (G.A j) × FSeq G K)
    (hw : (cEnv alg β j h0 s0).weight (alg j) z0 ω ≠ 0) (k0 : Fin K)
    (hL : ((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).length = t)
    (b : Fin (G.A j))
    (hlt : (G.H : ℝ) * ξ (G.A j) t ι <
      ∑ q : Fin ((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).length,
        lrW G.H ((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).length
            (q.val + 1) *
          (devExp alg β (unflat (curZ z0 (List.ofFn ω))) j b h0 s0
              (((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).get q) -
            jExpUp alg β (unflat (curZ z0 (List.ofFn ω))) j h0 s0
              (((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).get q))) :
    ξ (G.A j) t ι < (cEnv alg β j h0 s0).weightedRegret (alg j) G.H z0 ω := by
  have hH : (0 : ℝ) < G.H := by have := hG.H_pos; exact_mod_cast this
  have hp := visits_prefix_full β (curZ z0 (List.ofFn ω)) h0 s0 k0
  have ht : t ≤ (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).length :=
    le_trans (le_of_eq hL.symm) hp.length_le
  have key : ∑ q : Fin ((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).length,
        lrW G.H ((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).length
            (q.val + 1) *
          (devExp alg β (unflat (curZ z0 (List.ofFn ω))) j b h0 s0
              (((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).get q) -
            jExpUp alg β (unflat (curZ z0 (List.ofFn ω))) j h0 s0
              (((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).get q)) =
      (G.H : ℝ) * ∑ i : Fin t, lrW G.H t (i.val + 1) *
        ((∑ b', (cEnv alg β j h0 s0).theta (alg j) z0 ω i.val b' *
            (cEnv alg β j h0 s0).loss z0 (AdaptiveEnv.past ω i.val) b') -
          (cEnv alg β j h0 s0).loss z0 (AdaptiveEnv.past ω i.val) b) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (finCongr hL) _ _ (fun q => ?_)
    have hq : q.val < t := lt_of_lt_of_eq q.isLt hL
    have hcv : ((finCongr hL) q).val = q.val := rfl
    rw [hcv, round_regret alg β hG halg j h0 s0 t z0 ω hw ht q.val hq b]
    have hgq : ((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).get q =
        (fullVis β h0 s0 (curZ z0 (List.ofFn ω))).get ⟨q.val, lt_of_lt_of_le hq ht⟩ := by
      simp only [List.get_eq_getElem]
      exact hp.getElem q.isLt
    rw [← hgq, ← devExp_avg alg β (unflat (curZ z0 (List.ofFn ω))) j h0 s0]
    have hlr : lrW G.H ((runState G β (unflat (curZ z0 (List.ofFn ω))) k0.val).visits h0 s0).length
        (q.val + 1) = lrW G.H t (q.val + 1) := congrArg (fun n => lrW G.H n (q.val + 1)) hL
    rw [hlr]
    unfold flatDev devExp
    field_simp
  have hwr : ∑ i : Fin t, lrW G.H t (i.val + 1) *
        ((∑ b', (cEnv alg β j h0 s0).theta (alg j) z0 ω i.val b' *
            (cEnv alg β j h0 s0).loss z0 (AdaptiveEnv.past ω i.val) b') -
          (cEnv alg β j h0 s0).loss z0 (AdaptiveEnv.past ω i.val) b) ≤
      (cEnv alg β j h0 s0).weightedRegret (alg j) G.H z0 ω := by
    unfold AdaptiveEnv.weightedRegret
    refine le_ciSup_of_le ?_ b ?_
    · exact (Set.finite_range _).bddAbove
    · exact le_refl _
  rw [key] at hlt
  have := lt_of_mul_lt_mul_left hlt hH.le
  linarith

lemma reg_event (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (hβ0 : ∀ j t, 0 ≤ β j t)
    (ξ : ℕ → ℕ → ℝ → ℝ) (hA : ∀ j, Assumption1 G.H (alg j) ξ) (ι : ℝ) (hι : 0 < ι)
    (j : Fin G.m) (h0 : Fin G.H) (s0 : Fin G.S) (t : ℕ) :
    trainProb G alg β K (fun τ => ∃ k0 : Fin K, ∃ b : Fin (G.A j),
      ((runState G β τ k0.val).visits h0 s0).length = t ∧
      (G.H : ℝ) * ξ (G.A j) t ι <
        ∑ q : Fin ((runState G β τ k0.val).visits h0 s0).length,
          lrW G.H ((runState G β τ k0.val).visits h0 s0).length (q.val + 1) *
            (devExp alg β τ j b h0 s0 (((runState G β τ k0.val).visits h0 s0).get q) -
              jExpUp alg β τ j h0 s0 (((runState G β τ k0.val).visits h0 s0).get q))) ≤
      Real.exp (-ι) := by
  have hfb : ∀ (k : Fin K) (z : FSeq G K), visFb β j h0 s0 k z ∈ Set.Icc (0 : ℝ) 1 := by
    intro k z
    unfold visFb
    have hr := hG.r_mem j h0 s0 (z (slot h0 k)).2
    have hH : (0 : ℝ) < G.H := by have := hG.H_pos; exact_mod_cast this
    have hh0 : (h0.val : ℝ) + 1 ≤ G.H := by exact_mod_cast h0.isLt
    have hv : 0 ≤ (runState G β (unflat z) k.val).vUpAfter j (unflat z k) h0 ∧
        (runState G β (unflat z) k.val).vUpAfter j (unflat z k) h0 ≤ (G.H : ℝ) - h0.val - 1 := by
      unfold RunState.vUpAfter
      split_ifs with hh
      · obtain ⟨-, i2, i3, -⟩ := vrange hG β hβ0 (unflat z) k.val j ⟨h0.val + 1, hh⟩
          (unflat z k ⟨h0.val + 1, hh⟩).1
        refine ⟨i2, ?_⟩
        simp only [Nat.cast_add, Nat.cast_one] at i3
        linarith
      · have : (G.H : ℝ) ≤ h0.val + 1 := by exact_mod_cast (not_lt.1 hh)
        constructor <;> linarith
    have hh0 : (h0.val : ℝ) + 1 ≤ G.H := by exact_mod_cast h0.isLt
    obtain ⟨hr0, hr1⟩ := hr
    constructor
    · apply div_nonneg _ hH.le; linarith
    · rw [div_le_one hH]; linarith
  have hv := cEnv_valid alg β hG halg j h0 s0 hfb
  rw [trainProb_flat alg β]
  have hlaw := law_A (K := K) alg β hG halg j h0 s0 t (fun z : FSeq G K => if (∃ k0 : Fin K, ∃ b : Fin (G.A j),
      ((runState G β (unflat z) k0.val).visits h0 s0).length = t ∧
      (G.H : ℝ) * ξ (G.A j) t ι <
        ∑ q : Fin ((runState G β (unflat z) k0.val).visits h0 s0).length,
          lrW G.H ((runState G β (unflat z) k0.val).visits h0 s0).length (q.val + 1) *
            (devExp alg β (unflat z) j b h0 s0 (((runState G β (unflat z) k0.val).visits h0 s0).get q) -
              jExpUp alg β (unflat z) j h0 s0 (((runState G β (unflat z) k0.val).visits h0 s0).get q)))
      then (1 : ℝ) else 0)
  beta_reduce at hlaw
  refine le_trans (le_of_eq (Eq.trans ?_ hlaw.symm)) ?_
  · apply Finset.sum_congr rfl
    intro x _
    congr
  have hlog : Real.log (1 / Real.exp (-ι)) = ι := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hA1 := hA j (FSeq G K) (cEnv alg β j h0 s0) hv t (Real.exp (-ι)) (Real.exp_pos _)
    (by
      have := Real.exp_lt_exp.2 (show -ι < 0 by linarith)
      simpa using this)
  rw [hlog] at hA1
  refine le_trans ?_ hA1
  unfold AdaptiveEnv.regretExceedProb
  apply Finset.sum_le_sum
  intro z0 _
  apply Finset.sum_le_sum
  intro ω _
  have hwn : 0 ≤ (cEnv alg β j h0 s0).weight (alg j) z0 ω := by
    unfold AdaptiveEnv.weight
    exact mul_nonneg (hv.1 z0) (Finset.prod_nonneg fun i _ => mul_nonneg
      (by unfold AdaptiveEnv.theta; exact (halg j).1 _ _) (hv.2.2.1 _ _ _ _))
  by_cases hw : (cEnv alg β j h0 s0).weight (alg j) z0 ω = 0
  · simp [hw]
  split_ifs with h1 h2
  · exact le_refl _
  · exfalso; apply h2
    obtain ⟨k0, b, hL, hlt⟩ := h1
    exact reg_point alg β hG halg ξ ι j h0 s0 t z0 ω hw k0 hL b hlt
  · simpa using hwn
  · exact le_refl _

lemma hR_bound (hG : G.Standing) (halg : ∀ j, (alg j).Valid) (hβ0 : ∀ j t, 0 ≤ β j t)
    (ξ : ℕ → ℕ → ℝ → ℝ) (hA : ∀ j, Assumption1 G.H (alg j) ξ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hK : 1 ≤ K) (hA2 : 2 ≤ G.Amax) :
    trainProb G alg β K (fun τ => ¬ RegOK alg β ξ (iota G K δ) τ) ≤ δ / 2 := by
  have hAmax1 : 1 ≤ G.Amax := by omega
  have hι := iota_pos hG hK hδ0 hδ1 hAmax1
  let B : Fin G.m × Fin G.H × Fin G.S × Fin K → (Fin K → Episode G) → Prop :=
    fun i τ => ∃ k0 : Fin K, ∃ b : Fin (G.A i.1),
      ((runState G β τ k0.val).visits i.2.1 i.2.2.1).length = i.2.2.2.val + 1 ∧
      (G.H : ℝ) * ξ (G.A i.1) (i.2.2.2.val + 1) (iota G K δ) <
        ∑ q : Fin ((runState G β τ k0.val).visits i.2.1 i.2.2.1).length,
          lrW G.H ((runState G β τ k0.val).visits i.2.1 i.2.2.1).length (q.val + 1) *
            (devExp alg β τ i.1 b i.2.1 i.2.2.1 (((runState G β τ k0.val).visits i.2.1 i.2.2.1).get q) -
              jExpUp alg β τ i.1 i.2.1 i.2.2.1 (((runState G β τ k0.val).visits i.2.1 i.2.2.1).get q))
  have hB : ∀ i, trainProb G alg β K (B i) ≤ Real.exp (-iota G K δ) := by
    rintro ⟨j, h0, s0, i⟩
    exact reg_event alg β hG halg hβ0 ξ hA (iota G K δ) hι j h0 s0 (i.val + 1)
  have hcover : ∀ τ, ¬ RegOK alg β ξ (iota G K δ) τ →
      ∃ i ∈ (Finset.univ : Finset (Fin G.m × Fin G.H × Fin G.S × Fin K)), B i τ := by
    intro τ hn
    unfold RegOK at hn
    push_neg at hn
    obtain ⟨k, j, h0, s0, b, hlt⟩ := hn
    have hLK : ((runState G β τ k.val).visits h0 s0).length < K := by
      rw [visits_eq]
      exact lt_of_le_of_lt (visList_length_le _ s0 k.val) k.isLt
    have hL0 : ((runState G β τ k.val).visits h0 s0).length ≠ 0 := by
      intro h0L
      have hx := xi_nonneg G.H (alg j) (halg j) ξ (hA j) (hG.A_pos j)
        ((runState G β τ k.val).visits h0 s0).length (iota G K δ) hι
      have hH : (0 : ℝ) ≤ G.H := by positivity
      have hs : ∑ q : Fin ((runState G β τ k.val).visits h0 s0).length,
          lrW G.H ((runState G β τ k.val).visits h0 s0).length (q.val + 1) *
            (devExp alg β τ j b h0 s0 (((runState G β τ k.val).visits h0 s0).get q) -
              jExpUp alg β τ j h0 s0 (((runState G β τ k.val).visits h0 s0).get q)) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        exact absurd q.isLt (by omega)
      rw [hs] at hlt
      nlinarith [mul_nonneg hH hx]
    refine ⟨(j, h0, s0, ⟨((runState G β τ k.val).visits h0 s0).length - 1, by omega⟩),
      Finset.mem_univ _, k, b, ?_, ?_⟩
    · show ((runState G β τ k.val).visits h0 s0).length =
        ((runState G β τ k.val).visits h0 s0).length - 1 + 1
      omega
    · have e : ((runState G β τ k.val).visits h0 s0).length - 1 + 1 =
          ((runState G β τ k.val).visits h0 s0).length := by omega
      show (G.H : ℝ) * ξ (G.A j) (((runState G β τ k.val).visits h0 s0).length - 1 + 1) (iota G K δ) < _
      rw [e]
      exact hlt
  have hm : (1 : ℝ) ≤ G.m := by exact_mod_cast hG.m_pos
  have hH : (1 : ℝ) ≤ G.H := by exact_mod_cast hG.H_pos
  have hS : (1 : ℝ) ≤ G.S := by exact_mod_cast hG.S_pos
  have hA : (2 : ℝ) ≤ G.Amax := by exact_mod_cast hA2
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hN : 0 < (G.m : ℝ) * G.H * G.S * G.Amax * K / δ := by
    apply div_pos _ hδ0
    positivity
  have hei : Real.exp (iota G K δ) = (G.m : ℝ) * G.H * G.S * G.Amax * K / δ := by
    unfold iota; exact Real.exp_log hN
  calc trainProb G alg β K (fun τ => ¬ RegOK alg β ξ (iota G K δ) τ)
      ≤ trainProb G alg β K (fun τ => ∃ i ∈ (Finset.univ :
          Finset (Fin G.m × Fin G.H × Fin G.S × Fin K)), B i τ) :=
        trainProb_mono alg β hG halg _ _ hcover
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin G.m × Fin G.H × Fin G.S × Fin K)),
          trainProb G alg β K (B i) := trainProb_union alg β hG halg _ B
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin G.m × Fin G.H × Fin G.S × Fin K)),
          Real.exp (-iota G K δ) := Finset.sum_le_sum (fun i _ => hB i)
    _ ≤ δ / 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.exp_neg, hei]
        simp only [Fintype.card_prod, Fintype.card_fin]
        push_cast
        have e : (G.m : ℝ) * (G.H * (G.S * K)) * (G.m * G.H * G.S * G.Amax * K / δ)⁻¹ =
            δ / G.Amax := by
          field_simp
        rw [e]
        apply div_le_div_of_nonneg_left hδ0.le (by norm_num) hA

lemma goodClaim2 : GoodProbClaim 2 := by
  intro G hG alg halg ξ hA β hβ0 δ hδ0 hδ1 K hK hA2 hβ
  exact goodProb_of_bounds alg β hG halg ξ hA δ hδ0 hδ1 hK hβ
    (hR_bound alg β hG halg hβ0 ξ hA δ hδ0 hδ1 hK hA2)
    (hM_bound alg β hG halg hβ0 δ hδ0 hδ1 hK hA2)

end layerR

end VLearning.CCE.Aux

open VLearning.CCE in
theorem solution :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, ∃ C : ℝ, ∀ (G : Game), G.Standing →
      ∀ (alg : ∀ j, BanditRule (G.A j)), (∀ j, (alg j).Valid) →
      ∀ (ξ : ℕ → ℕ → ℝ → ℝ) (Ξ : ℕ → ℝ → ℝ → ℝ),
        (∀ j, Assumption1 G.H (alg j) ξ) →
        (∀ B B' t x, 0 < x → B ≤ B' → ξ B t x ≤ ξ B' t x) →
        (∀ B (t : ℕ) x, 0 < x → ∑ t' ∈ Finset.Icc 1 t, ξ B t' x ≤ Ξ B t x) →
        (∀ B x, 0 < x → ConcaveOn ℝ (Set.Ici 0) (fun t => Ξ B t x)) →
      ∀ (β : Fin G.m → ℕ → ℝ), (∀ j t, 0 ≤ β j t) →
      ∀ (δ : ℝ), 0 < δ → δ < 1 → ∀ K : ℕ, 1 ≤ K →
        (∀ j t, 1 ≤ t → t ≤ K →
          c₀ * bonusScale G ξ (G.A j) (iota G K δ) t ≤
              ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ∧
            ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ≤
              c₁ * bonusScale G ξ (G.A j) (iota G K δ) t) →
        1 - δ ≤ trainProb G alg β K (fun τ => ∀ j : Fin G.m,
          brValTop G alg β τ j - outValTop G alg β τ j ≤
            C * ((G.H : ℝ) ^ 2 * G.S / K * Ξ G.Amax ((K : ℝ) / G.S) (iota G K δ) +
              Real.sqrt ((G.H : ℝ) ^ 5 * G.S * iota G K δ / K))) := by
  exact VLearning.CCE.Aux.solution_of_good 2 (by norm_num) VLearning.CCE.Aux.goodClaim2
