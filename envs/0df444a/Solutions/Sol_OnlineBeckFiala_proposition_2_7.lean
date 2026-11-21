-- Prove2me | solution 1 for OnlineBeckFiala.proposition_2_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:50:32.422259+00:00
-- url     : https://prove2.me/submissions/106e3159-bc1d-4ae6-8ca9-cbe8fd674441

import Mathlib
import Definitions.Def_OnlineBeckFiala_walkLaw
import Theorems.Thm_OnlineBeckFiala_lemma_2_2
import Definitions.Def_OnlineBeckFiala_OnlineSigner

section
/-!
# P27 plan (Proposition 2.7)
P27a: explicit measurable coupling ff a b (copy of the L26 construction) with real-valued facts.
P27b: inverse-CDF sampler on a finite weight vector (measurable, law lemma, support lemma).
P27c: one-step map dd(x,u,v) of the three walks; law of each coordinate = stepMeasure;
      sum = +-1 on the good event.
P27d: Omega = N -> (state x uniform) with infinitePi; process X, locality, measurability,
      independence of X_t and U_t, marginal law X_t j = densityLaw (induction via lemma_2_2).
P27e: OnlineSigner, union bound, final theorem chk_proposition_2_7.
-/

open MeasureTheory

namespace OnlineBeckFiala

namespace Dev.P27.C

/-- the 12 admissible patterns: single nonzero entries and triples with sum ±1 -/
def pats : Fin 12 → (Fin 3 → SignType) :=
  ![![1,0,0],
   ![-1,0,0],
   ![0,1,0],
   ![0,-1,0],
   ![0,0,1],
   ![0,0,-1],
   ![1,1,-1],
   ![1,-1,1],
   ![1,-1,-1],
   ![-1,1,1],
   ![-1,1,-1],
   ![-1,-1,1]]

/-- counts (out of 12) of the coupling for the vertex type `(a,b,c)`, index `9a+3b+c` -/
def tbl : List (List ℕ) :=
  [[4,0,4,0,4,0,0,0,0,0,0,0],
   [4,0,4,0,0,4,0,0,0,0,0,0],
   [2,0,2,0,4,2,2,0,0,0,0,0],
   [4,0,0,4,4,0,0,0,0,0,0,0],
   [4,0,0,4,0,4,0,0,0,0,0,0],
   [2,0,0,2,2,4,0,2,0,0,0,0],
   [2,0,4,2,2,0,0,2,0,0,0,0],
   [2,0,2,4,0,2,2,0,0,0,0,0],
   [0,0,0,4,4,0,4,0,0,0,0,0],
   [0,4,4,0,4,0,0,0,0,0,0,0],
   [0,4,4,0,0,4,0,0,0,0,0,0],
   [0,2,2,0,2,4,0,0,0,2,0,0],
   [0,4,0,4,4,0,0,0,0,0,0,0],
   [0,4,0,4,0,4,0,0,0,0,0,0],
   [0,2,0,2,2,4,0,0,0,0,0,2],
   [0,2,2,4,2,0,0,0,0,2,0,0],
   [0,2,2,4,0,2,0,0,0,0,2,0],
   [0,0,0,4,0,4,0,0,0,4,0,0],
   [4,2,2,0,2,0,0,0,0,2,0,0],
   [2,4,2,0,0,2,2,0,0,0,0,0],
   [0,4,0,0,4,0,4,0,0,0,0,0],
   [2,4,0,2,2,0,0,2,0,0,0,0],
   [2,4,0,2,0,2,0,0,2,0,0,0],
   [0,4,0,0,0,4,0,4,0,0,0,0],
   [0,4,4,0,0,0,0,4,0,0,0,0],
   [0,4,0,4,0,0,4,0,0,0,0,0],
   [0,2,0,2,0,2,2,2,0,2,0,0]]

def cnt (a b c : Fin 3) (k : Fin 12) : ℕ := ((tbl.getD (9 * a.val + 3 * b.val + c.val) []).getD k.val 0)

def ea : Fin 3 → ℕ := ![4, 0, 4]
def eb : Fin 3 → ℕ := ![0, 4, 4]

theorem F2 : ∀ a b c : Fin 3, ∑ k, cnt a b c k = 12 := by decide +kernel

theorem F3 : ∀ a b c j : Fin 3,
    ∑ k, cnt a b c k * (if pats k j = 1 then 1 else 0) = ea (![a, b, c] j) := by decide +kernel

theorem F4 : ∀ a b c j : Fin 3,
    ∑ k, cnt a b c k * (if pats k j = -1 then 1 else 0) = eb (![a, b, c] j) := by decide +kernel

theorem F5 : ∀ a b c : Fin 3, ∀ k, cnt a b c k ≠ 0 →
    (∑ j, ((pats k j : SignType) : ℤ)) = 1 ∨ (∑ j, ((pats k j : SignType) : ℤ)) = -1 := by
  decide +kernel


noncomputable def w (a b : Fin 3 → ℝ) (j : Fin 3) : Fin 3 → ℝ :=
  ![1 - 3 * b j, 1 - 3 * a j, 3 * a j + 3 * b j - 1]

noncomputable def W (a b : Fin 3 → ℝ) (t : Fin 3 → Fin 3) : ℝ := ∏ j, w a b j (t j)

noncomputable def gg (a b : Fin 3 → ℝ) (t : Fin 3 → Fin 3) (k : Fin 12) : ℝ :=
  W a b t * (cnt (t 0) (t 1) (t 2) k : ℝ) / 12

theorem sum_w (a b : Fin 3 → ℝ) (j : Fin 3) : ∑ s, w a b j s = 1 := by
  simp [w, Fin.sum_univ_three]; ring

theorem w_nonneg (a b : Fin 3 → ℝ)
    (ha1 : ∀ j, a j ≤ 1 / 3) (hb0 : ∀ j, 0 ≤ b j) (ha0 : ∀ j, 0 ≤ a j) (hb1 : ∀ j, b j ≤ 1 / 3)
    (hab : ∀ j, 1 / 3 ≤ a j + b j) (j s : Fin 3) : 0 ≤ w a b j s := by
  have := ha1 j; have := hb1 j; have := hab j
  fin_cases s <;> simp [w] <;> linarith

theorem W_nonneg (a b : Fin 3 → ℝ)
    (ha1 : ∀ j, a j ≤ 1 / 3) (hb0 : ∀ j, 0 ≤ b j) (ha0 : ∀ j, 0 ≤ a j) (hb1 : ∀ j, b j ≤ 1 / 3)
    (hab : ∀ j, 1 / 3 ≤ a j + b j) (t : Fin 3 → Fin 3) : 0 ≤ W a b t :=
  Finset.prod_nonneg fun j _ => w_nonneg a b ha1 hb0 ha0 hb1 hab j (t j)

theorem marg (a b : Fin 3 → ℝ) (j0 : Fin 3) (h : Fin 3 → ℝ) :
    ∑ t : Fin 3 → Fin 3, W a b t * h (t j0) = ∑ s, w a b j0 s * h s := by
  have key := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin 3)))
    (fun i s => w a b i s * if i = j0 then h s else 1)
  rw [Fintype.piFinset_univ] at key
  have e1 : ∀ t : Fin 3 → Fin 3, (∏ i, (w a b i (t i) * if i = j0 then h (t i) else 1)) =
      W a b t * h (t j0) := by
    intro t
    rw [Finset.prod_mul_distrib]
    simp [W]
  simp only [e1] at key
  rw [← key]
  fin_cases j0 <;> simp [sum_w]

theorem sumW (a b : Fin 3 → ℝ) : ∑ t : Fin 3 → Fin 3, W a b t = 1 := by
  have := marg a b 0 (fun _ => 1)
  simpa [sum_w] using this

noncomputable def ff (a b : Fin 3 → ℝ) (δ : Fin 3 → SignType) : ℝ :=
  ∑ t : Fin 3 → Fin 3, ∑ k, gg a b t k * (if pats k = δ then 1 else 0)

theorem gg_nonneg (a b : Fin 3 → ℝ)
    (ha1 : ∀ j, a j ≤ 1 / 3) (hb0 : ∀ j, 0 ≤ b j) (ha0 : ∀ j, 0 ≤ a j) (hb1 : ∀ j, b j ≤ 1 / 3)
    (hab : ∀ j, 1 / 3 ≤ a j + b j) (t : Fin 3 → Fin 3) (k : Fin 12) : 0 ≤ gg a b t k := by
  unfold gg
  have := W_nonneg a b ha1 hb0 ha0 hb1 hab t
  positivity

open Classical in
theorem sumS (a b : Fin 3 → ℝ) (S : Set (Fin 3 → SignType)) :
    ∑ δ, S.indicator (ff a b) δ =
      ∑ t : Fin 3 → Fin 3, ∑ k, gg a b t k * (if pats k ∈ S then 1 else 0) := by
  have h1 : ∀ δ, S.indicator (ff a b) δ = ∑ t : Fin 3 → Fin 3, ∑ k,
      gg a b t k * (if pats k = δ then (if pats k ∈ S then 1 else 0) else 0) := by
    intro δ
    unfold ff
    simp only [Set.indicator]
    by_cases hδ : δ ∈ S
    · rw [if_pos hδ]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases e : pats k = δ <;> simp [e, hδ]
    · rw [if_neg hδ]
      symm
      refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun k _ => ?_
      by_cases e : pats k = δ <;> simp [e, hδ]
  rw [Finset.sum_congr rfl fun δ _ => h1 δ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp

theorem sum_cnt (a b : Fin 3 → ℝ) (t : Fin 3 → Fin 3) :
    ∑ k, gg a b t k = W a b t := by
  unfold gg
  have := F2 (t 0) (t 1) (t 2)
  have h : (∑ k, (cnt (t 0) (t 1) (t 2) k : ℝ)) = 12 := by exact_mod_cast this
  rw [← Finset.sum_div, ← Finset.mul_sum, h]; ring


open Classical in
theorem margP (a b : Fin 3 → ℝ) (P : (Fin 3 → SignType) → Prop) (e : Fin 3 → ℕ) (j : Fin 3)
    (hP : ∀ x y z : Fin 3, ∑ k, cnt x y z k * (if P (pats k) then 1 else 0) = e (![x, y, z] j)) :
    ∑ t : Fin 3 → Fin 3, ∑ k, gg a b t k * (if pats k ∈ {δ | P δ} then 1 else 0) =
      ∑ s, w a b j s * ((e s : ℝ) / 12) := by
  rw [← marg a b j (fun s => (e s : ℝ) / 12)]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h := hP (t 0) (t 1) (t 2)
  have h' : (∑ k, (cnt (t 0) (t 1) (t 2) k : ℝ) * (if P (pats k) then 1 else 0)) = (e (t j) : ℝ) := by
    have : ![t 0, t 1, t 2] j = t j := by fin_cases j <;> rfl
    rw [this] at h
    exact_mod_cast h
  simp only [Set.mem_setOf_eq]
  unfold gg
  calc ∑ k, W a b t * (cnt (t 0) (t 1) (t 2) k : ℝ) / 12 * (if P (pats k) then 1 else 0)
      = W a b t / 12 * ∑ k, (cnt (t 0) (t 1) (t 2) k : ℝ) * (if P (pats k) then 1 else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ = _ := by rw [h']; ring

end Dev.P27.C

namespace Dev.P27.C
variable {n : ℕ}

theorem cube_meas (L : ℝ) : MeasurableSet (cube (n := n) L) := by
  have : cube (n := n) L = ⋂ i, (fun x : Fin n → ℝ => x i) ⁻¹' Set.Ioo (-L) L := by
    ext x; simp [cube]
  rw [this]
  exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ioo


theorem step_meas (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (hμm : Measurable μ) (v : Fin n → ℝ) :
    Measurable (stepMeasure μ L v) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  unfold stepMeasure
  have hind : Measurable fun x : Fin n → ℝ => s.indicator (1 : (Fin n → ℝ) → ENNReal) x :=
    measurable_one.indicator hs
  have hind1 : Measurable fun x : Fin n → ℝ => s.indicator (1 : (Fin n → ℝ) → ENNReal) (x + v) :=
    hind.comp (measurable_add_const v)
  have hind2 : Measurable fun x : Fin n → ℝ => s.indicator (1 : (Fin n → ℝ) → ENNReal) (x - v) :=
    hind.comp (measurable_sub_const v)
  have m1 : Measurable fun x => μ (x + v) := hμm.comp (measurable_add_const v)
  have m2 : Measurable fun x => μ (x - v) := hμm.comp (measurable_sub_const v)
  have hpP : Measurable fun x => pPlus μ v x := by
    unfold pPlus; fun_prop
  have hpM : Measurable fun x => pMinus μ v x := by
    unfold pMinus; fun_prop
  have hpZ : Measurable fun x => pZero μ v x := by
    unfold pZero; fun_prop
  simp only [apply_ite (fun m : Measure (Fin n → ℝ) => m s)]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  refine Measurable.ite (p := fun x => x ∈ cube L) (cube_meas L) ?_ hind
  exact ((hpP.ennreal_ofReal.mul hind1).add (hpM.ennreal_ofReal.mul hind2)).add
    (hpZ.ennreal_ofReal.mul hind)

theorem ff_valid (a b : Fin 3 → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j ≤ 1 / 3) (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1 / 3)
    (hab : ∀ j, 1 / 3 ≤ a j + b j) :
    (∀ δ, 0 ≤ ff a b δ) ∧ ∑ δ, ff a b δ = 1 ∧
    (∀ j, ∑ δ, (if δ j = 1 then ff a b δ else 0) = a j) ∧
    (∀ j, ∑ δ, (if δ j = -1 then ff a b δ else 0) = b j) ∧
    (∀ δ, 0 < ff a b δ → (∑ j, (δ j : ℤ)) = 1 ∨ (∑ j, (δ j : ℤ)) = -1) := by
  classical
  have hgg := gg_nonneg a b ha1 hb0 ha0 hb1 hab
  have hff : ∀ δ, 0 ≤ ff a b δ := fun δ =>
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun k _ => by
      have := hgg t k; split_ifs <;> simp [this]
  have hsum : ∑ δ, ff a b δ = 1 := by
    have := sumS a b Set.univ
    simp only [Set.indicator_univ, Set.mem_univ, if_true, mul_one] at this
    rw [this]
    simp only [sum_cnt]
    exact sumW a b
  refine ⟨hff, hsum, fun j => ?_, fun j => ?_, ?_⟩
  · have h1 := sumS a b {δ | δ j = 1}
    have h2 := margP a b (fun δ => δ j = 1) ea j (fun x y z => by
      have := F3 x y z j; simpa using this)
    have : ∑ δ, (if δ j = 1 then ff a b δ else 0) = ∑ δ, ({δ | δ j = 1} : Set _).indicator (ff a b) δ := by
      refine Finset.sum_congr rfl fun δ _ => ?_
      by_cases hδ : δ j = 1 <;> simp [Set.indicator, hδ]
    rw [this, h1, h2]
    fin_cases j <;> simp [w, ea, Fin.sum_univ_three] <;> ring
  · have h1 := sumS a b {δ | δ j = -1}
    have h2 := margP a b (fun δ => δ j = -1) eb j (fun x y z => by
      have := F4 x y z j; simpa using this)
    have : ∑ δ, (if δ j = -1 then ff a b δ else 0) = ∑ δ, ({δ | δ j = -1} : Set _).indicator (ff a b) δ := by
      refine Finset.sum_congr rfl fun δ _ => ?_
      by_cases hδ : δ j = -1 <;> simp [Set.indicator, hδ]
    rw [this, h1, h2]
    fin_cases j <;> simp [w, eb, Fin.sum_univ_three] <;> ring
  · intro δ hpos
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    have e : pats k = δ := by
      by_contra hne; simp [hne] at hk
    have hc : cnt (t 0) (t 1) (t 2) k ≠ 0 := by
      intro h0; simp [gg, h0] at hk
    subst e
    exact F5 _ _ _ k hc

end Dev.P27.C

end OnlineBeckFiala
end

section
open MeasureTheory

namespace OnlineBeckFiala.Dev.P27

variable {m : ℕ}

/-- exclusive cumulative sum -/
noncomputable def cum (w : Fin m → ℝ) (k : ℕ) : ℝ := ∑ i : Fin m, if i.val < k then w i else 0

/-- inverse-CDF index -/
noncomputable def idx (w : Fin m → ℝ) (u : ℝ) : ℕ :=
  ((Finset.range m).filter fun k => cum w (k + 1) ≤ u).card

theorem cum_zero (w : Fin m → ℝ) : cum w 0 = 0 := by simp [cum]

theorem cum_mono (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) {k k' : ℕ} (h : k ≤ k') :
    cum w k ≤ cum w k' :=
  Finset.sum_le_sum fun i _ => by
    by_cases h1 : (i : ℕ) < k <;> by_cases h2 : (i : ℕ) < k' <;> simp [h1, h2, hw i] <;> omega

theorem cum_nonneg (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (k : ℕ) : 0 ≤ cum w k := by
  rw [← cum_zero w]; exact cum_mono w hw (Nat.zero_le k)

theorem cum_m (w : Fin m → ℝ) : cum w m = ∑ i, w i := by
  simp [cum]

theorem cum_succ (w : Fin m → ℝ) (k : ℕ) (hk : k < m) :
    cum w (k + 1) = cum w k + w ⟨k, hk⟩ := by
  unfold cum
  have e : w ⟨k, hk⟩ = ∑ i : Fin m, if i = ⟨k, hk⟩ then w i else 0 := by simp
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < k
  · have : i ≠ ⟨k, hk⟩ := fun h => by simp [h] at h1
    simp [h1, this]; omega
  · by_cases h2 : i = ⟨k, hk⟩
    · subst h2; simp
    · have : ¬ (i : ℕ) < k + 1 := by
        intro h; apply h2; ext; simp; omega
      simp [h1, h2, this]

theorem idx_eq (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (u : ℝ) (k : ℕ) (hk : k < m)
    (h1 : cum w k ≤ u) (h2 : u < cum w (k + 1)) : idx w u = k := by
  unfold idx
  have : (Finset.range m).filter (fun k' => cum w (k' + 1) ≤ u) = Finset.range k := by
    ext k'
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h⟩
      by_contra hc
      have := cum_mono w hw (show k + 1 ≤ k' + 1 by omega)
      linarith
    · intro h
      refine ⟨by omega, le_trans (cum_mono w hw (show k' + 1 ≤ k by omega)) h1⟩
  rw [this]; simp

theorem exists_k (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) : ∃ k, ∃ hk : k < m, cum w k ≤ u ∧ u < cum w (k + 1) := by
  classical
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hs
    · exact h
  have hex : ∃ k, u < cum w (k + 1) := ⟨m - 1, by
    rw [Nat.sub_add_cancel hm, cum_m, hs]; exact hu1⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · have := Nat.find_min' hex (show u < cum w (m - 1 + 1) from by
      rw [Nat.sub_add_cancel hm, cum_m, hs]; exact hu1)
    omega
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, cum_zero]; exact hu0
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [Nat.sub_add_cancel h] at this
      exact not_lt.mp this

theorem meas_idx {α : Type*} [MeasurableSpace α] (w : α → Fin m → ℝ) (u : α → ℝ)
    (hw : ∀ i, Measurable fun z => w z i) (hu : Measurable u) :
    Measurable fun z => idx (w z) (u z) := by
  have hc : ∀ k, Measurable fun z => cum (w z) k := fun k =>
    Finset.measurable_sum _ fun i _ => by
      by_cases h : (i : ℕ) < k
      · simpa [h] using hw i
      · simp [h]
  have : (fun z => idx (w z) (u z)) = fun z =>
      ∑ k ∈ Finset.range m, if cum (w z) (k + 1) ≤ u z then 1 else 0 := by
    ext z; unfold idx; rw [Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurableSet_le (hc (k + 1)) hu) measurable_const measurable_const

/-- the law of the index under the uniform law on `[0,1)` -/
theorem idx_law (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)).map (idx w) =
      ∑ i : Fin m, ENNReal.ofReal (w i) • Measure.dirac (i : ℕ) := by
  rw [Measure.ext_iff_singleton]
  intro k
  have hmeas : Measurable (idx w) := by
    simpa using meas_idx (fun _ : ℝ => w) id (fun i => measurable_const) measurable_id
  rw [Measure.map_apply hmeas (measurableSet_singleton k), Measure.restrict_apply' measurableSet_Ico]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply' _
    (measurableSet_singleton k), smul_eq_mul]
  by_cases hk : k < m
  · have hset : (idx w ⁻¹' {k}) ∩ Set.Ico 0 1 = Set.Ico (cum w k) (cum w (k + 1)) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico]
      constructor
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨k0, hk0, a, b⟩ := exists_k w hw hs u h2 h3
        have := idx_eq w hw u k0 hk0 a b
        rw [h1] at this; subst this; exact ⟨a, b⟩
      · rintro ⟨a, b⟩
        refine ⟨idx_eq w hw u k hk a b, le_trans (cum_nonneg w hw k) a, ?_⟩
        calc u < cum w (k + 1) := b
          _ ≤ cum w m := cum_mono w hw hk
          _ = 1 := by rw [cum_m, hs]
    rw [hset, Real.volume_Ico, cum_succ w k hk]
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
    · simp
    · intro i _ hi
      have : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
      simp [this]
    · simp
  · have hset : (idx w ⁻¹' {k}) ∩ Set.Ico 0 1 = ∅ := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, h3⟩
      obtain ⟨k0, hk0, a, b⟩ := exists_k w hw hs u h2 h3
      have := idx_eq w hw u k0 hk0 a b
      omega
    rw [hset]; simp only [measure_empty]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    have : (i : ℕ) ≠ k := fun h => hk (h ▸ i.2)
    simp [this]

end OnlineBeckFiala.Dev.P27
end

section
open MeasureTheory

namespace OnlineBeckFiala.Dev.P27

/-- the uniform law on `[0,1)` -/
noncomputable abbrev unif : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1)

instance : IsProbabilityMeasure unif :=
  ⟨by simp [Measure.restrict_apply_univ]⟩

/-- hypotheses on the density -/
structure Hy {n : ℕ} (L : ℝ) (μ : (Fin n → ℝ) → ℝ) : Prop where
  m : Measurable μ
  pos : ∀ x ∈ cube L, 0 < μ x
  zero : ∀ x ∉ cube L, μ x = 0

section
variable {n : ℕ} {L : ℝ} {μ : (Fin n → ℝ) → ℝ}

theorem Hy.nonneg (hy : Hy L μ) (x : Fin n → ℝ) : 0 ≤ μ x := by
  by_cases h : x ∈ cube L
  · exact (hy.pos x h).le
  · rw [hy.zero x h]

theorem pPlus_nonneg (hy : Hy L μ) (v x : Fin n → ℝ) : 0 ≤ pPlus μ v x := by
  unfold pPlus
  have := hy.nonneg (x + v); have := hy.nonneg x
  have : 0 ≤ μ (x + v) / μ x := by positivity
  positivity

theorem pMinus_nonneg (hy : Hy L μ) (v x : Fin n → ℝ) : 0 ≤ pMinus μ v x := by
  unfold pMinus
  have := hy.nonneg (x - v); have := hy.nonneg x
  have : 0 ≤ μ (x - v) / μ x := by positivity
  positivity

theorem pPlus_le (v x : Fin n → ℝ) : pPlus μ v x ≤ 1 / 3 := by
  unfold pPlus
  have := min_le_left (1 : ℝ) (μ (x + v) / μ x)
  linarith

theorem pMinus_le (v x : Fin n → ℝ) : pMinus μ v x ≤ 1 / 3 := by
  unfold pMinus
  have := min_le_left (1 : ℝ) (μ (x - v) / μ x)
  linarith

theorem meas_pPlus (hy : Hy L μ) (v : Fin n → ℝ) : Measurable (pPlus μ v) := by
  have m1 : Measurable fun x => μ (x + v) := hy.m.comp (measurable_add_const v)
  have := hy.m
  unfold pPlus; fun_prop

theorem meas_pMinus (hy : Hy L μ) (v : Fin n → ℝ) : Measurable (pMinus μ v) := by
  have m1 : Measurable fun x => μ (x - v) := hy.m.comp (measurable_sub_const v)
  have := hy.m
  unfold pMinus; fun_prop

theorem cube_meas' (L : ℝ) : MeasurableSet (cube (n := n) L) := C.cube_meas L

open Classical in
/-- the `+1` probability of a walk at `y` (zero off the cube) -/
noncomputable def pa (μ : (Fin n → ℝ) → ℝ) (L : ℝ) (v y : Fin n → ℝ) : ℝ :=
  if y ∈ cube L then pPlus μ v y else 0

open Classical in
noncomputable def pb (μ : (Fin n → ℝ) → ℝ) (L : ℝ) (v y : Fin n → ℝ) : ℝ :=
  if y ∈ cube L then pMinus μ v y else 0

theorem pa_nonneg (hy : Hy L μ) (v y : Fin n → ℝ) : 0 ≤ pa μ L v y := by
  unfold pa; split_ifs
  · exact pPlus_nonneg hy v y
  · exact le_rfl

theorem pb_nonneg (hy : Hy L μ) (v y : Fin n → ℝ) : 0 ≤ pb μ L v y := by
  unfold pb; split_ifs
  · exact pMinus_nonneg hy v y
  · exact le_rfl

theorem pa_le (v y : Fin n → ℝ) : pa μ L v y ≤ 1 / 3 := by
  unfold pa; split_ifs
  · exact pPlus_le v y
  · norm_num

theorem pb_le (v y : Fin n → ℝ) : pb μ L v y ≤ 1 / 3 := by
  unfold pb; split_ifs
  · exact pMinus_le v y
  · norm_num

theorem meas_pa (hy : Hy L μ) (v : Fin n → ℝ) : Measurable (pa μ L v) := by
  unfold pa
  exact Measurable.ite (cube_meas' L) (meas_pPlus hy v) measurable_const

theorem meas_pb (hy : Hy L μ) (v : Fin n → ℝ) : Measurable (pb μ L v) := by
  unfold pb
  exact Measurable.ite (cube_meas' L) (meas_pMinus hy v) measurable_const

/-- all three walkers balanced -/
def good (μ : (Fin n → ℝ) → ℝ) (L : ℝ) (v : Fin n → ℝ) (x : Fin 3 → Fin n → ℝ) : Prop :=
  ∀ j, IsBalanced L μ v (x j)

theorem good_meas (hy : Hy L μ) (v : Fin n → ℝ) : MeasurableSet {x | good μ L v x} := by
  have : {x | good μ L v x} = ⋂ j : Fin 3, (fun x : Fin 3 → Fin n → ℝ => x j) ⁻¹'
      ({y | y ∈ cube L} ∩ {y | 1 / 3 ≤ pPlus μ v y + pMinus μ v y}) := by
    ext x; simp [good, IsBalanced]
  rw [this]
  refine MeasurableSet.iInter fun j => measurable_pi_apply j ?_
  exact (cube_meas' L).inter (measurableSet_le measurable_const
    ((meas_pPlus hy v).add (meas_pMinus hy v)))

theorem pa_eq {v y : Fin n → ℝ} (hb : IsBalanced L μ v y) : pa μ L v y = pPlus μ v y := by
  unfold pa; rw [if_pos hb.1]

theorem pb_eq {v y : Fin n → ℝ} (hb : IsBalanced L μ v y) : pb μ L v y = pMinus μ v y := by
  unfold pb; rw [if_pos hb.1]

open Classical in
theorem idx_law_set {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (A : Set ℕ) :
    unif (idx w ⁻¹' A) = ∑ i : Fin m, if (i : ℕ) ∈ A then ENNReal.ofReal (w i) else 0 := by
  have hmeas : Measurable (idx w) := by
    simpa using meas_idx (fun _ : ℝ => w) id (fun i => measurable_const) measurable_id
  rw [← Measure.map_apply hmeas (MeasurableSet.of_discrete), idx_law w hw hs]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete), smul_eq_mul, Set.indicator, Pi.one_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) ∈ A <;> simp [h]

theorem law3 (f : ℝ → ℝ) (hf : Measurable f) (h3 : ∀ u, f u = 1 ∨ f u = -1 ∨ f u = 0)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (h1 : unif {u | f u = 1} = ENNReal.ofReal a) (h2 : unif {u | f u = -1} = ENNReal.ofReal b)
    (y v : Fin n → ℝ) (B : Set (Fin n → ℝ)) :
    unif {u | y + f u • v ∈ B} = ENNReal.ofReal a * B.indicator 1 (y + v) +
      ENNReal.ofReal b * B.indicator 1 (y - v) + ENNReal.ofReal (1 - a - b) * B.indicator 1 y := by
  classical
  have m1 : MeasurableSet {u | f u = 1} := hf (measurableSet_singleton _)
  have m2 : MeasurableSet {u | f u = -1} := hf (measurableSet_singleton _)
  have m0 : MeasurableSet {u | f u = 0} := hf (measurableSet_singleton _)
  have d12 : Disjoint {u | f u = 1} {u | f u = -1} := by
    rw [Set.disjoint_left]; intro u h h'; simp only [Set.mem_setOf_eq] at h h'; rw [h] at h'; norm_num at h'
  have d120 : Disjoint ({u | f u = 1} ∪ {u | f u = -1}) {u | f u = 0} := by
    rw [Set.disjoint_left]; intro u h h'; simp only [Set.mem_setOf_eq, Set.mem_union] at h h'
    rcases h with h | h <;> rw [h] at h' <;> norm_num at h'
  have hz : unif {u | f u = 0} = ENNReal.ofReal (1 - a - b) := by
    have htot : unif ({u | f u = 1} ∪ {u | f u = -1} ∪ {u | f u = 0}) = 1 := by
      have : ({u | f u = 1} ∪ {u | f u = -1} ∪ {u | f u = 0}) = Set.univ := by
        ext u
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        rcases h3 u with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      rw [this]; exact measure_univ
    rw [measure_union d120 m0, measure_union d12 m2, h1, h2, ← ENNReal.ofReal_add ha hb] at htot
    have : ENNReal.ofReal (a + b) + ENNReal.ofReal (1 - a - b) = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; simp
    exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 (htot.trans this.symm)
  have e1' : y + (1 : ℝ) • v = y + v := by simp
  have e2' : y + (-1 : ℝ) • v = y - v := by simp [sub_eq_add_neg]
  have e0' : y + (0 : ℝ) • v = y := by simp
  have e2'' : y + -v = y - v := (sub_eq_add_neg y v).symm
  have hset : {u | y + f u • v ∈ B} = ((if y + v ∈ B then {u | f u = 1} else ∅) ∪
      (if y - v ∈ B then {u | f u = -1} else ∅)) ∪ (if y ∈ B then {u | f u = 0} else ∅) := by
    ext u
    by_cases b1 : y + v ∈ B <;> by_cases b2 : y - v ∈ B <;> by_cases b3 : y ∈ B <;>
      rcases h3 u with h | h | h <;> (simp [h, e1', e2', e0', e2'', b1, b2, b3] <;> norm_num)
  have mi : ∀ (p : Prop) (S : Set ℝ), MeasurableSet S → MeasurableSet (if p then S else ∅) := by
    intro p S hS; split_ifs <;> simp [hS]
  have s1 : ∀ p : Prop, (if p then {u | f u = 1} else ∅) ⊆ {u | f u = 1} := by
    intro p; split_ifs <;> simp
  have s2 : ∀ p : Prop, (if p then {u | f u = -1} else ∅) ⊆ {u | f u = -1} := by
    intro p; split_ifs <;> simp
  have s0 : ∀ p : Prop, (if p then {u | f u = 0} else ∅) ⊆ {u | f u = 0} := by
    intro p; split_ifs <;> simp
  have e1 : unif (if y + v ∈ B then {u | f u = 1} else ∅) = ENNReal.ofReal a * B.indicator 1 (y + v) := by
    by_cases b : y + v ∈ B <;> simp [b, h1, Set.indicator]
  have e2 : unif (if y - v ∈ B then {u | f u = -1} else ∅) = ENNReal.ofReal b * B.indicator 1 (y - v) := by
    by_cases b : y - v ∈ B <;> simp [b, h2, Set.indicator]
  have e0 : unif (if y ∈ B then {u | f u = 0} else ∅) = ENNReal.ofReal (1 - a - b) * B.indicator 1 y := by
    by_cases b : y ∈ B <;> simp [b, hz, Set.indicator]
  rw [hset, measure_union (d120.mono (Set.union_subset_union (s1 _) (s2 _)) (s0 _)) (mi _ _ m0),
    measure_union (d12.mono (s1 _) (s2 _)) (mi _ _ m2), e1, e2, e0]

end

end OnlineBeckFiala.Dev.P27
end

section
open MeasureTheory

namespace OnlineBeckFiala.Dev.P27

abbrev Pat := Fin 3 → SignType

noncomputable def enc : Pat ≃ Fin (Fintype.card Pat) := Fintype.equivFin _

noncomputable def wE (a b : Fin 3 → ℝ) : Fin (Fintype.card Pat) → ℝ :=
  fun i => C.ff a b (enc.symm i)

noncomputable def patR (j : Fin 3) (k : ℕ) : ℝ :=
  if h : k < Fintype.card Pat then (((enc.symm ⟨k, h⟩ j : SignType) : ℤ) : ℝ) else 0

theorem patR_fin (j : Fin 3) (i : Fin (Fintype.card Pat)) :
    patR j i = (((enc.symm i j : SignType) : ℤ) : ℝ) := by
  simp only [patR, dif_pos i.2, Fin.eta]

theorem cast_eq_iff (t s : SignType) : (((t : ℤ) : ℝ) = ((s : ℤ) : ℝ)) ↔ t = s := by
  rcases t <;> rcases s <;> simp <;> norm_num

theorem patR_val (j : Fin 3) (k : ℕ) : patR j k = 1 ∨ patR j k = -1 ∨ patR j k = 0 := by
  unfold patR
  split_ifs
  · rcases (enc.symm ⟨k, ‹_›⟩ j : SignType) <;> simp
  · simp

open Classical in
noncomputable def dd {n : ℕ} (μ : (Fin n → ℝ) → ℝ) (L : ℝ) (v : Fin n → ℝ)
    (x : Fin 3 → Fin n → ℝ) (u : ℝ) : Fin 3 → ℝ :=
  if good μ L v x then
    fun j => patR j (idx (wE (fun i => pa μ L v (x i)) (fun i => pb μ L v (x i))) u)
  else fun j => if u < pa μ L v (x j) then 1 else
    if u < pa μ L v (x j) + pb μ L v (x j) then -1 else 0

section
variable {n : ℕ} {L : ℝ} {μ : (Fin n → ℝ) → ℝ}

theorem dd_val (v : Fin n → ℝ) (x : Fin 3 → Fin n → ℝ) (u : ℝ) (j : Fin 3) :
    dd μ L v x u j = 1 ∨ dd μ L v x u j = -1 ∨ dd μ L v x u j = 0 := by
  unfold dd
  split_ifs
  · exact patR_val _ _
  · dsimp only
    split_ifs <;> simp

theorem meas_ff {α : Type*} [MeasurableSpace α] (a b : α → Fin 3 → ℝ)
    (ha : ∀ j, Measurable fun z => a z j) (hb : ∀ j, Measurable fun z => b z j) (δ : Pat) :
    Measurable fun z => C.ff (a z) (b z) δ := by
  have hw : ∀ j s, Measurable fun z => C.w (a z) (b z) j s := by
    intro j s
    have := ha j; have := hb j
    fin_cases s <;> simp [C.w] <;> fun_prop
  unfold C.ff
  refine Finset.measurable_sum _ fun t _ => Finset.measurable_sum _ fun k _ => ?_
  unfold C.gg C.W
  have hprod : Measurable fun z => ∏ j, C.w (a z) (b z) j (t j) :=
    Finset.measurable_prod _ fun j _ => hw j (t j)
  exact ((hprod.mul_const _).div_const _).mul measurable_const

theorem meas_ddA (hy : Hy L μ) (v : Fin n → ℝ) (j : Fin 3) :
    Measurable fun q : (Fin 3 → Fin n → ℝ) × ℝ =>
      patR j (idx (wE (fun i => pa μ L v (q.1 i)) (fun i => pb μ L v (q.1 i))) q.2) := by
  have ha : ∀ j, Measurable fun q : (Fin 3 → Fin n → ℝ) × ℝ => pa μ L v (q.1 j) := fun j =>
    (meas_pa hy v).comp ((measurable_pi_apply j).comp measurable_fst)
  have hb : ∀ j, Measurable fun q : (Fin 3 → Fin n → ℝ) × ℝ => pb μ L v (q.1 j) := fun j =>
    (meas_pb hy v).comp ((measurable_pi_apply j).comp measurable_fst)
  have hw : ∀ i : Fin (Fintype.card Pat), Measurable fun q : (Fin 3 → Fin n → ℝ) × ℝ =>
      wE (fun i => pa μ L v (q.1 i)) (fun i => pb μ L v (q.1 i)) i := by
    intro i
    have h := meas_ff (fun q : (Fin 3 → Fin n → ℝ) × ℝ => fun i => pa μ L v (q.1 i))
      (fun q : (Fin 3 → Fin n → ℝ) × ℝ => fun i => pb μ L v (q.1 i)) ha hb (enc.symm i)
    unfold wE
    exact h
  have hi := meas_idx (fun q : (Fin 3 → Fin n → ℝ) × ℝ =>
    wE (fun i => pa μ L v (q.1 i)) (fun i => pb μ L v (q.1 i))) Prod.snd hw measurable_snd
  exact (measurable_from_nat (f := patR j)).comp hi

theorem dd_meas (hy : Hy L μ) (v : Fin n → ℝ) :
    Measurable fun q : (Fin 3 → Fin n → ℝ) × ℝ => dd μ L v q.1 q.2 := by
  classical
  rw [measurable_pi_iff]
  intro j
  have hg : MeasurableSet {q : (Fin 3 → Fin n → ℝ) × ℝ | good μ L v q.1} :=
    measurable_fst (good_meas hy v)
  have ha : ∀ j, Measurable fun q : (Fin 3 → Fin n → ℝ) × ℝ => pa μ L v (q.1 j) := fun j =>
    (meas_pa hy v).comp ((measurable_pi_apply j).comp measurable_fst)
  have hb : ∀ j, Measurable fun q : (Fin 3 → Fin n → ℝ) × ℝ => pb μ L v (q.1 j) := fun j =>
    (meas_pb hy v).comp ((measurable_pi_apply j).comp measurable_fst)
  unfold dd
  simp only [apply_ite (fun f : Fin 3 → ℝ => f j)]
  refine Measurable.ite hg (meas_ddA hy v j) ?_
  exact Measurable.ite (measurableSet_lt measurable_snd (ha j)) measurable_const
      (Measurable.ite (measurableSet_lt measurable_snd ((ha j).add (hb j))) measurable_const
        measurable_const)

theorem bad_law1 (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    unif {u | (if u < a then (1 : ℝ) else if u < a + b then -1 else 0) = 1} = ENNReal.ofReal a := by
  have h1 : {u : ℝ | (if u < a then (1 : ℝ) else if u < a + b then -1 else 0) = 1} = Set.Iio a := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Iio]
    by_cases h : u < a <;> by_cases h2 : u < a + b <;> norm_num [h, h2]
  have h2 : Set.Iio a ∩ Set.Ico 0 1 = Set.Ico 0 a := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, by linarith⟩
  rw [Measure.restrict_apply' measurableSet_Ico, h1, h2, Real.volume_Ico, sub_zero]

theorem bad_law2 (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a + b ≤ 1) :
    unif {u | (if u < a then (1 : ℝ) else if u < a + b then -1 else 0) = -1} = ENNReal.ofReal b := by
  have h1 : {u : ℝ | (if u < a then (1 : ℝ) else if u < a + b then -1 else 0) = -1} =
      Set.Ico a (a + b) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Ico]
    by_cases h : u < a <;> by_cases h2 : u < a + b <;> norm_num [h, h2, not_lt.mp]
  rw [Measure.restrict_apply' measurableSet_Ico, h1,
    Set.inter_eq_left.mpr (Set.Ico_subset_Ico ha0 hab), Real.volume_Ico, add_sub_cancel_left]

theorem good_valid (hy : Hy L μ) (v : Fin n → ℝ) (x : Fin 3 → Fin n → ℝ) (hg : good μ L v x) :
    (∀ j, 0 ≤ pa μ L v (x j)) ∧ (∀ j, pa μ L v (x j) ≤ 1 / 3) ∧ (∀ j, 0 ≤ pb μ L v (x j)) ∧
    (∀ j, pb μ L v (x j) ≤ 1 / 3) ∧ (∀ j, 1 / 3 ≤ pa μ L v (x j) + pb μ L v (x j)) :=
  ⟨fun j => pa_nonneg hy v _, fun j => pa_le v _, fun j => pb_nonneg hy v _, fun j => pb_le v _,
    fun j => by rw [pa_eq (hg j), pb_eq (hg j)]; exact (hg j).2⟩

theorem good_law (hy : Hy L μ) (v : Fin n → ℝ) (x : Fin 3 → Fin n → ℝ) (hg : good μ L v x)
    (j : Fin 3) (s : SignType) :
    unif {u | dd μ L v x u j = ((s : ℤ) : ℝ)} = ENNReal.ofReal
      (∑ δ : Pat, if δ j = s then C.ff (fun i => pa μ L v (x i)) (fun i => pb μ L v (x i)) δ else 0) := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := good_valid hy v x hg
  obtain ⟨hff0, hsum, -, -, -⟩ := C.ff_valid _ _ h1 h2 h3 h4 h5
  have hw : ∀ i, 0 ≤ wE (fun i => pa μ L v (x i)) (fun i => pb μ L v (x i)) i := fun i => hff0 _
  have hs : ∑ i, wE (fun i => pa μ L v (x i)) (fun i => pb μ L v (x i)) i = 1 :=
    (Equiv.sum_comp enc.symm (C.ff (fun i => pa μ L v (x i)) (fun i => pb μ L v (x i)))).trans hsum
  have hset : {u | dd μ L v x u j = ((s : ℤ) : ℝ)} = idx (wE (fun i => pa μ L v (x i))
      (fun i => pb μ L v (x i))) ⁻¹' {k | patR j k = ((s : ℤ) : ℝ)} := by
    ext u; simp [dd, hg]
  rw [hset, idx_law_set _ hw hs,
    ENNReal.ofReal_sum_of_nonneg (fun δ _ => by split_ifs; exact hff0 δ; exact le_rfl),
    ← Equiv.sum_comp enc.symm (fun δ => ENNReal.ofReal
      (if δ j = s then C.ff (fun i => pa μ L v (x i)) (fun i => pb μ L v (x i)) δ else 0))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Set.mem_ofPred_eq, patR_fin, cast_eq_iff, wE]
  split_ifs <;> simp

theorem dd_law1 (hy : Hy L μ) (v : Fin n → ℝ) (x : Fin 3 → Fin n → ℝ) (j : Fin 3) :
    unif {u | dd μ L v x u j = 1} = ENNReal.ofReal (pa μ L v (x j)) := by
  classical
  by_cases hg : good μ L v x
  · obtain ⟨h1, h2, h3, h4, h5⟩ := good_valid hy v x hg
    obtain ⟨-, -, hA, -, -⟩ := C.ff_valid _ _ h1 h2 h3 h4 h5
    have := good_law hy v x hg j 1
    simp only [SignType.coe_one, Int.cast_one] at this
    rw [this, hA j]
  · have h : ∀ u, dd μ L v x u j = (if u < pa μ L v (x j) then (1 : ℝ) else
        if u < pa μ L v (x j) + pb μ L v (x j) then -1 else 0) := by
      intro u; simp [dd, hg]
    simp only [h]
    exact bad_law1 _ _ (pa_nonneg hy v _) (by linarith [pa_le (L := L) (μ := μ) v (x j)])

theorem dd_law2 (hy : Hy L μ) (v : Fin n → ℝ) (x : Fin 3 → Fin n → ℝ) (j : Fin 3) :
    unif {u | dd μ L v x u j = -1} = ENNReal.ofReal (pb μ L v (x j)) := by
  classical
  by_cases hg : good μ L v x
  · obtain ⟨h1, h2, h3, h4, h5⟩ := good_valid hy v x hg
    obtain ⟨-, -, -, hB, -⟩ := C.ff_valid _ _ h1 h2 h3 h4 h5
    have := good_law hy v x hg j (-1)
    simp only [SignType.coe_neg, SignType.coe_one, Int.cast_neg, Int.cast_one] at this
    rw [this, hB j]
  · have h : ∀ u, dd μ L v x u j = (if u < pa μ L v (x j) then (1 : ℝ) else
        if u < pa μ L v (x j) + pb μ L v (x j) then -1 else 0) := by
      intro u; simp [dd, hg]
    simp only [h]
    exact bad_law2 _ _ (pa_nonneg hy v _) (pb_nonneg hy v _)
      (by linarith [pa_le (L := L) (μ := μ) v (x j), pb_le (L := L) (μ := μ) v (x j)])

theorem step_law (hy : Hy L μ) (v : Fin n → ℝ) (x : Fin 3 → Fin n → ℝ) (j : Fin 3)
    (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    unif {u | x j + dd μ L v x u j • v ∈ B} = stepMeasure μ L v (x j) B := by
  have hm : Measurable fun u => dd μ L v x u j :=
    (measurable_pi_apply j).comp ((dd_meas hy v).comp (measurable_const.prodMk measurable_id))
  rw [law3 (fun u => dd μ L v x u j) hm (dd_val v x · j) (pa μ L v (x j)) (pb μ L v (x j))
    (pa_nonneg hy v _) (pb_nonneg hy v _)
    (by linarith [pa_le (L := L) (μ := μ) v (x j), pb_le (L := L) (μ := μ) v (x j)])
    (dd_law1 hy v x j) (dd_law2 hy v x j) (x j) v B]
  unfold stepMeasure
  by_cases hc : x j ∈ cube L
  · simp only [if_pos hc, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hB,
      smul_eq_mul, pa, pb, pZero]
  · simp only [if_neg hc, Measure.dirac_apply' _ hB, pa, pb]
    simp [hc]

theorem dd_sum (hy : Hy L μ) (v : Fin n → ℝ) (x : Fin 3 → Fin n → ℝ) (hg : good μ L v x)
    (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    ∑ j, dd μ L v x u j = 1 ∨ ∑ j, dd μ L v x u j = -1 := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := good_valid hy v x hg
  obtain ⟨hff0, hsum, -, -, hsup⟩ := C.ff_valid _ _ h1 h2 h3 h4 h5
  set w := wE (fun i => pa μ L v (x i)) (fun i => pb μ L v (x i)) with hwdef
  have hw : ∀ i, 0 ≤ w i := fun i => hff0 _
  have hs : ∑ i, w i = 1 :=
    (Equiv.sum_comp enc.symm (C.ff (fun i => pa μ L v (x i)) (fun i => pb μ L v (x i)))).trans hsum
  obtain ⟨k, hk, a, b⟩ := exists_k w hw hs u hu.1 hu.2
  have hidx := idx_eq w hw u k hk a b
  have hpos : 0 < w ⟨k, hk⟩ := by
    have := cum_succ w k hk
    linarith
  have hdd : ∀ j, dd μ L v x u j = (((enc.symm ⟨k, hk⟩ j : SignType) : ℤ) : ℝ) := by
    intro j
    unfold dd
    rw [if_pos hg]
    show patR j (idx w u) = _
    rw [hidx]
    unfold patR
    rw [dif_pos hk]
  have := hsup _ hpos
  simp only [hdd]
  have hc : ∑ j, (((enc.symm ⟨k, hk⟩ j : SignType) : ℤ) : ℝ) =
      ((∑ j, ((enc.symm ⟨k, hk⟩ j : SignType) : ℤ) : ℤ) : ℝ) := (Int.cast_sum _ _).symm
  rw [hc]
  rcases this with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

end

end OnlineBeckFiala.Dev.P27
end

section
open MeasureTheory ProbabilityTheory

namespace OnlineBeckFiala.Dev.P27

section
variable {n : ℕ} {L : ℝ} {μ : (Fin n → ℝ) → ℝ}

/-- one coordinate of the randomness: three initial samples and one uniform -/
abbrev St (n : ℕ) := (Fin 3 → Fin n → ℝ) × ℝ

noncomputable def nu (μ : (Fin n → ℝ) → ℝ) : Measure (St n) :=
  (Measure.pi fun _ : Fin 3 => densityLaw μ).prod unif

noncomputable def Pm (μ : (Fin n → ℝ) → ℝ) : Measure (ℕ → St n) :=
  Measure.infinitePi fun _ => nu μ

theorem densityLaw_prob (hy : Hy L μ) (hμint : ∫ x, μ x = 1) :
    IsProbabilityMeasure (densityLaw μ) := by
  have hi : Integrable μ := by
    by_contra h
    rw [integral_undef h] at hμint; norm_num at hμint
  refine ⟨?_⟩
  unfold densityLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hy.nonneg), hμint]
  simp

/-- the three walks -/
noncomputable def Xs (μ : (Fin n → ℝ) → ℝ) (L : ℝ) (vs : ℕ → Fin n → ℝ) :
    ℕ → (ℕ → St n) → Fin 3 → Fin n → ℝ
  | 0, ω => (ω 0).1
  | t + 1, ω => fun j => Xs μ L vs t ω j + dd μ L (vs t) (Xs μ L vs t ω) (ω (t + 1)).2 j • vs t

theorem Xs_meas (hy : Hy L μ) (vs : ℕ → Fin n → ℝ) (t : ℕ) : Measurable (Xs μ L vs t) := by
  induction t with
  | zero => exact measurable_fst.comp (measurable_pi_apply 0)
  | succ t ih =>
    rw [measurable_pi_iff]
    intro j
    have hU : Measurable fun ω : ℕ → St n => (ω (t + 1)).2 :=
      measurable_snd.comp (measurable_pi_apply (t + 1))
    have hd := (measurable_pi_apply j).comp ((dd_meas hy (vs t)).comp (ih.prodMk hU))
    exact ((measurable_pi_apply j).comp ih).add (hd.smul_const (vs t))

theorem Xs_congr_a (vs vs' : ℕ → Fin n → ℝ) (t : ℕ) (h : ∀ s < t, vs s = vs' s)
    (ω : ℕ → St n) : Xs μ L vs t ω = Xs μ L vs' t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 := ih (fun s hs => h s (by omega))
    have h2 := h t (by omega)
    simp only [Xs, h1, h2]

theorem Xs_congr_ω (vs : ℕ → Fin n → ℝ) (t : ℕ) (ω ω' : ℕ → St n) (h : ∀ i ≤ t, ω i = ω' i) :
    Xs μ L vs t ω = Xs μ L vs t ω' := by
  induction t with
  | zero => simp only [Xs, h 0 le_rfl]
  | succ t ih =>
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h (t + 1) le_rfl
    simp only [Xs, h1, h2]

section
variable [IsProbabilityMeasure (densityLaw μ)]

instance : IsProbabilityMeasure (nu μ) := by unfold nu; infer_instance

instance : IsProbabilityMeasure (Pm μ) := by unfold Pm; infer_instance

theorem indep_XU (hy : Hy L μ) (vs : ℕ → Fin n → ℝ) (t : ℕ) :
    IndepFun (Xs μ L vs t) (fun ω : ℕ → St n => (ω (t + 1)).2) (Pm μ) := by
  have hind : iIndepFun (fun i (ω : ℕ → St n) => ω i) (Pm μ) :=
    iIndepFun_infinitePi (P := fun _ => nu μ) (X := fun _ (s : St n) => s) (fun i => measurable_id)
  have h := hind.indepFun_finset (Finset.range (t + 1)) {t + 1} (by simp)
    (fun i => measurable_pi_apply i)
  let ext : (↥(Finset.range (t + 1)) → St n) → (ℕ → St n) := fun r i =>
    if hi : i ∈ Finset.range (t + 1) then r ⟨i, hi⟩ else default
  have hext : Measurable ext := by
    rw [measurable_pi_iff]
    intro i
    by_cases hi : i ∈ Finset.range (t + 1)
    · simp only [ext, dif_pos hi]; exact measurable_pi_apply _
    · simp only [ext, dif_neg hi]; exact measurable_const
  have e1 : Xs μ L vs t = (Xs μ L vs t ∘ ext) ∘ (fun ω (i : ↥(Finset.range (t + 1))) => ω i) := by
    funext ω
    apply Xs_congr_ω
    intro i hi
    have : i ∈ Finset.range (t + 1) := Finset.mem_range.2 (by omega)
    show ω i = ext (fun (i : ↥(Finset.range (t + 1))) => ω i) i
    simp only [ext, dif_pos this]
  have e2 : (fun ω : ℕ → St n => (ω (t + 1)).2) =
      (fun r : (↥({t + 1} : Finset ℕ)) → St n => (r ⟨t + 1, by simp⟩).2) ∘
        (fun ω (i : ↥({t + 1} : Finset ℕ)) => ω i) := rfl
  rw [e1, e2]
  exact h.comp ((Xs_meas hy vs t).comp hext)
    (measurable_snd.comp (measurable_pi_apply _))

theorem map_U (t : ℕ) : (Pm μ).map (fun ω : ℕ → St n => (ω (t + 1)).2) = unif := by
  have : (fun ω : ℕ → St n => (ω (t + 1)).2) = Prod.snd ∘ (fun ω : ℕ → St n => ω (t + 1)) := rfl
  rw [this, ← Measure.map_map measurable_snd (measurable_pi_apply _)]
  unfold Pm
  rw [Measure.infinitePi_map_eval]
  unfold nu
  rw [Measure.map_snd_prod]
  simp

theorem law_X (hy : Hy L μ) (hμint : ∫ x, μ x = 1) (vs : ℕ → Fin n → ℝ) :
    ∀ t j, (Pm μ).map (fun ω => Xs μ L vs t ω j) = densityLaw μ := by
  intro t
  induction t with
  | zero =>
    intro j
    have : (fun ω : ℕ → St n => Xs μ L vs 0 ω j) =
        ((fun x : Fin 3 → Fin n → ℝ => x j) ∘ Prod.fst) ∘ (fun ω : ℕ → St n => ω 0) := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j |>.comp measurable_fst)
      (measurable_pi_apply 0)]
    unfold Pm
    rw [Measure.infinitePi_map_eval]
    unfold nu
    rw [← Measure.map_map (measurable_pi_apply j) measurable_fst, Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
    exact (measurePreserving_eval (fun _ : Fin 3 => densityLaw μ) j).map_eq
  | succ t ih =>
    intro j
    have hY := Xs_meas hy vs t
    have hU : Measurable fun ω : ℕ → St n => (ω (t + 1)).2 :=
      measurable_snd.comp (measurable_pi_apply (t + 1))
    have hg : Measurable fun ω : ℕ → St n => (Xs μ L vs t ω, (ω (t + 1)).2) := hY.prodMk hU
    have hjoint : (Pm μ).map (fun ω : ℕ → St n => (Xs μ L vs t ω, (ω (t + 1)).2)) =
        ((Pm μ).map (Xs μ L vs t)).prod unif := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hU.aemeasurable).1
        (indep_XU hy vs t), map_U]
    have hF : Measurable fun q : (Fin 3 → Fin n → ℝ) × ℝ =>
        q.1 j + dd μ L (vs t) q.1 q.2 j • vs t :=
      ((measurable_pi_apply j).comp measurable_fst).add
        (((measurable_pi_apply j).comp (dd_meas hy (vs t))).smul_const (vs t))
    have hmeas : Measurable fun ω : ℕ → St n => Xs μ L vs (t + 1) ω j :=
      (measurable_pi_apply j).comp (Xs_meas hy vs (t + 1))
    refine Measure.ext fun B hB => ?_
    rw [Measure.map_apply hmeas hB]
    have hmf : Measurable fun y => stepMeasure μ L (vs t) y B :=
      (Measure.measurable_coe hB).comp (C.step_meas L μ hy.m (vs t))
    calc (Pm μ) ((fun ω => Xs μ L vs (t + 1) ω j) ⁻¹' B)
        = (Pm μ) ((fun ω : ℕ → St n => (Xs μ L vs t ω, (ω (t + 1)).2)) ⁻¹'
            ((fun q : (Fin 3 → Fin n → ℝ) × ℝ => q.1 j + dd μ L (vs t) q.1 q.2 j • vs t) ⁻¹' B)) := rfl
      _ = ((Pm μ).map (fun ω : ℕ → St n => (Xs μ L vs t ω, (ω (t + 1)).2)))
            ((fun q : (Fin 3 → Fin n → ℝ) × ℝ => q.1 j + dd μ L (vs t) q.1 q.2 j • vs t) ⁻¹' B) :=
          (Measure.map_apply hg (hF hB)).symm
      _ = (((Pm μ).map (Xs μ L vs t)).prod unif)
            ((fun q : (Fin 3 → Fin n → ℝ) × ℝ => q.1 j + dd μ L (vs t) q.1 q.2 j • vs t) ⁻¹' B) := by
          rw [hjoint]
      _ = ∫⁻ x, unif (Prod.mk x ⁻¹'
            ((fun q : (Fin 3 → Fin n → ℝ) × ℝ => q.1 j + dd μ L (vs t) q.1 q.2 j • vs t) ⁻¹' B))
            ∂((Pm μ).map (Xs μ L vs t)) := Measure.prod_apply (hF hB)
      _ = ∫⁻ x, stepMeasure μ L (vs t) (x j) B ∂((Pm μ).map (Xs μ L vs t)) :=
          lintegral_congr fun x => step_law hy (vs t) x j B hB
      _ = ∫⁻ y, stepMeasure μ L (vs t) y B ∂(((Pm μ).map (Xs μ L vs t)).map (fun x => x j)) :=
          (lintegral_map hmf (measurable_pi_apply j)).symm
      _ = ∫⁻ y, stepMeasure μ L (vs t) y B ∂(densityLaw μ) := by
          rw [Measure.map_map (measurable_pi_apply j) hY]
          exact congrArg (fun m => ∫⁻ y, stepMeasure μ L (vs t) y B ∂m) (ih j)
      _ = ((densityLaw μ).bind (stepMeasure μ L (vs t))) B :=
          (Measure.bind_apply hB (C.step_meas L μ hy.m (vs t)).aemeasurable).symm
      _ = walkLaw μ L [vs t] B := rfl
      _ = densityLaw μ B := by
          rw [lemma_2_2 L μ hy.m hy.pos hy.zero hμint [vs t]]

end

end

end OnlineBeckFiala.Dev.P27
end

section
open MeasureTheory ProbabilityTheory

namespace OnlineBeckFiala.Dev.P27

section
variable {n : ℕ} {L : ℝ} {μ : (Fin n → ℝ) → ℝ}

open Classical in
noncomputable def eps (d : Fin 3 → ℝ) : ℝ := if ∑ j, d j = -1 then -1 else 1

theorem eps_pm (d : Fin 3 → ℝ) : eps d = 1 ∨ eps d = -1 := by
  unfold eps; split_ifs <;> simp

theorem eps_meas : Measurable eps := by
  classical
  unfold eps
  exact Measurable.ite (measurableSet_eq_fun (Finset.measurable_sum _ fun j _ =>
    measurable_pi_apply j) measurable_const) measurable_const measurable_const

theorem eps_eq (d : Fin 3 → ℝ) (h : ∑ j, d j = 1 ∨ ∑ j, d j = -1) : eps d = ∑ j, d j := by
  unfold eps
  rcases h with h | h
  · rw [if_neg (by rw [h]; norm_num), h]
  · rw [if_pos h, h]

/-- the sign chosen at time `t` -/
noncomputable def sgn (μ : (Fin n → ℝ) → ℝ) (L : ℝ) (vs : ℕ → Fin n → ℝ) (t : ℕ)
    (ω : ℕ → St n) : ℝ :=
  eps (dd μ L (vs t) (Xs μ L vs t ω) (ω (t + 1)).2)

theorem sgn_meas (hy : Hy L μ) (vs : ℕ → Fin n → ℝ) (t : ℕ) : Measurable (sgn μ L vs t) := by
  have hU : Measurable fun ω : ℕ → St n => (ω (t + 1)).2 :=
    measurable_snd.comp (measurable_pi_apply (t + 1))
  exact eps_meas.comp ((dd_meas hy (vs t)).comp ((Xs_meas hy vs t).prodMk hU))

theorem sgn_online (vs vs' : ℕ → Fin n → ℝ) (t : ℕ) (h : ∀ s ≤ t, vs s = vs' s) :
    sgn μ L vs t = sgn μ L vs' t := by
  funext ω
  unfold sgn
  rw [Xs_congr_a vs vs' t (fun s hs => h s hs.le) ω, h t le_rfl]

theorem densityLaw_cube (hy : Hy L μ) : densityLaw μ (cube L)ᶜ = 0 := by
  unfold densityLaw
  rw [withDensity_apply _ (cube_meas' L).compl]
  rw [setLIntegral_congr_fun (cube_meas' L).compl (g := fun _ => 0)
    (fun x hx => by simp [hy.zero x hx])]
  simp

variable [IsProbabilityMeasure (densityLaw μ)]

theorem ae_good (hy : Hy L μ) (hμint : ∫ x, μ x = 1) (vs : ℕ → Fin n → ℝ) :
    ∀ᵐ ω ∂(Pm μ), ∀ t, (∀ j, Xs μ L vs t ω j ∈ cube L) ∧ (ω (t + 1)).2 ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro t
  have h1 : ∀ j, ∀ᵐ ω ∂(Pm μ), Xs μ L vs t ω j ∈ cube L := by
    intro j
    have hm : Measurable fun ω => Xs μ L vs t ω j :=
      (measurable_pi_apply j).comp (Xs_meas hy vs t)
    refine ae_of_ae_map hm.aemeasurable ?_
    rw [law_X hy hμint vs t j, ae_iff]
    exact densityLaw_cube hy
  have h2 : ∀ᵐ ω ∂(Pm μ), (ω (t + 1)).2 ∈ Set.Ico (0 : ℝ) 1 := by
    have hU : Measurable fun ω : ℕ → St n => (ω (t + 1)).2 :=
      measurable_snd.comp (measurable_pi_apply (t + 1))
    refine ae_of_ae_map hU.aemeasurable ?_
    rw [map_U]
    exact ae_restrict_mem measurableSet_Ico
  filter_upwards [ae_all_iff.2 h1, h2] with ω a b using ⟨a, b⟩

end

end OnlineBeckFiala.Dev.P27
end

section
open MeasureTheory ProbabilityTheory

namespace OnlineBeckFiala.Dev.P27

section
variable {n : ℕ} {L : ℝ} {μ : (Fin n → ℝ) → ℝ}

theorem norm_le_of_cube (hL : 0 < L) {x : Fin n → ℝ} (h : x ∈ cube L) : ‖x‖ ≤ L := by
  refine (pi_norm_le_iff_of_nonneg hL.le).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨(h i).1.le, (h i).2.le⟩

theorem det_bound (hy : Hy L μ) (hL : 0 < L) (vs : ℕ → Fin n → ℝ) (T : ℕ) (ω : ℕ → St n)
    (hG : ∀ t, (∀ j, Xs μ L vs t ω j ∈ cube L) ∧ (ω (t + 1)).2 ∈ Set.Ico (0 : ℝ) 1)
    (hbal : ∀ t < T, ∀ j, IsBalanced L μ (vs t) (Xs μ L vs t ω j))
    (k : ℕ) (hk : k < T) :
    ‖∑ s ∈ Finset.range (k + 1), sgn μ L vs s ω • vs s‖ ≤ 6 * L := by
  have hs : ∀ s < T, sgn μ L vs s ω • vs s =
      ∑ j, (Xs μ L vs (s + 1) ω j - Xs μ L vs s ω j) := by
    intro s hs
    have hg : good μ L (vs s) (Xs μ L vs s ω) := hbal s hs
    have h1 := dd_sum hy (vs s) _ hg _ (hG s).2
    unfold sgn
    rw [eps_eq _ h1, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Xs]
    abel
  rw [Finset.sum_congr rfl (fun s hs' => hs s (by simp at hs'; omega)), Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_range_sub (fun s => Xs μ L vs s ω j) (k + 1)]
  calc ‖∑ j, (Xs μ L vs (k + 1) ω j - Xs μ L vs 0 ω j)‖
      ≤ ∑ j, ‖Xs μ L vs (k + 1) ω j - Xs μ L vs 0 ω j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, (L + L) := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · exact norm_le_of_cube hL ((hG (k + 1)).1 j)
        · exact norm_le_of_cube hL ((hG 0).1 j)
    _ = 6 * L := by simp; ring

variable [IsProbabilityMeasure (densityLaw μ)]

theorem core (V : Set (Fin n → ℝ)) (hy : Hy L μ) (hL : 0 < L) (hμint : ∫ x, μ x = 1) (θ : ENNReal)
    (h8 : ∀ v ∈ V, densityLaw μ {x | ¬ IsBalanced L μ v x} ≤ θ)
    (T : ℕ) (vs : ℕ → Fin n → ℝ) (hvs : ∀ t < T, vs t ∈ V) :
    Pm μ {ω | ∃ k < T, 6 * L < ‖∑ s ∈ Finset.range (k + 1), sgn μ L vs s ω • vs s‖} ≤
      3 * (T : ENNReal) * θ := by
  classical
  set B : ℕ → Fin 3 → Set (ℕ → St n) := fun t j =>
    {ω | ¬ IsBalanced L μ (vs t) (Xs μ L vs t ω j)} with hB
  set Bad : Set (ℕ → St n) := ⋃ t ∈ Finset.range T, ⋃ j, B t j with hBad
  set G : Set (ℕ → St n) := {ω | ∀ t, (∀ j, Xs μ L vs t ω j ∈ cube L) ∧
    (ω (t + 1)).2 ∈ Set.Ico (0 : ℝ) 1} with hG
  have hGc : Pm μ Gᶜ = 0 := by
    have := ae_good hy hμint vs
    rw [ae_iff] at this
    exact this
  have hsub : {ω | ∃ k < T, 6 * L < ‖∑ s ∈ Finset.range (k + 1), sgn μ L vs s ω • vs s‖} ⊆
      Bad ∪ Gᶜ := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or, Set.mem_compl_iff, not_not] at hnot
    obtain ⟨hnb, hgω⟩ := hnot
    obtain ⟨k, hk, hlt⟩ := hω
    have hbal : ∀ t < T, ∀ j, IsBalanced L μ (vs t) (Xs μ L vs t ω j) := by
      intro t ht j
      by_contra hj
      exact hnb (by
        simp only [hBad, Set.mem_iUnion]
        exact ⟨t, Finset.mem_range.2 ht, j, hj⟩)
    exact absurd (det_bound hy hL vs T ω hgω hbal k hk) (not_le.2 hlt)
  have hBt : ∀ t < T, ∀ j, Pm μ (B t j) ≤ θ := by
    intro t ht j
    have hm : Measurable fun ω => Xs μ L vs t ω j :=
      (measurable_pi_apply j).comp (Xs_meas hy vs t)
    calc Pm μ (B t j) = Pm μ ((fun ω => Xs μ L vs t ω j) ⁻¹' {x | ¬ IsBalanced L μ (vs t) x}) := rfl
      _ ≤ (Pm μ).map (fun ω => Xs μ L vs t ω j) {x | ¬ IsBalanced L μ (vs t) x} :=
          Measure.le_map_apply hm.aemeasurable _
      _ = densityLaw μ {x | ¬ IsBalanced L μ (vs t) x} := by rw [law_X hy hμint vs t j]
      _ ≤ θ := h8 _ (hvs t ht)
  calc Pm μ {ω | ∃ k < T, 6 * L < ‖∑ s ∈ Finset.range (k + 1), sgn μ L vs s ω • vs s‖}
      ≤ Pm μ (Bad ∪ Gᶜ) := measure_mono hsub
    _ ≤ Pm μ Bad + Pm μ Gᶜ := measure_union_le _ _
    _ = Pm μ Bad := by rw [hGc, add_zero]
    _ ≤ ∑ t ∈ Finset.range T, Pm μ (⋃ j, B t j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ t ∈ Finset.range T, ∑ j : Fin 3, Pm μ (B t j) :=
        Finset.sum_le_sum fun t _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ t ∈ Finset.range T, ∑ _j : Fin 3, θ :=
        Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => hBt t (Finset.mem_range.1 ht) j
    _ = 3 * (T : ENNReal) * θ := by
        simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end

end OnlineBeckFiala.Dev.P27
end

section
open MeasureTheory

namespace OnlineBeckFiala

theorem chk_proposition_2_7 {n : ℕ} (V : Set (Fin n → ℝ)) (L : ℝ) (hL : 0 < L)
    (μ : (Fin n → ℝ) → ℝ) (hμm : Measurable μ) (hμpos : ∀ x ∈ cube L, 0 < μ x)
    (hμzero : ∀ x ∉ cube L, μ x = 0)
    (hμint : ∫ x, μ x = 1) (θ : ENNReal)
    (h8 : ∀ v ∈ V, densityLaw μ {x | ¬ IsBalanced L μ v x} ≤ θ) :
    ∃ alg : OnlineSigner n, ∀ (T : ℕ) (vs : ℕ → (Fin n → ℝ)), (∀ t < T, vs t ∈ V) →
      alg.P {ω | ∃ k < T, 6 * L < ‖prefixSum alg vs k ω‖} ≤ 3 * (T : ENNReal) * θ := by
  have hy : Dev.P27.Hy L μ := ⟨hμm, hμpos, hμzero⟩
  haveI : IsProbabilityMeasure (densityLaw μ) := Dev.P27.densityLaw_prob hy hμint
  let alg : OnlineSigner n :=
    { Ω := ℕ → Dev.P27.St n
      P := Dev.P27.Pm μ
      sign := fun vs t ω => Dev.P27.sgn μ L vs t ω
      sign_pm := fun vs t ω => Dev.P27.eps_pm _
      online := fun a a' t h => Dev.P27.sgn_online a a' t h
      meas := fun a t => Dev.P27.sgn_meas hy a t }
  refine ⟨alg, fun T vs hvs => ?_⟩
  exact Dev.P27.core V hy hL hμint θ h8 T vs hvs

end OnlineBeckFiala

end

theorem solution : type_of% @OnlineBeckFiala.chk_proposition_2_7 := @OnlineBeckFiala.chk_proposition_2_7
