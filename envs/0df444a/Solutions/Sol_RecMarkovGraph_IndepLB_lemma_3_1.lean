-- Prove2me | solution 1 for RecMarkovGraph.IndepLB.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:02:55.536961+00:00
-- url     : https://prove2.me/submissions/de4978b2-2b8d-4920-ad22-a9dd41d2efa0

import Mathlib
import Definitions.Def_RecMarkovGraph_IndepLB_Model

open Filter Topology Finset
open scoped Classical

namespace RecMarkovGraph.IndepLB.T22Aux


lemma recSeq_mem (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1) :
    ∀ k, 0 ≤ recSeq (1 - r) p k ∧ recSeq (1 - r) p k ≤ 1
  | 0 => ⟨hp.le, hp1⟩
  | k + 1 => by
    obtain ⟨h0, h1⟩ := recSeq_mem p r hp hp1 hr hr1 k
    simp only [recSeq, fa]
    have hpos : 0 ≤ 1 - (1 - r) * recSeq (1 - r) p k := by nlinarith
    constructor
    · exact mul_nonneg h0 hpos
    · nlinarith [mul_nonneg (mul_nonneg h0 h0) (by linarith : (0:ℝ) ≤ 1 - r)]

lemma stepWeight_nonneg (r q : ℝ) (hr : 0 < r) (hr1 : r < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (P Q : Prop) : 0 ≤ stepWeight r q P Q := by
  unfold stepWeight
  split_ifs <;> nlinarith

lemma stepWeight_sum (r q : ℝ) (P : Prop) :
    ∑ b : Bool, stepWeight r q P (b = true) = 1 := by
  simp only [Fintype.sum_bool, stepWeight]
  split_ifs <;> simp_all

lemma chainWeight_nonneg (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (m : ℕ) (x : ℕ → Prop) : 0 ≤ chainWeight p r m x := by
  unfold chainWeight
  by_cases hm : m = 0
  · rw [if_pos hm]; exact zero_le_one
  · rw [if_neg hm]
    refine mul_nonneg (by split_ifs <;> linarith) (Finset.prod_nonneg fun j _ => ?_)
    obtain ⟨h0, h1⟩ := recSeq_mem p r hp hp1 hr hr1 j
    exact stepWeight_nonneg r _ hr hr1 h0 h1 _ _

lemma stepWeight_congr (r q : ℝ) (P P' Q Q' : Prop) (hP : P ↔ P') (hQ : Q ↔ Q') :
    stepWeight r q P Q = stepWeight r q P' Q' := by
  rw [propext hP, propext hQ]

lemma chainWeight_congr (p r : ℝ) (m : ℕ) (x y : ℕ → Prop) (h : ∀ j < m, (x j ↔ y j)) :
    chainWeight p r m x = chainWeight p r m y := by
  unfold chainWeight
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm]
    congr 1
    · exact if_congr (h 0 (by omega)) rfl rfl
    · refine Finset.prod_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      exact stepWeight_congr r _ _ _ _ _ (h j (by omega)) (h (j + 1) (by omega))

lemma chainWeight_succ (p r : ℝ) (m : ℕ) (hm : 1 ≤ m) (x : ℕ → Prop) :
    chainWeight p r (m + 1) x =
      chainWeight p r m x * stepWeight r (recSeq (1 - r) p (m - 1)) (x (m - 1)) (x m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold chainWeight
  simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  rw [Finset.prod_range_succ]
  ring

/-- The row law sums to one. -/
lemma rowSum (p r : ℝ) : ∀ m : ℕ,
    ∑ y : Fin m → Bool, chainWeight p r m (fun j => ∃ h : j < m, y ⟨j, h⟩ = true) = 1
  | 0 => by simp [chainWeight]
  | m + 1 => by
    rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Bool)) _ _ (fun _ => rfl)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hlt : ∀ (y' : Fin m → Bool) (b : Bool), ∀ j < m,
        ((∃ h : j < m + 1, (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨j, h⟩ = true) ↔
          ∃ h : j < m, y' ⟨j, h⟩ = true) := by
      intro y' b j hj
      have e : ∀ h : j < m + 1, (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨j, h⟩ = y' ⟨j, hj⟩ := by
        intro h
        simp only [Fin.snocEquiv_apply]
        exact Fin.snoc_castSucc (α := fun _ => Bool) (p := y') (x := b) (i := ⟨j, hj⟩)
      constructor
      · rintro ⟨h, hh⟩; exact ⟨hj, by rw [← e h]; exact hh⟩
      · rintro ⟨h, hh⟩; exact ⟨by omega, by rw [e]; exact hh⟩
    have hlast : ∀ (y' : Fin m → Bool) (b : Bool),
        ((∃ h : m < m + 1, (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨m, h⟩ = true) ↔ b = true) := by
      intro y' b
      have e : (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨m, by omega⟩ = b := by
        simp only [Fin.snocEquiv_apply]
        exact Fin.snoc_last (α := fun _ => Bool) (p := y') (x := b)
      constructor
      · rintro ⟨h, hh⟩; rw [← e]; exact hh
      · intro hb; exact ⟨by omega, by rw [e]; exact hb⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [chainWeight, Nat.add_one_ne_zero, if_false, Nat.sub_self, Finset.range_zero,
        Finset.prod_empty, mul_one]
      rw [Fintype.sum_unique]
      rw [Fintype.sum_bool]
      have h1 := hlast (default : Fin 0 → Bool) true
      have h2 := hlast (default : Fin 0 → Bool) false
      split_ifs with ha hb hb
      · exact absurd (h2.mp hb) (by simp)
      · ring
      · exact absurd (h1.mpr rfl) ha
      · exact absurd (h1.mpr rfl) ha
    · rw [← rowSum p r m]
      refine Finset.sum_congr rfl (fun y' _ => ?_)
      have hc : ∀ b : Bool, chainWeight p r (m + 1)
          (fun j => ∃ h : j < m + 1, (Fin.snocEquiv (fun _ => Bool) (b, y')) ⟨j, h⟩ = true) =
          chainWeight p r m (fun j => ∃ h : j < m, y' ⟨j, h⟩ = true) *
            stepWeight r (recSeq (1 - r) p (m - 1)) (∃ h : m - 1 < m, y' ⟨m - 1, h⟩ = true)
              (b = true) := by
        intro b
        rw [chainWeight_succ p r m hm]
        rw [chainWeight_congr p r m _ _ (hlt y' b)]
        exact congrArg _ (stepWeight_congr r _ _ _ _ _ (hlt y' b (m - 1) (by omega)) (hlast y' b))
      simp only [hc]
      rw [← Finset.mul_sum, stepWeight_sum, mul_one]

noncomputable def rowEquiv (n : ℕ) : SimpleGraph (Fin n) ≃ (∀ i : Fin n, Fin i → Bool) where
  toFun G i j := decide (G.Adj ⟨j, j.2.trans i.2⟩ i)
  invFun f :=
    { Adj := fun a b => (∃ h : b.val < a.val, f a ⟨b, h⟩ = true) ∨
        (∃ h : a.val < b.val, f b ⟨a, h⟩ = true)
      symm := ⟨fun _ _ h => Or.symm h⟩
      loopless := ⟨fun a h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h⟩ }
  left_inv G := by
    ext a b
    simp only [decide_eq_true_eq, Fin.eta]
    rcases lt_trichotomy a.val b.val with h | h | h
    · constructor
      · rintro (⟨h', _⟩ | ⟨_, h'⟩)
        · omega
        · exact h'
      · intro hab; exact Or.inr ⟨h, hab⟩
    · have : a = b := Fin.ext h
      subst this
      simp
    · constructor
      · rintro (⟨_, h'⟩ | ⟨h', _⟩)
        · exact G.adj_symm h'
        · omega
      · intro hab; exact Or.inl ⟨h, G.adj_symm hab⟩
  right_inv f := by
    funext i j
    have hj := j.2
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro (⟨h', _⟩ | ⟨_, h'⟩)
      · omega
      · exact h'
    · intro hf; exact Or.inr ⟨hj, hf⟩

lemma weight_eq (n : ℕ) (p r : ℝ) (G : SimpleGraph (Fin n)) :
    rmrgWeight n p r G = ∏ i : Fin n,
      chainWeight p r i (fun j => ∃ h : j < (i : ℕ), rowEquiv n G i ⟨j, h⟩ = true) := by
  unfold rmrgWeight
  refine Finset.prod_congr rfl (fun i _ => chainWeight_congr p r _ _ _ (fun j hj => ?_))
  simp only [rowEquiv, Equiv.coe_fn_mk, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩; exact ⟨hj, h⟩
  · rintro ⟨_, h⟩; exact ⟨hj.trans i.2, h⟩

lemma weight_nonneg (n : ℕ) (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (G : SimpleGraph (Fin n)) : 0 ≤ rmrgWeight n p r G :=
  Finset.prod_nonneg fun i _ => chainWeight_nonneg p r hp hp1 hr hr1 _ _

lemma total_eq_one (n : ℕ) (p r : ℝ) : rmrgProb n p r (fun _ => True) = 1 := by
  unfold rmrgProb
  simp only [if_true, mul_one]
  rw [Fintype.sum_equiv (rowEquiv n) _
    (fun f => ∏ i : Fin n, chainWeight p r i (fun j => ∃ h : j < (i : ℕ), f i ⟨j, h⟩ = true))
    (fun G => weight_eq n p r G)]
  have hps := Fintype.prod_sum (fun (i : Fin n) (y : Fin i → Bool) =>
    chainWeight p r i (fun j => ∃ h : j < (i : ℕ), y ⟨j, h⟩ = true))
  rw [← hps]
  exact Finset.prod_eq_one (fun i _ => rowSum p r i)

lemma prob_mono (n : ℕ) (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (E F : SimpleGraph (Fin n) → Prop) (h : ∀ G, E G → F G) :
    rmrgProb n p r E ≤ rmrgProb n p r F := by
  unfold rmrgProb
  refine Finset.sum_le_sum (fun G _ => mul_le_mul_of_nonneg_left ?_
    (weight_nonneg n p r hp hp1 hr hr1 G))
  by_cases hE : E G
  · simp [hE, h G hE]
  · simp only [hE, if_false]; split_ifs <;> norm_num

lemma prob_le_one (n : ℕ) (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (E : SimpleGraph (Fin n) → Prop) : rmrgProb n p r E ≤ 1 := by
  rw [← total_eq_one n p r]
  exact prob_mono n p r hp hp1 hr hr1 _ _ (fun _ _ => trivial)


/-! ## Stage A: one row -/

/-- the Prop-valued row pattern of a Boolean row -/
def X {m : ℕ} (y : Fin m → Bool) : ℕ → Prop := fun j => ∃ h : j < m, y ⟨j, h⟩ = true

/-- expectation under the law of a row of length `m` -/
noncomputable def RE (p r : ℝ) (m : ℕ) (g : (Fin m → Bool) → ℝ) : ℝ :=
  ∑ y : Fin m → Bool, chainWeight p r m (X y) * g y

def snocB {m : ℕ} (y : Fin m → Bool) (b : Bool) : Fin (m + 1) → Bool :=
  Fin.snoc (α := fun _ => Bool) y b

lemma X_snoc_lt {m : ℕ} (y : Fin m → Bool) (b : Bool) (j : ℕ) (hj : j < m) :
    X (snocB y b) j ↔ X y j := by
  have e : ∀ h : j < m + 1, (snocB y b) ⟨j, h⟩ = y ⟨j, hj⟩ := by
    intro h
    exact Fin.snoc_castSucc (α := fun _ => Bool) (p := y) (x := b) (i := ⟨j, hj⟩)
  constructor
  · rintro ⟨h, hh⟩; exact ⟨hj, by rw [← e h]; exact hh⟩
  · rintro ⟨h, hh⟩; exact ⟨by omega, by rw [e]; exact hh⟩

lemma X_snoc_last {m : ℕ} (y : Fin m → Bool) (b : Bool) : X (snocB y b) m ↔ b = true := by
  have e : (snocB y b) ⟨m, by omega⟩ = b :=
    Fin.snoc_last (α := fun _ => Bool) (p := y) (x := b)
  constructor
  · rintro ⟨h, hh⟩; rw [← e]; exact hh
  · intro hb; exact ⟨by omega, by rw [e]; exact hb⟩

lemma RE_snoc (p r : ℝ) (m : ℕ) (hm : 1 ≤ m) (g : (Fin (m + 1) → Bool) → ℝ) :
    RE p r (m + 1) g = RE p r m (fun y => ∑ b : Bool,
      stepWeight r (recSeq (1 - r) p (m - 1)) (X y (m - 1)) (b = true) * g (snocB y b)) := by
  unfold RE
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Bool)) _ _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have h1 : (Fin.snocEquiv (fun _ => Bool)) (b, y) = snocB y b := rfl
  rw [h1, chainWeight_succ p r m hm, chainWeight_congr p r m _ _ (X_snoc_lt y b),
    stepWeight_congr r _ _ _ _ _ (X_snoc_lt y b (m - 1) (by omega)) (X_snoc_last y b)]
  ring

lemma RE_one (p r : ℝ) (g : (Fin 1 → Bool) → ℝ) :
    RE p r 1 g = p * g (fun _ => true) + (1 - p) * g (fun _ => false) := by
  unfold RE
  rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool).symm _ _ (fun _ => rfl)]
  rw [Fintype.sum_bool]
  have ht : X ((Equiv.funUnique (Fin 1) Bool).symm true) 0 := ⟨by omega, rfl⟩
  have hf : ¬ X ((Equiv.funUnique (Fin 1) Bool).symm false) 0 := by
    rintro ⟨_, h⟩; simp at h
  simp only [chainWeight, one_ne_zero, if_false, Nat.sub_self, Finset.range_zero,
    Finset.prod_empty, mul_one]
  rw [if_pos ht, if_neg hf]
  rfl

lemma RE_linear (p r : ℝ) (m : ℕ) (a : ℝ) (g h : (Fin m → Bool) → ℝ) :
    RE p r m (fun y => a * g y + h y) = a * RE p r m g + RE p r m h := by
  unfold RE
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

lemma RE_const (p r : ℝ) (m : ℕ) (c : ℝ) : RE p r m (fun _ => c) = c := by
  unfold RE
  rw [← Finset.sum_mul, show (∑ y : Fin m → Bool, chainWeight p r m (X y)) = 1 from rowSum p r m,
    one_mul]

lemma RE_mono (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1) (m : ℕ)
    (g h : (Fin m → Bool) → ℝ) (hgh : ∀ y, g y ≤ h y) : RE p r m g ≤ RE p r m h := by
  unfold RE
  exact Finset.sum_le_sum (fun y _ =>
    mul_le_mul_of_nonneg_left (hgh y) (chainWeight_nonneg p r hp hp1 hr hr1 m _))

/-- one transition, averaged against `c + d·[b]` -/
lemma stepSum (r q : ℝ) (P : Prop) (c d : ℝ) :
    ∑ b : Bool, stepWeight r q P (b = true) * (c + d * (if b = true then 1 else 0)) =
      c + d * (if P then r * q else q) := by
  simp only [Fintype.sum_bool, stepWeight]
  by_cases hP : P <;> simp [hP] <;> ring

/-- indicator of the last edge of the row -/
noncomputable def L (m : ℕ) (y : Fin m → Bool) : ℝ := if X y (m - 1) then 1 else 0

lemma stepTrue_eq (r q : ℝ) (P : Prop) :
    (if P then r * q else q) = q - (1 - r) * q * (if P then 1 else 0) := by
  split_ifs <;> ring

lemma L_snoc {m : ℕ} (y : Fin m → Bool) (b : Bool) :
    L (m + 1) (snocB y b) = if b = true then 1 else 0 := by
  unfold L
  simp only [Nat.add_sub_cancel]
  by_cases hb : b = true
  · rw [if_pos ((X_snoc_last y b).mpr hb), if_pos hb]
  · rw [if_neg (fun h => hb ((X_snoc_last y b).mp h)), if_neg hb]

/-- the marginal of the last edge of a row of length `m ≥ 1` is `x_m` -/
lemma marg (p r : ℝ) : ∀ m : ℕ, 1 ≤ m → RE p r m (L m) = recSeq (1 - r) p (m - 1)
  | 0, h => absurd h (by omega)
  | 1, _ => by
    rw [RE_one]
    have ht : L 1 (fun _ => true) = 1 := if_pos ⟨by omega, rfl⟩
    have hf : L 1 (fun _ => false) = 0 := if_neg (by rintro ⟨_, h⟩; simp at h)
    rw [ht, hf]; simp [recSeq]
  | m + 2, _ => by
    have ih := marg p r (m + 1) (by omega)
    rw [RE_snoc p r (m + 1) (by omega)]
    have : ∀ y : Fin (m + 1) → Bool, (∑ b : Bool,
        stepWeight r (recSeq (1 - r) p (m + 1 - 1)) (X y (m + 1 - 1)) (b = true) *
          L (m + 1 + 1) (snocB y b)) =
        (-((1 - r) * recSeq (1 - r) p (m + 1 - 1))) * L (m + 1) y +
          recSeq (1 - r) p (m + 1 - 1) := by
      intro y
      have := stepSum r (recSeq (1 - r) p (m + 1 - 1)) (X y (m + 1 - 1)) 0 1
      simp only [zero_add, one_mul] at this
      simp only [L_snoc]
      rw [this, stepTrue_eq]
      unfold L
      ring
    simp only [this]
    rw [RE_linear, RE_const, ih]
    show _ = recSeq (1 - r) p (m + 1)
    rw [recSeq]
    simp only [Nat.add_sub_cancel, fa]
    ring

/-- number of present edges of a row -/
noncomputable def s (m : ℕ) (y : Fin m → Bool) : ℝ := ∑ j : Fin m, (if y j = true then 1 else 0)

lemma s_nonneg (m : ℕ) (y : Fin m → Bool) : 0 ≤ s m y :=
  Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

lemma s_snoc {m : ℕ} (y : Fin m → Bool) (b : Bool) :
    s (m + 1) (snocB y b) = s m y + (if b = true then 1 else 0) := by
  unfold s
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show snocB y b (Fin.castSucc j) = y j from
      Fin.snoc_castSucc (α := fun _ => Bool) (p := y) (x := b) (i := j)]
  · rw [show snocB y b (Fin.last m) = b from Fin.snoc_last (α := fun _ => Bool) (p := y) (x := b)]

/-- expected row sum -/
noncomputable def fS (p r : ℝ) (m : ℕ) : ℝ := ∑ k ∈ range m, recSeq (1 - r) p k

lemma first_moment (p r : ℝ) : ∀ m : ℕ, RE p r m (s m) = fS p r m
  | 0 => by simp [RE, s, fS]
  | 1 => by
    rw [RE_one]
    simp [s, fS, recSeq]
  | m + 2 => by
    have ih := first_moment p r (m + 1)
    have hmarg := marg p r (m + 1) (by omega)
    rw [RE_snoc p r (m + 1) (by omega)]
    have : ∀ y : Fin (m + 1) → Bool, (∑ b : Bool,
        stepWeight r (recSeq (1 - r) p (m + 1 - 1)) (X y (m + 1 - 1)) (b = true) *
          s (m + 1 + 1) (snocB y b)) =
        (-((1 - r) * recSeq (1 - r) p (m + 1 - 1))) * L (m + 1) y +
          (1 * s (m + 1) y + recSeq (1 - r) p (m + 1 - 1)) := by
      intro y
      have := stepSum r (recSeq (1 - r) p (m + 1 - 1)) (X y (m + 1 - 1)) (s (m + 1) y) 1
      simp only [s_snoc]
      simp only [one_mul] at this ⊢
      rw [this, stepTrue_eq]
      unfold L
      ring
    simp only [this]
    rw [RE_linear, RE_linear, RE_const, ih, hmarg]
    simp only [fS, Finset.sum_range_succ, Nat.add_sub_cancel, recSeq, fa]
    ring

lemma fS_mono (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1) {a b : ℕ}
    (hab : a ≤ b) : fS p r a ≤ fS p r b := by
  unfold fS
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    (fun k _ _ => (recSeq_mem p r hp hp1 hr hr1 k).1)

lemma fS_nonneg (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1) (m : ℕ) :
    0 ≤ fS p r m := by
  have := fS_mono p r hp hp1 hr hr1 (Nat.zero_le m)
  simpa [fS] using this

/-- recursion inequality for the second moment -/
lemma second_step (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (m : ℕ) (hm : 1 ≤ m) :
    RE p r (m + 1) (fun y => s (m + 1) y ^ 2) ≤
      RE p r m (fun y => s m y ^ 2) + recSeq (1 - r) p (m - 1) * (2 * fS p r m + 1) := by
  set q := recSeq (1 - r) p (m - 1)
  obtain ⟨hq0, hq1⟩ := recSeq_mem p r hp hp1 hr hr1 (m - 1)
  rw [RE_snoc p r m hm]
  have key : ∀ y : Fin m → Bool, (∑ b : Bool,
      stepWeight r q (X y (m - 1)) (b = true) * s (m + 1) (snocB y b) ^ 2) ≤
      (2 * q) * s m y + (1 * s m y ^ 2 + q) := by
    intro y
    have := stepSum r q (X y (m - 1)) (s m y ^ 2) (2 * s m y + 1)
    have e : ∀ b : Bool, s (m + 1) (snocB y b) ^ 2 =
        s m y ^ 2 + (2 * s m y + 1) * (if b = true then 1 else 0) := by
      intro b; rw [s_snoc]; cases b <;> simp <;> ring
    simp only [e]
    rw [this]
    have hle : (if X y (m - 1) then r * q else q) ≤ q := by
      split_ifs <;> nlinarith
    have hs := s_nonneg m y
    nlinarith
  calc _ ≤ RE p r m (fun y => (2 * q) * s m y + (1 * s m y ^ 2 + q)) :=
        RE_mono p r hp hp1 hr hr1 m _ _ key
    _ = _ := by
        rw [RE_linear, RE_linear, RE_const, first_moment]
        ring

lemma second_moment_aux (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (N : ℕ) : ∀ m : ℕ, 1 ≤ m → m ≤ N →
      RE p r m (fun y => s m y ^ 2) ≤ 1 + (2 * fS p r N + 1) * fS p r (m - 1) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _
    rw [RE_one]
    simp [s, fS]
    linarith
  | succ m hm ih =>
    intro hmN
    have h1 := ih (by omega)
    have h2 := second_step p r hp hp1 hr hr1 m hm
    have h3 : fS p r m ≤ fS p r N := fS_mono p r hp hp1 hr hr1 (by omega)
    have h4 : fS p r (m + 1 - 1) = fS p r (m - 1) + recSeq (1 - r) p (m - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp [fS, Finset.sum_range_succ]
    obtain ⟨hq0, _⟩ := recSeq_mem p r hp hp1 hr hr1 (m - 1)
    rw [h4]
    nlinarith

lemma second_moment (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (N m : ℕ) (hm : m ≤ N) :
    RE p r m (fun y => s m y ^ 2) ≤ 1 + (2 * fS p r N + 1) * fS p r N := by
  have hN := fS_nonneg p r hp hp1 hr hr1 N
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp [RE, s]
    nlinarith
  · have := second_moment_aux p r hp hp1 hr hr1 N m h hm
    have h2 : fS p r (m - 1) ≤ fS p r N := fS_mono p r hp hp1 hr hr1 (by omega)
    nlinarith


/-! ## Stage B: the whole graph -/

noncomputable def Ex (n : ℕ) (p r : ℝ) (Φ : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), rmrgWeight n p r G * Φ G

lemma Ex_prod (n : ℕ) (p r : ℝ) (T : Finset (Fin n)) (φ : ∀ l : Fin n, (Fin l → Bool) → ℝ) :
    Ex n p r (fun G => ∏ l ∈ T, φ l (rowEquiv n G l)) = ∏ l ∈ T, RE p r l (φ l) := by
  unfold Ex
  have h1 : ∀ G, rmrgWeight n p r G * ∏ l ∈ T, φ l (rowEquiv n G l) =
      ∏ l : Fin n, (chainWeight p r l (X (rowEquiv n G l)) *
        (if l ∈ T then φ l (rowEquiv n G l) else 1)) := by
    intro G
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, weight_eq]
    rfl
  simp only [h1]
  rw [Fintype.sum_equiv (rowEquiv n) _
    (fun f => ∏ l : Fin n, (chainWeight p r l (X (f l)) * (if l ∈ T then φ l (f l) else 1)))
    (fun G => rfl)]
  have hps := Fintype.prod_sum (fun (l : Fin n) (y : Fin l → Bool) =>
    chainWeight p r l (X y) * (if l ∈ T then φ l y else 1))
  rw [← hps]
  calc _ = ∏ l : Fin n, (if l ∈ T then RE p r l (φ l) else 1) := by
        refine Finset.prod_congr rfl (fun l _ => ?_)
        split_ifs with hl
        · rfl
        · have := RE_const p r l 1
          simpa [RE] using this
    _ = _ := by rw [Finset.prod_ite_mem, Finset.univ_inter]

lemma Ex_sum (n : ℕ) (p r : ℝ) {ι : Type*} (S : Finset ι) (Φ : ι → SimpleGraph (Fin n) → ℝ) :
    Ex n p r (fun G => ∑ i ∈ S, Φ i G) = ∑ i ∈ S, Ex n p r (Φ i) := by
  unfold Ex
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma Ex_linear (n : ℕ) (p r : ℝ) (a : ℝ) (Φ Ψ : SimpleGraph (Fin n) → ℝ) :
    Ex n p r (fun G => a * Φ G + Ψ G) = a * Ex n p r Φ + Ex n p r Ψ := by
  unfold Ex
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun G _ => ?_)
  ring

lemma Ex_const (n : ℕ) (p r : ℝ) (c : ℝ) : Ex n p r (fun _ => c) = c := by
  have h := total_eq_one n p r
  unfold rmrgProb at h
  unfold Ex
  rw [← Finset.sum_mul]
  simp only [if_true, mul_one] at h
  rw [h, one_mul]

lemma card_edges (n : ℕ) (G : SimpleGraph (Fin n)) :
    (G.edgeFinset.card : ℝ) = ∑ l : Fin n, s l (rowEquiv n G l) := by
  have h2 : (2 : ℝ) * G.edgeFinset.card = ∑ v, (G.degree v : ℝ) := by
    have := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast this.symm
  have hdeg : ∀ v, (G.degree v : ℝ) = ∑ u, (if G.Adj v u then 1 else 0) := by
    intro v
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter]
    push_cast
    rfl
  have hsplit : ∀ v u, (if G.Adj v u then (1 : ℝ) else 0) =
      (if u < v ∧ G.Adj u v then 1 else 0) + (if v < u ∧ G.Adj v u then 1 else 0) := by
    intro v u
    by_cases h : G.Adj v u
    · have hne : u ≠ v := fun e => G.loopless.irrefl v (e ▸ h)
      rcases lt_or_gt_of_ne hne with hl | hl
      · simp [h, G.adj_symm h, hl, not_lt.mpr hl.le]
      · simp [h, hl, not_lt.mpr hl.le]
    · have h' : ¬ G.Adj u v := fun h' => h (G.adj_symm h')
      simp [h, h']
  have hA : ∑ v : Fin n, ∑ u : Fin n, (if v < u ∧ G.Adj v u then (1 : ℝ) else 0) =
      ∑ v : Fin n, ∑ u : Fin n, (if u < v ∧ G.Adj u v then (1 : ℝ) else 0) := Finset.sum_comm
  have hrow : ∀ v : Fin n, ∑ u : Fin n, (if u < v ∧ G.Adj u v then (1 : ℝ) else 0) =
      s v (rowEquiv n G v) := by
    intro v
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u : Fin n => u < v)]
    have h0 : ∑ u ∈ Finset.univ.filter (fun u : Fin n => ¬ u < v),
        (if u < v ∧ G.Adj u v then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero (fun u hu => by
        simp only [Finset.mem_filter] at hu
        simp [hu.2])
    rw [h0, add_zero]
    unfold s
    symm
    refine Finset.sum_bij (fun (j : Fin v) _ => (⟨j.val, j.2.trans v.2⟩ : Fin n)) ?_ ?_ ?_ ?_
    · intro j _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.mk_lt_mk.mpr j.2
    · intro a _ b _ hab
      exact Fin.ext (by simpa using congrArg Fin.val hab)
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact ⟨⟨b.val, hb⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro j _
      have hj : (⟨j.val, j.2.trans v.2⟩ : Fin n) < v := Fin.mk_lt_mk.mpr j.2
      simp only [rowEquiv, Equiv.coe_fn_mk, decide_eq_true_eq, hj, true_and]
  have : (2 : ℝ) * G.edgeFinset.card = 2 * ∑ l : Fin n, s l (rowEquiv n G l) := by
    rw [h2]
    simp only [hdeg, hsplit, Finset.sum_add_distrib, hA, hrow]
    ring
  linarith

lemma Ex_row (n : ℕ) (p r : ℝ) (l : Fin n) (φ : ∀ l : Fin n, (Fin l → Bool) → ℝ) :
    Ex n p r (fun G => φ l (rowEquiv n G l)) = RE p r l (φ l) := by
  have := Ex_prod n p r {l} φ
  simpa using this

lemma Ex_edges (n : ℕ) (p r : ℝ) :
    Ex n p r (fun G => (G.edgeFinset.card : ℝ)) = ∑ l : Fin n, fS p r l := by
  simp only [card_edges]
  rw [Ex_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Ex_row n p r l (fun l => s l), first_moment]

lemma Ex_edges_sq (n : ℕ) (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1) :
    Ex n p r (fun G => (G.edgeFinset.card : ℝ) ^ 2) - (∑ l : Fin n, fS p r l) ^ 2 ≤
      n * (1 + (2 * fS p r n + 1) * fS p r n) := by
  have e1 : ∀ G : SimpleGraph (Fin n), (G.edgeFinset.card : ℝ) ^ 2 =
      ∑ l : Fin n, ∑ k : Fin n, s l (rowEquiv n G l) * s k (rowEquiv n G k) := by
    intro G
    rw [card_edges, sq, Finset.sum_mul_sum]
  simp only [e1]
  rw [Ex_sum]
  simp only [Ex_sum]
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  have hdiag : ∀ l : Fin n, ∑ k : Fin n,
      Ex n p r (fun G => s l (rowEquiv n G l) * s k (rowEquiv n G k)) -
        ∑ k : Fin n, fS p r l * fS p r k =
      RE p r l (fun y => s l y ^ 2) - fS p r l ^ 2 := by
    intro l
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single l]
    · have := Ex_row n p r l (fun l y => s l y ^ 2)
      simp only [sq] at this ⊢
      rw [this]
    · intro k _ hk
      have := Ex_prod n p r {l, k} (fun l y => s l y)
      simp only [Finset.prod_pair (Ne.symm hk)] at this
      rw [this, first_moment, first_moment, sub_self]
    · intro h; exact absurd (Finset.mem_univ l) h
  simp only [hdiag]
  calc ∑ l : Fin n, (RE p r l (fun y => s l y ^ 2) - fS p r l ^ 2)
      ≤ ∑ _l : Fin n, (1 + (2 * fS p r n + 1) * fS p r n) := by
        refine Finset.sum_le_sum (fun l _ => ?_)
        have := second_moment p r hp hp1 hr hr1 n l (le_of_lt l.2)
        nlinarith [sq_nonneg (fS p r l)]
    _ = _ := by simp; ring



/-- truncation: a function of the first `k` edges has the same mean under every longer row -/
lemma RE_trunc (p r : ℝ) (k : ℕ) (hk : 1 ≤ k) (h : (ℕ → Prop) → ℝ)
    (hh : ∀ x x' : ℕ → Prop, (∀ j < k, (x j ↔ x' j)) → h x = h x') :
    ∀ m, k ≤ m → RE p r m (fun y => h (X y)) = RE p r k (fun y => h (X y)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [RE_snoc p r m (by omega), ← ih]
    congr 1
    funext y
    have e : ∀ b : Bool, h (X (snocB y b)) = h (X y) := fun b =>
      hh _ _ (fun j hj => X_snoc_lt y b j (by omega))
    simp only [e]
    rw [← Finset.sum_mul]
    have := stepSum r (recSeq (1 - r) p (m - 1)) (X y (m - 1)) 1 0
    simp only [zero_mul, add_zero, mul_one] at this
    rw [this, one_mul]

lemma marg_any (p r : ℝ) (m j : ℕ) (hj : j < m) :
    RE p r m (fun y => if X y j then 1 else 0) = recSeq (1 - r) p j := by
  have := RE_trunc p r (j + 1) (by omega) (fun x => if x j then 1 else 0)
    (fun x x' hxx => by simp only [propext (hxx j (by omega))]) m hj
  rw [this]
  have hm := marg p r (j + 1) (by omega)
  exact hm

lemma prob_adj (n : ℕ) (p r : ℝ) (i j : Fin n) (hji : j < i) :
    rmrgProb n p r (fun G => G.Adj j i) = recSeq (1 - r) p j := by
  have h := Ex_row n p r i (fun l y => if X y j then 1 else 0)
  rw [marg_any p r i j hji] at h
  rw [← h]
  unfold rmrgProb Ex
  refine Finset.sum_congr rfl (fun G _ => ?_)
  congr 1
  have : G.Adj j i ↔ X (rowEquiv n G i) j := by
    simp only [X, rowEquiv, Equiv.coe_fn_mk, decide_eq_true_eq]
    exact ⟨fun h => ⟨hji, h⟩, fun ⟨_, h⟩ => h⟩
  simp only [this]

end RecMarkovGraph.IndepLB.T22Aux

open RecMarkovGraph.IndepLB RecMarkovGraph.IndepLB.T22Aux in
theorem solution (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (n : ℕ) (i j : Fin n) (hj : 1 ≤ (j : ℕ)) (hji : j < i) :
    rmrgProb n p r (fun G => G.Adj j i) =
      rmrgProb n p r (fun G => G.Adj ⟨(j : ℕ) - 1, by omega⟩ i) *
        (1 - (1 - r) * rmrgProb n p r (fun G => G.Adj ⟨(j : ℕ) - 1, by omega⟩ i)) := by
  rw [prob_adj n p r i j hji, prob_adj n p r i ⟨(j : ℕ) - 1, by omega⟩
    (by rw [Fin.lt_def] at hji ⊢; simp only; omega)]
  obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨(j : ℕ) - 1, by omega⟩
  simp only [hk, Nat.add_sub_cancel]
  rfl
