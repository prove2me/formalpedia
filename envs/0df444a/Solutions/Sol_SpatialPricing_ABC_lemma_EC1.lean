-- Prove2me | solution 1 for SpatialPricing.ABC.lemma_EC1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:10:23.467287+00:00
-- url     : https://prove2.me/submissions/eefa13a0-deb7-4f39-a85f-ee662cb7412e

import Mathlib
import Definitions.Def_SpatialPricing_ABC_Setting

open SpatialPricing.ABC

noncomputable section

namespace SPABCEC1

/-- Flip the bit of a path at period `u` (Fin index `u-1`) on arc `i0 → j0`. -/
def flipP (P : Instance) (u : Fin P.T) (i0 j0 : Fin P.N) (ω : P.Path) : P.Path :=
  fun s i j => if s = u ∧ i = i0 ∧ j = j0 then !ω s i j else ω s i j

lemma flipP_invol (P : Instance) (u : Fin P.T) (i0 j0 : Fin P.N) :
    Function.Involutive (flipP P u i0 j0) := by
  intro ω; funext s i j
  simp only [flipP]
  split_ifs <;> simp

lemma D_mem (P : Instance) (t : ℕ) (ω : P.Path) (i j : Fin P.N) :
    P.D t ω i j = 0 ∨ P.D t ω i j = 1 := by
  unfold Instance.D; split_ifs <;> simp

lemma D_flip_other (P : Instance) (u : ℕ) (hu1 : 1 ≤ u) (huT : u ≤ P.T)
    (i0 j0 : Fin P.N) (ω : P.Path) (t : ℕ) (i j : Fin P.N)
    (h : ¬ (t = u ∧ i = i0 ∧ j = j0)) :
    P.D t (flipP P ⟨u - 1, by omega⟩ i0 j0 ω) i j = P.D t ω i j := by
  unfold Instance.D
  split_ifs with h1 h2 h3 h3 h2 <;> simp only [flipP] at * <;>
    first
    | rfl
    | (exfalso
       rw [if_neg] at h2
       · exact h3 h2
       · rintro ⟨hs, hi, hj⟩
         apply h; refine ⟨?_, hi, hj⟩
         have := congrArg Fin.val hs; simp at this; omega)
    | (exfalso
       rw [if_neg] at h2
       · exact h2 h3
       · rintro ⟨hs, hi, hj⟩
         apply h; refine ⟨?_, hi, hj⟩
         have := congrArg Fin.val hs; simp at this; omega)

lemma D_flip_self (P : Instance) (u : ℕ) (hu1 : 1 ≤ u) (huT : u ≤ P.T)
    (i0 j0 : Fin P.N) (ω : P.Path) :
    P.D u (flipP P ⟨u - 1, by omega⟩ i0 j0 ω) i0 j0 = 1 - P.D u ω i0 j0 := by
  unfold Instance.D
  rw [dif_pos ⟨hu1, huT⟩, dif_pos ⟨hu1, huT⟩]
  simp only [flipP, and_self, if_true]
  cases ω ⟨u - 1, by omega⟩ i0 j0 <;> simp

/-- The factor of `pathProb` for coordinate `(t,i,j)`. -/
def fac (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (t : ℕ) (ω : P.Path)
    (i j : Fin P.N) : ℝ :=
  if P.D t ω i j = 1 then x t i j else 1 - x t i j

lemma pathProb_eq (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (ω : P.Path) :
    P.pathProb (fun t _ i j => x t i j) ω =
      ∏ t ∈ Finset.Icc 1 P.T, ∏ i, ∏ j, fac P x t ω i j := rfl

/-- The rest product, with coordinate `(u,i0,j0)` removed. -/
def rest (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (u : ℕ) (i0 j0 : Fin P.N)
    (ω : P.Path) : ℝ :=
  ∏ t ∈ Finset.Icc 1 P.T, ∏ i, ∏ j,
    if t = u ∧ i = i0 ∧ j = j0 then 1 else fac P x t ω i j

lemma pathProb_split (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (u : ℕ)
    (hu1 : 1 ≤ u) (huT : u ≤ P.T) (i0 j0 : Fin P.N) (ω : P.Path) :
    P.pathProb (fun t _ i j => x t i j) ω = fac P x u ω i0 j0 * rest P x u i0 j0 ω := by
  rw [pathProb_eq, rest]
  have : ∀ t i j, fac P x t ω i j =
      (if t = u ∧ i = i0 ∧ j = j0 then fac P x t ω i j else 1) *
      (if t = u ∧ i = i0 ∧ j = j0 then 1 else fac P x t ω i j) := by
    intro t i j; split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun t _ => Finset.prod_congr rfl
    (fun i _ => Finset.prod_congr rfl (fun j _ => this t i j)))]
  simp only [Finset.prod_mul_distrib]
  congr 1
  have hu : u ∈ Finset.Icc 1 P.T := Finset.mem_Icc.2 ⟨hu1, huT⟩
  rw [Finset.prod_eq_single_of_mem u hu]
  · rw [Finset.prod_eq_single_of_mem i0 (Finset.mem_univ _)]
    · rw [Finset.prod_eq_single_of_mem j0 (Finset.mem_univ _)]
      · simp
      · intro j _ hj; simp [hj]
    · intro i _ hi
      apply Finset.prod_eq_one; intro j _; simp [hi]
  · intro t _ ht
    apply Finset.prod_eq_one; intro i _
    apply Finset.prod_eq_one; intro j _; simp [ht]

lemma rest_flip (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (u : ℕ)
    (hu1 : 1 ≤ u) (huT : u ≤ P.T) (i0 j0 : Fin P.N) (ω : P.Path) :
    rest P x u i0 j0 (flipP P ⟨u - 1, by omega⟩ i0 j0 ω) = rest P x u i0 j0 ω := by
  unfold rest
  apply Finset.prod_congr rfl; intro t _
  apply Finset.prod_congr rfl; intro i _
  apply Finset.prod_congr rfl; intro j _
  split_ifs with h
  · rfl
  · unfold fac; rw [D_flip_other P u hu1 huT i0 j0 ω t i j h]

/-- Single-coordinate factorization. -/
lemma factor (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (u : ℕ)
    (hu1 : 1 ≤ u) (huT : u ≤ P.T) (i0 j0 : Fin P.N) (F : P.Path → ℝ)
    (hF : ∀ ω, F (flipP P ⟨u - 1, by omega⟩ i0 j0 ω) = F ω) :
    ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * (P.D u ω i0 j0 * F ω) =
      x u i0 j0 * ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * F ω := by
  set fl := flipP P ⟨u - 1, by omega⟩ i0 j0
  set R := rest P x u i0 j0
  set D0 : P.Path → ℝ := fun ω => P.D u ω i0 j0
  have hfac : ∀ ω, fac P x u ω i0 j0 =
      x u i0 j0 * D0 ω + (1 - x u i0 j0) * (1 - D0 ω) := by
    intro ω; unfold fac
    rcases D_mem P u ω i0 j0 with h | h <;> simp [D0, h]
  have hA : ∑ ω, D0 ω * R ω * F ω = ∑ ω, (1 - D0 ω) * R ω * F ω := by
    have e := Equiv.sum_comp (Function.Involutive.toPerm fl (flipP_invol P _ i0 j0))
      (fun ω => D0 ω * R ω * F ω)
    rw [← e]
    apply Finset.sum_congr rfl; intro ω _
    simp only [Function.Involutive.coe_toPerm, D0]
    rw [D_flip_self P u hu1 huT, show R (fl ω) = R ω from rest_flip P x u hu1 huT i0 j0 ω, hF]
  have lhs : ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * (P.D u ω i0 j0 * F ω) =
      x u i0 j0 * ∑ ω, D0 ω * R ω * F ω := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ω _
    rw [pathProb_split P x u hu1 huT i0 j0, hfac]
    rcases D_mem P u ω i0 j0 with h | h <;> simp [D0, h] <;> ring
  have rhs : ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * F ω =
      ∑ ω, D0 ω * R ω * F ω := by
    have : ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * F ω =
        x u i0 j0 * ∑ ω, D0 ω * R ω * F ω +
          (1 - x u i0 j0) * ∑ ω, (1 - D0 ω) * R ω * F ω := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro ω _
      rw [pathProb_split P x u hu1 huT i0 j0, hfac]; ring
    rw [this, ← hA]; ring
  rw [lhs, rhs]

/-! ### Total mass -/

lemma sum_prod3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (g : α → β → γ → Bool → ℝ) (hg : ∀ a b c, g a b c true + g a b c false = 1) :
    ∑ ω : α → β → γ → Bool, ∏ a, ∏ b, ∏ c, g a b c (ω a b c) = 1 := by
  calc ∑ ω : α → β → γ → Bool, ∏ a, ∏ b, ∏ c, g a b c (ω a b c)
      = ∏ a, ∑ v : β → γ → Bool, ∏ b, ∏ c, g a b c (v b c) :=
        (Fintype.prod_sum (fun a (v : β → γ → Bool) => ∏ b, ∏ c, g a b c (v b c))).symm
    _ = ∏ a, ∏ b, ∑ w : γ → Bool, ∏ c, g a b c (w c) := by
        apply Finset.prod_congr rfl; intro a _
        exact (Fintype.prod_sum (fun b (w : γ → Bool) => ∏ c, g a b c (w c))).symm
    _ = ∏ a, ∏ b, ∏ c, ∑ e : Bool, g a b c e := by
        apply Finset.prod_congr rfl; intro a _
        apply Finset.prod_congr rfl; intro b _
        exact (Fintype.prod_sum (fun c (e : Bool) => g a b c e)).symm
    _ = 1 := by simp [hg]

lemma Icc_eq_image (T : ℕ) :
    Finset.Icc 1 T = (Finset.univ : Finset (Fin T)).image (fun s => s.val + 1) := by
  ext t; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨t - 1, by omega⟩, by simp; omega⟩
  · rintro ⟨s, rfl⟩; exact ⟨by omega, s.2⟩

def gbit (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (s : Fin P.T) (i j : Fin P.N)
    (b : Bool) : ℝ :=
  if b then x (s.val + 1) i j else 1 - x (s.val + 1) i j

lemma total_mass (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) :
    ∑ ω, P.pathProb (fun t _ i j => x t i j) ω = 1 := by
  have h : ∀ ω : P.Path, P.pathProb (fun t _ i j => x t i j) ω =
      ∏ s : Fin P.T, ∏ i, ∏ j, gbit P x s i j (ω s i j) := by
    intro ω
    rw [pathProb_eq, Icc_eq_image, Finset.prod_image (by
      intro a _ b _ hab; exact Fin.ext (by simpa using hab))]
    apply Finset.prod_congr rfl; intro s _
    apply Finset.prod_congr rfl; intro i _
    apply Finset.prod_congr rfl; intro j _
    unfold fac Instance.D gbit
    rw [dif_pos ⟨by omega, s.2⟩]
    have : (⟨s.val + 1 - 1, by omega⟩ : Fin P.T) = s := Fin.ext (by simp)
    rw [this]
    cases ω s i j <;> simp
  rw [Finset.sum_congr rfl (fun ω _ => h ω)]
  exact sum_prod3 (gbit P x) (fun a b c => by simp [gbit])

lemma pathProb_nonneg (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ)
    (hx : ∀ t ∈ Finset.Icc 1 P.T, ∀ i j, 0 ≤ x t i j ∧ x t i j ≤ 1) (ω : P.Path) :
    0 ≤ P.pathProb (fun t _ i j => x t i j) ω := by
  rw [pathProb_eq]
  apply Finset.prod_nonneg; intro t ht
  apply Finset.prod_nonneg; intro i _
  apply Finset.prod_nonneg; intro j _
  unfold fac; obtain ⟨a, b⟩ := hx t ht i j
  split_ifs <;> linarith

/-! ### Exponential maximal inequality by backward induction -/

open Classical in
/-- Real indicator of a proposition. -/
def ind (p : Prop) : ℝ := if p then 1 else 0

lemma ind_nonneg (p : Prop) : 0 ≤ ind p := by unfold ind; split_ifs <;> norm_num

lemma ind_le_one (p : Prop) : ind p ≤ 1 := by unfold ind; split_ifs <;> norm_num

lemma ind_or_le (p q : Prop) : ind (p ∨ q) ≤ ind p + ind q := by
  unfold ind; split_ifs <;> simp_all

lemma ind_congr {p q : Prop} (h : p ↔ q) : ind p = ind q := by
  obtain rfl := propext h; rfl

/-- Exceedance event of the shifted partial sums started at `u`. -/
def Ev (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (i j : Fin P.N) (t2 : ℕ)
    (σ y : ℝ) (u : ℕ) (a : ℝ) (ω : P.Path) : Prop :=
  ∃ t ∈ Finset.Icc u t2, y < a + σ * ∑ s ∈ Finset.Icc u t, (P.D s ω i j - x s i j)

lemma Ev_succ (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (i j : Fin P.N) (t2 : ℕ)
    (σ y : ℝ) (u : ℕ) (hu : u ≤ t2) (a : ℝ) (ω : P.Path) :
    Ev P x i j t2 σ y u a ω ↔
      (y < a + σ * (P.D u ω i j - x u i j)) ∨
        Ev P x i j t2 σ y (u + 1) (a + σ * (P.D u ω i j - x u i j)) ω := by
  unfold Ev
  have hsplit : ∀ t, u ≤ t → ∑ s ∈ Finset.Icc u t, (P.D s ω i j - x s i j) =
      (P.D u ω i j - x u i j) + ∑ s ∈ Finset.Icc (u + 1) t, (P.D s ω i j - x s i j) := by
    intro t ht
    rw [← Finset.insert_Icc_add_one_left_eq_Icc ht, Finset.sum_insert (by simp)]
  constructor
  · rintro ⟨t, ht, hlt⟩
    rw [Finset.mem_Icc] at ht
    by_cases htu : t = u
    · subst htu; left; simpa using hlt
    · right
      refine ⟨t, Finset.mem_Icc.2 ⟨by omega, ht.2⟩, ?_⟩
      rw [hsplit t ht.1] at hlt; linarith
  · rintro (h | ⟨t, ht, hlt⟩)
    · exact ⟨u, Finset.mem_Icc.2 ⟨le_rfl, hu⟩, by simpa using h⟩
    · rw [Finset.mem_Icc] at ht
      refine ⟨t, Finset.mem_Icc.2 ⟨by omega, ht.2⟩, ?_⟩
      rw [hsplit t (by omega)]; linarith

lemma Ev_flip (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (i j : Fin P.N) (t2 : ℕ)
    (σ y : ℝ) (u : ℕ) (hu1 : 1 ≤ u) (huT : u ≤ P.T) (a : ℝ) (ω : P.Path) :
    Ev P x i j t2 σ y (u + 1) a (flipP P ⟨u - 1, by omega⟩ i j ω) ↔
      Ev P x i j t2 σ y (u + 1) a ω := by
  unfold Ev
  have : ∀ t, ∑ s ∈ Finset.Icc (u + 1) t,
      (P.D s (flipP P ⟨u - 1, by omega⟩ i j ω) i j - x s i j) =
      ∑ s ∈ Finset.Icc (u + 1) t, (P.D s ω i j - x s i j) := by
    intro t
    apply Finset.sum_congr rfl; intro s hs
    rw [Finset.mem_Icc] at hs
    rw [D_flip_other P u hu1 huT i j ω s i j (by omega)]
  simp only [this]

/-- One-step moment generating factor. -/
def mgf (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (i j : Fin P.N) (σ q : ℝ)
    (s : ℕ) : ℝ :=
  x s i j * Real.exp (q * σ * (1 - x s i j)) +
    (1 - x s i j) * Real.exp (q * σ * (0 - x s i j))

lemma mgf_ge_one (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ) (i j : Fin P.N)
    (σ q : ℝ) (s : ℕ) (h0 : 0 ≤ x s i j) (h1 : x s i j ≤ 1) : 1 ≤ mgf P x i j σ q s := by
  unfold mgf
  have e1 := Real.add_one_le_exp (q * σ * (1 - x s i j))
  have e2 := Real.add_one_le_exp (q * σ * (0 - x s i j))
  have : 0 ≤ 1 - x s i j := by linarith
  nlinarith [mul_le_mul_of_nonneg_left e1 h0, mul_le_mul_of_nonneg_left e2 this]

lemma prod_mgf_ge_one (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ)
    (hx : ∀ t ∈ Finset.Icc 1 P.T, ∀ i j, 0 ≤ x t i j ∧ x t i j ≤ 1)
    (i j : Fin P.N) (σ q : ℝ) (u t2 : ℕ) (hu : 1 ≤ u) (ht2 : t2 ≤ P.T) :
    1 ≤ ∏ s ∈ Finset.Icc u t2, mgf P x i j σ q s := by
  have := Finset.prod_le_prod (s := Finset.Icc u t2) (f := fun _ => (1 : ℝ))
    (g := fun s => mgf P x i j σ q s) (fun _ _ => zero_le_one) (fun s hs => by
      rw [Finset.mem_Icc] at hs
      obtain ⟨a, b⟩ := hx s (Finset.mem_Icc.2 ⟨by omega, by omega⟩) i j
      exact mgf_ge_one P x i j σ q s a b)
  simpa using this

lemma main_ind (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ)
    (hx : ∀ t ∈ Finset.Icc 1 P.T, ∀ i j, 0 ≤ x t i j ∧ x t i j ≤ 1)
    (i j : Fin P.N) (t2 : ℕ) (ht2 : t2 ≤ P.T) (σ y q : ℝ) (hq : 0 ≤ q) :
    ∀ k u, u + k = t2 + 1 → 1 ≤ u → ∀ a,
      ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * ind (Ev P x i j t2 σ y u a ω) ≤
        Real.exp (q * (a - y)) * ∏ s ∈ Finset.Icc u t2, mgf P x i j σ q s := by
  set w := fun ω => P.pathProb (fun t _ i j => x t i j) ω with hw
  have hw0 : ∀ ω, 0 ≤ w ω := pathProb_nonneg P x hx
  intro k
  induction k with
  | zero =>
    intro u hu _ a
    have hemp : Finset.Icc u t2 = ∅ := by
      rw [Finset.Icc_eq_empty_iff]; omega
    have : ∀ ω, ¬ Ev P x i j t2 σ y u a ω := by
      rintro ω ⟨t, ht, _⟩; rw [hemp] at ht; simp at ht
    simp [ind, this, hemp, Real.exp_nonneg]
  | succ k ih =>
    intro u hu hu1 a
    have hut2 : u ≤ t2 := by omega
    have huT : u ≤ P.T := by omega
    obtain ⟨xa, xb⟩ := hx u (Finset.mem_Icc.2 ⟨hu1, huT⟩) i j
    set xu := x u i j
    set a1 := a + σ * (1 - xu)
    set a0 := a + σ * (0 - xu)
    set G1 : P.Path → ℝ := fun ω => ind (y < a1 ∨ Ev P x i j t2 σ y (u + 1) a1 ω)
    set G0 : P.Path → ℝ := fun ω => ind (y < a0 ∨ Ev P x i j t2 σ y (u + 1) a0 ω)
    have hsplit : ∀ ω, ind (Ev P x i j t2 σ y u a ω) =
        P.D u ω i j * G1 ω + (G0 ω - P.D u ω i j * G0 ω) := by
      intro ω
      rw [ind_congr (Ev_succ P x i j t2 σ y u hut2 a ω)]
      rcases D_mem P u ω i j with h | h <;> rw [h] <;> simp [G1, G0, a1, a0, xu]
    have hG1 : ∀ ω, G1 (flipP P ⟨u - 1, by omega⟩ i j ω) = G1 ω := by
      intro ω; simp only [G1]; rw [ind_congr (or_congr Iff.rfl (Ev_flip P x i j t2 σ y u hu1 huT a1 ω))]
    have hG0 : ∀ ω, G0 (flipP P ⟨u - 1, by omega⟩ i j ω) = G0 ω := by
      intro ω; simp only [G0]; rw [ind_congr (or_congr Iff.rfl (Ev_flip P x i j t2 σ y u hu1 huT a0 ω))]
    have f1 := factor P x u hu1 huT i j G1 hG1
    have f0 := factor P x u hu1 huT i j G0 hG0
    have hsum : ∑ ω, w ω * ind (Ev P x i j t2 σ y u a ω) =
        xu * ∑ ω, w ω * G1 ω + (1 - xu) * ∑ ω, w ω * G0 ω := by
      simp only [hsplit, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [f1, f0]; ring
    set Pr := ∏ s ∈ Finset.Icc (u + 1) t2, mgf P x i j σ q s
    have hPr1 : 1 ≤ Pr := prod_mgf_ge_one P x hx i j σ q (u + 1) t2 (by omega) ht2
    have bound : ∀ a' : ℝ, ∑ ω, w ω * ind (y < a' ∨ Ev P x i j t2 σ y (u + 1) a' ω) ≤
        Real.exp (q * (a' - y)) * Pr := by
      intro a'
      by_cases hy : y < a'
      · have : ∀ ω, ind (y < a' ∨ Ev P x i j t2 σ y (u + 1) a' ω) = 1 := by
          intro ω; simp [ind, hy]
        simp only [this, mul_one]
        rw [total_mass]
        have : 1 ≤ Real.exp (q * (a' - y)) := Real.one_le_exp (by nlinarith)
        nlinarith
      · have : ∀ ω, ind (y < a' ∨ Ev P x i j t2 σ y (u + 1) a' ω) =
            ind (Ev P x i j t2 σ y (u + 1) a' ω) := by
          intro ω; apply ind_congr; simp [hy]
        simp only [this]
        exact ih (u + 1) (by omega) (by omega) a'
    have b1 := bound a1
    have b0 := bound a0
    have hprod : ∏ s ∈ Finset.Icc u t2, mgf P x i j σ q s = mgf P x i j σ q u * Pr := by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc hut2, Finset.prod_insert (by simp)]
    show ∑ ω, w ω * ind (Ev P x i j t2 σ y u a ω) ≤ _
    rw [hsum, hprod]
    have e1 : Real.exp (q * (a1 - y)) = Real.exp (q * (a - y)) * Real.exp (q * σ * (1 - xu)) := by
      rw [← Real.exp_add]; congr 1; simp only [a1]; ring
    have e0 : Real.exp (q * (a0 - y)) = Real.exp (q * (a - y)) * Real.exp (q * σ * (0 - xu)) := by
      rw [← Real.exp_add]; congr 1; simp only [a0]; ring
    have hxu1 : 0 ≤ 1 - xu := by linarith
    calc xu * ∑ ω, w ω * G1 ω + (1 - xu) * ∑ ω, w ω * G0 ω
        ≤ xu * (Real.exp (q * (a1 - y)) * Pr) + (1 - xu) * (Real.exp (q * (a0 - y)) * Pr) := by
          gcongr
      _ = Real.exp (q * (a - y)) * (mgf P x i j σ q u * Pr) := by
          rw [e1, e0]; unfold mgf; ring

/-! ### Bernoulli moment bound -/

lemma mgf_le (x z : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (hz : |z| ≤ 1) :
    x * Real.exp (z * (1 - x)) + (1 - x) * Real.exp (z * (0 - x)) ≤
      Real.exp (min x (1 - x) * z ^ 2) := by
  have hA := Real.abs_exp_sub_one_sub_id_le hz
  have hB := Real.abs_exp_sub_one_sub_id_le (x := -z) (by rwa [abs_neg])
  have hA' := (le_abs_self _).trans hA
  have hB' := (le_abs_self _).trans hB
  have e1 : Real.exp (z * (1 - x)) = Real.exp z * Real.exp (z * (0 - x)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (z * (0 - x)) = Real.exp (z * (1 - x)) * Real.exp (-z) := by
    rw [← Real.exp_add]; ring_nf
  have hx1 : 0 ≤ 1 - x := by linarith
  -- bound (A): by x z^2
  have bA : x * Real.exp (z * (1 - x)) + (1 - x) * Real.exp (z * (0 - x)) ≤
      Real.exp (x * z ^ 2) := by
    have : x * Real.exp (z * (1 - x)) + (1 - x) * Real.exp (z * (0 - x)) =
        Real.exp (z * (0 - x)) * (1 + x * (Real.exp z - 1)) := by rw [e1]; ring
    rw [this]
    have h := Real.add_one_le_exp (x * (Real.exp z - 1))
    calc Real.exp (z * (0 - x)) * (1 + x * (Real.exp z - 1))
        ≤ Real.exp (z * (0 - x)) * Real.exp (x * (Real.exp z - 1)) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = Real.exp (x * (Real.exp z - 1 - z)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (x * z ^ 2) := by
          apply Real.exp_le_exp.2; exact mul_le_mul_of_nonneg_left hA' h0
  have bB : x * Real.exp (z * (1 - x)) + (1 - x) * Real.exp (z * (0 - x)) ≤
      Real.exp ((1 - x) * z ^ 2) := by
    have : x * Real.exp (z * (1 - x)) + (1 - x) * Real.exp (z * (0 - x)) =
        Real.exp (z * (1 - x)) * (1 + (1 - x) * (Real.exp (-z) - 1)) := by rw [e2]; ring
    rw [this]
    have h := Real.add_one_le_exp ((1 - x) * (Real.exp (-z) - 1))
    calc Real.exp (z * (1 - x)) * (1 + (1 - x) * (Real.exp (-z) - 1))
        ≤ Real.exp (z * (1 - x)) * Real.exp ((1 - x) * (Real.exp (-z) - 1)) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = Real.exp ((1 - x) * (Real.exp (-z) - 1 - -z)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp ((1 - x) * z ^ 2) := by
          apply Real.exp_le_exp.2
          have : (-z) ^ 2 = z ^ 2 := by ring
          rw [this] at hB'
          exact mul_le_mul_of_nonneg_left hB' hx1
  rcases min_cases x (1 - x) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> assumption

lemma prod_mgf_le (P : Instance) (x : ℕ → Fin P.N → Fin P.N → ℝ)
    (hx : ∀ t ∈ Finset.Icc 1 P.T, ∀ i j, 0 ≤ x t i j ∧ x t i j ≤ 1)
    (i j : Fin P.N) (σ q : ℝ) (hσ : σ = 1 ∨ σ = -1) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (t1 t2 : ℕ) (ht1 : 1 ≤ t1) (ht2 : t2 ≤ P.T) :
    ∏ s ∈ Finset.Icc t1 t2, mgf P x i j σ q s ≤
      Real.exp ((∑ s ∈ Finset.Icc t1 t2, min (x s i j) (1 - x s i j)) * q ^ 2) := by
  rw [Finset.sum_mul, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro s hs
    rw [Finset.mem_Icc] at hs
    obtain ⟨a, b⟩ := hx s (Finset.mem_Icc.2 ⟨by omega, by omega⟩) i j
    exact (zero_le_one.trans (mgf_ge_one P x i j σ q s a b))
  · intro s hs
    rw [Finset.mem_Icc] at hs
    obtain ⟨a, b⟩ := hx s (Finset.mem_Icc.2 ⟨by omega, by omega⟩) i j
    have hz : |q * σ| ≤ 1 := by
      rcases hσ with rfl | rfl <;> simp [abs_of_pos hq0, hq1]
    have hz2 : (q * σ) ^ 2 = q ^ 2 := by rcases hσ with rfl | rfl <;> ring
    have := mgf_le (x s i j) (q * σ) a b hz
    rw [hz2] at this
    exact this

end SPABCEC1

open SPABCEC1 in
theorem solution (P : Instance)
    (x : ℕ → Fin P.N → Fin P.N → ℝ)
    (hx : ∀ t ∈ Finset.Icc 1 P.T, ∀ i j, 0 ≤ x t i j ∧ x t i j ≤ 1)
    (t1 t2 : ℕ) (ht1 : 1 ≤ t1) (ht12 : t1 < t2) (ht2 : t2 ≤ P.T)
    (i j : Fin P.N) (y q : ℝ) (hy : 0 ≤ y) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    let π : ℕ → P.Path → Fin P.N → Fin P.N → ℝ := fun t _ i j => x t i j
    let S : P.Path → Prop := fun ω =>
      ∃ t ∈ Finset.Icc t1 t2,
        y < |∑ s ∈ Finset.Icc t1 t, (P.D s ω i j - x s i j)|
    P.prob π S ≤
      2 * Real.exp ((∑ s ∈ Finset.Icc t1 t2,
        min (x s i j) (1 - x s i j)) * q ^ 2 - q * y) ∧
    2 * Real.exp ((∑ s ∈ Finset.Icc t1 t2,
      min (x s i j) (1 - x s i j)) * q ^ 2 - q * y) ≤
        2 * Real.exp (((t2 - t1 : ℕ) : ℝ) * q ^ 2 - q * y) := by
  intro π S
  set V := ∑ s ∈ Finset.Icc t1 t2, min (x s i j) (1 - x s i j) with hV
  constructor
  · have hprob : P.prob π S = ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * ind (S ω) := by
      unfold Instance.prob
      apply Finset.sum_congr rfl; intro ω _
      unfold ind; split_ifs <;> simp [π]
    have hS : ∀ ω, ind (S ω) ≤ ind (Ev P x i j t2 1 y t1 0 ω) +
        ind (Ev P x i j t2 (-1) y t1 0 ω) := by
      intro ω
      refine le_trans (le_of_eq (ind_congr ?_)) (ind_or_le _ _)
      simp only [S, Ev, lt_abs, zero_add, one_mul, neg_one_mul]
      constructor
      · rintro ⟨t, ht, h | h⟩
        · exact Or.inl ⟨t, ht, h⟩
        · exact Or.inr ⟨t, ht, h⟩
      · rintro (⟨t, ht, h⟩ | ⟨t, ht, h⟩)
        · exact ⟨t, ht, Or.inl h⟩
        · exact ⟨t, ht, Or.inr h⟩
    have hk : t1 + (t2 + 1 - t1) = t2 + 1 := by omega
    have bp := main_ind P x hx i j t2 ht2 1 y q hq0.le (t2 + 1 - t1) t1 hk ht1 0
    have bm := main_ind P x hx i j t2 ht2 (-1) y q hq0.le (t2 + 1 - t1) t1 hk ht1 0
    have pp := prod_mgf_le P x hx i j 1 q (Or.inl rfl) hq0 hq1 t1 t2 ht1 ht2
    have pm := prod_mgf_le P x hx i j (-1) q (Or.inr rfl) hq0 hq1 t1 t2 ht1 ht2
    rw [← hV] at pp pm
    have hw0 := pathProb_nonneg P x hx
    have hsum : ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * ind (S ω) ≤
        ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * ind (Ev P x i j t2 1 y t1 0 ω) +
        ∑ ω, P.pathProb (fun t _ i j => x t i j) ω * ind (Ev P x i j t2 (-1) y t1 0 ω) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro ω _
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hS ω) (hw0 ω)
    have he : Real.exp (q * (0 - y)) * Real.exp (V * q ^ 2) = Real.exp (V * q ^ 2 - q * y) := by
      rw [← Real.exp_add]; ring_nf
    have hepos := (Real.exp_pos (q * (0 - y))).le
    rw [hprob]
    nlinarith [mul_le_mul_of_nonneg_left pp hepos, mul_le_mul_of_nonneg_left pm hepos]
  · have hmin : V ≤ ((t2 - t1 : ℕ) : ℝ) := by
      have : V ≤ ∑ _s ∈ Finset.Icc t1 t2, (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum; intro s _
        rcases min_cases (x s i j) (1 - x s i j) with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] <;> linarith
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
      have h2 : ((t2 + 1 - t1 : ℕ) : ℝ) = ((t2 - t1 : ℕ) : ℝ) + 1 := by
        rw [show t2 + 1 - t1 = (t2 - t1) + 1 by omega]; push_cast; ring
      have h3 : (1 : ℝ) ≤ ((t2 - t1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ t2 - t1 by omega)
      rw [h2] at this; linarith
    have : V * q ^ 2 - q * y ≤ ((t2 - t1 : ℕ) : ℝ) * q ^ 2 - q * y := by
      have := mul_le_mul_of_nonneg_right hmin (sq_nonneg q); linarith
    have := Real.exp_le_exp.2 this
    linarith

end
