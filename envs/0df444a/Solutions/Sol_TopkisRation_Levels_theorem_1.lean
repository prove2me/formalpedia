-- Prove2me | solution 1 for TopkisRation.Levels.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T08:42:29.384613+00:00
-- url     : https://prove2.me/submissions/31a57d3f-99f4-459e-9e98-46af6095bbcf

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model
import Definitions.Def_TopkisRation_Levels_Split
import Theorems.Thm_TopkisRation_Levels_lemma_2
import Theorems.Thm_TopkisRation_Levels_lemma_3
import Theorems.Thm_TopkisRation_Levels_lemma_4
import Theorems.Thm_TopkisRation_Levels_eq_6
import Theorems.Thm_TopkisRation_Levels_criticalLevel_exists

set_option autoImplicit false

namespace T1Aux

open TopkisRation.Levels

/-! ## Generic one-dimensional facts -/

/-- The clamp of a critical level `zb` into `[l, r]` (`r` when `zb = ⊤`). -/
noncomputable def cl (zb : WithTop ℝ) (l r : ℝ) : ℝ :=
  WithTop.untopD r (zb.map fun x => max (min x r) l)

lemma cl_top (l r : ℝ) : cl ⊤ l r = r := by simp [cl]

lemma cl_coe (x l r : ℝ) : cl (x : WithTop ℝ) l r = max (min x r) l := by
  unfold cl; rw [WithTop.map_coe, WithTop.untopD_coe]

lemma clamp_id (φ : ℝ → ℝ) {l r : ℝ} (hlr : l ≤ r) (x : ℝ) :
    φ (max (min x r) l) = φ (max x l) + φ (min x r) - φ x := by
  rcases le_total x l with h | h
  · rw [min_eq_left (h.trans hlr), max_eq_right h]; ring
  · rcases le_total x r with h' | h'
    · rw [min_eq_left h', max_eq_left h]; ring
    · rw [min_eq_right h', max_eq_left hlr, max_eq_left h]; ring

lemma conv_anti {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Ici 0) φ) {x0 : ℝ}
    (hmin : ∀ y, 0 ≤ y → φ x0 ≤ φ y) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ x0) :
    φ b ≤ φ a := by
  rcases hab.lt_or_eq with hab | rfl
  · rcases hb.lt_or_eq with hb | rfl
    · have h0 := hφ.slope_mono_adjacent (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (by linarith)) hab hb
      have h1 : φ x0 - φ b ≤ 0 := by linarith [hmin b (by linarith)]
      have h2 : (φ x0 - φ b) / (x0 - b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 (by linarith)
      have h3 : (φ b - φ a) / (b - a) ≤ 0 := h0.trans h2
      have h4 := (div_le_iff₀ (by linarith : (0:ℝ) < b - a)).mp h3
      linarith
    · exact hmin a ha
  · exact le_refl _

lemma conv_mono {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Ici 0) φ) {x0 : ℝ} (hx0 : 0 ≤ x0)
    (hmin : ∀ y, 0 ≤ y → φ x0 ≤ φ y) {a b : ℝ} (ha : x0 ≤ a) (hab : a ≤ b) :
    φ a ≤ φ b := by
  rcases ha.lt_or_eq with ha | rfl
  · rcases hab.lt_or_eq with hab | rfl
    · have h0 := hφ.slope_mono_adjacent (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (by linarith)) ha hab
      have h1 : 0 ≤ (φ a - φ x0) / (a - x0) :=
        div_nonneg (by linarith [hmin a (by linarith)]) (by linarith)
      have h3 := h1.trans h0
      have h4 := (le_div_iff₀ (by linarith : (0:ℝ) < b - a)).mp h3
      linarith
    · exact le_refl _
  · exact hmin b (by linarith)

/-- Unimodality: the clamped critical level minimises `φ` over `[l, r] ∩ [0, ∞)`. -/
lemma cl_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Ici 0) φ) {zb : WithTop ℝ}
    (hz : IsCriticalLevel φ zb) {l r v : ℝ} (hlv : l ≤ v) (hvr : v ≤ r) (hv : 0 ≤ v) :
    φ (cl zb l r) ≤ φ v := by
  rcases hz with ⟨rfl, hanti⟩ | ⟨x0, rfl, hx0, hmin, -⟩
  · rw [cl_top]
    exact hanti.antitoneOn (Set.mem_Ici.2 hv) (Set.mem_Ici.2 (hv.trans hvr)) hvr
  · rw [cl_coe]
    rcases le_total x0 r with h1 | h1
    · rw [min_eq_left h1]
      rcases le_total x0 l with h2 | h2
      · rw [max_eq_right h2]; exact conv_mono hφ hx0 hmin h2 hlv
      · rw [max_eq_left h2]; exact hmin v hv
    · rw [min_eq_right h1, max_eq_left (hlv.trans hvr)]; exact conv_anti hφ hmin hv hvr h1

lemma crit_nonneg {φ : ℝ → ℝ} {zb : WithTop ℝ} (hz : IsCriticalLevel φ zb) {x : ℝ}
    (hx : zb = (x : WithTop ℝ)) : 0 ≤ x := by
  rcases hz with ⟨h, -⟩ | ⟨x0, h, hx0, -, -⟩
  · rw [h] at hx; exact absurd hx.symm (WithTop.coe_ne_top)
  · rw [h] at hx; rw [← WithTop.coe_eq_coe.1 hx]; exact hx0

lemma cl_mem {zb : WithTop ℝ} {l r : ℝ} (hlr : l ≤ r) : l ≤ cl zb l r ∧ cl zb l r ≤ r := by
  induction zb using WithTop.recTopCoe with
  | top => rw [cl_top]; exact ⟨hlr, le_rfl⟩
  | coe x => rw [cl_coe]; exact ⟨le_max_right _ _, max_le (min_le_right _ _) hlr⟩

/-! ## Tail sums -/

variable {n : ℕ}

lemma nn {B : Fin n → ℝ} (hB : 0 ≤ B) (i : Fin n) : 0 ≤ B i := hB i

def T (B : Fin n → ℝ) (m : ℕ) : ℝ := ∑ i : Fin n, if m ≤ i.val then B i else 0

lemma tailSum_eq (B : Fin n → ℝ) (j : Fin n) : tailSum B j = T B j.val := by
  unfold tailSum T
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_Ici, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]

lemma T_zero (B : Fin n → ℝ) : T B 0 = ∑ j, B j := by
  unfold T; apply Finset.sum_congr rfl; intro i _; rw [if_pos (Nat.zero_le _)]

lemma T_top (B : Fin n → ℝ) : T B n = 0 := by
  unfold T
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg (not_le.2 i.isLt)]

lemma T_succ (B : Fin n → ℝ) (j : Fin n) : T B j.val = B j + T B (j.val + 1) := by
  unfold T
  rw [show B j = ∑ i : Fin n, if i = j then B i else 0 by simp, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : i = j
  · subst h1; simp
  · have : i.val ≠ j.val := fun h => h1 (Fin.ext h)
    by_cases h2 : j.val + 1 ≤ i.val
    · rw [if_pos (by omega), if_neg h1, if_pos h2]; ring
    · rw [if_neg (by omega), if_neg h1, if_neg h2]; ring

lemma T_mono {B : Fin n → ℝ} (hB : 0 ≤ B) {m m' : ℕ} (h : m ≤ m') : T B m' ≤ T B m := by
  unfold T
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h1 h2 <;> first | exact le_rfl | exact hB i | omega

lemma T_nonneg {B : Fin n → ℝ} (hB : 0 ≤ B) (m : ℕ) : 0 ≤ T B m := by
  unfold T
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hB i
  · exact le_rfl

lemma T_add_single (B : Fin n → ℝ) (j : Fin n) (ε : ℝ) (m : ℕ) :
    T (B + ε • Pi.single j 1) m = T B m + (if m ≤ j.val then ε else 0) := by
  unfold T
  rw [show (if m ≤ j.val then ε else 0) =
      ∑ i : Fin n, if i = j then (if m ≤ i.val then ε else 0) else 0 by simp,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : i = j
  · subst h1; simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      if_true]
    split_ifs <;> ring
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne h1, smul_eq_mul, mul_zero,
      add_zero, if_neg h1]

lemma T_congr {B B' : Fin n → ℝ} {j : Fin n} (hBB : ∀ i, j < i → B i = B' i) {m : ℕ}
    (hm : j.val < m) : T B m = T B' m := by
  unfold T
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · exact hBB i (by rw [Fin.lt_def]; omega)
  · rfl

/-! ## uVec and rationU in clamp form -/

lemma uVec_eq {B : Fin n → ℝ} (hB : 0 ≤ B) (z w : ℝ) (i : Fin n) :
    uVec (z - w) B i = max (min w (z - T B (i.val + 1))) (z - T B i.val) - (z - T B i.val) := by
  simp only [uVec, tailSum_eq]
  have h1 := T_succ B i
  have h2 := nn hB i
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma uVec_zero {B : Fin n → ℝ} (hB : 0 ≤ B) : uVec 0 B = B := by
  funext i
  have h := uVec_eq hB 0 0 i
  rw [sub_zero] at h
  rw [h]
  have h1 := T_succ B i
  have h2 := nn hB i
  have h3 := T_nonneg hB (i.val + 1)
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma uVec_nonneg {B : Fin n → ℝ} (hB : 0 ≤ B) (s : ℝ) : 0 ≤ uVec s B := by
  intro i
  simp only [uVec, Pi.zero_apply]
  exact le_min (le_max_right _ _) (hB i)

lemma rationU_eq {B : Fin n → ℝ} (hB : 0 ≤ B) (zbar : Fin n → WithTop ℝ) (z : ℝ) (i : Fin n) :
    rationU zbar z B i = cl (zbar i) (z - T B i.val) (z - T B (i.val + 1)) - (z - T B i.val) := by
  have h1 := T_succ B i
  have h2 := nn hB i
  unfold rationU
  induction zbar i using WithTop.recTopCoe with
  | top => simp only [WithTop.map_top, WithTop.untopD_top, cl_top]; linarith
  | coe x =>
    simp only [WithTop.map_coe, WithTop.untopD_coe, cl_coe, tailSum_eq]
    simp only [min_def, max_def]
    split_ifs <;> linarith

/-- On the class-`j` segment of the issuing path, `uVec` is explicit. -/
lemma uVec_seg {B : Fin n → ℝ} (hB : 0 ≤ B) {z x : ℝ} (j : Fin n)
    (hlx : z - T B j.val ≤ x) (hxr : x ≤ z - T B (j.val + 1)) (i : Fin n) :
    uVec (z - x) B i = if i < j then B i else if i = j then x - (z - T B j.val) else 0 := by
  rw [uVec_eq hB]
  have hi := T_succ B i
  have hbi := nn hB i
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_pos h]
    have : T B j.val ≤ T B (i.val + 1) := T_mono hB (by rw [Fin.lt_def] at h; omega)
    simp only [min_def, max_def]
    split_ifs <;> linarith
  · simp only [lt_irrefl, if_false, if_true]
    simp only [min_def, max_def]
    split_ifs <;> linarith
  · rw [if_neg (not_lt.2 h.le), if_neg (Fin.ne_of_gt h)]
    have : T B i.val ≤ T B (j.val + 1) := T_mono hB (by rw [Fin.lt_def] at h; omega)
    simp only [min_def, max_def]
    split_ifs <;> linarith

end T1Aux

/-! ## Part 2: the model -/

namespace T1Aux

open TopkisRation.Levels MeasureTheory

variable {n : ℕ}

lemma single_nonneg (j : Fin n) {x : ℝ} (hx : 0 ≤ x) : (0 : Fin n → ℝ) ≤ x • Pi.single j 1 := by
  intro i
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs
  · simpa using hx
  · simp

lemma single_gt (j : Fin n) (x : ℝ) {i : Fin n} (h : j < i) : (x • Pi.single j (1 : ℝ)) i = 0 := by
  simp [Pi.single_apply, ne_of_gt h]

lemma lr_le {B : Fin n → ℝ} (hB : 0 ≤ B) (z : ℝ) (j : Fin n) :
    z - T B j.val ≤ z - T B (j.val + 1) := by
  linarith [T_succ B j, nn hB j]

noncomputable def Fv (M : Model n) (s : ℕ) (z : ℝ) (B : Fin n → ℝ) (w : ℝ) : ℝ :=
  M.p s ⬝ᵥ uVec (z - w) B + M.g (s - 1) w (M.a s • uVec (z - w) B) + M.h s w

def CG (M : Model n) (s : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ j : Fin n, ∀ z : ℝ, 0 ≤ z → ∀ b b' : Fin n → ℝ, 0 ≤ b → 0 ≤ b' →
    (∀ i, j < i → b i = b' i) →
    M.g s z b - M.g s (z + ε) (b + ε • Pi.single j 1) =
      M.g s z b' - M.g s (z + ε) (b' + ε • Pi.single j 1)

def CF (M : Model n) (s : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ j : Fin n, ∀ z : ℝ, 0 ≤ z → ∀ B B' : Fin n → ℝ, 0 ≤ B → 0 ≤ B' →
    (∀ i, j < i → B i = B' i) →
    M.f s z B - M.f s (z + ε) (B + ε • Pi.single j 1) =
      M.f s z B' - M.f s (z + ε) (B' + ε • Pi.single j 1)

lemma seg (M : Model n) (s : ℕ) (ha : M.a s = 0 ∨ M.a s = 1) (hC : CG M (s - 1))
    {B : Fin n → ℝ} (hB : 0 ≤ B) {z : ℝ} (j : Fin n) {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y)
    (hlx : z - T B j.val ≤ x) (hyr : y ≤ z - T B (j.val + 1)) :
    Fv M s z B x - Fv M s z B y = M.levelObj s j x - M.levelObj s j y := by
  set U := uVec (z - x) B with hUdef
  have hUy : uVec (z - y) B = U + (y - x) • Pi.single j 1 := by
    funext i
    rw [uVec_seg hB j (hlx.trans hxy) hyr i, hUdef, Pi.add_apply,
      uVec_seg hB j hlx (hxy.trans hyr) i]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with h1 h2 h2
    · exact absurd h1 (by rw [h2]; exact lt_irrefl _)
    · ring
    · ring
    · ring
  have hU0 : 0 ≤ U := uVec_nonneg hB _
  have hUgt : ∀ i, j < i → U i = 0 := by
    intro i hi
    rw [hUdef, uVec_seg hB j hlx (hxy.trans hyr) i, if_neg (not_lt.2 hi.le), if_neg (ne_of_gt hi)]
  unfold Fv Model.levelObj
  rw [hUy]
  have hp : M.p s ⬝ᵥ (U + (y - x) • Pi.single j 1) = M.p s ⬝ᵥ U + (y - x) * M.p s j := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
  rw [hp]
  rcases ha with ha | ha
  · rw [ha]; simp only [zero_smul]; ring
  · rw [ha]; simp only [one_smul]
    rcases hxy.lt_or_eq with hlt | heq
    · have h := hC (y - x) (by linarith) j x hx0 U (x • Pi.single j 1) hU0 (single_nonneg j hx0)
        (fun i hi => by rw [hUgt i hi, single_gt j x hi])
      rw [show x + (y - x) = y by ring,
        show x • Pi.single j (1:ℝ) + (y - x) • Pi.single j 1 = y • Pi.single j 1 by
          rw [← add_smul]; congr 1; ring] at h
      linarith
    · subst heq; rw [← hUdef]; simp

lemma path (M : Model n) (s : ℕ) (ha : M.a s = 0 ∨ M.a s = 1) (hC : CG M (s - 1))
    {B : Fin n → ℝ} (hB : 0 ≤ B) {z w : ℝ} (hw0 : 0 ≤ w) (hwL : z - ∑ j, B j ≤ w)
    (hwz : w ≤ z) :
    Fv M s z B w = Fv M s z B z + ∑ j : Fin n,
      (M.levelObj s j (max (min w (z - T B (j.val + 1))) (z - T B j.val)) -
        M.levelObj s j (z - T B (j.val + 1))) := by
  set P : ℕ → ℝ := fun m => max w (z - T B m) with hP
  have key : ∀ j : Fin n, Fv M s z B (P j.val) - Fv M s z B (P (j.val + 1)) =
      M.levelObj s j (max (min w (z - T B (j.val + 1))) (z - T B j.val)) -
        M.levelObj s j (z - T B (j.val + 1)) := by
    intro j
    have hlr := lr_le hB z j
    simp only [hP]
    rcases le_total w (z - T B (j.val + 1)) with h | h
    · rw [max_eq_right h, min_eq_left h]
      exact seg M s ha hC hB j (le_max_of_le_left hw0) (max_le h hlr) (le_max_right _ _) le_rfl
    · rw [max_eq_left h, max_eq_left (hlr.trans h), min_eq_right h, max_eq_left hlr]
      ring
  have htel : ∑ j : Fin n, (Fv M s z B (P j.val) - Fv M s z B (P (j.val + 1))) =
      Fv M s z B (P 0) - Fv M s z B (P n) :=
    (Fin.sum_univ_eq_sum_range (fun m => Fv M s z B (P m) - Fv M s z B (P (m + 1))) n).trans
      (Finset.sum_range_sub' _ n)
  have hP0 : P 0 = w := by simp only [hP, T_zero]; exact max_eq_left hwL
  have hPn : P n = z := by simp only [hP, T_top, sub_zero]; exact max_eq_right hwz
  rw [hP0, hPn] at htel
  rw [← Finset.sum_congr rfl (fun j _ => key j), htel]
  ring

/-! ### The nested point `wstar` -/

lemma top_or_coe (x : WithTop ℝ) : x = ⊤ ∨ ∃ a : ℝ, x = (a : WithTop ℝ) := by
  induction x using WithTop.recTopCoe with
  | top => exact Or.inl rfl
  | coe a => exact Or.inr ⟨a, rfl⟩

noncomputable def cc (B : Fin n → ℝ) (z : ℝ) (zbar : Fin n → WithTop ℝ) (j : Fin n) : ℝ :=
  cl (zbar j) (z - T B j.val) (z - T B (j.val + 1))

noncomputable def wstar (B : Fin n → ℝ) (z : ℝ) (zbar : Fin n → WithTop ℝ) : ℝ :=
  z - ∑ i, ((z - T B (i.val + 1)) - cc B z zbar i)

section Cons

variable {B : Fin n → ℝ} (hB : 0 ≤ B) {z : ℝ} {zbar : Fin n → WithTop ℝ}
  (hanti : Antitone zbar) (hzz : ∀ j (x : ℝ), zbar j = (x : WithTop ℝ) → 0 ≤ x)
include hB

lemma cc_mem (j : Fin n) : z - T B j.val ≤ cc B z zbar j ∧ cc B z zbar j ≤ z - T B (j.val + 1) :=
  cl_mem (lr_le hB z j)

include hzz in
lemma cc_ge (j : Fin n) : min 0 (z - T B (j.val + 1)) ≤ cc B z zbar j := by
  unfold cc
  rcases top_or_coe (zbar j) with h | ⟨x, h⟩
  · rw [h, cl_top]; exact min_le_right _ _
  · rw [h, cl_coe]
    have hx := hzz j x h
    exact (min_le_min_right _ hx).trans (le_max_left _ _)

include hanti in
lemma nest {i j : Fin n} (hij : i < j) (h : cc B z zbar i < z - T B (i.val + 1)) :
    cc B z zbar j = z - T B j.val := by
  have hij' : i.val + 1 ≤ j.val := by rw [Fin.lt_def] at hij; omega
  have hT : T B j.val ≤ T B (i.val + 1) := T_mono hB hij'
  unfold cc at h
  rcases top_or_coe (zbar i) with hi | ⟨xi, hi⟩
  · rw [hi, cl_top] at h; exact absurd h (lt_irrefl _)
  · rw [hi, cl_coe] at h
    have hxi : xi < z - T B (i.val + 1) := by
      by_contra hc
      push_neg at hc
      rw [min_eq_right hc] at h
      exact absurd h (not_lt.2 (le_max_left _ _))
    have hle : zbar j ≤ zbar i := hanti hij.le
    rcases top_or_coe (zbar j) with hj | ⟨xj, hj⟩
    · rw [hj, hi] at hle; exact absurd hle (by simp)
    · rw [hj, hi, WithTop.coe_le_coe] at hle
      unfold cc
      rw [hj, cl_coe]
      have : min xj (z - T B (j.val + 1)) ≤ z - T B j.val :=
        (min_le_left _ _).trans (by linarith)
      exact max_eq_right this

include hanti in
lemma nest' {i j : Fin n} (hij : i < j) (h : z - T B j.val < cc B z zbar j) :
    cc B z zbar i = z - T B (i.val + 1) := by
  by_contra hc
  have hlt := lt_of_le_of_ne (cc_mem hB i).2 hc
  rw [nest hB hanti hij hlt] at h
  exact lt_irrefl _ h

lemma sum_split (j : Fin n) (c : ℝ) :
    c + T B (j.val + 1) =
      ∑ i : Fin n, ((if i = j then c else 0) + (if j.val + 1 ≤ i.val then B i else 0)) := by
  rw [Finset.sum_add_distrib]
  simp [T]

include hanti in
lemma wstar_le (j : Fin n) (h : cc B z zbar j < z - T B (j.val + 1)) :
    wstar B z zbar ≤ cc B z zbar j := by
  unfold wstar
  have hsum : ((z - T B (j.val + 1)) - cc B z zbar j) + T B (j.val + 1) ≤
      ∑ i, ((z - T B (i.val + 1)) - cc B z zbar i) := by
    rw [sum_split hB j]
    apply Finset.sum_le_sum
    intro i _
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_neg (ne_of_lt hij), if_neg (by rw [Fin.lt_def] at hij; omega)]
      linarith [(cc_mem hB (z := z) (zbar := zbar) i).2]
    · simp
    · rw [if_neg (ne_of_gt hij), if_pos (by rw [Fin.lt_def] at hij; omega),
        nest hB hanti hij h]
      linarith [T_succ B i]
  linarith

include hanti in
lemma wstar_ge (j : Fin n) (h : z - T B j.val < cc B z zbar j) :
    cc B z zbar j ≤ wstar B z zbar := by
  unfold wstar
  have hsum : ∑ i, ((z - T B (i.val + 1)) - cc B z zbar i) ≤
      ((z - T B (j.val + 1)) - cc B z zbar j) + T B (j.val + 1) := by
    rw [sum_split hB j]
    apply Finset.sum_le_sum
    intro i _
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_neg (ne_of_lt hij), if_neg (by rw [Fin.lt_def] at hij; omega),
        nest' hB hanti hij h]
      simp
    · simp
    · rw [if_neg (ne_of_gt hij), if_pos (by rw [Fin.lt_def] at hij; omega)]
      linarith [T_succ B i, (cc_mem hB (z := z) (zbar := zbar) i).1]
  linarith

include hanti in
lemma wstar_clamp (j : Fin n) :
    max (min (wstar B z zbar) (z - T B (j.val + 1))) (z - T B j.val) = cc B z zbar j := by
  obtain ⟨h1, h2⟩ := cc_mem hB (z := z) (zbar := zbar) j
  rcases h1.lt_or_eq with h1 | h1 <;> rcases h2.lt_or_eq with h2 | h2
  · have := wstar_le hB hanti j h2
    have := wstar_ge hB hanti j h1
    simp only [min_def, max_def]; split_ifs <;> linarith
  · have := wstar_ge hB hanti j h1
    simp only [min_def, max_def]; split_ifs <;> linarith
  · have := wstar_le hB hanti j h2
    simp only [min_def, max_def]; split_ifs <;> linarith
  · simp only [min_def, max_def]; split_ifs <;> linarith

lemma wstar_le_z : wstar B z zbar ≤ z := by
  unfold wstar
  have : 0 ≤ ∑ i, ((z - T B (i.val + 1)) - cc B z zbar i) :=
    Finset.sum_nonneg (fun i _ => by linarith [(cc_mem hB (z := z) (zbar := zbar) i).2])
  linarith

lemma wstar_ge_L : z - ∑ j, B j ≤ wstar B z zbar := by
  unfold wstar
  have : ∑ i, ((z - T B (i.val + 1)) - cc B z zbar i) ≤ ∑ i, B i :=
    Finset.sum_le_sum (fun i _ => by
      linarith [(cc_mem hB (z := z) (zbar := zbar) i).1, T_succ B i])
  linarith

include hanti hzz in
lemma wstar_nonneg (hz : 0 ≤ z) : 0 ≤ wstar B z zbar := by
  have key : ∀ m, m ≤ n → min 0 (z - T B m) ≤ wstar B z zbar := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [T_zero]
      exact (min_le_right _ _).trans (wstar_ge_L hB)
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      set j : Fin n := ⟨m, by omega⟩ with hj
      have e1 : T B j.val = T B m := rfl
      have e2 : T B (j.val + 1) = T B (m + 1) := rfl
      have hjr := cc_mem hB (z := z) (zbar := zbar) j
      have hcg := cc_ge hB hzz (z := z) j
      rw [e1, e2] at hjr
      rw [e2] at hcg
      rcases le_total (z - T B (m + 1)) 0 with hr | hr
      · rw [min_eq_right hr]
        rw [min_eq_right hr] at hcg
        rcases hjr.1.lt_or_eq with hlt | heq
        · have := wstar_ge hB hanti j hlt
          linarith
        · have h' := ih
          rw [min_eq_right (by linarith)] at h'
          linarith
      · rw [min_eq_left hr]
        rw [min_eq_left hr] at hcg
        rcases le_total 0 (z - T B m) with hl | hl
        · have h' := ih
          rw [min_eq_left hl] at h'
          exact h'
        · rcases hjr.1.lt_or_eq with hlt | heq
          · have := wstar_ge hB hanti j hlt
            linarith
          · have h' := ih
            rw [min_eq_right hl] at h'
            linarith
  have := key n le_rfl
  rw [T_top, sub_zero, min_eq_left hz] at this
  exact this

include hanti in
lemma rationU_wstar : rationU zbar z B = uVec (z - wstar B z zbar) B := by
  funext i
  rw [rationU_eq hB, uVec_eq hB, wstar_clamp hB hanti]
  rfl

include hzz in
lemma cc_eq_r (j : Fin n) (hr : z - T B (j.val + 1) ≤ 0) : cc B z zbar j = z - T B (j.val + 1) := by
  have h1 := cc_ge hB hzz (z := z) j
  rw [min_eq_right hr] at h1
  exact le_antisymm (cc_mem hB j).2 h1

end Cons

end T1Aux

/-! ## Part 3: the stage step -/

namespace T1Aux

open TopkisRation.Levels MeasureTheory

variable {n : ℕ}

lemma phi_convex (M : Model n) (hM : M.Standing) {s : ℕ} (hs : s ∈ Finset.Icc 1 M.k) (j : Fin n) :
    ConvexOn ℝ (Set.Ici 0) (M.levelObj s j) := by
  have hk := Finset.mem_Icc.1 hs
  have hg := (lemma_2 M hM (s - 1) (by omega)).1.1
  set L : ℝ →ₗ[ℝ] ℝ × (Fin n → ℝ) :=
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prod
      ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (M.a s • Pi.single j (1:ℝ))) with hL
  have hδ : (0 : Fin n → ℝ) ≤ M.a s • Pi.single j (1:ℝ) := single_nonneg j (hM.a_nonneg s hs)
  have h1 := hg.comp_linearMap L
  have hsub : Set.Ici (0:ℝ) ⊆ L ⁻¹' (Set.Ici (0:ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) := by
    intro w hw
    simp only [Set.mem_preimage, hL, LinearMap.prod_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Set.mem_prod, Set.mem_Ici]
    exact ⟨hw, smul_nonneg hw hδ⟩
  have h2 : ConvexOn ℝ (Set.Ici 0) (fun w : ℝ => M.g (s - 1) w (M.a s • w • Pi.single j 1)) := by
    refine (h1.subset hsub (convex_Ici 0)).congr ?_
    intro w _
    show M.g (s - 1) w (w • (M.a s • Pi.single j (1:ℝ))) = _
    rw [smul_comm]
  have h3 : ConvexOn ℝ (Set.Ici 0) (fun w : ℝ => M.p s j * w) :=
    ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩
  have h4 := (h3.add (hM.h_convex s hs)).add h2
  have e : M.levelObj s j = (fun w : ℝ => M.p s j * w) + M.h s +
      (fun w : ℝ => M.g (s - 1) w (M.a s • w • Pi.single j 1)) := by
    funext w; simp only [Model.levelObj, Pi.add_apply]
  rw [e]; exact h4

lemma fw_eq (M : Model n) (hM : M.Standing) {s : ℕ} (hs : s ∈ Finset.Icc 1 M.k) {z : ℝ}
    (hz : 0 ≤ z) {B : Fin n → ℝ} (hB : 0 ≤ B) {w : ℝ}
    (hw : w ∈ Set.Icc (max (z - ∑ j, B j) 0) z) :
    M.fw s w z B = Fv M s z B w := by
  obtain ⟨hmem, hle⟩ := lemma_4 M hM s hs z hz B hB w hw
  have hL : IsLeast ((fun u => M.p s ⬝ᵥ u + M.g (s - 1) w (M.a s • u)) ''
      {u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w})
      (M.p s ⬝ᵥ uVec (z - w) B + M.g (s - 1) w (M.a s • uVec (z - w) B)) :=
    ⟨⟨_, hmem, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hle u hu⟩
  unfold Model.fw Fv
  rw [hL.csInf_eq]

lemma stepA (M : Model n) (hM : M.Standing) {s : ℕ} (hs : s ∈ Finset.Icc 1 M.k)
    (ha : M.a s = 0 ∨ M.a s = 1) (hC : CG M (s - 1)) {zbar : Fin n → WithTop ℝ}
    (hz : ∀ j, IsCriticalLevel (M.levelObj s j) (zbar j)) (hanti : Antitone zbar)
    {z : ℝ} (hz0 : 0 ≤ z) {B : Fin n → ℝ} (hB : 0 ≤ B) :
    M.f s z B = Fv M s z B (wstar B z zbar) ∧ rationU zbar z B ∈ feasible z B ∧
      M.f s z B = M.obj s (M.g (s - 1)) z B (rationU zbar z B) := by
  have hzz : ∀ j (x : ℝ), zbar j = (x : WithTop ℝ) → 0 ≤ x := fun j x h => crit_nonneg (hz j) h
  have hw0 := wstar_nonneg hB hanti hzz hz0
  have hwL := wstar_ge_L hB (z := z) (zbar := zbar)
  have hwz := wstar_le_z hB (z := z) (zbar := zbar)
  have hmemI : wstar B z zbar ∈ Set.Icc (max (z - ∑ j, B j) 0) z := ⟨max_le hwL hw0, hwz⟩
  have hmin : ∀ w ∈ Set.Icc (max (z - ∑ j, B j) 0) z,
      Fv M s z B (wstar B z zbar) ≤ Fv M s z B w := by
    rintro w ⟨hw1, hw2⟩
    have hwL' := (le_max_left _ _).trans hw1
    have hw0' := (le_max_right _ _).trans hw1
    rw [path M s ha hC hB hw0 hwL hwz, path M s ha hC hB hw0' hwL' hw2]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro j _
    rw [wstar_clamp hB hanti j]
    apply sub_le_sub_right
    have hlr := lr_le hB z j
    rcases le_or_gt 0 (z - T B (j.val + 1)) with hr | hr
    · exact cl_le (phi_convex M hM hs j) (hz j) (le_max_right _ _)
        (max_le (min_le_right _ _) hlr) (le_max_of_le_left (le_min hw0' hr))
    · have e1 : max (min w (z - T B (j.val + 1))) (z - T B j.val) = z - T B (j.val + 1) := by
        rw [min_eq_right (by linarith), max_eq_left hlr]
      simp only [e1, cc_eq_r hB hzz j hr.le, le_refl]
  have hf : M.f s z B = Fv M s z B (wstar B z zbar) := by
    rw [(eq_6 M hM s hs z hz0 B hB).1]
    apply IsLeast.csInf_eq
    refine ⟨⟨wstar B z zbar, hmemI, fw_eq M hM hs hz0 hB hmemI⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    show _ ≤ M.fw s w z B
    rw [fw_eq M hM hs hz0 hB hw]
    exact hmin w hw
  obtain ⟨⟨h0, hle, hsum⟩, -⟩ := lemma_4 M hM s hs z hz0 B hB _ hmemI
  rw [← rationU_wstar hB hanti] at h0 hle hsum
  refine ⟨hf, ⟨h0, hle, by rw [hsum]; linarith⟩, ?_⟩
  rw [hf]
  unfold Model.obj Fv
  rw [hsum, sub_sub_cancel, rationU_wstar hB hanti]
  ring

lemma incr (M : Model n) (hM : M.Standing) {s : ℕ} (hs : s ∈ Finset.Icc 1 M.k)
    (ha : M.a s = 0 ∨ M.a s = 1) (hC : CG M (s - 1)) {j i : Fin n} (hji : j < i) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    M.levelObj s j y - M.levelObj s j x ≤ M.levelObj s i y - M.levelObj s i x := by
  have hk := Finset.mem_Icc.1 hs
  have hp : M.p s j ≤ M.p s i := hM.p_mono s hs hji.le
  have hpp : M.p s j * y - M.p s j * x ≤ M.p s i * y - M.p s i * x := by nlinarith
  rcases hxy.lt_or_eq with hlt | heq
  · unfold Model.levelObj
    rcases ha with ha | ha
    · rw [ha]; simp only [zero_smul]; linarith
    · rw [ha]; simp only [one_smul]
      have key : ∀ m : Fin n, M.g (s - 1) y (y • Pi.single m 1) -
          M.g (s - 1) x (x • Pi.single m 1) =
          M.g (s - 1) y ((y - x) • Pi.single m 1) - M.g (s - 1) x 0 := by
        intro m
        have h := hC (y - x) (by linarith) m x hx (x • Pi.single m 1) 0 (single_nonneg m hx)
          le_rfl (fun i hi => by simp [single_gt m x hi])
        rw [show x + (y - x) = y by ring, zero_add,
          show x • Pi.single m (1:ℝ) + (y - x) • Pi.single m 1 = y • Pi.single m 1 by
            rw [← add_smul]; congr 1; ring] at h
        linarith
      have h3 := (lemma_3 M hM i j hji (y - x) (by linarith)).2 (s - 1) (by omega) y
        (by linarith) ((y - x) • Pi.single i 1) (single_nonneg i (by linarith)) (by simp)
      rw [show (y - x) • Pi.single i (1:ℝ) - (y - x) • (Pi.single i 1 - Pi.single j 1) =
          (y - x) • Pi.single j 1 by rw [smul_sub]; abel] at h3
      linarith [key j, key i]
  · subst heq; simp

lemma anti (M : Model n) (hM : M.Standing) {s : ℕ} (hs : s ∈ Finset.Icc 1 M.k)
    (ha : M.a s = 0 ∨ M.a s = 1) (hC : CG M (s - 1)) {zbar : Fin n → WithTop ℝ}
    (hz : ∀ j, IsCriticalLevel (M.levelObj s j) (zbar j)) : Antitone zbar := by
  intro j i hji
  rcases hji.lt_or_eq with hji | rfl
  · rcases hz i with ⟨hi, hanti_i⟩ | ⟨xi, hi, hxi0, hmini, hsmall⟩
    · rcases hz j with ⟨hj, -⟩ | ⟨xj, hj, hxj0, hminj, -⟩
      · simp [hi, hj]
      · exfalso
        have h1 := incr M hM hs ha hC hji hxj0 (by linarith : xj ≤ xj + 1)
        have h2 : M.levelObj s i (xj + 1) < M.levelObj s i xj :=
          hanti_i (Set.mem_Ici.2 hxj0) (Set.mem_Ici.2 (by linarith)) (by linarith)
        have h3 := hminj (xj + 1) (by linarith)
        linarith
    · rcases hz j with ⟨hj, -⟩ | ⟨xj, hj, hxj0, hminj, -⟩
      · rw [hj]; exact le_top
      · rw [hi, hj, WithTop.coe_le_coe]
        by_contra hlt
        push_neg at hlt
        have h1 := incr M hM hs ha hC hji hxj0 hlt.le
        have h2 := hminj xi hxi0
        have h3 : xi ≤ xj := hsmall xj hxj0 (fun w hw => by linarith [hmini w hw])
        linarith
  · exact le_rfl

lemma CG0 (M : Model n) : CG M 0 := by
  intro ε hε j z hz b b' hb hb' hbb
  have hs1 : ∀ c : Fin n → ℝ, ∑ i, (c + ε • (Pi.single j (1:ℝ) : Fin n → ℝ)) i = ∑ i, c i + ε := by
    intro c
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_right_inj]
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
    simp
  simp only [Model.g]
  rw [hs1 b, hs1 b', show z + ε - (∑ i, b i + ε) = z - ∑ i, b i by ring,
    show z + ε - (∑ i, b' i + ε) = z - ∑ i, b' i by ring]
  ring

lemma cl_diff (φ : ℝ → ℝ) (zb : WithTop ℝ) {l l' r r' : ℝ} (h1 : l ≤ r) (h2 : l ≤ r')
    (h3 : l' ≤ r) (h4 : l' ≤ r') :
    φ (cl zb l r) - φ (cl zb l r') = φ (cl zb l' r) - φ (cl zb l' r') := by
  induction zb using WithTop.recTopCoe with
  | top => simp only [cl_top]
  | coe x =>
    rw [cl_coe, cl_coe, cl_coe, cl_coe, clamp_id φ h1, clamp_id φ h2, clamp_id φ h3,
      clamp_id φ h4]
    ring

lemma V_diff (φ : Fin n → ℝ → ℝ) (zbar : Fin n → WithTop ℝ) {B B' : Fin n → ℝ} (hB : 0 ≤ B)
    (hB' : 0 ≤ B') {j : Fin n} (hBB : ∀ i, j < i → B i = B' i) {ε : ℝ} (hε : 0 < ε) (z : ℝ) :
    (∑ i, (φ i (cc B z zbar i) - φ i (z - T B (i.val + 1)))) -
      (∑ i, (φ i (cc (B + ε • Pi.single j 1) (z + ε) zbar i) -
        φ i (z + ε - T (B + ε • Pi.single j 1) (i.val + 1)))) =
    (∑ i, (φ i (cc B' z zbar i) - φ i (z - T B' (i.val + 1)))) -
      (∑ i, (φ i (cc (B' + ε • Pi.single j 1) (z + ε) zbar i) -
        φ i (z + ε - T (B' + ε • Pi.single j 1) (i.val + 1)))) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold cc
  simp only [T_add_single]
  have e : ∀ a : ℝ, z + ε - (a + ε) = z - a := fun a => by ring
  rcases lt_trichotomy i j with h | h | h
  · have h1 : i.val ≤ j.val := by rw [Fin.lt_def] at h; omega
    have h2 : i.val + 1 ≤ j.val := by rw [Fin.lt_def] at h; omega
    simp only [if_pos h1, if_pos h2, e, sub_self]
  · have hv : i.val = j.val := congrArg Fin.val h
    have h1 : i.val ≤ j.val := by omega
    have h2 : ¬ (i.val + 1 ≤ j.val) := by omega
    simp only [if_pos h1, if_neg h2, add_zero, e]
    rw [T_congr hBB (m := i.val + 1) (by omega)]
    have hl1 := lr_le hB z i
    have hl2 := lr_le hB' z i
    rw [T_congr hBB (m := i.val + 1) (by omega)] at hl1
    have := cl_diff (φ i) (zbar i) (l := z - T B i.val) (l' := z - T B' i.val)
      (r := z - T B' (i.val + 1)) (r' := z + ε - T B' (i.val + 1)) hl1 (by linarith) hl2
      (by linarith)
    linarith
  · have h1 : ¬ (i.val ≤ j.val) := by rw [Fin.lt_def] at h; omega
    have h2 : ¬ (i.val + 1 ≤ j.val) := by rw [Fin.lt_def] at h; omega
    simp only [if_neg h1, if_neg h2, add_zero]
    rw [T_congr hBB (m := i.val) (by rw [Fin.lt_def] at h; omega),
      T_congr hBB (m := i.val + 1) (by rw [Fin.lt_def] at h; omega)]

lemma fval (M : Model n) (hM : M.Standing) {s : ℕ} (hs : s ∈ Finset.Icc 1 M.k)
    (ha : M.a s = 0 ∨ M.a s = 1) (hC : CG M (s - 1)) {zbar : Fin n → WithTop ℝ}
    (hz : ∀ j, IsCriticalLevel (M.levelObj s j) (zbar j)) (hanti : Antitone zbar)
    {z : ℝ} (hz0 : 0 ≤ z) {B : Fin n → ℝ} (hB : 0 ≤ B) :
    M.f s z B = M.p s ⬝ᵥ B + M.g (s - 1) z (M.a s • B) + M.h s z +
      ∑ j : Fin n, (M.levelObj s j (cc B z zbar j) - M.levelObj s j (z - T B (j.val + 1))) := by
  have hzz : ∀ j (x : ℝ), zbar j = (x : WithTop ℝ) → 0 ≤ x := fun j x h => crit_nonneg (hz j) h
  rw [(stepA M hM hs ha hC hz hanti hz0 hB).1,
    path M s ha hC hB (wstar_nonneg hB hanti hzz hz0) (wstar_ge_L hB) (wstar_le_z hB)]
  simp only [wstar_clamp hB hanti]
  unfold Fv
  rw [sub_self, uVec_zero hB]

lemma stepCF (M : Model n) (hM : M.Standing) {s : ℕ} (hs : s ∈ Finset.Icc 1 M.k)
    (ha : M.a s = 0 ∨ M.a s = 1) (hC : CG M (s - 1)) {zbar : Fin n → WithTop ℝ}
    (hz : ∀ j, IsCriticalLevel (M.levelObj s j) (zbar j)) (hanti : Antitone zbar) :
    CF M s := by
  intro ε hε j z hz0 B B' hB hB' hBB
  have hz1 : 0 ≤ z + ε := by linarith
  have hB1 : 0 ≤ B + ε • Pi.single j 1 := add_nonneg hB (single_nonneg j hε.le)
  have hB1' : 0 ≤ B' + ε • Pi.single j 1 := add_nonneg hB' (single_nonneg j hε.le)
  rw [fval M hM hs ha hC hz hanti hz0 hB, fval M hM hs ha hC hz hanti hz1 hB1,
    fval M hM hs ha hC hz hanti hz0 hB', fval M hM hs ha hC hz hanti hz1 hB1']
  have hp : ∀ c : Fin n → ℝ, M.p s ⬝ᵥ (c + ε • Pi.single j 1) = M.p s ⬝ᵥ c + ε * M.p s j := by
    intro c; rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
  have hG : M.g (s - 1) z (M.a s • B) - M.g (s - 1) (z + ε) (M.a s • (B + ε • Pi.single j 1)) =
      M.g (s - 1) z (M.a s • B') - M.g (s - 1) (z + ε) (M.a s • (B' + ε • Pi.single j 1)) := by
    rcases ha with ha | ha
    · rw [ha]; simp only [zero_smul]
    · rw [ha]; simp only [one_smul]; exact hC ε hε j z hz0 B B' hB hB' hBB
  have hV := V_diff (M.levelObj s) zbar hB hB' hBB hε z
  rw [hp B, hp B']
  linarith

lemma g_succ (M : Model n) (s : ℕ) (z : ℝ) (b : Fin n → ℝ) :
    M.g (s + 1) z b = ∫ x, M.f (s + 1) z (b + x) ∂(M.μ (s + 1)) := rfl

lemma stepCG (M : Model n) (hM : M.Standing) {s : ℕ} (hs : s ∈ Finset.Icc 1 M.k)
    (hCF : CF M s) : CG M s := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by have := (Finset.mem_Icc.1 hs).1; omega⟩
  intro ε hε j z hz0 b b' hb hb' hbb
  have hint := (lemma_2 M hM (s' + 1) (Finset.mem_Icc.1 hs).2).2.2.2 (by omega)
  have hz1 : 0 ≤ z + ε := by linarith
  have hb1 : 0 ≤ b + ε • Pi.single j 1 := add_nonneg hb (single_nonneg j hε.le)
  have hb1' : 0 ≤ b' + ε • Pi.single j 1 := add_nonneg hb' (single_nonneg j hε.le)
  simp only [g_succ]
  rw [← integral_sub (hint z hz0 b hb) (hint (z + ε) hz1 _ hb1),
    ← integral_sub (hint z hz0 b' hb') (hint (z + ε) hz1 _ hb1')]
  apply integral_congr_ae
  filter_upwards [hM.μ_nonneg (s' + 1) hs] with x hx
  try dsimp only
  rw [show b + ε • Pi.single j 1 + x = (b + x) + ε • Pi.single j 1 by abel,
    show b' + ε • Pi.single j 1 + x = (b' + x) + ε • Pi.single j 1 by abel]
  exact hCF ε hε j z hz0 (b + x) (b' + x) (add_nonneg hb hx) (add_nonneg hb' hx)
    (fun i hi => by simp only [Pi.add_apply, hbb i hi])

lemma step (M : Model n) (hM : M.Standing) {s : ℕ} (hs : s ∈ Finset.Icc 1 M.k)
    (ha : M.a s = 0 ∨ M.a s = 1) (hC : CG M (s - 1)) (zbar : Fin n → WithTop ℝ)
    (hz : ∀ j, IsCriticalLevel (M.levelObj s j) (zbar j)) :
    Antitone zbar ∧
    (∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B →
      rationU zbar z B ∈ feasible z B ∧
        M.f s z B = M.obj s (M.g (s - 1)) z B (rationU zbar z B)) ∧
    CF M s ∧ CG M s := by
  have hanti := anti M hM hs ha hC hz
  have hCF := stepCF M hM hs ha hC hz hanti
  exact ⟨hanti, fun z hz0 B hB => (stepA M hM hs ha hC hz hanti hz0 hB).2, hCF,
    stepCG M hM hs hCF⟩

end T1Aux

open TopkisRation.Levels in
theorem solution {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (ha : ∀ i ∈ Finset.Icc 1 t, M.a i = 0 ∨ M.a i = 1)
    (zbar : Fin n → WithTop ℝ) (hz : ∀ j, IsCriticalLevel (M.levelObj t j) (zbar j)) :
    (∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B →
        rationU zbar z B ∈ feasible z B ∧
        M.f t z B = M.obj t (M.g (t - 1)) z B (rationU zbar z B)) ∧
    Antitone zbar ∧
    (∀ ε : ℝ, 0 < ε → ∀ j : Fin n, ∀ z, 0 ≤ z →
      (∀ B B' : Fin n → ℝ, 0 ≤ B → 0 ≤ B' → (∀ i, j < i → B i = B' i) →
        M.f t z B - M.f t (z + ε) (B + ε • Pi.single j 1) =
          M.f t z B' - M.f t (z + ε) (B' + ε • Pi.single j 1)) ∧
      (∀ b b' : Fin n → ℝ, 0 ≤ b → 0 ≤ b' → (∀ i, j < i → b i = b' i) →
        M.g t z b - M.g t (z + ε) (b + ε • Pi.single j 1) =
          M.g t z b' - M.g t (z + ε) (b' + ε • Pi.single j 1)))  := by
  have hk := Finset.mem_Icc.1 ht
  have hCall : ∀ s, s + 1 ≤ t → T1Aux.CG M s := by
    intro s
    induction s with
    | zero => intro _; exact T1Aux.CG0 M
    | succ s ih =>
      intro hs
      have hs' : s + 1 ∈ Finset.Icc 1 M.k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hzb := fun j => (criticalLevel_exists M hM (s + 1) hs' j).exists.choose_spec
      exact (T1Aux.step M hM hs' (ha (s + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
        (by simpa using ih (by omega)) _ hzb).2.2.2
  have hC : T1Aux.CG M (t - 1) := hCall (t - 1) (by omega)
  obtain ⟨hanti, hA, hCF, hCG⟩ :=
    T1Aux.step M hM ht (ha t (Finset.mem_Icc.2 ⟨hk.1, le_rfl⟩)) hC zbar hz
  exact ⟨hA, hanti, fun ε hε j z hz0 =>
    ⟨fun B B' hB hB' h => hCF ε hε j z hz0 B B' hB hB' h,
     fun b b' hb hb' h => hCG ε hε j z hz0 b b' hb hb' h⟩⟩
