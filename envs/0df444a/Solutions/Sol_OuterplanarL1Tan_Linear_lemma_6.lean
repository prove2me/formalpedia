-- Prove2me | solution 1 for OuterplanarL1Tan.Linear.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:19:16.167201+00:00
-- url     : https://prove2.me/submissions/dede4e01-a28e-41d9-83f5-b2fb0954314f

import Mathlib
import Definitions.Def_OuterplanarL1Tan_Linear_L1Distance
import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.K

open OuterplanarL1Tan.Linear
open scoped Classical

section Cuts

variable {X : Type} [Fintype X]

/-- Thresholds `θ` at which the sublevel set of `h` is exactly `S`. -/
def A (h : X → ℝ) (S : Finset X) : Set ℝ := {θ | ∀ z, z ∈ S ↔ h z ≤ θ}

def sep (x y : X) (S : Finset X) : Prop := ¬ (x ∈ S ↔ y ∈ S)

lemma A_meas (h : X → ℝ) (S : Finset X) : MeasurableSet (A h S) := by
  have : A h S = ⋂ z, (if z ∈ S then Set.Ici (h z) else Set.Iio (h z)) := by
    ext θ
    simp only [A, Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' fun z => ?_
    by_cases hz : z ∈ S <;> simp [hz]
  rw [this]
  refine MeasurableSet.iInter fun z => ?_
  split_ifs
  · exact measurableSet_Ici
  · exact measurableSet_Iio

lemma Ico_eq (h : X → ℝ) (x y : X) :
    Set.Ico (min (h x) (h y)) (max (h x) (h y)) =
      ⋃ S ∈ (Finset.univ.filter (sep x y)), A h S := by
  ext θ
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop,
    Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Finset.univ.filter (fun z => h z ≤ θ), ?_, ?_⟩
    · simp only [sep, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hiff
      rcases le_total (h x) (h y) with hxy | hxy
      · rw [min_eq_left hxy] at h1
        rw [max_eq_right hxy] at h2
        exact absurd (hiff.1 h1) (not_le.2 h2)
      · rw [min_eq_right hxy] at h1
        rw [max_eq_left hxy] at h2
        exact absurd (hiff.2 h1) (not_le.2 h2)
    · intro z; simp
  · rintro ⟨S, hS, hθ⟩
    unfold sep at hS
    rw [hθ x, hθ y] at hS
    by_cases a : h x ≤ θ <;> by_cases b : h y ≤ θ
    · exact absurd ⟨fun _ => b, fun _ => a⟩ hS
    · exact ⟨(min_le_left _ _).trans a, lt_of_lt_of_le (not_le.1 b) (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans b, lt_of_lt_of_le (not_le.1 a) (le_max_left _ _)⟩
    · exact absurd ⟨fun h' => absurd h' a, fun h' => absurd h' b⟩ hS

lemma abs_eq_sum (h : X → ℝ) (x y : X) :
    |h x - h y| = ∑ S, if sep x y S then (MeasureTheory.volume (A h S)).toReal else 0 := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ.filter (sep x y)) : Set (Finset X)) (A h) := by
    intro S _ T _ hST
    rw [Function.onFun, Set.disjoint_left]
    intro θ hS hT
    apply hST
    ext z
    rw [hS z, hT z]
  have hvol := congrArg MeasureTheory.volume (Ico_eq h x y)
  rw [Real.volume_Ico, MeasureTheory.measure_biUnion_finset hdisj (fun S _ => A_meas h S)]
    at hvol
  have hfin : ∀ S ∈ Finset.univ.filter (sep x y), MeasureTheory.volume (A h S) ≠ ⊤ := by
    intro S hS
    have : MeasureTheory.volume (A h S) ≤
        ∑ S ∈ Finset.univ.filter (sep x y), MeasureTheory.volume (A h S) :=
      Finset.single_le_sum (f := fun S => MeasureTheory.volume (A h S))
        (fun _ _ => bot_le) hS
    rw [← hvol] at this
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  have e : |h x - h y| = ∑ S ∈ Finset.univ.filter (sep x y),
      (MeasureTheory.volume (A h S)).toReal := by
    rw [← ENNReal.toReal_sum hfin, ← hvol, ENNReal.toReal_ofReal]
    · exact (max_sub_min_eq_abs' _ _).symm
    · simp
  rw [e, Finset.sum_filter]

end Cuts

lemma alpha_exists {X : Type} [Fintype X] (δ : X → X → ℝ) (isL1 : IsL1Distance δ) :
    ∃ α : Finset X → ℝ, (∀ S, 0 ≤ α S) ∧
      ∀ x y, δ x y = ∑ S, if sep x y S then α S else 0 := by
  obtain ⟨f, hf⟩ := isL1
  refine ⟨fun S => ∑' c, (MeasureTheory.volume (A (fun x => f x c) S)).toReal,
    fun S => tsum_nonneg fun c => ENNReal.toReal_nonneg, ?_⟩
  intro x y
  have h1 : HasSum (fun c => |f x c - f y c|) (δ x y) := by
    rw [hf x y]
    have := lp.hasSum_norm (p := 1) (E := fun _ : ℕ => ℝ) (by simp) (f x - f y)
    simpa using this
  have h2 : ∀ c, |f x c - f y c| = ∑ S, if sep x y S then
      (MeasureTheory.volume (A (fun x => f x c) S)).toReal else 0 :=
    fun c => abs_eq_sum (fun x => f x c) x y
  have h3 : ∀ S : Finset X, HasSum (fun c => if sep x y S then
      (MeasureTheory.volume (A (fun x => f x c) S)).toReal else 0)
      (if sep x y S then ∑' c, (MeasureTheory.volume (A (fun x => f x c) S)).toReal else 0) := by
    intro S
    by_cases hs : sep x y S
    · simp only [hs, if_true]
      apply Summable.hasSum
      refine Summable.of_nonneg_of_le (fun c => ENNReal.toReal_nonneg) (fun c => ?_) h1.summable
      rw [h2 c]
      have := Finset.single_le_sum
        (f := fun S => if sep x y S then
          (MeasureTheory.volume (A (fun x => f x c) S)).toReal else 0)
        (fun S _ => by dsimp only; split_ifs <;> simp) (Finset.mem_univ S)
      simpa [hs] using this
    · simp only [hs, if_false]
      exact hasSum_zero
  have h4 := hasSum_sum (s := Finset.univ) (fun S _ => h3 S)
  have h5 : HasSum (fun c => |f x c - f y c|)
      (∑ S, if sep x y S then ∑' c, (MeasureTheory.volume (A (fun x => f x c) S)).toReal
        else 0) := by
    simp_rw [h2]
    exact h4
  exact h1.unique h5

/-! ### Random partition -/

noncomputable section Part

variable {X : Type} [Fintype X]

def qq (α : Finset X → ℝ) (r : ℝ) (S : Finset X) : ℝ := Real.exp (-(α S) / (2 * r))

def Pw (α : Finset X → ℝ) (r : ℝ) (ω : Finset (Finset X)) : ℝ :=
  ∏ S, if S ∈ ω then 1 - qq α r S else qq α r S

def Tp (ω : Finset (Finset X)) (x : X) : Finset X :=
  Finset.univ.filter (fun z => ∀ S ∈ ω, (x ∈ S ↔ z ∈ S))

def uu (α : Finset X → ℝ) (r : ℝ) (x : X) (i : Finset (Finset X) × Finset X) : ℝ :=
  if i.2 = Tp i.1 x then Pw α r i.1 else 0

lemma sum_powerset_ite {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) :
    ∑ ω : Finset ι, ∏ S, (if S ∈ ω then a S else b S) = ∏ S, (a S + b S) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_ite]
  have e1 : Finset.univ.filter (fun S => S ∈ t) = t := by ext; simp
  have e2 : Finset.univ.filter (fun S => ¬ S ∈ t) = Finset.univ \ t := by ext; simp
  rw [e1, e2]

lemma qq_pos (α : Finset X → ℝ) (r : ℝ) (S : Finset X) : 0 < qq α r S := Real.exp_pos _

lemma qq_le_one (α : Finset X → ℝ) (r : ℝ) (hα : ∀ S, 0 ≤ α S) (hr : 0 < r) (S : Finset X) :
    qq α r S ≤ 1 := by
  unfold qq
  rw [Real.exp_le_one_iff]
  have := hα S
  have : 0 ≤ α S / (2 * r) := by positivity
  rw [neg_div]; linarith

lemma Pw_nonneg (α : Finset X → ℝ) (r : ℝ) (hα : ∀ S, 0 ≤ α S) (hr : 0 < r)
    (ω : Finset (Finset X)) : 0 ≤ Pw α r ω := by
  unfold Pw
  refine Finset.prod_nonneg fun S _ => ?_
  split_ifs
  · linarith [qq_le_one α r hα hr S]
  · exact (qq_pos α r S).le

lemma sum_Pw (α : Finset X → ℝ) (r : ℝ) : ∑ ω, Pw α r ω = 1 := by
  unfold Pw
  convert sum_powerset_ite (fun S : Finset X => 1 - qq α r S) (fun S => qq α r S) using 3 <;> simp

lemma sum_Pw_sep (α : Finset X → ℝ) (r : ℝ) (B : Finset X → Prop) :
    ∑ ω, (if ∀ S ∈ ω, ¬ B S then Pw α r ω else 0) =
      ∏ S, if B S then qq α r S else 1 := by
  have key : ∀ ω : Finset (Finset X), (if ∀ S ∈ ω, ¬ B S then Pw α r ω else 0) =
      ∏ S, (if S ∈ ω then (if B S then 0 else 1 - qq α r S) else qq α r S) := by
    intro ω
    by_cases hω : ∀ S ∈ ω, ¬ B S
    · rw [if_pos hω]
      unfold Pw
      refine Finset.prod_congr rfl fun S _ => ?_
      by_cases hS : S ∈ ω
      · simp [hS, hω S hS]
      · simp [hS]
    · rw [if_neg hω]
      push_neg at hω
      obtain ⟨S, hS, hB⟩ := hω
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ S) (by simp [hS, hB])
  simp_rw [key]
  refine (sum_powerset_ite (fun S : Finset X => if B S then (0:ℝ) else 1 - qq α r S)
    (fun S => qq α r S)).trans ?_
  refine Finset.prod_congr rfl fun S _ => ?_
  by_cases hB : B S <;> simp [hB]

lemma Tp_eq_iff (ω : Finset (Finset X)) (x y : X) :
    Tp ω x = Tp ω y ↔ ∀ S ∈ ω, ¬ sep x y S := by
  unfold Tp sep
  constructor
  · intro h S hS
    have hy : y ∈ Finset.univ.filter (fun z => ∀ S ∈ ω, (y ∈ S ↔ z ∈ S)) := by simp
    rw [← h] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have := hy S hS
    tauto
  · intro h
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine forall_congr' fun S => forall_congr' fun hS => ?_
    have := h S hS
    tauto

end Part

theorem partition_map {X : Type} [Fintype X] (δ : X → X → ℝ) (isL1 : IsL1Distance δ)
    (r : ℝ) (hr : 0 < r) :
    ∃ (M : Type) (_ : Fintype M) (u : X → M → ℝ),
      (∀ x i, 0 ≤ u x i) ∧ (∀ x, ∑ i, u x i = 1) ∧
      (∀ x y i, u x i = u y i ∨ u x i = 0 ∨ u y i = 0) ∧
      (∀ x y, ∑ i, min (u x i) (u y i) = Real.exp (-(δ x y) / (2 * r))) := by
  obtain ⟨α, hα0, hα⟩ := alpha_exists δ isL1
  refine ⟨Finset (Finset X) × Finset X, inferInstance, uu α r, ?_, ?_, ?_, ?_⟩
  · intro x i
    unfold uu
    split_ifs
    · exact Pw_nonneg α r hα0 hr _
    · exact le_rfl
  · intro x
    unfold uu
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact sum_Pw α r
  · intro x y i
    unfold uu
    by_cases h1 : i.2 = Tp i.1 x <;> by_cases h2 : i.2 = Tp i.1 y
    · left; rw [if_pos h1, if_pos h2]
    · right; right; rw [if_neg h2]
    · right; left; rw [if_neg h1]
    · left; rw [if_neg h1, if_neg h2]
  · intro x y
    rw [Fintype.sum_prod_type]
    have e : ∀ ω : Finset (Finset X), ∑ T : Finset X, min (uu α r x (ω, T)) (uu α r y (ω, T)) =
        if ∀ S ∈ ω, ¬ sep x y S then Pw α r ω else 0 := by
      intro ω
      by_cases h : Tp ω x = Tp ω y
      · rw [if_pos ((Tp_eq_iff ω x y).1 h)]
        unfold uu
        simp only [h, min_self]
        simp
      · rw [if_neg (mt (Tp_eq_iff ω x y).2 h)]
        refine Finset.sum_eq_zero fun T _ => ?_
        unfold uu
        simp only
        by_cases h1 : T = Tp ω x
        · have h2 : T ≠ Tp ω y := fun h2 => h (h1.symm.trans h2)
          simp only [h1, if_true]
          rw [if_neg (h1 ▸ h2 : ¬ Tp ω x = Tp ω y)]
          exact min_eq_right (Pw_nonneg α r hα0 hr ω)
        · simp only [h1, if_false]
          exact min_eq_left (by split_ifs; exact Pw_nonneg α r hα0 hr ω; exact le_rfl)
    simp_rw [e]
    rw [sum_Pw_sep]
    rw [hα x y, neg_div]
    have : ∀ S : Finset X, (if sep x y S then qq α r S else 1) =
        Real.exp (if sep x y S then -(α S) / (2 * r) else 0) := by
      intro S; unfold qq; split_ifs <;> simp
    simp_rw [this]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs <;> simp [neg_div]

end OuterplanarL1Tan.Dev.K
end

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.L6

open MeasureTheory

theorem one_sub_exp_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  have := Real.add_one_le_exp (-x)
  linarith

theorem one_sub_exp_ge {x : ℝ} (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ 1 - Real.exp (-x) := by
  have h1 : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx
  have hpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
  have h2 : Real.exp (-x) * (1 + x + x ^ 2 / 2) ≤ 1 := by
    have : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-x) * (1 + x + x ^ 2 / 2) ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 1 := this
  have h3 : (1 + x + x ^ 2 / 2) * (1 - x + x ^ 2 / 2) ≥ 1 := by nlinarith [sq_nonneg (x ^ 2)]
  have h4 : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
    by_contra hc
    push Not at hc
    have : Real.exp (-x) * (1 + x + x ^ 2 / 2) > (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) :=
      mul_lt_mul_of_pos_right hc hpos
    nlinarith
  linarith

/-- the cell `[(j+1)η, (j+2)η)` -/
def cell (η : ℝ) (j : ℕ) : Set ℝ := Set.Ico (((j : ℝ) + 1) * η) (((j : ℝ) + 2) * η)

/-- the length of a set inside a cell -/
noncomputable def W (η : ℝ) (S : Set ℝ) (j : ℕ) : ℝ := (volume (cell η j ∩ S)).toReal

theorem cell_meas (η : ℝ) (j : ℕ) : MeasurableSet (cell η j) := measurableSet_Ico

theorem cell_vol_ne_top (η : ℝ) (j : ℕ) : volume (cell η j) ≠ ⊤ := by
  unfold cell; rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top

theorem W_nonneg (η : ℝ) (S : Set ℝ) (j : ℕ) : 0 ≤ W η S j := ENNReal.toReal_nonneg

theorem W_pos {η : ℝ} {S : Set ℝ} {j : ℕ} (h : 0 < W η S j) : ∃ x, x ∈ cell η j ∧ x ∈ S := by
  by_contra hc
  push Not at hc
  have : cell η j ∩ S = ∅ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    exact fun ⟨a, b⟩ => hc x a b
  unfold W at h
  rw [this] at h
  simp at h

theorem cell_disjoint {η : ℝ} (hη : 0 < η) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (cell η i) (cell η j) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  unfold cell at hx hx'
  simp only [Set.mem_Ico] at hx hx'
  rcases lt_or_gt_of_ne hij with h | h
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    nlinarith [hx.2, hx'.1]
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    nlinarith [hx.1, hx'.2]

theorem cells_union {η : ℝ} (hη : 0 < η) (J : ℕ) :
    (⋃ j ∈ Finset.range J, cell η j) = Set.Ico η (((J : ℝ) + 1) * η) := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, Set.mem_Ico]
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    have : (j : ℝ) + 1 ≤ J := by exact_mod_cast hj
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    have hx0 : 0 ≤ x / η - 1 := by
      rw [sub_nonneg, le_div_iff₀ hη]; linarith
    refine ⟨⌊x / η - 1⌋₊, ?_, ?_, ?_⟩
    · have : x / η - 1 < J := by
        rw [sub_lt_iff_lt_add, div_lt_iff₀ hη]; nlinarith
      exact_mod_cast (Nat.floor_lt hx0).2 this
    · have := Nat.floor_le hx0
      have h3 : ((⌊x / η - 1⌋₊ : ℝ) + 1) * η ≤ x := by
        have : (⌊x / η - 1⌋₊ : ℝ) + 1 ≤ x / η := by linarith
        calc _ ≤ x / η * η := mul_le_mul_of_nonneg_right this hη.le
          _ = x := by field_simp
      exact h3
    · have := Nat.lt_floor_add_one (x / η - 1)
      have : x / η < (⌊x / η - 1⌋₊ : ℝ) + 2 := by linarith
      calc x = x / η * η := by field_simp
        _ < _ := mul_lt_mul_of_pos_right this hη

theorem sumW_eq {η : ℝ} (hη : 0 < η) (J : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    ∑ j ∈ Finset.range J, W η S j =
      (volume (S ∩ Set.Ico η (((J : ℝ) + 1) * η))).toReal := by
  unfold W
  rw [← ENNReal.toReal_sum (fun j _ => ne_top_of_le_ne_top (cell_vol_ne_top η j)
    (measure_mono Set.inter_subset_left))]
  congr 1
  rw [← cells_union hη J, ← measure_biUnion_finset]
  · congr 1
    ext x; simp [Set.mem_iUnion, and_comm]
  · intro i _ j _ hij
    exact (cell_disjoint hη hij).mono Set.inter_subset_left Set.inter_subset_left
  · intro j _
    exact (cell_meas η j).inter hS

theorem sumW_le {η : ℝ} (hη : 0 < η) (J : ℕ) {S : Set ℝ} (hS : MeasurableSet S)
    (hfin : volume S ≠ ⊤) : ∑ j ∈ Finset.range J, W η S j ≤ (volume S).toReal := by
  rw [sumW_eq hη J hS]
  exact ENNReal.toReal_mono hfin (measure_mono Set.inter_subset_left)

theorem sumW_eq_of_sub {η : ℝ} (hη : 0 < η) (J : ℕ) {S : Set ℝ} (hS : MeasurableSet S)
    (hsub : S ⊆ Set.Ico η (((J : ℝ) + 1) * η)) :
    ∑ j ∈ Finset.range J, W η S j = (volume S).toReal := by
  rw [sumW_eq hη J hS, Set.inter_eq_left.2 hsub]

theorem W_add (η : ℝ) (A B : Set ℝ) (hB : MeasurableSet B) (j : ℕ) :
    W η A j = W η (A ∩ B) j + W η (A \ B) j := by
  unfold W
  have h := measure_inter_add_sdiff (μ := volume) (cell η j ∩ A) hB
  have e1 : (cell η j ∩ A) ∩ B = cell η j ∩ (A ∩ B) := by rw [Set.inter_assoc]
  have e2 : (cell η j ∩ A) \ B = cell η j ∩ (A \ B) := by
    ext x; simp [and_assoc]
  rw [e1, e2] at h
  rw [← h, ENNReal.toReal_add]
  · exact ne_top_of_le_ne_top (cell_vol_ne_top η j)
      (measure_mono (Set.inter_subset_left : cell η j ∩ (A ∩ B) ⊆ cell η j))
  · exact ne_top_of_le_ne_top (cell_vol_ne_top η j)
      (measure_mono (Set.inter_subset_left : cell η j ∩ (A \ B) ⊆ cell η j))

theorem inv_sum {η : ℝ} (hη : 0 < η) (J : ℕ) {S : Set ℝ} (hS : MeasurableSet S)
    (hfin : volume S ≠ ⊤) {a : ℝ} (ha : η < a) (hSa : ∀ x ∈ S, a ≤ x) :
    ∑ j ∈ Finset.range J, W η S j / (((j : ℝ) + 1) * η) ≤ (volume S).toReal / (a - η) := by
  have hpos : 0 < a - η := by linarith
  calc ∑ j ∈ Finset.range J, W η S j / (((j : ℝ) + 1) * η)
      ≤ ∑ j ∈ Finset.range J, W η S j / (a - η) := by
        apply Finset.sum_le_sum
        intro j _
        rcases (W_nonneg η S j).eq_or_lt with h0 | h0
        · rw [← h0]; simp
        · obtain ⟨x, hx1, hx2⟩ := W_pos h0
          have h1 := hSa x hx2
          unfold cell at hx1
          simp only [Set.mem_Ico] at hx1
          have : a - η < ((j : ℝ) + 1) * η := by nlinarith [hx1.2]
          exact div_le_div_of_nonneg_left (W_nonneg η S j) hpos this.le
    _ = (∑ j ∈ Finset.range J, W η S j) / (a - η) := by rw [Finset.sum_div]
    _ ≤ (volume S).toReal / (a - η) :=
        div_le_div_of_nonneg_right (sumW_le hη J hS hfin) hpos.le

theorem piece_bound {η : ℝ} (J : ℕ) {S : Set ℝ} {b : ℝ} (hb : 0 < b) (hSb : ∀ x ∈ S, x < b)
    (hη : 0 < η) {c : ℝ} (hc : 0 ≤ c) :
    (∑ j ∈ Finset.range J, W η S j) * (1 - Real.exp (-c / (2 * b))) ≤
      ∑ j ∈ Finset.range J, W η S j * (1 - Real.exp (-c / (2 * (((j : ℝ) + 1) * η)))) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rcases (W_nonneg η S j).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · obtain ⟨x, hx1, hx2⟩ := W_pos h0
    have h1 := hSb x hx2
    unfold cell at hx1
    simp only [Set.mem_Ico] at hx1
    have hr : ((j : ℝ) + 1) * η ≤ b := by linarith [hx1.1]
    have hrp : 0 < ((j : ℝ) + 1) * η := by positivity
    apply mul_le_mul_of_nonneg_left _ h0.le
    have : -c / (2 * (((j : ℝ) + 1) * η)) ≤ -c / (2 * b) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := Real.exp_le_exp.2 this
    linarith

end OuterplanarL1Tan.Dev.L6
end

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.L6

open MeasureTheory

/-- the cell identity for two blocks -/
theorem cell_l1 {M : Type} [Fintype M] (u v : M → ℝ) (hu : ∑ i, u i = 1) (hv : ∑ i, v i = 1)
    (hc : ∀ i, u i = v i ∨ u i = 0 ∨ v i = 0) (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i)
    (w w' : ℝ) (hw : 0 ≤ w) (hw' : 0 ≤ w') :
    ∑ i, |w * u i - w' * v i| =
      |w - w'| * (∑ i, min (u i) (v i)) + (w + w') * (1 - ∑ i, min (u i) (v i)) := by
  have key : ∀ i, |w * u i - w' * v i| =
      |w - w'| * min (u i) (v i) + w * (u i - min (u i) (v i)) + w' * (v i - min (u i) (v i)) := by
    intro i
    rcases hc i with h | h | h
    · rw [← h]; simp only [min_self, sub_self, mul_zero, add_zero]
      rw [← sub_mul, abs_mul, abs_of_nonneg (hu0 i)]
    · rw [h]; have := hv0 i; simp [abs_of_nonneg, mul_nonneg hw' this, this]
    · rw [h]; have := hu0 i; simp [abs_of_nonneg, mul_nonneg hw this, this]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hu, hv]
  ring

theorem cell_upper (m k p q : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hk : 0 ≤ k) (hp : 0 ≤ p)
    (hq : 0 ≤ q) :
    |(k + p) - (k + q)| * m + ((k + p) + (k + q)) * (1 - m) ≤ p + q + 2 * k * (1 - m) := by
  have h1 : |(k + p) - (k + q)| ≤ p + q := by
    rw [abs_le]; constructor <;> linarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hm0, mul_nonneg (add_nonneg hp hq) (sub_nonneg.2 hm1)]

theorem cell_lower (m w w' : ℝ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hw : 0 ≤ w) (hw' : 0 ≤ w') :
    w * (1 - m) ≤ |w - w'| * m + (w + w') * (1 - m) := by
  nlinarith [mul_nonneg (abs_nonneg (w - w')) hm0, mul_nonneg hw' (sub_nonneg.2 hm1)]

/-- scale window -/
def A (s : ℝ) : Set ℝ := Set.Icc s (2 * s)

theorem A_meas (s : ℝ) : MeasurableSet (A s) := measurableSet_Icc

theorem A_fin (s : ℝ) : volume (A s) ≠ ⊤ := by
  unfold A; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

theorem vol_mono {S T : Set ℝ} (h : S ⊆ T) (hT : volume T ≠ ⊤) :
    (volume S).toReal ≤ (volume T).toReal := ENNReal.toReal_mono hT (measure_mono h)

theorem diff_vol_aux {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    (volume (A s \ A t)).toReal + (volume (A t \ A s)).toReal ≤ 3 * (s - t) := by
  have h1 : A s \ A t ⊆ Set.Ioc (2 * t) (2 * s) := by
    intro x hx
    simp only [A, Set.mem_diff, Set.mem_Icc, not_and, not_le] at hx
    obtain ⟨⟨a, b⟩, c⟩ := hx
    exact ⟨by have := c (by linarith); linarith, b⟩
  have h2 : A t \ A s ⊆ Set.Ico t s := by
    intro x hx
    simp only [A, Set.mem_diff, Set.mem_Icc, not_and, not_le] at hx
    obtain ⟨⟨a, b⟩, c⟩ := hx
    refine ⟨a, ?_⟩
    by_contra hc
    push Not at hc
    have := c hc
    linarith
  have e1 := vol_mono h1 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have e2 := vol_mono h2 (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at e1
  rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)] at e2
  linarith

theorem diff_vol {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (volume (A s \ A t)).toReal + (volume (A t \ A s)).toReal ≤ 3 * |s - t| := by
  rcases le_total t s with h | h
  · rw [abs_of_nonneg (by linarith)]; exact diff_vol_aux ht h
  · rw [abs_of_nonpos (by linarith), add_comm]
    have := diff_vol_aux hs h
    linarith

/-- the weighted harmonic sum over the common part -/
theorem K_sum {η : ℝ} (hη : 0 < η) (J : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hl : max s t = 0 ∨ 16 * η ≤ max s t) :
    ∑ j ∈ Finset.range J, W η (A s ∩ A t) j / (((j : ℝ) + 1) * η) ≤ 1 := by
  set l := max s t with hl_def
  have hKsub : A s ∩ A t ⊆ Set.Icc l (2 * l) := by
    intro x hx
    simp only [A, Set.mem_inter_iff, Set.mem_Icc] at hx
    obtain ⟨⟨a, b⟩, c, d⟩ := hx
    refine ⟨max_le a c, ?_⟩
    rcases le_total s t with h | h
    · rw [hl_def, max_eq_right h]; linarith
    · rw [hl_def, max_eq_left h]; linarith
  rcases hl with h0 | h16
  · have hl0 : l = 0 := h0
    have : ∀ j, W η (A s ∩ A t) j = 0 := by
      intro j
      rcases (W_nonneg η (A s ∩ A t) j).eq_or_lt with h | h
      · exact h.symm
      · exfalso
        obtain ⟨x, hx1, hx2⟩ := W_pos h
        have := hKsub hx2
        simp only [Set.mem_Icc, hl0] at this
        have h1 : x = 0 := by linarith [this.1, this.2]
        unfold cell at hx1
        simp only [Set.mem_Ico] at hx1
        nlinarith [hx1.1]
    simp [this]
  · have hlpos : 0 < l := by linarith
    have hKm : MeasurableSet (A s ∩ A t) := (A_meas s).inter (A_meas t)
    have hKfin : volume (A s ∩ A t) ≠ ⊤ :=
      ne_top_of_le_ne_top (A_fin s) (measure_mono Set.inter_subset_left)
    have hB : MeasurableSet (Set.Iio (3 * l / 2)) := measurableSet_Iio
    have hsplit : ∀ j, W η (A s ∩ A t) j =
        W η ((A s ∩ A t) ∩ Set.Iio (3 * l / 2)) j + W η ((A s ∩ A t) \ Set.Iio (3 * l / 2)) j :=
      fun j => W_add η _ _ hB j
    have hK1fin : volume ((A s ∩ A t) ∩ Set.Iio (3 * l / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top hKfin (measure_mono Set.inter_subset_left)
    have hK2fin : volume ((A s ∩ A t) \ Set.Iio (3 * l / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top hKfin (measure_mono Set.diff_subset)
    have i1 := inv_sum hη J (hKm.inter hB) hK1fin (a := l) (by linarith)
      (fun x hx => (hKsub hx.1).1)
    have i2 := inv_sum hη J (hKm.diff hB) hK2fin (a := 3 * l / 2) (by linarith)
      (fun x hx => by
        have := hx.2
        simp only [Set.mem_Iio, not_lt] at this
        exact this)
    have v1 : (volume ((A s ∩ A t) ∩ Set.Iio (3 * l / 2))).toReal ≤ l / 2 := by
      have : (A s ∩ A t) ∩ Set.Iio (3 * l / 2) ⊆ Set.Ico l (3 * l / 2) :=
        fun x hx => ⟨(hKsub hx.1).1, hx.2⟩
      have := vol_mono this (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)] at this
      linarith
    have v2 : (volume ((A s ∩ A t) \ Set.Iio (3 * l / 2))).toReal ≤ l / 2 := by
      have : (A s ∩ A t) \ Set.Iio (3 * l / 2) ⊆ Set.Icc (3 * l / 2) (2 * l) :=
        fun x hx => ⟨by have := hx.2; simpa using this, (hKsub hx.1).2⟩
      have := vol_mono this (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at this
      linarith
    have c1 : (volume ((A s ∩ A t) ∩ Set.Iio (3 * l / 2))).toReal / (l - η) ≤ 8 / 15 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have c2 : (volume ((A s ∩ A t) \ Set.Iio (3 * l / 2))).toReal / (3 * l / 2 - η) ≤ 8 / 23 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc ∑ j ∈ Finset.range J, W η (A s ∩ A t) j / (((j : ℝ) + 1) * η)
        = ∑ j ∈ Finset.range J, (W η ((A s ∩ A t) ∩ Set.Iio (3 * l / 2)) j / (((j : ℝ) + 1) * η)
          + W η ((A s ∩ A t) \ Set.Iio (3 * l / 2)) j / (((j : ℝ) + 1) * η)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hsplit j, add_div]
      _ ≤ 8 / 15 + 8 / 23 := by
          rw [Finset.sum_add_distrib]; linarith
      _ ≤ 1 := by norm_num

/-- the lower bound on the scale integral -/
theorem lower_core {η : ℝ} (hη : 0 < η) (J : ℕ) {s : ℝ} (hs16 : 16 * η ≤ s)
    (hsJ : 2 * s < ((J : ℝ) + 1) * η) {a : ℝ} (ha : 0 ≤ a) :
    (1 / 4) * min a s ≤
      ∑ j ∈ Finset.range J, W η (A s) j * (1 - Real.exp (-a / (2 * (((j : ℝ) + 1) * η)))) := by
  have hspos : 0 < s := by linarith
  set a' := min a s with ha'
  have ha'0 : 0 ≤ a' := le_min ha hspos.le
  have ha's : a' ≤ s := min_le_right _ _
  -- reduce to a'
  have step0 : ∑ j ∈ Finset.range J, W η (A s) j * (1 - Real.exp (-a' / (2 * (((j : ℝ) + 1) * η))))
      ≤ ∑ j ∈ Finset.range J, W η (A s) j * (1 - Real.exp (-a / (2 * (((j : ℝ) + 1) * η)))) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (W_nonneg _ _ _)
    have : -a / (2 * (((j : ℝ) + 1) * η)) ≤ -a' / (2 * (((j : ℝ) + 1) * η)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [min_le_left a s]
    have := Real.exp_le_exp.2 this
    linarith
  refine le_trans ?_ step0
  -- pieces
  let P : ℕ → Set ℝ := fun i => Set.Ico (s * (1 + (i : ℝ) / 4)) (s * (1 + ((i : ℝ) + 1) / 4))
  have hPmeas : ∀ i, MeasurableSet (P i) := fun i => measurableSet_Ico
  have hPsub : ∀ i ∈ Finset.range 4, P i ⊆ A s := by
    intro i hi x hx
    have : (i : ℝ) + 1 ≤ 4 := by exact_mod_cast Finset.mem_range.1 hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [P, Set.mem_Ico] at hx
    refine ⟨?_, ?_⟩
    · nlinarith [hx.1]
    · nlinarith [hx.2]
  have hPdisj : ∀ i ∈ Finset.range 4, ∀ k ∈ Finset.range 4, i ≠ k → Disjoint (P i) (P k) := by
    intro i _ k _ hik
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [P, Set.mem_Ico] at hx hx'
    rcases lt_or_gt_of_ne hik with h | h
    · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast h
      nlinarith [hx.2, hx'.1]
    · have : (k : ℝ) + 1 ≤ i := by exact_mod_cast h
      nlinarith [hx.1, hx'.2]
  have hcellsum : ∀ j, ∑ i ∈ Finset.range 4, W η (P i) j ≤ W η (A s) j := by
    intro j
    unfold W
    rw [← ENNReal.toReal_sum (fun i _ => ne_top_of_le_ne_top (cell_vol_ne_top η j)
      (measure_mono Set.inter_subset_left))]
    apply ENNReal.toReal_mono
    · exact ne_top_of_le_ne_top (cell_vol_ne_top η j) (measure_mono Set.inter_subset_left)
    · rw [← measure_biUnion_finset]
      · apply measure_mono
        intro x hx
        simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hx
        obtain ⟨i, hi, hx1, hx2⟩ := hx
        exact ⟨hx1, hPsub i (Finset.mem_range.2 hi) hx2⟩
      · intro i hi k hk hik
        exact (hPdisj i hi k hk hik).mono Set.inter_subset_right Set.inter_subset_right
      · intro i _
        exact (cell_meas η j).inter (hPmeas i)
  let E : ℕ → ℝ := fun j => 1 - Real.exp (-a' / (2 * (((j : ℝ) + 1) * η)))
  have hE0 : ∀ j, 0 ≤ E j := by
    intro j
    have : -a' / (2 * (((j : ℝ) + 1) * η)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have := Real.exp_le_one_iff.2 this
    simp only [E]; linarith
  have step1 : ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range J, W η (P i) j * E j
      ≤ ∑ j ∈ Finset.range J, W η (A s) j * E j := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcellsum j) (hE0 j)
  refine le_trans ?_ step1
  have step2 : ∀ i ∈ Finset.range 4,
      (s / 4) * (1 - Real.exp (-a' / (2 * (s * (1 + ((i : ℝ) + 1) / 4))))) ≤
        ∑ j ∈ Finset.range J, W η (P i) j * E j := by
    intro i hi
    have hi4 : (i : ℝ) + 1 ≤ 4 := by exact_mod_cast Finset.mem_range.1 hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hsum : ∑ j ∈ Finset.range J, W η (P i) j = s / 4 := by
      rw [sumW_eq_of_sub hη J (hPmeas i)]
      · simp only [P]
        rw [Real.volume_Ico, ENNReal.toReal_ofReal (by nlinarith)]
        ring
      · intro x hx
        have := hPsub i hi hx
        simp only [A, Set.mem_Icc] at this
        constructor <;> nlinarith [this.1, this.2]
    have := piece_bound (η := η) J (S := P i) (b := s * (1 + ((i : ℝ) + 1) / 4))
      (by positivity) (fun x hx => hx.2) hη ha'0
    rw [hsum] at this
    exact this
  refine le_trans ?_ (Finset.sum_le_sum step2)
  -- numeric
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  set t := a' / s with ht
  have ht0 : 0 ≤ t := div_nonneg ha'0 hspos.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hspos]; exact ha's
  have hat : a' = t * s := by rw [ht]; field_simp
  have e : ∀ c : ℝ, 0 < c → -a' / (2 * (s * c)) = -(t / (2 * c)) := by
    intro c hc
    rw [hat]; field_simp
  have b : ∀ c : ℝ, 0 < c → t / (2 * c) - (t / (2 * c)) ^ 2 / 2 ≤
      1 - Real.exp (-a' / (2 * (s * c))) := by
    intro c hc
    rw [e c hc]
    exact one_sub_exp_ge (by positivity)
  have b0 := b (1 + (0 + 1) / 4) (by norm_num)
  have b1 := b (1 + (1 + 1) / 4) (by norm_num)
  have b2 := b (1 + (2 + 1) / 4) (by norm_num)
  have b3 := b (1 + (3 + 1) / 4) (by norm_num)
  have hs4 : 0 ≤ s / 4 := by positivity
  have := mul_le_mul_of_nonneg_left b0 hs4
  have := mul_le_mul_of_nonneg_left b1 hs4
  have := mul_le_mul_of_nonneg_left b2 hs4
  have := mul_le_mul_of_nonneg_left b3 hs4
  have hnum : t ≤ (t / (2 * (1 + (0 + 1) / 4)) - (t / (2 * (1 + (0 + 1) / 4))) ^ 2 / 2) +
      (t / (2 * (1 + (1 + 1) / 4)) - (t / (2 * (1 + (1 + 1) / 4))) ^ 2 / 2) +
      (t / (2 * (1 + (2 + 1) / 4)) - (t / (2 * (1 + (2 + 1) / 4))) ^ 2 / 2) +
      (t / (2 * (1 + (3 + 1) / 4)) - (t / (2 * (1 + (3 + 1) / 4))) ^ 2 / 2) := by
    norm_num
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht1)]
  have hst : s / 4 * t = a' / 4 := by rw [hat]; ring
  nlinarith [mul_le_mul_of_nonneg_left hnum hs4]

end OuterplanarL1Tan.Dev.L6
end

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.L6

open MeasureTheory OuterplanarL1Tan.Linear

theorem l1norm1 {ι : Type} [Fintype ι] (f : ι → ℝ) :
    ‖WithLp.toLp 1 f‖ = ∑ i, |f i| := by
  rw [PiLp.norm_eq_of_nat 1 (by norm_num)]
  simp

theorem l1norm2 {ι : Type} [Fintype ι] (f g : ι → ℝ) :
    ‖WithLp.toLp 1 f - WithLp.toLp 1 g‖ = ∑ i, |f i - g i| := by
  rw [← WithLp.toLp_sub, PiLp.norm_eq_of_nat 1 (by norm_num)]
  simp

theorem scales {X : Type} [Fintype X] (h : X → ℝ) (nonnegative : ∀ x, 0 ≤ h x) :
    ∃ η : ℝ, 0 < η ∧ (∀ x, h x = 0 ∨ 16 * η ≤ h x) ∧
      ∃ J : ℕ, ∀ x, 2 * h x < ((J : ℝ) + 1) * η := by
  have hη : ∃ η : ℝ, 0 < η ∧ ∀ x, h x = 0 ∨ 16 * η ≤ h x := by
    by_cases hne : (Finset.univ.filter (fun x => 0 < h x)).Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := Finset.exists_min_image _ h hne
      have hx0' : 0 < h x0 := (Finset.mem_filter.1 hx0).2
      refine ⟨h x0 / 16, by positivity, fun x => ?_⟩
      rcases (nonnegative x).eq_or_lt with h0 | h0
      · exact Or.inl h0.symm
      · right
        have := hmin x (Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩)
        linarith
    · refine ⟨1, one_pos, fun x => ?_⟩
      left
      by_contra hc
      exact hne ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_ne (nonnegative x)
        (Ne.symm hc)⟩⟩
  obtain ⟨η, hη0, hη⟩ := hη
  refine ⟨η, hη0, hη, ?_⟩
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * (∑ x, h x) / η)
  refine ⟨J, fun x => ?_⟩
  have h1 : h x ≤ ∑ x, h x :=
    Finset.single_le_sum (fun y _ => nonnegative y) (Finset.mem_univ x)
  rw [div_lt_iff₀ hη0] at hJ
  nlinarith

end OuterplanarL1Tan.Dev.L6

namespace OuterplanarL1Tan.Linear

open OuterplanarL1Tan.Dev.L6 MeasureTheory

theorem chk_lemma_6 {X : Type} [Fintype X] (δ : X → X → ℝ)
    (isL1 : IsL1Distance δ) (h : X → ℝ) (nonnegative : ∀ x, 0 ≤ h x) :
    ∃ N : ℕ, ∃ Ψ : X → L1Vector N,
      (∀ x, ‖Ψ x‖ = h x) ∧
      (∀ x y, ‖Ψ x - Ψ y‖ ≤ δ x y + 3 * |h x - h y|) ∧
      (∀ x y, (1 / 4 : ℝ) * min (δ x y) (max (h x) (h y)) ≤
        ‖Ψ x - Ψ y‖) := by
  obtain ⟨η, hη, hηh, J, hJ⟩ := scales h nonnegative
  have hδ0 : ∀ x y, 0 ≤ δ x y := by
    obtain ⟨f, hf⟩ := isL1
    intro x y; rw [hf]; exact norm_nonneg _
  have hδsymm : ∀ x y, δ x y = δ y x := by
    obtain ⟨f, hf⟩ := isL1
    intro x y; rw [hf, hf, norm_sub_rev]
  choose M hF u hu0 hu1 hc hm using fun j : ℕ =>
    OuterplanarL1Tan.Dev.K.partition_map δ isL1 (((j : ℝ) + 1) * η) (by positivity)
  letI : ∀ j, Fintype (M j) := hF
  let ι : Type := Σ j : Fin J, M j.val
  let Ψ' : X → ι → ℝ := fun x p => W η (A (h x)) p.1.val * u p.1.val x p.2
  let e := Fintype.equivFin ι
  let Ψ : X → L1Vector (Fintype.card ι) := fun x =>
    WithLp.toLp 1 (fun k : Fin (Fintype.card ι) => Ψ' x (e.symm k))
  -- sums of W
  have Wsum : ∀ x, ∑ j ∈ Finset.range J, W η (A (h x)) j = h x := by
    intro x
    rcases (nonnegative x).eq_or_lt with h0 | h0
    · have := sumW_le hη J (A_meas (h x)) (A_fin (h x))
      rw [← h0] at this ⊢
      have h2 : (volume (A 0)).toReal = 0 := by simp [A]
      have h3 : 0 ≤ ∑ j ∈ Finset.range J, W η (A 0) j :=
        Finset.sum_nonneg (fun j _ => W_nonneg _ _ _)
      linarith
    · have h16 : 16 * η ≤ h x := (hηh x).resolve_left h0.ne'
      rw [sumW_eq_of_sub hη J (A_meas _)]
      · unfold A; rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
      · intro z hz
        simp only [A, Set.mem_Icc] at hz
        exact ⟨by linarith [hz.1], by linarith [hz.2, hJ x]⟩
  have Wnonneg : ∀ x j, 0 ≤ W η (A (h x)) j := fun x j => W_nonneg _ _ _
  have normPsi : ∀ x, ‖Ψ x‖ = h x := by
    intro x
    simp only [Ψ]
    rw [l1norm1]
    rw [Equiv.sum_comp e.symm (fun p => |Ψ' x p|)]
    rw [Fintype.sum_sigma, ← Wsum x, ← Fin.sum_univ_eq_sum_range (fun j => W η (A (h x)) j) J]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Ψ']
    have : ∀ i, |W η (A (h x)) j.val * u j.val x i| = W η (A (h x)) j.val * u j.val x i := by
      intro i; exact abs_of_nonneg (mul_nonneg (Wnonneg x _) (hu0 _ _ _))
    simp_rw [this]
    rw [← Finset.mul_sum, hu1, mul_one]
  have normDiff : ∀ x y, ‖Ψ x - Ψ y‖ = ∑ j ∈ Finset.range J,
      (|W η (A (h x)) j - W η (A (h y)) j| * Real.exp (-(δ x y) / (2 * (((j : ℝ) + 1) * η))) +
       (W η (A (h x)) j + W η (A (h y)) j) *
        (1 - Real.exp (-(δ x y) / (2 * (((j : ℝ) + 1) * η))))) := by
    intro x y
    simp only [Ψ]
    rw [l1norm2]
    rw [Equiv.sum_comp e.symm (fun p => |Ψ' x p - Ψ' y p|)]
    rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun j => |W η (A (h x)) j - W η (A (h y)) j| * Real.exp (-(δ x y) / (2 * (((j : ℝ) + 1) * η))) +
       (W η (A (h x)) j + W η (A (h y)) j) *
        (1 - Real.exp (-(δ x y) / (2 * (((j : ℝ) + 1) * η))))) J]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Ψ']
    rw [cell_l1 (u j.val x) (u j.val y) (hu1 _ _) (hu1 _ _) (hc _ x y) (hu0 _ x) (hu0 _ y)
      _ _ (Wnonneg x _) (Wnonneg y _), hm]
  have mbounds : ∀ (x y : X) (j : ℕ), 0 ≤ Real.exp (-(δ x y) / (2 * (((j : ℝ) + 1) * η))) ∧
      Real.exp (-(δ x y) / (2 * (((j : ℝ) + 1) * η))) ≤ 1 := by
    intro x y j
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 ?_⟩
    have hr : 0 < ((j : ℝ) + 1) * η := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hδ0 x y]) (by linarith)
  refine ⟨Fintype.card ι, Ψ, normPsi, ?_, ?_⟩
  · -- upper bound
    intro x y
    rw [normDiff]
    set a := δ x y with ha
    have ha0 : 0 ≤ a := hδ0 x y
    have hx : ∀ j, W η (A (h x)) j = W η (A (h x) ∩ A (h y)) j + W η (A (h x) \ A (h y)) j :=
      fun j => W_add η _ _ (A_meas _) j
    have hy : ∀ j, W η (A (h y)) j = W η (A (h x) ∩ A (h y)) j + W η (A (h y) \ A (h x)) j := by
      intro j
      rw [Set.inter_comm]; exact W_add η _ _ (A_meas _) j
    have hcell : ∀ j, (|W η (A (h x)) j - W η (A (h y)) j| * Real.exp (-a / (2 * (((j : ℝ) + 1) * η))) +
       (W η (A (h x)) j + W η (A (h y)) j) *
        (1 - Real.exp (-a / (2 * (((j : ℝ) + 1) * η))))) ≤
        W η (A (h x) \ A (h y)) j + W η (A (h y) \ A (h x)) j +
          W η (A (h x) ∩ A (h y)) j / (((j : ℝ) + 1) * η) * a := by
      intro j
      have hrp : 0 < ((j : ℝ) + 1) * η := by positivity
      obtain ⟨m0, m1⟩ := mbounds x y j
      rw [hx j, hy j]
      refine le_trans (cell_upper _ _ _ _ m0 m1 (W_nonneg _ _ _) (W_nonneg _ _ _)
        (W_nonneg _ _ _)) ?_
      have h1 : 1 - Real.exp (-a / (2 * (((j : ℝ) + 1) * η))) ≤ a / (2 * (((j : ℝ) + 1) * η)) := by
        have := one_sub_exp_le (a / (2 * (((j : ℝ) + 1) * η)))
        rwa [← neg_div] at this
      have hk := W_nonneg η (A (h x) ∩ A (h y)) j
      have : 2 * W η (A (h x) ∩ A (h y)) j * (1 - Real.exp (-a / (2 * (((j : ℝ) + 1) * η)))) ≤
          W η (A (h x) ∩ A (h y)) j / (((j : ℝ) + 1) * η) * a := by
        calc _ ≤ 2 * W η (A (h x) ∩ A (h y)) j * (a / (2 * (((j : ℝ) + 1) * η))) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = _ := by field_simp
      linarith
    refine le_trans (Finset.sum_le_sum (fun j _ => hcell j)) ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have s1 := sumW_le hη J ((A_meas _).diff (A_meas (h y))) (ne_top_of_le_ne_top (A_fin (h x))
      (measure_mono Set.diff_subset))
    have s2 := sumW_le hη J ((A_meas _).diff (A_meas (h x))) (ne_top_of_le_ne_top (A_fin (h y))
      (measure_mono Set.diff_subset))
    have s3 := diff_vol (nonnegative x) (nonnegative y)
    have s4 : ∑ j ∈ Finset.range J, W η (A (h x) ∩ A (h y)) j / (((j : ℝ) + 1) * η) * a ≤ a := by
      rw [← Finset.sum_mul]
      have := K_sum hη J (nonnegative x) (nonnegative y) (by
        rcases hηh x with h1 | h1 <;> rcases hηh y with h2 | h2
        · left; rw [h1, h2]; simp
        · right; exact le_trans h2 (le_max_right _ _)
        · right; exact le_trans h1 (le_max_left _ _)
        · right; exact le_trans h1 (le_max_left _ _))
      nlinarith
    linarith
  · -- lower bound
    have low : ∀ x y, (1 / 4 : ℝ) * min (δ x y) (h x) ≤ ‖Ψ x - Ψ y‖ := by
      intro x y
      rcases (nonnegative x).eq_or_lt with h0 | h0
      · have : min (δ x y) (h x) ≤ 0 := by rw [← h0]; exact min_le_right _ _
        have := norm_nonneg (Ψ x - Ψ y)
        linarith
      · have h16 : 16 * η ≤ h x := (hηh x).resolve_left h0.ne'
        rw [normDiff]
        refine le_trans (lower_core hη J h16 (hJ x) (hδ0 x y)) ?_
        apply Finset.sum_le_sum
        intro j _
        obtain ⟨m0, m1⟩ := mbounds x y j
        exact cell_lower _ _ _ m0 m1 (Wnonneg x j) (Wnonneg y j)
    intro x y
    rcases le_total (h y) (h x) with hh | hh
    · rw [max_eq_left hh]; exact low x y
    · rw [max_eq_right hh, hδsymm x y, norm_sub_rev]; exact low y x

end OuterplanarL1Tan.Linear
end

theorem solution : type_of% @OuterplanarL1Tan.Linear.chk_lemma_6 := @OuterplanarL1Tan.Linear.chk_lemma_6
