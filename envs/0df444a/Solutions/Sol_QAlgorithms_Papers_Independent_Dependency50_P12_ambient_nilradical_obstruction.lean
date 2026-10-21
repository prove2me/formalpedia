-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.ambient_nilradical_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T09:29:37.011956+00:00
-- url     : https://prove2.me/submissions/4ec57289-1fdf-4030-96ec-69bd69a7a3d0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

open QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup



theorem g55a_lim {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [ContinuousAdd X] [ContinuousSMul ℝ X]
    {W : Set X} (hcl : IsClosed W) (hc : IsCone W) {w u : X}
    (h : ∀ s : ℝ, w + s • u ∈ W) : u ∈ W := by
  have ht : Filter.Tendsto (fun l : ℝ => l⁻¹ • w + u) Filter.atTop (nhds u) := by
    have := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const w).add_const u
    simpa using this
  refine hcl.mem_of_tendsto ht ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with l hl
  have := hc.2.2 l⁻¹ (inv_nonneg.2 hl.le) _ (h l)
  rwa [smul_add, smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at this

theorem g55a_expAd_nil {n : ℕ} (T w : affineAlgebra n) (h : ⁅T, ⁅T, w⁆⁆ = 0) :
    expAd T w = w + ⁅T, w⁆ := by
  unfold expAd
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, adMap]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have h2 : (adMap T ^ 2) w = 0 := by
      simp [pow_two, adMap, h]
    have hz : ∀ m : ℕ, (adMap T ^ (m + 2)) w = 0 := by
      intro m
      rw [pow_add, Module.End.mul_apply, h2, map_zero]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [hz, smul_zero]

theorem g55a_aff_pos (m : ℕ) :
    ¬ (∃ W : Set (affineAlgebra (m+1)), IsClosed W ∧ IsCone W ∧ edge W = {0} ∧
      (∀ X : affineAlgebra (m+1), ∃ Y ∈ W, ∃ Z ∈ W, X = Y - Z) ∧
      (∀ X : affineAlgebra (m+1), expAd X '' W ⊆ W)) := by
  rintro ⟨W, hcl, hc, hedge, hgen, hinv⟩
  have : ContinuousSMul ℝ (affineAlgebra (m+1)) :=
    inferInstanceAs (ContinuousSMul ℝ (affineAlgebra (m+1)).toSubmodule)
  have hl : (Fin.last (m+1)) ≠ 0 := by simp [Fin.ext_iff]
  let X0 : affineAlgebra (m+1) := ⟨Matrix.single 0 0 1, by
    intro j; simp [Matrix.single_apply, hl]⟩
  let T : affineAlgebra (m+1) := ⟨Matrix.single 0 (Fin.last (m+1)) 1, by
    intro j; simp [Matrix.single_apply, hl]⟩
  -- find w ∈ W with w 0 0 ≠ 0
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W, (w : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0 ≠ 0 := by
    obtain ⟨Y, hY, Z, hZ, hXYZ⟩ := hgen X0
    have h := congrArg (fun M : affineAlgebra (m+1) => (M : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0) hXYZ
    change (Matrix.single (0 : Fin (m+2)) (0 : Fin (m+2)) (1:ℝ)) 0 0 =
      (Y : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0 - (Z : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0 at h
    by_cases hY0 : (Y : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 0 = 0
    · refine ⟨Z, hZ, ?_⟩
      intro hZ0; rw [hY0, hZ0] at h; simp at h
    · exact ⟨Y, hY, hY0⟩
  have hwl : ∀ j, (w : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) (Fin.last (m+1)) j = 0 := w.2
  have h1 : (T : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) * w = 0 := by
    ext i j; simp [T, Matrix.mul_apply, Matrix.single_apply, hwl, ite_and]
  have h2 : (T : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) * T = 0 := by
    ext i j; simp [T, Matrix.mul_apply, Matrix.single_apply, hl.symm, ite_and]
  have hT0 : ⁅T, ⁅T, w⁆⁆ = 0 := by
    apply Subtype.ext
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def]
    simp only [mul_sub, sub_mul, ← Matrix.mul_assoc, h1, h2, Matrix.zero_mul, Matrix.mul_zero]
    rw [Matrix.mul_assoc (w : Matrix (Fin (m+2)) (Fin (m+2)) ℝ), h2]
    simp
  have hTT : ∀ s : ℝ, ⁅s • T, ⁅s • T, w⁆⁆ = 0 := by
    intro s
    simp [smul_lie, lie_smul, hT0]
  set u := ⁅T, w⁆ with hu
  have hu0 : u ≠ 0 := by
    intro h
    have := congrArg (fun M : affineAlgebra (m+1) =>
      (M : Matrix (Fin (m+2)) (Fin (m+2)) ℝ) 0 (Fin.last (m+1))) h
    simp only [hu, LieSubalgebra.coe_bracket, Ring.lie_def, h1, Matrix.sub_apply] at this
    simp [T, Matrix.mul_apply, Matrix.single_apply] at this
    exact hw0 this
  have hline : ∀ s : ℝ, w + s • u ∈ W := by
    intro s
    have hm := hinv (s • T) ⟨w, hw, rfl⟩
    rw [g55a_expAd_nil _ _ (hTT s), smul_lie] at hm
    exact hm
  have hu1 : u ∈ W := g55a_lim hcl hc hline
  have hu2 : -u ∈ W := g55a_lim hcl hc (fun s => by simpa using hline (-s))
  have : u ∈ edge W := ⟨hu1, hu2⟩
  rw [hedge] at this
  exact hu0 this

theorem g55a_aff_zero_sub (X : affineAlgebra 0) : X = 0 := by
  apply Subtype.ext
  ext i j
  have hi : i = Fin.last 0 := by
    apply Fin.ext
    have hbound : i.val < 1 := i.isLt
    omega
  subst hi
  exact X.2 j

namespace G56N

variable {n : ℕ}

lemma ne_last {i : Fin (n+1)} (hi : i.val < n) : i ≠ Fin.last n := by
  intro h; rw [h] at hi; simp at hi

def el (i j : Fin (n+1)) (hi : i.val < n) : affineAlgebra n :=
  ⟨Matrix.single i j 1, by
    intro m; simp [Matrix.single_apply, ne_last hi]⟩

def tr (i : Fin (n+1)) (hi : i.val < n) : affineAlgebra n := el i (Fin.last n) hi

lemma coe_lie (X Y : affineAlgebra n) :
    ((⁅X, Y⁆ : affineAlgebra n) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) =
      (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) * Y - Y * X := by
  rw [LieSubalgebra.coe_bracket, Ring.lie_def]

lemma last_row (X : affineAlgebra n) (j : Fin (n+1)) : (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (Fin.last n) j = 0 :=
  X.2 j

lemma tr_ne (i : Fin (n+1)) (hi : i.val < n) : tr i hi ≠ 0 := by
  intro h
  have := congrArg (fun X : affineAlgebra n => (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i (Fin.last n)) h
  simp [tr, el] at this

/-- Nilpotency kills eigenvalues of ad on translations. -/
lemma nil_zero (I : LieIdeal ℝ (affineAlgebra n)) [LieModule.IsNilpotent I I] (Z : affineAlgebra n)
    (hZ : Z ∈ I) (i : Fin (n+1)) (hi : i.val < n) (c : ℝ) (h : ⁅Z, tr i hi⁆ = c • tr i hi) : c = 0 := by
  have hy : ⁅Z, tr i hi⁆ ∈ I := by
    rw [← lie_skew]; exact neg_mem (I.lie_mem hZ)
  obtain ⟨N, hN⟩ := LieModule.isNilpotent_toEnd_of_isNilpotent ℝ I I ⟨Z, hZ⟩
  have key : ∀ m : ℕ, (((LieModule.toEnd ℝ I I ⟨Z, hZ⟩ ^ m) ⟨_, hy⟩ : I) : affineAlgebra n) =
      c ^ (m + 1) • tr i hi := by
    intro m
    induction m with
    | zero => simp [h]
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply, LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket, ih]
      simp only [lie_smul, h, smul_smul, pow_succ]
  have := key N
  rw [hN] at this
  simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at this
  have h2 : c ^ (N + 1) = 0 := by
    by_contra hc
    exact tr_ne i hi (smul_eq_zero.mp this.symm |>.resolve_left hc)
  exact pow_eq_zero_iff (Nat.succ_ne_zero N) |>.mp h2

lemma offdiag (I : LieIdeal ℝ (affineAlgebra n)) [LieModule.IsNilpotent I I] (Z : affineAlgebra n)
    (hZ : Z ∈ I) (i j : Fin (n+1)) (hi : i.val < n) (hj : j.val < n) (hij : i ≠ j) :
    (Z : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i j = 0 := by
  have h3 : ⁅el i j hi, ⁅el j i hj, ⁅el j i hj, Z⁆⁆⁆ ∈ I :=
    I.lie_mem (I.lie_mem (I.lie_mem hZ))
  have hc := nil_zero I _ h3 i hi (-2 * (Z : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i j) ?_
  · linarith
  apply Subtype.ext
  have hl : Fin.last n ≠ i := (ne_last hi).symm
  have hl' : Fin.last n ≠ j := (ne_last hj).symm
  have hi' : i ≠ Fin.last n := ne_last hi
  have hj' : j ≠ Fin.last n := ne_last hj
  have e1 : ∀ {p q : Fin (n+1)}, p ≠ q → ∀ (a b : Fin (n+1)) (x y : ℝ),
      Matrix.single a p x * Matrix.single q b y = 0 := by
    intro p q h a b x y
    exact Matrix.single_mul_single_of_ne x a p q h y
  rw [coe_lie, coe_lie, coe_lie, coe_lie]
  simp only [tr, el]
  simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, Matrix.single_mul_mul_single,
    Matrix.single_mul_single_same, e1 hij,
    e1 hij.symm, e1 hl,
    e1 hl', e1 hi',
    e1 hj', Matrix.zero_mul, Matrix.mul_zero, sub_zero, zero_sub]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.single_mul_mul_single,
    Matrix.single_mul_single_same, e1 hij,
    e1 hij.symm, e1 hl,
    e1 hl', e1 hi',
    e1 hj', Matrix.zero_mul, Matrix.mul_zero, sub_zero, zero_sub]
  ext a b
  simp [Matrix.single_apply]
  split_ifs <;> ring

lemma diag (I : LieIdeal ℝ (affineAlgebra n)) [LieModule.IsNilpotent I I] (Z : affineAlgebra n)
    (hZ : Z ∈ I) (i : Fin (n+1)) (hi : i.val < n) :
    (Z : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i i = 0 := by
  apply nil_zero I Z hZ i hi
  apply Subtype.ext
  rw [coe_lie]
  rw [show (((Z : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i i • tr i hi : affineAlgebra n) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) =
    (Z : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i i • Matrix.single i (Fin.last n) 1 from rfl]
  ext a b
  have hz := last_row Z
  change ((Z : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) * (Matrix.single i (Fin.last n) 1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) a b -
    ((Matrix.single i (Fin.last n) 1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) * (Z : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) a b =
    (Z : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i i * Matrix.single i (Fin.last n) (1 : ℝ) a b
  by_cases hb : b = Fin.last n
  · subst hb
    rw [Matrix.mul_single_apply_same]
    by_cases ha : a = i
    · subst ha; rw [Matrix.single_mul_apply_same, hz]; simp
    · rw [Matrix.single_mul_apply_of_ne (h := ha)]
      simp only [Matrix.single_apply, Ne.symm ha, false_and, and_true, if_false, mul_zero, mul_one, sub_zero]
      by_cases hl : a = Fin.last n
      · subst hl; exact hz _
      · have : a.val < n := by
          have := a.2; have h2 : a.val ≠ n := fun h => hl (Fin.ext (by simpa using h)); omega
        exact offdiag I Z hZ a i this hi ha
  · rw [Matrix.mul_single_apply_of_ne (hbj := hb)]
    by_cases ha : a = i
    · subst ha; rw [Matrix.single_mul_apply_same, hz]; simp [Matrix.single_apply, Ne.symm hb]
    · rw [Matrix.single_mul_apply_of_ne (h := ha)]; simp [Matrix.single_apply, Ne.symm hb]

lemma sub_trans (I : LieIdeal ℝ (affineAlgebra n)) [LieModule.IsNilpotent I I] (Z : affineAlgebra n)
    (hZ : Z ∈ I) : Z ∈ affineTranslations n := by
  intro i j hi hj
  by_cases h : i = j
  · subst h; exact diag I Z hZ i hi
  · exact offdiag I Z hZ i j hi hj h

lemma trans_mul (X Y : affineAlgebra n) (hY : Y ∈ affineTranslations n) (hX : X ∈ affineTranslations n) :
    (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) * Y = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : m = Fin.last n
  · subst hm; simp [last_row Y]
  · have hmn : m.val < n := by
      have := m.2; have h2 : m.val ≠ n := fun h => hm (Fin.ext (by simpa using h)); omega
    by_cases ha : a = Fin.last n
    · subst ha; simp [last_row X]
    · have han : a.val < n := by
        have := a.2; have h2 : a.val ≠ n := fun h => ha (Fin.ext (by simpa using h)); omega
      simp [hX a m han hmn]

def T (n : ℕ) : LieIdeal ℝ (affineAlgebra n) where
  carrier := affineTranslations n
  add_mem' := by
    intro X Y hX hY i j hi hj
    simp [hX i j hi hj, hY i j hi hj]
  zero_mem' := by intro i j _ _; rfl
  smul_mem' := by
    intro c X hX i j hi hj
    simp [hX i j hi hj]
  lie_mem := by
    intro X Y hY i j hi hj
    rw [coe_lie]
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    have h1 : ∀ m, (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i m * (Y : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) m j = 0 := by
      intro m
      by_cases hm : m = Fin.last n
      · subst hm; simp [last_row Y]
      · have hmn : m.val < n := by
          have := m.2; have h2 : m.val ≠ n := fun h => hm (Fin.ext (by simpa using h)); omega
        simp [hY m j hmn hj]
    have h2 : ∀ m, (Y : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i m * (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) m j = 0 := by
      intro m
      by_cases hm : m = Fin.last n
      · subst hm; simp [last_row X]
      · have hmn : m.val < n := by
          have := m.2; have h2 : m.val ≠ n := fun h => hm (Fin.ext (by simpa using h)); omega
        simp [hY i m hi hmn]
    simp [h1, h2]

instance T_abelian (n : ℕ) : IsLieAbelian (T n) := by
  constructor
  intro x y
  apply Subtype.ext
  rw [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket]
  apply Subtype.ext
  rw [coe_lie, trans_mul _ _ y.2 x.2, trans_mul _ _ x.2 y.2]
  simp

end G56N

open G56N in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ((QAlgorithms.Papers.Independent.Dependency50.P12.nilradical : LieIdeal ℝ (affineAlgebra (d^2-1))) : Set (affineAlgebra (d^2-1))) =
      affineTranslations (d^2-1) ∧
    (∀ X Y : affineAlgebra (d^2-1), X ∈ QAlgorithms.Papers.Independent.Dependency50.P12.nilradical → Y ∈ QAlgorithms.Papers.Independent.Dependency50.P12.nilradical → ⁅X,Y⁆ = 0) ∧
    (∀ xi : affineAlgebra (d^2-1) →ₗ[ℝ] ℝ, ∀ X Y : affineAlgebra (d^2-1),
      X ∈ QAlgorithms.Papers.Independent.Dependency50.P12.nilradical → Y ∈ QAlgorithms.Papers.Independent.Dependency50.P12.nilradical → xi ⁅X,Y⁆ = 0) ∧
    ¬ (∃ W : Set (affineAlgebra (d^2-1)), IsClosed W ∧ IsCone W ∧ edge W = {0} ∧
      (∀ X : affineAlgebra (d^2-1), ∃ Y ∈ W, ∃ Z ∈ W, X = Y-Z) ∧
      ∀ X : affineAlgebra (d^2-1), expAd X '' W ⊆ W) := by
  have hle : (QAlgorithms.Papers.Independent.Dependency50.P12.nilradical : LieIdeal ℝ (affineAlgebra (d^2-1))) ≤ T (d^2-1) :=
    sSup_le fun I hI => by
      haveI : LieModule.IsNilpotent I I := hI
      exact fun Z hZ => sub_trans I Z hZ
  have hge : T (d^2-1) ≤ (QAlgorithms.Papers.Independent.Dependency50.P12.nilradical : LieIdeal ℝ (affineAlgebra (d^2-1))) :=
    le_sSup (show LieModule.IsNilpotent (T (d^2-1)) (T (d^2-1)) from inferInstance)
  have heq : ((QAlgorithms.Papers.Independent.Dependency50.P12.nilradical : LieIdeal ℝ (affineAlgebra (d^2-1))) : Set (affineAlgebra (d^2-1))) =
      affineTranslations (d^2-1) := by
    ext X
    exact ⟨fun h => hle h, fun h => hge (show X ∈ T (d^2-1) from h)⟩
  have hbr : ∀ X Y : affineAlgebra (d^2-1), X ∈ QAlgorithms.Papers.Independent.Dependency50.P12.nilradical → Y ∈ QAlgorithms.Papers.Independent.Dependency50.P12.nilradical → ⁅X,Y⁆ = 0 := by
    intro X Y hX hY
    have hX' : X ∈ affineTranslations (d^2-1) := hle hX
    have hY' : Y ∈ affineTranslations (d^2-1) := hle hY
    apply Subtype.ext
    rw [coe_lie, trans_mul _ _ hY' hX', trans_mul _ _ hX' hY']
    simp
  refine ⟨heq, hbr, fun xi X Y hX hY => by rw [hbr X Y hX hY, map_zero], ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, d^2 - 1 = m + 1 := ⟨d^2 - 2, by
    have : 4 ≤ d^2 := by nlinarith
    omega⟩
  have := g55a_aff_pos m
  rw [← hm] at this
  exact this
