-- Prove2me | solution 1 for RLInference.QValueCLT.theorem_1_q_value_clt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T14:22:47.865088+00:00
-- url     : https://prove2.me/submissions/5f0fd6f7-a0f8-4282-9f14-e0040fbcaaf0

import Mathlib
import Definitions.Def_RLInference_QValueCLT_Setting


set_option autoImplicit false

open MeasureTheory Filter Topology Finset

namespace M1

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- cylinder weight -/
noncomputable def wt (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (xs : Fin (n + 1) → X) : ℝ :=
  ν (xs 0) * ∏ i : Fin n, P (xs i.castSucc) (xs i.succ)

/-- path increment sum -/
def pathS (h : X → X → ℝ) (n : ℕ) (xs : Fin (n + 1) → X) : ℝ :=
  ∑ k : Fin n, h (xs k.castSucc) (xs k.succ)

lemma wt_snoc (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (xs : Fin (n + 1) → X) (y : X) :
    wt P ν (n + 1) (Fin.snoc xs y : Fin (n + 2) → X) = wt P ν n xs * P (xs (Fin.last n)) y := by
  unfold wt
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc xs y : Fin (n + 2) → X) 0 = xs 0 := by
    simp
  rw [h0]
  have h1 : ∀ i : Fin n, P ((Fin.snoc xs y : Fin (n + 2) → X) i.castSucc.castSucc)
      ((Fin.snoc xs y : Fin (n + 2) → X) i.castSucc.succ) = P (xs i.castSucc) (xs i.succ) := by
    intro i
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  have h2 : P ((Fin.snoc xs y : Fin (n + 2) → X) (Fin.last n).castSucc)
      ((Fin.snoc xs y : Fin (n + 2) → X) (Fin.last n).succ) = P (xs (Fin.last n)) y := by
    rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  simp only [h1, h2]
  ring

lemma sum_snoc {M : Type*} [AddCommMonoid M] (n : ℕ) (F : (Fin (n + 2) → X) → M) :
    ∑ xs : Fin (n + 2) → X, F xs =
      ∑ xs : Fin (n + 1) → X, ∑ y : X, F (Fin.snoc xs y) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => X)).sum_comp]
  rw [Fintype.sum_prod_type_right]
  rfl

lemma pathS_snoc (h : X → X → ℝ) (n : ℕ) (xs : Fin (n + 1) → X) (y : X) :
    pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X) = pathS h n xs + h (xs (Fin.last n)) y := by
  unfold pathS
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

/-- expectation over paths -/
noncomputable def EE (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (G : (Fin (n + 1) → X) → ℝ) : ℝ :=
  ∑ xs : Fin (n + 1) → X, wt P ν n xs * G xs

lemma EE_succ (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (F : (Fin (n + 2) → X) → ℝ) :
    EE P ν (n + 1) F = ∑ xs : Fin (n + 1) → X, wt P ν n xs *
      ∑ y : X, P (xs (Fin.last n)) y * F (Fin.snoc xs y) := by
  unfold EE
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun xs _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [wt_snoc]; ring

lemma wt_nonneg (P : Matrix X X ℝ) (ν : X → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hν : ∀ x, 0 ≤ ν x)
    (n : ℕ) (xs : Fin (n + 1) → X) : 0 ≤ wt P ν n xs :=
  mul_nonneg (hν _) (Finset.prod_nonneg fun i _ => hP _ _)

lemma EE_mono (P : Matrix X X ℝ) (ν : X → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hν : ∀ x, 0 ≤ ν x)
    (n : ℕ) {F G : (Fin (n + 1) → X) → ℝ} (hFG : ∀ xs, F xs ≤ G xs) :
    EE P ν n F ≤ EE P ν n G :=
  Finset.sum_le_sum fun xs _ => mul_le_mul_of_nonneg_left (hFG xs) (wt_nonneg P ν hP hν n xs)

lemma EE_one (P : Matrix X X ℝ) (ν : X → ℝ) (hrow : ∀ x, ∑ y, P x y = 1)
    (hν1 : ∑ x, ν x = 1) (n : ℕ) : EE P ν n (fun _ => 1) = 1 := by
  induction n with
  | zero =>
    unfold EE wt
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [← hν1]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) _ _ (fun x => by simp)
  | succ n ih =>
    rw [EE_succ]
    simp only [mul_one, hrow]
    simpa [EE] using ih

lemma EE_const (P : Matrix X X ℝ) (ν : X → ℝ) (hrow : ∀ x, ∑ y, P x y = 1)
    (hν1 : ∑ x, ν x = 1) (n : ℕ) (c : ℝ) : EE P ν n (fun _ => c) = c := by
  have := EE_one P ν hrow hν1 n
  unfold EE at this ⊢
  simp only [← Finset.sum_mul, mul_comm _ c, ← Finset.mul_sum] at this ⊢
  have h1 : ∑ i : Fin (n + 1) → X, wt P ν n i = 1 := by simpa using this
  rw [h1, mul_one]

lemma EE_add (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (F G : (Fin (n + 1) → X) → ℝ) :
    EE P ν n (fun xs => F xs + G xs) = EE P ν n F + EE P ν n G := by
  unfold EE; simp [mul_add, Finset.sum_add_distrib]

lemma EE_smul (P : Matrix X X ℝ) (ν : X → ℝ) (n : ℕ) (c : ℝ) (F : (Fin (n + 1) → X) → ℝ) :
    EE P ν n (fun xs => c * F xs) = c * EE P ν n F := by
  unfold EE; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun xs _ => ?_; ring

/-- moment of the increment kernel -/
noncomputable def aj (P : Matrix X X ℝ) (h : X → X → ℝ) (j : ℕ) (x : X) : ℝ :=
  ∑ y, P x y * h x y ^ j

lemma aj_abs_le (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (h : X → X → ℝ) (B : ℝ) (hB : ∀ x y, |h x y| ≤ B) (j : ℕ) (x : X) :
    |aj P h j x| ≤ B ^ j := by
  unfold aj
  calc |∑ y, P x y * h x y ^ j| ≤ ∑ y, |P x y * h x y ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, P x y * B ^ j := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (hP x y), abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hB x y) j) (hP x y)
    _ = B ^ j := by rw [← Finset.sum_mul, hrow, one_mul]

lemma inner2 (P : Matrix X X ℝ) (hrow : ∀ x, ∑ y, P x y = 1) (h : X → X → ℝ)
    (hh : ∀ x, ∑ y, P x y * h x y = 0) (x : X) (s : ℝ) :
    ∑ y, P x y * (s + h x y) ^ 2 = s ^ 2 + aj P h 2 x := by
  have : ∀ y, P x y * (s + h x y) ^ 2 =
      s ^ 2 * P x y + 2 * s * (P x y * h x y) + P x y * h x y ^ 2 := fun y => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hrow, hh, aj]
  ring

lemma inner4 (P : Matrix X X ℝ) (hrow : ∀ x, ∑ y, P x y = 1) (h : X → X → ℝ)
    (hh : ∀ x, ∑ y, P x y * h x y = 0) (x : X) (s : ℝ) :
    ∑ y, P x y * (s + h x y) ^ 4 =
      s ^ 4 + 6 * s ^ 2 * aj P h 2 x + 4 * s * aj P h 3 x + aj P h 4 x := by
  have : ∀ y, P x y * (s + h x y) ^ 4 =
      s ^ 4 * P x y + 4 * s ^ 3 * (P x y * h x y) + 6 * s ^ 2 * (P x y * h x y ^ 2)
        + 4 * s * (P x y * h x y ^ 3) + P x y * h x y ^ 4 := fun y => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hrow, hh, aj]
  ring

lemma pathS_abs_le (h : X → X → ℝ) (B : ℝ) (hB : ∀ x y, |h x y| ≤ B) (n : ℕ)
    (xs : Fin (n + 1) → X) : |pathS h n xs| ≤ n * B := by
  unfold pathS
  calc |∑ k : Fin n, h (xs k.castSucc) (xs k.succ)|
      ≤ ∑ k : Fin n, |h (xs k.castSucc) (xs k.succ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, B := Finset.sum_le_sum fun k _ => hB _ _
    _ = n * B := by simp

lemma moment2 (P : Matrix X X ℝ) (ν : X → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (h : X → X → ℝ)
    (hh : ∀ x, ∑ y, P x y * h x y = 0) (B : ℝ) (hB : ∀ x y, |h x y| ≤ B) (n : ℕ) :
    EE P ν n (fun xs => pathS h n xs ^ 2) ≤ n * B ^ 2 := by
  induction n with
  | zero => simp [EE, pathS]
  | succ n ih =>
    rw [EE_succ]
    have e : ∀ xs : Fin (n + 1) → X, ∑ y, P (xs (Fin.last n)) y *
        (pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X)) ^ 2 =
        pathS h n xs ^ 2 + aj P h 2 (xs (Fin.last n)) := fun xs => by
      simp only [pathS_snoc]
      exact inner2 P hrow h hh _ _
    have : ∑ xs : Fin (n + 1) → X, wt P ν n xs * ∑ y, P (xs (Fin.last n)) y *
        (pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X)) ^ 2 =
        EE P ν n (fun xs => pathS h n xs ^ 2 + aj P h 2 (xs (Fin.last n))) := by
      unfold EE; exact Finset.sum_congr rfl fun xs _ => by rw [e]
    rw [this]
    have hle : EE P ν n (fun xs => pathS h n xs ^ 2 + aj P h 2 (xs (Fin.last n))) ≤
        EE P ν n (fun xs => pathS h n xs ^ 2 + B ^ 2) :=
      EE_mono P ν hP hν n fun xs => by
        have := aj_abs_le P hP hrow h B hB 2 (xs (Fin.last n))
        linarith [(abs_le.mp this).2]
    have hR : EE P ν n (fun xs => pathS h n xs ^ 2 + B ^ 2) =
        EE P ν n (fun xs => pathS h n xs ^ 2) + B ^ 2 := by
      rw [EE_add, EE_const P ν hrow hν1]
    rw [hR] at hle
    push_cast
    nlinarith [hle, ih]

lemma moment4 (P : Matrix X X ℝ) (ν : X → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (h : X → X → ℝ)
    (hh : ∀ x, ∑ y, P x y * h x y = 0) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x y, |h x y| ≤ B) (n : ℕ) :
    EE P ν n (fun xs => pathS h n xs ^ 4) ≤ 10 * B ^ 4 * (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp [EE, pathS]
  | succ n ih =>
    rw [EE_succ]
    have e : ∀ xs : Fin (n + 1) → X, ∑ y, P (xs (Fin.last n)) y *
        (pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X)) ^ 4 =
        pathS h n xs ^ 4 + 6 * pathS h n xs ^ 2 * aj P h 2 (xs (Fin.last n))
          + 4 * pathS h n xs * aj P h 3 (xs (Fin.last n)) + aj P h 4 (xs (Fin.last n)) :=
      fun xs => by
        simp only [pathS_snoc]
        exact inner4 P hrow h hh _ _
    have : ∑ xs : Fin (n + 1) → X, wt P ν n xs * ∑ y, P (xs (Fin.last n)) y *
        (pathS h (n + 1) (Fin.snoc xs y : Fin (n + 2) → X)) ^ 4 =
        EE P ν n (fun xs => pathS h n xs ^ 4 + 6 * pathS h n xs ^ 2 * aj P h 2 (xs (Fin.last n))
          + 4 * pathS h n xs * aj P h 3 (xs (Fin.last n)) + aj P h 4 (xs (Fin.last n))) := by
      unfold EE; exact Finset.sum_congr rfl fun xs _ => by rw [e]
    rw [this]
    have hle : EE P ν n (fun xs => pathS h n xs ^ 4 + 6 * pathS h n xs ^ 2 * aj P h 2 (xs (Fin.last n))
          + 4 * pathS h n xs * aj P h 3 (xs (Fin.last n)) + aj P h 4 (xs (Fin.last n))) ≤
        EE P ν n (fun xs => (pathS h n xs ^ 4 + (6 * B ^ 2) * pathS h n xs ^ 2)
          + (4 * n * B ^ 4 + B ^ 4)) := by
      refine EE_mono P ν hP hν n fun xs => ?_
      have a2 := (abs_le.mp (aj_abs_le P hP hrow h B hB 2 (xs (Fin.last n)))).2
      have a4 := (abs_le.mp (aj_abs_le P hP hrow h B hB 4 (xs (Fin.last n)))).2
      have a3 := aj_abs_le P hP hrow h B hB 3 (xs (Fin.last n))
      have hs := pathS_abs_le h B hB n xs
      have hm : |pathS h n xs * aj P h 3 (xs (Fin.last n))| ≤ n * B * B ^ 3 := by
        rw [abs_mul]
        exact mul_le_mul hs a3 (abs_nonneg _) (by positivity)
      have hm' := (abs_le.mp hm).2
      have hsq : 0 ≤ pathS h n xs ^ 2 := sq_nonneg _
      have h6 : 6 * pathS h n xs ^ 2 * aj P h 2 (xs (Fin.last n)) ≤ 6 * B ^ 2 * pathS h n xs ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left a2 hsq]
      nlinarith [h6, hm', a4]
    have hR : EE P ν n (fun xs => (pathS h n xs ^ 4 + (6 * B ^ 2) * pathS h n xs ^ 2)
          + (4 * n * B ^ 4 + B ^ 4)) = EE P ν n (fun xs => pathS h n xs ^ 4)
          + (6 * B ^ 2) * EE P ν n (fun xs => pathS h n xs ^ 2) + (4 * n * B ^ 4 + B ^ 4) := by
      rw [EE_add, EE_add, EE_smul, EE_const P ν hrow hν1]
    rw [hR] at hle
    have h2 := moment2 P ν hP hrow hν hν1 h hh B hB n
    have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
    have hB4 : 0 ≤ B ^ 4 := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith [hle, ih, mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 6 * B ^ 2),
      mul_nonneg hn hB4]

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

lemma cyl_meas (Z : ℕ → Ω → X) (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (n : ℕ) (xs : Fin (n + 1) → X) : MeasurableSet {ω | ∀ i : Fin (n + 1), Z i ω = xs i} := by
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => hmeas _ _

lemma measurable_path (Z : ℕ → Ω → X) (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (n : ℕ) {β : Type*} [MeasurableSpace β] (G : (Fin (n + 1) → X) → β) :
    Measurable (fun ω => G (fun i : Fin (n + 1) => Z i ω)) := by
  letI : MeasurableSpace (Fin (n + 1) → X) := ⊤
  have hW : Measurable (fun ω => (fun i : Fin (n + 1) => Z i ω)) := by
    refine measurable_to_countable' fun xs => ?_
    have : (fun ω => (fun i : Fin (n + 1) => Z i ω)) ⁻¹' {xs} =
        {ω | ∀ i : Fin (n + 1), Z i ω = xs i} := by
      ext ω; simp [funext_iff]
    rw [this]; exact cyl_meas Z hmeas n xs
  exact (measurable_from_top (f := G)).comp hW

lemma lintegral_path (μ : Measure Ω) (Z : ℕ → Ω → X)
    (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (n : ℕ) (G : (Fin (n + 1) → X) → ENNReal) :
    ∫⁻ ω, G (fun i : Fin (n + 1) => Z i ω) ∂μ =
      ∑ xs : Fin (n + 1) → X, G xs * μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} := by
  have key : ∀ ω, G (fun i : Fin (n + 1) => Z i ω) =
      ∑ xs : Fin (n + 1) → X,
        ({ω | ∀ i : Fin (n + 1), Z i ω = xs i}).indicator (fun _ => G xs) ω := by
    intro ω
    rw [Finset.sum_eq_single (fun i : Fin (n + 1) => Z i ω)]
    · simp [Set.indicator]
    · intro xs _ hne
      have : ω ∉ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} := by
        intro hω
        apply hne
        funext i
        exact (hω i).symm
      simp [Set.indicator_of_notMem this]
    · simp
  simp_rw [key]
  rw [lintegral_finset_sum]
  · refine Finset.sum_congr rfl fun xs _ => ?_
    rw [lintegral_indicator_const (cyl_meas Z hmeas n xs)]
  · intro xs _
    exact measurable_const.indicator (cyl_meas Z hmeas n xs)

end Meas

lemma pathS_eq_range {Ω : Type*} (Z : ℕ → Ω → X) (h : X → X → ℝ) (t : ℕ) (ω : Ω) :
    pathS h t (fun i : Fin (t + 1) => Z i ω) = ∑ k ∈ Finset.range t, h (Z k ω) (Z (k + 1) ω) := by
  unfold pathS
  have := Fin.sum_univ_eq_sum_range (fun k => h (Z k ω) (Z (k + 1) ω)) t
  rw [← this]
  simp

theorem markov_mds_slln {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (ν : X → ℝ) (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (Z : ℕ → Ω → X) (hmeas : ∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x})
    (hlaw : ∀ (n : ℕ) (xs : Fin (n + 1) → X),
      μ {ω | ∀ i : Fin (n + 1), Z i ω = xs i} =
        ENNReal.ofReal (ν (xs 0) * ∏ i : Fin n, P (xs i.castSucc) (xs i.succ)))
    (h : X → X → ℝ) (hh : ∀ x, ∑ y, P x y * h x y = 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℕ => (1 / (t : ℝ)) * ∑ k ∈ Finset.range t, h (Z k ω) (Z (k + 1) ω))
      atTop (𝓝 0) := by
  set B : ℝ := ∑ x, ∑ y, |h x y| with hBdef
  have hB : ∀ x y, |h x y| ≤ B := fun x y =>
    (Finset.single_le_sum (f := fun y => |h x y|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ y)).trans
      (Finset.single_le_sum (f := fun x => ∑ y, |h x y|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ x))
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  let f : ℕ → Ω → ENNReal := fun t ω =>
    ENNReal.ofReal ((pathS h t (fun i : Fin (t + 1) => Z i ω) / t) ^ 4)
  have hfm : ∀ t, Measurable (f t) := fun t =>
    measurable_path Z hmeas t (fun xs => ENNReal.ofReal ((pathS h t xs / t) ^ 4))
  have hint : ∀ t, ∫⁻ ω, f t ω ∂μ ≤ ENNReal.ofReal (10 * B ^ 4 / (t : ℝ) ^ 2) := by
    intro t
    have := lintegral_path μ Z hmeas t (fun xs => ENNReal.ofReal ((pathS h t xs / t) ^ 4))
    show ∫⁻ ω, ENNReal.ofReal ((pathS h t (fun i : Fin (t + 1) => Z i ω) / t) ^ 4) ∂μ ≤ _
    rw [this]
    simp_rw [hlaw]
    have hw : ∀ xs : Fin (t + 1) → X, ν (xs 0) * ∏ i : Fin t, P (xs i.castSucc) (xs i.succ)
        = wt P ν t xs := fun _ => rfl
    simp_rw [hw]
    calc ∑ xs : Fin (t + 1) → X, ENNReal.ofReal ((pathS h t xs / t) ^ 4) *
          ENNReal.ofReal (wt P ν t xs)
        = ∑ xs : Fin (t + 1) → X, ENNReal.ofReal ((pathS h t xs / t) ^ 4 * wt P ν t xs) :=
          Finset.sum_congr rfl fun xs _ => (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (∑ xs : Fin (t + 1) → X, (pathS h t xs / t) ^ 4 * wt P ν t xs) :=
          (ENNReal.ofReal_sum_of_nonneg fun xs _ =>
            mul_nonneg (by positivity) (wt_nonneg P ν hP hν t xs)).symm
      _ ≤ ENNReal.ofReal (10 * B ^ 4 / (t : ℝ) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          have e1 : ∑ xs : Fin (t + 1) → X, (pathS h t xs / t) ^ 4 * wt P ν t xs =
              EE P ν t (fun xs => (1 / (t : ℝ) ^ 4) * pathS h t xs ^ 4) := by
            unfold EE
            refine Finset.sum_congr rfl fun xs _ => ?_
            rw [div_pow]; ring
          rw [e1, EE_smul]
          rcases Nat.eq_zero_or_pos t with rfl | ht
          · simp
          · have m4 := moment4 P ν hP hrow hν hν1 h hh B hB0 hB t
            have htpos : (0 : ℝ) < t := by exact_mod_cast ht
            calc 1 / (t : ℝ) ^ 4 * EE P ν t (fun xs => pathS h t xs ^ 4)
                ≤ 1 / (t : ℝ) ^ 4 * (10 * B ^ 4 * (t : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left m4 (by positivity)
              _ = 10 * B ^ 4 / (t : ℝ) ^ 2 := by field_simp
  have hsumm : Summable (fun t : ℕ => 10 * B ^ 4 / (t : ℝ) ^ 2) :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (10 * B ^ 4)).congr
      fun t => by rw [mul_one_div]
  have hsum : ∑' t, ∫⁻ ω, f t ω ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' t : ℕ, ENNReal.ofReal (10 * B ^ 4 / (t : ℝ) ^ 2)) ?_
      (ENNReal.tsum_le_tsum hint)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity) hsumm]
    exact ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ ω ∂μ, ∑' t, f t ω < ⊤ := by
    have hm : Measurable (fun ω => ∑' t, f t ω) := Measurable.ennreal_tsum hfm
    have hl : ∫⁻ ω, ∑' t, f t ω ∂μ ≠ ⊤ := by
      rw [lintegral_tsum (fun t => (hfm t).aemeasurable)]; exact hsum
    exact ae_lt_top hm hl
  filter_upwards [hlt] with ω hω
  have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h1 : Tendsto (fun t : ℕ => (pathS h t (fun i : Fin (t + 1) => Z i ω) / t) ^ 4)
      atTop (𝓝 0) := by
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    rw [ENNReal.toReal_zero] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp, f]
    exact ENNReal.toReal_ofReal (by positivity)
  have h3 : Tendsto (fun t : ℕ => pathS h t (fun i : Fin (t + 1) => Z i ω) / t) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at h1 ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h1 (ε ^ 4) (by positivity)
    refine ⟨N, fun t ht => ?_⟩
    have h4 := hN t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h4
    rw [Real.dist_eq, sub_zero]
    by_contra hcon
    push_neg at hcon
    have h5 : ε ^ 4 ≤ |pathS h t (fun i : Fin (t + 1) => Z i ω) / t| ^ 4 :=
      pow_le_pow_left₀ hε.le hcon 4
    rw [Even.pow_abs (by decide)] at h5
    linarith
  refine h3.congr fun t => ?_
  rw [pathS_eq_range]
  ring

end M1


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace QVCLT40192638

section ChainStep

variable {X : Type*} [MeasurableSpace X] (κ : Kernel X X) [IsMarkovKernel κ] (lam : Measure X)

lemma chain_eq_traj :
    MarkovChainCLT.chainMeasure κ lam =
      Kernel.trajMeasure (X := fun _ ↦ X) lam
        (BanditAlgorithm.markovChainStep κ) := by
  rw [MarkovChainCLT.chainMeasure, BanditAlgorithm.markovChainKernel, Kernel.trajMeasure]
  ext s hs
  rw [Measure.bind_apply hs (by fun_prop), Measure.bind_apply hs (by fun_prop),
    lintegral_map (Kernel.measurable_coe _ hs) (by fun_prop)]
  rfl

lemma chain_step_measure [IsProbabilityMeasure lam] (n : ℕ) :
    (MarkovChainCLT.chainMeasure κ lam).map (Preorder.frestrictLe n) ⊗ₘ
        BanditAlgorithm.markovChainStep κ n =
      (MarkovChainCLT.chainMeasure κ lam).map
        (fun ω ↦ (Preorder.frestrictLe n ω, ω (n + 1))) := by
  rw [chain_eq_traj]
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- One-step integral identity (tower property) for the chain measure. -/
lemma chain_step_integral [IsProbabilityMeasure lam] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) (F : (Finset.Iic n → X) × X → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hC : ∀ p, ‖F p‖ ≤ C) :
    ∫ ω, F (Preorder.frestrictLe n ω, ω (n + 1)) ∂(MarkovChainCLT.chainMeasure κ lam) =
      ∫ ω, (∫ z, F (Preorder.frestrictLe n ω, z) ∂(κ (ω n)))
        ∂(MarkovChainCLT.chainMeasure κ lam) := by
  set μ := MarkovChainCLT.chainMeasure κ lam
  have hg : Measurable (fun ω : ℕ → X ↦ (Preorder.frestrictLe n ω, ω (n + 1))) := by fun_prop
  rw [← integral_map hg.aemeasurable hF.aestronglyMeasurable, ← chain_step_measure]
  have hint : Integrable F (μ.map (Preorder.frestrictLe n) ⊗ₘ
      BanditAlgorithm.markovChainStep κ n) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Eventually.of_forall hC)
  rw [Measure.integral_compProd hint]
  have hm : StronglyMeasurable (fun h : Finset.Iic n → X ↦
      ∫ z, F (h, z) ∂(BanditAlgorithm.markovChainStep κ n h)) :=
    hF.integral_kernel_prod_right'
  rw [integral_map (Preorder.measurable_frestrictLe n).aemeasurable hm.aestronglyMeasurable]
  rfl

lemma chain_map_zero [IsProbabilityMeasure lam] :
    (MarkovChainCLT.chainMeasure κ lam).map (fun ω ↦ ω 0) = lam := by
  have h3 : (MarkovChainCLT.chainMeasure κ lam).map (fun ω ↦ ω 0) =
      ((MarkovChainCLT.chainMeasure κ lam).map (Preorder.frestrictLe 0)).map
        (fun h : Finset.Iic 0 → X ↦ h ⟨0, by simp⟩) := by
    have hm : Measurable (fun h : Finset.Iic 0 → X ↦ h ⟨0, by simp⟩) := by fun_prop
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs, Measure.map_apply hm hs,
      Measure.map_apply (Preorder.measurable_frestrictLe 0) (hm hs)]
    rfl
  rw [h3,
    chain_eq_traj, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_map (measurable_pi_apply _) (MeasurableEquiv.measurable _)]
  have h2 : ((fun h : Finset.Iic 0 → X ↦ h ⟨0, by simp⟩) ∘
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ X)).symm) = id := by
    funext x; rfl
  rw [h2, Measure.map_id]

lemma chain_cyl_step [IsProbabilityMeasure lam] (n : ℕ) (A : Set (Finset.Iic n → X))
    (hA : MeasurableSet A) (B : Set X) (hB : MeasurableSet B) :
    MarkovChainCLT.chainMeasure κ lam {ω | Preorder.frestrictLe n ω ∈ A ∧ ω (n + 1) ∈ B} =
      ∫⁻ ω in Preorder.frestrictLe n ⁻¹' A, κ (ω n) B ∂(MarkovChainCLT.chainMeasure κ lam) := by
  have hset : {ω : ℕ → X | Preorder.frestrictLe n ω ∈ A ∧ ω (n + 1) ∈ B} =
      (fun ω ↦ (Preorder.frestrictLe n ω, ω (n + 1))) ⁻¹' (A ×ˢ B) := rfl
  rw [hset, ← Measure.map_apply (by fun_prop) (hA.prod hB), ← chain_step_measure,
    Measure.compProd_apply_prod hA hB,
    setLIntegral_map hA (Kernel.measurable_coe _ hB) (Preorder.measurable_frestrictLe n)]
  rfl

end ChainStep

section DataChain

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]

open RLInference.QValueCLT

lemma mixture_fst (c : S × A → ENNReal) (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)]
    (y : S × A) :
    (∑ y' : S × A, c y' • (Measure.dirac y').prod (R y')) {p | p.1 = y} = c y := by
  have hset : {p : (S × A) × ℝ | p.1 = y} = {y} ×ˢ Set.univ := by ext p; simp
  rw [hset, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, measure_univ, mul_one]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    rw [Measure.dirac_apply' _ (measurableSet_singleton y)]
    simp [Set.indicator, Ne.symm hb, hb]
  · simp

lemma data_cyl (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (ν₀ : PMF S) (n : ℕ) (xs : Fin (n + 1) → S × A) :
    MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)
        {ω | ∀ i : Fin (n + 1), (ω i).1 = xs i} =
      ENNReal.ofReal ((ν₀ (xs 0).1).toReal * (π (xs 0).1 (xs 0).2).toReal *
        ∏ i : Fin n, Ptilde P π (xs i.castSucc) (xs i.succ)) := by
  induction n with
  | zero =>
    have hset : {ω : ℕ → (S × A) × ℝ | ∀ i : Fin (0 + 1), (ω i).1 = xs i} =
        (fun ω ↦ ω 0) ⁻¹' {p | p.1 = xs 0} := by
      ext ω; simp [Fin.forall_fin_one]
    rw [hset, ← Measure.map_apply (measurable_pi_apply 0)
      (show MeasurableSet {p : (S × A) × ℝ | p.1 = xs 0} from
        measurable_fst (measurableSet_singleton _)), chain_map_zero, initLaw, mixture_fst]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  | succ n ih =>
    set Aset : Set (Finset.Iic n → (S × A) × ℝ) :=
      {h | ∀ i : Fin (n + 1), (h ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩).1 = xs i.castSucc}
      with hAdef
    have hA : MeasurableSet Aset := by
      rw [hAdef, Set.ofPred_forall]
      exact MeasurableSet.iInter fun i =>
        (measurable_fst.comp (measurable_pi_apply _)) (measurableSet_singleton _)
    have hB : MeasurableSet {p : (S × A) × ℝ | p.1 = xs (Fin.last (n + 1))} :=
      measurable_fst (measurableSet_singleton _)
    have hset : {ω : ℕ → (S × A) × ℝ | ∀ i : Fin (n + 1 + 1), (ω i).1 = xs i} =
        {ω | Preorder.frestrictLe (π := fun _ : ℕ ↦ (S × A) × ℝ) n ω ∈ Aset ∧
          ω (n + 1) ∈ {p | p.1 = xs (Fin.last (n + 1))}} := by
      ext ω
      simp only [Set.mem_setOf_eq, hAdef, Preorder.frestrictLe_apply]
      rw [Fin.forall_fin_succ']
      simp
    have hpre : Preorder.frestrictLe (π := fun _ : ℕ ↦ (S × A) × ℝ) n ⁻¹' Aset =
        {ω | ∀ i : Fin (n + 1), (ω i).1 = xs i.castSucc} := by
      ext ω; simp [hAdef, Preorder.frestrictLe_apply]
    rw [hset, chain_cyl_step _ _ n Aset hA _ hB]
    have hc : ∀ ω ∈ Preorder.frestrictLe (π := fun _ : ℕ ↦ (S × A) × ℝ) n ⁻¹' Aset,
        dataKernel P π R (ω n) {p | p.1 = xs (Fin.last (n + 1))} =
          P (xs (Fin.last n).castSucc) (xs (Fin.last (n + 1))).1 *
            π (xs (Fin.last (n + 1))).1 (xs (Fin.last (n + 1))).2 := by
      intro ω hω
      rw [hpre] at hω
      have h1 : (ω n).1 = xs (Fin.last n).castSucc := by
        have := hω (Fin.last n); simpa using this
      show dataStep P π R (ω n).1 _ = _
      rw [h1, dataStep, mixture_fst]
    rw [setLIntegral_congr_fun ((Preorder.measurable_frestrictLe n) hA) hc, setLIntegral_const,
      hpre, ih (fun i => xs i.castSucc)]
    rw [Fin.prod_univ_castSucc, ← ENNReal.ofReal_toReal (a := P _ _ * π _ _)
      (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)), ← ENNReal.ofReal_mul']
    · congr 1
      simp only [Ptilde, Pmat, ENNReal.toReal_mul, Fin.succ_castSucc, Fin.castSucc_zero,
        Fin.succ_last]
      ring
    · unfold Ptilde Pmat; positivity

end DataChain

end QVCLT40192638


set_option autoImplicit false

open Filter Topology Matrix

namespace QVCLT40192638

section Stationary

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma pow_entry_nonneg (M : Matrix ι ι ℝ) (hM0 : ∀ x y, 0 ≤ M x y) (m : ℕ) :
    ∀ x y, 0 ≤ (M ^ m) x y := by
  induction m with
  | zero => intro x y; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ m ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hM0 z y)

lemma vecMul_pow_of_inv (M : Matrix ι ι ℝ) (v : ι → ℝ) (hv : Matrix.vecMul v M = v) (m : ℕ) :
    Matrix.vecMul v (M ^ m) = v := by
  induction m with
  | zero => rw [pow_zero, Matrix.vecMul_one]
  | succ m ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hv]

/-- A nonnegative invariant vector of an irreducible nonnegative matrix that is positive
somewhere is positive everywhere. -/
lemma inv_pos_everywhere (M : Matrix ι ι ℝ) (hM0 : ∀ x y, 0 ≤ M x y)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (M ^ m) x y) (v : ι → ℝ) (hv0 : ∀ x, 0 ≤ v x)
    (hv : Matrix.vecMul v M = v) (x : ι) (hx : 0 < v x) (y : ι) : 0 < v y := by
  obtain ⟨m, hm⟩ := hirr x y
  have h := congrFun (vecMul_pow_of_inv M v hv m) y
  rw [Matrix.vecMul, dotProduct] at h
  rw [← h]
  have hle : v x * (M ^ m) x y ≤ ∑ z, v z * (M ^ m) z y :=
    Finset.single_le_sum (f := fun z => v z * (M ^ m) z y)
      (fun z _ => mul_nonneg (hv0 z) (pow_entry_nonneg M hM0 m z y)) (Finset.mem_univ x)
  exact lt_of_lt_of_le (mul_pos hx hm) hle

/-- Uniqueness of the stationary law: an invariant vector with zero sum vanishes. -/
lemma stat_unique (M : Matrix ι ι ℝ) (hM0 : ∀ x y, 0 ≤ M x y) (hM1 : ∀ x, ∑ y, M x y = 1)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (M ^ m) x y) (d : ι → ℝ)
    (hd : ∀ y, ∑ x, d x * M x y = d y) (hs : ∑ x, d x = 0) : d = 0 := by
  -- |d| is invariant
  have hle : ∀ y, |d y| ≤ ∑ x, |d x| * M x y := by
    intro y
    rw [← hd y]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_mul, abs_of_nonneg (hM0 x y)]
  have hsum : ∑ y, (∑ x, |d x| * M x y - |d y|) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hM1, mul_one, sub_self]
  have habs : ∀ y, ∑ x, |d x| * M x y = |d y| := by
    intro y
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sub_nonneg.2 (hle y))).1 hsum y
      (Finset.mem_univ y)
    linarith
  -- positive and negative parts are invariant
  set p : ι → ℝ := fun x => (|d x| + d x) / 2 with hp
  set q : ι → ℝ := fun x => (|d x| - d x) / 2 with hq
  have hpinv : Matrix.vecMul p M = p := by
    funext y
    simp only [Matrix.vecMul, dotProduct, hp, add_div, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div,
      ← Finset.sum_div, habs, hd]
  have hqinv : Matrix.vecMul q M = q := by
    funext y
    simp only [Matrix.vecMul, dotProduct, hq, sub_div, sub_mul, Finset.sum_sub_distrib, div_mul_eq_mul_div,
      ← Finset.sum_div, habs, hd]
  have hp0 : ∀ x, 0 ≤ p x := fun x => by
    simp only [hp]; linarith [neg_abs_le (d x)]
  have hq0 : ∀ x, 0 ≤ q x := fun x => by
    simp only [hq]; linarith [le_abs_self (d x)]
  funext x
  rcases lt_trichotomy (d x) 0 with h | h | h
  · exfalso
    have hqx : 0 < q x := by simp only [hq]; rw [abs_of_neg h]; linarith
    have hall : ∀ y, d y < 0 := by
      intro y
      have := inv_pos_everywhere M hM0 hirr q hq0 hqinv x hqx y
      simp only [hq] at this
      by_contra hc; push Not at hc; rw [abs_of_nonneg hc] at this; linarith
    have : ∑ y, d y < 0 := Finset.sum_neg (fun y _ => hall y) ⟨x, Finset.mem_univ x⟩
    linarith
  · exact h
  · exfalso
    have hpx : 0 < p x := by simp only [hp]; rw [abs_of_pos h]; linarith
    have hall : ∀ y, 0 < d y := by
      intro y
      have := inv_pos_everywhere M hM0 hirr p hp0 hpinv x hpx y
      simp only [hp] at this
      by_contra hc; push Not at hc; rw [abs_of_nonpos hc] at this; linarith
    have : 0 < ∑ y, d y := Finset.sum_pos (fun y _ => hall y) ⟨x, Finset.mem_univ x⟩
    linarith

/-- Empirical frequencies that are asymptotically invariant converge to the stationary law. -/
lemma tendsto_stat (M : Matrix ι ι ℝ) (hM0 : ∀ x y, 0 ≤ M x y) (hM1 : ∀ x, ∑ y, M x y = 1)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (M ^ m) x y) (w : ι → ℝ) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * M x y = w y) (f : ℕ → ι → ℝ)
    (hf1 : ∀ᶠ n in atTop, ∑ x, f n x = 1)
    (hf : ∀ y, Tendsto (fun n => ∑ x, f n x * M x y - f n y) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 w) := by
  let T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) × ℝ :=
    { toFun := fun d => (fun y => ∑ x, d x * M x y - d y, ∑ x, d x)
      map_add' := by
        intro a b
        ext y <;> simp [Finset.sum_add_distrib, add_mul] <;> ring
      map_smul' := by
        intro c a
        ext y <;> simp [Finset.mul_sum, mul_assoc, mul_sub] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd0
    have h1 := congrArg Prod.fst hd0
    have h2 := congrArg Prod.snd hd0
    refine stat_unique M hM0 hM1 hirr d (fun y => ?_) h2
    have := congrFun h1 y
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_zero, Pi.zero_apply] at this
    linarith
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T (LinearMap.ker_eq_bot.2 hinj)
  have hgc : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hT : Tendsto (fun n => T (f n - w)) atTop (𝓝 0) := by
    rw [Prod.zero_eq_mk, nhds_prod_eq]
    refine Tendsto.prodMk ?_ ?_
    · rw [tendsto_pi_nhds]
      intro y
      have this : ∀ n, ∑ x, (f n - w) x * M x y - (f n - w) y =
          (∑ x, f n x * M x y - f n y) - (∑ x, w x * M x y - w y) := by
        intro n
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        ring
      simp_rw [this, hw_stat y, sub_self, sub_zero]
      simpa using hf y
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hf1] with n hn
      simp only [T, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Finset.sum_sub_distrib, hn,
        hw_sum, sub_self]
  have h3 : Tendsto (fun n => g (T (f n - w))) atTop (𝓝 0) := by
    have := (hgc.tendsto 0).comp hT
    rw [map_zero] at this
    exact this
  have h4 : (fun n => g (T (f n - w))) = fun n => f n - w := by
    funext n
    exact congrFun (congrArg DFunLike.coe hg) (f n - w)
  rw [h4] at h3
  simpa using h3.add_const w

end Stationary

end QVCLT40192638


namespace QVCLT40192638

section C1pair

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]

open RLInference.QValueCLT MeasureTheory ProbabilityTheory Filter Topology

omit [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma pt_nonneg (P : S × A → PMF S) (π : S → PMF A) (x y : S × A) :
    0 ≤ Ptilde P π x y := by
  unfold Ptilde Pmat
  positivity

omit [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma pmf_toReal_sum {T : Type} [Fintype T] (μ : PMF T) : ∑ a, (μ a).toReal = 1 := by
  have h : ∑ a, μ a = 1 := (tsum_fintype _).symm.trans μ.tsum_coe
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ _), h, ENNReal.toReal_one]

omit [DecidableEq A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma pt_fst (P : S × A → PMF S) (π : S → PMF A) (x : S × A) (k : S) :
    ∑ y, Ptilde P π x y * (if y.1 = k then (1 : ℝ) else 0) = Pmat P x k := by
  unfold Ptilde
  simp only [mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.mul_sum, pmf_toReal_sum, mul_one]

omit [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma pt_row (P : S × A → PMF S) (π : S → PMF A) (x : S × A) :
    ∑ y, Ptilde P π x y = 1 := by
  unfold Ptilde
  rw [Fintype.sum_prod_type]
  simp only
  simp_rw [← Finset.mul_sum, pmf_toReal_sum, mul_one]
  unfold Pmat
  exact pmf_toReal_sum (P x)

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma visits_eq (n : ℕ) (ω : ℕ → (S × A) × ℝ) (y : S × A) :
    (visits n ω y : ℝ) = ∑ k ∈ Finset.range n, if (ω k).1 = y then (1 : ℝ) else 0 := by
  unfold visits
  rw [Finset.natCast_card_filter]

/-- the M1 Markov SLLN applied to the state-action chain of the data process -/
lemma chain_slln (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (ν₀ : PMF S) (h : S × A → S × A → ℝ)
    (hh : ∀ x, ∑ y, Ptilde P π x y * h x y = 0) :
    ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      Tendsto (fun t : ℕ => (1 / (t : ℝ)) * ∑ k ∈ Finset.range t, h (ω k).1 (ω (k + 1)).1)
        atTop (𝓝 0) := by
  have hν1 : ∑ x : S × A, (ν₀ x.1).toReal * (π x.1 x.2).toReal = 1 := by
    simp_rw [← ENNReal.toReal_mul]
    rw [← ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _)), sum_pmf_mul_pmf, ENNReal.toReal_one]
  have hmeas : ∀ (n : ℕ) (x : S × A), MeasurableSet {ω : ℕ → (S × A) × ℝ | (ω n).1 = x} :=
    fun n x => (measurable_fst.comp (measurable_pi_apply n)) (measurableSet_singleton x)
  exact M1.markov_mds_slln (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
    (Ptilde P π) (pt_nonneg P π) (pt_row P π)
    (fun x => (ν₀ x.1).toReal * (π x.1 x.2).toReal) (fun x => by positivity) hν1
    (fun t ω => (ω t).1) hmeas (fun n xs => data_cyl P π R ν₀ n xs) h hh

/-- visit frequencies converge to the stationary law -/
lemma visits_ae (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (ν₀ : PMF S)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) :
    ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      Tendsto (fun n : ℕ => fun x => (visits n ω x : ℝ) / n) atTop (𝓝 w) := by
  have hall : ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      ∀ z : S × A, Tendsto (fun t : ℕ => (1 / (t : ℝ)) * ∑ k ∈ Finset.range t,
        ((if (ω (k + 1)).1 = z then (1 : ℝ) else 0) - Ptilde P π (ω k).1 z)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro z
    refine chain_slln P π R ν₀ (fun x' y => (if y = z then (1 : ℝ) else 0) - Ptilde P π x' z) ?_
    intro x
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, pt_row, one_mul, sub_self]
  filter_upwards [hall] with ω hω
  refine tendsto_stat (Ptilde P π) (pt_nonneg P π) (pt_row P π) hirr w hw_sum hw_stat _ ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← Finset.sum_div]
    simp_rw [visits_eq]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    have : (n : ℝ) ≠ 0 := by positivity
    exact div_self this
  · intro y
    have h1 := (hω y).neg
    rw [neg_zero] at h1
    have h2 : Tendsto (fun n : ℕ => ((if (ω n).1 = y then (1 : ℝ) else 0) -
        (if (ω 0).1 = y then (1 : ℝ) else 0)) / (n : ℝ)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat 2)
      rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
      gcongr
      split_ifs <;> norm_num
    have key : ∀ n : ℕ, ∑ x, (visits n ω x : ℝ) / n * Ptilde P π x y - (visits n ω y : ℝ) / n =
        -((1 / (n : ℝ)) * ∑ k ∈ Finset.range n,
          ((if (ω (k + 1)).1 = y then (1 : ℝ) else 0) - Ptilde P π (ω k).1 y)) +
        ((if (ω n).1 = y then (1 : ℝ) else 0) - (if (ω 0).1 = y then (1 : ℝ) else 0)) / (n : ℝ) := by
      intro n
      have hB : ∑ x, (visits n ω x : ℝ) * Ptilde P π x y =
          ∑ k ∈ Finset.range n, Ptilde P π (ω k).1 y := by
        simp_rw [visits_eq, Finset.sum_mul, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hS : ∑ x, (visits n ω x : ℝ) / n * Ptilde P π x y =
          (∑ x, (visits n ω x : ℝ) * Ptilde P π x y) / n := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun x _ => by ring
      have hc1 := Finset.sum_range_succ (fun k => if (ω k).1 = y then (1 : ℝ) else 0) n
      have hc2 := Finset.sum_range_succ' (fun k => if (ω k).1 = y then (1 : ℝ) else 0) n
      rw [hS, hB, visits_eq, Finset.sum_sub_distrib]
      have hac : ∑ k ∈ Finset.range n, (if (ω (k + 1)).1 = y then (1 : ℝ) else 0) =
          ∑ k ∈ Finset.range n, (if (ω k).1 = y then (1 : ℝ) else 0) +
            (if (ω n).1 = y then (1 : ℝ) else 0) - (if (ω 0).1 = y then (1 : ℝ) else 0) := by
        linarith
      rw [hac]
      ring
    simp_rw [key]
    simpa using h1.add h2

/-- empirical transition probabilities converge -/
lemma PHat_ae (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (ν₀ : PMF S) (p0 : S × A → S → ℝ)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) :
    ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      ∀ x k, Tendsto (fun n => PHat p0 n ω x k) atTop (𝓝 (Pmat P x k)) := by
  have hall : ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      ∀ q : (S × A) × S, Tendsto (fun t : ℕ => (1 / (t : ℝ)) * ∑ k ∈ Finset.range t,
        (if (ω k).1 = q.1 then (1 : ℝ) else 0) *
          ((if (ω (k + 1)).1.1 = q.2 then (1 : ℝ) else 0) - Pmat P q.1 q.2)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro q
    refine chain_slln P π R ν₀ (fun x' y => (if x' = q.1 then (1 : ℝ) else 0) *
      ((if y.1 = q.2 then (1 : ℝ) else 0) - Pmat P q.1 q.2)) ?_
    intro x
    by_cases hx : x = q.1
    · subst hx
      simp only [if_true, one_mul, mul_sub, Finset.sum_sub_distrib, pt_fst, ← Finset.sum_mul,
        pt_row, sub_self]
    · simp [hx]
  filter_upwards [hall, visits_ae P π R ν₀ hirr w hw_sum hw_stat] with ω hω hv x k
  have hvx : Tendsto (fun n : ℕ => (visits n ω x : ℝ) / n) atTop (𝓝 (w x)) :=
    (continuous_apply x).continuousAt.tendsto.comp hv
  have hpc : Tendsto (fun n : ℕ => (((Finset.range n).filter fun t => (ω t).1 = x ∧
      (ω (t + 1)).1.1 = k).card : ℝ) / n) atTop (𝓝 (w x * Pmat P x k)) := by
    have e : ∀ n : ℕ, (((Finset.range n).filter fun t => (ω t).1 = x ∧
        (ω (t + 1)).1.1 = k).card : ℝ) / n =
        (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (if (ω j).1 = x then (1 : ℝ) else 0) *
          ((if (ω (j + 1)).1.1 = k then (1 : ℝ) else 0) - Pmat P x k) +
        (visits n ω x : ℝ) / n * Pmat P x k := by
      intro n
      rw [Finset.natCast_card_filter, visits_eq]
      have hsum : ∑ j ∈ Finset.range n, (if (ω j).1 = x then (1 : ℝ) else 0) *
          ((if (ω (j + 1)).1.1 = k then (1 : ℝ) else 0) - Pmat P x k) =
          ∑ j ∈ Finset.range n, (if (ω j).1 = x ∧ (ω (j + 1)).1.1 = k then (1 : ℝ) else 0) -
          (∑ j ∈ Finset.range n, (if (ω j).1 = x then (1 : ℝ) else 0)) * Pmat P x k := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h1 : (ω j).1 = x <;> by_cases h2 : (ω (j + 1)).1.1 = k <;> simp [h1, h2]
      rw [hsum]
      ring
    simp_rw [e]
    simpa using (hω (x, k)).add (hvx.mul_const (Pmat P x k))
  have hwx := hw_pos x
  have hev : ∀ᶠ n : ℕ in atTop, 0 < (visits n ω x : ℝ) / n :=
    hvx.eventually (lt_mem_nhds hwx)
  have hlim := hpc.div hvx hwx.ne'
  rw [mul_div_cancel_left₀ _ hwx.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hvpos : 0 < visits n ω x := by
    have : (0 : ℝ) < visits n ω x := by
      have := mul_pos hn hn0
      rwa [div_mul_cancel₀ _ hn0.ne'] at this
    exact_mod_cast this
  simp only [PHat, hvpos, if_true]
  rw [Pi.div_apply, div_div_div_cancel_right₀ hn0.ne']

end C1pair

end QVCLT40192638


set_option autoImplicit false

open MeasureTheory Filter Topology

namespace QVCLT40192638

section Rajchman

variable {Ω : Type*} [MeasurableSpace Ω]

/-- a.s. convergence from summable second moments `∫ g m ^ 2 ≤ C / m ^ 2`. -/
lemma ae_tendsto_zero_of_sq_bound (μ : Measure Ω) (g : ℕ → Ω → ℝ) (hg : ∀ m, Measurable (g m))
    (hint : ∀ m, Integrable (fun ω => g m ω ^ 2) μ) (C : ℝ)
    (hC : ∀ m, ∫ ω, g m ω ^ 2 ∂μ ≤ C / (m : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, Tendsto (fun m => g m ω) atTop (𝓝 0) := by
  let f : ℕ → Ω → ENNReal := fun m ω => ENNReal.ofReal (g m ω ^ 2)
  have hfm : ∀ m, Measurable (f m) := fun m => ENNReal.measurable_ofReal.comp ((hg m).pow_const 2)
  have hle : ∀ m, ∫⁻ ω, f m ω ∂μ ≤ ENNReal.ofReal (|C| / (m : ℝ) ^ 2) := by
    intro m
    rw [← ofReal_integral_eq_lintegral_ofReal (hint m) (Eventually.of_forall fun ω => by positivity)]
    refine ENNReal.ofReal_le_ofReal ((hC m).trans ?_)
    gcongr
    exact le_abs_self C
  have hsumm : Summable (fun m : ℕ => |C| / (m : ℝ) ^ 2) :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left |C|).congr
      fun m => by rw [mul_one_div]
  have hsum : ∑' m, ∫⁻ ω, f m ω ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' m : ℕ, ENNReal.ofReal (|C| / (m : ℝ) ^ 2)) ?_
      (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsumm]
    exact ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ ω ∂μ, ∑' m, f m ω < ⊤ := by
    have hm : Measurable (fun ω => ∑' m, f m ω) := Measurable.ennreal_tsum hfm
    have hl : ∫⁻ ω, ∑' m, f m ω ∂μ ≠ ⊤ := by
      rw [lintegral_tsum (fun m => (hfm m).aemeasurable)]; exact hsum
    exact ae_lt_top hm hl
  filter_upwards [hlt] with ω hω
  have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h1 : Tendsto (fun m : ℕ => g m ω ^ 2) atTop (𝓝 0) := by
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    rw [ENNReal.toReal_zero] at h2
    refine h2.congr fun m => ?_
    simp only [Function.comp, f]
    exact ENNReal.toReal_ofReal (by positivity)
  have h3 : Tendsto (fun m : ℕ => |g m ω|) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    refine this.congr fun m => ?_
    simp [Function.comp, Real.sqrt_sq_eq_abs]
  exact tendsto_zero_iff_abs_tendsto_zero _ |>.2 h3

/-- Rajchman's strong law: orthogonal, uniformly `L²`-bounded variables. -/
lemma rajchman (μ : Measure Ω) [IsProbabilityMeasure μ] (D : ℕ → Ω → ℝ)
    (hm : ∀ k, Measurable (D k)) (hL2 : ∀ k, MemLp (D k) 2 μ) (σ2 : ℝ)
    (hv : ∀ k, ∫ ω, D k ω ^ 2 ∂μ ≤ σ2)
    (horth : ∀ j k, j < k → ∫ ω, D j ω * D k ω ∂μ = 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, D k ω)
      atTop (𝓝 0) := by
  have hσ : 0 ≤ σ2 := (integral_nonneg fun ω => sq_nonneg (D 0 ω)).trans (hv 0)
  have hSL2 : ∀ n, MemLp (fun ω => ∑ k ∈ Finset.range n, D k ω) 2 μ :=
    fun n => by
      have := memLp_finsetSum' (Finset.range n) (fun k _ => hL2 k)
      convert this using 1
      ext ω
      simp [Finset.sum_apply]
  have hS2 : ∀ n, ∫ ω, (∑ k ∈ Finset.range n, D k ω) ^ 2 ∂μ ≤ n * σ2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcross : ∫ ω, (∑ k ∈ Finset.range n, D k ω) * D n ω ∂μ = 0 := by
        simp_rw [Finset.sum_mul]
        have hfs := integral_finsetSum (μ := μ) (Finset.range n) (f := fun j ω => D j ω * D n ω)
          (fun j _ => (hL2 j).integrable_mul (hL2 n))
        rw [hfs]
        exact Finset.sum_eq_zero fun j hj => horth j n (Finset.mem_range.1 hj)
      have e : ∀ ω, (∑ k ∈ Finset.range (n + 1), D k ω) ^ 2 =
          (∑ k ∈ Finset.range n, D k ω) ^ 2 + 2 * ((∑ k ∈ Finset.range n, D k ω) * D n ω) +
            D n ω ^ 2 := fun ω => by rw [Finset.sum_range_succ]; ring
      simp_rw [e]
      have i1 : Integrable (fun ω => (∑ k ∈ Finset.range n, D k ω) ^ 2) μ := (hSL2 n).integrable_sq
      have i2 : Integrable (fun ω => (∑ k ∈ Finset.range n, D k ω) * D n ω) μ :=
        (hSL2 n).integrable_mul (hL2 n)
      have i3 : Integrable (fun ω => D n ω ^ 2) μ := (hL2 n).integrable_sq
      have i2' : Integrable (fun ω => 2 * ((∑ k ∈ Finset.range n, D k ω) * D n ω)) μ :=
        i2.const_mul 2
      have i12 : Integrable (fun ω => (∑ k ∈ Finset.range n, D k ω) ^ 2 +
          2 * ((∑ k ∈ Finset.range n, D k ω) * D n ω)) μ := i1.add i2'
      rw [integral_add i12 i3, integral_add i1 i2', integral_const_mul, hcross]
      push_cast
      linarith [hv n]
  -- block sums
  let g1 : ℕ → Ω → ℝ := fun m ω => (∑ k ∈ Finset.range (m ^ 2), D k ω) / (m : ℝ) ^ 2
  let G : ℕ → Ω → ℝ := fun m ω => ∑ k ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), |D k ω|
  let g2 : ℕ → Ω → ℝ := fun m ω => G m ω / (m : ℝ) ^ 2
  have hGL2 : ∀ m, MemLp (G m) 2 μ := fun m => by
    have := memLp_finsetSum' (Finset.Ico (m ^ 2) ((m + 1) ^ 2)) (fun k _ => (hL2 k).abs)
    convert this using 1
    ext ω
    simp [G, Finset.sum_apply]
  have hG2 : ∀ m, ∫ ω, G m ω ^ 2 ∂μ ≤ (2 * m + 1) ^ 2 * σ2 := by
    intro m
    have hcard : ((Finset.Ico (m ^ 2) ((m + 1) ^ 2)).card : ℝ) = 2 * m + 1 := by
      rw [Nat.card_Ico]
      have : (m + 1) ^ 2 - m ^ 2 = 2 * m + 1 := by
        rw [show (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) by ring]; omega
      rw [this]; push_cast; ring
    have hpt : ∀ ω, G m ω ^ 2 ≤ (2 * m + 1) * ∑ k ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), D k ω ^ 2 :=
      fun ω => by
        have := sq_sum_le_card_mul_sum_sq (s := Finset.Ico (m ^ 2) ((m + 1) ^ 2))
          (f := fun k => |D k ω|)
        simp only [sq_abs] at this
        rw [hcard] at this
        exact this
    have i4 : Integrable (fun ω => ∑ k ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), D k ω ^ 2) μ :=
      integrable_finsetSum _ fun k _ => (hL2 k).integrable_sq
    calc ∫ ω, G m ω ^ 2 ∂μ
        ≤ ∫ ω, (2 * m + 1) * ∑ k ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), D k ω ^ 2 ∂μ :=
          integral_mono (hGL2 m).integrable_sq (i4.const_mul _) hpt
      _ = (2 * m + 1) * ∑ k ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), ∫ ω, D k ω ^ 2 ∂μ := by
          rw [integral_const_mul, integral_finsetSum _ fun k _ => (hL2 k).integrable_sq]
      _ ≤ (2 * m + 1) * ∑ k ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), σ2 := by
          gcongr with k hk
          exact hv k
      _ = (2 * m + 1) ^ 2 * σ2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  have hA1 : ∀ᵐ ω ∂μ, Tendsto (fun m => g1 m ω) atTop (𝓝 0) := by
    refine ae_tendsto_zero_of_sq_bound μ g1 (fun m => ?_) (fun m => ?_) σ2 (fun m => ?_)
    · exact (Finset.measurable_sum _ fun k _ => hm k).div_const _
    · refine ((hSL2 (m ^ 2)).integrable_sq.div_const (((m : ℝ) ^ 2) ^ 2)).congr
        (Eventually.of_forall fun ω => ?_)
      simp only [g1]
      ring
    · rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp [g1]
      · have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
        simp only [g1, div_pow]
        rw [integral_div]
        calc (∫ ω, (∑ k ∈ Finset.range (m ^ 2), D k ω) ^ 2 ∂μ) / ((m : ℝ) ^ 2) ^ 2
            ≤ ((m ^ 2 : ℕ) * σ2) / ((m : ℝ) ^ 2) ^ 2 := by gcongr; exact hS2 _
          _ = σ2 / (m : ℝ) ^ 2 := by push_cast; field_simp
  have hA2 : ∀ᵐ ω ∂μ, Tendsto (fun m => g2 m ω) atTop (𝓝 0) := by
    refine ae_tendsto_zero_of_sq_bound μ g2 (fun m => ?_) (fun m => ?_) (9 * σ2) (fun m => ?_)
    · exact (Finset.measurable_sum _ fun k _ => (hm k).abs).div_const _
    · refine ((hGL2 m).integrable_sq.div_const (((m : ℝ) ^ 2) ^ 2)).congr
        (Eventually.of_forall fun ω => ?_)
      simp only [g2]
      ring
    · rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp [g2]
      · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        simp only [g2, div_pow]
        rw [integral_div]
        calc (∫ ω, G m ω ^ 2 ∂μ) / ((m : ℝ) ^ 2) ^ 2
            ≤ ((2 * m + 1) ^ 2 * σ2) / ((m : ℝ) ^ 2) ^ 2 := by gcongr; exact hG2 m
          _ ≤ (9 * (m : ℝ) ^ 2 * σ2) / ((m : ℝ) ^ 2) ^ 2 := by
              gcongr
              nlinarith
          _ = 9 * σ2 / (m : ℝ) ^ 2 := by field_simp
  filter_upwards [hA1, hA2] with ω h1 h2
  have hsq : Tendsto Nat.sqrt atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * b, fun n hn => Nat.le_sqrt.2 hn⟩
  have hb : Tendsto (fun n : ℕ => |g1 (Nat.sqrt n) ω| + g2 (Nat.sqrt n) ω) atTop (𝓝 0) := by
    have := ((h1.comp hsq).abs.add (h2.comp hsq))
    simpa using this
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop 1] with n hn
  set m := Nat.sqrt n with hmdef
  have hm1 : 1 ≤ m := Nat.le_sqrt.2 (by simpa using hn)
  have hlo : m ^ 2 ≤ n := Nat.sqrt_le' n
  have hhi : n < (m + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hmR : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hloR : (m : ℝ) ^ 2 ≤ n := by exact_mod_cast hlo
  have hsplit : ∑ k ∈ Finset.range n, D k ω =
      ∑ k ∈ Finset.range (m ^ 2), D k ω + ∑ k ∈ Finset.Ico (m ^ 2) n, D k ω :=
    (Finset.sum_range_add_sum_Ico _ hlo).symm
  have hgap : |∑ k ∈ Finset.Ico (m ^ 2) n, D k ω| ≤ G m ω :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hhi.le)
        fun _ _ _ => abs_nonneg _)
  have hG0 : 0 ≤ G m ω := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n), hsplit]
  calc 1 / (n : ℝ) * |∑ k ∈ Finset.range (m ^ 2), D k ω + ∑ k ∈ Finset.Ico (m ^ 2) n, D k ω|
      ≤ 1 / (m : ℝ) ^ 2 * (|∑ k ∈ Finset.range (m ^ 2), D k ω| + G m ω) := by
        gcongr
        exact (abs_add_le _ _).trans (by linarith)
    _ = |g1 m ω| + g2 m ω := by
        simp only [g1, g2, abs_div, abs_of_pos hmR]
        ring

end Rajchman

end QVCLT40192638

namespace QVCLT40192638

section ChainStep2

open MeasureTheory ProbabilityTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] (κ : Kernel X X) [IsMarkovKernel κ] (lam : Measure X)

/-- One-step integral identity for integrable (not necessarily bounded) functionals. -/
lemma chain_step_integral' [IsProbabilityMeasure lam] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) (F : (Finset.Iic n → X) × X → E) (hF : StronglyMeasurable F)
    (hi : Integrable (fun ω => F (Preorder.frestrictLe n ω, ω (n + 1)))
      (MarkovChainCLT.chainMeasure κ lam)) :
    ∫ ω, F (Preorder.frestrictLe n ω, ω (n + 1)) ∂(MarkovChainCLT.chainMeasure κ lam) =
      ∫ ω, (∫ z, F (Preorder.frestrictLe n ω, z) ∂(κ (ω n)))
        ∂(MarkovChainCLT.chainMeasure κ lam) := by
  set μ := MarkovChainCLT.chainMeasure κ lam
  have hg : Measurable (fun ω : ℕ → X ↦ (Preorder.frestrictLe n ω, ω (n + 1))) := by fun_prop
  rw [← integral_map hg.aemeasurable hF.aestronglyMeasurable, ← chain_step_measure]
  have hint : Integrable F (μ.map (Preorder.frestrictLe n) ⊗ₘ
      BanditAlgorithm.markovChainStep κ n) := by
    rw [chain_step_measure]
    exact (integrable_map_measure hF.aestronglyMeasurable hg.aemeasurable).2 hi
  rw [Measure.integral_compProd hint]
  have hm : StronglyMeasurable (fun h : Finset.Iic n → X ↦
      ∫ z, F (h, z) ∂(BanditAlgorithm.markovChainStep κ n h)) :=
    hF.integral_kernel_prod_right'
  rw [integral_map (Preorder.measurable_frestrictLe n).aemeasurable hm.aestronglyMeasurable]
  rfl

/-- One-step lintegral identity. -/
lemma chain_step_lintegral [IsProbabilityMeasure lam] (n : ℕ)
    (F : (Finset.Iic n → X) × X → ENNReal) (hF : Measurable F) :
    ∫⁻ ω, F (Preorder.frestrictLe n ω, ω (n + 1)) ∂(MarkovChainCLT.chainMeasure κ lam) =
      ∫⁻ ω, (∫⁻ z, F (Preorder.frestrictLe n ω, z) ∂(κ (ω n)))
        ∂(MarkovChainCLT.chainMeasure κ lam) := by
  set μ := MarkovChainCLT.chainMeasure κ lam
  have hg : Measurable (fun ω : ℕ → X ↦ (Preorder.frestrictLe n ω, ω (n + 1))) := by fun_prop
  rw [← lintegral_map hF hg, ← chain_step_measure, Measure.lintegral_compProd hF]
  have hm : Measurable (fun h : Finset.Iic n → X ↦
      ∫⁻ z, F (h, z) ∂(BanditAlgorithm.markovChainStep κ n h)) :=
    hF.lintegral_kernel_prod_right'
  rw [lintegral_map hm (Preorder.measurable_frestrictLe n)]
  rfl

end ChainStep2

end QVCLT40192638

namespace QVCLT40192638

section C1rew

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]

open RLInference.QValueCLT MeasureTheory ProbabilityTheory Filter Topology

/-- Centred reward observed at the pair `x`. -/
noncomputable def gx (R : S × A → Measure ℝ) (x : S × A) (z : (S × A) × ℝ) : ℝ :=
  if z.1 = x then z.2 - muR R x else 0

lemma gx_meas (R : S × A → Measure ℝ) (x : S × A) : Measurable (gx R x) := by
  unfold gx
  exact Measurable.ite (measurable_fst (measurableSet_singleton x))
    (measurable_snd.sub measurable_const) measurable_const

lemma mix_lintegral (c : S × A → ENNReal) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (G : (S × A) × ℝ → ENNReal) (hG : Measurable G) :
    ∫⁻ z, G z ∂(∑ y, c y • (Measure.dirac y).prod (R y)) =
      ∑ y, c y * ∫⁻ r, G (y, r) ∂(R y) := by
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [lintegral_smul_measure, Measure.dirac_prod, lintegral_map hG (by fun_prop), smul_eq_mul]

lemma mix_integral (c : S × A → ENNReal) (hc : ∀ y, c y ≠ ⊤) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (G : (S × A) × ℝ → ℝ) (hG : Measurable G)
    (hint : ∀ y, Integrable (fun r => G (y, r)) (R y)) :
    ∫ z, G z ∂(∑ y, c y • (Measure.dirac y).prod (R y)) =
      ∑ y, (c y).toReal * ∫ r, G (y, r) ∂(R y) := by
  have hI : ∀ y, Integrable G ((Measure.dirac y).prod (R y)) := by
    intro y
    rw [Measure.dirac_prod]
    exact (integrable_map_measure hG.aestronglyMeasurable (by fun_prop)).2 (hint y)
  rw [integral_finsetSum_measure (fun y _ => (hI y).smul_measure (hc y))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_smul_measure, Measure.dirac_prod,
    integral_map (by fun_prop) hG.aestronglyMeasurable, smul_eq_mul]

/-- The reward variance at `x`, written as an integral. -/
noncomputable def Vx (R : S × A → Measure ℝ) (x : S × A) : ℝ :=
  ∫ r, (r - muR R x) ^ 2 ∂(R x)

omit [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma Vx_nonneg (R : S × A → Measure ℝ) (x : S × A) : 0 ≤ Vx R x :=
  integral_nonneg fun r => sq_nonneg _

lemma mix_lint_sq (c : S × A → ENNReal) (hc : ∑ y, c y = 1) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (x : S × A) :
    ∫⁻ z, ENNReal.ofReal (gx R x z ^ 2) ∂(∑ y, c y • (Measure.dirac y).prod (R y)) ≤
      ENNReal.ofReal (Vx R x) := by
  rw [mix_lintegral c R (fun z => ENNReal.ofReal (gx R x z ^ 2))
    (ENNReal.measurable_ofReal.comp ((gx_meas R x).pow_const 2))]
  rw [Finset.sum_eq_single x]
  · have hcx : c x ≤ 1 := hc ▸ Finset.single_le_sum (fun y _ => zero_le) (Finset.mem_univ x)
    have hmem : MemLp (fun r : ℝ => r - muR R x) 2 (R x) := (hR x).sub (memLp_const _)
    have heq : ∫⁻ r, ENNReal.ofReal (gx R x (x, r) ^ 2) ∂(R x) = ENNReal.ofReal (Vx R x) := by
      simp only [gx, if_true, Vx]
      rw [ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
        (Filter.Eventually.of_forall fun r => sq_nonneg _)]
    rw [heq]
    calc c x * ENNReal.ofReal (Vx R x) ≤ 1 * ENNReal.ofReal (Vx R x) := by gcongr
      _ = _ := one_mul _
  · intro y _ hy
    simp [gx, hy]
  · intro h; exact absurd (Finset.mem_univ x) h

lemma gx_integral_zero (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)]
    (hR : ∀ x, MemLp id 2 (R x)) (x : S × A) (c : S × A → ENNReal) (hc : ∀ y, c y ≠ ⊤) :
    ∫ z, gx R x z ∂(∑ y, c y • (Measure.dirac y).prod (R y)) = 0 := by
  have hint : ∀ y, Integrable (fun r => gx R x (y, r)) (R y) := by
    intro y
    by_cases hy : y = x
    · subst hy
      simp only [gx, if_true]
      exact ((hR y).integrable one_le_two).sub (integrable_const _)
    · simp [gx, hy]
  rw [mix_integral c hc R _ (gx_meas R x) hint]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hy : y = x
  · subst hy
    simp only [gx, if_true]
    have hi : Integrable (fun r : ℝ => r) (R y) := (hR y).integrable one_le_two
    rw [integral_sub hi (integrable_const _), integral_const]
    simp [muR]
  · simp [gx, hy]

lemma chain_lint_sq (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (ν₀ : PMF S)
    (x : S × A) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (gx R x (ω k) ^ 2)
      ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) ≤
      ENNReal.ofReal (Vx R x) := by
  have hG : Measurable (fun z => ENNReal.ofReal (gx R x z ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((gx_meas R x).pow_const 2)
  cases k with
  | zero =>
    have h := lintegral_map
      (μ := MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) hG
      (measurable_pi_apply 0)
    rw [chain_map_zero] at h
    rw [← h, initLaw]
    exact mix_lint_sq _ (sum_pmf_mul_pmf ν₀ π) R hR x
  | succ j =>
    have h : (∫⁻ ω, ENNReal.ofReal (gx R x (ω (j + 1)) ^ 2)
        ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))) =
        ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (gx R x z ^ 2) ∂(dataKernel P π R (ω j)))
          ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) :=
      chain_step_lintegral (dataKernel P π R) (initLaw ν₀ π R) j
        (fun p => ENNReal.ofReal (gx R x p.2 ^ 2)) (hG.comp measurable_snd)
    rw [h]
    calc _ ≤ ∫⁻ _ω, ENNReal.ofReal (Vx R x)
          ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) := by
          refine lintegral_mono fun ω => ?_
          exact mix_lint_sq (fun y => P (ω j).1 y.1 * π y.1 y.2)
            (sum_pmf_mul_pmf (P (ω j).1) π) R hR x
      _ = _ := by simp

lemma chain_memLp (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (ν₀ : PMF S)
    (x : S × A) (k : ℕ) :
    MemLp (fun ω : ℕ → (S × A) × ℝ => gx R x (ω k)) 2
      (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) := by
  have hm : Measurable (fun ω : ℕ → (S × A) × ℝ => gx R x (ω k)) :=
    (gx_meas R x).comp (measurable_pi_apply k)
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  exact (chain_lint_sq P π R hR ν₀ x k).trans_lt ENNReal.ofReal_lt_top

lemma chain_sq_le (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (ν₀ : PMF S)
    (x : S × A) (k : ℕ) :
    ∫ ω, gx R x (ω k) ^ 2
      ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) ≤ Vx R x := by
  have hm : Measurable (fun ω : ℕ → (S × A) × ℝ => gx R x (ω k)) :=
    (gx_meas R x).comp (measurable_pi_apply k)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    (hm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (Vx_nonneg R x) (chain_lint_sq P π R hR ν₀ x k)

lemma chain_orth (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (ν₀ : PMF S)
    (x : S × A) (j k : ℕ) (hjk : j < k) :
    ∫ ω, gx R x (ω j) * gx R x (ω k)
      ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hjn : j ∈ Finset.Iic n := Finset.mem_Iic.2 (by omega)
  have hF : Measurable (fun p : (Finset.Iic n → (S × A) × ℝ) × ((S × A) × ℝ) =>
      gx R x (p.1 ⟨j, hjn⟩) * gx R x p.2) :=
    ((gx_meas R x).comp ((measurable_pi_apply _).comp measurable_fst)).mul
      ((gx_meas R x).comp measurable_snd)
  have h : (∫ ω, gx R x (ω j) * gx R x (ω (n + 1))
      ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))) =
      ∫ ω, (∫ z, gx R x (ω j) * gx R x z ∂(dataKernel P π R (ω n)))
        ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) :=
    chain_step_integral' (dataKernel P π R) (initLaw ν₀ π R) n _ hF.stronglyMeasurable
      ((chain_memLp P π R hR ν₀ x j).integrable_mul (chain_memLp P π R hR ν₀ x (n + 1)))
  rw [h]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun ω => ?_)
  show ∫ z, gx R x (ω j) * gx R x z ∂(dataKernel P π R (ω n)) = 0
  rw [integral_const_mul]
  have h0 : ∫ z, gx R x z ∂(dataKernel P π R (ω n)) = 0 :=
    gx_integral_zero R hR x (fun y => P (ω n).1 y.1 * π y.1 y.2)
      (fun y => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
  simp [h0]

omit [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma muHat_alg (u0 : S × A → ℝ) (R : S × A → Measure ℝ) (n : ℕ) (ω : ℕ → (S × A) × ℝ)
    (x : S × A) (h : 0 < visits n ω x) :
    muHat u0 n ω x = muR R x +
      ((1 / (n : ℝ)) * ∑ k ∈ Finset.range n, gx R x (ω k)) / ((visits n ω x : ℝ) / n) := by
  have hle : visits n ω x ≤ n := by
    unfold visits
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hsum : ∑ k ∈ Finset.range n, gx R x (ω k) =
      (∑ t ∈ (Finset.range n).filter (fun t => (ω t).1 = x), (ω t).2) -
        (visits n ω x : ℝ) * muR R x := by
    simp only [gx]
    rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rfl
  have hv : (0 : ℝ) < visits n ω x := by exact_mod_cast h
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le h hle)
  rw [muHat, if_pos h, hsum]
  field_simp
  ring

lemma muHat_ae (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (ν₀ : PMF S)
    (u0 : S × A → ℝ)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) :
    ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      ∀ x, Tendsto (fun n => muHat u0 n ω x) atTop (𝓝 (muR R x)) := by
  have hrj : ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      ∀ x, Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, gx R x (ω k))
        atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro x
    have hm : ∀ k, Measurable (fun ω : ℕ → (S × A) × ℝ => gx R x (ω k)) :=
      fun k => (gx_meas R x).comp (measurable_pi_apply k)
    exact rajchman (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (fun k ω => gx R x (ω k)) hm
      (fun k => chain_memLp P π R hR ν₀ x k) (Vx R x) (fun k => chain_sq_le P π R hR ν₀ x k)
      (fun j k hjk => chain_orth P π R hR ν₀ x j k hjk)
  filter_upwards [hrj, visits_ae P π R ν₀ hirr w hw_sum hw_stat] with ω h1 h2 x
  have hvx : Tendsto (fun n : ℕ => (visits n ω x : ℝ) / n) atTop (𝓝 (w x)) :=
    tendsto_pi_nhds.1 h2 x
  have hev : ∀ᶠ n : ℕ in atTop, 0 < visits n ω x := by
    filter_upwards [hvx.eventually (lt_mem_nhds (hw_pos x))] with n hn
    by_contra h0
    have h00 : visits n ω x = 0 := by omega
    simp [h00] at hn
  have hlim := (tendsto_const_nhds (x := muR R x)).add ((h1 x).div hvx (hw_pos x).ne')
  rw [zero_div, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with n hn
  exact (muHat_alg u0 R n ω x hn).symm

theorem C1_of_pos (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (u0 : S × A → ℝ) (p0 : S × A → S → ℝ)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (ν₀ : PMF S) :
    ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      Tendsto (fun n => thetaHat u0 p0 n ω) atTop (𝓝 (theta R P)) := by
  filter_upwards [muHat_ae P π R hR ν₀ u0 hirr w hw_pos hw_sum hw_stat,
    PHat_ae P π R ν₀ p0 hirr w hw_pos hw_sum hw_stat] with ω h1 h2
  refine tendsto_pi_nhds.2 fun i => ?_
  cases i with
  | inl x => exact h1 x
  | inr q => exact h2 q.1 q.2

end C1rew

end QVCLT40192638

namespace QVCLT40192638

section ExpMart

open MeasureTheory ProbabilityTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] (κ : Kernel X X) [IsMarkovKernel κ] (lam : Measure X)

/-- One factor of the exponential martingale: `exp(i s g(x,z)) / ψ(x)`. -/
noncomputable def emFac (g : X → X → ℝ) (s : ℝ) (ψ : X → ℂ) (x z : X) : ℂ :=
  Complex.exp (((s * g x z : ℝ) : ℂ) * Complex.I) / ψ x

lemma emFac_meas (g : X → X → ℝ) (hg : Measurable (Function.uncurry g)) (s : ℝ) (ψ : X → ℂ)
    (hψm : Measurable ψ) : Measurable (Function.uncurry (emFac g s ψ)) := by
  unfold emFac
  have h1 : Measurable (fun p : X × X => (((s * g p.1 p.2 : ℝ) : ℂ) * Complex.I)) :=
    (Complex.measurable_ofReal.comp (measurable_const.mul hg)).mul measurable_const
  exact (Complex.measurable_exp.comp h1).div (hψm.comp measurable_fst)

lemma emFac_norm (g : X → X → ℝ) (s : ℝ) (ψ : X → ℂ) (c : ℝ) (hc : 0 < c)
    (hψc : ∀ x, c ≤ ‖ψ x‖) (x z : X) : ‖emFac g s ψ x z‖ ≤ c⁻¹ := by
  unfold emFac
  rw [norm_div, Complex.norm_exp_ofReal_mul_I, one_div]
  exact inv_anti₀ hc (hψc x)

lemma emFac_prod_norm (g : X → X → ℝ) (s : ℝ) (ψ : X → ℂ) (c : ℝ) (hc : 0 < c)
    (hψc : ∀ x, c ≤ ‖ψ x‖) {ι : Type*} (T : Finset ι) (a b : ι → X) :
    ‖∏ t ∈ T, emFac g s ψ (a t) (b t)‖ ≤ c⁻¹ ^ T.card := by
  rw [norm_prod]
  calc ∏ t ∈ T, ‖emFac g s ψ (a t) (b t)‖ ≤ ∏ _t ∈ T, c⁻¹ :=
        Finset.prod_le_prod (fun t _ => norm_nonneg _)
          (fun t _ => emFac_norm g s ψ c hc hψc (a t) (b t))
    _ = c⁻¹ ^ T.card := Finset.prod_const _

/-- The exponential martingale identity: `E[∏_{t<n} exp(i s g(X_t,X_{t+1})) / ψ(X_t)] = 1`
when `ψ(x) = ∫ exp(i s g(x,z)) κ(x)(dz)` is bounded away from zero. -/
lemma exp_mart [IsProbabilityMeasure lam] (g : X → X → ℝ) (hg : Measurable (Function.uncurry g))
    (s : ℝ) (ψ : X → ℂ) (hψm : Measurable ψ)
    (hψdef : ∀ x, ∫ z, Complex.exp (((s * g x z : ℝ) : ℂ) * Complex.I) ∂(κ x) = ψ x)
    (c : ℝ) (hc : 0 < c) (hψc : ∀ x, c ≤ ‖ψ x‖) (n : ℕ) :
    ∫ ω, (∏ t ∈ Finset.range n, emFac g s ψ (ω t) (ω (t + 1)))
      ∂(MarkovChainCLT.chainMeasure κ lam) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n ∈ Finset.Iic n := Finset.mem_Iic.2 le_rfl
    let F : (Finset.Iic n → X) × X → ℂ := fun p =>
      (∏ t : Fin n, emFac g s ψ (p.1 ⟨t.val, Finset.mem_Iic.2 t.isLt.le⟩)
        (p.1 ⟨t.val + 1, Finset.mem_Iic.2 t.isLt⟩)) * emFac g s ψ (p.1 ⟨n, hn⟩) p.2
    have hEm := emFac_meas g hg s ψ hψm
    have hA : ∀ i : Finset.Iic n, Measurable (fun p : (Finset.Iic n → X) × X => p.1 i) :=
      fun i => (measurable_pi_apply i).comp measurable_fst
    have hP : ∀ t : Fin n, Measurable (fun p : (Finset.Iic n → X) × X =>
        emFac g s ψ (p.1 ⟨t.val, Finset.mem_Iic.2 t.isLt.le⟩)
          (p.1 ⟨t.val + 1, Finset.mem_Iic.2 t.isLt⟩)) :=
      fun t => hEm.comp ((hA ⟨t.val, Finset.mem_Iic.2 t.isLt.le⟩).prodMk
        (hA ⟨t.val + 1, Finset.mem_Iic.2 t.isLt⟩))
    have hQ : Measurable (fun p : (Finset.Iic n → X) × X => emFac g s ψ (p.1 ⟨n, hn⟩) p.2) :=
      hEm.comp ((hA ⟨n, hn⟩).prodMk measurable_snd)
    have hFm : Measurable F := (Finset.measurable_prod _ fun t _ => hP t).mul hQ
    have hFb : ∀ p, ‖F p‖ ≤ c⁻¹ ^ (n + 1) := by
      intro p
      simp only [F]
      rw [norm_mul, pow_succ]
      have h1 := emFac_prod_norm g s ψ c hc hψc (Finset.univ : Finset (Fin n))
        (fun t => p.1 ⟨t.val, Finset.mem_Iic.2 t.isLt.le⟩)
        (fun t => p.1 ⟨t.val + 1, Finset.mem_Iic.2 t.isLt⟩)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      exact mul_le_mul h1 (emFac_norm g s ψ c hc hψc _ _) (norm_nonneg _)
        (pow_nonneg (inv_nonneg.2 hc.le) _)
    have key := chain_step_integral κ lam n F hFm.stronglyMeasurable _ hFb
    have hL : ∀ ω : ℕ → X, F (Preorder.frestrictLe n ω, ω (n + 1)) =
        ∏ t ∈ Finset.range (n + 1), emFac g s ψ (ω t) (ω (t + 1)) := by
      intro ω
      rw [Finset.prod_range_succ]
      simp only [F, Preorder.frestrictLe_apply]
      rw [Fin.prod_univ_eq_prod_range (fun t => emFac g s ψ (ω t) (ω (t + 1))) n]
    have hR : ∀ ω : ℕ → X, ∫ z, F (Preorder.frestrictLe n ω, z) ∂(κ (ω n)) =
        ∏ t ∈ Finset.range n, emFac g s ψ (ω t) (ω (t + 1)) := by
      intro ω
      simp only [F, Preorder.frestrictLe_apply]
      rw [integral_const_mul,
        Fin.prod_univ_eq_prod_range (fun t => emFac g s ψ (ω t) (ω (t + 1))) n]
      have hne : ψ (ω n) ≠ 0 := by
        intro h0
        have := hψc (ω n)
        rw [h0, norm_zero] at this
        linarith
      have hI : ∫ z, emFac g s ψ (ω n) z ∂(κ (ω n)) = 1 := by
        unfold emFac
        rw [integral_div, hψdef, div_self hne]
      rw [hI, mul_one]
    simp_rw [hL] at key
    rw [key]
    simp_rw [hR]
    exact ih

end ExpMart

end QVCLT40192638
namespace QVCLT40192638

section CharLower

open MeasureTheory ProbabilityTheory Filter Topology

/-- C2b (lower bound): `‖E exp(i s g)‖ ≥ Re E exp(i s g) = E cos(s g) ≥ 1 - s² E[g²]/2`. -/
lemma psi_norm_ge {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (g : Y → ℝ) (hgm : Measurable g) (hg : MemLp g 2 ν) (s : ℝ) :
    1 - s ^ 2 * (∫ y, g y ^ 2 ∂ν) / 2 ≤
      ‖∫ y, Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I) ∂ν‖ := by
  have hm : Measurable (fun y => Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I)) :=
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul hgm)).mul measurable_const)
  have hint : Integrable (fun y => Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I)) ν :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)
  have hre : (∫ y, Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I) ∂ν).re =
      ∫ y, Real.cos (s * g y) ∂ν := by
    have h := integral_re hint
    calc (∫ y, Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I) ∂ν).re
        = RCLike.re (∫ y, Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I) ∂ν) := rfl
      _ = ∫ y, RCLike.re (Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I)) ∂ν := h.symm
      _ = ∫ y, Real.cos (s * g y) ∂ν := by
        congr 1
        funext y
        exact Complex.exp_ofReal_mul_I_re _
  have hsq : Integrable (fun y => g y ^ 2) ν := hg.integrable_sq
  have hcos : Integrable (fun y => Real.cos (s * g y)) ν :=
    Integrable.of_bound (Real.measurable_cos.comp (measurable_const.mul hgm)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hlow : ∫ y, (1 - s ^ 2 / 2 * g y ^ 2) ∂ν = 1 - s ^ 2 * (∫ y, g y ^ 2 ∂ν) / 2 := by
    rw [integral_sub (integrable_const _) (hsq.const_mul _), integral_const, integral_const_mul]
    simp
    ring
  rw [← hlow]
  calc ∫ y, (1 - s ^ 2 / 2 * g y ^ 2) ∂ν ≤ ∫ y, Real.cos (s * g y) ∂ν := by
        refine integral_mono ((integrable_const _).sub (hsq.const_mul _)) hcos fun y => ?_
        have := Real.one_sub_sq_div_two_le_cos (x := s * g y)
        simp only
        nlinarith [this]
    _ = (∫ y, Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I) ∂ν).re := hre.symm
    _ ≤ _ := Complex.re_le_norm _

end CharLower

end QVCLT40192638
namespace QVCLT40192638

section CharTaylor

open MeasureTheory ProbabilityTheory Filter Topology

/-- C2b (Taylor): `E exp(i s g) = 1 - s² E[g²]/2 + o(s²)` for a centred square-integrable `g`. -/
lemma psi_taylor {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (g : Y → ℝ) (hgm : Measurable g) (hg : MemLp g 2 ν) (h0 : ∫ y, g y ∂ν = 0) :
    (fun s : ℝ => (∫ y, Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I) ∂ν) -
        (1 - ((s ^ 2 * (∫ y, g y ^ 2 ∂ν) / 2 : ℝ) : ℂ))) =o[𝓝 0] fun s => s ^ 2 := by
  have hint : MemLp id 2 (ν.map g) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hgm.aemeasurable).2 hg
  have hT := taylor_isLittleO_univ (x₀ := (0:ℝ)) (contDiff_charFun hint)
  have hE : ∀ s : ℝ, taylorWithinEval (charFun (ν.map g)) 2 Set.univ 0 s =
      1 - ((s ^ 2 * (∫ y, g y ^ 2 ∂ν) / 2 : ℝ) : ℂ) := by
    intro s
    rw [taylorWithinEval_charFun_two_zero hgm.aemeasurable hint]
    simp only [Pi.pow_apply]
    rw [h0]
    push_cast
    ring
  have hC : ∀ s : ℝ, charFun (ν.map g) s =
      ∫ y, Complex.exp (((s * g y : ℝ) : ℂ) * Complex.I) ∂ν := by
    intro s
    rw [charFun_apply_real, integral_map hgm.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    push_cast
    rfl
  simp only [sub_zero] at hT
  refine hT.congr_left (fun s => ?_)
  rw [hE, hC]

/-- `z_n^{m_n} → exp(w c)` when `n (z_n - 1) → c` and `m_n / n → w`. -/
lemma pow_tendsto_exp (z : ℕ → ℂ) (m : ℕ → ℕ) (c : ℂ) (w : ℝ)
    (hz : Tendsto (fun n : ℕ => (n : ℂ) * (z n - 1)) atTop (𝓝 c))
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 w)) :
    Tendsto (fun n => z n ^ m n) atTop (𝓝 (Complex.exp (w * c))) := by
  have hy : Tendsto (fun n : ℕ => z n - 1) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    have h1 := hinv.mul hz
    rw [Complex.ofReal_zero, zero_mul] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    push_cast
    field_simp
  have hball : ∀ᶠ n : ℕ in atTop, ‖z n - 1‖ < 1 / 2 := by
    have := hy.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1 / 2))
    filter_upwards [this] with n hn
    rwa [dist_zero_right] at hn
  have hlog : Tendsto (fun n => (m n : ℂ) * Complex.log (z n)) atTop (𝓝 ((w : ℂ) * c)) := by
    have hmain : Tendsto (fun n : ℕ => (((m n : ℝ) / n : ℝ) : ℂ) * ((n : ℂ) * (z n - 1)))
        atTop (𝓝 ((w : ℂ) * c)) :=
      ((Complex.continuous_ofReal.tendsto w).comp hm).mul hz
    have herr : Tendsto (fun n : ℕ => (m n : ℂ) * Complex.log (z n) -
        (((m n : ℝ) / n : ℝ) : ℂ) * ((n : ℂ) * (z n - 1))) atTop (𝓝 0) := by
      have hb : Tendsto (fun n : ℕ => ((m n : ℝ) / n) * ‖(n : ℂ) * (z n - 1)‖ * ‖z n - 1‖)
          atTop (𝓝 (w * ‖c‖ * ‖(0:ℂ)‖)) :=
        (hm.mul hz.norm).mul hy.norm
      rw [norm_zero, mul_zero] at hb
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [eventually_ge_atTop 1, hball] with n hn hyn
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have h1z : 1 + (z n - 1) = z n := by ring
      have heq : (m n : ℂ) * Complex.log (z n) -
          (((m n : ℝ) / n : ℝ) : ℂ) * ((n : ℂ) * (z n - 1)) =
          (m n : ℂ) * (Complex.log (1 + (z n - 1)) - (z n - 1)) := by
        rw [h1z]
        push_cast
        field_simp
      rw [heq, norm_mul, Complex.norm_natCast]
      have hL := Complex.norm_log_one_add_sub_self_le (z := z n - 1) (by linarith)
      have hinv : (1 - ‖z n - 1‖)⁻¹ ≤ 2 := by
        calc (1 - ‖z n - 1‖)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
          _ = 2 := by norm_num
      have hq : ‖z n - 1‖ ^ 2 * (1 - ‖z n - 1‖)⁻¹ / 2 ≤ ‖z n - 1‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖z n - 1‖)
        linarith
      have hr : ((m n : ℝ) / n) * ‖(n : ℂ) * (z n - 1)‖ * ‖z n - 1‖ =
          (m n : ℝ) * ‖z n - 1‖ ^ 2 := by
        rw [norm_mul, Complex.norm_natCast]
        field_simp
      rw [hr]
      exact mul_le_mul_of_nonneg_left (hL.trans hq) (Nat.cast_nonneg _)
    simpa using herr.add hmain
  have hexp := (Complex.continuous_exp.tendsto _).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hball] with n hyn
  have hz0 : z n ≠ 0 := by
    intro h
    rw [h] at hyn
    norm_num at hyn
  simp only [Function.comp]
  rw [Complex.exp_nat_mul, Complex.exp_log hz0]

/-- Product version over a finite index type. -/
lemma prod_pow_tendsto {X : Type*} [Fintype X] (z : X → ℕ → ℂ) (m : X → ℕ → ℕ) (c : X → ℂ)
    (w : X → ℝ) (hz : ∀ x, Tendsto (fun n : ℕ => (n : ℂ) * (z x n - 1)) atTop (𝓝 (c x)))
    (hm : ∀ x, Tendsto (fun n : ℕ => (m x n : ℝ) / n) atTop (𝓝 (w x))) :
    Tendsto (fun n => ∏ x, z x n ^ m x n) atTop (𝓝 (Complex.exp (∑ x, (w x : ℂ) * c x))) := by
  rw [Complex.exp_sum]
  exact tendsto_finsetProd _ fun x _ => pow_tendsto_exp (z x) (m x) (c x) (w x) (hz x) (hm x)

/-- `∏_{t∈s} f(Z t) = ∏_x f(x)^{#{t ∈ s | Z t = x}}`. -/
lemma prod_comp_eq_prod_pow {ι X M : Type*} [Fintype X] [DecidableEq X] [CommMonoid M]
    (s : Finset ι) (Z : ι → X) (f : X → M) :
    ∏ t ∈ s, f (Z t) = ∏ x, f x ^ (s.filter (fun t => Z t = x)).card := by
  rw [← Finset.prod_fiberwise s Z (fun t => f (Z t))]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_congr rfl (fun t ht => congrArg f (Finset.mem_filter.1 ht).2),
    Finset.prod_const]

/-- `n (ψ(u/√n) - 1) → -u² v/2` from the second-order Taylor expansion of `ψ` at `0`. -/
lemma nat_mul_psi_tendsto (ψ : ℝ → ℂ) (v : ℝ)
    (hψ : (fun s : ℝ => ψ s - (1 - ((s ^ 2 * v / 2 : ℝ) : ℂ))) =o[𝓝 0] fun s => s ^ 2)
    (u : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) * (ψ (u / Real.sqrt n) - 1)) atTop
      (𝓝 (-(((u ^ 2 * v / 2 : ℝ)) : ℂ))) := by
  have hs : Tendsto (fun n : ℕ => u / Real.sqrt n) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := u)).div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have ho := hψ.comp_tendsto hs
  have hsq : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * (u / Real.sqrt n) ^ 2 = u ^ 2 := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    field_simp
  have h1 : Tendsto (fun n : ℕ => (n : ℂ) * (ψ (u / Real.sqrt n) -
      (1 - ((((u / Real.sqrt n)) ^ 2 * v / 2 : ℝ) : ℂ)))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hc : 0 < ε / (2 * (u ^ 2 + 1)) := by positivity
    filter_upwards [Asymptotics.isLittleO_iff.1 ho hc, eventually_ge_atTop 1] with n hn hn1
    simp only [Function.comp, Real.norm_eq_abs] at hn
    rw [dist_zero_right, norm_mul, Complex.norm_natCast]
    calc _ ≤ (n : ℝ) * (ε / (2 * (u ^ 2 + 1)) * |(u / Real.sqrt n) ^ 2|) :=
          mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg n)
      _ = ε / (2 * (u ^ 2 + 1)) * ((n : ℝ) * (u / Real.sqrt n) ^ 2) := by
          rw [abs_of_nonneg (sq_nonneg _)]; ring
      _ = ε / (2 * (u ^ 2 + 1)) * u ^ 2 := by rw [hsq n hn1]
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  have h2 := h1.add (tendsto_const_nhds (x := (-(((u ^ 2 * v / 2 : ℝ)) : ℂ))))
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hk : (n : ℝ) * ((u / Real.sqrt n) ^ 2 * v / 2) = u ^ 2 * v / 2 := by
    linear_combination (v / 2) * hsq n hn
  calc (n : ℂ) * (ψ (u / Real.sqrt n) - (1 - ((((u / Real.sqrt n)) ^ 2 * v / 2 : ℝ) : ℂ))) +
        -(((u ^ 2 * v / 2 : ℝ)) : ℂ)
      = (n : ℂ) * (ψ (u / Real.sqrt n) - 1) +
          ((((n : ℝ) * ((u / Real.sqrt n) ^ 2 * v / 2) : ℝ) : ℂ) - ((u ^ 2 * v / 2 : ℝ) : ℂ)) := by
        push_cast; ring
    _ = (n : ℂ) * (ψ (u / Real.sqrt n) - 1) := by rw [hk]; ring

end CharTaylor

end QVCLT40192638
namespace QVCLT40192638

section ChainCLT

open MeasureTheory ProbabilityTheory Filter Topology

lemma one_sub_ge_exp (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.exp (-2 * x) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by linarith
  have hne : 1 - x ≠ 0 := hpos.ne'
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    have hm : 1 ≤ (1 + 2 * x) * (1 - x) := by nlinarith
    calc (1 - x)⁻¹ = (1 - x)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (1 - x)⁻¹ * ((1 + 2 * x) * (1 - x)) :=
          mul_le_mul_of_nonneg_left hm (inv_nonneg.2 hpos.le)
      _ = 1 + 2 * x := by
          rw [mul_comm (1 + 2 * x), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  calc Real.exp (-2 * x) ≤ Real.exp (Real.log (1 - x)) := Real.exp_le_exp.2 (by linarith)
    _ = 1 - x := Real.exp_log hpos

/-- `∫ f_n p_n → L` when `∫ f_n = 1`, `‖f_n‖ ≤ C`, `‖p_n‖ ≤ 1` and `p_n → L` a.s. -/
lemma integral_mul_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f p : ℕ → Ω → ℂ) (L : ℂ) (C : ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp : ∀ n, AEStronglyMeasurable (p n) μ)
    (hfC : ∀ᶠ n in atTop, ∀ ω, ‖f n ω‖ ≤ C)
    (hf1 : ∀ᶠ n in atTop, ∫ ω, f n ω ∂μ = 1)
    (hp1 : ∀ n ω, ‖p n ω‖ ≤ 1)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => p n ω) atTop (𝓝 L)) :
    Tendsto (fun n => ∫ ω, f n ω * p n ω ∂μ) atTop (𝓝 L) := by
  have hpL : ∀ n ω, ‖p n ω - L‖ ≤ 1 + ‖L‖ := fun n ω =>
    (norm_sub_le _ _).trans (by linarith [hp1 n ω])
  have hD : Tendsto (fun n => ∫ ω, ‖p n ω - L‖ ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => 1 + ‖L‖)
      (F := fun n ω => ‖p n ω - L‖) (f := fun _ => (0 : ℝ))
      (fun n => ((hp n).sub aestronglyMeasurable_const).norm) (integrable_const _)
      (fun n => ae_of_all _ fun ω => by rw [norm_norm]; exact hpL n ω)
      (hlim.mono fun ω h => by simpa using (h.sub_const L).norm)
    simpa using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun n => C * ∫ ω, ‖p n ω - L‖ ∂μ) atTop (𝓝 (C * 0)) := hD.const_mul C
  rw [mul_zero] at hb
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hb
  filter_upwards [hfC, hf1] with n hC h1
  have hfi : Integrable (f n) μ := Integrable.of_bound (hf n) C (Eventually.of_forall hC)
  have hpi : Integrable (fun ω => p n ω - L) μ :=
    Integrable.of_bound ((hp n).sub aestronglyMeasurable_const) (1 + ‖L‖)
      (Eventually.of_forall (hpL n))
  have hfpi : Integrable (fun ω => f n ω * p n ω) μ :=
    Integrable.of_bound ((hf n).mul (hp n)) (C * 1)
      (Eventually.of_forall fun ω => by
        rw [norm_mul]
        calc ‖f n ω‖ * ‖p n ω‖ ≤ ‖f n ω‖ * 1 :=
              mul_le_mul_of_nonneg_left (hp1 n ω) (norm_nonneg _)
          _ ≤ C * 1 := by rw [mul_one, mul_one]; exact hC ω)
  have heq : (∫ ω, f n ω * p n ω ∂μ) - L = ∫ ω, f n ω * (p n ω - L) ∂μ := by
    rw [show (fun ω => f n ω * (p n ω - L)) = fun ω => f n ω * p n ω - f n ω * L from
      funext fun ω => mul_sub _ _ _, integral_sub hfpi (hfi.mul_const L), integral_mul_const, h1,
      one_mul]
  rw [heq]
  calc ‖∫ ω, f n ω * (p n ω - L) ∂μ‖ ≤ ∫ ω, C * ‖p n ω - L‖ ∂μ :=
        norm_integral_le_of_norm_le (hpi.norm.const_mul C) (Eventually.of_forall fun ω => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC ω) (norm_nonneg _))
    _ = C * ∫ ω, ‖p n ω - L‖ ∂μ := integral_const_mul _ _

set_option maxHeartbeats 1000000 in
/-- C2d: scalar CLT for a chain martingale `∑_{t<n} G(cls X_t)(X_{t+1})` whose increments have
conditional mean zero and depend on the present state only through a finite class `cls`. -/
theorem chain_clt_scalar {X F : Type*} [MeasurableSpace X] [Fintype F] [DecidableEq F]
    [MeasurableSpace F] [MeasurableSingletonClass F]
    (κ : Kernel X X) [IsMarkovKernel κ] (lam : Measure X) [IsProbabilityMeasure lam]
    (cls : X → F) (hcls : Measurable cls)
    (K : F → Measure X) [∀ f, IsProbabilityMeasure (K f)] (hκ : ∀ x, κ x = K (cls x))
    (G : F → X → ℝ) (hG : ∀ f, Measurable (G f)) (hG2 : ∀ f, MemLp (G f) 2 (K f))
    (hG0 : ∀ f, ∫ z, G f z ∂(K f) = 0)
    (w : F → ℝ) (hw : ∀ f, 0 ≤ w f)
    (hvis : ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure κ lam), ∀ f, Tendsto
      (fun n : ℕ => (((Finset.range n).filter (fun t => cls (ω t) = f)).card : ℝ) / n)
      atTop (𝓝 (w f))) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, G (cls (ω t)) (ω (t + 1)))
      atTop id (fun _ => MarkovChainCLT.chainMeasure κ lam)
      (gaussianReal 0 (∑ f, w f * ∫ z, G f z ^ 2 ∂(K f)).toNNReal) := by
  have hg : Measurable (Function.uncurry (fun (x : X) (z : X) => G (cls x) z)) := by
    have h1 : Measurable (fun q : F × X => G q.1 q.2) :=
      measurable_from_prod_countable_right (fun f => hG f)
    exact h1.comp ((hcls.comp measurable_fst).prodMk measurable_snd)
  have hgt : ∀ t : ℕ, Measurable (fun ω : ℕ → X => G (cls (ω t)) (ω (t + 1))) := by
    intro t
    have h := hg.comp (f := fun ω : ℕ → X => (ω t, ω (t + 1)))
      ((measurable_pi_apply t).prodMk (measurable_pi_apply (t + 1)))
    exact h
  have hYm : ∀ n : ℕ, Measurable (fun ω : ℕ → X =>
      (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, G (cls (ω t)) (ω (t + 1))) := fun n =>
    (Finset.measurable_sum _ fun t _ => hgt t).const_mul _
  refine { forall_aemeasurable := fun n => (hYm n).aemeasurable,
           aemeasurable_limit := aemeasurable_id,
           tendsto := ?_ }
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun u => ?_
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id]
  rw [charFun_gaussianReal]
  have hv0 : ∀ f, 0 ≤ ∫ z, G f z ^ 2 ∂(K f) := fun f => integral_nonneg fun z => sq_nonneg _
  have hV0 : 0 ≤ ∑ f, w f * ∫ z, G f z ^ 2 ∂(K f) :=
    Finset.sum_nonneg fun f _ => mul_nonneg (hw f) (hv0 f)
  obtain ⟨vmax, hvle⟩ : ∃ vmax : ℝ, ∀ f, ∫ z, G f z ^ 2 ∂(K f) ≤ vmax :=
    ⟨∑ f, ∫ z, G f z ^ 2 ∂(K f), fun f =>
      Finset.single_le_sum (fun f _ => hv0 f) (Finset.mem_univ f)⟩
  let Φ : F → ℝ → ℂ := fun f s => ∫ z, Complex.exp (((s * G f z : ℝ) : ℂ) * Complex.I) ∂(K f)
  let ψ : ℕ → X → ℂ := fun n x => Φ (cls x) (u / Real.sqrt n)
  have hlow : ∀ f s, 1 - s ^ 2 * (∫ z, G f z ^ 2 ∂(K f)) / 2 ≤ ‖Φ f s‖ := fun f s =>
    psi_norm_ge (K f) (G f) (hG f) (hG2 f) s
  have hup : ∀ f s, ‖Φ f s‖ ≤ 1 := by
    intro f s
    refine (norm_integral_le_of_norm_le_const
      (Eventually.of_forall fun z => (Complex.norm_exp_ofReal_mul_I _).le)).trans ?_
    simp
  have hN : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) ∧ u ^ 2 * vmax ≤ n := by
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (u ^ 2 * vmax)] with n h1 h2
    exact ⟨by exact_mod_cast h1, h2⟩
  have hsn : ∀ n : ℕ, 1 ≤ (n : ℝ) → (u / Real.sqrt n) ^ 2 = u ^ 2 / n := by
    intro n hn
    rw [div_pow, Real.sq_sqrt (by linarith)]
  have hx : ∀ n : ℕ, 1 ≤ (n : ℝ) → u ^ 2 * vmax ≤ n → ∀ f,
      (u / Real.sqrt n) ^ 2 * (∫ z, G f z ^ 2 ∂(K f)) / 2 ≤ 1 / 2 := by
    intro n hn1 hn2 f
    rw [hsn n hn1]
    have hnpos : (0 : ℝ) < n := by linarith
    have : u ^ 2 / n * (∫ z, G f z ^ 2 ∂(K f)) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hnpos]
      exact (mul_le_mul_of_nonneg_left (hvle f) (sq_nonneg u)).trans hn2
    linarith
  have hhalf : ∀ n : ℕ, 1 ≤ (n : ℝ) → u ^ 2 * vmax ≤ n → ∀ x, (1 / 2 : ℝ) ≤ ‖ψ n x‖ := by
    intro n hn1 hn2 x
    have h1 := hlow (cls x) (u / Real.sqrt n)
    have h2 := hx n hn1 hn2 (cls x)
    show (1 / 2 : ℝ) ≤ ‖Φ (cls x) (u / Real.sqrt n)‖
    linarith
  have hfac : ∀ n : ℕ, 1 ≤ (n : ℝ) → u ^ 2 * vmax ≤ n → ∀ x,
      Real.exp (-(u ^ 2 * vmax / n)) ≤ ‖ψ n x‖ := by
    intro n hn1 hn2 x
    have h1 := hlow (cls x) (u / Real.sqrt n)
    have h2 := hx n hn1 hn2 (cls x)
    have h0 : 0 ≤ (u / Real.sqrt n) ^ 2 * (∫ z, G (cls x) z ^ 2 ∂(K (cls x))) / 2 := by
      have := hv0 (cls x)
      positivity
    have h3 := one_sub_ge_exp _ h0 h2
    have h4 : -(u ^ 2 * vmax / n) ≤
        -2 * ((u / Real.sqrt n) ^ 2 * (∫ z, G (cls x) z ^ 2 ∂(K (cls x))) / 2) := by
      rw [hsn n hn1]
      have hnpos : (0 : ℝ) < n := by linarith
      have := mul_le_mul_of_nonneg_left (hvle (cls x)) (div_nonneg (sq_nonneg u) hnpos.le)
      have e : u ^ 2 * vmax / n = u ^ 2 / n * vmax := by ring
      rw [e]
      linarith
    calc Real.exp (-(u ^ 2 * vmax / n))
        ≤ Real.exp (-2 * ((u / Real.sqrt n) ^ 2 * (∫ z, G (cls x) z ^ 2 ∂(K (cls x))) / 2)) :=
          Real.exp_le_exp.2 h4
      _ ≤ 1 - (u / Real.sqrt n) ^ 2 * (∫ z, G (cls x) z ^ 2 ∂(K (cls x))) / 2 := h3
      _ ≤ ‖ψ n x‖ := h1
  have hprod_low : ∀ n : ℕ, 1 ≤ (n : ℝ) → u ^ 2 * vmax ≤ n → ∀ ω : ℕ → X,
      Real.exp (-(u ^ 2 * vmax)) ≤ ‖∏ t ∈ Finset.range n, ψ n (ω t)‖ := by
    intro n hn1 hn2 ω
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [norm_prod]
    calc Real.exp (-(u ^ 2 * vmax))
        = ∏ _t ∈ Finset.range n, Real.exp (-(u ^ 2 * vmax / n)) := by
          rw [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]
          congr 1
          field_simp
      _ ≤ ∏ t ∈ Finset.range n, ‖ψ n (ω t)‖ :=
          Finset.prod_le_prod (fun t _ => (Real.exp_pos _).le) (fun t _ => hfac n hn1 hn2 (ω t))
  have hψm : ∀ n, Measurable (ψ n) := fun n =>
    (measurable_of_finite (fun f => Φ f (u / Real.sqrt n))).comp hcls
  let fN : ℕ → (ℕ → X) → ℂ := fun n ω => ∏ t ∈ Finset.range n,
    emFac (fun x z => G (cls x) z) (u / Real.sqrt n) (ψ n) (ω t) (ω (t + 1))
  let pN : ℕ → (ℕ → X) → ℂ := fun n ω => ∏ t ∈ Finset.range n, ψ n (ω t)
  have hfm : ∀ n, Measurable (fN n) := by
    intro n
    have ht : ∀ t : ℕ, Measurable (fun ω : ℕ → X =>
        emFac (fun x z => G (cls x) z) (u / Real.sqrt n) (ψ n) (ω t) (ω (t + 1))) := by
      intro t
      have h := (emFac_meas (fun x z => G (cls x) z) hg (u / Real.sqrt n) (ψ n) (hψm n)).comp
        (f := fun ω : ℕ → X => (ω t, ω (t + 1)))
        ((measurable_pi_apply t).prodMk (measurable_pi_apply (t + 1)))
      exact h
    exact Finset.measurable_prod _ fun t _ => ht t
  have hpm : ∀ n, Measurable (pN n) := fun n =>
    Finset.measurable_prod _ fun t _ => (hψm n).comp (measurable_pi_apply t)
  have hchar : ∀ᶠ n : ℕ in atTop,
      charFun ((MarkovChainCLT.chainMeasure κ lam).map (fun ω : ℕ → X =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, G (cls (ω t)) (ω (t + 1)))) u =
      ∫ ω, fN n ω * pN n ω ∂(MarkovChainCLT.chainMeasure κ lam) := by
    filter_upwards [hN] with n hn
    rw [charFun_apply_real, integral_map (hYm n).aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have hne : ∀ t, ψ n (ω t) ≠ 0 := fun t h => by
      have := hhalf n hn.1 hn.2 (ω t)
      rw [h, norm_zero] at this
      norm_num at this
    show Complex.exp (↑u * ↑((Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, G (cls (ω t)) (ω (t + 1)))
        * Complex.I) = (∏ t ∈ Finset.range n,
          emFac (fun x z => G (cls x) z) (u / Real.sqrt n) (ψ n) (ω t) (ω (t + 1))) *
        ∏ t ∈ Finset.range n, ψ n (ω t)
    rw [← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl (fun t _ =>
      show emFac (fun x z => G (cls x) z) (u / Real.sqrt n) (ψ n) (ω t) (ω (t + 1)) * ψ n (ω t) =
        Complex.exp (((u / Real.sqrt n * G (cls (ω t)) (ω (t + 1)) : ℝ) : ℂ) * Complex.I) from by
          unfold emFac
          exact div_mul_cancel₀ _ (hne t))]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hf1 : ∀ᶠ n : ℕ in atTop, ∫ ω, fN n ω ∂(MarkovChainCLT.chainMeasure κ lam) = 1 := by
    filter_upwards [hN] with n hn
    exact exp_mart κ lam (fun x z => G (cls x) z) hg (u / Real.sqrt n) (ψ n) (hψm n)
      (fun x => by rw [hκ x]) (1 / 2) (by norm_num) (hhalf n hn.1 hn.2) n
  have hfC : ∀ᶠ n : ℕ in atTop, ∀ ω, ‖fN n ω‖ ≤ (Real.exp (-(u ^ 2 * vmax)))⁻¹ := by
    filter_upwards [hN] with n hn
    intro ω
    have hp := hprod_low n hn.1 hn.2 ω
    have heq : ‖fN n ω‖ = ‖pN n ω‖⁻¹ := by
      simp only [fN, pN, emFac, norm_prod, norm_div, Complex.norm_exp_ofReal_mul_I, one_div]
      rw [Finset.prod_inv_distrib]
    rw [heq]
    exact inv_anti₀ (Real.exp_pos _) hp
  have hp1 : ∀ n ω, ‖pN n ω‖ ≤ 1 := by
    intro n ω
    simp only [pN]
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun t _ => hup _ _)
  have hlimit : ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure κ lam), Tendsto (fun n => pN n ω) atTop
      (𝓝 (Complex.exp (∑ f, (w f : ℂ) *
        -(((u ^ 2 * (∫ z, G f z ^ 2 ∂(K f)) / 2 : ℝ)) : ℂ)))) := by
    filter_upwards [hvis] with ω hω
    have hz : ∀ f, Tendsto (fun n : ℕ => (n : ℂ) * (Φ f (u / Real.sqrt n) - 1)) atTop
        (𝓝 (-(((u ^ 2 * (∫ z, G f z ^ 2 ∂(K f)) / 2 : ℝ)) : ℂ))) := fun f =>
      nat_mul_psi_tendsto (Φ f) _ (psi_taylor (K f) (G f) (hG f) (hG2 f) (hG0 f)) u
    have := prod_pow_tendsto (fun f n => Φ f (u / Real.sqrt n))
      (fun f n => ((Finset.range n).filter (fun t => cls (ω t) = f)).card) _ w hz hω
    refine this.congr' (Eventually.of_forall fun n => ?_)
    exact (prod_comp_eq_prod_pow (Finset.range n) (fun t => cls (ω t))
      (fun f => Φ f (u / Real.sqrt n))).symm
  have hmain := integral_mul_tendsto (MarkovChainCLT.chainMeasure κ lam) fN pN _ _
    (fun n => (hfm n).aestronglyMeasurable) (fun n => (hpm n).aestronglyMeasurable)
    hfC hf1 hp1 hlimit
  have hL : (∑ f, (w f : ℂ) * -(((u ^ 2 * (∫ z, G f z ^ 2 ∂(K f)) / 2 : ℝ)) : ℂ)) =
      (u : ℂ) * ((0 : ℝ) : ℂ) * Complex.I -
        (((∑ f, w f * ∫ z, G f z ^ 2 ∂(K f)).toNNReal : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2 := by
    rw [Real.coe_toNNReal _ hV0, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
      Complex.ofReal_sum, Finset.sum_mul, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    push_cast
    ring
  rw [← hL]
  exact hmain.congr' (hchar.mono fun n h => h.symm)

end ChainCLT

end QVCLT40192638

namespace QVCLT40192638

section C2gen

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type} [MeasurableSpace Ω]

/-- Convergence in distribution to a constant gives convergence in measure (copy of asm2). -/
lemma tid_const_tim {Ω' E : Type}
    [MeasurableSpace Ω'] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Y : ℕ → Ω → E} {Z : Ω' → E} (c : E)
    (h : TendstoInDistribution Y atTop Z (fun _ => μ) μ') (hZ : ∀ ω, Z ω = c) :
    TendstoInMeasure μ Y atTop (fun _ => c) := by
  intro ε hε
  set F : Set E := {y | ε ≤ edist y c} with hF
  have hFc : IsClosed F := isClosed_le continuous_const (continuous_id.edist continuous_const)
  have hlim : limsup (fun n => (μ.map (Y n)) F) atTop ≤ (μ'.map Z) F :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hFc
  have hZF : (μ'.map Z) F = 0 := by
    rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit hFc.measurableSet]
    have : Z ⁻¹' F = ∅ := by
      ext ω
      simp [hF, hZ ω, hε.ne']
    simp [this]
  have hmeas : ∀ n, μ {ω | ε ≤ edist (Y n ω) c} = (μ.map (Y n)) F := fun n => by
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hFc.measurableSet]
    rfl
  simp_rw [hmeas]
  rw [hZF] at hlim
  exact tendsto_of_le_liminf_of_limsup_le (by simp) hlim

lemma tim_add {μ : Measure Ω} {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => 0)) (hg : TendstoInMeasure μ g atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => f n ω + g n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have h1 := hf (ε / 2) (by positivity)
  have h2 := hg (ε / 2) (by positivity)
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
    (fun _ => by simp) (fun n => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, sub_zero] at hω ⊢
  by_contra hc
  push_neg at hc
  linarith [norm_add_le (f n ω) (g n ω), hc.1, hc.2]

lemma tim_sum {ι : Type*} (s : Finset ι) {μ : Measure Ω} (f : ι → ℕ → Ω → ℝ)
    (hf : ∀ i ∈ s, TendstoInMeasure μ (f i) atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => ∑ i ∈ s, f i n ω) atTop (fun _ => 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro ε hε
    simp [hε.ne']
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact tim_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Slutsky to zero: `X_n ⇒ Z`, `D_n → d` in measure, `g (x, d) = 0` give `g (X_n, D_n) → 0`. -/
lemma tim_of_slutsky {Ω' : Type} [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (X D : ℕ → Ω → ℝ) (Z : Ω' → ℝ) (d : ℝ) (g : ℝ × ℝ → ℝ) (hg : Continuous g)
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) μ')
    (hD : TendstoInMeasure μ D atTop (fun _ => d)) (hDm : ∀ n, AEMeasurable (D n) μ)
    (hg0 : ∀ x, g (x, d) = 0) :
    TendstoInMeasure μ (fun n ω => g (X n ω, D n ω)) atTop (fun _ => 0) := by
  have h := hX.continuous_comp_prodMk_of_tendstoInMeasure_const hg hD hDm
  exact tid_const_tim (0 : ℝ) h (fun ω => hg0 (Z ω))

lemma tim_of_ae_eventually_eq {μ : Measure Ω} [IsFiniteMeasure μ] (f g : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : ∀ n, AEStronglyMeasurable (g n) μ)
    (h : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, f n ω = g n ω) :
    TendstoInMeasure μ (fun n ω => f n ω - g n ω) atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_tendsto_ae (fun n => (hf n).sub (hg n)) ?_
  filter_upwards [h] with ω hω
  exact tendsto_const_nhds.congr' (hω.mono fun n hn => by simp [hn])

end C2gen

section C2comp

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]

open RLInference.QValueCLT MeasureTheory ProbabilityTheory Filter Topology

lemma dataStep_isProb (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (x : S × A) : IsProbabilityMeasure (dataStep P π R x) :=
  (inferInstance : IsProbabilityMeasure (dataKernel P π R (x, 0)))

lemma dataStep_integral (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (x : S × A) (G : (S × A) × ℝ → ℝ) (hG : Measurable G)
    (hint : ∀ y, Integrable (fun r => G (y, r)) (R y)) :
    ∫ z, G z ∂(dataStep P π R x) = ∑ y, Ptilde P π x y * ∫ r, G (y, r) ∂(R y) := by
  unfold dataStep
  rw [mix_integral _ (fun y => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
    R G hG hint]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.toReal_mul]
  rfl

/-- Transition-count increment for the coordinate `(x, k)`. -/
noncomputable def Hk (P : S × A → PMF S) (x : S × A) (k : S) (f : S × A)
    (z : (S × A) × ℝ) : ℝ :=
  if f = x then (if z.1.1 = k then (1 : ℝ) else 0) - Pmat P x k else 0

omit [DecidableEq A] [MeasurableSingletonClass A] in
lemma ind_meas (k : S) :
    Measurable (fun z : (S × A) × ℝ => if z.1.1 = k then (1 : ℝ) else 0) :=
  (measurable_of_finite (fun s : S => if s = k then (1 : ℝ) else 0)).comp measurable_fst.fst

omit [MeasurableSingletonClass A] in
lemma Hk_meas (P : S × A → PMF S) (x : S × A) (k : S) (f : S × A) :
    Measurable (Hk P x k f) := by
  unfold Hk
  by_cases h : f = x
  · simp only [h, eq_self_iff_true, if_true]
    exact (ind_meas k).sub_const _
  · simp only [h, if_false]
    exact measurable_const

omit [MeasurableSingletonClass A] in
lemma Hk_memLp (P : S × A → PMF S) (x : S × A) (k : S) (f : S × A)
    (μ : Measure ((S × A) × ℝ)) [IsFiniteMeasure μ] :
    MemLp (Hk P x k f) 2 μ := by
  refine MemLp.of_bound (Hk_meas P x k f).aestronglyMeasurable (1 + |Pmat P x k|)
    (Filter.Eventually.of_forall fun z => ?_)
  unfold Hk
  have h1 := le_abs_self (Pmat P x k)
  have h2 := neg_abs_le (Pmat P x k)
  split_ifs <;> (rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)

lemma Hk_integral (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (x : S × A) (k : S) (f : S × A) :
    ∫ z, Hk P x k f z ∂(dataStep P π R f) = 0 := by
  by_cases h : f = x
  · subst h
    rw [dataStep_integral P π R f (Hk P f k f) (Hk_meas P f k f)
      (fun y => (integrable_const ((if y.1 = k then (1 : ℝ) else 0) - Pmat P f k)).congr
        (ae_of_all _ fun r => by simp [Hk]))]
    have e : ∀ y : S × A, ∫ r, Hk P f k f (y, r) ∂(R y) =
        (if y.1 = k then (1 : ℝ) else 0) - Pmat P f k := fun y => by
      have hc : (fun r : ℝ => Hk P f k f (y, r)) =
          fun _ => (if y.1 = k then (1 : ℝ) else 0) - Pmat P f k := by
        funext r
        simp [Hk]
      rw [hc, integral_const]
      simp
    simp_rw [e, mul_sub, Finset.sum_sub_distrib, pt_fst, ← Finset.sum_mul, pt_row, one_mul,
      sub_self]
  · simp [Hk, h]

/-- Component CLT, reward coordinate `y` (summed at the shifted times `t + 1`). -/
lemma comp_clt_inl (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (ν₀ : PMF S) (y : S × A) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, gx R y (ω (t + 1)))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (gaussianReal 0 (∑ f, w f * ∫ z, gx R y z ^ 2 ∂(dataStep P π R f)).toNNReal) := by
  haveI := dataStep_isProb P π R
  have hvis := visits_ae P π R ν₀ hirr w hw_sum hw_stat
  refine chain_clt_scalar (dataKernel P π R) (initLaw ν₀ π R) (fun z => z.1) measurable_fst
    (dataStep P π R) (fun _ => rfl) (fun _ => gx R y) (fun _ => gx_meas R y)
    (fun f => ?_) (fun f => ?_) w hw_nonneg ?_
  · rw [memLp_two_iff_integrable_sq (gx_meas R y).aestronglyMeasurable]
    refine ⟨((gx_meas R y).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => sq_nonneg _)]
    unfold dataStep
    exact (mix_lint_sq _ (sum_pmf_mul_pmf (P f) π) R hR y).trans_lt ENNReal.ofReal_lt_top
  · unfold dataStep
    exact gx_integral_zero R hR y _
      (fun y' => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
  · filter_upwards [hvis] with ω hω f
    exact tendsto_pi_nhds.1 hω f

/-- Component CLT, transition coordinate `(x, k)`. -/
lemma comp_clt_inr (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)]
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (ν₀ : PMF S) (x : S × A) (k : S) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, Hk P x k (ω t).1 (ω (t + 1)))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (gaussianReal 0 (∑ f, w f * ∫ z, Hk P x k f z ^ 2 ∂(dataStep P π R f)).toNNReal) := by
  haveI := dataStep_isProb P π R
  have hvis := visits_ae P π R ν₀ hirr w hw_sum hw_stat
  refine chain_clt_scalar (dataKernel P π R) (initLaw ν₀ π R) (fun z => z.1) measurable_fst
    (dataStep P π R) (fun _ => rfl) (Hk P x k) (Hk_meas P x k)
    (fun f => Hk_memLp P x k f _) (fun f => Hk_integral P π R x k f) w hw_nonneg ?_
  filter_upwards [hvis] with ω hω f
  exact tendsto_pi_nhds.1 hω f

end C2comp

end QVCLT40192638

namespace QVCLT40192638
section SQ
variable {S A : Type} [Fintype S] [DecidableEq S]
open RLInference.QValueCLT Matrix
lemma SigmaP_quad (P' : S × A → S → ℝ) (x : S × A) (v : S → ℝ) :
    ∑ k₁, ∑ k₂, v k₁ * SigmaP P' x k₁ k₂ * v k₂ =
      ∑ k, P' x k * v k ^ 2 - (∑ k, P' x k * v k) ^ 2 := by
  have h : ∀ k₁ k₂, v k₁ * SigmaP P' x k₁ k₂ * v k₂ =
      (if k₁ = k₂ then P' x k₁ * v k₁ ^ 2 else 0) - (P' x k₁ * v k₁) * (P' x k₂ * v k₂) := by
    intro k₁ k₂
    unfold SigmaP
    split_ifs with hk
    · subst hk; ring
    · ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [sq (∑ k, P' x k * v k), Finset.sum_mul_sum]

end SQ
end QVCLT40192638



namespace QVCLT40192638

section C2comb

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]

open RLInference.QValueCLT MeasureTheory ProbabilityTheory Filter Topology Matrix

lemma gx_memLp_dataStep (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (y f : S × A) :
    MemLp (gx R y) 2 (dataStep P π R f) := by
  rw [memLp_two_iff_integrable_sq (gx_meas R y).aestronglyMeasurable]
  refine ⟨((gx_meas R y).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  unfold dataStep
  exact (mix_lint_sq _ (sum_pmf_mul_pmf (P f) π) R hR y).trans_lt ENNReal.ofReal_lt_top

lemma gx_integral_dataStep (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (y f : S × A) :
    ∫ z, gx R y z ∂(dataStep P π R f) = 0 := by
  unfold dataStep
  exact gx_integral_zero R hR y _
    (fun y' => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))

/-- Combined increment for a coefficient vector `c`. -/
noncomputable def Hc (P : S × A → PMF S) (R : S × A → Measure ℝ)
    (c : (S × A) ⊕ ((S × A) × S) → ℝ) (f : S × A) (z : (S × A) × ℝ) : ℝ :=
  ∑ y, c (Sum.inl y) * gx R y z + ∑ q : (S × A) × S, c (Sum.inr q) * Hk P q.1 q.2 f z

lemma Hc_meas (P : S × A → PMF S) (R : S × A → Measure ℝ)
    (c : (S × A) ⊕ ((S × A) × S) → ℝ) (f : S × A) : Measurable (Hc P R c f) := by
  unfold Hc
  exact (Finset.measurable_sum _ fun y _ => (gx_meas R y).const_mul _).add
    (Finset.measurable_sum _ fun q _ => (Hk_meas P q.1 q.2 f).const_mul _)

lemma Hc_memLp (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (c : (S × A) ⊕ ((S × A) × S) → ℝ) (f : S × A) :
    MemLp (Hc P R c f) 2 (dataStep P π R f) := by
  haveI := dataStep_isProb P π R f
  unfold Hc
  exact (memLp_finset_sum _ fun y _ => (gx_memLp_dataStep P π R hR y f).const_mul _).add
    (memLp_finset_sum _ fun q _ => (Hk_memLp P q.1 q.2 f _).const_mul _)

lemma Hc_integral (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (c : (S × A) ⊕ ((S × A) × S) → ℝ) (f : S × A) :
    ∫ z, Hc P R c f z ∂(dataStep P π R f) = 0 := by
  haveI := dataStep_isProb P π R f
  have h1 : ∀ y, Integrable (fun z => c (Sum.inl y) * gx R y z) (dataStep P π R f) :=
    fun y => ((gx_memLp_dataStep P π R hR y f).integrable one_le_two).const_mul _
  have h2 : ∀ q : (S × A) × S, Integrable (fun z => c (Sum.inr q) * Hk P q.1 q.2 f z)
      (dataStep P π R f) :=
    fun q => ((Hk_memLp P q.1 q.2 f _).integrable one_le_two).const_mul _
  unfold Hc
  rw [integral_add (integrable_finset_sum _ fun y _ => h1 y)
      (integrable_finset_sum _ fun q _ => h2 q),
    integral_finset_sum _ fun y _ => h1 y, integral_finset_sum _ fun q _ => h2 q]
  simp [integral_const_mul, gx_integral_dataStep P π R hR, Hk_integral P π R]

/-- Combined-direction CLT. -/
lemma comb_clt (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (ν₀ : PMF S)
    (c : (S × A) ⊕ ((S × A) × S) → ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, Hc P R c (ω t).1 (ω (t + 1)))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (gaussianReal 0 (∑ f, w f * ∫ z, Hc P R c f z ^ 2 ∂(dataStep P π R f)).toNNReal) := by
  haveI := dataStep_isProb P π R
  have hvis := visits_ae P π R ν₀ hirr w hw_sum hw_stat
  refine chain_clt_scalar (dataKernel P π R) (initLaw ν₀ π R) (fun z => z.1) measurable_fst
    (dataStep P π R) (fun _ => rfl) (Hc P R c) (Hc_meas P R c)
    (fun f => Hc_memLp P π R hR c f) (fun f => Hc_integral P π R hR c f) w hw_nonneg ?_
  filter_upwards [hvis] with ω hω f
  exact tendsto_pi_nhds.1 hω f

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma Hc_apply (P : S × A → PMF S) (R : S × A → Measure ℝ)
    (c : (S × A) ⊕ ((S × A) × S) → ℝ) (f : S × A) (y : S × A) (r : ℝ) :
    Hc P R c f (y, r) = c (Sum.inl y) * (r - muR R y) +
      (c (Sum.inr (f, y.1)) - ∑ k, Pmat P f k * c (Sum.inr (f, k))) := by
  have h1 : ∑ y', c (Sum.inl y') * gx R y' (y, r) = c (Sum.inl y) * (r - muR R y) := by
    simp [gx, mul_ite]
  have h2 : ∑ q : (S × A) × S, c (Sum.inr q) * Hk P q.1 q.2 f (y, r) =
      c (Sum.inr (f, y.1)) - ∑ k, Pmat P f k * c (Sum.inr (f, k)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single f]
    · simp only [Hk, if_true, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
      congr 1
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · intro x _ hx
      simp [Hk, Ne.symm hx]
    · simp
  unfold Hc
  rw [h1, h2]

omit [DecidableEq S] [Fintype A] [DecidableEq A] [MeasurableSpace S]
  [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma int_sq_affine (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)]
    (hR : ∀ x, MemLp id 2 (R x)) (y : S × A) (a b : ℝ) :
    ∫ r, (a * (r - muR R y) + b) ^ 2 ∂(R y) = a ^ 2 * Vx R y + b ^ 2 := by
  have hi : Integrable (fun r : ℝ => r) (R y) := (hR y).integrable one_le_two
  have hd : Integrable (fun r : ℝ => r - muR R y) (R y) := hi.sub (integrable_const _)
  have hs : Integrable (fun r : ℝ => (r - muR R y) ^ 2) (R y) :=
    ((hR y).sub (memLp_const (muR R y))).integrable_sq
  have e : ∀ r : ℝ, (a * (r - muR R y) + b) ^ 2 =
      a ^ 2 * (r - muR R y) ^ 2 + (2 * a * b) * (r - muR R y) + b ^ 2 := fun r => by ring
  have h12 : Integrable (fun r : ℝ => a ^ 2 * (r - muR R y) ^ 2 + 2 * a * b * (r - muR R y))
      (R y) := (hs.const_mul _).add (hd.const_mul _)
  simp_rw [e]
  rw [integral_add h12 (integrable_const _),
    integral_add (hs.const_mul _) (hd.const_mul _), integral_const_mul, integral_const_mul,
    integral_sub hi (integrable_const _)]
  simp [Vx, muR]

omit [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma pt_marg (P : S × A → PMF S) (π : S → PMF A) (f : S × A) (h : S → ℝ) :
    ∑ y, Ptilde P π f y * h y.1 = ∑ k, Pmat P f k * h k := by
  have e : ∀ s, ∑ a, Pmat P f s * (π s a).toReal * h s = Pmat P f s * h s := fun s => by
    rw [← Finset.sum_mul, ← Finset.mul_sum, pmf_toReal_sum, mul_one]
  unfold Ptilde
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun s _ => e s

lemma Hc_var (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (c : (S × A) ⊕ ((S × A) × S) → ℝ) (f : S × A) :
    ∫ z, Hc P R c f z ^ 2 ∂(dataStep P π R f) =
      ∑ y, Ptilde P π f y * (c (Sum.inl y) ^ 2 * Vx R y) +
      (∑ k, Pmat P f k * c (Sum.inr (f, k)) ^ 2 -
        (∑ k, Pmat P f k * c (Sum.inr (f, k))) ^ 2) := by
  have hint : ∀ y, Integrable (fun r => Hc P R c f (y, r) ^ 2) (R y) := by
    intro y
    have hm : MemLp (fun r : ℝ => c (Sum.inl y) * (r - muR R y) +
        (c (Sum.inr (f, y.1)) - ∑ k, Pmat P f k * c (Sum.inr (f, k)))) 2 (R y) :=
      (((hR y).sub (memLp_const _)).const_mul _).add (memLp_const _)
    simp_rw [Hc_apply]
    exact hm.integrable_sq
  rw [dataStep_integral P π R f (fun z => Hc P R c f z ^ 2) ((Hc_meas P R c f).pow_const 2) hint]
  simp_rw [Hc_apply, int_sq_affine R hR, mul_add, Finset.sum_add_distrib]
  congr 1
  set m := ∑ k, Pmat P f k * c (Sum.inr (f, k)) with hm
  rw [pt_marg P π f (fun s => (c (Sum.inr (f, s)) - m) ^ 2)]
  have hs : ∑ k, Pmat P f k = 1 := pmf_toReal_sum (P f)
  have e : ∀ k, Pmat P f k * (c (Sum.inr (f, k)) - m) ^ 2 =
      Pmat P f k * c (Sum.inr (f, k)) ^ 2 - 2 * m * (Pmat P f k * c (Sum.inr (f, k))) +
        m ^ 2 * Pmat P f k := fun k => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, ← hm]
  ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma quad_SigmaRP (P' : S × A → S → ℝ) (sig2 w : S × A → ℝ)
    (v : (S × A) ⊕ ((S × A) × S) → ℝ) :
    v ⬝ᵥ SigmaRP P' sig2 w *ᵥ v = ∑ x, v (Sum.inl x) * (sig2 x / w x) * v (Sum.inl x) +
      ∑ x, (w x)⁻¹ * ∑ k₁, ∑ k₂, v (Sum.inr (x, k₁)) * SigmaP P' x k₁ k₂ * v (Sum.inr (x, k₂)) := by
  have hDP : ∀ (u : (S × A) × S → ℝ) (p : (S × A) × S),
      ∑ q, DP P' w p q * u q = ∑ k₂, SigmaP P' p.1 p.2 k₂ / w p.1 * u (p.1, k₂) := by
    intro u p
    rw [Fintype.sum_prod_type, Finset.sum_eq_single p.1]
    · simp [DP]
    · intro y _ hy
      simp [DP, Ne.symm hy]
    · simp
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, SigmaRP,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add, diagonal_apply, ite_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hDP]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => by ring
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₁ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₂ _ => ?_
    rw [div_eq_mul_inv]
    ring

omit [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [MeasurableSpace S]
  [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma sigma2R_eq_Vx (R : S × A → Measure ℝ) (y : S × A) : sigma2R R y = Vx R y := by
  unfold sigma2R
  rw [variance_eq_integral measurable_id.aemeasurable]
  rfl

/-- Coefficients `t_j / w_j` of a direction `t`. -/
noncomputable def cw (w : S × A → ℝ) (t : (S × A) ⊕ ((S × A) × S) → ℝ) :
    (S × A) ⊕ ((S × A) × S) → ℝ :=
  Sum.elim (fun y => t (Sum.inl y) / w y) (fun q => t (Sum.inr q) / w q.1)

lemma comb_var (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y)
    (t : (S × A) ⊕ ((S × A) × S) → ℝ) :
    ∑ f, w f * ∫ z, Hc P R (cw w t) f z ^ 2 ∂(dataStep P π R f) =
      t ⬝ᵥ SigmaRP (Pmat P) (sigma2R R) w *ᵥ t := by
  rw [quad_SigmaRP]
  have hL : ∀ f, w f * ∫ z, Hc P R (cw w t) f z ^ 2 ∂(dataStep P π R f) =
      (∑ y, w f * (Ptilde P π f y * (cw w t (Sum.inl y) ^ 2 * Vx R y))) +
      w f * (∑ k, Pmat P f k * cw w t (Sum.inr (f, k)) ^ 2 -
        (∑ k, Pmat P f k * cw w t (Sum.inr (f, k))) ^ 2) := fun f => by
    rw [Hc_var P π R hR, mul_add, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun f _ => hL f, Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun y _ => ?_
    have e : ∑ f, w f * (Ptilde P π f y * (cw w t (Sum.inl y) ^ 2 * Vx R y)) =
        (∑ f, w f * Ptilde P π f y) * (cw w t (Sum.inl y) ^ 2 * Vx R y) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun f _ => by ring
    have hw := (hw_pos y).ne'
    rw [e, hw_stat y, sigma2R_eq_Vx]
    simp only [cw, Sum.elim_inl]
    field_simp
    try ring
  · refine Finset.sum_congr rfl fun x _ => ?_
    have hq : ∑ k₁, ∑ k₂, t (Sum.inr (x, k₁)) * SigmaP (Pmat P) x k₁ k₂ * t (Sum.inr (x, k₂)) =
        ∑ k, Pmat P x k * t (Sum.inr (x, k)) ^ 2 - (∑ k, Pmat P x k * t (Sum.inr (x, k))) ^ 2 :=
      SigmaP_quad (Pmat P) x (fun k => t (Sum.inr (x, k)))
    rw [hq]
    have hw := (hw_pos x).ne'
    simp only [cw, Sum.elim_inr]
    have e1 : ∑ k, Pmat P x k * (t (Sum.inr (x, k)) / w x) ^ 2 =
        (∑ k, Pmat P x k * t (Sum.inr (x, k)) ^ 2) / w x ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, Pmat P x k * (t (Sum.inr (x, k)) / w x) =
        (∑ k, Pmat P x k * t (Sum.inr (x, k))) / w x := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1, e2]
    field_simp
    try ring

/-- Direction CLT with the target variance `tᵀ Σ_{R,P} t`. -/
lemma dir_clt (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (ν₀ : PMF S)
    (t : (S × A) ⊕ ((S × A) × S) → ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (Real.sqrt n)⁻¹ * ∑ s ∈ Finset.range n, Hc P R (cw w t) (ω s).1 (ω (s + 1)))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (gaussianReal 0 (t ⬝ᵥ SigmaRP (Pmat P) (sigma2R R) w *ᵥ t).toNNReal) := by
  have h := comb_clt P π R hR hirr w (fun x => (hw_pos x).le) hw_sum hw_stat ν₀ (cw w t)
  rwa [comb_var P π R hR w hw_pos hw_stat t] at h

end C2comb

end QVCLT40192638

namespace QVCLT40192638

section C2rem

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]

open RLInference.QValueCLT MeasureTheory ProbabilityTheory Filter Topology

lemma visits_meas2 (n : ℕ) (x : S × A) :
    Measurable (fun ω : ℕ → (S × A) × ℝ => (visits n ω x : ℝ)) := by
  have h : ∀ ω : ℕ → (S × A) × ℝ, (visits n ω x : ℝ) =
      ∑ t ∈ Finset.range n, if (ω t).1 = x then (1 : ℝ) else 0 := fun ω => by
    rw [Finset.sum_boole]
    rfl
  simp_rw [h]
  exact Finset.measurable_sum _ fun t _ =>
    Measurable.ite ((measurable_fst.comp (measurable_pi_apply t)) (measurableSet_singleton x))
      measurable_const measurable_const

/-- `n / visits` tends to `1 / w` in measure. -/
lemma Dn_tim (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (ν₀ : PMF S)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (y : S × A) :
    TendstoInMeasure (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) => (n : ℝ) / visits n ω y) atTop
      (fun _ => 1 / w y) := by
  refine tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_const.div (visits_meas2 n y)).aestronglyMeasurable) ?_
  filter_upwards [visits_ae P π R ν₀ hirr w hw_sum hw_stat] with ω hω
  have h1 := (tendsto_pi_nhds.1 hω y).inv₀ (hw_pos y).ne'
  rw [one_div]
  exact h1.congr fun n => inv_div _ _

/-- The boundary term `gx (ω n) / √n` tends to `0` in measure (Chebyshev). -/
lemma bnd_tim (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (ν₀ : PMF S) (y : S × A) :
    TendstoInMeasure (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) => (Real.sqrt n)⁻¹ * gx R y (ω n)) atTop
      (fun _ => 0) := by
  set μ := MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R) with hμ
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hb : ∀ n : ℕ, 1 ≤ n → μ {ω | ε ≤ ‖(Real.sqrt n)⁻¹ * gx R y (ω n) - 0‖} ≤
      ENNReal.ofReal (Vx R y) / ENNReal.ofReal (ε ^ 2 * n) := by
    intro n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hpos : 0 < ε ^ 2 * n := mul_pos (pow_pos hε 2) hn'
    have hsub : {ω : ℕ → (S × A) × ℝ | ε ≤ ‖(Real.sqrt n)⁻¹ * gx R y (ω n) - 0‖} ⊆
        {ω | ENNReal.ofReal (ε ^ 2 * n) ≤ ENNReal.ofReal (gx R y (ω n) ^ 2)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, sub_zero, norm_mul, norm_inv, Real.norm_eq_abs] at hω ⊢
      apply ENNReal.ofReal_le_ofReal
      have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
      rw [abs_of_pos hs, inv_mul_eq_div, le_div_iff₀ hs] at hω
      have h3 : (ε * Real.sqrt n) ^ 2 ≤ |gx R y (ω n)| ^ 2 :=
        pow_le_pow_left₀ (by positivity) hω 2
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), sq_abs] at h3
      exact h3
    have hm : AEMeasurable (fun ω : ℕ → (S × A) × ℝ => ENNReal.ofReal (gx R y (ω n) ^ 2)) μ :=
      (ENNReal.measurable_ofReal.comp
        (((gx_meas R y).comp (measurable_pi_apply n)).pow_const 2)).aemeasurable
    have hmk := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal (ε ^ 2 * n))
    calc μ {ω | ε ≤ ‖(Real.sqrt n)⁻¹ * gx R y (ω n) - 0‖}
        ≤ μ {ω | ENNReal.ofReal (ε ^ 2 * n) ≤ ENNReal.ofReal (gx R y (ω n) ^ 2)} :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (Vx R y) / ENNReal.ofReal (ε ^ 2 * n) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hpos).ne')
          (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hmk.trans (chain_lint_sq P π R hR ν₀ y n)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Vx R y) / ENNReal.ofReal (ε ^ 2 * n))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (Vx R y / (ε ^ 2 * n))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      exact (tendsto_const_div_atTop_nhds_zero_nat (Vx R y / ε ^ 2)).congr fun n => div_div _ _ _
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : 0 < ε ^ 2 * (n : ℝ) := mul_pos (pow_pos hε 2) (Nat.cast_pos.2 hn)
    rw [ENNReal.ofReal_div_of_pos hpos]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun n => by simp) ((eventually_ge_atTop 1).mono hb)

end C2rem

end QVCLT40192638

namespace QVCLT40192638

section C2alg

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]

open RLInference.QValueCLT MeasureTheory ProbabilityTheory Filter Topology

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma visits_le_n (n : ℕ) (ω : ℕ → (S × A) × ℝ) (x : S × A) : visits n ω x ≤ n := by
  unfold visits
  exact (Finset.card_filter_le _ _).trans (by simp)

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma scale_alg (n v T : ℝ) (hn : 0 < n) (hv : 0 < v) :
    Real.sqrt n * ((1 / n * T) / (v / n)) = n / v * ((Real.sqrt n)⁻¹ * T) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hn' : n = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn.le).symm
  set s := Real.sqrt n
  rw [hn']
  field_simp

/-- Reward coordinate of the scaled error, in terms of the shifted sum and the boundary terms. -/
lemma mu_scaled (u0 : S × A → ℝ) (R : S × A → Measure ℝ) (n : ℕ) (ω : ℕ → (S × A) × ℝ)
    (y : S × A) (h : 0 < visits n ω y) :
    Real.sqrt n * (muHat u0 n ω y - muR R y) = (n : ℝ) / visits n ω y *
      ((Real.sqrt n)⁻¹ * (∑ s ∈ Finset.range n, gx R y (ω (s + 1)) + gx R y (ω 0) -
        gx R y (ω n))) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (lt_of_lt_of_le h (visits_le_n n ω y))
  have hv : (0 : ℝ) < visits n ω y := Nat.cast_pos.2 h
  have h1 := Finset.sum_range_succ (fun k => gx R y (ω k)) n
  have h2 := Finset.sum_range_succ' (fun k => gx R y (ω k)) n
  have hsum : ∑ k ∈ Finset.range n, gx R y (ω k) =
      ∑ s ∈ Finset.range n, gx R y (ω (s + 1)) + gx R y (ω 0) - gx R y (ω n) := by
    linarith
  rw [muHat_alg u0 R n ω y h, add_sub_cancel_left, ← hsum]
  exact scale_alg _ _ _ hn hv

/-- Transition coordinate of the scaled error. -/
lemma P_scaled (P : S × A → PMF S) (p0 : S × A → S → ℝ) (n : ℕ) (ω : ℕ → (S × A) × ℝ)
    (x : S × A) (k : S) (h : 0 < visits n ω x) :
    Real.sqrt n * (PHat p0 n ω x k - Pmat P x k) = (n : ℝ) / visits n ω x *
      ((Real.sqrt n)⁻¹ * ∑ s ∈ Finset.range n, Hk P x k (ω s).1 (ω (s + 1))) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (lt_of_lt_of_le h (visits_le_n n ω x))
  have hv : (0 : ℝ) < visits n ω x := Nat.cast_pos.2 h
  have hc : ∑ s ∈ Finset.range n, Hk P x k (ω s).1 (ω (s + 1)) =
      (((Finset.range n).filter fun t => (ω t).1 = x ∧ (ω (t + 1)).1.1 = k).card : ℝ) -
        (visits n ω x : ℝ) * Pmat P x k := by
    simp only [Hk]
    rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_boole, Finset.filter_filter]
    rfl
  have hP : PHat p0 n ω x k = (((Finset.range n).filter fun t => (ω t).1 = x ∧
      (ω (t + 1)).1.1 = k).card : ℝ) / (visits n ω x : ℝ) := by
    simp [PHat, h]
  rw [hc, hP]
  have e : (((Finset.range n).filter fun t => (ω t).1 = x ∧ (ω (t + 1)).1.1 = k).card : ℝ) /
      (visits n ω x : ℝ) - Pmat P x k =
      (1 / (n : ℝ) * ((((Finset.range n).filter fun t => (ω t).1 = x ∧
        (ω (t + 1)).1.1 = k).card : ℝ) - (visits n ω x : ℝ) * Pmat P x k)) /
        ((visits n ω x : ℝ) / n) := by
    field_simp
  rw [e]
  exact scale_alg _ _ _ hn hv

end C2alg

end QVCLT40192638

namespace QVCLT40192638
section C2x
open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RLInference.QValueCLT
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

lemma SigmaP_quad_nonneg (P' : S × A → S → ℝ) (x : S × A) (h0 : ∀ k, 0 ≤ P' x k)
    (h1 : ∑ k, P' x k = 1) (v : S → ℝ) :
    0 ≤ ∑ k₁, ∑ k₂, v k₁ * SigmaP P' x k₁ k₂ * v k₂ := by
  rw [SigmaP_quad]
  have key : ∀ m : ℝ, ∑ k, P' x k * (v k - m) ^ 2 =
      ∑ k, P' x k * v k ^ 2 - 2 * m * (∑ k, P' x k * v k) + m ^ 2 := by
    intro m
    have e : ∀ k, P' x k * (v k - m) ^ 2 =
        P' x k * v k ^ 2 - 2 * m * (P' x k * v k) + m ^ 2 * P' x k := fun k => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, mul_one]
  have hnn := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) =>
    mul_nonneg (h0 k) (sq_nonneg (v k - ∑ k, P' x k * v k)))
  rw [key] at hnn
  nlinarith [hnn]

lemma SigmaP_symm (P' : S × A → S → ℝ) (x : S × A) (k₁ k₂ : S) :
    SigmaP P' x k₁ k₂ = SigmaP P' x k₂ k₁ := by
  unfold SigmaP
  by_cases h : k₁ = k₂
  · subst h; rfl
  · simp [h, Ne.symm h, mul_comm]

/-- C5: `Σ_{R,P}` is positive semidefinite (stochastic rows, `σ² ≥ 0`, `w > 0`). -/
lemma SigmaRP_posSemidef (P' : S × A → S → ℝ) (sig2 w : S × A → ℝ)
    (h0 : ∀ x k, 0 ≤ P' x k) (h1 : ∀ x, ∑ k, P' x k = 1)
    (hs : ∀ x, 0 ≤ sig2 x) (hw : ∀ x, 0 < w x) :
    (SigmaRP P' sig2 w).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · refine IsHermitian.fromBlocks ?_ (by simp) ?_
    · ext x y
      rw [conjTranspose_apply, star_trivial]
      by_cases h : x = y
      · subst h; rfl
      · simp [diagonal_apply, h, Ne.symm h]
    · ext p q
      rw [conjTranspose_apply, star_trivial]
      by_cases h : p.1 = q.1
      · simp only [DP]
        rw [if_pos h.symm, if_pos h, h, SigmaP_symm]
      · simp [DP, h, Ne.symm h]
  · have hDP : ∀ (u : (S × A) × S → ℝ) (p : (S × A) × S),
        ∑ q, DP P' w p q * u q = ∑ k₂, SigmaP P' p.1 p.2 k₂ / w p.1 * u (p.1, k₂) := by
      intro u p
      rw [Fintype.sum_prod_type, Finset.sum_eq_single p.1]
      · simp [DP]
      · intro y _ hy
        simp [DP, Ne.symm hy]
      · simp
    have h2 : ∀ x : S × A, 0 ≤ ∑ k₁, v (Sum.inr (x, k₁)) *
        ∑ k₂, SigmaP P' x k₁ k₂ / w x * v (Sum.inr (x, k₂)) := by
      intro x
      have e : ∑ k₁, v (Sum.inr (x, k₁)) * ∑ k₂, SigmaP P' x k₁ k₂ / w x * v (Sum.inr (x, k₂)) =
          (w x)⁻¹ * ∑ k₁, ∑ k₂, v (Sum.inr (x, k₁)) * SigmaP P' x k₁ k₂ * v (Sum.inr (x, k₂)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k₁ _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k₂ _ => ?_
        rw [div_eq_mul_inv]; ring
      rw [e]
      exact mul_nonneg (inv_nonneg.2 (hw x).le) (SigmaP_quad_nonneg P' x (h0 x) (h1 x) _)
    simp only [star_trivial, dotProduct, mulVec, Fintype.sum_sum_type, SigmaRP,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add, diagonal_apply, ite_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply add_nonneg
    · refine Finset.sum_nonneg fun x _ => ?_
      have hc := div_nonneg (hs x) (hw x).le
      nlinarith [mul_nonneg hc (mul_self_nonneg (v (Sum.inl x)))]
    · simp only [hDP]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_nonneg fun x _ => ?_
      dsimp only
      exact h2 x

section C5b



lemma Ptilde_nonneg (P : S × A → PMF S) (π : S → PMF A) (x y : S × A) :
    0 ≤ Ptilde P π x y := by
  unfold Ptilde Pmat
  positivity

lemma Ptilde_pow_nonneg (P : S × A → PMF S) (π : S → PMF A) (m : ℕ) (x y : S × A) :
    0 ≤ (Ptilde P π ^ m) x y := by
  induction m generalizing y with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih z) (Ptilde_nonneg P π z y)

lemma vecMul_Ptilde_pow (P : S × A → PMF S) (π : S → PMF A) (w : S × A → ℝ)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (m : ℕ) :
    w ᵥ* (Ptilde P π ^ m) = w := by
  have h1 : w ᵥ* Ptilde P π = w := by
    funext y
    simp only [vecMul, dotProduct]
    exact hw_stat y
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ← vecMul_vecMul, ih, h1]

/-- C5b: an irreducible chain's stationary law charges every pair. -/
lemma w_pos (P : S × A → PMF S) (π : S → PMF A)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (y : S × A) : 0 < w y := by
  obtain ⟨x0, hx0⟩ : ∃ x0, 0 < w x0 := by
    by_contra h
    push_neg at h
    have : ∑ x, w x = 0 := Finset.sum_eq_zero fun x _ => le_antisymm (h x) (hw_nonneg x)
    linarith
  obtain ⟨m, hm⟩ := hirr x0 y
  have e := congrFun (vecMul_Ptilde_pow P π w hw_stat m) y
  simp only [vecMul, dotProduct] at e
  have hle : w x0 * (Ptilde P π ^ m) x0 y ≤ ∑ x, w x * (Ptilde P π ^ m) x y :=
    Finset.single_le_sum (f := fun x => w x * (Ptilde P π ^ m) x y)
      (fun x _ => mul_nonneg (hw_nonneg x) (Ptilde_pow_nonneg P π m x y)) (Finset.mem_univ x0)
  have := mul_pos hx0 hm
  linarith

end C5b

lemma Pmat_nonneg (P : S × A → PMF S) (x : S × A) (k : S) : 0 ≤ Pmat P x k := by
  unfold Pmat
  positivity

lemma Pmat_sum (P : S × A → PMF S) (x : S × A) : ∑ k, Pmat P x k = 1 := by
  unfold Pmat
  have h : ∑ k, P x k = 1 := (tsum_fintype _).symm.trans (P x).tsum_coe
  rw [← ENNReal.toReal_sum (fun k _ => PMF.apply_ne_top _ _), h, ENNReal.toReal_one]

variable [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A]

lemma meas_eqset (t : ℕ) (x : S × A) :
    MeasurableSet {ω : ℕ → (S × A) × ℝ | (ω t).1 = x} :=
  (measurable_fst.comp (measurable_pi_apply t)) (measurableSet_singleton x)

lemma meas_eqset2 (t : ℕ) (x : S × A) (k : S) :
    MeasurableSet {ω : ℕ → (S × A) × ℝ | (ω t).1 = x ∧ (ω (t + 1)).1.1 = k} :=
  (meas_eqset t x).inter
    ((measurable_fst.comp (measurable_fst.comp (measurable_pi_apply (t + 1))))
      (measurableSet_singleton k))

lemma visits_real (n : ℕ) (ω : ℕ → (S × A) × ℝ) (x : S × A) :
    (visits n ω x : ℝ) = ∑ t ∈ Finset.range n, if (ω t).1 = x then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  rfl

lemma visits_meas (n : ℕ) (x : S × A) :
    Measurable (fun ω : ℕ → (S × A) × ℝ => (visits n ω x : ℝ)) := by
  simp_rw [visits_real]
  exact Finset.measurable_sum _ fun t _ =>
    Measurable.ite (meas_eqset t x) measurable_const measurable_const

lemma visits_pos_meas (n : ℕ) (x : S × A) :
    MeasurableSet {ω : ℕ → (S × A) × ℝ | 0 < visits n ω x} := by
  have e : {ω : ℕ → (S × A) × ℝ | 0 < visits n ω x} =
      {ω | (0 : ℝ) < (visits n ω x : ℝ)} := by
    ext ω
    simp
  rw [e]
  exact measurableSet_lt measurable_const (visits_meas n x)

lemma muHat_meas (u0 : S × A → ℝ) (n : ℕ) :
    Measurable (fun ω : ℕ → (S × A) × ℝ => muHat u0 n ω) := by
  refine measurable_pi_lambda _ fun x => ?_
  have hs : Measurable (fun ω : ℕ → (S × A) × ℝ =>
      ∑ t ∈ (Finset.range n).filter (fun t => (ω t).1 = x), (ω t).2) := by
    simp_rw [Finset.sum_filter]
    exact Finset.measurable_sum _ fun t _ =>
      Measurable.ite (meas_eqset t x) (measurable_snd.comp (measurable_pi_apply t))
        measurable_const
  exact Measurable.ite (visits_pos_meas n x) (hs.div (visits_meas n x)) measurable_const

lemma PHat_meas (p0 : S × A → S → ℝ) (n : ℕ) :
    Measurable (fun ω : ℕ → (S × A) × ℝ => PHat p0 n ω) := by
  refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun k => ?_
  have hc : Measurable (fun ω : ℕ → (S × A) × ℝ =>
      (((Finset.range n).filter fun t => (ω t).1 = x ∧ (ω (t + 1)).1.1 = k).card : ℝ)) := by
    have e : ∀ ω : ℕ → (S × A) × ℝ,
        (((Finset.range n).filter fun t => (ω t).1 = x ∧ (ω (t + 1)).1.1 = k).card : ℝ) =
          ∑ t ∈ Finset.range n, if (ω t).1 = x ∧ (ω (t + 1)).1.1 = k then (1 : ℝ) else 0 :=
      fun ω => by rw [Finset.sum_boole]
    simp_rw [e]
    exact Finset.measurable_sum _ fun t _ =>
      Measurable.ite (meas_eqset2 t x k) measurable_const measurable_const
  exact Measurable.ite (visits_pos_meas n x) (hc.div (visits_meas n x)) measurable_const

lemma thetaHat_meas (u0 : S × A → ℝ) (p0 : S × A → S → ℝ) (n : ℕ) :
    Measurable (fun ω : ℕ → (S × A) × ℝ => thetaHat u0 p0 n ω) := by
  refine measurable_pi_lambda _ fun i => ?_
  rcases i with x | q
  · exact (measurable_pi_apply x).comp (muHat_meas u0 n)
  · exact (measurable_pi_apply q.2).comp ((measurable_pi_apply q.1).comp (PHat_meas p0 n))

/-- C6: the Euclidean plug-in parameter is measurable. -/
lemma thetaHatE_meas (u0 : S × A → ℝ) (p0 : S × A → S → ℝ) (n : ℕ) :
    Measurable (fun ω : ℕ → (S × A) × ℝ =>
      (WithLp.toLp 2 (thetaHat u0 p0 n ω) : EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)))) :=
  (PiLp.continuous_toLp 2 _).measurable.comp (thetaHat_meas u0 p0 n)

end C2x
end QVCLT40192638

section C7wrap
open MeasureTheory ProbabilityTheory Filter Matrix Topology Complex

namespace QVCLT40192638

lemma charFun_map_eq_inner {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → EuclideanSpace ℝ ι) (hY : AEMeasurable Y μ) (t : EuclideanSpace ℝ ι) :
    charFun (μ.map Y) t = charFun (μ.map (fun ω => inner ℝ t (Y ω))) 1 := by
  have hY' : AEMeasurable (fun ω => inner ℝ t (Y ω)) μ :=
    (continuous_const.inner continuous_id).measurable.comp_aemeasurable hY
  rw [charFun_apply, charFun_apply_real, integral_map hY, integral_map hY']
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [real_inner_comm]
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · exact (Continuous.aestronglyMeasurable (by fun_prop))

/-- C7: Cramer-Wold device to a multivariate Gaussian limit. -/
theorem C7_cramerWold {ι Ω : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → EuclideanSpace ℝ ι) (hY : ∀ n, AEMeasurable (Y n) μ)
    (Sig : Matrix ι ι ℝ) (hSig : Sig.PosSemidef)
    (h : ∀ t : EuclideanSpace ℝ ι, TendstoInDistribution
      (fun (n : ℕ) ω => inner ℝ t (Y n ω)) atTop id (fun _ => μ)
      (gaussianReal 0 (t ⬝ᵥ Sig *ᵥ t).toNNReal)) :
    TendstoInDistribution Y atTop id (fun _ => μ) (multivariateGaussian 0 Sig) where
  forall_aemeasurable := hY
  aemeasurable_limit := aemeasurable_id
  tendsto := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun (fun t => ?_)
    have h2 := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 (h t).tendsto 1
    simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at h2 ⊢
    have hnn : 0 ≤ t ⬝ᵥ Sig *ᵥ t := by
      have := (posSemidef_iff_dotProduct_mulVec.1 hSig).2 t
      simpa [star_trivial] using this
    rw [charFun_multivariateGaussian hSig, charFun_gaussianReal] at *
    have e : ∀ n, charFun (μ.map (Y n)) t = charFun (μ.map (fun ω => inner ℝ t (Y n ω))) 1 :=
      fun n => charFun_map_eq_inner μ (Y n) (hY n) t
    simp only [e]
    convert h2 using 2
    simp [Real.coe_toNNReal _ hnn]

end QVCLT40192638
end C7wrap


namespace QVCLT40192638

section C2fin

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]

open RLInference.QValueCLT MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable def Xm (R : S × A → Measure ℝ) (y : S × A) (n : ℕ) (ω : ℕ → (S × A) × ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ s ∈ Finset.range n, gx R y (ω (s + 1))

noncomputable def Xp (P : S × A → PMF S) (q : (S × A) × S) (n : ℕ) (ω : ℕ → (S × A) × ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ s ∈ Finset.range n, Hk P q.1 q.2 (ω s).1 (ω (s + 1))

noncomputable def Dv (n : ℕ) (ω : ℕ → (S × A) × ℝ) (x : S × A) : ℝ :=
  (n : ℝ) / (visits n ω x : ℝ)

noncomputable def Bd (R : S × A → Measure ℝ) (y : S × A) (n : ℕ) (ω : ℕ → (S × A) × ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * (gx R y (ω 0) - gx R y (ω n))

noncomputable def Rem (P : S × A → PMF S) (R : S × A → Measure ℝ) (w : S × A → ℝ)
    (t : (S × A) ⊕ ((S × A) × S) → ℝ) (n : ℕ) (ω : ℕ → (S × A) × ℝ) : ℝ :=
  ∑ y, (t (Sum.inl y) * ((Dv n ω y - 1 / w y) * Xm R y n ω) +
      t (Sum.inl y) * (Dv n ω y * Bd R y n ω)) +
    ∑ q : (S × A) × S, t (Sum.inr q) * ((Dv n ω q.1 - 1 / w q.1) * Xp P q n ω)

lemma Hc_sum_lin (P : S × A → PMF S) (R : S × A → Measure ℝ)
    (c : (S × A) ⊕ ((S × A) × S) → ℝ) (n : ℕ) (ω : ℕ → (S × A) × ℝ) :
    (Real.sqrt n)⁻¹ * ∑ s ∈ Finset.range n, Hc P R c (ω s).1 (ω (s + 1)) =
      ∑ y, c (Sum.inl y) * Xm R y n ω + ∑ q : (S × A) × S, c (Sum.inr q) * Xp P q n ω := by
  unfold Hc Xm Xp
  simp only [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun s _ => by ring)
  · exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun s _ => by ring)

lemma inner_toLp_eq {ι : Type} [Fintype ι] (t : EuclideanSpace ℝ ι) (f : ι → ℝ) :
    inner ℝ t (WithLp.toLp 2 f : EuclideanSpace ℝ ι) = ∑ i, t i * f i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma alg_rem (P : S × A → PMF S) (R : S × A → Measure ℝ) (u0 : S × A → ℝ)
    (p0 : S × A → S → ℝ) (w : S × A → ℝ) (t : EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)))
    (n : ℕ) (ω : ℕ → (S × A) × ℝ) (hv : ∀ x, 0 < visits n ω x) :
    inner ℝ t (WithLp.toLp 2 (fun i => Real.sqrt n * (thetaHat u0 p0 n ω i - theta R P i)) :
        EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S))) -
      (Real.sqrt n)⁻¹ * ∑ s ∈ Finset.range n, Hc P R (cw w t) (ω s).1 (ω (s + 1)) =
      Rem P R w t n ω := by
  rw [inner_toLp_eq, Fintype.sum_sum_type, Hc_sum_lin]
  simp only [thetaHat, theta, Sum.elim_inl, Sum.elim_inr, cw]
  have h1 : ∑ y, t (Sum.inl y) * (Real.sqrt n * (muHat u0 n ω y - muR R y)) -
      ∑ y, t (Sum.inl y) / w y * Xm R y n ω =
      ∑ y, (t (Sum.inl y) * ((Dv n ω y - 1 / w y) * Xm R y n ω) +
        t (Sum.inl y) * (Dv n ω y * Bd R y n ω)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mu_scaled u0 R n ω y (hv y)]
    unfold Dv Xm Bd
    ring
  have h2 : ∑ q : (S × A) × S, t (Sum.inr q) * (Real.sqrt n * (PHat p0 n ω q.1 q.2 - Pmat P q.1 q.2)) -
      ∑ q : (S × A) × S, t (Sum.inr q) / w q.1 * Xp P q n ω =
      ∑ q : (S × A) × S, t (Sum.inr q) * ((Dv n ω q.1 - 1 / w q.1) * Xp P q n ω) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [P_scaled P p0 n ω q.1 q.2 (hv q.1)]
    unfold Dv Xp
    ring
  unfold Rem
  linarith

lemma Dv_meas (n : ℕ) (x : S × A) :
    Measurable (fun ω : ℕ → (S × A) × ℝ => Dv n ω x) :=
  measurable_const.div (visits_meas2 n x)

lemma Bd_meas (R : S × A → Measure ℝ) (y : S × A) (n : ℕ) :
    Measurable (fun ω : ℕ → (S × A) × ℝ => Bd R y n ω) :=
  measurable_const.mul (((gx_meas R y).comp (measurable_pi_apply 0)).sub
    ((gx_meas R y).comp (measurable_pi_apply n)))

lemma Bd_tim (P : S × A → PMF S) (π : S → PMF A) (R : S × A → Measure ℝ)
    [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x)) (ν₀ : PMF S) (y : S × A) :
    TendstoInMeasure (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) => Bd R y n ω) atTop (fun _ => 0) := by
  have h0 : TendstoInMeasure (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) => (Real.sqrt n)⁻¹ * gx R y (ω 0)) atTop
      (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) (Filter.Eventually.of_forall fun ω => ?_)
    · exact (measurable_const.mul ((gx_meas R y).comp (measurable_pi_apply 0))).aestronglyMeasurable
    · have := (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
        tendsto_natCast_atTop_atTop).mul_const (gx R y (ω 0))
      simpa using this
  have hn : TendstoInMeasure (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) => -((Real.sqrt n)⁻¹ * gx R y (ω n))) atTop
      (fun _ => 0) := by
    intro ε hε
    have := bnd_tim P π R hR ν₀ y ε hε
    simpa [edist_dist, Real.dist_eq] using this
  have e : (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) => Bd R y n ω) =
      fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (Real.sqrt n)⁻¹ * gx R y (ω 0) + -((Real.sqrt n)⁻¹ * gx R y (ω n)) := by
    funext n ω
    unfold Bd
    ring
  rw [e]
  exact tim_add h0 hn

lemma Rem_tim (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (ν₀ : PMF S)
    (t : (S × A) ⊕ ((S × A) × S) → ℝ) :
    TendstoInMeasure (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) => Rem P R w t n ω) atTop (fun _ => 0) := by
  have hw_nonneg : ∀ x, 0 ≤ w x := fun x => (hw_pos x).le
  unfold Rem
  refine tim_add (tim_sum Finset.univ _ fun y _ => tim_add ?_ ?_)
    (tim_sum Finset.univ _ fun q _ => ?_)
  · exact tim_of_slutsky (fun n ω => Xm R y n ω) (fun n ω => Dv n ω y) id (1 / w y)
      (fun p => t (Sum.inl y) * ((p.2 - 1 / w y) * p.1)) (by fun_prop)
      (comp_clt_inl P π R hR hirr w hw_nonneg hw_sum hw_stat ν₀ y)
      (Dn_tim P π R ν₀ hirr w hw_pos hw_sum hw_stat y)
      (fun n => (Dv_meas n y).aemeasurable) (fun x => by simp)
  · have hD := Dn_tim P π R ν₀ hirr w hw_pos hw_sum hw_stat y
    have hDd : TendstoInDistribution (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) => Dv n ω y) atTop
        (fun _ => 1 / w y) (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
        (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) :=
      TendstoInMeasure.tendstoInDistribution hD (fun n => (Dv_meas n y).aemeasurable)
    exact tim_of_slutsky (fun n ω => Dv n ω y) (fun n ω => Bd R y n ω) (fun _ => 1 / w y) 0
      (fun p => t (Sum.inl y) * (p.1 * p.2)) (by fun_prop) hDd
      (Bd_tim P π R hR ν₀ y) (fun n => (Bd_meas R y n).aemeasurable) (fun x => by simp)
  · exact tim_of_slutsky (fun n ω => Xp P q n ω) (fun n ω => Dv n ω q.1) id (1 / w q.1)
      (fun p => t (Sum.inr q) * ((p.2 - 1 / w q.1) * p.1)) (by fun_prop)
      (comp_clt_inr P π R hirr w hw_nonneg hw_sum hw_stat ν₀ q.1 q.2)
      (Dn_tim P π R ν₀ hirr w hw_pos hw_sum hw_stat q.1)
      (fun n => (Dv_meas n q.1).aemeasurable) (fun x => by simp)

theorem C2_of_pos (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (u0 : S × A → ℝ) (p0 : S × A → S → ℝ)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (ν₀ : PMF S) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (WithLp.toLp 2 (fun i => Real.sqrt n * (thetaHat u0 p0 n ω i - theta R P i)) :
          EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S))))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (multivariateGaussian 0 (SigmaRP (Pmat P) (sigma2R R) w)) := by
  have hw_nonneg : ∀ x, 0 ≤ w x := fun x => (hw_pos x).le
  have hY : ∀ n : ℕ, Measurable (fun ω : ℕ → (S × A) × ℝ =>
      (WithLp.toLp 2 (fun i => Real.sqrt n * (thetaHat u0 p0 n ω i - theta R P i)) :
        EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)))) := fun n =>
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i =>
      measurable_const.mul (((measurable_pi_apply i).comp (thetaHat_meas u0 p0 n)).sub
        measurable_const))
  have hXm : ∀ y (n : ℕ), AEMeasurable (fun ω => Xm R y n ω)
      (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) := fun y n =>
    (comp_clt_inl P π R hR hirr w hw_nonneg hw_sum hw_stat ν₀ y).forall_aemeasurable n
  have hXp : ∀ (q : (S × A) × S) (n : ℕ), AEMeasurable (fun ω => Xp P q n ω)
      (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) := fun q n =>
    (comp_clt_inr P π R hirr w hw_nonneg hw_sum hw_stat ν₀ q.1 q.2).forall_aemeasurable n
  refine C7_cramerWold _ _ (fun n => (hY n).aemeasurable) _
    (SigmaRP_posSemidef (Pmat P) (sigma2R R) w (Pmat_nonneg P) (Pmat_sum P)
      (fun x => by rw [sigma2R_eq_Vx]; exact Vx_nonneg R x) hw_pos) (fun t => ?_)
  have hU := dir_clt P π R hR hirr w hw_pos hw_sum hw_stat ν₀ t
  have hRm : ∀ n : ℕ, AEMeasurable (fun ω => Rem P R w t n ω)
      (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) := by
    intro n
    unfold Rem
    refine AEMeasurable.add (Finset.aemeasurable_fun_sum Finset.univ fun y _ => ?_)
      (Finset.aemeasurable_fun_sum Finset.univ fun q _ => ?_)
    · exact (aemeasurable_const.mul (((Dv_meas n y).aemeasurable.sub aemeasurable_const).mul
        (hXm y n))).add
        (aemeasurable_const.mul ((Dv_meas n y).aemeasurable.mul (Bd_meas R y n).aemeasurable))
    · exact aemeasurable_const.mul (((Dv_meas n q.1).aemeasurable.sub aemeasurable_const).mul
        (hXp q n))
  have hYin : ∀ n : ℕ, AEMeasurable (fun ω : ℕ → (S × A) × ℝ => inner ℝ t
      ((WithLp.toLp 2 (fun i => Real.sqrt n * (thetaHat u0 p0 n ω i - theta R P i)) :
        EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)))))
      (MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)) := fun n =>
    ((continuous_const.inner continuous_id).measurable.comp (hY n)).aemeasurable
  have hev : ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      ∀ᶠ n : ℕ in atTop, inner ℝ t
        ((WithLp.toLp 2 (fun i => Real.sqrt n * (thetaHat u0 p0 n ω i - theta R P i)) :
          EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)))) -
        (Real.sqrt n)⁻¹ * ∑ s ∈ Finset.range n, Hc P R (cw w t) (ω s).1 (ω (s + 1)) =
        Rem P R w t n ω := by
    filter_upwards [visits_ae P π R ν₀ hirr w hw_sum hw_stat] with ω hω
    have hx : ∀ x, ∀ᶠ n in atTop, 0 < visits n ω x := fun x => by
      filter_upwards [(tendsto_pi_nhds.1 hω x).eventually (lt_mem_nhds (hw_pos x))] with n hn
      rcases Nat.eq_zero_or_pos (visits n ω x) with h0 | h0
      · simp [h0] at hn
      · exact h0
    filter_upwards [Filter.eventually_all.2 hx] with n hn
    exact alg_rem P R u0 p0 w t n ω hn
  have h1 := tim_of_ae_eventually_eq _ _
    (fun n => ((hYin n).sub (hU.forall_aemeasurable n)).aestronglyMeasurable)
    (fun n => (hRm n).aestronglyMeasurable) hev
  have h3 := tim_add h1 (Rem_tim P π R hR hirr w hw_pos hw_sum hw_stat ν₀ t)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hU ?_ (fun n => hYin n)
  exact TendstoInMeasure.congr_left (fun n => Filter.Eventually.of_forall fun ω => by simp) h3

end C2fin

end QVCLT40192638


open MeasureTheory ProbabilityTheory Filter Matrix Topology

namespace QVCLT40192638

open RLInference.QValueCLT

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

section C3
set_option linter.unusedSectionVars false

lemma iSup_le_iSup_add [Nonempty A] (f g : A → ℝ) (c : ℝ) (h : ∀ a, f a ≤ g a + c) :
    ⨆ a, f a ≤ (⨆ a, g a) + c :=
  ciSup_le fun a => by
    have := le_ciSup (Set.finite_range g).bddAbove a
    linarith [h a]

lemma abs_iSup_sub_le [Nonempty A] (f g : A → ℝ) (c : ℝ) (h : ∀ a, |f a - g a| ≤ c) :
    |(⨆ a, f a) - ⨆ a, g a| ≤ c := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [iSup_le_iSup_add f g c fun a => by linarith [(abs_sub_le_iff.1 (h a)).1]]
  · linarith [iSup_le_iSup_add g f c fun a => by linarith [(abs_sub_le_iff.1 (h a)).2]]

/-- The Bellman operator is `γB`-Lipschitz in sup norm when every row of `|P'|` sums to `≤ B`. -/
lemma bellman_dist [Nonempty A] (γ : ℝ) (hγ0 : 0 ≤ γ) (r : S × A → ℝ) (P' : S × A → S → ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, ∑ k, |P' x k| ≤ B) (Q Q' : S × A → ℝ) :
    dist (bellman γ r P' Q) (bellman γ r P' Q') ≤ γ * B * dist Q Q' := by
  refine (dist_pi_le_iff (by positivity)).2 fun x => ?_
  rw [Real.dist_eq]
  simp only [bellman]
  have hk : ∀ k, |(⨆ a, Q (k, a)) - ⨆ a, Q' (k, a)| ≤ dist Q Q' := fun k =>
    abs_iSup_sub_le _ _ _ fun a => by rw [← Real.dist_eq]; exact dist_le_pi_dist Q Q' (k, a)
  have e : r x + γ * ∑ k, P' x k * (⨆ a, Q (k, a)) - (r x + γ * ∑ k, P' x k * ⨆ a, Q' (k, a)) =
      γ * ∑ k, P' x k * ((⨆ a, Q (k, a)) - ⨆ a, Q' (k, a)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e, abs_mul, abs_of_nonneg hγ0, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hγ0
  calc |∑ k, P' x k * ((⨆ a, Q (k, a)) - ⨆ a, Q' (k, a))|
      ≤ ∑ k, |P' x k| * |(⨆ a, Q (k, a)) - ⨆ a, Q' (k, a)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
    _ ≤ ∑ k, |P' x k| * dist Q Q' :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (abs_nonneg _)
    _ = (∑ k, |P' x k|) * dist Q Q' := by rw [Finset.sum_mul]
    _ ≤ B * dist Q Q' := mul_le_mul_of_nonneg_right (hB x) dist_nonneg

lemma bellman_contracting [Nonempty A] (γ : ℝ) (hγ0 : 0 ≤ γ) (r : S × A → ℝ)
    (P' : S × A → S → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, ∑ k, |P' x k| ≤ B)
    (hκ : γ * B < 1) : ContractingWith (Real.toNNReal (γ * B)) (bellman γ r P') := by
  refine ⟨Real.toNNReal_lt_one.2 hκ, LipschitzWith.of_dist_le_mul fun Q Q' => ?_⟩
  rw [Real.coe_toNNReal _ (by positivity)]
  exact bellman_dist γ hγ0 r P' B hB0 hB Q Q'

/-- Under a contraction bound, value iteration converges to `bellmanFix`, a fixed point. -/
lemma bellmanFix_spec [Nonempty A] (γ : ℝ) (hγ0 : 0 ≤ γ) (r : S × A → ℝ)
    (P' : S × A → S → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, ∑ k, |P' x k| ≤ B)
    (hκ : γ * B < 1) :
    Tendsto (fun m : ℕ => (bellman γ r P')^[m] 0) atTop (𝓝 (bellmanFix γ r P')) ∧
      bellman γ r P' (bellmanFix γ r P') = bellmanFix γ r P' := by
  have hK := bellman_contracting γ hγ0 r P' B hB0 hB hκ
  have ht := hK.tendsto_iterate_fixedPoint 0
  have hfix : bellmanFix γ r P' = ContractingWith.fixedPoint _ hK := ht.limUnder_eq
  rw [hfix]
  exact ⟨ht, hK.fixedPoint_isFixedPt⟩

/-- Uniqueness: any Bellman fixed point equals `bellmanFix` under a contraction bound. -/
lemma eq_bellmanFix [Nonempty A] (γ : ℝ) (hγ0 : 0 ≤ γ) (r : S × A → ℝ)
    (P' : S × A → S → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, ∑ k, |P' x k| ≤ B)
    (hκ : γ * B < 1) (Q : S × A → ℝ) (hQ : bellman γ r P' Q = Q) : Q = bellmanFix γ r P' := by
  have hK := bellman_contracting γ hγ0 r P' B hB0 hB hκ
  have hfix : bellmanFix γ r P' = ContractingWith.fixedPoint _ hK :=
    (hK.tendsto_iterate_fixedPoint 0).limUnder_eq
  rw [hfix]
  exact hK.fixedPoint_unique hQ

lemma abs_vstar_le [Nonempty A] (Q : S × A → ℝ) (k : S) : |⨆ a, Q (k, a)| ≤ ‖Q‖ := by
  have := abs_iSup_sub_le (fun a => Q (k, a)) (fun _ => (0:ℝ)) ‖Q‖
    (fun a => by simpa [Real.norm_eq_abs] using norm_le_pi_norm Q (k, a))
  simpa using this

lemma rowsum_bound (P0 P' : S × A → S → ℝ) (hP00 : ∀ x k, 0 ≤ P0 x k)
    (hP01 : ∀ x, ∑ k, P0 x k = 1) (ε : ℝ) (hP : ∀ x k, |P' x k - P0 x k| ≤ ε) (x : S × A) :
    ∑ k, |P' x k| ≤ 1 + (Fintype.card S : ℝ) * ε := by
  calc ∑ k, |P' x k| ≤ ∑ k, (P0 x k + ε) := Finset.sum_le_sum fun k _ => by
          have := abs_sub_abs_le_abs_sub (P' x k) (P0 x k)
          rw [abs_of_nonneg (hP00 x k)] at this
          linarith [hP x k]
    _ = 1 + (Fintype.card S : ℝ) * ε := by
          rw [Finset.sum_add_distrib, hP01 x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma pert_bound [Nonempty A] (γ : ℝ) (hγ0 : 0 ≤ γ) (r0 r : S × A → ℝ) (P0 P' : S × A → S → ℝ)
    (hP00 : ∀ x k, 0 ≤ P0 x k) (hP01 : ∀ x, ∑ k, P0 x k = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hr : ∀ x, |r x - r0 x| ≤ ε) (hP : ∀ x k, |P' x k - P0 x k| ≤ ε)
    (Q0 Q : S × A → ℝ) (hQ0 : bellman γ r0 P0 Q0 = Q0) (hQ : bellman γ r P' Q = Q) :
    dist Q Q0 ≤ γ * (1 + (Fintype.card S : ℝ) * ε) * dist Q Q0 +
      (ε + γ * ((Fintype.card S : ℝ) * ε) * ‖Q0‖) := by
  have hB := rowsum_bound P0 P' hP00 hP01 ε hP
  have h1 := bellman_dist γ hγ0 r P' _ (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hε))
    hB Q Q0
  have h2 : dist (bellman γ r P' Q0) (bellman γ r0 P0 Q0) ≤
      ε + γ * ((Fintype.card S : ℝ) * ε) * ‖Q0‖ := by
    refine (dist_pi_le_iff (add_nonneg hε (mul_nonneg (mul_nonneg hγ0
      (mul_nonneg (Nat.cast_nonneg _) hε)) (norm_nonneg _)))).2 fun x => ?_
    rw [Real.dist_eq]
    simp only [bellman]
    have e : r x + γ * ∑ k, P' x k * (⨆ a, Q0 (k, a)) - (r0 x + γ * ∑ k, P0 x k * ⨆ a, Q0 (k, a)) =
        (r x - r0 x) + γ * ∑ k, (P' x k - P0 x k) * (⨆ a, Q0 (k, a)) := by
      simp only [sub_mul, Finset.sum_sub_distrib]; ring
    rw [e]
    have hs : |∑ k, (P' x k - P0 x k) * (⨆ a, Q0 (k, a))| ≤ (Fintype.card S : ℝ) * ε * ‖Q0‖ := by
      calc _ ≤ ∑ k, |(P' x k - P0 x k) * (⨆ a, Q0 (k, a))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : S, ε * ‖Q0‖ := Finset.sum_le_sum fun k _ => by
            rw [abs_mul]; exact mul_le_mul (hP x k) (abs_vstar_le Q0 k) (abs_nonneg _) hε
        _ = (Fintype.card S : ℝ) * ε * ‖Q0‖ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    calc |(r x - r0 x) + γ * ∑ k, (P' x k - P0 x k) * (⨆ a, Q0 (k, a))|
        ≤ |r x - r0 x| + |γ * ∑ k, (P' x k - P0 x k) * (⨆ a, Q0 (k, a))| := abs_add_le _ _
      _ ≤ ε + γ * ((Fintype.card S : ℝ) * ε * ‖Q0‖) := by
          rw [abs_mul, abs_of_nonneg hγ0]
          exact add_le_add (hr x) (mul_le_mul_of_nonneg_left hs hγ0)
      _ = _ := by ring
  calc dist Q Q0 = dist (bellman γ r P' Q) (bellman γ r0 P0 Q0) := by rw [hQ, hQ0]
    _ ≤ dist (bellman γ r P' Q) (bellman γ r P' Q0) +
          dist (bellman γ r P' Q0) (bellman γ r0 P0 Q0) := dist_triangle _ _ _
    _ ≤ _ := add_le_add h1 h2

lemma iSup_eq_greedy [Nonempty A] (Q : S × A → ℝ) (aStar : S → A)
    (h : ∀ (s : S) (a : A), a ≠ aStar s → Q (s, a) < Q (s, aStar s)) (k : S) :
    ⨆ a, Q (k, a) = Q (k, aStar k) :=
  le_antisymm (ciSup_le fun a => by
      by_cases ha : a = aStar k
      · exact le_of_eq (by rw [ha])
      · exact (h k a ha).le)
    (le_ciSup (f := fun a => Q (k, a)) (Set.finite_range _).bddAbove (aStar k))

lemma key_identity (γ : ℝ) (r0 r : S × A → ℝ) (P0 P' : S × A → S → ℝ) (Q0 Q : S × A → ℝ)
    (V0 V : S → ℝ) (hQ0 : ∀ x, Q0 x = r0 x + γ * ∑ k, P0 x k * V0 k)
    (hQ : ∀ x, Q x = r x + γ * ∑ k, P' x k * V k) (x : S × A) :
    (Q x - Q0 x) - γ * ∑ k, P0 x k * (V k - V0 k) =
      (r x - r0 x) + γ * ∑ k, (P' x k - P0 x k) * V0 k +
        γ * ∑ k, (P' x k - P0 x k) * (V k - V0 k) := by
  rw [hQ x, hQ0 x]
  have e : ∑ k, P' x k * V k = ∑ k, P0 x k * V0 k + ∑ k, P0 x k * (V k - V0 k) +
      ∑ k, (P' x k - P0 x k) * V0 k + ∑ k, (P' x k - P0 x k) * (V k - V0 k) := by
    simp only [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]; ring

lemma ptildeStar_mulVec (P0 : S × A → S → ℝ) (aStar : S → A) (u : S × A → ℝ) (x : S × A) :
    (PtildeStar P0 aStar *ᵥ u) x = ∑ k, P0 x k * u (k, aStar k) := by
  simp [mulVec, dotProduct, PtildeStar, Fintype.sum_prod_type]

lemma M_mulVec (γ : ℝ) (P0 : S × A → S → ℝ) (aStar : S → A) (u : S × A → ℝ) (x : S × A) :
    ((1 - γ • PtildeStar P0 aStar) *ᵥ u) x = u x - γ * ∑ k, P0 x k * u (k, aStar k) := by
  rw [sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply, ptildeStar_mulVec,
    smul_eq_mul]

lemma blockV_mulVec (V : S → ℝ) (u : (S × A) × S → ℝ) (x : S × A) :
    (blockV V *ᵥ u) x = ∑ k, u (x, k) * V k := by
  simp only [mulVec, dotProduct, blockV, Matrix.of_apply, ite_mul, zero_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [mul_comm]

lemma M_isUnit (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (P0 : S × A → S → ℝ)
    (hP00 : ∀ x k, 0 ≤ P0 x k) (hP01 : ∀ x, ∑ k, P0 x k = 1) (aStar : S → A) :
    IsUnit (1 - γ • PtildeStar P0 aStar).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have hz : (1 - γ • PtildeStar P0 aStar) *ᵥ (v - w) = 0 := by
    rw [mulVec_sub, hvw, sub_self]
  have hzx : ∀ x, (v - w) x = γ * ∑ k, P0 x k * (v - w) (k, aStar k) := fun x => by
    have := congrFun hz x
    rw [M_mulVec, Pi.zero_apply] at this
    linarith
  have hn : ‖v - w‖ ≤ γ * ‖v - w‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hγ0 (norm_nonneg _))).2 fun x => ?_
    rw [hzx x, Real.norm_eq_abs, abs_mul, abs_of_nonneg hγ0]
    refine mul_le_mul_of_nonneg_left ?_ hγ0
    calc |∑ k, P0 x k * (v - w) (k, aStar k)| ≤ ∑ k, P0 x k * ‖v - w‖ :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
            rw [abs_mul, abs_of_nonneg (hP00 x k)]
            exact mul_le_mul_of_nonneg_left
              (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (v - w) (k, aStar k)) (hP00 x k))
      _ = ‖v - w‖ := by rw [← Finset.sum_mul, hP01 x, one_mul]
  have h0 : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

/-- The Bellman fixed point as a function of the packed parameter (sup-norm space). -/
noncomputable def gfun (γ : ℝ) (v : (S × A) ⊕ ((S × A) × S) → ℝ) : S × A → ℝ :=
  bellmanFix γ (fun x => v (Sum.inl x)) (fun x k => v (Sum.inr (x, k)))

set_option maxHeartbeats 1000000 in
lemma g_hasFDerivAt [Nonempty A] (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r0 : S × A → ℝ)
    (P0 : S × A → S → ℝ) (hP00 : ∀ x k, 0 ≤ P0 x k) (hP01 : ∀ x, ∑ k, P0 x k = 1)
    (aStar : S → A)
    (hAstar : ∀ (s : S) (a : A), a ≠ aStar s →
      bellmanFix γ r0 P0 (s, a) < bellmanFix γ r0 P0 (s, aStar s)) :
    HasFDerivAt (gfun (S := S) (A := A) γ)
      (LinearMap.toContinuousLinearMap
        (Matrix.mulVecLin (gradPhi γ P0 aStar (Vstar (bellmanFix γ r0 P0)))))
      (Sum.elim r0 (fun q => P0 q.1 q.2)) := by
  set v0 : (S × A) ⊕ ((S × A) × S) → ℝ := Sum.elim r0 (fun q => P0 q.1 q.2) with hv0
  set Q0 := bellmanFix γ r0 P0 with hQ0def
  have hB0 : ∀ x, ∑ k, |P0 x k| ≤ 1 := fun x => by simp [abs_of_nonneg (hP00 x _), hP01 x]
  have hQ0 : bellman γ r0 P0 Q0 = Q0 :=
    (bellmanFix_spec γ hγ0 r0 P0 1 zero_le_one hB0 (by simpa using hγ1)).2
  obtain ⟨ε0, hε0pos, hε0⟩ : ∃ ε0 : ℝ, 0 < ε0 ∧ (Fintype.card S : ℝ) * ε0 ≤ (1 - γ) / 2 :=
    ⟨(1 - γ) / (2 * ((Fintype.card S : ℝ) + 1)), div_pos (by linarith) (by positivity), by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith⟩
  have hloc : ∀ h : (S × A) ⊕ ((S × A) × S) → ℝ, ‖h‖ ≤ ε0 →
      bellman γ (fun x => (v0 + h) (Sum.inl x)) (fun x k => (v0 + h) (Sum.inr (x, k)))
        (gfun γ (v0 + h)) = gfun γ (v0 + h) ∧
      dist (gfun γ (v0 + h)) Q0 ≤ 2 * (1 + γ * (Fintype.card S : ℝ) * ‖Q0‖) / (1 - γ) * ‖h‖ := by
    intro h hh
    have hn : 0 ≤ ‖h‖ := norm_nonneg h
    have hr : ∀ x, |(v0 + h) (Sum.inl x) - r0 x| ≤ ‖h‖ := fun x => by
      simpa [hv0, Real.norm_eq_abs] using norm_le_pi_norm h (Sum.inl x)
    have hP : ∀ x k, |(v0 + h) (Sum.inr (x, k)) - P0 x k| ≤ ‖h‖ := fun x k => by
      simpa [hv0, Real.norm_eq_abs] using norm_le_pi_norm h (Sum.inr (x, k))
    have a1 : γ * ((Fintype.card S : ℝ) * ‖h‖) ≤ (Fintype.card S : ℝ) * ‖h‖ :=
      mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) hn) hγ1.le
    have a2 : (Fintype.card S : ℝ) * ‖h‖ ≤ (Fintype.card S : ℝ) * ε0 :=
      mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
    have hsmall : γ * (1 + (Fintype.card S : ℝ) * ‖h‖) ≤ (1 + γ) / 2 := by
      have : γ * (1 + (Fintype.card S : ℝ) * ‖h‖) = γ + γ * ((Fintype.card S : ℝ) * ‖h‖) := by
        ring
      linarith
    have hfix := (bellmanFix_spec γ hγ0 (fun x => (v0 + h) (Sum.inl x))
      (fun x k => (v0 + h) (Sum.inr (x, k))) (1 + (Fintype.card S : ℝ) * ‖h‖)
      (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hn))
      (rowsum_bound P0 _ hP00 hP01 ‖h‖ hP) (by linarith)).2
    refine ⟨hfix, ?_⟩
    have hd' := pert_bound γ hγ0 r0 _ P0 _ hP00 hP01 ‖h‖ hn hr hP Q0 (gfun γ (v0 + h)) hQ0 hfix
    have hm := mul_le_mul_of_nonneg_right hsmall (dist_nonneg (x := gfun γ (v0 + h)) (y := Q0))
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith [hd', hm]
  have hev : ∀ᶠ h in 𝓝 (0 : (S × A) ⊕ ((S × A) × S) → ℝ), ‖h‖ ≤ ε0 := by
    have ht : Tendsto (fun h : (S × A) ⊕ ((S × A) × S) → ℝ => ‖h‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : (S × A) ⊕ ((S × A) × S) → ℝ))
    exact ht (Iic_mem_nhds hε0pos)
  have hT : Tendsto (fun h => gfun γ (v0 + h)) (𝓝 0) (𝓝 Q0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
      (hev.mono fun h hh => (hloc h hh).2) ?_
    simpa using (continuous_norm.tendsto (0 : (S × A) ⊕ ((S × A) × S) → ℝ)).const_mul
      (2 * (1 + γ * (Fintype.card S : ℝ) * ‖Q0‖) / (1 - γ))
  have hgreedy : ∀ᶠ h in 𝓝 (0 : (S × A) ⊕ ((S × A) × S) → ℝ), ∀ s : S, ∀ a : A, a ≠ aStar s →
      gfun γ (v0 + h) (s, a) < gfun γ (v0 + h) (s, aStar s) := by
    refine Filter.eventually_all.2 fun s => Filter.eventually_all.2 fun a => ?_
    by_cases ha : a = aStar s
    · exact Eventually.of_forall fun _ hne => absurd ha hne
    · have h1 : Tendsto (fun h => gfun γ (v0 + h) (s, aStar s) - gfun γ (v0 + h) (s, a)) (𝓝 0)
          (𝓝 (Q0 (s, aStar s) - Q0 (s, a))) :=
        (((continuous_apply (s, aStar s)).tendsto Q0).comp hT).sub
          (((continuous_apply (s, a)).tendsto Q0).comp hT)
      have h2 : 0 < Q0 (s, aStar s) - Q0 (s, a) := sub_pos.2 (hAstar s a ha)
      have h3 : ∀ᶠ h in 𝓝 (0 : (S × A) ⊕ ((S × A) × S) → ℝ),
          0 < gfun γ (v0 + h) (s, aStar s) - gfun γ (v0 + h) (s, a) := h1 (Ioi_mem_nhds h2)
      exact h3.mono fun h hh _ => sub_pos.1 hh
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  set Mm : Matrix (S × A) (S × A) ℝ := 1 - γ • PtildeStar P0 aStar with hMm
  have hunit : IsUnit Mm.det := M_isUnit γ hγ0 hγ1 P0 hP00 hP01 aStar
  set C : ℝ := ‖LinearMap.toContinuousLinearMap (Matrix.mulVecLin Mm⁻¹)‖ with hC
  set K : ℝ := 2 * (1 + γ * (Fintype.card S : ℝ) * ‖Q0‖) / (1 - γ) with hK
  have hO : (fun h => gfun γ (v0 + h) - gfun γ v0 -
      (LinearMap.toContinuousLinearMap
        (Matrix.mulVecLin (gradPhi γ P0 aStar (Vstar Q0)))) h) =O[𝓝 0]
      (fun h : (S × A) ⊕ ((S × A) × S) → ℝ => ‖h‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound (C * γ * (Fintype.card S : ℝ) * K) ?_
    filter_upwards [hev, hgreedy] with h hh hg
    obtain ⟨hfix, hdist⟩ := hloc h hh
    set Q := gfun γ (v0 + h) with hQdef
    have hV : ∀ k, ⨆ a, Q (k, a) = Q (k, aStar k) := iSup_eq_greedy Q aStar hg
    have hV0 : ∀ k, ⨆ a, Q0 (k, a) = Q0 (k, aStar k) := iSup_eq_greedy Q0 aStar hAstar
    have hid : ∀ x, (Q - Q0) x - γ * ∑ k, P0 x k * (Q - Q0) (k, aStar k) =
        h (Sum.inl x) + γ * ∑ k, h (Sum.inr (x, k)) * Q0 (k, aStar k) +
          γ * ∑ k, h (Sum.inr (x, k)) * (Q - Q0) (k, aStar k) := by
      intro x
      have := key_identity γ r0 (fun x => (v0 + h) (Sum.inl x)) P0
        (fun x k => (v0 + h) (Sum.inr (x, k))) Q0 Q
        (fun k => Q0 (k, aStar k)) (fun k => Q (k, aStar k))
        (fun x => by have := congrFun hQ0 x; simp only [bellman, hV0] at this; exact this.symm)
        (fun x => by have := congrFun hfix x; simp only [bellman, hV] at this; exact this.symm) x
      simpa [hv0] using this
    set d := Q - Q0 with hd
    set u : S × A → ℝ := fun x => γ * ∑ k, h (Sum.inr (x, k)) * d (k, aStar k) with hu
    set L : S × A → ℝ := (fun x => h (Sum.inl x)) +
      γ • (blockV (Vstar Q0) *ᵥ (fun q => h (Sum.inr q))) with hL
    have hMd : Mm *ᵥ d = L + u := by
      ext x
      rw [hMm, M_mulVec, hid x]
      simp only [hL, hu, Pi.add_apply, Pi.smul_apply, smul_eq_mul, blockV_mulVec, Vstar, hV0]
    have hG : gradPhi γ P0 aStar (Vstar Q0) *ᵥ h = Mm⁻¹ *ᵥ L := by
      rw [gradPhi, ← mulVec_mulVec, fromCols_mulVec, one_mulVec, smul_mulVec]
      rfl
    have e1 : Mm⁻¹ *ᵥ (Mm *ᵥ d) = d := by
      rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
    have hdeq : d - gradPhi γ P0 aStar (Vstar Q0) *ᵥ h = Mm⁻¹ *ᵥ u := by
      calc d - gradPhi γ P0 aStar (Vstar Q0) *ᵥ h
          = Mm⁻¹ *ᵥ (Mm *ᵥ d) - gradPhi γ P0 aStar (Vstar Q0) *ᵥ h := by rw [e1]
        _ = Mm⁻¹ *ᵥ u := by rw [hMd, hG, mulVec_add, add_sub_cancel_left]
    have hdn : ‖d‖ ≤ K * ‖h‖ := by rw [hd, ← dist_eq_norm]; exact hdist
    have hun : ‖u‖ ≤ γ * (Fintype.card S : ℝ) * (‖h‖ * ‖d‖) := by
      refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hγ0 (Nat.cast_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 fun x => ?_
      rw [hu, Real.norm_eq_abs, abs_mul, abs_of_nonneg hγ0, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hγ0
      calc |∑ k, h (Sum.inr (x, k)) * d (k, aStar k)| ≤ ∑ k : S, ‖h‖ * ‖d‖ :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
              rw [abs_mul]
              exact mul_le_mul
                (by simpa [Real.norm_eq_abs] using norm_le_pi_norm h (Sum.inr (x, k)))
                (by simpa [Real.norm_eq_abs] using norm_le_pi_norm d (k, aStar k))
                (abs_nonneg _) (norm_nonneg _))
        _ = (Fintype.card S : ℝ) * (‖h‖ * ‖d‖) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hg0 : gfun γ v0 = Q0 := rfl
    have hGl : (LinearMap.toContinuousLinearMap
        (Matrix.mulVecLin (gradPhi γ P0 aStar (Vstar Q0)))) h =
          gradPhi γ P0 aStar (Vstar Q0) *ᵥ h := rfl
    rw [hg0, hGl, ← hd, hdeq, Real.norm_of_nonneg (by positivity)]
    have hCb : ‖Mm⁻¹ *ᵥ u‖ ≤ C * ‖u‖ :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Mm⁻¹)).le_opNorm u
    have hC0 : 0 ≤ C := norm_nonneg _
    have hγN : 0 ≤ γ * (Fintype.card S : ℝ) := mul_nonneg hγ0 (Nat.cast_nonneg _)
    calc ‖Mm⁻¹ *ᵥ u‖ ≤ C * ‖u‖ := hCb
      _ ≤ C * (γ * (Fintype.card S : ℝ) * (‖h‖ * (K * ‖h‖))) :=
          mul_le_mul_of_nonneg_left (hun.trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hdn (norm_nonneg h)) hγN)) hC0
      _ = C * γ * (Fintype.card S : ℝ) * K * ‖h‖ ^ 2 := by ring
  exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

theorem C3_bellmanFix_hasFDerivAt [Nonempty A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : S × A → ℝ) (P' : S × A → S → ℝ)
    (hP'0 : ∀ x k, 0 ≤ P' x k) (hP'1 : ∀ x, ∑ k, P' x k = 1) (aStar : S → A)
    (hAstar : ∀ (s : S) (a : A), a ≠ aStar s →
      bellmanFix γ r P' (s, a) < bellmanFix γ r P' (s, aStar s)) :
    HasFDerivAt
      (fun θ : EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)) =>
        (WithLp.toLp 2 (bellmanFix γ (fun x => θ (Sum.inl x)) (fun x k => θ (Sum.inr (x, k)))) :
          EuclideanSpace ℝ (S × A)))
      (LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (gradPhi γ P' aStar (Vstar (bellmanFix γ r P')))))
      (WithLp.toLp 2 (Sum.elim r (fun q => P' q.1 q.2))) := by
  have hg := g_hasFDerivAt γ hγ0 hγ1 r P' hP'0 hP'1 aStar hAstar
  have hc := (EuclideanSpace.equiv (S × A) ℝ).symm.hasFDerivAt.comp
    (WithLp.toLp 2 (Sum.elim r (fun q => P' q.1 q.2)) :
      EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)))
    (hg.comp (WithLp.toLp 2 (Sum.elim r (fun q => P' q.1 q.2)) :
      EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)))
      (EuclideanSpace.equiv ((S × A) ⊕ ((S × A) × S)) ℝ).hasFDerivAt)
  refine hc.congr_fderiv ?_
  ext θ i
  simp [Matrix.toEuclideanLin, Matrix.mulVecLin]
  rfl

end C3


/-- Summing against a row of `blockV V` picks out the block of `x`. -/
lemma sum_blockV (V : S → ℝ) (x : S × A) (f : (S × A) × S → ℝ) :
    ∑ q, blockV (A := A) V x q * f q = ∑ k, V k * f (x, k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp [blockV]
  · intro z _ hz
    simp [blockV, Ne.symm hz]
  · simp

/-- Core block identity: `blockV V * D_P * blockVᵀ = W⁻¹ D_Q`. -/
lemma blockV_DP_blockVT (P' : S × A → S → ℝ) (V : S → ℝ) (w : S × A → ℝ) :
    blockV (A := A) V * DP P' w * (blockV (A := A) V)ᵀ =
      diagonal (fun x => (w x)⁻¹) * DQ P' V := by
  ext x y
  rw [mul_apply]
  have key : ∀ q', (blockV (A := A) V * DP P' w) x q' = ∑ k₁, V k₁ * DP P' w (x, k₁) q' :=
    fun q' => by rw [mul_apply]; exact sum_blockV V x (fun q => DP P' w q q')
  simp_rw [key, transpose_apply]
  have h2 : ∑ q', (∑ k₁, V k₁ * DP P' w (x, k₁) q') * blockV (A := A) V y q' =
      ∑ k₂, V k₂ * ∑ k₁, V k₁ * DP P' w (x, k₁) (y, k₂) := by
    rw [← sum_blockV V y (fun q' => ∑ k₁, V k₁ * DP P' w (x, k₁) q')]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [h2, diagonal_mul]
  simp only [DP, DQ, diagonal_apply]
  by_cases h : x = y
  · subst h
    simp only [if_true, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k₂ _ => Finset.sum_congr rfl (fun k₁ _ => ?_))
    rw [div_eq_mul_inv]
    ring
  · simp [h]

/-- The delta-method covariance `∇φ Σ_{R,P} ∇φᵀ` equals `Σ_Q` (App. A.1, (5)). -/
lemma gradPhi_SigmaRP (γ : ℝ) (P' : S × A → S → ℝ) (aStar : S → A) (V : S → ℝ)
    (sig2 w : S × A → ℝ) :
    gradPhi γ P' aStar V * SigmaRP P' sig2 w * (gradPhi γ P' aStar V)ᵀ =
      SigmaQ γ P' aStar V sig2 w := by
  unfold gradPhi SigmaRP SigmaQ
  rw [transpose_mul, transpose_fromCols]
  set M := (1 - γ • PtildeStar P' aStar)⁻¹
  have h1 : fromCols (1 : Matrix (S × A) (S × A) ℝ) (γ • blockV (A := A) V) *
      fromBlocks (diagonal fun x => sig2 x / w x) 0 0 (DP P' w) *
      fromRows (1 : Matrix (S × A) (S × A) ℝ)ᵀ (γ • blockV (A := A) V)ᵀ =
      diagonal (fun x => (w x)⁻¹) * (diagonal sig2 + γ ^ 2 • DQ P' V) := by
    rw [fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp only [Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add, transpose_one,
      Matrix.mul_one, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [blockV_DP_blockVT, mul_add, diagonal_mul_diagonal, Matrix.mul_smul, ← sq]
    congr 2
    ext x
    rw [div_eq_mul_inv, mul_comm]
  have h1' : ∀ N : Matrix (S × A) (S × A) ℝ,
      fromCols (1 : Matrix (S × A) (S × A) ℝ) (γ • blockV (A := A) V) *
        (fromBlocks (diagonal fun x => sig2 x / w x) 0 0 (DP P' w) *
          (fromRows (1 : Matrix (S × A) (S × A) ℝ)ᵀ (γ • blockV (A := A) V)ᵀ * N)) =
        diagonal (fun x => (w x)⁻¹) * ((diagonal sig2 + γ ^ 2 • DQ P' V) * N) := by
    intro N
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  simp only [Matrix.mul_assoc]
  rw [h1']


/-- `Σ_Q` is positive semidefinite (via `Σ_Q = ∇φ Σ_{R,P} ∇φᵀ`). -/
lemma SigmaQ_posSemidef (γ : ℝ) (P' : S × A → S → ℝ) (aStar : S → A) (V : S → ℝ)
    (sig2 w : S × A → ℝ) (h0 : ∀ x k, 0 ≤ P' x k) (h1 : ∀ x, ∑ k, P' x k = 1)
    (hs : ∀ x, 0 ≤ sig2 x) (hw : ∀ x, 0 < w x) :
    (SigmaQ γ P' aStar V sig2 w).PosSemidef := by
  rw [← gradPhi_SigmaRP]
  have := (SigmaRP_posSemidef P' sig2 w h0 h1 hs hw).mul_mul_conjTranspose_same
    (gradPhi γ P' aStar V)
  rwa [conjTranspose_eq_transpose_of_trivial] at this

section C4
open Complex

/-- Convergence in distribution to a constant gives convergence in measure. -/
lemma tendstoInMeasure_of_tendstoInDistribution_const {Ω Ω' E : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Y : ℕ → Ω → E} {Z : Ω' → E} (c : E)
    (h : TendstoInDistribution Y atTop Z (fun _ => μ) μ') (hZ : ∀ ω, Z ω = c) :
    TendstoInMeasure μ Y atTop (fun _ => c) := by
  intro ε hε
  set F : Set E := {y | ε ≤ edist y c} with hF
  have hFc : IsClosed F := isClosed_le continuous_const (continuous_id.edist continuous_const)
  have hlim : limsup (fun n => (μ.map (Y n)) F) atTop ≤ (μ'.map Z) F :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hFc
  have hZF : (μ'.map Z) F = 0 := by
    rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit hFc.measurableSet]
    have : Z ⁻¹' F = ∅ := by
      ext ω
      simp [hF, hZ ω, hε.ne']
    simp [this]
  have hmeas : ∀ n, μ {ω | ε ≤ edist (Y n ω) c} = (μ.map (Y n)) F := fun n => by
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hFc.measurableSet]
    rfl
  simp_rw [hmeas]
  rw [hZF] at hlim
  exact tendsto_of_le_liminf_of_limsup_le (by simp) hlim

/-- Replace the limit variable by one with the same law. -/
lemma tendstoInDistribution_congr_limit {Ω Ω' Ω'' E : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace Ω''] [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {ν : Measure Ω''} [IsProbabilityMeasure ν]
    {Y : ℕ → Ω → E} {Z : Ω' → E} {W : Ω'' → E}
    (h : TendstoInDistribution Y atTop Z (fun _ => μ) μ') (hW : AEMeasurable W ν)
    (he : μ'.map Z = ν.map W) :
    TendstoInDistribution Y atTop W (fun _ => μ) ν where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hW
  tendsto := by
    have e : (⟨ν.map W, Measure.isProbabilityMeasure_map hW⟩ : ProbabilityMeasure E) =
        ⟨μ'.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩ := Subtype.ext he.symm
    rw [e]
    exact h.tendsto

/-- Linear image of a centred multivariate Gaussian. -/
lemma multivariateGaussian_map_toEuclideanLin {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (Sig : Matrix ι ι ℝ) (hSig : Sig.PosSemidef) (G : Matrix κ ι ℝ) :
    (multivariateGaussian 0 Sig).map (Matrix.toEuclideanLin G) =
      multivariateGaussian 0 (G * Sig * Gᵀ) := by
  have hPSD : (G * Sig * Gᵀ).PosSemidef := by
    have := hSig.mul_mul_conjTranspose_same G
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hc : Continuous (Matrix.toEuclideanLin G) := LinearMap.continuous_of_finiteDimensional _
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, integral_map hc.measurable.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop)), charFun_multivariateGaussian hPSD]
  have hin : ∀ x : EuclideanSpace ℝ ι, inner ℝ (Matrix.toEuclideanLin G x) t =
      inner ℝ x (Matrix.toEuclideanLin Gᵀ t) := by
    intro x
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply,
      star_trivial]
    rw [mulVec_transpose, dotProduct_mulVec]
  simp_rw [hin, ← charFun_apply, charFun_multivariateGaussian hSig]
  congr 2
  · simp
  · simp only [Matrix.toEuclideanLin_apply]
    have e : t.ofLp ⬝ᵥ (G * Sig * Gᵀ) *ᵥ t.ofLp = (t.ofLp ᵥ* G) ⬝ᵥ Sig *ᵥ (t.ofLp ᵥ* G) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
    rw [e, mulVec_transpose]

/-- Step (a): a root-n CLT forces consistency. -/
lemma tendstoInMeasure_sub_of_clt {ι Ω Ω' : Type} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Zl : Ω' → EuclideanSpace ℝ ι}
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (θ : EuclideanSpace ℝ ι)
    (h : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (X n ω - θ)) atTop Zl
      (fun _ => μ) μ') :
    TendstoInMeasure μ (fun n ω => X n ω - θ) atTop (fun _ => 0) := by
  have hc : TendstoInMeasure μ (fun (n : ℕ) (_ : Ω) => (Real.sqrt n)⁻¹) atTop
      (fun _ => (0 : ℝ)) := by
    have ht : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => ht)
  have ha1 := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : EuclideanSpace ℝ ι × ℝ => p.2 • p.1) (by fun_prop) hc
    (fun _ => aemeasurable_const)
  have ha2 := tendstoInMeasure_of_tendstoInDistribution_const (0 : EuclideanSpace ℝ ι) ha1
    (fun ω => by simp)
  intro ε hε
  refine (ha2 ε hε).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- Step (b): a function tending to `0` at `θ`, composed with a consistent sequence. -/
lemma tendstoInMeasure_comp_of_tendsto {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} (Y : ℕ → Ω → EuclideanSpace ℝ ι) (θ : EuclideanSpace ℝ ι)
    (hY : TendstoInMeasure μ (fun n ω => Y n ω - θ) atTop (fun _ => 0))
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρ0 : Tendsto ρ (𝓝 θ) (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => ρ (Y n ω)) atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδρ⟩ := Metric.tendsto_nhds_nhds.1 hρ0 ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hY δ hδ)
    (fun _ => zero_le) (fun n => measure_mono ?_)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have h1 : dist (Y n ω) θ < δ := by rwa [dist_eq_norm, ← dist_zero_right]
  have h2 := hδρ h1
  linarith

/-- Step (c): exact norm of the scaled Taylor remainder. -/
lemma remainder_norm {ι κ : Type} [Fintype ι] [Fintype κ]
    (φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)
    (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (θ x : EuclideanSpace ℝ ι) (s : ℝ)
    (hs : 0 ≤ s) :
    ‖s • (φ x - φ θ) - L (s • (x - θ))‖ =
      (‖x - θ‖⁻¹ * ‖φ x - φ θ - L (x - θ)‖) * ‖s • (x - θ)‖ := by
  rw [map_smul, ← smul_sub, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  by_cases hx : x - θ = 0
  · have : x = θ := sub_eq_zero.1 hx
    simp [this]
  · have hn : ‖x - θ‖ ≠ 0 := norm_ne_zero_iff.2 hx
    field_simp

/-- Measurability of the Taylor ratio along `X n`. -/
lemma dm_rho_meas {ι κ Ω : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (θ : EuclideanSpace ℝ ι)
    (φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)
    (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (hX : ∀ n, AEMeasurable (X n) μ) (hφX : ∀ n, AEMeasurable (fun ω => φ (X n ω)) μ) (n : ℕ) :
    AEMeasurable (fun ω => ‖X n ω - θ‖⁻¹ * ‖φ (X n ω) - φ θ - L (X n ω - θ)‖) μ := by
  have h1 : AEMeasurable (fun ω => X n ω - θ) μ := (hX n).sub_const θ
  have h2 : AEMeasurable (fun ω => L (X n ω - θ)) μ :=
    L.continuous.measurable.comp_aemeasurable h1
  have h3 : AEMeasurable (fun ω => φ (X n ω) - φ θ - L (X n ω - θ)) μ :=
    ((hφX n).sub_const _).sub h2
  exact h1.norm.inv.mul h3.norm

/-- A sequence tending to `0` in measure times a tight (CLT) sequence tends to `0`. -/
lemma dm_hb {ι Ω Ω' : Type} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Zl : Ω' → EuclideanSpace ℝ ι}
    (V : ℕ → Ω → EuclideanSpace ℝ ι) (r : ℕ → Ω → ℝ)
    (h : TendstoInDistribution V atTop Zl (fun _ => μ) ν)
    (hr : TendstoInMeasure μ r atTop (fun _ => 0)) (hrm : ∀ n, AEMeasurable (r n) μ) :
    TendstoInMeasure μ (fun n ω => r n ω * ‖V n ω‖) atTop (fun _ => (0 : ℝ)) := by
  have hb1 := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : EuclideanSpace ℝ ι × ℝ => p.2 * ‖p.1‖) (by fun_prop) hr hrm
  exact tendstoInMeasure_of_tendstoInDistribution_const (0 : ℝ) hb1 (fun ω => by simp)

/-- Transfer convergence to `0` in measure along equal distances to `0`. -/
lemma tendstoInMeasure_of_edist_eq {Ω E F : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (R : ℕ → Ω → E) (b : ℕ → Ω → F)
    (hk : ∀ n ω, edist (R n ω) 0 = edist (b n ω) 0)
    (hb : TendstoInMeasure μ b atTop (fun _ => 0)) :
    TendstoInMeasure μ R atTop (fun _ => 0) := by
  intro ε hε
  simp only [hk]
  exact hb ε hε

/-- Step (c'): the scaled Taylor remainder tends to `0` in measure. -/
lemma dm_hR0 {ι κ Ω : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (θ : EuclideanSpace ℝ ι)
    (φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)
    (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (hb : TendstoInMeasure μ (fun (n : ℕ) ω =>
      (‖X n ω - θ‖⁻¹ * ‖φ (X n ω) - φ θ - L (X n ω - θ)‖) *
        ‖Real.sqrt (n : ℝ) • (X n ω - θ)‖) atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure μ (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (φ (X n ω) - φ θ) -
      L (Real.sqrt (n : ℝ) • (X n ω - θ))) atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_edist_eq _ _ (fun n ω => ?_) hb
  rw [edist_dist, edist_dist, dist_zero_right, dist_zero_right,
    remainder_norm φ L θ (X n ω) _ (Real.sqrt_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- Slutsky tail of the delta method, with abstract sequences. -/
lemma dm_tail {ι κ Ω Ω' : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Zl : Ω' → EuclideanSpace ℝ ι}
    (V : ℕ → Ω → EuclideanSpace ℝ ι) (W : ℕ → Ω → EuclideanSpace ℝ κ)
    (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (h : TendstoInDistribution V atTop Zl (fun _ => μ) ν)
    (hR : TendstoInMeasure μ (fun n ω => W n ω - L (V n ω)) atTop (fun _ => 0))
    (hRm : ∀ n, AEMeasurable (fun ω => W n ω - L (V n ω)) μ) :
    TendstoInDistribution W atTop (fun ω => L (Zl ω)) (fun _ => μ) ν := by
  have hd := (h.continuous_comp L.continuous).add_of_tendstoInMeasure_const hR hRm
  have hd2 := tendstoInDistribution_congr_limit (W := fun ω => L (Zl ω)) hd
    (L.continuous.measurable.comp_aemeasurable h.aemeasurable_limit)
    (by congr 1; funext ω; simp)
  exact TendstoInDistribution.congr (fun n => Eventually.of_forall fun ω => by simp)
    (Eventually.of_forall fun _ => rfl) hd2

lemma dm_hRm {ι κ Ω : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (θ : EuclideanSpace ℝ ι)
    (φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)
    (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (hX : ∀ n, AEMeasurable (X n) μ) (hφX : ∀ n, AEMeasurable (fun ω => φ (X n ω)) μ)
    (n : ℕ) : AEMeasurable (fun ω => Real.sqrt (n : ℝ) • (φ (X n ω) - φ θ) -
      L (Real.sqrt (n : ℝ) • (X n ω - θ))) μ := by
  have h1 : AEMeasurable (fun ω => Real.sqrt (n : ℝ) • (X n ω - θ)) μ :=
    (continuous_const_smul (Real.sqrt (n : ℝ))).measurable.comp_aemeasurable
      ((hX n).sub_const θ)
  have h2 : AEMeasurable (fun ω => L (Real.sqrt (n : ℝ) • (X n ω - θ))) μ :=
    L.continuous.measurable.comp_aemeasurable h1
  have h3 : AEMeasurable (fun ω => Real.sqrt (n : ℝ) • (φ (X n ω) - φ θ)) μ :=
    (continuous_const_smul (Real.sqrt (n : ℝ))).measurable.comp_aemeasurable
      ((hφX n).sub_const (φ θ))
  exact h3.sub h2

lemma dm_hb_X {ι κ Ω Ω' : Type} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν] {Zl : Ω' → EuclideanSpace ℝ ι}
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (θ : EuclideanSpace ℝ ι)
    (φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)
    (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (hφ : HasFDerivAt φ L θ)
    (hX : ∀ n, AEMeasurable (X n) μ) (hφX : ∀ n, AEMeasurable (fun ω => φ (X n ω)) μ)
    (h : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (X n ω - θ)) atTop Zl
      (fun _ => μ) ν) :
    TendstoInMeasure μ (fun (n : ℕ) ω =>
      (‖X n ω - θ‖⁻¹ * ‖φ (X n ω) - φ θ - L (X n ω - θ)‖) *
        ‖Real.sqrt (n : ℝ) • (X n ω - θ)‖) atTop (fun _ => (0 : ℝ)) := by
  have hXθ := tendstoInMeasure_sub_of_clt X θ h
  have hρX : TendstoInMeasure μ (fun n ω => ‖X n ω - θ‖⁻¹ * ‖φ (X n ω) - φ θ - L (X n ω - θ)‖)
      atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_comp_of_tendsto X θ hXθ
      (fun x => ‖x - θ‖⁻¹ * ‖φ x - φ θ - L (x - θ)‖) (hasFDerivAt_iff_tendsto.1 hφ)
  exact dm_hb (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (X n ω - θ))
    (fun n ω => ‖X n ω - θ‖⁻¹ * ‖φ (X n ω) - φ θ - L (X n ω - θ)‖) h hρX
    (dm_rho_meas X θ φ L hX hφX)

/-- Delta method with a general derivative `L`. -/
lemma delta_method_clm {ι κ Ω Ω' : Type} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν] {Zl : Ω' → EuclideanSpace ℝ ι}
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (θ : EuclideanSpace ℝ ι)
    (φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)
    (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) (hφ : HasFDerivAt φ L θ)
    (hX : ∀ n, AEMeasurable (X n) μ) (hφX : ∀ n, AEMeasurable (fun ω => φ (X n ω)) μ)
    (h : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (X n ω - θ)) atTop Zl
      (fun _ => μ) ν) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (φ (X n ω) - φ θ)) atTop
      (fun ω => L (Zl ω)) (fun _ => μ) ν :=
  dm_tail (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (X n ω - θ))
    (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (φ (X n ω) - φ θ)) L h
    (dm_hR0 X θ φ L (dm_hb_X X θ φ L hφ hX hφX h)) (dm_hRm X θ φ L hX hφX)

/-- C4: multivariate delta method (generic). -/
theorem C4_delta_method {ι κ Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (hX : ∀ n, AEMeasurable (X n) μ)
    (θ : EuclideanSpace ℝ ι) (Sig : Matrix ι ι ℝ) (hSig : Sig.PosSemidef)
    (φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) (G : Matrix κ ι ℝ)
    (hφ : HasFDerivAt φ (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G)) θ)
    (hφX : ∀ n, AEMeasurable (fun ω => φ (X n ω)) μ)
    (h : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (X n ω - θ)) atTop id
      (fun _ => μ) (multivariateGaussian 0 Sig)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (φ (X n ω) - φ θ)) atTop id
      (fun _ => μ) (multivariateGaussian 0 (G * Sig * Gᵀ)) := by
  have hd := delta_method_clm X θ φ _ hφ hX hφX h
  refine tendstoInDistribution_congr_limit hd aemeasurable_id ?_
  rw [Measure.map_id, ← multivariateGaussian_map_toEuclideanLin Sig hSig G]
  rfl

end C4

section C6



/-- One Bellman step is measurable in all its arguments. -/
lemma bellman_meas [Nonempty A] {β : Type} [MeasurableSpace β] (γ : ℝ)
    (r : β → S × A → ℝ) (P' : β → S × A → S → ℝ) (Q : β → S × A → ℝ)
    (hr : Measurable r) (hP : Measurable P') (hQ : Measurable Q) :
    Measurable (fun b => bellman γ (r b) (P' b) (Q b)) := by
  refine measurable_pi_lambda _ fun x => ?_
  have h1 : Measurable (fun b => r b x) := (measurable_pi_apply x).comp hr
  have h2 : ∀ k, Measurable (fun b => P' b x k) := fun k =>
    (measurable_pi_apply k).comp ((measurable_pi_apply x).comp hP)
  have h3 : ∀ k, Measurable (fun b => ⨆ a, Q b (k, a)) := fun k =>
    Measurable.iSup fun a => (measurable_pi_apply (k, a)).comp hQ
  have h4 : Measurable (fun b => ∑ k, P' b x k * ⨆ a, Q b (k, a)) :=
    Finset.measurable_sum _ fun k _ => (h2 k).mul (h3 k)
  exact h1.add (measurable_const.mul h4)

/-- Value-iteration iterates are measurable in the parameter. -/
lemma bellman_iter_meas [Nonempty A] (γ : ℝ) (m : ℕ) :
    Measurable (fun p : (S × A → ℝ) × (S × A → S → ℝ) => (bellman γ p.1 p.2)^[m] 0) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact bellman_meas γ (fun p => p.1) (fun p => p.2) _ measurable_fst measurable_snd ih

/-- The Bellman fixed point is measurable in the parameter. -/
lemma bellmanFix_meas [Nonempty A] (γ : ℝ) :
    Measurable (fun p : (S × A → ℝ) × (S × A → S → ℝ) => bellmanFix γ p.1 p.2) :=
  (StronglyMeasurable.limUnder (l := atTop)
    (fun m => (bellman_iter_meas (S := S) (A := A) γ m).stronglyMeasurable)).measurable

/-- The plug-in map `θ ↦ φ(θ)` on the Euclidean parameter space is measurable. -/
lemma phi_meas [Nonempty A] (γ : ℝ) :
    Measurable (fun θ : EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)) =>
      (WithLp.toLp 2 (bellmanFix γ (fun x => θ (Sum.inl x)) (fun x k => θ (Sum.inr (x, k)))) :
        EuclideanSpace ℝ (S × A))) := by
  have hc1 : Continuous (fun θ : EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)) =>
      (fun x => θ (Sum.inl x))) := by fun_prop
  have hc2 : Continuous (fun θ : EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)) =>
      (fun x k => θ (Sum.inr (x, k)))) := by fun_prop
  have hm := (bellmanFix_meas (S := S) (A := A) γ).comp (hc1.measurable.prodMk hc2.measurable)
  exact (PiLp.continuous_toLp 2 _).measurable.comp hm
end C6

section ASM

/-- Almost-sure part of the plug-in principle (continuous mapping). -/
lemma as_part {ι κ Ω : Type} [Fintype ι] [Fintype κ] [MeasurableSpace Ω] {μ : Measure Ω}
    (Y : ℕ → Ω → ι → ℝ) (t : ι → ℝ) (φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)
    (hφ : ContinuousAt φ (WithLp.toLp 2 t)) (Q : ℕ → Ω → κ → ℝ) (q : κ → ℝ)
    (hQ : ∀ n ω, (φ (WithLp.toLp 2 (Y n ω))).ofLp = Q n ω) (hq : (φ (WithLp.toLp 2 t)).ofLp = q)
    (h : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 t)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω) atTop (𝓝 q) := by
  filter_upwards [h] with ω hω
  have h1 : Tendsto (fun n => (WithLp.toLp 2 (Y n ω) : EuclideanSpace ℝ ι)) atTop
      (𝓝 (WithLp.toLp 2 t)) := ((PiLp.continuous_toLp 2 _).tendsto t).comp hω
  have h2 := ((PiLp.continuous_ofLp 2 _).tendsto _).comp (hφ.tendsto.comp h1)
  simp only [Function.comp_def, hQ, hq] at h2
  exact h2

/-- Distribution part of the plug-in principle (delta method in coordinates). -/
lemma clt_part {ι κ Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ι → ℝ) (t : ι → ℝ)
    (hY : ∀ n, AEMeasurable (fun ω => (WithLp.toLp 2 (Y n ω) : EuclideanSpace ℝ ι)) μ)
    (Sig : Matrix ι ι ℝ) (hSig : Sig.PosSemidef)
    (φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) (G : Matrix κ ι ℝ)
    (hφ : HasFDerivAt φ (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G))
      (WithLp.toLp 2 t))
    (hφm : Measurable φ) (Q : ℕ → Ω → κ → ℝ) (q : κ → ℝ)
    (hQ : ∀ n ω, (φ (WithLp.toLp 2 (Y n ω))).ofLp = Q n ω) (hq : (φ (WithLp.toLp 2 t)).ofLp = q)
    (Sig' : Matrix κ κ ℝ) (hSig' : G * Sig * Gᵀ = Sig')
    (h : TendstoInDistribution (fun (n : ℕ) ω =>
      (WithLp.toLp 2 (fun i => Real.sqrt n * (Y n ω i - t i)) : EuclideanSpace ℝ ι))
      atTop id (fun _ => μ) (multivariateGaussian 0 Sig)) :
    TendstoInDistribution (fun (n : ℕ) ω =>
      (WithLp.toLp 2 (fun x => Real.sqrt n * (Q n ω x - q x)) : EuclideanSpace ℝ κ))
      atTop id (fun _ => μ) (multivariateGaussian 0 Sig') := by
  have e : (fun (n : ℕ) ω => Real.sqrt (n : ℝ) •
      ((WithLp.toLp 2 (Y n ω) : EuclideanSpace ℝ ι) - WithLp.toLp 2 t)) =
      fun (n : ℕ) ω =>
        (WithLp.toLp 2 (fun i => Real.sqrt n * (Y n ω i - t i)) : EuclideanSpace ℝ ι) := by
    funext n ω
    ext i
    simp
  have h' := h
  rw [← e] at h'
  have hd := C4_delta_method μ _ hY _ Sig hSig φ G hφ (fun n => hφm.comp_aemeasurable (hY n)) h'
  have e2 : (fun (n : ℕ) ω => Real.sqrt (n : ℝ) •
      (φ (WithLp.toLp 2 (Y n ω)) - φ (WithLp.toLp 2 t))) =
      fun (n : ℕ) ω =>
        (WithLp.toLp 2 (fun x => Real.sqrt n * (Q n ω x - q x)) : EuclideanSpace ℝ κ) := by
    funext n ω
    ext x
    simp [← hQ n ω, ← hq]
  rw [e2, hSig'] at hd
  exact hd


variable [Nonempty S] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Assembly: the target follows from C1 (consistency), C2 (CLT of the parameter) and
C3 (differentiability of the Bellman fixed point). -/
theorem parent_of_children (γ : ℝ) (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)]
    (u0 : S × A → ℝ) (p0 : S × A → S → ℝ) (aStar : S → A)
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y) (ν₀ : PMF S)
    (hC1 : ∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      Tendsto (fun n => thetaHat u0 p0 n ω) atTop (𝓝 (theta R P)))
    (hC2 : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (WithLp.toLp 2 (fun i => Real.sqrt n * (thetaHat u0 p0 n ω i - theta R P i)) :
          EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S))))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (multivariateGaussian 0 (SigmaRP (Pmat P) (sigma2R R) w)))
    (hC3 : HasFDerivAt
      (fun θ : EuclideanSpace ℝ ((S × A) ⊕ ((S × A) × S)) =>
        (WithLp.toLp 2 (bellmanFix γ (fun x => θ (Sum.inl x)) (fun x k => θ (Sum.inr (x, k)))) :
          EuclideanSpace ℝ (S × A)))
      (LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (gradPhi γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))))))
      (WithLp.toLp 2 (Sum.elim (muR R) (fun q => Pmat P q.1 q.2)))) :
    (∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      Tendsto (fun n => QHat γ u0 p0 n ω) atTop (𝓝 (bellmanFix γ (muR R) (Pmat P)))) ∧
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (WithLp.toLp 2
            (fun x => Real.sqrt n * (QHat γ u0 p0 n ω x - bellmanFix γ (muR R) (Pmat P) x)) :
          EuclideanSpace ℝ (S × A)))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (multivariateGaussian 0
        (SigmaQ γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))) (sigma2R R) w)) := by
  constructor
  · exact as_part (fun n ω => thetaHat u0 p0 n ω) (theta R P) _ hC3.continuousAt
      (fun n ω => QHat γ u0 p0 n ω) (bellmanFix γ (muR R) (Pmat P)) (fun n ω => rfl) rfl hC1
  · exact clt_part _ (fun n ω => thetaHat u0 p0 n ω) (theta R P)
      (fun n => (thetaHatE_meas u0 p0 n).aemeasurable) _
      (SigmaRP_posSemidef (Pmat P) (sigma2R R) w (Pmat_nonneg P) (Pmat_sum P)
        (fun x => variance_nonneg _ _) (w_pos P π hirr w hw_nonneg hw_sum hw_stat))
      _ _ hC3 (phi_meas γ) (fun n ω => QHat γ u0 p0 n ω) (bellmanFix γ (muR R) (Pmat P))
      (fun n ω => rfl) rfl _ (gradPhi_SigmaRP _ _ _ _ _ _) hC2


end ASM

end QVCLT40192638

open RLInference.QValueCLT MeasureTheory ProbabilityTheory Filter Matrix Topology in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (P : S × A → PMF S) (π : S → PMF A)
    (R : S × A → Measure ℝ) [∀ x, IsProbabilityMeasure (R x)] (hR : ∀ x, MemLp id 2 (R x))
    (u0 : S × A → ℝ) (p0 : S × A → S → ℝ)
    (hp0_nonneg : ∀ x k, 0 ≤ p0 x k) (hp0_sum : ∀ x, ∑ k, p0 x k = 1)
    (aStar : S → A)
    (hAstar : ∀ (s : S) (a : A), a ≠ aStar s →
      bellmanFix γ (muR R) (Pmat P) (s, a) < bellmanFix γ (muR R) (Pmat P) (s, aStar s))
    (hirr : ∀ x y, ∃ m : ℕ, 0 < (Ptilde P π ^ m) x y)
    (w : S × A → ℝ) (hw_nonneg : ∀ x, 0 ≤ w x) (hw_sum : ∑ x, w x = 1)
    (hw_stat : ∀ y, ∑ x, w x * Ptilde P π x y = w y)
    (ν₀ : PMF S) :
    (∀ᵐ ω ∂(MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R)),
      Tendsto (fun n => QHat γ u0 p0 n ω) atTop (𝓝 (bellmanFix γ (muR R) (Pmat P)))) ∧
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → (S × A) × ℝ) =>
        (WithLp.toLp 2
            (fun x => Real.sqrt n * (QHat γ u0 p0 n ω x - bellmanFix γ (muR R) (Pmat P) x)) :
          EuclideanSpace ℝ (S × A)))
      atTop id (fun _ => MarkovChainCLT.chainMeasure (dataKernel P π R) (initLaw ν₀ π R))
      (multivariateGaussian 0
        (SigmaQ γ (Pmat P) aStar (Vstar (bellmanFix γ (muR R) (Pmat P))) (sigma2R R) w)) := by
  have hwp := QVCLT40192638.w_pos P π hirr w hw_nonneg hw_sum hw_stat
  exact QVCLT40192638.parent_of_children (γ := γ) (P := P) (π := π) (R := R) (u0 := u0)
    (p0 := p0) (aStar := aStar) (hirr := hirr) (w := w) (hw_nonneg := hw_nonneg)
    (hw_sum := hw_sum) (hw_stat := hw_stat) (ν₀ := ν₀)
    (hC1 := QVCLT40192638.C1_of_pos P π R hR u0 p0 hirr w hwp hw_sum hw_stat ν₀)
    (hC2 := QVCLT40192638.C2_of_pos P π R hR u0 p0 hirr w hwp hw_sum hw_stat ν₀)
    (hC3 := QVCLT40192638.C3_bellmanFix_hasFDerivAt γ hγ0 hγ1 (muR R) (Pmat P)
      (QVCLT40192638.Pmat_nonneg P) (QVCLT40192638.Pmat_sum P) aStar hAstar)
