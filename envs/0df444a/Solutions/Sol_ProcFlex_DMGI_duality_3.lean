-- Prove2me | solution 1 for ProcFlex.DMGI.duality_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:37:30.584261+00:00
-- url     : https://prove2.me/submissions/531633ef-cc56-44b0-97e8-f109ddc38b54

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model

open Finset ProcFlex.DMGI

namespace PFD

variable {m n T : ℕ}

/-- The Lagrangian of the profit LP (1). -/
noncomputable def Lag (S : System m n T) (A : Design m n) (d : Fin n → ℝ)
    (u : (Fin n → ℝ) × (Fin m → ℝ)) (x : Fin m → Fin n → ℝ) : ℝ :=
  ∑ a ∈ A, S.p a.2 * x a.1 a.2 + ∑ i, u.1 i * (d i - ∑ j, x j i) +
    ∑ j, u.2 j * (S.C j - ∑ i, x j i)

noncomputable def coef (S : System m n T) (A : Design m n) (u : (Fin n → ℝ) × (Fin m → ℝ))
    (j : Fin m) (i : Fin n) : ℝ :=
  (if (j, i) ∈ A then S.p i else 0) - u.1 i - u.2 j

lemma Lag_x (S : System m n T) (A : Design m n) (d : Fin n → ℝ)
    (u : (Fin n → ℝ) × (Fin m → ℝ)) (x : Fin m → Fin n → ℝ) :
    Lag S A d u x = (∑ i, u.1 i * d i + ∑ j, u.2 j * S.C j) +
      ∑ j, ∑ i, x j i * coef S A u j i := by
  unfold Lag coef
  have h1 : ∑ a ∈ A, S.p a.2 * x a.1 a.2 =
      ∑ j, ∑ i, x j i * (if (j, i) ∈ A then S.p i else 0) := by
    rw [← Fintype.sum_prod_type' (fun j i => x j i * (if (j, i) ∈ A then S.p i else 0))]
    rw [← sum_filter_add_sum_filter_not univ (fun a : Fin m × Fin n => a ∈ A)]
    have : univ.filter (fun a : Fin m × Fin n => a ∈ A) = A := by ext; simp
    rw [this]
    have h0 : ∑ a ∈ univ.filter (fun a : Fin m × Fin n => a ∉ A),
        x a.1 a.2 * (if (a.1, a.2) ∈ A then S.p a.2 else 0) = 0 := by
      apply sum_eq_zero; intro a ha; simp at ha; simp [ha]
    rw [h0, add_zero]
    apply sum_congr rfl; intro a ha; simp [ha]; ring
  rw [h1]
  have e1 : ∑ j, ∑ i, x j i * ((if (j, i) ∈ A then S.p i else 0) - u.1 i - u.2 j) =
      ∑ j, ∑ i, x j i * (if (j, i) ∈ A then S.p i else 0) - ∑ j, ∑ i, x j i * u.1 i -
        ∑ j, ∑ i, x j i * u.2 j := by
    rw [← sum_sub_distrib, ← sum_sub_distrib]; apply sum_congr rfl; intro j _
    rw [← sum_sub_distrib, ← sum_sub_distrib]; apply sum_congr rfl; intro i _; ring
  have e2 : ∑ j, ∑ i, x j i * u.1 i = ∑ i, u.1 i * ∑ j, x j i := by
    rw [sum_comm]; apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl
    intro j _; ring
  have e3 : ∑ j, ∑ i, x j i * u.2 j = ∑ j, u.2 j * ∑ i, x j i := by
    apply sum_congr rfl; intro j _; rw [mul_sum]; apply sum_congr rfl; intro i _; ring
  have e4 : ∑ i, u.1 i * (d i - ∑ j, x j i) = ∑ i, u.1 i * d i - ∑ i, u.1 i * ∑ j, x j i := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; ring
  have e5 : ∑ j, u.2 j * (S.C j - ∑ i, x j i) = ∑ j, u.2 j * S.C j - ∑ j, u.2 j * ∑ i, x j i := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; ring
  rw [e1, e2, e3, e4, e5]; ring

lemma Lag_u (S : System m n T) (A : Design m n) (d : Fin n → ℝ)
    (u : (Fin n → ℝ) × (Fin m → ℝ)) (x : Fin m → Fin n → ℝ) :
    Lag S A d u x = ∑ a ∈ A, S.p a.2 * x a.1 a.2 + ∑ i, u.1 i * (d i - ∑ j, x j i) +
      ∑ j, u.2 j * (S.C j - ∑ i, x j i) := rfl

lemma sum_aff {ι : Type*} [Fintype ι] (a b : ℝ) (u v w : ι → ℝ) :
    ∑ i, (a * u i + b * v i) * w i = a * ∑ i, u i * w i + b * ∑ i, v i * w i := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]; apply sum_congr rfl; intro i _; ring

lemma Lag_affine_u (S : System m n T) (A : Design m n) (d : Fin n → ℝ)
    (x : Fin m → Fin n → ℝ) (u v : (Fin n → ℝ) × (Fin m → ℝ)) (a b : ℝ) (hab : a + b = 1) :
    Lag S A d (a • u + b • v) x = a * Lag S A d u x + b * Lag S A d v x := by
  simp only [Lag_u, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [sum_aff, sum_aff]
  linear_combination (-(∑ a ∈ A, S.p a.2 * x a.1 a.2)) * hab

lemma Lag_affine_x (S : System m n T) (A : Design m n) (d : Fin n → ℝ)
    (u : (Fin n → ℝ) × (Fin m → ℝ)) (x y : Fin m → Fin n → ℝ) (a b : ℝ) (hab : a + b = 1) :
    Lag S A d u (a • x + b • y) = a * Lag S A d u x + b * Lag S A d u y := by
  simp only [Lag_x, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ j, ∑ i, (a * x j i + b * y j i) * coef S A u j i =
      a * ∑ i, x j i * coef S A u j i + b * ∑ i, y j i * coef S A u j i := fun j => sum_aff _ _ _ _ _
  simp only [this]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  linear_combination (-(∑ i, u.1 i * d i + ∑ j, u.2 j * S.C j)) * hab

end PFD

namespace PFD

variable {m n T : ℕ}

lemma profit_le (S : System m n T) (A : Design m n) (d : Fin n → ℝ)
    (y : Fin n → ℝ) (z : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hz : ∀ j, 0 ≤ z j) (hf : ∀ a ∈ A, S.p a.2 ≤ y a.2 + z a.1)
    (x : Fin m → Fin n → ℝ) (hx : S.lpData.PrimalFeasible d x) :
    S.lpData.profit A x ≤ ∑ i, d i * y i + ∑ j, S.C j * z j := by
  obtain ⟨hx0, hxd, hxC⟩ := hx
  unfold ProfitLPData.profit
  calc ∑ a ∈ A, S.lpData.p a.2 * x a.1 a.2
      ≤ ∑ a ∈ A, (y a.2 + z a.1) * x a.1 a.2 :=
        sum_le_sum (fun a ha => mul_le_mul_of_nonneg_right (hf a ha) (hx0 _ _))
    _ ≤ ∑ a : Fin m × Fin n, (y a.2 + z a.1) * x a.1 a.2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun a _ _ => mul_nonneg (add_nonneg (hy _) (hz _)) (hx0 _ _))
    _ = ∑ i, y i * ∑ j, x j i + ∑ j, z j * ∑ i, x j i := by
        rw [Fintype.sum_prod_type]
        simp only [add_mul, sum_add_distrib, mul_sum]
        rw [sum_comm]
    _ ≤ ∑ i, d i * y i + ∑ j, S.C j * z j := by
        apply add_le_add
        · apply sum_le_sum; intro i _
          rw [mul_comm (d i)]
          exact mul_le_mul_of_nonneg_left (hxd i) (hy i)
        · apply sum_le_sum; intro j _
          rw [mul_comm (S.C j)]
          exact mul_le_mul_of_nonneg_left (hxC j) (hz j)

lemma zero_feasible (S : System m n T) (hS : S.IsValid) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    S.lpData.PrimalFeasible d 0 := by
  refine ⟨fun _ _ => le_refl _, fun i => ?_, fun j => ?_⟩
  · simpa using hd i
  · simp only [Pi.zero_apply, sum_const_zero]; exact hS.2.2.2.1 j

lemma weak (S : System m n T) (hS : S.IsValid) (A : Design m n) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (y : Fin n → ℝ) (z : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hz : ∀ j, 0 ≤ z j) (hf : ∀ a ∈ A, S.p a.2 ≤ y a.2 + z a.1) :
    g S A d ≤ ∑ i, d i * y i + ∑ j, S.C j * z j := by
  unfold g ProfitLPData.value
  refine csSup_le ⟨S.lpData.profit A 0, 0, zero_feasible S hS d hd, rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact profit_le S A d y z hy hz hf x hx

lemma affine_convex_concave {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E}
    (hs : Convex ℝ s) (F : E → ℝ)
    (hF : ∀ u v (a b : ℝ), a + b = 1 → F (a • u + b • v) = a * F u + b * F v) :
    ConvexOn ℝ s F ∧ ConcaveOn ℝ s F :=
  ⟨⟨hs, fun u _ v _ a b _ _ hab => by rw [hF u v a b hab]; simp [smul_eq_mul]⟩,
   ⟨hs, fun u _ v _ a b _ _ hab => by rw [hF u v a b hab]; simp [smul_eq_mul]⟩⟩

lemma sum_upd2 (c : Fin m → Fin n → ℝ) (x : Fin m → Fin n → ℝ) (j : Fin m) (i : Fin n) (t : ℝ) :
    ∑ j', ∑ i', (if j' = j ∧ i' = i then t else x j' i') * c j' i' =
      ∑ j', ∑ i', x j' i' * c j' i' + (t - x j i) * c j i := by
  have h : ∀ j' i', (if j' = j ∧ i' = i then t else x j' i') * c j' i' =
      x j' i' * c j' i' + (if j' = j then (if i' = i then (t - x j i) * c j i else 0) else 0) := by
    intro j' i'
    by_cases h1 : j' = j
    · by_cases h2 : i' = i
      · subst h1; subst h2; simp; ring
      · simp [h1, h2]
    · simp [h1]
  simp only [h, sum_add_distrib]
  simp

lemma sum_upd1 {k : ℕ} (c : Fin k → ℝ) (y : Fin k → ℝ) (i : Fin k) (t : ℝ) :
    ∑ i', (if i' = i then t else y i') * c i' = ∑ i', y i' * c i' + (t - y i) * c i := by
  have h : ∀ i', (if i' = i then t else y i') * c i' =
      y i' * c i' + (if i' = i then (t - y i) * c i else 0) := by
    intro i'; by_cases h1 : i' = i
    · subst h1; simp; ring
    · simp [h1]
  simp only [h, sum_add_distrib]; simp

end PFD

open PFD in
theorem solution {m n T : ℕ} (S : System m n T) (hS : S.IsValid)
    (A : Design m n) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    IsLeast {v : ℝ | ∃ (y : Fin n → ℝ) (z : Fin m → ℝ),
      DualFeasible S A y z ∧ v = dualObj S d y z} (g S A d) := by
  refine ⟨?_, ?_⟩
  swap
  · rintro v ⟨y, z, ⟨hf, hy, hz⟩, rfl⟩
    exact weak S hS A d hd y z hy hz hf
  obtain ⟨_, _, _, hC, _, hpos, _⟩ := hS
  set M : ℝ := ∑ t, S.P t + 1 with hMdef
  set B : ℝ := ∑ i, d i + ∑ j, S.C j + 1 with hBdef
  have hpM : ∀ i, S.p i < M := by
    intro i
    have : S.P (S.cat i) ≤ ∑ t, S.P t :=
      single_le_sum (f := S.P) (fun t _ => le_of_lt (hpos t)) (mem_univ _)
    unfold System.p; linarith
  have hM0 : 0 ≤ M := by
    have := sum_nonneg (fun t (_ : t ∈ univ) => le_of_lt (hpos t)); linarith
  have hdB : ∀ i, d i < B := by
    intro i
    have h1 : d i ≤ ∑ i, d i := single_le_sum (fun i _ => hd i) (mem_univ i)
    have h2 : 0 ≤ ∑ j, S.C j := sum_nonneg (fun j _ => hC j)
    linarith
  have hCB : ∀ j, S.C j < B := by
    intro j
    have h1 : S.C j ≤ ∑ j, S.C j := single_le_sum (fun j _ => hC j) (mem_univ j)
    have h2 : 0 ≤ ∑ i, d i := sum_nonneg (fun i _ => hd i)
    linarith
  have hB0 : 0 ≤ B := by
    have := sum_nonneg (fun i (_ : i ∈ univ) => hd i)
    have := sum_nonneg (fun j (_ : j ∈ univ) => hC j)
    linarith
  let X : Set ((Fin n → ℝ) × (Fin m → ℝ)) := Set.Icc (0, 0) (fun _ => M, fun _ => M)
  let Y : Set (Fin m → Fin n → ℝ) := Set.Icc 0 (fun _ _ => B)
  have hX0 : ((0 : Fin n → ℝ), (0 : Fin m → ℝ)) ∈ X := by
    simp only [X, Set.mem_Icc, Prod.mk_le_mk]
    refine ⟨⟨le_refl _, le_refl _⟩, fun _ => hM0, fun _ => hM0⟩
  have hY0 : (0 : Fin m → Fin n → ℝ) ∈ Y := by
    simp only [Y, Set.mem_Icc]
    exact ⟨le_refl _, fun _ _ => hB0⟩
  obtain ⟨a, ha, xs, hxs, hsad⟩ := Sion.exists_isSaddlePointOn (f := Lag S A d)
    ⟨_, hX0⟩ (convex_Icc _ _) isCompact_Icc
    (fun x _ => by
      apply LowerSemicontinuous.lowerSemicontinuousOn
      apply Continuous.lowerSemicontinuous
      unfold Lag; fun_prop)
    (fun x _ => ((affine_convex_concave (convex_Icc _ _) (fun u => Lag S A d u x)
      (fun u v a b hab => Lag_affine_u S A d x u v a b hab)).1).quasiconvexOn)
    (convex_Icc _ _) ⟨_, hY0⟩ isCompact_Icc
    (fun u _ => by
      apply UpperSemicontinuous.upperSemicontinuousOn
      apply Continuous.upperSemicontinuous
      unfold Lag; fun_prop)
    (fun u _ => ((affine_convex_concave (convex_Icc _ _) (fun x => Lag S A d u x)
      (fun x y a b hab => Lag_affine_x S A d u x y a b hab)).2).quasiconcaveOn)
  obtain ⟨ys, zs⟩ := a
  have S1 : ∀ u ∈ X, Lag S A d (ys, zs) xs ≤ Lag S A d u xs := fun u hu => hsad u hu xs hxs
  have S2 : ∀ w ∈ Y, Lag S A d (ys, zs) w ≤ Lag S A d (ys, zs) xs :=
    fun w hw => hsad (ys, zs) ha w hw
  simp only [X, Set.mem_Icc, Prod.mk_le_mk] at ha
  obtain ⟨⟨hys0, hzs0⟩, hysM, hzsM⟩ := ha
  replace hys0 : ∀ i, 0 ≤ ys i := fun i => hys0 i
  replace hzs0 : ∀ j, 0 ≤ zs j := fun j => hzs0 j
  replace hysM : ∀ i, ys i ≤ M := fun i => hysM i
  replace hzsM : ∀ j, zs j ≤ M := fun j => hzsM j
  simp only [Y, Set.mem_Icc] at hxs
  obtain ⟨hxs0, hxsB⟩ := hxs
  replace hxs0 : ∀ j i, 0 ≤ xs j i := fun j i => hxs0 j i
  replace hxsB : ∀ j i, xs j i ≤ B := fun j i => hxsB j i
  -- coordinate facts
  have ys_M : ∀ i, d i - ∑ j, xs j i < 0 → ys i = M := by
    intro i hi
    by_contra hne
    have hlt : ys i < M := lt_of_le_of_ne (hysM i) hne
    have hmem : ((fun i' => if i' = i then M else ys i'), zs) ∈ X := by
      simp only [X, Set.mem_Icc, Prod.mk_le_mk]
      refine ⟨⟨fun i' => ?_, hzs0⟩, fun i' => ?_, hzsM⟩
      · by_cases h : i' = i
        · simp [h, hM0]
        · simp [h]; exact hys0 i'
      · by_cases h : i' = i
        · simp [h]
        · simp [h]; exact hysM i'
    have := S1 _ hmem
    simp only [Lag_u] at this
    rw [sum_upd1] at this
    nlinarith
  have zs_M : ∀ j, S.C j - ∑ i, xs j i < 0 → zs j = M := by
    intro j hj
    by_contra hne
    have hlt : zs j < M := lt_of_le_of_ne (hzsM j) hne
    have hmem : (ys, (fun j' => if j' = j then M else zs j')) ∈ X := by
      simp only [X, Set.mem_Icc, Prod.mk_le_mk]
      refine ⟨⟨hys0, fun j' => ?_⟩, hysM, fun j' => ?_⟩
      · by_cases h : j' = j
        · simp [h, hM0]
        · simp [h]; exact hzs0 j'
      · by_cases h : j' = j
        · simp [h]
        · simp [h]; exact hzsM j'
    have := S1 _ hmem
    simp only [Lag_u] at this
    rw [sum_upd1] at this
    nlinarith
  have x_B : ∀ j i, 0 < coef S A (ys, zs) j i → xs j i = B := by
    intro j i hc
    by_contra hne
    have hlt : xs j i < B := lt_of_le_of_ne (hxsB j i) hne
    have hmem : (fun j' i' => if j' = j ∧ i' = i then B else xs j' i') ∈ Y := by
      simp only [Y, Set.mem_Icc]
      refine ⟨fun j' i' => ?_, fun j' i' => ?_⟩
      · by_cases h : j' = j ∧ i' = i
        · simp only [h, and_self, if_true, Pi.zero_apply]; exact hB0
        · simp only [h, if_false]; exact hxs0 j' i'
      · by_cases h : j' = j ∧ i' = i
        · simp only [h, and_self, if_true]; exact le_refl _
        · simp only [h, if_false]; exact hxsB j' i'
    have := S2 _ hmem
    rw [Lag_x, Lag_x, sum_upd2] at this
    nlinarith
  have x_0 : ∀ j i, coef S A (ys, zs) j i < 0 → xs j i = 0 := by
    intro j i hc
    by_contra hne
    have hlt : 0 < xs j i := lt_of_le_of_ne (hxs0 j i) (Ne.symm hne)
    have hmem : (fun j' i' => if j' = j ∧ i' = i then 0 else xs j' i') ∈ Y := by
      simp only [Y, Set.mem_Icc]
      refine ⟨fun j' i' => ?_, fun j' i' => ?_⟩
      · by_cases h : j' = j ∧ i' = i
        · simp only [h, and_self, if_true, Pi.zero_apply]; exact le_refl _
        · simp only [h, if_false]; exact hxs0 j' i'
      · by_cases h : j' = j ∧ i' = i
        · simp only [h, and_self, if_true]; exact hB0
        · simp only [h, if_false]; exact hxsB j' i'
    have := S2 _ hmem
    rw [Lag_x, Lag_x, sum_upd2] at this
    nlinarith
  have hite_le : ∀ j i, (if (j, i) ∈ A then S.p i else 0) ≤ S.p i := by
    intro j i; split_ifs
    · exact le_refl _
    · exact le_of_lt (hpos _)
  -- dual feasibility
  have hfeas : ∀ a ∈ A, S.p a.2 ≤ ys a.2 + zs a.1 := by
    rintro ⟨j, i⟩ hji
    by_contra hcon
    push Not at hcon
    have hc : 0 < coef S A (ys, zs) j i := by
      simp only [coef, if_pos hji]; linarith
    have hB := x_B j i hc
    have hsum : B ≤ ∑ j', xs j' i := by
      rw [← hB]; exact single_le_sum (f := fun j' => xs j' i) (fun j' _ => hxs0 j' i) (mem_univ j)
    have hyM := ys_M i (by linarith [hdB i])
    have := hpM i
    simp only at hcon
    linarith [hzs0 j]
  -- primal feasibility
  have hxd : ∀ i, ∑ j, xs j i ≤ d i := by
    intro i
    by_contra hcon; push Not at hcon
    have hyM := ys_M i (by linarith)
    have hz : ∀ j, xs j i = 0 := by
      intro j; apply x_0
      simp only [coef]; linarith [hite_le j i, hpM i, hzs0 j]
    simp [hz] at hcon; linarith [hd i]
  have hxC : ∀ j, ∑ i, xs j i ≤ S.C j := by
    intro j
    by_contra hcon; push Not at hcon
    have hzM := zs_M j (by linarith)
    have hz : ∀ i, xs j i = 0 := by
      intro i; apply x_0
      simp only [coef]; linarith [hite_le j i, hpM i, hys0 i]
    simp [hz] at hcon; linarith [hC j]
  have hprim : S.lpData.PrimalFeasible d xs := ⟨hxs0, hxd, hxC⟩
  -- value
  have hv1 : Lag S A d (ys, zs) 0 = ∑ i, d i * ys i + ∑ j, S.C j * zs j := by
    simp only [Lag_u, Pi.zero_apply, mul_zero, sum_const_zero, sub_zero, zero_add]
    congr 1 <;> apply sum_congr rfl <;> intro _ _ <;> ring
  have hv2 : Lag S A d (0, 0) xs = S.lpData.profit A xs := by
    simp only [Lag_u, Pi.zero_apply, zero_mul, sum_const_zero, add_zero]; rfl
  have hle1 := S2 0 hY0
  have hle2 := S1 (0, 0) hX0
  have hbdd : BddAbove (S.lpData.profit A '' {x | S.lpData.PrimalFeasible d x}) := by
    refine ⟨∑ i, d i * ys i + ∑ j, S.C j * zs j, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact profit_le S A d ys zs hys0 hzs0 hfeas x hx
  have hprof : S.lpData.profit A xs ≤ g S A d := by
    unfold g ProfitLPData.value
    exact le_csSup hbdd ⟨xs, hprim, rfl⟩
  have hg := weak S ⟨by assumption, by assumption, by assumption, hC, by assumption, hpos,
    by assumption⟩ A d hd ys zs hys0 hzs0 hfeas
  refine ⟨ys, zs, ⟨hfeas, hys0, hzs0⟩, ?_⟩
  show g S A d = ∑ i, d i * ys i + ∑ j, S.C j * zs j
  linarith
