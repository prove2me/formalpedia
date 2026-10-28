-- Prove2me | solution 1 for SparseLpLq.SmallP.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:02:12.590743+00:00
-- url     : https://prove2.me/submissions/f2a682c0-84cb-412d-88e1-cb709571adcd

import Definitions.Def_SparseLpLq_SmallP_Setting
import Init
import Mathlib


section
namespace Queelius.SparseExtreme
open SparseLpLq.SmallP

theorem orthant_convex {n : ℕ} (s : Fin n → Bool) : Convex ℝ (orthant s) := by
  intro x hx y hy a b ha hb hab i
  have hxi := hx i
  have hyi := hy i
  change if s i then 0 ≤ a*x i+b*y i else a*x i+b*y i ≤ 0
  cases hsi : s i <;> simp only [hsi, Bool.false_eq_true, ↓reduceIte] at hxi hyi ⊢
  · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hxi)
      (mul_nonpos_of_nonneg_of_nonpos hb hyi)
  · exact add_nonneg (mul_nonneg ha hxi) (mul_nonneg hb hyi)

theorem abs_combination {n : ℕ} {s : Fin n → Bool} {x y : Fin n → ℝ}
    (hx : x ∈ orthant s) (hy : y ∈ orthant s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (i : Fin n) : |a*x i+b*y i| = a*|x i|+b*|y i| := by
  have hxi := hx i
  have hyi := hy i
  cases hsi : s i <;> simp only [hsi, Bool.false_eq_true, ↓reduceIte] at hxi hyi
  · rw [abs_of_nonpos hxi, abs_of_nonpos hyi,
      abs_of_nonpos (add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hxi)
        (mul_nonpos_of_nonneg_of_nonpos hb hyi))]
    ring
  · rw [abs_of_nonneg hxi, abs_of_nonneg hyi,
      abs_of_nonneg (add_nonneg (mul_nonneg ha hxi) (mul_nonneg hb hyi))]

theorem abs_coordinate_injective {n : ℕ} {s : Fin n → Bool} {x y : Fin n → ℝ}
    (hx : x ∈ orthant s) (hy : y ∈ orthant s) (i : Fin n)
    (h : |x i| = |y i|) : x i = y i := by
  have hxi := hx i
  have hyi := hy i
  cases hsi : s i <;> simp only [hsi, Bool.false_eq_true, ↓reduceIte] at hxi hyi
  · simpa [abs_of_nonpos hxi, abs_of_nonpos hyi] using h
  · simpa [abs_of_nonneg hxi, abs_of_nonneg hyi] using h

theorem lp_strict_concave {n : ℕ} (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (s : Fin n → Bool) : StrictConcaveOn ℝ (orthant s) (lpObj p) := by
  refine ⟨orthant_convex s, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hcoord : ∃ i, |x i| ≠ |y i| := by
    by_contra! h
    exact hxy (funext fun i => abs_coordinate_injective hx hy i (h i))
  have hc := Real.strictConcaveOn_rpow hp.1 hp.2
  have hle (i : Fin n) : a*|x i|^p+b*|y i|^p ≤ (a*|x i|+b*|y i|)^p :=
    hc.concaveOn.2 (show |x i| ∈ Set.Ici 0 from abs_nonneg (x i))
      (show |y i| ∈ Set.Ici 0 from abs_nonneg (y i)) ha.le hb.le hab
  have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      a*|x i|^p+b*|y i|^p < (a*|x i|+b*|y i|)^p := by
    obtain ⟨i,hi⟩ := hcoord
    exact ⟨i,Finset.mem_univ _,hc.2 (show |x i| ∈ Set.Ici 0 from abs_nonneg (x i))
      (show |y i| ∈ Set.Ici 0 from abs_nonneg (y i)) hi ha hb hab⟩
  have hs := Finset.sum_lt_sum (fun i _ => hle i) hlt
  simpa only [lpObj,ne_of_gt hp.1,↓reduceIte,smul_eq_mul,Pi.add_apply,Pi.smul_apply,
    abs_combination hx hy ha.le hb.le,Finset.sum_add_distrib,Finset.mul_sum] using hs

theorem strict_concave_min_extreme {n : ℕ} {S T : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : StrictConcaveOn ℝ S f) (hTS : T ⊆ S) {x : Fin n → ℝ} (hx : x ∈ T)
    (hmin : ∀ y ∈ T, f x ≤ f y) : x ∈ Set.extremePoints ℝ T := by
  refine ⟨hx, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  by_cases hyz : y=z
  · rw [hyz,← add_smul,hab,one_smul] at heq
    exact hyz.trans heq
  · have hlt := hf.2 (hTS hy) (hTS hz) hyz ha hb hab
    rw [heq] at hlt
    have hmy := mul_le_mul_of_nonneg_left (hmin y hy) ha.le
    have hmz := mul_le_mul_of_nonneg_left (hmin z hz) hb.le
    simp only [smul_eq_mul] at hlt
    have hw : a*f x+b*f x=f x := by rw [← add_mul,hab,one_mul]
    linarith

theorem orthant_min_extreme {n : ℕ} (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (s : Fin n → Bool) (T : Set (Fin n → ℝ)) (hT : T ⊆ orthant s)
    (x : Fin n → ℝ) (hx : x ∈ T) (hmin : ∀ y ∈ T, lpObj p x ≤ lpObj p y) :
    x ∈ Set.extremePoints ℝ T :=
  strict_concave_min_extreme (lp_strict_concave p hp s) hT hx hmin

end Queelius.SparseExtreme

end

section
namespace Queelius.SparseExtreme.Controls
open SparseLpLq.SmallP

theorem objective_nonnegative {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : 0 ≤ lpObj p x := by
  classical
  unfold lpObj
  split_ifs
  · positivity
  · exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _

theorem zero_minimizes {n : ℕ} (p : ℝ) :
    ∀ x : Fin n → ℝ, lpObj p (0 : Fin n → ℝ) ≤ lpObj p x := by
  intro x
  have hz : lpObj p (0 : Fin n → ℝ) = 0 := by
    by_cases hp : p=0
    · simp [lpObj,hp]
    · simp [lpObj,hp,Real.zero_rpow hp]
  rw [hz]
  exact objective_nonnegative p x

theorem origin_not_extreme_univ :
    (0 : Fin 1 → ℝ) ∉ Set.extremePoints ℝ Set.univ := by
  intro h
  have he := h.2 (show (fun _ : Fin 1 => (-1:ℝ)) ∈ Set.univ from Set.mem_univ _)
    (show (fun _ : Fin 1 => (1:ℝ)) ∈ Set.univ from Set.mem_univ _)
    (show (0 : Fin 1 → ℝ) ∈ openSegment ℝ (fun _ => (-1:ℝ)) (fun _ => (1:ℝ)) from by
      refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
      ext i
      norm_num)
  have := congrFun he 0
  norm_num at this

theorem one_affine {n : ℕ} {s : Fin n → Bool} {x y : Fin n → ℝ}
    (hx : x ∈ orthant s) (hy : y ∈ orthant s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    lpObj 1 (a • x+b • y) = a*lpObj 1 x+b*lpObj 1 y := by
  simp only [lpObj,one_ne_zero,↓reduceIte,Real.rpow_one,Pi.add_apply,Pi.smul_apply,
    smul_eq_mul,abs_combination hx hy ha hb,Finset.sum_add_distrib,Finset.mul_sum]

def simplex : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0+x 1=1}
noncomputable def simplexCenter : Fin 2 → ℝ := ![1/2,1/2]

theorem simplex_objective (x : Fin 2 → ℝ) (hx : x ∈ simplex) : lpObj 1 x = 1 := by
  simpa [lpObj,Fin.sum_univ_two,abs_of_nonneg hx.1,abs_of_nonneg hx.2.1] using hx.2.2

theorem one_endpoint_counterexample :
    simplex ⊆ orthant (fun _ => true) ∧ simplexCenter ∈ simplex ∧
      (∀ y ∈ simplex, lpObj 1 simplexCenter ≤ lpObj 1 y) ∧
      simplexCenter ∉ Set.extremePoints ℝ simplex := by
  have hc : simplexCenter ∈ simplex := by norm_num [simplex,simplexCenter]
  refine ⟨?_,hc,?_,?_⟩
  · intro x hx i
    fin_cases i
    · exact hx.1
    · exact hx.2.1
  · intro y hy
    rw [simplex_objective _ hc,simplex_objective _ hy]
  · intro he
    have h := he.2 (show ![(1:ℝ),0] ∈ simplex from by norm_num [simplex])
      (show ![(0:ℝ),1] ∈ simplex from by norm_num [simplex])
      (show simplexCenter ∈ openSegment ℝ ![(1:ℝ),0] ![(0:ℝ),1] from by
        refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
        ext i
        fin_cases i <;> norm_num [simplexCenter])
    have := congrFun h 0
    norm_num [simplexCenter] at this

theorem zero_dimension (T : Set (Fin 0 → ℝ)) (x : Fin 0 → ℝ) (hx : x ∈ T) :
    x ∈ Set.extremePoints ℝ T := by
  rw [Set.extremePoints_eq_self]
  exact hx

def positiveInterval : Set (Fin 1 → ℝ) := {x | 1 ≤ x 0 ∧ x 0 ≤ 2}
noncomputable def intervalCenter : Fin 1 → ℝ := fun _ => 3/2

theorem zero_positive_objective (x : Fin 1 → ℝ) (hx : 1 ≤ x 0) : lpObj 0 x = 1 := by
  have hne : x 0 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
  have hall : ∀ i : Fin 1, x i ≠ 0 := by
    intro i
    fin_cases i
    exact hne
  simp [lpObj,hall]

theorem zero_endpoint_counterexample :
    positiveInterval ⊆ orthant (fun _ => true) ∧ intervalCenter ∈ positiveInterval ∧
      (∀ y ∈ positiveInterval, lpObj 0 intervalCenter ≤ lpObj 0 y) ∧
      intervalCenter ∉ Set.extremePoints ℝ positiveInterval := by
  have hc : intervalCenter ∈ positiveInterval := by norm_num [positiveInterval,intervalCenter]
  refine ⟨?_,hc,?_,?_⟩
  · intro x hx i
    fin_cases i
    exact le_trans zero_le_one hx.1
  · intro y hy
    rw [zero_positive_objective _ hc.1,zero_positive_objective _ hy.1]
  · intro he
    have h := he.2 (show (fun _ : Fin 1 => (1:ℝ)) ∈ positiveInterval from by norm_num [positiveInterval])
      (show (fun _ : Fin 1 => (2:ℝ)) ∈ positiveInterval from by norm_num [positiveInterval])
      (show intervalCenter ∈ openSegment ℝ (fun _ => (1:ℝ)) (fun _ => (2:ℝ)) from by
        refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
        ext i
        norm_num [intervalCenter])
    have := congrFun h 0
    norm_num [intervalCenter] at this

end Queelius.SparseExtreme.Controls

end

section
open scoped ENNReal Matrix

namespace Queelius.SparseExtreme
open SparseLpLq.SmallP

theorem orthant_piece_min_extreme {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma p : ℝ) (q : ℝ≥0∞) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (s : Fin n → Bool) (x : Fin n → ℝ) (hx : x ∈ orthant s ∩ FEA A b sigma q)
    (hmin : ∀ y ∈ orthant s ∩ FEA A b sigma q, lpObj p x ≤ lpObj p y) :
    x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b sigma q) :=
  orthant_min_extreme p hp s _ (fun _ h => h.1) x hx hmin

theorem global_solution_in_orthant_extremes {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma p : ℝ) (q : ℝ≥0∞) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (x : Fin n → ℝ) (hx : x ∈ SOL A b sigma p q) :
    ∃ s : Fin n → Bool, x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b sigma q) := by
  classical
  let s : Fin n → Bool := fun i => decide (0 ≤ x i)
  have hs : x ∈ orthant s := by
    intro i
    by_cases h : 0 ≤ x i
    · simpa [s,h] using h
    · simpa [s,h] using le_of_lt (lt_of_not_ge h)
  exact ⟨s,orthant_piece_min_extreme A b sigma p q hp s x ⟨hs,hx.1⟩
    (fun y hy => hx.2 y hy.2)⟩

end Queelius.SparseExtreme

open SparseLpLq.SmallP
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (s : Fin n → Bool)
    (hne : (orthant s ∩ FEA A b σ 1).Nonempty)
    (x : Fin n → ℝ) (hx : x ∈ orthant s ∩ FEA A b σ 1)
    (hopt : ∀ y ∈ orthant s ∩ FEA A b σ 1, lpObj p x ≤ lpObj p y) :
    x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b σ 1) :=
  Queelius.SparseExtreme.orthant_piece_min_extreme A b σ p 1 hp s x hx hopt

end
