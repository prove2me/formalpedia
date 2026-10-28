-- Prove2me | solution 1 for SparseLpLq.SmallP.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:38:26.883178+00:00
-- url     : https://prove2.me/submissions/afbfd78e-8e97-4272-bd18-589958b22ccb

import Definitions.Def_SparseLpLq_SmallP_Setting
import Init
import Mathlib


section
namespace Queelius.FiniteHalfspaces
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {n : ℕ}

def region (a : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i,a i x ≤ b i}

def active (a : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ) (x : Fin n → ℝ) : Set ι :=
  {i | a i x = b i}

theorem active_determines_extreme (a : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {x y : Fin n → ℝ} (hx : x ∈ Set.extremePoints ℝ (region a b))
    (hy : y ∈ region a b) (hactive : active a b x ⊆ active a b y) : x=y := by
  classical
  let I := {i : ι // a i x ≠ b i}
  have hslack (i : I) : 0 < (b i-a i x)/(|a i (x-y)|+1) := by
    apply div_pos
    · exact sub_pos.mpr (lt_of_le_of_ne (hx.1 i) i.property)
    · positivity
  obtain ⟨e,he,heps⟩ := Pi.exists_forall_pos_add_lt (x:=fun _ : I => (0:ℝ)) hslack
  let z : Fin n → ℝ := x+e • (x-y)
  have hz : z ∈ region a b := by
    intro i
    change a i (x+e • (x-y)) ≤ b i
    rw [map_add,map_smul]
    simp only [smul_eq_mul]
    by_cases hi : a i x=b i
    · have hiy : a i y=b i := hactive hi
      simp [map_sub,hi,hiy]
    · have hd : 0 < |a i (x-y)|+1 := by positivity
      have hh : e*(|a i (x-y)|+1) < b i-a i x :=
        (lt_div_iff₀ hd).mp (by simpa using heps ⟨i,hi⟩)
      have hm := mul_le_mul_of_nonneg_left (le_abs_self (a i (x-y))) he.le
      nlinarith
  have hd : 0 < 1+e := by linarith
  have hc : e/(1+e)+1/(1+e)=(1:ℝ) := by field_simp; ring
  have hseg : x ∈ openSegment ℝ y z := by
    refine ⟨e/(1+e),1/(1+e),div_pos he hd,one_div_pos.mpr hd,hc,?_⟩
    ext i
    change e/(1+e)*y i+1/(1+e)*(x i+e*(x i-y i))=x i
    field_simp
    ring
  exact (hx.2 hy hz hseg).symm

theorem extreme_active_injective (a : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    Set.InjOn (active a b) (Set.extremePoints ℝ (region a b)) := by
  intro x hx y hy he
  exact active_determines_extreme a b hx hy.1 (le_of_eq he)

theorem finite_extreme_region (a : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    (Set.extremePoints ℝ (region a b)).Finite := by
  exact Set.finite_univ.of_injOn (fun _ _ => Set.mem_univ _) (extreme_active_injective a b)

end Queelius.FiniteHalfspaces

end

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
namespace Queelius.SparseHalfspaces
open Matrix
open scoped ENNReal
variable {ι : Type*} [Fintype ι]

theorem signed_dot_le (u v : ι → ℝ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    u ⬝ᵥ v ≤ ∑ i, |v i| := by
  apply Finset.sum_le_sum
  intro i hi
  rcases hu i with h | h
  · simpa [h] using le_abs_self (v i)
  · simpa [h] using neg_le_abs (v i)

noncomputable def maximizingSign (v : ι → ℝ) (i : ι) : ℝ :=
  if 0 ≤ v i then 1 else -1

theorem maximizingSign_values (v : ι → ℝ) (i : ι) :
    maximizingSign v i = 1 ∨ maximizingSign v i = -1 := by
  unfold maximizingSign
  split_ifs <;> simp

theorem maximizingSign_dot (v : ι → ℝ) : maximizingSign v ⬝ᵥ v = ∑ i, |v i| := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : 0 ≤ v i
  · simp [maximizingSign, h, abs_of_nonneg h]
  · simp [maximizingSign, h, abs_of_neg (lt_of_not_ge h)]

theorem sum_abs_le_iff (v : ι → ℝ) (σ : ℝ) :
    (∑ i, |v i|) ≤ σ ↔ ∀ u : ι → ℝ, (∀ i, u i = 1 ∨ u i = -1) → u ⬝ᵥ v ≤ σ := by
  constructor
  · intro h u hu
    exact (signed_dot_le u v hu).trans h
  · intro h
    simpa only [maximizingSign_dot] using h (maximizingSign v) (maximizingSign_values v)

theorem qNorm_one {m : ℕ} (v : Fin m → ℝ) : SparseLpLq.SmallP.qNorm 1 v = ∑ i, |v i| := by
  simp [SparseLpLq.SmallP.qNorm, PiLp.norm_eq_of_L1, Real.norm_eq_abs]

theorem feasible_halfspaces {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (σ : ℝ) :
    SparseLpLq.SmallP.FEA A b σ 1 =
      {x | ∀ u : Fin m → ℝ, (∀ i, u i = 1 ∨ u i = -1) → u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b + σ} := by
  ext x
  change SparseLpLq.SmallP.qNorm 1 (A *ᵥ x - b) ≤ σ ↔ _
  rw [qNorm_one, sum_abs_le_iff]
  constructor
  · intro h u hu
    have hh := h u hu
    rw [dotProduct_sub] at hh
    linarith
  · intro h u hu
    rw [dotProduct_sub]
    have hh := h u hu
    linarith
end Queelius.SparseHalfspaces

open scoped ENNReal Matrix

theorem halfspace_solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) :
    SparseLpLq.SmallP.FEA A b σ 1 =
      {x | ∀ u : Fin m → ℝ, (∀ i, u i = 1 ∨ u i = -1) → u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b + σ} :=
  Queelius.SparseHalfspaces.feasible_halfspaces A b σ

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
theorem orthant_solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (s : Fin n → Bool)
    (hne : (orthant s ∩ FEA A b σ 1).Nonempty)
    (x : Fin n → ℝ) (hx : x ∈ orthant s ∩ FEA A b σ 1)
    (hopt : ∀ y ∈ orthant s ∩ FEA A b σ 1, lpObj p x ≤ lpObj p y) :
    x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b σ 1) :=
  Queelius.SparseExtreme.orthant_piece_min_extreme A b σ p 1 hp s x hx hopt

end

section
namespace Queelius.SparseFinite
open SparseLpLq.SmallP Matrix
open scoped BigOperators ENNReal

def signVec {m : ℕ} (u : Fin m → Bool) (i : Fin m) : ℝ := if u i then 1 else -1

theorem signVec_values {m : ℕ} (u : Fin m → Bool) (i : Fin m) :
    signVec u i=1 ∨ signVec u i= -1 := by
  unfold signVec
  split <;> simp

theorem signVec_covers {m : ℕ} (v : Fin m → ℝ) (hv : ∀ i,v i=1 ∨ v i= -1) :
    ∃ u : Fin m → Bool,signVec u=v := by
  classical
  refine ⟨fun i => decide (v i=1),?_⟩
  funext i
  rcases hv i with hi | hi <;> norm_num [signVec,hi]

theorem feasible_bool_halfspaces {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) :
    FEA A b sigma 1 = {x | ∀ u : Fin m → Bool,
      signVec u ⬝ᵥ (A *ᵥ x) ≤ signVec u ⬝ᵥ b+sigma} := by
  rw [Queelius.SparseHalfspaces.feasible_halfspaces]
  ext x
  constructor
  · exact fun h u => h _ (signVec_values u)
  · intro h v hv
    obtain ⟨u,rfl⟩ := signVec_covers v hv
    exact h u

def signedMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin m → Bool) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := signVec u ⬝ᵥ (A *ᵥ x)
  map_add' x y := by simp [mulVec_add,dotProduct_add]
  map_smul' c x := by simp [mulVec_smul,dotProduct_smul]

def orthantMap {n : ℕ} (s : Fin n → Bool) (i : Fin n) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  (if s i then (-1:ℝ) else 1) • LinearMap.proj i

def constraints {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s : Fin n → Bool) :
    (Fin n ⊕ (Fin m → Bool)) → (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  Sum.elim (orthantMap s) (signedMap A)

def bounds {m n : ℕ} (b : Fin m → ℝ) (sigma : ℝ) :
    (Fin n ⊕ (Fin m → Bool)) → ℝ := Sum.elim (fun _ => 0) (fun u => signVec u ⬝ᵥ b+sigma)

theorem orthant_region {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) (s : Fin n → Bool) :
    orthant s ∩ FEA A b sigma 1 = Queelius.FiniteHalfspaces.region (constraints A s) (bounds b sigma) := by
  rw [feasible_bool_halfspaces]
  ext x
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Queelius.FiniteHalfspaces.region]
  change (x ∈ orthant s ∧ ∀ u,signVec u ⬝ᵥ (A *ᵥ x) ≤ signVec u ⬝ᵥ b+sigma) ↔
    ∀ i,constraints A s i x ≤ bounds b sigma i
  constructor
  · rintro ⟨ho,hf⟩ (i|u)
    · have h := ho i
      cases hi : s i <;> simpa [constraints,bounds,orthantMap,hi] using h
    · exact hf u
  · intro h
    constructor
    · intro i
      have hh := h (Sum.inl i)
      cases hi : s i <;> simpa [constraints,bounds,orthantMap,hi] using hh
    · exact fun u => h (Sum.inr u)

theorem finite_orthant_extremes {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) (s : Fin n → Bool) :
    (Set.extremePoints ℝ (orthant s ∩ FEA A b sigma 1)).Finite := by
  rw [orthant_region]
  exact Queelius.FiniteHalfspaces.finite_extreme_region _ _

end Queelius.SparseFinite

end

section
namespace Queelius.SparseFinite
open SparseLpLq.SmallP
open scoped ENNReal Matrix

def candidates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (sigma : ℝ) :
    Set (Fin n → ℝ) := ⋃ s : Fin n → Bool,Set.extremePoints ℝ (orthant s ∩ FEA A b sigma 1)

theorem candidates_finite {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) : (candidates A b sigma).Finite := by
  exact Set.finite_iUnion (finite_orthant_extremes A b sigma)

theorem solution_subset_candidates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) :
    SOL A b sigma p 1 ⊆ candidates A b sigma := by
  intro x hx
  obtain ⟨s,hs⟩ := Queelius.SparseExtreme.global_solution_in_orthant_extremes A b sigma p 1 hp x hx
  exact Set.mem_iUnion.mpr ⟨s,hs⟩

theorem finite_solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) :
    (SOL A b sigma p 1).Finite :=
  (candidates_finite A b sigma).subset (solution_subset_candidates A b sigma p hp)

theorem finite_all_solutions {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) :
    (⋃ p ∈ Set.Ioo (0:ℝ) 1,SOL A b sigma p 1).Finite := by
  apply (candidates_finite A b sigma).subset
  exact Set.iUnion_subset fun p => Set.iUnion_subset fun hp => solution_subset_candidates A b sigma p hp

theorem negative_radius_empty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) (hs : sigma < 0) : FEA A b sigma 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  change qNorm 1 (A *ᵥ x-b) ≤ sigma at hx
  rw [Queelius.SparseHalfspaces.qNorm_one] at hx
  exact (not_le_of_gt hs) ((Finset.sum_nonneg fun i _ => abs_nonneg ((A *ᵥ x-b) i)).trans hx)

theorem negative_radius_candidates_empty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) (hs : sigma < 0) : candidates A b sigma = ∅ := by
  simp [candidates,negative_radius_empty A b sigma hs]

theorem zero_dimensional_feasible_solution {m : ℕ} (A : Matrix (Fin m) (Fin 0) ℝ)
    (b : Fin m → ℝ) (sigma p : ℝ) (x : Fin 0 → ℝ) (hx : x ∈ FEA A b sigma 1) :
    SOL A b sigma p 1 = {x} := by
  ext y
  have h : y=x := Subsingleton.elim _ _
  subst y
  simp only [Set.mem_singleton_iff,iff_true]
  exact ⟨hx,fun z _ => by simp only [Subsingleton.elim z x,le_refl]⟩

end Queelius.SparseFinite
open SparseLpLq.SmallP
open scoped ENNReal Matrix

theorem finite_proposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b) :
    (∀ p ∈ Set.Ioo (0 : ℝ) 1, (SOL A b σ p 1).Finite) ∧
      (⋃ p ∈ Set.Ioo (0 : ℝ) 1, SOL A b σ p 1).Finite :=
  ⟨fun p hp => Queelius.SparseFinite.finite_solution A b σ p hp,
    Queelius.SparseFinite.finite_all_solutions A b σ⟩

end

section
namespace Queelius.SparseSmallP
open SparseLpLq.SmallP
open scoped BigOperators ENNReal Matrix

theorem lpObj_support_sum {n : ℕ} (p : ℝ) (x : Fin n → ℝ) :
    lpObj p x=∑ i ∈ Finset.univ.filter (fun i => x i≠0),|x i|^p := by
  classical
  by_cases hp : p=0
  · subst p
    simp [lpObj]
  · rw [lpObj,if_neg hp]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    have hz : x i=0 := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hn
    simp [hz,Real.zero_rpow hp]

theorem lp_curve_continuous {n : ℕ} (x : Fin n → ℝ) : Continuous (fun p : ℝ => lpObj p x) := by
  classical
  simp_rw [lpObj_support_sum]
  apply continuous_finsetSum
  intro i hi
  exact Real.continuous_const_rpow (abs_ne_zero.mpr (Finset.mem_filter.mp hi).2)

theorem support_minimizer {n : ℕ} (T : Set (Fin n → ℝ)) (hne : T.Nonempty) :
    ∃ x ∈ T,∀ y ∈ T,lpObj 0 x ≤ lpObj 0 y := by
  classical
  let card : (Fin n → ℝ) → ℕ := fun x => (Finset.univ.filter (fun i => x i≠0)).card
  have he : ∃ k : ℕ,∃ x ∈ T,card x=k := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨card x,x,hx,rfl⟩
  obtain ⟨x,hx,hc⟩ := Nat.find_spec he
  refine ⟨x,hx,?_⟩
  intro y hy
  have hmin := Nat.find_min' he (show ∃ x ∈ T,card x=card y from ⟨y,hy,rfl⟩)
  simp only [lpObj,if_pos rfl]
  change (card x : ℝ) ≤ (card y : ℝ)
  rw [hc]
  exact_mod_cast hmin

theorem zero_solution_exists {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) (q : ℝ≥0∞) (hne : (FEA A b sigma q).Nonempty) :
    (SOL A b sigma 0 q).Nonempty := by
  obtain ⟨x,hx,hm⟩ := support_minimizer (FEA A b sigma q) hne
  exact ⟨x,hx,hm⟩

end Queelius.SparseSmallP

end

section
namespace Queelius.SparseSmallP
open scoped Topology

theorem finite_candidate_threshold {α : Type*} (K : Set α) (hK : K.Finite)
    (cost : ℝ → α → ℝ) (hc : ∀ x,Continuous (fun p => cost p x)) (base : α) :
    ∃ delta ∈ Set.Ioc (0:ℝ) 1,∀ p ∈ Set.Ioo 0 delta,∀ x ∈ K,
      cost p x ≤ cost p base → cost 0 x ≤ cost 0 base := by
  have he (x : α) : ∀ᶠ p in nhds (0:ℝ),cost 0 base<cost 0 x → cost p base<cost p x := by
    by_cases hx : cost 0 base<cost 0 x
    · exact ((hc base).continuousAt.eventually_lt (hc x).continuousAt hx).mono (fun p hp _ => hp)
    · exact Filter.Eventually.of_forall (fun p hp => False.elim (hx hp))
  have hall : ∀ᶠ p in nhds (0:ℝ),∀ x ∈ K,cost 0 base<cost 0 x → cost p base<cost p x :=
    hK.eventually_all.mpr (fun x hx => he x)
  obtain ⟨e,he0,heall⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨min 1 e,⟨lt_min zero_lt_one he0,min_le_left _ _⟩,?_⟩
  intro p hp x hx hcost
  have hp0 : 0<p := hp.1
  have hpe : p<e := hp.2.trans_le (min_le_right _ _)
  have hdist : dist p (0:ℝ)<e := by simpa [Real.dist_eq,abs_of_pos hp0] using hpe
  exact le_of_not_gt (fun hbad => not_lt_of_ge hcost (heall hdist x hx hbad))

end Queelius.SparseSmallP

end

section
namespace Queelius.SparseSmallP
open SparseLpLq.SmallP
open scoped Topology

theorem lp_curve_analytic {n : ℕ} (x : Fin n → ℝ) (p : ℝ) :
    AnalyticAt ℝ (fun q => lpObj q x) p := by
  classical
  simp_rw [lpObj_support_sum]
  have hs : AnalyticAt ℝ (∑ i ∈ Finset.univ.filter (fun i => x i≠0),fun q : ℝ => |x i|^q) p := by
    apply Finset.analyticAt_sum
    intro i hi
    have hx : 0 < |x i| := abs_pos.mpr (Finset.mem_filter.mp hi).2
    simp_rw [Real.rpow_def_of_pos hx]
    exact (analyticAt_const.mul analyticAt_id).rexp'
  convert hs using 1
  funext q
  simp only [Finset.sum_apply]

theorem analytic_sign_right {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    (∀ᶠ p in 𝓝[>] (0:ℝ),f p=0) ∨
    (∀ᶠ p in 𝓝[>] (0:ℝ),0<f p) ∨ (∀ᶠ p in 𝓝[>] (0:ℝ),f p<0) := by
  by_cases hz : ∀ᶠ p in 𝓝 (0:ℝ),f p=0
  · exact Or.inl (hz.filter_mono nhdsWithin_le_nhds)
  obtain ⟨k,g,hg,hg0,heq⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
  have hp : ∀ᶠ p in 𝓝[>] (0:ℝ),0<p := self_mem_nhdsWithin
  have he : ∀ᶠ p in 𝓝[>] (0:ℝ),f p=(p-0)^k • g p := heq.filter_mono nhdsWithin_le_nhds
  rcases lt_or_gt_of_ne hg0 with hn | hn
  · right; right
    have hgneg : ∀ᶠ p in 𝓝 (0:ℝ),g p<0 := hg.continuousAt.eventually_lt_const hn
    filter_upwards [he,hp,hgneg.filter_mono nhdsWithin_le_nhds] with p he hp hgneg
    simpa [he,smul_eq_mul] using mul_neg_of_pos_of_neg (pow_pos hp k) hgneg
  · right; left
    have hgpos : ∀ᶠ p in 𝓝 (0:ℝ),0<g p := hg.continuousAt.eventually_const_lt hn
    filter_upwards [he,hp,hgpos.filter_mono nhdsWithin_le_nhds] with p he hp hgpos
    simpa [he,smul_eq_mul] using mul_pos (pow_pos hp k) hgpos

theorem analytic_order_eventually_constant {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    ∃ b : Prop,∀ᶠ p in 𝓝[>] (0:ℝ),(f p≤g p)↔b := by
  rcases analytic_sign_right (hf.sub hg) with he | hp | hn
  · exact ⟨True,he.mono (fun p h => by simp only [Pi.sub_apply] at h; simp only [iff_true]; linarith)⟩
  · exact ⟨False,hp.mono (fun p h => by simp only [Pi.sub_apply] at h; simp only [iff_false]; linarith)⟩
  · exact ⟨True,hn.mono (fun p h => by simp only [Pi.sub_apply] at h; simp only [iff_true]; linarith)⟩

end Queelius.SparseSmallP

end

section
namespace Queelius.SparseSmallP
open SparseLpLq.SmallP Queelius.SparseFinite
open scoped Matrix ENNReal

theorem small_p_inclusion {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (sigma : ℝ) (hne : (FEA A b sigma 1).Nonempty) :
    ∃ pstar ∈ Set.Ioc (0:ℝ) 1,∀ p ∈ Set.Ioo 0 pstar,SOL A b sigma p 1 ⊆ SOL A b sigma 0 1 := by
  obtain ⟨base,hbase⟩ := zero_solution_exists A b sigma 1 hne
  obtain ⟨delta,hdelta,hth⟩ := finite_candidate_threshold (candidates A b sigma)
    (candidates_finite A b sigma) (fun p x => lpObj p x) lp_curve_continuous base
  refine ⟨delta,hdelta,?_⟩
  intro p hp x hx
  have hp1 : p ∈ Set.Ioo (0:ℝ) 1 := ⟨hp.1,hp.2.trans_le hdelta.2⟩
  have hxK := solution_subset_candidates A b sigma p hp1 hx
  have h0 := hth p hp x hxK (hx.2 base hbase.1)
  exact ⟨hx.1,fun y hy => h0.trans (hbase.2 y hy)⟩

theorem first_root_conclusion {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b) :
    ∃ pstar ∈ Set.Ioc (0:ℝ) 1,∀ p ∈ Set.Ioo 0 pstar,SOL A b σ p 1 ⊆ SOL A b σ 0 1 :=
  small_p_inclusion A b σ hfeas

end Queelius.SparseSmallP

end

section
namespace Queelius.SparseSmallP
open scoped Topology

theorem finite_analytic_order_stable {α : Type*} (K : Set α) (hK : K.Finite)
    (cost : ℝ → α → ℝ) (ha : ∀ x,AnalyticAt ℝ (fun p => cost p x) 0) :
    ∃ delta>0,∀ p∈Set.Ioc 0 delta,∀ q∈Set.Ioc 0 delta,∀ x∈K,∀ y∈K,
      (cost p x≤cost p y ↔ cost q x≤cost q y) := by
  classical
  choose b hb using fun x y => analytic_order_eventually_constant (ha x) (ha y)
  have hall : ∀ᶠ p in 𝓝[>] (0:ℝ),∀ x∈K,∀ y∈K,(cost p x≤cost p y)↔b x y :=
    hK.eventually_all.mpr (fun x hx => hK.eventually_all.mpr (fun y hy => hb x y))
  obtain ⟨delta,hdelta,hh⟩ := (nhdsGT_basis_Ioc (0:ℝ)).eventually_iff.mp hall
  refine ⟨delta,hdelta,fun p hp q hq x hx y hy => ?_⟩
  exact (hh hp x hx y hy).trans (hh hq x hx y hy).symm

end Queelius.SparseSmallP

end

section
namespace Queelius.SparseSmallP.Controls
open SparseLpLq.SmallP

theorem zero_and_nonzero_coordinate (p : ℝ) : lpObj p ![(0:ℝ),2]=(2:ℝ)^p := by
  rw [lpObj_support_sum]
  norm_num [Fin.sum_univ_two,Finset.sum_filter]

theorem moving_candidates_counterexample :
    (∀ x : ℝ,Continuous (fun p : ℝ => (x-p)^2)) ∧
    ∀ delta : ℝ,0<delta → ∃ p ∈ Set.Ioo 0 delta,
      (∀ x : ℝ,(p-p)^2 ≤ (x-p)^2) ∧ 0<p^2 := by
  constructor
  · intro x; fun_prop
  · intro delta hd
    refine ⟨delta/2,⟨by linarith,by linarith⟩,?_,?_⟩
    · intro x
      simpa only [sub_self,zero_pow (by decide : 2≠0)] using sq_nonneg (x-delta/2)
    · exact pow_pos (by linarith) _

end Queelius.SparseSmallP.Controls

end

section
namespace Queelius.SparseSmallP
open SparseLpLq.SmallP
open scoped Matrix ENNReal

theorem lp_continuous_vector {n : ℕ} (p : ℝ) (hp : 0<p) :
    Continuous (lpObj (n:=n) p) := by
  change Continuous (fun x : Fin n → ℝ => lpObj p x)
  simp only [lpObj,if_neg (ne_of_gt hp)]
  apply continuous_finsetSum
  intro i hi
  exact (Real.continuous_rpow_const hp.le).comp (continuous_apply i).abs

theorem lp_nonneg {n : ℕ} (p : ℝ) (hp : 0<p) (x : Fin n → ℝ) : 0≤lpObj p x := by
  simp only [lpObj,if_neg (ne_of_gt hp)]
  exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)

theorem lp_coordinate_bound {n : ℕ} (p : ℝ) (hp : 0<p) (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ (lpObj p x)^p⁻¹ := by
  apply (Real.le_rpow_inv_iff_of_pos (abs_nonneg _) (lp_nonneg p hp x) hp).mpr
  simp only [lpObj,if_neg (ne_of_gt hp)]
  exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)

theorem compact_lp_sublevel {n : ℕ} (p : ℝ) (hp : 0<p) (r : ℝ) :
    IsCompact {x : Fin n → ℝ | lpObj p x ≤ r} := by
  have hc : IsClosed {x : Fin n → ℝ | lpObj p x ≤ r} :=
    isClosed_le (lp_continuous_vector p hp) continuous_const
  by_cases hr : 0≤r
  · apply isCompact_Icc.of_isClosed_subset hc
    intro x hx
    have hcoord : ∀ i,|x i|≤r^p⁻¹ := fun i =>
      (lp_coordinate_bound p hp x i).trans (Real.rpow_le_rpow (lp_nonneg p hp x) hx (inv_nonneg.mpr hp.le))
    exact ⟨fun i => (abs_le.mp (hcoord i)).1,fun i => (abs_le.mp (hcoord i)).2⟩
  · have he : {x : Fin n → ℝ | lpObj p x ≤ r}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hr ((lp_nonneg p hp x).trans hx)
    rw [he]
    exact isCompact_empty

theorem positive_minimizer_exists {n : ℕ} (T : Set (Fin n → ℝ))
    (hT : IsClosed T) (hne : T.Nonempty) (p : ℝ) (hp : 0<p) :
    ∃ x∈T,∀ y∈T,lpObj p x≤lpObj p y := by
  obtain ⟨base,hbase⟩ := hne
  let K := T∩{x | lpObj p x≤lpObj p base}
  have hK : IsCompact K := (compact_lp_sublevel p hp (lpObj p base)).inter_left hT
  have hbaseK : base∈K := ⟨hbase,show lpObj p base≤lpObj p base from le_rfl⟩
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn ⟨base,hbaseK⟩ (lp_continuous_vector p hp).continuousOn
  refine ⟨x,hx.1,fun y hy => ?_⟩
  by_cases hle : lpObj p y≤lpObj p base
  · exact hmin ⟨hy,hle⟩
  · exact hx.2.trans (le_of_not_ge hle)

theorem feasible_closed {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) : IsClosed (FEA A b sigma 1) := by
  unfold FEA
  simp_rw [Queelius.SparseHalfspaces.qNorm_one]
  apply isClosed_le _ continuous_const
  simp only [Matrix.mulVec,dotProduct,Pi.sub_apply]
  fun_prop

theorem positive_solution_exists {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma p : ℝ) (hp : 0<p) (hne : (FEA A b sigma 1).Nonempty) :
    (SOL A b sigma p 1).Nonempty := by
  obtain ⟨x,hx,hm⟩ := positive_minimizer_exists _ (feasible_closed A b sigma) hne p hp
  exact ⟨x,hx,hm⟩

end Queelius.SparseSmallP

end

section
namespace Queelius.SparseSmallP
open SparseLpLq.SmallP Queelius.SparseFinite
open scoped Matrix ENNReal

theorem candidates_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) : candidates A b sigma ⊆ FEA A b sigma 1 := by
  intro x hx
  obtain ⟨s,hs⟩ := Set.mem_iUnion.mp hx
  exact (extremePoints_subset hs).2

theorem solution_iff_candidates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma p : ℝ) (hp : p∈Set.Ioo (0:ℝ) 1)
    (hne : (FEA A b sigma 1).Nonempty) (x : Fin n → ℝ) :
    x∈SOL A b sigma p 1 ↔ x∈candidates A b sigma ∧
      ∀ y∈candidates A b sigma,lpObj p x≤lpObj p y := by
  constructor
  · intro hx
    exact ⟨solution_subset_candidates A b sigma p hp hx,
      fun y hy => hx.2 y (candidates_feasible A b sigma hy)⟩
  · rintro ⟨hx,hm⟩
    obtain ⟨z,hz⟩ := positive_solution_exists A b sigma p hp.1 hne
    exact ⟨candidates_feasible A b sigma hx,fun y hy =>
      (hm z (solution_subset_candidates A b sigma p hp hz)).trans (hz.2 y hy)⟩

theorem eventual_solution_equality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) (hne : (FEA A b sigma 1).Nonempty)
    (cap : ℝ) (hc0 : 0<cap) (hc1 : cap≤1) :
    ∃ pbar∈Set.Ioo 0 cap,∀ p∈Set.Ioc 0 pbar,SOL A b sigma p 1=SOL A b sigma pbar 1 := by
  obtain ⟨delta,hd,hh⟩ := finite_analytic_order_stable (candidates A b sigma)
    (candidates_finite A b sigma) (fun p x => lpObj p x) (fun x => lp_curve_analytic x 0)
  let pbar := min delta (cap/2)
  have hb0 : 0<pbar := lt_min hd (half_pos hc0)
  have hbc : pbar<cap := (min_le_right _ _).trans_lt (half_lt_self hc0)
  have hbd : pbar≤delta := min_le_left _ _
  have hb1 : pbar<1 := hbc.trans_le hc1
  refine ⟨pbar,⟨hb0,hbc⟩,?_⟩
  intro p hp
  ext x
  rw [solution_iff_candidates A b sigma p ⟨hp.1,hp.2.trans_lt hb1⟩ hne,
    solution_iff_candidates A b sigma pbar ⟨hb0,hb1⟩ hne]
  constructor
  · rintro ⟨hx,hm⟩
    exact ⟨hx,fun y hy => (hh p ⟨hp.1,hp.2.trans hbd⟩ pbar ⟨hb0,hbd⟩ x hx y hy).mp (hm y hy)⟩
  · rintro ⟨hx,hm⟩
    exact ⟨hx,fun y hy => (hh p ⟨hp.1,hp.2.trans hbd⟩ pbar ⟨hb0,hbd⟩ x hx y hy).mpr (hm y hy)⟩

theorem complete_theorem_2_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (sigma : ℝ) (hne : (FEA A b sigma 1).Nonempty) :
    ∃ pstar∈Set.Ioc (0:ℝ) 1,
      (∀ p∈Set.Ioo 0 pstar,SOL A b sigma p 1 ⊆ SOL A b sigma 0 1) ∧
      ∃ pbar∈Set.Ioo 0 pstar,∀ p∈Set.Ioc 0 pbar,SOL A b sigma p 1=SOL A b sigma pbar 1 := by
  obtain ⟨pstar,hp,hincl⟩ := small_p_inclusion A b sigma hne
  exact ⟨pstar,hp,hincl,eventual_solution_equality A b sigma hne pstar hp.1 hp.2⟩

end Queelius.SparseSmallP
open SparseLpLq.SmallP
open scoped Matrix ENNReal

theorem submission_primary_solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b) :
    ∃ pstar ∈ Set.Ioc (0 : ℝ) 1,
      (∀ p ∈ Set.Ioo 0 pstar, SOL A b σ p 1 ⊆ SOL A b σ 0 1) ∧
        ∃ pbar ∈ Set.Ioo 0 pstar, ∀ p ∈ Set.Ioc 0 pbar, SOL A b σ p 1 = SOL A b σ pbar 1 :=
  Queelius.SparseSmallP.complete_theorem_2_2 A b σ hfeas

end

section
namespace Queelius.SparseSmallP.Controls
open SparseLpLq.SmallP

theorem tied_first_log_moment : logMoment 1 ![(1:ℝ),4]=logMoment 1 ![(2:ℝ),2] := by
  have hl : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    ring
  norm_num [logMoment,Fin.sum_univ_two,Finset.sum_filter,hl]
  ring

theorem tied_moment_cost_difference (p : ℝ) :
    lpObj p ![(1:ℝ),4]-lpObj p ![(2:ℝ),2]=((2:ℝ)^p-1)^2 := by
  have hr : (4:ℝ)^p=(2:ℝ)^p*(2:ℝ)^p := by
    rw [show (4:ℝ)=2*2 by norm_num,Real.mul_rpow (by norm_num) (by norm_num)]
  simp only [lpObj_support_sum]
  norm_num [Fin.sum_univ_two,Finset.sum_filter,hr]
  ring

theorem tied_moment_strict_order (p : ℝ) (hp : 0<p) :
    lpObj p ![(2:ℝ),2]<lpObj p ![(1:ℝ),4] := by
  have h := Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hp
  have hsq : 0<((2:ℝ)^p-1)^2 := sq_pos_of_pos (sub_pos.mpr h)
  rw [← tied_moment_cost_difference] at hsq
  linarith

theorem zero_sublevel_unbounded :
    {x : Fin 1 → ℝ | lpObj 0 x ≤ 1}=Set.univ := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true,lpObj,↓reduceIte]
  have h : (Finset.univ.filter (fun i : Fin 1 => x i≠0)).card≤1 := by
    simpa using Finset.card_filter_le (s:=Finset.univ) (p:=fun i : Fin 1 => x i≠0)
  exact_mod_cast h

end Queelius.SparseSmallP.Controls

end


theorem solution : (
  ∀ {m n : Nat} (A : Matrix (Fin m) (Fin n) Real) (b : Fin m → Real) (σ : Real),
    @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) σ →
      @Set.Nonempty (Fin n → Real)
          (@SparseLpLq.SmallP.FEA m n A b σ (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne))) →
        @LT.lt Real Real.instLT σ
            (@SparseLpLq.SmallP.qNorm m (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne)) b) →
          And
            (∀ (p : Real),
              @Membership.mem Real (Set Real) (@Set.instMembership Real)
                  (@Set.Ioo Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                  p →
                @Set.Finite (Fin n → Real)
                  (@SparseLpLq.SmallP.SOL m n A b σ p
                    (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne))))
            (@Set.Finite (Fin n → Real)
              (@Set.iUnion (Fin n → Real) Real fun (p : Real) =>
                @Set.iUnion (Fin n → Real)
                  (@Membership.mem Real (Set Real) (@Set.instMembership Real)
                    (@Set.Ioo Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                      (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                    p)
                  fun
                    (h :
                      @Membership.mem Real (Set Real) (@Set.instMembership Real)
                        (@Set.Ioo Real Real.instPreorder
                          (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
                          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                        p) =>
                  @SparseLpLq.SmallP.SOL m n A b σ p
                    (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne))))
) := @finite_proposition
