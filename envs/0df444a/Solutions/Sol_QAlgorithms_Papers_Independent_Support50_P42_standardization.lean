-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.standardization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:49:31.037993+00:00
-- url     : https://prove2.me/submissions/a1fb613a-ef0c-4f93-b30a-9ff743cc4226

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== P42ST =====

noncomputable section

open scoped BigOperators Matrix ComplexConjugate
open MeasureTheory ProbabilityTheory
open QAlgorithms QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50.P42
open Information100.P21 (Op Vec FiniteLOCC)
open Dependency50.P42 (dimensionedPower singlets)
open Next46.P39 (rectAct)

namespace X4P42S
open Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

lemma conj_pure {I : Type*} [Fintype I] (A : Matrix I I ℂ) (v : EuclideanSpace ℂ I) :
    conjSuperop A (pureDensity v) = pureDensity (WithLp.toLp 2 (A *ᵥ (WithLp.ofLp v))) := by
  ext p q
  simp only [conjSuperop, pureDensity, Matrix.mul_apply, Matrix.of_apply, conjTranspose_apply,
    PiLp.toLp_apply, mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- the scaled singlet coefficient matrix [[0,1],[-1,0]] -/
def t : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

lemma t_unit (a c : Fin 2) : ∑ b, t a b * conj (t c b) = if a = c then 1 else 0 := by
  fin_cases a <;> fin_cases c <;> simp [t, Fin.sum_univ_two]

def e (ell : ℕ) := Dependency50.P42.copyIndex 2 ell

def U (ell : ℕ) : Matrix (Fin (2^ell)) (Fin (2^ell)) ℂ :=
  fun a b => ∏ i, t ((e ell).symm a i) ((e ell).symm b i)

lemma U_mem (ell : ℕ) : U ell ∈ Matrix.unitaryGroup (Fin (2^ell)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a c
  simp only [Matrix.mul_apply, star_apply, U, RCLike.star_def, map_prod]
  rw [← (e ell).sum_comp]
  simp only [Equiv.symm_apply_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => t ((e ell).symm a i) b * conj (t ((e ell).symm c i) b))]
  simp_rw [t_unit]
  rw [Matrix.one_apply]
  by_cases h : a = c
  · subst h; simp
  · have : ∃ i, (e ell).symm a i ≠ (e ell).symm c i := by
      by_contra hc; push Not at hc
      exact h ((e ell).symm.injective (funext hc))
    obtain ⟨i, hi⟩ := this
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma singlet_coef (x y : Fin 2) :
    Dependency50.P42.singletVector (x, y) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * t x y := by
  fin_cases x <;> fin_cases y <;> simp [Dependency50.P42.singletVector, t]

lemma uniform_apply (d : ℕ) (z : Fin d × Fin d) :
    uniformKet d z = if z.1 = z.2 then ((Real.sqrt (d : ℝ))⁻¹ : ℂ) else 0 := rfl

lemma last (ell : ℕ) :
    conjSuperop (Matrix.kronecker (U ell) (1 : Op (Fin (2^ell))))
        (pureDensity (uniformKet (2^ell))) = singlets ell := by
  rw [conj_pure]
  have hv : (WithLp.toLp 2 (Matrix.kronecker (U ell) (1 : Op (Fin (2^ell))) *ᵥ
      (WithLp.ofLp (uniformKet (2^ell)))) : EuclideanSpace ℂ _) =
      WithLp.toLp 2 (fun z : Fin (2^ell) × Fin (2^ell) =>
        ((Real.sqrt ((2:ℝ)^ell))⁻¹ : ℂ) * U ell z.1 z.2) := by
    congr 1
    funext z
    simp only [mulVec, dotProduct, Matrix.kronecker, kroneckerMap_apply, one_apply]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single z.2]
    · rw [Finset.sum_eq_single z.2]
      · simp [uniform_apply]; ring
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : z.2 = c
      · subst hc; simp [uniform_apply, Ne.symm hb, hb]
      · simp [hc]
    · simp
  rw [hv]
  ext p q
  simp only [pureDensity, Matrix.of_apply, PiLp.toLp_apply, singlets, dimensionedPower,
    Information100.P80.groupedPower, Dependency50.P42.singletState, U, map_mul, map_prod]
  simp only [singlet_coef, map_mul, Complex.conj_ofReal, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, e]
  have h1 : ((Real.sqrt ((2:ℝ)^ell))⁻¹ : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) ^ ell := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv]
    congr 1
    have hs : Real.sqrt ((2:ℝ)^ell) = Real.sqrt 2 ^ ell := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
        Real.mul_self_sqrt (by norm_num)]
    rw [hs, ← inv_pow]
    congr 1
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp; linarith
  rw [map_inv₀, Complex.conj_ofReal, h1]

lemma trim_kraus (D ell : ℕ) :
    (trim D ell)ᴴ*trim D ell+(trimFailure D ell)ᴴ*trimFailure D ell=1 := by
  ext j j'
  simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, trim, trimFailure,
    diagonal_apply, one_apply]
  by_cases hj : j.val < 2^ell
  · rw [Finset.sum_eq_single ⟨j.val, hj⟩]
    · rw [Finset.sum_eq_zero]
      · by_cases h : j = j'
        · subst h; simp
        · have : ¬ j.val = j'.val := fun h' => h (Fin.ext h')
          simp [this, h]
      · intro x _
        by_cases h : x = j
        · subst h; simp [hj]
        · simp [h, Ne.symm h]
    · intro b _ hb
      have : ¬ b.val = j.val := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  · rw [Finset.sum_eq_zero]
    · rw [Finset.sum_eq_single j]
      · by_cases h : j = j'
        · subst h; simp [hj]
        · simp [h, hj]
      · intro b _ hb; simp [Ne.symm hb, hb]
      · simp
    · intro i _
      have : ¬ i.val = j.val := fun h => hj (h ▸ i.2)
      simp [this]

lemma trim_branch (D ell : ℕ) (hlo : 2^ell ≤ D) (z : Fin (2^ell) × Fin (2^ell)) :
    rectAct (Matrix.kronecker (trim D ell) (trim D ell)) (uniformKet D) z =
      if z.1 = z.2 then ((Real.sqrt (D : ℝ))⁻¹ : ℂ) else 0 := by
  simp only [rectAct, PiLp.toLp_apply, mulVec, dotProduct, Matrix.kronecker, kroneckerMap_apply,
    trim]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single ⟨z.1.val, lt_of_lt_of_le z.1.2 hlo⟩]
  · rw [Finset.sum_eq_single ⟨z.2.val, lt_of_lt_of_le z.2.2 hlo⟩]
    · simp only [if_true, one_mul, uniform_apply]
      by_cases h : z.1 = z.2
      · simp [h]
      · have : ¬ (⟨z.1.val, lt_of_lt_of_le z.1.2 hlo⟩ : Fin D) = ⟨z.2.val, lt_of_lt_of_le z.2.2 hlo⟩ :=
          fun h' => h (Fin.ext (Fin.mk.inj h'))
        simp [h, this]
    · intro b _ hb
      have : ¬ z.2.val = b.val := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp
  · intro b _ hb
    have : ¬ z.1.val = b.val := fun h => hb (Fin.ext h.symm)
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [this]
  · simp

lemma trim_density (D ell : ℕ) (hlo : 2^ell ≤ D) :
    pureDensity (rectAct (Matrix.kronecker (trim D ell) (trim D ell)) (uniformKet D))=
      (((2 : ℝ)^ell/D : ℝ) : ℂ) • pureDensity (uniformKet (2^ell)) := by
  have hD : (0 : ℝ) < D := by
    have : (0:ℝ) < (2:ℝ)^ell := by positivity
    exact lt_of_lt_of_le this (by exact_mod_cast hlo)
  ext z w
  simp only [pureDensity, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [trim_branch D ell hlo z, trim_branch D ell hlo w, uniform_apply, uniform_apply]
  split_ifs <;> simp
  have h2 : (0 : ℝ) < ((2^ell : ℕ) : ℝ) := by positivity
  rw [← mul_inv, ← mul_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt hD.le,
    Real.mul_self_sqrt (by positivity)]
  have : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  field_simp

theorem main (D ell : ℕ) (hD : 0<D) (epsilon : ℝ)
    (he : 0<epsilon) (hlo : 2^ell≤D)
    (hhi : (D : ℝ)<(1+epsilon)*(2 : ℝ)^ell) :
    (trim D ell)ᴴ*trim D ell+(trimFailure D ell)ᴴ*trimFailure D ell=1 ∧
    pureDensity (rectAct (Matrix.kronecker (trim D ell) (trim D ell)) (uniformKet D))=
      (((2 : ℝ)^ell/D : ℝ) : ℂ) • pureDensity (uniformKet (2^ell)) ∧
    1-epsilon<(2 : ℝ)^ell/D ∧
    0≤1-(2 : ℝ)^ell/D ∧ 1-(2 : ℝ)^ell/D<epsilon ∧
    ∃ U V : Matrix.unitaryGroup (Fin (2^ell)) ℂ,
      conjSuperop (Matrix.kronecker (U : Op (Fin (2^ell))) (V : Op (Fin (2^ell))))
        (pureDensity (uniformKet (2^ell)))=singlets ell := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hlo' : (2 : ℝ)^ell ≤ D := by exact_mod_cast hlo
  have hp : (0 : ℝ) < (2 : ℝ)^ell := by positivity
  have hc : 1-epsilon<(2 : ℝ)^ell/D := by
    rw [lt_div_iff₀ hDr]
    nlinarith [mul_pos he he, mul_pos he hp]
  refine ⟨trim_kraus D ell, trim_density D ell hlo, hc, ?_, by linarith, ?_⟩
  · rw [sub_nonneg, div_le_one hDr]; exact hlo'
  · refine ⟨⟨U ell, U_mem ell⟩, 1, ?_⟩
    simpa using last ell

end X4P42S

theorem solution (D ell : ℕ) (hD : 0<D) (epsilon : ℝ)
    (he : 0<epsilon) (hlo : 2^ell≤D)
    (hhi : (D : ℝ)<(1+epsilon)*(2 : ℝ)^ell) :
    (trim D ell)ᴴ*trim D ell+(trimFailure D ell)ᴴ*trimFailure D ell=1 ∧
    pureDensity (rectAct (Matrix.kronecker (trim D ell) (trim D ell)) (uniformKet D))=
      (((2 : ℝ)^ell/D : ℝ) : ℂ) • pureDensity (uniformKet (2^ell)) ∧
    1-epsilon<(2 : ℝ)^ell/D ∧
    0≤1-(2 : ℝ)^ell/D ∧ 1-(2 : ℝ)^ell/D<epsilon ∧
    ∃ U V : Matrix.unitaryGroup (Fin (2^ell)) ℂ,
      conjSuperop (Matrix.kronecker (U : Op (Fin (2^ell))) (V : Op (Fin (2^ell))))
        (pureDensity (uniformKet (2^ell)))=singlets ell :=
  X4P42S.main D ell hD epsilon he hlo hhi

#print axioms solution
