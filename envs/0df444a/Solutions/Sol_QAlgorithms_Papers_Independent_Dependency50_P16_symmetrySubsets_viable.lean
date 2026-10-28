-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.symmetrySubsets_viable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:24:32.608023+00:00
-- url     : https://prove2.me/submissions/87e55715-6701-447a-94b1-c563a99a72b2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

def S200V_R {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k, Complex.normSq (V k i j)

theorem S200V_exists_U {n r : ℕ} (hn : 2 ≤ n) (V : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) :
    ∃ U, specialUnitary U ∧ ∀ i j, rates V U i j = S200V_R V (σ⁻¹ i) (σ⁻¹ j) := by
  let i0 : Fin n := ⟨0, by omega⟩
  let d : Fin n → ℂ := fun i => if i = i0 then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 1
  have hd : ∀ i, star (d i) * d i = 1 := by
    intro i
    simp only [d]
    split_ifs
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · simp
  have hd' : ∀ i, Complex.normSq (d i) = 1 := by
    intro i
    have := hd i
    rw [Complex.star_def, mul_comm, Complex.mul_conj] at this
    exact_mod_cast this
  refine ⟨σ.permMatrix ℂ * Matrix.diagonal d, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_permMatrix,
      Matrix.diagonal_conjTranspose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (σ⁻¹.permMatrix ℂ), ← Matrix.permMatrix_mul]
    simp only [mul_inv_cancel, Matrix.permMatrix_one, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact hd i
  · rw [Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal]
    rw [Finset.prod_eq_single i0]
    · simp only [d, if_pos rfl]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · intro b _ hb; simp [d, hb]
    · simp
  · intro i j
    unfold rates S200V_R
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_permMatrix, Matrix.diagonal_conjTranspose]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (σ⁻¹.permMatrix ℂ),
      ← Matrix.mul_assoc (σ⁻¹.permMatrix ℂ * V k)]
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp only [Matrix.submatrix_apply, id, map_mul, hd']
    simp [hd']

theorem S200V_exists_A {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) (τ : Equiv.Perm (Fin n)) :
    ∃ A ∈ fields D, ∀ x : Fin n → ℝ, A *ᵥ x = fun i =>
      ∑ j, S200V_R D.jump (τ i) (τ j) * x j - (∑ k, S200V_R D.jump (τ k) (τ i)) * x i := by
  obtain ⟨U, hU, hr⟩ := S200V_exists_U hn D.jump τ⁻¹
  refine ⟨populationGenerator D.jump U, ⟨U, hU, rfl⟩, fun x => ?_⟩
  funext i
  simp only [inv_inv] at hr
  unfold populationGenerator
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
  simp only [Matrix.mulVec, dotProduct, hr]

theorem S200V_f_inv {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    ∑ τ : Equiv.Perm (Fin n), R (τ (π i)) (τ (π j)) = ∑ τ : Equiv.Perm (Fin n), R (τ i) (τ j) := by
  exact Equiv.sum_comp (Equiv.mulRight π) (fun τ : Equiv.Perm (Fin n) => R (τ i) (τ j))

theorem S200V_trans {n : ℕ} (i0 i1 i j : Fin n) (h01 : i0 ≠ i1) (hij : i ≠ j) :
    ∃ π : Equiv.Perm (Fin n), π i0 = i ∧ π i1 = j := by
  let s := Equiv.swap i0 i
  have hs : s i1 ≠ i := by
    intro h; apply h01; apply s.injective; rw [h]; simp [s]
  refine ⟨Equiv.swap (s i1) j * s, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    have : s i0 = i := by simp [s]
    rw [this, Equiv.swap_apply_of_ne_of_ne (Ne.symm hs) hij]
  · simp [Equiv.Perm.mul_apply]

theorem S200V_avg {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Fin n → ℝ, ∑ i, x i = 1 →
      (-c) • (x - barycenter n) ∈ convexHull ℝ (derivatives D x) := by
  choose A hA hAx using S200V_exists_A hn D
  set R := S200V_R D.jump with hRdef
  let f : Fin n → Fin n → ℝ := fun i j => ∑ τ : Equiv.Perm (Fin n), R (τ i) (τ j)
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set α := f i0 i1 with hα
  have hf : ∀ i j, i ≠ j → f i j = α := by
    intro i j hij
    obtain ⟨π, h1, h2⟩ := S200V_trans i0 i1 i j h01 hij
    rw [hα, ← h1, ← h2]
    exact S200V_f_inv R π i0 i1
  have hR0 : ∀ i j, 0 ≤ R i j := fun i j =>
    Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  have hα0 : 0 ≤ α := Finset.sum_nonneg fun τ _ => hR0 _ _
  set N : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨n * α / N, by positivity, fun x hx => ?_⟩
  have hsum : ∀ i, ∑ τ, (A τ *ᵥ x) i = α * (1 - n * x i) := by
    intro i
    have e : ∑ τ, (A τ *ᵥ x) i = ∑ j, (f i j * x j - f j i * x i) := by
      simp only [hAx, f, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_comm
    rw [e]
    have : ∀ j, f i j * x j - f j i * x i = α * (x j - x i) := by
      intro j
      by_cases hji : j = i
      · subst hji; ring
      · have e1 := hf i j (Ne.symm hji)
        have e2 := hf j i hji
        rw [e1, e2]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hx]
    simp
  have hmem : Finset.univ.centerMass (fun _ => (1 : ℝ)) (fun τ => A τ *ᵥ x) ∈
      convexHull ℝ (derivatives D x) :=
    Finset.univ.centerMass_mem_convexHull (fun _ _ => zero_le_one)
      (by simpa using Fintype.card_pos) (fun τ _ => ⟨A τ, hA τ, rfl⟩)
  convert hmem using 1
  funext i
  simp only [Finset.centerMass, one_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Pi.smul_apply, Finset.sum_apply, hsum, Pi.sub_apply, barycenter, smul_eq_mul]
  rw [← hN]
  field_simp
  ring

theorem S200V_bsum {n : ℕ} (hn : 2 ≤ n) : ∑ i : Fin n, barycenter n i = 1 := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp [barycenter, this]

theorem S200V_path {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x₀ ∈ simplex n, relaxedSolution D (Set.Ici 0)
      (fun t => barycenter n + Real.exp (-c * t) • (x₀ - barycenter n)) := by
  obtain ⟨c, hc, hmem⟩ := S200V_avg hn D
  refine ⟨c, hc, fun x₀ hx₀ => ?_⟩
  have hb := S200V_bsum hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsum : ∀ t : ℝ, ∑ i, (barycenter n + Real.exp (-c * t) • (x₀ - barycenter n)) i = 1 := by
    intro t
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hb, hx₀.2]
    ring
  refine ⟨fun t ht => ⟨fun i => ?_, hsum t⟩, fun t => (-c * Real.exp (-c * t)) • (x₀ - barycenter n),
    fun t _ => ⟨?_, ?_⟩, Filter.Eventually.of_forall fun t => ?_⟩
  · have he : Real.exp (-c * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ t := ht
      nlinarith
    have he0 := (Real.exp_pos (-c * t)).le
    have hxi := hx₀.1 i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, barycenter]
    have hinv : 0 ≤ (n : ℝ)⁻¹ := by positivity
    nlinarith [mul_nonneg he0 hxi, mul_nonneg (sub_nonneg.2 he) hinv]
  · exact (Continuous.smul (f := fun t : ℝ => -c * Real.exp (-c * t)) (by fun_prop)
      continuous_const).intervalIntegrable _ _
  · rw [intervalIntegral.integral_smul_const]
    have hI : ∫ s in (0:ℝ)..t, -c * Real.exp (-c * s) = Real.exp (-c * t) - 1 := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
        (f := fun s => Real.exp (-c * s)) (f' := fun s => -c * Real.exp (-c * s))
        (fun s _ => by
          have h := ((hasDerivAt_id s).const_mul (-c)).exp
          exact h.congr_deriv (by simp only [id]; ring))
        ((Continuous.intervalIntegrable (by fun_prop) _ _))
      rw [this]; simp
    rw [hI]
    simp only [mul_zero, Real.exp_zero, one_smul]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · have := hmem _ (hsum t)
    convert this using 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

theorem S200V_main {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    (∀ H : Subgroup (Equiv.Perm (Fin n)),
      viable D {x | x ∈ simplex n ∧ ∀ p ∈ H, ∀ i, x (p i) = x i}) ∧
    viable D (chamber n) ∧
    (∀ p : Equiv.Perm (Fin n), viable D {x | ∃ y ∈ chamber n, x = fun i => y (p i)}) := by
  obtain ⟨c, hc, hP⟩ := S200V_path hn D
  have anti : ∀ y : Fin n → ℝ, Antitone y → ∀ t : ℝ,
      Antitone (barycenter n + Real.exp (-c * t) • (y - barycenter n)) := by
    intro y hy t i j hij
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, barycenter]
    have := hy hij
    have he := Real.exp_pos (-c * t)
    nlinarith
  refine ⟨fun H x hx => ⟨_, hP x hx.1, by simp, fun t ht => ⟨(hP x hx.1).1 t ht, fun p hp i => ?_⟩⟩,
    fun x hx => ⟨_, hP x hx.1, by simp, fun t ht => ⟨(hP x hx.1).1 t ht, anti x hx.2 t⟩⟩,
    fun p x hx => ?_⟩
  · simp [barycenter, hx.2 p hp i]
  · obtain ⟨y, hy, rfl⟩ := hx
    have hs : (fun i => y (p i)) ∈ simplex n :=
      ⟨fun i => hy.1.1 _, by rw [Equiv.sum_comp p y]; exact hy.1.2⟩
    refine ⟨_, hP _ hs, by simp, fun t ht => ⟨_, ⟨(hP y hy.1).1 t ht, anti y hy.2 t⟩, ?_⟩⟩
    funext i
    simp [barycenter]

end QAlgorithms.Papers.Independent.Dependency50.P16

open QAlgorithms.Papers.Independent.Dependency50.P16 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    (∀ H : Subgroup (Equiv.Perm (Fin n)),
      viable D {x | x ∈ simplex n ∧ ∀ p ∈ H, ∀ i, x (p i) = x i}) ∧
    viable D (chamber n) ∧
    (∀ p : Equiv.Perm (Fin n), viable D {x | ∃ y ∈ chamber n, x = fun i => y (p i)}) :=
  S200V_main hn D


end
