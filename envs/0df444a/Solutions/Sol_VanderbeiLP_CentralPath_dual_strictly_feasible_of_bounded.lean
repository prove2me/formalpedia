-- Prove2me | solution 1 for VanderbeiLP.CentralPath.dual_strictly_feasible_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:02:02.009998+00:00
-- url     : https://prove2.me/submissions/c443ecdd-578a-43d1-85a2-0426502a3c0e

import Mathlib
import Definitions.Def_VanderbeiLP_CentralPath_BarrierProblem

open Matrix Filter Topology


namespace VanderbeiLP.CentralPath

lemma lin_decomp {k : ℕ} (φ : (Fin k → ℝ) →ₗ[ℝ] ℝ) (z : Fin k → ℝ) :
    φ z = ∑ j, z j * φ (Pi.single j 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ φ z]
  refine Finset.sum_congr rfl fun x _ => ?_
  have e : (fun j => if x = j then (1:ℝ) else 0) = Pi.single x 1 := by
    ext j; simp [Pi.single_apply, eq_comm]
  rw [e]; rfl

lemma nonpos_of_forall_pos {a b : ℝ} (h : ∀ t : ℝ, 0 < t → a + t * b < 0) : a ≤ 0 := by
  by_contra ha
  push_neg at ha
  have := h (a / (|b| + 1)) (by positivity)
  have h1 : a / (|b| + 1) * b ≥ -(a / (|b| + 1) * |b|) := by
    have : -|b| ≤ b := neg_abs_le b
    have hp : 0 ≤ a / (|b| + 1) := by positivity
    nlinarith
  have h2 : a - a / (|b| + 1) * |b| = a / (|b| + 1) := by field_simp; ring
  have h3 : 0 < a / (|b| + 1) := by positivity
  linarith

theorem gordan_core {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℝ)
    (h : ∀ d : Fin q → ℝ, (∀ j, 0 ≤ d j) → (∀ i, (B *ᵥ d) i ≤ 0) → d = 0) :
    ∃ y : Fin p → ℝ, (∀ i, 0 < y i) ∧ ∀ j, 0 < (Bᵀ *ᵥ y) j := by
  by_contra hcon
  push_neg at hcon
  let P : Set ((Fin p → ℝ) × (Fin q → ℝ)) := (Set.pi Set.univ fun _ => Set.Ioi 0) ×ˢ (Set.pi Set.univ fun _ => Set.Ioi 0)
  let L : (Fin p → ℝ) →ₗ[ℝ] ((Fin p → ℝ) × (Fin q → ℝ)) := LinearMap.prod LinearMap.id (Bᵀ.mulVecLin)
  have hPc : Convex ℝ P :=
    (convex_pi fun _ _ => convex_Ioi 0).prod (convex_pi fun _ _ => convex_Ioi 0)
  have hPo : IsOpen P :=
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi).prod
      (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi)
  have hWc : Convex ℝ (LinearMap.range L : Set ((Fin p → ℝ) × (Fin q → ℝ))) := (LinearMap.range L).convex
  have hmemP : ∀ v : (Fin p → ℝ) × (Fin q → ℝ), v ∈ P ↔ (∀ i, 0 < v.1 i) ∧ ∀ j, 0 < v.2 j := by
    intro v; simp [P, Set.mem_prod, Set.mem_pi]
  have hdisj : Disjoint P (LinearMap.range L : Set ((Fin p → ℝ) × (Fin q → ℝ))) := by
    rw [Set.disjoint_left]
    rintro v hv ⟨y, rfl⟩
    rw [hmemP] at hv
    obtain ⟨j, hj⟩ := hcon y hv.1
    have := hv.2 j
    simp [L] at this
    rw [Matrix.mulVec_transpose] at hj
    linarith
  obtain ⟨f, u, hs, ht⟩ := geometric_hahn_banach_open hPc hPo hWc hdisj
  have hu : u ≤ 0 := by simpa using ht 0 ⟨0, by simp⟩
  have hW0 : ∀ y, f (y, Bᵀ *ᵥ y) = 0 := by
    intro y
    set c := f (y, Bᵀ *ᵥ y) with hc
    by_contra hc0
    have := ht (L ((-(|u| + 1) / c) • y)) ⟨_, rfl⟩
    have e : L ((-(|u| + 1) / c) • y) = (-(|u| + 1) / c) • (y, Bᵀ *ᵥ y) := by
      simp [L, Matrix.mulVec_transpose]
    rw [e, map_smul, smul_eq_mul, ← hc] at this
    have : -(|u| + 1) / c * c = -(|u| + 1) := by field_simp
    have h2 := abs_nonneg u
    have h3 := neg_abs_le u
    linarith
  let one : (Fin p → ℝ) × (Fin q → ℝ) := (fun _ => 1, fun _ => 1)
  have hone : f one < u := hs one ((hmemP one).mpr ⟨fun _ => one_pos, fun _ => one_pos⟩)
  have hadd : ∀ y z, f (y, z) = f (y, 0) + f (0, z) := by
    intro y z
    rw [← map_add]; simp
  -- coordinate nonpositivity
  have h1 : ∀ i, f (Pi.single i 1, 0) ≤ 0 := by
    intro i
    apply nonpos_of_forall_pos (b := f one)
    intro t ht0
    have hm : (Pi.single i 1 + t • (fun _ : Fin p => (1 : ℝ)), t • (fun _ : Fin q => (1 : ℝ))) ∈ P := by
      rw [hmemP]
      refine ⟨fun k => ?_, fun j => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
        have : 0 ≤ (Pi.single i 1 : Fin p → ℝ) k := by
          by_cases hk : k = i <;> simp [hk, Pi.single_apply]
        linarith
      · simpa using ht0
    have := hs _ hm
    have e : (Pi.single i 1 + t • (fun _ : Fin p => (1 : ℝ)), t • (fun _ : Fin q => (1 : ℝ))) =
        (Pi.single i 1, 0) + t • one := by
      ext <;> simp [one]
    rw [e, map_add, map_smul, smul_eq_mul] at this
    linarith
  have h2 : ∀ j, f (0, Pi.single j 1) ≤ 0 := by
    intro j
    apply nonpos_of_forall_pos (b := f one)
    intro t ht0
    have hm : (t • (fun _ : Fin p => (1 : ℝ)), Pi.single j 1 + t • (fun _ : Fin q => (1 : ℝ))) ∈ P := by
      rw [hmemP]
      refine ⟨fun k => ?_, fun k => ?_⟩
      · simpa using ht0
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
        have : 0 ≤ (Pi.single j 1 : Fin q → ℝ) k := by
          by_cases hk : k = j <;> simp [hk, Pi.single_apply]
        linarith
    have := hs _ hm
    have e : (t • (fun _ : Fin p => (1 : ℝ)), Pi.single j 1 + t • (fun _ : Fin q => (1 : ℝ))) =
        (0, Pi.single j 1) + t • one := by
      ext <;> simp [one]
    rw [e, map_add, map_smul, smul_eq_mul] at this
    linarith
  -- linear decompositions
  let f1 : (Fin p → ℝ) →ₗ[ℝ] ℝ := (f : ((Fin p → ℝ) × (Fin q → ℝ)) →ₗ[ℝ] ℝ) ∘ₗ (LinearMap.inl ℝ _ _)
  let f2 : (Fin q → ℝ) →ₗ[ℝ] ℝ := (f : ((Fin p → ℝ) × (Fin q → ℝ)) →ₗ[ℝ] ℝ) ∘ₗ (LinearMap.inr ℝ _ _)
  have hf1 : ∀ y, f (y, 0) = ∑ i, y i * f (Pi.single i 1, 0) := fun y => lin_decomp f1 y
  have hf2 : ∀ z, f (0, z) = ∑ j, z j * f (0, Pi.single j 1) := fun z => lin_decomp f2 z
  -- the recession direction
  let d : Fin q → ℝ := fun j => - f (0, Pi.single j 1)
  have hd0 : ∀ j, 0 ≤ d j := fun j => by simp only [d]; linarith [h2 j]
  have hrow : ∀ i, f (Pi.single i 1, 0) = - f (0, fun j => B i j) := by
    intro i
    have := hW0 (Pi.single i 1)
    rw [hadd] at this
    have e : Bᵀ *ᵥ (Pi.single i 1 : Fin p → ℝ) = fun j => B i j := by
      ext j; simp [mulVec, dotProduct, Pi.single_apply]
    rw [e] at this
    linarith
  have hBd : ∀ i, (B *ᵥ d) i = f (Pi.single i 1, 0) := by
    intro i
    rw [hrow i, hf2]
    simp only [mulVec, dotProduct, d]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdz := h d hd0 (fun i => by rw [hBd]; exact h1 i)
  have hz : ∀ j, f (0, Pi.single j 1) = 0 := fun j => by
    have := congrFun hdz j
    simp [d] at this
    exact this
  have hf20 : ∀ z, f (0, z) = 0 := fun z => by rw [hf2]; simp [hz]
  have hf10 : ∀ i, f (Pi.single i 1, 0) = 0 := fun i => by rw [hrow, hf20]; simp
  have : f one = 0 := by
    have e : one = ((fun _ => 1 : Fin p → ℝ), 0) + (0, (fun _ => 1 : Fin q → ℝ)) := by
      ext <;> simp [one]
    rw [e, map_add, hf20, hf1]
    simp [hf10]
  linarith

lemma large_shift {p : ℕ} (q0 r : Fin p → ℝ) (hq : ∀ j, 0 < q0 j) :
    ∃ t : ℝ, 0 < t ∧ ∀ j, r j < t * q0 j := by
  have hs : 0 ≤ ∑ j, |r j| / q0 j :=
    Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (hq j).le
  refine ⟨∑ j, |r j| / q0 j + 1, by linarith, fun j => ?_⟩
  have h1 : |r j| / q0 j ≤ ∑ j, |r j| / q0 j :=
    Finset.single_le_sum (f := fun j => |r j| / q0 j) (fun j _ => by have := hq j; positivity)
      (Finset.mem_univ j)
  have h2 : |r j| / q0 j * q0 j = |r j| := div_mul_cancel₀ _ (hq j).ne'
  have h3 := hq j
  have h4 := le_abs_self (r j)
  nlinarith

lemma recession_of_bounded {k : ℕ} (S : Set (Fin k → ℝ)) (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (d : Fin k → ℝ) (hd : d ≠ 0)
    (h : ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → x + t • d ∈ S) : False := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbdd
  obtain ⟨x0, hx0⟩ := hne
  have hdp : 0 < ‖d‖ := norm_pos_iff.mpr hd
  set t := (C + ‖x0‖ + 1) / ‖d‖ with ht
  have ht0 : 0 ≤ t := by
    have := hC x0 hx0
    have : 0 ≤ C := le_trans (norm_nonneg _) this
    exact div_nonneg (by linarith [norm_nonneg x0]) hdp.le
  have h1 := hC _ (h x0 hx0 t ht0)
  have h2 : ‖t • d‖ = C + ‖x0‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ht]; field_simp
  have h3 : ‖t • d‖ ≤ ‖x0 + t • d‖ + ‖x0‖ := by
    have := norm_sub_le (x0 + t • d) x0
    have e : x0 + t • d - x0 = t • d := by abel
    rw [e] at this
    exact this
  linarith

theorem dual_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hne : (primalFeasibleSet A b).Nonempty)
    (hbdd : Bornology.IsBounded (primalFeasibleSet A b)) :
    DualStrictlyFeasible A c := by
  have hrec : ∀ d : Fin n → ℝ, (∀ j, 0 ≤ d j) → (∀ i, (A *ᵥ d) i ≤ 0) → d = 0 := by
    intro d hd0 hAd
    by_contra hd
    refine recession_of_bounded _ hne hbdd d hd ?_
    intro x hx t ht
    refine ⟨fun j => ?_, fun i => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hx.1 j) (mul_nonneg ht (hd0 j))
    · rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hx.2 i
      have := mul_nonneg ht (neg_nonneg.mpr (hAd i))
      linarith
  obtain ⟨y0, hy0, hAy0⟩ := gordan_core A hrec
  obtain ⟨t, ht, hts⟩ := large_shift (Aᵀ *ᵥ y0) (fun j => c j - (Aᵀ *ᵥ (fun _ => (1:ℝ))) j) hAy0
  refine ⟨fun i => 1 + t * y0 i, Aᵀ *ᵥ (fun i => 1 + t * y0 i) - c, by abel, fun i => ?_, fun j => ?_⟩
  · have := hy0 i; positivity
  · have e : (fun i => 1 + t * y0 i) = (fun _ => (1:ℝ)) + t • y0 := by
      ext i; simp
    rw [e]
    simp only [mulVec_add, mulVec_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hts j
    linarith

theorem primal_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hne : (dualFeasibleSet A c).Nonempty)
    (hbdd : Bornology.IsBounded (dualFeasibleSet A c)) :
    PrimalStrictlyFeasible A b := by
  have hrec : ∀ d : Fin m → ℝ, (∀ j, 0 ≤ d j) → (∀ i, ((-Aᵀ) *ᵥ d) i ≤ 0) → d = 0 := by
    intro d hd0 hAd
    by_contra hd
    refine recession_of_bounded _ hne hbdd d hd ?_
    intro y hy t ht
    refine ⟨fun j => ?_, fun j => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hy.1 j) (mul_nonneg ht (hd0 j))
    · rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hy.2 j
      have h2 := hAd j
      rw [neg_mulVec, Pi.neg_apply] at h2
      have := mul_nonneg ht (neg_nonneg.mpr h2)
      linarith
  obtain ⟨x0, hx0, hAx0⟩ := gordan_core (-Aᵀ) hrec
  rw [transpose_neg, transpose_transpose] at hAx0
  obtain ⟨t, ht, hts⟩ := large_shift (-(A *ᵥ x0)) (fun i => (A *ᵥ (fun _ => (1:ℝ))) i - b i)
    (fun i => by simpa [neg_mulVec] using hAx0 i)
  refine ⟨fun j => 1 + t * x0 j, b - A *ᵥ (fun j => 1 + t * x0 j), by abel, fun j => ?_, fun i => ?_⟩
  · have := hx0 j; positivity
  · have e : (fun j => 1 + t * x0 j) = (fun _ => (1:ℝ)) + t • x0 := by
      ext i; simp
    rw [e]
    simp only [mulVec_add, mulVec_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hts i
    simp only [Pi.neg_apply] at this
    linarith

end VanderbeiLP.CentralPath

open VanderbeiLP.CentralPath


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hne : (primalFeasibleSet A b).Nonempty)
    (hbdd : Bornology.IsBounded (primalFeasibleSet A b)) :
    DualStrictlyFeasible A c := by
  exact dual_core A b c hne hbdd
