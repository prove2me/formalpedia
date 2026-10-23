-- Prove2me | solution 1 for VanderbeiLP.CentralPath.central_path_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:08:44.588863+00:00
-- url     : https://prove2.me/submissions/c23808ce-52ed-4630-92f5-d2223fd3df5e

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



lemma cp_term_nonpos {x z x' z' μ : ℝ} (hx : 0 < x) (hz : 0 < z) (hx' : 0 < x') (hz' : 0 < z')
    (h1 : x * z = μ) (h2 : x' * z' = μ) : (x - x') * (z - z') ≤ 0 := by
  rcases lt_trichotomy x x' with h | h | h
  · have : z' < z := by nlinarith
    nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 this)]
  · subst h; simp
  · have : z < z' := by nlinarith
    nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 this)]

lemma cp_eq_of_nonneg {x z x' z' μ : ℝ} (hx : 0 < x) (hz : 0 < z) (hx' : 0 < x') (hz' : 0 < z')
    (h1 : x * z = μ) (h2 : x' * z' = μ) (h : 0 ≤ (x - x') * (z - z')) : x = x' ∧ z = z' := by
  rcases lt_trichotomy x x' with h3 | h3 | h3
  · have : z' < z := by nlinarith
    nlinarith [mul_pos (sub_pos.2 h3) (sub_pos.2 this)]
  · subst h3
    refine ⟨rfl, ?_⟩
    have : x * z = x * z' := by rw [h1, h2]
    exact mul_left_cancel₀ hx.ne' this
  · have : z < z' := by nlinarith
    nlinarith [mul_pos (sub_pos.2 h3) (sub_pos.2 this)]

lemma cp_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (μ : ℝ)
    {x x' : Fin n → ℝ} {w w' y y' : Fin m → ℝ} {z z' : Fin n → ℝ}
    (h : IsCentralPathPoint A b c μ x w y z) (h' : IsCentralPathPoint A b c μ x' w' y' z') :
    x = x' ∧ w = w' ∧ y = y' ∧ z = z' := by
  obtain ⟨hb, hc, hxz, hyw, hx, hw, hy, hz⟩ := h
  obtain ⟨hb', hc', hxz', hyw', hx', hw', hy', hz'⟩ := h'
  have hdz : z - z' = Aᵀ *ᵥ (y - y') := by
    rw [mulVec_sub]
    ext j
    have := congrFun hc j
    have := congrFun hc' j
    simp only [Pi.sub_apply] at *
    linarith
  have hdw : A *ᵥ (x - x') = -(w - w') := by
    rw [mulVec_sub]
    ext i
    have h1 := congrFun hb i
    have h2 := congrFun hb' i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at *
    linarith
  have key : (x - x') ⬝ᵥ (z - z') + (w - w') ⬝ᵥ (y - y') = 0 := by
    rw [hdz, dotProduct_mulVec, vecMul_transpose, hdw, neg_dotProduct]
    ring
  have t1 : ∀ j, (x - x') j * (z - z') j ≤ 0 := fun j => by
    simp only [Pi.sub_apply]
    exact cp_term_nonpos (hx j) (hz j) (hx' j) (hz' j) (hxz j) (hxz' j)
  have t2 : ∀ i, (w - w') i * (y - y') i ≤ 0 := fun i => by
    simp only [Pi.sub_apply]
    exact cp_term_nonpos (μ := μ) (hw i) (hy i) (hw' i) (hy' i) (by rw [mul_comm]; exact hyw i)
      (by rw [mul_comm]; exact hyw' i)
  have s1 : ∑ j, (x - x') j * (z - z') j ≤ 0 := Finset.sum_nonpos fun j _ => t1 j
  have s2 : ∑ i, (w - w') i * (y - y') i ≤ 0 := Finset.sum_nonpos fun i _ => t2 i
  have key' : ∑ j, (x - x') j * (z - z') j + ∑ i, (w - w') i * (y - y') i = 0 := by
    simpa [dotProduct] using key
  have e1 : ∑ j, (x - x') j * (z - z') j = 0 := by linarith
  have e2 : ∑ i, (w - w') i * (y - y') i = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonpos (fun j _ => t1 j)] at e1
  rw [Finset.sum_eq_zero_iff_of_nonpos (fun i _ => t2 i)] at e2
  have r1 : ∀ j, x j = x' j ∧ z j = z' j := fun j => by
    have := e1 j (Finset.mem_univ j)
    simp only [Pi.sub_apply] at this
    exact cp_eq_of_nonneg (hx j) (hz j) (hx' j) (hz' j) (hxz j) (hxz' j) this.ge
  have r2 : ∀ i, w i = w' i ∧ y i = y' i := fun i => by
    have := e2 i (Finset.mem_univ i)
    simp only [Pi.sub_apply] at this
    exact cp_eq_of_nonneg (μ := μ) (hw i) (hy i) (hw' i) (hy' i) (by rw [mul_comm]; exact hyw i)
      (by rw [mul_comm]; exact hyw' i) this.ge
  exact ⟨funext fun j => (r1 j).1, funext fun i => (r2 i).1, funext fun i => (r2 i).2,
    funext fun j => (r1 j).2⟩



lemma cp_g_eq {μ k s : ℝ} (hμ : 0 < μ) (hk : 0 < k) (hs : 0 < s) :
    μ * Real.log s - k * s =
      (μ * Real.log (μ / k) - μ) - μ * (k * s / μ - 1 - Real.log (k * s / μ)) := by
  have h1 : Real.log (k * s / μ) = Real.log k + Real.log s - Real.log μ := by
    rw [Real.log_div (by positivity) hμ.ne', Real.log_mul hk.ne' hs.ne']
  have h2 : Real.log (μ / k) = Real.log μ - Real.log k := Real.log_div hμ.ne' hk.ne'
  rw [h1, h2]; field_simp; ring

lemma cp_D_nonneg {μ k s : ℝ} (hμ : 0 < μ) (hk : 0 < k) (hs : 0 < s) :
    0 ≤ μ * (k * s / μ - 1 - Real.log (k * s / μ)) := by
  have := Real.log_le_sub_one_of_pos (show 0 < k * s / μ by positivity)
  exact mul_nonneg hμ.le (by linarith)

lemma cp_box1 {μ k s Δ : ℝ} (hμ : 0 < μ) (hk : 0 < k) (hs : 0 < s)
    (h : μ * (k * s / μ - 1 - Real.log (k * s / μ)) ≤ Δ) :
    μ * Real.exp (-(Δ / μ + 1)) / k ≤ s ∧ s ≤ μ * (2 * (Δ / μ) + 2) / k := by
  obtain ⟨u, hu⟩ : ∃ u, u = k * s / μ := ⟨_, rfl⟩
  rw [← hu] at h
  have hu0 : 0 < u := by rw [hu]; positivity
  have hδ : u - 1 - Real.log u ≤ Δ / μ := by
    rw [le_div_iff₀ hμ]; linarith [mul_comm μ (u - 1 - Real.log u)]
  have hs' : s = μ * u / k := by rw [hu]; field_simp
  have hl : Real.exp (-(Δ / μ + 1)) ≤ u := by
    rw [← Real.le_log_iff_exp_le hu0]
    linarith
  have hh : u ≤ 2 * (Δ / μ) + 2 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < u / 2 by positivity)
    rw [Real.log_div hu0.ne' (by norm_num)] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    linarith
  rw [hs']
  constructor
  · gcongr
  · gcongr

lemma cp_F_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (yb : Fin m → ℝ) (zb : Fin n → ℝ) (hdual : Aᵀ *ᵥ yb - zb = c) (μ : ℝ)
    (x : Fin n → ℝ) (w : Fin m → ℝ) (hb : A *ᵥ x + w = b) :
    barrierFunction c μ x w = yb ⬝ᵥ b + ∑ j, (μ * Real.log (x j) - zb j * x j) +
      ∑ i, (μ * Real.log (w i) - yb i * w i) := by
  have e1 : c ⬝ᵥ x = yb ⬝ᵥ (A *ᵥ x) - zb ⬝ᵥ x := by
    rw [← hdual, sub_dotProduct, mulVec_transpose, dotProduct_mulVec]
  have e2 : yb ⬝ᵥ b = yb ⬝ᵥ (A *ᵥ x) + yb ⬝ᵥ w := by rw [← hb, dotProduct_add]
  unfold barrierFunction
  rw [e1, e2]
  generalize yb ⬝ᵥ (A *ᵥ x) = s1
  simp only [dotProduct, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

noncomputable def Dd (μ k s : ℝ) : ℝ := μ * (k * s / μ - 1 - Real.log (k * s / μ))
noncomputable def Mm (μ k : ℝ) : ℝ := μ * Real.log (μ / k) - μ

lemma cp_F_eq2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (yb : Fin m → ℝ) (zb : Fin n → ℝ) (hdual : Aᵀ *ᵥ yb - zb = c) (hy : ∀ i, 0 < yb i)
    (hz : ∀ j, 0 < zb j) (μ : ℝ) (hμ : 0 < μ)
    (x : Fin n → ℝ) (w : Fin m → ℝ) (hb : A *ᵥ x + w = b) (hx : ∀ j, 0 < x j) (hw : ∀ i, 0 < w i) :
    barrierFunction c μ x w = (yb ⬝ᵥ b + ∑ j, Mm μ (zb j) + ∑ i, Mm μ (yb i)) -
      ∑ j, Dd μ (zb j) (x j) - ∑ i, Dd μ (yb i) (w i) := by
  rw [cp_F_eq A b c yb zb hdual μ x w hb]
  have h1 : ∑ j, (μ * Real.log (x j) - zb j * x j) = ∑ j, Mm μ (zb j) - ∑ j, Dd μ (zb j) (x j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => cp_g_eq hμ (hz j) (hx j)
  have h2 : ∑ i, (μ * Real.log (w i) - yb i * w i) = ∑ i, Mm μ (yb i) - ∑ i, Dd μ (yb i) (w i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => cp_g_eq hμ (hy i) (hw i)
  rw [h1, h2]; ring

theorem exists_barrier_max {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : PrimalStrictlyFeasible A b) (hD : DualStrictlyFeasible A c) (μ : ℝ) (hμ : 0 < μ) :
    ∃ (x : Fin n → ℝ) (w : Fin m → ℝ), IsBarrierSolution A b c μ x w := by
  obtain ⟨x0, w0, hb0, hx0, hw0⟩ := hP
  obtain ⟨yb, zb, hdual, hy, hz⟩ := hD
  set K0 : ℝ := yb ⬝ᵥ b + ∑ j, Mm μ (zb j) + ∑ i, Mm μ (yb i) with hK0
  set F0 : ℝ := barrierFunction c μ x0 w0 with hF0
  set Δ : ℝ := K0 - F0 with hΔ
  let lx : Fin n → ℝ := fun j => μ * Real.exp (-(Δ / μ + 1)) / zb j
  let ux : Fin n → ℝ := fun j => μ * (2 * (Δ / μ) + 2) / zb j
  let lw : Fin m → ℝ := fun i => μ * Real.exp (-(Δ / μ + 1)) / yb i
  let uw : Fin m → ℝ := fun i => μ * (2 * (Δ / μ) + 2) / yb i
  have hlx : ∀ j, 0 < lx j := fun j => by have := hz j; positivity
  have hlw : ∀ i, 0 < lw i := fun i => by have := hy i; positivity
  have hlevel : ∀ (x : Fin n → ℝ) (w : Fin m → ℝ), A *ᵥ x + w = b → (∀ j, 0 < x j) →
      (∀ i, 0 < w i) → F0 ≤ barrierFunction c μ x w →
      (∀ j, lx j ≤ x j ∧ x j ≤ ux j) ∧ (∀ i, lw i ≤ w i ∧ w i ≤ uw i) := by
    intro x w hb hx hw hF
    have hFe := cp_F_eq2 A b c yb zb hdual hy hz μ hμ x w hb hx hw
    have hSx : 0 ≤ ∑ j, Dd μ (zb j) (x j) :=
      Finset.sum_nonneg fun j _ => cp_D_nonneg hμ (hz j) (hx j)
    have hSw : 0 ≤ ∑ i, Dd μ (yb i) (w i) :=
      Finset.sum_nonneg fun i _ => cp_D_nonneg hμ (hy i) (hw i)
    have hsum : ∑ j, Dd μ (zb j) (x j) + ∑ i, Dd μ (yb i) (w i) ≤ Δ := by
      rw [hΔ]; linarith
    constructor
    · intro j
      have h1 : Dd μ (zb j) (x j) ≤ ∑ j, Dd μ (zb j) (x j) :=
        Finset.single_le_sum (f := fun j => Dd μ (zb j) (x j))
          (fun j _ => cp_D_nonneg hμ (hz j) (hx j)) (Finset.mem_univ j)
      have h2 : Dd μ (zb j) (x j) ≤ Δ := by linarith
      exact cp_box1 hμ (hz j) (hx j) h2
    · intro i
      have h1 : Dd μ (yb i) (w i) ≤ ∑ i, Dd μ (yb i) (w i) :=
        Finset.single_le_sum (f := fun i => Dd μ (yb i) (w i))
          (fun i _ => cp_D_nonneg hμ (hy i) (hw i)) (Finset.mem_univ i)
      have h2 : Dd μ (yb i) (w i) ≤ Δ := by linarith
      exact cp_box1 hμ (hy i) (hw i) h2
  let K : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
    {p | A *ᵥ p.1 + p.2 = b} ∩ (Set.Icc lx ux ×ˢ Set.Icc lw uw)
  have hKc : IsCompact K := by
    apply IsCompact.inter_left ?_ ?_
    · exact (isCompact_Icc).prod (isCompact_Icc)
    · exact isClosed_eq (Continuous.add (((Matrix.mulVecLin A).continuous_of_finiteDimensional).comp
        continuous_fst) continuous_snd) continuous_const
  have h0K : (x0, w0) ∈ K := by
    have := hlevel x0 w0 hb0 hx0 hw0 le_rfl
    refine ⟨hb0, ?_, ?_⟩
    · exact ⟨fun j => (this.1 j).1, fun j => (this.1 j).2⟩
    · exact ⟨fun i => (this.2 i).1, fun i => (this.2 i).2⟩
  have hcont : ContinuousOn (fun p : (Fin n → ℝ) × (Fin m → ℝ) => barrierFunction c μ p.1 p.2) K := by
    unfold barrierFunction
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · simp only [dotProduct]
      fun_prop
    · refine continuousOn_const.mul (continuousOn_finsetSum _ fun j _ => ?_)
      refine ContinuousOn.log (by fun_prop) fun p hp => ?_
      have := hlx j
      have := hp.2.1.1 j
      linarith
    · refine continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => ?_)
      refine ContinuousOn.log (by fun_prop) fun p hp => ?_
      have := hlw i
      have := hp.2.2.1 i
      linarith
  obtain ⟨p, hpK, hpmax⟩ := hKc.exists_isMaxOn ⟨_, h0K⟩ hcont
  have hpmax' := isMaxOn_iff.mp hpmax
  have hpx : ∀ j, 0 < p.1 j := fun j => lt_of_lt_of_le (hlx j) (hpK.2.1.1 j)
  have hpw : ∀ i, 0 < p.2 i := fun i => lt_of_lt_of_le (hlw i) (hpK.2.2.1 i)
  refine ⟨p.1, p.2, hpK.1, hpx, hpw, fun x' w' hb' hx' hw' => ?_⟩
  by_cases hF : F0 ≤ barrierFunction c μ x' w'
  · have := hlevel x' w' hb' hx' hw' hF
    exact hpmax' (x', w') ⟨hb', ⟨fun j => (this.1 j).1, fun j => (this.1 j).2⟩,
      ⟨fun i => (this.2 i).1, fun i => (this.2 i).2⟩⟩
  · push_neg at hF
    have := hpmax' (x0, w0) h0K
    simp only at this
    linarith

lemma cp_log_deriv (a b : ℝ) (ha : 0 < a) :
    HasDerivAt (fun t : ℝ => Real.log (a + t * b)) (b / a) 0 := by
  have hl : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const b).const_add a
  have := hl.log (by simpa using ha.ne')
  simpa using this

lemma cp_kkt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (μ : ℝ)
    (x : Fin n → ℝ) (w : Fin m → ℝ) (hb : A *ᵥ x + w = b) (hx : ∀ j, 0 < x j) (hw : ∀ i, 0 < w i)
    (hmax : ∀ (x' : Fin n → ℝ) (w' : Fin m → ℝ), A *ᵥ x' + w' = b → (∀ j, 0 < x' j) →
      (∀ i, 0 < w' i) → barrierFunction c μ x' w' ≤ barrierFunction c μ x w)
    (dx : Fin n → ℝ) :
    c ⬝ᵥ dx + μ * ∑ j, dx j / x j - μ * ∑ i, (A *ᵥ dx) i / w i = 0 := by
  let φ : ℝ → ℝ := fun t => c ⬝ᵥ x + t * (c ⬝ᵥ dx) + μ * ∑ j, Real.log (x j + t * dx j) +
    μ * ∑ i, Real.log (w i + t * (-(A *ᵥ dx) i))
  have hder : HasDerivAt φ (c ⬝ᵥ dx + μ * ∑ j, dx j / x j + μ * ∑ i, (-(A *ᵥ dx) i) / w i) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => c ⬝ᵥ x + t * (c ⬝ᵥ dx)) (c ⬝ᵥ dx) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (c ⬝ᵥ dx)).const_add (c ⬝ᵥ x)
    have h2 : HasDerivAt (fun t : ℝ => ∑ j, Real.log (x j + t * dx j)) (∑ j, dx j / x j) 0 :=
      HasDerivAt.fun_sum (fun j _ => cp_log_deriv (x j) (dx j) (hx j))
    have h3 : HasDerivAt (fun t : ℝ => ∑ i, Real.log (w i + t * (-(A *ᵥ dx) i)))
        (∑ i, (-(A *ᵥ dx) i) / w i) 0 :=
      HasDerivAt.fun_sum (fun i _ => cp_log_deriv (w i) (-(A *ᵥ dx) i) (hw i))
    exact (h1.add (h2.const_mul μ)).add (h3.const_mul μ)
  have hpx : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j, 0 < x j + t * dx j := by
    rw [Filter.eventually_all]; intro j
    have : Tendsto (fun t : ℝ => x j + t * dx j) (𝓝 0) (𝓝 (x j + 0 * dx j)) :=
      (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
    rw [zero_mul, add_zero] at this
    exact this.eventually (lt_mem_nhds (hx j))
  have hpw : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, 0 < w i + t * (-(A *ᵥ dx) i) := by
    rw [Filter.eventually_all]; intro i
    have : Tendsto (fun t : ℝ => w i + t * (-(A *ᵥ dx) i)) (𝓝 0) (𝓝 (w i + 0 * (-(A *ᵥ dx) i))) :=
      (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
    rw [zero_mul, add_zero] at this
    exact this.eventually (lt_mem_nhds (hw i))
  have hloc : IsLocalMax φ 0 := by
    filter_upwards [hpx, hpw] with t h1 h2
    have hfe : A *ᵥ (x + t • dx) + (w + t • (-(A *ᵥ dx))) = b := by
      rw [mulVec_add, mulVec_smul, ← hb]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    have := hmax (x + t • dx) (w + t • (-(A *ᵥ dx))) hfe (fun j => by simpa using h1 j)
      (fun i => by simpa using h2 i)
    have e : barrierFunction c μ (x + t • dx) (w + t • (-(A *ᵥ dx))) = φ t := by
      simp only [barrierFunction, φ, dotProduct_add, dotProduct_smul, smul_eq_mul, Pi.add_apply,
        Pi.smul_apply, Pi.neg_apply]
    have e0 : barrierFunction c μ x w = φ 0 := by
      simp only [barrierFunction, φ, zero_mul, add_zero]
    rw [e, e0] at this
    exact this
  have := hloc.hasDerivAt_eq_zero hder
  have e : ∑ i, (-(A *ᵥ dx) i) / w i = -∑ i, (A *ᵥ dx) i / w i := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by rw [neg_div]
  rw [e] at this
  linarith

theorem exists_cp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : PrimalStrictlyFeasible A b) (hD : DualStrictlyFeasible A c) (μ : ℝ) (hμ : 0 < μ) :
    ∃ (x : Fin n → ℝ) (w y : Fin m → ℝ) (z : Fin n → ℝ), IsCentralPathPoint A b c μ x w y z := by
  obtain ⟨x, w, hb, hx, hw, hmax⟩ := exists_barrier_max A b c hP hD μ hμ
  refine ⟨x, w, fun i => μ / w i, fun j => μ / x j, hb, ?_, ?_, ?_, hx, hw, ?_, ?_⟩
  · ext j
    have := cp_kkt A b c μ x w hb hx hw hmax (Pi.single j 1)
    have e1 : c ⬝ᵥ (Pi.single j 1 : Fin n → ℝ) = c j := by simp
    have e2 : ∑ k, (Pi.single j 1 : Fin n → ℝ) k / x k = 1 / x j := by
      simp [Pi.single_apply, ite_div]
    have e3 : ∑ i, (A *ᵥ (Pi.single j 1 : Fin n → ℝ)) i / w i = ∑ i, A i j / w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [mulVec, dotProduct, Pi.single_apply]
    rw [e1, e2, e3] at this
    simp only [Pi.sub_apply, mulVec, dotProduct, transpose_apply]
    have e4 : ∑ i, A i j * (μ / w i) = μ * ∑ i, A i j / w i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e4]
    have e5 : μ / x j = μ * (1 / x j) := by ring
    rw [e5]
    linarith
  · intro j; have := hx j; field_simp
  · intro i; have := hw i; field_simp
  · intro i; have := hw i; have := hμ; positivity
  · intro j; have := hx j; have := hμ; positivity


theorem cp_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (h : (PrimalStrictlyFeasible A b ∧ Bornology.IsBounded (primalFeasibleSet A b)) ∨
      (DualStrictlyFeasible A c ∧ Bornology.IsBounded (dualFeasibleSet A c))) :
    ∀ μ : ℝ, 0 < μ →
      ∃! p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin m → ℝ) × (Fin n → ℝ),
        IsCentralPathPoint A b c μ p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  intro μ hμ
  have hboth : PrimalStrictlyFeasible A b ∧ DualStrictlyFeasible A c := by
    rcases h with ⟨hP, hbdd⟩ | ⟨hD, hbdd⟩
    · refine ⟨hP, ?_⟩
      obtain ⟨x, w, hb, hx, hw⟩ := hP
      refine dual_core A b c ⟨x, fun j => (hx j).le, fun i => ?_⟩ hbdd
      have := congrFun hb i
      simp only [Pi.add_apply] at this
      linarith [hw i]
    · refine ⟨?_, hD⟩
      obtain ⟨y, z, hc, hy, hz⟩ := hD
      refine primal_core A b c ⟨y, fun i => (hy i).le, fun j => ?_⟩ hbdd
      have := congrFun hc j
      simp only [Pi.sub_apply] at this
      linarith [hz j]
  obtain ⟨x, w, y, z, hcp⟩ := exists_cp A b c hboth.1 hboth.2 μ hμ
  refine ⟨(x, w, y, z), hcp, fun q hq => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := cp_unique A b c μ hq hcp
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

end VanderbeiLP.CentralPath

open VanderbeiLP.CentralPath


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (h : (PrimalStrictlyFeasible A b ∧ Bornology.IsBounded (primalFeasibleSet A b)) ∨
      (DualStrictlyFeasible A c ∧ Bornology.IsBounded (dualFeasibleSet A c))) :
    ∀ μ : ℝ, 0 < μ →
      ∃! p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin m → ℝ) × (Fin n → ℝ),
        IsCentralPathPoint A b c μ p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  exact cp_core A b c h
