-- Prove2me | solution 1 for VanderbeiLP.SelfDual.predictor_step_length_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T08:24:30.148518+00:00
-- url     : https://prove2.me/submissions/79a75756-400c-4e78-8e27-17151f9e3e1e

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual

open Matrix

set_option autoImplicit false

namespace VSD963
open VanderbeiLP.SelfDual

lemma skew_quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (v : Fin n → ℝ) : v ⬝ᵥ (A *ᵥ v) = 0 := by
  have h1 : v ⬝ᵥ (A *ᵥ v) = (Aᵀ *ᵥ v) ⬝ᵥ v := by
    rw [dotProduct_mulVec, mulVec_transpose]
  rw [show Aᵀ = -A from hA, neg_mulVec, neg_dotProduct, dotProduct_comm (A *ᵥ v) v] at h1
  linarith

lemma sum_dxdz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (x z dx dz : Fin n → ℝ) (hstep : IsStepDirection A 0 x z dx dz) :
    ∑ j, dx j * dz j = 0 := by
  obtain ⟨h1, h2⟩ := hstep
  have hfeas : A *ᵥ (x + dx) + (z + dz) = 0 := by
    have e : A *ᵥ (x + dx) + (z + dz) = (A *ᵥ x + z) + (A *ᵥ dx + dz) := by
      rw [mulVec_add]; abel
    rw [e, h1]; unfold rho; simp; abel
  have hz : z + dz = -(A *ᵥ (x + dx)) :=
    eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hfeas)
  have hq := skew_quad A hA (x + dx)
  have hdot : (x + dx) ⬝ᵥ (z + dz) = 0 := by rw [hz, dotProduct_neg, hq, neg_zero]
  have hexp : (x + dx) ⬝ᵥ (z + dz) = ∑ j, dx j * dz j := by
    simp only [dotProduct, Pi.add_apply]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro j _
    linear_combination h2 j
  linarith

lemma abs_comp (x z dx dz : ℝ) (hx : 0 < x) (hz : 0 < z)
    (h : z * dx + x * dz = 0 * 1 - x * z) :
    |dx * dz| ≤ x * z / 2 - dx * dz := by
  have hxz := mul_pos hx hz
  rcases le_or_gt (dx * dz) 0 with ha | ha
  · rw [abs_of_nonpos ha]; nlinarith
  · rw [abs_of_pos ha]
    have e : (z * dx + x * dz) ^ 2 = (x * z) ^ 2 := by rw [h]; ring
    have key : 4 * (x * z) * (dx * dz) ≤ (x * z) ^ 2 := by
      nlinarith [sq_nonneg (z * dx - x * dz)]
    have h4 : 4 * (dx * dz) ≤ x * z := by nlinarith
    linarith

lemma en_add {n : ℕ} (u v : Fin n → ℝ) :
    euclidNorm (u + v) ≤ euclidNorm u + euclidNorm v := by
  unfold euclidNorm
  have hu := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (u j)))
  have hv := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (v j)))
  have cs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v
  have hsu := Real.sqrt_nonneg (∑ j, u j ^ 2)
  have hsv := Real.sqrt_nonneg (∑ j, v j ^ 2)
  have e : ∑ j, (u + v) j ^ 2 = ∑ j, u j ^ 2 + 2 * ∑ j, u j * v j + ∑ j, v j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply]; ring
  calc Real.sqrt (∑ j, (u + v) j ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ j, u j ^ 2) + Real.sqrt (∑ j, v j ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [e]; nlinarith
    _ = Real.sqrt (∑ j, u j ^ 2) + Real.sqrt (∑ j, v j ^ 2) :=
        Real.sqrt_sq (by positivity)

lemma en_smul {n : ℕ} (s : ℝ) (u : Fin n → ℝ) :
    euclidNorm (fun j => s * u j) = |s| * euclidNorm u := by
  unfold euclidNorm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg s), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma en_le_l1 {n : ℕ} (a : Fin n → ℝ) : euclidNorm a ≤ ∑ j, |a j| := by
  unfold euclidNorm
  have hs : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  calc Real.sqrt (∑ j, a j ^ 2) ≤ Real.sqrt ((∑ j, |a j|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc ∑ j, a j ^ 2 = ∑ j, |a j| * |a j| := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [← sq, sq_abs]
          _ ≤ ∑ j, |a j| * ∑ i, |a i| := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (fun k _ => abs_nonneg (a k)) (Finset.mem_univ j))
                (abs_nonneg _)
          _ = (∑ j, |a j|) ^ 2 := by rw [← Finset.sum_mul, sq]
    _ = ∑ j, |a j| := Real.sqrt_sq hs

lemma comp_le {n : ℕ} (v : Fin n → ℝ) (j : Fin n) : |v j| ≤ euclidNorm v :=
  Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => v i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j))

lemma prod_t {n : ℕ} (x z dx dz : Fin n → ℝ)
    (h2 : ∀ j, z j * dx j + x j * dz j = 0 * mu x z - x j * z j) (t : ℝ) (j : Fin n) :
    (x + t • dx) j * (z + t • dz) j = (1 - t) * (x j * z j) + t ^ 2 * (dx j * dz j) := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination t * h2 j

lemma mu_t {n : ℕ} (x z dx dz : Fin n → ℝ)
    (h2 : ∀ j, z j * dx j + x j * dz j = 0 * mu x z - x j * z j)
    (hsum : ∑ j, dx j * dz j = 0) (t : ℝ) :
    mu (x + t • dx) (z + t • dz) = (1 - t) * mu x z := by
  unfold mu
  simp only [dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => prod_t x z dx dz h2 t j), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  ring

lemma resid_t {n : ℕ} (x z dx dz : Fin n → ℝ)
    (h2 : ∀ j, z j * dx j + x j * dz j = 0 * mu x z - x j * z j)
    (hsum : ∑ j, dx j * dz j = 0) (t : ℝ) :
    centralityResidual (x + t • dx) (z + t • dz) =
      (fun j => (1 - t) * centralityResidual x z j) + (fun j => t ^ 2 * (dx j * dz j)) := by
  funext j
  show (x + t • dx) j * (z + t • dz) j - mu (x + t • dx) (z + t • dz) =
    (1 - t) * (x j * z j - mu x z) + t ^ 2 * (dx j * dz j)
  rw [prod_t x z dx dz h2 t j, mu_t x z dx dz h2 hsum t]
  ring

lemma lin_pos (x z dx dz t : ℝ) (hx : 0 < x) (hz : 0 < z) (ht : 0 ≤ t)
    (h : ∀ s : ℝ, 0 ≤ s → s ≤ t → 0 < (x + s * dx) * (z + s * dz)) :
    0 < x + t * dx ∧ 0 < z + t * dz := by
  constructor
  · by_contra hc
    push_neg at hc
    have hdx : dx < 0 := by nlinarith
    have hs0 : 0 ≤ x / (-dx) := div_nonneg hx.le (by linarith)
    have hst : x / (-dx) ≤ t := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have hh := h _ hs0 hst
    have e : x + x / (-dx) * dx = 0 := by rw [div_neg, neg_mul, div_mul_cancel₀ x hdx.ne]; ring
    rw [e, zero_mul] at hh
    exact lt_irrefl _ hh
  · by_contra hc
    push_neg at hc
    have hdz : dz < 0 := by nlinarith
    have hs0 : 0 ≤ z / (-dz) := div_nonneg hz.le (by linarith)
    have hst : z / (-dz) ≤ t := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have hh := h _ hs0 hst
    have e : z + z / (-dz) * dz = 0 := by rw [div_neg, neg_mul, div_mul_cancel₀ z hdz.ne]; ring
    rw [e, mul_zero] at hh
    exact lt_irrefl _ hh

end VSD963

open VanderbeiLP.SelfDual in
theorem solution {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (x z dx dz : Fin n → ℝ) (hN : (x, z) ∈ Nbhd (1 / 4 : ℝ))
    (hstep : IsStepDirection A 0 x z dx dz) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 / (2 * Real.sqrt n) →
      (x + t • dx, z + t • dz) ∈ Nbhd (1 / 2 : ℝ)) ∧
    1 / (2 * Real.sqrt n) ≤ predictorStepLength x z dx dz := by
  obtain ⟨hx, hz, hc⟩ := hN
  have hx' : ∀ j, 0 < x j := hx
  have hz' : ∀ j, 0 < z j := hz
  have hc' : euclidNorm (centralityResidual x z) ≤ 1 / 4 * mu x z := hc
  have h2 := hstep.2
  have hsum := VSD963.sum_dxdz A hA x z dx dz hstep
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdotpos : 0 < x ⬝ᵥ z :=
    Finset.sum_pos (fun j _ => mul_pos (hx' j) (hz' j)) Finset.univ_nonempty
  have hmu : 0 < mu x z := by unfold mu; positivity
  have hnmu : (n : ℝ) * mu x z = x ⬝ᵥ z := by unfold mu; field_simp
  -- l1 bound on dx ∘ dz
  have hl1 : ∑ j, |dx j * dz j| ≤ n * mu x z / 2 := by
    have hb : ∀ j, |dx j * dz j| ≤ x j * z j / 2 - dx j * dz j := fun j =>
      VSD963.abs_comp (x j) (z j) (dx j) (dz j) (hx' j) (hz' j)
        (by have := h2 j; rw [this]; ring)
    calc ∑ j, |dx j * dz j| ≤ ∑ j, (x j * z j / 2 - dx j * dz j) := Finset.sum_le_sum (fun j _ => hb j)
      _ = (x ⬝ᵥ z) / 2 - ∑ j, dx j * dz j := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div]; rfl
      _ = n * mu x z / 2 := by rw [hsum, hnmu]; ring
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hs1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ n by omega))
  -- step conditions
  have hcond : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / (2 * Real.sqrt n) → t ≤ 1 / 2 ∧ 2 * n * t ^ 2 ≤ 1 - t := by
    intro t ht0 ht
    have ht' : t * (2 * Real.sqrt n) ≤ 1 := (le_div_iff₀ (by positivity)).mp ht
    have hm := mul_le_mul ht' ht' (by positivity) zero_le_one
    constructor
    · nlinarith
    · nlinarith
  have hres : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / (2 * Real.sqrt n) →
      euclidNorm (centralityResidual (x + t • dx) (z + t • dz)) ≤ 1 / 2 * ((1 - t) * mu x z) := by
    intro t ht0 ht
    obtain ⟨ht2, hq⟩ := hcond t ht0 ht
    rw [VSD963.resid_t x z dx dz h2 hsum t]
    have e1 := VSD963.en_smul (1 - t) (centralityResidual x z)
    have e2 := VSD963.en_smul (t ^ 2) (fun j => dx j * dz j)
    have l1 := VSD963.en_le_l1 (fun j => dx j * dz j)
    rw [abs_of_nonneg (by linarith)] at e1
    rw [abs_of_nonneg (by positivity)] at e2
    have hadd := VSD963.en_add (fun j => (1 - t) * centralityResidual x z j)
      (fun j => t ^ 2 * (dx j * dz j))
    have hl1' : euclidNorm (fun j => dx j * dz j) ≤ n * mu x z / 2 := le_trans l1 hl1
    have hA1 : (1 - t) * euclidNorm (centralityResidual x z) ≤ (1 - t) * (1 / 4 * mu x z) :=
      mul_le_mul_of_nonneg_left hc' (by linarith)
    have hA2 : t ^ 2 * euclidNorm (fun j => dx j * dz j) ≤ t ^ 2 * (n * mu x z / 2) :=
      mul_le_mul_of_nonneg_left hl1' (by positivity)
    have hA3 : mu x z * (2 * n * t ^ 2) ≤ mu x z * (1 - t) := mul_le_mul_of_nonneg_left hq hmu.le
    nlinarith
  have hprod : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / (2 * Real.sqrt n) → ∀ j,
      0 < (x j + t * dx j) * (z j + t * dz j) := by
    intro t ht0 ht j
    obtain ⟨ht2, hq⟩ := hcond t ht0 ht
    have hr := hres t ht0 ht
    have hcj := VSD963.comp_le (centralityResidual (x + t • dx) (z + t • dz)) j
    have hm := VSD963.mu_t x z dx dz h2 hsum t
    have e : centralityResidual (x + t • dx) (z + t • dz) j =
        (x j + t * dx j) * (z j + t * dz j) - (1 - t) * mu x z := by
      simp only [centralityResidual, hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e] at hcj
    have hpos : 0 < (1 - t) * mu x z := mul_pos (by linarith) hmu
    have := neg_abs_le ((x j + t * dx j) * (z j + t * dz j) - (1 - t) * mu x z)
    linarith
  have part1 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / (2 * Real.sqrt n) →
      (x + t • dx, z + t • dz) ∈ Nbhd (1 / 2 : ℝ) := by
    intro t ht0 ht
    have hlin : ∀ j, 0 < x j + t * dx j ∧ 0 < z j + t * dz j := fun j =>
      VSD963.lin_pos (x j) (z j) (dx j) (dz j) t (hx' j) (hz' j) ht0
        (fun s hs0 hst => hprod s hs0 (le_trans hst ht) j)
    refine ⟨fun j => ?_, fun j => ?_, ?_⟩
    · show 0 < (x + t • dx) j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact (hlin j).1
    · show 0 < (z + t • dz) j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact (hlin j).2
    · show euclidNorm (centralityResidual (x + t • dx) (z + t • dz)) ≤
        1 / 2 * mu (x + t • dx) (z + t • dz)
      rw [VSD963.mu_t x z dx dz h2 hsum t]
      exact hres t ht0 ht
  refine ⟨part1, ?_⟩
  unfold predictorStepLength
  apply le_csSup
  · refine ⟨1, fun t ht => ?_⟩
    obtain ⟨htx, htz, -⟩ := ht
    have htx' : ∀ j, 0 < (x + t • dx) j := htx
    have htz' : ∀ j, 0 < (z + t • dz) j := htz
    have hd : 0 < (x + t • dx) ⬝ᵥ (z + t • dz) :=
      Finset.sum_pos (fun j _ => mul_pos (htx' j) (htz' j)) Finset.univ_nonempty
    have hmt : 0 < mu (x + t • dx) (z + t • dz) := by unfold mu; positivity
    rw [VSD963.mu_t x z dx dz h2 hsum t] at hmt
    by_contra hcon
    push_neg at hcon
    nlinarith
  · exact part1 _ (by positivity) le_rfl
