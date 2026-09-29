-- Prove2me | solution 1 for conditional_khintchine_scale_moment_from_row_column_energy_moment
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T14:29:56.25728+00:00
-- url     : https://prove2.me/submissions/15b4d06a-9960-4294-82fd-73208b8a2808

import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_bernoulli_expectation_sqrt_le_sqrt_expectation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.CompleteLattice.Finset
open MatrixCompletion
open scoped Classical BigOperators

namespace SolKh

variable {n₁ n₂ : ℕ}

/-- Linearity: pulling a constant out of the Bernoulli expectation. -/
theorem bernoulliExpectation_const_mul (p c : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    bernoulliExpectation p (fun Ω => c * F Ω) =
      c * bernoulliExpectation p F := by
  unfold bernoulliExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Ω _
  ring

/-- Nonnegativity of the sampled row/column energies (each is an `iSup` over a
nonempty finite index of sums of nonnegative terms). -/
theorem sampledRowEnergyMax_nonneg (hn₁ : 0 < n₁)
    (Ω : Finset (Fin n₁ × Fin n₂)) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ sampledRowEnergyMax Ω X := by
  unfold sampledRowEnergyMax
  have hne : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
  obtain ⟨i₀⟩ := hne
  refine le_ciSup_of_le ?_ i₀ ?_
  · -- bounded above: finite range
    exact Set.Finite.bddAbove (Set.finite_range _)
  · apply Finset.sum_nonneg
    intro j _
    split <;> positivity

theorem sampledColumnEnergyMax_nonneg (hn₂ : 0 < n₂)
    (Ω : Finset (Fin n₁ × Fin n₂)) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ sampledColumnEnergyMax Ω X := by
  unfold sampledColumnEnergyMax
  have hne : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
  obtain ⟨j₀⟩ := hne
  refine le_ciSup_of_le ?_ j₀ ?_
  · exact Set.Finite.bddAbove (Set.finite_range _)
  · apply Finset.sum_nonneg
    intro i _
    split <;> positivity

/-- `(√a)^q = √(a^q)` for `0 ≤ a`. -/
theorem sqrt_pow_comm (a : ℝ) (ha : 0 ≤ a) (q : ℕ) :
    (Real.sqrt a) ^ q = Real.sqrt (a ^ q) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast (a ^ (1/2:ℝ)) q, ← Real.rpow_mul ha,
      ← Real.rpow_natCast a q, ← Real.rpow_mul ha]
  ring_nf

end SolKh

open SolKh

theorem solution
    (Cenergy Ckh : ℝ) :
    0 < Cenergy →
    0 < Ckh →
    ∃ Crad : ℝ, 0 < Crad ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (Ckh * Real.sqrt (q : ℝ) *
                (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                Real.sqrt
                  (max (sampledRowEnergyMax Omega X)
                    (sampledColumnEnergyMax Omega X))) ^ q) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCe hCkh
  refine ⟨Ckh * Real.sqrt Cenergy, ?_, ?_⟩
  · positivity
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm hmlb hq1 hqlb hqub hqp hH
  -- Abbreviations
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set n : ℝ := (↑(max n₁ n₂) : ℝ) with hn
  set Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Ω => max (sampledRowEnergyMax Ω X) (sampledColumnEnergyMax Ω X) with hZ
  set C : ℝ := entrySupNorm X with hC
  -- p ∈ [0,1]
  have hp0 : 0 ≤ p := by
    rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp]
    rw [div_le_one (by positivity)]
    calc (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
      _ = (n₁ : ℝ) * (n₂ : ℝ) := by push_cast; ring
  -- Z ≥ 0
  have hZnonneg : ∀ Ω, 0 ≤ Z Ω := by
    intro Ω
    rw [hZ]
    exact le_max_of_le_left (sampledRowEnergyMax_nonneg hn₁ Ω X)
  -- Step 1: rewrite LHS integrand: (k·√(Z))^q = k^q · √(Z^q)
  have hk : (0:ℝ) ≤ Ckh * Real.sqrt (q:ℝ) * p⁻¹ := by positivity
  -- pointwise: (Ckh√q p⁻¹ · √(Z Ω))^q = (Ckh√q p⁻¹)^q · √((Z Ω)^q)
  have hint : ∀ Ω,
      (Ckh * Real.sqrt (q:ℝ) * p⁻¹ * Real.sqrt (Z Ω)) ^ q
        = (Ckh * Real.sqrt (q:ℝ) * p⁻¹) ^ q * Real.sqrt ((Z Ω) ^ q) := by
    intro Ω
    rw [mul_pow]
    congr 1
    rw [sqrt_pow_comm _ (hZnonneg Ω)]
  -- LHS = (k)^q · E[√(Z^q)]
  have hLHS :
      bernoulliExpectation p
          (fun Ω => (Ckh * Real.sqrt (q:ℝ) * p⁻¹ * Real.sqrt (Z Ω)) ^ q)
        = (Ckh * Real.sqrt (q:ℝ) * p⁻¹) ^ q *
            bernoulliExpectation p (fun Ω => Real.sqrt ((Z Ω) ^ q)) := by
    rw [← bernoulliExpectation_const_mul]
    apply congrArg
    funext Ω
    exact hint Ω
  -- Child A: E[√(Z^q)] ≤ √(E[Z^q])
  have hJensen :
      bernoulliExpectation p (fun Ω => Real.sqrt ((Z Ω) ^ q))
        ≤ Real.sqrt (bernoulliExpectation p (fun Ω => (Z Ω) ^ q)) :=
    bernoulli_expectation_sqrt_le_sqrt_expectation p (fun Ω => (Z Ω) ^ q)
      hp0 hp1 (fun Ω => pow_nonneg (hZnonneg Ω) q)
  -- H gives E[Z^q] ≤ (Ce p n C^2)^q, and √ is monotone
  have hHbound : Real.sqrt (bernoulliExpectation p (fun Ω => (Z Ω) ^ q))
      ≤ Real.sqrt ((Cenergy * p * n * C ^ 2) ^ q) := by
    apply Real.sqrt_le_sqrt
    exact hH
  -- √((Ce p n C²)^q) = (Ce p n C²)^(q/2) but keep as √ of a power; combine constants
  -- Chain: LHS = k^q · E[√(Z^q)] ≤ k^q · √(E[Z^q]) ≤ k^q · √((Ce p n C²)^q)
  have hChain :
      bernoulliExpectation p
          (fun Ω => (Ckh * Real.sqrt (q:ℝ) * p⁻¹ * Real.sqrt (Z Ω)) ^ q)
        ≤ (Ckh * Real.sqrt (q:ℝ) * p⁻¹) ^ q *
            Real.sqrt ((Cenergy * p * n * C ^ 2) ^ q) := by
    rw [hLHS]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hk q)
    exact le_trans hJensen hHbound
  -- Now reduce the RHS target to the same closed form and finish by algebra.
  refine le_trans hChain (le_of_eq ?_)
  -- Goal: k^q · √((Ce p n C²)^q) = (Crad · √(qn/p) · C)^q   (Crad = Ckh · √Ce)
  -- nonneg facts
  have hCnn : 0 ≤ C := by
    rw [hC]; unfold entrySupNorm
    refine Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))
  have hnnn : 0 ≤ n := by rw [hn]; positivity
  have hbaseB : 0 ≤ Cenergy * p * n * C ^ 2 := by positivity
  -- √((Ce p n C²)^q) = (√(Ce p n C²))^q
  rw [← sqrt_pow_comm _ hbaseB, ← mul_pow]
  -- now both sides are (·)^q; reduce to base equality
  congr 1
  -- base_L = Ckh√q p⁻¹ · √(Ce p n C²);  base_R = Ckh√Ce · √(qn/p) · C
  -- Expand √(Ce p n C²) = √Ce·√p·√n·√(C²) = √Ce·√p·√n·C
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq hCnn]
  -- base_R: √(qn/p) = √q·√n·√(p⁻¹)
  rw [show ((q:ℝ) * n / p) = (q:ℝ) * n * p⁻¹ by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  -- Now compare; both have √Ce, √q, √n, √p / √(p⁻¹), and the p⁻¹ factor.
  -- Use √(p⁻¹) = (√p)⁻¹ and rearrange.
  rw [Real.sqrt_inv]
  rcases eq_or_lt_of_le hp0 with hp_eq | hp_pos
  · -- p = 0 : both sides reduce to 0
    rw [← hp_eq]; simp
  · have hsp : Real.sqrt p ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt hp0]
