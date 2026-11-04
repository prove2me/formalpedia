-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P18.pureState_marginalEntropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-03T22:44:20.010023+00:00
-- url     : https://prove2.me/submissions/12a9640c-c00d-4d0d-8d64-4e15e62264a6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_finiteEntropy_mul_conjTranspose_eq_transpose
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_finiteEntropy_mono_of_posSemidef
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_finiteEntropy_tendsto

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18
open scoped Matrix ComplexOrder
/-! Reduction. -/

/-- Products of ℓ² coordinates along two injective reindexings are summable. -/
theorem pme_summable {K T : Type} (u : Hilbert K) (e1 e2 : T → K)
    (h1 : Function.Injective e1) (h2 : Function.Injective e2) :
    Summable (fun t => u (e1 t) * star (u (e2 t))) := by
  have hs : Summable (fun k => ‖u k‖ ^ 2) := by
    have := (lp.memℓp u).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    simpa using this
  refine Summable.of_norm_bounded ((hs.comp_injective h1).add (hs.comp_injective h2)) ?_
  intro t
  rw [norm_mul, norm_star]
  have := two_mul_le_add_sq ‖u (e1 t)‖ ‖u (e2 t)‖
  simp only [Function.comp]
  nlinarith [norm_nonneg (u (e1 t)), norm_nonneg (u (e2 t))]

/-- The finite block `u(i,r)`, `i ∈ s`, `r ∈ t`. -/
def pmeBlock {I J : Type} (u : I × J → ℂ) (s : Finset I) (t : Finset J) : Matrix s t ℂ :=
  fun i r => u (i.1, r.1)

theorem pme_block_apply {I J : Type} (u : I × J → ℂ) (s : Finset I) (t : Finset J) (i j : s) :
    (pmeBlock u s t * (pmeBlock u s t)ᴴ) i j = ∑ r ∈ t, u (i.1, r) * star (u (j.1, r)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pmeBlock]
  exact Finset.sum_coe_sort t (fun r => u (i.1, r) * star (u (j.1, r)))

/-- Enlarging the second window adds a positive semidefinite term. -/
theorem pme_mono {I J : Type} (u : I × J → ℂ) (s : Finset I) :
    Monotone (fun t : Finset J => finiteEntropy (pmeBlock u s t * (pmeBlock u s t)ᴴ)) := by
  intro t t' htt
  refine finiteEntropy_mono_of_posSemidef (Matrix.posSemidef_self_mul_conjTranspose _) ?_
  let V : Matrix s t' ℂ := fun i r => if r.1 ∈ t then 0 else u (i.1, r.1)
  have hV : pmeBlock u s t' * (pmeBlock u s t')ᴴ - pmeBlock u s t * (pmeBlock u s t)ᴴ =
      V * Vᴴ := by
    ext i j
    rw [Matrix.sub_apply, pme_block_apply, pme_block_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    change _ = ∑ r : t', (if r.1 ∈ t then (0 : ℂ) else u (i.1, r.1)) *
      star (if r.1 ∈ t then (0 : ℂ) else u (j.1, r.1))
    rw [Finset.sum_coe_sort t' (fun r => (if r ∈ t then 0 else u (i.1, r)) *
      star (if r ∈ t then 0 else u (j.1, r)))]
    have key : ∀ r, (if r ∈ t then (0 : ℂ) else u (i.1, r)) *
        star (if r ∈ t then 0 else u (j.1, r)) =
        u (i.1, r) * star (u (j.1, r)) -
          (if r ∈ t then u (i.1, r) * star (u (j.1, r)) else 0) := by
      intro r; split_ifs <;> simp
    simp only [key, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.mpr htt]
  show (pmeBlock u s t' * (pmeBlock u s t')ᴴ - pmeBlock u s t * (pmeBlock u s t)ᴴ).PosSemidef
  rw [hV]; exact Matrix.posSemidef_self_mul_conjTranspose _

/-- One compression of a partial trace is the supremum over finite second windows. -/
theorem pme_side {I J : Type} (u : I × J → ℂ)
    (hsum : ∀ i j, Summable (fun r => u (i, r) * star (u (j, r)))) (s : Finset I) :
    finiteEntropy (coordinateCompression s (fun i j : I => ∑' r : J, u (i, r) * star (u (j, r)))) =
      ⨆ t : Finset J, finiteEntropy (pmeBlock u s t * (pmeBlock u s t)ᴴ) := by
  have hT : Tendsto (fun t : Finset J => pmeBlock u s t * (pmeBlock u s t)ᴴ) atTop
      (nhds (coordinateCompression s (fun i j : I => ∑' r : J, u (i, r) * star (u (j, r))))) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [pme_block_apply]
    exact (hsum i.1 j.1).hasSum
  have h1 := finiteEntropy_tendsto (Eventually.of_forall
    (fun t => Matrix.posSemidef_self_mul_conjTranspose (pmeBlock u s t))) hT
  exact tendsto_nhds_unique h1 (tendsto_atTop_iSup (pme_mono u s))

theorem pme_main {I J : Type} [Countable I] [Countable J]
    (psi : PureState (I × J)) :
    homogeneousEntropy (traceSecond psi.val.coefficients) =
      homogeneousEntropy (traceFirst psi.val.coefficients) := by
  obtain ⟨u, -, hu⟩ := psi.property
  rw [hu]
  have hA : ∀ s : Finset I, finiteEntropy (coordinateCompression s (traceSecond (rankOne u))) =
      ⨆ t : Finset J, finiteEntropy (pmeBlock (⇑u) s t * (pmeBlock (⇑u) s t)ᴴ) := fun s =>
    pme_side (⇑u) (fun i j => pme_summable u (fun r => (i, r)) (fun r => (j, r))
      (fun _ _ h => (Prod.ext_iff.1 h).2) (fun _ _ h => (Prod.ext_iff.1 h).2)) s
  have hB : ∀ t : Finset J, finiteEntropy (coordinateCompression t (traceFirst (rankOne u))) =
      ⨆ s : Finset I, finiteEntropy (pmeBlock (fun p : J × I => u (p.2, p.1)) t s *
        (pmeBlock (fun p : J × I => u (p.2, p.1)) t s)ᴴ) := fun t =>
    pme_side (fun p : J × I => u (p.2, p.1)) (fun i j => pme_summable u (fun r => (r, i))
      (fun r => (r, j)) (fun _ _ h => (Prod.ext_iff.1 h).1) (fun _ _ h => (Prod.ext_iff.1 h).1)) t
  unfold homogeneousEntropy
  simp only [hA, hB]
  rw [iSup_comm]
  refine iSup_congr fun t => iSup_congr fun s => ?_
  exact finiteEntropy_mul_conjTranspose_eq_transpose (pmeBlock (⇑u) s t)

end QAlgorithms.Papers.Independent.Claimed50.P18

open QAlgorithms.Papers.Independent.Claimed50.P18 in
theorem solution {I J : Type} [Countable I] [Countable J]
    (psi : PureState (I × J)) :
    homogeneousEntropy (traceSecond psi.val.coefficients) =
      homogeneousEntropy (traceFirst psi.val.coefficients) :=
  pme_main psi
