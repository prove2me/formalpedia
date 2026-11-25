-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_cycle_of_mul_d4b13781df53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:26.398835+00:00
-- url     : https://prove2.me/submissions/5a1b5ae3-c668-4ed2-acb1-ccbf0271fdee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowHeightCycleEq
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (μ : InfinitePlace K → Measure (Fin (e + 1) × Fin n → ℂ))
    (hμ : ∀ (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (δ₁ δ₂ : ℕ), f ≠ 0 → g ≠ 0 →
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (f * g) (δ₁ + δ₂) =
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ f δ₁ + ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ g δ₂)
    {ι : Type} (Z : ι →₀ ℕ) (f : ι → MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ι → ℕ)
    (hf : ∀ i ∈ Z.support, f i ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z f) (Z.sum fun i m => m * δ i) =
      Z.sum fun i m => (m : ℝ) * ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (f i) (δ i) := by
  classical
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (1 : MvPolynomial (Fin (e + 1) × Fin n) K) 0 = 0 := by
    have := hμ 1 1 0 0 one_ne_zero one_ne_zero
    simp only [mul_one, add_zero] at this
    linarith
  have hpow : ∀ (g : MvPolynomial (Fin (e + 1) × Fin n) K) (d : ℕ), g ≠ 0 → ∀ m : ℕ,
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (g ^ m) (m * d) = m * ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ g d := by
    intro g d hg m
    induction m with
    | zero => simpa using h1
    | succ m ih =>
      rw [pow_succ, Nat.succ_mul, hμ _ _ _ _ (pow_ne_zero _ hg) hg, ih]
      push_cast
      ring
  have key : ∀ s : Finset ι, (∀ i ∈ s, f i ≠ 0) →
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (∏ i ∈ s, f i ^ Z i) (∑ i ∈ s, Z i * δ i) =
        ∑ i ∈ s, (Z i : ℝ) * ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (f i) (δ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using h1
    | insert a s ha ih =>
      intro hs
      have hfa := hs a (Finset.mem_insert_self a s)
      have hrest : ∀ i ∈ s, f i ≠ 0 := fun i hi => hs i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
        hμ _ _ _ _ (pow_ne_zero _ hfa)
          (Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hrest i hi)),
        hpow _ _ hfa, ih hrest]
  exact key Z.support hf
end GroundTheory.Heights₂.Heights.ChowHeightCycleEq
