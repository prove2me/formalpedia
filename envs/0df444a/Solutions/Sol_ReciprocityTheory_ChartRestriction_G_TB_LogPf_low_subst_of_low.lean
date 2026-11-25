-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.low_subst_of_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:12.267122+00:00
-- url     : https://prove2.me/submissions/42f4da54-8f7c-4231-ba3c-d7dee87f6311

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.FG.SolveVAux
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {σ τ : Type}
private theorem low_mul_lemma {m n : ℕ} {f g : MvPowerSeries τ k} (hf : Low m f) (hg : Low n g) :
    Low (m + n) (f * g) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  | simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  | simp only [Finset.mem_antidiagonal] at hx
  have e : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree d := by
    rw [← hx]
    first
    | exact (map_add _ _ _).symm
    | simp [Finsupp.degree, Finsupp.sum_add_index']
  by_cases h1 : Finsupp.degree x.1 < m
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]
private theorem low_pow_lemma_2 {f : MvPowerSeries τ k} (hf : Low 1 f) (n : ℕ) : Low n (f ^ n) := by
  induction n with
  | zero => intro d hd; omega
  | succ n ih => rw [pow_succ]; exact low_mul_lemma ih hf
private theorem low_prod_lemma_3 {a : σ → MvPowerSeries τ k} (ha : ∀ s, Low 1 (a s)) (e : σ →₀ ℕ)
    (S : Finset σ) : Low (∑ s ∈ S, e s) (∏ s ∈ S, a s ^ e s) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · intro d hd
    simp at hd
  · intro s S hs ih
    rw [Finset.sum_insert hs, Finset.prod_insert hs]
    exact low_mul_lemma (low_pow_lemma_2 (ha s) _) ih
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.FG.SolveVAux
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {σ τ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution [Finite σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, Low 1 (a s)) {N : ℕ}
    {g : MvPowerSeries σ k} (hg : Low N g) : Low N (subst a g) := by
  classical
  have hc : ∀ s, constantCoeff (a s) = 0 := fun s => by
    have h0 := ha s 0 (by simp)
    simpa using h0
  intro d hd
  have hS : HasSubst a := by
    exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  rw [MvPowerSeries.coeff_subst hS]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e.degree < N
  · exact smul_eq_zero_of_left (hg e he) _
  · have hl : Low e.degree (e.prod fun s n => a s ^ n) := by
      have h := low_prod_lemma_3 ha e e.support
      have hdeg : e.degree = ∑ s ∈ e.support, e s := by
        first
        | rfl
        | exact Finsupp.degree_eq_sum e
        | simp [Finsupp.degree]
      rw [hdeg]
      exact h
    exact smul_eq_zero_of_right _ (hl d (by omega))
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
