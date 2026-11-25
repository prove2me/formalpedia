-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.scale_sImg_expr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:50.500136+00:00
-- url     : https://prove2.me/submissions/7854c305-6f07-41b6-ac97-d113bd494260

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleEquiv_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleEquiv_C
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Scale
variable {S σ : Type*} [CommRing S]
end Scale
section Blocks
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
private theorem prop_insertNth_of_forall {n : ℕ} {M : Type*} (Q : M → Prop) (j₀ : Fin (n + 1))
    (a : M) (f : Fin n → M) (ha : Q a) (hf : ∀ k, Q (f k)) (j : Fin (n + 1)) :
    Q (Fin.insertNth (α := fun _ => M) j₀ a f j) := by
  by_cases hj : j = j₀
  · subst hj
    rw [Fin.insertNth_apply_same]
    exact ha
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [Fin.insertNth_apply_succAbove]
    exact hf k
end Blocks
section Norm
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
end Norm
namespace Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (NumberField.RingOfIntegers K) (A c)]
variable (d : Data K ι Ω WT A)
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin (D + 1)) (hb : b ≠ 0) (u : Ωˣ) (j₀ : Fin (N + 1))
    (x : Fin N → Ω) (p : TVar D N) :
    scaleEquiv (InBlock (D := D) (N := N) b) u
      (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
        (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
          else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
        (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2) =
      (if p.1 = b then C (u : Ω) else 1) *
      Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
        (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
          else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
        (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2 := by
  obtain ⟨i, j⟩ := p
  have hX : ∀ k : Fin N, scaleEquiv (InBlock (D := D) (N := N) b) u
      (MvPolynomial.X (Sum.inr (i, k))) =
        (if i = b then C (u : Ω) else 1) * MvPolynomial.X (Sum.inr (i, k)) := by
    intro k
    rw [scaleEquiv_X]
    by_cases h : i = b
    · simp [InBlock, h]
    · simp [InBlock, h]
  have hA : scaleEquiv (InBlock (D := D) (N := N) b) u
      (if i = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (x k)) =
      (if i = b then C (u : Ω) else 1) *
        (if i = 0 then MvPolynomial.X (Sum.inl ())
          else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (x k)) := by
    by_cases h0 : i = 0
    · subst h0
      have hb' : ¬ ((0 : Fin (D + 1)) = b) := fun h => hb h.symm
      rw [if_pos rfl, if_neg hb', one_mul, scaleEquiv_X]
      simp [InBlock]
    · rw [if_neg h0, map_neg, map_sum, mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hX, scaleEquiv_C, mul_assoc]
  exact prop_insertNth_of_forall
    (fun m => scaleEquiv (InBlock (D := D) (N := N) b) u m = (if i = b then C (u : Ω) else 1) * m)
    j₀ _ _ hA hX j
end ReciprocityTheory.ChartRestriction.G.T0
