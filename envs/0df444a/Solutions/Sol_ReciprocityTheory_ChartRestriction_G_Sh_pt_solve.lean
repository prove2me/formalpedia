-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_solve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:22.285805+00:00
-- url     : https://prove2.me/submissions/07721a0e-35c0-481a-977c-4f8cf173e57a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptGood_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptGood_lim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptSolveMap_fixed_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptSolveMap_agree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptSolveMap_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
variable {d : ℕ} {σ τ : Type*} [Finite σ]
  (A : (Fin d → MvPowerSeries τ C) → σ → MvPowerSeries τ C)
  (K : Fin d → MvPowerSeries σ C) (M N : Matrix (Fin d) (Fin d) C)
  (f : Fin d → MvPowerSeries τ C)
variable {A K}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (hNM : N * M = 1) (hMN : M * N = 1) (hN : ∀ i j, N i j ∈ ptIntSub v)
    (hf : PTGood v f)
    (hA0 : ∀ x, PTGood v x → ∀ s, constantCoeff (A x s) = 0)
    (hAi : ∀ x, PTGood v x → ∀ s, A x s ∈ ptIntSer v τ)
    (hAag : ∀ k x y, PTGood v x → PTGood v y → PTAgree k x y →
      ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A x s) = coeff e (A y s))
    (hK : ∀ b α, coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y, PTGood v x → PTGood v y → ∀ s ∈ α.support, A x s = A y s)
    (hKi : ∀ b, K b ∈ ptIntSer v σ) (hK0 : ∀ b, constantCoeff (K b) = 0) :
    ∃! x : Fin d → MvPowerSeries τ C,
      PTGood v x ∧ ∀ b, ∑ a, M a b • x a + subst (A x) (K b) = f b := by
  have hag : ∀ k (x y : Fin d → MvPowerSeries τ C), PTGood v x → PTGood v y → PTAgree k x y →
      PTAgree (k + 1) (ptSolveMap A K N f x) (ptSolveMap A K N f y) :=
    fun k x y hx hy hxy => ptSolveMap_agree (N := N) (f := f) hA0 hAag hK k x y hx hy hxy
  have hgood : ∀ x, PTGood v x → PTGood v (ptSolveMap A K N f x) :=
    fun x hx => ptSolveMap_good (N := N) (f := f) hN hf hA0 hAi hKi hK0 x hx
  have hzero : ∀ x y : Fin d → MvPowerSeries τ C, PTAgree 0 x y :=
    fun x y i e he => absurd he (Nat.not_lt_zero _)
  have hmono : ∀ k l (x y : Fin d → MvPowerSeries τ C), l ≤ k → PTAgree k x y → PTAgree l x y :=
    fun k l x y hlk h i e he => h i e (lt_of_lt_of_le he hlk)
  have htrans : ∀ k (x y z : Fin d → MvPowerSeries τ C), PTAgree k x y → PTAgree k y z →
      PTAgree k x z :=
    fun k x y z h1 h2 i e he => (h1 i e he).trans (h2 i e he)
  have hit : ∀ n, PTGood v ((ptSolveMap A K N f)^[n] 0) := by
    intro n
    induction n with
    | zero => exact ptGood_zero
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hgood _ ih
  have hstep : ∀ k, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + 1] 0) := by
    intro k
    induction k with
    | zero => exact hzero _ _
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (k + 1)]
      exact hag k _ _ (hit k) (hit (k + 1)) ih
  have hchain : ∀ k m, PTAgree k ((ptSolveMap A K N f)^[k] 0) ((ptSolveMap A K N f)^[k + m] 0) := by
    intro k m
    induction m with
    | zero => exact fun i e he => rfl
    | succ m ih =>
      exact htrans k _ _ _ ih (hmono (k + m) k _ _ (Nat.le_add_right k m) (hstep (k + m)))
  let x : Fin d → MvPowerSeries τ C :=
    fun i e => coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i)
  have hx : ∀ n, PTAgree n x ((ptSolveMap A K N f)^[n] 0) := by
    intro n i e he
    show coeff e ((ptSolveMap A K N f)^[e.degree + 1] 0 i) = _
    have hle : e.degree + 1 ≤ n := he
    have h1 := hchain (e.degree + 1) (n - (e.degree + 1))
    rw [Nat.add_sub_cancel' hle] at h1
    exact h1 i e (Nat.lt_succ_self _)
  have hxg : PTGood v x := ptGood_lim hit x hx
  have hfix : ptSolveMap A K N f x = x := by
    apply PTAgree.eq
    intro k
    cases k with
    | zero => exact hzero _ _
    | succ k =>
      have h1 : PTAgree (k + 1) (ptSolveMap A K N f x) ((ptSolveMap A K N f)^[k + 1] 0) := by
        rw [Function.iterate_succ_apply']
        exact hag k _ _ hxg (hit k) (hx k)
      exact htrans _ _ _ _ h1 (fun i e he => ((hx (k + 1)) i e he).symm)
  refine ⟨x, ⟨hxg, (ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f)
    hNM hMN x).mp hfix⟩, ?_⟩
  rintro y ⟨hyg, hy⟩
  have hyfix := (ptSolveMap_fixed_iff (A := A) (K := K) (M := M) (N := N) (f := f)
    hNM hMN y).mpr hy
  apply PTAgree.eq
  intro k
  induction k with
  | zero => exact hzero _ _
  | succ k ih =>
    have h2 := hag k y x hyg hxg ih
    rwa [hyfix, hfix] at h2
end ReciprocityTheory.ChartRestriction.G.Sh
