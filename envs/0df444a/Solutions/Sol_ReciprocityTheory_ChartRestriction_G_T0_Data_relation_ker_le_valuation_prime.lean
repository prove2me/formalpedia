-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.relation_ker_le_valuation_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:55.886039+00:00
-- url     : https://prove2.me/submissions/c50abca2-270f-42a9-93d7-4518eb0a309f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_relation_section_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (p : Ideal (KTp K d.D d.N))
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hpos : 0 < w (d.rationalBaseRow c))
    (Q : KTp K d.D d.N) (hQ : d.relationEliminateColumn c Q = 0) : Q ∈ p := by
  set Ψ : MvPolynomial (TVar d.D d.N) (Ω c) →ₐ[Ω c] OmS (Ω c) d.D d.N :=
    MvPolynomial.aeval (sImg (d.jc c) (d.x c)) with hΨ
  have htop : (0 : WithTop ℤ) < ⊤ := WithTop.coe_lt_top 0
  have hsHX : ∀ n : TVar d.D d.N, d.sH c (MvPolynomial.X n) = sImg (d.jc c) (d.x c) n :=
    fun n => MvPolynomial.aeval_X _ _
  have hΨX : ∀ n : TVar d.D d.N, Ψ (MvPolynomial.X n) = sImg (d.jc c) (d.x c) n :=
    fun n => MvPolynomial.aeval_X _ _
  have hΨs : ∀ n : TVar d.D d.N, Ψ (MvPolynomial.X n) = d.sH c (MvPolynomial.X n) :=
    fun n => (hΨX n).trans (hsHX n).symm
  have hΨC : ∀ r : Ω c, Ψ (MvPolynomial.C r) = algebraMap (Ω c) (OmS (Ω c) d.D d.N) r :=
    fun r => MvPolynomial.aeval_C _ _
  have hnn : ∀ x : KTp K d.D d.N, 0 ≤ w (d.sH c x) := fun x => (hw.2 x).1
  have key : ∀ R : KTp K d.D d.N, 0 < w (d.sH c R - Ψ (d.relationEliminateColumn c R)) := by
    intro R
    induction R using MvPolynomial.induction_on
    next a =>
      have e1 : d.sH c (MvPolynomial.C a) = algebraMap K (OmS (Ω c) d.D d.N) a := by
        rw [← MvPolynomial.algebraMap_eq]
        exact (d.sH c).commutes a
      have e2 : d.relationEliminateColumn c (MvPolynomial.C a) =
          algebraMap K (MvPolynomial (TVar d.D d.N) (Ω c)) a := by
        rw [← MvPolynomial.algebraMap_eq]
        exact (d.relationEliminateColumn c).commutes a
      rw [e1, e2, IsScalarTower.algebraMap_apply K (Ω c) (MvPolynomial (TVar d.D d.N) (Ω c)) a,
        AlgHom.commutes, ← IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N) a, sub_self,
        AddValuation.map_zero]
      exact htop
    next P₁ P₂ h₁ h₂ =>
      simp only [map_add]
      rw [add_sub_add_comm]
      exact lt_of_lt_of_le (lt_min h₁ h₂) (AddValuation.map_add _ _ _)
    next P n hP =>
      have hXn : 0 < w (d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c (MvPolynomial.X n))) := by
        obtain ⟨i, j⟩ := n
        have hr : d.relationEliminateColumn c (MvPolynomial.X (i, j)) = if j = d.jc c then
            -∑ k ∈ Finset.univ.erase (d.jc c), MvPolynomial.X (i, k) *
              MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c))
            else MvPolynomial.X (i, j) := MvPolynomial.aeval_X _ _
        rw [hr]
        split_ifs with hj
        · subst hj
          rw [map_neg, map_sum, sub_neg_eq_add]
          simp only [map_mul, hΨs, hΨC]
          rw [relation_section_identity d hd c i]
          split_ifs with hi
          · exact hpos
          · rw [AddValuation.map_zero]
            exact htop
        · rw [hΨs, sub_self, AddValuation.map_zero]
          exact htop
      simp only [map_mul]
      have e : d.sH c P * d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c P) * Ψ (d.relationEliminateColumn c (MvPolynomial.X n)) =
          d.sH c P * (d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c (MvPolynomial.X n))) +
            (d.sH c P - Ψ (d.relationEliminateColumn c P)) * Ψ (d.relationEliminateColumn c (MvPolynomial.X n)) := by ring
      rw [e]
      have hb : 0 ≤ w (Ψ (d.relationEliminateColumn c (MvPolynomial.X n))) := by
        have h3 := AddValuation.map_sub w (d.sH c (MvPolynomial.X n))
          (d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c (MvPolynomial.X n)))
        rw [sub_sub_cancel] at h3
        exact le_trans (le_min (hnn _) hXn.le) h3
      refine lt_of_lt_of_le (lt_min ?_ ?_) (AddValuation.map_add _ _ _)
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hXn (le_add_of_nonneg_left (hnn P))
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hP (le_add_of_nonneg_right hb)
  have h := key Q
  rw [hQ, map_zero, sub_zero] at h
  exact ((hw.2 Q).2).1 h
end ReciprocityTheory.ChartRestriction.G.T0.Data
