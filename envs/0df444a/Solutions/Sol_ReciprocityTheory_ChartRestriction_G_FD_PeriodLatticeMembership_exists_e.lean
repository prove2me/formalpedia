-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.exists_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:04:56.080078+00:00
-- url     : https://prove2.me/submissions/614ed336-d851-4809-a108-9d1f5f20f175

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r)
variable {X}
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
theorem _root_.solution (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) (hωi : LinearIndependent ℝ ω) :
    ∃ e : (Fin (Fintype.card X.Ψ) → ℤ) → (X.Ψ → ℝ), (∀ k j, 2 * ∑ τ, e k τ * ω j τ = k j) ∧
      Function.Injective e ∧ (∀ k k', e (k - k') = e k - e k') ∧
      ∀ ν : X.Ψ → ℝ, (∀ j, ∃ n : ℤ, 2 * ∑ τ, ν τ * ω j τ = n) → ∃ k, e k = ν := by
  classical
  let W : Matrix (Fin (Fintype.card X.Ψ)) X.Ψ ℝ := Matrix.of fun j τ => 2 * ω j τ
  have hA : ∀ ν j, (W.mulVecLin ν) j = 2 * ∑ τ, ν τ * ω j τ := by
    intro ν j
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, W, Matrix.of_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hspan : Submodule.span ℝ (Set.range ω) = ⊤ := by
    rcases isEmpty_or_nonempty (Fin (Fintype.card X.Ψ)) with hE | hE
    · have h0 : Fintype.card X.Ψ = 0 := Nat.eq_zero_of_not_pos (fun h => hE.false ⟨0, h⟩)
      have hΨ : IsEmpty X.Ψ := Fintype.card_eq_zero_iff.mp h0
      exact Subsingleton.elim _ _
    · exact hωi.span_eq_top_of_card_eq_finrank (by simp)
  have hinj : Function.Injective W.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ν hν
    have h0 : ∀ j, ∑ τ, ν τ * ω j τ = 0 := by
      intro j
      have h1 := congrFun hν j
      rw [hA] at h1
      simpa using h1
    let φ : (X.Ψ → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun w => ∑ τ, ν τ * w τ
        map_add' := by
          intro a b
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c a
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          ring }
    have hle : Submodule.span ℝ (Set.range ω) ≤ LinearMap.ker φ :=
      Submodule.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        exact LinearMap.mem_ker.mpr (h0 j))
    have hmem : ν ∈ Submodule.span ℝ (Set.range ω) := by
      rw [hspan]
      exact Submodule.mem_top
    have hsq : ∑ τ, ν τ * ν τ = 0 := LinearMap.mem_ker.mp (hle hmem)
    funext τ
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => mul_self_nonneg (ν τ))).mp hsq τ
      (Finset.mem_univ τ)
    exact mul_self_eq_zero.mp h2
  have hsurj : Function.Surjective W.mulVecLin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  let L := LinearEquiv.ofBijective W.mulVecLin ⟨hinj, hsurj⟩
  have hL : ∀ ν j, L ν j = 2 * ∑ τ, ν τ * ω j τ := fun ν j => hA ν j
  refine ⟨fun k => L.symm (fun j => (k j : ℝ)), ?_, ?_, ?_, ?_⟩
  · intro k j
    show 2 * ∑ τ, L.symm (fun j => (k j : ℝ)) τ * ω j τ = k j
    rw [← hL, L.apply_symm_apply]
  · intro k k' h
    have h' : L.symm (fun j => (k j : ℝ)) = L.symm (fun j => (k' j : ℝ)) := h
    have h1 := L.symm.injective h'
    funext j
    exact_mod_cast congrFun h1 j
  · intro k k'
    show L.symm (fun j => (((k - k') j : ℤ) : ℝ)) =
      L.symm (fun j => (k j : ℝ)) - L.symm (fun j => (k' j : ℝ))
    rw [show (fun j => (((k - k') j : ℤ) : ℝ)) = (fun j => (k j : ℝ)) - (fun j => (k' j : ℝ)) by
      funext j
      simp]
    exact map_sub L.symm _ _
  · intro ν hν
    choose n hn using hν
    refine ⟨n, ?_⟩
    show L.symm (fun j => (n j : ℝ)) = ν
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [hL]
    exact (hn j).symm
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
