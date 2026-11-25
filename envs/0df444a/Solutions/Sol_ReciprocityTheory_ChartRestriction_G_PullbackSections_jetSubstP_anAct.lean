-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_anAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:55:45.208386+00:00
-- url     : https://prove2.me/submissions/33afe9b3-8816-4d7b-9f65-63051c2bf7f3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
variable [Algebra c.F ℂ]
variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) (a : 𝓞 E) (b : Jet ℂ (Fin 1 × Fin g) m) :
    jetSubstP m (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) b =
      jetScaleP m (fun k => ty k (a : E)) b := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  unfold jetSubstP jetScaleP
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk]
  have key : ∀ p : Fin 1 × Fin g,
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (psTrunc m (anAct ty a p.2) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2)))) =
      Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1))
        (MvPolynomial.C (ty p.2 (a : E)) * MvPolynomial.X p) := by
    rintro ⟨i, k⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    set q : Fin 1 × Fin g := ((0 : Fin 1), k) with hq
    have hps : psTrunc m (anAct ty a k) =
        if Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) then
          MvPolynomial.C (ty k (a : E)) * MvPolynomial.X q else 0 := by
      unfold psTrunc anAct
      by_cases hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ))
      · rw [if_pos hmem, Finset.sum_eq_single (Finsupp.single q 1)]
        · simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, MvPolynomial.C_mul_X_eq_monomial, hq]
        · intro e _ he
          simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, he]
        · intro h
          exact absurd hmem h
      · rw [if_neg hmem]
        apply Finset.sum_eq_zero
        intro e he
        have hne : e ≠ Finsupp.single q 1 := fun h => hmem (h ▸ he)
        simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ← hq, hne]
    rw [hps]
    by_cases hm0 : m = 0
    · subst hm0
      have hnot : Finsupp.single q 1 ∉ (degLE 0 : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        intro hmem
        rw [degLE, Finset.mem_filter] at hmem
        have := hmem.2
        rw [Finsupp.sum_single_index rfl] at this
        omega
      rw [if_neg hnot]
      simp only [map_zero, sub_zero]
      symm
      rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
    · have hmem : Finsupp.single q 1 ∈ (degLE m : Finset ((Fin 1 × Fin g) →₀ ℕ)) := by
        rw [degLE, Finset.mem_filter, Finsupp.sum_single_index rfl]
        refine ⟨Finset.mem_image.2 ⟨fun j => if j = q then ⟨1, by omega⟩ else 0, Finset.mem_univ _, ?_⟩, by omega⟩
        ext j
        by_cases hj : j = q
        · subst hj
          simp
        · simp [hj, Finsupp.single_apply, Ne.symm hj]
      rw [if_pos hmem]
      simp [MvPolynomial.constantCoeff_X, hq]
  show (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f) = (Ideal.Quotient.mkₐ ℂ _) (MvPolynomial.aeval _ f)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
  congr 2
  funext p
  exact key p
end ReciprocityTheory.ChartRestriction.G.PullbackSections
