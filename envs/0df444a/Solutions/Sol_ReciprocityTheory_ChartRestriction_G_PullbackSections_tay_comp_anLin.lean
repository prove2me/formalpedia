-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.tay_comp_anLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:11:11.636318+00:00
-- url     : https://prove2.me/submissions/f8847d52-90df-4533-876a-e6f1784ab74e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anLin_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anLin_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_IsTayF_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_sum_single_smul


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
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {g g' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) :
    tay (θ ∘ A) 0 = MvPowerSeries.subst (fun p => ((anLin A p : MvPolynomial (Fin 1 × Fin g') ℂ) :
      MvPowerSeries (Fin 1 × Fin g') ℂ)) (tay θ 0) := by
  have hθ' : ContDiffAt ℂ ω θ (A 0) := by rw [map_zero]; exact hθ
  have hA : ContDiffAt ℂ ω (θ ∘ A) 0 := hθ'.comp (0 : Fin g' → ℂ) A.contDiff.contDiffAt
  have hv : ∀ q : Fin 1 × Fin g', A (Pi.single q.2 1) =
      ∑ p : Fin 1 × Fin g, A (Pi.single q.2 1) p.2 • (Pi.single p.2 1 : Fin g → ℂ) := by
    intro q
    rw [Fintype.sum_prod_type, Fin.sum_univ_one]
    exact sum_single_smul _
  have hLd : ∀ (p : Fin 1 × Fin g) (q : Fin 1 × Fin g'),
      MvPowerSeries.pderiv ℂ q ((anLin A p : MvPolynomial (Fin 1 × Fin g') ℂ) : MvPowerSeries (Fin 1 × Fin g') ℂ) =
        MvPowerSeries.C (A (Pi.single q.2 1) p.2) := by
    intro p q
    obtain ⟨a, j⟩ := q
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    rw [anLin_coe, map_sum, Finset.sum_eq_single j]
    · rw [Derivation.leibniz, MvPowerSeries.pderiv_C, smul_zero, add_zero, MvPowerSeries.pderiv_X, smul_eq_mul]
      simp
    · intro k _ hk
      rw [Derivation.leibniz, MvPowerSeries.pderiv_C, smul_zero, add_zero, MvPowerSeries.pderiv_X, smul_eq_mul]
      simp [Prod.ext_iff, hk]
    · simp
  exact (TCPf.isTayF_tay hA).eq (TCPf.isTayF_comp hθ A hv (TCPf.isTayF_subst θ hθ _ _ (anLin_cc A) hLd))
end ReciprocityTheory.ChartRestriction.G.PullbackSections
