-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_dualEv_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:34.081082+00:00
-- url     : https://prove2.me/submissions/5692814e-70f5-40db-9614-41c7e2b6d952

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_dualEv_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p v : Fin n → ℂ)
    (hK : ∀ k ∈ K, dualEv p v k = 0) :
    ∃ χ : locRing K p →+* DualNumber ℂ,
      ∀ x, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x) = dualEv p v x := by
  have hunit : ∀ y : (ptIdeal p).primeCompl, IsUnit ((dualEv p v).toRingHom (y : MvPolynomial (Fin n) ℂ)) := by
    intro y
    refine TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ?_
    have hy : eval p (y : MvPolynomial (Fin n) ℂ) ≠ 0 := fun h => y.2 (RingHom.mem_ker.2 h)
    have := dualEv_fst p v (y : MvPolynomial (Fin n) ℂ)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [this]
    exact hy.isUnit
  let g : locPt p →+* DualNumber ℂ := IsLocalization.lift (M := (ptIdeal p).primeCompl) hunit
  have hg : ∀ x, g (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p) x) = dualEv p v x := fun x =>
    IsLocalization.lift_eq hunit x
  have hK' : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≤ RingHom.ker g := by
    rw [Ideal.map_le_iff_le_comap]
    intro k hk
    rw [Ideal.mem_comap, RingHom.mem_ker, hg]
    exact hK k hk
  refine ⟨Ideal.Quotient.lift _ g (fun a ha => RingHom.mem_ker.1 (hK' ha)), fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ) (locPt p) (locRing K p),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk, hg]
end ReciprocityTheory.AnForm.R
