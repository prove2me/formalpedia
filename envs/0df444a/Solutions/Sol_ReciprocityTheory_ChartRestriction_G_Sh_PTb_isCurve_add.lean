-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:37:14.019404+00:00
-- url     : https://prove2.me/submissions/144b6fb4-b2de-42c0-8bad-c896f2989892

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_mvIsInt_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_psIsInt_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
private theorem hs_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact hasSubst_of_constantCoeff_zero ha0
  | exact HasSubst.of_constantCoeff_zero' ha0
  | exact hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
  | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
private theorem cc_lemma_3 {σ τ : Type} [Finite σ] {f : MvPowerSeries σ C}
    (hf : constantCoeff f = 0) {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) : constantCoeff (subst a f) = 0 := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst (hs_lemma_2 ha0)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · rw [he, coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext fun s => by simpa using h s)
    have hp : constantCoeff (e.prod fun s n => a s ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, ha0 s, zero_pow hs])
    rw [coeff_zero_eq_constantCoeff_apply, hp, smul_zero]
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) {ga gb : Fin d → PowerSeries C}
    (ha : IsCurve v ga) (hb : IsCurve v gb) : IsCurve v (G.add ga gb) := by
  intro a
  have hs0 : ∀ s, constantCoeff (Sum.elim ga gb s) = 0 := by
    rintro (s | s)
    · exact (ha s).1
    · exact (hb s).1
  have hsI : ∀ s, MvIsInt v (Sum.elim ga gb s) := by
    rintro (s | s)
    · exact psIsInt_iff.mp (ha s).2
    · exact psIsInt_iff.mp (hb s).2
  exact ⟨cc_lemma_3 (G.F_const a) hs0, psIsInt_iff.mpr (mvIsInt_subst v (G.F_int a) hsI hs0)⟩
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
