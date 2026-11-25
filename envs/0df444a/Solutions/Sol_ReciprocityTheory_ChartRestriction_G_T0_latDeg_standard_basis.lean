-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.latDeg_standard_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:10:28.766252+00:00
-- url     : https://prove2.me/submissions/2ec2208e-2d6c-49e6-b4de-0a318ec9bded

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_pi_single_one_mem_hStd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hStd_eq_span_pi_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_standardLattice_fg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_latDegBasis_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {n : ℕ} (h : n = r) (v : Fin n → Fin r → K)
    (hv : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn (hStd K r) v) :
    ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) v = 0 := by
  classical
  let std : Fin n → Fin r → K := fun i => Pi.single (finCongr h i) 1
  have hstd_eq : std = ⇑(Pi.basisFun K (Fin r)) ∘ finCongr h := by
    funext i
    simp [std]
  have hrange : Set.range std = Set.range fun i : Fin r => (Pi.single i (1 : K) : Fin r → K) := by
    rw [hstd_eq, (finCongr h).surjective.range_comp]
    ext x
    simp
  have hstd : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn (hStd K r) std := by
    refine ⟨fun i => pi_single_one_mem_hStd _, ?_, fun x _ => ?_⟩
    · rw [hstd_eq]
      exact (Pi.basisFun K (Fin r)).linearIndependent.comp _ (finCongr h).injective
    · rw [hstd_eq, (finCongr h).surjective.range_comp, (Pi.basisFun K (Fin r)).span_eq]
      trivial
  rw [ReciprocityTheory.MultiplicativeHeights.latDegBasis_holds K r n _ (hStd K r) v std (fun _ => PosDef.one) standardLattice_fg
    hv hstd]
  have hspan : Submodule.span (𝓞 K) (Set.range std) = hStd K r := by
    rw [hrange, hStd_eq_span_pi_single]
  have hgram : ∀ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.gramC 1 σ std = 1 := by
    intro σ
    ext i j
    simp only [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, Matrix.of_apply, one_mulVec, dotProduct,
      Pi.star_apply, std, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single (finCongr h i)]
      · simp
      · intro l _ hl
        have hl' : ¬ l = Fin.cast h i := hl
        simp [Pi.single_apply, hl']
      · simp
    · rw [if_neg hij]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = finCongr h i
      · have : l ≠ finCongr h j := by
          rw [hl]; exact fun e => hij ((finCongr h).injective e)
        have this' : ¬ l = Fin.cast h j := this
        simp [Pi.single_apply, this']
      · have hl' : ¬ l = Fin.cast h i := hl
        simp [Pi.single_apply, hl']
  simp only [ReciprocityTheory.MultiplicativeHeights.latDeg, hspan, AddSubgroup.relIndex_self, Nat.cast_one, Real.log_one,
    hgram, det_one, Complex.one_re, Finset.sum_const_zero, mul_zero, sub_zero]
end ReciprocityTheory.ChartRestriction.G.T0
