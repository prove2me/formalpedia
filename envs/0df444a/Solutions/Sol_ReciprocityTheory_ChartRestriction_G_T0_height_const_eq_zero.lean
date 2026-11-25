-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.height_const_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:43.861548+00:00
-- url     : https://prove2.me/submissions/a0a8a4de-9f6c-483b-b112-188540df6794

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_blockSphereProb_isProbabilityMeasure

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
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : K) :
    ReciprocityTheory.MultiplicativeHeights.h0 (MvPolynomial.C a : MvPolynomial (Fin B × Fin n) K) = 0 := by
  classical
  unfold ReciprocityTheory.MultiplicativeHeights.h0
  haveI := blockSphereProb_isProbabilityMeasure (B := B) hn
  have hmean : ∀ σ : K →+* ℂ,
      ReciprocityTheory.MultiplicativeHeights.blockSphereMean B n (MvPolynomial.map σ (MvPolynomial.C a)) = Real.log ‖σ a‖ := by
    intro σ
    unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp [MvPolynomial.map_C, MvPolynomial.eval_C]
  have hgauss : ∀ w : FinitePlace K,
      ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C a : MvPolynomial (Fin B × Fin n) K) = w a := by
    intro w
    unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
    by_cases ha : a = 0
    · simp [ha]
    · rw [MvPolynomial.support_C, if_neg ha, Finset.sup_singleton, MvPolynomial.coeff_C, if_pos rfl,
        Real.coe_toNNReal (w a) (by exact w.1.nonneg a)]
  simp_rw [hgauss, hmean]
  by_cases ha : a = 0
  · simp [ha]
  rw [div_eq_zero_iff]
  left
  have hfin : (Function.mulSupport fun w : FinitePlace K => w a).Finite :=
    NumberField.FinitePlace.mulSupport_finite ha
  have hsub : (Function.support fun w : FinitePlace K => Real.log (w a)) ⊆ hfin.toFinset := by
    intro w hw
    rw [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    show Real.log (w a) = 0
    rw [h1, Real.log_one]
  rw [finsum_eq_sum_of_support_subset _ hsub, ← Real.log_prod (fun w _ => w.1.ne_zero ha),
    ← finprod_eq_prod_of_mulSupport_subset _ (by rw [Set.Finite.coe_toFinset]),
    NumberField.FinitePlace.prod_eq_inv_abs_norm ha,
    ← Real.log_prod (fun σ _ => by simpa using ha), ← norm_prod]
  have hN : ∏ σ : K →+* ℂ, σ a = ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => σ a) (fun σ => σ a) (fun σ => rfl),
      ← Algebra.norm_eq_prod_embeddings ℚ ℂ a]
    simp
  rw [hN]
  push_cast
  rw [Real.log_inv]
  simp
end ReciprocityTheory.ChartRestriction.G.T0
