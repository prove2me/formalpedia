-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.comp_smul_paT_mem_paPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:38.870825+00:00
-- url     : https://prove2.me/submissions/b4f9b67d-e0ea-414e-b527-377c27f823d7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paMono_smul_paT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPF_mem_paPoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {c : ℕ} (t : ℝ) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    (fun z => F (t • paT z)) ∈ paPoly (ι := Fin (Fintype.card ι)) c := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    have hfun : (fun z => paMono α (t • paT z)) = ((t : ℂ) ^ α.degree) •
        paMono (ι := Fin (Fintype.card ι)) (Finsupp.equivMapDomain (Fintype.equivFin ι) α) :=
      funext fun z => by rw [Pi.smul_apply, smul_eq_mul, paMono_smul_paT]
    rw [hfun]
    refine (paPoly _).smul_mem _ ?_
    have hd : (Finsupp.equivMapDomain (Fintype.equivFin ι) α).sum (fun _ e => e) ≤ c := by
      rw [Finsupp.sum_equivMapDomain]
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 hα)).2
    refine paPF_mem_paPoly (p := MvPolynomial.monomial _ 1) ?_
    rw [MvPolynomial.totalDegree_monomial _ one_ne_zero]
    exact hd
  | zero => exact (paPoly _).zero_mem
  | add x y _ _ hx hy => exact (paPoly _).add_mem hx hy
  | smul a x _ hx => exact (paPoly _).smul_mem a hx
end ReciprocityTheory.ChartRestriction.G.I2
