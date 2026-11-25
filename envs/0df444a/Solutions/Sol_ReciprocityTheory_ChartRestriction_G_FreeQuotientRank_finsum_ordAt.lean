-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finsum_ordAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:24:34.869681+00:00
-- url     : https://prove2.me/submissions/def8342f-b448-4162-96b8-cf440303b5ba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hadamard
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_log_norm_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v =
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ x) := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    FinitePlace.mulSupport_finite hx
  have hprod := NumberField.prod_abs_eq_one hx
  have hA : 0 < ∏ w : InfinitePlace K, w x ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 hx) _
  set s := hfin.toFinset with hs
  have hBs : ∏ᶠ w : FinitePlace K, w x = ∏ w ∈ s, w x :=
    finprod_eq_prod_of_mulSupport_subset _ (by simp [s])
  have hB : 0 < ∏ w ∈ s, w x := Finset.prod_pos fun w _ => FinitePlace.pos_iff.2 hx
  rw [hBs] at hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA.ne' hB.ne', Real.log_one,
    Real.log_prod (fun w _ => (pow_pos (InfinitePlace.pos_iff.2 hx) _).ne'),
    Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hx).ne')] at hlog
  simp only [Real.log_pow] at hlog
  have hfs : ∑ w ∈ s, Real.log (w x) = ∑ᶠ w : FinitePlace K, Real.log (w x) := by
    rw [finsum_eq_sum_of_support_subset]
    intro w hw
    simp only [Function.mem_support] at hw
    simp only [s, Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    rw [h1, Real.log_one]
  have heq : ∑ᶠ w : FinitePlace K, Real.log (w x) =
      -∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v := by
    rw [← finsum_neg_distrib, ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finsum_congr fun v => ?_
    have h3 : (FinitePlace.equivHeightOneSpectrum.symm v) x = ‖FinitePlace.embedding v x‖ := by
      rw [← FinitePlace.mk_apply]
      rfl
    rw [h3, log_norm_emb v hx]
  linarith
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
