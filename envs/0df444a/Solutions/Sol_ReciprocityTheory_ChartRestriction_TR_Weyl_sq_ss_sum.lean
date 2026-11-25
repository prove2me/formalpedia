-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ss_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:54:29.356079+00:00
-- url     : https://prove2.me/submissions/671faef5-85f2-4d49-ae92-328dd7fc1e88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqChar
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_SSZ_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_gt_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
open ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {K : Type*} [Field K] (N : ℕ) (ν : Fin N → ℕ) [Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx N N ν)]
    (t : Fin N → K) :
    ∑ m : ↥(Formalism.GradedWeylDivisibility.ssIdx N N ν), ∏ a, t a ^ Formalism.GradedWeylDivisibility.rowWt m.1 a = gtChar N (fun i => (ν i : ℤ)) t := by
  have : Fintype (sq_SSZ N (fun i => (ν i : ℤ))) := @Fintype.ofFinite _ (sq_SSZ_finite N _)
  refine (Fintype.sum_equiv (sq_ssEquiv N ν) _ (fun g => sq_mono t g.1) (fun m => rfl)).trans ?_
  exact sq_gt_sum N _ (fun s => Int.natCast_nonneg _) t
end ReciprocityTheory.ChartRestriction.TR.Weyl
