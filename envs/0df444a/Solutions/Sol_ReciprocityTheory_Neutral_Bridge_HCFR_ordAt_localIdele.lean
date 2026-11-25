-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.ordAt_localIdele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:35:01.680323+00:00
-- url     : https://prove2.me/submissions/86d68c88-692c-46c5-bfbb-5fc39e2c8acd

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_valued_eq_exp_of_isUniformiserAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
open Classical
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (v w : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ)
    (hπ : IsUniformiserAt K v (π : v.adicCompletion K)) :
    ordAt K w (localIdele K v π) = if w = v then 1 else 0 := by
  unfold ordAt
  split_ifs with h
  · subst h
    have hc : ((localIdele K w π : Ideles K) : AdeleRing (𝓞 K) K).2 w = π :=
      RestrictedProduct.mulSingle_eq_same _ _ _
    rw [hc, valued_eq_exp_of_isUniformiserAt K w _ hπ, WithZero.log_exp]
    norm_num
  · have hc : ((localIdele K v π : Ideles K) : AdeleRing (𝓞 K) K).2 w = 1 :=
      RestrictedProduct.mulSingle_eq_of_ne _ _ h
    rw [hc]
    simp
end ReciprocityTheory.Neutral.Bridge.HCFR
