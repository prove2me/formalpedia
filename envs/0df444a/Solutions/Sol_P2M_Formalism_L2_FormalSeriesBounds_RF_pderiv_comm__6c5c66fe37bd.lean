-- Prove2me | solution 1 for P2M_Formalism_L2_FormalSeriesBounds_RF_pderiv_comm__6c5c66fe37bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:11.621091+00:00
-- url     : https://prove2.me/submissions/bc96c9d8-43b2-4c74-b32c-ca6da6abe1f6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {σ R : Type} [CommRing R] (i j : σ) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [MvPolynomial.pderiv_monomial]
    by_cases hij : i = j
    · subst hij
      rfl
    · congr 1
      · rw [tsub_right_comm]
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hij, if_neg (Ne.symm hij),
          tsub_zero]
        ring
  | add p q hp hq => simp only [map_add, hp, hq]
end Formalism.L2.FormalSeriesBounds.RF
