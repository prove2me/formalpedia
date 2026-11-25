-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_quotGen_proof__1cc5bb5ca961
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:58.462313+00:00
-- url     : https://prove2.me/submissions/f71df901-d9f7-46cf-aaf2-cb9969e958e5

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_exists_quotient_spanning_family_finrank
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_height_loss_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution : QuotGen := by
  intro E _ _ M _ _ _ _ I hI
  have hc := height_loss_bound E M I
  have h0 : Ideal.absNorm I ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  have : Finite (M ⧸ (I • (⊤ : Submodule (𝓞 E) M))) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ h0)
  exact exists_quotient_spanning_family_finrank I
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
