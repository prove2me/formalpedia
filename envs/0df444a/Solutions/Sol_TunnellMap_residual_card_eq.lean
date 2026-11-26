-- Prove2me | solution 1 for TunnellMap.residual_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:50.637535+00:00
-- url     : https://prove2.me/submissions/b28c2181-7437-450b-9480-5ee85bd8b7c6

import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_ResidualBalance

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BOddRep n) = Fintype.card (ARep n)) :
    Fintype.card (BResidual n) = Fintype.card (AResidual n) := by
  classical
  have hdirect :
      Fintype.card {p : BOddRep n // DirectSourceUsed p} =
        Fintype.card {p : ARep n // DirectTargetUsed p} :=
    Fintype.card_congr (directSubsetEquiv hn)
  change Fintype.card {p : BOddRep n // ¬ DirectSourceUsed p} =
    Fintype.card {p : ARep n // ¬ DirectTargetUsed p}
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hbalance, hdirect]
end TunnellMap
