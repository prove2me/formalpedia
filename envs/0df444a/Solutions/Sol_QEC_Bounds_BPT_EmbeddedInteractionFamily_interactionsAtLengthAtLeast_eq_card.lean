-- Prove2me | solution 1 for QEC.Bounds.BPT.EmbeddedInteractionFamily.interactionsAtLengthAtLeast_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:23:00.853446+00:00
-- url     : https://prove2.me/submissions/389d71c1-4c06-4227-ab2d-3c0421eaf701

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound

set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.EmbeddedInteractionFamily
namespace QEC.Bounds.BPT.EmbeddedInteractionFamily
theorem _root_.solution {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (data : EmbeddedInteractionFamily ι κ) (i : Nat) (threshold : ℝ) :
    data.interactionsAtLengthAtLeast i threshold =
      ((data.presentation i).interactionsAtLengthAtLeast (data.embedding i) threshold).card :=
  rfl
end QEC.Bounds.BPT.EmbeddedInteractionFamily
