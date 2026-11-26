-- Prove2me | solution 1 for TDLC.betaEtaLoopNontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:20.485959+00:00
-- url     : https://prove2.me/submissions/d695c6b9-75d0-4144-8b04-a7f32ca96fd6


import Definitions.Def_TDLC_Solution
import Theorems.Thm_TDLC_path2PreservesParity

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} (f : A → B) (a : A) :
    Path2
      (Path.lEmbed (Step.beta f a) ++ₚ
        Path.inv (Path.lEmbed (Step.apCong (fun k : A → B => k a) (Step.eta f))))
      (.nil (f a)) → False := by
  intro cells
  have h := path2PreservesParity cells
  change true = false at h
  exact Bool.noConfusion h
end TDLC
