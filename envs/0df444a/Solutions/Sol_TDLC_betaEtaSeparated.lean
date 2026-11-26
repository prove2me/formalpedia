-- Prove2me | solution 1 for TDLC.betaEtaSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:10.69363+00:00
-- url     : https://prove2.me/submissions/4048d052-35e9-4f42-ad6f-43764ca79d93


import Definitions.Def_TDLC_Solution
import Theorems.Thm_TDLC_step2PreservesParity

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} (f : A → B) (a : A) :
    Step2
      (Path.lEmbed (Step.beta f a))
      (Path.lEmbed (Step.apCong (fun k : A → B => k a) (Step.eta f))) → False := by
  intro cell
  have h := step2PreservesParity cell
  change true = false at h
  exact Bool.noConfusion h
end TDLC
