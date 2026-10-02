-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.exc_iff_argmax_isIntegralBaseSet
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T19:33:14.292246+00:00
-- url     : https://prove2.me/submissions/99202e53-69d0-481b-8845-f8b5a45d264b

import Theorems.Thm_SteinitzExchange_Extension_exc_iff_argmax_isIntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange

set_option autoImplicit false

-- Reuse the proved Theorem 4.4 from the Extension mission.
-- Its accepted reduction is by choi; dependencies include WillR,
-- mrfancypants, and the supporting-face/midpoint contributions of sometik179.
-- The two missions use definitionally identical exchange and maximizer predicates.
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : SteinitzExchange.LocalSupermod.IsIntegralBaseSet B)
    (ω : (V → ℤ) → ℝ) :
    SteinitzExchange.LocalSupermod.SatisfiesEXC B ω ↔
      ∀ p : V → ℝ, SteinitzExchange.LocalSupermod.IsIntegralBaseSet
        (SteinitzExchange.LocalSupermod.argmaxB B (SteinitzExchange.LocalSupermod.perturb ω p)) :=
  SteinitzExchange.Extension.exc_iff_argmax_isIntegralBaseSet B hB ω

#print axioms solution
