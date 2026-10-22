-- Prove2me | solution 1 for SelfishRouting.Linear.lemma_4_3_b
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:19:42.398753+00:00
-- url     : https://prove2.me/submissions/f3c736ef-7084-4c9a-b168-3a2d04d9f821

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

set_option autoImplicit false

open KellyStochasticNetworks SelfishRouting.Linear

lemma srl_linkFlow_half {J R : ℕ} (A : Fin J → Fin R → ℝ) (x : Fin R → ℝ) (j : Fin J) :
    linkFlow A (fun r => x r / 2) j = linkFlow A x j / 2 := by
  unfold linkFlow
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ => by ring)

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (a b : Fin J → ℝ)
    (x : Fin R → ℝ) (r : Fin R) :
    SelfishRouting.Bicriteria.pathLatency A (marginalLatency a b) (fun r => x r / 2) r =
      SelfishRouting.Bicriteria.pathLatency A (linLatency a b) x r := by
  unfold SelfishRouting.Bicriteria.pathLatency
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [srl_linkFlow_half]
  simp only [marginalLatency, linLatency]
  ring
