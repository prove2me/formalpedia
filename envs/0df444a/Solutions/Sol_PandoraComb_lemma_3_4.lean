-- Prove2me | solution 1 for PandoraComb.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:32:40.131458+00:00
-- url     : https://prove2.me/submissions/9fd3bc58-96a7-482d-8ffa-6ee430039b14

import Definitions.Def_PandoraComb_ClosedForms

open PandoraComb in
theorem solution {ι : Type*} [DecidableEq ι] (c : Finset ι → ℝ) (T : Finset ι) (h ℓ : ι)
    (hh : h ∉ T) (hℓ : ℓ ∉ T) :
    marginal c h (insert ℓ T) - marginal c ℓ (insert h T) = marginal c h T - marginal c ℓ T := by
  unfold marginal
  rw [Finset.insert_comm h ℓ T]
  ring
