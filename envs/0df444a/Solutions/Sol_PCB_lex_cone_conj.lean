-- Prove2me | solution 1 for PCB.lex_cone_conj
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:01:58.073638+00:00
-- url     : https://prove2.me/submissions/1f1e5f23-316a-4909-96cb-ff4924a3c08f

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

open PCB

theorem solution {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) :
    ∀ g ∈ lexCone W, ∀ x : G, x * g * x⁻¹ ∈ lexCone W := by
  rintro g ⟨j, hj, hc⟩ x
  have h1 : ∀ i : Fin k, j < i → W.nf 1 i = 1 :=
    (W.towerMem j 1).1 (W.tower j).one_mem
  refine ⟨j, fun i hi => ?_, ?_⟩
  · rw [W.nf_conj, hj i hi]
    have := W.nf_conj x 1 i
    rw [mul_one, mul_inv_cancel, h1 i hi] at this
    exact this.symm
  · rw [W.nf_conj]; exact W.conjOn_cone x j _ hc
