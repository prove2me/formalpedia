-- Prove2me | solution 1 for TarchaBraids.configProj_isQuotientCoveringMap_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T23:25:55.814903+00:00
-- url     : https://prove2.me/submissions/b785b405-f032-44ae-a22e-f6354662efe7

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1
import Theorems.Thm_BraidsLinksMCG_prop_1_1_covering

open Topology
open BraidsLinksMCG
open TarchaBraids

theorem solution (n : ℕ) :
    IsQuotientCoveringMap (configProj n) (Equiv.Perm (Fin n)) := by
  rw [isQuotientCoveringMap_iff_isCoveringMap_and]
  refine ⟨(BraidsLinksMCG.prop_1_1_covering n).1, ?_, inferInstance, ?_, ?_⟩
  · intro x
    refine Quotient.inductionOn x ?_
    intro p
    exact ⟨p, rfl⟩
  · rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro g p hgp
    apply Equiv.ext
    intro i
    have hval :
        (orderedConfigPermute g p).1 (g i) = p.1 (g i) := by
      change (g • p : OrderedConfig n).1 (g i) = p.1 (g i)
      rw [hgp]
    have hpi : p.1 i = p.1 (g i) := by
      simpa [orderedConfigPermute, Function.comp_apply] using hval
    have hi : i = g i := p.2 hpi
    simpa using hi.symm
  · intro p q
    change Quotient.mk (configSetoid n) p = Quotient.mk (configSetoid n) q ↔ _
    rw [Quotient.eq, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      apply Subtype.ext
      funext i
      change q.1 (g.symm i) = p.1 i
      rw [hg]
      simp [Function.comp_apply]
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      change orderedConfigPermute g q = p at hg
      rw [← hg]
      funext i
      simp [orderedConfigPermute, Function.comp_apply]
