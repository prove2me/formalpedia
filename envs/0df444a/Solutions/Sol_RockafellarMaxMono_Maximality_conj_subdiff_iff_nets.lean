-- Prove2me | solution 1 for RockafellarMaxMono.Maximality.conj_subdiff_iff_nets
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T19:25:10.418907+00:00
-- url     : https://prove2.me/submissions/fe2ccc04-f311-4382-8214-f7dcaf0cd21a

import Theorems.Thm_RockafellarMaxMono_Cyclic_conj_subdiff_iff_nets

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Shared_Conj
open RockafellarMaxMono
open Filter Topology
universe u


theorem solution {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x' : StrongDual ℝ E) (x'' : StrongDual ℝ (StrongDual ℝ E)) :
    x'' ∈ Shared.subdiff (Shared.conj f) x' ↔
      ∃ (I : Type u) (_ : PartialOrder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (xs' : I → StrongDual ℝ E) (xs : I → E),
        Tendsto xs' atTop (𝓝 x') ∧
        (∃ C : ℝ, ∀ i, ‖xs i‖ ≤ C) ∧
        (∀ y' : StrongDual ℝ E,
          Tendsto (fun i => NormedSpace.inclusionInDoubleDual ℝ E (xs i) y') atTop (𝓝 (x'' y'))) ∧
        ∀ i, xs' i ∈ Shared.subdiff f (xs i) :=
  RockafellarMaxMono.Cyclic.conj_subdiff_iff_nets f hf hlsc x' x''