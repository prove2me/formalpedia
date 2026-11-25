-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_mem_oB_bbdbf3002751
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:36.510847+00:00
-- url     : https://prove2.me/submissions/70daaa6b-d4bb-4d80-931c-e9c42976556f

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_b_inj_4cf57cb8133b
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_sum_genB_4a8d184a7d19

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {O : Type} [CommRing O] (φ : O →+* ℂ) (x : V) :
    x ∈ (oB b φ).carrier ↔ ∃ c : Fin n → O, x = ∑ i, φ (c i) • b i := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c (b i), sum_genB b fun v => φ (c v) • v⟩
  · rintro ⟨c, rfl⟩
    classical
    refine ⟨fun v => if h : ∃ i, b i = v then c h.choose else 0, ?_⟩
    rw [show (oB b φ).gen = genB b from rfl, sum_genB b fun v => φ (if h : ∃ i, b i = v then c h.choose else 0) • v]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : ∃ k, b k = b i := ⟨i, rfl⟩
    rw [dif_pos h, b_inj b h.choose_spec]
end Formalism.BasicNotions.Examples₂.NZ
