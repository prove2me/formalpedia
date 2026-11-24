-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_jB_lat_9c43534322f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:44:53.393803+00:00
-- url     : https://prove2.me/submissions/05cb6d54-afa1-4a7d-8c9b-373f6335b9bb

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_stdL_f14a35be741f
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_apply_eaf8db158c18
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_repr_jB_8730e632e624
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_b_inj_4cf57cb8133b
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_sum_genB_4a8d184a7d19
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (x : Fin n → K) : x ∈ (stdH K n).L ↔ ∃ c : V → 𝓞 K,
    jB σ b x = ∑ v ∈ genB b, σ ((c v : 𝓞 K) : K) • v := by
  rw [mem_stdL]
  constructor
  · intro h
    choose c hc using h
    classical
    refine ⟨fun v => if h : ∃ i, b i = v then c h.choose else 0, ?_⟩
    rw [sum_genB b fun v => σ (((if h : ∃ i, b i = v then c h.choose else 0 : 𝓞 K)) : K) • v, jB_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : ∃ k, b k = b i := ⟨i, rfl⟩
    rw [dif_pos h, b_inj b h.choose_spec, hc i]
  · rintro ⟨c, hc⟩ i
    refine ⟨c (b i), σ.injective ?_⟩
    rw [sum_genB b fun v => σ ((c v : 𝓞 K) : K) • v] at hc
    have h1 := congrArg (fun y => b.repr y i) hc
    have h2 : (∑ k, σ ((c (b k) : 𝓞 K) : K) • b k) = jB σ b (fun k => ((c (b k) : 𝓞 K) : K)) := rfl
    simp only [h2, repr_jB] at h1
    exact h1
end Formalism.BasicNotions.Examples₂.NZ
