-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_mem_stdL_f14a35be741f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:18.319889+00:00
-- url     : https://prove2.me/submissions/41a75039-e090-4fa9-8f5e-5b03ee2d0622

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
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
variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (x : Fin n → K) : x ∈ (stdH K n).L ↔ ∀ i, ∃ c : 𝓞 K, x i = (c : K) := by
  show x ∈ Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) ↔ _
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      intro i
      by_cases h : i = k
      · exact ⟨1, by subst h; simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => exact fun _ => ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro i
      obtain ⟨a, ha⟩ := hy i
      obtain ⟨b, hb⟩ := hz i
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul a y _ hy =>
      intro i
      obtain ⟨c, hc⟩ := hy i
      exact ⟨a * c, by rw [Pi.smul_apply, hc, Algebra.smul_def]; simp⟩
  · intro h
    choose c hc using h
    have : x = ∑ i, c i • Pi.basisFun K (Fin n) i := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same, hc k, Algebra.smul_def, mul_one]
      · intro i _ hi
        rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_of_ne (Ne.symm hi), smul_zero]
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.BasicNotions.Examples₂.NZ
