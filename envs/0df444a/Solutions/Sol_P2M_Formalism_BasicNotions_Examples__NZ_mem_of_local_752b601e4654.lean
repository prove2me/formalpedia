-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_mem_of_local_752b601e4654
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:38.088274+00:00
-- url     : https://prove2.me/submissions/3f0542bc-88f1-4f62-8184-a8d6f2fb0e5d

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
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (Λ : Submodule A M) (x : M)
    (h : ∀ P : Ideal A, P.IsMaximal → ∃ d : A, d ∉ P ∧ d • x ∈ Λ) : x ∈ Λ := by
  let I : Ideal A :=
    { carrier := {d | d • x ∈ Λ}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • x ∈ Λ
        rw [add_smul]; exact Λ.add_mem ha hb
      zero_mem' := by
        show (0 : A) • x ∈ Λ
        rw [zero_smul]; exact Λ.zero_mem
      smul_mem' := fun c {a} ha => by
        show (c • a) • x ∈ Λ
        rw [smul_eq_mul, mul_smul]; exact Λ.smul_mem c ha }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨d, hd, hx⟩ := h P hP
    exact hd (hle hx)
  have : (1 : A) ∈ I := by rw [hI]; trivial
  simpa using (show (1 : A) • x ∈ Λ from this)
end Formalism.BasicNotions.Examples₂.NZ
