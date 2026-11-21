-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.permutation_family
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:08:31.883586+00:00
-- url     : https://prove2.me/submissions/36cfceab-446d-4066-a534-ea8a6e718afc

import Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_field_size_spec
import Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_hash_order_stream_is_bounded
import Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_polynomial_family_fraction
import Theorems.Thm_StableMSR_Recovery_Supplement_OrderStream_serialized_family_decodes
import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_stream_writer
import Definitions.Def_StableMSR_Recovery_Supplement_RandomExecution

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream

set_option maxHeartbeats 1600000
open scoped Classical

theorem solution :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
        ∀ m : ℕ, 1 ≤ m → ∃ t ≤ a * m ^ b,
          let s := execute P m 0 (fun _ _ => 0) t
          s.halted = true ∧ s.work ≤ a * m ^ b ∧
          PermutationFamily m (MinSumFPT.outputSets s) ∧
          (MinSumFPT.outputSets s).length ≤ a * m ^ b ∧
          ∀ T : Finset ℕ, T ⊆ Finset.range m → T.Nonempty →
            ∀ z ∈ T, firstFraction (MinSumFPT.outputSets s) T z ≤ 3 / (2 * (T.card : ℝ)) := by
  classical
  obtain ⟨hl,hv⟩ := hash_order_stream_is_bounded
  obtain ⟨a,b,ha,hb,P,hp,ex⟩ := bounded_stream_writer span word hl hv
  refine ⟨a,b,ha,hb,P,hp,?_⟩
  intro m hm
  obtain ⟨t,ht,halt,work,sz,write⟩ := ex m hm
  have out := serialized_family_decodes m _ write
  obtain ⟨fl,ok,frac⟩ := polynomial_family_fraction m
  refine ⟨t,ht,halt,work,?_,?_,?_⟩
  · rw [out];exact ok
  · rw [out,fl]
    apply le_trans _ sz
    unfold OrderStream.span
    rw [Nat.mul_succ]
    omega
  · rw [out];exact frac
