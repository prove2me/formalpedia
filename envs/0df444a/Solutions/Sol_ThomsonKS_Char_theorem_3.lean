-- Prove2me | solution 1 for ThomsonKS.Char.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:28:17.262994+00:00
-- url     : https://prove2.me/submissions/b2b01355-13b2-47cb-b0f9-24e32e7b305f

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting
import Theorems.Thm_ThomsonKS_Char_theorem_1
import Theorems.Thm_ThomsonKS_Char_corollary_1
import Theorems.Thm_ThomsonKS_Char_sigmaTilde_dense

open ThomsonKS.Char Filter Topology

theorem solution (F : Solution) (hF : IsSolution F) (hW : WPO F) (hA : An F)
    (hI : SInv F) (hC : Cont F) (hM : Mon F) :
    ∀ P : Finset ℕ, ∀ S ∈ DivProb P, F P S = KS P S := by
  intro P S hS
  obtain ⟨Sk, hSk, ht⟩ := sigmaTilde_dense P S hS
  have hSk' : ∀ k, Sk k ∈ DivProb P := fun k => (hSk k).1
  have h1 := hC P Sk S hS hSk' ht
  have h2 := theorem_1.2.2.2.2.1 P Sk S hS hSk' ht
  have e : (fun k => F P (Sk k)) = fun k => KS P (Sk k) :=
    funext fun k => corollary_1 F hF hW hA hI hM P (Sk k) (hSk k)
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2
