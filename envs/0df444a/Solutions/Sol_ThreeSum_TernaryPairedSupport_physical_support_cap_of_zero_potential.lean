-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupport.physical_support_cap_of_zero_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:46:37.982924+00:00
-- url     : https://prove2.me/submissions/1c30cee1-21e5-4e5c-9357-0539d6e99604

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Theorems.Thm_ThreeSum_TernaryPairedSupport_physical_support_cap

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupport
open Finset
attribute [local instance] Classical.propDecidable
variable {K E V W : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
  [AddCommGroup W] [Module K W] [Fintype W]
  [Fintype E]
variable {P D : Type*} [Fintype P] [DecidableEq D]
namespace ThreeSum.TernaryPairedSupport
theorem _root_.solution
    (L R : P → V) (H : V →ₗ[K] W) (o : W) (mode : P → D) (m : ℕ)
    (weight : (Fin m → P) → ℕ)
    (hroot : ∀ i, H (L i+R i)=o)
    (hmode : ∀ a b, L a+R a=L b+R b → mode a=mode b)
    (hhash : ∀ a b, H (L a)=H (L b) → mode a=mode b)
    (hpos : ∀ e, LinearIndependent K
      (taggedEndpoints (K := K) (L ∘ e) (R ∘ e)) → 0 < weight e)
    (hzero : (∑ e : Fin m → P, weight e)=0) :
    (physicalSupport mode).card ≤ 2 * Fintype.card K ^ m := by
  apply physical_support_cap L R H o mode m hroot hmode hhash
  intro e he
  have hz : weight e=0 := by
    have hh := single_le_sum (f := weight) (fun _ _ => Nat.zero_le _) (mem_univ e)
    rw [hzero] at hh
    omega
  exact (Nat.ne_of_gt (hpos e he)) hz
end ThreeSum.TernaryPairedSupport
