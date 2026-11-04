-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupportConcrete.physical_support_cap_of_zero_minors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:12.554876+00:00
-- url     : https://prove2.me/submissions/8bcf9513-1d7d-43b4-9929-63ca68457deb

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_flatten_injective
import Theorems.Thm_ThreeSum_TernaryPairedSupportConcrete_cast_tupleMatrix
import Theorems.Thm_ThreeSum_TernaryPairedPotential_rowWeight_pos_of_mod_independent
import Theorems.Thm_ThreeSum_TernaryPairedSupport_physical_support_cap_of_zero_potential


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupportConcrete
open Finset TernaryPairedPotential TernaryPairedSupport
open scoped BigOperators
variable {K : Type*} [Field K]
variable {P W D : Type*} [Fintype P] [Fintype K]
  [AddCommGroup W] [Module K W] [Fintype W] [DecidableEq D]
namespace ThreeSum.TernaryPairedSupportConcrete
theorem _root_.solution {J : ℕ}
    (L R : P → Fin J → ℤ) (H : (Fin J → K) →ₗ[K] W) (o : W)
    (mode : P → D) (m : ℕ)
    (hroot : ∀ a, H ((fun j => (L a j : K))+(fun j => (R a j : K)))=o)
    (hmode : ∀ a b, (fun j => (L a j : K))+(fun j => (R a j : K)) =
      (fun j => (L b j : K))+(fun j => (R b j : K)) → mode a=mode b)
    (hhash : ∀ a b, H (fun j => (L a j : K))=H (fun j => (L b j : K)) → mode a=mode b)
    (hzero : (∑ e : Fin m → P, rowWeight (tupleMatrix L R e))=0) :
    (physicalSupport mode).card ≤ 2*Fintype.card K^m := by
  classical
  apply physical_support_cap_of_zero_potential
    (fun a j => (L a j : K)) (fun a j => (R a j : K)) H o mode m
    (fun e => rowWeight (tupleMatrix L R e)) hroot hmode hhash
    (hzero := hzero)
  intro e he
  apply rowWeight_pos_of_mod_independent _ (Int.castRingHom K)
  change LinearIndependent K (fun i j => (tupleMatrix L R e i j : K))
  rw [cast_tupleMatrix]
  exact he.map' (flatten J) (LinearMap.ker_eq_bot.mpr (flatten_injective J))
end ThreeSum.TernaryPairedSupportConcrete
