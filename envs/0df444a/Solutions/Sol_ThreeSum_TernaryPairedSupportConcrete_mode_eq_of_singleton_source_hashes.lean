-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupportConcrete.mode_eq_of_singleton_source_hashes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:35:44.137794+00:00
-- url     : https://prove2.me/submissions/bbd6571c-ff90-4a0e-a6f3-63bc1336b545

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupportConcrete
open Finset TernaryPairedPotential TernaryPairedSupport
open scoped BigOperators
variable {K : Type*} [Field K]
variable {P W D : Type*} [Fintype P] [Fintype K]
  [AddCommGroup W] [Module K W] [Fintype W] [DecidableEq D]
namespace ThreeSum.TernaryPairedSupportConcrete
theorem _root_.solution {B C : Type*} {J : ℕ}
    (left : P → B) (right : P → C)
    (L : B → Fin J → K) (R : C → Fin J → K)
    (H : (Fin J → K) →ₗ[K] W) (o : W) (mode : P → D)
    (hleft : Function.Injective (fun b => H (L b)))
    (hright : Function.Injective (fun c => H (R c)))
    (hroot : ∀ a, H (L (left a)+R (right a))=o)
    (hmode : ∀ a b, left a=left b → right a=right b → mode a=mode b) :
    ∀ a b, H (L (left a))=H (L (left b)) → mode a=mode b := by
  intro a b hab
  apply hmode a b (hleft hab)
  apply hright
  have ha := hroot a
  have hb := hroot b
  rw [map_add] at ha hb
  exact add_left_cancel (hab ▸ ha.trans hb.symm)
end ThreeSum.TernaryPairedSupportConcrete
