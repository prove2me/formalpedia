-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.surj_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:37.551538+00:00
-- url     : https://prove2.me/submissions/2031a633-5030-4ae0-8fc8-576c4ced4e32

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_H_mk
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_lift_cocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
noncomputable section
universe u
open Cx
open ReciprocityTheory.Coh.InflationTower
variable {R : Type u} [CommRing R]
namespace ReciprocityTheory.Coh.InflationTower
theorem _root_.solution (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m))
    (hT : IsTowerLim A τ L π) (n : ℕ) (y : ∀ m, (A m).H n) (hy : ∀ m, (τ m).H n (y (m + 1)) = y m) :
    ∃ x, ∀ m, (π m).H n x = y m := by
  have step : ∀ m (z : (A m).Z n), (Submodule.Quotient.mk z : (A m).H n) = y m →
      ∃ z' : (A (m+1)).Z n, (Submodule.Quotient.mk z' : (A (m+1)).H n) = y (m+1) ∧ (τ m).Z n z' = z := by
    intro m z hz
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (y (m+1))
    obtain ⟨z', h1, h2⟩ := lift_cocycle (τ m) (hT.surj m) n w z (by rw [hw, hy, hz])
    exact ⟨z', h1.trans hw, h2⟩
  let seq : ∀ m, {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m} := fun m =>
    Nat.rec (motive := fun m => {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m})
      ⟨Classical.choose (Submodule.Quotient.mk_surjective _ (y 0)),
        Classical.choose_spec (Submodule.Quotient.mk_surjective _ (y 0))⟩
      (fun m s => ⟨Classical.choose (step m s.1 s.2), (Classical.choose_spec (step m s.1 s.2)).1⟩) m
  have hseq : ∀ m, (τ m).Z n (seq (m+1)).1 = (seq m).1 := fun m =>
    (Classical.choose_spec (step m (seq m).1 (seq m).2)).2
  obtain ⟨x, hx⟩ := hT.lift n (fun m => ((seq m).1 : (A m).X n)) (fun m => congrArg Subtype.val (hseq m))
  have hdx : L.d n x = 0 := by
    apply hT.ext
    intro m
    rw [(π m).comm, hx]; exact (seq m).1.2
  refine ⟨Submodule.Quotient.mk ⟨x, hdx⟩, fun m => ?_⟩
  rw [H_mk, ← (seq m).2]
  congr 1; exact Subtype.ext (hx m)
end ReciprocityTheory.Coh.InflationTower
