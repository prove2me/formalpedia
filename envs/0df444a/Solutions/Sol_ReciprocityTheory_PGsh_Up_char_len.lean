-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.char_len
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:34.805563+00:00
-- url     : https://prove2.me/submissions/c411327c-cc2c-4cdc-9455-4e91cf70865f

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
import Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_hasLen_coker_det__d6b912bda411


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] [IsDomain R]
variable {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hv : v.Integers R) {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (ι : Fin g → Fin N)
    (s : ℕ) (hs : s ≤ g)
    (hι : Submodule.span R (Set.range fun b : Fin s => fun a : Fin s =>
      M (Fin.castLE hs a) (ι (Fin.castLE hs b))) = omTr M s hs) :
    HasLen v R ((Fin s → R) ⧸ omTr M s hs)
      (v (algebraMap R C (Matrix.of fun a b : Fin s => M (Fin.castLE hs a) (ι (Fin.castLE hs b))).det)) := by
  have h := hasLen_coker_det' v R hv (Fin s) (Matrix.of fun a b : Fin s => M (Fin.castLE hs a) (ι (Fin.castLE hs b)))
  have hr : LinearMap.range (Matrix.of fun a b : Fin s => M (Fin.castLE hs a)
      (ι (Fin.castLE hs b))).mulVecLin = omTr M s hs := by
    rw [Matrix.range_mulVecLin, ← hι]
    rfl
  rw [hr] at h
  exact h
end ReciprocityTheory.PGsh.Up
