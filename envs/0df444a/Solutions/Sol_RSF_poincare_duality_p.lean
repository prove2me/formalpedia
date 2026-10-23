-- Prove2me | solution 1 for RSF.poincare_duality_p
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:42:49.644657+00:00
-- url     : https://prove2.me/submissions/013de857-27c1-496d-8d2f-3c3dc998b4d4

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

open RSF


/-- Rigid cohomology world with `H i = Bool` and trivial Tate object `Unit`:
no pairing into `Unit` can be nondegenerate. -/
def rsf86_rw : RigidCohWorld where
  ℓ := 2
  hℓ := by norm_num
  P := 2
  hP := by norm_num
  K := Unit
  X := Unit
  nonarchField := True
  algClosed := True
  mixedChar := True
  properSmooth := True
  pureDim := True
  d := 0
  H := fun _ => Bool
  add := fun _ x y => xor x y
  zero := fun _ => false
  smul := fun _ _ x => x
  Tate := Unit
  tadd := fun _ _ => ()
  tzero := ()
  tsmul := fun _ _ => ()

theorem solution : ¬ (∀ w : RigidCohWorld,
    w.ℓ = w.P →
    w.nonarchField → w.algClosed → w.mixedChar →
    w.properSmooth → w.pureDim →
    ∃ pair : ∀ i : ℤ, w.H (2 * (w.d : ℤ) - i) → w.H i → w.Tate,
      (∀ (i : ℤ) (x y : w.H (2 * (w.d : ℤ) - i)) (z : w.H i),
        pair i (w.add (2 * (w.d : ℤ) - i) x y) z = w.tadd (pair i x z) (pair i y z)) ∧
      (∀ (i : ℤ) (k : ZMod w.ℓ) (x : w.H (2 * (w.d : ℤ) - i)) (z : w.H i),
        pair i (w.smul (2 * (w.d : ℤ) - i) k x) z = w.tsmul k (pair i x z)) ∧
      (∀ (i : ℤ) (x : w.H (2 * (w.d : ℤ) - i)) (y z : w.H i),
        pair i x (w.add i y z) = w.tadd (pair i x y) (pair i x z)) ∧
      (∀ (i : ℤ) (k : ZMod w.ℓ) (x : w.H (2 * (w.d : ℤ) - i)) (z : w.H i),
        pair i x (w.smul i k z) = w.tsmul k (pair i x z)) ∧
      (∀ (i : ℤ) (x : w.H (2 * (w.d : ℤ) - i)),
        (∀ z : w.H i, pair i x z = w.tzero) → x = w.zero (2 * (w.d : ℤ) - i)) ∧
      (∀ (i : ℤ) (z : w.H i),
        (∀ x : w.H (2 * (w.d : ℤ) - i), pair i x z = w.tzero) → z = w.zero i) ∧
      (∀ (i : ℤ) (φ : ZModLinear w.ℓ (w.H i) w.Tate
            (w.add i) (w.zero i) (w.smul i) w.tadd w.tzero w.tsmul),
        ∃ u : w.H (2 * (w.d : ℤ) - i), ∀ z : w.H i, pair i u z = φ.map z)) := by
  intro h
  obtain ⟨pair, -, -, -, -, hnd, -, -⟩ := h rsf86_rw rfl trivial trivial trivial trivial trivial
  exact Bool.noConfusion (hnd 0 true (fun _ => rfl))
