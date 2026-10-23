-- Prove2me | solution 1 for RSF.twist_computation
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:41:07.919695+00:00
-- url     : https://prove2.me/submissions/b73864a9-1ffe-4249-a8ad-084cd016b25c

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

open RSF

/-- Degenerate six-functor world: one space, one map, objects `Bool`. -/
def rsf86_w (unitV : Bool) (tens pullV ushV : Bool) (bdcs etale adic pcoh : Prop) : SixFunctorWorld where
  Space := Unit
  Map := fun _ _ => Unit
  idMap := fun _ => ()
  compMap := fun _ _ _ _ _ => ()
  C := fun _ => Bool
  unit := fun _ => unitV
  tensor := fun _ _ _ => tens
  internalHom := fun _ _ _ => false
  pull := fun _ _ _ _ => pullV
  push := fun _ _ _ M => M
  lshriek := fun _ _ _ M => M
  ushriek := fun _ _ _ _ => ushV
  shift := fun _ _ M => M
  tateTwist := fun _ _ M => M
  IsBdcs := fun _ _ _ => bdcs
  IsEtale := fun _ _ _ => etale
  IsProper := fun _ _ _ => True
  IsAdicSmooth := fun _ _ _ => adic
  IsPCohSmooth := fun _ _ _ => pcoh
  IsPureDim := fun _ _ _ _ => True
  diamond := fun _ _ f => f

theorem solution : ¬ (∀ (w : SixFunctorWorld) (X Y : w.Space) (f : w.Map Y X) (d : ℕ),
    w.IsAdicSmooth Y X f → w.IsPureDim Y X f d →
    w.ushriek Y X f (w.unit X) = w.shift Y (2 * d) (w.tateTwist Y d (w.unit Y))) := by
  intro h
  have := h (rsf86_w true false false false True True True True) () () () 0 trivial trivial
  exact Bool.noConfusion this
