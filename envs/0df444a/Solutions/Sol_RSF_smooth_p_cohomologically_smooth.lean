-- Prove2me | solution 1 for RSF.smooth_p_cohomologically_smooth
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:41:37.672581+00:00
-- url     : https://prove2.me/submissions/e1a5413c-c3c7-4872-a2b2-d97fd23ee5cf

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

theorem solution : ¬ (∀ (w : SixFunctorWorld) (X Y : w.Space) (f : w.Map X Y),
    w.IsAdicSmooth X Y f → w.IsPCohSmooth X Y (w.diamond X Y f)) := by
  intro h
  exact h (rsf86_w true false false false True True True False) () () () trivial
