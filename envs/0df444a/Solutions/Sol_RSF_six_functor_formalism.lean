-- Prove2me | solution 1 for RSF.six_functor_formalism
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:42:10.344418+00:00
-- url     : https://prove2.me/submissions/1df01f20-6714-4369-a866-8b04ee39f352

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

theorem solution : ¬ (∀ w : SixFunctorWorld,
    (∀ (X Y Z : w.Space) (f : w.Map X Y) (g : w.Map Y Z) (M : w.C Z),
      w.pull X Z (w.compMap X Y Z f g) M = w.pull X Y f (w.pull Y Z g M)) ∧
    (∀ (X Y Z : w.Space) (f : w.Map X Y) (g : w.Map Y Z) (M : w.C X),
      w.push X Z (w.compMap X Y Z f g) M = w.push Y Z g (w.push X Y f M)) ∧
    (∀ (X Y Z : w.Space) (f : w.Map X Y) (g : w.Map Y Z)
        (hf : w.IsBdcs X Y f) (hg : w.IsBdcs Y Z g) (M : w.C X),
      w.lshriek X Z (w.compMap X Y Z f g) M = w.lshriek Y Z g (w.lshriek X Y f M)) ∧
    (∀ (X Y Z : w.Space) (f : w.Map X Y) (g : w.Map Y Z)
        (hf : w.IsBdcs X Y f) (hg : w.IsBdcs Y Z g) (M : w.C Z),
      w.ushriek X Z (w.compMap X Y Z f g) M = w.ushriek X Y f (w.ushriek Y Z g M)) ∧
    (∀ (X Y : w.Space) (f : w.Map X Y) (hf : w.IsEtale X Y f) (M : w.C Y),
      w.ushriek X Y f M = w.pull X Y f M) ∧
    (∀ (X Y : w.Space) (f : w.Map X Y) (hf : w.IsProper X Y f) (M : w.C X),
      w.lshriek X Y f M = w.push X Y f M) ∧
    (∀ (X Y : w.Space) (f : w.Map X Y) (hf : w.IsBdcs X Y f) (N : w.C X) (M : w.C Y),
      w.lshriek X Y f (w.tensor X N (w.pull X Y f M))
        = w.tensor Y (w.lshriek X Y f N) M) ∧
    (∀ (s : CartSquare w) (hf : w.IsBdcs s.Y s.X s.f) (N : w.C s.Y),
      w.pull s.X' s.X s.g (w.lshriek s.Y s.X s.f N)
        = w.lshriek s.Y' s.X' s.f' (w.pull s.Y' s.Y s.g' N))) := by
  intro h
  have := (h (rsf86_w true false false true True True True True)).2.2.2.2.1 () () () trivial true
  exact Bool.noConfusion this
