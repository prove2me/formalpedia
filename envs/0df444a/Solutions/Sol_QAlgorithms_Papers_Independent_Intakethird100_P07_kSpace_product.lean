-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kSpace_product
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:03:03.640207+00:00
-- url     : https://prove2.me/submissions/3775e5f0-5413-4603-ac57-cba604596ff0

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.CategoryTheory.Adjunction.Limits
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Proposition B.8, PDF p. 36: the concrete kified product cone is limiting,
including its canonical projection maps. The empty family is allowed. -/
theorem solution (I : Type u) (Y : I → CompactlyGenerated.{u, u}) :
    Nonempty (Limits.IsLimit (kProductCone Y)) := by
  classical
  refine ⟨Limits.Fan.IsLimit.mk (kProductCone Y) (fun s => ?_) ?_ ?_⟩
  · let f : C(s.pt, ∀ i, Y i) := ⟨fun x i => s.proj i x,
      continuous_pi (fun i => (s.proj i).hom.hom.continuous)⟩
    exact CompactlyGenerated.ofHom ⟨f,
      continuous_from_uCompactlyGeneratedSpace (X := s.pt) (Y := KSpace (∀ i, Y i)) f
        (fun S g => (kProbe S (f.comp g)).continuous)⟩
  · intro s i
    ext x
    rfl
  · intro s m hm
    ext x
    change (m x : ∀ i, Y i) = fun i => s.proj i x
    funext i
    exact congrArg (fun f => f x) (hm i)
