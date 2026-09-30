-- Prove2me | solution 1 for TauCeti.NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_inter_pos
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:58.852658+00:00
-- url     : https://prove2.me/submissions/58903c0a-9d66-41e1-b055-8381b040bbdd

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cutting a reflection-invariant subset of the mixed space at a finset of real places

Let `S` be a finset of real places and `A` a subset of the mixed space preserved by the reflection
`negAt {w}` of the real coordinate at each single place `w` of `S`.  The `2 ^ S.card` sign patterns
along `S` then cut `A` into pieces of equal volume, exhausting `A` up to the null set where some
coordinate of `S` vanishes.

Cutting `A` down to the points that are positive at every place of `S` therefore divides its
volume by `2 ^ S.card`, the real coordinates outside `S` staying free.  A set whose membership
depends on the real coordinates only through their absolute values is invariant at every real
place, and for `S` all of the real places the statement is then Mathlib's
`NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_plusPart`.

## Main results

* `TauCeti.NumberField.mixedEmbedding.isOpen_setOfPred_forall_mem_pos`: the points positive at
  every place of a finset of real places form an open set.
* `TauCeti.NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_inter_pos`: for a set invariant
  under reflection at each place of `S`, the volume is `2 ^ S.card` times the volume of the part
  that is positive at every place of `S`.
-/

 section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding
end TauCeti.NumberField.mixedEmbedding
section TauCeti.NumberField.mixedEmbedding
open TauCeti TauCeti.NumberField TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- A set stable under reflecting the real coordinate at the place `w` has twice the volume of its
part where that coordinate is positive. -/
private theorem TauCeti.NumberField.mixedEmbedding.volume_eq_two_mul_volume_inter_pos_at {B : _root_.Set (_root_.NumberField.mixedEmbedding.mixedSpace K)}
    {w : {w : _root_.NumberField.InfinitePlace K // w.IsReal}}
    (hB : ∀ x : _root_.NumberField.mixedEmbedding.mixedSpace K, _root_.NumberField.mixedEmbedding.negAt ({w} : _root_.Set _) x ∈ B ↔ x ∈ B) (hm : _root_.MeasurableSet B) :
    _root_.MeasureTheory.MeasureSpace.volume B = 2 * _root_.MeasureTheory.MeasureSpace.volume (B ∩ {x | 0 < x.1 w}) := by
  have hmP : _root_.MeasurableSet (B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | 0 < x.1 w}) :=
    hm.inter (_root_.measurableSet_lt _root_.measurable_const (by fun_prop))
  have hmN : _root_.MeasurableSet (B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | x.1 w < 0}) :=
    hm.inter (_root_.measurableSet_lt (by fun_prop) _root_.measurable_const)
  -- reflecting at `w` carries the part of `B` negative at `w` onto the part positive at `w`
  have hNP : B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | x.1 w < 0}
      = _root_.NumberField.mixedEmbedding.negAt ({w} : _root_.Set _) ⁻¹' (B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | 0 < x.1 w}) := by
    ext x
    simp [hB]
  have hcover : (B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | 0 < x.1 w} ∪ B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | x.1 w < 0})
      ∪ B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | x.1 w = 0} = B := by
    ext x
    grind
  have hdisj : _root_.Disjoint (B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | 0 < x.1 w})
      (B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | x.1 w < 0}) := by
    grind
  -- the slice where the coordinate vanishes is null, so it does not change the volume
  have hvolB : _root_.MeasureTheory.MeasureSpace.volume B = _root_.MeasureTheory.MeasureSpace.volume (B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | 0 < x.1 w}
      ∪ B ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | x.1 w < 0}) := by
    nth_rewrite 1 [← hcover]
    exact _root_.MeasureTheory.measure_congr <| _root_.MeasureTheory.union_ae_eq_left_of_ae_eq_empty <| ae_eq_empty.mpr <|
      _root_.MeasureTheory.measure_mono_null _root_.Set.inter_subset_right (_root_.NumberField.mixedEmbedding.volume_eq_zero w)
  rw [hvolB, _root_.MeasureTheory.measure_union hdisj hmN, hNP,
    volume_preserving_negAt.measure_preimage hmP.nullMeasurableSet, _root_.two_mul]

omit [_root_.NumberField K] in
/-- The points positive at every place of `S` form an open set: it is a finite intersection of
open half spaces. -/
theorem TauCeti.NumberField.mixedEmbedding.isOpen_setOfPred_forall_mem_pos (S : _root_.Finset {w : _root_.NumberField.InfinitePlace K // w.IsReal}) :
    _root_.IsOpen {x : _root_.NumberField.mixedEmbedding.mixedSpace K | ∀ w ∈ S, 0 < x.1 w} := by
  simp only [_root_.Set.ofPred_forall]
  exact _root_.isOpen_biInter_finset fun w _ ↦ _root_.isOpen_lt _root_.continuous_const (by fun_prop)

open scoped Classical in
/-- **The volume of a sign cut at a finset of real places.**  If reflecting the real coordinate at
any one place of `S` preserves `A`, then prescribing a positive sign at each place of `S` divides
the volume of `A` by `2 ^ S.card`. -/
theorem solution (S : _root_.Finset {w : _root_.NumberField.InfinitePlace K // w.IsReal})
    {A : _root_.Set (_root_.NumberField.mixedEmbedding.mixedSpace K)}
    (hA : ∀ w ∈ S, ∀ x : _root_.NumberField.mixedEmbedding.mixedSpace K, _root_.NumberField.mixedEmbedding.negAt ({w} : _root_.Set _) x ∈ A ↔ x ∈ A)
    (hm : _root_.MeasurableSet A) : _root_.MeasureTheory.MeasureSpace.volume A = 2 ^ S.card * _root_.MeasureTheory.MeasureSpace.volume (A ∩ {x | ∀ w ∈ S, 0 < x.1 w}) := by
  induction S using _root_.Finset.induction_on with
  | empty => simp
  | @insert w S hw ih =>
    -- reflecting at `w` fixes `A`, and it fixes the cut along `S` because `w ∉ S`
    have hstable (x : _root_.NumberField.mixedEmbedding.mixedSpace K) : _root_.NumberField.mixedEmbedding.negAt ({w} : _root_.Set _) x ∈ A ∩ {x | ∀ v ∈ S, 0 < x.1 v}
        ↔ x ∈ A ∩ {x | ∀ v ∈ S, 0 < x.1 v} := by
      grind [_root_.NumberField.mixedEmbedding.negAt_apply_isReal_and_notMem]
    simp only [_root_.Finset.forall_mem_insert, _root_.Set.ofPred_and]
    rw [_root_.Finset.card_insert_of_notMem hw, _root_.pow_succ,
      ih fun v hv ↦ hA v (_root_.Finset.mem_insert_of_mem hv),
      _root_.Set.inter_comm {x : _root_.NumberField.mixedEmbedding.mixedSpace K | 0 < x.1 w}, ← _root_.Set.inter_assoc,
      _root_.TauCeti.NumberField.mixedEmbedding.volume_eq_two_mul_volume_inter_pos_at hstable
        (hm.inter (_root_.TauCeti.NumberField.mixedEmbedding.isOpen_setOfPred_forall_mem_pos S).measurableSet), _root_.mul_assoc]

end TauCeti.NumberField.mixedEmbedding

end
end
