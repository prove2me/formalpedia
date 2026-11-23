-- Prove2me | solution 1 for X25519Dalek.fnOk_edwardsPoint_mul_by_pow_2_four_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T20:12:33.609571+00:00
-- url     : https://prove2.me/submissions/dfccc942-01a7-4fa6-85f9-c1cc5c41bb1a

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.BitVec
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_X25519Dalek_Spec
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Arm64Facts_steps_codeLoaded_v2
import Theorems.Thm_X25519Dalek_fnOk_fe51_mul_v2
import Theorems.Thm_X25519Dalek_fnOk_projectivePoint_double_v2

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

section
/-! Port of google-deepmind/code-verification @ 8c8d371f arm64-semantics/ProofLib/Invariant.lean (Apache-2.0): every Step keeps frozen memory, so loaded code stays loaded. -/


/-! Port of ProofLib/ReadWritevFrame.lean (same commit). -/
namespace ProofLib
open Arm64

open Arm64

namespace RwvFrame

variable {R : State → State → Prop}

end RwvFrame

end ProofLib


namespace Arm64

namespace Perm

@[simp] theorem rwx_protNone : Perm.protNone.rwx = Perm.protNone := rfl
@[simp] theorem rwx_ro : Perm.ro.rwx = Perm.ro := rfl
@[simp] theorem rwx_rw : Perm.rw.rwx = Perm.rw := rfl
@[simp] theorem rwx_rx : Perm.rx.rwx = Perm.rx := rfl
@[simp] theorem rwx_rwx (p : Perm) : p.rwx.rwx = p.rwx := rfl
@[simp] theorem rwx_r (p : Perm) : p.rwx.r = p.r := rfl
@[simp] theorem rwx_w (p : Perm) : p.rwx.w = p.w := rfl
@[simp] theorem rwx_x (p : Perm) : p.rwx.x = p.x := rfl
@[simp] theorem rwx_frozen (p : Perm) : p.rwx.frozen = p.frozen := rfl

end Perm

@[simp] theorem _root_.Option.map_rwx_some (p : Perm) : (some p).map Perm.rwx = some p.rwx := rfl
@[simp] theorem _root_.Option.map_rwx_none : (none : Option Perm).map Perm.rwx = none := rfl

namespace Memory

/-! ## Base interface of the representation -/

@[simp] theorem perm_map_rwx (m : Memory) (a : BitVec 64) : (m.perm a).map Perm.rwx = m.perm a := by
  unfold perm
  rcases m.cells a with _ | ⟨_ | p, _⟩ <;> rfl

@[simp] theorem read8_write8 (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8) :
    (m.write8 a1 v).read8 a2 = if a2 = a1 then v else m.read8 a2 := by
  unfold read8 write8
  by_cases h : a2 = a1 <;> simp [h]

@[simp] theorem perm_write8_apply (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8) :
    (m.write8 a1 v).perm a2 = m.perm a2 := by
  unfold write8 rawPerm perm
  by_cases h : a2 = a1
  · subst h
    dsimp only
    simp only [↓reduceIte]
    rcases m.cells a2 with _ | ⟨_ | p, _⟩ <;> rfl
  · simp [h]

@[simp] theorem isLazyFree_write8 (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8) :
    (m.write8 a1 v).isLazyFree a2 = if a2 = a1 then false else m.isLazyFree a2 := by
  unfold write8 rawPerm isLazyFree
  by_cases h : a2 = a1
  · subst h
    dsimp only
    simp only [↓reduceIte]
    rcases m.cells a2 with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩
    · rfl
    · rfl
    · cases r <;> cases w <;> cases x <;> cases lf <;> rfl
  · simp [h]

@[simp] theorem isAnon_write8_apply (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8) :
    (m.write8 a1 v).isAnon a2 = m.isAnon a2 := by
  unfold write8 rawPerm isAnon
  by_cases h : a2 = a1
  · subst h
    dsimp only
    simp only [↓reduceIte]
    rcases m.cells a2 with _ | ⟨_ | p, _⟩ <;> rfl
  · simp [h]

@[simp] theorem read8_empty (a : BitVec 64) : empty.read8 a = 0#8 := rfl
@[simp] theorem perm_empty (a : BitVec 64) : empty.perm a = none := rfl
@[simp] theorem isLazyFree_empty (a : BitVec 64) : empty.isLazyFree a = false := rfl
@[simp] theorem isAnon_empty (a : BitVec 64) : empty.isAnon a = false := rfl

@[simp] theorem read8_ofFn (bytes : BitVec 64 → BitVec 8) (p : BitVec 64 → Option Perm) (a : BitVec 64) :
    (ofFn bytes p).read8 a = bytes a := rfl
@[simp] theorem perm_ofFn (bytes : BitVec 64 → BitVec 8) (p : BitVec 64 → Option Perm) (a : BitVec 64) :
    (ofFn bytes p).perm a = (p a).map Perm.rwx := by
  unfold ofFn perm
  dsimp only
  cases p a <;> rfl
@[simp] theorem isLazyFree_ofFn (bytes : BitVec 64 → BitVec 8) (p : BitVec 64 → Option Perm) (a : BitVec 64) :
    (ofFn bytes p).isLazyFree a = match p a with | some q => q.lazyFree | none => false := by
  unfold ofFn isLazyFree
  dsimp only
  cases p a <;> rfl
@[simp] theorem isAnon_ofFn (bytes : BitVec 64 → BitVec 8) (p : BitVec 64 → Option Perm) (a : BitVec 64) :
    (ofFn bytes p).isAnon a = match p a with | some q => q.anon | none => false := by
  unfold ofFn isAnon
  dsimp only
  cases p a <;> rfl

theorem perm_mk (f : BitVec 64 → Option (Option Perm × BitVec 8)) (a : BitVec 64) :
    perm ⟨f⟩ a = match f a with | some (some p, _) => some p.rwx | _ => none := rfl
theorem read8_mk (f : BitVec 64 → Option (Option Perm × BitVec 8)) (a : BitVec 64) :
    read8 ⟨f⟩ a = match f a with | some (_, b) => b | none => 0#8 := rfl
theorem isLazyFree_mk (f : BitVec 64 → Option (Option Perm × BitVec 8)) (a : BitVec 64) :
    isLazyFree ⟨f⟩ a = match f a with | some (some p, _) => p.lazyFree | _ => false := rfl
theorem isAnon_mk (f : BitVec 64 → Option (Option Perm × BitVec 8)) (a : BitVec 64) :
    isAnon ⟨f⟩ a = match f a with | some (some p, _) => p.anon | _ => false := rfl

theorem isLazyFree_eq_false_of_unmapped {m : Memory} {a : BitVec 64}
    (hu : (m.perm a).mapped = false) : m.isLazyFree a = false := by
  unfold perm at hu
  unfold isLazyFree
  cases hca : m.cells a with
  | none => rfl
  | some pb =>
    rcases pb with ⟨po, _⟩
    cases po with
    | none => rfl
    | some _ => simp [hca] at hu

@[simp] theorem write8_write8_same (m : Memory) (a : BitVec 64) (x y : BitVec 8) :
    (m.write8 a x).write8 a y = m.write8 a y := by
  ext addr
  unfold write8 rawPerm
  by_cases h : addr = a
  · subst h
    dsimp only
    simp only [↓reduceIte]
    rcases m.cells addr with _ | ⟨_ | ⟨r, w, xv, lf, an⟩, _⟩
    · rfl
    · rfl
    · cases r <;> cases w <;> cases xv <;> cases lf <;> rfl
  · simp [h]

@[simp] theorem read8_mapFresh (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm)
    (a : BitVec 64) : (m.mapFresh base len p).read8 a = m.read8 a := by
  rw [mapFresh, read8_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isLazyFree_mapZero (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.mapZero base len).isLazyFree a = m.isLazyFree a := by
  rw [mapZero, isLazyFree_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [h.1, h.2, Bool.not_false, Bool.and_self, ↓reduceIte]
    exact (isLazyFree_eq_false_of_unmapped h.2).symm
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem read8_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.setPermNonFrozen base len p).read8 a = m.read8 a := by
  rw [setPermNonFrozen, read8_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isLazyFree_setPermNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.setPermNonFrozen base len p).isLazyFree a = m.isLazyFree a := by
  rw [setPermNonFrozen, isLazyFree_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isLazyFree_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) :
    (m.setPermNonFrozen base len p).isLazyFree = m.isLazyFree :=
  funext (isLazyFree_setPermNonFrozen_apply m base len p)

@[simp] theorem isAnon_setPermNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.setPermNonFrozen base len p).isAnon a = m.isAnon a := by
  rw [setPermNonFrozen, isAnon_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isAnon_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) :
    (m.setPermNonFrozen base len p).isAnon = m.isAnon :=
  funext (isAnon_setPermNonFrozen_apply m base len p)

theorem perm_zeroNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.zeroNonFrozen base len).perm a = m.perm a := by
  rw [zeroNonFrozen, perm_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    unfold perm
    rcases m.cells a with _ | ⟨_ | p, _⟩ <;> rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem perm_zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    (m.zeroNonFrozen base len).perm = m.perm :=
  funext (perm_zeroNonFrozen_apply m base len)

@[simp] theorem isAnon_zeroNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.zeroNonFrozen base len).isAnon a = m.isAnon a := by
  rw [zeroNonFrozen, isAnon_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    have hm : (m.perm a).mapped = true := by simp only [Bool.and_eq_true] at h; exact h.1.2
    unfold perm at hm ⊢
    unfold isAnon
    rcases hca : m.cells a with _ | ⟨_ | p, _⟩
    · simp [hca] at hm
    · simp [hca] at hm
    · rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isAnon_zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    (m.zeroNonFrozen base len).isAnon = m.isAnon :=
  funext (isAnon_zeroNonFrozen_apply m base len)

theorem perm_madvFreeNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.madvFreeNonFrozen base len).perm a = m.perm a := by
  rw [madvFreeNonFrozen, perm_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    unfold perm
    rcases m.cells a with _ | ⟨_ | p, _⟩ <;> rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem perm_madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    (m.madvFreeNonFrozen base len).perm = m.perm :=
  funext (perm_madvFreeNonFrozen_apply m base len)

@[simp] theorem read8_madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.madvFreeNonFrozen base len).read8 a = m.read8 a := by
  rw [madvFreeNonFrozen, read8_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isAnon_madvFreeNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.madvFreeNonFrozen base len).isAnon a = m.isAnon a := by
  rw [madvFreeNonFrozen, isAnon_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    have hm : (m.perm a).mapped = true := by simp only [Bool.and_eq_true] at h; exact h.1.2
    unfold perm at hm ⊢
    unfold isAnon
    rcases hca : m.cells a with _ | ⟨_ | p, _⟩
    · simp [hca] at hm
    · simp [hca] at hm
    · rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isAnon_madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    (m.madvFreeNonFrozen base len).isAnon = m.isAnon :=
  funext (isAnon_madvFreeNonFrozen_apply m base len)

/-! ## Permissions are unchanged by writes -/

@[simp] theorem perm_write8 (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).perm = m.perm := funext fun b => perm_write8_apply m a b v
@[simp] theorem perm_write16 (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (m.write16 a v).perm = m.perm := by simp only [write16, perm_write8]
@[simp] theorem perm_write32 (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (m.write32 a v).perm = m.perm := by simp only [write32, perm_write8]
@[simp] theorem perm_write64 (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).perm = m.perm := by simp only [write64, perm_write8]
@[simp] theorem perm_write128 (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    (m.write128 a v).perm = m.perm := by simp only [write128, perm_write64]
@[simp] theorem perm_writeSized (m : Memory) (sz : MemWidth) (a v : BitVec 64) :
    (m.writeSized sz a v).perm = m.perm := by
  cases sz <;> simp only [writeSized, perm_write8, perm_write16, perm_write32, perm_write64]
@[simp] theorem perm_writeSimdSized (m : Memory) (sz : SimdMemSize) (a : BitVec 64)
    (v : BitVec 128) : (m.writeSimdSized sz a v).perm = m.perm := by
  cases sz <;> simp only [writeSimdSized, perm_write8, perm_write16, perm_write32, perm_write64,
    perm_write128]
@[simp] theorem perm_writeBytes (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes a bs).perm = m.perm := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => exact (ih _ _).trans (perm_write8 _ _ _)

@[simp] theorem isAnon_write8 (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isAnon = m.isAnon := funext fun b => isAnon_write8_apply m a b v
@[simp] theorem isAnon_write16 (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (m.write16 a v).isAnon = m.isAnon := by simp only [write16, isAnon_write8]
@[simp] theorem isAnon_write32 (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (m.write32 a v).isAnon = m.isAnon := by simp only [write32, isAnon_write8]
@[simp] theorem isAnon_write64 (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).isAnon = m.isAnon := by simp only [write64, isAnon_write8]
@[simp] theorem isAnon_write128 (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    (m.write128 a v).isAnon = m.isAnon := by simp only [write128, isAnon_write64]
@[simp] theorem isAnon_writeSized (m : Memory) (sz : MemWidth) (a v : BitVec 64) :
    (m.writeSized sz a v).isAnon = m.isAnon := by
  cases sz <;> simp only [writeSized, isAnon_write8, isAnon_write16, isAnon_write32, isAnon_write64]
@[simp] theorem isAnon_writeSimdSized (m : Memory) (sz : SimdMemSize) (a : BitVec 64)
    (v : BitVec 128) : (m.writeSimdSized sz a v).isAnon = m.isAnon := by
  cases sz <;> simp only [writeSimdSized, isAnon_write8, isAnon_write16, isAnon_write32,
    isAnon_write64, isAnon_write128]
@[simp] theorem isAnon_writeBytes (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes a bs).isAnon = m.isAnon := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => exact (ih _ _).trans (isAnon_write8 _ _ _)

/-- `allPerm` only depends on `perm`. -/
theorem allPerm_congr {m m' : Memory} (h : m'.perm = m.perm) (p : Option Perm → Bool)
    (a : BitVec 64) (n : Nat) : m'.allPerm p a n = m.allPerm p a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [allPerm, h, ih]

theorem canMap_congr {m m' : Memory} (h : m'.perm = m.perm) (a : BitVec 64) (n : Nat) :
    m'.canMap a n = m.canMap a n := allPerm_congr h _ a n

@[simp] theorem canMap_write8 (m : Memory) (a : BitVec 64) (v : BitVec 8)
    (b : BitVec 64) (n : Nat) : (m.write8 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write8 m a v) b n
@[simp] theorem canMap_write16 (m : Memory) (a : BitVec 64) (v : BitVec 16)
    (b : BitVec 64) (n : Nat) : (m.write16 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write16 m a v) b n
@[simp] theorem canMap_write32 (m : Memory) (a : BitVec 64) (v : BitVec 32)
    (b : BitVec 64) (n : Nat) : (m.write32 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write32 m a v) b n
@[simp] theorem canMap_write64 (m : Memory) (a : BitVec 64) (v : BitVec 64)
    (b : BitVec 64) (n : Nat) : (m.write64 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write64 m a v) b n
@[simp] theorem canMap_write128 (m : Memory) (a : BitVec 64) (v : BitVec 128)
    (b : BitVec 64) (n : Nat) : (m.write128 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write128 m a v) b n

/-! ## `KeepsFrozen` -/

@[simp]
theorem KeepsFrozen.refl (m : Memory) : m.KeepsFrozen m := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

end Memory

end Arm64
end

section
/-! # Separation-logic heap algebra

Ported from google-deepmind/code-verification @ 8c8d371f (Apache-2.0),
`arm64-semantics/ProofLib/CoreLemmas.lean` and `ProofLib/SepLogic/Model.lean`: the plain lemmas
about `Heap.Disjoint`, `Heap.union`, `Heap.Matches` and `sepConj`, with ProofLib's custom simp
attributes removed. -/

set_option autoImplicit false

namespace Arm64

namespace SepProp
theorem satisfies_iff {P : SepProp} {m : Memory} :
    (m ⊨ P) ↔ ∃ h : Heap, P.holds h ∧ h.Matches m := Iff.rfl
theorem entails_iff {P Q : SepProp} : (P ⊢ Q) ↔ ∀ h : Heap, P.holds h → Q.holds h := Iff.rfl
theorem holds_emp_iff {h : Heap} : (emp : SepProp).holds h ↔ h = Heap.empty := Iff.rfl
theorem holds_sepConj_iff {P Q : SepProp} {h : Heap} :
    (P ∗ Q).holds h ↔
      ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.holds h₁ ∧ Q.holds h₂ := Iff.rfl
theorem holds_sepExists_iff {α : Sort _} {P : α → SepProp} {h : Heap} :
    (sepExists P).holds h ↔ ∃ x, (P x).holds h := Iff.rfl
end SepProp

theorem holds_pointsTo8_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8 a v).holds h ↔ h = Heap.singleton a v := Iff.rfl

namespace Heap

theorem Disjoint.symm {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) : h₂.Disjoint h₁ := by
  refine ⟨fun a => ?_, fun γ k => (hd.2.1 γ k).symm, fun γ k => (hd.2.2.1 γ k).symm,
    fun γ k oa v h => hd.2.2.2.1 γ k oa v h.symm, fun a => (hd.2.2.2.2 a).symm⟩
  rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inr ⟨b, h2, h1⟩)

theorem Disjoint.of_phys_left {h₁ h₂ : Heap}
    (ha : h₁.auth = fun _ _ => none := by rfl)
    (hf : h₁.frag = fun _ _ => none := by rfl)
    (hp : ∀ a, h₁.phys a = none ∨ h₂.phys a = none ∨
      ∃ b, h₁.phys a = some (.ro b) ∧ h₂.phys a = some (.ro b))
    (hm : h₁.mapped = fun _ => false := by rfl) :
    h₁.Disjoint h₂ := by
  refine ⟨hp, fun γ k => Or.inl (congrFun (congrFun ha γ) k),
    fun γ k => Or.inl (congrFun (congrFun hf γ) k), fun γ k oa v h => ?_,
    fun a => Or.inl (congrFun hm a)⟩
  rcases h with ⟨h1, _⟩ | ⟨_, h1⟩
  · rw [congrFun (congrFun ha γ) k] at h1; contradiction
  · rw [congrFun (congrFun hf γ) k] at h1; contradiction

@[simp]
theorem disjoint_empty_left (h : Heap) : Heap.empty.Disjoint h :=
  Disjoint.of_phys_left rfl rfl (fun _ => Or.inl rfl)

@[simp]
theorem disjoint_empty_right (h : Heap) : h.Disjoint Heap.empty :=
  (disjoint_empty_left h).symm

@[simp]
theorem union_empty_left (h : Heap) : Heap.empty.union h = h := by
  cases h; rfl

@[simp]
theorem union_empty_right (h : Heap) : h.union Heap.empty = h := by
  apply Heap.ext
  · funext a; dsimp [union, empty]; cases h.phys a <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.auth γ k <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.frag γ k <;> rfl
  · funext a; dsimp [union, empty]; cases h.mapped a <;> rfl

theorem union_comm_of_disjoint {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) :
    h₁.union h₂ = h₂.union h₁ := by
  apply Heap.ext
  · funext a; dsimp [union]
    rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
    · rw [h1]; cases h₂.phys a <;> rfl
    · rw [h2]; cases h₁.phys a <;> rfl
    · rw [h1, h2]
  · funext γ k; dsimp [union]
    rcases hd.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.auth γ k <;> rfl
    · rw [h2]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]
    rcases hd.2.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.frag γ k <;> rfl
    · rw [h2]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]
    rcases hd.2.2.2.2 a with h1 | h2
    · rw [h1]; cases h₂.mapped a <;> rfl
    · rw [h2]; cases h₁.mapped a <;> rfl

theorem union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  apply Heap.ext
  · funext a; dsimp [union]; cases h₁.phys a <;> rfl
  · funext γ k; dsimp [union]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]; cases h₁.mapped a <;> rfl

theorem disjoint_union_left {h₁ h₂ h₃ : Heap} (hd12 : h₁.Disjoint h₂) :
    (h₁.union h₂).Disjoint h₃ ↔ h₁.Disjoint h₃ ∧ h₂.Disjoint h₃ := by
  constructor
  · intro hd
    have hphys1 : ∀ a, h₁.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₁.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => exact Or.inl rfl
        | some c => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
    have hphys2 : ∀ a, h₂.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₂.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
        | some c =>
          rw [h] at hu
          rcases hd12.1 a with h1 | h2 | ⟨b', h1, h2⟩
          · rw [h] at h1; contradiction
          · exact Or.inl h2
          · rw [h1] at h; cases h; cases hu; exact Or.inr (Or.inr ⟨b, h2, h3⟩)
    have hauth1 : ∀ γ k, h₁.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hauth2 : ∀ γ k, h₂.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hfrag1 : ∀ γ k, h₁.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hfrag2 : ∀ γ k, h₂.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hcompat1 : ∀ γ k oa v,
        ((h₁.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₁.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      ·exact Or.inl ⟨by dsimp [union]; rw [ha], hf⟩
      · exact Or.inr ⟨ha, by dsimp [union]; rw [hf]⟩
    have hcompat2 : ∀ γ k oa v,
        ((h₂.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₂.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · rcases hd12.2.1 γ k with h1 | h2
        · exact Or.inl ⟨by dsimp [union]; rw [h1, ha], hf⟩
        · rw [ha] at h2; contradiction
      · rcases hd12.2.2.1 γ k with h1 | h2
        · exact Or.inr ⟨ha, by dsimp [union]; rw [h1, hf]⟩
        · rw [hf] at h2; contradiction
    have hmapped1 : ∀ a, h₁.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    have hmapped2 : ∀ a, h₂.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    exact ⟨⟨hphys1, hauth1, hfrag1, hcompat1, hmapped1⟩, ⟨hphys2, hauth2, hfrag2, hcompat2, hmapped2⟩⟩
  · rintro ⟨hd1, hd2⟩
    refine ⟨fun a => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v h => ?_, fun a => ?_⟩
    · dsimp [union]
      cases h : h₁.phys a with
      | none => exact hd2.1 a
      | some c =>
        rcases hd1.1 a with h1 | h3 | ⟨b, h1, h3⟩
        · rw [h] at h1; contradiction
        · exact Or.inr (Or.inl h3)
        · rw [h] at h1; exact Or.inr (Or.inr ⟨b, h1, h3⟩)
    · dsimp [union]
      cases h : h₁.auth γ k with
      | none => exact hd2.2.1 γ k
      | some oa =>
        rcases hd1.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · dsimp [union]
      cases h : h₁.frag γ k with
      | none => exact hd2.2.2.1 γ k
      | some v =>
        rcases hd1.2.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · dsimp [union] at ha
        cases h1 : h₁.auth γ k with
        | none =>
          rw [h1] at ha
          exact hd2.2.2.2.1 γ k oa v (Or.inl ⟨ha, hf⟩)
        | some oa' =>
          rw [h1] at ha; cases ha
          exact hd1.2.2.2.1 γ k oa v (Or.inl ⟨h1, hf⟩)
      · dsimp [union] at hf
        cases h1 : h₁.frag γ k with
        | none =>
          rw [h1] at hf
          exact hd2.2.2.2.1 γ k oa v (Or.inr ⟨ha, hf⟩)
        | some v' =>
          rw [h1] at hf; cases hf
          exact hd1.2.2.2.1 γ k oa v (Or.inr ⟨ha, h1⟩)
    · dsimp [union]
      cases h : h₁.mapped a with
      | false => exact hd2.2.2.2.2 a
      | true =>
        rcases hd1.2.2.2.2 a with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} (hd23 : h₂.Disjoint h₃) :
    h₁.Disjoint (h₂.union h₃) ↔ h₁.Disjoint h₂ ∧ h₁.Disjoint h₃ := by
  constructor
  · intro hd
    have hd' := (disjoint_union_left hd23).mp hd.symm
    exact ⟨hd'.1.symm, hd'.2.symm⟩
  · rintro ⟨hd1, hd2⟩
    exact ((disjoint_union_left hd23).mpr ⟨hd1.symm, hd2.symm⟩).symm

theorem GhostValid.of_union_left {h₁ h₂ : Heap} (hv : (h₁.union h₂).GhostValid) :
    h₁.GhostValid := by
  rcases hv with ⟨b, hb⟩
  refine ⟨b, fun γ hγ k => ?_⟩
  have ⟨hau, hfu⟩ := hb γ hγ k
  dsimp [Heap.union] at hau hfu
  constructor
  · cases h : h₁.auth γ k with
    | none => rfl
    | some _ => rw [h] at hau; contradiction
  · cases h : h₁.frag γ k with
    | none => rfl
    | some _ => rw [h] at hfu; contradiction

theorem Matches.of_union_left {h₁ h₂ : Heap} {m : Memory}
    (hm : (h₁.union h₂).Matches m) :
    h₁.Matches m :=
  ⟨fun a c h1 => hm.1 a c (by dsimp [Heap.union]; rw [h1]),
    GhostValid.of_union_left hm.2.1,
    fun a h1 => hm.2.2 a (by dsimp [Heap.union]; rw [h1, Bool.true_or])⟩

end Heap

theorem Entails.refl (P : SepProp) : P ⊢ P := SepProp.entails_iff.mpr fun _ h => h

theorem Entails.trans {P Q R : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  SepProp.entails_iff.mpr fun h hp => SepProp.entails_iff.mp h2 h (SepProp.entails_iff.mp h1 h hp)

theorem Satisfies.mono {P Q : SepProp} (h : P ⊢ Q) {m : Memory} (hm : m ⊨ P) : m ⊨ Q := by
  rcases SepProp.satisfies_iff.mp hm with ⟨hp, hP, hM⟩
  exact SepProp.satisfies_iff.mpr ⟨hp, SepProp.entails_iff.mp h hp hP, hM⟩











theorem sepConj_comm (P Q : SepProp) : (P ∗ Q) = (Q ∗ P) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hq, hp⟩
  · rintro ⟨h₁, h₂, hd, rfl, hq, hp⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hp, hq⟩



@[simp]
theorem sepConj_assoc (P Q R : SepProp) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁₂, h₃, hd12_3, rfl, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩
    have ⟨hd1_3, hd2_3⟩ := (Heap.disjoint_union_left hd1_2).mp hd12_3
    exact ⟨h₁, h₂.union h₃, (Heap.disjoint_union_right hd2_3).mpr ⟨hd1_2, hd1_3⟩,
      Heap.union_assoc h₁ h₂ h₃, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
  · rintro ⟨h₁, h₂₃, hd1_23, rfl, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
    have ⟨hd1_2, hd1_3⟩ := (Heap.disjoint_union_right hd2_3).mp hd1_23
    exact ⟨h₁.union h₂, h₃, (Heap.disjoint_union_left hd1_2).mpr ⟨hd1_3, hd2_3⟩,
      (Heap.union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩

/-- Left commutativity of separating conjunction: `P ∗ (Q ∗ R) = Q ∗ (P ∗ R)`. -/
theorem sepConj_left_comm (P Q R : SepProp) : (P ∗ (Q ∗ R)) = (Q ∗ (P ∗ R)) := by
  rw [← sepConj_assoc, sepConj_comm P Q, sepConj_assoc]

instance instAssociativeSepConj : Std.Associative SepProp.sepConj where
  assoc := sepConj_assoc

instance instCommutativeSepConj : Std.Commutative SepProp.sepConj where
  comm := sepConj_comm

theorem Entails.of_eq {P Q : SepProp} (heq : P = Q := by ac_rfl) : P ⊢ Q :=
  heq ▸ Entails.refl P

theorem Satisfies.of_eq {P Q : SepProp} {m : Memory}
    (h : m ⊨ P) (heq : P = Q := by ac_rfl) : m ⊨ Q :=
  heq ▸ h

@[simp]
theorem emp_sepConj (P : SepProp) : (SepProp.emp ∗ P) = P := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_emp_iff]
  constructor
  · rintro ⟨h₁, h₂, _, rfl, rfl, hp⟩
    simpa using hp
  · intro hp
    exact ⟨Heap.empty, h, Heap.disjoint_empty_left h, (Heap.union_empty_left h).symm, rfl, hp⟩

@[simp]
theorem sepConj_emp (P : SepProp) : (P ∗ SepProp.emp) = P := by
  rw [sepConj_comm, emp_sepConj]


end Arm64
end

section
/-! # Byte-slice ownership: reads, writes, splits

Plain-Lean replacements for the parts of DeepMind's ProofLib (google-deepmind/code-verification
@ 8c8d371f, Apache-2.0, `ProofLib/SepLogic/Bytes.lean`) that the x25519 ladder proofs use:
`a ↦ₛ bs` owns `bs` at `a`; a store to an owned byte updates the list; `pointsTo64` and `memRegion`
are byte slices. -/

set_option autoImplicit false

namespace Arm64

theorem pointsToBytes_cons (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    (a ↦ₛ (b :: bs)) = (a ↦₈ b) ∗ ((a + 1#64) ↦ₛ bs) := rfl
theorem pointsToBytes_nil (a : BitVec 64) : (a ↦ₛ ([] : List (BitVec 8))) = emp := rfl

namespace Heap

/-- `h` with the cell at `x` replaced by `c`. -/
def upd (h : Heap) (x : BitVec 64) (c : HeapCell) : Heap :=
  { h with phys := fun y => if y = x then some c else h.phys y }

theorem upd_union_left (h₁ h₂ : Heap) (x : BitVec 64) (c : HeapCell) :
    (h₁.union h₂).upd x c = (h₁.upd x c).union h₂ := by
  apply Heap.ext
  · funext y; by_cases hy : y = x <;> simp [upd, union, hy]
  · rfl
  · rfl
  · rfl

theorem upd_union_right (h₁ h₂ : Heap) (x : BitVec 64) (c : HeapCell) (hx : h₁.phys x = none) :
    (h₁.union h₂).upd x c = h₁.union (h₂.upd x c) := by
  apply Heap.ext
  · funext y; by_cases hy : y = x
    · subst hy; simp [upd, union, hx]
    · simp [upd, union, hy]
  · rfl
  · rfl
  · rfl

theorem Disjoint.upd_left {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} (c : HeapCell)
    (hx : h₂.phys x = none) : (h₁.upd x c).Disjoint h₂ := by
  refine ⟨fun y => ?_, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
  by_cases hy : y = x
  · subst hy; exact Or.inr (Or.inl hx)
  · simp only [upd, hy, if_false]; exact hd.1 y

theorem Disjoint.upd_right {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} (c : HeapCell)
    (hx : h₁.phys x = none) : h₁.Disjoint (h₂.upd x c) :=
  (hd.symm.upd_left c hx).symm

theorem rw_phys_right_none {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} {b : BitVec 8}
    (hx : h₁.phys x = some (.rw b)) : h₂.phys x = none := by
  rcases hd.1 x with h | h | ⟨b', h1, _⟩
  · rw [hx] at h; cases h
  · exact h
  · rw [hx] at h1; cases h1

theorem rw_phys_left_none {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} {b : BitVec 8}
    (hx : h₂.phys x = some (.rw b)) : h₁.phys x = none :=
  rw_phys_right_none hd.symm hx

end Heap

/-! ## Memory facts about `write8` -/

namespace Memory

theorem read8_write8_same' (m : Memory) (x : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).read8 x = v := by
  simp [write8, read8]

theorem read8_write8_ne' (m : Memory) {x y : BitVec 64} (v : BitVec 8) (h : y ≠ x) :
    (m.write8 x v).read8 y = m.read8 y := by
  simp [write8, read8, h]

theorem perm_write8' (m : Memory) (x y : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).perm y = m.perm y := by
  by_cases h : y = x
  · subst h; simp only [write8, perm, rawPerm, if_true]
    cases hc : m.cells y with
    | none => rfl
    | some c => obtain ⟨p, b⟩ := c; cases p <;> rfl
  · simp [write8, perm, h]

theorem isAnon_write8' (m : Memory) (x y : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).isAnon y = m.isAnon y := by
  by_cases h : y = x
  · subst h; simp only [write8, isAnon, rawPerm, if_true]
    cases hc : m.cells y with
    | none => rfl
    | some c => obtain ⟨p, b⟩ := c; cases p <;> rfl
  · simp [write8, isAnon, h]

theorem isLazyFree_write8_same' (m : Memory) (x : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).isLazyFree x = false := by
  simp only [write8, isLazyFree, rawPerm, if_true]
  cases hc : m.cells x with
  | none => rfl
  | some c => obtain ⟨p, b⟩ := c; cases p <;> rfl

theorem isLazyFree_write8_ne' (m : Memory) {x y : BitVec 64} (v : BitVec 8) (h : y ≠ x) :
    (m.write8 x v).isLazyFree y = m.isLazyFree y := by
  simp [write8, isLazyFree, h]

end Memory

namespace Heap

theorem Matches.upd_write {h : Heap} {m : Memory} (hm : h.Matches m) {x : BitVec 64} {b : BitVec 8}
    (hx : h.phys x = some (.rw b)) (v : BitVec 8) :
    (h.upd x (.rw v)).Matches (m.write8 x v) := by
  refine ⟨fun y c hy => ?_, hm.2.1, fun y hy => ?_⟩
  · by_cases hyx : y = x
    · subst hyx
      simp only [upd, if_true, Option.some.injEq] at hy
      subst hy
      have h0 := hm.1 y _ hx
      simp only at h0
      refine ⟨Memory.read8_write8_same' _ _ _, ?_, Memory.isLazyFree_write8_same' _ _ _⟩
      rw [Memory.perm_write8']; exact h0.2.1
    · simp only [upd, hyx, if_false] at hy
      have h0 := hm.1 y c hy
      rw [Memory.read8_write8_ne' _ _ hyx, Memory.perm_write8', Memory.isLazyFree_write8_ne' _ _ hyx]
      exact h0
  · have h0 := hm.2.2 y hy
    rw [Memory.perm_write8', Memory.isAnon_write8']; exact h0

end Heap

/-! ## Byte slices as heaps -/

theorem bytes_phys : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h → ∀ (j : Nat) (hj : j < bs.length),
      h.phys (a + BitVec.ofNat 64 j) = some (.rw bs[j])
  | _, [], _, _, j, hj => by simp at hj
  | a, b :: bs, h, hh, j, hj => by
    obtain ⟨h1, h2, hd, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    cases j with
    | zero => simp [Heap.union, Heap.singleton]
    | succ j =>
      have ih := bytes_phys h2h j (by simp at hj; omega)
      have ha : a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc]; congr 1; bv_omega
      have hne : a + 1#64 + BitVec.ofNat 64 j ≠ a := by
        intro he
        have := Heap.rw_phys_left_none hd ih
        rw [he] at this; simp [Heap.singleton] at this
      rw [ha]
      simp only [Heap.union, Heap.singleton, hne, if_false, ih, List.getElem_cons_succ]

theorem bytes_upd : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h → ∀ (j : Nat) (hj : j < bs.length) (v : BitVec 8),
      (a ↦ₛ bs.set j v).holds (h.upd (a + BitVec.ofNat 64 j) (.rw v))
  | _, [], _, _, j, hj, _ => by simp at hj
  | a, b :: bs, h, hh, j, hj, v => by
    obtain ⟨h1, h2, hd, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    have h2a : h2.phys a = none :=
      Heap.rw_phys_right_none hd (b := b) (by simp [Heap.singleton])
    cases j with
    | zero =>
      simp only [List.set_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      rw [Heap.upd_union_left]
      refine SepProp.holds_sepConj_iff.mpr ⟨Heap.singleton a v, h2, ?_, ?_, rfl, h2h⟩
      · exact Heap.Disjoint.of_phys_left rfl rfl (fun y => by
          by_cases hy : y = a
          · subst hy; exact Or.inr (Or.inl h2a)
          · exact Or.inl (by simp [Heap.singleton, hy])) rfl
      · apply Heap.ext
        · funext y; by_cases hy : y = a <;> simp [Heap.upd, Heap.union, Heap.singleton, hy]
        · rfl
        · rfl
        · rfl
    | succ j =>
      have hj' : j < bs.length := by simp at hj; omega
      have ih := bytes_upd h2h j hj' v
      have ha : a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc]; congr 1; bv_omega
      have hph := bytes_phys h2h j hj'
      have hne : a + 1#64 + BitVec.ofNat 64 j ≠ a := by
        intro he; rw [he] at hph; rw [h2a] at hph; cases hph
      have h1x : (Heap.singleton a b).phys (a + 1#64 + BitVec.ofNat 64 j) = none := by
        simp [Heap.singleton, hne]
      rw [ha, Heap.upd_union_right _ _ _ _ h1x, List.set_cons_succ]
      exact SepProp.holds_sepConj_iff.mpr ⟨_, _, hd.upd_right _ h1x, rfl, rfl, ih⟩

/-! ## Satisfaction-level reads and writes -/

theorem sat_bytes_read {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (j : Nat) (hj : j < bs.length) :
    m.read8 (a + BitVec.ofNat 64 j) = bs[j] ∧ m.perm (a + BitVec.ofNat 64 j) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 j) = false := by
  obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1h, _⟩ := SepProp.holds_sepConj_iff.mp hh
  have hp := bytes_phys h1h j hj
  have := (Heap.Matches.of_union_left hm).1 _ _ hp
  exact this

theorem sat_bytes_write {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (j : Nat) (hj : j < bs.length) (v : BitVec 8) :
    (m.write8 (a + BitVec.ofNat 64 j) v) ⊨ (a ↦ₛ bs.set j v) ∗ F := by
  obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1h, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
  have hp := bytes_phys h1h j hj
  refine SepProp.satisfies_iff.mpr ⟨(h1.upd (a + BitVec.ofNat 64 j) (.rw v)).union h2, ?_, ?_⟩
  · exact SepProp.holds_sepConj_iff.mpr ⟨_, _, hd.upd_left _ (Heap.rw_phys_right_none hd hp), rfl,
      bytes_upd h1h j hj v, h2h⟩
  · rw [← Heap.upd_union_left]
    exact hm.upd_write (b := bs[j]) (by simp [Heap.union, hp]) v

/-! ## Splitting byte slices -/

theorem pointsToBytes_append (a : BitVec 64) (xs ys : List (BitVec 8)) :
    (a ↦ₛ (xs ++ ys)) = (a ↦ₛ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦ₛ ys) := by
  induction xs generalizing a with
  | nil => simp [pointsToBytes_nil]
  | cons x xs ih =>
    rw [List.cons_append, pointsToBytes_cons, pointsToBytes_cons, ih, sepConj_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (x :: xs).length := by
      simp only [List.length_cons]; rw [BitVec.add_assoc]; congr 1; bv_omega
    rw [e]

theorem pointsToBytes_split (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat) (hn : n ≤ bs.length) :
    (a ↦ₛ bs) = (a ↦ₛ bs.take n) ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs.drop n) := by
  have h := pointsToBytes_append a (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

/-- Unpack a 64-bit word into its 8 little-endian bytes. -/
def unpack64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

@[simp] theorem unpack64_length (v : BitVec 64) : (unpack64 v).length = 8 := rfl

theorem pointsTo64_eq_bytes (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦ₛ unpack64 v) := by
  simp only [pointsTo64, unpack64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by rw [BitVec.add_assoc]; rfl
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by rw [BitVec.add_assoc]; rfl
  have h4 : a + 3#64 + 1#64 = a + 4#64 := by rw [BitVec.add_assoc]; rfl
  have h5 : a + 4#64 + 1#64 = a + 5#64 := by rw [BitVec.add_assoc]; rfl
  have h6 : a + 5#64 + 1#64 = a + 6#64 := by rw [BitVec.add_assoc]; rfl
  have h7 : a + 6#64 + 1#64 = a + 7#64 := by rw [BitVec.add_assoc]; rfl
  rw [h2, h3, h4, h5, h6, h7]

end Arm64
end

section
/-! # Regions, existentials and pure facts

`memRegion a n` (a stack frame) is a byte slice of length `n` with unknown contents; pure
assertions and separating existentials move in and out of `⊨`. -/

set_option autoImplicit false

namespace Arm64

theorem sepConj_mono {P P' Q Q' : SepProp} (h1 : P ⊢ P') (h2 : Q ⊢ Q') : (P ∗ Q) ⊢ (P' ∗ Q') := by
  intro h hh
  obtain ⟨h₁, h₂, hd, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  exact SepProp.holds_sepConj_iff.mpr ⟨h₁, h₂, hd, rfl, h1 _ hp, h2 _ hq⟩

theorem sat_sep_mono {m : Memory} {P P' Q : SepProp} (hs : m ⊨ P ∗ Q) (h1 : P ⊢ P') :
    m ⊨ P' ∗ Q :=
  Satisfies.mono (sepConj_mono h1 (Entails.refl Q)) hs

theorem pure_sepConj_holds {φ : Prop} {P : SepProp} {h : Heap} :
    (⌜φ⌝ ∗ P).holds h ↔ φ ∧ P.holds h := by
  constructor
  · intro hh
    obtain ⟨h₁, h₂, _, rfl, ⟨rfl, hφ⟩, hp⟩ := SepProp.holds_sepConj_iff.mp hh
    exact ⟨hφ, by rw [Heap.union_empty_left]; exact hp⟩
  · rintro ⟨hφ, hp⟩
    exact SepProp.holds_sepConj_iff.mpr ⟨Heap.empty, h, Heap.disjoint_empty_left h,
      (Heap.union_empty_left h).symm, ⟨rfl, hφ⟩, hp⟩

theorem sat_pure_sep {m : Memory} {φ : Prop} {P : SepProp} : (m ⊨ ⌜φ⌝ ∗ P) ↔ φ ∧ (m ⊨ P) := by
  constructor
  · intro hs
    obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
    have := pure_sepConj_holds.mp hh
    exact ⟨this.1, SepProp.satisfies_iff.mpr ⟨h, this.2, hm⟩⟩
  · rintro ⟨hφ, hs⟩
    obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
    exact SepProp.satisfies_iff.mpr ⟨h, pure_sepConj_holds.mpr ⟨hφ, hh⟩, hm⟩

theorem sepExists_sepConj {α : Sort _} (P : α → SepProp) (Q : SepProp) :
    ((∃∗ x, P x) ∗ Q) = ∃∗ x, (P x ∗ Q) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_sepExists_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, ⟨x, hp⟩, hq⟩; exact ⟨x, h₁, h₂, hd, rfl, hp, hq⟩
  · rintro ⟨x, h₁, h₂, hd, rfl, hp, hq⟩; exact ⟨h₁, h₂, hd, rfl, ⟨x, hp⟩, hq⟩

theorem sat_sepExists {m : Memory} {α : Sort _} {P : α → SepProp} :
    (m ⊨ ∃∗ x, P x) ↔ ∃ x, m ⊨ P x := by
  constructor
  · intro hs
    obtain ⟨h, ⟨x, hp⟩, hm⟩ := SepProp.satisfies_iff.mp hs
    exact ⟨x, SepProp.satisfies_iff.mpr ⟨h, hp, hm⟩⟩
  · rintro ⟨x, hs⟩
    obtain ⟨h, hp, hm⟩ := SepProp.satisfies_iff.mp hs
    exact SepProp.satisfies_iff.mpr ⟨h, ⟨x, hp⟩, hm⟩

theorem regionHeap_phys (base : BitVec 64) (len : Nat) (m : Memory) (y : BitVec 64) :
    (regionHeap base len m).phys y =
      if (y - base).toNat < len then some (.rw (m.read8 y)) else none := by
  unfold regionHeap InRegion; exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

/-! ## Byte-slice heaps carry no ghost state and nothing outside the slice -/

theorem bytes_shape : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h →
      h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false) ∧
      ∀ y, bs.length ≤ (y - a).toNat → h.phys y = none
  | a, [], h, hh => by
    rw [pointsToBytes_nil, SepProp.holds_emp_iff] at hh; subst hh
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  | a, b :: bs, h, hh => by
    obtain ⟨h1, h2, _, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    obtain ⟨ha, hf, hm, hp⟩ := bytes_shape h2h
    refine ⟨?_, ?_, ?_, fun y hy => ?_⟩
    · funext γ k; simp [Heap.union, Heap.singleton, ha]
    · funext γ k; simp [Heap.union, Heap.singleton, hf]
    · funext y; simp [Heap.union, Heap.singleton, hm]
    · have hya : y ≠ a := by
        intro he; subst he; simp at hy
      have : bs.length ≤ (y - (a + 1#64)).toNat := by
        simp only [List.length_cons] at hy; bv_omega
      simp [Heap.union, Heap.singleton, hya, hp y this]

theorem bytes_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) ⊢ memRegion a bs.length := by
  intro h hh
  obtain ⟨ha, hf, hm, hp⟩ := bytes_shape hh
  refine ⟨Memory.ofFn (fun y => bs.getD (y - a).toNat 0), ?_⟩
  show h = regionHeap a bs.length _
  apply Heap.ext
  · funext y
    rw [regionHeap_phys]
    split
    · rename_i hy
      have := bytes_phys hh (y - a).toNat hy
      rw [show a + BitVec.ofNat 64 (y - a).toNat = y by bv_omega] at this
      rw [this]
      simp only [Memory.read8, Memory.ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy,
        Option.getD_some]
    · rename_i hy; exact hp y (by omega)
  · exact ha
  · exact hf
  · exact hm

theorem regionHeap_holds_bytes : ∀ (n : Nat) (a : BitVec 64) (m : Memory), n < 2 ^ 64 →
    (a ↦ₛ m.readBytes a n).holds (regionHeap a n m)
  | 0, a, m, _ => by
    show _ = _
    apply Heap.ext
    · funext y; simp [regionHeap, InRegion, Heap.empty]
    · rfl
    · rfl
    · rfl
  | n + 1, a, m, hn => by
    have ih := regionHeap_holds_bytes n (a + 1#64) m (by omega)
    refine SepProp.holds_sepConj_iff.mpr ⟨Heap.singleton a (m.read8 a), regionHeap (a + 1#64) n m,
      ?_, ?_, rfl, ih⟩
    · exact Heap.Disjoint.of_phys_left rfl rfl (fun y => by
        by_cases hy : y = a
        · subst hy; right; left
          rw [regionHeap_phys, if_neg]; bv_omega
        · left; simp [Heap.singleton, hy]) rfl
    · apply Heap.ext
      · funext y
        by_cases hy : y = a
        · subst hy
          simp only [Heap.union, Heap.singleton, if_true, regionHeap_phys]
          rw [if_pos (by bv_omega)]
        · simp only [Heap.union, Heap.singleton, hy, if_false, regionHeap_phys]
          have e : ((y - a).toNat < n + 1) ↔ ((y - (a + 1#64)).toNat < n) := by
            constructor <;> intro h <;> bv_omega
          by_cases hc : (y - (a + 1#64)).toNat < n
          · rw [if_pos (e.mpr hc), if_pos hc]
          · rw [if_neg (fun h => hc (e.mp h)), if_neg hc]
      · rfl
      · rfl
      · rfl

theorem readBytes_length (m : Memory) : ∀ (a : BitVec 64) (n : Nat), (m.readBytes a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by simp [Memory.readBytes, readBytes_length m (a + 1#64) n]

theorem memRegion_entails_bytes (a : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    memRegion a n ⊢ ∃∗ bs, ⌜bs.length = n⌝ ∗ (a ↦ₛ bs) := by
  intro h hh
  obtain ⟨m, hm⟩ := hh
  change h = regionHeap a n m at hm
  subst hm
  exact ⟨m.readBytes a n, pure_sepConj_holds.mpr ⟨readBytes_length m a n,
    regionHeap_holds_bytes n a m hn⟩⟩

end Arm64
end

section
/-! # 64-bit cells and byte reads: values and permissions from ownership -/

set_option autoImplicit false

namespace Arm64

theorem dand {P : Prop} [Decidable P] (h : P) (a : Bool) : (decide P && a) = a := by simp [h]

theorem concat8_extract (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> simp <;> first | (intro; omega) | (rw [dand] <;> first | omega | (congr 1; omega))

theorem canRead_of {m : Memory} : ∀ {x : BitVec 64} {n : Nat},
    (∀ i < n, (m.perm (x + BitVec.ofNat 64 i)).r = true ∧
      m.isLazyFree (x + BitVec.ofNat 64 i) = false) → m.canRead x n = true
  | _, 0, _ => rfl
  | x, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    have ih := canRead_of (x := x + 1#64) (n := n) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    simp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree] at ih ⊢
    simp only [Bool.and_eq_true] at ih
    simp [h0.1, h0.2, ih.1, ih.2]

theorem canWrite_of {m : Memory} : ∀ {x : BitVec 64} {n : Nat},
    (∀ i < n, m.perm (x + BitVec.ofNat 64 i) = some Perm.rw) → m.canWrite x n = true
  | _, 0, _ => rfl
  | x, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    have ih := canWrite_of (x := x + 1#64) (n := n) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    simp only [Memory.canWrite, Memory.allPerm] at ih ⊢
    simp [h0, ih, Perm.rw]

/-- Byte `i` of `unpack64 v`. -/
theorem unpack64_getElem (v : BitVec 64) (i : Nat) (hi : i < 8) :
    (unpack64 v)[i]'(by simp; omega) = v.extractLsb' (8 * i) 8 := by
  interval_cases i <;> rfl

theorem sat64_byte {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (i : Nat) (hi : i < 8) :
    m.read8 (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 ∧
      m.perm (a + BitVec.ofNat 64 i) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 i) = false := by
  rw [pointsTo64_eq_bytes] at hs
  have := sat_bytes_read hs i (by simp; omega)
  rwa [unpack64_getElem v i hi] at this

theorem sat64_read {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F) :
    m.read64 a = v ∧ m.canRead a 8 = true ∧ m.canWrite a 8 = true := by
  refine ⟨?_, canRead_of (fun i hi => ?_), canWrite_of (fun i hi => (sat64_byte hs i hi).2.1)⟩
  · have h0 := (sat64_byte hs 0 (by omega)).1
    have h1 := (sat64_byte hs 1 (by omega)).1
    have h2 := (sat64_byte hs 2 (by omega)).1
    have h3 := (sat64_byte hs 3 (by omega)).1
    have h4 := (sat64_byte hs 4 (by omega)).1
    have h5 := (sat64_byte hs 5 (by omega)).1
    have h6 := (sat64_byte hs 6 (by omega)).1
    have h7 := (sat64_byte hs 7 (by omega)).1
    simp only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
    simp only [Memory.read64]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    exact concat8_extract v
  · have := sat64_byte hs i hi
    rw [this.2.1]; exact ⟨rfl, this.2.2⟩

theorem sat64_write {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (w : BitVec 64) : m.write64 a w ⊨ (a ↦₆₄ w) ∗ F := by
  rw [pointsTo64_eq_bytes] at hs ⊢
  have e : ∀ i : Nat, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 i := fun _ => rfl
  have s0 := sat_bytes_write hs 0 (by simp) (w.extractLsb' 0 8)
  have s1 := sat_bytes_write s0 1 (by simp) (w.extractLsb' 8 8)
  have s2 := sat_bytes_write s1 2 (by simp) (w.extractLsb' 16 8)
  have s3 := sat_bytes_write s2 3 (by simp) (w.extractLsb' 24 8)
  have s4 := sat_bytes_write s3 4 (by simp) (w.extractLsb' 32 8)
  have s5 := sat_bytes_write s4 5 (by simp) (w.extractLsb' 40 8)
  have s6 := sat_bytes_write s5 6 (by simp) (w.extractLsb' 48 8)
  have s7 := sat_bytes_write s6 7 (by simp) (w.extractLsb' 56 8)
  clear e
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at s7
  simp only [Memory.write64, BitVec.add_zero]
  convert s7 using 3
  simp [unpack64]

end Arm64
end

section
/-! # Instruction fetch in the placed x25519 library, and execution by backward chaining

`Step` does not depend on which block's program runs it when no hooks are installed, so a callee's
contract (stated for its own block) is usable from the caller's block. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

/-- Block `i` of the library. -/
abbrev blk (i : Nat) : CodeBlock := x25519CliMultiLib.blocks.getD i { code := [] }

/-- Block `i`'s placed program, as in `fnOk`. -/
abbrev bprog (mpl : MultiPlacement) (i : Nat) : Program := x25519CliMultiLib.blockProgram mpl i

theorem hook_none (mpl : MultiPlacement) (i : Nat) (pc : BitVec 64) : (bprog mpl i).externAt? pc = none := by
  simp only [bprog, Program.externAt?, Program.hookAtOff?, MultiPlacedLib.blockProgram, PlacedLib.program]
  simp

theorem step_transfer {p q : Program} (hp : ∀ pc, p.externAt? pc = none)
    (hq : ∀ pc, q.externAt? pc = none) (hs : p.svc = q.svc) {s s' : State}
    (h : Step p s s') : Step q s s' := by
  have hf : ∀ m pc, p.fetchMem m pc = q.fetchMem m pc := by
    intro m pc; simp only [Program.fetchMem, hp, hq]
  cases h with
  | exec hrun hfe =>
    have := Step.exec (prog := q) hrun (by rw [← hf]; exact hfe)
    simpa only [Program.evalInst, hs] using this
  | halt_unmapped hrun hfe _ =>
    exact Step.halt_unmapped hrun (by rw [← hf]; exact hfe) (hq _)
  | externHook _ he _ _ => rw [hp] at he; cases he
  | extern_fault _ he _ => rw [hp] at he; cases he

theorem steps_transfer {p q : Program} (hp : ∀ pc, p.externAt? pc = none)
    (hq : ∀ pc, q.externAt? pc = none) (hs : p.svc = q.svc) {s s' : State}
    (h : Steps p s s') : Steps q s s' := by
  induction h with
  | refl => exact Steps.refl _
  | step h1 _ ih => exact Steps.step (step_transfer hp hq hs h1) ih

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

theorem bsteps_transfer {mpl : MultiPlacement} {i j : Nat} {s s' : State}
    (h : Steps (bprog mpl i) s s') : Steps (bprog mpl j) s s' :=
  steps_transfer (hook_none mpl i) (hook_none mpl j) rfl h

/-! ## Reaching a final state -/

def Reach (p : Program) (s : State) (Q : State → Prop) : Prop := ∃ sf, Steps p s sf ∧ Q sf

theorem Reach.done {p : Program} {s : State} {Q : State → Prop} (h : Q s) : Reach p s Q :=
  ⟨s, Steps.refl s, h⟩

theorem Reach.exec {p : Program} {s : State} {Q : State → Prop} {i : Instr}
    (hrun : s.status = .Running) (hf : p.fetchMem s.mem s.pc = some i)
    (h : Reach p (execInstWithSvc (evalSvc p.svc) i s) Q) : Reach p s Q := by
  obtain ⟨sf, hst, hq⟩ := h
  exact ⟨sf, Steps.step (Step.exec hrun hf) hst, hq⟩

theorem Reach.steps {p : Program} {s s' : State} {Q : State → Prop} (h1 : Steps p s s')
    (h : Reach p s' Q) : Reach p s Q := by
  obtain ⟨sf, hst, hq⟩ := h
  exact ⟨sf, Steps.trans' h1 hst, hq⟩

/-! ## Fetching from the loaded code -/

theorem length_bytesOfWordLE (w : BitVec 32) : (bytesOfWordLE w).length = 4 := by
  simp [bytesOfWordLE, bytesLE]

theorem drop_take_flatMap_bytesOfWordLE {α : Type} (g : α → BitVec 32) :
    ∀ (L : List α) (j : Nat) (hj : j < L.length),
      ((L.flatMap fun a => bytesOfWordLE (g a)).drop (4 * j)).take 4 =
        bytesOfWordLE (g (L[j]'hj))
  | [], _, hj => by simp at hj
  | a :: L, 0, _ => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_append_of_le_length (by simp [length_bytesOfWordLE])]
    exact List.take_of_length_le (by simp [length_bytesOfWordLE])
  | a :: L, j + 1, hj => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 4 * (j + 1) = (bytesOfWordLE (g a)).length + 4 * j by
          simp [length_bytesOfWordLE]; omega,
      ← List.drop_drop, List.drop_left]
    exact drop_take_flatMap_bytesOfWordLE g L j (by simp at hj; omega)

theorem take4_drop_patched {b : CodeBlock} {pl : Placement} {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ b.code.length) :
    ((b.patched pl).drop off).take 4 = bytesOfWordLE (b.patchedWord pl off) := by
  have hj : off / 4 < (List.range (b.code.length / 4)).length := by
    simp only [List.length_range]; omega
  have h := drop_take_flatMap_bytesOfWordLE (fun j => b.patchedWord pl (4 * j))
    (List.range (b.code.length / 4)) (off / 4) hj
  rw [List.getElem_range, show 4 * (off / 4) = off by omega] at h
  exact h

theorem sum_replicate' (n k : Nat) : (List.replicate n k).sum = n * k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem patched_length (b : CodeBlock) (pl : Placement) (h4 : b.code.length % 4 = 0) :
    (b.patched pl).length = b.code.length := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE, List.map_const', List.length_range, sum_replicate']
  omega

theorem codeLoaded_cell {p : Program} {m : Memory} (h : p.CodeLoaded m) (i : Nat)
    (hi : i < p.code.length) :
    m.read8 (p.base + BitVec.ofNat 64 i) = p.code[i] ∧
    m.perm (p.base + BitVec.ofNat 64 i) = some Perm.rx := by
  unfold Program.CodeLoaded at h
  exact ⟨(h.2.2 i hi).1, (h.2.2 i hi).2.1⟩

theorem blocks_length : x25519CliMultiLib.blocks.length = 19 := rfl

theorem blk_placeable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {i : Nat}
    (hi : i < 19) : (blk i).Placeable (x25519CliMultiLib.blockPlacement mpl i) := by
  have := hP.blocks_ok i (by rw [blocks_length]; exact hi)
  simpa [blk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [blocks_length]; exact hi)]
    using this

theorem read8_code {mpl : MultiPlacement} {m : Memory} {i : Nat}
    (hCL : (bprog mpl i).CodeLoaded m) (h4 : (blk i).code.length % 4 = 0) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ (blk i).code.length) (hk : k < 4) :
    m.read8 (mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      ((blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off).extractLsb' (8 * k) 8 ∧
    m.perm (mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (bprog mpl i).code.length = (blk i).code.length := patched_length _ _ h4
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (bprog mpl i).base + BitVec.ofNat 64 (off + k) := by
    show _ = mpl.base i + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (b := blk i) (pl := x25519CliMultiLib.blockPlacement mpl i) hal hlen
  have hlp : ((blk i).patched (x25519CliMultiLib.blockPlacement mpl i)).length = (blk i).code.length :=
    patched_length _ _ h4
  have e1 : (bprog mpl i).code[off + k]'(by omega) =
      ((((blk i).patched (x25519CliMultiLib.blockPlacement mpl i)).drop off).take 4)[k]'(by
        simp only [List.length_take, List.length_drop, hlp]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + j < 32 := by omega
  simp [hj, this]; omega

theorem concat_bytes32 (w : BitVec 32) :
    (w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8) = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> simp <;> first | (intro; omega) | (rw [dand] <;> first | omega | (congr 1; omega))

/-- The instruction fetched at offset `off` of block `i`, by any hook-free program. -/
theorem fetch_word {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m : Memory}
    {i : Nat} (hi : i < 19) (hCL : (bprog mpl i).CodeLoaded m) {off : Nat} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ (blk i).code.length) (p : Program) (hp : ∀ pc, p.externAt? pc = none) :
    p.fetchMem m (mpl.base i + BitVec.ofNat 64 off) =
      decode ((blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off) := by
  have hPl := blk_placeable hP hi
  have h4 : (blk i).code.length % 4 = 0 := hPl.len_aligned
  have hb4 : (mpl.base i).toNat % 4 = 0 := by
    have h1 := hPl.base_aligned; have h2 := hPl.align_pos
    simp only [MultiPlacedLib.blockPlacement] at h1
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h2.2) (Nat.dvd_of_mod_eq_zero h1))
  have hnw : (mpl.base i).toNat + (blk i).code.length ≤ 2 ^ 64 := hPl.no_wrap
  have hpc : (mpl.base i + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : ((mpl.base i).toNat + off) % 2 ^ 64 = (mpl.base i).toNat + off :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have r0 := read8_code hCL h4 hal hlen (k := 0) (by omega)
  have r1 := read8_code hCL h4 hal hlen (k := 1) (by omega)
  have r2 := read8_code hCL h4 hal hlen (k := 2) (by omega)
  have r3 := read8_code hCL h4 hal hlen (k := 3) (by omega)
  simp only [Program.fetchMem, hp, Option.isSome_none, Bool.false_eq_true, if_false, hpc,
    ne_eq, not_true_eq_false]
  generalize mpl.base i + BitVec.ofNat 64 off = a at *
  generalize (blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off = w at *
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at r0 r1 r2 r3
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at r0
  have hx : m.canExec a 4 = true := by
    simp only [Memory.canExec, Memory.allPerm, BitVec.add_assoc, BitVec.reduceAdd]
    simp [r0.2, r1.2, r2.2, r3.2, Perm.rx]
  simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
  congr 1
  simp only [Memory.read32, BitVec.add_zero]
  rw [r0.1, r1.1, r2.1, r3.1]
  exact concat_bytes32 w

theorem patchedWord_plain (b : CodeBlock) (pl : Placement) {off : Nat} (h : b.relocAt? off = none) :
    b.patchedWord pl off = b.wordAt off := by
  simp [CodeBlock.patchedWord, h]

end X25519Dalek.EMulP
end

section
/-! # Abstract machine states

Every state inside a block proof is `mkS s0 pc r sp ps m v`: the state `s0` with the program
counter, the general registers, the stack pointer, the flags, the memory and the vector registers
replaced. The instruction evaluators map such states to such states, and these lemmas let `simp`
compute the result without unfolding `State`. -/

set_option autoImplicit false

namespace X25519Dalek.EMulP

open Arm64

def upd {α : Type} (r : BitVec 5 → α) (i : BitVec 5) (v : α) : BitVec 5 → α :=
  fun j => if j = i then v else r j

@[simp] theorem upd_same {α : Type} (r : BitVec 5 → α) (i : BitVec 5) (v : α) : upd r i v i = v := by
  simp [upd]

/-- `upd` at literal indices: `simp` decides the index comparison. -/
@[simp] theorem upd_apply {α : Type} (r : BitVec 5 → α) (i j : BitVec 5) (v : α) :
    upd r i v j = if j = i then v else r j := rfl

def mkS (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64) (ps : PState)
    (m : Memory) (v : BitVec 5 → BitVec 128) : State :=
  { s0 with pc := pc, regs := ⟨r⟩, sp := sp, pstate := ps, mem := m, vregs := ⟨v⟩ }

section
variable (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64) (ps : PState)
  (m : Memory) (v : BitVec 5 → BitVec 128)

@[simp] theorem mkS_pc : (mkS s0 pc r sp ps m v).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 pc r sp ps m v).sp = sp := rfl
@[simp] theorem mkS_mem : (mkS s0 pc r sp ps m v).mem = m := rfl
@[simp] theorem mkS_pstate : (mkS s0 pc r sp ps m v).pstate = ps := rfl
@[simp] theorem mkS_status : (mkS s0 pc r sp ps m v).status = s0.status := rfl
@[simp] theorem mkS_spAligned : (mkS s0 pc r sp ps m v).spAligned = ((sp &&& 0b1111#64) == 0#64) := rfl

@[simp] theorem mkS_readGpr (i : BitVec 5) :
    (mkS s0 pc r sp ps m v).readReg64 (.gpr i) = if i = 31#5 then 0#64 else r i := by
  simp [mkS, State.readReg64, RegFile.read]
@[simp] theorem mkS_readSp : (mkS s0 pc r sp ps m v).readReg64 .sp = sp := rfl
@[simp] theorem mkS_readXzr : (mkS s0 pc r sp ps m v).readReg64 .xzr = 0#64 := rfl

@[simp] theorem mkS_writeGpr (i : BitVec 5) (x : BitVec 64) :
    (mkS s0 pc r sp ps m v).writeReg64 (.gpr i) x =
      mkS s0 pc (if i = 31#5 then r else upd r i x) sp ps m v := by
  by_cases h : i = 31#5
  · simp [mkS, State.writeReg64, h]
  · simp [mkS, State.writeReg64, h, RegFile.write]; rfl
@[simp] theorem mkS_writeSp (x : BitVec 64) :
    (mkS s0 pc r sp ps m v).writeReg64 .sp x = mkS s0 pc r x ps m v := rfl
@[simp] theorem mkS_writeXzr (x : BitVec 64) :
    (mkS s0 pc r sp ps m v).writeReg64 .xzr x = mkS s0 pc r sp ps m v := rfl

@[simp] theorem mkS_advancePC : (mkS s0 pc r sp ps m v).advancePC = mkS s0 (pc + 4#64) r sp ps m v := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 pc r sp ps m v).setPC q = mkS s0 q r sp ps m v := rfl
@[simp] theorem mkS_setPState (q : PState) :
    (mkS s0 pc r sp ps m v).setPState q = mkS s0 pc r sp q m v := rfl
@[simp] theorem mkS_setMem (q : Memory) : (mkS s0 pc r sp ps m v).setMem q = mkS s0 pc r sp ps q v := rfl

@[simp] theorem mkS_readV (i : BitVec 5) : (mkS s0 pc r sp ps m v).readVReg128 i = v i := rfl
@[simp] theorem mkS_writeV (i : BitVec 5) (x : BitVec 128) :
    (mkS s0 pc r sp ps m v).writeVReg128 i x = mkS s0 pc r sp ps m (upd v i x) := by
  simp only [mkS, State.writeVReg128, VRegFile.write]; rfl

end

end X25519Dalek.EMulP
end

section
/-! # Code stays loaded; stepping on abstract states; small stack frames -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

theorem codeLoaded_keepsFrozen {p : Program} {m m' : Memory} (h : p.CodeLoaded m)
    (hk : m.KeepsFrozen m') : p.CodeLoaded m' := by
  unfold Program.CodeLoaded at h ⊢
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2.2 i hi
  have hf : m.Frozen (p.base + BitVec.ofNat 64 i) := by
    simp [Memory.Frozen, h2, Perm.rx, Perm.frozen, Perm.rwx]
  obtain ⟨k1, k2, k3, _⟩ := hk _ hf
  exact ⟨k1.trans h1, k2.trans h2, k3.trans h3⟩

theorem libCodeLoaded_keepsFrozen {mpl : MultiPlacement} {m m' : Memory}
    (h : x25519CliMultiLib.CodeLoaded mpl m) (hk : m.KeepsFrozen m') :
    x25519CliMultiLib.CodeLoaded mpl m' :=
  fun i hi => codeLoaded_keepsFrozen (h i hi) hk

/-- Fetch at offset `off` of block `i` from any memory that kept the frozen bytes of `m0`. -/
theorem fetch_at {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {i : Nat} (hi : i < 19) (j : Nat) {off : Nat}
    {inst : Instr}
    (h : (off % 4 = 0 ∧ off + 4 ≤ (blk i).code.length) ∧ (blk i).relocAt? off = none ∧
      decode ((blk i).wordAt off) = some inst)
    {m : Memory} (hk : m0.KeepsFrozen m) :
    (bprog mpl j).fetchMem m (mpl.base i + BitVec.ofNat 64 off) = some inst := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk i (by rw [blocks_length]; exact hi)
  rw [fetch_word hP hi hCL' h.1.1 h.1.2 _ (hook_none mpl j), patchedWord_plain _ _ h.2.1]
  exact h.2.2

theorem pc_add (b : BitVec 64) (k j : Nat) :
    b + BitVec.ofNat 64 k + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (k + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Byte lists of length 8 are words -/

end X25519Dalek.EMulP
end

section
/-! # Decoding a relocated cross-block `BL`

Adapted from the sibling batch q445-xd-edwards (`Solutions/X25519DalekEdwards/Reloc.lean`), which
follows the zlib CRC-32 mission's proofs (`ZlibCrc32.Small.RelocBase`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_b_class (w : BitVec 32) (hK : w &&& 0x7c000000#32 = 0x14000000#32) :
    decode w = some (if w.getLsbD 31 then .bl (((w.extractLsb' 0 26).signExtend 64) <<< 2)
      else .b (((w.extractLsb' 0 26).signExtend 64) <<< 2)) := by
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide),
    beq_false_of_mask hK (C := 0x10000000#32) (M := 0x1f000000#32) (by decide),
    beq_false_of_mask hK (C := 0x11000000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x12000000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x12800000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x13000000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x13800000#32) (M := 0x7f800000#32) (by decide), hK]
  cases h : w.getLsbD 31 <;> simp [h]

theorem hi_bits27 (D : BitVec 64) (h1 : -(2^27:Int) ≤ D.toInt) (h2 : D.toInt < 2^27) :
    ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  by_cases hs : 2 * D.toNat < 2 ^ 64
  · rw [if_pos hs] at h2
    have hD : D.toNat < 2 ^ 27 := by omega
    have g : ∀ j, 27 ≤ j → D.getLsbD j = false := fun j hj =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hD (Nat.pow_le_pow_right (by norm_num) hj))
    rw [g i hi1, g 27 le_rfl]
  · rw [if_neg hs] at h1
    have hE : (~~~D).toNat < 2 ^ 27 := by rw [BitVec.toNat_not]; omega
    have g : ∀ j, 27 ≤ j → j < 64 → D.getLsbD j = true := by
      intro j hj1 hj2
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by norm_num) hj1))
      have e : (~~~D).getLsbD j = false := this
      rw [BitVec.getLsbD_not] at e
      simpa [hj2] using e
    rw [g i hi1 hi2, g 27 le_rfl (by norm_num)]


theorem lo_bits2 (D : BitVec 64) (h : D.toNat % 4 = 0) : ∀ i, i < 2 → D.getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize D.toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

theorem cbits (j : Nat) (hj : j < 26) : (0x94000000#32 : BitVec 32).getLsbD j = false ∧
    (0x03ffffff#32 : BitVec 32).getLsbD j = true := by
  interval_cases j <;> decide

theorem bl_offset_bits (D : BitVec 64) (hlo : ∀ i, i < 2 → D.getLsbD i = false)
    (hhi : ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27) :
    ((((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32)).extractLsb' 0 26).signExtend 64)
      <<< 2 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.msb_eq_getLsbD_last]
  rcases (show i < 2 ∨ (2 ≤ i ∧ i < 28) ∨ 28 ≤ i by omega) with h | ⟨h1, h2⟩ | h
  · simp [h, hlo i h]
  · have c := cbits (i - 2) (by omega)
    simp [hi, show ¬ i < 2 by omega, show i - 2 < 26 by omega, show i - 2 < 32 by omega]
    simp only [← BitVec.getLsbD_eq_getElem, c.1, c.2, Bool.false_and, Bool.false_or, Bool.and_true]
    simp [show i - 2 < 64 by omega]; congr 1; omega
  · have c := cbits 25 (by omega)
    simp [hi, show ¬ i < 2 by omega, show ¬ i - 2 < 26 by omega, c.1, c.2]
    simp only [← BitVec.getLsbD_eq_getElem]
    rw [hhi i (by omega) hi]
    simp [show i - 2 < 64 by omega]

/-- A relocated `BL` (template `0x94000000`) calls its target. -/
theorem decode_branchWord_bl {P T : BitVec 64} (hr : BranchInRange P T) :
    decode (branchWord 0x94000000#32 P T) = some (.bl (T - P)) := by
  have hm : ((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32))
      &&& 0x7c000000#32 = 0x14000000#32 := by
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc ((T - P) >>> 2 |>.setWidth 32)]
    simp
  have h31 : ((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).getLsbD 31
      = true := by simp
  have hoff : ((((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).extractLsb' 0 26).signExtend 64)
      <<< 2 = T - P := by
    exact bl_offset_bits _ (lo_bits2 _ hr.1) (hi_bits27 _ hr.2.1 hr.2.2)
  rw [branchWord, decode_b_class _ hm, h31, if_pos rfl, hoff]

/-- The `BL callee` at offset `off` of block `i` (a `call26` relocation to the first symbol of
block `j`, which is not a symbol of block `i`): fetched as `bl (base j - (base i + off))`. -/
theorem fetch_bl {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 m : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (hk : m0.KeepsFrozen m) {i j k off : Nat}
    (hi : i < 19) (sym : String) (b : CodeBlock) (hb : blk i = b)
    (hal : off % 4 = 0 ∧ off + 4 ≤ b.code.length)
    (hr : b.relocAt? off = some { off := off, kind := .call26, sym := sym })
    (hmem : ({ off := off, kind := .call26, sym := sym } : RelocEntry) ∈ b.relocs)
    (hw : b.wordAt off = 0x94000000#32)
    (hlk : lookup sym b.symbols = none)
    (hlj : lookupBlockSym sym x25519CliMultiLib.blocks = some (j, 0))
    (hrel1 : b.relaxableAt off = false) (hrel2 : 4 ≤ off → b.relaxableAt (off - 4) = false)
    (hwk : b.weakRefs = []) :
    (bprog mpl k).fetchMem m (mpl.base i + BitVec.ofNat 64 off) =
      some (.bl (mpl.base j + BitVec.ofNat 64 0 - (mpl.base i + BitVec.ofNat 64 off))) := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk i (by rw [blocks_length]; exact hi)
  rw [fetch_word hP hi hCL' hal.1 (by rw [hb]; exact hal.2) _ (hook_none mpl k), hb]
  have hres : x25519CliMultiLib.resolve mpl sym = mpl.base j + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.resolve, hlj]
  have hb2b : b.b2bNext? { off := off, kind := .call26, sym := sym } = none := by
    rw [CodeBlock.b2bNext?]; simp only [hlk]; simp
  have htg : b.target (x25519CliMultiLib.blockPlacement mpl i)
      { off := off, kind := .call26, sym := sym } = mpl.base j + BitVec.ofNat 64 0 := by
    rw [CodeBlock.target, CodeBlock.resolve]; simp only [hlk]
    simp [addSignedAddr, MultiPlacedLib.blockPlacement, hres]
  have hT : b.relocTarget (x25519CliMultiLib.blockPlacement mpl i) off
      { off := off, kind := .call26, sym := sym } = mpl.base j + BitVec.ofNat 64 0 := by
    rw [CodeBlock.relocTarget, hb2b]
    split <;> simp_all
  have hpl : b.Placeable (x25519CliMultiLib.blockPlacement mpl i) := hb ▸ blk_placeable hP hi
  have hrange : BranchInRange (mpl.base i + BitVec.ofNat 64 off) (mpl.base j + BitVec.ofNat 64 0) := by
    have h := (hpl.relocs_ok _ hmem).2.2
    rw [hT] at h
    exact h
  have hpw : b.patchedWord (x25519CliMultiLib.blockPlacement mpl i) off =
      branchWord 0x94000000#32 (mpl.base i + BitVec.ofNat 64 off) (mpl.base j + BitVec.ofNat 64 0) := by
    have hbase : (x25519CliMultiLib.blockPlacement mpl i).base = mpl.base i := rfl
    have hr1 : b.relaxedAt (x25519CliMultiLib.blockPlacement mpl i) off = false := by
      simp [CodeBlock.relaxedAt, hrel1]
    have hr2 : (decide (4 ≤ off) && b.relaxedAt (x25519CliMultiLib.blockPlacement mpl i) (off - 4)) = false := by
      by_cases h4 : 4 ≤ off
      · simp [CodeBlock.relaxedAt, hrel2 h4]
      · simp [h4]
    have hu : b.undefWeakBranch (x25519CliMultiLib.blockPlacement mpl i)
        { off := off, kind := .call26, sym := sym } = false := by
      simp [CodeBlock.undefWeakBranch, hwk]
    rw [CodeBlock.patchedWord]
    simp only [hr, hr1, hr2, hw, hbase, hu, hT, Bool.false_eq_true, if_false]
    simp [RelocKind.isGotOrTlsIe, patchRelocWord]
  rw [hpw, decode_branchWord_bl hrange]

end X25519Dalek.EMulP
end

section
/-! # 128-bit loads and stores, 32-byte buffers as 64-bit cells, stack regions -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

/-! ## 32-byte buffers -/

/-! ## Stack regions -/

theorem memRegion_split (a : BitVec 64) (n k : Nat) (hnk : n + k < 2 ^ 64) :
    memRegion a (n + k) ⊢ memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k := by
  intro h hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a (n + k) hnk h hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  rw [pointsToBytes_split a bs n (by omega)] at hb
  have e1 : (bs.take n).length = n := by simp [hl]
  have e2 : (bs.drop n).length = k := by simp [hl]
  have m1 := bytes_entails_memRegion a (bs.take n)
  have m2 := bytes_entails_memRegion (a + BitVec.ofNat 64 n) (bs.drop n)
  rw [e1] at m1
  rw [e2] at m2
  exact sepConj_mono m1 m2 h hb

theorem memRegion_merge (a b : BitVec 64) (n k : Nat) (hb : b = a + BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) :
    memRegion a n ∗ memRegion b k ⊢ memRegion a (n + k) := by
  subst hb
  intro h hh
  have h2 := sepConj_mono (memRegion_entails_bytes a n hn)
    (memRegion_entails_bytes (a + BitVec.ofNat 64 n) k hk) h hh
  rw [sepExists_sepConj] at h2
  obtain ⟨bs1, h2⟩ := h2
  dsimp only at h2
  rw [sepConj_comm, sepExists_sepConj] at h2
  obtain ⟨bs2, h2⟩ := h2
  dsimp only at h2
  have h3 : (⌜bs1.length = n⌝ ∗ ⌜bs2.length = k⌝ ∗ (a ↦ₛ bs1) ∗
      ((a + BitVec.ofNat 64 n) ↦ₛ bs2)).holds h := by
    have := Entails.of_eq (P := (⌜bs2.length = k⌝ ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs2)) ∗
      (⌜bs1.length = n⌝ ∗ (a ↦ₛ bs1)))
      (Q := ⌜bs1.length = n⌝ ∗ ⌜bs2.length = k⌝ ∗ (a ↦ₛ bs1) ∗
      ((a + BitVec.ofNat 64 n) ↦ₛ bs2))
    exact this h h2
  obtain ⟨hl1, h3⟩ := pure_sepConj_holds.mp h3
  obtain ⟨hl2, h3⟩ := pure_sepConj_holds.mp h3
  have := bytes_entails_memRegion a (bs1 ++ bs2)
  rw [pointsToBytes_append, hl1, List.length_append, hl1, hl2] at this
  exact this h h3

theorem cell_memRegion8 (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [pointsTo64_eq_bytes]
  exact unpack64_length v ▸ bytes_entails_memRegion a (unpack64 v)

/-! ## Runs of 64-bit cells -/

/-- Owned 64-bit cells holding `l` at `a`, `a + 8`, … -/
def cellsFrom : BitVec 64 → List (BitVec 64) → SepProp
  | _, [] => emp
  | a, v :: l => (a ↦₆₄ v) ∗ cellsFrom (a + 8#64) l

theorem cellsFrom_nil (a : BitVec 64) : cellsFrom a [] = emp := rfl
theorem cellsFrom_cons (a v : BitVec 64) (l : List (BitVec 64)) :
    cellsFrom a (v :: l) = (a ↦₆₄ v) ∗ cellsFrom (a + 8#64) l := rfl

theorem addr_succ (a : BitVec 64) (k : Nat) :
    a + 8#64 + BitVec.ofNat 64 (8 * k) = a + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem cells_read : ∀ (l : List (BitVec 64)) (a : BitVec 64) (F : SepProp) (m : Memory),
    (m ⊨ cellsFrom a l ∗ F) → ∀ k (hk : k < l.length),
      m.read64 (a + BitVec.ofNat 64 (8 * k)) = l[k] ∧
      m.canRead (a + BitVec.ofNat 64 (8 * k)) 8 = true ∧
      m.canWrite (a + BitVec.ofNat 64 (8 * k)) 8 = true
  | [], _, _, _, _, k, hk => by simp at hk
  | v :: l, a, F, m, hs, 0, _ => by
    rw [cellsFrom_cons, sepConj_assoc] at hs
    simpa using sat64_read hs
  | v :: l, a, F, m, hs, k + 1, hk => by
    rw [cellsFrom_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := cells_read l (a + 8#64) _ m hs k (by simpa using hk)
    rw [addr_succ] at this
    simpa using this

theorem cells_write : ∀ (l : List (BitVec 64)) (a : BitVec 64) (F : SepProp) (m : Memory),
    (m ⊨ cellsFrom a l ∗ F) → ∀ k, k < l.length → ∀ w : BitVec 64,
      (m.write64 (a + BitVec.ofNat 64 (8 * k)) w ⊨ cellsFrom a (l.set k w) ∗ F)
  | [], _, _, _, _, k, hk, _ => by simp at hk
  | v :: l, a, F, m, hs, 0, _, w => by
    rw [cellsFrom_cons, sepConj_assoc] at hs
    rw [List.set_cons_zero, cellsFrom_cons, sepConj_assoc]
    simpa using sat64_write hs w
  | v :: l, a, F, m, hs, k + 1, hk, w => by
    rw [cellsFrom_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := cells_write l (a + 8#64) _ m hs k (by simpa using hk) w
    rw [List.set_cons_succ, cellsFrom_cons, sepConj_assoc, sepConj_left_comm]
    rw [addr_succ] at this
    exact this

theorem allPerm_add (m : Memory) (p : Option Perm → Bool) :
    ∀ (n k : Nat) (x : BitVec 64),
      m.allPerm p x (n + k) = (m.allPerm p x n && m.allPerm p (x + BitVec.ofNat 64 n) k)
  | 0, k, x => by simp [Memory.allPerm]
  | n + 1, k, x => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [Memory.allPerm]
    rw [allPerm_add m p n k (x + 1#64), Bool.and_assoc]
    congr 3
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem allNoLazyFree_add (m : Memory) :
    ∀ (n k : Nat) (x : BitVec 64),
      m.allNoLazyFree x (n + k) = (m.allNoLazyFree x n && m.allNoLazyFree (x + BitVec.ofNat 64 n) k)
  | 0, k, x => by simp [Memory.allNoLazyFree]
  | n + 1, k, x => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [Memory.allNoLazyFree]
    rw [allNoLazyFree_add m n k (x + 1#64), Bool.and_assoc]
    congr 3
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem canRead16 {m : Memory} {x : BitVec 64} (h1 : m.canRead x 8 = true)
    (h2 : m.canRead (x + 8#64) 8 = true) : m.canRead x 16 = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at h1 h2 ⊢
  rw [show (16 : Nat) = 8 + 8 from rfl, allPerm_add, allNoLazyFree_add]
  simp [h1.1, h1.2, h2.1, h2.2]

theorem canWrite16 {m : Memory} {x : BitVec 64} (h1 : m.canWrite x 8 = true)
    (h2 : m.canWrite (x + 8#64) 8 = true) : m.canWrite x 16 = true := by
  simp only [Memory.canWrite] at h1 h2 ⊢
  rw [show (16 : Nat) = 8 + 8 from rfl, allPerm_add]
  simp [h1, h2]

theorem cells_read128 {l : List (BitVec 64)} {a : BitVec 64} {F : SepProp} {m : Memory}
    (hs : m ⊨ cellsFrom a l ∗ F) (k : Nat) (hk : k + 1 < l.length) :
    m.read128 (a + BitVec.ofNat 64 (8 * k)) = l[k + 1] ++ l[k] ∧
      m.canRead (a + BitVec.ofNat 64 (8 * k)) 16 = true ∧
      m.canWrite (a + BitVec.ofNat 64 (8 * k)) 16 = true := by
  have r0 := cells_read l a F m hs k (by omega)
  have r1 := cells_read l a F m hs (k + 1) hk
  have e : a + BitVec.ofNat 64 (8 * k) + 8#64 = a + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨?_, canRead16 r0.2.1 (e ▸ r1.2.1), canWrite16 r0.2.2 (e ▸ r1.2.2)⟩
  simp only [Memory.read128, e, r0.1, r1.1]

theorem cells_write128 {l : List (BitVec 64)} {a : BitVec 64} {F : SepProp} {m : Memory}
    (hs : m ⊨ cellsFrom a l ∗ F) (k : Nat) (hk : k + 1 < l.length) (x : BitVec 128) :
    m.write128 (a + BitVec.ofNat 64 (8 * k)) x ⊨
      cellsFrom a ((l.set k (x.extractLsb' 0 64)).set (k + 1) (x.extractLsb' 64 64)) ∗ F := by
  have h1 := cells_write l a F m hs k (by omega) (x.extractLsb' 0 64)
  have h2 := cells_write _ a F _ h1 (k + 1) (by simp; omega) (x.extractLsb' 64 64)
  have e : a + BitVec.ofNat 64 (8 * k) + 8#64 = a + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  simp only [Memory.write128, e]
  exact h2

theorem cellsFrom_append : ∀ (a : BitVec 64) (l1 l2 : List (BitVec 64)),
    cellsFrom a (l1 ++ l2) = cellsFrom a l1 ∗ cellsFrom (a + BitVec.ofNat 64 (8 * l1.length)) l2
  | a, [], l2 => by simp [cellsFrom_nil]
  | a, v :: l1, l2 => by
    rw [List.cons_append, cellsFrom_cons, cellsFrom_append (a + 8#64) l1 l2, cellsFrom_cons,
      sepConj_assoc, List.length_cons, addr_succ]

theorem cellsFrom_entails_memRegion : ∀ (a : BitVec 64) (l : List (BitVec 64)),
    8 * l.length < 2 ^ 64 → cellsFrom a l ⊢ memRegion a (8 * l.length)
  | a, [], _ => by
    intro h hh
    exact ⟨Memory.empty, by
      rw [cellsFrom_nil] at hh
      show h = regionHeap a 0 Memory.empty
      rw [hh]; ext y <;> simp [regionHeap, InRegion, Heap.empty]⟩
  | a, v :: l, hl => by
    rw [cellsFrom_cons, List.length_cons, show 8 * (l.length + 1) = 8 + 8 * l.length by ring]
    have ih := cellsFrom_entails_memRegion (a + 8#64) l (by simp at hl; omega)
    exact Entails.trans (sepConj_mono (cell_memRegion8 a v) ih)
      (memRegion_merge a (a + 8#64) 8 (8 * l.length) rfl (by norm_num) (by simp at hl; omega))

/-! ## Frame permutations -/

end X25519Dalek.EMulP
end

section
/-! # One lemma per instruction shape on abstract states `mkS`

The instructions of the two entry blocks (17 and 18). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

theorem awc_false_fst (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

theorem awc_sub (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).1 = x - y := by
  simp only [AddWithCarry64, if_true]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hx := x.isLt; have hy := y.isLt
  omega

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_sub_sp (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .SUB .sp .sp imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r (sp - imm.zeroExtend 64) ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_sub]

theorem ex_add_sp (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD .sp .sp imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r (sp + imm.zeroExtend 64) ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst]

theorem ex_add_gpr_sp (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) .sp imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (sp + imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, hd]

theorem ex_sub_gpr_gpr (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .SUB (.gpr d) (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n - imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_sub, hd, hn]

theorem ex_mov (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr n) .LSL 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n)) sp ps m v := by
  simp [execInstWithSvc, execLogicalShift, evalLogical, State.readReg, State.writeReg, shiftVal,
    shift64, hd, hn]

theorem ex_bl (off : BitVec 64) :
    execInstWithSvc svc (.bl off) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + off) (upd r 30#5 (pc + 4#64)) sp ps m v := by
  simp [execInstWithSvc]

theorem ex_ret :
    execInstWithSvc svc (.ret (.gpr 30#5)) (mkS s0 pc r sp ps m v) = mkS s0 (r 30#5) r sp ps m v := by
  simp [execInstWithSvc]

theorem ex_stp64_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 8 = true)
    (hw2 : m.canWrite (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps ((m.write64 (sp + off) (r a)).write64 (sp + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw1, hw2, ha, hb,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldp64_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead (sp + off) 8 = true)
    (hr2 : m.canRead (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 (sp + off))) b (m.read64 (sp + off + 8#64)))
        sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr1, hr2, ha, hb,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_str64_sp (a : BitVec 5) (ha : a ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw : m.canWrite (sp + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (sp + off) (r a)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw, ha,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldr64_sp (a : BitVec 5) (ha : a ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr : m.canRead (sp + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (sp + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr, ha,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_ldpq_gpr (n t1 t2 : BitVec 5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hr1 : m.canRead (r n + off) 16 = true) (hr2 : m.canRead (r n + off + 16#64) 16 = true) :
    execInstWithSvc svc (.ldpSimd .Q128 t1 t2 (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps m
        (upd (upd v t1 (m.read128 (r n + off))) t2 (m.read128 (r n + off + 16#64))) := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr1, hr2, hn,
    Memory.readSimdSized, AddrMode.baseReg]

theorem ex_stpq_sp (t1 t2 : BitVec 5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 16 = true)
    (hw2 : m.canWrite (sp + off + 16#64) 16 = true) :
    execInstWithSvc svc (.stpSimd .Q128 t1 t2 (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps ((m.write128 (sp + off) (v t1)).write128 (sp + off + 16#64) (v t2)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw1, hw2,
    Memory.writeSimdSized, AddrMode.baseReg]

end exec

end X25519Dalek.EMulP
end

section
/-! # Small facts shared by the two entry-block proofs -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

/-! ## Small facts -/

theorem al16_iff (x : BitVec 64) : (x &&& 0b1111#64 = 0#64) ↔ x.toNat % 16 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and]
  have : (0b1111#64 : BitVec 64).toNat = 2 ^ 4 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem al16_sub (x : BitVec 64) (k : Nat) (hk : k % 16 = 0) (hk2 : k < 2 ^ 64)
    (h : x &&& 0b1111#64 = 0#64) : (x - BitVec.ofNat 64 k) &&& 0b1111#64 = 0#64 := by
  rw [al16_iff] at h ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2]
  have := x.isLt
  omega

theorem sat_false {m : Memory} {F : SepProp} (h : m ⊨ ⌜False⌝ ∗ F) : False :=
  (sat_pure_sep.mp h).1

theorem readGpr_unfold (s : State) (i : BitVec 5) :
    s.readReg64 (.gpr i) = if i = 31#5 then 0#64 else s.regs.regs i := by
  simp [State.readReg64, RegFile.read]

theorem mkS_regs' (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) :
    (mkS s0 pc r sp ps m v).regs = ⟨r⟩ := rfl

theorem reach_congr {p : Program} {s s' : State} {Q : State → Prop} (h : s' = s)
    (H : Reach p s' Q) : Reach p s Q := by subst h; exact H

theorem z12 (k : Nat) (hk : k < 2 ^ 12) :
    (BitVec.ofNat 12 k).zeroExtend 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp; omega


end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): calling `mul` through its published contract

Adapted from the sibling batch q444-xd-field (`G/P22Call.lean`, block 5). The library code stays
loaded across every step by the published `Arm64Facts.steps_codeLoaded`; `RL` is `Reach` under
the hypothesis that the library is loaded in the current memory. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

abbrev mulName : String := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul"
abbrev mulpName : String := "<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2"
abbrev dblName : String := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double"

theorem mul_lookup : lookupBlockSym mulName x25519CliMultiLib.blocks = some (1, 0) := by
  decide +kernel
theorem mulp_lookup : lookupBlockSym mulpName x25519CliMultiLib.blocks = some (9, 0) := by
  decide +kernel
theorem dbl_lookup : lookupBlockSym dblName x25519CliMultiLib.blocks = some (7, 0) := by
  decide +kernel

/-- The callee-saved registers `x19`–`x29` of `sf` are those of `r`. -/
def KeptRegs (sf : State) (r : BitVec 5 → BitVec 64) : Prop :=
  ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → sf.regs.regs k = r k

theorem kept_of_cs {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
    {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {sf : State}
    (h : CalleeSavedPreserved (mkS s0 pc r sp ps m v) sf) : KeptRegs sf r := by
  intro k hk1 hk2
  obtain ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, -⟩ := h
  simp (config := { decide := true }) only [readGpr_unfold, mkS_readGpr, mkS_regs', Reg.fp, if_false] at a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29
  have hk : k = BitVec.ofNat 5 k.toNat := by simp
  generalize hj : k.toNat = j at hk hk1 hk2
  subst hk
  interval_cases j
  all_goals first | exact a19 | exact a20 | exact a21 | exact a22 | exact a23 | exact a24 | exact a25 | exact a26 | exact a27 | exact a28 | exact a29


/-- `Reach` for block 9, given that the library is loaded in the current memory. -/
def RL (mpl : MultiPlacement) (s : State) (Q : State → Prop) : Prop :=
  x25519CliMultiLib.CodeLoaded mpl s.mem → Reach (bprog mpl 9) s Q

theorem libCL_steps {mpl : MultiPlacement} {p : Program} {s s' : State} (h : Steps p s s')
    (hL : x25519CliMultiLib.CodeLoaded mpl s.mem) : x25519CliMultiLib.CodeLoaded mpl s'.mem :=
  fun i hi => Arm64Facts.steps_codeLoaded_v2 h (hL i hi)

theorem RL.mk {mpl : MultiPlacement} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {i : Instr} (hrun : s0.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc = some i)
    (h : RL mpl (execInstWithSvc (evalSvc (bprog mpl 9).svc) i (mkS s0 pc r sp ps m v)) Q) :
    RL mpl (mkS s0 pc r sp ps m v) Q := by
  intro hL
  have hf' := hf hL
  have hst : Step (bprog mpl 9) (mkS s0 pc r sp ps m v)
      (execInstWithSvc (evalSvc (bprog mpl 9).svc) i (mkS s0 pc r sp ps m v)) := Step.exec hrun hf'
  exact Reach.exec hrun hf' (h (libCL_steps (Steps.step hst (Steps.refl _)) hL))

theorem RL.done {mpl : MultiPlacement} {s : State} {Q : State → Prop} (h : Q s) : RL mpl s Q :=
  fun _ => Reach.done h

theorem RL.congr {mpl : MultiPlacement} {s s' : State} {Q : State → Prop} (h : s' = s)
    (H : RL mpl s' Q) : RL mpl s Q := by subst h; exact H

/-- `fnAddr` from a symbol lookup, stated for an arbitrary library so that the lookup is never
evaluated during elaboration. -/
theorem fnAddr_of_lookup {lib : MultiPlacedLib} {mpl : MultiPlacement} {name : String} {i off : Nat}
    (h : lookupBlockSym name lib.blocks = some (i, off)) :
    lib.fnAddr mpl name = mpl.base i + BitVec.ofNat 64 off := by
  unfold MultiPlacedLib.fnAddr; rw [h]

/-- A call to `mul` from block 9 at offset `off`; the callee's 224-byte frame is below `sp`. -/
theorem call_mul {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hM : fnOk mulName (fun _ => fe51MulSpec)) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {out a b : BitVec 64} {A B O : List (BitVec 8)} {F : SepProp}
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 off))))
    (hal : sp &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = out) (h0 : r 0#5 = a) (h1 : r 1#5 = b)
    (hmem : m ⊨ ((a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F)
    (hA : fe51LimbsBounded A (2 ^ 54)) (hB : fe51LimbsBounded B (2 ^ 54)) (hO : O.length = 40)
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running →
      sf.pc = mpl.base 9 + BitVec.ofNat 64 (off + 4) → sf.sp = sp → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ ((a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ res) ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F) →
      fe51LimbsBounded res (2 ^ 52) →
      fe51ValOfBytes res % p25519 = fe51ValOfBytes A * fe51ValOfBytes B % p25519 →
      RL mpl sf Q) :
    RL mpl (mkS sb (mpl.base 9 + BitVec.ofNat 64 off) r sp ps m v) Q := by
  refine RL.mk hrun hf ?_
  rw [ex_bl]
  have epc : mpl.base 9 + BitVec.ofNat 64 off + (mpl.base 1 + BitVec.ofNat 64 0 -
      (mpl.base 9 + BitVec.ofNat 64 off)) = mpl.base 1 + BitVec.ofNat 64 0 := by abel
  rw [epc]
  intro hCL
  obtain ⟨i1, o1, hlk1, hsub⟩ := hM
  rw [mul_lookup] at hlk1
  obtain ⟨rfl, rfl⟩ : 1 = i1 ∧ 0 = o1 := by simpa using hlk1
  have hfa : x25519CliMultiLib.fnAddr mpl mulName = mpl.base 1 + BitVec.ofNat 64 0 :=
    fnAddr_of_lookup mul_lookup
  set s1 := mkS sb (mpl.base 1 + BitVec.ofNat 64 0) (upd r 30#5 (mpl.base 9 + BitVec.ofNat 64 off + 4#64))
    sp ps m v with hs1
  have hCL1 : x25519CliMultiLib.CodeLoaded mpl s1.mem := hCL
  have hpre : s1.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec ((fun _ => fe51MulSpec) mpl) (mpl.base 1))).pre
        (out, a, b, O, A, B) s1 ∗ F := by
    have e8 : s1.readReg64 Reg.x8 = out := by simp [hs1, Reg.x8, h8]
    have e0 : s1.readReg64 Reg.x0 = a := by simp [hs1, Reg.x0, h0]
    have e1 : s1.readReg64 Reg.x1 = b := by simp [hs1, Reg.x1, h1]
    have h10 : s1.mem ⊨ ⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧
        s1.readReg64 Reg.x1 = b ∧ O.length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧
        fe51LimbsBounded B (2 ^ 54)⌝ ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝ ∗
        (((a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ O) ∗ stackFrame s1 224) ∗ F) := by
      rw [sat_pure_sep, sat_pure_sep]
      exact ⟨⟨e8, e0, e1, hO, hA, hB⟩, hCL1, hmem⟩
    show s1.mem ⊨ ((⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧
        s1.readReg64 Reg.x1 = b ∧ O.length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧
        fe51LimbsBounded B (2 ^ 54)⌝ ∗
        (a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ O) ∗ stackFrame s1 224) ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝) ∗ F
    exact Satisfies.of_eq h10
  obtain ⟨sf, hsteps, hout⟩ := hsub mpl hP (out, a, b, O, A, B) F s1 (by simp [hs1, hfa])
    hrun hpre (by simp [hs1, hal]) (hCL1 1 (by decide))
  refine Reach.steps (bsteps_transfer hsteps) ?_
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  rotate_left
  · exact (sat_false hpan).elim
  · exact (sat_false hex).elim
  · exact (sat_false hoom).elim
  have hpc' : sf.pc = mpl.base 9 + BitVec.ofNat 64 (off + 4) := by
    rw [hpcf]; simp [hs1, upd_apply, BitVec.add_assoc, BitVec.ofNat_add]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  have hCLf : x25519CliMultiLib.CodeLoaded mpl sf.mem := libCL_steps hsteps hCL1
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, fe51MulSpec, stackFrame, hsp'] at hpost
  have hp2 := Satisfies.of_eq hpost (Q := (∃∗ res : List (BitVec 8), (out ↦ₛ res) ∗
      ⌜fe51LimbsBounded res (2 ^ 52) ∧ fe51ValOfBytes res % p25519 =
        fe51ValOfBytes A * fe51ValOfBytes B % p25519⌝) ∗
      ((a ↦ₛ A) ∗ (b ↦ₛ B) ∗ memRegion (sp - BitVec.ofNat 64 224) 224 ∗ F))
  rw [sepExists_sepConj, sat_sepExists] at hp2
  obtain ⟨res, hp2⟩ := hp2
  have hp3 := Satisfies.of_eq hp2 (Q := ⌜fe51LimbsBounded res (2 ^ 52) ∧ fe51ValOfBytes res % p25519 =
        fe51ValOfBytes A * fe51ValOfBytes B % p25519⌝ ∗
      (((a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ res) ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F))
  rw [sat_pure_sep] at hp3
  obtain ⟨⟨hb52, hval⟩, hp3⟩ := hp3
  have hcs' := hcs
  simp only [hs1] at hcs'
  refine hcont sf res hrunf hpc' hsp' ?_ ?_ hp3 hb52 hval hCLf
  · intro k hk1 hk2
    have := kept_of_cs hcs' k hk1 hk2
    rw [this, upd_apply, if_neg]
    intro e; subst e; simp at hk2
  · have := hcs'.2.2.2.2.2.2.2.2.2.2.2
    rw [this]; rfl

/-- The postcondition facts of `ProjectivePoint::double`. -/
def DblPost (self_bs res : List (BitVec 8)) : Prop :=
  res.length = 160 ∧
    edExtOfBytes res = edProjDouble (fe51ValAt self_bs 0) (fe51ValAt self_bs 40) (fe51ValAt self_bs 80) ∧
      fe51LimbsBoundedAt res 0 (2 ^ 52) ∧
        fe51LimbsBoundedAt res 40 (2 ^ 53) ∧
          fe51LimbsBoundedAt res 80 (2 ^ 52) ∧ fe51LimbsBoundedAt res 120 (2 ^ 52)

/-- A call to `ProjectivePoint::double` from block 9 at offset `off`; the callee's 400-byte frame
is below `sp`. -/
theorem call_dbl {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hD : fnOk dblName (fun _ => projectivePointDoubleSpec)) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {out a : BitVec 64} {A O : List (BitVec 8)} {F : SepProp}
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 7 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 off))))
    (hal : sp &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = out) (h0 : r 0#5 = a)
    (hmem : m ⊨ ((a ↦ₛ A) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 400) 400) ∗ F)
    (hA : A.length = 120 ∧ fe51LimbsBoundedAt A 0 (2 ^ 53) ∧ fe51LimbsBoundedAt A 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt A 80 (2 ^ 54)) (hO : O.length = 160)
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running →
      sf.pc = mpl.base 9 + BitVec.ofNat 64 (off + 4) → sf.sp = sp → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ ((a ↦ₛ A) ∗ (out ↦ₛ res) ∗ memRegion (sp - BitVec.ofNat 64 400) 400) ∗ F) →
      DblPost A res → RL mpl sf Q) :
    RL mpl (mkS sb (mpl.base 9 + BitVec.ofNat 64 off) r sp ps m v) Q := by
  refine RL.mk hrun hf ?_
  rw [ex_bl]
  have epc : mpl.base 9 + BitVec.ofNat 64 off + (mpl.base 7 + BitVec.ofNat 64 0 -
      (mpl.base 9 + BitVec.ofNat 64 off)) = mpl.base 7 + BitVec.ofNat 64 0 := by abel
  rw [epc]
  intro hCL
  obtain ⟨i1, o1, hlk1, hsub⟩ := hD
  rw [dbl_lookup] at hlk1
  obtain ⟨rfl, rfl⟩ : 7 = i1 ∧ 0 = o1 := by simpa using hlk1
  have hfa : x25519CliMultiLib.fnAddr mpl dblName = mpl.base 7 + BitVec.ofNat 64 0 :=
    fnAddr_of_lookup dbl_lookup
  set s1 := mkS sb (mpl.base 7 + BitVec.ofNat 64 0) (upd r 30#5 (mpl.base 9 + BitVec.ofNat 64 off + 4#64))
    sp ps m v with hs1
  have hCL1 : x25519CliMultiLib.CodeLoaded mpl s1.mem := hCL
  obtain ⟨hA0, hA1, hA2, hA3⟩ := hA
  have hpre : s1.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec ((fun _ => projectivePointDoubleSpec) mpl) (mpl.base 7))).pre
        (out, a, O, A) s1 ∗ F := by
    have e8 : s1.readReg64 Reg.x8 = out := by simp [hs1, Reg.x8, h8]
    have e0 : s1.readReg64 Reg.x0 = a := by simp [hs1, Reg.x0, h0]
    have h10 : s1.mem ⊨ ⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧
        O.length = 160 ∧ A.length = 120 ∧ fe51LimbsBoundedAt A 0 (2 ^ 53) ∧
        fe51LimbsBoundedAt A 40 (2 ^ 53) ∧ fe51LimbsBoundedAt A 80 (2 ^ 54)⌝ ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝ ∗
        (((a ↦ₛ A) ∗ (out ↦ₛ O) ∗ stackFrame s1 400) ∗ F) := by
      rw [sat_pure_sep, sat_pure_sep]
      exact ⟨⟨e8, e0, hO, hA0, hA1, hA2, hA3⟩, hCL1, hmem⟩
    show s1.mem ⊨ ((⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧
        O.length = 160 ∧ A.length = 120 ∧ fe51LimbsBoundedAt A 0 (2 ^ 53) ∧
        fe51LimbsBoundedAt A 40 (2 ^ 53) ∧ fe51LimbsBoundedAt A 80 (2 ^ 54)⌝ ∗
        (a ↦ₛ A) ∗ (out ↦ₛ O) ∗ stackFrame s1 400) ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝) ∗ F
    exact Satisfies.of_eq h10
  obtain ⟨sf, hsteps, hout⟩ := hsub mpl hP (out, a, O, A) F s1 (by simp [hs1, hfa])
    hrun hpre (by simp [hs1, hal]) (hCL1 7 (by decide))
  refine Reach.steps (bsteps_transfer hsteps) ?_
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  rotate_left
  · exact (sat_false hpan).elim
  · exact (sat_false hex).elim
  · exact (sat_false hoom).elim
  have hpc' : sf.pc = mpl.base 9 + BitVec.ofNat 64 (off + 4) := by
    rw [hpcf]; simp [hs1, upd_apply, BitVec.add_assoc, BitVec.ofNat_add]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  have hCLf : x25519CliMultiLib.CodeLoaded mpl sf.mem := libCL_steps hsteps hCL1
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, projectivePointDoubleSpec, stackFrame,
    hsp'] at hpost
  have hp2 := Satisfies.of_eq hpost (Q := (∃∗ res : List (BitVec 8), (out ↦ₛ res) ∗ ⌜DblPost A res⌝) ∗
      ((a ↦ₛ A) ∗ memRegion (sp - BitVec.ofNat 64 400) 400 ∗ F))
  rw [sepExists_sepConj, sat_sepExists] at hp2
  obtain ⟨res, hp2⟩ := hp2
  have hp3 := Satisfies.of_eq hp2 (Q := ⌜DblPost A res⌝ ∗
      (((a ↦ₛ A) ∗ (out ↦ₛ res) ∗ memRegion (sp - BitVec.ofNat 64 400) 400) ∗ F))
  rw [sat_pure_sep] at hp3
  obtain ⟨hpost', hp3⟩ := hp3
  have hcs' := hcs
  simp only [hs1] at hcs'
  refine hcont sf res hrunf hpc' hsp' ?_ ?_ hp3 hpost' hCLf
  · intro k hk1 hk2
    have := kept_of_cs hcs' k hk1 hk2
    rw [this, upd_apply, if_neg]
    intro e; subst e; simp at hk2
  · have := hcs'.2.2.2.2.2.2.2.2.2.2.2
    rw [this]; rfl

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): fetch lemmas (generated by tools/mk_fetch.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

section fetch09
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m)
include hP hCL

theorem f09_0 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 0) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffc0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_4 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 4) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x1c#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_8 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 8) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_12 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 12) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000030#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_16 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 16) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.sp) 0x000#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_20 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 20) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x1c0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_24 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 24) =
    some (Arm64.Instr.ldrSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x00#5) 0x0000000000000028#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_28 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 28) =
    some (Arm64.Instr.ldrSimd (Arm64.SimdMemSize.Q128) 0x01#5 (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x00#5) 0x0000000000000038#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_32 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 32) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_36 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 36) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_40 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 40) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000020#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_44 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 44) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x01#5) 0x001#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_48 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 48) =
    some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x08#5) 0x0000000000000028#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_52 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 52) =
    some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x01#5 (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x08#5) 0x0000000000000038#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_56 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 56) =
    some (Arm64.Instr.ldpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000050#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_60 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 60) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000070#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_64 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 64) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000c0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_68 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 68) =
    some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000f0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_72 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 72) =
    some (Arm64.Instr.ldpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_76 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 76) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000110#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_80 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 80) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000048#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_84 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 84) =
    some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000a0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_88 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 88) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000e8#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_92 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 92) =
    some (Arm64.Instr.bCond (Arm64.CondCode.EQ) 0x0000000000000078#64) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_96 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 96) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x15#5) (Arm64.Reg.sp) 0x000#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_100 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 100) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x1d#5) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_104 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 104) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x000#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_108 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 108) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_112 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 112) =
    some (.bl (mpl.base 7 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 112))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) dblName x25519CliBlk09 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) dbl_lookup (by decide) (fun _ => by decide) rfl

theorem f09_116 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 116) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_120 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 120) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x000#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_124 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 124) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x15#5) 0x078#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_128 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 128) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 128))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) mulName x25519CliBlk09 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f09_132 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 132) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x16#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_136 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 136) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x15#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_140 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 140) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x15#5) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_144 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 144) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 144))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) mulName x25519CliBlk09 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f09_148 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 148) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x16#5) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_152 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 152) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x15#5) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_156 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 156) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x15#5) 0x078#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_160 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 160) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 160))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) mulName x25519CliBlk09 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f09_164 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 164) =
    some (Arm64.Instr.ldpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffa0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_168 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 168) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x14#5) 0x001#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_172 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 172) =
    some (Arm64.Instr.ldrSimd (Arm64.SimdMemSize.Q128) 0x02#5 (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffc0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_176 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 176) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffd0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_180 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 180) =
    some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000e0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_184 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 184) =
    some (Arm64.Instr.ldpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffff60#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_188 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 188) =
    some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x02#5 (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000100#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_192 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 192) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000110#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_196 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 196) =
    some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000a0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_200 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 200) =
    some (Arm64.Instr.ldpSimd (Arm64.SimdMemSize.Q128) 0x02#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffff80#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_204 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 204) =
    some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x02#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000c0#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_208 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 208) =
    some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xffffffffffffff98#64) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_212 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 212) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_216 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 216) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_220 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 220) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x1d#5) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_224 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 224) =
    some (.bl (mpl.base 7 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 224))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) dblName x25519CliBlk09 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) dbl_lookup (by decide) (fun _ => by decide) rfl

theorem f09_228 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 228) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_232 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 232) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x14#5) 0x078#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_236 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 236) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_240 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 240) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 240))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) mulName x25519CliBlk09 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f09_244 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 244) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x13#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_248 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 248) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x14#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_252 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 252) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x14#5) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_256 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 256) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 256))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) mulName x25519CliBlk09 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f09_260 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 260) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x13#5) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_264 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 264) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x14#5) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_268 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 268) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x14#5) 0x078#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_272 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 272) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 272))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) mulName x25519CliBlk09 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f09_276 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 276) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x13#5) 0x078#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_280 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 280) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_284 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 284) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x14#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_288 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 288) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 288))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) mulName x25519CliBlk09 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f09_292 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 292) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x1c0#12 false) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_296 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 296) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000030#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_300 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 300) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x1c#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_304 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 304) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_308 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 308) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000040#64)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f09_312 : (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 312) =
    some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) :=
  fetch_at hP hCL (by decide) 9 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

end fetch09

end X25519Dalek.EMulP
end

section
/-! # Instruction shapes of block 8 not covered by the shared step lemmas

`ex_movz32` is copied from the sibling batch q444-xd-field (`G/P22Steps.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_add_gpr_gpr (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, hd, hn]

theorem ex_ldur64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hr : m.canRead (r n + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.UnscaledOffset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (r n + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr, ha, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_ldr64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hr : m.canRead (r n + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (r n + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr, ha, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

end exec

end X25519Dalek.EMulP
end

section
/-! # Buffers as runs of 64-bit words

`cellsFrom a ws` (owned words at `a, a + 8, …`) is the byte slice `ws.flatMap unpack64`; a byte
buffer is the run of its little-endian words `wordsOf bs off k`. Adapted from the sibling batch
q446-xd-ladder (`Words.lean`, `Fe.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64

theorem cellsFrom_eq_bytes : ∀ (a : BitVec 64) (ws : List (BitVec 64)),
    cellsFrom a ws = (a ↦ₛ ws.flatMap unpack64)
  | a, [] => by rw [cellsFrom_nil]; rfl
  | a, w :: ws => by
    rw [cellsFrom_cons, cellsFrom_eq_bytes (a + 8#64) ws, List.flatMap_cons, pointsToBytes_append,
      pointsTo64_eq_bytes]
    rfl

theorem flatMap_unpack64_length (ws : List (BitVec 64)) :
    (ws.flatMap unpack64).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatMap_cons, ih]; omega

theorem readLE_getLsbD (bs : List (BitVec 8)) (off : Nat) : ∀ (n i : Nat), n ≤ 8 →
    (ByteSlice.readLE bs off n).getLsbD i = (decide (i < 8 * n) && (bs.getD (off + i / 8) 0).getLsbD (i % 8))
  | 0, i, _ => by simp [ByteSlice.readLE]
  | n + 1, i, hn => by
    rw [ByteSlice.readLE, BitVec.getLsbD_or, readLE_getLsbD bs off n i (by omega),
      BitVec.getLsbD_shiftLeft]
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth]
    by_cases h1 : i < 8 * n
    · have h2 : i < 8 * (n + 1) := by omega
      simp [h1, h2]
    · by_cases h3 : i < 8 * (n + 1)
      · have e1 : i / 8 = n := by omega
        have e2 : i % 8 = i - 8 * n := by omega
        simp [h1, h3, e1, e2, show i < 64 by omega, show i - 8 * n < 64 by omega]
      · have h4 : 8 ≤ i - 8 * n := by omega
        simp [h1, h3, BitVec.getLsbD_of_ge _ _ h4]

theorem unpack64_getLsbD (w : BitVec 64) (j k : Nat) (hj : j < 8) (hk : k < 8) :
    ((unpack64 w).getD j 0).getLsbD k = w.getLsbD (8 * j + k) := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), unpack64_getElem w j hj]
  simp [hk]

theorem readLE_unpack64_append (w : BitVec 64) (rest : List (BitVec 8)) :
    ByteSlice.readLE (unpack64 w ++ rest) 0 8 = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [readLE_getLsbD _ _ 8 i le_rfl, Nat.zero_add, List.getD_append _ _ _ _ (by simp; omega),
    unpack64_getLsbD w _ _ (by omega) (by omega)]
  simp [show i < 8 * 8 by omega, Nat.div_add_mod]

theorem readLE_append_shift (l rest : List (BitVec 8)) (hl : l.length = 8) (off : Nat) :
    ∀ n, ByteSlice.readLE (l ++ rest) (8 + off) n = ByteSlice.readLE rest off n
  | 0 => rfl
  | n + 1 => by
    simp only [ByteSlice.readLE]
    rw [readLE_append_shift l rest hl off n, List.getD_append_right _ _ _ _ (by omega), hl]
    congr 4; omega

theorem unpack64_readLE (bs : List (BitVec 8)) (off : Nat) (h : off + 8 ≤ bs.length) :
    unpack64 (ByteSlice.readLE bs off 8) = (bs.drop off).take 8 := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    have h1' : j < 8 := by simpa using h1
    rw [unpack64_getElem _ j h1']
    simp only [List.getElem_take, List.getElem_drop]
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [BitVec.getLsbD_extractLsb', readLE_getLsbD _ _ 8 _ le_rfl]
    have e1 : (8 * j + k) / 8 = j := by omega
    have e2 : (8 * j + k) % 8 = k := by omega
    simp [hk, e1, e2, show 8 * j + k < 64 by omega, List.getElem?_eq_getElem (show off + j < bs.length by omega)]

theorem readLE_flat : ∀ (ws : List (BitVec 64)) (i : Nat) (hi : i < ws.length),
    ByteSlice.readLE (ws.flatMap unpack64) (8 * i) 8 = ws[i]
  | [], _, hi => by simp at hi
  | w :: ws, 0, _ => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.getElem_cons_zero]
    exact readLE_unpack64_append w _
  | w :: ws, i + 1, hi => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 8 * (i + 1) = 8 + 8 * i by ring, readLE_append_shift _ _ (unpack64_length w) _ 8]
    exact readLE_flat ws i (by simp at hi; omega)

/-- The `k` little-endian words of `bs` from byte offset `off`. -/
def wordsOf (bs : List (BitVec 8)) : Nat → Nat → List (BitVec 64)
  | _, 0 => []
  | off, k + 1 => ByteSlice.readLE bs off 8 :: wordsOf bs (off + 8) k

theorem wordsOf_flat (bs : List (BitVec 8)) : ∀ (k off : Nat), off + 8 * k ≤ bs.length →
    (wordsOf bs off k).flatMap unpack64 = (bs.drop off).take (8 * k)
  | 0, off, _ => by simp [wordsOf]
  | k + 1, off, h => by
    simp only [wordsOf, List.flatMap_cons]
    rw [wordsOf_flat bs k (off + 8) (by omega), unpack64_readLE bs off (by omega)]
    rw [show 8 * (k + 1) = 8 + 8 * k by ring, List.take_add, List.drop_drop, Nat.add_comm off 8]

theorem bytes_eq_cells (a : BitVec 64) (bs : List (BitVec 8)) (k : Nat) (h : bs.length = 8 * k) :
    (a ↦ₛ bs) = cellsFrom a (wordsOf bs 0 k) := by
  rw [cellsFrom_eq_bytes, wordsOf_flat bs k 0 (by omega), List.drop_zero,
    List.take_of_length_le (by omega)]

theorem cellsFrom_append3 (a : BitVec 64) (l1 l2 l3 : List (BitVec 64)) :
    cellsFrom a (l1 ++ l2 ++ l3) = cellsFrom a l1 ∗
      cellsFrom (a + BitVec.ofNat 64 (8 * l1.length)) l2 ∗
        cellsFrom (a + BitVec.ofNat 64 (8 * (l1.length + l2.length))) l3 := by
  rw [cellsFrom_append, cellsFrom_append, sepConj_assoc, List.length_append]

theorem wordsOf_length (bs : List (BitVec 8)) : ∀ (k off : Nat), (wordsOf bs off k).length = k
  | 0, _ => rfl
  | k + 1, off => by simp [wordsOf, wordsOf_length bs k (off + 8)]

/-- Limb bounds and value of a buffer made of five words. -/
theorem fe51_of_words (w0 w1 w2 w3 w4 : BitVec 64) (B : Nat) (h0 : w0.toNat < B) (h1 : w1.toNat < B)
    (h2 : w2.toNat < B) (h3 : w3.toNat < B) (h4 : w4.toNat < B) :
    fe51LimbsBounded ([w0, w1, w2, w3, w4].flatMap unpack64) B ∧
      fe51ValOfBytes ([w0, w1, w2, w3, w4].flatMap unpack64) = fe51Val w0 w1 w2 w3 w4 := by
  have r := readLE_flat [w0, w1, w2, w3, w4]
  have e0 := r 0 (by simp); have e1 := r 1 (by simp); have e2 := r 2 (by simp)
  have e3 := r 3 (by simp); have e4 := r 4 (by simp)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, List.getElem_cons_zero,
    List.getElem_cons_succ] at e0 e1 e2 e3 e4
  refine ⟨⟨by rw [flatMap_unpack64_length]; rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e0]; exact h0
  · rw [e1]; exact h1
  · rw [e2]; exact h2
  · rw [e3]; exact h3
  · rw [e4]; exact h4
  · simp only [fe51ValOfBytes, e0, e1, e2, e3, e4]

end X25519Dalek.EMulP
end

section
/-! # The words block 9 writes, and store lemmas -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

end exec

/-- A read of word `k` of a run of cells whose `k`-th entry is known to be `v` (checked by `rfl`). -/
theorem cells_rd {l : List (BitVec 64)} {a : BitVec 64} {F : SepProp} {m : Memory}
    (hs : m ⊨ cellsFrom a l ∗ F) (k o : Nat) (v : BitVec 64) (ho : 8 * k = o) (hk : l[k]? = some v) :
      m.read64 (a + BitVec.ofNat 64 o) = v ∧
      m.canRead (a + BitVec.ofNat 64 o) 8 = true ∧
      m.canWrite (a + BitVec.ofNat 64 o) 8 = true := by
  subst ho
  obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp hk
  have := cells_read _ _ _ _ hs k hlt
  rw [hv] at this
  exact this

/-- `STR Xa, [SP, #off]` into a run of cells. -/
theorem RL_str_sp {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a : BitVec 5) (ha : a ≠ 31#5)
    (off : BitVec 64) (k : Nat) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.str .X64 (.gpr a) (.Offset .sp off)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hx : sp + off = base + BitVec.ofNat 64 (8 * k)) (hk : k < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F)
    (h : ∀ m' : Memory, (m' ⊨ cellsFrom base (L.set k (r a)) ∗ F) →
      RL mpl (mkS sb (pc + 4#64) r sp ps m' v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have r0 := cells_read _ _ _ _ hs k hk
  refine RL.mk hrun hf ?_
  rw [ex_str64_sp a ha off hal (by rw [hx]; exact r0.2.2)]
  apply h
  rw [hx]
  exact cells_write _ _ _ _ hs k hk (r a)

/-- `STP Xa, Xb, [SP, #off]` into a run of cells. -/
theorem RL_stp_sp {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a b : BitVec 5) (ha : a ≠ 31#5)
    (hb : b ≠ 31#5) (off : BitVec 64) (k : Nat) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.stp .W64 (.gpr a) (.gpr b) (.Offset .sp off)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hx : sp + off = base + BitVec.ofNat 64 (8 * k)) (hk : k + 1 < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F)
    (h : ∀ m' : Memory, (m' ⊨ cellsFrom base ((L.set k (r a)).set (k + 1) (r b)) ∗ F) →
      RL mpl (mkS sb (pc + 4#64) r sp ps m' v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have r0 := cells_read _ _ _ _ hs k (by omega)
  have r1 := cells_read _ _ _ _ hs (k + 1) hk
  have e1 : base + BitVec.ofNat 64 (8 * k) + 8#64 = base + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  refine RL.mk hrun hf ?_
  rw [ex_stp64_sp a b ha hb off hal (by rw [hx]; exact r0.2.2) (by rw [hx, e1]; exact r1.2.2)]
  apply h
  have w0 := cells_write _ _ _ _ hs k (by omega) (r a)
  have w1 := cells_write _ _ _ _ w0 (k + 1) (by simp; omega) (r b)
  rw [hx, e1]
  exact w1

end X25519Dalek.EMulP
end

section
/-! # `mul` calls on runs of words

The three multiplication calls of block 9, with the operands and the result as five-word runs
inside the caller's word lists (adapted from `Dbl/Call2.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

/-- All five words are `< B`. -/
def B5 (a0 a1 a2 a3 a4 : BitVec 64) (B : Nat) : Prop :=
  a0.toNat < B ∧ a1.toNat < B ∧ a2.toNat < B ∧ a3.toNat < B ∧ a4.toNat < B

theorem wordsOf5 (bs : List (BitVec 8)) :
    wordsOf bs 0 5 = [ByteSlice.readLE bs 0 8, ByteSlice.readLE bs 8 8, ByteSlice.readLE bs 16 8,
      ByteSlice.readLE bs 24 8, ByteSlice.readLE bs 32 8] := rfl

/-- A multiplication call on five-word runs. -/
theorem call_w {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hM : fnOk mulName (fun _ => fe51MulSpec)) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {bo ba bb : BitVec 64}
    {i0 i1 i2 i3 i4 j0 j1 j2 j3 j4 o0 o1 o2 o3 o4 : BitVec 64}
    {F : SepProp}
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 off))))
    (hal : sp &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = bo) (h0 : r 0#5 = ba) (h1 : r 1#5 = bb)
    (hmem : m ⊨ (cellsFrom ba [i0, i1, i2, i3, i4] ∗ cellsFrom bb [j0, j1, j2, j3, j4] ∗
      cellsFrom bo [o0, o1, o2, o3, o4] ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F)
    (hbi : B5 i0 i1 i2 i3 i4 (2 ^ 54)) (hbj : B5 j0 j1 j2 j3 j4 (2 ^ 54))
    (hcont : ∀ (sf : State) (z0 z1 z2 z3 z4 : BitVec 64), sf.status = .Running →
      sf.pc = mpl.base 9 + BitVec.ofNat 64 (off + 4) → sf.sp = sp → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ (cellsFrom ba [i0, i1, i2, i3, i4] ∗ cellsFrom bb [j0, j1, j2, j3, j4] ∗
        cellsFrom bo [z0, z1, z2, z3, z4] ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F) →
      B5 z0 z1 z2 z3 z4 (2 ^ 52) →
      fe51Val z0 z1 z2 z3 z4 % p25519 = fe51Val i0 i1 i2 i3 i4 * fe51Val j0 j1 j2 j3 j4 % p25519 →
      RL mpl sf Q) :
    RL mpl (mkS sb (mpl.base 9 + BitVec.ofNat 64 off) r sp ps m v) Q := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := hbi
  obtain ⟨b0, b1, b2, b3, b4⟩ := hbj
  obtain ⟨hA, hAv⟩ := fe51_of_words i0 i1 i2 i3 i4 (2 ^ 54) a0 a1 a2 a3 a4
  obtain ⟨hB, hBv⟩ := fe51_of_words j0 j1 j2 j3 j4 (2 ^ 54) b0 b1 b2 b3 b4
  rw [cellsFrom_eq_bytes, cellsFrom_eq_bytes, cellsFrom_eq_bytes] at hmem
  refine call_mul hP hM hrun hf hal h8 h0 h1 hmem hA hB
    (by rw [flatMap_unpack64_length]; rfl) ?_
  intro sf res hrun' hpc hsp hk hv hm' hb' hval
  have hl : res.length = 8 * 5 := hb'.1
  rw [bytes_eq_cells bo res 5 hl, wordsOf5, ← cellsFrom_eq_bytes, ← cellsFrom_eq_bytes] at hm'
  obtain ⟨_, c0, c1, c2, c3, c4⟩ := hb'
  refine hcont sf _ _ _ _ _ hrun' hpc hsp hk hv hm' ⟨c0, c1, c2, c3, c4⟩ ?_
  rw [← hAv, ← hBv]; exact hval

theorem cells_split3 (a : BitVec 64) (L : List (BitVec 64)) (k n : Nat) (h : k + n ≤ L.length) :
    cellsFrom a L = cellsFrom a (L.take k) ∗ cellsFrom (a + BitVec.ofNat 64 (8 * k)) ((L.drop k).take n) ∗
      cellsFrom (a + BitVec.ofNat 64 (8 * (k + n))) (L.drop (k + n)) := by
  have e : L = L.take k ++ (L.drop k).take n ++ L.drop (k + n) := by
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  conv_lhs => rw [e]
  rw [cellsFrom_append3]
  have l1 : (L.take k).length = k := by simp; omega
  have l2 : ((L.drop k).take n).length = n := by simp; omega
  rw [l1, l2]

theorem cells_merge3 (a : BitVec 64) (L M : List (BitVec 64)) (k n : Nat) (h : k + n ≤ L.length)
    (hM : M.length = n) :
    cellsFrom a (L.take k) ∗ cellsFrom (a + BitVec.ofNat 64 (8 * k)) M ∗
      cellsFrom (a + BitVec.ofNat 64 (8 * (k + n))) (L.drop (k + n)) =
    cellsFrom a (L.take k ++ M ++ L.drop (k + n)) := by
  rw [cellsFrom_append3]
  have l1 : (L.take k).length = k := by simp; omega
  rw [l1, hM]

theorem take5_eq (L : List (BitVec 64)) (k : Nat) (h : k + 5 ≤ L.length) :
    (L.drop k).take 5 = [L.getD k 0, L.getD (k + 1) 0, L.getD (k + 2) 0, L.getD (k + 3) 0,
      L.getD (k + 4) 0] := by
  have g : ∀ t, L.getD (k + t) 0 = (L.drop k).getD t 0 := by
    intro t; simp [List.getD_eq_getElem?_getD]
  have h' : 5 ≤ (L.drop k).length := by simp; omega
  have g0 := g 0
  rw [Nat.add_zero] at g0
  rw [g0, g 1, g 2, g 3, g 4]
  generalize L.drop k = M at h' ⊢
  rcases M with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, rest⟩⟩⟩⟩⟩ <;> simp at h' ⊢

theorem win5 (S : List (BitVec 64)) (i k : Nat) (h : i + 5 ≤ k) (hk : k ≤ S.length) :
    ((S.take k).drop i).take 5 =
      [S.getD i 0, S.getD (i + 1) 0, S.getD (i + 2) 0, S.getD (i + 3) 0, S.getD (i + 4) 0] := by
  rw [List.drop_take, List.take_take, show min 5 (k - i) = 5 by omega]
  exact take5_eq S i (by omega)

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): the instruction shapes not covered by the shared
step lemmas (128-bit loads and stores, pre/post-indexed pairs, `SUBS w, w, #1`, `B.cond`) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_ldurq_gpr (n t : BitVec 5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hr : m.canRead (r n + off) 16 = true) :
    execInstWithSvc svc (.ldrSimd .Q128 t (.UnscaledOffset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps m (upd v t (m.read128 (r n + off))) := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr, hn,
    Memory.readSimdSized, AddrMode.baseReg]

theorem ex_sturq_gpr (n t : BitVec 5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw : m.canWrite (r n + off) 16 = true) :
    execInstWithSvc svc (.strSimd .Q128 t (.UnscaledOffset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write128 (r n + off) (v t)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, hn,
    Memory.writeSimdSized, AddrMode.baseReg]

theorem ex_strq_sp (t : BitVec 5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw : m.canWrite (sp + off) 16 = true) :
    execInstWithSvc svc (.strSimd .Q128 t (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write128 (sp + off) (v t)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw,
    Memory.writeSimdSized, AddrMode.baseReg]

theorem ex_stp_pre_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 8 = true)
    (hw2 : m.canWrite (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.PreIndex .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r (sp + off) ps
        ((m.write64 (sp + off) (r a)).write64 (sp + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw1, hw2, ha, hb,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldp_post_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead sp 8 = true)
    (hr2 : m.canRead (sp + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.PostIndex .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 sp)) b (m.read64 (sp + 8#64)))
        (sp + off) ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr1, hr2, ha, hb,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_bcond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) (mkS s0 pc r sp ps m v) =
      mkS s0 (if ConditionHolds c ps then pc + off else pc + 4#64) r sp ps m v := by
  by_cases h : ConditionHolds c ps = true <;> simp [execInstWithSvc, h]

/-- `SUBS Wd, Wn, #1` on a small positive count `k`: the result `k - 1` and `Z = (k = 1)`. -/
theorem awc32_sub1 (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 32) :
    (AddWithCarry32 (BitVec.ofNat 32 k) (4294967294#32) true).1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [AddWithCarry32, if_true, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem awc32_sub1_z (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 32) :
    (AddWithCarry32 (BitVec.ofNat 32 k) (4294967294#32) true).2.z = decide (k = 1) := by
  have e : (AddWithCarry32 (BitVec.ofNat 32 k) (4294967294#32) true).2.z =
      ((AddWithCarry32 (BitVec.ofNat 32 k) (4294967294#32) true).1 == 0#32) := rfl
  rw [e, awc32_sub1 k hk1 hk2]
  by_cases hk : k = 1
  · subst hk; decide
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h0
    have := congrArg BitVec.toNat h0
    simp at this
    omega

theorem ex_subs1 (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 32)
    (hx : (r n).truncate 32 = BitVec.ofNat 32 k) :
    ∃ ps' : PState, ps'.z = decide (k = 1) ∧
      execInstWithSvc svc (.addSubImm .W32 .SUBS (.gpr d) (.gpr n) 1#12 false) (mkS s0 pc r sp ps m v) =
        mkS s0 (pc + 4#64) (upd r d (BitVec.ofNat 64 (k - 1))) sp ps' m v := by
  have hr : (mkS s0 pc r sp ps m v).readReg32 (Reg.gpr n) = BitVec.ofNat 32 k := by
    simp [State.readReg32, hn, hx]
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, hr, hd]
  refine ⟨_, awc32_sub1_z k hk1 hk2, ?_⟩
  rw [awc32_sub1 k hk1 hk2]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end exec

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): 128-bit moves on runs of cells, and the two calls
(`ProjectivePoint::double`, `FieldElement51::mul`) on runs of words -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

@[simp] theorem extract_lo128 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi']

@[simp] theorem extract_hi128 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : ¬ (64 + i < 64) := by omega
  simp [hi', this]

theorem cs_upd {v : BitVec 5 → BitVec 128} {i : BitVec 5} {x : BitVec 128} (hi : i.toNat < 8)
    {X : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    (h : VRegFile.calleeSaved ⟨v⟩ = X) : VRegFile.calleeSaved ⟨upd v i x⟩ = X := by
  rw [← h]
  have hne : ∀ k : BitVec 5, 8 ≤ k.toNat → (k = i) = False := fun k hk => by
    apply propext; constructor
    · intro e; subst e; omega
    · intro e; exact e.elim
  simp only [VRegFile.calleeSaved, VRegFile.read, upd_apply, hne 8#5 (by decide), hne 9#5 (by decide),
    hne 10#5 (by decide), hne 11#5 (by decide), hne 12#5 (by decide), hne 13#5 (by decide),
    hne 14#5 (by decide), hne 15#5 (by decide), if_false]

/-- Address arithmetic on literal offsets. -/
theorem addr2 (b : BitVec 64) (x y z w : Nat) (h : (x + y) % 2 ^ 64 = (z + w) % 2 ^ 64) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 z + BitVec.ofNat 64 w := by
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1; apply BitVec.eq_of_toNat_eq; simpa using h

theorem addr1 (b : BitVec 64) (x z w : Nat) (h : x % 2 ^ 64 = (z + w) % 2 ^ 64) :
    b + BitVec.ofNat 64 x = b + BitVec.ofNat 64 z + BitVec.ofNat 64 w := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 1; apply BitVec.eq_of_toNat_eq; simpa using h

theorem asub (b : BitVec 64) (x y z : Nat) (h : x = y + z) :
    b + BitVec.ofNat 64 x - BitVec.ofNat 64 y = b + BitVec.ofNat 64 z := by
  subst h; rw [BitVec.ofNat_add]; abel

/-! ## 128-bit loads and stores on runs of cells -/

/-- `LDP Qt1, Qt2, [Xn, #off]` from four cells. -/
theorem RL_ldpq {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (n t1 t2 : BitVec 5) (hn : n ≠ 31#5)
    (off : BitVec 64) (k : Nat) (w0 w1 w2 w3 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k)) (hk : k + 3 < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F)
    (h0 : L[k]? = some w0) (h1 : L[k + 1]? = some w1) (h2 : L[k + 2]? = some w2)
    (h3 : L[k + 3]? = some w3)
    (h : RL mpl (mkS sb (pc + 4#64) r sp ps m (upd (upd v t1 (w1 ++ w0)) t2 (w3 ++ w2))) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have a := cells_read128 hs k (by omega)
  have b := cells_read128 hs (k + 2) hk
  have e : base + BitVec.ofNat 64 (8 * k) + 16#64 = base + BitVec.ofNat 64 (8 * (k + 2)) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  obtain ⟨_, g0⟩ := List.getElem?_eq_some_iff.mp h0
  obtain ⟨_, g1⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨_, g2⟩ := List.getElem?_eq_some_iff.mp h2
  obtain ⟨_, g3⟩ := List.getElem?_eq_some_iff.mp h3
  refine RL.mk hrun hf ?_
  rw [ex_ldpq_gpr n t1 t2 hn off (by rw [hx]; exact a.2.1) (by rw [hx, e]; exact b.2.1), hx, e, a.1,
    b.1, g0, g1, g2, g3]
  exact h

/-- `LDUR Qt, [Xn, #off]` from two cells. -/
theorem RL_ldurq {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (n t : BitVec 5) (hn : n ≠ 31#5)
    (off : BitVec 64) (k : Nat) (w0 w1 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldrSimd .Q128 t (.UnscaledOffset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k)) (hk : k + 1 < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F)
    (h0 : L[k]? = some w0) (h1 : L[k + 1]? = some w1)
    (h : RL mpl (mkS sb (pc + 4#64) r sp ps m (upd v t (w1 ++ w0))) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have a := cells_read128 hs k hk
  obtain ⟨_, g0⟩ := List.getElem?_eq_some_iff.mp h0
  obtain ⟨_, g1⟩ := List.getElem?_eq_some_iff.mp h1
  refine RL.mk hrun hf ?_
  rw [ex_ldurq_gpr n t hn off (by rw [hx]; exact a.2.1), hx, a.1, g0, g1]
  exact h

/-- `STP Qt1, Qt2, [SP, #off]` into four cells. -/
theorem RL_stpq_sp {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (t1 t2 : BitVec 5)
    (off : BitVec 64) (k : Nat) (a0 a1 b0 b1 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.stpSimd .Q128 t1 t2 (.Offset .sp off)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hx : sp + off = base + BitVec.ofNat 64 (8 * k)) (hk : k + 3 < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F) (hv1 : v t1 = a1 ++ a0) (hv2 : v t2 = b1 ++ b0)
    (h : ∀ m' : Memory, (m' ⊨ cellsFrom base ((((L.set k a0).set (k + 1) a1).set (k + 2) b0).set (k + 3) b1) ∗ F) →
      RL mpl (mkS sb (pc + 4#64) r sp ps m' v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have a := cells_read128 hs k (by omega)
  have b := cells_read128 hs (k + 2) hk
  have e : base + BitVec.ofNat 64 (8 * k) + 16#64 = base + BitVec.ofNat 64 (8 * (k + 2)) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  refine RL.mk hrun hf ?_
  rw [ex_stpq_sp t1 t2 off hal (by rw [hx]; exact a.2.2) (by rw [hx, e]; exact b.2.2), hx, e]
  apply h
  have w1 := cells_write128 hs k (by omega) (v t1)
  have w2 := cells_write128 w1 (k + 2) (by simp; omega) (v t2)
  rw [hv1, hv2] at w2 ⊢
  simp only [extract_lo128, extract_hi128] at w2
  exact w2

/-- `STR Qt, [SP, #off]` into two cells. -/
theorem RL_strq_sp {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (t : BitVec 5)
    (off : BitVec 64) (k : Nat) (a0 a1 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.strSimd .Q128 t (.Offset .sp off)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hx : sp + off = base + BitVec.ofNat 64 (8 * k)) (hk : k + 1 < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F) (hv : v t = a1 ++ a0)
    (h : ∀ m' : Memory, (m' ⊨ cellsFrom base ((L.set k a0).set (k + 1) a1) ∗ F) →
      RL mpl (mkS sb (pc + 4#64) r sp ps m' v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have a := cells_read128 hs k hk
  refine RL.mk hrun hf ?_
  rw [ex_strq_sp t off hal (by rw [hx]; exact a.2.2), hx]
  apply h
  have w1 := cells_write128 hs k hk (v t)
  rw [hv] at w1 ⊢
  simp only [extract_lo128, extract_hi128] at w1
  exact w1

/-- `STUR Qt, [Xn, #off]` into two cells. -/
theorem RL_sturq {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (n t : BitVec 5) (hn : n ≠ 31#5)
    (off : BitVec 64) (k : Nat) (a0 a1 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.strSimd .Q128 t (.UnscaledOffset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k)) (hk : k + 1 < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F) (hv : v t = a1 ++ a0)
    (h : ∀ m' : Memory, (m' ⊨ cellsFrom base ((L.set k a0).set (k + 1) a1) ∗ F) →
      RL mpl (mkS sb (pc + 4#64) r sp ps m' v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have a := cells_read128 hs k hk
  refine RL.mk hrun hf ?_
  rw [ex_sturq_gpr n t hn off (by rw [hx]; exact a.2.2), hx]
  apply h
  have w1 := cells_write128 hs k hk (v t)
  rw [hv] at w1 ⊢
  simp only [extract_lo128, extract_hi128] at w1
  exact w1

/-- `LDR Xa, [Xn, #off]` / `LDUR Xa, [Xn, #off]` from a cell. -/
theorem RL_ldr {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a n : BitVec 5) (ha : a ≠ 31#5)
    (hn : n ≠ 31#5) (off : BitVec 64) (k : Nat) (w : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldr .W64 .X64 false (.gpr a) (.Offset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ cellsFrom base L ∗ F) (h0 : L[k]? = some w)
    (h : RL mpl (mkS sb (pc + 4#64) (upd r a w) sp ps m v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have c := cells_rd hs k (8 * k) w rfl h0
  refine RL.mk hrun hf ?_
  rw [ex_ldr64_gpr a n ha hn off (by rw [hx]; exact c.2.1), hx, c.1]
  exact h

theorem RL_ldur {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a n : BitVec 5) (ha : a ≠ 31#5)
    (hn : n ≠ 31#5) (off : BitVec 64) (k : Nat) (w : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldr .W64 .X64 false (.gpr a) (.UnscaledOffset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ cellsFrom base L ∗ F) (h0 : L[k]? = some w)
    (h : RL mpl (mkS sb (pc + 4#64) (upd r a w) sp ps m v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have c := cells_rd hs k (8 * k) w rfl h0
  refine RL.mk hrun hf ?_
  rw [ex_ldur64_gpr a n ha hn off (by rw [hx]; exact c.2.1), hx, c.1]
  exact h

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): the calls on runs of words

`call_dblw`: `ProjectivePoint::double` from a 15-word run into a 20-word run; `call_win`: a
product of two five-word windows of one run into a five-word window of another run. Both own
the 400-byte area below `SP` (the larger of the two callee frames). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

theorem readLE_flat' (ws : List (BitVec 64)) (i : Nat) (hi : i < ws.length) :
    ByteSlice.readLE (ws.flatMap unpack64) (8 * i) 8 = ws.getD i 0 := by
  rw [readLE_flat ws i hi, List.getD_eq_getElem _ _ hi]

/-- Limb bounds and value of the field element at word `i` of a run of words. -/
theorem flat_at (ws : List (BitVec 64)) (i : Nat) (h : i + 5 ≤ ws.length) (B : Nat) :
    (fe51LimbsBoundedAt (ws.flatMap unpack64) (8 * i) B ↔
      B5 (ws.getD i 0) (ws.getD (i + 1) 0) (ws.getD (i + 2) 0) (ws.getD (i + 3) 0) (ws.getD (i + 4) 0) B) ∧
    fe51ValAt (ws.flatMap unpack64) (8 * i) =
      fe51Val (ws.getD i 0) (ws.getD (i + 1) 0) (ws.getD (i + 2) 0) (ws.getD (i + 3) 0) (ws.getD (i + 4) 0) := by
  have e1 : 8 * i + 8 = 8 * (i + 1) := by ring
  have e2 : 8 * i + 16 = 8 * (i + 2) := by ring
  have e3 : 8 * i + 24 = 8 * (i + 3) := by ring
  have e4 : 8 * i + 32 = 8 * (i + 4) := by ring
  simp only [fe51LimbsBoundedAt, fe51ValAt, B5, e1, e2, e3, e4]
  rw [readLE_flat' ws i (by omega), readLE_flat' ws (i + 1) (by omega), readLE_flat' ws (i + 2) (by omega),
    readLE_flat' ws (i + 3) (by omega), readLE_flat' ws (i + 4) (by omega)]
  exact ⟨Iff.rfl, rfl⟩

/-- The facts `ProjectivePoint::double` gives on its 160-byte result, for an input of 15 words. -/
def DblW (res : List (BitVec 8)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : BitVec 64) : Prop :=
  edExtOfBytes res = edProjDouble (fe51Val p0 p1 p2 p3 p4) (fe51Val p5 p6 p7 p8 p9)
      (fe51Val p10 p11 p12 p13 p14) ∧
    fe51LimbsBoundedAt res 0 (2 ^ 52) ∧ fe51LimbsBoundedAt res 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res 80 (2 ^ 52) ∧ fe51LimbsBoundedAt res 120 (2 ^ 52)

/-- `ProjectivePoint::double` from the 15 words at `a` into the 20 words at `o`. -/
theorem call_dblw {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hD : fnOk dblName (fun _ => projectivePointDoubleSpec)) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {o a : BitVec 64} {C : List (BitVec 64)}
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : BitVec 64) {F : SepProp}
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 7 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 off))))
    (hal : sp &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = o) (h0 : r 0#5 = a) (hC : C.length = 20)
    (hmem : m ⊨ cellsFrom o C ∗ cellsFrom a [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗
      memRegion (sp - BitVec.ofNat 64 400) 400 ∗ F)
    (hbX : B5 p0 p1 p2 p3 p4 (2 ^ 53)) (hbY : B5 p5 p6 p7 p8 p9 (2 ^ 53))
    (hbZ : B5 p10 p11 p12 p13 p14 (2 ^ 54))
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running →
      sf.pc = mpl.base 9 + BitVec.ofNat 64 (off + 4) → sf.sp = sp → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ cellsFrom o (wordsOf res 0 20) ∗
        cellsFrom a [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗
        memRegion (sp - BitVec.ofNat 64 400) 400 ∗ F) →
      DblW res p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 → RL mpl sf Q) :
    RL mpl (mkS sb (mpl.base 9 + BitVec.ofNat 64 off) r sp ps m v) Q := by
  have fX := flat_at [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] 0 (by simp)
  have fY := flat_at [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] 5 (by simp)
  have fZ := flat_at [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] 10 (by simp)
  rw [cellsFrom_eq_bytes o C, cellsFrom_eq_bytes a] at hmem
  refine call_dbl hP hD hrun hf hal h8 h0 (Satisfies.of_eq hmem)
    ⟨by rw [flatMap_unpack64_length]; rfl, (fX (2 ^ 53)).1.mpr hbX, (fY (2 ^ 53)).1.mpr hbY, (fZ (2 ^ 54)).1.mpr hbZ⟩
    (by rw [flatMap_unpack64_length, hC]) ?_
  intro sf res hrun' hpc hsp hk hv hm' hpost
  obtain ⟨hl, hval, b0, b1, b2, b3⟩ := hpost
  rw [bytes_eq_cells o res 20 hl, ← cellsFrom_eq_bytes a] at hm'
  refine hcont sf res hrun' hpc hsp hk hv (Satisfies.of_eq hm') ⟨?_, b0, b1, b2, b3⟩
  have eX : fe51ValAt ([p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14].flatMap unpack64) 0 =
      fe51Val p0 p1 p2 p3 p4 := (fX 0).2
  have eY : fe51ValAt ([p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14].flatMap unpack64) 40 =
      fe51Val p5 p6 p7 p8 p9 := (fY 0).2
  have eZ : fe51ValAt ([p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14].flatMap unpack64) 80 =
      fe51Val p10 p11 p12 p13 p14 := (fZ 0).2
  rw [hval, eX, eY, eZ]

theorem e400 (sp : BitVec 64) :
    sp - BitVec.ofNat 64 400 + BitVec.ofNat 64 176 = sp - BitVec.ofNat 64 224 := by
  rw [show (BitVec.ofNat 64 400 : BitVec 64) = BitVec.ofNat 64 176 + BitVec.ofNat 64 224 by rfl]; abel

theorem memRegion_400 (sp : BitVec 64) {m : Memory} {F : SepProp}
    (h : m ⊨ memRegion (sp - BitVec.ofNat 64 400) 400 ∗ F) :
    m ⊨ memRegion (sp - BitVec.ofNat 64 400) 176 ∗ memRegion (sp - BitVec.ofNat 64 224) 224 ∗ F := by
  have h1 := sat_sep_mono h (memRegion_split (sp - BitVec.ofNat 64 400) 176 224 (by norm_num))
  rw [e400] at h1
  exact Satisfies.of_eq h1

theorem memRegion_400' (sp : BitVec 64) {m : Memory} {F : SepProp}
    (h : m ⊨ memRegion (sp - BitVec.ofNat 64 400) 176 ∗ memRegion (sp - BitVec.ofNat 64 224) 224 ∗ F) :
    m ⊨ memRegion (sp - BitVec.ofNat 64 400) 400 ∗ F := by
  rw [← sepConj_assoc] at h
  have h1 := sat_sep_mono h (memRegion_merge (sp - BitVec.ofNat 64 400) (sp - BitVec.ofNat 64 224) 176 224
    (e400 sp).symm
    (by norm_num) (by norm_num))
  exact h1

/-- A product of windows `i` and `j` (`i + 5 ≤ j`) of the run `A` at `a` into window `k` of the
run `B` at `b`. -/
theorem call_win {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hM : fnOk mulName (fun _ => fe51MulSpec)) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {a b : BitVec 64} {A B : List (BitVec 64)} {F : SepProp}
    (i j k : Nat) (hij : i + 5 ≤ j) (hj : j + 5 ≤ A.length) (hk : k + 5 ≤ B.length)
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m (mpl.base 9 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 9 + BitVec.ofNat 64 off))))
    (hal : sp &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = b + BitVec.ofNat 64 (8 * k)) (h0 : r 0#5 = a + BitVec.ofNat 64 (8 * i))
    (h1 : r 1#5 = a + BitVec.ofNat 64 (8 * j))
    (hmem : m ⊨ cellsFrom a A ∗ cellsFrom b B ∗ memRegion (sp - BitVec.ofNat 64 400) 400 ∗ F)
    (hbi : B5 (A.getD i 0) (A.getD (i + 1) 0) (A.getD (i + 2) 0) (A.getD (i + 3) 0)
      (A.getD (i + 4) 0) (2 ^ 54))
    (hbj : B5 (A.getD j 0) (A.getD (j + 1) 0) (A.getD (j + 2) 0) (A.getD (j + 3) 0)
      (A.getD (j + 4) 0) (2 ^ 54))
    (hcont : ∀ (sf : State) (z0 z1 z2 z3 z4 : BitVec 64), sf.status = .Running →
      sf.pc = mpl.base 9 + BitVec.ofNat 64 (off + 4) → sf.sp = sp → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ cellsFrom a A ∗ cellsFrom b (B.take k ++ [z0, z1, z2, z3, z4] ++ B.drop (k + 5)) ∗
        memRegion (sp - BitVec.ofNat 64 400) 400 ∗ F) →
      B5 z0 z1 z2 z3 z4 (2 ^ 52) →
      fe51Val z0 z1 z2 z3 z4 % p25519 =
        fe51Val (A.getD i 0) (A.getD (i + 1) 0) (A.getD (i + 2) 0) (A.getD (i + 3) 0) (A.getD (i + 4) 0) *
        fe51Val (A.getD j 0) (A.getD (j + 1) 0) (A.getD (j + 2) 0) (A.getD (j + 3) 0)
          (A.getD (j + 4) 0) % p25519 →
      RL mpl sf Q) :
    RL mpl (mkS sb (mpl.base 9 + BitVec.ofNat 64 off) r sp ps m v) Q := by
  have hik' : i + 5 ≤ (A.take j).length := by simp; omega
  have hm1 := Satisfies.of_eq hmem (Q := memRegion (sp - BitVec.ofNat 64 400) 400 ∗
    (cellsFrom a A ∗ cellsFrom b B ∗ F))
  have hm2 := memRegion_400 sp hm1
  rw [cells_split3 a A j 5 hj, cells_split3 a (A.take j) i 5 hik', win5 A i j hij (by omega),
    take5_eq A j hj, cells_split3 b B k 5 hk, take5_eq B k hk] at hm2
  refine call_w hP hM (o0 := B.getD k 0) (o1 := B.getD (k + 1) 0) (o2 := B.getD (k + 2) 0)
    (o3 := B.getD (k + 3) 0) (o4 := B.getD (k + 4) 0)
    (F := memRegion (sp - BitVec.ofNat 64 400) 176 ∗ cellsFrom a ((A.take j).take i) ∗
      cellsFrom (a + BitVec.ofNat 64 (8 * (i + 5))) ((A.take j).drop (i + 5)) ∗
      cellsFrom (a + BitVec.ofNat 64 (8 * (j + 5))) (A.drop (j + 5)) ∗
      cellsFrom b (B.take k) ∗ cellsFrom (b + BitVec.ofNat 64 (8 * (k + 5))) (B.drop (k + 5)) ∗ F)
    hrun hf hal h8 h0 h1 (Satisfies.of_eq hm2) hbi hbj ?_
  intro sf z0 z1 z2 z3 z4 hrun' hpc hsp hkr hv hm' hb' hval
  refine hcont sf z0 z1 z2 z3 z4 hrun' hpc hsp hkr hv ?_ hb' hval
  have hm3 : sf.mem ⊨ memRegion (sp - BitVec.ofNat 64 400) 176 ∗ memRegion (sp - BitVec.ofNat 64 224) 224 ∗
      (cellsFrom a A ∗ cellsFrom b (B.take k ++ [z0, z1, z2, z3, z4] ++ B.drop (k + 5)) ∗ F) := by
    rw [← cells_merge3 b B _ k 5 hk rfl, cells_split3 a A j 5 hj, cells_split3 a (A.take j) i 5 hik',
      win5 A i j hij (by omega), take5_eq A j hj]
    exact Satisfies.of_eq hm'
  exact Satisfies.of_eq (memRegion_400' sp hm3)

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): the field arithmetic

One loop iteration maps the `ProjectivePoint` `(X, Y, Z)` to `edAsProjective (edProjDouble X Y Z)`
(`stepP`); the last iteration ends with `edAsExtended`. Values are compared modulo `p25519`. -/

set_option autoImplicit false

namespace X25519Dalek.EMulP

/-- One `ProjectivePoint::double` followed by `CompletedPoint::as_projective`. -/
def stepP (x y z : Nat) : EdExtPoint := edAsProjective (edProjDouble x y z)

theorem edProjDouble_mod (x y z : Nat) :
    edProjDouble (x % p25519) (y % p25519) (z % p25519) = edProjDouble x y z := by
  simp only [edProjDouble, Nat.mod_mod]

theorem stepP_mod (x y z : Nat) :
    stepP (x % p25519) (y % p25519) (z % p25519) = stepP x y z := by
  simp only [stepP, edProjDouble_mod]

theorem fpMul_mod (a b : Nat) : fpMul (a % p25519) (b % p25519) = a * b % p25519 := by
  simp only [fpMul, Nat.mod_mod, ← Nat.mul_mod]

/-- The values after one loop iteration: the three products of the `CompletedPoint` `res`. -/
theorem iter_vals (res : List (BitVec 8)) (x y z : Nat) (hD : edExtOfBytes res = edProjDouble x y z)
    (a b c : Nat)
    (ha : a % p25519 = fe51ValAt res 0 * fe51ValAt res 120 % p25519)
    (hb : b % p25519 = fe51ValAt res 40 * fe51ValAt res 80 % p25519)
    (hc : c % p25519 = fe51ValAt res 80 * fe51ValAt res 120 % p25519) :
    a % p25519 = (stepP x y z).X ∧ b % p25519 = (stepP x y z).Y ∧ c % p25519 = (stepP x y z).Z := by
  simp only [stepP, ← hD, edAsProjective, edExtOfBytes, fpMul_mod]
  exact ⟨ha, hb, hc⟩

/-- The values of the result: the four products of the last `CompletedPoint` `res`. -/
theorem final_vals (res : List (BitVec 8)) (x y z : Nat) (hD : edExtOfBytes res = edProjDouble x y z)
    (a b c d : Nat)
    (ha : a % p25519 = fe51ValAt res 0 * fe51ValAt res 120 % p25519)
    (hb : b % p25519 = fe51ValAt res 40 * fe51ValAt res 80 % p25519)
    (hc : c % p25519 = fe51ValAt res 80 * fe51ValAt res 120 % p25519)
    (hd : d % p25519 = fe51ValAt res 0 * fe51ValAt res 40 % p25519) :
    (⟨a % p25519, b % p25519, c % p25519, d % p25519⟩ : EdExtPoint) =
      edAsExtended (edProjDouble x y z) := by
  simp only [← hD, edAsExtended, edExtOfBytes, fpMul_mod]
  rw [ha, hb, hc, hd]

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): reads from the second run of a heap, register
bookkeeping across calls, and the words of a `CompletedPoint` -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

theorem RL_ldpq2 {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {A F : SepProp} (n t1 t2 : BitVec 5) (hn : n ≠ 31#5)
    (off : BitVec 64) (k : Nat) (w0 w1 w2 w3 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k)) (hk : k + 3 < L.length)
    (hs : m ⊨ A ∗ cellsFrom base L ∗ F)
    (h0 : L[k]? = some w0) (h1 : L[k + 1]? = some w1) (h2 : L[k + 2]? = some w2)
    (h3 : L[k + 3]? = some w3)
    (h : RL mpl (mkS sb (pc + 4#64) r sp ps m (upd (upd v t1 (w1 ++ w0)) t2 (w3 ++ w2))) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  rw [sepConj_left_comm] at hs
  exact RL_ldpq n t1 t2 hn off k w0 w1 w2 w3 hrun hf hx hk hs h0 h1 h2 h3 h

theorem RL_ldurq2 {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {A F : SepProp} (n t : BitVec 5) (hn : n ≠ 31#5)
    (off : BitVec 64) (k : Nat) (w0 w1 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldrSimd .Q128 t (.UnscaledOffset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k)) (hk : k + 1 < L.length)
    (hs : m ⊨ A ∗ cellsFrom base L ∗ F)
    (h0 : L[k]? = some w0) (h1 : L[k + 1]? = some w1)
    (h : RL mpl (mkS sb (pc + 4#64) r sp ps m (upd v t (w1 ++ w0))) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  rw [sepConj_left_comm] at hs
  exact RL_ldurq n t hn off k w0 w1 hrun hf hx hk hs h0 h1 h

theorem RL_ldur2 {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {A F : SepProp} (a n : BitVec 5) (ha : a ≠ 31#5)
    (hn : n ≠ 31#5) (off : BitVec 64) (k : Nat) (w : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldr .W64 .X64 false (.gpr a) (.UnscaledOffset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ A ∗ cellsFrom base L ∗ F) (h0 : L[k]? = some w)
    (h : RL mpl (mkS sb (pc + 4#64) (upd r a w) sp ps m v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  rw [sepConj_left_comm] at hs
  exact RL_ldur a n ha hn off k w hrun hf hx hs h0 h

theorem RL_ldr2 {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {A F : SepProp} (a n : BitVec 5) (ha : a ≠ 31#5)
    (hn : n ≠ 31#5) (off : BitVec 64) (k : Nat) (w : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldr .W64 .X64 false (.gpr a) (.Offset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ A ∗ cellsFrom base L ∗ F) (h0 : L[k]? = some w)
    (h : RL mpl (mkS sb (pc + 4#64) (upd r a w) sp ps m v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  rw [sepConj_left_comm] at hs
  exact RL_ldr a n ha hn off k w hrun hf hx hs h0 h

/-- Registers `x19`–`x29` survive writes to lower registers. -/
theorem kept_upd {r r0 : BitVec 5 → BitVec 64} {i : BitVec 5} {x : BitVec 64}
    (h : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → r k = r0 k) (hi : i.toNat < 19) :
    ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → upd r i x k = r0 k := by
  intro k h1 h2
  have : k ≠ i := by intro e; subst e; omega
  rw [upd_apply, if_neg this]; exact h k h1 h2

theorem kept_upd20 {r r0 : BitVec 5 → BitVec 64} {i : BitVec 5} {x : BitVec 64}
    (h : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → k ≠ 20#5 → r k = r0 k)
    (hi : i.toNat < 19 ∨ i = 20#5) :
    ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → k ≠ 20#5 → upd r i x k = r0 k := by
  intro k h1 h2 h3
  have : k ≠ i := by
    intro e; subst e
    rcases hi with hi | hi
    · omega
    · exact h3 hi
  rw [upd_apply, if_neg this]; exact h k h1 h2 h3

theorem kept_trans {sf : State} {r r0 : BitVec 5 → BitVec 64} (hk : KeptRegs sf r)
    (h : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → r k = r0 k) :
    ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → sf.regs.regs k = r0 k :=
  fun k h1 h2 => (hk k h1 h2).trans (h k h1 h2)

theorem wordsOf_getD (bs : List (BitVec 8)) : ∀ (k off i : Nat), i < k →
    (wordsOf bs off k).getD i 0 = ByteSlice.readLE bs (off + 8 * i) 8
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, off, 0, _ => by simp [wordsOf]
  | k + 1, off, i + 1, h => by
    simp only [wordsOf, List.getD_cons_succ]
    rw [wordsOf_getD bs k (off + 8) i (by omega)]
    congr 1; ring

/-- Window `i` of the 20 words of a `CompletedPoint`. -/
theorem win_bnd (res : List (BitVec 8)) (i : Nat) (hi : i + 5 ≤ 20) {B B' : Nat}
    (h : fe51LimbsBoundedAt res (8 * i) B) (hB : B ≤ B') :
    B5 ((wordsOf res 0 20).getD i 0) ((wordsOf res 0 20).getD (i + 1) 0)
      ((wordsOf res 0 20).getD (i + 2) 0) ((wordsOf res 0 20).getD (i + 3) 0)
      ((wordsOf res 0 20).getD (i + 4) 0) B' := by
  have e1 : 8 * i + 8 = 8 * (i + 1) := by ring
  have e2 : 8 * i + 16 = 8 * (i + 2) := by ring
  have e3 : 8 * i + 24 = 8 * (i + 3) := by ring
  have e4 : 8 * i + 32 = 8 * (i + 4) := by ring
  simp only [fe51LimbsBoundedAt, e1, e2, e3, e4] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  rw [wordsOf_getD res 20 0 i (by omega), wordsOf_getD res 20 0 (i + 1) (by omega),
    wordsOf_getD res 20 0 (i + 2) (by omega), wordsOf_getD res 20 0 (i + 3) (by omega),
    wordsOf_getD res 20 0 (i + 4) (by omega)]
  simp only [Nat.zero_add]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem win_val (res : List (BitVec 8)) (i : Nat) (hi : i + 5 ≤ 20) :
    fe51Val ((wordsOf res 0 20).getD i 0) ((wordsOf res 0 20).getD (i + 1) 0)
      ((wordsOf res 0 20).getD (i + 2) 0) ((wordsOf res 0 20).getD (i + 3) 0)
      ((wordsOf res 0 20).getD (i + 4) 0) = fe51ValAt res (8 * i) := by
  have e1 : 8 * i + 8 = 8 * (i + 1) := by ring
  have e2 : 8 * i + 16 = 8 * (i + 2) := by ring
  have e3 : 8 * i + 24 = 8 * (i + 3) := by ring
  have e4 : 8 * i + 32 = 8 * (i + 4) := by ring
  rw [wordsOf_getD res 20 0 i (by omega), wordsOf_getD res 20 0 (i + 1) (by omega),
    wordsOf_getD res 20 0 (i + 2) (by omega), wordsOf_getD res 20 0 (i + 3) (by omega),
    wordsOf_getD res 20 0 (i + 4) (by omega)]
  simp only [fe51ValAt, Nat.zero_add, e1, e2, e3, e4]

theorem B5_mono {a0 a1 a2 a3 a4 : BitVec 64} {B B' : Nat} (h : B5 a0 a1 a2 a3 a4 B) (hB : B ≤ B') :
    B5 a0 a1 a2 a3 a4 B' := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem RL_subs1 {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 32)
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.addSubImm .W32 .SUBS (.gpr d) (.gpr n) 1#12 false))
    (hx : (r n).truncate 32 = BitVec.ofNat 32 k)
    (h : ∀ ps' : PState, ps'.z = decide (k = 1) →
      RL mpl (mkS sb (pc + 4#64) (upd r d (BitVec.ofNat 64 (k - 1))) sp ps' m v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  refine RL.mk hrun hf ?_
  obtain ⟨ps', hz, he⟩ := ex_subs1 (svc := evalSvc (bprog mpl 9).svc) (s0 := sb) (pc := pc) (sp := sp)
    (ps := ps) (m := m) (v := v) d n hd hn k hk1 hk2 hx
  rw [he]
  exact h ps' hz

theorem RL_pc_congr {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc pc' : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    (h : pc = pc') (H : RL mpl (mkS sb pc' r sp ps m v) Q) : RL mpl (mkS sb pc r sp ps m v) Q := by
  subst h; exact H

theorem al16_add (x : BitVec 64) (k : Nat) (hk : k % 16 = 0) (h : x &&& 0b1111#64 = 0#64) :
    (x + BitVec.ofNat 64 k) &&& 0b1111#64 = 0#64 := by
  rw [al16_iff] at h ⊢
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- `STP Xa, Xb, [SP, #off]!` into the first two cells of a run at `sp + off`. -/
theorem RL_stp_pre {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a b : BitVec 5) (ha : a ≠ 31#5)
    (hb : b ≠ 31#5) (off : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.stp .W64 (.gpr a) (.gpr b) (.PreIndex .sp off)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hx : sp + off = base) (hk : 1 < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F)
    (h : ∀ m' : Memory, (m' ⊨ cellsFrom base ((L.set 0 (r a)).set 1 (r b)) ∗ F) →
      RL mpl (mkS sb (pc + 4#64) r base ps m' v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have r0 := cells_read _ _ _ _ hs 0 (by omega)
  have r1 := cells_read _ _ _ _ hs 1 hk
  have e0 : base + BitVec.ofNat 64 (8 * 0) = base := by simp
  have e1 : base + 8#64 = base + BitVec.ofNat 64 (8 * 1) := rfl
  rw [e0] at r0
  refine RL.mk hrun hf ?_
  rw [ex_stp_pre_sp a b ha hb off hal (by rw [hx]; exact r0.2.2) (by rw [hx, e1]; exact r1.2.2), hx]
  apply h
  have w0 := cells_write _ _ _ _ hs 0 (by omega) (r a)
  have w1 := cells_write _ _ _ _ w0 1 (by simp; omega) (r b)
  rw [e0] at w0 w1
  rw [e1]
  exact w1

/-- `LDP Xa, Xb, [SP], #off` from the first two cells of a run at `sp`. -/
theorem RL_ldp_post {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {L : List (BitVec 64)} {F : SepProp} (a b : BitVec 5) (ha : a ≠ 31#5)
    (hb : b ≠ 31#5) (off : BitVec 64) (w0 w1 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldp .W64 false (.gpr a) (.gpr b) (.PostIndex .sp off)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hs : m ⊨ cellsFrom sp L ∗ F) (h0 : L[0]? = some w0) (h1 : L[1]? = some w1)
    (h : RL mpl (mkS sb (pc + 4#64) (upd (upd r a w0) b w1) (sp + off) ps m v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have c0 := cells_rd hs 0 0 w0 rfl h0
  have c1 := cells_rd hs 1 8 w1 rfl h1
  have e0 : sp + BitVec.ofNat 64 0 = sp := by simp
  rw [e0] at c0
  refine RL.mk hrun hf ?_
  rw [ex_ldp_post_sp a b ha hb off hal c0.2.1 c1.2.1, c0.1]
  rw [show sp + 8#64 = sp + BitVec.ofNat 64 8 from rfl, c1.1]
  exact h

/-- `LDP Xa, Xb, [SP, #off]` from two cells. -/
theorem RL_ldp_sp {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a b : BitVec 5) (ha : a ≠ 31#5)
    (hb : b ≠ 31#5) (off : BitVec 64) (k : Nat) (w0 w1 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldp .W64 false (.gpr a) (.gpr b) (.Offset .sp off)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hx : sp + off = base + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ cellsFrom base L ∗ F) (h0 : L[k]? = some w0) (h1 : L[k + 1]? = some w1)
    (h : RL mpl (mkS sb (pc + 4#64) (upd (upd r a w0) b w1) sp ps m v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have c0 := cells_rd hs k (8 * k) w0 rfl h0
  have c1 := cells_rd hs (k + 1) (8 * (k + 1)) w1 rfl h1
  have e1 : base + BitVec.ofNat 64 (8 * k) + 8#64 = base + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  refine RL.mk hrun hf ?_
  rw [ex_ldp64_sp a b ha hb off hal (by rw [hx]; exact c0.2.1) (by rw [hx, e1]; exact c1.2.1), hx, e1,
    c0.1, c1.1]
  exact h

/-- `LDR Xa, [SP, #off]` from a cell. -/
theorem RL_ldr_sp {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a : BitVec 5) (ha : a ≠ 31#5)
    (off : BitVec 64) (k : Nat) (w0 : BitVec 64) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 9).fetchMem m pc =
      some (.ldr .W64 .X64 false (.gpr a) (.Offset .sp off)))
    (hal : sp &&& 0b1111#64 = 0#64)
    (hx : sp + off = base + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ cellsFrom base L ∗ F) (h0 : L[k]? = some w0)
    (h : RL mpl (mkS sb (pc + 4#64) (upd r a w0) sp ps m v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have c0 := cells_rd hs k (8 * k) w0 rfl h0
  refine RL.mk hrun hf ?_
  rw [ex_ldr64_sp a ha off hal (by rw [hx]; exact c0.2.1), hx, c0.1]
  exact h

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): one iteration of the doubling loop (offsets 104–208)

`ProjectivePoint::double` of the point at `SP + 160` into `SP`, the three products `X·T`, `Y·Z`,
`Z·T` into `SP + 288`, the copy of those 15 words back to `SP + 160`, `w20 := w20 - 1` and the
branch back to 104 (or on to 212 when the count reaches zero). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

set_option maxHeartbeats 4000000 in
theorem loop_iter {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hD : fnOk dblName (fun _ => projectivePointDoubleSpec)) (hM : fnOk mulName (fun _ => fe51MulSpec))
    {Q : State → Prop} {sb : State} {r : BitVec 5 → BitVec 64} {SP : BitVec 64} {ps : PState}
    {m : Memory} {v : BitVec 5 → BitVec 128} {F : SepProp} {C : List (BitVec 64)}
    (n : Nat) (hn1 : 1 ≤ n) (hn2 : n < 2 ^ 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 : BitVec 64)
    (hrun : sb.status = .Running) (halSP : SP &&& 0b1111#64 = 0#64)
    (h20 : (r 20#5).truncate 32 = BitVec.ofNat 32 n) (h21 : r 21#5 = SP)
    (h22 : r 22#5 = SP + BitVec.ofNat 64 288) (h29 : r 29#5 = SP + BitVec.ofNat 64 448)
    (hC : C.length = 20)
    (hm : m ⊨ cellsFrom SP C ∗
      cellsFrom (SP + BitVec.ofNat 64 160) [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗
      memRegion (SP - BitVec.ofNat 64 400) 400 ∗
      cellsFrom (SP + BitVec.ofNat 64 288)
        [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19] ∗ F)
    (hbX : B5 p0 p1 p2 p3 p4 (2 ^ 53)) (hbY : B5 p5 p6 p7 p8 p9 (2 ^ 53))
    (hbZ : B5 p10 p11 p12 p13 p14 (2 ^ 54))
    (hK : ∀ (sb' : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory)
        (v' : BitVec 5 → BitVec 128) (C' : List (BitVec 64))
        (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 : BitVec 64),
      sb'.status = .Running →
      (∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → k ≠ 20#5 → r' k = r k) →
      r' 20#5 = BitVec.ofNat 64 (n - 1) →
      VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨v⟩ →
      C'.length = 20 →
      (m' ⊨ cellsFrom SP C' ∗
        cellsFrom (SP + BitVec.ofNat 64 160) [u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14] ∗
        memRegion (SP - BitVec.ofNat 64 400) 400 ∗
        cellsFrom (SP + BitVec.ofNat 64 288)
          [u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, q15, q16, q17, q18, q19] ∗ F) →
      B5 u0 u1 u2 u3 u4 (2 ^ 52) → B5 u5 u6 u7 u8 u9 (2 ^ 52) → B5 u10 u11 u12 u13 u14 (2 ^ 52) →
      fe51Val u0 u1 u2 u3 u4 % p25519 =
        (stepP (fe51Val p0 p1 p2 p3 p4) (fe51Val p5 p6 p7 p8 p9) (fe51Val p10 p11 p12 p13 p14)).X →
      fe51Val u5 u6 u7 u8 u9 % p25519 =
        (stepP (fe51Val p0 p1 p2 p3 p4) (fe51Val p5 p6 p7 p8 p9) (fe51Val p10 p11 p12 p13 p14)).Y →
      fe51Val u10 u11 u12 u13 u14 % p25519 =
        (stepP (fe51Val p0 p1 p2 p3 p4) (fe51Val p5 p6 p7 p8 p9) (fe51Val p10 p11 p12 p13 p14)).Z →
      RL mpl (mkS sb' (mpl.base 9 + BitVec.ofNat 64 (if n = 1 then 212 else 104)) r' SP ps' m' v') Q) :
    RL mpl (mkS sb (mpl.base 9 + BitVec.ofNat 64 104) r SP ps m v) Q := by
  -- 104: add x8, sp, #0
  refine RL.mk hrun (f09_104 hP) ?_
  rw [ex_add_gpr_sp 8#5 (by decide), z12 _ (by norm_num), pc_add]
  -- 108: add x0, sp, #160
  refine RL.mk hrun (f09_108 hP) ?_
  rw [ex_add_gpr_sp 0#5 (by decide), z12 _ (by norm_num), pc_add]
  -- 112: bl double
  refine call_dblw hP hD (off := 112) (o := SP) (a := SP + BitVec.ofNat 64 160)
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 hrun (f09_112 hP) halSP
    (by simp [upd_apply]) (by simp [upd_apply]) hC hm hbX hbY hbZ ?_
  intro sf1 res hrun1 hpc1 hsp1 hk1 hv1 hm1 hd1
  obtain ⟨hD1, b0, b1, b2, b3⟩ := hd1
  refine RL.congr (s' := mkS sf1 (mpl.base 9 + BitVec.ofNat 64 116) sf1.regs.regs SP sf1.pstate sf1.mem
    sf1.vregs.regs) (by rw [← hpc1, ← hsp1]; rfl) ?_
  have K1 := kept_trans hk1 (kept_upd (kept_upd (fun _ _ _ => rfl) (by decide)) (by decide))
  have g21 : sf1.regs.regs 21#5 = SP := (K1 21#5 (by decide) (by decide)).trans h21
  have g22 : sf1.regs.regs 22#5 = SP + BitVec.ofNat 64 288 := (K1 22#5 (by decide) (by decide)).trans h22
  have g29 : sf1.regs.regs 29#5 = SP + BitVec.ofNat 64 448 := (K1 29#5 (by decide) (by decide)).trans h29
  -- 116: sub x8, x29, #160
  refine RL.mk hrun1 (f09_116 hP) ?_
  rw [ex_sub_gpr_gpr 8#5 29#5 (by decide) (by decide), z12 _ (by norm_num), pc_add, g29,
    asub SP 448 160 288 rfl]
  -- 120: add x0, sp, #0
  refine RL.mk hrun1 (f09_120 hP) ?_
  rw [ex_add_gpr_sp 0#5 (by decide), z12 _ (by norm_num), pc_add]
  -- 124: add x1, x21, #120
  refine RL.mk hrun1 (f09_124 hP) ?_
  rw [ex_add_gpr_gpr 1#5 21#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 128: bl mul (X * T)
  refine call_win hP hM (off := 128) (a := SP) (b := SP + BitVec.ofNat 64 288) (A := wordsOf res 0 20)
    (B := [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19])
    (F := cellsFrom (SP + BitVec.ofNat 64 160)
      [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗ F)
    0 15 0 (by norm_num) (by simp [wordsOf_length]) (by simp) hrun1 (f09_128 hP) halSP
    (by simp [upd_apply]) (by simp [upd_apply]) (by simp [upd_apply, g21])
    (Satisfies.of_eq hm1) (win_bnd res 0 (by norm_num) b0 (by norm_num))
    (win_bnd res 15 (by norm_num) b3 (by norm_num)) ?_
  intro sf2 x0 x1 x2 x3 x4 hrun2 hpc2 hsp2 hk2 hv2 hm2 hb2 hval2
  simp only [List.take, List.drop, List.cons_append, List.nil_append] at hm2
  rw [win_val res 0 (by norm_num), win_val res 15 (by norm_num)] at hval2
  refine RL.congr (s' := mkS sf2 (mpl.base 9 + BitVec.ofNat 64 132) sf2.regs.regs SP sf2.pstate sf2.mem
    sf2.vregs.regs) (by rw [← hpc2, ← hsp2]; rfl) ?_
  have K2 := kept_trans hk2 (kept_upd (kept_upd (kept_upd K1 (by decide)) (by decide)) (by decide))
  have g21 : sf2.regs.regs 21#5 = SP := (K2 21#5 (by decide) (by decide)).trans h21
  have g22 : sf2.regs.regs 22#5 = SP + BitVec.ofNat 64 288 := (K2 22#5 (by decide) (by decide)).trans h22
  -- 132: add x8, x22, #40
  refine RL.mk hrun2 (f09_132 hP) ?_
  rw [ex_add_gpr_gpr 8#5 22#5 (by decide) (by decide), z12 _ (by norm_num), pc_add, g22]
  -- 136: add x0, x21, #40
  refine RL.mk hrun2 (f09_136 hP) ?_
  rw [ex_add_gpr_gpr 0#5 21#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 140: add x1, x21, #80
  refine RL.mk hrun2 (f09_140 hP) ?_
  rw [ex_add_gpr_gpr 1#5 21#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 144: bl mul (Y * Z)
  refine call_win hP hM (off := 144) (a := SP) (b := SP + BitVec.ofNat 64 288) (A := wordsOf res 0 20)
    (B := [x0, x1, x2, x3, x4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19])
    (F := cellsFrom (SP + BitVec.ofNat 64 160)
      [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗ F)
    5 10 5 (by norm_num) (by simp [wordsOf_length]) (by simp) hrun2 (f09_144 hP) halSP
    (by simp [upd_apply]) (by simp [upd_apply, g21]) (by simp [upd_apply, g21])
    hm2 (win_bnd res 5 (by norm_num) b1 (by norm_num))
    (win_bnd res 10 (by norm_num) b2 (by norm_num)) ?_
  intro sf3 y0 y1 y2 y3 y4 hrun3 hpc3 hsp3 hk3 hv3 hm3 hb3 hval3
  simp only [List.take, List.drop, List.cons_append, List.nil_append] at hm3
  rw [win_val res 5 (by norm_num), win_val res 10 (by norm_num)] at hval3
  refine RL.congr (s' := mkS sf3 (mpl.base 9 + BitVec.ofNat 64 148) sf3.regs.regs SP sf3.pstate sf3.mem
    sf3.vregs.regs) (by rw [← hpc3, ← hsp3]; rfl) ?_
  have K3 := kept_trans hk3 (kept_upd (kept_upd (kept_upd K2 (by decide)) (by decide)) (by decide))
  have g21 : sf3.regs.regs 21#5 = SP := (K3 21#5 (by decide) (by decide)).trans h21
  have g22 : sf3.regs.regs 22#5 = SP + BitVec.ofNat 64 288 := (K3 22#5 (by decide) (by decide)).trans h22
  -- 148: add x8, x22, #80
  refine RL.mk hrun3 (f09_148 hP) ?_
  rw [ex_add_gpr_gpr 8#5 22#5 (by decide) (by decide), z12 _ (by norm_num), pc_add, g22]
  -- 152: add x0, x21, #80
  refine RL.mk hrun3 (f09_152 hP) ?_
  rw [ex_add_gpr_gpr 0#5 21#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 156: add x1, x21, #120
  refine RL.mk hrun3 (f09_156 hP) ?_
  rw [ex_add_gpr_gpr 1#5 21#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 160: bl mul (Z * T)
  refine call_win hP hM (off := 160) (a := SP) (b := SP + BitVec.ofNat 64 288) (A := wordsOf res 0 20)
    (B := [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19])
    (F := cellsFrom (SP + BitVec.ofNat 64 160)
      [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗ F)
    10 15 10 (by norm_num) (by simp [wordsOf_length]) (by simp) hrun3 (f09_160 hP) halSP
    (by simp [upd_apply]) (by simp [upd_apply, g21]) (by simp [upd_apply, g21])
    hm3 (win_bnd res 10 (by norm_num) b2 (by norm_num))
    (win_bnd res 15 (by norm_num) b3 (by norm_num)) ?_
  intro sf4 t0 t1 t2 t3 t4 hrun4 hpc4 hsp4 hk4 hv4 hm4 hb4 hval4
  simp only [List.take, List.drop, List.cons_append, List.nil_append] at hm4
  rw [win_val res 10 (by norm_num), win_val res 15 (by norm_num)] at hval4
  refine RL.congr (s' := mkS sf4 (mpl.base 9 + BitVec.ofNat 64 164) sf4.regs.regs SP sf4.pstate sf4.mem
    sf4.vregs.regs) (by rw [← hpc4, ← hsp4]; rfl) ?_
  have K4 := kept_trans hk4 (kept_upd (kept_upd (kept_upd K3 (by decide)) (by decide)) (by decide))
  have g20 : (sf4.regs.regs 20#5).truncate 32 = BitVec.ofNat 32 n := by
    rw [K4 20#5 (by decide) (by decide)]; exact h20
  have g29 : sf4.regs.regs 29#5 = SP + BitVec.ofNat 64 448 := (K4 29#5 (by decide) (by decide)).trans h29
  have hV : VRegFile.calleeSaved ⟨sf4.vregs.regs⟩ = VRegFile.calleeSaved ⟨v⟩ :=
    hv4.trans (hv3.trans (hv2.trans hv1))
  have hc : sf4.mem ⊨ cellsFrom (SP + BitVec.ofNat 64 160)
      [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗
      cellsFrom (SP + BitVec.ofNat 64 288)
        [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, q15, q16, q17, q18, q19] ∗
      (cellsFrom SP (wordsOf res 0 20) ∗ memRegion (SP - BitVec.ofNat 64 400) 400 ∗ F) :=
    Satisfies.of_eq hm4
  clear hm1 hm2 hm3 hm4
  -- 164: ldp q0, q1, [x29, #-96]
  refine RL_ldpq2 29#5 0#5 1#5 (by decide) _ 8 y3 y4 t0 t1 hrun4 (f09_164 hP)
    (by rw [g29]; exact addr2 SP 448 _ 288 (8 * 8) (by norm_num)) (by simp) hc rfl rfl rfl rfl ?_
  rw [pc_add]
  -- 168: subs w20, w20, #1
  refine RL_subs1 20#5 20#5 (by decide) (by decide) n hn1 hn2 hrun4 (f09_168 hP) g20 ?_
  intro ps' hz
  rw [pc_add]
  -- 172: ldr q2, [x29, #-64]
  refine RL_ldurq2 29#5 2#5 (by decide) _ 12 t2 t3 hrun4 (f09_172 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, g29]
        exact addr2 SP 448 _ 288 (8 * 12) (by norm_num)) (by simp) hc rfl rfl ?_
  rw [pc_add]
  -- 176: ldur x8, [x29, #-48]
  refine RL_ldur2 8#5 29#5 (by decide) (by decide) _ 14 t4 hrun4 (f09_176 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, g29]
        exact addr2 SP 448 _ 288 (8 * 14) (by norm_num)) hc rfl ?_
  rw [pc_add]
  -- 180: stp q0, q1, [sp, #224]
  refine RL_stpq_sp 0#5 1#5 _ 8 y3 y4 t0 t1 hrun4 (f09_180 hP) halSP
    (addr1 SP 224 160 (8 * 8) (by norm_num)) (by simp) hc (by simp [upd_apply]) (by simp [upd_apply]) ?_
  intro m5 hc5
  rw [pc_add]
  simp only [List.set_cons_succ, List.set_cons_zero] at hc5
  -- 184: ldp q0, q1, [x29, #-160]
  refine RL_ldpq2 29#5 0#5 1#5 (by decide) _ 0 x0 x1 x2 x3 hrun4 (f09_184 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, g29]
        exact addr2 SP 448 _ 288 (8 * 0) (by norm_num)) (by simp) hc5 rfl rfl rfl rfl ?_
  rw [pc_add]
  -- 188: str q2, [sp, #256]
  refine RL_strq_sp 2#5 _ 12 t2 t3 hrun4 (f09_188 hP) halSP
    (addr1 SP 256 160 (8 * 12) (by norm_num)) (by simp) hc5 (by simp [upd_apply]) ?_
  intro m6 hc6
  rw [pc_add]
  simp only [List.set_cons_succ, List.set_cons_zero] at hc6
  -- 192: str x8, [sp, #272]
  refine RL_str_sp 8#5 (by decide) _ 14 hrun4 (f09_192 hP) halSP
    (addr1 SP 272 160 (8 * 14) (by norm_num)) (by simp) hc6 ?_
  intro m7 hc7
  rw [pc_add]
  simp only [List.set_cons_succ, List.set_cons_zero, upd_apply] at hc7
  -- 196: stp q0, q1, [sp, #160]
  refine RL_stpq_sp 0#5 1#5 _ 0 x0 x1 x2 x3 hrun4 (f09_196 hP) halSP
    (addr1 SP 160 160 (8 * 0) (by norm_num)) (by simp) hc7 (by simp [upd_apply]) (by simp [upd_apply]) ?_
  intro m8 hc8
  rw [pc_add]
  simp only [List.set_cons_succ, List.set_cons_zero] at hc8
  -- 200: ldp q2, q0, [x29, #-128]
  refine RL_ldpq2 29#5 2#5 0#5 (by decide) _ 4 x4 y0 y1 y2 hrun4 (f09_200 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, g29]
        exact addr2 SP 448 _ 288 (8 * 4) (by norm_num)) (by simp) hc8 rfl rfl rfl rfl ?_
  rw [pc_add]
  -- 204: stp q2, q0, [sp, #192]
  refine RL_stpq_sp 2#5 0#5 _ 4 x4 y0 y1 y2 hrun4 (f09_204 hP) halSP
    (addr1 SP 192 160 (8 * 4) (by norm_num)) (by simp) hc8 (by simp [upd_apply]) (by simp [upd_apply]) ?_
  intro m9 hc9
  rw [pc_add]
  simp only [List.set_cons_succ, List.set_cons_zero] at hc9
  -- 208: b.ne 104
  refine RL.mk hrun4 (f09_208 hP) ?_
  rw [ex_bcond]
  refine RL_pc_congr (pc' := mpl.base 9 + BitVec.ofNat 64 (if n = 1 then 212 else 104)) ?_ ?_
  · simp only [ConditionHolds, hz]
    by_cases h1 : n = 1
    · simp only [h1, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true, pc_add]
    · simp only [h1, decide_false, Bool.not_false, if_true, if_false, pc_add]
      rfl
  obtain ⟨ha, hb, hc'⟩ := iter_vals res _ _ _ hD1 _ _ _ hval2 hval3 hval4
  refine hK sf4 _ ps' m9 _ (wordsOf res 0 20) x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 t0 t1 t2 t3 t4 hrun4 ?_ ?_ ?_
    (wordsOf_length res 20 0) (Satisfies.of_eq hc9) hb2 hb3 hb4 ha hb hc'
  · exact kept_upd20 (kept_upd20 (fun k h1 h2 _ => K4 k h1 h2) (Or.inr rfl)) (Or.inl (by decide))
  · simp [upd_apply]
  · exact cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide)
      (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) hV))))))

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): the prologue (offsets 0–100)

Saves `x29 x30 x28 x22 x21 x20 x19` in the 64 bytes below the entry `sp`, sets `SP = sp - 512`
and `x29 = SP + 448`, copies `(X, Y, Z)` of `self` to `SP + 160`, sets `w20 = k - 1 = 3`,
`x21 = SP`, `x22 = SP + 288`, and arrives at the loop head 104. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

theorem e_pre (SP : BitVec 64) :
    SP + BitVec.ofNat 64 512 + 0xffffffffffffffc0#64 = SP + BitVec.ofNat 64 448 := by
  rw [BitVec.add_assoc]; congr 1

theorem add_ofNat0 (b : BitVec 64) : b + BitVec.ofNat 64 0 = b := by simp

theorem e_sub448 (SP : BitVec 64) : SP + BitVec.ofNat 64 448 - BitVec.ofNat 64 448 = SP := by
  abel

set_option maxHeartbeats 4000000 in
theorem pro {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    {Q : State → Prop} {sb : State} {r : BitVec 5 → BitVec 64} {SP : BitVec 64} {ps : PState}
    {m : Memory} {v : BitVec 5 → BitVec 128} {F : SepProp} {self : BitVec 64}
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 : BitVec 64)
    (X0 X1 X2 X3 X4 Y0 Y1 Y2 Y3 Y4 Z0 Z1 Z2 Z3 Z4 T0 T1 T2 T3 T4 : BitVec 64)
    (hrun : sb.status = .Running) (halSP : SP &&& 0b1111#64 = 0#64)
    (h0 : r 0#5 = self) (h1 : (r 1#5).truncate 32 = 4#32)
    (hm : m ⊨ cellsFrom (SP + BitVec.ofNat 64 448) [w0, w1, w2, w3, w4, w5, w6, w7] ∗
      cellsFrom (SP + BitVec.ofNat 64 160) [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14] ∗
      cellsFrom self [X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Z0, Z1, Z2, Z3, Z4, T0, T1, T2, T3, T4] ∗ F)
    (hK : ∀ (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory) (v' : BitVec 5 → BitVec 128),
      r' 19#5 = r 8#5 → r' 20#5 = BitVec.ofNat 64 3 → r' 21#5 = SP →
      r' 22#5 = SP + BitVec.ofNat 64 288 → r' 29#5 = SP + BitVec.ofNat 64 448 →
      (∀ k : BitVec 5, 23 ≤ k.toNat → k.toNat < 29 → r' k = r k) →
      VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨v⟩ →
      (m' ⊨ cellsFrom (SP + BitVec.ofNat 64 448) [r 29#5, r 30#5, r 28#5, w3, r 22#5, r 21#5, r 20#5, r 19#5] ∗
        cellsFrom (SP + BitVec.ofNat 64 160) [X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Z0, Z1, Z2, Z3, Z4] ∗
        cellsFrom self [X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Z0, Z1, Z2, Z3, Z4, T0, T1, T2, T3, T4] ∗ F) →
      RL mpl (mkS sb (mpl.base 9 + BitVec.ofNat 64 104) r' SP ps' m' v') Q) :
    RL mpl (mkS sb (mpl.base 9 + BitVec.ofNat 64 0) r (SP + BitVec.ofNat 64 512) ps m v) Q := by
  have hal0 : (SP + BitVec.ofNat 64 512) &&& 0b1111#64 = 0#64 := al16_add SP 512 (by norm_num) halSP
  have hal1 : (SP + BitVec.ofNat 64 448) &&& 0b1111#64 = 0#64 := al16_add SP 448 (by norm_num) halSP
  -- 0: stp x29, x30, [sp, #-64]!
  refine RL_stp_pre 29#5 30#5 (by decide) (by decide) _ hrun (f09_0 hP) hal0 (e_pre SP) (by simp) hm ?_
  intro m1 hm1
  simp only [List.set_cons_succ, List.set_cons_zero] at hm1
  rw [pc_add]
  -- 4: str x28, [sp, #16]
  refine RL_str_sp 28#5 (by decide) _ 2 hrun (f09_4 hP) hal1 rfl (by simp) hm1 ?_
  intro m2 hm2
  simp only [List.set_cons_succ, List.set_cons_zero] at hm2
  rw [pc_add]
  -- 8: stp x22, x21, [sp, #32]
  refine RL_stp_sp 22#5 21#5 (by decide) (by decide) _ 4 hrun (f09_8 hP) hal1 rfl (by simp) hm2 ?_
  intro m3 hm3
  simp only [List.set_cons_succ, List.set_cons_zero] at hm3
  rw [pc_add]
  -- 12: stp x20, x19, [sp, #48]
  refine RL_stp_sp 20#5 19#5 (by decide) (by decide) _ 6 hrun (f09_12 hP) hal1 rfl (by simp) hm3 ?_
  intro m4 hm4
  simp only [List.set_cons_succ, List.set_cons_zero] at hm4
  rw [pc_add]
  -- 16: add x29, sp, #0
  refine RL.mk hrun (f09_16 hP) ?_
  rw [ex_add_gpr_sp 29#5 (by decide), z12 _ (by norm_num), pc_add, add_ofNat0]
  -- 20: sub sp, sp, #448
  refine RL.mk hrun (f09_20 hP) ?_
  rw [ex_sub_sp, z12 _ (by norm_num), pc_add, e_sub448]
  have hc : m4 ⊨ cellsFrom (SP + BitVec.ofNat 64 160) [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14] ∗
      cellsFrom self [X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Z0, Z1, Z2, Z3, Z4, T0, T1, T2, T3, T4] ∗
      (cellsFrom (SP + BitVec.ofNat 64 448) [r 29#5, r 30#5, r 28#5, w3, r 22#5, r 21#5, r 20#5, r 19#5] ∗ F) :=
    Satisfies.of_eq hm4
  clear hm1 hm2 hm3 hm4
  -- 24: ldur q0, [x0, #40]
  refine RL_ldurq2 0#5 0#5 (by decide) _ 5 Y0 Y1 hrun (f09_24 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, h0] <;> rfl) (by simp) hc rfl rfl ?_
  rw [pc_add]
  -- 28: ldur q1, [x0, #56]
  refine RL_ldurq2 0#5 1#5 (by decide) _ 7 Y2 Y3 hrun (f09_28 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, h0] <;> rfl) (by simp) hc rfl rfl ?_
  rw [pc_add]
  -- 32: mov x19, x8
  refine RL.mk hrun (f09_32 hP) ?_
  rw [ex_mov 19#5 8#5 (by decide) (by decide), pc_add]
  -- 36: add x8, sp, #160
  refine RL.mk hrun (f09_36 hP) ?_
  rw [ex_add_gpr_sp 8#5 (by decide), z12 _ (by norm_num), pc_add]
  -- 40: ldr x9, [x0, #32]
  refine RL_ldr2 9#5 0#5 (by decide) (by decide) _ 4 X4 hrun (f09_40 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, h0] <;> rfl) hc rfl ?_
  rw [pc_add]
  -- 44: subs w20, w1, #1
  refine RL_subs1 20#5 1#5 (by decide) (by decide) 4 (by norm_num) (by norm_num) hrun (f09_44 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, h1] <;> rfl) ?_
  intro ps1 hz1
  rw [pc_add]
  -- 48: str q0, [x8, #40]
  refine RL_sturq 8#5 0#5 (by decide) _ 5 Y0 Y1 hrun (f09_48 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, ite_true] <;> rfl) (by simp) hc
    (by simp [upd_apply]) ?_
  intro m5 hc5
  simp only [List.set_cons_succ, List.set_cons_zero] at hc5
  rw [pc_add]
  -- 52: str q1, [x8, #56]
  refine RL_sturq 8#5 1#5 (by decide) _ 7 Y2 Y3 hrun (f09_52 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, ite_true] <;> rfl) (by simp) hc5
    (by simp [upd_apply]) ?_
  intro m6 hc6
  simp only [List.set_cons_succ, List.set_cons_zero] at hc6
  rw [pc_add]
  -- 56: ldp q0, q1, [x0, #80]
  refine RL_ldpq2 0#5 0#5 1#5 (by decide) _ 10 Z0 Z1 Z2 Z3 hrun (f09_56 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, h0] <;> rfl) (by simp) hc6
    rfl rfl rfl rfl ?_
  rw [pc_add]
  -- 60: ldr x8, [x0, #112]
  refine RL_ldr2 8#5 0#5 (by decide) (by decide) _ 14 Z4 hrun (f09_60 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, h0] <;> rfl) hc6 rfl ?_
  rw [pc_add]
  -- 64: str x9, [sp, #192]
  refine RL_str_sp 9#5 (by decide) _ 4 hrun (f09_64 hP) halSP
    (addr1 SP 192 160 (8 * 4) (by norm_num)) (by simp) hc6 ?_
  intro m7 hc7
  simp only [List.set_cons_succ, List.set_cons_zero, upd_apply] at hc7
  rw [pc_add]
  -- 68: stp q0, q1, [sp, #240]
  refine RL_stpq_sp 0#5 1#5 _ 10 Z0 Z1 Z2 Z3 hrun (f09_68 hP) halSP
    (addr1 SP 240 160 (8 * 10) (by norm_num)) (by simp) hc7 (by simp [upd_apply]) (by simp [upd_apply]) ?_
  intro m8 hc8
  simp only [List.set_cons_succ, List.set_cons_zero] at hc8
  rw [pc_add]
  -- 72: ldp q0, q1, [x0]
  refine RL_ldpq2 0#5 0#5 1#5 (by decide) _ 0 X0 X1 X2 X3 hrun (f09_72 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, h0] <;> rfl) (by simp) hc8
    rfl rfl rfl rfl ?_
  rw [pc_add]
  -- 76: str x8, [sp, #272]
  refine RL_str_sp 8#5 (by decide) _ 14 hrun (f09_76 hP) halSP
    (addr1 SP 272 160 (8 * 14) (by norm_num)) (by simp) hc8 ?_
  intro m9 hc9
  simp only [List.set_cons_succ, List.set_cons_zero, upd_apply] at hc9
  rw [pc_add]
  -- 80: ldr x8, [x0, #72]
  refine RL_ldr2 8#5 0#5 (by decide) (by decide) _ 9 Y4 hrun (f09_80 hP)
    (by simp (config := { decide := true }) only [upd_apply, ite_false, h0] <;> rfl) hc9 rfl ?_
  rw [pc_add]
  -- 84: stp q0, q1, [sp, #160]
  refine RL_stpq_sp 0#5 1#5 _ 0 X0 X1 X2 X3 hrun (f09_84 hP) halSP
    (addr1 SP 160 160 (8 * 0) (by norm_num)) (by simp) hc9 (by simp [upd_apply]) (by simp [upd_apply]) ?_
  intro m10 hc10
  simp only [List.set_cons_succ, List.set_cons_zero] at hc10
  rw [pc_add]
  -- 88: str x8, [sp, #232]
  refine RL_str_sp 8#5 (by decide) _ 9 hrun (f09_88 hP) halSP
    (addr1 SP 232 160 (8 * 9) (by norm_num)) (by simp) hc10 ?_
  intro m11 hc11
  simp only [List.set_cons_succ, List.set_cons_zero, upd_apply] at hc11
  rw [pc_add]
  -- 92: b.eq 212 (not taken: w20 = 3)
  refine RL.mk hrun (f09_92 hP) ?_
  rw [ex_bcond]
  refine RL_pc_congr (pc' := mpl.base 9 + BitVec.ofNat 64 96) ?_ ?_
  · simp only [ConditionHolds, hz1]
    simp only [show (4 = 1) = False by decide, decide_false, Bool.false_eq_true, if_false, pc_add]
  -- 96: add x21, sp, #0
  refine RL.mk hrun (f09_96 hP) ?_
  rw [ex_add_gpr_sp 21#5 (by decide), z12 _ (by norm_num), pc_add, add_ofNat0]
  -- 100: sub x22, x29, #160
  refine RL.mk hrun (f09_100 hP) ?_
  rw [ex_sub_gpr_gpr 22#5 29#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  refine hK _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Satisfies.of_eq hc11)
  · simp [upd_apply]
  · simp [upd_apply]
  · simp [upd_apply]
  · simp (config := { decide := true }) only [upd_apply, ite_false, ite_true]
    exact asub SP 448 160 288 rfl
  · simp (config := { decide := true }) only [upd_apply, ite_false, ite_true]
  · intro k h1 h2
    have n0 : k ≠ 0#5 := by intro e; subst e; simp at h1
    have n1 : k ≠ 8#5 := by intro e; subst e; simp at h1
    have n2 : k ≠ 9#5 := by intro e; subst e; simp at h1
    have n3 : k ≠ 19#5 := by intro e; subst e; simp at h1
    have n4 : k ≠ 20#5 := by intro e; subst e; simp at h1
    have n5 : k ≠ 21#5 := by intro e; subst e; simp at h1
    have n6 : k ≠ 22#5 := by intro e; subst e; simp at h1
    have n7 : k ≠ 29#5 := by intro e; subst e; simp at h2
    simp only [upd_apply, if_neg n0, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6,
      if_neg n7]
  · exact cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) rfl)))

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9): the last doubling and the epilogue (offsets 212–312)

`ProjectivePoint::double` of the point at `SP + 160` into `SP + 288`, the four products
`X·T`, `Y·Z`, `Z·T`, `X·Y` into `out` (`CompletedPoint::as_extended`), the restore of
`x19 x20 x21 x22 x28 x29 x30` and `ret`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 Arm64.Obj

set_option maxHeartbeats 4000000 in
theorem tail {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hD : fnOk dblName (fun _ => projectivePointDoubleSpec)) (hM : fnOk mulName (fun _ => fe51MulSpec))
    {Q : State → Prop} {sb : State} {r : BitVec 5 → BitVec 64} {SP : BitVec 64} {ps : PState}
    {m : Memory} {v : BitVec 5 → BitVec 128} {F : SepProp} {out : BitVec 64} {C : List (BitVec 64)}
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : BitVec 64)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 o16 o17 o18 o19 : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (hrun : sb.status = .Running) (halSP : SP &&& 0b1111#64 = 0#64)
    (h19 : r 19#5 = out) (h29 : r 29#5 = SP + BitVec.ofNat 64 448) (hC : C.length = 20)
    (hm : m ⊨ cellsFrom (SP + BitVec.ofNat 64 288) C ∗
      cellsFrom (SP + BitVec.ofNat 64 160) [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗
      memRegion (SP - BitVec.ofNat 64 400) 400 ∗
      cellsFrom out [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19] ∗
      cellsFrom (SP + BitVec.ofNat 64 448) [w0, w1, w2, w3, w4, w5, w6, w7] ∗ F)
    (hbX : B5 p0 p1 p2 p3 p4 (2 ^ 53)) (hbY : B5 p5 p6 p7 p8 p9 (2 ^ 53))
    (hbZ : B5 p10 p11 p12 p13 p14 (2 ^ 54))
    (hK : ∀ (sb' : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory)
        (v' : BitVec 5 → BitVec 128) (C' : List (BitVec 64))
        (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 t0 t1 t2 t3 t4 z0 z1 z2 z3 z4 : BitVec 64),
      sb'.status = .Running →
      r' 19#5 = w7 → r' 20#5 = w6 → r' 21#5 = w5 → r' 22#5 = w4 → r' 28#5 = w2 → r' 29#5 = w0 →
      r' 30#5 = w1 →
      (∀ k : BitVec 5, 23 ≤ k.toNat → k.toNat < 28 → r' k = r k) →
      VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨v⟩ →
      C'.length = 20 →
      (m' ⊨ cellsFrom (SP + BitVec.ofNat 64 448) [w0, w1, w2, w3, w4, w5, w6, w7] ∗
        cellsFrom (SP + BitVec.ofNat 64 288) C' ∗
        cellsFrom out [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4] ∗
        memRegion (SP - BitVec.ofNat 64 400) 400 ∗
        cellsFrom (SP + BitVec.ofNat 64 160) [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗
        F) →
      B5 x0 x1 x2 x3 x4 (2 ^ 52) → B5 y0 y1 y2 y3 y4 (2 ^ 52) → B5 t0 t1 t2 t3 t4 (2 ^ 52) →
      B5 z0 z1 z2 z3 z4 (2 ^ 52) →
      (⟨fe51Val x0 x1 x2 x3 x4 % p25519, fe51Val y0 y1 y2 y3 y4 % p25519,
          fe51Val t0 t1 t2 t3 t4 % p25519, fe51Val z0 z1 z2 z3 z4 % p25519⟩ : EdExtPoint) =
        edAsExtended (edProjDouble (fe51Val p0 p1 p2 p3 p4) (fe51Val p5 p6 p7 p8 p9)
          (fe51Val p10 p11 p12 p13 p14)) →
      RL mpl (mkS sb' w1 r' (SP + BitVec.ofNat 64 448 + 0x0000000000000040#64) ps' m' v') Q) :
    RL mpl (mkS sb (mpl.base 9 + BitVec.ofNat 64 212) r SP ps m v) Q := by
  -- 212: sub x8, x29, #160
  refine RL.mk hrun (f09_212 hP) ?_
  rw [ex_sub_gpr_gpr 8#5 29#5 (by decide) (by decide), z12 _ (by norm_num), pc_add, h29,
    asub SP 448 160 288 rfl]
  -- 216: add x0, sp, #160
  refine RL.mk hrun (f09_216 hP) ?_
  rw [ex_add_gpr_sp 0#5 (by decide), z12 _ (by norm_num), pc_add]
  -- 220: sub x20, x29, #160
  refine RL.mk hrun (f09_220 hP) ?_
  rw [ex_sub_gpr_gpr 20#5 29#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_false, ite_true, h29]
  rw [asub SP 448 160 288 rfl]
  -- 224: bl double
  refine call_dblw hP hD (off := 224) (o := SP + BitVec.ofNat 64 288) (a := SP + BitVec.ofNat 64 160)
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 hrun (f09_224 hP) halSP
    (by simp [upd_apply]) (by simp [upd_apply]) hC hm hbX hbY hbZ ?_
  intro sf1 res hrun1 hpc1 hsp1 hk1 hv1 hm1 hd1
  obtain ⟨hD1, b0, b1, b2, b3⟩ := hd1
  refine RL.congr (s' := mkS sf1 (mpl.base 9 + BitVec.ofNat 64 228) sf1.regs.regs SP sf1.pstate sf1.mem
    sf1.vregs.regs) (by rw [← hpc1, ← hsp1]; rfl) ?_
  have K1 : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → k ≠ 20#5 → sf1.regs.regs k = r k := by
    intro k a b c
    rw [hk1 k a b]
    exact kept_upd20 (i := 20#5) (kept_upd20 (i := 0#5) (kept_upd20 (i := 8#5) (fun _ _ _ _ => rfl)
      (Or.inl (by decide))) (Or.inl (by decide))) (Or.inr rfl) k a b c
  have g19 : sf1.regs.regs 19#5 = out := (K1 19#5 (by decide) (by decide) (by decide)).trans h19
  have g20 : sf1.regs.regs 20#5 = SP + BitVec.ofNat 64 288 := by
    rw [hk1 20#5 (by decide) (by decide)]; simp [upd_apply]
  have g29 : sf1.regs.regs 29#5 = SP + BitVec.ofNat 64 448 :=
    (K1 29#5 (by decide) (by decide) (by decide)).trans h29
  have hc : sf1.mem ⊨ cellsFrom (SP + BitVec.ofNat 64 288) (wordsOf res 0 20) ∗
      cellsFrom out [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19] ∗
      memRegion (SP - BitVec.ofNat 64 400) 400 ∗
      (cellsFrom (SP + BitVec.ofNat 64 448) [w0, w1, w2, w3, w4, w5, w6, w7] ∗
        cellsFrom (SP + BitVec.ofNat 64 160) [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗
        F) := Satisfies.of_eq hm1
  clear hm1
  -- 228: sub x0, x29, #160
  refine RL.mk hrun1 (f09_228 hP) ?_
  rw [ex_sub_gpr_gpr 0#5 29#5 (by decide) (by decide), z12 _ (by norm_num), pc_add, g29,
    asub SP 448 160 288 rfl]
  -- 232: add x1, x20, #120
  refine RL.mk hrun1 (f09_232 hP) ?_
  rw [ex_add_gpr_gpr 1#5 20#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 236: mov x8, x19
  refine RL.mk hrun1 (f09_236 hP) ?_
  rw [ex_mov 8#5 19#5 (by decide) (by decide), pc_add]
  -- 240: bl mul (X * T)
  refine call_win hP hM (off := 240) 0 15 0 (by norm_num) (by simp [wordsOf_length]) (by simp) hrun1
    (f09_240 hP) halSP (by simp [upd_apply, g19]) (by simp [upd_apply])
    (by simp [upd_apply, g20, BitVec.add_assoc]) hc (win_bnd res 0 (by norm_num) b0 (by norm_num))
    (win_bnd res 15 (by norm_num) b3 (by norm_num)) ?_
  intro sf2 x0 x1 x2 x3 x4 hrun2 hpc2 hsp2 hk2 hv2 hm2 hb2 hval2
  simp only [List.take, List.drop, List.cons_append, List.nil_append] at hm2
  rw [win_val res 0 (by norm_num), win_val res 15 (by norm_num)] at hval2
  refine RL.congr (s' := mkS sf2 (mpl.base 9 + BitVec.ofNat 64 244) sf2.regs.regs SP sf2.pstate sf2.mem
    sf2.vregs.regs) (by rw [← hpc2, ← hsp2]; rfl) ?_
  have K2 := kept_trans hk2 (kept_upd (kept_upd (kept_upd (fun k a b => rfl) (by decide)) (by decide))
    (by decide))
  have g19b : sf2.regs.regs 19#5 = out := (K2 19#5 (by decide) (by decide)).trans g19
  have g20b : sf2.regs.regs 20#5 = SP + BitVec.ofNat 64 288 := (K2 20#5 (by decide) (by decide)).trans g20
  -- 244: add x8, x19, #40
  refine RL.mk hrun2 (f09_244 hP) ?_
  rw [ex_add_gpr_gpr 8#5 19#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 248: add x0, x20, #40
  refine RL.mk hrun2 (f09_248 hP) ?_
  rw [ex_add_gpr_gpr 0#5 20#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 252: add x1, x20, #80
  refine RL.mk hrun2 (f09_252 hP) ?_
  rw [ex_add_gpr_gpr 1#5 20#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 256: bl mul (Y * Z)
  refine call_win hP hM (off := 256) 5 10 5 (by norm_num) (by simp [wordsOf_length]) (by simp) hrun2
    (f09_256 hP) halSP (by simp [upd_apply, g19b]) (by simp [upd_apply, g20b, BitVec.add_assoc])
    (by simp [upd_apply, g20b, BitVec.add_assoc]) hm2 (win_bnd res 5 (by norm_num) b1 (by norm_num))
    (win_bnd res 10 (by norm_num) b2 (by norm_num)) ?_
  intro sf3 y0 y1 y2 y3 y4 hrun3 hpc3 hsp3 hk3 hv3 hm3 hb3 hval3
  simp only [List.take, List.drop, List.cons_append, List.nil_append] at hm3
  rw [win_val res 5 (by norm_num), win_val res 10 (by norm_num)] at hval3
  refine RL.congr (s' := mkS sf3 (mpl.base 9 + BitVec.ofNat 64 260) sf3.regs.regs SP sf3.pstate sf3.mem
    sf3.vregs.regs) (by rw [← hpc3, ← hsp3]; rfl) ?_
  have K3 := kept_trans hk3 (kept_upd (kept_upd (kept_upd K2 (by decide)) (by decide)) (by decide))
  have g19c : sf3.regs.regs 19#5 = out := (K3 19#5 (by decide) (by decide)).trans g19
  have g20c : sf3.regs.regs 20#5 = SP + BitVec.ofNat 64 288 := (K3 20#5 (by decide) (by decide)).trans g20
  -- 260: add x8, x19, #80
  refine RL.mk hrun3 (f09_260 hP) ?_
  rw [ex_add_gpr_gpr 8#5 19#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 264: add x0, x20, #80
  refine RL.mk hrun3 (f09_264 hP) ?_
  rw [ex_add_gpr_gpr 0#5 20#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 268: add x1, x20, #120
  refine RL.mk hrun3 (f09_268 hP) ?_
  rw [ex_add_gpr_gpr 1#5 20#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 272: bl mul (Z * T)
  refine call_win hP hM (off := 272) 10 15 10 (by norm_num) (by simp [wordsOf_length]) (by simp) hrun3
    (f09_272 hP) halSP (by simp [upd_apply, g19c]) (by simp [upd_apply, g20c, BitVec.add_assoc])
    (by simp [upd_apply, g20c, BitVec.add_assoc]) hm3 (win_bnd res 10 (by norm_num) b2 (by norm_num))
    (win_bnd res 15 (by norm_num) b3 (by norm_num)) ?_
  intro sf4 t0 t1 t2 t3 t4 hrun4 hpc4 hsp4 hk4 hv4 hm4 hb4 hval4
  simp only [List.take, List.drop, List.cons_append, List.nil_append] at hm4
  rw [win_val res 10 (by norm_num), win_val res 15 (by norm_num)] at hval4
  refine RL.congr (s' := mkS sf4 (mpl.base 9 + BitVec.ofNat 64 276) sf4.regs.regs SP sf4.pstate sf4.mem
    sf4.vregs.regs) (by rw [← hpc4, ← hsp4]; rfl) ?_
  have K4 := kept_trans hk4 (kept_upd (kept_upd (kept_upd K3 (by decide)) (by decide)) (by decide))
  have g19d : sf4.regs.regs 19#5 = out := (K4 19#5 (by decide) (by decide)).trans g19
  have g20d : sf4.regs.regs 20#5 = SP + BitVec.ofNat 64 288 := (K4 20#5 (by decide) (by decide)).trans g20
  have g29d : sf4.regs.regs 29#5 = SP + BitVec.ofNat 64 448 := (K4 29#5 (by decide) (by decide)).trans g29
  -- 276: add x8, x19, #120
  refine RL.mk hrun4 (f09_276 hP) ?_
  rw [ex_add_gpr_gpr 8#5 19#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 280: sub x0, x29, #160
  refine RL.mk hrun4 (f09_280 hP) ?_
  rw [ex_sub_gpr_gpr 0#5 29#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 284: add x1, x20, #40
  refine RL.mk hrun4 (f09_284 hP) ?_
  rw [ex_add_gpr_gpr 1#5 20#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  -- 288: bl mul (X * Y)
  refine call_win hP hM (off := 288) 0 5 15 (by norm_num) (by simp [wordsOf_length]) (by simp) hrun4
    (f09_288 hP) halSP (by simp [upd_apply, g19d])
    (by simp (config := { decide := true }) only [upd_apply, ite_false, ite_true, g29d]
        rw [asub SP 448 160 288 rfl]; simp)
    (by simp [upd_apply, g20d, BitVec.add_assoc]) hm4 (win_bnd res 0 (by norm_num) b0 (by norm_num))
    (win_bnd res 5 (by norm_num) b1 (by norm_num)) ?_
  intro sf5 z0 z1 z2 z3 z4 hrun5 hpc5 hsp5 hk5 hv5 hm5 hb5 hval5
  simp only [List.take, List.drop, List.cons_append, List.nil_append] at hm5
  rw [win_val res 0 (by norm_num), win_val res 5 (by norm_num)] at hval5
  refine RL.congr (s' := mkS sf5 (mpl.base 9 + BitVec.ofNat 64 292) sf5.regs.regs SP sf5.pstate sf5.mem
    sf5.vregs.regs) (by rw [← hpc5, ← hsp5]; rfl) ?_
  have K5 := kept_trans hk5 (kept_upd (kept_upd (kept_upd K4 (by decide)) (by decide)) (by decide))
  have hc5 : sf5.mem ⊨ cellsFrom (SP + BitVec.ofNat 64 448) [w0, w1, w2, w3, w4, w5, w6, w7] ∗
      (cellsFrom (SP + BitVec.ofNat 64 288) (wordsOf res 0 20) ∗
        cellsFrom out [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4] ∗
        memRegion (SP - BitVec.ofNat 64 400) 400 ∗
        (cellsFrom (SP + BitVec.ofNat 64 160) [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] ∗
          F)) := Satisfies.of_eq hm5
  have hal1 : (SP + BitVec.ofNat 64 448) &&& 0b1111#64 = 0#64 := al16_add SP 448 (by norm_num) halSP
  -- 292: add sp, sp, #448
  refine RL.mk hrun5 (f09_292 hP) ?_
  rw [ex_add_sp, z12 _ (by norm_num), pc_add]
  -- 296: ldp x20, x19, [sp, #48]
  refine RL_ldp_sp 20#5 19#5 (by decide) (by decide) _ 6 w6 w7 hrun5 (f09_296 hP) hal1 rfl hc5 rfl rfl ?_
  rw [pc_add]
  -- 300: ldr x28, [sp, #16]
  refine RL_ldr_sp 28#5 (by decide) _ 2 w2 hrun5 (f09_300 hP) hal1 rfl hc5 rfl ?_
  rw [pc_add]
  -- 304: ldp x22, x21, [sp, #32]
  refine RL_ldp_sp 22#5 21#5 (by decide) (by decide) _ 4 w4 w5 hrun5 (f09_304 hP) hal1 rfl hc5 rfl rfl ?_
  rw [pc_add]
  -- 308: ldp x29, x30, [sp], #64
  refine RL_ldp_post 29#5 30#5 (by decide) (by decide) _ w0 w1 hrun5 (f09_308 hP) hal1 hc5 rfl rfl ?_
  rw [pc_add]
  -- 312: ret
  refine RL.mk hrun5 (f09_312 hP) ?_
  rw [ex_ret]
  refine RL_pc_congr (pc' := w1) (by simp [upd_apply]) ?_
  refine hK sf5 _ _ _ _ (wordsOf res 0 20) x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 t0 t1 t2 t3 t4 z0 z1 z2 z3 z4
    hrun5 (by simp [upd_apply]) (by simp [upd_apply]) (by simp [upd_apply]) (by simp [upd_apply])
    (by simp [upd_apply]) (by simp [upd_apply]) (by simp [upd_apply]) ?_
    (hv5.trans (hv4.trans (hv3.trans (hv2.trans hv1)))) (wordsOf_length res 20 0) hc5 hb2 hb3 hb4 hb5
    (final_vals res _ _ _ hD1 _ _ _ _ hval2 hval3 hval4 hval5)
  intro k h1 h2
  have n19 : k ≠ 19#5 := by intro e; subst e; simp at h1
  have n20 : k ≠ 20#5 := by intro e; subst e; simp at h1
  have n21 : k ≠ 21#5 := by intro e; subst e; simp at h1
  have n22 : k ≠ 22#5 := by intro e; subst e; simp at h1
  have n28 : k ≠ 28#5 := by intro e; subst e; simp at h2
  have n29 : k ≠ 29#5 := by intro e; subst e; simp at h2
  have n30 : k ≠ 30#5 := by intro e; subst e; simp at h2
  simp only [upd_apply, if_neg n19, if_neg n20, if_neg n21, if_neg n22, if_neg n28, if_neg n29,
    if_neg n30]
  rw [K5 k (by omega) (by omega)]
  exact K1 k (by omega) (by omega) n20

end X25519Dalek.EMulP
end

section
/-! # `EdwardsPoint::mul_by_pow_2` (block 9, `k = 4`): the contract

The frame `SP = sp - 512` is split into the `CompletedPoint` (`SP`), the `ProjectivePoint`
(`SP + 160`), an unused word (`SP + 280`), the products (`SP + 288`) and the saved registers
(`SP + 448`); the prologue, three loop iterations and the tail are composed. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

theorem sat_split {m : Memory} {a c : BitVec 64} {n k : Nat} {F : SepProp}
    (h : m ⊨ memRegion a (n + k) ∗ F) (hnk : n + k < 2 ^ 64) (hc : a + BitVec.ofNat 64 n = c) :
    m ⊨ memRegion a n ∗ memRegion c k ∗ F := by
  have := sat_sep_mono h (memRegion_split a n k hnk)
  rw [sepConj_assoc, hc] at this
  exact this

theorem sat_cells {m : Memory} {a : BitVec 64} {k : Nat} {F : SepProp}
    (h : m ⊨ memRegion a (8 * k) ∗ F) (hk : 8 * k < 2 ^ 64) :
    ∃ bs : List (BitVec 8), m ⊨ cellsFrom a (wordsOf bs 0 k) ∗ F := by
  have h3 := sat_sep_mono h (memRegion_entails_bytes a (8 * k) hk)
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨bs, h3⟩ := h3
  rw [sepConj_assoc, sat_pure_sep] at h3
  obtain ⟨hl, h3⟩ := h3
  rw [bytes_eq_cells a bs k hl] at h3
  exact ⟨bs, h3⟩

theorem sat_merge {m : Memory} {a b : BitVec 64} {n k : Nat} {F : SepProp}
    (h : m ⊨ memRegion a n ∗ memRegion b k ∗ F) (hb : b = a + BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) : m ⊨ memRegion a (n + k) ∗ F := by
  rw [← sepConj_assoc] at h
  exact sat_sep_mono h (memRegion_merge a b n k hb hn hk)

theorem sat_cells_region {m : Memory} {a : BitVec 64} {l : List (BitVec 64)} {k : Nat} {F : SepProp}
    (h : m ⊨ cellsFrom a l ∗ F) (hl : l.length = k) (hk : 8 * k < 2 ^ 64) :
    m ⊨ memRegion a (8 * k) ∗ F := by
  have := sat_sep_mono h (cellsFrom_entails_memRegion a l (by rw [hl]; exact hk))
  rw [hl] at this
  exact this

theorem sub_add_lit (SP : BitVec 64) (a b c : Nat) (h : c + a = b) :
    SP + BitVec.ofNat 64 c = SP - BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  subst h; rw [BitVec.ofNat_add]; abel

theorem rearr_init {m : Memory} {V Qc G P C MR S O R : SepProp}
    (h : m ⊨ V ∗ Qc ∗ G ∗ P ∗ C ∗ MR ∗ (S ∗ O ∗ R)) : m ⊨ V ∗ P ∗ S ∗ (Qc ∗ C ∗ MR ∗ (G ∗ O ∗ R)) :=
  Satisfies.of_eq h

theorem rearr_pro_loop {m : Memory} {V P S Qc C MR Rest : SepProp}
    (h : m ⊨ V ∗ P ∗ S ∗ (Qc ∗ C ∗ MR ∗ Rest)) : m ⊨ C ∗ P ∗ MR ∗ Qc ∗ (V ∗ S ∗ Rest) :=
  Satisfies.of_eq h

theorem rearr_loop_tail {m : Memory} {C P MR Qc V S G O R : SepProp}
    (h : m ⊨ C ∗ P ∗ MR ∗ Qc ∗ (V ∗ S ∗ (G ∗ O ∗ R))) : m ⊨ Qc ∗ P ∗ MR ∗ O ∗ V ∗ (C ∗ S ∗ G ∗ R) :=
  Satisfies.of_eq h

theorem rearr_final {m : Memory} {V Qc O MR P C S G R : SepProp}
    (h : m ⊨ V ∗ Qc ∗ O ∗ MR ∗ P ∗ (C ∗ S ∗ G ∗ R)) : m ⊨ MR ∗ C ∗ P ∗ G ∗ Qc ∗ V ∗ (S ∗ O ∗ R) :=
  Satisfies.of_eq h

/-- The frame cells back into the 912-byte stack frame. -/
theorem frame_merge {m : Memory} {SP : BitVec 64} {V Qc P C G : List (BitVec 64)} {X : SepProp}
    (hV : V.length = 8) (hQ : Qc.length = 20) (hP : P.length = 15) (hC : C.length = 20)
    (hG : G.length = 1)
    (h : m ⊨ memRegion (SP - BitVec.ofNat 64 400) 400 ∗ cellsFrom SP C ∗
      cellsFrom (SP + BitVec.ofNat 64 160) P ∗ cellsFrom (SP + BitVec.ofNat 64 280) G ∗
      cellsFrom (SP + BitVec.ofNat 64 288) Qc ∗ cellsFrom (SP + BitVec.ofNat 64 448) V ∗ X) :
    m ⊨ memRegion (SP - BitVec.ofNat 64 400) 912 ∗ X := by
  have e0 : SP = SP - BitVec.ofNat 64 400 + BitVec.ofNat 64 400 := by abel
  rw [sepConj_left_comm] at h
  have h1 := sat_cells_region h hC (by norm_num)
  rw [sepConj_left_comm] at h1
  have h2 := sat_merge h1 e0 (by norm_num) (by norm_num)
  rw [sepConj_left_comm] at h2
  have h3 := sat_cells_region h2 hP (by norm_num)
  rw [sepConj_left_comm] at h3
  have h4 := sat_merge h3 (sub_add_lit SP 400 (400 + 8 * 20) 160 rfl) (by norm_num) (by norm_num)
  rw [sepConj_left_comm] at h4
  have h5 := sat_cells_region h4 hG (by norm_num)
  rw [sepConj_left_comm] at h5
  have h6 := sat_merge h5 (sub_add_lit SP 400 (400 + 8 * 20 + 8 * 15) 280 rfl) (by norm_num) (by norm_num)
  rw [sepConj_left_comm] at h6
  have h7 := sat_cells_region h6 hQ (by norm_num)
  rw [sepConj_left_comm] at h7
  have h8 := sat_merge h7 (sub_add_lit SP 400 (400 + 8 * 20 + 8 * 15 + 8 * 1) 288 rfl) (by norm_num)
    (by norm_num)
  rw [sepConj_left_comm] at h8
  have h9 := sat_cells_region h8 hV (by norm_num)
  rw [sepConj_left_comm] at h9
  have h10 := sat_merge h9 (sub_add_lit SP 400 (400 + 8 * 20 + 8 * 15 + 8 * 1 + 8 * 20) 448 rfl)
    (by norm_num) (by norm_num)
  exact h10

theorem post_intro {m : Memory} {A B R : SepProp} {out : BitVec 64} {res : List (BitVec 8)}
    {P : List (BitVec 8) → Prop} (h : m ⊨ A ∗ B ∗ (out ↦ₛ res) ∗ R) (hp : P res) :
    m ⊨ (A ∗ B ∗ ∃∗ r, (out ↦ₛ r) ∗ ⌜P r⌝) ∗ R := by
  have e : ((A ∗ B ∗ ∃∗ r, (out ↦ₛ r) ∗ ⌜P r⌝) ∗ R) = ((∃∗ r, (out ↦ₛ r) ∗ ⌜P r⌝) ∗ (A ∗ B ∗ R)) := by
    ac_rfl
  rw [e, sepExists_sepConj, sat_sepExists]
  refine ⟨res, ?_⟩
  have e2 : (((out ↦ₛ res) ∗ ⌜P res⌝) ∗ (A ∗ B ∗ R)) = (⌜P res⌝ ∗ (A ∗ B ∗ (out ↦ₛ res) ∗ R)) := by
    ac_rfl
  rw [e2, sat_pure_sep]
  exact ⟨hp, h⟩

theorem words20_ex (bs : List (BitVec 8)) : ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17
    a18 a19 : BitVec 64, wordsOf bs 0 20 =
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19] :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem words15_ex (bs : List (BitVec 8)) : ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : BitVec 64,
    wordsOf bs 0 15 = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14] :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem words8_ex (bs : List (BitVec 8)) : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64,
    wordsOf bs 0 8 = [a0, a1, a2, a3, a4, a5, a6, a7] :=
  ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- Facts on the words of a 160-byte buffer: field elements `j = 0, 1, 2, 3`. -/
theorem self_words {bs : List (BitVec 8)} {X0 X1 X2 X3 X4 Y0 Y1 Y2 Y3 Y4 Z0 Z1 Z2 Z3 Z4 T0 T1 T2 T3 T4 : BitVec 64}
    (h : wordsOf bs 0 20 = [X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Z0, Z1, Z2, Z3, Z4, T0, T1, T2, T3, T4]) :
    fe51ValAt bs 0 = fe51Val X0 X1 X2 X3 X4 ∧ fe51ValAt bs 40 = fe51Val Y0 Y1 Y2 Y3 Y4 ∧
      fe51ValAt bs 80 = fe51Val Z0 Z1 Z2 Z3 Z4 := by
  have a := win_val bs 0 (by norm_num)
  have b := win_val bs 5 (by norm_num)
  have c := win_val bs 10 (by norm_num)
  rw [h] at a b c
  exact ⟨a.symm, b.symm, c.symm⟩

theorem self_bnd {bs : List (BitVec 8)} {X0 X1 X2 X3 X4 Y0 Y1 Y2 Y3 Y4 Z0 Z1 Z2 Z3 Z4 T0 T1 T2 T3 T4 : BitVec 64}
    (h : wordsOf bs 0 20 = [X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Z0, Z1, Z2, Z3, Z4, T0, T1, T2, T3, T4])
    (hb : fe51Point4Bounded bs (2 ^ 53)) :
    B5 X0 X1 X2 X3 X4 (2 ^ 53) ∧ B5 Y0 Y1 Y2 Y3 Y4 (2 ^ 53) ∧ B5 Z0 Z1 Z2 Z3 Z4 (2 ^ 54) := by
  obtain ⟨_, b0, b1, b2, _⟩ := hb
  have a := win_bnd bs 0 (by norm_num) b0 le_rfl
  have b := win_bnd bs 5 (by norm_num) b1 le_rfl
  have c := win_bnd bs 10 (by norm_num) b2 (B' := 2 ^ 54) (by norm_num)
  rw [h] at a b c
  exact ⟨a, b, c⟩

theorem out_post (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 t0 t1 t2 t3 t4 z0 z1 z2 z3 z4 : BitVec 64)
    (hx : B5 x0 x1 x2 x3 x4 (2 ^ 52)) (hy : B5 y0 y1 y2 y3 y4 (2 ^ 52))
    (ht : B5 t0 t1 t2 t3 t4 (2 ^ 52)) (hz : B5 z0 z1 z2 z3 z4 (2 ^ 52)) :
    fe51Point4Bounded
      ([x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4].flatMap unpack64)
      (2 ^ 52) ∧
    edExtOfBytes ([x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4].flatMap unpack64) =
      ⟨fe51Val x0 x1 x2 x3 x4 % p25519, fe51Val y0 y1 y2 y3 y4 % p25519,
        fe51Val t0 t1 t2 t3 t4 % p25519, fe51Val z0 z1 z2 z3 z4 % p25519⟩ := by
  have f0 := flat_at [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4] 0
    (by simp) (2 ^ 52)
  have f1 := flat_at [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4] 5
    (by simp) (2 ^ 52)
  have f2 := flat_at [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4] 10
    (by simp) (2 ^ 52)
  have f3 := flat_at [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4] 15
    (by simp) (2 ^ 52)
  refine ⟨⟨by rw [flatMap_unpack64_length]; rfl, f0.1.mpr hx, f1.1.mpr hy, f2.1.mpr ht, f3.1.mpr hz⟩, ?_⟩
  have e0 : fe51ValAt ([x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4].flatMap
    unpack64) 0 = fe51Val x0 x1 x2 x3 x4 := f0.2
  have e1 : fe51ValAt ([x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4].flatMap
    unpack64) 40 = fe51Val y0 y1 y2 y3 y4 := f1.2
  have e2 : fe51ValAt ([x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4].flatMap
    unpack64) 80 = fe51Val t0 t1 t2 t3 t4 := f2.2
  have e3 : fe51ValAt ([x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, t0, t1, t2, t3, t4, z0, z1, z2, z3, z4].flatMap
    unpack64) 120 = fe51Val z0 z1 z2 z3 z4 := f3.2
  simp only [edExtOfBytes, e0, e1, e2, e3]

set_option maxHeartbeats 4000000 in
theorem mulp_ok (hD : fnOk dblName (fun _ => projectivePointDoubleSpec))
    (hM : fnOk mulName (fun _ => fe51MulSpec)) :
    fnOk mulpName (fun _ => edwardsPointMulByPow2_4Spec) := by
  refine ⟨9, 0, mulp_lookup, fun mpl hP => ?_⟩
  rintro ⟨out, self, k, out_bs, self_bs⟩ R s0 hpc hrun hpre hal hCLp
  have hfa : x25519CliMultiLib.fnAddr mpl mulpName = mpl.base 9 + BitVec.ofNat 64 0 :=
    fnAddr_of_lookup mulp_lookup
  rw [hfa] at hpc
  change s0.mem ⊨ ((⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = self ∧ s0.readReg32 Reg.x1 = k ∧
      out_bs.length = 160 ∧ fe51Point4Bounded self_bs (2 ^ 53) ∧ k = 4#32⌝ ∗
      (self ↦ₛ self_bs) ∗ (out ↦ₛ out_bs) ∗ stackFrame s0 912) ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) ∗ R at hpre
  have h1 := Satisfies.of_eq hpre
    (Q := ⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = self ∧ s0.readReg32 Reg.x1 = k ∧
      out_bs.length = 160 ∧ fe51Point4Bounded self_bs (2 ^ 53) ∧ k = 4#32⌝ ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ stackFrame s0 912 ∗
      ((self ↦ₛ self_bs) ∗ (out ↦ₛ out_bs) ∗ R))
  rw [sat_pure_sep, sat_pure_sep] at h1
  obtain ⟨⟨hx8, hx0, hx1, hlo, hbs, hk4⟩, hCL, h1⟩ := h1
  subst hk4
  clear hpre
  have hls : self_bs.length = 160 := hbs.1
  have hal0 : s0.sp &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
  have halSP : (s0.sp - BitVec.ofNat 64 512) &&& 0b1111#64 = 0#64 :=
    al16_sub _ 512 (by norm_num) (by norm_num) hal0
  generalize hSP : s0.sp - BitVec.ofNat 64 512 = SP at halSP
  have hS0 : s0.sp = SP + BitVec.ofNat 64 512 := by rw [← hSP]; abel
  have hst : stackFrame s0 912 = memRegion (SP - BitVec.ofNat 64 400) (400 + 512) := by
    show memRegion _ _ = _
    rw [hS0, show (BitVec.ofNat 64 912 : BitVec 64) = BitVec.ofNat 64 512 + BitVec.ofNat 64 400 by rfl]
    congr 1; abel
  rw [hst] at h1
  have h2 := sat_split h1 (by norm_num) (show SP - BitVec.ofNat 64 400 + BitVec.ofNat 64 400 = SP by abel)
  rw [sepConj_left_comm] at h2
  have h3 := sat_split (n := 8 * 20) (k := 352) h2 (by norm_num) (rfl : SP + BitVec.ofNat 64 (8 * 20) = SP + BitVec.ofNat 64 160)
  obtain ⟨bsC, h4⟩ := sat_cells h3 (by norm_num)
  rw [sepConj_left_comm] at h4
  have h5 := sat_split (n := 8 * 15) (k := 232) h4 (by norm_num)
    (show SP + BitVec.ofNat 64 160 + BitVec.ofNat 64 (8 * 15) = SP + BitVec.ofNat 64 280 by rw [pc_add])
  obtain ⟨bsP, h6⟩ := sat_cells h5 (by norm_num)
  rw [sepConj_left_comm] at h6
  have h7 := sat_split (n := 8 * 1) (k := 224) h6 (by norm_num)
    (show SP + BitVec.ofNat 64 280 + BitVec.ofNat 64 (8 * 1) = SP + BitVec.ofNat 64 288 by rw [pc_add])
  obtain ⟨bsG, h8⟩ := sat_cells h7 (by norm_num)
  rw [sepConj_left_comm] at h8
  have h9 := sat_split (n := 8 * 20) (k := 64) h8 (by norm_num)
    (show SP + BitVec.ofNat 64 288 + BitVec.ofNat 64 (8 * 20) = SP + BitVec.ofNat 64 448 by rw [pc_add])
  obtain ⟨bsQ, h10⟩ := sat_cells h9 (by norm_num)
  rw [sepConj_left_comm] at h10
  obtain ⟨bsV, h12⟩ := sat_cells (k := 8) h10 (by norm_num)
  clear h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rw [bytes_eq_cells self self_bs 20 (by rw [hls]), bytes_eq_cells out out_bs 20 (by rw [hlo])] at h12
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hV⟩ := words8_ex bsV
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, hPw⟩ := words15_ex bsP
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, hQ⟩ :=
    words20_ex bsQ
  obtain ⟨X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Z0, Z1, Z2, Z3, Z4, T0, T1, T2, T3, T4, hSf⟩ :=
    words20_ex self_bs
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, hO⟩ :=
    words20_ex out_bs
  rw [hV, hPw, hQ, hSf, hO] at h12
  obtain ⟨hvX, hvY, hvZ⟩ := self_words hSf
  obtain ⟨hbX, hbY, hbZ⟩ := self_bnd hSf hbs
  have h8r : s0.regs.regs 8#5 = out := by simpa [readGpr_unfold] using hx8
  have h0r : s0.regs.regs 0#5 = self := by simpa [readGpr_unfold] using hx0
  have h1r : (s0.regs.regs 1#5).truncate 32 = 4#32 := by simpa [State.readReg32, readGpr_unfold] using hx1
  show Reach (bprog mpl 9) s0 _
  refine reach_congr (s' := mkS s0 (mpl.base 9 + BitVec.ofNat 64 0) s0.regs.regs (SP + BitVec.ofNat 64 512)
    s0.pstate s0.mem s0.vregs.regs) (by rw [← hpc, ← hS0]; rfl) ?_
  refine pro hP w0 w1 w2 w3 w4 w5 w6 w7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    X0 X1 X2 X3 X4 Y0 Y1 Y2 Y3 Y4 Z0 Z1 Z2 Z3 Z4 T0 T1 T2 T3 T4 hrun halSP h0r h1r (rearr_init h12) ?_ hCL
  intro r1 ps1 m1 v1 g19 g20 g21 g22 g29 gk gv hm1
  -- three loop iterations
  refine loop_iter hP hD hM 3 (by norm_num) (by norm_num) X0 X1 X2 X3 X4 Y0 Y1 Y2 Y3 Y4 Z0 Z1 Z2 Z3 Z4
    q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 hrun halSP
    (by rw [g20]; rfl) g21 g22 g29 (wordsOf_length _ _ _) (rearr_pro_loop hm1) hbX hbY
    (B5_mono hbZ (by norm_num)) ?_
  intro sb2 r2 ps2 m2 v2 C2 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 hrun2 k2 k20 cv2 hC2 hm2
    ba1 ba2 ba3 va1 va2 va3
  rw [if_neg (by decide)]
  refine loop_iter hP hD hM 2 (by norm_num) (by norm_num) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
    a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 q15 q16 q17 q18 q19 hrun2 halSP
    (by rw [k20]; rfl) ((k2 21#5 (by decide) (by decide) (by decide)).trans g21)
    ((k2 22#5 (by decide) (by decide) (by decide)).trans g22)
    ((k2 29#5 (by decide) (by decide) (by decide)).trans g29) hC2 hm2
    (B5_mono ba1 (by norm_num)) (B5_mono ba2 (by norm_num)) (B5_mono ba3 (by norm_num)) ?_
  intro sb3 r3 ps3 m3 v3 C3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 hrun3 k3 k30 cv3 hC3 hm3
    bb1 bb2 bb3 vb1 vb2 vb3
  rw [if_neg (by decide)]
  refine loop_iter hP hD hM 1 (by norm_num) (by norm_num) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 q15 q16 q17 q18 q19 hrun3 halSP
    (by rw [k30]; rfl) ((k3 21#5 (by decide) (by decide) (by decide)).trans
      ((k2 21#5 (by decide) (by decide) (by decide)).trans g21))
    ((k3 22#5 (by decide) (by decide) (by decide)).trans
      ((k2 22#5 (by decide) (by decide) (by decide)).trans g22))
    ((k3 29#5 (by decide) (by decide) (by decide)).trans
      ((k2 29#5 (by decide) (by decide) (by decide)).trans g29)) hC3 hm3
    (B5_mono bb1 (by norm_num)) (B5_mono bb2 (by norm_num)) (B5_mono bb3 (by norm_num)) ?_
  intro sb4 r4 ps4 m4 v4 C4 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 hrun4 k4 k40 cv4 hC4 hm4
    bc1 bc2 bc3 vc1 vc2 vc3
  rw [if_pos rfl]
  -- the tail
  have k19 : r4 19#5 = out := by
    rw [k4 19#5 (by decide) (by decide) (by decide), k3 19#5 (by decide) (by decide) (by decide),
      k2 19#5 (by decide) (by decide) (by decide), g19, h8r]
  refine tail hP hD hM c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14
    o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 o16 o17 o18 o19
    (s0.regs.regs 29#5) (s0.regs.regs 30#5) (s0.regs.regs 28#5) w3 (s0.regs.regs 22#5)
    (s0.regs.regs 21#5) (s0.regs.regs 20#5) (s0.regs.regs 19#5) hrun4 halSP k19
    ((k4 29#5 (by decide) (by decide) (by decide)).trans ((k3 29#5 (by decide) (by decide) (by decide)).trans
      ((k2 29#5 (by decide) (by decide) (by decide)).trans g29)))
    (by simp) (rearr_loop_tail hm4)
    (B5_mono bc1 (by norm_num)) (B5_mono bc2 (by norm_num)) (B5_mono bc3 (by norm_num)) ?_
  intro sb5 r5 ps5 m5 v5 C5 x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 t0 t1 t2 t3 t4 z0 z1 z2 z3 z4 hrun5
    f19 f20 f21 f22 f28 f29 f30 fk cv5 hC5 hm5 bx by' bt bz hval
  refine RL.done ?_
  have hspS : SP + BitVec.ofNat 64 448 + 0x0000000000000040#64 = s0.sp := by
    rw [hS0, pc_add]
  have hkk : ∀ j : BitVec 5, 23 ≤ j.toNat → j.toNat < 28 → r5 j = s0.regs.regs j := by
    intro j a b
    have n20 : j ≠ 20#5 := by intro e; subst e; simp at a
    rw [fk j a b, k4 j (by omega) (by omega) n20, k3 j (by omega) (by omega) n20,
      k2 j (by omega) (by omega) n20, gk j a (by omega)]
  left
  refine ⟨⟨?_, hspS, hrun5⟩, ⟨hspS, ?_⟩, ?_⟩
  · simp [readGpr_unfold, Reg.lr]
  · simp only [CalleeSavedPreserved, readGpr_unfold, mkS_readGpr]
    simp (config := { decide := true }) only [mkS_regs', ite_false, Reg.fp, f19, f20, f21, f22, f28, f29,
      hkk 23#5 (by decide) (by decide), hkk 24#5 (by decide) (by decide), hkk 25#5 (by decide) (by decide),
      hkk 26#5 (by decide) (by decide), hkk 27#5 (by decide) (by decide), true_and]
    show VRegFile.calleeSaved ⟨v5⟩ = VRegFile.calleeSaved s0.vregs
    exact cv5.trans (cv4.trans (cv3.trans (cv2.trans gv)))
  · obtain ⟨hpb, hpe⟩ := out_post x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 t0 t1 t2 t3 t4 z0 z1 z2 z3 z4 bx by' bt bz
    have E1 : stepP (fe51Val X0 X1 X2 X3 X4) (fe51Val Y0 Y1 Y2 Y3 Y4) (fe51Val Z0 Z1 Z2 Z3 Z4) =
        stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z := by
      show _ = stepP (fe51ValAt self_bs 0 % p25519) (fe51ValAt self_bs 40 % p25519)
        (fe51ValAt self_bs 80 % p25519)
      rw [stepP_mod, hvX, hvY, hvZ]
    rw [E1] at va1 va2 va3
    have E2 : stepP (fe51Val a0 a1 a2 a3 a4) (fe51Val a5 a6 a7 a8 a9) (fe51Val a10 a11 a12 a13 a14) =
        stepP (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).X
          (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).Y
          (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).Z := by
      rw [← stepP_mod (fe51Val a0 a1 a2 a3 a4), va1, va2, va3]
    rw [E2] at vb1 vb2 vb3
    have E3 : stepP (fe51Val b0 b1 b2 b3 b4) (fe51Val b5 b6 b7 b8 b9) (fe51Val b10 b11 b12 b13 b14) =
        stepP (stepP (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).X
          (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).Y
          (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).Z).X
        (stepP (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).X
          (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).Y
          (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).Z).Y
        (stepP (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).X
          (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).Y
          (stepP (edExtOfBytes self_bs).X (edExtOfBytes self_bs).Y (edExtOfBytes self_bs).Z).Z).Z := by
      rw [← stepP_mod (fe51Val b0 b1 b2 b3 b4), vb1, vb2, vb3]
    rw [E3] at vc1 vc2 vc3
    rw [← edProjDouble_mod (fe51Val c0 c1 c2 c3 c4), vc1, vc2, vc3] at hval
    have hfm := frame_merge (by rfl) hC5 (by rfl) hC4 (wordsOf_length _ _ _) (rearr_final hm5)
    rw [← hSf, ← bytes_eq_cells self self_bs 20 (by rw [hls]), cellsFrom_eq_bytes out] at hfm
    simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, edwardsPointMulByPow2_4Spec, stackFrame,
      mkS_sp]
    have hsp912 : SP + BitVec.ofNat 64 448 + 0x0000000000000040#64 - BitVec.ofNat 64 912 =
        SP - BitVec.ofNat 64 400 := by
      rw [pc_add, show (BitVec.ofNat 64 912 : BitVec 64) = BitVec.ofNat 64 (448 + 64) + BitVec.ofNat 64 400
        by rfl]
      abel
    rw [hsp912]
    refine post_intro (Satisfies.of_eq hfm) ⟨hpb, ?_⟩
    rw [hpe, hval]
    rfl

theorem fnOk_edwardsPoint_mul_by_pow_2_four_dev :
    fnOk
      "<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2"
      (fun _ => edwardsPointMulByPow2_4Spec) :=
  mulp_ok fnOk_projectivePoint_double_v2 fnOk_fe51_mul_v2.1

end X25519Dalek.EMulP
end

open X25519Dalek in
theorem solution : fnOk "<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2" (fun _ => edwardsPointMulByPow2_4Spec) := X25519Dalek.EMulP.fnOk_edwardsPoint_mul_by_pow_2_four_dev

