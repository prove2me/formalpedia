-- Prove2me | solution 1 for X25519Dalek.fnOk_projectivePoint_double
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T15:31:56.409356+00:00
-- url     : https://prove2.me/submissions/ffe38b79-7d57-4b72-945a-94c38db3955b

import Mathlib
import Definitions.Def_X25519Dalek_Spec
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Arm64Facts_steps_codeLoaded
import Theorems.Thm_X25519Dalek_fnOk_fe51_pow2k

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
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_omega
  have h4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have h5 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
  have h6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have h7 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
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

namespace X25519Dalek.EDbl

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

end X25519Dalek.EDbl
end

section
/-! # Abstract machine states

Every state inside a block proof is `mkS s0 pc r sp ps m v`: the state `s0` with the program
counter, the general registers, the stack pointer, the flags, the memory and the vector registers
replaced. The instruction evaluators map such states to such states, and these lemmas let `simp`
compute the result without unfolding `State`. -/

set_option autoImplicit false

namespace X25519Dalek.EDbl

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

end X25519Dalek.EDbl
end

section
/-! # Code stays loaded; stepping on abstract states; small stack frames -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

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

end X25519Dalek.EDbl
end

section
/-! # Decoding a relocated cross-block `BL`

Adapted from the sibling batch q445-xd-edwards (`Solutions/X25519DalekEdwards/Reloc.lean`), which
follows the zlib CRC-32 mission's proofs (`ZlibCrc32.Small.RelocBase`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

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

end X25519Dalek.EDbl
end

section
/-! # 128-bit loads and stores, 32-byte buffers as 64-bit cells, stack regions -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

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

end X25519Dalek.EDbl
end

section
/-! # One lemma per instruction shape on abstract states `mkS`

The instructions of the two entry blocks (17 and 18). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

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

theorem ex_ldr64_sp (a : BitVec 5) (ha : a ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr : m.canRead (sp + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (sp + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr, ha,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

end exec

end X25519Dalek.EDbl
end

section
/-! # Small facts shared by the two entry-block proofs -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

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


end X25519Dalek.EDbl
end

section
/-! # `ProjectivePoint::double` (block 7): calling `pow2k` through its published contract

Adapted from the sibling batch q444-xd-field (`G/P22Call.lean`, block 5). The library code stays
loaded across every step by the published `Arm64Facts.steps_codeLoaded`; `RL` is `Reach` under
the hypothesis that the library is loaded in the current memory. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

open Arm64 Arm64.Obj

abbrev p2kName : String := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k"
abbrev dblName : String := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double"

theorem p2k_lookup : lookupBlockSym p2kName x25519CliMultiLib.blocks = some (2, 0) := by
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


/-- `Reach` for block 7, given that the library is loaded in the current memory. -/
def RL (mpl : MultiPlacement) (s : State) (Q : State → Prop) : Prop :=
  x25519CliMultiLib.CodeLoaded mpl s.mem → Reach (bprog mpl 7) s Q

theorem libCL_steps {mpl : MultiPlacement} {p : Program} {s s' : State} (h : Steps p s s')
    (hL : x25519CliMultiLib.CodeLoaded mpl s.mem) : x25519CliMultiLib.CodeLoaded mpl s'.mem :=
  fun i hi => Arm64Facts.steps_codeLoaded h (hL i hi)

theorem RL.mk {mpl : MultiPlacement} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {i : Instr} (hrun : s0.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 7).fetchMem m pc = some i)
    (h : RL mpl (execInstWithSvc (evalSvc (bprog mpl 7).svc) i (mkS s0 pc r sp ps m v)) Q) :
    RL mpl (mkS s0 pc r sp ps m v) Q := by
  intro hL
  have hf' := hf hL
  have hst : Step (bprog mpl 7) (mkS s0 pc r sp ps m v)
      (execInstWithSvc (evalSvc (bprog mpl 7).svc) i (mkS s0 pc r sp ps m v)) := Step.exec hrun hf'
  exact Reach.exec hrun hf' (h (libCL_steps (Steps.step hst (Steps.refl _)) hL))

theorem RL.done {mpl : MultiPlacement} {s : State} {Q : State → Prop} (h : Q s) : RL mpl s Q :=
  fun _ => Reach.done h

theorem RL.congr {mpl : MultiPlacement} {s s' : State} {Q : State → Prop} (h : s' = s)
    (H : RL mpl s' Q) : RL mpl s Q := by subst h; exact H

/-- A call to `pow2k` from block 7 at offset `off`; the callee's 96-byte frame is below `sp`. -/
theorem call_p2k {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hM : fnOk p2kName (fun _ => fe51Pow2kSpec)) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {out a : BitVec 64} {kk : Nat} {A O : List (BitVec 8)} {F : SepProp}
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 7 + BitVec.ofNat 64 off))))
    (hal : sp &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = out) (h0 : r 0#5 = a) (h1 : r 1#5 = BitVec.ofNat 64 kk) (hk1 : 0 < kk) (hk2 : kk < 256)
    (hmem : m ⊨ ((a ↦ₛ A) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 96) 96) ∗ F)
    (hA : fe51LimbsBounded A (2 ^ 54)) (hO : O.length = 40)
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running →
      sf.pc = mpl.base 7 + BitVec.ofNat 64 (off + 4) → sf.sp = sp → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ ((a ↦ₛ A) ∗ (out ↦ₛ res) ∗ memRegion (sp - BitVec.ofNat 64 96) 96) ∗ F) →
      fe51LimbsBounded res (2 ^ 52) →
      fe51ValOfBytes res % p25519 = fpPow (fe51ValOfBytes A % p25519) (2 ^ kk) →
      RL mpl sf Q) :
    RL mpl (mkS sb (mpl.base 7 + BitVec.ofNat 64 off) r sp ps m v) Q := by
  refine RL.mk hrun hf ?_
  rw [ex_bl]
  have epc : mpl.base 7 + BitVec.ofNat 64 off + (mpl.base 2 + BitVec.ofNat 64 0 -
      (mpl.base 7 + BitVec.ofNat 64 off)) = mpl.base 2 + BitVec.ofNat 64 0 := by abel
  rw [epc]
  intro hCL
  obtain ⟨i1, o1, hlk1, hsub⟩ := hM
  rw [p2k_lookup] at hlk1
  obtain ⟨rfl, rfl⟩ : 2 = i1 ∧ 0 = o1 := by simpa using hlk1
  have hfa : x25519CliMultiLib.fnAddr mpl p2kName = mpl.base 2 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, p2k_lookup]
  set s1 := mkS sb (mpl.base 2 + BitVec.ofNat 64 0) (upd r 30#5 (mpl.base 7 + BitVec.ofNat 64 off + 4#64))
    sp ps m v with hs1
  have hCL1 : x25519CliMultiLib.CodeLoaded mpl s1.mem := hCL
  have hpre : s1.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec ((fun _ => fe51Pow2kSpec) mpl) (mpl.base 2))).pre
        (out, a, BitVec.ofNat 32 kk, O, A) s1 ∗ F := by
    have e8 : s1.readReg64 Reg.x8 = out := by simp [hs1, Reg.x8, h8]
    have e0 : s1.readReg64 Reg.x0 = a := by simp [hs1, Reg.x0, h0]
    have e1 : s1.readReg32 Reg.x1 = BitVec.ofNat 32 kk := by
      simp [hs1, Reg.x1, h1, State.readReg32]
    have h10 : s1.mem ⊨ ⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧
        s1.readReg32 Reg.x1 = BitVec.ofNat 32 kk ∧ O.length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧
        0 < (BitVec.ofNat 32 kk).toNat ∧ (BitVec.ofNat 32 kk).toNat < 256⌝ ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝ ∗
        (((a ↦ₛ A) ∗ (out ↦ₛ O) ∗ stackFrame s1 96) ∗ F) := by
      rw [sat_pure_sep, sat_pure_sep]
      refine ⟨⟨e8, e0, e1, hO, hA, ?_, ?_⟩, hCL1, hmem⟩
      · simp only [BitVec.toNat_ofNat]; omega
      · simp only [BitVec.toNat_ofNat]; omega
    show s1.mem ⊨ ((⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧
        s1.readReg32 Reg.x1 = BitVec.ofNat 32 kk ∧ O.length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧
        0 < (BitVec.ofNat 32 kk).toNat ∧ (BitVec.ofNat 32 kk).toNat < 256⌝ ∗
        (a ↦ₛ A) ∗ (out ↦ₛ O) ∗ stackFrame s1 96) ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝) ∗ F
    exact Satisfies.of_eq h10
  obtain ⟨sf, hsteps, hout⟩ := hsub mpl hP (out, a, BitVec.ofNat 32 kk, O, A) F s1 (by simp [hs1, hfa])
    hrun hpre (by simp [hs1, hal]) (hCL1 2 (by decide))
  refine Reach.steps (bsteps_transfer hsteps) ?_
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  rotate_left
  · exact (sat_false hpan).elim
  · exact (sat_false hex).elim
  · exact (sat_false hoom).elim
  have hpc' : sf.pc = mpl.base 7 + BitVec.ofNat 64 (off + 4) := by
    rw [hpcf]; simp [hs1, upd_apply, BitVec.add_assoc, BitVec.ofNat_add]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  have hCLf : x25519CliMultiLib.CodeLoaded mpl sf.mem := libCL_steps hsteps hCL1
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, fe51Pow2kSpec, stackFrame, hsp'] at hpost
  have hp2 := Satisfies.of_eq hpost (Q := (∃∗ res : List (BitVec 8), (out ↦ₛ res) ∗
      ⌜fe51LimbsBounded res (2 ^ 52) ∧ fe51ValOfBytes res % p25519 =
        fpPow (fe51ValOfBytes A % p25519) (2 ^ (BitVec.ofNat 32 kk).toNat)⌝) ∗
      ((a ↦ₛ A) ∗ memRegion (sp - BitVec.ofNat 64 96) 96 ∗ F))
  rw [sepExists_sepConj, sat_sepExists] at hp2
  obtain ⟨res, hp2⟩ := hp2
  have hp3 := Satisfies.of_eq hp2 (Q := ⌜fe51LimbsBounded res (2 ^ 52) ∧ fe51ValOfBytes res % p25519 =
        fpPow (fe51ValOfBytes A % p25519) (2 ^ (BitVec.ofNat 32 kk).toNat)⌝ ∗
      (((a ↦ₛ A) ∗ (out ↦ₛ res) ∗ memRegion (sp - BitVec.ofNat 64 96) 96) ∗ F))
  rw [sat_pure_sep] at hp3
  obtain ⟨⟨hb52, hval⟩, hp3⟩ := hp3
  have hkk : (BitVec.ofNat 32 kk).toNat = kk := by simp; omega
  rw [hkk] at hval
  have hcs' := hcs
  simp only [hs1] at hcs'
  refine hcont sf res hrunf hpc' hsp' ?_ ?_ hp3 hb52 hval hCLf
  · intro k hk1 hk2
    have := kept_of_cs hcs' k hk1 hk2
    rw [this, upd_apply, if_neg]
    intro e; subst e; simp at hk2
  · have := hcs'.2.2.2.2.2.2.2.2.2.2.2
    rw [this]; rfl

end X25519Dalek.EDbl
end

section
/-! # `ProjectivePoint::double` (block 7): fetch lemmas (generated by tools/mk_fetch.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

open Arm64 Arm64.Obj

section fetch07
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m)
include hP hCL

theorem f07_0 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 0) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x130#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_4 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 4) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000d0#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_8 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 8) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000e0#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_12 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 12) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000f0#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_16 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 16) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000100#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_20 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 20) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000110#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_24 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 24) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000120#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_28 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 28) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.sp) 0x0d0#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_32 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 32) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_36 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 36) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x000#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_40 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 40) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0001#16 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_44 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 44) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_48 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 48) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 7 + BitVec.ofNat 64 48))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) p2kName x25519CliBlk07 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f07_52 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 52) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_56 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 56) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x14#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_60 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 60) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0001#16 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_64 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 64) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 7 + BitVec.ofNat 64 64))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) p2kName x25519CliBlk07 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f07_68 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 68) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_72 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 72) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x14#5) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_76 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 76) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0001#16 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_80 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 80) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 7 + BitVec.ofNat 64 80))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) p2kName x25519CliBlk07 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f07_84 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 84) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x15#5) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000050#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_88 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 88) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x058#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_92 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 92) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000060#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_96 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 96) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0001#16 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_100 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 100) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x14#5) 0x0000000000000000#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_104 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 104) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x08#5) 63 62) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_108 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 108) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x14#5) 0x0000000000000020#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_112 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 112) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x14#5) 0x0000000000000030#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_116 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 116) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x17#5) (Arm64.Reg.gpr 0x09#5) 63 62) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_120 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 120) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_124 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 124) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x14#5) 0x0000000000000010#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_128 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 128) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_132 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 132) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffa8#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_136 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 136) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000070#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_140 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 140) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_144 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 144) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x14#5) 0x0000000000000040#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_148 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 148) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x0a#5) 63 62) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_152 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 152) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x0b#5) 63 62) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_156 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 156) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_160 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 160) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_164 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 164) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffc8#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_168 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 168) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x030#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_172 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 172) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffb8#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_176 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 176) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 7 + BitVec.ofNat 64 176))) :=
  fetch_bl hP hCL (Memory.KeepsFrozen.refl m) (by decide) p2kName x25519CliBlk07 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f07_180 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 180) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x10#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000028#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_184 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 184) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVN) (Arm64.Reg.gpr 0x0d#5) 0x012f#16 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_188 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 188) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000000#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_192 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 192) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gpr 0x0d#5) 0x007f#16 48) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_196 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 196) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x12#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000038#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_200 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 200) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000048#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_204 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 204) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x03#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_208 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 208) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_212 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 212) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_216 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 216) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_220 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 220) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_224 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 224) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_228 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 228) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_232 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 232) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr) 0x007ffffffffffff0#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_236 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 236) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_240 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 240) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x11#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_244 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 244) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_248 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 248) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_252 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 252) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_256 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 256) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x12#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_260 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 260) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_264 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 264) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_268 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 268) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_272 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 272) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffe8#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_276 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 276) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x07#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffe0#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_280 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 280) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x05#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffd0#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_284 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 284) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_288 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 288) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_292 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 292) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x12#5) 51 63) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_296 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 296) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_300 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 300) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_304 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 304) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x00#5) 0x0013#16 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_308 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 308) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_312 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 312) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_316 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 316) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_320 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 320) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_324 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 324) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x06#5) 51 63) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_328 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 328) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_332 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 332) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_336 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 336) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x04#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_340 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 340) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_344 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 344) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_348 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 348) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1b#5)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_352 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 352) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x05#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_356 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 356) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x07#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_360 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 360) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_364 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 364) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x1a#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_368 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 368) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x05#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_372 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 372) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_376 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 376) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_380 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 380) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0f#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_384 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 384) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_388 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 388) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000000#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_392 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 392) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x11#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_396 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 396) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x07#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000010#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_400 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 400) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x10#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_404 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 404) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_408 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 408) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000020#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_412 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 412) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x11#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_416 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 416) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_420 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 420) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x01#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_424 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 424) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x03#5)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_428 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 428) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x15#5) (Arm64.ShiftType.LSL) 1) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_432 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 432) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000030#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_436 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 436) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_440 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 440) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_444 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 444) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x11#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_448 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 448) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000040#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_452 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 452) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_456 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 456) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_460 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 460) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_464 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 464) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x17#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_468 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 468) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0c#5) 51 63) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_472 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 472) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_476 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 476) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000050#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_480 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 480) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_484 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 484) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0d#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_488 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 488) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000060#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_492 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 492) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_496 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 496) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_500 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 500) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x0f#5)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_504 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 504) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x09#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_508 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 508) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_512 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 512) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x08#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_516 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 516) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) 0x0007ffffffffffff#64) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_520 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 520) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_524 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 524) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_528 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 528) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_532 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 532) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000070#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_536 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 536) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000080#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_540 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 540) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000090#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_544 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 544) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000120#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_548 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 548) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000110#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_552 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 552) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000100#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_556 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 556) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000f0#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_560 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 560) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000e0#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_564 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 564) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000d0#64)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_568 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 568) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x130#12 false) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

theorem f07_572 : (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 572) =
    some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) :=
  fetch_at hP hCL (by decide) 7 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ (Memory.KeepsFrozen.refl m)

end fetch07

end X25519Dalek.EDbl
end

section
/-! # Instruction shapes of block 7 not covered by the shared step lemmas

`ex_movz32` is copied from the sibling batch q444-xd-field (`G/P22Steps.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_movz32 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W32 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (imm.zeroExtend 64)) sp ps m v := by
  simp only [execInstWithSvc, execMoveWide, State.writeReg, mkS_writeGpr, hd, if_false,
    mkS_advancePC]
  congr 2
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem ex_add_gpr_gpr (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, hd, hn]

theorem ex_ldp64_gpr (a b n : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hr1 : m.canRead (r n + off) 8 = true) (hr2 : m.canRead (r n + off + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 (r n + off))) b (m.read64 (r n + off + 8#64)))
        sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr1, hr2, ha, hb, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_stp64_gpr (a b n : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw1 : m.canWrite (r n + off) 8 = true) (hw2 : m.canWrite (r n + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps ((m.write64 (r n + off) (r a)).write64 (r n + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw1, hw2, ha, hb, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_stur64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw : m.canWrite (r n + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.UnscaledOffset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (r n + off) (r a)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, ha, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldur64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hr : m.canRead (r n + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.UnscaledOffset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (r n + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr, ha, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_lsl1 (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.bitfield .W64 .UBFM (.gpr d) (.gpr n) 63 62) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n <<< 1)) sp ps m v := by
  have e : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := rfl
  simp [execInstWithSvc, evalBitfield, State.readReg, State.writeReg, hd, hn, e]

theorem ex_lsr51 (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.bitfield .W64 .UBFM (.gpr d) (.gpr n) 51 63) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n >>> 51)) sp ps m v := by
  have e : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := rfl
  simp [execInstWithSvc, evalBitfield, State.readReg, State.writeReg, hd, hn, e]

theorem ex_add_rr (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + r k)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, shiftVal, shift64,
    hd, hn, hk]

theorem ex_sub_rr (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUB (.gpr d) (.gpr n) (.gpr k) .LSL 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n - r k)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_sub, shiftVal, shift64,
    hd, hn, hk]

theorem ex_add_lsr51 (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSR 51) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + (r k >>> 51))) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, shiftVal, shift64,
    hd, hn, hk]

theorem ex_add_lsl1 (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL 1) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + (r k <<< 1))) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, shiftVal, shift64,
    hd, hn, hk]

theorem ex_and_imm (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n &&& mask)) sp ps m v := by
  simp [execInstWithSvc, execLogicalImm, evalLogical, State.readReg, State.writeReg, hd, hn]

theorem ex_orr_imm (d : BitVec 5) (hd : d ≠ 31#5) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm .W64 .ORR (.gpr d) .xzr mask) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d mask) sp ps m v := by
  simp [execInstWithSvc, execLogicalImm, evalLogical, State.readReg, State.writeReg, hd]

theorem ex_movn64 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W64 .MOVN (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (~~~(imm.zeroExtend 64))) sp ps m v := by
  simp [execInstWithSvc, execMoveWide, State.writeReg, hd]

theorem ex_movk64_48 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W64 .MOVK (.gpr d) imm 48) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d ((r d &&& ~~~(0xffff#64 <<< 48)) ||| (imm.zeroExtend 64 <<< 48)))
        sp ps m v := by
  simp [execInstWithSvc, execMoveWide, State.readReg, State.writeReg, hd]

theorem ex_umaddl (d n k a : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) (ha : a ≠ 31#5) :
    execInstWithSvc svc (.dataProc3 .W64 .UMADDL (.gpr d) (.gpr n) (.gpr k) (.gpr a)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64)
        (upd r d (r a + ((r n).truncate 32).zeroExtend 64 * ((r k).truncate 32).zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, State.readReg32, State.writeReg, hd, hn, hk, ha]

end exec

end X25519Dalek.EDbl
end

section
/-! # Buffers as runs of 64-bit words

`cellsFrom a ws` (owned words at `a, a + 8, …`) is the byte slice `ws.flatMap unpack64`; a byte
buffer is the run of its little-endian words `wordsOf bs off k`. Adapted from the sibling batch
q446-xd-ladder (`Words.lean`, `Fe.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

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

end X25519Dalek.EDbl
end

section
/-! # The twenty words `ProjectivePoint::double` writes, and a store lemma -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

open Arm64 Arm64.Obj

theorem a8 (b : BitVec 64) (x y : Nat) (h : x + 8 = y) :
    b + BitVec.ofNat 64 x + 8#64 = b + BitVec.ofNat 64 y := by
  rw [BitVec.add_assoc, ← h, BitVec.ofNat_add]

theorem aoff (b : BitVec 64) (x y z : Nat) (h : (x + y) % 2 ^ 64 = z) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 z := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← h]; apply BitVec.eq_of_toNat_eq; simp

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_ldp64_gpr' (a b n : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    {x : BitVec 64} (hx : r n = x)
    (hr1 : m.canRead (x + off) 8 = true) (hr2 : m.canRead (x + off + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 (x + off))) b (m.read64 (x + off + 8#64)))
        sp ps m v := by
  subst hx; exact ex_ldp64_gpr a b n ha hb hn off hr1 hr2

theorem ex_ldur64_gpr' (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    {x : BitVec 64} (hx : r n = x) (hr : m.canRead (x + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.UnscaledOffset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (x + off))) sp ps m v := by
  subst hx; exact ex_ldur64_gpr a n ha hn off hr

end exec

theorem bias0_eq : (~~~BitVec.zeroExtend 64 (0x12f#16) &&& ~~~(0xffff#64 <<< 48) |||
    BitVec.zeroExtend 64 (0x7f#16) <<< 48) = 36028797018963664#64 := by decide +kernel

theorem c19_eq : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (0x13#16))) = 19#64 := by
  decide +kernel

/-- `FieldElement51::reduce` of the five limbs `d0 … d4`, word `i`. -/
abbrev red0 (d0 d4 : BitVec 64) : BitVec 64 :=
  (d0 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64

abbrev redi (di dprev : BitVec 64) : BitVec 64 :=
  (di &&& 2251799813685247#64) + dprev >>> 51

/-- The words of the `CompletedPoint` written by `ProjectivePoint::double`: `X' = reduce(W - (XX + YY)
+ 16p)`, `Y' = XX + YY`, `Z' = reduce(YY - XX + 16p)`, `T' = reduce(2 ZZ - Z' + 16p)`. -/
def outList (xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4 zz0 zz1 zz2 zz3 zz4 w0 w1 w2 w3 w4 : BitVec 64) :
    List (BitVec 64) :=
  let d0 := w0 - (xx0 + yy0) + 36028797018963664#64
  let d1 := w1 - (xx1 + yy1) + 36028797018963952#64
  let d2 := w2 - (xx2 + yy2) + 36028797018963952#64
  let d3 := w3 - (xx3 + yy3) + 36028797018963952#64
  let d4 := w4 - (xx4 + yy4) + 36028797018963952#64
  let e0 := yy0 + 36028797018963664#64 - xx0
  let e1 := yy1 - xx1 + 36028797018963952#64
  let e2 := yy2 - xx2 + 36028797018963952#64
  let e3 := yy3 - xx3 + 36028797018963952#64
  let e4 := yy4 - xx4 + 36028797018963952#64
  let z0 := red0 e0 e4
  let z1 := redi e1 e0
  let z2 := redi e2 e1
  let z3 := redi e3 e2
  let z4 := redi e4 e3
  let f0 := 36028797018963664#64 + zz0 <<< 1 - z0
  let f1 := zz1 <<< 1 - z1 + 36028797018963952#64
  let f2 := zz2 <<< 1 - z2 + 36028797018963952#64
  let f3 := zz3 <<< 1 - z3 + 36028797018963952#64
  let f4 := zz4 <<< 1 - z4 + 36028797018963952#64
  [red0 d0 d4, redi d1 d0, redi d2 d1, redi d3 d2, redi d4 d3,
   xx0 + yy0, xx1 + yy1, xx2 + yy2, xx3 + yy3, xx4 + yy4,
   z0, z1, z2, z3, z4,
   red0 f0 f4, redi f1 f0, redi f2 f1, redi f3 f2, redi f4 f3]

/-- A store pair `STP Xa, Xb, [Xn, #off]` into a run of cells, with the new memory abstracted. -/
theorem RL_stp {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a b n : BitVec 5) (ha : a ≠ 31#5)
    (hb : b ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64) (k : Nat) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 7).fetchMem m pc =
      some (.stp .W64 (.gpr a) (.gpr b) (.Offset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k)) (hk : k + 1 < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F)
    (h : ∀ m' : Memory, (m' ⊨ cellsFrom base ((L.set k (r a)).set (k + 1) (r b)) ∗ F) →
      RL mpl (mkS sb (pc + 4#64) r sp ps m' v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have r0 := cells_read _ _ _ _ hs k (by omega)
  have r1 := cells_read _ _ _ _ hs (k + 1) hk
  have e1 : base + BitVec.ofNat 64 (8 * k) + 8#64 = base + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  refine RL.mk hrun hf ?_
  rw [ex_stp64_gpr a b n ha hb hn off (by rw [hx]; exact r0.2.2)
    (by rw [hx, e1]; exact r1.2.2)]
  apply h
  have w0 := cells_write _ _ _ _ hs k (by omega) (r a)
  have w1 := cells_write _ _ _ _ w0 (k + 1) (by simp; omega) (r b)
  rw [hx, e1]
  exact w1

/-- `STP Xa, Xb, [SP, #off]` into a run of cells. -/
theorem RL_stp_sp {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a b : BitVec 5) (ha : a ≠ 31#5)
    (hb : b ≠ 31#5) (off : BitVec 64) (k : Nat) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 7).fetchMem m pc =
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

/-- `STUR Xa, [Xn, #off]` into a run of cells. -/
theorem RL_stur {mpl : MultiPlacement} {Q : State → Prop} {sb : State} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {base : BitVec 64} {L : List (BitVec 64)} {F : SepProp} (a n : BitVec 5) (ha : a ≠ 31#5)
    (hn : n ≠ 31#5) (off : BitVec 64) (k : Nat) (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 7).fetchMem m pc =
      some (.str .X64 (.gpr a) (.UnscaledOffset (.gpr n) off)))
    (hx : r n + off = base + BitVec.ofNat 64 (8 * k)) (hk : k < L.length)
    (hs : m ⊨ cellsFrom base L ∗ F)
    (h : ∀ m' : Memory, (m' ⊨ cellsFrom base (L.set k (r a)) ∗ F) →
      RL mpl (mkS sb (pc + 4#64) r sp ps m' v) Q) :
    RL mpl (mkS sb pc r sp ps m v) Q := by
  have r0 := cells_read _ _ _ _ hs k hk
  refine RL.mk hrun hf ?_
  rw [ex_stur64_gpr a n ha hn off (by rw [hx]; exact r0.2.2)]
  apply h
  rw [hx]
  exact cells_write _ _ _ _ hs k hk (r a)

end X25519Dalek.EDbl
end

section
/-! # `pow2k` calls on runs of words

The squaring calls of block 7, with the operand and the result as five-word runs inside the
caller's word lists. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

open Arm64 Arm64.Obj

/-- All five words are `< B`. -/
def B5 (a0 a1 a2 a3 a4 : BitVec 64) (B : Nat) : Prop :=
  a0.toNat < B ∧ a1.toNat < B ∧ a2.toNat < B ∧ a3.toNat < B ∧ a4.toNat < B

theorem wordsOf5 (bs : List (BitVec 8)) :
    wordsOf bs 0 5 = [ByteSlice.readLE bs 0 8, ByteSlice.readLE bs 8 8, ByteSlice.readLE bs 16 8,
      ByteSlice.readLE bs 24 8, ByteSlice.readLE bs 32 8] := rfl

/-- A squaring call (`pow2k(·, 1)`) on five-word runs. -/
theorem call_w {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hM : fnOk p2kName (fun _ => fe51Pow2kSpec)) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {bo bi : BitVec 64} {i0 i1 i2 i3 i4 o0 o1 o2 o3 o4 : BitVec 64}
    {F : SepProp}
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 7 + BitVec.ofNat 64 off))))
    (hal : sp &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = bo) (h0 : r 0#5 = bi) (h1 : r 1#5 = BitVec.ofNat 64 1)
    (hmem : m ⊨ (cellsFrom bi [i0, i1, i2, i3, i4] ∗ cellsFrom bo [o0, o1, o2, o3, o4] ∗
      memRegion (sp - BitVec.ofNat 64 96) 96) ∗ F)
    (hb : B5 i0 i1 i2 i3 i4 (2 ^ 54))
    (hcont : ∀ (sf : State) (z0 z1 z2 z3 z4 : BitVec 64), sf.status = .Running →
      sf.pc = mpl.base 7 + BitVec.ofNat 64 (off + 4) → sf.sp = sp → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ (cellsFrom bi [i0, i1, i2, i3, i4] ∗ cellsFrom bo [z0, z1, z2, z3, z4] ∗
        memRegion (sp - BitVec.ofNat 64 96) 96) ∗ F) →
      B5 z0 z1 z2 z3 z4 (2 ^ 52) →
      fe51Val z0 z1 z2 z3 z4 % p25519 = fpPow (fe51Val i0 i1 i2 i3 i4 % p25519) (2 ^ 1) →
      RL mpl sf Q) :
    RL mpl (mkS sb (mpl.base 7 + BitVec.ofNat 64 off) r sp ps m v) Q := by
  obtain ⟨b0, b1, b2, b3, b4⟩ := hb
  obtain ⟨hA, hAv⟩ := fe51_of_words i0 i1 i2 i3 i4 (2 ^ 54) b0 b1 b2 b3 b4
  rw [cellsFrom_eq_bytes, cellsFrom_eq_bytes] at hmem
  refine call_p2k hP hM (kk := 1) hrun hf hal h8 h0 h1 (by norm_num) (by norm_num) hmem hA
    (by rw [flatMap_unpack64_length]; rfl) ?_
  intro sf res hrun' hpc hsp hk hv hm' hb' hval
  have hl : res.length = 8 * 5 := hb'.1
  rw [bytes_eq_cells bo res 5 hl, wordsOf5, ← cellsFrom_eq_bytes] at hm'
  obtain ⟨_, c0, c1, c2, c3, c4⟩ := hb'
  refine hcont sf _ _ _ _ _ hrun' hpc hsp hk hv hm' ⟨c0, c1, c2, c3, c4⟩ ?_
  rw [← hAv]; exact hval

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

/-- The standard heap of block 7 between calls: the 304-byte frame as 38 words, `self` as 15
words, `out` as 20 words, the callee frame, and the caller's frame `R`. -/
abbrev Heap7 (SP self out : BitVec 64) (S Sf O : List (BitVec 64)) (R : SepProp) : SepProp :=
  cellsFrom SP S ∗ cellsFrom self Sf ∗ cellsFrom out O ∗ memRegion (SP - BitVec.ofNat 64 96) 96 ∗ R

/-- A squaring call from `self`'s words `i … i+4` to the frame's words `j … j+4`. -/
theorem call_fs {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hM : fnOk p2kName (fun _ => fe51Pow2kSpec)) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {SP : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {self out : BitVec 64} {S Sf O : List (BitVec 64)} {R : SepProp}
    (i j : Nat) (hi : i + 5 ≤ Sf.length) (hj : j + 5 ≤ S.length)
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 7 + BitVec.ofNat 64 off))))
    (hal : SP &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = SP + BitVec.ofNat 64 (8 * j)) (h0 : r 0#5 = self + BitVec.ofNat 64 (8 * i))
    (h1 : r 1#5 = BitVec.ofNat 64 1)
    (hmem : m ⊨ Heap7 SP self out S Sf O R)
    (hb : B5 (Sf.getD i 0) (Sf.getD (i + 1) 0) (Sf.getD (i + 2) 0) (Sf.getD (i + 3) 0)
      (Sf.getD (i + 4) 0) (2 ^ 54))
    (hcont : ∀ (sf : State) (z0 z1 z2 z3 z4 : BitVec 64), sf.status = .Running →
      sf.pc = mpl.base 7 + BitVec.ofNat 64 (off + 4) → sf.sp = SP → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ Heap7 SP self out (S.take j ++ [z0, z1, z2, z3, z4] ++ S.drop (j + 5)) Sf O R) →
      B5 z0 z1 z2 z3 z4 (2 ^ 52) →
      fe51Val z0 z1 z2 z3 z4 % p25519 = fpPow (fe51Val (Sf.getD i 0) (Sf.getD (i + 1) 0)
        (Sf.getD (i + 2) 0) (Sf.getD (i + 3) 0) (Sf.getD (i + 4) 0) % p25519) (2 ^ 1) →
      RL mpl sf Q) :
    RL mpl (mkS sb (mpl.base 7 + BitVec.ofNat 64 off) r SP ps m v) Q := by
  unfold Heap7 at hmem
  rw [cells_split3 SP S j 5 hj, cells_split3 self Sf i 5 hi, take5_eq S j hj, take5_eq Sf i hi] at hmem
  refine call_w hP hM (o0 := S.getD j 0) (o1 := S.getD (j + 1) 0) (o2 := S.getD (j + 2) 0)
    (o3 := S.getD (j + 3) 0) (o4 := S.getD (j + 4) 0)
    (F := cellsFrom SP (S.take j) ∗ cellsFrom (SP + BitVec.ofNat 64 (8 * (j + 5))) (S.drop (j + 5)) ∗
      cellsFrom self (Sf.take i) ∗ cellsFrom (self + BitVec.ofNat 64 (8 * (i + 5))) (Sf.drop (i + 5)) ∗
      cellsFrom out O ∗ R) hrun hf hal h8 h0 h1 (Satisfies.of_eq hmem) hb ?_
  intro sf z0 z1 z2 z3 z4 hrun' hpc hsp hk hv hm' hb' hval
  refine hcont sf z0 z1 z2 z3 z4 hrun' hpc hsp hk hv ?_ hb' hval
  unfold Heap7
  rw [← cells_merge3 SP S _ j 5 hj rfl, cells_split3 self Sf i 5 hi, take5_eq Sf i hi]
  exact Satisfies.of_eq hm'

/-- A squaring call from the frame's words `i … i+4` to its words `i+5 … i+9`. -/
theorem call_ss {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hM : fnOk p2kName (fun _ => fe51Pow2kSpec)) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {SP : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {self out : BitVec 64} {S Sf O : List (BitVec 64)} {R : SepProp}
    (i : Nat) (hi : i + 10 ≤ S.length)
    (hrun : sb.status = .Running)
    (hf : x25519CliMultiLib.CodeLoaded mpl m → (bprog mpl 7).fetchMem m (mpl.base 7 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 7 + BitVec.ofNat 64 off))))
    (hal : SP &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = SP + BitVec.ofNat 64 (8 * (i + 5))) (h0 : r 0#5 = SP + BitVec.ofNat 64 (8 * i))
    (h1 : r 1#5 = BitVec.ofNat 64 1)
    (hmem : m ⊨ Heap7 SP self out S Sf O R)
    (hb : B5 (S.getD i 0) (S.getD (i + 1) 0) (S.getD (i + 2) 0) (S.getD (i + 3) 0)
      (S.getD (i + 4) 0) (2 ^ 54))
    (hcont : ∀ (sf : State) (z0 z1 z2 z3 z4 : BitVec 64), sf.status = .Running →
      sf.pc = mpl.base 7 + BitVec.ofNat 64 (off + 4) → sf.sp = SP → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ Heap7 SP self out (S.take (i + 5) ++ [z0, z1, z2, z3, z4] ++ S.drop (i + 5 + 5)) Sf O R) →
      B5 z0 z1 z2 z3 z4 (2 ^ 52) →
      fe51Val z0 z1 z2 z3 z4 % p25519 = fpPow (fe51Val (S.getD i 0) (S.getD (i + 1) 0)
        (S.getD (i + 2) 0) (S.getD (i + 3) 0) (S.getD (i + 4) 0) % p25519) (2 ^ 1) →
      RL mpl sf Q) :
    RL mpl (mkS sb (mpl.base 7 + BitVec.ofNat 64 off) r SP ps m v) Q := by
  unfold Heap7 at hmem
  have hj : i + 5 + 5 ≤ S.length := by omega
  rw [cells_split3 SP S (i + 5) 5 hj, cells_split3 SP (S.take (i + 5)) i 5 (by simp; omega),
    take5_eq S (i + 5) hj, take5_eq (S.take (i + 5)) i (by simp; omega)] at hmem
  have eg : ∀ t, t < 5 → (S.take (i + 5)).getD (i + t) 0 = S.getD (i + t) 0 := by
    intro t ht
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]
  rw [show i = i + 0 from rfl, eg 0 (by omega), eg 1 (by omega), eg 2 (by omega), eg 3 (by omega),
    eg 4 (by omega)] at hmem
  simp only [Nat.add_zero] at hmem
  refine call_w hP hM (o0 := S.getD (i + 5) 0) (o1 := S.getD (i + 5 + 1) 0) (o2 := S.getD (i + 5 + 2) 0)
    (o3 := S.getD (i + 5 + 3) 0) (o4 := S.getD (i + 5 + 4) 0)
    (F := cellsFrom SP ((S.take (i + 5)).take i) ∗ cellsFrom (SP + BitVec.ofNat 64 (8 * (i + 5)))
      ((S.take (i + 5)).drop (i + 5)) ∗ cellsFrom (SP + BitVec.ofNat 64 (8 * (i + 5 + 5))) (S.drop (i + 5 + 5)) ∗
      cellsFrom self Sf ∗ cellsFrom out O ∗ R) hrun hf hal h8 h0 h1 (Satisfies.of_eq hmem) hb ?_
  intro sf z0 z1 z2 z3 z4 hrun' hpc hsp hk hv hm' hb' hval
  refine hcont sf z0 z1 z2 z3 z4 hrun' hpc hsp hk hv ?_ hb' hval
  unfold Heap7
  rw [← cells_merge3 SP S _ (i + 5) 5 hj rfl, cells_split3 SP (S.take (i + 5)) i 5 (by simp; omega),
    take5_eq (S.take (i + 5)) i (by simp; omega)]
  rw [show i = i + 0 from rfl, eg 0 (by omega), eg 1 (by omega), eg 2 (by omega), eg 3 (by omega),
    eg 4 (by omega)]
  simp only [Nat.add_zero]
  exact Satisfies.of_eq hm'

end X25519Dalek.EDbl
end

section
/-! # `ProjectivePoint::double` (block 7), offsets 0–176: the prologue and the four squarings
(generated by tools/mk_segAB.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

open Arm64 Arm64.Obj

theorem asub (b : BitVec 64) (x y z : Nat) (h : x = y + z) :
    b + BitVec.ofNat 64 x - BitVec.ofNat 64 y = b + BitVec.ofNat 64 z := by
  subst h; rw [BitVec.ofNat_add]; abel

theorem B5_mono {a0 a1 a2 a3 a4 : BitVec 64} {B B' : Nat} (h : B5 a0 a1 a2 a3 a4 B) (hB : B ≤ B') :
    B5 a0 a1 a2 a3 a4 B' := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem add53 {a b : BitVec 64} (ha : a.toNat < 2 ^ 53) (hb : b.toNat < 2 ^ 53) : (a + b).toNat < 2 ^ 54 := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega

theorem B5_add {x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : BitVec 64} (hy : B5 y0 y1 y2 y3 y4 (2 ^ 53))
    (hx : B5 x0 x1 x2 x3 x4 (2 ^ 53)) :
    B5 (y0 + x0) (y1 + x1) (y2 + x2) (y3 + x3) (y4 + x4) (2 ^ 54) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := hy
  obtain ⟨b0, b1, b2, b3, b4⟩ := hx
  exact ⟨add53 a0 b0, add53 a1 b1, add53 a2 b2, add53 a3 b3, add53 a4 b4⟩

set_option maxHeartbeats 4000000 in
theorem segAB {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hK : fnOk p2kName (fun _ => fe51Pow2kSpec)) {Q : State → Prop}
    {sb : State} {r : BitVec 5 → BitVec 64} {sp0 SP : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {self out : BitVec 64} {R : SepProp}
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 : BitVec 64) (X0 X1 X2 X3 X4 Y0 Y1 Y2 Y3 Y4 Z0 Z1 Z2 Z3 Z4 : BitVec 64) (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 o16 o17 o18 o19 : BitVec 64)
    (hrun : sb.status = .Running) (halSP : SP &&& 0b1111#64 = 0#64)
    (hSP : sp0 - BitVec.ofNat 64 304 = SP)
    (h8 : r 8#5 = out) (h0 : r 0#5 = self)
    (hm : m ⊨ Heap7 SP self out [u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u25, u26, u27, u28, u29, u30, u31, u32, u33, u34, u35, u36, u37] [X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Z0, Z1, Z2, Z3, Z4] [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19] R)
    (hbX : B5 X0 X1 X2 X3 X4 (2 ^ 53)) (hbY : B5 Y0 Y1 Y2 Y3 Y4 (2 ^ 53))
    (hbZ : B5 Z0 Z1 Z2 Z3 Z4 (2 ^ 54))
    (hC : ∀ (sb' : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory)
      (v' : BitVec 5 → BitVec 128)
      (xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4 zz0 zz1 zz2 zz3 zz4 w0 w1 w2 w3 w4 : BitVec 64),
      sb'.status = .Running → r' 19#5 = out → r' 21#5 = zz0 → r' 22#5 = zz1 <<< 1 →
      r' 23#5 = zz2 <<< 1 → r' 20#5 = zz3 <<< 1 → r' 24#5 = zz4 <<< 1 →
      r' 29#5 = SP + BitVec.ofNat 64 208 →
      VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨v⟩ →
      (m' ⊨ Heap7 SP self out [xx0, xx1, xx2, xx3, xx4, yy0, yy1, yy2, yy3, yy4, zz0, zz1, zz2, zz3, zz4,
        Y0 + X0, Y1 + X1, Y2 + X2, Y3 + X3, Y4 + X4, w0, w1, w2, w3, w4, u25, r 29#5, r 30#5, r 28#5, r 27#5, r 26#5, r 25#5, r 24#5, r 23#5, r 22#5, r 21#5, r 20#5, r 19#5]
        [X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Z0, Z1, Z2, Z3, Z4] [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19] R) →
      B5 xx0 xx1 xx2 xx3 xx4 (2 ^ 52) → B5 yy0 yy1 yy2 yy3 yy4 (2 ^ 52) →
      B5 zz0 zz1 zz2 zz3 zz4 (2 ^ 52) → B5 w0 w1 w2 w3 w4 (2 ^ 52) →
      fe51Val xx0 xx1 xx2 xx3 xx4 % p25519 = fpPow (fe51Val X0 X1 X2 X3 X4 % p25519) (2 ^ 1) →
      fe51Val yy0 yy1 yy2 yy3 yy4 % p25519 = fpPow (fe51Val Y0 Y1 Y2 Y3 Y4 % p25519) (2 ^ 1) →
      fe51Val zz0 zz1 zz2 zz3 zz4 % p25519 = fpPow (fe51Val Z0 Z1 Z2 Z3 Z4 % p25519) (2 ^ 1) →
      fe51Val w0 w1 w2 w3 w4 % p25519 =
        fpPow (fe51Val (Y0 + X0) (Y1 + X1) (Y2 + X2) (Y3 + X3) (Y4 + X4) % p25519) (2 ^ 1) →
      RL mpl (mkS sb' (mpl.base 7 + BitVec.ofNat 64 180) r' SP ps' m' v') Q) :
    RL mpl (mkS sb (mpl.base 7 + BitVec.ofNat 64 0) r sp0 ps m v) Q := by
  -- 0: sub sp, sp, #304
  refine RL.mk hrun (f07_0 hP) ?_
  rw [ex_sub_sp, z12 _ (by norm_num), hSP, pc_add]
  -- 4: stp x29, x30, [sp, #208]
  refine RL_stp_sp 29#5 30#5 (by decide) (by decide) _ 26 hrun (f07_4 hP) halSP rfl (by simp) hm ?_
  intro m1 hm1
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hm1
  rw [pc_add]
  -- 8: stp x28, x27, [sp, #224]
  refine RL_stp_sp 28#5 27#5 (by decide) (by decide) _ 28 hrun (f07_8 hP) halSP rfl (by simp) hm1 ?_
  intro m2 hm2
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hm2
  rw [pc_add]
  -- 12: stp x26, x25, [sp, #240]
  refine RL_stp_sp 26#5 25#5 (by decide) (by decide) _ 30 hrun (f07_12 hP) halSP rfl (by simp) hm2 ?_
  intro m3 hm3
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hm3
  rw [pc_add]
  -- 16: stp x24, x23, [sp, #256]
  refine RL_stp_sp 24#5 23#5 (by decide) (by decide) _ 32 hrun (f07_16 hP) halSP rfl (by simp) hm3 ?_
  intro m4 hm4
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hm4
  rw [pc_add]
  -- 20: stp x22, x21, [sp, #272]
  refine RL_stp_sp 22#5 21#5 (by decide) (by decide) _ 34 hrun (f07_20 hP) halSP rfl (by simp) hm4 ?_
  intro m5 hm5
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hm5
  rw [pc_add]
  -- 24: stp x20, x19, [sp, #288]
  refine RL_stp_sp 20#5 19#5 (by decide) (by decide) _ 36 hrun (f07_24 hP) halSP rfl (by simp) hm5 ?_
  intro m6 hm6
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hm6
  rw [pc_add]
  -- 28
  refine RL.mk hrun (f07_28 hP) ?_
  rw [ex_add_gpr_sp 29#5 (by decide), z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h8, h0, Nat.reduceAdd]
  -- 32
  refine RL.mk hrun (f07_32 hP) ?_
  rw [ex_mov 19#5 8#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h8, h0, Nat.reduceAdd]
  -- 36
  refine RL.mk hrun (f07_36 hP) ?_
  rw [ex_add_gpr_sp 8#5 (by decide), z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h8, h0, Nat.reduceAdd]
  -- 40
  refine RL.mk hrun (f07_40 hP) ?_
  rw [ex_movz32 1#5 (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h8, h0, Nat.reduceAdd]
  -- 44
  refine RL.mk hrun (f07_44 hP) ?_
  rw [ex_mov 20#5 0#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h8, h0, Nat.reduceAdd]
  -- 48: bl pow2k (call 1)
  refine call_fs hP hK 0 0 (by simp) (by simp) hrun (f07_48 hP) halSP (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h8, h0] <;> first | rfl | simp) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h8, h0] <;> first | rfl | simp) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h8, h0] <;> rfl) hm6 (B5_mono hbX (by norm_num)) ?_
  intro sf1 a0 a1 a2 a3 a4 hrun1 hpc1 hsp1 hk1 hv1 hc1 hb1 hval1
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hc1 hval1
  refine RL.congr (s' := mkS sf1 (mpl.base 7 + BitVec.ofNat 64 52) sf1.regs.regs SP sf1.pstate sf1.mem sf1.vregs.regs) (by rw [← hpc1, ← hsp1]; rfl) ?_
  have g19_1 : sf1.regs.regs 19#5 = out := (hk1 19#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h8, h0] <;> rfl)
  have g20_1 : sf1.regs.regs 20#5 = self := (hk1 20#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h8, h0] <;> rfl)
  have g29_1 : sf1.regs.regs 29#5 = SP + BitVec.ofNat 64 208 := (hk1 29#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h8, h0] <;> rfl)
  -- 52
  refine RL.mk hrun1 (f07_52 hP) ?_
  rw [ex_add_gpr_sp 8#5 (by decide), z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_1, g20_1, g29_1, Nat.reduceAdd]
  -- 56
  refine RL.mk hrun1 (f07_56 hP) ?_
  rw [ex_add_gpr_gpr 0#5 20#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_1, g20_1, g29_1, Nat.reduceAdd]
  -- 60
  refine RL.mk hrun1 (f07_60 hP) ?_
  rw [ex_movz32 1#5 (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_1, g20_1, g29_1, Nat.reduceAdd]
  -- 64: bl pow2k (call 2)
  refine call_fs hP hK 5 5 (by simp) (by simp) hrun1 (f07_64 hP) halSP (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_1, g20_1, g29_1] <;> first | rfl | simp) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_1, g20_1, g29_1] <;> first | rfl | simp) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_1, g20_1, g29_1] <;> rfl) hc1 (B5_mono hbY (by norm_num)) ?_
  intro sf2 b0 b1 b2 b3 b4 hrun2 hpc2 hsp2 hk2 hv2 hc2 hb2 hval2
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hc2 hval2
  refine RL.congr (s' := mkS sf2 (mpl.base 7 + BitVec.ofNat 64 68) sf2.regs.regs SP sf2.pstate sf2.mem sf2.vregs.regs) (by rw [← hpc2, ← hsp2]; rfl) ?_
  have g19_2 : sf2.regs.regs 19#5 = out := (hk2 19#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_1, g20_1, g29_1] <;> rfl)
  have g20_2 : sf2.regs.regs 20#5 = self := (hk2 20#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_1, g20_1, g29_1] <;> rfl)
  have g29_2 : sf2.regs.regs 29#5 = SP + BitVec.ofNat 64 208 := (hk2 29#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_1, g20_1, g29_1] <;> rfl)
  -- 68
  refine RL.mk hrun2 (f07_68 hP) ?_
  rw [ex_add_gpr_sp 8#5 (by decide), z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_2, g20_2, g29_2, Nat.reduceAdd]
  -- 72
  refine RL.mk hrun2 (f07_72 hP) ?_
  rw [ex_add_gpr_gpr 0#5 20#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_2, g20_2, g29_2, Nat.reduceAdd]
  -- 76
  refine RL.mk hrun2 (f07_76 hP) ?_
  rw [ex_movz32 1#5 (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_2, g20_2, g29_2, Nat.reduceAdd]
  -- 80: bl pow2k (call 3)
  refine call_fs hP hK 10 10 (by simp) (by simp) hrun2 (f07_80 hP) halSP (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_2, g20_2, g29_2] <;> first | rfl | simp) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_2, g20_2, g29_2] <;> first | rfl | simp) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_2, g20_2, g29_2] <;> rfl) hc2 (B5_mono hbZ (by norm_num)) ?_
  intro sf3 c0 c1 c2 c3 c4 hrun3 hpc3 hsp3 hk3 hv3 hc3 hb3 hval3
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hc3 hval3
  refine RL.congr (s' := mkS sf3 (mpl.base 7 + BitVec.ofNat 64 84) sf3.regs.regs SP sf3.pstate sf3.mem sf3.vregs.regs) (by rw [← hpc3, ← hsp3]; rfl) ?_
  have g19_3 : sf3.regs.regs 19#5 = out := (hk3 19#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_2, g20_2, g29_2] <;> rfl)
  have g20_3 : sf3.regs.regs 20#5 = self := (hk3 20#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_2, g20_2, g29_2] <;> rfl)
  have g29_3 : sf3.regs.regs 29#5 = SP + BitVec.ofNat 64 208 := (hk3 29#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_2, g20_2, g29_2] <;> rfl)
  have q10 := cells_read _ _ _ _ hc3 10 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q10
  have q11 := cells_read _ _ _ _ hc3 11 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q11
  -- 84
  refine RL.mk hrun3 (f07_84 hP) ?_
  rw [ex_ldp64_sp 21#5 8#5 (by decide) (by decide) _ halSP q10.2.1 (by rw [a8 SP 80 88 rfl]; exact q11.2.1), a8 SP 80 88 rfl, q10.1, q11.1, pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 88
  refine RL.mk hrun3 (f07_88 hP) ?_
  rw [ex_sub_gpr_gpr 0#5 29#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  rw [asub SP 208 88 120 rfl]
  have q12 := cells_read _ _ _ _ hc3 12 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q12
  have q13 := cells_read _ _ _ _ hc3 13 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q13
  -- 92
  refine RL.mk hrun3 (f07_92 hP) ?_
  rw [ex_ldp64_sp 9#5 10#5 (by decide) (by decide) _ halSP q12.2.1 (by rw [a8 SP 96 104 rfl]; exact q13.2.1), a8 SP 96 104 rfl, q12.1, q13.1, pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 96
  refine RL.mk hrun3 (f07_96 hP) ?_
  rw [ex_movz32 1#5 (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  have f0 := cells_read _ _ _ _ (by (try unfold Heap7 at hc3); rw [sepConj_left_comm] at hc3; exact hc3) 0 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f0
  have f1 := cells_read _ _ _ _ (by (try unfold Heap7 at hc3); rw [sepConj_left_comm] at hc3; exact hc3) 1 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f1
  -- 100
  refine RL.mk hrun3 (f07_100 hP) ?_
  rw [ex_ldp64_gpr' 11#5 12#5 20#5 (by decide) (by decide) (by decide) _ (x := self) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3]) f0.2.1 (by rw [a8 self 0 8 rfl]; exact f1.2.1), a8 self 0 8 rfl, f0.1, f1.1, pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 104
  refine RL.mk hrun3 (f07_104 hP) ?_
  rw [ex_lsl1 22#5 8#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  have f4 := cells_read _ _ _ _ (by (try unfold Heap7 at hc3); rw [sepConj_left_comm] at hc3; exact hc3) 4 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f4
  have f5 := cells_read _ _ _ _ (by (try unfold Heap7 at hc3); rw [sepConj_left_comm] at hc3; exact hc3) 5 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f5
  -- 108
  refine RL.mk hrun3 (f07_108 hP) ?_
  rw [ex_ldp64_gpr' 8#5 13#5 20#5 (by decide) (by decide) (by decide) _ (x := self) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3]) f4.2.1 (by rw [a8 self 32 40 rfl]; exact f5.2.1), a8 self 32 40 rfl, f4.1, f5.1, pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  have f6 := cells_read _ _ _ _ (by (try unfold Heap7 at hc3); rw [sepConj_left_comm] at hc3; exact hc3) 6 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f6
  have f7 := cells_read _ _ _ _ (by (try unfold Heap7 at hc3); rw [sepConj_left_comm] at hc3; exact hc3) 7 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f7
  -- 112
  refine RL.mk hrun3 (f07_112 hP) ?_
  rw [ex_ldp64_gpr' 14#5 15#5 20#5 (by decide) (by decide) (by decide) _ (x := self) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3]) f6.2.1 (by rw [a8 self 48 56 rfl]; exact f7.2.1), a8 self 48 56 rfl, f6.1, f7.1, pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 116
  refine RL.mk hrun3 (f07_116 hP) ?_
  rw [ex_lsl1 23#5 9#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 120
  refine RL.mk hrun3 (f07_120 hP) ?_
  rw [ex_add_rr 11#5 13#5 11#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  have f2 := cells_read _ _ _ _ (by (try unfold Heap7 at hc3); rw [sepConj_left_comm] at hc3; exact hc3) 2 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f2
  have f3 := cells_read _ _ _ _ (by (try unfold Heap7 at hc3); rw [sepConj_left_comm] at hc3; exact hc3) 3 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f3
  -- 124
  refine RL.mk hrun3 (f07_124 hP) ?_
  rw [ex_ldp64_gpr' 9#5 13#5 20#5 (by decide) (by decide) (by decide) _ (x := self) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3]) f2.2.1 (by rw [a8 self 16 24 rfl]; exact f3.2.1), a8 self 16 24 rfl, f2.1, f3.1, pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 128
  refine RL.mk hrun3 (f07_128 hP) ?_
  rw [ex_add_rr 12#5 14#5 12#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 132: store
  refine RL_stp 11#5 12#5 29#5 (by decide) (by decide) (by decide) _ 15 hrun3 (f07_132 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3]; exact aoff SP 208 18446744073709551528 120 rfl) (by simp) hc3 ?_
  intro m7 hm7
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hm7
  rw [pc_add]
  have q14 := cells_read _ _ _ _ hm7 14 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q14
  -- 136
  refine RL.mk hrun3 (f07_136 hP) ?_
  rw [ex_ldr64_sp 11#5 (by decide) _ halSP q14.2.1, q14.1, pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 140
  refine RL.mk hrun3 (f07_140 hP) ?_
  rw [ex_add_rr 9#5 15#5 9#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  have f8 := cells_read _ _ _ _ (by (try unfold Heap7 at hm7); rw [sepConj_left_comm] at hm7; exact hm7) 8 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f8
  have f9 := cells_read _ _ _ _ (by (try unfold Heap7 at hm7); rw [sepConj_left_comm] at hm7; exact hm7) 9 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at f9
  -- 144
  refine RL.mk hrun3 (f07_144 hP) ?_
  rw [ex_ldp64_gpr' 14#5 15#5 20#5 (by decide) (by decide) (by decide) _ (x := self) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3]) f8.2.1 (by rw [a8 self 64 72 rfl]; exact f9.2.1), a8 self 64 72 rfl, f8.1, f9.1, pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 148
  refine RL.mk hrun3 (f07_148 hP) ?_
  rw [ex_lsl1 20#5 10#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 152
  refine RL.mk hrun3 (f07_152 hP) ?_
  rw [ex_lsl1 24#5 11#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 156
  refine RL.mk hrun3 (f07_156 hP) ?_
  rw [ex_add_rr 8#5 15#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 160
  refine RL.mk hrun3 (f07_160 hP) ?_
  rw [ex_add_rr 10#5 14#5 13#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  -- 164: store
  refine RL_stur 8#5 29#5 (by decide) (by decide) _ 19 hrun3 (f07_164 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3]; exact aoff SP 208 18446744073709551560 152 rfl) (by simp) hm7 ?_
  intro m8 hm8
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hm8
  rw [pc_add]
  -- 168
  refine RL.mk hrun3 (f07_168 hP) ?_
  rw [ex_sub_gpr_gpr 8#5 29#5 (by decide) (by decide), z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, Nat.reduceAdd]
  rw [asub SP 208 48 160 rfl]
  -- 172: store
  refine RL_stp 9#5 10#5 29#5 (by decide) (by decide) (by decide) _ 17 hrun3 (f07_172 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3]; exact aoff SP 208 18446744073709551544 136 rfl) (by simp) hm8 ?_
  intro m9 hm9
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3, List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hm9
  rw [pc_add]
  -- 176: bl pow2k (call 4)
  refine call_ss hP hK 15 (by simp) hrun3 (f07_176 hP) halSP (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl) hm9 (B5_add hbY hbX) ?_
  intro sf4 w0 w1 w2 w3 w4 hrun4 hpc4 hsp4 hk4 hv4 hc4 hb4 hval4
  simp only [List.set_cons_succ, List.set_cons_zero, List.take, List.drop, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero] at hc4 hval4
  refine RL.congr (s' := mkS sf4 (mpl.base 7 + BitVec.ofNat 64 180) sf4.regs.regs SP sf4.pstate sf4.mem sf4.vregs.regs) (by rw [← hpc4, ← hsp4]; rfl) ?_
  have g19_4 : sf4.regs.regs 19#5 = out := (hk4 19#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl)
  have g21_4 : sf4.regs.regs 21#5 = c0 := (hk4 21#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl)
  have g22_4 : sf4.regs.regs 22#5 = c1 <<< 1 := (hk4 22#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl)
  have g23_4 : sf4.regs.regs 23#5 = c2 <<< 1 := (hk4 23#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl)
  have g20_4 : sf4.regs.regs 20#5 = c3 <<< 1 := (hk4 20#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl)
  have g24_4 : sf4.regs.regs 24#5 = c4 <<< 1 := (hk4 24#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl)
  have g29_4 : sf4.regs.regs 29#5 = SP + BitVec.ofNat 64 208 := (hk4 29#5 (by decide) (by decide)).trans (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, g19_3, g20_3, g29_3] <;> rfl)
  exact hC sf4 sf4.regs.regs sf4.pstate sf4.mem sf4.vregs.regs a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 w0 w1 w2 w3 w4 hrun4 g19_4 g21_4 g22_4 g23_4 g20_4 g24_4 g29_4 (hv4.trans (hv3.trans (hv2.trans hv1))) hc4 hb1 hb2 hb3 hb4 hval1 hval2 hval3 hval4

end X25519Dalek.EDbl
end

section
/-! # `ProjectivePoint::double` (block 7), offsets 180–572: the field arithmetic after the last
call and the epilogue (generated by tools/mk_segC.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

open Arm64 Arm64.Obj

set_option maxHeartbeats 4000000 in
theorem segC {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {Q : State → Prop}
    {sb : State} {r : BitVec 5 → BitVec 64} {SP : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {out : BitVec 64} {F : SepProp}
    (xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4 zz0 zz1 zz2 zz3 zz4 s0 s1 s2 s3 s4 w0 w1 w2 w3 w4 g c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 o16 o17 o18 o19 : BitVec 64)
    (hrun : sb.status = .Running) (hal : SP &&& 0b1111#64 = 0#64)
    (h19 : r 19#5 = out) (h21 : r 21#5 = zz0) (h22 : r 22#5 = zz1 <<< 1) (h23 : r 23#5 = zz2 <<< 1)
    (h20 : r 20#5 = zz3 <<< 1) (h24 : r 24#5 = zz4 <<< 1) (h29 : r 29#5 = SP + BitVec.ofNat 64 208)
    (hm : m ⊨ cellsFrom SP [xx0, xx1, xx2, xx3, xx4, yy0, yy1, yy2, yy3, yy4, zz0, zz1, zz2, zz3, zz4, s0, s1, s2, s3, s4, w0, w1, w2, w3, w4, g, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] ∗ cellsFrom out [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19] ∗ F)
    (hQ : ∀ sf : State, sf.status = .Running → sf.pc = c1 → sf.sp = SP + BitVec.ofNat 64 304 →
      sf.regs.regs 19#5 = c11 → sf.regs.regs 20#5 = c10 → sf.regs.regs 21#5 = c9 →
      sf.regs.regs 22#5 = c8 → sf.regs.regs 23#5 = c7 → sf.regs.regs 24#5 = c6 →
      sf.regs.regs 25#5 = c5 → sf.regs.regs 26#5 = c4 → sf.regs.regs 27#5 = c3 →
      sf.regs.regs 28#5 = c2 → sf.regs.regs 29#5 = c0 → sf.vregs.regs = v →
      (sf.mem ⊨ cellsFrom SP [xx0, xx1, xx2, xx3, xx4, yy0, yy1, yy2, yy3, yy4, zz0, zz1, zz2, zz3, zz4, s0, s1, s2, s3, s4, w0, w1, w2, w3, w4, g, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] ∗
        cellsFrom out (outList xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4 zz0 zz1 zz2 zz3 zz4 w0 w1 w2 w3 w4) ∗ F) →
      Q sf) :
    RL mpl (mkS sb (mpl.base 7 + BitVec.ofNat 64 180) r SP ps m v) Q := by
  -- stack reads (all before any store)
  have q0 := cells_read _ _ _ _ hm 0 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q0
  have q1 := cells_read _ _ _ _ hm 1 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q1
  have q2 := cells_read _ _ _ _ hm 2 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q2
  have q3 := cells_read _ _ _ _ hm 3 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q3
  have q4 := cells_read _ _ _ _ hm 4 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q4
  have q5 := cells_read _ _ _ _ hm 5 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q5
  have q6 := cells_read _ _ _ _ hm 6 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q6
  have q7 := cells_read _ _ _ _ hm 7 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q7
  have q8 := cells_read _ _ _ _ hm 8 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q8
  have q9 := cells_read _ _ _ _ hm 9 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q9
  have q20 := cells_read _ _ _ _ hm 20 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q20
  have q21 := cells_read _ _ _ _ hm 21 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q21
  have q22 := cells_read _ _ _ _ hm 22 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q22
  have q23 := cells_read _ _ _ _ hm 23 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q23
  have q24 := cells_read _ _ _ _ hm 24 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at q24
  have hmo := hm
  rw [sepConj_left_comm] at hmo
  -- 180: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_180 hP) ?_
  rw [ex_ldp64_sp 8#5 16#5 (by decide) (by decide) _ hal q5.2.1 (by rw [a8 SP 40 48 rfl]; exact q6.2.1), pc_add, a8 SP 40 48 rfl, q5.1, q6.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 184: r.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVN) (Arm64.Reg.gp
  refine RL.mk hrun (f07_184 hP) ?_
  rw [ex_movn64 13#5 (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 188: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_188 hP) ?_
  rw [ex_ldp64_sp 15#5 0#5 (by decide) (by decide) _ hal q0.2.1 (by rw [a8 SP 0 8 rfl]; exact q1.2.1), pc_add, a8 SP 0 8 rfl, q0.1, q1.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 192: r.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gp
  refine RL.mk hrun (f07_192 hP) ?_
  rw [ex_movk64_48 13#5 (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 196: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_196 hP) ?_
  rw [ex_ldp64_sp 17#5 18#5 (by decide) (by decide) _ hal q7.2.1 (by rw [a8 SP 56 64 rfl]; exact q8.2.1), pc_add, a8 SP 56 64 rfl, q7.1, q8.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 200: r.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 
  refine RL.mk hrun (f07_200 hP) ?_
  rw [ex_ldr64_sp 2#5 (by decide) _ hal q9.2.1, pc_add, q9.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 204: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_204 hP) ?_
  rw [ex_ldp64_sp 1#5 3#5 (by decide) (by decide) _ hal q2.2.1 (by rw [a8 SP 16 24 rfl]; exact q3.2.1), pc_add, a8 SP 16 24 rfl, q2.1, q3.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 208: r.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 
  refine RL.mk hrun (f07_208 hP) ?_
  rw [ex_ldr64_sp 4#5 (by decide) _ hal q4.2.1, pc_add, q4.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 212: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_212 hP) ?_
  rw [ex_add_rr 11#5 15#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 216: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_216 hP) ?_
  rw [ex_add_rr 8#5 8#5 13#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 220: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_220 hP) ?_
  rw [ex_add_rr 14#5 0#5 16#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 224: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_224 hP) ?_
  rw [ex_sub_rr 15#5 8#5 15#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 228: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_228 hP) ?_
  rw [ex_sub_rr 16#5 16#5 0#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 232: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gp
  refine RL.mk hrun (f07_232 hP) ?_
  rw [ex_orr_imm 8#5 (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 236: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_236 hP) ?_
  rw [ex_sub_rr 0#5 17#5 1#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 240: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_240 hP) ?_
  rw [ex_add_rr 12#5 1#5 17#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 244: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_244 hP) ?_
  rw [ex_add_rr 17#5 16#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 248: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_248 hP) ?_
  rw [ex_add_rr 16#5 0#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 252: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_252 hP) ?_
  rw [ex_sub_rr 0#5 2#5 4#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 256: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_256 hP) ?_
  rw [ex_add_rr 10#5 3#5 18#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 260: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_260 hP) ?_
  rw [ex_sub_rr 1#5 18#5 3#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 264: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_264 hP) ?_
  rw [ex_add_rr 18#5 0#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 268: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_268 hP) ?_
  rw [ex_add_rr 9#5 4#5 2#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 272: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_272 hP) ?_
  have e1 : SP + BitVec.ofNat 64 208 + 0xffffffffffffffe8#64 = SP + BitVec.ofNat 64 184 := aoff SP 208 18446744073709551592 184 rfl
  rw [ex_ldp64_gpr' 26#5 0#5 29#5 (by decide) (by decide) (by decide) _ (x := SP + BitVec.ofNat 64 208) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29]) (by rw [e1]; exact q23.2.1) (by rw [e1, a8 SP 184 192 rfl]; exact q24.2.1), pc_add, e1, a8 SP 184 192 rfl, q23.1, q24.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 276: r.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 
  refine RL.mk hrun (f07_276 hP) ?_
  have e1 : SP + BitVec.ofNat 64 208 + 0xffffffffffffffe0#64 = SP + BitVec.ofNat 64 176 := aoff SP 208 18446744073709551584 176 rfl
  rw [ex_ldur64_gpr' 7#5 29#5 (by decide) (by decide) _ (x := SP + BitVec.ofNat 64 208) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29]) (by rw [e1]; exact q22.2.1), pc_add, e1, q22.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 280: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_280 hP) ?_
  have e1 : SP + BitVec.ofNat 64 208 + 0xffffffffffffffd0#64 = SP + BitVec.ofNat 64 160 := aoff SP 208 18446744073709551568 160 rfl
  rw [ex_ldp64_gpr' 4#5 5#5 29#5 (by decide) (by decide) (by decide) _ (x := SP + BitVec.ofNat 64 208) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29]) (by rw [e1]; exact q20.2.1) (by rw [e1, a8 SP 160 168 rfl]; exact q21.2.1), pc_add, e1, a8 SP 160 168 rfl, q20.1, q21.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 284: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_284 hP) ?_
  rw [ex_add_rr 1#5 1#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 288: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_288 hP) ?_
  rw [ex_sub_rr 7#5 7#5 12#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 292: r.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gp
  refine RL.mk hrun (f07_292 hP) ?_
  rw [ex_lsr51 2#5 18#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 296: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_296 hP) ?_
  rw [ex_and_imm 18#5 18#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 300: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_300 hP) ?_
  rw [ex_sub_rr 6#5 0#5 9#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 304: r.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gp
  refine RL.mk hrun (f07_304 hP) ?_
  rw [ex_movz32 0#5 (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 308: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_308 hP) ?_
  rw [ex_sub_rr 26#5 26#5 10#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 312: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_312 hP) ?_
  rw [ex_sub_rr 4#5 4#5 11#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 316: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_316 hP) ?_
  rw [ex_add_rr 6#5 6#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 320: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_320 hP) ?_
  rw [ex_sub_rr 5#5 5#5 14#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 324: r.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gp
  refine RL.mk hrun (f07_324 hP) ?_
  rw [ex_lsr51 25#5 6#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 328: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_328 hP) ?_
  rw [ex_add_rr 4#5 4#5 13#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 332: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_332 hP) ?_
  rw [ex_add_rr 5#5 5#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 336: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_336 hP) ?_
  rw [ex_and_imm 27#5 4#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 340: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_340 hP) ?_
  rw [ex_add_rr 7#5 7#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 344: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_344 hP) ?_
  rw [ex_add_rr 26#5 26#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 348: r.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Re
  refine RL.mk hrun (f07_348 hP) ?_
  rw [ex_umaddl 25#5 25#5 0#5 27#5 (by decide) (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 352: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_352 hP) ?_
  rw [ex_and_imm 27#5 5#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 356: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_356 hP) ?_
  rw [ex_and_imm 28#5 7#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 360: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_360 hP) ?_
  rw [ex_add_lsr51 4#5 27#5 4#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 364: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_364 hP) ?_
  rw [ex_and_imm 27#5 26#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 368: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_368 hP) ?_
  rw [ex_add_lsr51 5#5 28#5 5#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 372: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_372 hP) ?_
  rw [ex_and_imm 6#5 6#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 376: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_376 hP) ?_
  rw [ex_add_lsr51 7#5 27#5 7#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 380: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_380 hP) ?_
  rw [ex_and_imm 3#5 15#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 384: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_384 hP) ?_
  rw [ex_add_lsr51 6#5 6#5 26#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 388: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x04
  refine RL_stp 25#5 4#5 19#5 (by decide) (by decide) (by decide) _ 0 hrun (f07_388 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo ?_
  intro m1 hmo1
  clear hmo
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo1
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 392: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_392 hP) ?_
  rw [ex_and_imm 4#5 17#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 396: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x07
  refine RL_stp 5#5 7#5 19#5 (by decide) (by decide) (by decide) _ 2 hrun (f07_396 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo1 ?_
  intro m2 hmo2
  clear hmo1
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo2
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 400: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_400 hP) ?_
  rw [ex_and_imm 5#5 16#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 404: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_404 hP) ?_
  rw [ex_add_lsr51 15#5 4#5 15#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 408: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0b
  refine RL_stp 6#5 11#5 19#5 (by decide) (by decide) (by decide) _ 4 hrun (f07_408 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo2 ?_
  intro m3 hmo3
  clear hmo2
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo3
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 412: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_412 hP) ?_
  rw [ex_add_lsr51 11#5 5#5 17#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 416: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_416 hP) ?_
  rw [ex_add_lsr51 17#5 18#5 1#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 420: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_420 hP) ?_
  rw [ex_and_imm 25#5 1#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 424: r.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Re
  refine RL.mk hrun (f07_424 hP) ?_
  rw [ex_umaddl 2#5 2#5 0#5 3#5 (by decide) (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 428: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_428 hP) ?_
  rw [ex_add_lsl1 13#5 13#5 21#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 432: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0c
  refine RL_stp 14#5 12#5 19#5 (by decide) (by decide) (by decide) _ 6 hrun (f07_432 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo3 ?_
  intro m4 hmo4
  clear hmo3
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo4
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 436: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_436 hP) ?_
  rw [ex_add_lsr51 14#5 25#5 16#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 440: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_440 hP) ?_
  rw [ex_sub_rr 12#5 22#5 15#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 444: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_444 hP) ?_
  rw [ex_sub_rr 16#5 24#5 17#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 448: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09
  refine RL_stp 10#5 9#5 19#5 (by decide) (by decide) (by decide) _ 8 hrun (f07_448 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo4 ?_
  intro m5 hmo5
  clear hmo4
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo5
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 452: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_452 hP) ?_
  rw [ex_add_rr 10#5 12#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 456: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_456 hP) ?_
  rw [ex_add_rr 12#5 16#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 460: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_460 hP) ?_
  rw [ex_sub_rr 13#5 13#5 2#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 464: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_464 hP) ?_
  rw [ex_sub_rr 9#5 23#5 11#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 468: r.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gp
  refine RL.mk hrun (f07_468 hP) ?_
  rw [ex_lsr51 16#5 12#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 472: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gp
  refine RL.mk hrun (f07_472 hP) ?_
  rw [ex_sub_rr 18#5 20#5 14#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 476: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x0f
  refine RL_stp 2#5 15#5 19#5 (by decide) (by decide) (by decide) _ 10 hrun (f07_476 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo5 ?_
  intro m6 hmo6
  clear hmo5
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo6
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 480: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_480 hP) ?_
  rw [ex_add_rr 9#5 9#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 484: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_484 hP) ?_
  rw [ex_and_imm 15#5 13#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 488: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0e
  refine RL_stp 11#5 14#5 19#5 (by decide) (by decide) (by decide) _ 12 hrun (f07_488 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo6 ?_
  intro m7 hmo7
  clear hmo6
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo7
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 492: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_492 hP) ?_
  rw [ex_add_rr 8#5 18#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 496: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_496 hP) ?_
  rw [ex_and_imm 11#5 10#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 500: r.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Re
  refine RL.mk hrun (f07_500 hP) ?_
  rw [ex_umaddl 15#5 16#5 0#5 15#5 (by decide) (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 504: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_504 hP) ?_
  rw [ex_and_imm 14#5 9#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 508: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_508 hP) ?_
  rw [ex_add_lsr51 11#5 11#5 13#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 512: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_512 hP) ?_
  rw [ex_and_imm 13#5 8#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 516: r.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gp
  refine RL.mk hrun (f07_516 hP) ?_
  rw [ex_and_imm 12#5 12#5 (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 520: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_520 hP) ?_
  rw [ex_add_lsr51 10#5 14#5 10#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 524: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_524 hP) ?_
  rw [ex_add_lsr51 9#5 13#5 9#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 528: r.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gp
  refine RL.mk hrun (f07_528 hP) ?_
  rw [ex_add_lsr51 8#5 12#5 8#5 (by decide) (by decide) (by decide), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 532: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0f
  refine RL_stp 17#5 15#5 19#5 (by decide) (by decide) (by decide) _ 14 hrun (f07_532 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo7 ?_
  intro m8 hmo8
  clear hmo7
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo8
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 536: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a
  refine RL_stp 11#5 10#5 19#5 (by decide) (by decide) (by decide) _ 16 hrun (f07_536 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo8 ?_
  intro m9 hmo9
  clear hmo8
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo9
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 540: r.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08
  refine RL_stp 9#5 8#5 19#5 (by decide) (by decide) (by decide) _ 18 hrun (f07_540 hP) (by simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29] <;> rfl) (by simp) hmo9 ?_
  intro m10 hmo10
  clear hmo9
  simp (config := { decide := true }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, List.set_cons_succ, List.set_cons_zero] at hmo10
  rw [pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 544: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_544 hP) ?_
  have hmf := hmo10
  rw [sepConj_left_comm] at hmf
  have p26 := cells_read _ _ _ _ hmf 26 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p26
  have p27 := cells_read _ _ _ _ hmf 27 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p27
  have p28 := cells_read _ _ _ _ hmf 28 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p28
  have p29 := cells_read _ _ _ _ hmf 29 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p29
  have p30 := cells_read _ _ _ _ hmf 30 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p30
  have p31 := cells_read _ _ _ _ hmf 31 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p31
  have p32 := cells_read _ _ _ _ hmf 32 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p32
  have p33 := cells_read _ _ _ _ hmf 33 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p33
  have p34 := cells_read _ _ _ _ hmf 34 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p34
  have p35 := cells_read _ _ _ _ hmf 35 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p35
  have p36 := cells_read _ _ _ _ hmf 36 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p36
  have p37 := cells_read _ _ _ _ hmf 37 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at p37
  rw [ex_ldp64_sp 20#5 19#5 (by decide) (by decide) _ hal p36.2.1 (by rw [a8 SP 288 296 rfl]; exact p37.2.1), pc_add, a8 SP 288 296 rfl, p36.1, p37.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 548: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_548 hP) ?_
  rw [ex_ldp64_sp 22#5 21#5 (by decide) (by decide) _ hal p34.2.1 (by rw [a8 SP 272 280 rfl]; exact p35.2.1), pc_add, a8 SP 272 280 rfl, p34.1, p35.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 552: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_552 hP) ?_
  rw [ex_ldp64_sp 24#5 23#5 (by decide) (by decide) _ hal p32.2.1 (by rw [a8 SP 256 264 rfl]; exact p33.2.1), pc_add, a8 SP 256 264 rfl, p32.1, p33.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 556: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_556 hP) ?_
  rw [ex_ldp64_sp 26#5 25#5 (by decide) (by decide) _ hal p30.2.1 (by rw [a8 SP 240 248 rfl]; exact p31.2.1), pc_add, a8 SP 240 248 rfl, p30.1, p31.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 560: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_560 hP) ?_
  rw [ex_ldp64_sp 28#5 27#5 (by decide) (by decide) _ hal p28.2.1 (by rw [a8 SP 224 232 rfl]; exact p29.2.1), pc_add, a8 SP 224 232 rfl, p28.1, p29.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 564: r.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gp
  refine RL.mk hrun (f07_564 hP) ?_
  rw [ex_ldp64_sp 29#5 30#5 (by decide) (by decide) _ hal p26.2.1 (by rw [a8 SP 208 216 rfl]; exact p27.2.1), pc_add, a8 SP 208 216 rfl, p26.1, p27.1]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 568: r.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.sp) 
  refine RL.mk hrun (f07_568 hP) ?_
  rw [ex_add_sp, z12 _ (by norm_num), pc_add]
  simp (config := { decide := true, failIfUnchanged := false }) only [upd_apply, ite_true, ite_false, h19, h20, h21, h22, h23, h24, h29, bias0_eq, c19_eq, Nat.reduceAdd]
  -- 572: r.ret (Arm64.Reg.gpr 0x1e#5))
  refine RL.mk hrun (f07_572 hP) ?_
  rw [ex_ret]
  refine RL.done (hQ _ hrun ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl hmf)
  all_goals simp (config := { decide := true }) only [mkS_pc, mkS_sp, mkS_regs', upd_apply, ite_true, ite_false]

end X25519Dalek.EDbl
end

section
/-! # The field arithmetic of `ProjectivePoint::double`

The twenty words `outList …` written by block 7 are the `CompletedPoint` `edProjDouble X Y Z`,
with limbs below `2^52, 2^53, 2^52, 2^52`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

open Arm64 hiding fpAdd fpSub fpMul fpNeg

theorem mask51_toNat (d : BitVec 64) :
    (d &&& 2251799813685247#64).toNat = d.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem lsr51_toNat (d : BitVec 64) :
    (d >>> 51).toNat = d.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem umaddl19_lsr51_toNat (d0 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) +
      BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64).toNat =
      d0.toNat % 2 ^ 51 + (d4.toNat / 2 ^ 51) * 19 := by
  have hd4 : d4.toNat < 2 ^ 64 := d4.isLt
  have hze : (BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51))).toNat = d4.toNat / 2 ^ 51 := by
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, lsr51_toNat]
    omega
  have hm := mask51_toNat d0
  rw [BitVec.toNat_add, BitVec.toNat_mul, hze, hm, show (19#64).toNat = 19 from rfl]
  omega

theorem add_mask51_lsr51_toNat (di dprev : BitVec 64) :
    ((di &&& 2251799813685247#64) + (dprev >>> 51)).toNat =
      di.toNat % 2 ^ 51 + dprev.toNat / 2 ^ 51 := by
  have hprev : dprev.toNat < 2 ^ 64 := dprev.isLt
  rw [BitVec.toNat_add, mask51_toNat, lsr51_toNat]
  omega

theorem fe51Reduce_bounded (d0 d1 d2 d3 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) +
      BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64).toNat < 2 ^ 52 ∧
    ((d1 &&& 2251799813685247#64) + (d0 >>> 51)).toNat < 2 ^ 52 ∧
    ((d2 &&& 2251799813685247#64) + (d1 >>> 51)).toNat < 2 ^ 52 ∧
    ((d3 &&& 2251799813685247#64) + (d2 >>> 51)).toNat < 2 ^ 52 ∧
    ((d4 &&& 2251799813685247#64) + (d3 >>> 51)).toNat < 2 ^ 52 := by
  have h0 := d0.isLt; have h1 := d1.isLt; have h2 := d2.isLt; have h3 := d3.isLt; have h4 := d4.isLt
  rw [umaddl19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
    add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
  omega

theorem fe51Reduce_val_mod (d0 d1 d2 d3 d4 : BitVec 64) :
    fe51Val
      ((d0 &&& 2251799813685247#64) +
        BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64)
      ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
      ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
      ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
      ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) % p25519 =
    fe51Val d0 d1 d2 d3 d4 % p25519 := by
  have hid :
      fe51Val
        ((d0 &&& 2251799813685247#64) +
          BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64)
        ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
        ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
        ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
        ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) +
      p25519 * (d4.toNat / 2 ^ 51) =
      fe51Val d0 d1 d2 d3 d4 := by
    unfold fe51Val p25519
    rw [umaddl19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
      add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
    omega
  rw [← hid, Nat.add_mul_mod_self_left]

theorem bv64_add_bias0_sub (a b : BitVec 64) :
    (a + 36028797018963664#64) - b = (a - b) + 36028797018963664#64 := by
  bv_omega

theorem bv64_bias0_add_sub (a b : BitVec 64) :
    (36028797018963664#64 + a) - b = (a - b) + 36028797018963664#64 := by
  bv_omega

theorem sub_bias0_toNat (a b : BitVec 64) (ha : a.toNat < 2 ^ 54) (hb : b.toNat < 2 ^ 54) :
    ((a - b) + 36028797018963664#64).toNat = a.toNat + 36028797018963664 - b.toNat := by
  bv_omega

theorem sub_bias1_toNat (a b : BitVec 64) (ha : a.toNat < 2 ^ 54) (hb : b.toNat < 2 ^ 54) :
    ((a - b) + 36028797018963952#64).toNat = a.toNat + 36028797018963952 - b.toNat := by
  bv_omega

theorem fe51Sub_val_mod (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) {B1 B2 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hb : b0.toNat < B2 ∧ b1.toNat < B2 ∧ b2.toNat < B2 ∧
          b3.toNat < B2 ∧ b4.toNat < B2)
    (hB1 : decide (B1 ≤ 2 ^ 54) = true := by decide)
    (hB2 : decide (B2 ≤ 2 ^ 54) = true := by decide) :
    fe51Val
      ((a0 - b0) + 36028797018963664#64)
      ((a1 - b1) + 36028797018963952#64)
      ((a2 - b2) + 36028797018963952#64)
      ((a3 - b3) + 36028797018963952#64)
      ((a4 - b4) + 36028797018963952#64) % p25519 =
    fpSub (fe51Val a0 a1 a2 a3 a4 % p25519) (fe51Val b0 b1 b2 b3 b4 % p25519) := by
  have hle1 : B1 ≤ 2 ^ 54 := of_decide_eq_true hB1
  have hle2 : B2 ≤ 2 ^ 54 := of_decide_eq_true hB2
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4⟩
  have hval :
      fe51Val
        ((a0 - b0) + 36028797018963664#64)
        ((a1 - b1) + 36028797018963952#64)
        ((a2 - b2) + 36028797018963952#64)
        ((a3 - b3) + 36028797018963952#64)
        ((a4 - b4) + 36028797018963952#64) =
      fe51Val a0 a1 a2 a3 a4 + 16 * p25519 - fe51Val b0 b1 b2 b3 b4 := by
    unfold fe51Val p25519
    rw [sub_bias0_toNat a0 b0 (by omega) (by omega), sub_bias1_toNat a1 b1 (by omega) (by omega),
        sub_bias1_toNat a2 b2 (by omega) (by omega), sub_bias1_toNat a3 b3 (by omega) (by omega),
        sub_bias1_toNat a4 b4 (by omega) (by omega)]
    omega
  rw [hval]
  unfold fpSub
  have hlt : fe51Val b0 b1 b2 b3 b4 < 16 * p25519 := by
    unfold fe51Val p25519; omega
  have hdiv : fe51Val b0 b1 b2 b3 b4 =
      p25519 * (fe51Val b0 b1 b2 b3 b4 / p25519) + fe51Val b0 b1 b2 b3 b4 % p25519 :=
    (Nat.div_add_mod _ _).symm
  have hq : fe51Val b0 b1 b2 b3 b4 / p25519 ≤ 15 := by
    unfold p25519 at hlt ⊢; omega
  have hmodB_lt : fe51Val b0 b1 b2 b3 b4 % p25519 < p25519 :=
    Nat.mod_lt _ (by unfold p25519; omega)
  have hmodB : (fe51Val b0 b1 b2 b3 b4 % p25519) % p25519 = fe51Val b0 b1 b2 b3 b4 % p25519 :=
    Nat.mod_eq_of_lt hmodB_lt
  rw [hmodB]
  have hrew : fe51Val a0 a1 a2 a3 a4 + 16 * p25519 - fe51Val b0 b1 b2 b3 b4 =
      (fe51Val a0 a1 a2 a3 a4 + (p25519 - fe51Val b0 b1 b2 b3 b4 % p25519)) +
        p25519 * (15 - fe51Val b0 b1 b2 b3 b4 / p25519) := by
    unfold p25519 at hdiv hq hmodB_lt ⊢
    omega
  rw [hrew, Nat.add_mul_mod_self_left, Nat.add_sub_assoc (Nat.le_of_lt hmodB_lt),
      ← Nat.mod_add_mod]

theorem fe51Add_bounded (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) (B : Nat) {B1 B2 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧ a3.toNat < B1 ∧ a4.toNat < B1)
    (hb : b0.toNat < B2 ∧ b1.toNat < B2 ∧ b2.toNat < B2 ∧ b3.toNat < B2 ∧ b4.toNat < B2)
    (hB : decide (B1 + B2 ≤ B ∧ B ≤ 2 ^ 64) = true := by decide) :
    (a0 + b0).toNat < B ∧ (a1 + b1).toNat < B ∧ (a2 + b2).toNat < B ∧
    (a3 + b3).toNat < B ∧ (a4 + b4).toNat < B := by
  have ⟨h1, h2⟩ := of_decide_eq_true hB
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4⟩
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

theorem fe51Add_val_mod (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) {B1 B2 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hb : b0.toNat < B2 ∧ b1.toNat < B2 ∧ b2.toNat < B2 ∧
          b3.toNat < B2 ∧ b4.toNat < B2)
    (hB1 : decide (B1 ≤ 2 ^ 54) = true := by decide)
    (hB2 : decide (B2 ≤ 2 ^ 54) = true := by decide) :
    fe51Val (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) % p25519 =
    fpAdd (fe51Val a0 a1 a2 a3 a4 % p25519) (fe51Val b0 b1 b2 b3 b4 % p25519) := by
  have hle1 : B1 ≤ 2 ^ 54 := of_decide_eq_true hB1
  have hle2 : B2 ≤ 2 ^ 54 := of_decide_eq_true hB2
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4⟩
  have h0 : (a0 + b0).toNat = a0.toNat + b0.toNat := by bv_omega
  have h1 : (a1 + b1).toNat = a1.toNat + b1.toNat := by bv_omega
  have h2 : (a2 + b2).toNat = a2.toNat + b2.toNat := by bv_omega
  have h3 : (a3 + b3).toNat = a3.toNat + b3.toNat := by bv_omega
  have h4 : (a4 + b4).toNat = a4.toNat + b4.toNat := by bv_omega
  have hval :
      fe51Val (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) =
      fe51Val a0 a1 a2 a3 a4 + fe51Val b0 b1 b2 b3 b4 := by
    unfold fe51Val
    rw [h0, h1, h2, h3, h4]
    omega
  rw [hval]
  unfold fpAdd
  exact Nat.add_mod _ _ _

theorem fe51Shl1_bounded (a0 a1 a2 a3 a4 : BitVec 64) (B : Nat) {B1 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hB : decide (2 * B1 ≤ B ∧ B ≤ 2 ^ 64) = true := by decide) :
    (a0 <<< 1).toNat < B ∧ (a1 <<< 1).toNat < B ∧ (a2 <<< 1).toNat < B ∧
    (a3 <<< 1).toNat < B ∧ (a4 <<< 1).toNat < B := by
  have ⟨h1, h2⟩ := of_decide_eq_true hB
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

theorem fe51Shl1_val_mod (a0 a1 a2 a3 a4 : BitVec 64) {B1 : Nat}
    (ha : a0.toNat < B1 ∧ a1.toNat < B1 ∧ a2.toNat < B1 ∧
          a3.toNat < B1 ∧ a4.toNat < B1)
    (hB : decide (B1 ≤ 2 ^ 53) = true := by decide) :
    fe51Val (a0 <<< 1) (a1 <<< 1) (a2 <<< 1) (a3 <<< 1) (a4 <<< 1) % p25519 =
    fpAdd (fe51Val a0 a1 a2 a3 a4 % p25519) (fe51Val a0 a1 a2 a3 a4 % p25519) := by
  have hle : B1 ≤ 2 ^ 53 := of_decide_eq_true hB
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  have h0 : (a0 <<< 1).toNat = 2 * a0.toNat := by bv_omega
  have h1 : (a1 <<< 1).toNat = 2 * a1.toNat := by bv_omega
  have h2 : (a2 <<< 1).toNat = 2 * a2.toNat := by bv_omega
  have h3 : (a3 <<< 1).toNat = 2 * a3.toNat := by bv_omega
  have h4 : (a4 <<< 1).toNat = 2 * a4.toNat := by bv_omega
  have hval :
      fe51Val (a0 <<< 1) (a1 <<< 1) (a2 <<< 1) (a3 <<< 1) (a4 <<< 1) =
      fe51Val a0 a1 a2 a3 a4 + fe51Val a0 a1 a2 a3 a4 := by
    unfold fe51Val
    rw [h0, h1, h2, h3, h4]
    omega
  rw [hval]
  unfold fpAdd
  exact Nat.add_mod _ _ _

theorem fpPow_two_eq_fpSq (x : Nat) : fpPow x 2 = fpSq x := by
  unfold fpPow modPow fpSq fpMul
  rw [modPowLoop, modPowLoop, modPowLoop]
  change (1 * (x % p25519 * (x % p25519) % p25519) % p25519) % p25519 =
    x % p25519 * (x % p25519) % p25519
  simp only [Nat.mod_mod, Nat.one_mul]

/-- The words of `ProjectivePoint::double`'s result: limb bounds and value. -/
theorem outList_ok (xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4 zz0 zz1 zz2 zz3 zz4 w0 w1 w2 w3 w4
    X0 X1 X2 X3 X4 Y0 Y1 Y2 Y3 Y4 Z0 Z1 Z2 Z3 Z4 : BitVec 64)
    (bxx : B5 xx0 xx1 xx2 xx3 xx4 (2 ^ 52)) (byy : B5 yy0 yy1 yy2 yy3 yy4 (2 ^ 52))
    (bzz : B5 zz0 zz1 zz2 zz3 zz4 (2 ^ 52)) (bw : B5 w0 w1 w2 w3 w4 (2 ^ 52))
    (bX : B5 X0 X1 X2 X3 X4 (2 ^ 53)) (bY : B5 Y0 Y1 Y2 Y3 Y4 (2 ^ 53))
    (hxx : fe51Val xx0 xx1 xx2 xx3 xx4 % p25519 = fpPow (fe51Val X0 X1 X2 X3 X4 % p25519) (2 ^ 1))
    (hyy : fe51Val yy0 yy1 yy2 yy3 yy4 % p25519 = fpPow (fe51Val Y0 Y1 Y2 Y3 Y4 % p25519) (2 ^ 1))
    (hzz : fe51Val zz0 zz1 zz2 zz3 zz4 % p25519 = fpPow (fe51Val Z0 Z1 Z2 Z3 Z4 % p25519) (2 ^ 1))
    (hw : fe51Val w0 w1 w2 w3 w4 % p25519 =
      fpPow (fe51Val (Y0 + X0) (Y1 + X1) (Y2 + X2) (Y3 + X3) (Y4 + X4) % p25519) (2 ^ 1)) :
    let res := (outList xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4 zz0 zz1 zz2 zz3 zz4 w0 w1 w2 w3 w4).flatMap
      unpack64
    res.length = 160 ∧ fe51LimbsBoundedAt res 0 (2 ^ 52) ∧ fe51LimbsBoundedAt res 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res 80 (2 ^ 52) ∧ fe51LimbsBoundedAt res 120 (2 ^ 52) ∧
      edExtOfBytes res = edProjDouble (fe51Val X0 X1 X2 X3 X4) (fe51Val Y0 Y1 Y2 Y3 Y4)
        (fe51Val Z0 Z1 Z2 Z3 Z4) := by
  intro res
  have rd := readLE_flat (outList xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4 zz0 zz1 zz2 zz3 zz4 w0 w1 w2 w3 w4)
  have r0 := rd 0 (by simp [outList]); have r1 := rd 1 (by simp [outList])
  have r2 := rd 2 (by simp [outList]); have r3 := rd 3 (by simp [outList])
  have r4 := rd 4 (by simp [outList]); have r5 := rd 5 (by simp [outList])
  have r6 := rd 6 (by simp [outList]); have r7 := rd 7 (by simp [outList])
  have r8 := rd 8 (by simp [outList]); have r9 := rd 9 (by simp [outList])
  have r10 := rd 10 (by simp [outList]); have r11 := rd 11 (by simp [outList])
  have r12 := rd 12 (by simp [outList]); have r13 := rd 13 (by simp [outList])
  have r14 := rd 14 (by simp [outList]); have r15 := rd 15 (by simp [outList])
  have r16 := rd 16 (by simp [outList]); have r17 := rd 17 (by simp [outList])
  have r18 := rd 18 (by simp [outList]); have r19 := rd 19 (by simp [outList])
  simp only [outList, Nat.reduceMul, List.getElem_cons_succ, List.getElem_cons_zero] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
  obtain ⟨a0, a1, a2, a3, a4⟩ := bxx
  obtain ⟨b0, b1, b2, b3, b4⟩ := byy
  obtain ⟨c0, c1, c2, c3, c4⟩ := bzz
  obtain ⟨d0, d1, d2, d3, d4⟩ := bw
  -- the pieces
  have hadd_b := fe51Add_bounded xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4 (2 ^ 53)
    ⟨a0, a1, a2, a3, a4⟩ ⟨b0, b1, b2, b3, b4⟩
  have hadd_v := fe51Add_val_mod xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4
    ⟨a0, a1, a2, a3, a4⟩ ⟨b0, b1, b2, b3, b4⟩
  have hzb := fe51Reduce_bounded (yy0 + 36028797018963664#64 - xx0) (yy1 - xx1 + 36028797018963952#64)
    (yy2 - xx2 + 36028797018963952#64) (yy3 - xx3 + 36028797018963952#64)
    (yy4 - xx4 + 36028797018963952#64)
  have hshl_b := fe51Shl1_bounded zz0 zz1 zz2 zz3 zz4 (2 ^ 53) ⟨c0, c1, c2, c3, c4⟩
  have hshl_v := fe51Shl1_val_mod zz0 zz1 zz2 zz3 zz4 ⟨c0, c1, c2, c3, c4⟩
  have hsum_v := fe51Add_val_mod Y0 Y1 Y2 Y3 Y4 X0 X1 X2 X3 X4 bY bX
  refine ⟨by simp [res, outList, flatMap_unpack64_length], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [fe51LimbsBoundedAt, Nat.reduceAdd, res, outList, r0, r1, r2, r3, r4]
    exact fe51Reduce_bounded _ _ _ _ _
  · simp only [fe51LimbsBoundedAt, Nat.reduceAdd, res, outList, r5, r6, r7, r8, r9]
    exact hadd_b
  · simp only [fe51LimbsBoundedAt, Nat.reduceAdd, res, outList, r10, r11, r12, r13, r14]
    exact hzb
  · simp only [fe51LimbsBoundedAt, Nat.reduceAdd, res, outList, r15, r16, r17, r18, r19]
    exact fe51Reduce_bounded _ _ _ _ _
  · simp only [edExtOfBytes, fe51ValAt, Nat.reduceAdd, res, outList, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9,
      r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, edProjDouble]
    rw [fe51Reduce_val_mod, fe51Reduce_val_mod, fe51Reduce_val_mod,
      bv64_add_bias0_sub, bv64_bias0_add_sub,
      fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ ⟨d0, d1, d2, d3, d4⟩ hadd_b,
      fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hshl_b (fe51Reduce_bounded _ _ _ _ _),
      fe51Reduce_val_mod,
      fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ ⟨b0, b1, b2, b3, b4⟩ ⟨a0, a1, a2, a3, a4⟩]
    rw [hadd_v, hshl_v, hw, hxx, hyy, hzz, hsum_v]
    simp only [Nat.pow_one, fpPow_two_eq_fpSq]
    unfold fpAdd
    rw [Nat.add_comm (fe51Val Y0 Y1 Y2 Y3 Y4 % p25519) (fe51Val X0 X1 X2 X3 X4 % p25519)]

end X25519Dalek.EDbl
end

section
/-! # `ProjectivePoint::double` (block 7): the contract (generated by tools/mk_main.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EDbl

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

theorem wordsOf15 (bs : List (BitVec 8)) : wordsOf bs 0 15 = [ByteSlice.readLE bs 0 8, ByteSlice.readLE bs 8 8, ByteSlice.readLE bs 16 8, ByteSlice.readLE bs 24 8, ByteSlice.readLE bs 32 8, ByteSlice.readLE bs 40 8, ByteSlice.readLE bs 48 8, ByteSlice.readLE bs 56 8, ByteSlice.readLE bs 64 8, ByteSlice.readLE bs 72 8, ByteSlice.readLE bs 80 8, ByteSlice.readLE bs 88 8, ByteSlice.readLE bs 96 8, ByteSlice.readLE bs 104 8, ByteSlice.readLE bs 112 8] := rfl
theorem wordsOf20 (bs : List (BitVec 8)) : wordsOf bs 0 20 = [ByteSlice.readLE bs 0 8, ByteSlice.readLE bs 8 8, ByteSlice.readLE bs 16 8, ByteSlice.readLE bs 24 8, ByteSlice.readLE bs 32 8, ByteSlice.readLE bs 40 8, ByteSlice.readLE bs 48 8, ByteSlice.readLE bs 56 8, ByteSlice.readLE bs 64 8, ByteSlice.readLE bs 72 8, ByteSlice.readLE bs 80 8, ByteSlice.readLE bs 88 8, ByteSlice.readLE bs 96 8, ByteSlice.readLE bs 104 8, ByteSlice.readLE bs 112 8, ByteSlice.readLE bs 120 8, ByteSlice.readLE bs 128 8, ByteSlice.readLE bs 136 8, ByteSlice.readLE bs 144 8, ByteSlice.readLE bs 152 8] := rfl
theorem wordsOf38 (bs : List (BitVec 8)) : wordsOf bs 0 38 = [ByteSlice.readLE bs 0 8, ByteSlice.readLE bs 8 8, ByteSlice.readLE bs 16 8, ByteSlice.readLE bs 24 8, ByteSlice.readLE bs 32 8, ByteSlice.readLE bs 40 8, ByteSlice.readLE bs 48 8, ByteSlice.readLE bs 56 8, ByteSlice.readLE bs 64 8, ByteSlice.readLE bs 72 8, ByteSlice.readLE bs 80 8, ByteSlice.readLE bs 88 8, ByteSlice.readLE bs 96 8, ByteSlice.readLE bs 104 8, ByteSlice.readLE bs 112 8, ByteSlice.readLE bs 120 8, ByteSlice.readLE bs 128 8, ByteSlice.readLE bs 136 8, ByteSlice.readLE bs 144 8, ByteSlice.readLE bs 152 8, ByteSlice.readLE bs 160 8, ByteSlice.readLE bs 168 8, ByteSlice.readLE bs 176 8, ByteSlice.readLE bs 184 8, ByteSlice.readLE bs 192 8, ByteSlice.readLE bs 200 8, ByteSlice.readLE bs 208 8, ByteSlice.readLE bs 216 8, ByteSlice.readLE bs 224 8, ByteSlice.readLE bs 232 8, ByteSlice.readLE bs 240 8, ByteSlice.readLE bs 248 8, ByteSlice.readLE bs 256 8, ByteSlice.readLE bs 264 8, ByteSlice.readLE bs 272 8, ByteSlice.readLE bs 280 8, ByteSlice.readLE bs 288 8, ByteSlice.readLE bs 296 8] := rfl

theorem final_mem {m : Memory} {SP self out : BitVec 64} {S Sf L : List (BitVec 64)} {R : SepProp}
    {self_bs : List (BitVec 8)} (hS : S.length = 38) (hSf : cellsFrom self Sf = (self ↦ₛ self_bs))
    (h : m ⊨ cellsFrom SP S ∗ cellsFrom out L ∗ (cellsFrom self Sf ∗ memRegion (SP - BitVec.ofNat 64 96) 96 ∗ R)) :
    m ⊨ (self ↦ₛ self_bs) ∗ memRegion (SP - BitVec.ofNat 64 96) 400 ∗ (out ↦ₛ L.flatMap unpack64) ∗ R := by
  have h1 := sat_sep_mono h (cellsFrom_entails_memRegion SP S (by rw [hS]; norm_num))
  rw [hS, hSf, cellsFrom_eq_bytes] at h1
  have h2 := Satisfies.of_eq h1 (Q := (memRegion (SP - BitVec.ofNat 64 96) 96 ∗ memRegion SP (8 * 38)) ∗
    ((self ↦ₛ self_bs) ∗ (out ↦ₛ L.flatMap unpack64) ∗ R))
  have h3 := sat_sep_mono h2 (memRegion_merge (SP - BitVec.ofNat 64 96) SP 96 (8 * 38) (by bv_omega)
    (by norm_num) (by norm_num))
  exact Satisfies.of_eq h3

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

set_option maxHeartbeats 4000000 in
theorem dbl_ok (hK : fnOk p2kName (fun _ => fe51Pow2kSpec)) :
    fnOk dblName (fun _ => projectivePointDoubleSpec) := by
  refine ⟨7, 0, dbl_lookup, fun mpl hP => ?_⟩
  rintro ⟨out, self, out_bs, self_bs⟩ R s0 hpc hrun hpre hal hCLp
  have hfa : x25519CliMultiLib.fnAddr mpl dblName = mpl.base 7 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, dbl_lookup]
  rw [hfa] at hpc
  change s0.mem ⊨ ((⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = self ∧ out_bs.length = 160 ∧
      self_bs.length = 120 ∧ fe51LimbsBoundedAt self_bs 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt self_bs 40 (2 ^ 53) ∧ fe51LimbsBoundedAt self_bs 80 (2 ^ 54)⌝ ∗
      (self ↦ₛ self_bs) ∗ (out ↦ₛ out_bs) ∗ stackFrame s0 400) ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) ∗ R at hpre
  have h1 := Satisfies.of_eq hpre
    (Q := ⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = self ∧ out_bs.length = 160 ∧
      self_bs.length = 120 ∧ fe51LimbsBoundedAt self_bs 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt self_bs 40 (2 ^ 53) ∧ fe51LimbsBoundedAt self_bs 80 (2 ^ 54)⌝ ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ stackFrame s0 400 ∗
      ((self ↦ₛ self_bs) ∗ (out ↦ₛ out_bs) ∗ R))
  rw [sat_pure_sep, sat_pure_sep] at h1
  obtain ⟨⟨hx8, hx0, hlo, hls, hb0, hb40, hb80⟩, hCL, h1⟩ := h1
  clear hpre
  have hal0 : s0.sp &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
  have halSP : (s0.sp - BitVec.ofNat 64 304) &&& 0b1111#64 = 0#64 :=
    al16_sub _ 304 (by norm_num) (by norm_num) hal0
  generalize hSP : s0.sp - BitVec.ofNat 64 304 = SP at halSP
  have hst : stackFrame s0 400 = memRegion (SP - BitVec.ofNat 64 96) (96 + 8 * 38) := by
    show memRegion _ _ = _
    rw [show s0.sp - BitVec.ofNat 64 400 = SP - BitVec.ofNat 64 96 by rw [← hSP]; bv_omega]
  rw [hst] at h1
  have h2 := sat_sep_mono h1 (memRegion_split _ 96 (8 * 38) (by norm_num))
  rw [show SP - BitVec.ofNat 64 96 + BitVec.ofNat 64 96 = SP by bv_omega, sepConj_assoc] at h2
  rw [sepConj_left_comm] at h2
  have h3 := sat_sep_mono h2 (memRegion_entails_bytes SP (8 * 38) (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨bs, h3⟩ := h3
  rw [sepConj_assoc, sat_pure_sep] at h3
  obtain ⟨hlb, h3⟩ := h3
  rw [bytes_eq_cells SP bs 38 hlb, bytes_eq_cells self self_bs 15 (by rw [hls]),
    bytes_eq_cells out out_bs 20 (by rw [hlo]), wordsOf38, wordsOf15, wordsOf20] at h3
  rw [sepConj_left_comm (memRegion (SP - BitVec.ofNat 64 96) 96),
    sepConj_left_comm (memRegion (SP - BitVec.ofNat 64 96) 96)] at h3
  have h8 : s0.regs.regs 8#5 = out := by simpa [readGpr_unfold] using hx8
  have h0 : s0.regs.regs 0#5 = self := by simpa [readGpr_unfold] using hx0
  simp only [fe51LimbsBoundedAt, Nat.reduceAdd] at hb0 hb40 hb80
  show Reach (bprog mpl 7) s0 _
  refine reach_congr (s' := mkS s0 (mpl.base 7 + BitVec.ofNat 64 0) s0.regs.regs s0.sp s0.pstate
    s0.mem s0.vregs.regs) (by rw [← hpc]; rfl) ?_
  refine segAB hP hK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun halSP hSP h8 h0 h3 hb0 hb40 hb80 ?_ hCL
  intro sb' r' ps' m' v' xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4 zz0 zz1 zz2 zz3 zz4 w0 w1 w2 w3 w4
    hrun' g19 g21 g22 g23 g20 g24 g29 hv' hm' bxx byy bzz bw hxx hyy hzz hw
  unfold Heap7 at hm'
  rw [sepConj_left_comm (cellsFrom self _) (cellsFrom out _)] at hm'
  refine segC hP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun' halSP g19 g21 g22 g23 g20 g24 g29 hm' ?_
  intro sf hrunf hpcf hspf f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 hvf hmf
  have hspS : sf.sp = s0.sp := by rw [hspf, ← hSP]; bv_omega
  left
  refine ⟨⟨?_, hspS, hrunf⟩, ⟨hspS, ?_⟩, ?_⟩
  · rw [hpcf]; simp [readGpr_unfold, Reg.lr]
  · simp only [CalleeSavedPreserved, readGpr_unfold]
    simp (config := { decide := true }) only [ite_false, Reg.fp, f19, f20, f21, f22, f23, f24, f25, f26,
      f27, f28, f29, true_and]
    show VRegFile.calleeSaved sf.vregs = VRegFile.calleeSaved s0.vregs
    rw [show sf.vregs = ⟨v'⟩ from by rw [← hvf]]
    exact hv'
  · obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5⟩ := outList_ok xx0 xx1 xx2 xx3 xx4 yy0 yy1 yy2 yy3 yy4
      zz0 zz1 zz2 zz3 zz4 w0 w1 w2 w3 w4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bxx byy bzz bw hb0 hb40 hxx hyy hzz hw
    have hfm := final_mem (by simp) (by rw [← wordsOf15, ← bytes_eq_cells self self_bs 15 (by rw [hls])]) hmf
    simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, projectivePointDoubleSpec, stackFrame]
    rw [show sf.sp - BitVec.ofNat 64 400 = SP - BitVec.ofNat 64 96 by rw [hspf]; bv_omega]
    exact post_intro hfm ⟨hL0, hL1, hL2, hL3, hL4, hL5⟩

theorem fnOk_projectivePoint_double_dev :
    fnOk "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double"
      (fun _ => projectivePointDoubleSpec) :=
  dbl_ok fnOk_fe51_pow2k

end X25519Dalek.EDbl
end

open X25519Dalek in
theorem solution : fnOk "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" (fun _ => projectivePointDoubleSpec) := X25519Dalek.EDbl.fnOk_projectivePoint_double_dev
