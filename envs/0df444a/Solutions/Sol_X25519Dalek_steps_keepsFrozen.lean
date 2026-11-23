-- Prove2me | solution 1 for X25519Dalek.steps_keepsFrozen
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T12:30:27.759151+00:00
-- url     : https://prove2.me/submissions/8611ffc0-8b75-408f-8108-fe7f636473d1

import Mathlib
import Definitions.Def_Arm64_ISA_Semantics

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

theorem canWrite_congr {m m' : Memory} (h : m'.perm = m.perm) (a : BitVec 64) (n : Nat) :
    m'.canWrite a n = m.canWrite a n := allPerm_congr h _ a n
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

/-- `allPerm` as a bounded quantifier. -/
theorem allPerm_iff (m : Memory) (p : Option Perm → Bool) (a : BitVec 64) (n : Nat) :
    m.allPerm p a n = true ↔ ∀ i < n, p (m.perm (a + BitVec.ofNat 64 i)) = true := by
  induction n generalizing a with
  | zero => simp [allPerm]
  | succ n ih =>
    simp only [allPerm, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hs⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := hs i (by omega)
        have e : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
          apply BitVec.eq_of_toNat_eq; simp; omega
        rwa [e] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have e : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; simp; omega
      rw [e]; exact h (i + 1) (by omega)

/-- Split `allPerm` over `[a, a + (n + k))` into `[a, a + n)` and `[a + n, a + n + k)`. -/
theorem allPerm_add (m : Memory) (p : Option Perm → Bool) (a : BitVec 64) (n k : Nat) :
    m.allPerm p a (n + k) = (m.allPerm p a n && m.allPerm p (a + BitVec.ofNat 64 n) k) := by
  induction n generalizing a with
  | zero => simp [allPerm]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [allPerm, ih, Bool.and_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (n + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e]

/-! ## `KeepsFrozen` -/

@[simp]
theorem KeepsFrozen.refl (m : Memory) : m.KeepsFrozen m := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsFrozen.trans {m₁ m₂ m₃ : Memory} (h₁ : m₁.KeepsFrozen m₂) (h₂ : m₂.KeepsFrozen m₃) :
    m₁.KeepsFrozen m₃ := by
  intro a ha
  obtain ⟨hb₁, hp₁, hlf₁, ha₁⟩ := h₁ a ha
  have ha₂ : m₂.Frozen a := by unfold Frozen at *; rw [hp₁]; exact ha
  obtain ⟨hb₂, hp₂, hlf₂, h_an₂⟩ := h₂ a ha₂
  exact ⟨hb₂.trans hb₁, hp₂.trans hp₁, hlf₂.trans hlf₁, h_an₂.trans ha₁⟩

/-- Same permissions and anonymous bits, and the contents / `isLazyFree` only differ at writable bytes. -/
theorem KeepsFrozen.of_perm_eq {m m' : Memory} (hp : m'.perm = m.perm)
    (hb : ∀ a, m.Frozen a → m'.read8 a = m.read8 a)
    (hlf : ∀ a, m.Frozen a → m'.isLazyFree a = m.isLazyFree a := by intros; rfl)
    (hanon : m'.isAnon = m.isAnon := by simp) : m.KeepsFrozen m' :=
  fun a ha => ⟨hb a ha, by rw [hp], hlf a ha, by rw [hanon]⟩

/-- A byte whose permission allows a store (`w && !x`) is not frozen. -/
theorem not_frozen_of_writable {m : Memory} {a : BitVec 64}
    (h : ((m.perm a).w && !(m.perm a).x) = true) : ¬ m.Frozen a := by
  unfold Frozen
  rcases hperm : m.perm a with _ | p <;>
    simp [hperm, Option.w, Option.x, Option.frozen, Perm.frozen] at h ⊢
  intro _; exact h.1

/-- If `[a, a + n)` is writable, every frozen byte lies outside it. -/
theorem ne_of_canWrite {m : Memory} {a : BitVec 64} {n : Nat} (h : m.canWrite a n = true)
    {b : BitVec 64} (hb : m.Frozen b) {i : Nat} (hi : i < n) : b ≠ a + BitVec.ofNat 64 i := by
  rintro rfl
  exact not_frozen_of_writable ((allPerm_iff m _ a n).1 h i hi) hb

theorem keepsFrozen_write8 {m : Memory} {a : BitVec 64} (h : m.canWrite a 1 = true)
    (v : BitVec 8) : m.KeepsFrozen (m.write8 a v) := by
  refine KeepsFrozen.of_perm_eq (by simp)
    (fun b hb => ?_) (fun b hb => ?_)
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    simp only [BitVec.add_zero] at h0; simp [h0]
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    simp only [BitVec.add_zero] at h0; simp [h0]

theorem keepsFrozen_write16 {m : Memory} {a : BitVec 64} (h : m.canWrite a 2 = true)
    (v : BitVec 16) : m.KeepsFrozen (m.write16 a v) := by
  refine KeepsFrozen.of_perm_eq (by simp) (fun b hb => ?_) (fun b hb => ?_)
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    simp only [write16, read8_write8, h0, h1, ↓reduceIte]
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    simp only [write16, isLazyFree_write8, h0, h1, ↓reduceIte]

theorem keepsFrozen_write32 {m : Memory} {a : BitVec 64} (h : m.canWrite a 4 = true)
    (v : BitVec 32) : m.KeepsFrozen (m.write32 a v) := by
  refine KeepsFrozen.of_perm_eq (by simp) (fun b hb => ?_) (fun b hb => ?_)
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    have h2 := ne_of_canWrite h hb (i := 2) (by omega)
    have h3 := ne_of_canWrite h hb (i := 3) (by omega)
    simp only [write32, read8_write8, h0, h1, h2, h3, ↓reduceIte]
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    have h2 := ne_of_canWrite h hb (i := 2) (by omega)
    have h3 := ne_of_canWrite h hb (i := 3) (by omega)
    simp only [write32, isLazyFree_write8, h0, h1, h2, h3, ↓reduceIte]

theorem keepsFrozen_write64 {m : Memory} {a : BitVec 64} (h : m.canWrite a 8 = true)
    (v : BitVec 64) : m.KeepsFrozen (m.write64 a v) := by
  refine KeepsFrozen.of_perm_eq (by simp) (fun b hb => ?_) (fun b hb => ?_)
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    have h2 := ne_of_canWrite h hb (i := 2) (by omega)
    have h3 := ne_of_canWrite h hb (i := 3) (by omega)
    have h4 := ne_of_canWrite h hb (i := 4) (by omega)
    have h5 := ne_of_canWrite h hb (i := 5) (by omega)
    have h6 := ne_of_canWrite h hb (i := 6) (by omega)
    have h7 := ne_of_canWrite h hb (i := 7) (by omega)
    simp only [write64, read8_write8, h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    have h2 := ne_of_canWrite h hb (i := 2) (by omega)
    have h3 := ne_of_canWrite h hb (i := 3) (by omega)
    have h4 := ne_of_canWrite h hb (i := 4) (by omega)
    have h5 := ne_of_canWrite h hb (i := 5) (by omega)
    have h6 := ne_of_canWrite h hb (i := 6) (by omega)
    have h7 := ne_of_canWrite h hb (i := 7) (by omega)
    simp only [write64, isLazyFree_write8, h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]

theorem keepsFrozen_write128 {m : Memory} {a : BitVec 64} (h : m.canWrite a 16 = true)
    (v : BitVec 128) : m.KeepsFrozen (m.write128 a v) := by
  have h' := h
  unfold canWrite at h'
  rw [show (16 : Nat) = 8 + 8 from rfl, allPerm_add, Bool.and_eq_true] at h'
  refine (keepsFrozen_write64 h'.1 _).trans (keepsFrozen_write64 ?_ _)
  rw [canWrite_congr (perm_write64 _ _ _)]
  exact h'.2

theorem keepsFrozen_writeSized {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : m.canWrite a sz.bytes = true) (v : BitVec 64) : m.KeepsFrozen (m.writeSized sz a v) := by
  cases sz
  · exact keepsFrozen_write8 h _
  · exact keepsFrozen_write16 h _
  · exact keepsFrozen_write32 h _
  · exact keepsFrozen_write64 h _

theorem keepsFrozen_writeSimdSized {m : Memory} {sz : SimdMemSize} {a : BitVec 64}
    (h : m.canWrite a sz.bytes = true) (v : BitVec 128) :
    m.KeepsFrozen (m.writeSimdSized sz a v) := by
  cases sz
  · exact keepsFrozen_write8 h _
  · exact keepsFrozen_write16 h _
  · exact keepsFrozen_write32 h _
  · exact keepsFrozen_write64 h _
  · exact keepsFrozen_write128 h _

end Memory

/-! ## Every step keeps frozen memory -/

theorem evalSvc_keepsFrozen (svc : State → State) (s : State) :
    s.mem.KeepsFrozen (evalSvc svc s).mem := by
  intro a hf
  have hf' : (s.mem.perm a).frozen = true := hf
  have hcell : (evalSvc svc s).mem.cells a = s.mem.cells a := by simp [evalSvc, hf']
  simp [Memory.read8, Memory.perm, Memory.isLazyFree, Memory.isAnon, hcell]

@[simp]
theorem evalSvc_tpidrEl0 (svc : State → State) (s : State) :
    (evalSvc svc s).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

namespace Memory

theorem keepsFrozen_writeSized' {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : ¬(!m.canWrite a sz.bytes) = true) (v : BitVec 64) : m.KeepsFrozen (m.writeSized sz a v) :=
  keepsFrozen_writeSized (by simpa using h) v

theorem keepsFrozen_writeSimdSized' {m : Memory} {sz : SimdMemSize} {a : BitVec 64}
    (h : ¬(!m.canWrite a sz.bytes) = true) (v : BitVec 128) :
    m.KeepsFrozen (m.writeSimdSized sz a v) :=
  keepsFrozen_writeSimdSized (by simpa using h) v

theorem keepsFrozen_writeSized2' {m : Memory} {sz : MemWidth} {a b : BitVec 64}
    (h : ¬(!(m.canWrite a sz.bytes && m.canWrite b sz.bytes)) = true) (v w : BitVec 64) :
    m.KeepsFrozen ((m.writeSized sz a v).writeSized sz b w) := by
  have h : m.canWrite a sz.bytes = true ∧ m.canWrite b sz.bytes = true := by simpa using h
  refine (keepsFrozen_writeSized h.1 v).trans (keepsFrozen_writeSized ?_ w)
  rw [canWrite_congr (perm_writeSized _ _ _ _)]; exact h.2

theorem keepsFrozen_writeSimdSized2' {m : Memory} {sz : SimdMemSize} {a b : BitVec 64}
    (h : ¬(!(m.canWrite a sz.bytes && m.canWrite b sz.bytes)) = true) (v w : BitVec 128) :
    m.KeepsFrozen ((m.writeSimdSized sz a v).writeSimdSized sz b w) := by
  have h : m.canWrite a sz.bytes = true ∧ m.canWrite b sz.bytes = true := by simpa using h
  refine (keepsFrozen_writeSimdSized h.1 v).trans (keepsFrozen_writeSimdSized ?_ w)
  rw [canWrite_congr (perm_writeSimdSized _ _ _ _)]; exact h.2

/-- The memory written by `st1` (single structure, post-index): one lane of 1/2/4/8 bytes. -/
theorem keepsFrozen_st1 {m : Memory} {ea : BitVec 64} {c1 c2 c3 : Bool} {b8 : BitVec 8}
    {h16 : BitVec 16} {w32 : BitVec 32} {d64 : BitVec 64}
    (h : ¬(!m.canWrite ea (if c1 = true then 1 else if c2 = true then 2
      else if c3 = true then 4 else 8)) = true) :
    m.KeepsFrozen (if c1 = true then (m.write8 ea b8, 1#64)
      else if c2 = true then (m.write16 ea h16, 2#64)
      else if c3 = true then (m.write32 ea w32, 4#64)
      else (m.write64 ea d64, 8#64)).fst := by
  simp only [Bool.not_eq_true'] at h
  cases c1 <;> cases c2 <;> cases c3 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  all_goals first
    | exact keepsFrozen_write8 (by simpa using h) _ | exact keepsFrozen_write16 (by simpa using h) _
    | exact keepsFrozen_write32 (by simpa using h) _ | exact keepsFrozen_write64 (by simpa using h) _

/-- Two adjacent `sz` stores at `a`, `a + sz` guarded by one `canWrite a (2 * sz)` check
    (`STXP`, `CASP`). -/
theorem keepsFrozen_writeSizedPair {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : m.canWrite a (2 * sz.bytes) = true) (v w : BitVec 64) :
    m.KeepsFrozen ((m.writeSized sz a v).writeSized sz (a + BitVec.ofNat 64 sz.bytes) w) := by
  unfold canWrite at h
  rw [show 2 * sz.bytes = sz.bytes + sz.bytes by omega, allPerm_add, Bool.and_eq_true] at h
  refine (keepsFrozen_writeSized h.1 v).trans (keepsFrozen_writeSized ?_ w)
  rw [canWrite_congr (perm_writeSized _ _ _ _)]; exact h.2

theorem keepsFrozen_writeSizedPair' {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : ¬(!m.canWrite a (2 * sz.bytes)) = true) (v w : BitVec 64) :
    m.KeepsFrozen ((m.writeSized sz a v).writeSized sz (a + BitVec.ofNat 64 sz.bytes) w) :=
  keepsFrozen_writeSizedPair (by simpa using h) v w

theorem keepsFrozen_writeSizedPairRW' {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : ¬(!(m.canRead a (2 * sz.bytes) && m.canWrite a (2 * sz.bytes))) = true) (v w : BitVec 64) :
    m.KeepsFrozen ((m.writeSized sz a v).writeSized sz (a + BitVec.ofNat 64 sz.bytes) w) :=
  keepsFrozen_writeSizedPair (by simp at h; exact h.2) v w

/-- A store guarded by a combined read-and-write check (`CAS`, LSE atomics). -/
theorem keepsFrozen_writeSizedRW' {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : ¬(!(m.canRead a sz.bytes && m.canWrite a sz.bytes)) = true) (v : BitVec 64) :
    m.KeepsFrozen (m.writeSized sz a v) :=
  keepsFrozen_writeSized (by simp at h; exact h.2) v

end Memory

/-- `simdStoreRegs` (ST1 multiple structures, DC ZVA) writes only inside `[ea, ea + k * sz)`. -/
theorem keepsFrozen_simdStoreRegs (sz : SimdMemSize) (rd : BitVec 5 → BitVec 128) :
    ∀ (k : Nat) (vt : BitVec 5) (ea : BitVec 64) (m : Memory),
      m.canWrite ea (k * sz.bytes) = true → m.KeepsFrozen (simdStoreRegs sz rd k vt ea m)
  | 0, _, _, m, _ => Memory.KeepsFrozen.refl m
  | k + 1, vt, ea, m, h => by
    unfold Memory.canWrite at h
    rw [Nat.succ_mul, Nat.add_comm, Memory.allPerm_add, Bool.and_eq_true] at h
    simp only [simdStoreRegs]
    refine (Memory.keepsFrozen_writeSimdSized h.1 _).trans
      (keepsFrozen_simdStoreRegs sz rd k _ _ _ ?_)
    rw [Memory.canWrite_congr (Memory.perm_writeSimdSized _ _ _ _)]; exact h.2

theorem keepsFrozen_simdStoreRegs' {sz : SimdMemSize} {rd : BitVec 5 → BitVec 128} {k n : Nat}
    {vt : BitVec 5} {ea : BitVec 64} {m : Memory} (hn : k * sz.bytes = n)
    (h : ¬(!m.canWrite ea n) = true) : m.KeepsFrozen (simdStoreRegs sz rd k vt ea m) :=
  keepsFrozen_simdStoreRegs sz rd k vt ea m (by subst hn; simpa using h)

/-- `simdLoadRegs` (LD1 multiple structures) only writes vector registers. -/
@[simp] theorem mem_simdLoadRegs (sz : SimdMemSize) (m : Memory) :
    ∀ (k : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State), (simdLoadRegs sz m k vt ea s).mem = s.mem
  | 0, _, _, _ => rfl
  | k + 1, vt, ea, s => by
    simp only [simdLoadRegs]; rw [mem_simdLoadRegs]; rfl

@[simp] theorem symtab_simdLoadRegs (sz : SimdMemSize) (m : Memory) :
    ∀ (k : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      (simdLoadRegs sz m k vt ea s).symtab = s.symtab
  | 0, _, _, _ => rfl
  | k + 1, vt, ea, s => by
    simp only [simdLoadRegs]; rw [symtab_simdLoadRegs]; rfl

/-! ## Instruction helpers -/

section ExecHelpers


theorem mem_execAddSubImm (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12)
    (shift12 : Bool) (s : State) : (execAddSubImm w op rd rn imm12 shift12 s).mem = s.mem := by
  simp only [execAddSubImm]; ((repeat' split) <;> rfl)
theorem mem_execAddSubExt (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType)
    (amt : Nat) (s : State) : (execAddSubExt w op rd rn rm ext amt s).mem = s.mem := by
  simp only [execAddSubExt]; ((repeat' split) <;> rfl)
theorem mem_execAddSubShift (w : Width) (op : AddSubOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) (s : State) : (execAddSubShift w op rd rn rm sh amt s).mem = s.mem := by
  simp only [execAddSubShift]; ((repeat' split) <;> rfl)
theorem mem_execAddSubCarry (w : Width) (op : AddSubOp) (rd rn rm : Reg) (s : State) :
    (execAddSubCarry w op rd rn rm s).mem = s.mem := by
  simp only [execAddSubCarry]; ((repeat' split) <;> rfl)
theorem mem_execLogicalImm (w : Width) (op : LogicalOp) (rd rn : Reg) (imm : BitVec 64)
    (s : State) : (execLogicalImm w op rd rn imm s).mem = s.mem := by
  simp only [execLogicalImm]; ((repeat' split) <;> rfl)
theorem mem_execLogicalShift (w : Width) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) (s : State) : (execLogicalShift w op rd rn rm sh amt s).mem = s.mem := by
  simp only [execLogicalShift]; ((repeat' split) <;> rfl)
theorem mem_execCondCompare (w : Width) (isSub isImm : Bool) (rn : Reg) (rhs : BitVec 64)
    (rm : Reg) (nzcv : BitVec 4) (cond : CondCode) (s : State) :
    (execCondCompare w isSub isImm rn rhs rm nzcv cond s).mem = s.mem := by
  simp only [execCondCompare]; ((repeat' split) <;> rfl)
theorem mem_execLdr (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (addr : AddrMode)
    (s : State) : (execLdr w size signed rt addr s).mem = s.mem := by
  simp only [execLdr]; ((repeat' split) <;> rfl)
theorem mem_execLdrLit (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg)
    (offset : BitVec 64) (s : State) : (execLdrLit w size signed rt offset s).mem = s.mem := by
  simp only [execLdrLit]; ((repeat' split) <;> rfl)
theorem mem_execLdp (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) :
    (execLdp w signed rt1 rt2 addr s).mem = s.mem := by
  simp only [execLdp]; ((repeat' split) <;> rfl)

theorem execStr_keepsFrozen (size : MemWidth) (rt : Reg) (addr : AddrMode) (s : State) :
    s.mem.KeepsFrozen (execStr size rt addr s).mem := by
  simp only [execStr]
  repeat' split
  all_goals first
    | exact Memory.KeepsFrozen.refl _
    | exact Memory.keepsFrozen_writeSized' ‹_› _

theorem execStp_keepsFrozen (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) :
    s.mem.KeepsFrozen (execStp w rt1 rt2 addr s).mem := by
  simp only [execStp]
  repeat' split
  all_goals first
    | exact Memory.KeepsFrozen.refl _
    | exact Memory.keepsFrozen_writeSized2' ‹_› _ _

end ExecHelpers

theorem keepsFrozen_ite {m : Memory} {c : Prop} [Decidable c] {s1 s2 : State}
    (h1 : c → m.KeepsFrozen s1.mem) (h2 : ¬c → m.KeepsFrozen s2.mem) :
    m.KeepsFrozen (if c then s1 else s2).mem := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

theorem KeepsFrozen_of_mem_eq {m : Memory} {s : State} (h : s.mem = m) : m.KeepsFrozen s.mem :=
  h ▸ Memory.KeepsFrozen.refl _

theorem keepsFrozen_applySimdResult (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    s.mem.KeepsFrozen (applySimdResult s rd r).mem := by
  cases r <;> exact Memory.KeepsFrozen.refl _

theorem keepsFrozen_applySimdSatResult (s : State) (rd : BitVec 5) (r : Except String (BitVec 128))
    (satFlags : Option (BitVec 32)) :
    s.mem.KeepsFrozen (applySimdSatResult s rd r satFlags).mem := by
  cases r <;> cases satFlags <;> exact Memory.KeepsFrozen.refl _

set_option maxHeartbeats 1600000 in
theorem evalInst_keepsFrozen (prog : Program) (inst : Instr) (s : State) :
    s.mem.KeepsFrozen (prog.evalInst inst s).mem := by
  unfold Program.evalInst execInstWithSvc
  split
  all_goals first
    | exact Memory.KeepsFrozen.refl _
    | (first
        | rw [mem_execAddSubImm] | rw [mem_execAddSubExt] | rw [mem_execAddSubShift]
        | rw [mem_execAddSubCarry] | rw [mem_execLogicalImm] | rw [mem_execLogicalShift]
        | rw [mem_execCondCompare] | rw [mem_execLdr] | rw [mem_execLdrLit] | rw [mem_execLdp]
       exact Memory.KeepsFrozen.refl _)
    | with_reducible exact execStr_keepsFrozen _ _ _ _
    | with_reducible exact execStp_keepsFrozen _ _ _ _ _
    | (try dsimp only
       repeat' (first
         | exact Memory.KeepsFrozen.refl _
         | exact keepsFrozen_applySimdResult _ _ _
         | exact keepsFrozen_applySimdSatResult _ _ _ _
         | exact evalSvc_keepsFrozen _ _
         | exact Memory.keepsFrozen_writeSized' ‹_› _
         | exact Memory.keepsFrozen_writeSimdSized' ‹_› _
         | exact Memory.keepsFrozen_writeSimdSized2' ‹_› _ _
         | exact Memory.keepsFrozen_writeSizedPair' ‹_› _ _
         | exact Memory.keepsFrozen_writeSizedPairRW' ‹_› _ _
         | exact Memory.keepsFrozen_writeSizedRW' ‹_› _
         | exact Memory.keepsFrozen_st1 ‹_›
         | exact keepsFrozen_simdStoreRegs' (by first | rfl | decide) ‹_›
         | exact KeepsFrozen_of_mem_eq (mem_simdLoadRegs _ _ _ _ _ _)
         | refine keepsFrozen_ite (fun _ => ?_) (fun _ => ?_)
         | split))

/-! ## Steps keep frozen memory and the symbol table, so loaded code stays loaded -/

namespace State

@[simp] theorem symtab_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by
  cases s; cases r <;> rfl
@[simp] theorem symtab_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).symtab = s.symtab :=
  symtab_writeReg64 s r (v.zeroExtend 64)
@[simp] theorem symtab_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).symtab = s.symtab := by
  cases w <;> exact symtab_writeReg64 s r _
@[simp] theorem symtab_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem symtab_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).symtab = s.symtab :=
  symtab_writeVReg128 s i (v.zeroExtend 128)
@[simp] theorem symtab_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).symtab = s.symtab :=
  symtab_writeVReg128 s i (v.zeroExtend 128)
@[simp] theorem symtab_advancePC (s : State) : (s.advancePC).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem symtab_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem symtab_setPState (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem symtab_setMem (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem symtab_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem symtab_setBrk (s : State) (b : BitVec 64) :
    (s.setBrk b).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem symtab_nextOracle (s : State) : (s.nextOracle).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem symtab_stepExclOracle (s : State) : (s.stepExclOracle).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem symtab_appendTrace (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).symtab = s.symtab := by
  cases s; rfl

@[simp] theorem sym_writeReg64 (s : State) (r : Reg) (v : BitVec 64) (o n : String) :
    (s.writeReg64 r v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeReg64]
@[simp] theorem sym_writeReg32 (s : State) (r : Reg) (v : BitVec 32) (o n : String) :
    (s.writeReg32 r v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeReg32]
@[simp] theorem sym_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) (o n : String) :
    (s.writeReg w r v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeReg]
@[simp] theorem sym_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) (o n : String) :
    (s.writeVReg128 i v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeVReg128]
@[simp] theorem sym_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) (o n : String) :
    (s.writeVReg64 i v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeVReg64]
@[simp] theorem sym_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) (o n : String) :
    (s.writeVReg32 i v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeVReg32]
@[simp] theorem sym_advancePC (s : State) (o n : String) :
    (s.advancePC).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_advancePC]
@[simp] theorem sym_setPC (s : State) (pc : BitVec 64) (o n : String) :
    (s.setPC pc).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setPC]
@[simp] theorem sym_setPState (s : State) (ps : PState) (o n : String) :
    (s.setPState ps).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setPState]
@[simp] theorem sym_setMem (s : State) (m : Memory) (o n : String) :
    (s.setMem m).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setMem]
@[simp] theorem sym_setStatus (s : State) (st : ExecStatus) (o n : String) :
    (s.setStatus st).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setStatus]
@[simp] theorem sym_setBrk (s : State) (b : BitVec 64) (o n : String) :
    (s.setBrk b).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setBrk]
@[simp] theorem sym_nextOracle (s : State) (o n : String) :
    (s.nextOracle).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_nextOracle]
@[simp] theorem sym_stepExclOracle (s : State) (o n : String) :
    (s.stepExclOracle).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_stepExclOracle]
@[simp] theorem sym_appendTrace (s : State) (evs : List TraceEvent) (o n : String) :
    (s.appendTrace evs).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_appendTrace]
@[simp] theorem symtab_setFs (s : State) (fs : FsState) :
    (s.setFs fs).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem sym_setFs (s : State) (fs : FsState) (o n : String) :
    (s.setFs fs).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setFs]
@[simp] theorem symtab_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem sym_setFpsr (s : State) (f : BitVec 32) (o n : String) :
    (s.setFpsr f).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setFpsr]
@[simp] theorem symtab_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem sym_orFpsr (s : State) (f : BitVec 32) (o n : String) :
    (s.orFpsr f).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_orFpsr]
@[simp] theorem symtab_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem sym_setSigAction (s : State) (sig : BitVec 32) (act : SigAction)
    (o n : String) :
    (s.setSigAction sig act).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setSigAction]
@[simp] theorem symtab_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem sym_setSigAltStack (s : State) (sas : SigAltStack)
    (o n : String) :
    (s.setSigAltStack sas).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setSigAltStack]
@[simp] theorem symtab_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem sym_setSigMask (s : State) (m : BitVec 64) (o n : String) :
    (s.setSigMask m).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setSigMask]
@[simp] theorem symtab_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem sym_setSigPending (s : State) (p : BitVec 64) (o n : String) :
    (s.setSigPending p).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setSigPending]
@[simp] theorem symtab_setPhysMemAvail (s : State) (v : Nat) :
    (s.setPhysMemAvail v).symtab = s.symtab := by
  cases s; rfl
@[simp] theorem sym_setPhysMemAvail (s : State) (v : Nat) (o n : String) :
    (s.setPhysMemAvail v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setPhysMemAvail]

end State

section ExecSymtabHelpers


end ExecSymtabHelpers

/-- Every step keeps every frozen byte. -/
theorem Step.keepsFrozen {prog : Program} {s s' : State} (h : Step prog s s') :
    s.mem.KeepsFrozen s'.mem := by
  cases h with
  | exec _ _ => exact evalInst_keepsFrozen _ _ _
  | halt_unmapped _ _ _ => exact Memory.KeepsFrozen.refl _
  | externHook _ _ hk _ => exact hk
  | extern_fault _ _ _ => exact Memory.KeepsFrozen.refl _

theorem Steps.keepsFrozen {prog : Program} {s s' : State} (h : Steps prog s s') :
    s.mem.KeepsFrozen s'.mem := by
  induction h with
  | refl _ => exact Memory.KeepsFrozen.refl _
  | step h1 _ ih => exact h1.keepsFrozen.trans ih

/-! ## Interface of the loaded-code predicates -/

end Arm64
end

theorem solution {prog : Arm64.Program} {s s' : Arm64.State} (h : Arm64.Steps prog s s') :
    s.mem.KeepsFrozen s'.mem :=
  Arm64.Steps.keepsFrozen h
