-- Prove2me | solution 1 for X25519Dalek.fnOk_montgomeryPoint_mul_clamped_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T19:42:22.408293+00:00
-- url     : https://prove2.me/submissions/382f5c38-63c2-4ee2-9f54-8082824c55e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_fnOk_montgomeryPoint_mul_v2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.BitVec
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.IntervalCases

section
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

@[simp]
theorem evalSvc_symtab (svc : State → State) (s : State) :
    (evalSvc svc s).symtab = s.symtab := by
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
end

section
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
end

section
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
end

section
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
end

section
section
/-! # 64-bit cells and byte reads: values and permissions from ownership -/

set_option autoImplicit false

namespace Arm64

theorem concat8_extract (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

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
end

section
section
/-! # Instruction fetch in the placed x25519 library, and execution by backward chaining

`Step` does not depend on which block's program runs it when no hooks are installed, so a callee's
contract (stated for its own block) is usable from the caller's block. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

/-- Block `i` of the library. -/
def blk (i : Nat) : CodeBlock := x25519CliMultiLib.blocks.getD i { code := [] }

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
  interval_cases i <;> simp

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

end X25519Dalek.LP

end
end

section
section
/-! # Abstract machine states

Every state inside a block proof is `mkS s0 pc r sp ps m v`: the state `s0` with the program
counter, the general registers, the stack pointer, the flags, the memory and the vector registers
replaced. The instruction evaluators map such states to such states, and these lemmas let `simp`
compute the result without unfolding `State`. -/

set_option autoImplicit false

namespace X25519Dalek.LP

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

theorem mkS_self (s : State) : mkS s s.pc s.regs.regs s.sp s.pstate s.mem s.vregs.regs = s := rfl

/-- Register reads of the entry state, as `mkS` sees them. -/
theorem readGpr_eq (s : State) (i : BitVec 5) (h : i ≠ 31#5) :
    s.readReg64 (.gpr i) = s.regs.regs i := by
  simp [State.readReg64, RegFile.read, h]

end X25519Dalek.LP

end
end

section
section
/-! # Code stays loaded; stepping on abstract states; small stack frames -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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

theorem Reach.mk {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {i : Instr} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some i)
    (h : Reach p (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r sp ps m v)) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q :=
  Reach.exec hrun hf h

theorem pc_add (b : BitVec 64) (k j : Nat) :
    b + BitVec.ofNat 64 k + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (k + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Byte lists of length 8 are words -/

def pack64 (l : List (BitVec 8)) : BitVec 64 :=
  l.getD 7 0 ++ l.getD 6 0 ++ l.getD 5 0 ++ l.getD 4 0 ++ l.getD 3 0 ++ l.getD 2 0 ++
    l.getD 1 0 ++ l.getD 0 0

theorem unpack64_pack64 (l : List (BitVec 8)) (h : l.length = 8) : unpack64 (pack64 l) = l := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [pack64, unpack64, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
      and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
      interval_cases i <;> simp

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

/-- Focus-free consequences of owning one 64-bit cell at the head. -/
theorem cell_write {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (w : BitVec 64) :
    m.canWrite a 8 = true ∧ m.KeepsFrozen (m.write64 a w) ∧ (m.write64 a w ⊨ (a ↦₆₄ w) ∗ F) := by
  have h := sat64_read hs
  exact ⟨h.2.2, Memory.keepsFrozen_write64 h.2.2 w, sat64_write hs w⟩

end X25519Dalek.LP

end
end

section
section
/-! # Arithmetic facts for the instruction evaluators and byte encodings -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64

@[simp] theorem awc_false_fst (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

@[simp] theorem awc_true_fst (x y : BitVec 64) : (AddWithCarry64 x y true).1 = x + y + 1#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

@[simp] theorem add_not_add_one (x y : BitVec 64) : x + ~~~y + 1#64 = x - y := by
  bv_omega

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem and15_toNat (x : BitVec 64) : (x &&& 15#64).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and]
  have : (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- Alignment of `sp - k` for `k` a multiple of 16, from alignment of `sp`. -/
theorem aligned_sub {x : BitVec 64} (h : (x &&& 15#64 == 0#64) = true) (k : Nat) (hk : k % 16 = 0)
    (hk' : k < 2 ^ 64) : (x - BitVec.ofNat 64 k &&& 15#64) = 0#64 := by
  have h0 : x &&& 15#64 = 0#64 := by simpa using h
  have h1 := congrArg BitVec.toNat h0
  rw [and15_toNat] at h1
  apply BitVec.eq_of_toNat_eq
  rw [and15_toNat]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_zero] at h1 ⊢
  rw [Nat.mod_eq_of_lt hk'] 
  omega

end X25519Dalek.LP

end
end

section
section
/-! # Relocated `BL` words and calls to other blocks -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_bl_class (w : BitVec 32) (hK : w &&& 0xfc000000#32 = 0x94000000#32) :
    decode w = some (.bl ((w.extractLsb' 0 26).signExtend 64 <<< 2)) := by
  have h7c : (w &&& 0x7c000000#32 == 0x14000000#32) = true := by
    have : w &&& 0x7c000000#32 = (w &&& 0xfc000000#32) &&& 0x7c000000#32 := by
      rw [BitVec.and_assoc]; rfl
    rw [this, hK]; rfl
  have h31 : w.getLsbD 31 = true := by
    have := congrArg (fun x => x.getLsbD 31) hK
    simp only [BitVec.getLsbD_and] at this
    simpa using this
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
    beq_false_of_mask hK (C := 0x13800000#32) (M := 0x7f800000#32) (by decide), h7c, h31]
  simp

theorem hi_bits27 (D : BitVec 64) (h1 : -(2^27:Int) ≤ D.toInt) (h2 : D.toInt < 2^27) :
    ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem lo_bits2 (D : BitVec 64) (h : D.toNat % 4 = 0) : ∀ i, i < 2 → D.getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize D.toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

theorem bw_mask (D : BitVec 64) :
    ((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32)) &&&
      0xfc000000#32 = 0x94000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  interval_cases i <;> simp

theorem bw_off (D : BitVec 64) (hlo : ∀ i, i < 2 → D.getLsbD i = false)
    (hhi : ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27) :
    ((((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32))).extractLsb' 0 26).signExtend 64 <<< 2 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.msb, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact (hlo _ (by omega)).symm | exact hlo _ (by omega) | rfl |
      exact (hhi _ (by omega) (by omega)).symm | exact hhi _ (by omega) (by omega)

/-- A relocated `bl` decodes to a branch-with-link whose offset reaches the target, when the
target is in range. -/
theorem decode_branchWord (place target : BitVec 64) (h : BranchInRange place target) :
    decode (branchWord 0x94000000#32 place target) = some (.bl (target - place)) := by
  unfold branchWord
  rw [decode_bl_class _ (bw_mask _)]
  congr 2
  exact bw_off _ (lo_bits2 _ h.1) (hi_bits27 _ h.2.1 h.2.2)

end X25519Dalek.LP

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

/-- The patched word of a `bl` to another block's function: a branch word to that function. -/
theorem patchedWord_call (i : Nat) (mpl : MultiPlacement) {off j offj : Nat} {name : String}
    (h : (blk i).relocAt? off = some { off := off, kind := .call26, sym := name } ∧
      (blk i).relaxableAt off = false ∧ (off < 4 ∨ (blk i).relaxableAt (off - 4) = false) ∧
      lookup name (blk i).symbols = none ∧ (blk i).weakRefs = [] ∧
      (blk i).wordAt off = 0x94000000#32)
    (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj)) :
    (blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off =
      branchWord 0x94000000#32 (mpl.base i + BitVec.ofNat 64 off) (mpl.base j + BitVec.ofNat 64 offj) := by
  obtain ⟨hr, hra, hra4, hsym, hweak, hw⟩ := h
  have h4 : (4 ≤ off && (blk i).relaxedAt (x25519CliMultiLib.blockPlacement mpl i) (off - 4)) = false := by
    rcases hra4 with h | h
    · simp; omega
    · simp [CodeBlock.relaxedAt, h]
  simp only [CodeBlock.patchedWord, hr, CodeBlock.relaxedAt, hra, Bool.false_and, Bool.false_eq_true,
    if_false]
  simp only [CodeBlock.relaxedAt] at h4
  rw [if_neg (by simp [h4])]
  simp only [RelocKind.isGotOrTlsIe, Bool.false_and, Bool.false_eq_true, if_false,
    CodeBlock.undefWeakBranch, hweak, List.contains_nil, CodeBlock.relocTarget, CodeBlock.b2bNext?,
    hsym, CodeBlock.target, CodeBlock.resolve, addSignedAddr, patchRelocWord, hw,
    MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hlk]
  split
  · rename_i heq; split at heq <;> simp at heq
  · simp

/-- Fetching the relocated `bl` at offset `off` of block `i`, calling the function at offset
`offj` of block `j`. -/
theorem fetch_bl {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {i : Nat} (hi : i < 19) (k : Nat) {off j offj : Nat}
    {name : String}
    (hoff : off % 4 = 0 ∧ off + 4 ≤ (blk i).code.length)
    (h : (blk i).relocAt? off = some { off := off, kind := .call26, sym := name } ∧
      (blk i).relaxableAt off = false ∧ (off < 4 ∨ (blk i).relaxableAt (off - 4) = false) ∧
      lookup name (blk i).symbols = none ∧ (blk i).weakRefs = [] ∧
      (blk i).wordAt off = 0x94000000#32)
    (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj))
    {m : Memory} (hk : m0.KeepsFrozen m) :
    (bprog mpl k).fetchMem m (mpl.base i + BitVec.ofNat 64 off) =
      some (.bl ((mpl.base j + BitVec.ofNat 64 offj) - (mpl.base i + BitVec.ofNat 64 off))) := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk i (by rw [blocks_length]; exact hi)
  rw [fetch_word hP hi hCL' hoff.1 hoff.2 _ (hook_none mpl k), patchedWord_call i mpl h hlk]
  apply decode_branchWord
  have hPl := blk_placeable hP hi
  have hmem : ({ off := off, kind := .call26, sym := name } : RelocEntry) ∈ (blk i).relocs := by
    have := h.1
    simp only [CodeBlock.relocAt?] at this
    exact List.mem_of_find?_eq_some this
  have := (hPl.relocs_ok _ hmem).2.2
  simp only [CodeBlock.relocInRange, CodeRelocInRange] at this
  have ht : (blk i).relocTarget (x25519CliMultiLib.blockPlacement mpl i) off
      { off := off, kind := .call26, sym := name } = mpl.base j + BitVec.ofNat 64 offj := by
    obtain ⟨_, _, _, hsym, _, _⟩ := h
    simp only [CodeBlock.relocTarget, CodeBlock.b2bNext?, hsym, CodeBlock.target, CodeBlock.resolve,
      addSignedAddr, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hlk]
    split
    · rename_i heq; split at heq <;> simp at heq
    · simp
  rw [ht] at this
  exact this

end X25519Dalek.LP

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

/-- Running a call to another function of the library, from its contract `fnOk`: the caller
continues from any state the callee may return in. -/
theorem Reach.call {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat)
    {S α : Type} [ToBaseSpec S α] {name : String} {spec : MultiPlacement → S} {j offj : Nat}
    (hok : fnOk name spec) (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj))
    (hj : j < 19) {s : State} {Q : State → Prop} (x : α) (R' : SepProp)
    (hpc : s.pc = mpl.base j + BitVec.ofNat 64 offj) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem)
    (hpre : s.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).pre x s ∗ R')
    (hpanic : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onPanic x s sf ∗ R'))
    (hexit : ∀ c sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onExit x c s sf ∗ R'))
    (hoom : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onOom x s sf ∗ R'))
    (hcont : ∀ sf, sf.pc = s.readReg64 Reg.lr → sf.sp = s.sp → sf.status = .Running →
      CalleeSavedPreserved s sf →
      (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).post x s sf ∗ R') →
      s.mem.KeepsFrozen sf.mem → Reach (bprog mpl k) sf Q) :
    Reach (bprog mpl k) s Q := by
  obtain ⟨j', off', hlk', hall⟩ := hok
  rw [hlk] at hlk'
  cases hlk'
  have hfa : x25519CliMultiLib.fnAddr mpl name = mpl.base j + BitVec.ofNat 64 offj := by
    simp [MultiPlacedLib.fnAddr, hlk]
  have hpre' : s.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec (spec mpl) (mpl.base j))).pre x s ∗ R' := by
    simp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, sat_pure_sep]
    exact ⟨hCL, hpre⟩
  obtain ⟨sf, hst, hout⟩ := hall mpl hP x R' s (by rw [hpc, hfa]) hrun hpre' hal
    (hCL j (by rw [blocks_length]; exact hj))
  have hkf := Steps.keepsFrozen hst
  have hst' : Steps (bprog mpl k) s sf := bsteps_transfer (i := j) hst
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
  · exact Reach.steps hst' (hcont sf hpcf hspf hrunf hcs hpost hkf)
  · exact absurd hp (hpanic sf)
  · exact absurd hp (hexit c sf)
  · exact absurd hp (hoom sf)

theorem not_sat_false {m : Memory} {R : SepProp} : ¬ (m ⊨ (⌜False⌝ : SepProp) ∗ R) := by
  rw [sat_pure_sep]; exact fun h => h.1

end X25519Dalek.LP

end
end

section
section
/-! # Stack frames as lists of 64-bit words

`a ↦₆₄* ws` owns the words `ws` at `a, a + 8, …`; indexed reads and writes; conversions to and
from byte slices and `memRegion`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64

theorem words_cons (a w : BitVec 64) (ws : List (BitVec 64)) :
    (a ↦₆₄* (w :: ws)) = (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄* ws) := rfl

theorem words_nil (a : BitVec 64) : (a ↦₆₄* ([] : List (BitVec 64))) = emp := rfl

theorem words_eq_bytes : ∀ (a : BitVec 64) (ws : List (BitVec 64)),
    (a ↦₆₄* ws) = (a ↦ₛ ws.flatMap unpack64)
  | a, [] => by rw [words_nil]; rfl
  | a, w :: ws => by
    rw [words_cons, words_eq_bytes (a + 8#64) ws, List.flatMap_cons, pointsToBytes_append,
      pointsTo64_eq_bytes]
    rfl

theorem flatMap_unpack64_length (ws : List (BitVec 64)) :
    (ws.flatMap unpack64).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatMap_cons, ih]; omega

theorem addr8 (a : BitVec 64) (i : Nat) :
    a + 8#64 + BitVec.ofNat 64 (8 * i) = a + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc]; congr 1; bv_omega

theorem sat_words_read : ∀ {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp},
    (m ⊨ (a ↦₆₄* ws) ∗ F) → ∀ (i : Nat) (hi : i < ws.length),
      m.read64 (a + BitVec.ofNat 64 (8 * i)) = ws[i] ∧
      m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true ∧
      m.canWrite (a + BitVec.ofNat 64 (8 * i)) 8 = true
  | _, _, [], _, _, i, hi => by simp at hi
  | m, a, w :: ws, F, hs, 0, _ => by
    rw [words_cons, sepConj_assoc] at hs
    simpa using sat64_read hs
  | m, a, w :: ws, F, hs, i + 1, hi => by
    rw [words_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := sat_words_read hs i (by simp at hi; omega)
    rw [addr8] at this
    simpa using this

theorem sat_words_write : ∀ {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp},
    (m ⊨ (a ↦₆₄* ws) ∗ F) → ∀ (i : Nat) (hi : i < ws.length) (w : BitVec 64),
      (m.write64 (a + BitVec.ofNat 64 (8 * i)) w ⊨ (a ↦₆₄* ws.set i w) ∗ F) ∧
      m.KeepsFrozen (m.write64 (a + BitVec.ofNat 64 (8 * i)) w)
  | _, _, [], _, _, i, hi, _ => by simp at hi
  | m, a, v :: ws, F, hs, 0, _, w => by
    rw [words_cons, sepConj_assoc] at hs
    have h := cell_write hs w
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.set_cons_zero]
    rw [words_cons, sepConj_assoc]
    exact ⟨h.2.2, h.2.1⟩
  | m, a, v :: ws, F, hs, i + 1, hi, w => by
    rw [words_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := sat_words_write hs i (by simp at hi; omega) w
    rw [addr8] at this
    rw [List.set_cons_succ, words_cons, sepConj_assoc, sepConj_left_comm]
    exact this

/-- The 64-bit little-endian words of a byte list, eight bytes at a time. -/
def chunks64 : List (BitVec 8) → Nat → List (BitVec 64)
  | _, 0 => []
  | bs, k + 1 => pack64 (bs.take 8) :: chunks64 (bs.drop 8) k

theorem chunks64_length (bs : List (BitVec 8)) (k : Nat) : (chunks64 bs k).length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => simp [chunks64, ih]

theorem chunks64_flat : ∀ (k : Nat) (bs : List (BitVec 8)), bs.length = 8 * k →
    (chunks64 bs k).flatMap unpack64 = bs
  | 0, bs, h => by simp at h; simp [chunks64, h]
  | k + 1, bs, h => by
    simp only [chunks64, List.flatMap_cons]
    rw [unpack64_pack64 _ (by simp; omega), chunks64_flat k (bs.drop 8) (by simp; omega),
      List.take_append_drop]

theorem memRegion_words (a : BitVec 64) (k : Nat) (hk : 8 * k < 2 ^ 64) :
    memRegion a (8 * k) ⊢ ∃∗ ws, ⌜ws.length = k⌝ ∗ (a ↦₆₄* ws) := by
  intro h hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a (8 * k) hk h hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  refine ⟨chunks64 bs k, pure_sepConj_holds.mpr ⟨chunks64_length bs k, ?_⟩⟩
  rw [words_eq_bytes, chunks64_flat k bs hl]
  exact hb

theorem words_memRegion (a : BitVec 64) (ws : List (BitVec 64)) :
    (a ↦₆₄* ws) ⊢ memRegion a (8 * ws.length) := by
  rw [words_eq_bytes, ← flatMap_unpack64_length]
  exact bytes_entails_memRegion a _

/-- Splitting a word list at index `n`. -/
theorem words_append (a : BitVec 64) (xs ys : List (BitVec 64)) :
    (a ↦₆₄* (xs ++ ys)) = (a ↦₆₄* xs) ∗ ((a + BitVec.ofNat 64 (8 * xs.length)) ↦₆₄* ys) := by
  rw [words_eq_bytes, words_eq_bytes, words_eq_bytes, List.flatMap_append, pointsToBytes_append,
    flatMap_unpack64_length]

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

@[simp] theorem extract_lo128 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi']

@[simp] theorem extract_hi128 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : ¬ (64 + i < 64) := by omega
  simp [hi', this]

theorem sat_bytes_access {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (k n : Nat) (h : k + n ≤ bs.length) :
    m.canRead (a + BitVec.ofNat 64 k) n = true ∧ m.canWrite (a + BitVec.ofNat 64 k) n = true := by
  have e : ∀ i, a + BitVec.ofNat 64 k + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (k + i) := by
    intro i; rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨canRead_of (fun i hi => ?_), canWrite_of (fun i hi => ?_)⟩
  · rw [e]; have := sat_bytes_read hs (k + i) (by omega); rw [this.2.1]; exact ⟨rfl, this.2.2⟩
  · rw [e]; exact (sat_bytes_read hs (k + i) (by omega)).2.1

theorem sat_words_access {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (k n : Nat) (h : k + n ≤ 8 * ws.length) :
    m.canRead (a + BitVec.ofNat 64 k) n = true ∧ m.canWrite (a + BitVec.ofNat 64 k) n = true := by
  rw [words_eq_bytes] at hs
  exact sat_bytes_access hs k n (by rw [flatMap_unpack64_length]; exact h)

theorem memRegion_append (a : BitVec 64) (n : Nat) (bs : List (BitVec 8)) (hn : n < 2 ^ 64) :
    (memRegion a n ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs)) ⊢ memRegion a (n + bs.length) := by
  intro h hh
  obtain ⟨h1, h2, hd, rfl, hm, hb⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨b0, hb0⟩ := memRegion_entails_bytes a n hn h1 hm
  obtain ⟨hl, hb0⟩ := pure_sepConj_holds.mp hb0
  have : (a ↦ₛ (b0 ++ bs)).holds (h1.union h2) := by
    rw [pointsToBytes_append, hl]
    exact SepProp.holds_sepConj_iff.mpr ⟨h1, h2, hd, rfl, hb0, hb⟩
  have := bytes_entails_memRegion a _ _ this
  simpa [hl] using this

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem zext12_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 12 n) = BitVec.ofNat 64 (n % 4096) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem zext16_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 (n % 65536) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

@[simp] theorem bf_beq_1 : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_2 : (BitfieldOp.BFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_3 : (BitfieldOp.UBFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_4 : (BitfieldOp.SBFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_5 : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := by decide
@[simp] theorem bf_beq_6 : (BitfieldOp.SBFM == BitfieldOp.SBFM) = true := by decide

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

/-- After a byte store into an owned slice, continue from an abstract memory. -/
theorem Reach.wr8 {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {vr : BitVec 5 → BitVec 128} {Q : State → Prop}
    {base a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp} {v : BitVec 8} (j : Nat)
    (hs : m ⊨ (base ↦ₛ bs) ∗ F) (ha : a = base + BitVec.ofNat 64 j) (hj : j < bs.length)
    (h : ∀ m', (m' ⊨ (base ↦ₛ bs.set j v) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc r sp ps m' vr) Q) :
    Reach p (mkS s0 pc r sp ps (m.write8 a v) vr) Q := by
  subst ha
  have hw := (sat_bytes_access hs j 1 (by omega)).2
  have hk := Memory.keepsFrozen_write8 (m := m) (by simpa using hw) v
  exact h _ (sat_bytes_write hs j hj v) hk

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem clamp_list (bs : List (BitVec 8)) (h : bs.length = 32) (V0 V31 : BitVec 8)
    (h0 : V0 = bs.getD 0 0 &&& 0xf8#8) (h31 : V31 = (bs.getD 31 0 &&& 0x7f#8) ||| 0x40#8) :
    (bs.set 0 V0).set 31 V31 = clampScalarBytes bs := by
  apply List.ext_getElem
  · simp [clampScalarBytes, h]
  · intro i h1 h2
    simp only [List.length_set] at h1
    rw [h] at h1
    simp only [clampScalarBytes, List.getElem_set, h0, h31]
    interval_cases i <;> simp [List.getElem_append, h, List.getD_eq_getElem?_getD]

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem add_sub_cancel' (a b : BitVec 64) : a + (b - a) = b := by bv_omega
theorem sub_add_cancel' (a : BitVec 64) (k : Nat) : a - BitVec.ofNat 64 k + BitVec.ofNat 64 k = a := by
  bv_omega

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem memRegion_append2 (a b c : BitVec 64) (n : Nat) (b1 b2 : List (BitVec 8))
    (hb : b = a + BitVec.ofNat 64 n) (hc : c = a + BitVec.ofNat 64 (n + b1.length))
    (hn : n + b1.length < 2 ^ 64) :
    ((memRegion a n ∗ (b ↦ₛ b1)) ∗ (c ↦ₛ b2)) ⊢ memRegion a (n + b1.length + b2.length) := by
  subst hb hc
  exact Entails.trans (sepConj_mono (memRegion_append a n b1 (by omega)) (Entails.refl _))
    (memRegion_append a (n + b1.length) b2 hn)

end X25519Dalek.LP

end
end

section
section
/-! # Block 16: per-offset instruction fetch (generated by tools_ladder/gen_code.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj


abbrev mulName : String :=
  "<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul"

theorem mul_lookup : lookupBlockSym mulName x25519CliMultiLib.blocks = some (15, 0) := by
  decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem c16_0 : (bprog mpl j).fetchMem m (mpl.base 16) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x030#12 false) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 0) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x030#12 false)) (by decide +kernel) hk
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem c16_4 : (bprog mpl j).fetchMem m (mpl.base 16 + 4#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64)) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 4) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64))) (by decide +kernel) hk
  exact this

theorem c16_8 : (bprog mpl j).fetchMem m (mpl.base 16 + 8#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x020#12 false) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 8) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x020#12 false)) (by decide +kernel) hk
  exact this

theorem c16_12 : (bprog mpl j).fetchMem m (mpl.base 16 + 12#64) =
    some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x000000000000001f#64)) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 12) (inst := (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x000000000000001f#64))) (by decide +kernel) hk
  exact this

theorem c16_16 : (bprog mpl j).fetchMem m (mpl.base 16 + 16#64) =
    some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000000#64)) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 16) (inst := (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000000#64))) (by decide +kernel) hk
  exact this

theorem c16_20 : (bprog mpl j).fetchMem m (mpl.base 16 + 20#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x0b#5) 0x0040#16 0) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 20) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x0b#5) 0x0040#16 0)) (by decide +kernel) hk
  exact this

theorem c16_24 : (bprog mpl j).fetchMem m (mpl.base 16 + 24#64) =
    some (Instr.bitfield (RegWidth.W32) (BitfieldOp.BFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) 0 5) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 24) (inst := (Instr.bitfield (RegWidth.W32) (BitfieldOp.BFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) 0 5)) (by decide +kernel) hk
  exact this

theorem c16_28 : (bprog mpl j).fetchMem m (mpl.base 16 + 28#64) =
    some (Instr.logicalImm (RegWidth.W32) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) 0x000000f8000000f8#64) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 28) (inst := (Instr.logicalImm (RegWidth.W32) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) 0x000000f8000000f8#64)) (by decide +kernel) hk
  exact this

theorem c16_32 : (bprog mpl j).fetchMem m (mpl.base 16 + 32#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000000#64)) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 32) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000000#64))) (by decide +kernel) hk
  exact this

theorem c16_36 : (bprog mpl j).fetchMem m (mpl.base 16 + 36#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x000000000000001f#64)) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 36) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x000000000000001f#64))) (by decide +kernel) hk
  exact this

theorem c16_40 : (bprog mpl j).fetchMem m (mpl.base 16 + 40#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000000#64)) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 40) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000000#64))) (by decide +kernel) hk
  exact this

theorem c16_44 : (bprog mpl j).fetchMem m (mpl.base 16 + 44#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x000#12 false) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 44) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x000#12 false)) (by decide +kernel) hk
  exact this

theorem c16_48 : (bprog mpl j).fetchMem m (mpl.base 16 + 48#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000000#64)) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 48) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000000#64))) (by decide +kernel) hk
  exact this

theorem c16_56 : (bprog mpl j).fetchMem m (mpl.base 16 + 56#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64)) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 56) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64))) (by decide +kernel) hk
  exact this

theorem c16_60 : (bprog mpl j).fetchMem m (mpl.base 16 + 60#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x030#12 false) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 60) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x030#12 false)) (by decide +kernel) hk
  exact this

theorem c16_64 : (bprog mpl j).fetchMem m (mpl.base 16 + 64#64) =
    some (Instr.ret (Reg.gpr 0x1e#5)) := by
  have := fetch_at (i := 16) hP hCL (by decide) j (off := 64) (inst := (Instr.ret (Reg.gpr 0x1e#5))) (by decide +kernel) hk
  exact this

theorem c16_52 : (bprog mpl j).fetchMem m (mpl.base 16 + 52#64) =
    some (.bl (mpl.base 15 + BitVec.ofNat 64 0 - (mpl.base 16 + BitVec.ofNat 64 52))) :=
  fetch_bl hP hCL (i := 16) (by decide) j (off := 52) (name := mulName) (by decide +kernel)
    (by decide +kernel) mul_lookup hk

end

end X25519Dalek.LP

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

abbrev mcName : String := "<curve25519_dalek::montgomery::MontgomeryPoint>::mul_clamped"

theorem mc_lookup : lookupBlockSym mcName x25519CliMultiLib.blocks = some (16, 0) := by
  decide +kernel

theorem list6 {α : Type} (l : List α) (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l, h with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

theorem x25519_eq_ladder (k u : List (BitVec 8)) (hk : k.length = 32) :
    x25519 k u = natToLeBytes 32
      (have u1 := decodeU255 u % p25519;
       have res := montLadderLoop 255 (leBytesToNat (clampScalarBytes k)) u1
         { U := 1, W := 0 } { U := u1, W := 1 };
       fpMul res.U (fpInv res.W)) := by
  simp [x25519, x25519Ladder, clampScalar, List.take_of_length_le, hk]

theorem mc_ok : fnOk mcName montgomeryPointMulClampedSpec := by
  refine ⟨16, 0, mc_lookup, fun mpl hP => ?_⟩
  intro x R s0 hpc hrun hpre hal hCLp
  obtain ⟨out, self, bytes, out_bs, self_bs, bytes_bs⟩ := x
  have hfa : x25519CliMultiLib.fnAddr mpl mcName = mpl.base 16 := by
    simp [MultiPlacedLib.fnAddr, mc_lookup]
  rw [hfa] at hpc
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpre
  have h1 := Satisfies.of_eq hpre
    (Q := ⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = self ∧ s0.readReg64 Reg.x1 = bytes ∧
        out_bs.length = 32 ∧ self_bs.length = 32 ∧ bytes_bs.length = 32⌝ ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ stackFrame s0 1728 ∗ (bytes ↦ₛ bytes_bs) ∗
      (self ↦ₛ self_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗
      (out ↦ₛ out_bs) ∗ R) (by ac_rfl)
  rw [sat_pure_sep, sat_pure_sep] at h1
  obtain ⟨⟨hx8, hx0, hx1, hlo, hls, hlb⟩, hCL, h1⟩ := h1
  have h2 := sat_sep_mono h1 (memRegion_words _ 216 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at h2
  obtain ⟨ws, h2⟩ := h2
  rw [sepConj_assoc, sat_pure_sep] at h2
  obtain ⟨hwl, h2⟩ := h2
  rw [← List.take_append_drop 210 ws, words_append] at h2
  obtain ⟨t0, t1, t2, t3, t4, t5, ht⟩ := list6 (ws.drop 210) (by simp [hwl])
  have hlow : (ws.take 210).length = 210 := by simp [hwl]
  rw [ht, hlow, show s0.sp - BitVec.ofNat 64 1728 + BitVec.ofNat 64 (8 * 210) = s0.sp - 48#64 by
    bv_omega, sepConj_assoc] at h2
  generalize ws.take 210 = low at h2 hlow
  clear h1 hpre ht hwl ws
  -- the run
  have e0 : mkS s0 (mpl.base 16) s0.regs.regs s0.sp s0.pstate s0.mem s0.vregs.regs = s0 := by
    rw [← hpc]; rfl
  show Reach _ s0 _
  conv => enter [2]; rw [← e0]
  generalize hQ : SubroutineOutcome _ _ _ _ = Q
  have hal' : (s0.sp &&& 15#64 == 0#64) = true := hal
  have hr0 : s0.regs.regs 0#5 = self := by rw [← readGpr_eq s0 0#5 (by decide)]; exact hx0
  have hr1 : s0.regs.regs 1#5 = bytes := by rw [← readGpr_eq s0 1#5 (by decide)]; exact hx1
  have hr8 : s0.regs.regs 8#5 = out := by rw [← readGpr_eq s0 8#5 (by decide)]; exact hx8
  -- 0: sub sp, sp, #48
  refine Reach.mk hrun (c16_0 hP hCL 16 (Memory.KeepsFrozen.refl _)) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8]
  -- 4: stp x29, x30, [sp, #32]
  have hT := h2
  rw [sepConj_left_comm] at hT
  obtain ⟨-, -, cw4⟩ := sat_words_read hT 4 (by simp)
  obtain ⟨-, -, cw5⟩ := sat_words_read hT 5 (by simp)
  obtain ⟨hT, kf1⟩ := sat_words_write hT 4 (by simp) (s0.regs.regs 29#5)
  obtain ⟨hT, kf1'⟩ := sat_words_write hT 5 (by simp) (s0.regs.regs 30#5)
  simp only [Nat.reduceMul, List.set_cons_succ, List.set_cons_zero, pc_add] at cw4 cw5 hT kf1 kf1'
  replace kf1 := kf1.trans kf1'
  clear kf1'
  have hal48 := aligned_sub hal' 48 (by decide) (by decide)
  refine Reach.mk hrun (c16_4 hP hCL 16 (Memory.KeepsFrozen.refl _)) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8, hal48, cw4, cw5]
  generalize ((s0.mem.write64 (s0.sp - 48#64 + 32#64) (s0.regs.regs 29#5)).write64 (s0.sp - 48#64 + 40#64)
    (s0.regs.regs 30#5)) = m1 at kf1 hT ⊢
  -- 8: add x29, sp, #32
  refine Reach.mk hrun (c16_8 hP hCL 16 kf1) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8]
  -- 12: ldrb w10, [x1, #31]; 16: ldrb w9, [x1]
  have hB := hT
  simp only [sepConj_left_comm _ (bytes ↦ₛ _)] at hB
  have b31 := sat_bytes_read hB 31 (by omega)
  have b0 := sat_bytes_read hB 0 (by omega)
  have crb31 := (sat_bytes_access hB 31 1 (by omega)).1
  have crb0 := (sat_bytes_access hB 0 1 (by omega)).1
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 crb0 b31 crb31
  refine Reach.mk hrun (c16_12 hP hCL 16 kf1) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8, crb31, b31.1]
  refine Reach.mk hrun (c16_16 hP hCL 16 kf1) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8, crb0, b0.1]
  -- 20, 24, 28
  refine Reach.mk hrun (c16_20 hP hCL 16 kf1) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8]
  refine Reach.mk hrun (c16_24 hP hCL 16 kf1) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8]
  refine Reach.mk hrun (c16_28 hP hCL 16 kf1) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8]
  -- 32: strb w9, [x1]
  have cwb0 := (sat_bytes_access hB 0 1 (by omega)).2
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at cwb0
  refine Reach.mk hrun (c16_32 hP hCL 16 kf1) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8, cwb0]
  refine Reach.wr8 0 hB (by simp) (by omega) (fun m2 hB2 kf2 => ?_)
  replace kf2 := kf1.trans kf2
  -- 36: strb w11, [x1, #31]
  have cwb31 := (sat_bytes_access hB2 31 1 (by simp; omega)).2
  refine Reach.mk hrun (c16_36 hP hCL 16 kf2) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8, cwb31]
  refine Reach.wr8 31 hB2 rfl (by simp; omega) (fun m3 hB3 kf3 => ?_)
  replace kf3 := kf2.trans kf3
  have g0 : bytes_bs[0] = bytes_bs.getD 0 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 0 < bytes_bs.length)]
  have g31 : bytes_bs[31] = bytes_bs.getD 31 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 31 < bytes_bs.length)]
  simp only [g0, g31] at hB3 ⊢
  generalize hb0 : bytes_bs.getD 0 0 = b0 at hB3 ⊢
  generalize hb31 : bytes_bs.getD 31 0 = b31 at hB3 ⊢
  generalize hV0 : (BitVec.truncate 8 _ : BitVec 8) = V0 at hB3
  generalize hV31 : (BitVec.truncate 8 _ : BitVec 8) = V31 at hB3
  have h0' : V0 = b0 &&& 0xf8#8 := by
    rw [← hV0]; apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp
  have h31' : V31 = (b31 &&& 0x7f#8) ||| 0x40#8 := by
    rw [← hV31]; apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp
  rw [clamp_list bytes_bs hlb V0 V31 (by rw [h0', hb0]) (by rw [h31', hb31])] at hB3
  have hcl32 : (clampScalarBytes bytes_bs).length = 8 * 4 := by simp [clampScalarBytes, hlb]
  rw [← chunks64_flat 4 _ hcl32, ← words_eq_bytes] at hB3
  -- 40: ldp q0, q1, [x1]
  obtain ⟨rd0, -, -⟩ := sat_words_read hB3 0 (by simp [chunks64_length])
  obtain ⟨rd1, -, -⟩ := sat_words_read hB3 1 (by simp [chunks64_length])
  obtain ⟨rd2, -, -⟩ := sat_words_read hB3 2 (by simp [chunks64_length])
  obtain ⟨rd3, -, -⟩ := sat_words_read hB3 3 (by simp [chunks64_length])
  have cq0 := (sat_words_access hB3 0 16 (by simp [chunks64_length])).1
  have cq1 := (sat_words_access hB3 16 16 (by simp [chunks64_length])).1
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at rd0 rd1 rd2 rd3 cq0 cq1
  refine Reach.mk hrun (c16_40 hP hCL 16 kf3) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8, rd0, rd1, rd2, rd3, cq0, cq1]
  -- 44: add x1, sp, #0
  refine Reach.mk hrun (c16_44 hP hCL 16 kf3) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8]
  -- 48: stp q0, q1, [sp]
  have hS := hB3
  rw [sepConj_left_comm] at hS
  have cs0 := (sat_words_access hS 0 16 (by simp)).2
  have cs1 := (sat_words_access hS 16 16 (by simp)).2
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at cs0 cs1
  refine Reach.mk hrun (c16_48 hP hCL 16 kf3) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, hr0, hr1, hr8, cs0, cs1, hal48]
  set cs := chunks64 (clampScalarBytes bytes_bs) 4 with hcs
  have hcsl : cs.length = 4 := chunks64_length _ _
  obtain ⟨w0, k0⟩ := sat_words_write hS 0 (by simp) (cs[0]'(by omega))
  obtain ⟨w1, k1⟩ := sat_words_write w0 1 (by simp) (cs[1]'(by omega))
  obtain ⟨w2, k2⟩ := sat_words_write w1 2 (by simp) (cs[2]'(by omega))
  obtain ⟨w3, k3⟩ := sat_words_write w2 3 (by simp) (cs[3]'(by omega))
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.set_cons_zero,
    List.set_cons_succ] at w3 k0 k1 k2 k3
  have kf4 := kf3.trans (k0.trans (k1.trans (k2.trans k3)))
  clear w0 w1 w2 k0 k1 k2 k3 hS
  generalize hm4 : Memory.write64 _ (s0.sp - 48#64 + 24#64) _ = m4 at w3 kf4 ⊢
  -- 52: bl mul
  refine Reach.mk hrun (c16_52 hP hCL 16 kf4) ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, add_sub_cancel', sub_add_cancel', hr0, hr1, hr8]
  -- the call to `mul`: precondition and frame
  have hcs4 : [cs[0]'(by omega), cs[1]'(by omega), cs[2]'(by omega), cs[3]'(by omega)] = cs := by
    apply List.ext_getElem
    · simp [hcsl]
    · intro i h1 h2; simp at h1; interval_cases i <;> rfl
  have hflat : cs.flatMap unpack64 = clampScalarBytes bytes_bs := by
    rw [hcs]; exact chunks64_flat 4 _ hcl32
  have htop : ((s0.sp - 48#64) ↦₆₄* [cs[0]'(by omega), cs[1]'(by omega), cs[2]'(by omega),
      cs[3]'(by omega), s0.regs.regs 29#5, s0.regs.regs 30#5]) =
      ((s0.sp - 48#64) ↦ₛ clampScalarBytes bytes_bs) ∗ ((s0.sp - 48#64 + 32#64) ↦₆₄*
        [s0.regs.regs 29#5, s0.regs.regs 30#5]) := by
    rw [show [cs[0]'(by omega), cs[1]'(by omega), cs[2]'(by omega), cs[3]'(by omega),
      s0.regs.regs 29#5, s0.regs.regs 30#5] = [cs[0]'(by omega), cs[1]'(by omega), cs[2]'(by omega),
      cs[3]'(by omega)] ++ [s0.regs.regs 29#5, s0.regs.regs 30#5] from rfl, words_append, hcs4,
      words_eq_bytes, hflat, hcsl]
  have hbw : (bytes ↦₆₄* cs) = (bytes ↦ₛ clampScalarBytes bytes_bs) := by rw [words_eq_bytes, hflat]
  rw [htop, hbw, sepConj_assoc] at w3
  have hW := sat_sep_mono (Satisfies.of_eq w3 (Q := ((s0.sp - 1728#64) ↦₆₄* low) ∗
      ((s0.sp - 48#64) ↦ₛ clampScalarBytes bytes_bs) ∗ ((s0.sp - 48#64 + 32#64) ↦₆₄*
        [s0.regs.regs 29#5, s0.regs.regs 30#5]) ∗ (bytes ↦ₛ clampScalarBytes bytes_bs) ∗
      (self ↦ₛ self_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗
      (out ↦ₛ out_bs) ∗ R) (by ac_rfl)) (words_memRegion _ low)
  rw [hlow, show s0.sp - 1728#64 = s0.sp - 48#64 - BitVec.ofNat 64 1680 by bv_omega] at hW
  clear w3 htop hbw
  generalize hrf : upd _ (30#5) (mpl.base 16 + 56#64) = rf
  generalize hvf : upd _ (1#5) _ = vf
  have f0 : rf 0#5 = self := by rw [← hrf]; simp [hr0]
  have f1 : rf 1#5 = s0.sp - 48#64 := by rw [← hrf]; simp
  have f8 : rf 8#5 = out := by rw [← hrf]; simp [hr8]
  have f30 : rf 30#5 = mpl.base 16 + 56#64 := by rw [← hrf]; simp
  have fcs : rf 19#5 = s0.regs.regs 19#5 ∧ rf 20#5 = s0.regs.regs 20#5 ∧ rf 21#5 = s0.regs.regs 21#5 ∧
      rf 22#5 = s0.regs.regs 22#5 ∧ rf 23#5 = s0.regs.regs 23#5 ∧ rf 24#5 = s0.regs.regs 24#5 ∧
      rf 25#5 = s0.regs.regs 25#5 ∧ rf 26#5 = s0.regs.regs 26#5 ∧ rf 27#5 = s0.regs.regs 27#5 ∧
      rf 28#5 = s0.regs.regs 28#5 := by rw [← hrf]; simp
  have fv : ∀ i : BitVec 5, i ≠ 0#5 → i ≠ 1#5 → vf i = s0.vregs.regs i := by
    intro i h0 h1; rw [← hvf]; simp [h0, h1]
  clear hrf hvf
  refine Reach.call hP 16 fnOk_montgomeryPoint_mul_v2 mul_lookup (by decide)
    (out, self, s0.sp - 48#64, out_bs, self_bs, clampScalarBytes bytes_bs)
    ((bytes ↦ₛ clampScalarBytes bytes_bs) ∗ ((s0.sp - 48#64 + 32#64) ↦₆₄*
      [s0.regs.regs 29#5, s0.regs.regs 30#5]) ∗ R)
    (by simp) hrun (by simpa [State.spAligned] using hal48) (libCodeLoaded_keepsFrozen hCL kf4) ?_
    (fun sf => not_sat_false) (fun c sf => not_sat_false) (fun sf => not_sat_false) ?_
  · simp only [ToBaseSpec.toSpec, mkS_mem, mkS_readGpr, stackFrame, mkS_sp, Reg.x8, Reg.x0, Reg.x1,
      BitVec.reduceEq, ite_false, f0, f1, f8]
    rw [sepConj_assoc, sat_pure_sep]
    refine ⟨⟨trivial, trivial, trivial, hlo, hls, by simpa using hcl32⟩, ?_⟩
    simp only [Nat.reduceMul] at hW
    exact Satisfies.of_eq hW (by ac_rfl)
  · intro sf hpcf hspf hrunf hcsf hpost hkf
    simp only [mkS_readGpr, Reg.lr, BitVec.reduceEq, ite_false, f30, mkS_sp, mkS_mem] at hpcf hspf hkf
    simp only [ToBaseSpec.toSpec, mkS_sp, hspf] at hpost
    rw [← mkS_self sf, hpcf, hspf]
    have kf5 := kf4.trans hkf
    -- 56: ldp x29, x30, [sp, #32]
    have hX := hpost
    rw [sepConj_assoc] at hX
    simp only [sepConj_left_comm _ ((s0.sp - 48#64 + 32#64) ↦₆₄* _)] at hX
    obtain ⟨rx29, crx29, -⟩ := sat_words_read hX 0 (by simp)
    obtain ⟨rx30, crx30, -⟩ := sat_words_read hX 1 (by simp)
    simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, pc_add] at rx29 crx29 rx30 crx30
    refine Reach.mk hrunf (c16_56 hP hCL 16 kf5) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, add_sub_cancel', sub_add_cancel', rx29, rx30, crx29, crx30, hal48, List.getElem_cons_zero, List.getElem_cons_succ]
    -- 60: add sp, sp, #48
    refine Reach.mk hrunf (c16_60 hP hCL 16 kf5) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, add_sub_cancel', sub_add_cancel']
    -- 64: ret
    refine Reach.mk hrunf (c16_64 hP hCL 16 kf5) ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, add_sub_cancel', sub_add_cancel']
    apply Reach.done
    rw [← hQ]
    left
    obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, cfp, cv⟩ := hcsf
    simp only [mkS_readGpr, BitVec.reduceEq, ite_false, Reg.fp, fcs.1, fcs.2.1, fcs.2.2.1, fcs.2.2.2.1,
      fcs.2.2.2.2.1, fcs.2.2.2.2.2.1, fcs.2.2.2.2.2.2.1, fcs.2.2.2.2.2.2.2.1, fcs.2.2.2.2.2.2.2.2.1,
      fcs.2.2.2.2.2.2.2.2.2] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28
    rw [readGpr_eq sf _ (by decide)] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28
    refine ⟨⟨?_, by simp, by simpa using hrunf⟩, ⟨by simp, ?_⟩, ?_⟩
    · simp [readGpr_eq]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try (simp only [mkS_readGpr, Reg.fp, BitVec.reduceEq, ↓reduceIte, upd_apply]; simp [readGpr_eq, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28]))
      have : calleeSavedVRegs (mkS sf (s0.regs.regs 30#5) (upd (upd sf.regs.regs (29#5) (s0.regs.regs 29#5))
          (30#5) (s0.regs.regs 30#5)) s0.sp sf.pstate sf.mem sf.vregs.regs) = calleeSavedVRegs sf := rfl
      rw [this, cv]
      simp [VRegFile.calleeSaved, VRegFile.read, mkS, fv]
    · simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mkS_mem, stackFrame, mkS_sp]
      rw [x25519_eq_ladder bytes_bs self_bs hlb]
      rw [words_eq_bytes] at hpost
      simp only [sepConj_assoc] at hpost
      simp only [sepConj_left_comm _ ((s0.sp - 48#64 + 32#64) ↦ₛ _)] at hpost
      simp only [sepConj_left_comm _ ((s0.sp - 48#64) ↦ₛ _)] at hpost
      simp only [sepConj_left_comm _ (memRegion _ _)] at hpost
      rw [← sepConj_assoc, ← sepConj_assoc] at hpost
      have hM := sat_sep_mono hpost (memRegion_append2 _ _ _ 1680 _ _ (by bv_omega)
        (by simp [hcl32]; bv_omega) (by simp [hcl32]))
      simp only [hcl32, List.length_flatMap, unpack64_length, hspf, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul] at hM
      rw [show s0.sp - 48#64 - BitVec.ofNat 64 1680 = s0.sp - BitVec.ofNat 64 1728 by bv_omega] at hM
      exact Satisfies.of_eq hM (by ac_rfl)

end X25519Dalek.LP

namespace X25519Dalek

theorem fnOk_montgomeryPoint_mul_clamped_dev :
    fnOk
      "<curve25519_dalek::montgomery::MontgomeryPoint>::mul_clamped"
      montgomeryPointMulClampedSpec :=
  LP.mc_ok

end X25519Dalek

end
end

section
open X25519Dalek

theorem solution :
    fnOk
      "<curve25519_dalek::montgomery::MontgomeryPoint>::mul_clamped"
      montgomeryPointMulClampedSpec := by
  apply X25519Dalek.fnOk_montgomeryPoint_mul_clamped_dev <;> assumption

end
