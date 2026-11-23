-- Prove2me | solution 1 for X25519Dalek.subroutineOk_publicKey_from
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T10:45:24.112317+00:00
-- url     : https://prove2.me/submissions/4e89669f-83d7-4ae4-8172-bb2494834b79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_fnOk_edwardsPoint_mul_base_clamped
import Theorems.Thm_X25519Dalek_fnOk_edwardsPoint_to_montgomery
import Theorems.Thm_X25519Dalek_edExtToMontgomeryU_mulBase_clamped
import Mathlib

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

namespace X25519Dalek.GP

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

end X25519Dalek.GP

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

namespace X25519Dalek.GP

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

/-- Register reads of the entry state, as `mkS` sees them. -/
theorem readGpr_eq (s : State) (i : BitVec 5) (h : i ≠ 31#5) :
    s.readReg64 (.gpr i) = s.regs.regs i := by
  simp [State.readReg64, RegFile.read, h]

end X25519Dalek.GP

end
end

section
section
/-! # Code stays loaded; stepping on abstract states; small stack frames -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

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

end X25519Dalek.GP

end
end

section
section
/-! # Decoding a relocated cross-block `BL`

Adapted from the sibling batch q445-xd-edwards (`Solutions/X25519DalekEdwards/Reloc.lean`), which
follows the zlib CRC-32 mission's proofs (`ZlibCrc32.Small.RelocBase`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

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
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem lo_bits2 (D : BitVec 64) (h : D.toNat % 4 = 0) : ∀ i, i < 2 → D.getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize D.toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

/-- A relocated `BL` (template `0x94000000`) calls its target. -/
theorem decode_branchWord_bl {P T : BitVec 64} (hr : BranchInRange P T) :
    decode (branchWord 0x94000000#32 P T) = some (.bl (T - P)) := by
  have hm : ((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32))
      &&& 0x7c000000#32 = 0x14000000#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
    interval_cases i <;> simp
  have h31 : ((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).getLsbD 31
      = true := by simp
  have hoff : ((((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).extractLsb' 0 26).signExtend 64)
      <<< 2 = T - P := by
    have hlo := lo_bits2 _ hr.1
    have hhi := hi_bits27 _ hr.2.1 hr.2.2
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
      BitVec.msb_eq_getLsbD_last]
    interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
      first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
        exact (hhi _ (by omega) (by omega)).symm | rfl
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

end X25519Dalek.GP

end
end

section
section
/-! # 128-bit loads and stores, 32-byte buffers as 64-bit cells, stack regions -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

open Arm64 Arm64.Obj

theorem append_lo (w v : BitVec 64) : (w ++ v).extractLsb' 0 64 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem append_hi (w v : BitVec 64) : (w ++ v).extractLsb' 64 64 = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : ¬ (64 + i < 64) := by omega
  simp [this, hi]

/-! ## 32-byte buffers -/

/-- The `k`-th 64-bit little-endian word of a byte list. -/
def chunk (bs : List (BitVec 8)) (k : Nat) : BitVec 64 := pack64 ((bs.drop (8 * k)).take 8)

theorem bytes8_cell (a : BitVec 64) (l : List (BitVec 8)) (h : l.length = 8) :
    (a ↦ₛ l) = (a ↦₆₄ pack64 l) := by
  rw [pointsTo64_eq_bytes, unpack64_pack64 _ h]

theorem bytes32_cells (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) = (a ↦₆₄ chunk bs 0) ∗ ((a + 8#64) ↦₆₄ chunk bs 1) ∗
      ((a + 16#64) ↦₆₄ chunk bs 2) ∗ ((a + 24#64) ↦₆₄ chunk bs 3) := by
  rw [pointsToBytes_split a bs 8 (by omega)]
  rw [pointsToBytes_split _ (bs.drop 8) 8 (by simp [h])]
  rw [pointsToBytes_split _ ((bs.drop 8).drop 8) 8 (by simp [h])]
  have e1 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have e2 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by
    rw [BitVec.add_assoc]; rfl
  have e3 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  rw [e3, e2, e1]
  have l3 : ((bs.drop 8).drop 8).drop 8 = (bs.drop 24).take 8 := by
    rw [List.drop_drop, List.drop_drop, List.take_of_length_le (by simp [h])]
  rw [l3, bytes8_cell _ _ (by simp [h]), bytes8_cell _ _ (by simp [h]),
    bytes8_cell _ _ (by simp [h]), bytes8_cell _ _ (by simp [h])]
  simp only [chunk, List.drop_drop, Nat.mul_zero, List.drop_zero]

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

theorem bytes32_eq_cellsFrom (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) = cellsFrom a [chunk bs 0, chunk bs 1, chunk bs 2, chunk bs 3] := by
  rw [bytes32_cells a bs h]
  simp only [cellsFrom_cons, cellsFrom_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

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

theorem perm312 (A B C D : SepProp) : (A ∗ B ∗ C ∗ D) = (C ∗ A ∗ B ∗ D) := by ac_rfl
theorem perm4123 (A B C D E : SepProp) : (A ∗ B ∗ C ∗ D ∗ E) = (D ∗ A ∗ B ∗ C ∗ E) := by ac_rfl

/-- A 64-byte region under a frame is a run of eight owned 64-bit cells. -/
theorem sat_region64_cells {m : Memory} {a : BitVec 64} {F : SepProp}
    (hs : m ⊨ memRegion a 64 ∗ F) :
    ∃ u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64,
      m ⊨ cellsFrom a [u0, u1, u2, u3, u4, u5, u6, u7] ∗ F := by
  have h := sat_sep_mono hs (memRegion_entails_bytes a 64 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at h
  obtain ⟨bs, h⟩ := h
  rw [sepConj_assoc, sat_pure_sep] at h
  obtain ⟨hl, h⟩ := h
  rw [pointsToBytes_split a bs 32 (by omega)] at h
  rw [bytes32_eq_cellsFrom _ (bs.take 32) (by simp [hl]),
    bytes32_eq_cellsFrom _ (bs.drop 32) (by simp [hl])] at h
  refine ⟨chunk (bs.take 32) 0, chunk (bs.take 32) 1, chunk (bs.take 32) 2, chunk (bs.take 32) 3,
    chunk (bs.drop 32) 0, chunk (bs.drop 32) 1, chunk (bs.drop 32) 2, chunk (bs.drop 32) 3, ?_⟩
  rw [show [chunk (bs.take 32) 0, chunk (bs.take 32) 1, chunk (bs.take 32) 2, chunk (bs.take 32) 3,
    chunk (bs.drop 32) 0, chunk (bs.drop 32) 1, chunk (bs.drop 32) 2, chunk (bs.drop 32) 3] =
    [chunk (bs.take 32) 0, chunk (bs.take 32) 1, chunk (bs.take 32) 2, chunk (bs.take 32) 3] ++
    [chunk (bs.drop 32) 0, chunk (bs.drop 32) 1, chunk (bs.drop 32) 2, chunk (bs.drop 32) 3] from rfl,
    cellsFrom_append]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
  exact h

theorem fe51LimbsBoundedAt_mono {bs : List (BitVec 8)} {off b1 b2 : Nat} (h : b1 ≤ b2)
    (hb : fe51LimbsBoundedAt bs off b1) : fe51LimbsBoundedAt bs off b2 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hb
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem fe51Point4Bounded_mono {bs : List (BitVec 8)} {b1 b2 : Nat} (h : b1 ≤ b2)
    (hb : fe51Point4Bounded bs b1) : fe51Point4Bounded bs b2 := by
  obtain ⟨hl, h0, h1, h2, h3⟩ := hb
  exact ⟨hl, fe51LimbsBoundedAt_mono h h0, fe51LimbsBoundedAt_mono h h1,
    fe51LimbsBoundedAt_mono h h2, fe51LimbsBoundedAt_mono h h3⟩

/-- The PublicKey::from stack frame after both calls merges back into one 1904-byte region. -/
theorem pk_stack_merge (T : BitVec 64) (b1 b2 : List (BitVec 8)) (h1 : b1.length = 160)
    (h2 : b2.length = 32) (l : List (BitVec 64)) (hl : l.length = 4) :
    memRegion (T - BitVec.ofNat 64 1680) 288 ∗ memRegion (T - BitVec.ofNat 64 1392) 1392 ∗
      (T ↦ₛ b1) ∗ ((T + 160#64) ↦ₛ b2) ∗ cellsFrom (T + 192#64) l ⊢
      memRegion (T - BitVec.ofNat 64 1680) 1904 := by
  have m1 := bytes_entails_memRegion T b1
  have m2 := bytes_entails_memRegion (T + 160#64) b2
  have m3 := cellsFrom_entails_memRegion (T + 192#64) l (by rw [hl]; norm_num)
  rw [h1] at m1
  rw [h2] at m2
  rw [hl] at m3
  have a0 := memRegion_merge (T - BitVec.ofNat 64 1680) (T - BitVec.ofNat 64 1392) 288 1392
    (by bv_omega) (by norm_num) (by norm_num)
  have a1 := memRegion_merge (T - BitVec.ofNat 64 1680) T (288 + 1392) 160 (by bv_omega)
    (by norm_num) (by norm_num)
  have a2 := memRegion_merge (T - BitVec.ofNat 64 1680) (T + 160#64) (288 + 1392 + 160) 32
    (by bv_omega) (by norm_num) (by norm_num)
  have a3 := memRegion_merge (T - BitVec.ofNat 64 1680) (T + 192#64) (288 + 1392 + 160 + 32)
    (8 * 4) (by bv_omega) (by norm_num) (by norm_num)
  refine Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono m1 (sepConj_mono m2 m3)))) ?_
  rw [← sepConj_assoc]
  refine Entails.trans (sepConj_mono a0 (Entails.refl _)) ?_
  rw [← sepConj_assoc]
  refine Entails.trans (sepConj_mono a1 (Entails.refl _)) ?_
  rw [← sepConj_assoc]
  refine Entails.trans (sepConj_mono a2 (Entails.refl _)) ?_
  exact a3

end X25519Dalek.GP

end
end

section
section
/-! # One lemma per instruction shape on abstract states `mkS`

The instructions of the two entry blocks (17 and 18). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

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

theorem ex_stpq_gpr (n t1 t2 : BitVec 5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw1 : m.canWrite (r n + off) 16 = true) (hw2 : m.canWrite (r n + off + 16#64) 16 = true) :
    execInstWithSvc svc (.stpSimd .Q128 t1 t2 (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps ((m.write128 (r n + off) (v t1)).write128 (r n + off + 16#64) (v t2)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw1, hw2, hn,
    Memory.writeSimdSized, AddrMode.baseReg]

end exec

end X25519Dalek.GP

end
end

section
section
/-! # Small facts shared by the two entry-block proofs -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

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

theorem clampScalarBytes_length (bs : List (BitVec 8)) (h : bs.length = 32) :
    (clampScalarBytes bs).length = 32 := by
  simp [clampScalarBytes, h]

theorem readGpr_unfold (s : State) (i : BitVec 5) :
    s.readReg64 (.gpr i) = if i = 31#5 then 0#64 else s.regs.regs i := by
  simp [State.readReg64, RegFile.read]

theorem mkS_vregs' (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) :
    (mkS s0 pc r sp ps m v).vregs = ⟨v⟩ := rfl

theorem mkS_regs' (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128) :
    (mkS s0 pc r sp ps m v).regs = ⟨r⟩ := rfl

theorem reach_congr {p : Program} {s s' : State} {Q : State → Prop} (h : s' = s)
    (H : Reach p s' Q) : Reach p s Q := by subst h; exact H

theorem z12 (k : Nat) (hk : k < 2 ^ 12) :
    (BitVec.ofNat 12 k).zeroExtend 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp; omega


end X25519Dalek.GP

end
end

section
section
/-! # `<PublicKey as From<&StaticSecret>>::from` (block 18, 17 instructions)

Route: google-deepmind/code-verification @ 8c8d371f, `PubFromSecretProof.lean`
(`public_key_from_static_secret_ok_of`, Apache-2.0), re-proved without ProofLib's tactics. The block
copies the secret to its stack frame, calls `mul_base_clamped` into a stack `EdwardsPoint`, and calls
`to_montgomery` on it with the caller's output buffer. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

open Arm64 Arm64.Obj

abbrev pkName : String :=
  "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from"
abbrev mbcName : String := "<curve25519_dalek::edwards::EdwardsPoint>::mul_base_clamped"
abbrev tmName : String := "<curve25519_dalek::edwards::EdwardsPoint>::to_montgomery"

theorem pk_lookup : lookupBlockSym pkName x25519CliMultiLib.blocks = some (18, 0) := by
  decide +kernel

theorem mbc_lookup : lookupBlockSym mbcName x25519CliMultiLib.blocks = some (14, 0) := by
  decide +kernel

theorem tm_lookup : lookupBlockSym tmName x25519CliMultiLib.blocks = some (10, 0) := by
  decide +kernel

section fetch18
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem f18_0 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 0) =
    some (.addSubImm .W64 .SUB .sp .sp 0x0e0#12 false) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_4 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 4) =
    some (.stp .W64 (.gpr 29#5) (.gpr 30#5) (.Offset .sp 0xc0#64)) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_8 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 8) =
    some (.str .X64 (.gpr 19#5) (.Offset .sp 0xd0#64)) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_12 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 12) =
    some (.addSubImm .W64 .ADD (.gpr 29#5) .sp 0x0c0#12 false) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_16 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 16) =
    some (.ldpSimd .Q128 0#5 1#5 (.Offset (.gpr 0#5) 0#64)) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_20 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 20) =
    some (.logicalShift .W64 .ORR (.gpr 19#5) .xzr (.gpr 8#5) .LSL 0) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_24 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 24) =
    some (.addSubImm .W64 .ADD (.gpr 8#5) .sp 0x000#12 false) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_28 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 28) =
    some (.addSubImm .W64 .SUB (.gpr 0#5) (.gpr 29#5) 0x020#12 false) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_32 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 32) =
    some (.stpSimd .Q128 0#5 1#5 (.Offset (.gpr 29#5) 0xffffffffffffffe0#64)) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_40 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 40) =
    some (.addSubImm .W64 .ADD (.gpr 0#5) .sp 0x000#12 false) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_44 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 44) =
    some (.logicalShift .W64 .ORR (.gpr 8#5) .xzr (.gpr 19#5) .LSL 0) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_52 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 52) =
    some (.ldp .W64 false (.gpr 29#5) (.gpr 30#5) (.Offset .sp 0xc0#64)) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_56 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 56) =
    some (.ldr .W64 .X64 false (.gpr 19#5) (.Offset .sp 0xd0#64)) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_60 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 60) =
    some (.addSubImm .W64 .ADD .sp .sp 0x0e0#12 false) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_64 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 64) =
    some (.ret (.gpr 30#5)) :=
  fetch_at hP hCL (by decide) 18 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f18_36 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 36) =
    some (.bl (mpl.base 14 + BitVec.ofNat 64 0 - (mpl.base 18 + BitVec.ofNat 64 36))) :=
  fetch_bl hP hCL hk (by decide) mbcName x25519CliBlk18 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mbc_lookup (by decide) (fun _ => by decide) rfl

theorem f18_48 : (bprog mpl 18).fetchMem m (mpl.base 18 + BitVec.ofNat 64 48) =
    some (.bl (mpl.base 10 + BitVec.ofNat 64 0 - (mpl.base 18 + BitVec.ofNat 64 48))) :=
  fetch_bl hP hCL hk (by decide) tmName x25519CliBlk18 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) tm_lookup (by decide) (fun _ => by decide) rfl

end fetch18

set_option maxHeartbeats 8000000 in
theorem pk_ok (hMBC : fnOk mbcName edwardsPointMulBaseClampedSpec)
    (hTM : fnOk tmName (fun _ => edwardsPointToMontgomerySpec))
    (hU : ∀ s : List (BitVec 8), s.length = 32 →
      natToLeBytes 32 (edExtToMontgomeryU (edMulBase ed25519BasepointTableBytes (clampScalarBytes s))) =
        x25519Pubkey s) :
    x25519CliMultiLib.subroutineOk pkName publicKeyFromSecretSpec := by
  refine ⟨by decide, 18, 0, pk_lookup, fun mpl hP => ?_⟩
  intro x R s0 hpc hrun hpre hal hCLp
  obtain ⟨out, sec, out_bs, sec_bs⟩ := x
  have hfa : x25519CliMultiLib.fnAddr mpl pkName = mpl.base 18 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, pk_lookup]
  rw [hfa] at hpc
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, publicKeyFromSecretSpec] at hpre ⊢
  have h1 := Satisfies.of_eq hpre
    (Q := ⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = sec ∧ out_bs.length = 32 ∧
        sec_bs.length = 32⌝ ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ stackFrame s0 1904 ∗
      ((sec ↦ₛ sec_bs) ∗ (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗
        (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (out ↦ₛ out_bs) ∗ R)) (by ac_rfl)
  rw [sat_pure_sep, sat_pure_sep] at h1
  obtain ⟨⟨hx8, hx0, hlo, hls⟩, hCL, h1⟩ := h1
  clear hpre
  -- the frame
  set T := s0.sp - 224#64 with hT
  have hTal : T &&& 0b1111#64 = 0#64 := by
    have : s0.sp &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
    exact al16_sub _ 224 (by norm_num) (by norm_num) this
  have hst : stackFrame s0 1904 = memRegion (T - BitVec.ofNat 64 1680) (1680 + 224) := by
    show memRegion _ _ = _
    rw [show s0.sp - BitVec.ofNat 64 1904 = T - BitVec.ofNat 64 1680 by rw [hT]; bv_omega]
  rw [hst, bytes32_eq_cellsFrom sec sec_bs hls] at h1
  have h2 := sat_sep_mono h1 (memRegion_split _ 1680 224 (by norm_num))
  have eB : T - BitVec.ofNat 64 1680 + BitVec.ofNat 64 1680 = T := by bv_omega
  rw [eB, sepConj_assoc, sepConj_left_comm] at h2
  have h3 := sat_sep_mono h2 (memRegion_split T 160 64 (by norm_num))
  rw [sepConj_assoc, sepConj_left_comm] at h3
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, h3⟩ := sat_region64_cells h3
  clear h1 h2
  -- h3 : cells (T+160) ∗ memRegion T 160 ∗ memRegion (T-1680) 1680 ∗ sec cells ∗ table ∗ one ∗ out ∗ R
  show Reach (bprog mpl 18) s0 _
  refine reach_congr (s' := mkS s0 (mpl.base 18 + BitVec.ofNat 64 0) s0.regs.regs s0.sp s0.pstate
    s0.mem s0.vregs.regs) (by rw [← hpc]; rfl) ?_
  -- 0: sub sp, sp, #224
  refine Reach.mk hrun (f18_0 hP hCL (Memory.KeepsFrozen.refl _)) ?_
  rw [ex_sub_sp, z12 _ (by norm_num), pc_add]
  -- 4: stp x29, x30, [sp, #192]
  have c4 := cells_read _ _ _ _ h3 4 (by simp)
  have c5 := cells_read _ _ _ _ h3 5 (by simp)
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at c4 c5
  have e200 : T + 192#64 + 8#64 = T + 200#64 := by rw [BitVec.add_assoc]; rfl
  refine Reach.mk hrun (f18_4 hP hCL (Memory.KeepsFrozen.refl _)) ?_
  rw [ex_stp64_sp _ _ (by decide) (by decide) _ hTal c4.2.2 (e200 ▸ c5.2.2), pc_add, e200]
  have h4 := cells_write _ _ _ _ h3 4 (by simp) (s0.regs.regs 29#5)
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h4
  have c5' := cells_read _ _ _ _ h4 5 (by simp)
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at c5'
  have h5 := cells_write _ _ _ _ h4 5 (by simp) (s0.regs.regs 30#5)
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
    List.set_cons_succ, List.set_cons_zero] at h5
  have k1 := (Memory.keepsFrozen_write64 c4.2.2 (s0.regs.regs 29#5)).trans
    (Memory.keepsFrozen_write64 c5'.2.2 (s0.regs.regs 30#5))
  clear h3 h4 c4 c5 c5'
  generalize hm1 : (s0.mem.write64 (T + 192#64) (s0.regs.regs 29#5)).write64
      (T + 200#64) (s0.regs.regs 30#5) = m1 at h5 k1 ⊢
  -- 8: str x19, [sp, #208]
  have c6 := cells_read _ _ _ _ h5 6 (by simp)
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at c6
  refine Reach.mk hrun (f18_8 hP hCL k1) ?_
  rw [ex_str64_sp _ (by decide) _ hTal c6.2.2, pc_add]
  have h6 := cells_write _ _ _ _ h5 6 (by simp) (s0.regs.regs 19#5)
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
    List.set_cons_succ, List.set_cons_zero] at h6
  have k2 := k1.trans (Memory.keepsFrozen_write64 c6.2.2 (s0.regs.regs 19#5))
  clear h5 c6 k1
  generalize hm2 : m1.write64 (T + 208#64) (s0.regs.regs 19#5) = m2 at h6 k2 ⊢
  -- 12: add x29, sp, #192
  refine Reach.mk hrun (f18_12 hP hCL k2) ?_
  rw [ex_add_gpr_sp _ (by decide), z12 _ (by norm_num), pc_add]
  -- 16: ldp q0, q1, [x0]
  have hx0' : upd s0.regs.regs 29#5 (T + BitVec.ofNat 64 192) 0#5 = sec := by
    rw [upd_apply, if_neg (by decide), ← readGpr_eq _ _ (by decide)]; exact hx0
  have hq := h6
  rw [perm4123] at hq
  have q0 := cells_read128 hq 0 (by simp)
  have q2 := cells_read128 hq 2 (by simp)
  simp only [Nat.reduceMul, BitVec.add_zero] at q0 q2
  refine Reach.mk hrun (f18_16 hP hCL k2) ?_
  rw [ex_ldpq_gpr 0#5 0#5 1#5 (by decide) 0#64 (by rw [hx0', BitVec.add_zero]; exact q0.2.1)
    (by rw [hx0', BitVec.add_zero]; exact q2.2.1), pc_add, hx0', BitVec.add_zero, q0.1, q2.1]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  clear hq q0 q2
  -- 20: mov x19, x8
  refine Reach.mk hrun (f18_20 hP hCL k2) ?_
  rw [ex_mov _ _ (by decide) (by decide), pc_add]
  -- 24: add x8, sp, #0
  refine Reach.mk hrun (f18_24 hP hCL k2) ?_
  rw [ex_add_gpr_sp _ (by decide), z12 _ (by norm_num), pc_add]
  -- 28: sub x0, x29, #32
  refine Reach.mk hrun (f18_28 hP hCL k2) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), z12 _ (by norm_num), pc_add]
  have e160 : T + 192#64 - 32#64 = T + 160#64 := by bv_omega
  simp (config := { decide := true }) only [upd_apply, ↓reduceIte, BitVec.add_zero, e160]
  -- 32: stp q0, q1, [x29, #-32]
  have hx29 : (upd (upd (upd (upd s0.regs.regs 29#5 (T + 192#64)) 19#5 (s0.regs.regs 8#5)) 8#5 T)
      0#5 (T + 160#64)) 29#5 = T + 192#64 := by simp [upd_apply]
  have eoff : T + 192#64 + 0xffffffffffffffe0#64 = T + 160#64 := by rw [BitVec.add_assoc]; rfl
  have e176 : T + 160#64 + 16#64 = T + 176#64 := by rw [BitVec.add_assoc]; rfl
  have w0 := cells_read128 h6 0 (by simp)
  have w2 := cells_read128 h6 2 (by simp)
  simp only [Nat.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
    BitVec.ofNat_eq_ofNat] at w0 w2
  refine Reach.mk hrun (f18_32 hP hCL k2) ?_
  rw [ex_stpq_gpr 29#5 0#5 1#5 (by decide) _ (by rw [hx29, eoff]; exact w0.2.2)
    (by rw [hx29, eoff, e176]; exact w2.2.2), pc_add, hx29, eoff, e176]
  simp only [upd_apply, show (0#5 : BitVec 5) ≠ 1#5 by decide, show (1#5 : BitVec 5) ≠ 0#5 by decide,
    if_true, if_false]
  have h7 := cells_write128 h6 0 (by simp) (chunk sec_bs 1 ++ chunk sec_bs 0)
  simp only [Nat.reduceMul, BitVec.add_zero] at h7
  have w2' := cells_read128 h7 2 (by simp)
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at w2'
  have h8 := cells_write128 h7 2 (by simp) (chunk sec_bs 3 ++ chunk sec_bs 2)
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
    List.set_cons_succ, List.set_cons_zero, append_lo, append_hi] at h8
  have k3 := k2.trans ((Memory.keepsFrozen_write128 w0.2.2 (chunk sec_bs 1 ++ chunk sec_bs 0)).trans
    (Memory.keepsFrozen_write128 w2'.2.2 (chunk sec_bs 3 ++ chunk sec_bs 2)))
  clear h6 h7 w0 w2 w2' k2
  generalize hm3 : (m2.write128 (T + 160#64) (chunk sec_bs 1 ++ chunk sec_bs 0)).write128
    (T + 176#64) (chunk sec_bs 3 ++ chunk sec_bs 2) = m3 at h8 k3 ⊢
  -- 36: bl mul_base_clamped
  refine Reach.mk hrun (f18_36 hP hCL k3) ?_
  rw [ex_bl, pc_add]
  have epc : mpl.base 18 + BitVec.ofNat 64 36 +
      (mpl.base 14 + BitVec.ofNat 64 0 - (mpl.base 18 + BitVec.ofNat 64 36)) =
      mpl.base 14 + BitVec.ofNat 64 0 := by abel
  rw [show (0 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 : Nat) = 36 from rfl, epc]
  simp only [BitVec.add_zero]
  -- the first call
  obtain ⟨i14, off14, hlk14, hsub⟩ := hMBC
  rw [mbc_lookup] at hlk14
  obtain ⟨rfl, rfl⟩ : 14 = i14 ∧ 0 = off14 := by simpa using hlk14
  have hfa14 : x25519CliMultiLib.fnAddr mpl mbcName = mpl.base 14 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, mbc_lookup]
  have hstk : cellsFrom (T + 160#64) [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3,
      s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] =
      ((T + 160#64) ↦ₛ sec_bs) ∗
        cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] := by
    rw [bytes32_eq_cellsFrom _ sec_bs hls,
      show [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3,
      s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] =
      [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ++
      [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] from rfl, cellsFrom_append]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
  rw [hstk] at h8
  have h9 := sat_sep_mono (Satisfies.of_eq h8 (Q := memRegion T 160 ∗ ((T + 160#64) ↦ₛ sec_bs) ∗
      cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] ∗
      memRegion (T - BitVec.ofNat 64 1680) 1680 ∗
      cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗
      (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
      (out ↦ₛ out_bs) ∗ R)) (memRegion_entails_bytes T 160 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at h9
  obtain ⟨pt, h9⟩ := h9
  rw [sepConj_assoc, sat_pure_sep] at h9
  obtain ⟨hpt, h9⟩ := h9
  have hCL3 := libCodeLoaded_keepsFrozen hCL k3
  have hx8' : s0.regs.regs 8#5 = out := by rw [← readGpr_eq _ _ (by decide)]; exact hx8
  have hpre' : m3 ⊨
      ((⌜T = T ∧ T + 160#64 = T + 160#64 ∧ pt.length = 160 ∧ sec_bs.length = 32⌝ ∗
        (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
        (T ↦ₛ pt) ∗ ((T + 160#64) ↦ₛ sec_bs) ∗ memRegion (T - BitVec.ofNat 64 1680) 1680) ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl m3⌝) ∗
      (cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] ∗
        cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗
        (out ↦ₛ out_bs) ∗ R) := by
    have h10 : m3 ⊨ ⌜T = T ∧ T + 160#64 = T + 160#64 ∧ pt.length = 160 ∧ sec_bs.length = 32⌝ ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl m3⌝ ∗ (T ↦ₛ pt) ∗ ((T + 160#64) ↦ₛ sec_bs) ∗
        cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] ∗
        memRegion (T - BitVec.ofNat 64 1680) 1680 ∗
        cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗
        (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
        (out ↦ₛ out_bs) ∗ R := by
      rw [sat_pure_sep, sat_pure_sep]
      exact ⟨⟨rfl, rfl, hpt, hls⟩, hCL3, h9⟩
    exact Satisfies.of_eq h10
  have hcall := hsub mpl hP (T, T + 160#64, pt, sec_bs)
    (cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] ∗
        cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗
        (out ↦ₛ out_bs) ∗ R)
    (mkS s0 (mpl.base 14)
      (upd (upd (upd (upd (upd s0.regs.regs 29#5 (T + 192#64)) 19#5 (s0.regs.regs 8#5)) 8#5 T) 0#5
        (T + 160#64)) 30#5 (mpl.base 18 + BitVec.ofNat 64 (36 + 4))) T s0.pstate m3
      (upd (upd s0.vregs.regs 0#5 (chunk sec_bs 1 ++ chunk sec_bs 0)) 1#5
        (chunk sec_bs 3 ++ chunk sec_bs 2)))
    (by simp [hfa14]) hrun
    (by simpa [MultiPlacedLib.withCodeLoaded, stackFrame, mkS_sp, upd_apply] using hpre')
    (by simp [hTal]) (hCL3 14 (by decide))
  obtain ⟨sf, hsteps, hout⟩ := hcall
  refine Reach.steps (bsteps_transfer hsteps) ?_
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  rotate_left
  · exact (sat_false hpan).elim
  · exact (sat_false hex).elim
  · exact (sat_false hoom).elim
  have hpc40 : sf.pc = mpl.base 18 + BitVec.ofNat 64 40 := by
    rw [hpcf]; simp [upd_apply]
  have hspT : sf.sp = T := by rw [hspf]; rfl
  have kf : s0.mem.KeepsFrozen sf.mem := k3.trans (Steps.keepsFrozen hsteps)
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, edwardsPointMulBaseClampedSpec,
    stackFrame, hspT] at hpost
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, perm4123, sepExists_sepConj, sat_sepExists] at hpost
  obtain ⟨res, hpost⟩ := hpost
  rw [sepConj_assoc, sepConj_assoc, perm312, sat_pure_sep] at hpost
  obtain ⟨⟨hres52, hres⟩, hpost⟩ := hpost
  simp (config := { decide := true }) only [CalleeSavedPreserved, readGpr_unfold, mkS_regs',
    mkS_vregs', upd_apply, ↓reduceIte, Reg.fp, calleeSavedVRegs, VRegFile.calleeSaved,
    VRegFile.read] at hcs
  obtain ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, -, av⟩ := hcs
  clear hpcf hspf
  refine reach_congr (s' := mkS sf (mpl.base 18 + BitVec.ofNat 64 40) sf.regs.regs T sf.pstate
    sf.mem sf.vregs.regs) (by rw [← hpc40, ← hspT]; rfl) ?_
  -- 40: add x0, sp, #0
  refine Reach.mk hrunf (f18_40 hP hCL kf) ?_
  rw [ex_add_gpr_sp _ (by decide), z12 _ (by norm_num), pc_add, BitVec.add_zero]
  -- 44: mov x8, x19
  refine Reach.mk hrunf (f18_44 hP hCL kf) ?_
  rw [ex_mov _ _ (by decide) (by decide), pc_add]
  -- 48: bl to_montgomery
  refine Reach.mk hrunf (f18_48 hP hCL kf) ?_
  rw [ex_bl, pc_add]
  have epc2 : mpl.base 18 + BitVec.ofNat 64 48 +
      (mpl.base 10 + BitVec.ofNat 64 0 - (mpl.base 18 + BitVec.ofNat 64 48)) =
      mpl.base 10 + BitVec.ofNat 64 0 := by abel
  rw [show (40 + 4 + 4 : Nat) = 48 from rfl, epc2]
  simp only [BitVec.add_zero]
  -- the second call
  obtain ⟨i10, off10, hlk10, hsub2⟩ := hTM
  rw [tm_lookup] at hlk10
  obtain ⟨rfl, rfl⟩ : 10 = i10 ∧ 0 = off10 := by simpa using hlk10
  have hfa10 : x25519CliMultiLib.fnAddr mpl tmName = mpl.base 10 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, tm_lookup]
  have hp2 := sat_sep_mono (Satisfies.of_eq hpost (Q := memRegion (T - BitVec.ofNat 64 1680) 1680 ∗
      (T ↦ₛ res) ∗ (out ↦ₛ out_bs) ∗ ((T + 160#64) ↦ₛ clampScalarBytes sec_bs) ∗
      (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
      cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] ∗
      cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗ R))
    (memRegion_split (T - BitVec.ofNat 64 1680) 288 1392 (by norm_num))
  have eC : T - BitVec.ofNat 64 1680 + BitVec.ofNat 64 288 = T - BitVec.ofNat 64 1392 := by bv_omega
  rw [eC] at hp2
  have hCLf := libCodeLoaded_keepsFrozen hCL kf
  have hpre2 : sf.mem ⊨
      ((⌜sf.regs.regs 19#5 = out ∧ T = T ∧ out_bs.length = 32 ∧ fe51Point4Bounded res (2 ^ 53)⌝ ∗
        (T ↦ₛ res) ∗ (out ↦ₛ out_bs) ∗ memRegion (T - BitVec.ofNat 64 1392) 1392) ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl sf.mem⌝) ∗
      (memRegion (T - BitVec.ofNat 64 1680) 288 ∗ ((T + 160#64) ↦ₛ clampScalarBytes sec_bs) ∗
        (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
        cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] ∗
        cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗ R) := by
    have h10 : sf.mem ⊨
        ⌜sf.regs.regs 19#5 = out ∧ T = T ∧ out_bs.length = 32 ∧ fe51Point4Bounded res (2 ^ 53)⌝ ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl sf.mem⌝ ∗
        (memRegion (T - BitVec.ofNat 64 1680) 288 ∗ memRegion (T - BitVec.ofNat 64 1392) 1392) ∗
        (T ↦ₛ res) ∗ (out ↦ₛ out_bs) ∗ ((T + 160#64) ↦ₛ clampScalarBytes sec_bs) ∗
        (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
        cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] ∗
        cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗ R := by
      rw [sat_pure_sep, sat_pure_sep]
      exact ⟨⟨a19.trans hx8', rfl, hlo, fe51Point4Bounded_mono (by norm_num) hres52⟩, hCLf, hp2⟩
    exact Satisfies.of_eq h10
  have hcall2 := hsub2 mpl hP (out, T, out_bs, res)
    (memRegion (T - BitVec.ofNat 64 1680) 288 ∗ ((T + 160#64) ↦ₛ clampScalarBytes sec_bs) ∗
        (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
        cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] ∗
        cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗ R)
    (mkS sf (mpl.base 10)
      (upd (upd (upd sf.regs.regs 0#5 T) 8#5 (upd sf.regs.regs 0#5 T 19#5)) 30#5
        (mpl.base 18 + BitVec.ofNat 64 (48 + 4))) T sf.pstate sf.mem sf.vregs.regs)
    (by simp [hfa10]) hrunf
    (by simpa [MultiPlacedLib.withCodeLoaded, stackFrame, mkS_sp, upd_apply] using hpre2)
    (by simp [hTal]) (hCLf 10 (by decide))
  obtain ⟨sf2, hsteps2, hout2⟩ := hcall2
  refine Reach.steps (bsteps_transfer hsteps2) ?_
  rcases hout2 with ⟨⟨hpcf2, hspf2, hrunf2⟩, ⟨_, hcs2⟩, hpost2⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ |
    ⟨_, hoom⟩
  rotate_left
  · exact (sat_false hpan).elim
  · exact (sat_false hex).elim
  · exact (sat_false hoom).elim
  have hpc52 : sf2.pc = mpl.base 18 + BitVec.ofNat 64 52 := by
    rw [hpcf2]; simp [upd_apply]
  have hspT2 : sf2.sp = T := by rw [hspf2]; rfl
  have kf2 : s0.mem.KeepsFrozen sf2.mem := kf.trans (by have := Steps.keepsFrozen hsteps2; exact this)
  simp (config := { decide := true }) only [CalleeSavedPreserved, readGpr_unfold, mkS_regs',
    mkS_vregs', upd_apply, ↓reduceIte, Reg.fp, calleeSavedVRegs, VRegFile.calleeSaved,
    VRegFile.read] at hcs2
  obtain ⟨b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, -, bv⟩ := hcs2
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, edwardsPointToMontgomerySpec,
    stackFrame, hspT2, hres, hU sec_bs hls] at hpost2
  clear hpcf2 hspf2
  refine reach_congr (s' := mkS sf2 (mpl.base 18 + BitVec.ofNat 64 52) sf2.regs.regs T sf2.pstate
    sf2.mem sf2.vregs.regs) (by rw [← hpc52, ← hspT2]; rfl) ?_
  -- 52: ldp x29, x30, [sp, #192]
  have hp3 := Satisfies.of_eq hpost2 (Q := cellsFrom (T + 192#64)
      [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7] ∗
      ((T ↦ₛ res) ∗ memRegion (T - BitVec.ofNat 64 1392) 1392 ∗
      (out ↦ₛ x25519Pubkey sec_bs) ∗ memRegion (T - BitVec.ofNat 64 1680) 288 ∗
      ((T + 160#64) ↦ₛ clampScalarBytes sec_bs) ∗
      (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
      cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗ R))
  have r0 := cells_read _ _ _ _ hp3 0 (by simp)
  have r1 := cells_read _ _ _ _ hp3 1 (by simp)
  have r2 := cells_read _ _ _ _ hp3 2 (by simp)
  simp only [Nat.reduceMul, BitVec.add_zero, List.getElem_cons_succ, List.getElem_cons_zero] at r0 r1
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
    List.getElem_cons_succ, List.getElem_cons_zero] at r2
  refine Reach.mk hrunf2 (f18_52 hP hCL kf2) ?_
  rw [ex_ldp64_sp _ _ (by decide) (by decide) _ hTal r0.2.1 r1.2.1, pc_add, r0.1, r1.1]
  -- 56: ldr x19, [sp, #208]
  refine Reach.mk hrunf2 (f18_56 hP hCL kf2) ?_
  rw [ex_ldr64_sp _ (by decide) _ hTal r2.2.1, pc_add, r2.1]
  -- 60: add sp, sp, #224
  refine Reach.mk hrunf2 (f18_60 hP hCL kf2) ?_
  rw [ex_add_sp, z12 _ (by norm_num), pc_add]
  -- 64: ret
  refine Reach.mk hrunf2 (f18_64 hP hCL kf2) ?_
  rw [ex_ret]
  refine Reach.done ?_
  have hS : T + BitVec.ofNat 64 224 = s0.sp := by rw [hT]; exact sub_add_cancel _ _
  left
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp [upd_apply, readGpr_unfold]
  · exact hS
  · exact hrunf2
  · exact hS
  · simp (config := { decide := true }) only [CalleeSavedPreserved, readGpr_unfold, mkS_regs',
      mkS_vregs', upd_apply, ↓reduceIte, Reg.fp, calleeSavedVRegs, VRegFile.calleeSaved,
      VRegFile.read]
    exact ⟨trivial, b20.trans a20, b21.trans a21, b22.trans a22, b23.trans a23, b24.trans a24,
      b25.trans a25, b26.trans a26, b27.trans a27, b28.trans a28, trivial, bv.trans av⟩
  · have h := sat_sep_mono (Satisfies.of_eq hp3
      (Q := (memRegion (T - BitVec.ofNat 64 1680) 288 ∗ memRegion (T - BitVec.ofNat 64 1392) 1392 ∗
        (T ↦ₛ res) ∗ ((T + 160#64) ↦ₛ clampScalarBytes sec_bs) ∗
        cellsFrom (T + 192#64) [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 19#5, u7]) ∗
        (cellsFrom sec [chunk sec_bs 0, chunk sec_bs 1, chunk sec_bs 2, chunk sec_bs 3] ∗
        (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
        (out ↦ₛ x25519Pubkey sec_bs) ∗ R)))
      (pk_stack_merge T res (clampScalarBytes sec_bs) hres52.1 (clampScalarBytes_length _ hls) _ rfl)
    rw [← bytes32_eq_cellsFrom sec sec_bs hls] at h
    have ea : T + BitVec.ofNat 64 224 - BitVec.ofNat 64 1904 = T - BitVec.ofNat 64 1680 := by
      bv_omega
    simp only [stackFrame, mkS_sp, mkS_mem, ea]
    exact Satisfies.of_eq h

theorem subroutineOk_publicKey_from_dev :
    x25519CliMultiLib.subroutineOk pkName publicKeyFromSecretSpec :=
  pk_ok fnOk_edwardsPoint_mul_base_clamped fnOk_edwardsPoint_to_montgomery
    edExtToMontgomeryU_mulBase_clamped

end X25519Dalek.GP

end
end

section
open X25519Dalek

theorem solution :
    x25519CliMultiLib.subroutineOk
      "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from"
      publicKeyFromSecretSpec := by
  apply X25519Dalek.GP.subroutineOk_publicKey_from_dev <;> assumption

end
