-- Prove2me | solution 1 for X25519Dalek.fnOk_fe51_pow22501
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T12:25:01.345727+00:00
-- url     : https://prove2.me/submissions/a37026cf-ff0c-4b64-a050-40471bc94842

import Mathlib
import Definitions.Def_X25519Dalek_Spec
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_X25519Dalek_steps_keepsFrozen
import Theorems.Thm_X25519Dalek_fnOk_fe51_pow2k
import Theorems.Thm_X25519Dalek_fnOk_fe51_mul

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

end Memory

/-! ## Every step keeps frozen memory -/

@[simp]
theorem evalSvc_tpidrEl0 (svc : State → State) (s : State) :
    (evalSvc svc s).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

namespace Memory

end Memory

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


end ExecHelpers

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

/-! ## Interface of the loaded-code predicates -/

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

theorem upd_ne {α : Type} (r : BitVec 5 → α) {i j : BitVec 5} (v : α) (h : j ≠ i) :
    upd r i v j = r j := by
  simp [upd, h]

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

end X25519Dalek.GP
end

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

theorem memRegion8_cell (a : BitVec 64) : memRegion a 8 ⊢ ∃∗ v, a ↦₆₄ v := by
  intro h hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a 8 (by omega) h hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  refine ⟨pack64 bs, ?_⟩
  show (a ↦₆₄ pack64 bs).holds h
  rw [← bytes8_cell a bs hl]; exact hb

theorem cell_memRegion8 (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [pointsTo64_eq_bytes]
  exact unpack64_length v ▸ bytes_entails_memRegion a (unpack64 v)

/-- Split off an owned 64-bit cell at the bottom of a region, under a frame. -/
theorem sat_region_cell {m : Memory} {a : BitVec 64} {n : Nat} {F : SepProp}
    (hn : n + 8 < 2 ^ 64) (hs : m ⊨ memRegion a (8 + n) ∗ F) :
    ∃ v, m ⊨ (a ↦₆₄ v) ∗ memRegion (a + 8#64) n ∗ F := by
  have h1 := sat_sep_mono hs (memRegion_split a 8 n (by omega))
  rw [sepConj_assoc] at h1
  have h2 := sat_sep_mono h1 (memRegion8_cell a)
  rw [sepExists_sepConj, sat_sepExists] at h2
  exact h2

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

theorem bytes32_eq_cellsFrom (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) = cellsFrom a [chunk bs 0, chunk bs 1, chunk bs 2, chunk bs 3] := by
  rw [bytes32_cells a bs h]
  simp only [cellsFrom_cons, cellsFrom_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

/-! ## Frame permutations -/

end X25519Dalek.GP
end

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

end exec

end X25519Dalek.GP
end

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


end X25519Dalek.GP
end

section
/-! # `pow22501`: calling `mul` and `pow2k` through their published contracts

A call from block 5 at byte offset `off`: the `BL` (relocated to the callee's block), the callee's
`fnOk` contract with the caller's frame `F`, and the return. The frame and step bookkeeping follow
the sibling batch q447-xd-goal's `PK.lean`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

open Arm64 Arm64.Obj

abbrev mulName : String :=
  "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul"
abbrev p2kName : String := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k"
abbrev p22Name : String := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501"

theorem mul_lookup : lookupBlockSym mulName x25519CliMultiLib.blocks = some (1, 0) := by
  decide +kernel
theorem p2k_lookup : lookupBlockSym p2kName x25519CliMultiLib.blocks = some (2, 0) := by
  decide +kernel
theorem p22_lookup : lookupBlockSym p22Name x25519CliMultiLib.blocks = some (5, 0) := by
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

/-- A call to `mul` from block 5 at offset `off`. -/
theorem call_mul {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hM : fnOk mulName (fun _ => fe51MulSpec)) {s0 : State}
    (hCL0 : x25519CliMultiLib.CodeLoaded mpl s0.mem) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {out a b : BitVec 64} {A B O : List (BitVec 8)} {F : SepProp}
    (hrun : sb.status = .Running) (hkf : s0.mem.KeepsFrozen m)
    (hf : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 off))))
    (hal : sp &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = out) (h0 : r 0#5 = a) (h1 : r 1#5 = b)
    (hmem : m ⊨ ((a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F)
    (hA : fe51LimbsBounded A (2 ^ 54)) (hB : fe51LimbsBounded B (2 ^ 54)) (hO : O.length = 40)
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running →
      sf.pc = mpl.base 5 + BitVec.ofNat 64 (off + 4) → sf.sp = sp → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ → s0.mem.KeepsFrozen sf.mem →
      (sf.mem ⊨ ((a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ res) ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F) →
      fe51LimbsBounded res (2 ^ 52) →
      fe51ValOfBytes res % p25519 = fe51ValOfBytes A * fe51ValOfBytes B % p25519 →
      Reach (bprog mpl 5) sf Q) :
    Reach (bprog mpl 5) (mkS sb (mpl.base 5 + BitVec.ofNat 64 off) r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  rw [ex_bl]
  have epc : mpl.base 5 + BitVec.ofNat 64 off + (mpl.base 1 + BitVec.ofNat 64 0 -
      (mpl.base 5 + BitVec.ofNat 64 off)) = mpl.base 1 + BitVec.ofNat 64 0 := by abel
  rw [epc]
  obtain ⟨i1, o1, hlk1, hsub⟩ := hM
  rw [mul_lookup] at hlk1
  obtain ⟨rfl, rfl⟩ : 1 = i1 ∧ 0 = o1 := by simpa using hlk1
  have hfa : x25519CliMultiLib.fnAddr mpl mulName = mpl.base 1 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, mul_lookup]
  have hCL := libCodeLoaded_keepsFrozen hCL0 hkf
  set s1 := mkS sb (mpl.base 1 + BitVec.ofNat 64 0) (upd r 30#5 (mpl.base 5 + BitVec.ofNat 64 off + 4#64))
    sp ps m v with hs1
  have hpre : s1.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec ((fun _ => fe51MulSpec) mpl) (mpl.base 1))).pre (out, a, b, O, A, B) s1 ∗ F := by
    have e8 : s1.readReg64 Reg.x8 = out := by simp [hs1, Reg.x8, h8]
    have e0 : s1.readReg64 Reg.x0 = a := by simp [hs1, Reg.x0, h0]
    have e1 : s1.readReg64 Reg.x1 = b := by simp [hs1, Reg.x1, h1]
    have h10 : s1.mem ⊨ ⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧ s1.readReg64 Reg.x1 = b ∧
        O.length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧ fe51LimbsBounded B (2 ^ 54)⌝ ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝ ∗
        (((a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ O) ∗ stackFrame s1 224) ∗ F) := by
      rw [sat_pure_sep, sat_pure_sep]; exact ⟨⟨e8, e0, e1, hO, hA, hB⟩, hCL, hmem⟩
    show s1.mem ⊨ ((⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧ s1.readReg64 Reg.x1 = b ∧
        O.length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧ fe51LimbsBounded B (2 ^ 54)⌝ ∗
        (a ↦ₛ A) ∗ (b ↦ₛ B) ∗ (out ↦ₛ O) ∗ stackFrame s1 224) ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝) ∗ F
    exact Satisfies.of_eq h10
  obtain ⟨sf, hsteps, hout⟩ := hsub mpl hP (out, a, b, O, A, B) F s1 (by simp [hs1, hfa]) hrun hpre
    (by simp [hs1, hal]) (hCL 1 (by decide))
  refine Reach.steps (bsteps_transfer hsteps) ?_
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  rotate_left
  · exact (sat_false hpan).elim
  · exact (sat_false hex).elim
  · exact (sat_false hoom).elim
  have hpc' : sf.pc = mpl.base 5 + BitVec.ofNat 64 (off + 4) := by
    rw [hpcf]; simp [hs1, upd_apply, BitVec.add_assoc, BitVec.ofNat_add]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  have kf : s0.mem.KeepsFrozen sf.mem := hkf.trans (X25519Dalek.steps_keepsFrozen hsteps)
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
  refine hcont sf res hrunf hpc' hsp' ?_ ?_ kf hp3 hb52 hval
  · intro k hk1 hk2
    have := kept_of_cs hcs' k hk1 hk2
    rw [this, upd_apply, if_neg]
    intro e; subst e; simp at hk2
  · have := hcs'.2.2.2.2.2.2.2.2.2.2.2
    rw [this]; rfl

/-- A call to `pow2k` from block 5 at offset `off`. -/
theorem call_p2k {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hM : fnOk p2kName (fun _ => fe51Pow2kSpec)) {s0 : State}
    (hCL0 : x25519CliMultiLib.CodeLoaded mpl s0.mem) {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory}
    {v : BitVec 5 → BitVec 128} {out a : BitVec 64} {kk : Nat} {A O : List (BitVec 8)} {F : SepProp}
    (hrun : sb.status = .Running) (hkf : s0.mem.KeepsFrozen m)
    (hf : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 off))))
    (hal : sp &&& 0b1111#64 = 0#64)
    (h8 : r 8#5 = out) (h0 : r 0#5 = a) (h1 : r 1#5 = BitVec.ofNat 64 kk) (hk1 : 0 < kk) (hk2 : kk < 256)
    (hmem : m ⊨ ((a ↦ₛ A) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F)
    (hA : fe51LimbsBounded A (2 ^ 54)) (hO : O.length = 40)
    (hcont : ∀ (sf : State) (res : List (BitVec 8)), sf.status = .Running →
      sf.pc = mpl.base 5 + BitVec.ofNat 64 (off + 4) → sf.sp = sp → KeptRegs sf r →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ → s0.mem.KeepsFrozen sf.mem →
      (sf.mem ⊨ ((a ↦ₛ A) ∗ (out ↦ₛ res) ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F) →
      fe51LimbsBounded res (2 ^ 52) →
      fe51ValOfBytes res % p25519 = fpPow (fe51ValOfBytes A % p25519) (2 ^ kk) →
      Reach (bprog mpl 5) sf Q) :
    Reach (bprog mpl 5) (mkS sb (mpl.base 5 + BitVec.ofNat 64 off) r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  rw [ex_bl]
  have epc : mpl.base 5 + BitVec.ofNat 64 off + (mpl.base 2 + BitVec.ofNat 64 0 -
      (mpl.base 5 + BitVec.ofNat 64 off)) = mpl.base 2 + BitVec.ofNat 64 0 := by abel
  rw [epc]
  obtain ⟨i1, o1, hlk1, hsub⟩ := hM
  rw [p2k_lookup] at hlk1
  obtain ⟨rfl, rfl⟩ : 2 = i1 ∧ 0 = o1 := by simpa using hlk1
  have hfa : x25519CliMultiLib.fnAddr mpl p2kName = mpl.base 2 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, p2k_lookup]
  have hCL := libCodeLoaded_keepsFrozen hCL0 hkf
  set s1 := mkS sb (mpl.base 2 + BitVec.ofNat 64 0) (upd r 30#5 (mpl.base 5 + BitVec.ofNat 64 off + 4#64))
    sp ps m v with hs1
  have esp : sp - BitVec.ofNat 64 224 + BitVec.ofNat 64 128 = sp - BitVec.ofNat 64 96 := by bv_omega
  have hm2 := Satisfies.of_eq hmem (Q := memRegion (sp - BitVec.ofNat 64 224) (128 + 96) ∗
    ((a ↦ₛ A) ∗ (out ↦ₛ O) ∗ F))
  have hm3 := sat_sep_mono hm2 (memRegion_split _ 128 96 (by norm_num))
  rw [esp] at hm3
  have hm4 : m ⊨ ((a ↦ₛ A) ∗ (out ↦ₛ O) ∗ memRegion (sp - BitVec.ofNat 64 96) 96) ∗ (memRegion (sp - BitVec.ofNat 64 224) 128 ∗ F) :=
    Satisfies.of_eq hm3
  have hpre : s1.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec ((fun _ => fe51Pow2kSpec) mpl) (mpl.base 2))).pre
        (out, a, BitVec.ofNat 32 kk, O, A) s1 ∗ (memRegion (sp - BitVec.ofNat 64 224) 128 ∗ F) := by
    have e8 : s1.readReg64 Reg.x8 = out := by simp [hs1, Reg.x8, h8]
    have e0 : s1.readReg64 Reg.x0 = a := by simp [hs1, Reg.x0, h0]
    have e1 : s1.readReg32 Reg.x1 = BitVec.ofNat 32 kk := by
      simp [hs1, Reg.x1, h1, State.readReg32]
    have h10 : s1.mem ⊨ ⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧
        s1.readReg32 Reg.x1 = BitVec.ofNat 32 kk ∧ O.length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧
        0 < (BitVec.ofNat 32 kk).toNat ∧ (BitVec.ofNat 32 kk).toNat < 256⌝ ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝ ∗
        (((a ↦ₛ A) ∗ (out ↦ₛ O) ∗ stackFrame s1 96) ∗ (memRegion (sp - BitVec.ofNat 64 224) 128 ∗ F)) := by
      rw [sat_pure_sep, sat_pure_sep]
      refine ⟨⟨e8, e0, e1, hO, hA, ?_, ?_⟩, hCL, hm4⟩
      · simp only [BitVec.toNat_ofNat]; omega
      · simp only [BitVec.toNat_ofNat]; omega
    show s1.mem ⊨ ((⌜s1.readReg64 Reg.x8 = out ∧ s1.readReg64 Reg.x0 = a ∧
        s1.readReg32 Reg.x1 = BitVec.ofNat 32 kk ∧ O.length = 40 ∧ fe51LimbsBounded A (2 ^ 54) ∧
        0 < (BitVec.ofNat 32 kk).toNat ∧ (BitVec.ofNat 32 kk).toNat < 256⌝ ∗
        (a ↦ₛ A) ∗ (out ↦ₛ O) ∗ stackFrame s1 96) ∗
        ⌜x25519CliMultiLib.CodeLoaded mpl s1.mem⌝) ∗ (memRegion (sp - BitVec.ofNat 64 224) 128 ∗ F)
    exact Satisfies.of_eq h10
  obtain ⟨sf, hsteps, hout⟩ := hsub mpl hP (out, a, BitVec.ofNat 32 kk, O, A) (memRegion (sp - BitVec.ofNat 64 224) 128 ∗ F) s1 (by simp [hs1, hfa])
    hrun hpre (by simp [hs1, hal]) (hCL 2 (by decide))
  refine Reach.steps (bsteps_transfer hsteps) ?_
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  rotate_left
  · exact (sat_false hpan).elim
  · exact (sat_false hex).elim
  · exact (sat_false hoom).elim
  have hpc' : sf.pc = mpl.base 5 + BitVec.ofNat 64 (off + 4) := by
    rw [hpcf]; simp [hs1, upd_apply, BitVec.add_assoc, BitVec.ofNat_add]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  have kf : s0.mem.KeepsFrozen sf.mem := hkf.trans (X25519Dalek.steps_keepsFrozen hsteps)
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, fe51Pow2kSpec, stackFrame, hsp'] at hpost
  have hp2 := Satisfies.of_eq hpost (Q := (∃∗ res : List (BitVec 8), (out ↦ₛ res) ∗
      ⌜fe51LimbsBounded res (2 ^ 52) ∧ fe51ValOfBytes res % p25519 =
        fpPow (fe51ValOfBytes A % p25519) (2 ^ (BitVec.ofNat 32 kk).toNat)⌝) ∗
      ((a ↦ₛ A) ∗ memRegion (sp - BitVec.ofNat 64 96) 96 ∗ (memRegion (sp - BitVec.ofNat 64 224) 128 ∗ F)))
  rw [sepExists_sepConj, sat_sepExists] at hp2
  obtain ⟨res, hp2⟩ := hp2
  have hp3 := Satisfies.of_eq hp2 (Q := ⌜fe51LimbsBounded res (2 ^ 52) ∧ fe51ValOfBytes res % p25519 =
        fpPow (fe51ValOfBytes A % p25519) (2 ^ (BitVec.ofNat 32 kk).toNat)⌝ ∗
      (memRegion (sp - BitVec.ofNat 64 224) 128 ∗ memRegion (sp - BitVec.ofNat 64 96) 96) ∗
        ((a ↦ₛ A) ∗ (out ↦ₛ res) ∗ F))
  rw [sat_pure_sep] at hp3
  obtain ⟨⟨hb52, hval⟩, hp3⟩ := hp3
  have hp4 := sat_sep_mono hp3 (memRegion_merge (sp - BitVec.ofNat 64 224) (sp - BitVec.ofNat 64 96)
    128 96 esp.symm (by norm_num) (by norm_num))
  have hp5 : sf.mem ⊨ ((a ↦ₛ A) ∗ (out ↦ₛ res) ∗ memRegion (sp - BitVec.ofNat 64 224) 224) ∗ F :=
    Satisfies.of_eq hp4
  have hkk : (BitVec.ofNat 32 kk).toNat = kk := by simp; omega
  rw [hkk] at hval
  have hcs' := hcs
  simp only [hs1] at hcs'
  refine hcont sf res hrunf hpc' hsp' ?_ ?_ kf hp5 hb52 hval
  · intro k hk1 hk2
    have := kept_of_cs hcs' k hk1 hk2
    rw [this, upd_apply, if_neg]
    intro e; subst e; simp at hk2
  · have := hcs'.2.2.2.2.2.2.2.2.2.2.2
    rw [this]; rfl

end X25519Dalek.GP
end

section
/-! # Instruction shapes of `pow22501` not covered by the shared step lemmas -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_stp64_pre_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 8 = true)
    (hw2 : m.canWrite (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.PreIndex .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r (sp + off) ps ((m.write64 (sp + off) (r a)).write64 (sp + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw1, hw2, ha, hb,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldp64_post_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead sp 8 = true)
    (hr2 : m.canRead (sp + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.PostIndex .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 sp)) b (m.read64 (sp + 8#64))) (sp + off) ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr1, hr2, ha, hb,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_movz32 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W32 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (imm.zeroExtend 64)) sp ps m v := by
  simp only [execInstWithSvc, execMoveWide, State.writeReg, mkS_writeGpr, hd, if_false,
    mkS_advancePC]
  congr 2
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem ex_str64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw : m.canWrite (r n + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (r n + off) (r a)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, ha, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldpq_sp (t1 t2 : BitVec 5) (off : BitVec 64) (hal : (sp &&& 0b1111#64) = 0#64)
    (hr1 : m.canRead (sp + off) 16 = true) (hr2 : m.canRead (sp + off + 16#64) 16 = true) :
    execInstWithSvc svc (.ldpSimd .Q128 t1 t2 (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps m
        (upd (upd v t1 (m.read128 (sp + off))) t2 (m.read128 (sp + off + 16#64))) := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr1, hr2,
    Memory.readSimdSized, AddrMode.baseReg]

theorem ex_strq_gpr (t n : BitVec 5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw : m.canWrite (r n + off) 16 = true) :
    execInstWithSvc svc (.strSimd .Q128 t (.UnscaledOffset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write128 (r n + off) (v t)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, hn,
    Memory.writeSimdSized, AddrMode.baseReg]

end exec

end X25519Dalek.GP
end

section
/-! # `pow22501` (block 5): fetch lemmas -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

open Arm64 Arm64.Obj

section fetch05
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem f05_0 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 0) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffd0#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_4 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 4) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x1c#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_8 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 8) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_12 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 12) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.sp) 0x000#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_16 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 16) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x300#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_20 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 20) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_24 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 24) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_28 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 28) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x008#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_32 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 32) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_36 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 36) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0001#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_40 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 40) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 40))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_44 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 44) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_48 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 48) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x008#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_52 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 52) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0001#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_56 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 56) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 56))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_60 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 60) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x030#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_64 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 64) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_68 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 68) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0001#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_72 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 72) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 72))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_76 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 76) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x058#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_80 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 80) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.sp) 0x030#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_84 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 84) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x14#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_88 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 88) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 88))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_92 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 92) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x080#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_96 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 96) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x008#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_100 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 100) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.sp) 0x058#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_104 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 104) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 104))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_108 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 108) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x0a8#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_112 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 112) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x080#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_116 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 116) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0001#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_120 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 120) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 120))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_124 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 124) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x0d0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_128 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 128) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x058#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_132 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 132) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.sp) 0x0a8#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_136 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 136) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 136))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_140 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 140) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x0f8#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_144 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 144) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x0d0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_148 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 148) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0005#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_152 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 152) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 152))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_156 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 156) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x120#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_160 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 160) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x0f8#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_164 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 164) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.sp) 0x0d0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_168 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 168) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 168))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_172 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 172) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x148#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_176 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 176) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x120#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_180 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 180) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x000a#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_184 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 184) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 184))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_188 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 188) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x170#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_192 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 192) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x148#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_196 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 196) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.sp) 0x120#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_200 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 200) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 200))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_204 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 204) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x198#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_208 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 208) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x170#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_212 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 212) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0014#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_216 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 216) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 216))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_220 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 220) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x1c0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_224 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 224) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x198#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_228 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 228) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.sp) 0x170#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_232 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 232) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 232))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_236 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 236) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.sp) 0x1e8#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_240 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 240) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x1c0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_244 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 244) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x000a#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_248 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 248) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 248))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_252 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 252) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x0f0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_256 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 256) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x1e8#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_260 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 260) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.sp) 0x120#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_264 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 264) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 264))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_268 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 268) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x0c8#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_272 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 272) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x0f0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_276 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 276) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0032#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_280 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 280) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 280))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_284 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 284) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_288 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 288) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x0c8#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_292 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 292) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x1d#5) 0x0f0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_296 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 296) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 296))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_300 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 300) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x078#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_304 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 304) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_308 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 308) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0064#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_312 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 312) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 312))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_316 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 316) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_320 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 320) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x078#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_324 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 324) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x1d#5) 0x0a0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_328 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 328) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 328))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_332 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 332) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1d#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_336 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 336) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x050#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_340 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 340) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0032#16 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_344 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 344) =
    some (.bl (mpl.base 2 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 344))) :=
  fetch_bl hP hCL hk (by decide) p2kName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) p2k_lookup (by decide) (fun _ => by decide) rfl

theorem f05_348 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 348) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1d#5) 0x028#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_352 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 352) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x1d#5) 0x0f0#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_356 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 356) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_360 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 360) =
    some (.bl (mpl.base 1 + BitVec.ofNat 64 0 - (mpl.base 5 + BitVec.ofNat 64 360))) :=
  fetch_bl hP hCL hk (by decide) mulName x25519CliBlk05 rfl ⟨by decide, by decide⟩ rfl (by decide)
    (by decide +kernel) (by decide) mul_lookup (by decide) (fun _ => by decide) rfl

theorem f05_364 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 364) =
    some (Arm64.Instr.ldpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x01#5 (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000080#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_368 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 368) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000a0#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_372 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 372) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000048#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_376 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 376) =
    some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x13#5) 0x0000000000000028#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_380 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 380) =
    some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x01#5 (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x13#5) 0x0000000000000038#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_384 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 384) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x300#12 false) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_388 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 388) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_392 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 392) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x1c#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_396 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 396) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000030#64)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

theorem f05_400 : (bprog mpl 5).fetchMem m (mpl.base 5 + BitVec.ofNat 64 400) =
    some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) :=
  fetch_at hP hCL (by decide) 5 ⟨⟨by decide, by decide⟩, by decide, by decide +kernel⟩ hk

end fetch05

end X25519Dalek.GP
end

section
/-! # `pow22501`: the stack layout -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

open Arm64 Arm64.Obj

theorem stack_layout {m : Memory} {SP2 : BitVec 64} {F : SepProp}
    (hs : m ⊨ memRegion (SP2 - BitVec.ofNat 64 224) (224 + 816) ∗ F) :
    ∃ (B0 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16 B17 B18 : List (BitVec 8)) (u0 u1 u2 u3 u4 u5 : BitVec 64),
      (B0.length = 40 ∧ B1.length = 40 ∧ B2.length = 40 ∧ B3.length = 40 ∧ B4.length = 40 ∧ B5.length = 40 ∧ B6.length = 40 ∧ B7.length = 40 ∧ B8.length = 40 ∧ B9.length = 40 ∧ B10.length = 40 ∧ B11.length = 40 ∧ B12.length = 40 ∧ B13.length = 40 ∧ B14.length = 40 ∧ B15.length = 40 ∧ B16.length = 40 ∧ B17.length = 40 ∧ B18.length = 40) ∧
      m ⊨ (memRegion (SP2 - BitVec.ofNat 64 224) 224 ∗ memRegion SP2 8 ∗
        ((SP2 + BitVec.ofNat 64 8) ↦ₛ B0) ∗ ((SP2 + BitVec.ofNat 64 48) ↦ₛ B1) ∗ ((SP2 + BitVec.ofNat 64 88) ↦ₛ B2) ∗ ((SP2 + BitVec.ofNat 64 128) ↦ₛ B3) ∗ ((SP2 + BitVec.ofNat 64 168) ↦ₛ B4) ∗ ((SP2 + BitVec.ofNat 64 208) ↦ₛ B5) ∗ ((SP2 + BitVec.ofNat 64 248) ↦ₛ B6) ∗ ((SP2 + BitVec.ofNat 64 288) ↦ₛ B7) ∗ ((SP2 + BitVec.ofNat 64 328) ↦ₛ B8) ∗ ((SP2 + BitVec.ofNat 64 368) ↦ₛ B9) ∗ ((SP2 + BitVec.ofNat 64 408) ↦ₛ B10) ∗ ((SP2 + BitVec.ofNat 64 448) ↦ₛ B11) ∗ ((SP2 + BitVec.ofNat 64 488) ↦ₛ B12) ∗ ((SP2 + BitVec.ofNat 64 528) ↦ₛ B13) ∗ ((SP2 + BitVec.ofNat 64 568) ↦ₛ B14) ∗ ((SP2 + BitVec.ofNat 64 608) ↦ₛ B15) ∗ ((SP2 + BitVec.ofNat 64 648) ↦ₛ B16) ∗ ((SP2 + BitVec.ofNat 64 688) ↦ₛ B17) ∗ ((SP2 + BitVec.ofNat 64 728) ↦ₛ B18) ∗
        ((SP2 + BitVec.ofNat 64 768) ↦₆₄ u0) ∗ ((SP2 + BitVec.ofNat 64 776) ↦₆₄ u1) ∗ ((SP2 + BitVec.ofNat 64 784) ↦₆₄ u2) ∗ ((SP2 + BitVec.ofNat 64 792) ↦₆₄ u3) ∗ ((SP2 + BitVec.ofNat 64 800) ↦₆₄ u4) ∗ ((SP2 + BitVec.ofNat 64 808) ↦₆₄ u5)) ∗ F := by
  have h := sat_sep_mono hs (memRegion_split _ 224 816 (by norm_num))
  rw [show SP2 - BitVec.ofNat 64 224 + BitVec.ofNat 64 224 = SP2 by bv_omega, sepConj_assoc] at h
  rw [sepConj_left_comm] at h
  have h0 := sat_sep_mono h (memRegion_split SP2 8 808 (by norm_num))
  rw [sepConj_assoc] at h0
  rw [sepConj_left_comm] at h0
  have g0 := sat_sep_mono h0 (memRegion_split (SP2 + BitVec.ofNat 64 8) 40 768 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 8 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 48 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g0
  have k0 := sat_sep_mono g0 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 8) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k0
  obtain ⟨B0, k0⟩ := k0
  rw [sepConj_assoc, sat_pure_sep] at k0
  obtain ⟨l0, k0⟩ := k0
  rw [sepConj_left_comm] at k0
  have g1 := sat_sep_mono k0 (memRegion_split (SP2 + BitVec.ofNat 64 48) 40 728 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 48 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 88 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g1
  have k1 := sat_sep_mono g1 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 48) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k1
  obtain ⟨B1, k1⟩ := k1
  rw [sepConj_assoc, sat_pure_sep] at k1
  obtain ⟨l1, k1⟩ := k1
  rw [sepConj_left_comm] at k1
  have g2 := sat_sep_mono k1 (memRegion_split (SP2 + BitVec.ofNat 64 88) 40 688 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 88 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 128 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g2
  have k2 := sat_sep_mono g2 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 88) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k2
  obtain ⟨B2, k2⟩ := k2
  rw [sepConj_assoc, sat_pure_sep] at k2
  obtain ⟨l2, k2⟩ := k2
  rw [sepConj_left_comm] at k2
  have g3 := sat_sep_mono k2 (memRegion_split (SP2 + BitVec.ofNat 64 128) 40 648 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 128 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 168 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g3
  have k3 := sat_sep_mono g3 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 128) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k3
  obtain ⟨B3, k3⟩ := k3
  rw [sepConj_assoc, sat_pure_sep] at k3
  obtain ⟨l3, k3⟩ := k3
  rw [sepConj_left_comm] at k3
  have g4 := sat_sep_mono k3 (memRegion_split (SP2 + BitVec.ofNat 64 168) 40 608 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 168 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 208 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g4
  have k4 := sat_sep_mono g4 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 168) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k4
  obtain ⟨B4, k4⟩ := k4
  rw [sepConj_assoc, sat_pure_sep] at k4
  obtain ⟨l4, k4⟩ := k4
  rw [sepConj_left_comm] at k4
  have g5 := sat_sep_mono k4 (memRegion_split (SP2 + BitVec.ofNat 64 208) 40 568 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 208 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 248 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g5
  have k5 := sat_sep_mono g5 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 208) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k5
  obtain ⟨B5, k5⟩ := k5
  rw [sepConj_assoc, sat_pure_sep] at k5
  obtain ⟨l5, k5⟩ := k5
  rw [sepConj_left_comm] at k5
  have g6 := sat_sep_mono k5 (memRegion_split (SP2 + BitVec.ofNat 64 248) 40 528 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 248 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 288 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g6
  have k6 := sat_sep_mono g6 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 248) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k6
  obtain ⟨B6, k6⟩ := k6
  rw [sepConj_assoc, sat_pure_sep] at k6
  obtain ⟨l6, k6⟩ := k6
  rw [sepConj_left_comm] at k6
  have g7 := sat_sep_mono k6 (memRegion_split (SP2 + BitVec.ofNat 64 288) 40 488 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 288 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 328 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g7
  have k7 := sat_sep_mono g7 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 288) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k7
  obtain ⟨B7, k7⟩ := k7
  rw [sepConj_assoc, sat_pure_sep] at k7
  obtain ⟨l7, k7⟩ := k7
  rw [sepConj_left_comm] at k7
  have g8 := sat_sep_mono k7 (memRegion_split (SP2 + BitVec.ofNat 64 328) 40 448 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 328 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 368 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g8
  have k8 := sat_sep_mono g8 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 328) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k8
  obtain ⟨B8, k8⟩ := k8
  rw [sepConj_assoc, sat_pure_sep] at k8
  obtain ⟨l8, k8⟩ := k8
  rw [sepConj_left_comm] at k8
  have g9 := sat_sep_mono k8 (memRegion_split (SP2 + BitVec.ofNat 64 368) 40 408 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 368 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 408 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g9
  have k9 := sat_sep_mono g9 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 368) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k9
  obtain ⟨B9, k9⟩ := k9
  rw [sepConj_assoc, sat_pure_sep] at k9
  obtain ⟨l9, k9⟩ := k9
  rw [sepConj_left_comm] at k9
  have g10 := sat_sep_mono k9 (memRegion_split (SP2 + BitVec.ofNat 64 408) 40 368 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 408 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 448 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g10
  have k10 := sat_sep_mono g10 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 408) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k10
  obtain ⟨B10, k10⟩ := k10
  rw [sepConj_assoc, sat_pure_sep] at k10
  obtain ⟨l10, k10⟩ := k10
  rw [sepConj_left_comm] at k10
  have g11 := sat_sep_mono k10 (memRegion_split (SP2 + BitVec.ofNat 64 448) 40 328 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 448 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 488 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g11
  have k11 := sat_sep_mono g11 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 448) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k11
  obtain ⟨B11, k11⟩ := k11
  rw [sepConj_assoc, sat_pure_sep] at k11
  obtain ⟨l11, k11⟩ := k11
  rw [sepConj_left_comm] at k11
  have g12 := sat_sep_mono k11 (memRegion_split (SP2 + BitVec.ofNat 64 488) 40 288 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 488 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 528 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g12
  have k12 := sat_sep_mono g12 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 488) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k12
  obtain ⟨B12, k12⟩ := k12
  rw [sepConj_assoc, sat_pure_sep] at k12
  obtain ⟨l12, k12⟩ := k12
  rw [sepConj_left_comm] at k12
  have g13 := sat_sep_mono k12 (memRegion_split (SP2 + BitVec.ofNat 64 528) 40 248 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 528 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 568 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g13
  have k13 := sat_sep_mono g13 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 528) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k13
  obtain ⟨B13, k13⟩ := k13
  rw [sepConj_assoc, sat_pure_sep] at k13
  obtain ⟨l13, k13⟩ := k13
  rw [sepConj_left_comm] at k13
  have g14 := sat_sep_mono k13 (memRegion_split (SP2 + BitVec.ofNat 64 568) 40 208 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 568 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 608 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g14
  have k14 := sat_sep_mono g14 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 568) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k14
  obtain ⟨B14, k14⟩ := k14
  rw [sepConj_assoc, sat_pure_sep] at k14
  obtain ⟨l14, k14⟩ := k14
  rw [sepConj_left_comm] at k14
  have g15 := sat_sep_mono k14 (memRegion_split (SP2 + BitVec.ofNat 64 608) 40 168 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 608 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 648 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g15
  have k15 := sat_sep_mono g15 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 608) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k15
  obtain ⟨B15, k15⟩ := k15
  rw [sepConj_assoc, sat_pure_sep] at k15
  obtain ⟨l15, k15⟩ := k15
  rw [sepConj_left_comm] at k15
  have g16 := sat_sep_mono k15 (memRegion_split (SP2 + BitVec.ofNat 64 648) 40 128 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 648 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 688 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g16
  have k16 := sat_sep_mono g16 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 648) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k16
  obtain ⟨B16, k16⟩ := k16
  rw [sepConj_assoc, sat_pure_sep] at k16
  obtain ⟨l16, k16⟩ := k16
  rw [sepConj_left_comm] at k16
  have g17 := sat_sep_mono k16 (memRegion_split (SP2 + BitVec.ofNat 64 688) 40 88 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 688 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 728 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g17
  have k17 := sat_sep_mono g17 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 688) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k17
  obtain ⟨B17, k17⟩ := k17
  rw [sepConj_assoc, sat_pure_sep] at k17
  obtain ⟨l17, k17⟩ := k17
  rw [sepConj_left_comm] at k17
  have g18 := sat_sep_mono k17 (memRegion_split (SP2 + BitVec.ofNat 64 728) 40 48 (by norm_num))
  rw [show SP2 + BitVec.ofNat 64 728 + BitVec.ofNat 64 40 = SP2 + BitVec.ofNat 64 768 by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], sepConj_assoc] at g18
  have k18 := sat_sep_mono g18 (memRegion_entails_bytes (SP2 + BitVec.ofNat 64 728) 40 (by norm_num))
  rw [sepExists_sepConj, sat_sepExists] at k18
  obtain ⟨B18, k18⟩ := k18
  rw [sepConj_assoc, sat_pure_sep] at k18
  obtain ⟨l18, k18⟩ := k18
  rw [sepConj_left_comm] at k18
  obtain ⟨u0, c0⟩ := sat_region_cell (n := 40) (by norm_num) k18
  rw [sepConj_left_comm] at c0
  rw [show SP2 + BitVec.ofNat 64 768 + 8#64 = SP2 + BitVec.ofNat 64 776 by
    rw [BitVec.add_assoc]; rfl] at c0
  obtain ⟨u1, c1⟩ := sat_region_cell (n := 32) (by norm_num) c0
  rw [sepConj_left_comm] at c1
  rw [show SP2 + BitVec.ofNat 64 776 + 8#64 = SP2 + BitVec.ofNat 64 784 by
    rw [BitVec.add_assoc]; rfl] at c1
  obtain ⟨u2, c2⟩ := sat_region_cell (n := 24) (by norm_num) c1
  rw [sepConj_left_comm] at c2
  rw [show SP2 + BitVec.ofNat 64 784 + 8#64 = SP2 + BitVec.ofNat 64 792 by
    rw [BitVec.add_assoc]; rfl] at c2
  obtain ⟨u3, c3⟩ := sat_region_cell (n := 16) (by norm_num) c2
  rw [sepConj_left_comm] at c3
  rw [show SP2 + BitVec.ofNat 64 792 + 8#64 = SP2 + BitVec.ofNat 64 800 by
    rw [BitVec.add_assoc]; rfl] at c3
  obtain ⟨u4, c4⟩ := sat_region_cell (n := 8) (by norm_num) c3
  rw [sepConj_left_comm] at c4
  rw [show SP2 + BitVec.ofNat 64 800 + 8#64 = SP2 + BitVec.ofNat 64 808 by
    rw [BitVec.add_assoc]; rfl] at c4
  have c5 := sat_sep_mono c4 (memRegion8_cell _)
  rw [sepExists_sepConj, sat_sepExists] at c5
  obtain ⟨u5, c5⟩ := c5
  refine ⟨B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, u0, u1, u2, u3, u4, u5, ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩, ?_⟩
  exact Satisfies.of_eq c5

end X25519Dalek.GP
end

section
/-! # Reordering separating conjunctions; pairs of 64-bit cells -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

open Arm64 Arm64.Obj

theorem pick2 (A1 A2 R : SepProp) : (A1 ∗ A2 ∗ R) = (A2 ∗ A1 ∗ R) := by ac_rfl
theorem pick3 (A1 A2 A3 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ R) = (A3 ∗ A1 ∗ A2 ∗ R) := by ac_rfl
theorem pick4 (A1 A2 A3 A4 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) = (A4 ∗ A1 ∗ A2 ∗ A3 ∗ R) := by ac_rfl
theorem pick5 (A1 A2 A3 A4 A5 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ R) = (A5 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) := by ac_rfl
theorem pick6 (A1 A2 A3 A4 A5 A6 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) = (A6 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ R) := by ac_rfl
theorem pick7 (A1 A2 A3 A4 A5 A6 A7 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) = (A7 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) := by ac_rfl
theorem pick8 (A1 A2 A3 A4 A5 A6 A7 A8 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ R) = (A8 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) := by ac_rfl
theorem pick9 (A1 A2 A3 A4 A5 A6 A7 A8 A9 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ R) = (A9 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ R) := by ac_rfl
theorem pick12 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ R) = (A12 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ R) := by ac_rfl
theorem pick13 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ R) = (A13 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ R) := by ac_rfl
theorem pick14 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ R) = (A14 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ R) := by ac_rfl
theorem pick15 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ R) = (A15 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ R) := by ac_rfl
theorem pick16 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ R) = (A16 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ R) := by ac_rfl
theorem pick17 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ R) = (A17 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ R) := by ac_rfl
theorem pick18 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ R) = (A18 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ R) := by ac_rfl
theorem pick19 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ R) = (A19 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ R) := by ac_rfl
theorem pick20 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ R) = (A20 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ R) := by ac_rfl
theorem pick21 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ R) = (A21 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ R) := by ac_rfl
theorem pick22 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ R) = (A22 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ R) := by ac_rfl
theorem pick23 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ R) = (A23 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ R) := by ac_rfl
theorem pick24 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ R) = (A24 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ R) := by ac_rfl
theorem pick25 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ R) = (A25 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ R) := by ac_rfl
theorem pick26 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ R) = (A26 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ R) := by ac_rfl
theorem pick27 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ A27 ∗ R) = (A27 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ R) := by ac_rfl
theorem pick28 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ A27 ∗ A28 ∗ R) = (A28 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ A27 ∗ R) := by ac_rfl
theorem pick29 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ A27 ∗ A28 ∗ A29 ∗ R) = (A29 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ A27 ∗ A28 ∗ R) := by ac_rfl
theorem pick30 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ A27 ∗ A28 ∗ A29 ∗ A30 ∗ R) = (A30 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ A27 ∗ A28 ∗ A29 ∗ R) := by ac_rfl
theorem pick32 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ A27 ∗ A28 ∗ A29 ∗ A30 ∗ A31 ∗ A32 ∗ R) = (A32 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗ A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 ∗ A22 ∗ A23 ∗ A24 ∗ A25 ∗ A26 ∗ A27 ∗ A28 ∗ A29 ∗ A30 ∗ A31 ∗ R) := by ac_rfl
theorem group3 (A B C F : SepProp) : (A ∗ B ∗ C ∗ F) = ((A ∗ B ∗ C) ∗ F) := by ac_rfl
theorem group4 (A B C D F : SepProp) : (A ∗ B ∗ C ∗ D ∗ F) = ((A ∗ B ∗ C ∗ D) ∗ F) := by ac_rfl

theorem pair_info {m : Memory} {a b v0 v1 : BitVec 64} {F : SepProp}
    (hs : m ⊨ (a ↦₆₄ v0) ∗ (b ↦₆₄ v1) ∗ F) :
    m.read64 a = v0 ∧ m.read64 b = v1 ∧ m.canWrite a 8 = true ∧ m.canWrite b 8 = true ∧
      m.canRead a 8 = true ∧ m.canRead b 8 = true := by
  have h1 := sat64_read hs
  rw [sepConj_left_comm] at hs
  have h2 := sat64_read hs
  exact ⟨h1.1, h2.1, h1.2.2, h2.2.2, h1.2.1, h2.2.1⟩

theorem pair_wr {m : Memory} {a b v0 v1 : BitVec 64} {F : SepProp}
    (hs : m ⊨ (a ↦₆₄ v0) ∗ (b ↦₆₄ v1) ∗ F) (w0 w1 : BitVec 64) :
    ((m.write64 a w0).write64 b w1 ⊨ (a ↦₆₄ w0) ∗ (b ↦₆₄ w1) ∗ F) ∧
      m.KeepsFrozen ((m.write64 a w0).write64 b w1) := by
  have i := pair_info hs
  have h1 := sat64_write hs w0
  rw [sepConj_left_comm] at h1
  have i2 := sat64_read h1
  have h2 := sat64_write h1 w1
  rw [sepConj_left_comm] at h2
  exact ⟨h2, (Memory.keepsFrozen_write64 i.2.2.1 w0).trans (Memory.keepsFrozen_write64 i2.2.2 w1)⟩

theorem cell_wr {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F) (w : BitVec 64) :
    (m.write64 a w ⊨ (a ↦₆₄ w) ∗ F) ∧ m.KeepsFrozen (m.write64 a w) :=
  ⟨sat64_write hs w, Memory.keepsFrozen_write64 (sat64_read hs).2.2 w⟩

theorem lb_mono {bs : List (BitVec 8)} (h : fe51LimbsBounded bs (2 ^ 52)) :
    fe51LimbsBounded bs (2 ^ 54) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨h0, by omega, by omega, by omega, by omega, by omega⟩

theorem lb_len {bs : List (BitVec 8)} {b : Nat} (h : fe51LimbsBounded bs b) : bs.length = 40 := h.1

end X25519Dalek.GP
end

section
/-! # `pow22501`: values, the reassembled stack frame, 40-byte buffers as cells

`modPowLoop_eq` is copied from DeepMind's `Shared51/SliceBase.lean` (google-deepmind/code-verification
@ 8c8d371f, Apache-2.0). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

open Arm64 Arm64.Obj

theorem modPowLoop_eq' (fuel : Nat) :
    ∀ (base exp m acc : Nat), exp < 2 ^ fuel → modPowLoop fuel base exp m acc = (acc * base ^ exp) % m := by
  induction fuel with
  | zero => intro base exp m acc hexp; (have h0 : exp = 0 := by omega); subst h0; simp [modPowLoop]
  | succ fuel ih =>
    intro base exp m acc hexp; unfold modPowLoop
    by_cases h0 : exp = 0
    · subst h0; simp
    · have hne : (exp == 0) = false := beq_false_of_ne h0
      have hdiv : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hexp; omega
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hsq : ((base * base) % m) ^ (exp / 2) % m = base ^ (2 * (exp / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rcases Nat.mod_two_eq_zero_or_one exp with heven | hodd
      · have hmod : (exp % 2 == 1) = false := by rw [heven]; rfl
        rw [hmod]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod, hsq, show 2 * (exp / 2) = exp by omega, ← Nat.mul_mod]
      · have hmod : (exp % 2 == 1) = true := by rw [hodd]; rfl
        rw [hmod]; simp only [↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod ((acc * base) % m), Nat.mod_mod, hsq, ← Nat.mul_mod,
            Nat.mul_assoc acc, ← Nat.pow_succ', show (2 * (exp / 2)).succ = exp by omega]

theorem fpPow_mod' (a e : Nat) (he : e < 2 ^ 256) : fpPow (a % p25519) e = a ^ e % p25519 := by
  unfold fpPow modPow
  rw [Nat.mod_mod, modPowLoop_eq' 256 (a % p25519) e p25519 1 he, Nat.one_mul, ← Nat.pow_mod a e p25519]

theorem vp {x y va e k : Nat} (h : x % p25519 = fpPow (y % p25519) (2 ^ k))
    (hy : y % p25519 = va ^ e % p25519) (hk : k < 256) : x % p25519 = va ^ (e * 2 ^ k) % p25519 := by
  rw [h, fpPow_mod' y _ (Nat.pow_lt_pow_right (by norm_num) hk), Nat.pow_mod, hy, ← Nat.pow_mod,
    ← pow_mul]

theorem vm {x y z va e1 e2 : Nat} (h : x % p25519 = y * z % p25519) (hy : y % p25519 = va ^ e1 % p25519)
    (hz : z % p25519 = va ^ e2 % p25519) : x % p25519 = va ^ (e1 + e2) % p25519 := by
  rw [h, Nat.mul_mod, hy, hz, ← Nat.mul_mod, ← pow_add]

theorem chunk_take32 (bs : List (BitVec 8)) (k : Nat) (hk : k < 4) : chunk (bs.take 32) k = chunk bs k := by
  unfold chunk
  congr 1
  rw [List.drop_take, List.take_take]
  congr 1; omega

theorem bytes40_cells (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 40) :
    (a ↦ₛ bs) = cellsFrom a [chunk bs 0, chunk bs 1, chunk bs 2, chunk bs 3] ∗
      ((a + BitVec.ofNat 64 32) ↦₆₄ chunk bs 4) := by
  rw [pointsToBytes_split a bs 32 (by omega), bytes32_eq_cellsFrom a (bs.take 32) (by simp [h]),
    bytes8_cell _ (bs.drop 32) (by simp [h]), chunk_take32 bs 0 (by omega), chunk_take32 bs 1 (by omega),
    chunk_take32 bs 2 (by omega), chunk_take32 bs 3 (by omega)]
  congr 2
  unfold chunk
  rw [List.take_of_length_le (by simp [h])]

theorem stack_unlayout {SP2 : BitVec 64} {B0 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16 B17 B18 : List (BitVec 8)} {u0 u1 u2 u3 u4 u5 : BitVec 64}
    (h0 : B0.length = 40) (h1 : B1.length = 40) (h2 : B2.length = 40) (h3 : B3.length = 40) (h4 : B4.length = 40) (h5 : B5.length = 40) (h6 : B6.length = 40) (h7 : B7.length = 40) (h8 : B8.length = 40) (h9 : B9.length = 40) (h10 : B10.length = 40) (h11 : B11.length = 40) (h12 : B12.length = 40) (h13 : B13.length = 40) (h14 : B14.length = 40) (h15 : B15.length = 40) (h16 : B16.length = 40) (h17 : B17.length = 40) (h18 : B18.length = 40) :
    (memRegion (SP2 - BitVec.ofNat 64 224) 224 ∗ memRegion SP2 8 ∗
        ((SP2 + BitVec.ofNat 64 8) ↦ₛ B0) ∗
        ((SP2 + BitVec.ofNat 64 48) ↦ₛ B1) ∗
        ((SP2 + BitVec.ofNat 64 88) ↦ₛ B2) ∗
        ((SP2 + BitVec.ofNat 64 128) ↦ₛ B3) ∗
        ((SP2 + BitVec.ofNat 64 168) ↦ₛ B4) ∗
        ((SP2 + BitVec.ofNat 64 208) ↦ₛ B5) ∗
        ((SP2 + BitVec.ofNat 64 248) ↦ₛ B6) ∗
        ((SP2 + BitVec.ofNat 64 288) ↦ₛ B7) ∗
        ((SP2 + BitVec.ofNat 64 328) ↦ₛ B8) ∗
        ((SP2 + BitVec.ofNat 64 368) ↦ₛ B9) ∗
        ((SP2 + BitVec.ofNat 64 408) ↦ₛ B10) ∗
        ((SP2 + BitVec.ofNat 64 448) ↦ₛ B11) ∗
        ((SP2 + BitVec.ofNat 64 488) ↦ₛ B12) ∗
        ((SP2 + BitVec.ofNat 64 528) ↦ₛ B13) ∗
        ((SP2 + BitVec.ofNat 64 568) ↦ₛ B14) ∗
        ((SP2 + BitVec.ofNat 64 608) ↦ₛ B15) ∗
        ((SP2 + BitVec.ofNat 64 648) ↦ₛ B16) ∗
        ((SP2 + BitVec.ofNat 64 688) ↦ₛ B17) ∗
        ((SP2 + BitVec.ofNat 64 728) ↦ₛ B18) ∗
        ((SP2 + BitVec.ofNat 64 768) ↦₆₄ u0) ∗ ((SP2 + BitVec.ofNat 64 776) ↦₆₄ u1) ∗ ((SP2 + BitVec.ofNat 64 784) ↦₆₄ u2) ∗ ((SP2 + BitVec.ofNat 64 792) ↦₆₄ u3) ∗ ((SP2 + BitVec.ofNat 64 800) ↦₆₄ u4) ∗ ((SP2 + BitVec.ofNat 64 808) ↦₆₄ u5)) ⊢ memRegion (SP2 - BitVec.ofNat 64 224) (224 + 816) := by
  have c5 := cell_memRegion8 (SP2 + BitVec.ofNat 64 808) u5
  have m5 : ((SP2 + BitVec.ofNat 64 800) ↦₆₄ u4) ∗ ((SP2 + BitVec.ofNat 64 808) ↦₆₄ u5) ⊢
      memRegion (SP2 + BitVec.ofNat 64 800) 16 :=
    Entails.trans (sepConj_mono (cell_memRegion8 _ u4) (cell_memRegion8 _ u5))
      (memRegion_merge _ _ 8 8 (by rw [BitVec.add_assoc]; rfl) (by norm_num) (by norm_num))
  have m3 : ((SP2 + BitVec.ofNat 64 792) ↦₆₄ u3) ∗ memRegion (SP2 + BitVec.ofNat 64 800) 16 ⊢
      memRegion (SP2 + BitVec.ofNat 64 792) 24 :=
    Entails.trans (sepConj_mono (cell_memRegion8 _ u3) (Entails.refl _))
      (memRegion_merge _ _ 8 16 (by rw [BitVec.add_assoc]; rfl) (by norm_num) (by norm_num))
  have m2 : ((SP2 + BitVec.ofNat 64 784) ↦₆₄ u2) ∗ memRegion (SP2 + BitVec.ofNat 64 792) 24 ⊢
      memRegion (SP2 + BitVec.ofNat 64 784) 32 :=
    Entails.trans (sepConj_mono (cell_memRegion8 _ u2) (Entails.refl _))
      (memRegion_merge _ _ 8 24 (by rw [BitVec.add_assoc]; rfl) (by norm_num) (by norm_num))
  have m1 : ((SP2 + BitVec.ofNat 64 776) ↦₆₄ u1) ∗ memRegion (SP2 + BitVec.ofNat 64 784) 32 ⊢
      memRegion (SP2 + BitVec.ofNat 64 776) 40 :=
    Entails.trans (sepConj_mono (cell_memRegion8 _ u1) (Entails.refl _))
      (memRegion_merge _ _ 8 32 (by rw [BitVec.add_assoc]; rfl) (by norm_num) (by norm_num))
  have m0 : ((SP2 + BitVec.ofNat 64 768) ↦₆₄ u0) ∗ memRegion (SP2 + BitVec.ofNat 64 776) 40 ⊢
      memRegion (SP2 + BitVec.ofNat 64 768) 48 :=
    Entails.trans (sepConj_mono (cell_memRegion8 _ u0) (Entails.refl _))
      (memRegion_merge _ _ 8 40 (by rw [BitVec.add_assoc]; rfl) (by norm_num) (by norm_num))
  have mc : (((SP2 + BitVec.ofNat 64 768) ↦₆₄ u0) ∗ ((SP2 + BitVec.ofNat 64 776) ↦₆₄ u1) ∗
      ((SP2 + BitVec.ofNat 64 784) ↦₆₄ u2) ∗ ((SP2 + BitVec.ofNat 64 792) ↦₆₄ u3) ∗
      ((SP2 + BitVec.ofNat 64 800) ↦₆₄ u4) ∗ ((SP2 + BitVec.ofNat 64 808) ↦₆₄ u5)) ⊢
      memRegion (SP2 + BitVec.ofNat 64 768) 48 :=
    Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) m5)))) (Entails.trans (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) m3))) (Entails.trans
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) m2)) (Entails.trans
      (sepConj_mono (Entails.refl _) m1) m0)))
  have s18 : ((SP2 + BitVec.ofNat 64 728) ↦ₛ B18) ∗ memRegion (SP2 + BitVec.ofNat 64 768) 48 ⊢
      memRegion (SP2 + BitVec.ofNat 64 728) 88 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 728) B18
    rw [h18] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 48 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s17 : ((SP2 + BitVec.ofNat 64 688) ↦ₛ B17) ∗ memRegion (SP2 + BitVec.ofNat 64 728) 88 ⊢
      memRegion (SP2 + BitVec.ofNat 64 688) 128 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 688) B17
    rw [h17] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 88 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s16 : ((SP2 + BitVec.ofNat 64 648) ↦ₛ B16) ∗ memRegion (SP2 + BitVec.ofNat 64 688) 128 ⊢
      memRegion (SP2 + BitVec.ofNat 64 648) 168 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 648) B16
    rw [h16] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 128 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s15 : ((SP2 + BitVec.ofNat 64 608) ↦ₛ B15) ∗ memRegion (SP2 + BitVec.ofNat 64 648) 168 ⊢
      memRegion (SP2 + BitVec.ofNat 64 608) 208 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 608) B15
    rw [h15] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 168 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s14 : ((SP2 + BitVec.ofNat 64 568) ↦ₛ B14) ∗ memRegion (SP2 + BitVec.ofNat 64 608) 208 ⊢
      memRegion (SP2 + BitVec.ofNat 64 568) 248 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 568) B14
    rw [h14] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 208 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s13 : ((SP2 + BitVec.ofNat 64 528) ↦ₛ B13) ∗ memRegion (SP2 + BitVec.ofNat 64 568) 248 ⊢
      memRegion (SP2 + BitVec.ofNat 64 528) 288 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 528) B13
    rw [h13] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 248 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s12 : ((SP2 + BitVec.ofNat 64 488) ↦ₛ B12) ∗ memRegion (SP2 + BitVec.ofNat 64 528) 288 ⊢
      memRegion (SP2 + BitVec.ofNat 64 488) 328 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 488) B12
    rw [h12] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 288 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s11 : ((SP2 + BitVec.ofNat 64 448) ↦ₛ B11) ∗ memRegion (SP2 + BitVec.ofNat 64 488) 328 ⊢
      memRegion (SP2 + BitVec.ofNat 64 448) 368 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 448) B11
    rw [h11] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 328 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s10 : ((SP2 + BitVec.ofNat 64 408) ↦ₛ B10) ∗ memRegion (SP2 + BitVec.ofNat 64 448) 368 ⊢
      memRegion (SP2 + BitVec.ofNat 64 408) 408 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 408) B10
    rw [h10] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 368 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s9 : ((SP2 + BitVec.ofNat 64 368) ↦ₛ B9) ∗ memRegion (SP2 + BitVec.ofNat 64 408) 408 ⊢
      memRegion (SP2 + BitVec.ofNat 64 368) 448 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 368) B9
    rw [h9] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 408 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s8 : ((SP2 + BitVec.ofNat 64 328) ↦ₛ B8) ∗ memRegion (SP2 + BitVec.ofNat 64 368) 448 ⊢
      memRegion (SP2 + BitVec.ofNat 64 328) 488 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 328) B8
    rw [h8] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 448 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s7 : ((SP2 + BitVec.ofNat 64 288) ↦ₛ B7) ∗ memRegion (SP2 + BitVec.ofNat 64 328) 488 ⊢
      memRegion (SP2 + BitVec.ofNat 64 288) 528 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 288) B7
    rw [h7] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 488 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s6 : ((SP2 + BitVec.ofNat 64 248) ↦ₛ B6) ∗ memRegion (SP2 + BitVec.ofNat 64 288) 528 ⊢
      memRegion (SP2 + BitVec.ofNat 64 248) 568 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 248) B6
    rw [h6] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 528 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s5 : ((SP2 + BitVec.ofNat 64 208) ↦ₛ B5) ∗ memRegion (SP2 + BitVec.ofNat 64 248) 568 ⊢
      memRegion (SP2 + BitVec.ofNat 64 208) 608 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 208) B5
    rw [h5] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 568 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s4 : ((SP2 + BitVec.ofNat 64 168) ↦ₛ B4) ∗ memRegion (SP2 + BitVec.ofNat 64 208) 608 ⊢
      memRegion (SP2 + BitVec.ofNat 64 168) 648 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 168) B4
    rw [h4] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 608 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s3 : ((SP2 + BitVec.ofNat 64 128) ↦ₛ B3) ∗ memRegion (SP2 + BitVec.ofNat 64 168) 648 ⊢
      memRegion (SP2 + BitVec.ofNat 64 128) 688 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 128) B3
    rw [h3] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 648 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s2 : ((SP2 + BitVec.ofNat 64 88) ↦ₛ B2) ∗ memRegion (SP2 + BitVec.ofNat 64 128) 688 ⊢
      memRegion (SP2 + BitVec.ofNat 64 88) 728 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 88) B2
    rw [h2] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 688 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s1 : ((SP2 + BitVec.ofNat 64 48) ↦ₛ B1) ∗ memRegion (SP2 + BitVec.ofNat 64 88) 728 ⊢
      memRegion (SP2 + BitVec.ofNat 64 48) 768 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 48) B1
    rw [h1] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 728 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have s0 : ((SP2 + BitVec.ofNat 64 8) ↦ₛ B0) ∗ memRegion (SP2 + BitVec.ofNat 64 48) 768 ⊢
      memRegion (SP2 + BitVec.ofNat 64 8) 808 := by
    have := bytes_entails_memRegion (SP2 + BitVec.ofNat 64 8) B0
    rw [h0] at this
    exact Entails.trans (sepConj_mono this (Entails.refl _))
      (memRegion_merge _ _ 40 768 (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by norm_num) (by norm_num))
  have mg : memRegion SP2 8 ∗ memRegion (SP2 + BitVec.ofNat 64 8) 808 ⊢ memRegion SP2 816 :=
    memRegion_merge _ _ 8 808 rfl (by norm_num) (by norm_num)
  have ms : memRegion (SP2 - BitVec.ofNat 64 224) 224 ∗ memRegion SP2 816 ⊢
      memRegion (SP2 - BitVec.ofNat 64 224) (224 + 816) :=
    memRegion_merge _ _ 224 816 (by bv_omega) (by norm_num) (by norm_num)
  refine Entails.trans (sepConj_mono (Entails.refl _) ?_) ms
  refine Entails.trans (sepConj_mono (Entails.refl _) ?_) mg
  exact (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) (Entails.trans (sepConj_mono (Entails.refl _) mc) s18)) s17)) s16)) s15)) s14)) s13)) s12)) s11)) s10)) s9)) s8)) s7)) s6)) s5)) s4)) s3)) s2)) s1)) s0)

theorem bytes40_cells' (a b : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 40)
    (hb : a + BitVec.ofNat 64 32 = b) :
    (a ↦ₛ bs) = cellsFrom a [chunk bs 0, chunk bs 1, chunk bs 2, chunk bs 3] ∗ (b ↦₆₄ chunk bs 4) := by
  rw [← hb]; exact bytes40_cells a bs h

theorem ne21 {k : BitVec 5} (h1 : 21 ≤ k.toNat) (h2 : k.toNat < 28) (i : BitVec 5)
    (hi : i.toNat < 21 ∨ 28 ≤ i.toNat := by decide) : k ≠ i := by
  intro e; subst e; omega

theorem ent_pure_right {P : SepProp} {φ : Prop} (h : φ) : P ⊢ (P ∗ ⌜φ⌝) := by
  intro k hk
  refine SepProp.holds_sepConj_iff.mpr ⟨k, Heap.empty, Heap.disjoint_empty_right k, (Heap.union_empty_right k).symm,
    hk, rfl, h⟩

theorem ent_ex2 {α β : Type} {P : α → β → SepProp} (x : α) (y : β) : P x y ⊢ ∃∗ a, ∃∗ b, P a b := by
  intro k hk
  exact ⟨x, ⟨y, hk⟩⟩

end X25519Dalek.GP
end

section
/-! # `FieldElement51::pow22501` (block 5): the contract -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.GP

open Arm64 Arm64.Obj

set_option maxHeartbeats 16000000 in
theorem p22_ok (hM : fnOk mulName (fun _ => fe51MulSpec)) (hK : fnOk p2kName (fun _ => fe51Pow2kSpec)) :
    fnOk p22Name (fun _ => fe51Pow22501Spec) := by
  refine ⟨5, 0, p22_lookup, fun mpl hP => ?_⟩
  rintro ⟨out, a, out_bs, a_bs⟩ R s0 hpc hrun hpre hal hCLp
  have hfa : x25519CliMultiLib.fnAddr mpl p22Name = mpl.base 5 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, p22_lookup]
  rw [hfa] at hpc
  change s0.mem ⊨ ((⌜s0.readReg64 Reg.x0 = out ∧ s0.readReg64 Reg.x1 = a ∧ out_bs.length = 80 ∧
      fe51LimbsBounded a_bs (2 ^ 54)⌝ ∗ (a ↦ₛ a_bs) ∗ (out ↦ₛ out_bs) ∗ stackFrame s0 1040) ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) ∗ R at hpre
  have h1 := Satisfies.of_eq hpre
    (Q := ⌜s0.readReg64 Reg.x0 = out ∧ s0.readReg64 Reg.x1 = a ∧ out_bs.length = 80 ∧
        fe51LimbsBounded a_bs (2 ^ 54)⌝ ∗ ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗
      stackFrame s0 1040 ∗ ((a ↦ₛ a_bs) ∗ (out ↦ₛ out_bs) ∗ R))
  rw [sat_pure_sep, sat_pure_sep] at h1
  obtain ⟨⟨hx0, hx1, hlo, hba⟩, hCL, h1⟩ := h1
  clear hpre
  set SP2 := s0.sp - BitVec.ofNat 64 816 with hSP2
  have hst : stackFrame s0 1040 = memRegion (SP2 - BitVec.ofNat 64 224) (224 + 816) := by
    show memRegion _ _ = _
    rw [show s0.sp - BitVec.ofNat 64 1040 = SP2 - BitVec.ofNat 64 224 by rw [hSP2]; bv_omega]
  rw [hst] at h1
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, u0, u1, u2, u3, u4, u5, hlens, h2⟩ := stack_layout h1
  clear h1
  obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12, hl13, hl14, hl15, hl16, hl17, hl18⟩ := hlens
  rw [pointsToBytes_split out out_bs 40 (by omega)] at h2
  have hal0 : s0.sp &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
  have halSP2 : SP2 &&& 0b1111#64 = 0#64 := al16_sub _ 816 (by norm_num) (by norm_num) hal0
  have hSP1 : s0.sp + 0xffffffffffffffd0#64 = SP2 + BitVec.ofNat 64 768 := by rw [hSP2]; bv_omega
  have halSP1 : (s0.sp + 0xffffffffffffffd0#64) &&& 0b1111#64 = 0#64 := by
    rw [show s0.sp + 0xffffffffffffffd0#64 = s0.sp - BitVec.ofNat 64 48 by bv_omega]
    exact al16_sub _ 48 (by norm_num) (by norm_num) hal0
  show Reach (bprog mpl 5) s0 _
  refine reach_congr (s' := mkS s0 (mpl.base 5 + BitVec.ofNat 64 0) s0.regs.regs s0.sp s0.pstate
    s0.mem s0.vregs.regs) (by rw [← hpc]; rfl) ?_
  -- 0: stp x29, x30, [sp, #-48]!
  have p0 := Satisfies.of_eq h2 (Q := ((SP2 + BitVec.ofNat 64 768) ↦₆₄ u0) ∗
    (((SP2 + BitVec.ofNat 64 776) ↦₆₄ u1) ∗ ((SP2 + BitVec.ofNat 64 784) ↦₆₄ u2) ∗
      ((SP2 + BitVec.ofNat 64 792) ↦₆₄ u3) ∗ ((SP2 + BitVec.ofNat 64 800) ↦₆₄ u4) ∗
      ((SP2 + BitVec.ofNat 64 808) ↦₆₄ u5) ∗ memRegion (SP2 - BitVec.ofNat 64 224) 224 ∗
      memRegion SP2 8 ∗
        ((SP2 + BitVec.ofNat 64 8) ↦ₛ B0) ∗
        ((SP2 + BitVec.ofNat 64 48) ↦ₛ B1) ∗
        ((SP2 + BitVec.ofNat 64 88) ↦ₛ B2) ∗
        ((SP2 + BitVec.ofNat 64 128) ↦ₛ B3) ∗
        ((SP2 + BitVec.ofNat 64 168) ↦ₛ B4) ∗
        ((SP2 + BitVec.ofNat 64 208) ↦ₛ B5) ∗
        ((SP2 + BitVec.ofNat 64 248) ↦ₛ B6) ∗
        ((SP2 + BitVec.ofNat 64 288) ↦ₛ B7) ∗
        ((SP2 + BitVec.ofNat 64 328) ↦ₛ B8) ∗
        ((SP2 + BitVec.ofNat 64 368) ↦ₛ B9) ∗
        ((SP2 + BitVec.ofNat 64 408) ↦ₛ B10) ∗
        ((SP2 + BitVec.ofNat 64 448) ↦ₛ B11) ∗
        ((SP2 + BitVec.ofNat 64 488) ↦ₛ B12) ∗
        ((SP2 + BitVec.ofNat 64 528) ↦ₛ B13) ∗
        ((SP2 + BitVec.ofNat 64 568) ↦ₛ B14) ∗
        ((SP2 + BitVec.ofNat 64 608) ↦ₛ B15) ∗
        ((SP2 + BitVec.ofNat 64 648) ↦ₛ B16) ∗
        ((SP2 + BitVec.ofNat 64 688) ↦ₛ B17) ∗
        ((SP2 + BitVec.ofNat 64 728) ↦ₛ B18) ∗
      (a ↦ₛ a_bs) ∗ (out ↦ₛ out_bs.take 40) ∗ ((out + BitVec.ofNat 64 40) ↦ₛ out_bs.drop 40) ∗ R))
  -- 0: stp x29, x30, [sp, #-48]!
  have i0 := pair_info p0
  refine Reach.mk hrun (f05_0 hP hCL (Memory.KeepsFrozen.refl _)) ?_
  have e776 : SP2 + BitVec.ofNat 64 768 + 8#64 = SP2 + BitVec.ofNat 64 776 := by
    rw [BitVec.add_assoc]; rfl
  rw [ex_stp64_pre_sp _ _ (by decide) (by decide) _ hal0 (by rw [hSP1]; exact i0.2.2.1)
    (by rw [hSP1, e776]; exact i0.2.2.2.1), pc_add, hSP1, e776]
  obtain ⟨p1, k1⟩ := pair_wr p0 (s0.regs.regs 29#5) (s0.regs.regs 30#5)
  have halSP1' : (SP2 + BitVec.ofNat 64 768) &&& 0b1111#64 = 0#64 := by rw [← hSP1]; exact halSP1
  -- 4: str x28, [sp, #16]
  have e784 : SP2 + BitVec.ofNat 64 768 + 16#64 = SP2 + BitVec.ofNat 64 784 := by
    rw [BitVec.add_assoc]; rfl
  rw [pick3] at p1
  refine Reach.mk hrun (f05_4 hP hCL k1) ?_
  rw [ex_str64_sp _ (by decide) _ halSP1' (by rw [e784]; exact (sat64_read p1).2.2), pc_add, e784]
  obtain ⟨p2, k2'⟩ := cell_wr p1 (s0.regs.regs 28#5)
  have k2 := k1.trans k2'
  -- 8: stp x20, x19, [sp, #32]
  have e800 : SP2 + BitVec.ofNat 64 768 + 32#64 = SP2 + BitVec.ofNat 64 800 := by
    rw [BitVec.add_assoc]; rfl
  have e808 : SP2 + BitVec.ofNat 64 800 + 8#64 = SP2 + BitVec.ofNat 64 808 := by
    rw [BitVec.add_assoc]; rfl
  rw [pick6, pick6] at p2
  have i8 := pair_info p2
  refine Reach.mk hrun (f05_8 hP hCL k2) ?_
  rw [ex_stp64_sp _ _ (by decide) (by decide) _ halSP1' (by rw [e800]; exact i8.2.2.1)
    (by rw [e800, e808]; exact i8.2.2.2.1), pc_add, e800, e808]
  obtain ⟨p3, k3'⟩ := pair_wr p2 (s0.regs.regs 20#5) (s0.regs.regs 19#5)
  have k3 := k2.trans k3'
  -- 12: add x29, sp, #0
  refine Reach.mk hrun (f05_12 hP hCL k3) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  -- 16: sub sp, sp, #768
  refine Reach.mk hrun (f05_16 hP hCL k3) ?_
  rw [ex_sub_sp, pc_add, show SP2 + BitVec.ofNat 64 768 - BitVec.zeroExtend 64 (0x300#12) = SP2 by
    rw [show BitVec.zeroExtend 64 (0x300#12 : BitVec 12) = BitVec.ofNat 64 768 from rfl]; bv_omega]
  -- 20: mov x20, x1
  refine Reach.mk hrun (f05_20 hP hCL k3) ?_
  rw [ex_mov _ _ (by decide) (by decide), pc_add]
  -- 24: mov x19, x0
  refine Reach.mk hrun (f05_24 hP hCL k3) ?_
  rw [ex_mov _ _ (by decide) (by decide), pc_add]
  have hx0' : s0.regs.regs 0#5 = out := by simpa [readGpr_unfold] using hx0
  have hx1' : s0.regs.regs 1#5 = a := by simpa [readGpr_unfold] using hx1
  have hlo40 : (out_bs.take 40).length = 40 := by simp [hlo]
  refine Reach.mk hrun (f05_28 hP hCL k3) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun (f05_32 hP hCL k3) ?_
  rw [ex_mov _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun (f05_36 hP hCL k3) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick7] at p3
  rw [pick9] at p3
  rw [pick28] at p3
  rw [group3] at p3
  have vA : fe51ValOfBytes a_bs % p25519 = fe51ValOfBytes a_bs ^ 1 % p25519 := by rw [pow_one]
  refine call_p2k hP hK hCL hrun k3 (f05_40 hP hCL k3) halSP2
    (by simp [upd_apply, hx0', hx1'] <;> (clear * -; bv_omega)) (by simp [upd_apply, hx0', hx1'] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) p3 hba hl0 ?_
  intro sf1 res1 hrun1 hpc1 hsp1 hk1 hv1 kf1 hm1 hb1 hval1
  refine reach_congr (s' := mkS sf1 (mpl.base 5 + BitVec.ofNat 64 44) sf1.regs.regs SP2 sf1.pstate
    sf1.mem sf1.vregs.regs) (by rw [← hpc1, ← hsp1]; rfl) ?_
  rw [← group3] at hm1
  have g19_1 : sf1.regs.regs 19#5 = out :=
    (hk1 19#5 (by decide) (by decide)).trans (by simp [upd_apply, hx0', hx1'])
  have g20_1 : sf1.regs.regs 20#5 = a :=
    (hk1 20#5 (by decide) (by decide)).trans (by simp [upd_apply, hx0', hx1'])
  have g29_1 : sf1.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk1 29#5 (by decide) (by decide)).trans (by simp [upd_apply, hx0', hx1'])
  have kp1 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf1.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk1 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5), upd_ne _ _ (ne21 h1 h2 19#5), upd_ne _ _ (ne21 h1 h2 20#5), upd_ne _ _ (ne21 h1 h2 29#5)]; try rfl)
  have vk1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := hv1
  have vc1 := vp hval1 vA (by norm_num)
  clear p3 hk1 hv1 hpc1 hsp1 hval1
  refine Reach.mk hrun1 (f05_44 hP hCL kf1) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun1 (f05_48 hP hCL kf1) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun1 (f05_52 hP hCL kf1) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick3] at hm1
  rw [pick28] at hm1
  rw [pick4] at hm1
  rw [group3] at hm1
  refine call_p2k hP hK hCL hrun1 kf1 (f05_56 hP hCL kf1) halSP2
    (by simp [upd_apply, g19_1, g20_1, g29_1] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_1, g20_1, g29_1] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm1 (lb_mono hb1) hl18 ?_
  intro sf2 res2 hrun2 hpc2 hsp2 hk2 hv2 kf2 hm2 hb2 hval2
  refine reach_congr (s' := mkS sf2 (mpl.base 5 + BitVec.ofNat 64 60) sf2.regs.regs SP2 sf2.pstate
    sf2.mem sf2.vregs.regs) (by rw [← hpc2, ← hsp2]; rfl) ?_
  rw [← group3] at hm2
  have g19_2 : sf2.regs.regs 19#5 = out :=
    (hk2 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_1, g20_1, g29_1])
  have g20_2 : sf2.regs.regs 20#5 = a :=
    (hk2 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_1, g20_1, g29_1])
  have g29_2 : sf2.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk2 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_1, g20_1, g29_1])
  have kp2 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf2.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk2 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp1 k h1 h2)
  have vk2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := hv2.trans vk1
  have vc2 := vp hval2 vc1 (by norm_num)
  clear hm1 hk2 hv2 hpc2 hsp2 hval2 g19_1 g20_1 g29_1 kp1 vk1 kf1 hrun1
  refine Reach.mk hrun2 (f05_60 hP hCL kf2) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun2 (f05_64 hP hCL kf2) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun2 (f05_68 hP hCL kf2) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick3] at hm2
  rw [pick12] at hm2
  rw [pick4] at hm2
  rw [group3] at hm2
  refine call_p2k hP hK hCL hrun2 kf2 (f05_72 hP hCL kf2) halSP2
    (by simp [upd_apply, g19_2, g20_2, g29_2] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_2, g20_2, g29_2] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm2 (lb_mono hb2) hl1 ?_
  intro sf3 res3 hrun3 hpc3 hsp3 hk3 hv3 kf3 hm3 hb3 hval3
  refine reach_congr (s' := mkS sf3 (mpl.base 5 + BitVec.ofNat 64 76) sf3.regs.regs SP2 sf3.pstate
    sf3.mem sf3.vregs.regs) (by rw [← hpc3, ← hsp3]; rfl) ?_
  rw [← group3] at hm3
  have g19_3 : sf3.regs.regs 19#5 = out :=
    (hk3 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_2, g20_2, g29_2])
  have g20_3 : sf3.regs.regs 20#5 = a :=
    (hk3 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_2, g20_2, g29_2])
  have g29_3 : sf3.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk3 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_2, g20_2, g29_2])
  have kp3 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf3.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk3 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp2 k h1 h2)
  have vk3 : calleeSavedVRegs sf3 = calleeSavedVRegs s0 := hv3.trans vk2
  have vc3 := vp hval3 vc2 (by norm_num)
  clear hm2 hk3 hv3 hpc3 hsp3 hval3 g19_2 g20_2 g29_2 kp2 vk2 kf2 hrun2
  refine Reach.mk hrun3 (f05_76 hP hCL kf3) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun3 (f05_80 hP hCL kf3) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun3 (f05_84 hP hCL kf3) ?_
  rw [ex_mov _ _ (by decide) (by decide), pc_add]
  rw [pick3] at hm3
  rw [pick13] at hm3
  rw [pick4] at hm3
  rw [pick6] at hm3
  rw [group4] at hm3
  refine call_mul hP hM hCL hrun3 kf3 (f05_88 hP hCL kf3) halSP2
    (by simp [upd_apply, g19_3, g20_3, g29_3] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_3, g20_3, g29_3] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_3, g20_3, g29_3] <;> (clear * -; bv_omega)) hm3 hba (lb_mono hb3) hl2 ?_
  intro sf4 res4 hrun4 hpc4 hsp4 hk4 hv4 kf4 hm4 hb4 hval4
  refine reach_congr (s' := mkS sf4 (mpl.base 5 + BitVec.ofNat 64 92) sf4.regs.regs SP2 sf4.pstate
    sf4.mem sf4.vregs.regs) (by rw [← hpc4, ← hsp4]; rfl) ?_
  rw [← group4] at hm4
  have g19_4 : sf4.regs.regs 19#5 = out :=
    (hk4 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_3, g20_3, g29_3])
  have g20_4 : sf4.regs.regs 20#5 = a :=
    (hk4 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_3, g20_3, g29_3])
  have g29_4 : sf4.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk4 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_3, g20_3, g29_3])
  have kp4 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf4.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk4 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp3 k h1 h2)
  have vk4 : calleeSavedVRegs sf4 = calleeSavedVRegs s0 := hv4.trans vk3
  have vc4 := vm hval4 vA vc3
  clear hm3 hk4 hv4 hpc4 hsp4 hval4 g19_3 g20_3 g29_3 kp3 vk3 kf3 hrun3
  refine Reach.mk hrun4 (f05_92 hP hCL kf4) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun4 (f05_96 hP hCL kf4) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun4 (f05_100 hP hCL kf4) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  rw [pick4] at hm4
  rw [pick14] at hm4
  rw [pick5] at hm4
  rw [pick7] at hm4
  rw [group4] at hm4
  refine call_mul hP hM hCL hrun4 kf4 (f05_104 hP hCL kf4) halSP2
    (by simp [upd_apply, g19_4, g20_4, g29_4] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_4, g20_4, g29_4] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_4, g20_4, g29_4] <;> (clear * -; bv_omega)) hm4 (lb_mono hb1) (lb_mono hb4) hl3 ?_
  intro sf5 res5 hrun5 hpc5 hsp5 hk5 hv5 kf5 hm5 hb5 hval5
  refine reach_congr (s' := mkS sf5 (mpl.base 5 + BitVec.ofNat 64 108) sf5.regs.regs SP2 sf5.pstate
    sf5.mem sf5.vregs.regs) (by rw [← hpc5, ← hsp5]; rfl) ?_
  rw [← group4] at hm5
  have g19_5 : sf5.regs.regs 19#5 = out :=
    (hk5 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_4, g20_4, g29_4])
  have g20_5 : sf5.regs.regs 20#5 = a :=
    (hk5 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_4, g20_4, g29_4])
  have g29_5 : sf5.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk5 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_4, g20_4, g29_4])
  have kp5 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf5.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk5 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp4 k h1 h2)
  have vk5 : calleeSavedVRegs sf5 = calleeSavedVRegs s0 := hv5.trans vk4
  have vc5 := vm hval5 vc1 vc4
  clear hm4 hk5 hv5 hpc5 hsp5 hval5 g19_4 g20_4 g29_4 kp4 vk4 kf4 hrun4
  refine Reach.mk hrun5 (f05_108 hP hCL kf5) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun5 (f05_112 hP hCL kf5) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun5 (f05_116 hP hCL kf5) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick4] at hm5
  rw [pick15] at hm5
  rw [pick5] at hm5
  rw [group3] at hm5
  refine call_p2k hP hK hCL hrun5 kf5 (f05_120 hP hCL kf5) halSP2
    (by simp [upd_apply, g19_5, g20_5, g29_5] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_5, g20_5, g29_5] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm5 (lb_mono hb5) hl4 ?_
  intro sf6 res6 hrun6 hpc6 hsp6 hk6 hv6 kf6 hm6 hb6 hval6
  refine reach_congr (s' := mkS sf6 (mpl.base 5 + BitVec.ofNat 64 124) sf6.regs.regs SP2 sf6.pstate
    sf6.mem sf6.vregs.regs) (by rw [← hpc6, ← hsp6]; rfl) ?_
  rw [← group3] at hm6
  have g19_6 : sf6.regs.regs 19#5 = out :=
    (hk6 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_5, g20_5, g29_5])
  have g20_6 : sf6.regs.regs 20#5 = a :=
    (hk6 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_5, g20_5, g29_5])
  have g29_6 : sf6.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk6 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_5, g20_5, g29_5])
  have kp6 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf6.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk6 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp5 k h1 h2)
  have vk6 : calleeSavedVRegs sf6 = calleeSavedVRegs s0 := hv6.trans vk5
  have vc6 := vp hval6 vc5 (by norm_num)
  clear hm5 hk6 hv6 hpc6 hsp6 hval6 g19_5 g20_5 g29_5 kp5 vk5 kf5 hrun5
  refine Reach.mk hrun6 (f05_124 hP hCL kf6) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun6 (f05_128 hP hCL kf6) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun6 (f05_132 hP hCL kf6) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  rw [pick3] at hm6
  rw [pick16] at hm6
  rw [pick4] at hm6
  rw [pick6] at hm6
  rw [group4] at hm6
  refine call_mul hP hM hCL hrun6 kf6 (f05_136 hP hCL kf6) halSP2
    (by simp [upd_apply, g19_6, g20_6, g29_6] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_6, g20_6, g29_6] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_6, g20_6, g29_6] <;> (clear * -; bv_omega)) hm6 (lb_mono hb4) (lb_mono hb6) hl5 ?_
  intro sf7 res7 hrun7 hpc7 hsp7 hk7 hv7 kf7 hm7 hb7 hval7
  refine reach_congr (s' := mkS sf7 (mpl.base 5 + BitVec.ofNat 64 140) sf7.regs.regs SP2 sf7.pstate
    sf7.mem sf7.vregs.regs) (by rw [← hpc7, ← hsp7]; rfl) ?_
  rw [← group4] at hm7
  have g19_7 : sf7.regs.regs 19#5 = out :=
    (hk7 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_6, g20_6, g29_6])
  have g20_7 : sf7.regs.regs 20#5 = a :=
    (hk7 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_6, g20_6, g29_6])
  have g29_7 : sf7.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk7 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_6, g20_6, g29_6])
  have kp7 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf7.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk7 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp6 k h1 h2)
  have vk7 : calleeSavedVRegs sf7 = calleeSavedVRegs s0 := hv7.trans vk6
  have vc7 := vm hval7 vc4 vc6
  clear hm6 hk7 hv7 hpc7 hsp7 hval7 g19_6 g20_6 g29_6 kp6 vk6 kf6 hrun6
  refine Reach.mk hrun7 (f05_140 hP hCL kf7) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun7 (f05_144 hP hCL kf7) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun7 (f05_148 hP hCL kf7) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick4] at hm7
  rw [pick17] at hm7
  rw [pick5] at hm7
  rw [group3] at hm7
  refine call_p2k hP hK hCL hrun7 kf7 (f05_152 hP hCL kf7) halSP2
    (by simp [upd_apply, g19_7, g20_7, g29_7] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_7, g20_7, g29_7] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm7 (lb_mono hb7) hl6 ?_
  intro sf8 res8 hrun8 hpc8 hsp8 hk8 hv8 kf8 hm8 hb8 hval8
  refine reach_congr (s' := mkS sf8 (mpl.base 5 + BitVec.ofNat 64 156) sf8.regs.regs SP2 sf8.pstate
    sf8.mem sf8.vregs.regs) (by rw [← hpc8, ← hsp8]; rfl) ?_
  rw [← group3] at hm8
  have g19_8 : sf8.regs.regs 19#5 = out :=
    (hk8 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_7, g20_7, g29_7])
  have g20_8 : sf8.regs.regs 20#5 = a :=
    (hk8 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_7, g20_7, g29_7])
  have g29_8 : sf8.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk8 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_7, g20_7, g29_7])
  have kp8 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf8.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk8 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp7 k h1 h2)
  have vk8 : calleeSavedVRegs sf8 = calleeSavedVRegs s0 := hv8.trans vk7
  have vc8 := vp hval8 vc7 (by norm_num)
  clear hm7 hk8 hv8 hpc8 hsp8 hval8 g19_7 g20_7 g29_7 kp7 vk7 kf7 hrun7
  refine Reach.mk hrun8 (f05_156 hP hCL kf8) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun8 (f05_160 hP hCL kf8) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun8 (f05_164 hP hCL kf8) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  rw [pick3] at hm8
  rw [pick18] at hm8
  rw [pick3] at hm8
  rw [pick4] at hm8
  rw [group4] at hm8
  refine call_mul hP hM hCL hrun8 kf8 (f05_168 hP hCL kf8) halSP2
    (by simp [upd_apply, g19_8, g20_8, g29_8] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_8, g20_8, g29_8] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_8, g20_8, g29_8] <;> (clear * -; bv_omega)) hm8 (lb_mono hb8) (lb_mono hb7) hl7 ?_
  intro sf9 res9 hrun9 hpc9 hsp9 hk9 hv9 kf9 hm9 hb9 hval9
  refine reach_congr (s' := mkS sf9 (mpl.base 5 + BitVec.ofNat 64 172) sf9.regs.regs SP2 sf9.pstate
    sf9.mem sf9.vregs.regs) (by rw [← hpc9, ← hsp9]; rfl) ?_
  rw [← group4] at hm9
  have g19_9 : sf9.regs.regs 19#5 = out :=
    (hk9 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_8, g20_8, g29_8])
  have g20_9 : sf9.regs.regs 20#5 = a :=
    (hk9 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_8, g20_8, g29_8])
  have g29_9 : sf9.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk9 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_8, g20_8, g29_8])
  have kp9 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf9.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk9 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp8 k h1 h2)
  have vk9 : calleeSavedVRegs sf9 = calleeSavedVRegs s0 := hv9.trans vk8
  have vc9 := vm hval9 vc8 vc7
  clear hm8 hk9 hv9 hpc9 hsp9 hval9 g19_8 g20_8 g29_8 kp8 vk8 kf8 hrun8
  refine Reach.mk hrun9 (f05_172 hP hCL kf9) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun9 (f05_176 hP hCL kf9) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun9 (f05_180 hP hCL kf9) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick4] at hm9
  rw [pick19] at hm9
  rw [pick5] at hm9
  rw [group3] at hm9
  refine call_p2k hP hK hCL hrun9 kf9 (f05_184 hP hCL kf9) halSP2
    (by simp [upd_apply, g19_9, g20_9, g29_9] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_9, g20_9, g29_9] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm9 (lb_mono hb9) hl8 ?_
  intro sf10 res10 hrun10 hpc10 hsp10 hk10 hv10 kf10 hm10 hb10 hval10
  refine reach_congr (s' := mkS sf10 (mpl.base 5 + BitVec.ofNat 64 188) sf10.regs.regs SP2 sf10.pstate
    sf10.mem sf10.vregs.regs) (by rw [← hpc10, ← hsp10]; rfl) ?_
  rw [← group3] at hm10
  have g19_10 : sf10.regs.regs 19#5 = out :=
    (hk10 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_9, g20_9, g29_9])
  have g20_10 : sf10.regs.regs 20#5 = a :=
    (hk10 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_9, g20_9, g29_9])
  have g29_10 : sf10.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk10 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_9, g20_9, g29_9])
  have kp10 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf10.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk10 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp9 k h1 h2)
  have vk10 : calleeSavedVRegs sf10 = calleeSavedVRegs s0 := hv10.trans vk9
  have vc10 := vp hval10 vc9 (by norm_num)
  clear hm9 hk10 hv10 hpc10 hsp10 hval10 g19_9 g20_9 g29_9 kp9 vk9 kf9 hrun9
  refine Reach.mk hrun10 (f05_188 hP hCL kf10) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun10 (f05_192 hP hCL kf10) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun10 (f05_196 hP hCL kf10) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  rw [pick3] at hm10
  rw [pick20] at hm10
  rw [pick3] at hm10
  rw [pick4] at hm10
  rw [group4] at hm10
  refine call_mul hP hM hCL hrun10 kf10 (f05_200 hP hCL kf10) halSP2
    (by simp [upd_apply, g19_10, g20_10, g29_10] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_10, g20_10, g29_10] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_10, g20_10, g29_10] <;> (clear * -; bv_omega)) hm10 (lb_mono hb10) (lb_mono hb9) hl9 ?_
  intro sf11 res11 hrun11 hpc11 hsp11 hk11 hv11 kf11 hm11 hb11 hval11
  refine reach_congr (s' := mkS sf11 (mpl.base 5 + BitVec.ofNat 64 204) sf11.regs.regs SP2 sf11.pstate
    sf11.mem sf11.vregs.regs) (by rw [← hpc11, ← hsp11]; rfl) ?_
  rw [← group4] at hm11
  have g19_11 : sf11.regs.regs 19#5 = out :=
    (hk11 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_10, g20_10, g29_10])
  have g20_11 : sf11.regs.regs 20#5 = a :=
    (hk11 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_10, g20_10, g29_10])
  have g29_11 : sf11.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk11 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_10, g20_10, g29_10])
  have kp11 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf11.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk11 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp10 k h1 h2)
  have vk11 : calleeSavedVRegs sf11 = calleeSavedVRegs s0 := hv11.trans vk10
  have vc11 := vm hval11 vc10 vc9
  clear hm10 hk11 hv11 hpc11 hsp11 hval11 g19_10 g20_10 g29_10 kp10 vk10 kf10 hrun10
  refine Reach.mk hrun11 (f05_204 hP hCL kf11) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun11 (f05_208 hP hCL kf11) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun11 (f05_212 hP hCL kf11) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick4] at hm11
  rw [pick21] at hm11
  rw [pick5] at hm11
  rw [group3] at hm11
  refine call_p2k hP hK hCL hrun11 kf11 (f05_216 hP hCL kf11) halSP2
    (by simp [upd_apply, g19_11, g20_11, g29_11] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_11, g20_11, g29_11] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm11 (lb_mono hb11) hl10 ?_
  intro sf12 res12 hrun12 hpc12 hsp12 hk12 hv12 kf12 hm12 hb12 hval12
  refine reach_congr (s' := mkS sf12 (mpl.base 5 + BitVec.ofNat 64 220) sf12.regs.regs SP2 sf12.pstate
    sf12.mem sf12.vregs.regs) (by rw [← hpc12, ← hsp12]; rfl) ?_
  rw [← group3] at hm12
  have g19_12 : sf12.regs.regs 19#5 = out :=
    (hk12 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_11, g20_11, g29_11])
  have g20_12 : sf12.regs.regs 20#5 = a :=
    (hk12 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_11, g20_11, g29_11])
  have g29_12 : sf12.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk12 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_11, g20_11, g29_11])
  have kp12 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf12.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk12 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp11 k h1 h2)
  have vk12 : calleeSavedVRegs sf12 = calleeSavedVRegs s0 := hv12.trans vk11
  have vc12 := vp hval12 vc11 (by norm_num)
  clear hm11 hk12 hv12 hpc12 hsp12 hval12 g19_11 g20_11 g29_11 kp11 vk11 kf11 hrun11
  refine Reach.mk hrun12 (f05_220 hP hCL kf12) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun12 (f05_224 hP hCL kf12) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun12 (f05_228 hP hCL kf12) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  rw [pick3] at hm12
  rw [pick22] at hm12
  rw [pick3] at hm12
  rw [pick4] at hm12
  rw [group4] at hm12
  refine call_mul hP hM hCL hrun12 kf12 (f05_232 hP hCL kf12) halSP2
    (by simp [upd_apply, g19_12, g20_12, g29_12] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_12, g20_12, g29_12] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_12, g20_12, g29_12] <;> (clear * -; bv_omega)) hm12 (lb_mono hb12) (lb_mono hb11) hl11 ?_
  intro sf13 res13 hrun13 hpc13 hsp13 hk13 hv13 kf13 hm13 hb13 hval13
  refine reach_congr (s' := mkS sf13 (mpl.base 5 + BitVec.ofNat 64 236) sf13.regs.regs SP2 sf13.pstate
    sf13.mem sf13.vregs.regs) (by rw [← hpc13, ← hsp13]; rfl) ?_
  rw [← group4] at hm13
  have g19_13 : sf13.regs.regs 19#5 = out :=
    (hk13 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_12, g20_12, g29_12])
  have g20_13 : sf13.regs.regs 20#5 = a :=
    (hk13 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_12, g20_12, g29_12])
  have g29_13 : sf13.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk13 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_12, g20_12, g29_12])
  have kp13 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf13.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk13 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp12 k h1 h2)
  have vk13 : calleeSavedVRegs sf13 = calleeSavedVRegs s0 := hv13.trans vk12
  have vc13 := vm hval13 vc12 vc11
  clear hm12 hk13 hv13 hpc13 hsp13 hval13 g19_12 g20_12 g29_12 kp12 vk12 kf12 hrun12
  refine Reach.mk hrun13 (f05_236 hP hCL kf13) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun13 (f05_240 hP hCL kf13) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun13 (f05_244 hP hCL kf13) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick4] at hm13
  rw [pick23] at hm13
  rw [pick5] at hm13
  rw [group3] at hm13
  refine call_p2k hP hK hCL hrun13 kf13 (f05_248 hP hCL kf13) halSP2
    (by simp [upd_apply, g19_13, g20_13, g29_13] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_13, g20_13, g29_13] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm13 (lb_mono hb13) hl12 ?_
  intro sf14 res14 hrun14 hpc14 hsp14 hk14 hv14 kf14 hm14 hb14 hval14
  refine reach_congr (s' := mkS sf14 (mpl.base 5 + BitVec.ofNat 64 252) sf14.regs.regs SP2 sf14.pstate
    sf14.mem sf14.vregs.regs) (by rw [← hpc14, ← hsp14]; rfl) ?_
  rw [← group3] at hm14
  have g19_14 : sf14.regs.regs 19#5 = out :=
    (hk14 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_13, g20_13, g29_13])
  have g20_14 : sf14.regs.regs 20#5 = a :=
    (hk14 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_13, g20_13, g29_13])
  have g29_14 : sf14.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk14 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_13, g20_13, g29_13])
  have kp14 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf14.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk14 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp13 k h1 h2)
  have vk14 : calleeSavedVRegs sf14 = calleeSavedVRegs s0 := hv14.trans vk13
  have vc14 := vp hval14 vc13 (by norm_num)
  clear hm13 hk14 hv14 hpc14 hsp14 hval14 g19_13 g20_13 g29_13 kp13 vk13 kf13 hrun13
  refine Reach.mk hrun14 (f05_252 hP hCL kf14) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun14 (f05_256 hP hCL kf14) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  refine Reach.mk hrun14 (f05_260 hP hCL kf14) ?_
  rw [ex_add_gpr_sp _ (by decide), pc_add]
  rw [pick3] at hm14
  rw [pick24] at hm14
  rw [pick8] at hm14
  rw [pick5] at hm14
  rw [group4] at hm14
  refine call_mul hP hM hCL hrun14 kf14 (f05_264 hP hCL kf14) halSP2
    (by simp [upd_apply, g19_14, g20_14, g29_14] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_14, g20_14, g29_14] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_14, g20_14, g29_14] <;> (clear * -; bv_omega)) hm14 (lb_mono hb14) (lb_mono hb9) hl13 ?_
  intro sf15 res15 hrun15 hpc15 hsp15 hk15 hv15 kf15 hm15 hb15 hval15
  refine reach_congr (s' := mkS sf15 (mpl.base 5 + BitVec.ofNat 64 268) sf15.regs.regs SP2 sf15.pstate
    sf15.mem sf15.vregs.regs) (by rw [← hpc15, ← hsp15]; rfl) ?_
  rw [← group4] at hm15
  have g19_15 : sf15.regs.regs 19#5 = out :=
    (hk15 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_14, g20_14, g29_14])
  have g20_15 : sf15.regs.regs 20#5 = a :=
    (hk15 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_14, g20_14, g29_14])
  have g29_15 : sf15.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk15 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_14, g20_14, g29_14])
  have kp15 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf15.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk15 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp14 k h1 h2)
  have vk15 : calleeSavedVRegs sf15 = calleeSavedVRegs s0 := hv15.trans vk14
  have vc15 := vm hval15 vc14 vc9
  clear hm14 hk15 hv15 hpc15 hsp15 hval15 g19_14 g20_14 g29_14 kp14 vk14 kf14 hrun14
  refine Reach.mk hrun15 (f05_268 hP hCL kf15) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun15 (f05_272 hP hCL kf15) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun15 (f05_276 hP hCL kf15) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick4] at hm15
  rw [pick25] at hm15
  rw [pick5] at hm15
  rw [group3] at hm15
  refine call_p2k hP hK hCL hrun15 kf15 (f05_280 hP hCL kf15) halSP2
    (by simp [upd_apply, g19_15, g20_15, g29_15] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_15, g20_15, g29_15] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm15 (lb_mono hb15) hl14 ?_
  intro sf16 res16 hrun16 hpc16 hsp16 hk16 hv16 kf16 hm16 hb16 hval16
  refine reach_congr (s' := mkS sf16 (mpl.base 5 + BitVec.ofNat 64 284) sf16.regs.regs SP2 sf16.pstate
    sf16.mem sf16.vregs.regs) (by rw [← hpc16, ← hsp16]; rfl) ?_
  rw [← group3] at hm16
  have g19_16 : sf16.regs.regs 19#5 = out :=
    (hk16 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_15, g20_15, g29_15])
  have g20_16 : sf16.regs.regs 20#5 = a :=
    (hk16 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_15, g20_15, g29_15])
  have g29_16 : sf16.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk16 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_15, g20_15, g29_15])
  have kp16 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf16.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk16 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp15 k h1 h2)
  have vk16 : calleeSavedVRegs sf16 = calleeSavedVRegs s0 := hv16.trans vk15
  have vc16 := vp hval16 vc15 (by norm_num)
  clear hm15 hk16 hv16 hpc16 hsp16 hval16 g19_15 g20_15 g29_15 kp15 vk15 kf15 hrun15
  refine Reach.mk hrun16 (f05_284 hP hCL kf16) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun16 (f05_288 hP hCL kf16) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun16 (f05_292 hP hCL kf16) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  rw [pick3] at hm16
  rw [pick26] at hm16
  rw [pick3] at hm16
  rw [pick4] at hm16
  rw [group4] at hm16
  refine call_mul hP hM hCL hrun16 kf16 (f05_296 hP hCL kf16) halSP2
    (by simp [upd_apply, g19_16, g20_16, g29_16] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_16, g20_16, g29_16] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_16, g20_16, g29_16] <;> (clear * -; bv_omega)) hm16 (lb_mono hb16) (lb_mono hb15) hl15 ?_
  intro sf17 res17 hrun17 hpc17 hsp17 hk17 hv17 kf17 hm17 hb17 hval17
  refine reach_congr (s' := mkS sf17 (mpl.base 5 + BitVec.ofNat 64 300) sf17.regs.regs SP2 sf17.pstate
    sf17.mem sf17.vregs.regs) (by rw [← hpc17, ← hsp17]; rfl) ?_
  rw [← group4] at hm17
  have g19_17 : sf17.regs.regs 19#5 = out :=
    (hk17 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_16, g20_16, g29_16])
  have g20_17 : sf17.regs.regs 20#5 = a :=
    (hk17 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_16, g20_16, g29_16])
  have g29_17 : sf17.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk17 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_16, g20_16, g29_16])
  have kp17 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf17.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk17 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp16 k h1 h2)
  have vk17 : calleeSavedVRegs sf17 = calleeSavedVRegs s0 := hv17.trans vk16
  have vc17 := vm hval17 vc16 vc15
  clear hm16 hk17 hv17 hpc17 hsp17 hval17 g19_16 g20_16 g29_16 kp16 vk16 kf16 hrun16
  refine Reach.mk hrun17 (f05_300 hP hCL kf17) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun17 (f05_304 hP hCL kf17) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun17 (f05_308 hP hCL kf17) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick4] at hm17
  rw [pick27] at hm17
  rw [pick5] at hm17
  rw [group3] at hm17
  refine call_p2k hP hK hCL hrun17 kf17 (f05_312 hP hCL kf17) halSP2
    (by simp [upd_apply, g19_17, g20_17, g29_17] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_17, g20_17, g29_17] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm17 (lb_mono hb17) hl16 ?_
  intro sf18 res18 hrun18 hpc18 hsp18 hk18 hv18 kf18 hm18 hb18 hval18
  refine reach_congr (s' := mkS sf18 (mpl.base 5 + BitVec.ofNat 64 316) sf18.regs.regs SP2 sf18.pstate
    sf18.mem sf18.vregs.regs) (by rw [← hpc18, ← hsp18]; rfl) ?_
  rw [← group3] at hm18
  have g19_18 : sf18.regs.regs 19#5 = out :=
    (hk18 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_17, g20_17, g29_17])
  have g20_18 : sf18.regs.regs 20#5 = a :=
    (hk18 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_17, g20_17, g29_17])
  have g29_18 : sf18.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk18 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_17, g20_17, g29_17])
  have kp18 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf18.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk18 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp17 k h1 h2)
  have vk18 : calleeSavedVRegs sf18 = calleeSavedVRegs s0 := hv18.trans vk17
  have vc18 := vp hval18 vc17 (by norm_num)
  clear hm17 hk18 hv18 hpc18 hsp18 hval18 g19_17 g20_17 g29_17 kp17 vk17 kf17 hrun17
  refine Reach.mk hrun18 (f05_316 hP hCL kf18) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun18 (f05_320 hP hCL kf18) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun18 (f05_324 hP hCL kf18) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  rw [pick3] at hm18
  rw [pick28] at hm18
  rw [pick3] at hm18
  rw [pick4] at hm18
  rw [group4] at hm18
  refine call_mul hP hM hCL hrun18 kf18 (f05_328 hP hCL kf18) halSP2
    (by simp [upd_apply, g19_18, g20_18, g29_18] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_18, g20_18, g29_18] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_18, g20_18, g29_18] <;> (clear * -; bv_omega)) hm18 (lb_mono hb18) (lb_mono hb17) hl17 ?_
  intro sf19 res19 hrun19 hpc19 hsp19 hk19 hv19 kf19 hm19 hb19 hval19
  refine reach_congr (s' := mkS sf19 (mpl.base 5 + BitVec.ofNat 64 332) sf19.regs.regs SP2 sf19.pstate
    sf19.mem sf19.vregs.regs) (by rw [← hpc19, ← hsp19]; rfl) ?_
  rw [← group4] at hm19
  have g19_19 : sf19.regs.regs 19#5 = out :=
    (hk19 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_18, g20_18, g29_18])
  have g20_19 : sf19.regs.regs 20#5 = a :=
    (hk19 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_18, g20_18, g29_18])
  have g29_19 : sf19.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk19 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_18, g20_18, g29_18])
  have kp19 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf19.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk19 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp18 k h1 h2)
  have vk19 : calleeSavedVRegs sf19 = calleeSavedVRegs s0 := hv19.trans vk18
  have vc19 := vm hval19 vc18 vc17
  clear hm18 hk19 hv19 hpc19 hsp19 hval19 g19_18 g20_18 g29_18 kp18 vk18 kf18 hrun18
  refine Reach.mk hrun19 (f05_332 hP hCL kf19) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun19 (f05_336 hP hCL kf19) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun19 (f05_340 hP hCL kf19) ?_
  rw [ex_movz32 _ (by decide), pc_add]
  rw [pick4] at hm19
  rw [pick21] at hm19
  rw [pick5] at hm19
  rw [group3] at hm19
  refine call_p2k hP hK hCL hrun19 kf19 (f05_344 hP hCL kf19) halSP2
    (by simp [upd_apply, g19_19, g20_19, g29_19] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_19, g20_19, g29_19] <;> (clear * -; bv_omega)) (by simp [upd_apply] <;> rfl) (by norm_num) (by norm_num) hm19 (lb_mono hb19) (lb_len hb2) ?_
  intro sf20 res20 hrun20 hpc20 hsp20 hk20 hv20 kf20 hm20 hb20 hval20
  refine reach_congr (s' := mkS sf20 (mpl.base 5 + BitVec.ofNat 64 348) sf20.regs.regs SP2 sf20.pstate
    sf20.mem sf20.vregs.regs) (by rw [← hpc20, ← hsp20]; rfl) ?_
  rw [← group3] at hm20
  have g19_20 : sf20.regs.regs 19#5 = out :=
    (hk20 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_19, g20_19, g29_19])
  have g20_20 : sf20.regs.regs 20#5 = a :=
    (hk20 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_19, g20_19, g29_19])
  have g29_20 : sf20.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk20 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_19, g20_19, g29_19])
  have kp20 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf20.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk20 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5), upd_ne _ _ (ne21 h1 h2 8#5)]; exact kp19 k h1 h2)
  have vk20 : calleeSavedVRegs sf20 = calleeSavedVRegs s0 := hv20.trans vk19
  have vc20 := vp hval20 vc19 (by norm_num)
  clear hm19 hk20 hv20 hpc20 hsp20 hval20 g19_19 g20_19 g29_19 kp19 vk19 kf19 hrun19
  refine Reach.mk hrun20 (f05_348 hP hCL kf20) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun20 (f05_352 hP hCL kf20) ?_
  rw [ex_sub_gpr_gpr _ _ (by decide) (by decide), pc_add]
  refine Reach.mk hrun20 (f05_356 hP hCL kf20) ?_
  rw [ex_mov _ _ (by decide) (by decide), pc_add]
  rw [pick3] at hm20
  rw [pick29] at hm20
  rw [pick8] at hm20
  rw [pick5] at hm20
  rw [group4] at hm20
  refine call_mul hP hM hCL hrun20 kf20 (f05_360 hP hCL kf20) halSP2
    (by simp [upd_apply, g19_20, g20_20, g29_20] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_20, g20_20, g29_20] <;> (clear * -; bv_omega)) (by simp [upd_apply, g19_20, g20_20, g29_20] <;> (clear * -; bv_omega)) hm20 (lb_mono hb20) (lb_mono hb15) hlo40 ?_
  intro sf21 res21 hrun21 hpc21 hsp21 hk21 hv21 kf21 hm21 hb21 hval21
  refine reach_congr (s' := mkS sf21 (mpl.base 5 + BitVec.ofNat 64 364) sf21.regs.regs SP2 sf21.pstate
    sf21.mem sf21.vregs.regs) (by rw [← hpc21, ← hsp21]; rfl) ?_
  rw [← group4] at hm21
  have g19_21 : sf21.regs.regs 19#5 = out :=
    (hk21 19#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_20, g20_20, g29_20])
  have g20_21 : sf21.regs.regs 20#5 = a :=
    (hk21 20#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_20, g20_20, g29_20])
  have g29_21 : sf21.regs.regs 29#5 = SP2 + BitVec.ofNat 64 768 :=
    (hk21 29#5 (by decide) (by decide)).trans (by simp [upd_apply, g19_20, g20_20, g29_20])
  have kp21 : ∀ k : BitVec 5, 21 ≤ k.toNat → k.toNat < 28 → sf21.regs.regs k = s0.regs.regs k :=
    fun k h1 h2 => (hk21 k (by omega) (by omega)).trans (by rw [upd_ne _ _ (ne21 h1 h2 8#5), upd_ne _ _ (ne21 h1 h2 1#5), upd_ne _ _ (ne21 h1 h2 0#5)]; exact kp20 k h1 h2)
  have vk21 : calleeSavedVRegs sf21 = calleeSavedVRegs s0 := hv21.trans vk20
  have vc21 := vm hval21 vc20 vc15
  clear hm20 hk21 hv21 hpc21 hsp21 hval21 g19_20 g20_20 g29_20 kp20 vk20 kf20 hrun20
  have ho2 : (out_bs.drop 40).length = 40 := by simp [hlo]
  rw [bytes40_cells (SP2 + BitVec.ofNat 64 128) res5 (lb_len hb5), bytes40_cells (out + BitVec.ofNat 64 40) (out_bs.drop 40) ho2] at hm21
  simp only [sepConj_assoc] at hm21
  rw [pick32] at hm21
  rw [pick32] at hm21
  rw [pick22] at hm21
  rw [pick22] at hm21
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm21
  have rd0 := cells_read128 hm21 0 (by simp)
  have rd2 := cells_read128 hm21 2 (by simp)
  simp only [Nat.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
    List.getElem_cons_succ, List.getElem_cons_zero] at rd0 rd2
  -- 364: ldp q0, q1, [sp, #128]
  refine Reach.mk hrun21 (f05_364 hP hCL kf21) ?_
  rw [ex_ldpq_sp _ _ _ halSP2 rd0.2.1 (by rw [BitVec.add_assoc]; exact rd2.2.1), pc_add, rd0.1,
    show SP2 + 128#64 + 16#64 = SP2 + 144#64 by rw [BitVec.add_assoc]; rfl, rd2.1]
  -- 368: ldr x8, [sp, #160]
  rw [pick2] at hm21
  have i8 := sat64_read hm21
  refine Reach.mk hrun21 (f05_368 hP hCL kf21) ?_
  rw [ex_ldr64_sp _ (by decide) _ halSP2 i8.2.1, pc_add, i8.1]
  -- 372: str x8, [x19, #72]
  rw [pick4] at hm21
  have i72 := sat64_read hm21
  have ea72 : upd sf21.regs.regs 8#5 (chunk res5 4) 19#5 + 72#64 = out + 72#64 := by simp [upd_apply, g19_21]
  refine Reach.mk hrun21 (f05_372 hP hCL kf21) ?_
  rw [ex_str64_gpr _ _ (by decide) (by decide) _ (by rw [ea72]; exact i72.2.2), pc_add, ea72,
    show upd sf21.regs.regs 8#5 (chunk res5 4) 8#5 = chunk res5 4 by simp [upd_apply]]
  obtain ⟨e72, ke72⟩ := cell_wr hm21 (chunk res5 4)
  have kfe1 := kf21.trans ke72
  -- 376: stur q0, [x19, #40]
  rw [pick4] at e72
  have w40 := cells_read128 e72 0 (by simp)
  simp only [Nat.reduceMul, BitVec.add_zero] at w40
  have ea40 : upd sf21.regs.regs 8#5 (chunk res5 4) 19#5 + 40#64 = out + BitVec.ofNat 64 40 := by
    simp [upd_apply, g19_21]
  refine Reach.mk hrun21 (f05_376 hP hCL kfe1) ?_
  rw [ex_strq_gpr _ _ (by decide) _ (by rw [ea40]; exact w40.2.2), pc_add, ea40,
    show upd (upd sf21.vregs.regs 0#5 (chunk res5 1 ++ chunk res5 0)) 1#5 (chunk res5 3 ++ chunk res5 2) 0#5 =
      chunk res5 1 ++ chunk res5 0 by simp [upd_apply]]
  have e40 := cells_write128 e72 0 (by simp) (chunk res5 1 ++ chunk res5 0)
  have kfe2 := kfe1.trans (Memory.keepsFrozen_write128 w40.2.2 (chunk res5 1 ++ chunk res5 0))
  simp only [Nat.reduceMul, BitVec.add_zero, List.set_cons_zero, List.set_cons_succ, append_lo,
    append_hi] at e40
  -- 380: stur q1, [x19, #56]
  have w56 := cells_read128 e40 2 (by simp)
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd] at w56
  have ea56 : upd sf21.regs.regs 8#5 (chunk res5 4) 19#5 + 56#64 = out + 56#64 := by
    simp [upd_apply, g19_21]
  refine Reach.mk hrun21 (f05_380 hP hCL kfe2) ?_
  rw [ex_strq_gpr _ _ (by decide) _ (by rw [ea56]; exact w56.2.2), pc_add, ea56,
    show upd (upd sf21.vregs.regs 0#5 (chunk res5 1 ++ chunk res5 0)) 1#5 (chunk res5 3 ++ chunk res5 2) 1#5 =
      chunk res5 3 ++ chunk res5 2 by simp [upd_apply]]
  have e56 := cells_write128 e40 2 (by simp) (chunk res5 3 ++ chunk res5 2)
  have kfe3 := kfe2.trans (Memory.keepsFrozen_write128 w56.2.2 (chunk res5 3 ++ chunk res5 2))
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, List.set_cons_zero, List.set_cons_succ,
    append_lo, append_hi] at e56
  -- 384: add sp, sp, #768
  refine Reach.mk hrun21 (f05_384 hP hCL kfe3) ?_
  rw [ex_add_sp, pc_add, show BitVec.zeroExtend 64 (0x300#12 : BitVec 12) = BitVec.ofNat 64 768 from rfl]
  rw [pick27] at e56
  rw [pick27] at e56
  have i88 := pair_info e56
  refine Reach.mk hrun21 (f05_388 hP hCL kfe3) ?_
  rw [ex_ldp64_sp _ _ (by decide) (by decide) _ halSP1' (by rw [e800]; exact i88.2.2.2.2.1)
    (by rw [e800, e808]; exact i88.2.2.2.2.2), pc_add, e800, e808]
  simp only [i88.1, i88.2.1]
  rw [pick28] at e56
  have i92 := sat64_read e56
  refine Reach.mk hrun21 (f05_392 hP hCL kfe3) ?_
  rw [ex_ldr64_sp _ (by decide) _ halSP1' (by rw [e784]; exact i92.2.1), pc_add, e784]
  simp only [i92.1]
  rw [pick30] at e56
  rw [pick30] at e56
  have i96 := pair_info e56
  refine Reach.mk hrun21 (f05_396 hP hCL kfe3) ?_
  rw [ex_ldp64_post_sp _ _ (by decide) (by decide) _ halSP1' i96.2.2.2.2.1
    (by rw [e776]; exact i96.2.2.2.2.2), pc_add, e776]
  simp only [i96.1, i96.2.1]
  refine Reach.mk hrun21 (f05_400 hP hCL kfe3) ?_
  rw [ex_ret]
  refine Reach.done ?_
  have hspf : SP2 + BitVec.ofNat 64 768 + 48#64 = s0.sp := by clear * - hSP2; rw [hSP2]; bv_omega
  left
  refine ⟨⟨?_, hspf, hrun21⟩, ⟨hspf, ?_⟩, ?_⟩
  · simp [upd_apply, readGpr_unfold, mkS_regs']
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [upd_apply, readGpr_unfold, mkS_regs']
    · simp [upd_apply, readGpr_unfold, mkS_regs']
    · simpa [upd_apply, readGpr_unfold, mkS_regs'] using kp21 21#5 (by decide) (by decide)
    · simpa [upd_apply, readGpr_unfold, mkS_regs'] using kp21 22#5 (by decide) (by decide)
    · simpa [upd_apply, readGpr_unfold, mkS_regs'] using kp21 23#5 (by decide) (by decide)
    · simpa [upd_apply, readGpr_unfold, mkS_regs'] using kp21 24#5 (by decide) (by decide)
    · simpa [upd_apply, readGpr_unfold, mkS_regs'] using kp21 25#5 (by decide) (by decide)
    · simpa [upd_apply, readGpr_unfold, mkS_regs'] using kp21 26#5 (by decide) (by decide)
    · simpa [upd_apply, readGpr_unfold, mkS_regs'] using kp21 27#5 (by decide) (by decide)
    · simp [upd_apply, readGpr_unfold, mkS_regs']
    · simp [upd_apply, readGpr_unfold, mkS_regs', Reg.fp]
    · simpa [calleeSavedVRegs, VRegFile.calleeSaved, VRegFile.read, upd_apply, mkS_vregs'] using vk21

  · have f21 : fe51ValOfBytes res21 % p25519 = fpPow (fe51ValOfBytes a_bs % p25519) (2 ^ 250 - 1) := by
      rw [vc21, fpPow_mod' _ _ (by norm_num)]; norm_num
    have f5 : fe51ValOfBytes res5 % p25519 = fpPow (fe51ValOfBytes a_bs % p25519) 11 := by
      rw [vc5, fpPow_mod' _ _ (by norm_num)]; norm_num
    have hq := Satisfies.of_eq e56 (Q := ((cellsFrom (SP2 + BitVec.ofNat 64 128) [chunk res5 0, chunk res5 1, chunk res5 2, chunk res5 3] ∗
        ((SP2 + BitVec.ofNat 64 160) ↦₆₄ chunk res5 4)) ∗
      (cellsFrom (out + BitVec.ofNat 64 40) [chunk res5 0, chunk res5 1, chunk res5 2, chunk res5 3] ∗ ((out + BitVec.ofNat 64 72) ↦₆₄ chunk res5 4))) ∗
      (memRegion (SP2 - BitVec.ofNat 64 224) 224 ∗ memRegion SP2 8 ∗ ((SP2 + BitVec.ofNat 64 8) ↦ₛ res1) ∗ ((SP2 + BitVec.ofNat 64 48) ↦ₛ res3) ∗ ((SP2 + BitVec.ofNat 64 88) ↦ₛ res4) ∗ ((SP2 + BitVec.ofNat 64 168) ↦ₛ res6) ∗ ((SP2 + BitVec.ofNat 64 208) ↦ₛ res7) ∗ ((SP2 + BitVec.ofNat 64 248) ↦ₛ res8) ∗ ((SP2 + BitVec.ofNat 64 288) ↦ₛ res9) ∗ ((SP2 + BitVec.ofNat 64 328) ↦ₛ res10) ∗ ((SP2 + BitVec.ofNat 64 368) ↦ₛ res11) ∗ ((SP2 + BitVec.ofNat 64 408) ↦ₛ res12) ∗ ((SP2 + BitVec.ofNat 64 448) ↦ₛ res13) ∗ ((SP2 + BitVec.ofNat 64 488) ↦ₛ res14) ∗ ((SP2 + BitVec.ofNat 64 528) ↦ₛ res15) ∗ ((SP2 + BitVec.ofNat 64 568) ↦ₛ res16) ∗ ((SP2 + BitVec.ofNat 64 608) ↦ₛ res17) ∗ ((SP2 + BitVec.ofNat 64 648) ↦ₛ res18) ∗ ((SP2 + BitVec.ofNat 64 688) ↦ₛ res19) ∗ ((SP2 + BitVec.ofNat 64 728) ↦ₛ res20) ∗ ((SP2 + BitVec.ofNat 64 768) ↦₆₄ (s0.regs.regs 29#5)) ∗ ((SP2 + BitVec.ofNat 64 776) ↦₆₄ (s0.regs.regs 30#5)) ∗ ((SP2 + BitVec.ofNat 64 784) ↦₆₄ (s0.regs.regs 28#5)) ∗ ((SP2 + BitVec.ofNat 64 792) ↦₆₄ u3) ∗ ((SP2 + BitVec.ofNat 64 800) ↦₆₄ (s0.regs.regs 20#5)) ∗ ((SP2 + BitVec.ofNat 64 808) ↦₆₄ (s0.regs.regs 19#5))) ∗
      (a ↦ₛ a_bs) ∗ (out ↦ₛ res21) ∗ R)
    rw [← bytes40_cells' (SP2 + BitVec.ofNat 64 128) (SP2 + BitVec.ofNat 64 160) res5 (lb_len hb5)
        (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]),
      ← bytes40_cells' (out + BitVec.ofNat 64 40) (out + BitVec.ofNat 64 72) res5 (lb_len hb5)
        (by rw [BitVec.add_assoc, ← BitVec.ofNat_add])] at hq
    have hq2 := Satisfies.of_eq hq (Q := (memRegion (SP2 - BitVec.ofNat 64 224) 224 ∗ memRegion SP2 8 ∗
        ((SP2 + BitVec.ofNat 64 8) ↦ₛ res1) ∗ ((SP2 + BitVec.ofNat 64 48) ↦ₛ res3) ∗ ((SP2 + BitVec.ofNat 64 88) ↦ₛ res4) ∗ ((SP2 + BitVec.ofNat 64 128) ↦ₛ res5) ∗ ((SP2 + BitVec.ofNat 64 168) ↦ₛ res6) ∗ ((SP2 + BitVec.ofNat 64 208) ↦ₛ res7) ∗ ((SP2 + BitVec.ofNat 64 248) ↦ₛ res8) ∗ ((SP2 + BitVec.ofNat 64 288) ↦ₛ res9) ∗ ((SP2 + BitVec.ofNat 64 328) ↦ₛ res10) ∗ ((SP2 + BitVec.ofNat 64 368) ↦ₛ res11) ∗ ((SP2 + BitVec.ofNat 64 408) ↦ₛ res12) ∗ ((SP2 + BitVec.ofNat 64 448) ↦ₛ res13) ∗ ((SP2 + BitVec.ofNat 64 488) ↦ₛ res14) ∗ ((SP2 + BitVec.ofNat 64 528) ↦ₛ res15) ∗ ((SP2 + BitVec.ofNat 64 568) ↦ₛ res16) ∗ ((SP2 + BitVec.ofNat 64 608) ↦ₛ res17) ∗ ((SP2 + BitVec.ofNat 64 648) ↦ₛ res18) ∗ ((SP2 + BitVec.ofNat 64 688) ↦ₛ res19) ∗ ((SP2 + BitVec.ofNat 64 728) ↦ₛ res20) ∗ ((SP2 + BitVec.ofNat 64 768) ↦₆₄ (s0.regs.regs 29#5)) ∗ ((SP2 + BitVec.ofNat 64 776) ↦₆₄ (s0.regs.regs 30#5)) ∗ ((SP2 + BitVec.ofNat 64 784) ↦₆₄ (s0.regs.regs 28#5)) ∗ ((SP2 + BitVec.ofNat 64 792) ↦₆₄ u3) ∗ ((SP2 + BitVec.ofNat 64 800) ↦₆₄ (s0.regs.regs 20#5)) ∗ ((SP2 + BitVec.ofNat 64 808) ↦₆₄ (s0.regs.regs 19#5))) ∗ ((a ↦ₛ a_bs) ∗ ((out ↦ₛ res21) ∗ ((out + BitVec.ofNat 64 40) ↦ₛ res5)) ∗ R))
    have hq3 := sat_sep_mono hq2 (stack_unlayout (lb_len hb1) (lb_len hb3) (lb_len hb4) (lb_len hb5) (lb_len hb6) (lb_len hb7) (lb_len hb8) (lb_len hb9) (lb_len hb10) (lb_len hb11) (lb_len hb12) (lb_len hb13) (lb_len hb14) (lb_len hb15) (lb_len hb16) (lb_len hb17) (lb_len hb18) (lb_len hb19) (lb_len hb20))
    have hap := pointsToBytes_append out res21 res5
    rw [lb_len hb21] at hap
    rw [← hap, show SP2 - BitVec.ofNat 64 224 = SP2 + BitVec.ofNat 64 768 + 48#64 - BitVec.ofNat 64 1040 by
      clear * - hSP2; bv_omega, show (224 + 816 : Nat) = 1040 from rfl] at hq3
    have hq4 := sat_sep_mono (Satisfies.of_eq hq3 (Q := (out ↦ₛ (res21 ++ res5)) ∗
        ((a ↦ₛ a_bs) ∗ memRegion (SP2 + BitVec.ofNat 64 768 + 48#64 - BitVec.ofNat 64 1040) 1040 ∗ R)))
      (Entails.trans (ent_pure_right (φ := fe51LimbsBounded res21 (2 ^ 52) ∧ fe51LimbsBounded res5 (2 ^ 52) ∧
          fe51ValOfBytes res21 % p25519 = fpPow (fe51ValOfBytes a_bs % p25519) (2 ^ 250 - 1) ∧
          fe51ValOfBytes res5 % p25519 = fpPow (fe51ValOfBytes a_bs % p25519) 11) ⟨hb21, hb5, f21, f5⟩)
        (ent_ex2 (P := fun t19_bs t3_bs => (out ↦ₛ (t19_bs ++ t3_bs)) ∗
          ⌜fe51LimbsBounded t19_bs (2 ^ 52) ∧ fe51LimbsBounded t3_bs (2 ^ 52) ∧
            fe51ValOfBytes t19_bs % p25519 = fpPow (fe51ValOfBytes a_bs % p25519) (2 ^ 250 - 1) ∧
            fe51ValOfBytes t3_bs % p25519 = fpPow (fe51ValOfBytes a_bs % p25519) 11⌝) res21 res5))
    have hq5 := Satisfies.of_eq hq4 (Q := ((a ↦ₛ a_bs) ∗
        memRegion (SP2 + BitVec.ofNat 64 768 + 48#64 - BitVec.ofNat 64 1040) 1040 ∗
        (∃∗ t19_bs, ∃∗ t3_bs, (out ↦ₛ (t19_bs ++ t3_bs)) ∗
          ⌜fe51LimbsBounded t19_bs (2 ^ 52) ∧ fe51LimbsBounded t3_bs (2 ^ 52) ∧
            fe51ValOfBytes t19_bs % p25519 = fpPow (fe51ValOfBytes a_bs % p25519) (2 ^ 250 - 1) ∧
            fe51ValOfBytes t3_bs % p25519 = fpPow (fe51ValOfBytes a_bs % p25519) 11⌝)) ∗ R)
    exact hq5

end X25519Dalek.GP
end


theorem solution :
    X25519Dalek.fnOk
      "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501"
      (fun _ => X25519Dalek.fe51Pow22501Spec) :=
  X25519Dalek.GP.p22_ok X25519Dalek.fnOk_fe51_mul.1 X25519Dalek.fnOk_fe51_pow2k
