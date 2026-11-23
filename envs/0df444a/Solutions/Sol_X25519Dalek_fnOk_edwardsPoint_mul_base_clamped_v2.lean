-- Prove2me | solution 1 for X25519Dalek.fnOk_edwardsPoint_mul_base_clamped_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T19:42:22.784839+00:00
-- url     : https://prove2.me/submissions/37929581-35d8-4515-bdeb-249024b80a99
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.IntervalCases
import Definitions.Def_X25519Dalek_Spec
import Definitions.Def_Arm64_Spec_SepLogicModel
import Theorems.Thm_X25519Dalek_ed25519BasepointTable_bounded_v2
import Theorems.Thm_X25519Dalek_fnOk_basepointTable_mul_base_v2
universe u

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

end Memory

/-! ## Every step keeps frozen memory -/

@[simp]
theorem evalSvc_tpidrEl0 (svc : State → State) (s : State) :
    (evalSvc svc s).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[simp]
theorem evalSvc_symtab (svc : State → State) (s : State) :
    (evalSvc svc s).symtab = s.symtab := by
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

theorem Program.codeLoaded_iff {prog : Program} {m : Memory} :
    prog.CodeLoaded m ↔
      prog.base.toNat % 4 = 0 ∧ prog.base.toNat + prog.code.length ≤ 2 ^ 64 ∧
      ∀ (i : Nat) (hi : i < prog.code.length),
        m.read8 (prog.base + BitVec.ofNat 64 i) = prog.code[i] ∧
        m.perm (prog.base + BitVec.ofNat 64 i) = some Perm.rx ∧
        m.isLazyFree (prog.base + BitVec.ofNat 64 i) = false := by
  unfold Program.CodeLoaded; exact Iff.rfl

theorem Program.CodeLoaded.intro {prog : Program} {m : Memory}
    (h_al : prog.base.toNat % 4 = 0) (h_len : prog.base.toNat + prog.code.length ≤ 2 ^ 64)
    (h : ∀ (i : Nat) (hi : i < prog.code.length),
      m.read8 (prog.base + BitVec.ofNat 64 i) = prog.code[i] ∧
      m.perm (prog.base + BitVec.ofNat 64 i) = some Perm.rx ∧
      m.isLazyFree (prog.base + BitVec.ofNat 64 i) = false) : prog.CodeLoaded m :=
  Program.codeLoaded_iff.2 ⟨h_al, h_len, h⟩

/-- Loaded code is frozen, so it stays loaded under any `KeepsFrozen` change. -/
theorem Program.CodeLoaded.of_keepsFrozen {prog : Program} {m m' : Memory}
    (hL : prog.CodeLoaded m) (hk : m.KeepsFrozen m') : prog.CodeLoaded m' := by
  obtain ⟨h1, h2, h3⟩ := Program.codeLoaded_iff.1 hL
  refine Program.CodeLoaded.intro h1 h2 fun i hi => ?_
  obtain ⟨hb, hp, hlf⟩ := h3 i hi
  have hf : m.Frozen (prog.base + BitVec.ofNat 64 i) := by
    unfold Memory.Frozen; rw [hp]; rfl
  obtain ⟨hb', hp', hlf', _⟩ := hk _ hf
  exact ⟨hb'.trans hb, hp'.trans hp, hlf'.trans hlf⟩

end Arm64
end

section
/-! Port of google-deepmind/code-verification @ 8c8d371f arm64-semantics/ProofLib/CoreLemmas.lean (Apache-2.0), section "Core Separation Logic Algebraic and Pure-Extraction Lemmas". -/

namespace Arm64

/-! Port of ProofLib/SepLogic/Model.lean (same commit). -/
namespace SepProp

/-- `m ⊨ P` holds iff some sub-heap satisfying `P` matches `m`. -/
theorem satisfies_iff {P : SepProp} {m : Memory} :
    (m ⊨ P) ↔ ∃ h : Heap, P.holds h ∧ h.Matches m := Iff.rfl

/-- `P ⊢ Q` holds iff every heap satisfying `P` satisfies `Q`. -/
theorem entails_iff {P Q : SepProp} : (P ⊢ Q) ↔ ∀ h : Heap, P.holds h → Q.holds h := Iff.rfl

theorem holds_bupd_iff {P : SepProp} {h : Heap} :
    (|==> P).holds h ↔ ∀ (m : Memory) (hf : Heap), h.Disjoint hf → (h.union hf).Matches m →
      ∃ h' : Heap, P.holds h' ∧ h'.Disjoint hf ∧ (h'.union hf).Matches m := Iff.rfl

theorem holds_emp_iff {h : Heap} : (emp : SepProp).holds h ↔ h = Heap.empty := Iff.rfl

theorem holds_pure_iff {φ : Prop} {h : Heap} : (⌜φ⌝ : SepProp).holds h ↔ h = Heap.empty ∧ φ :=
  Iff.rfl

theorem holds_sepConj_iff {P Q : SepProp} {h : Heap} :
    (P ∗ Q).holds h ↔
      ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.holds h₁ ∧ Q.holds h₂ := Iff.rfl

theorem holds_sepExists_iff {α : Sort _} {P : α → SepProp} {h : Heap} :
    (sepExists P).holds h ↔ ∃ x, (P x).holds h := Iff.rfl


end SepProp

theorem holds_pointsTo8_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8 a v).holds h ↔ h = Heap.singleton a v := Iff.rfl

theorem pointsToBytes_cons_def (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    pointsToBytes a (b :: bs) = (pointsTo8 a b ∗ pointsToBytes (a + 1#64) bs) := by rfl



open SepProp

/-! ## Core Separation Logic Algebraic and Pure-Extraction Lemmas -/

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

theorem GhostValid.of_phys {h : Heap}
    (ha : h.auth = fun _ _ => none := by rfl)
    (hf : h.frag = fun _ _ => none := by rfl) :
    h.GhostValid :=
  ⟨0, fun γ _ k => ⟨congrFun (congrFun ha γ) k, congrFun (congrFun hf γ) k⟩⟩

theorem GhostValid.union {h₁ h₂ : Heap}
    (hv1 : h₁.GhostValid) (hv2 : h₂.GhostValid) :
    (h₁.union h₂).GhostValid := by
  rcases hv1 with ⟨b1, hb1⟩
  rcases hv2 with ⟨b2, hb2⟩
  refine ⟨max b1 b2, fun γ hγ k => ?_⟩
  have ⟨ha1, hf1⟩ := hb1 γ (Nat.le_trans (Nat.le_max_left b1 b2) hγ) k
  have ⟨ha2, hf2⟩ := hb2 γ (Nat.le_trans (Nat.le_max_right b1 b2) hγ) k
  dsimp [Heap.union]
  rw [ha1, ha2, hf1, hf2]
  exact ⟨rfl, rfl⟩

theorem GhostValid.of_union_right {h₁ h₂ : Heap} (hv : (h₁.union h₂).GhostValid) :
    h₂.GhostValid := by
  rcases hv with ⟨b, hb⟩
  refine ⟨b, fun γ hγ k => ?_⟩
  have ⟨hau, hfu⟩ := hb γ hγ k
  dsimp [Heap.union] at hau hfu
  constructor
  · cases h1 : h₁.auth γ k with
    | none => rw [h1] at hau; exact hau
    | some _ => rw [h1] at hau; contradiction
  · cases h1 : h₁.frag γ k with
    | none => rw [h1] at hfu; exact hfu
    | some _ => rw [h1] at hfu; contradiction

theorem Matches.of_phys {h : Heap} {m : Memory}
    (ha : h.auth = fun _ _ => none := by rfl)
    (hf : h.frag = fun _ _ => none := by rfl)
    (hp : ∀ a c, h.phys a = some c →
      match c with
      | .rw b => m.read8 a = b ∧ m.perm a = some Perm.rw ∧ m.isLazyFree a = false
      | .ro b => m.read8 a = b ∧ (m.perm a).r = true ∧ m.isLazyFree a = false
      | .protNone b => m.read8 a = b ∧ m.perm a = some Perm.protNone ∧ m.isLazyFree a = false
      | .lazy => m.perm a = some Perm.rw
      | .protNoneLazy => m.perm a = some Perm.protNone)
    (hm : h.mapped = fun _ => false := by rfl) :
    h.Matches m :=
  ⟨hp, GhostValid.of_phys ha hf, fun a hmap => by rw [congrFun hm a] at hmap; contradiction⟩

theorem Matches.empty (m : Memory) : Heap.empty.Matches m :=
  Matches.of_phys rfl rfl (fun _ _ h => by contradiction)

theorem Matches.of_union_right {h₁ h₂ : Heap} {m : Memory}
    (hd : h₁.Disjoint h₂) (hm : (h₁.union h₂).Matches m) :
    h₂.Matches m := by
  refine ⟨fun a c h2 => ?_, GhostValid.of_union_right hm.2.1,
    fun a h2 => hm.2.2 a (by dsimp [Heap.union]; rw [h2, Bool.or_true])⟩
  apply hm.1 a c
  rw [union_comm_of_disjoint hd]
  dsimp [Heap.union]; rw [h2]

end Heap

theorem Entails.refl (P : SepProp) : P ⊢ P := SepProp.entails_iff.mpr fun _ h => h

theorem Entails.trans {P Q R : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  SepProp.entails_iff.mpr fun h hp => SepProp.entails_iff.mp h2 h (SepProp.entails_iff.mp h1 h hp)

theorem Satisfies.mono {P Q : SepProp} (h : P ⊢ Q) {m : Memory} (hm : m ⊨ P) : m ⊨ Q := by
  rcases SepProp.satisfies_iff.mp hm with ⟨hp, hP, hM⟩
  exact SepProp.satisfies_iff.mpr ⟨hp, SepProp.entails_iff.mp h hp hP, hM⟩

theorem bupd_intro (P : SepProp) : P ⊢ |==> P :=
  SepProp.entails_iff.mpr fun h hp => SepProp.holds_bupd_iff.mpr fun _ _ hd hm => ⟨h, hp, hd, hm⟩

@[simp]
theorem satisfies_bupd (P : SepProp) (m : Memory) : (m ⊨ |==> P) ↔ (m ⊨ P) := by
  constructor
  · intro hs
    obtain ⟨h, hbp, hm⟩ := SepProp.satisfies_iff.mp hs
    have hd : h.Disjoint Heap.empty := Heap.disjoint_empty_right h
    have hmu : (h.union Heap.empty).Matches m := by rwa [Heap.union_empty_right]
    rcases SepProp.holds_bupd_iff.mp hbp m Heap.empty hd hmu with ⟨h', hp', _, hm'⟩
    rw [Heap.union_empty_right] at hm'
    exact SepProp.satisfies_iff.mpr ⟨h', hp', hm'⟩
  · exact Satisfies.mono (bupd_intro P)

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

@[simp]
theorem pure_true : (⌜True⌝ : SepProp) = SepProp.emp := by
  ext h
  simp only [SepProp.holds_pure_iff, SepProp.holds_emp_iff, and_true]

@[simp]
theorem satisfies_emp (m : Memory) : (m ⊨ SepProp.emp) :=
  SepProp.satisfies_iff.mpr ⟨Heap.empty, SepProp.holds_emp_iff.mpr rfl, Heap.Matches.empty m⟩

@[simp]
theorem satisfies_pure (φ : Prop) (m : Memory) : (m ⊨ ⌜φ⌝) ↔ φ := by
  simp only [SepProp.satisfies_iff, SepProp.holds_pure_iff]
  constructor
  · rintro ⟨_, ⟨_, hφ⟩, _⟩; exact hφ
  · intro hφ; exact ⟨Heap.empty, ⟨rfl, hφ⟩, Heap.Matches.empty m⟩

theorem pure_sepConj (φ : Prop) (P : SepProp) : (⌜φ⌝ ∗ P) = ⟨fun h => φ ∧ P h⟩ := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_pure_iff]
  constructor
  · rintro ⟨h₁, h₂, _, rfl, ⟨rfl, hφ⟩, hp⟩
    exact ⟨hφ, by simpa using hp⟩
  · rintro ⟨hφ, hp⟩
    exact ⟨Heap.empty, h, Heap.disjoint_empty_left h, (Heap.union_empty_left h).symm, ⟨rfl, hφ⟩, hp⟩

@[simp]
theorem satisfies_pure_sepConj (φ : Prop) (P : SepProp) (m : Memory) :
    (m ⊨ ⌜φ⌝ ∗ P) ↔ (φ ∧ (m ⊨ P)) := by
  simp only [SepProp.satisfies_iff, pure_sepConj]
  constructor
  · rintro ⟨h, ⟨hφ, hp⟩, hm⟩
    exact ⟨hφ, ⟨h, hp, hm⟩⟩
  · rintro ⟨hφ, ⟨h, hp, hm⟩⟩
    exact ⟨h, ⟨hφ, hp⟩, hm⟩

@[simp]
theorem satisfies_sepConj_pure (P : SepProp) (φ : Prop) (m : Memory) :
    (m ⊨ P ∗ ⌜φ⌝) ↔ ((m ⊨ P) ∧ φ) := by
  rw [sepConj_comm, satisfies_pure_sepConj, And.comm]

@[simp]
theorem satisfies_sepConj_pure_assoc (P Q : SepProp) (φ : Prop) (m : Memory) :
    (m ⊨ P ∗ (⌜φ⌝ ∗ Q)) ↔ (φ ∧ (m ⊨ P ∗ Q)) := by
  rw [sepConj_left_comm, satisfies_pure_sepConj]

theorem sepConj_mono {P P' Q Q' : SepProp} (hp : P ⊢ P') (hq : Q ⊢ Q') :
    (P ∗ Q) ⊢ (P' ∗ Q') := by
  refine SepProp.entails_iff.mpr fun h hh => ?_
  obtain ⟨h₁, h₂, hd, rfl, h1, h2⟩ := SepProp.holds_sepConj_iff.mp hh
  exact SepProp.holds_sepConj_iff.mpr
    ⟨h₁, h₂, hd, rfl, SepProp.entails_iff.mp hp h₁ h1, SepProp.entails_iff.mp hq h₂ h2⟩

theorem sepConj_mono_left {P P' Q : SepProp} (hp : P ⊢ P') : (P ∗ Q) ⊢ (P' ∗ Q) :=
  sepConj_mono hp (Entails.refl Q)


theorem Entails.sepExists_intro {α : Sort u} {P : α → SepProp} (x : α) :
    P x ⊢ (∃∗ y, P y) :=
  SepProp.entails_iff.mpr fun _ hx => SepProp.holds_sepExists_iff.mpr ⟨x, hx⟩

theorem Entails.sepExists_elim {α : Sort u} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, P x ⊢ Q) : (∃∗ x, P x) ⊢ Q := by
  refine SepProp.entails_iff.mpr fun hp hh => ?_
  obtain ⟨x, hx⟩ := SepProp.holds_sepExists_iff.mp hh
  exact SepProp.entails_iff.mp (h x) hp hx

@[simp]
theorem sepExists_sepConj_left {α : Sort u} (P : α → SepProp) (Q : SepProp) :
    ((∃∗ x, P x) ∗ Q) = (∃∗ x, P x ∗ Q) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_sepExists_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, ⟨x, hpx⟩, hq⟩
    exact ⟨x, h₁, h₂, hd, rfl, hpx, hq⟩
  · rintro ⟨x, h₁, h₂, hd, rfl, hpx, hq⟩
    exact ⟨h₁, h₂, hd, rfl, ⟨x, hpx⟩, hq⟩

@[simp]
theorem sepExists_sepConj_right {α : Sort u} (P : SepProp) (Q : α → SepProp) :
    (P ∗ (∃∗ x, Q x)) = (∃∗ x, P ∗ Q x) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_sepExists_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, ⟨x, hqx⟩⟩
    exact ⟨x, h₁, h₂, hd, rfl, hp, hqx⟩
  · rintro ⟨x, h₁, h₂, hd, rfl, hp, hqx⟩
    exact ⟨h₁, h₂, hd, rfl, hp, ⟨x, hqx⟩⟩

@[simp]
theorem satisfies_sepExists {α : Sort u} (P : α → SepProp) (m : Memory) :
    (m ⊨ ∃∗ x, P x) ↔ (∃ x, m ⊨ P x) := by
  simp only [SepProp.satisfies_iff, SepProp.holds_sepExists_iff]
  constructor
  · rintro ⟨h, ⟨x, hpx⟩, hm⟩
    exact ⟨x, h, hpx, hm⟩
  · rintro ⟨x, h, hpx, hm⟩
    exact ⟨h, ⟨x, hpx⟩, hm⟩




end Arm64
end

section
/-! Port of google-deepmind/code-verification @ 8c8d371f arm64-semantics/ProofLib/CoreLemmas.lean (Apache-2.0): register-file, state and small-step lemmas. -/

namespace Arm64

/-! ## Register File and Architectural State Simplification Lemmas -/

namespace RegFile

@[simp]
theorem read_write (rf : RegFile) (idx1 idx2 : BitVec 5) (val : BitVec 64) :
    (rf.write idx1 val).read idx2 = if idx2 = idx1 then val else rf.read idx2 := rfl

@[simp]
theorem read_write_same (rf : RegFile) (idx : BitVec 5) (val : BitVec 64) :
    (rf.write idx val).read idx = val := by
  simp [read, write]

end RegFile

namespace VRegFile

@[simp]
theorem read_write (vf : VRegFile) (idx1 idx2 : BitVec 5) (val : BitVec 128) :
    (vf.write idx1 val).read idx2 = if idx2 = idx1 then val else vf.read idx2 := rfl

@[simp]
theorem read_write_same (vf : VRegFile) (idx : BitVec 5) (val : BitVec 128) :
    (vf.write idx val).read idx = val := by
  simp [read, write]

end VRegFile

namespace State

@[simp]
theorem readReg64_xzr (s : State) : s.readReg64 .xzr = 0#64 := by
  cases s; rfl

@[simp]
theorem readReg64_sp (s : State) : s.readReg64 .sp = s.sp := by
  cases s; rfl

@[simp]
theorem writeReg64_xzr (s : State) (v : BitVec 64) :
    s.writeReg64 .xzr v = s := by
  cases s; simp [State.writeReg64]

@[simp]
theorem readReg32_xzr (s : State) : s.readReg32 .xzr = 0#32 := by
  cases s; rfl

@[simp]
theorem writeReg32_xzr (s : State) (v : BitVec 32) :
    s.writeReg32 .xzr v = s := by
  cases s; simp [State.writeReg32, State.writeReg64]

@[simp]
theorem pc_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).pc = s.pc := by
  cases s; cases r <;> rfl

@[simp]
theorem pc_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).pc = s.pc :=
  pc_writeReg64 s r (v.zeroExtend 64)

@[simp]
theorem pc_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).pc = s.pc := by
  cases w <;> exact pc_writeReg64 s r _

@[simp]
theorem pstate_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).pstate = s.pstate := by
  cases s; cases r <;> rfl

@[simp]
theorem pstate_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).pstate = s.pstate :=
  pstate_writeReg64 s r (v.zeroExtend 64)

@[simp]
theorem pstate_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).pstate = s.pstate := by
  cases w <;> exact pstate_writeReg64 s r _

@[simp]
theorem mem_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by
  cases s; cases r <;> rfl

@[simp]
theorem mem_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem = s.mem :=
  mem_writeReg64 s r (v.zeroExtend 64)

@[simp]
theorem mem_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).mem = s.mem := by
  cases w <;> exact mem_writeReg64 s r _

@[simp]
theorem status_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).status = s.status := by
  cases s; cases r <;> rfl

@[simp]
theorem status_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).status = s.status :=
  status_writeReg64 s r (v.zeroExtend 64)

@[simp]
theorem status_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).status = s.status := by
  cases w <;> exact status_writeReg64 s r _

@[simp]
theorem sp_writeReg64_gpr (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr idx) v).sp = s.sp := by
  cases s; rfl

@[simp]
theorem readReg64_advancePC (s : State) (r : Reg) :
    s.advancePC.readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[simp]
theorem readReg64_setPC (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[simp]
theorem readReg64_setPState (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[simp]
theorem readReg64_setMem (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[simp]
theorem readReg64_writeReg64 (s : State) (r1 r2 : Reg) (v : BitVec 64) :
    (s.writeReg64 r1 v).readReg64 r2 =
      if r1 = .xzr ∨ r2 = .xzr ∨ r1 = .gpr 31#5 ∨ r2 = .gpr 31#5 then s.readReg64 r2
      else if r2 = r1 then v
      else s.readReg64 r2 := by
  cases r1 with
  | xzr =>
    cases r2 <;> simp [readReg64]
  | sp =>
    cases r2 with
    | xzr => simp [readReg64]
    | sp => simp [writeReg64, readReg64]
    | gpr idx2 =>
      by_cases h2 : idx2 = 31#5 <;> simp [h2, writeReg64, readReg64]
  | gpr idx1 =>
    by_cases h1 : idx1 = 31#5
    · subst h1
      cases r2 <;> simp [writeReg64, readReg64]
    · cases r2 with
      | xzr => simp [h1, readReg64]
      | sp => simp [h1, writeReg64, readReg64]
      | gpr idx2 =>
        by_cases h2 : idx2 = 31#5
        · subst h2; simp [h1, readReg64]
        · by_cases heq : idx2 = idx1
          · subst heq; simp [h1, writeReg64, readReg64]
          · simp [h1, h2, heq, writeReg64, readReg64]

/-! ### `fpsr` Projections & `setFpsr` / `orFpsr` Algebra -/

@[simp]
theorem fpsr_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).fpsr = f := by
  cases s; rfl

@[simp]
theorem fpsr_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).fpsr = s.fpsr ||| f := by
  cases s; rfl

@[simp]
theorem orFpsr_zero (s : State) : s.orFpsr 0#32 = s := by
  cases s; simp [State.orFpsr]

@[simp]
theorem orFpsr_orFpsr (s : State) (f1 f2 : BitVec 32) :
    (s.orFpsr f1).orFpsr f2 = s.orFpsr (f1 ||| f2) := by
  cases s; simp [State.orFpsr, BitVec.or_assoc]

@[simp]
theorem setFpsr_orFpsr (s : State) (f1 f2 : BitVec 32) :
    (s.setFpsr f1).orFpsr f2 = s.setFpsr (f1 ||| f2) := by
  cases s; rfl

@[simp]
theorem setFpsr_setFpsr (s : State) (f1 f2 : BitVec 32) :
    (s.setFpsr f1).setFpsr f2 = s.setFpsr f2 := by
  cases s; rfl

@[simp]
theorem orFpsr_setFpsr (s : State) (f1 f2 : BitVec 32) :
    (s.orFpsr f1).setFpsr f2 = s.setFpsr f2 := by
  cases s; rfl

@[simp]
theorem pc_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).pc = s.pc := by cases s; rfl
@[simp]
theorem pc_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).pc = s.pc := by cases s; rfl
@[simp]
theorem sp_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).sp = s.sp := by cases s; rfl
@[simp]
theorem sp_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).sp = s.sp := by cases s; rfl
@[simp]
theorem pstate_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).pstate = s.pstate := by cases s; rfl
@[simp]
theorem pstate_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).pstate = s.pstate := by cases s; rfl
@[simp]
theorem mem_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).mem = s.mem := by cases s; rfl
@[simp]
theorem mem_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).mem = s.mem := by cases s; rfl
@[simp]
theorem status_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).status = s.status := by cases s; rfl
@[simp]
theorem status_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).status = s.status := by cases s; rfl
@[simp]
theorem readReg64_setFpsr (s : State) (f : BitVec 32) (r : Reg) :
    (s.setFpsr f).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg64_orFpsr (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg32_setFpsr (s : State) (f : BitVec 32) (r : Reg) :
    (s.setFpsr f).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg32_orFpsr (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg_setFpsr (s : State) (f : BitVec 32) (w : Width) (r : Reg) :
    (s.setFpsr f).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp]
theorem readReg_orFpsr (s : State) (f : BitVec 32) (w : Width) (r : Reg) :
    (s.orFpsr f).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp]
theorem readVReg128_setFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.setFpsr f).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp]
theorem readVReg128_orFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.orFpsr f).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp]
theorem readVReg64_setFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.setFpsr f).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp]
theorem readVReg64_orFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.orFpsr f).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp]
theorem readVReg32_setFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.setFpsr f).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp]
theorem readVReg32_orFpsr (s : State) (f : BitVec 32) (idx : BitVec 5) :
    (s.orFpsr f).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp]
theorem tpidrEl0_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp]
theorem tpidrEl0_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp]
theorem brk_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).brk = s.brk := by cases s; rfl
@[simp]
theorem brk_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).brk = s.brk := by cases s; rfl
@[simp]
theorem brkStart_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).brkStart = s.brkStart := by cases s; rfl
@[simp]
theorem brkStart_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).brkStart = s.brkStart := by cases s; rfl
@[simp]
theorem fs_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).fs = s.fs := by cases s; rfl
@[simp]
theorem fs_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).fs = s.fs := by cases s; rfl
@[simp]
theorem oracle_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).oracle = s.oracle := by cases s; rfl
@[simp]
theorem oracle_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).oracle = s.oracle := by cases s; rfl
@[simp]
theorem oracleIdx_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp]
theorem oracleIdx_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp]
theorem trace_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).trace = s.trace := by cases s; rfl
@[simp]
theorem trace_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).trace = s.trace := by cases s; rfl

@[simp]
theorem fpsr_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).fpsr = s.fpsr := by
  cases s; cases r <;> rfl
@[simp]
theorem fpsr_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).fpsr = s.fpsr :=
  fpsr_writeReg64 s r (v.zeroExtend 64)
@[simp]
theorem fpsr_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).fpsr = s.fpsr := by
  cases w <;> exact fpsr_writeReg64 s r _
@[simp]
theorem fpsr_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) : (s.writeVReg128 idx v).fpsr = s.fpsr := by
  cases s; rfl
@[simp]
theorem fpsr_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) : (s.writeVReg64 idx v).fpsr = s.fpsr :=
  fpsr_writeVReg128 s idx (v.zeroExtend 128)
@[simp]
theorem fpsr_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) : (s.writeVReg32 idx v).fpsr = s.fpsr :=
  fpsr_writeVReg128 s idx (v.zeroExtend 128)
@[simp]
theorem fpsr_advancePC (s : State) : s.advancePC.fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem fpsr_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem fpsr_setPState (s : State) (ps : PState) : (s.setPState ps).fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem fpsr_setMem (s : State) (m : Memory) : (s.setMem m).fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem fpsr_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem fpsr_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem fpsr_setFs (s : State) (f : FsState) : (s.setFs f).fpsr = s.fpsr := by cases s; rfl
/-- Consume all leading `true` entries (spurious store-exclusive failures) and the succeeding
    decision (`false` or end-of-list) from `s.exclFails`, corresponding to the post-loop
    `exclFails` after an LL/SC retry loop succeeds. -/
def stepExclLoop (s : State) : State :=
  { s with exclFails := (s.exclFails.dropWhile (· == true)).tail }

@[simp]
theorem fpsr_nextOracle (s : State) : s.nextOracle.fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem fpsr_stepExclOracle (s : State) : s.stepExclOracle.fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem fpsr_stepExclLoop (s : State) : s.stepExclLoop.fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem symtab_stepExclLoop (s : State) : s.stepExclLoop.symtab = s.symtab := by cases s; rfl
@[simp]
theorem sym_stepExclLoop (s : State) (o n : String) : s.stepExclLoop.sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_stepExclLoop]
@[simp]
theorem fpsr_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).fpsr = s.fpsr := by cases s; rfl

@[simp]
theorem regs_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).regs = s.regs := by cases s; rfl
@[simp]
theorem vregs_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).vregs = s.vregs := by cases s; rfl
@[simp]
theorem readReg64_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (r : Reg) :
    (s.setSigAction sig act).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg32_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (r : Reg) :
    (s.setSigAction sig act).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (w : Width) (r : Reg) :
    (s.setSigAction sig act).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp]
theorem readVReg128_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (idx : BitVec 5) :
    (s.setSigAction sig act).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp]
theorem readVReg64_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (idx : BitVec 5) :
    (s.setSigAction sig act).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp]
theorem readVReg32_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) (idx : BitVec 5) :
    (s.setSigAction sig act).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp]
theorem sp_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).sp = s.sp := by cases s; rfl
@[simp]
theorem spAligned_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).spAligned = s.spAligned := by cases s; rfl
@[simp]
theorem pc_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).pc = s.pc := by cases s; rfl
@[simp]
theorem pstate_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).pstate = s.pstate := by cases s; rfl
@[simp]
theorem mem_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).mem = s.mem := by cases s; rfl
@[simp]
theorem tpidrEl0_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp]
theorem fpsr_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem brkStart_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).brkStart = s.brkStart := by cases s; rfl
@[simp]
theorem brk_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).brk = s.brk := by cases s; rfl
@[simp]
theorem fs_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).fs = s.fs := by cases s; rfl
@[simp]
theorem oracle_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).oracle = s.oracle := by cases s; rfl
@[simp]
theorem oracleIdx_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp]
theorem exclFails_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).exclFails = s.exclFails := by cases s; rfl
@[simp]
theorem exclWillFail_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).exclWillFail = s.exclWillFail := by cases s; rfl
@[simp]
theorem trace_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).trace = s.trace := by cases s; rfl
@[simp]
theorem status_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).status = s.status := by cases s; rfl


@[simp]
theorem getSigAction_setSigAction (s : State) (sig sig' : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).getSigAction sig' =
      if sig' = sig then act else s.getSigAction sig' := by
  cases s; unfold State.setSigAction State.getSigAction
  by_cases h : sig' = sig <;> simp [h]

@[simp]
theorem sigActions_setSigAction (s : State) (sig sig' : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).sigActions sig' =
      if sig' = sig then act else s.sigActions sig' := by
  cases s; unfold State.setSigAction
  by_cases h : sig' = sig <;> simp [h]

@[simp]
theorem setSigAction_setSigAction_same (s : State) (sig : BitVec 32) (a1 a2 : SigAction) :
    (s.setSigAction sig a1).setSigAction sig a2 = s.setSigAction sig a2 := by
  cases s; unfold State.setSigAction; congr; funext k
  by_cases h : k = sig <;> simp [h]

@[simp]
theorem getSigAction_writeReg64 (s : State) (r : Reg) (v : BitVec 64) (sig : BitVec 32) :
    (s.writeReg64 r v).getSigAction sig = s.getSigAction sig := by cases s; cases r <;> rfl
@[simp]
theorem getSigAction_writeReg32 (s : State) (r : Reg) (v : BitVec 32) (sig : BitVec 32) :
    (s.writeReg32 r v).getSigAction sig = s.getSigAction sig :=
  getSigAction_writeReg64 s r (v.zeroExtend 64) sig
@[simp]
theorem getSigAction_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) (sig : BitVec 32) :
    (s.writeReg w r v).getSigAction sig = s.getSigAction sig := by
  cases w <;> exact getSigAction_writeReg64 s r _ sig
@[simp]
theorem getSigAction_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) (sig : BitVec 32) :
    (s.writeVReg128 idx v).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) (sig : BitVec 32) :
    (s.writeVReg64 idx v).getSigAction sig = s.getSigAction sig :=
  getSigAction_writeVReg128 s idx (v.zeroExtend 128) sig
@[simp]
theorem getSigAction_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) (sig : BitVec 32) :
    (s.writeVReg32 idx v).getSigAction sig = s.getSigAction sig :=
  getSigAction_writeVReg128 s idx (v.zeroExtend 128) sig
@[simp]
theorem getSigAction_advancePC (s : State) (sig : BitVec 32) :
    s.advancePC.getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_setPC (s : State) (pc : BitVec 64) (sig : BitVec 32) :
    (s.setPC pc).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_setPState (s : State) (ps : PState) (sig : BitVec 32) :
    (s.setPState ps).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_setMem (s : State) (m : Memory) (sig : BitVec 32) :
    (s.setMem m).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_setStatus (s : State) (st : ExecStatus) (sig : BitVec 32) :
    (s.setStatus st).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_setBrk (s : State) (b : BitVec 64) (sig : BitVec 32) :
    (s.setBrk b).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_setFs (s : State) (f : FsState) (sig : BitVec 32) :
    (s.setFs f).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_setFpsr (s : State) (f : BitVec 32) (sig : BitVec 32) :
    (s.setFpsr f).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_orFpsr (s : State) (f : BitVec 32) (sig : BitVec 32) :
    (s.orFpsr f).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_nextOracle (s : State) (sig : BitVec 32) :
    s.nextOracle.getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_stepExclOracle (s : State) (sig : BitVec 32) :
    s.stepExclOracle.getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_stepExclLoop (s : State) (sig : BitVec 32) :
    s.stepExclLoop.getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_appendTrace (s : State) (evs : List TraceEvent) (sig : BitVec 32) :
    (s.appendTrace evs).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem getSigAction_setSigAltStack (s : State) (sas : SigAltStack) (sig : BitVec 32) :
    (s.setSigAltStack sas).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem sigActions_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).sigActions = s.sigActions := by cases s; rfl

@[simp]
theorem regs_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).regs = s.regs := by cases s; rfl
@[simp]
theorem vregs_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).vregs = s.vregs := by cases s; rfl
@[simp]
theorem readReg64_setSigAltStack (s : State) (sas : SigAltStack) (r : Reg) :
    (s.setSigAltStack sas).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg32_setSigAltStack (s : State) (sas : SigAltStack) (r : Reg) :
    (s.setSigAltStack sas).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg_setSigAltStack (s : State) (sas : SigAltStack) (w : Width) (r : Reg) :
    (s.setSigAltStack sas).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp]
theorem readVReg128_setSigAltStack (s : State) (sas : SigAltStack) (idx : BitVec 5) :
    (s.setSigAltStack sas).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp]
theorem readVReg64_setSigAltStack (s : State) (sas : SigAltStack) (idx : BitVec 5) :
    (s.setSigAltStack sas).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp]
theorem readVReg32_setSigAltStack (s : State) (sas : SigAltStack) (idx : BitVec 5) :
    (s.setSigAltStack sas).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp]
theorem sp_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).sp = s.sp := by cases s; rfl
@[simp]
theorem spAligned_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).spAligned = s.spAligned := by cases s; rfl
@[simp]
theorem pc_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).pc = s.pc := by cases s; rfl
@[simp]
theorem pstate_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).pstate = s.pstate := by cases s; rfl
@[simp]
theorem mem_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).mem = s.mem := by cases s; rfl
@[simp]
theorem tpidrEl0_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp]
theorem fpsr_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem brkStart_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).brkStart = s.brkStart := by cases s; rfl
@[simp]
theorem brk_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).brk = s.brk := by cases s; rfl
@[simp]
theorem fs_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).fs = s.fs := by cases s; rfl
@[simp]
theorem oracle_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).oracle = s.oracle := by cases s; rfl
@[simp]
theorem oracleIdx_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp]
theorem exclFails_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).exclFails = s.exclFails := by cases s; rfl
@[simp]
theorem exclWillFail_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).exclWillFail = s.exclWillFail := by cases s; rfl
@[simp]
theorem trace_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).trace = s.trace := by cases s; rfl
@[simp]
theorem status_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).status = s.status := by cases s; rfl


@[simp]
theorem sigAltStack_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).sigAltStack = sas := by cases s; rfl

@[simp]
theorem setSigAltStack_setSigAltStack (s : State) (sas1 sas2 : SigAltStack) :
    (s.setSigAltStack sas1).setSigAltStack sas2 = s.setSigAltStack sas2 := by cases s; rfl

@[simp]
theorem sigAltStack_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp]
theorem getSigAction_setSigMask (s : State) (m : BitVec 64) (sig : BitVec 32) :
    (s.setSigMask m).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem sigActions_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).sigActions = s.sigActions := by cases s; rfl
@[simp]
theorem sigAltStack_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).sigAltStack = s.sigAltStack := by cases s; rfl
@[simp]
theorem regs_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).regs = s.regs := by cases s; rfl
@[simp]
theorem vregs_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).vregs = s.vregs := by cases s; rfl
@[simp]
theorem readReg64_setSigMask (s : State) (m : BitVec 64) (r : Reg) :
    (s.setSigMask m).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg32_setSigMask (s : State) (m : BitVec 64) (r : Reg) :
    (s.setSigMask m).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg_setSigMask (s : State) (m : BitVec 64) (w : Width) (r : Reg) :
    (s.setSigMask m).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp]
theorem readVReg128_setSigMask (s : State) (m : BitVec 64) (idx : BitVec 5) :
    (s.setSigMask m).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp]
theorem readVReg64_setSigMask (s : State) (m : BitVec 64) (idx : BitVec 5) :
    (s.setSigMask m).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp]
theorem readVReg32_setSigMask (s : State) (m : BitVec 64) (idx : BitVec 5) :
    (s.setSigMask m).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp]
theorem sp_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).sp = s.sp := by cases s; rfl
@[simp]
theorem spAligned_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).spAligned = s.spAligned := by cases s; rfl
@[simp]
theorem pc_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).pc = s.pc := by cases s; rfl
@[simp]
theorem pstate_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).pstate = s.pstate := by cases s; rfl
@[simp]
theorem mem_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).mem = s.mem := by cases s; rfl
@[simp]
theorem tpidrEl0_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp]
theorem fpsr_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem brkStart_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).brkStart = s.brkStart := by cases s; rfl
@[simp]
theorem brk_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).brk = s.brk := by cases s; rfl
@[simp]
theorem fs_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).fs = s.fs := by cases s; rfl
@[simp]
theorem oracle_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).oracle = s.oracle := by cases s; rfl
@[simp]
theorem oracleIdx_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp]
theorem exclFails_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).exclFails = s.exclFails := by cases s; rfl
@[simp]
theorem exclWillFail_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).exclWillFail = s.exclWillFail := by cases s; rfl
@[simp]
theorem trace_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).trace = s.trace := by cases s; rfl
@[simp]
theorem status_setSigMask (s : State) (m : BitVec 64) :
    (s.setSigMask m).status = s.status := by cases s; rfl


@[simp]
theorem setSigMask_setSigMask (s : State) (m1 m2 : BitVec 64) :
    (s.setSigMask m1).setSigMask m2 = s.setSigMask m2 := by cases s; rfl

@[simp]
theorem getSigAction_setSigPending (s : State) (p : BitVec 64) (sig : BitVec 32) :
    (s.setSigPending p).getSigAction sig = s.getSigAction sig := by cases s; rfl
@[simp]
theorem sigActions_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).sigActions = s.sigActions := by cases s; rfl
@[simp]
theorem sigAltStack_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).sigAltStack = s.sigAltStack := by cases s; rfl
@[simp]
theorem regs_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).regs = s.regs := by cases s; rfl
@[simp]
theorem vregs_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).vregs = s.vregs := by cases s; rfl
@[simp]
theorem readReg64_setSigPending (s : State) (p : BitVec 64) (r : Reg) :
    (s.setSigPending p).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg32_setSigPending (s : State) (p : BitVec 64) (r : Reg) :
    (s.setSigPending p).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp]
theorem readReg_setSigPending (s : State) (p : BitVec 64) (w : Width) (r : Reg) :
    (s.setSigPending p).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp]
theorem readVReg128_setSigPending (s : State) (p : BitVec 64) (idx : BitVec 5) :
    (s.setSigPending p).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp]
theorem readVReg64_setSigPending (s : State) (p : BitVec 64) (idx : BitVec 5) :
    (s.setSigPending p).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[simp]
theorem readVReg32_setSigPending (s : State) (p : BitVec 64) (idx : BitVec 5) :
    (s.setSigPending p).readVReg32 idx = s.readVReg32 idx := by cases s; rfl
@[simp]
theorem sp_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).sp = s.sp := by cases s; rfl
@[simp]
theorem spAligned_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).spAligned = s.spAligned := by cases s; rfl
@[simp]
theorem pc_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).pc = s.pc := by cases s; rfl
@[simp]
theorem pstate_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).pstate = s.pstate := by cases s; rfl
@[simp]
theorem mem_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).mem = s.mem := by cases s; rfl
@[simp]
theorem tpidrEl0_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp]
theorem fpsr_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).fpsr = s.fpsr := by cases s; rfl
@[simp]
theorem brkStart_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).brkStart = s.brkStart := by cases s; rfl
@[simp]
theorem brk_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).brk = s.brk := by cases s; rfl
@[simp]
theorem fs_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).fs = s.fs := by cases s; rfl
@[simp]
theorem oracle_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).oracle = s.oracle := by cases s; rfl
@[simp]
theorem oracleIdx_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp]
theorem exclFails_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).exclFails = s.exclFails := by cases s; rfl
@[simp]
theorem exclWillFail_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).exclWillFail = s.exclWillFail := by cases s; rfl
@[simp]
theorem trace_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).trace = s.trace := by cases s; rfl
@[simp]
theorem status_setSigPending (s : State) (p : BitVec 64) :
    (s.setSigPending p).status = s.status := by cases s; rfl


@[simp]
theorem setSigPending_setSigPending (s : State) (p1 p2 : BitVec 64) :
    (s.setSigPending p1).setSigPending p2 = s.setSigPending p2 := by cases s; rfl

end State

/-! ## Small-Step Operational Semantics Lemmas -/

namespace Steps


end Steps


namespace StepsUntil

end StepsUntil

namespace StepsUntilPC

end StepsUntilPC


end Arm64
end

section
/-! # Blocks of `x25519CliMultiLib` as programs: hook-freeness, transfer of executions between
blocks, and instruction fetch from loaded code.

Fetch lemmas adapted from the zlib CRC-32 mission's proofs (`ZlibCrc32.Small.Machine`); the
transfer lemma follows google-deepmind/code-verification @ 8c8d371f
`ProofLib/Placed/Multi.lean` (`steps_transfer_same_svc`, Apache-2.0). -/

namespace X25519Dalek.Edw

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- Block `i` of the library, placed under `mpl`, as a program. -/
def prog (mpl : MultiPlacement) (i : Nat) : Program := x25519CliMultiLib.blockProgram mpl i

theorem hook_none (mpl : MultiPlacement) (i : Nat) (pc : BitVec 64) :
    (prog mpl i).externAt? pc = none := by
  simp [prog, Program.externAt?, Program.hookAtOff?, MultiPlacedLib.blockProgram,
    PlacedLib.program]

theorem prog_svc (mpl : MultiPlacement) (i : Nat) : (prog mpl i).svc = Syscall.standard := rfl

/-- Every block steps the same way: no hooks, same supervisor-call handler. -/
theorem step_transfer {mpl : MultiPlacement} {i j : Nat} {s s' : State}
    (h : Step (prog mpl i) s s') : Step (prog mpl j) s s' := by
  cases h with
  | halt_unmapped hrun hfm _ =>
    exact Step.halt_unmapped hrun
      (by simpa [Program.fetchMem, hook_none] using hfm) (hook_none _ _ _)
  | externHook _ hex => rw [hook_none] at hex; cases hex
  | extern_fault _ hex => rw [hook_none] at hex; cases hex
  | @exec inst hrun hfm =>
    have hfm2 : (prog mpl j).fetchMem s.mem s.pc = some inst := by
      simpa [Program.fetchMem, hook_none] using hfm
    have hev : (prog mpl i).evalInst inst s = (prog mpl j).evalInst inst s := by
      simp [Program.evalInst, prog_svc]
    rw [hev]
    exact Step.exec hrun hfm2

theorem steps_transfer {mpl : MultiPlacement} {i j : Nat} {s s' : State}
    (h : Steps (prog mpl i) s s') : Steps (prog mpl j) s s' := by
  induction h with
  | refl _ => exact Steps.refl _
  | step h1 _ ih => exact Steps.step (step_transfer h1) ih

/-! ## Fetch -/

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

theorem take4_drop_patched {blk : CodeBlock} {pl : Placement} {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    ((blk.patched pl).drop off).take 4 = bytesOfWordLE (blk.patchedWord pl off) := by
  have hj : off / 4 < (List.range (blk.code.length / 4)).length := by
    simp only [List.length_range]; omega
  have h := drop_take_flatMap_bytesOfWordLE (fun j => blk.patchedWord pl (4 * j))
    (List.range (blk.code.length / 4)) (off / 4) hj
  rw [List.getElem_range, show 4 * (off / 4) = off by omega] at h
  exact h

theorem patched_length (blk : CodeBlock) (pl : Placement) (h4 : blk.code.length % 4 = 0) :
    (blk.patched pl).length = blk.code.length := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE, List.map_const', List.sum_replicate, List.length_range,
    smul_eq_mul]
  omega

theorem codeLoaded_cell {p : Program} {m : Memory} (h : p.CodeLoaded m) (i : Nat)
    (hi : i < p.code.length) :
    m.read8 (p.base + BitVec.ofNat 64 i) = p.code[i] ∧
    m.perm (p.base + BitVec.ofNat 64 i) = some Perm.rx := by
  unfold Program.CodeLoaded at h
  exact ⟨(h.2.2 i hi).1, (h.2.2 i hi).2.1⟩

/-- Fetch from a hook-free program holding the patched code of a placeable block. -/
theorem fetch_word_gen {P : Program} {blk : CodeBlock} {pl : Placement}
    (hbase : P.base = pl.base) (hcode : P.code = blk.patched pl)
    (hhook : ∀ pc, P.externAt? pc = none) (hP : blk.Placeable pl)
    {m : Memory} (hCL : P.CodeLoaded m) {off : Nat} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ blk.code.length) :
    P.fetchMem m (pl.base + BitVec.ofNat 64 off) = decode (blk.patchedWord pl off) := by
  have hl : P.code.length = blk.code.length := by rw [hcode, patched_length _ _ hP.len_aligned]
  have hb4 : pl.base.toNat % 4 = 0 := by
    have h1 := hP.base_aligned; have h2 := hP.align_pos
    obtain ⟨k, hk⟩ : 4 ∣ blk.align := Nat.dvd_of_mod_eq_zero h2.2
    have : blk.align ∣ pl.base.toNat := Nat.dvd_of_mod_eq_zero h1
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans ⟨k, hk⟩ this)
  have hnw : pl.base.toNat + blk.code.length ≤ 2 ^ 64 := hP.no_wrap
  have rd : ∀ k, k < 4 →
      m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
        (blk.patchedWord pl off).extractLsb' (8 * k) 8 ∧
      m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
    intro k hk
    have h := codeLoaded_cell hCL (off + k) (by omega)
    have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
        P.base + BitVec.ofNat 64 (off + k) := by
      rw [hbase, BitVec.add_assoc, BitVec.ofNat_add]
    rw [ha]
    refine ⟨?_, h.2⟩
    rw [h.1]
    have ht := take4_drop_patched (blk := blk) (pl := pl) hal hlen
    have e1 : P.code[off + k]'(by omega) =
        (((blk.patched pl).drop off).take 4)[k]'(by
          simp [List.length_take, List.length_drop, patched_length _ _ hP.len_aligned]; omega) := by
      simp only [List.getElem_take, List.getElem_drop]; simp [hcode]
    rw [e1]
    simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
    have : 8 * k + i < 32 := by omega
    simp [hi, this]; omega
  have hpc : (pl.base + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : (pl.base.toNat + off) % 2 ^ 64 = pl.base.toNat + off := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have r0 := rd 0 (by omega)
  have r1 := rd 1 (by omega)
  have r2 := rd 2 (by omega)
  have r3 := rd 3 (by omega)
  simp only [Program.fetchMem, hhook, Option.isSome_none, Bool.false_eq_true, if_false, hpc,
    ne_eq, not_true_eq_false]
  generalize ha : pl.base + BitVec.ofNat 64 off = a at *
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at r0 r1 r2 r3
  have hx : m.canExec a 4 = true := by
    simp only [Memory.canExec, Memory.allPerm, BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.add_zero] at r0
    simp [r0.2, r1.2, r2.2, r3.2, Perm.rx]
  simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
  congr 1
  simp only [Memory.read32]
  rw [r0.1, r1.1, r2.1, r3.1]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

/-- Block `k`'s placement under `mpl`. -/
abbrev bpl (mpl : MultiPlacement) (k : Nat) : Placement := x25519CliMultiLib.blockPlacement mpl k

theorem fetch_block {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {k : Nat}
    {blk : CodeBlock} (hk : k < 19) (hblk : x25519CliBlocks.getD k { code := [] } = blk)
    {m : Memory} (hCL : (prog mpl k).CodeLoaded m) {off : Nat} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ blk.code.length) :
    (prog mpl k).fetchMem m (mpl.base k + BitVec.ofNat 64 off) =
      decode (blk.patchedWord (bpl mpl k) off) := by
  have h19 : x25519CliMultiLib.blocks.length = 19 := rfl
  have hk' : k < x25519CliMultiLib.blocks.length := by rw [h19]; exact hk
  have hPk : blk.Placeable (bpl mpl k) := by
    have := hP.blocks_ok k hk'
    have e : x25519CliMultiLib.blocks[k]'hk' = blk := by
      rw [← hblk, List.getD_eq_getElem?_getD]
      have hk2 : k < x25519CliBlocks.length := hk'
      rw [List.getElem?_eq_getElem hk2]; rfl
    rwa [e] at this
  exact fetch_word_gen (P := prog mpl k) (blk := blk) (pl := bpl mpl k) rfl
    (by show (x25519CliMultiLib.blockLib k).text.patched _ = _
        simp only [MultiPlacedLib.blockLib]; rw [show x25519CliMultiLib.blocks = x25519CliBlocks from rfl, hblk])
    (hook_none mpl k) hPk hCL hal hlen

/-- An unrelocated word: its decoding. -/
theorem patchedWord_plain (blk : CodeBlock) (pl : Placement) {off : Nat}
    (h : blk.relocAt? off = none) : blk.patchedWord pl off = blk.wordAt off := by
  simp [CodeBlock.patchedWord, h]

theorem fetch_plain {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {k : Nat}
    {blk : CodeBlock} (hk : k < 19) (hblk : x25519CliBlocks.getD k { code := [] } = blk)
    {m : Memory} (hCL : (prog mpl k).CodeLoaded m) {off : Nat} {i : Instr} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ blk.code.length) (hr : blk.relocAt? off = none)
    (hd : decode (blk.wordAt off) = some i) :
    (prog mpl k).fetchMem m (mpl.base k + BitVec.ofNat 64 off) = some i := by
  rw [fetch_block hP hk hblk hCL hal hlen, patchedWord_plain _ _ hr, hd]

end X25519Dalek.Edw
end

section
/-! # Byte loads and stores under a separation-logic frame

From `m ⊨ (a ↦ₛ bs) ∗ G`: the bytes are readable and writable in `m` with the listed values, and
a byte store inside them gives `(a ↦ₛ bs.set i v) ∗ G` for the updated memory. The same for
read-only bytes `a ↦ᵣ bs`, which are readable. -/

namespace X25519Dalek.Edw

open Arm64 Arm64.Obj Arm64.SepProp

/-! ## One owned byte -/

theorem cell_rw_of_matches {h : Heap} {m : Memory} (hm : h.Matches m) {a : BitVec 64}
    {b : BitVec 8} (hc : h.phys a = some (.rw b)) :
    m.read8 a = b ∧ m.perm a = some Perm.rw ∧ m.isLazyFree a = false := hm.1 a _ hc

/-- An owned byte under a frame: its value and permission. -/
theorem sat_pointsTo8 {a : BitVec 64} {b : BitVec 8} {G : SepProp} {m : Memory}
    (hs : m ⊨ (a ↦₈ b) ∗ G) :
    m.read8 a = b ∧ m.perm a = some Perm.rw ∧ m.isLazyFree a = false := by
  obtain ⟨h, hh, hm⟩ := satisfies_iff.mp hs
  obtain ⟨h1, h2, _, rfl, h1e, _⟩ := holds_sepConj_iff.mp hh
  rw [holds_pointsTo8_iff] at h1e; subst h1e
  have hc : (Heap.union (Heap.singleton a b) h2).phys a = some (.rw b) := by
    simp [Heap.union, Heap.singleton]
  exact cell_rw_of_matches hm hc

/-- A store to an owned byte under a frame. -/
theorem sat_write8 {a : BitVec 64} {b v : BitVec 8} {G : SepProp} {m : Memory}
    (hs : m ⊨ (a ↦₈ b) ∗ G) : m.write8 a v ⊨ (a ↦₈ v) ∗ G := by
  obtain ⟨h, hh, hm⟩ := satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1e, h2G⟩ := holds_sepConj_iff.mp hh
  rw [holds_pointsTo8_iff] at h1e; subst h1e
  have ha : (Heap.union (Heap.singleton a b) h2).phys a = some (.rw b) := by
    simp [Heap.union, Heap.singleton]
  obtain ⟨_, hpa, _⟩ := cell_rw_of_matches hm ha
  have h2a : h2.phys a = none := by
    rcases hd.1 a with h | h | ⟨c, h, _⟩
    · simp [Heap.singleton] at h
    · exact h
    · simp [Heap.singleton] at h
  have hd' : (Heap.singleton a v).Disjoint h2 := by
    refine ⟨fun x => ?_, hd.2.1, hd.2.2.1, ?_, hd.2.2.2.2⟩
    · by_cases hx : x = a
      · subst hx; exact Or.inr (Or.inl h2a)
      · exact Or.inl (by simp [Heap.singleton, hx])
    · intro γ k oa w hc
      rcases hc with ⟨h1, _⟩ | ⟨_, h1⟩
      · simp [Heap.singleton] at h1
      · simp [Heap.singleton] at h1
  have hm2 := Heap.Matches.of_union_right hd hm
  refine satisfies_iff.mpr ⟨(Heap.singleton a v).union h2,
    holds_sepConj_iff.mpr ⟨_, _, hd', rfl, rfl, h2G⟩, ?_⟩
  refine ⟨fun x c hx => ?_, ?_, fun x hx => ?_⟩
  · by_cases hxa : x = a
    · subst hxa
      simp [Heap.union, Heap.singleton] at hx; subst hx
      refine ⟨by simp, ?_, ?_⟩
      · rw [Memory.perm_write8_apply]; exact hpa
      · simp [Memory.isLazyFree_write8]
    · have hx2 : h2.phys x = some c := by simpa [Heap.union, Heap.singleton, hxa] using hx
      have hc := hm2.1 x c hx2
      have e1 : (m.write8 a v).read8 x = m.read8 x := by simp [Memory.read8_write8, hxa]
      have e2 : (m.write8 a v).perm x = m.perm x := by
        rw [Memory.perm_write8_apply]
      have e3 : (m.write8 a v).isLazyFree x = m.isLazyFree x := by
        simp [Memory.isLazyFree_write8, hxa]
      cases c <;> simp only [e1, e2, e3] <;> exact hc
  · exact Heap.GhostValid.union (Heap.GhostValid.of_phys (h := Heap.singleton a v) rfl rfl)
      hm2.2.1
  · have hx' : h2.mapped x = true := by simpa [Heap.union, Heap.singleton] using hx
    obtain ⟨h1, h2'⟩ := hm2.2.2 x hx'
    refine ⟨?_, ?_⟩
    · rw [Memory.perm_write8_apply]; exact h1
    · rw [Memory.isAnon_write8_apply]; exact h2'

/-! ## Owned byte lists -/

theorem pointsToBytes_cons_assoc (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8))
    (G : SepProp) : ((a ↦ₛ (b :: bs)) ∗ G) = ((a ↦₈ b) ∗ ((a + 1#64) ↦ₛ bs) ∗ G) := by
  rw [pointsToBytes_cons_def, sepConj_assoc]

theorem sat_bytes_read : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (G : SepProp) (m : Memory),
    (m ⊨ (a ↦ₛ bs) ∗ G) → ∀ i (hi : i < bs.length),
      m.read8 (a + BitVec.ofNat 64 i) = bs[i] ∧ m.perm (a + BitVec.ofNat 64 i) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 i) = false
  | [], _, _, _, _, i, hi => by simp at hi
  | b :: bs, a, G, m, hs, 0, _ => by
    rw [pointsToBytes_cons_assoc] at hs
    simpa using sat_pointsTo8 hs
  | b :: bs, a, G, m, hs, i + 1, hi => by
    rw [pointsToBytes_cons_assoc, sepConj_left_comm] at hs
    have := sat_bytes_read bs (a + 1#64) _ m hs i (by simpa using hi)
    rw [show a + BitVec.ofNat 64 (i + 1) = a + 1#64 + BitVec.ofNat 64 i by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
    simpa using this

theorem sat_bytes_write : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (G : SepProp) (m : Memory),
    (m ⊨ (a ↦ₛ bs) ∗ G) → ∀ i, i < bs.length → ∀ v : BitVec 8,
      (m.write8 (a + BitVec.ofNat 64 i) v ⊨ (a ↦ₛ bs.set i v) ∗ G)
  | [], _, _, _, _, i, hi, _ => by simp at hi
  | b :: bs, a, G, m, hs, 0, _, v => by
    rw [pointsToBytes_cons_assoc] at hs
    rw [List.set_cons_zero, pointsToBytes_cons_assoc]
    simpa using sat_write8 hs
  | b :: bs, a, G, m, hs, i + 1, hi, v => by
    rw [pointsToBytes_cons_assoc, sepConj_left_comm] at hs
    have := sat_bytes_write bs (a + 1#64) _ m hs i (by simpa using hi) v
    rw [List.set_cons_succ, pointsToBytes_cons_assoc, sepConj_left_comm]
    rw [show a + BitVec.ofNat 64 (i + 1) = a + 1#64 + BitVec.ofNat 64 i by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
    exact this

/-! ## Read-only byte lists -/

/-! ## Permission checks of loads and stores -/

theorem canRead1 {m : Memory} {a : BitVec 64} (hr : (m.perm a).r = true)
    (hl : m.isLazyFree a = false) : m.canRead a 1 = true := by
  simp [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree, hr, hl]

theorem canWrite1 {m : Memory} {a : BitVec 64} (hp : m.perm a = some Perm.rw) :
    m.canWrite a 1 = true := by
  simp [Memory.canWrite, Memory.allPerm, hp, Perm.rw]

theorem perm_rw_r {m : Memory} {a : BitVec 64} (hp : m.perm a = some Perm.rw) :
    (m.perm a).r = true := by
  simp [hp, Perm.rw]

end X25519Dalek.Edw
end

section
/-! # Decoding relocated words: `ADRP`/`ADD`/`ADR` (from the zlib CRC-32 mission's proofs,
`ZlibCrc32.Small.RelocBase`/`RelocTab`) and `B` (jump26). -/

namespace X25519Dalek.Edw

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_adr_class (w : BitVec 32) (hK : w &&& 0x1f000000#32 = 0x10000000#32) :
    decode w = some (.adr (w.getLsbD 31) (Reg.fromZRBits (w.extractLsb' 0 5))
      (if w.getLsbD 31 then ((w.extractLsb' 5 19 ++ w.extractLsb' 29 2).signExtend 64) <<< 12
       else (w.extractLsb' 5 19 ++ w.extractLsb' 29 2).signExtend 64)) := by
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide), hK]
  simp

theorem decode_addimm_class (w : BitVec 32) (hK : w &&& 0x1f800000#32 = 0x11000000#32) :
    decode w = some (
      let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
      .addSubImm (RegWidth.ofBool (w.getLsbD 31)) op
        (if op.setsFlags then Reg.fromZRBits (w.extractLsb' 0 5) else Reg.fromSPBits (w.extractLsb' 0 5))
        (Reg.fromSPBits (w.extractLsb' 5 5)) (w.extractLsb' 10 12) (w.getLsbD 22)) := by
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide),
    beq_false_of_mask hK (C := 0x10000000#32) (M := 0x1f000000#32) (by decide), hK]
  simp

theorem hi_bits32 (D : BitVec 64) (h1 : -(2^32:Int) ≤ D.toInt) (h2 : D.toInt < 2^32) :
    ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem hi_bits20 (D : BitVec 64) (h1 : -(2^20:Int) ≤ D.toInt) (h2 : D.toInt < 2^20) :
    ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem pageOf_eq (x : BitVec 64) : pageOf x = (x >>> 12) <<< 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pageOf, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem pageOf_toNat (x : BitVec 64) : (pageOf x).toNat = x.toNat / 4096 * 4096 := by
  rw [pageOf_eq]; simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]; omega

theorem lo_bits (a b : BitVec 64) : ∀ i, i < 12 → (pageOf a - pageOf b).getLsbD i = false := by
  intro i hi
  have h : (pageOf a - pageOf b).toNat % 4096 = 0 := by
    rw [BitVec.toNat_sub, pageOf_toNat, pageOf_toNat]
    have := a.isLt; have := b.isLt; omega
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize (pageOf a - pageOf b).toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

theorem page_add_lo (T : BitVec 64) : pageOf T + (T.extractLsb' 0 12).setWidth 64 = T := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, pageOf_toNat]
  simp [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  have := T.isLt; omega


theorem decode_nop : decode nopWord = some .nop := by decide


theorem awc_add' (x y : BitVec 64) :
    BitVec.truncate 64 (0#65 + (BitVec.zeroExtend 65 y + BitVec.zeroExtend 65 x)) = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_setWidth]
  omega


section words
variable (D : BitVec 64)

theorem wA_maskTab : adrpWordOff 0x90000000#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_31Tab : (adrpWordOff 0x90000000#32 D).getLsbD 31 = true := by
  simp [adrpWordOff]

theorem wA_rdTab : (adrpWordOff 0x90000000#32 D).extractLsb' 0 5 = 0#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_offTab (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff 0x90000000#32 D).extractLsb' 5 19 ++
      (adrpWordOff 0x90000000#32 D).extractLsb' 29 2).signExtend 64 <<< 12 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wC_maskTab : adrWordOff 0x10000000#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_31Tab : (adrWordOff 0x10000000#32 D).getLsbD 31 = false := by
  simp [adrWordOff]

theorem wC_rdTab : (adrWordOff 0x10000000#32 D).extractLsb' 0 5 = 0#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_offTab (hhi : ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20) :
    ((adrWordOff 0x10000000#32 D).extractLsb' 5 19 ++
      (adrWordOff 0x10000000#32 D).extractLsb' 29 2).signExtend 64 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | rfl | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wB_maskTab : lo12Word 0 0x91000000#32 D &&& 0x1f800000#32 = 0x11000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wB_bitsTab : (lo12Word 0 0x91000000#32 D).getLsbD 31 = true ∧
    (lo12Word 0 0x91000000#32 D).getLsbD 30 = false ∧
    (lo12Word 0 0x91000000#32 D).getLsbD 29 = false ∧
    (lo12Word 0 0x91000000#32 D).getLsbD 22 = false := by
  simp [lo12Word]

theorem wB_rdTab : (lo12Word 0 0x91000000#32 D).extractLsb' 0 5 = 0#5 ∧
    (lo12Word 0 0x91000000#32 D).extractLsb' 5 5 = 0#5 := by
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem wB_immTab : (lo12Word 0 0x91000000#32 D).extractLsb' 10 12 = D.extractLsb' 0 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

end words

theorem decode_ATab {P T : BitVec 64} (hr : AdrpInRange P T) :
    decode (adrpWord 0x90000000#32 P T) = some (.adr true (.gpr 0#5) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (wA_maskTab _), wA_31Tab, wA_rdTab,
    wA_offTab _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rfl

theorem decode_CTab {P T : BitVec 64} (hr : AdrInRange P T) :
    decode (adrWord (adrTemplate 0x91000000#32) P T) = some (.adr false (.gpr 0#5) (T - P)) := by
  rw [adrWord, show adrTemplate 0x91000000#32 = 0x10000000#32 by decide,
    decode_adr_class _ (wC_maskTab _), wC_31Tab, wC_rdTab, if_neg (by decide), wC_offTab _ (hi_bits20 _ hr.1 hr.2)]
  rfl

theorem decode_BTab (T : BitVec 64) :
    decode (lo12Word 0 0x91000000#32 T) =
      some (.addSubImm .W64 .ADD (.gpr 0#5) (.gpr 0#5) (T.extractLsb' 0 12) false) := by
  obtain ⟨b31, b30, b29, b22⟩ := wB_bitsTab T
  rw [decode_addimm_class _ (wB_maskTab _), b31, b30, b29, b22, wB_rdTab T |>.1, wB_rdTab T |>.2, wB_immTab]
  rfl


/-! ## `B` / `BL` -/

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

section bw
variable (D : BitVec 64)

theorem wJ_mask : ((0x14000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32))
    &&& 0x7c000000#32 = 0x14000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  interval_cases i <;> simp

theorem wJ_31 : ((0x14000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32)).getLsbD 31
    = false := by
  simp

theorem wJ_off (hlo : ∀ i, i < 2 → D.getLsbD i = false)
    (hhi : ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27) :
    ((((0x14000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32)).extractLsb' 0 26).signExtend 64)
      <<< 2 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.msb_eq_getLsbD_last]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm | rfl

end bw

/-- A relocated `B` (template `0x14000000`) branches to its target. -/
theorem decode_branchWord_b {P T : BitVec 64} (hr : BranchInRange P T) :
    decode (branchWord 0x14000000#32 P T) = some (.b (T - P)) := by
  rw [branchWord, decode_b_class _ (wJ_mask _), wJ_31, if_neg (by decide),
    wJ_off _ (lo_bits2 _ hr.1) (hi_bits27 _ hr.2.1 hr.2.2)]

end X25519Dalek.Edw
end

section
/-! # The basepoint-table bound `2 ^ 52` gives the bound `2 ^ 53` of `mul_base`'s contract -/

namespace X25519Dalek.Edw

open X25519Dalek

theorem fe51LimbsBoundedAt_mono {bs : List (BitVec 8)} {off b1 b2 : Nat}
    (h : fe51LimbsBoundedAt bs off b1) (hb : b1 ≤ b2) : fe51LimbsBoundedAt bs off b2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem fe51AffineNielsBoundedAt_mono {bs : List (BitVec 8)} {off b1 b2 : Nat}
    (h : fe51AffineNielsBoundedAt bs off b1) (hb : b1 ≤ b2) : fe51AffineNielsBoundedAt bs off b2 :=
  ⟨fe51LimbsBoundedAt_mono h.1 hb, fe51LimbsBoundedAt_mono h.2.1 hb, fe51LimbsBoundedAt_mono h.2.2 hb⟩

theorem table_bounded : fe51BasepointTable32Bounded ed25519BasepointTableBytes (2 ^ 53) := by
  obtain ⟨hl, h⟩ := X25519Dalek.ed25519BasepointTable_bounded_v2
  refine ⟨hl, fun i hi => ?_⟩
  obtain ⟨l, e0, e1, e2, e3, e4, e5, e6, e7⟩ := h i hi
  have hb : (2 ^ 52 : Nat) ≤ 2 ^ 53 := by norm_num
  exact ⟨l, fe51AffineNielsBoundedAt_mono e0 hb, fe51AffineNielsBoundedAt_mono e1 hb,
    fe51AffineNielsBoundedAt_mono e2 hb, fe51AffineNielsBoundedAt_mono e3 hb,
    fe51AffineNielsBoundedAt_mono e4 hb, fe51AffineNielsBoundedAt_mono e5 hb,
    fe51AffineNielsBoundedAt_mono e6 hb, fe51AffineNielsBoundedAt_mono e7 hb⟩

end X25519Dalek.Edw
end

section
namespace X25519Dalek.Edw

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem blk14_eq : x25519CliBlocks.getD 14 { code := [] } = x25519CliBlk14 := rfl


abbrev symTAB : String :=
  "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN"
abbrev symMB : String :=
  "<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base"

theorem lookup_TAB : lookupBlockSym symTAB x25519CliMultiLib.blocks = none := by decide
theorem lookup_MB : lookupBlockSym symMB x25519CliMultiLib.blocks = some (13, 0) := by decide

theorem resolve_TAB (mpl : MultiPlacement) : x25519CliMultiLib.resolve mpl symTAB = mpl.ρ symTAB := by
  simp [MultiPlacedLib.resolve, lookup_TAB]

theorem resolve_MB (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl symMB = mpl.base 13 + BitVec.ofNat 64 0 := by
  simp [MultiPlacedLib.resolve, lookup_MB]

theorem target14 (mpl : MultiPlacement) (o : Nat) (k : RelocKind) (sym : String)
    (hlk : lookup sym x25519CliBlk14.symbols = none) :
    x25519CliBlk14.target (bpl mpl 14) { off := o, kind := k, sym := sym } =
      x25519CliMultiLib.resolve mpl sym := by
  simp [CodeBlock.target, CodeBlock.resolve, hlk, addSignedAddr, MultiPlacedLib.blockPlacement]

theorem pw14_16 (mpl : MultiPlacement) :
    x25519CliBlk14.patchedWord (bpl mpl 14) 16 =
      if mpl.relax 14 16 then nopWord
      else adrpWord 0x90000000#32 (mpl.base 14 + BitVec.ofNat 64 16) (mpl.ρ symTAB) := by
  have hr : x25519CliBlk14.relocAt? 16 = some { off := 16, kind := .adrpHi21, sym := symTAB } := rfl
  have h1 : x25519CliBlk14.relaxableAt 16 = true := by decide
  have hw : x25519CliBlk14.wordAt 16 = 0x90000000#32 := by decide
  have hlk : lookup symTAB x25519CliBlk14.symbols = none := by decide
  have hrel : (bpl mpl 14).relax = mpl.relax 14 := rfl
  have hbase : (bpl mpl 14).base = mpl.base 14 := rfl
  have h12 : x25519CliBlk14.relaxableAt 12 = false := by decide
  have hT := target14 mpl 16 .adrpHi21 symTAB hlk
  rw [resolve_TAB] at hT
  cases h : mpl.relax 14 16 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h12, hr, hw, hrel, hbase,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, hT,
      patchRelocWord, RelocKind.isGotOrTlsIe]

theorem pw14_20 (mpl : MultiPlacement) :
    x25519CliBlk14.patchedWord (bpl mpl 14) 20 =
      if mpl.relax 14 16 then
        adrWord (adrTemplate 0x91000000#32) (mpl.base 14 + BitVec.ofNat 64 20) (mpl.ρ symTAB)
      else lo12Word 0 0x91000000#32 (mpl.ρ symTAB) := by
  have hr : x25519CliBlk14.relocAt? 20 = some { off := 20, kind := .addLo12, sym := symTAB } := rfl
  have h1 : x25519CliBlk14.relaxableAt 16 = true := by decide
  have h2 : x25519CliBlk14.relaxableAt 20 = false := by decide
  have hw : x25519CliBlk14.wordAt 20 = 0x91000000#32 := by decide
  have hlk : lookup symTAB x25519CliBlk14.symbols = none := by decide
  have hrel : (bpl mpl 14).relax = mpl.relax 14 := rfl
  have hbase : (bpl mpl 14).base = mpl.base 14 := rfl
  have hT := target14 mpl 20 .addLo12 symTAB hlk
  rw [resolve_TAB] at hT
  cases h : mpl.relax 14 16 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, hrel, hbase,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, hT,
      patchRelocWord, RelocKind.isGotOrTlsIe]

theorem pw14_40 (mpl : MultiPlacement) :
    x25519CliBlk14.patchedWord (bpl mpl 14) 40 =
      branchWord 0x14000000#32 (mpl.base 14 + BitVec.ofNat 64 40) (mpl.base 13 + BitVec.ofNat 64 0) := by
  have hr : x25519CliBlk14.relocAt? 40 = some { off := 40, kind := .jump26, sym := symMB } := rfl
  have h1 : x25519CliBlk14.relaxableAt 40 = false := by decide
  have h2 : x25519CliBlk14.relaxableAt 36 = false := by decide
  have hw : x25519CliBlk14.wordAt 40 = 0x14000000#32 := by decide
  have hlk : lookup symMB x25519CliBlk14.symbols = none := by decide
  have hbase : (bpl mpl 14).base = mpl.base 14 := rfl
  have hT := target14 mpl 40 .jump26 symMB hlk
  rw [resolve_MB] at hT
  have hwk : x25519CliBlk14.weakRefs = [] := rfl
  have hb2b : x25519CliBlk14.b2bNext? { off := 40, kind := .jump26, sym := symMB } = none := by
    simp [CodeBlock.b2bNext?, hlk]
  simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h1, h2, hr, hw, hbase,
      CodeBlock.relocTarget, hb2b, CodeBlock.undefWeakBranch, hwk, hT,
      patchRelocWord, RelocKind.isGotOrTlsIe]

theorem placeable14 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) :
    x25519CliBlk14.Placeable (bpl mpl 14) := hP.blocks_ok 14 (by decide)

theorem relocTarget14 (mpl : MultiPlacement) (o : Nat) (k : RelocKind) (sym : String)
    (hlk : lookup sym x25519CliBlk14.symbols = none) :
    x25519CliBlk14.relocTarget (bpl mpl 14) o { off := o, kind := k, sym := sym } =
      x25519CliMultiLib.resolve mpl sym := by
  have hb2b : x25519CliBlk14.b2bNext? { off := o, kind := k, sym := sym } = none := by
    simp [CodeBlock.b2bNext?, hlk]
  simp only [CodeBlock.relocTarget, hb2b]
  split <;> simp_all [target14]

theorem range14_16 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) :
    AdrpInRange (mpl.base 14 + BitVec.ofNat 64 16) (mpl.ρ symTAB) := by
  have hmem : ({ off := 16, kind := .adrpHi21, sym := symTAB } : RelocEntry) ∈ x25519CliBlk14.relocs := by
    decide
  have h := ((placeable14 hP).relocs_ok _ hmem).2.2
  rw [relocTarget14 mpl 16 .adrpHi21 symTAB (by decide), resolve_TAB] at h
  exact h

theorem range14_20 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hrel : mpl.relax 14 16 = true) :
    AdrInRange (mpl.base 14 + BitVec.ofNat 64 20) (mpl.ρ symTAB) := by
  have h1 : x25519CliBlk14.relaxableAt 16 = true := by decide
  have hr : x25519CliBlk14.relocAt? (16 + 4) = some { off := 20, kind := .addLo12, sym := symTAB } := rfl
  have h := (placeable14 hP).relaxed_ok 16 _ (by simp [CodeBlock.relaxedAt, h1]; exact hrel) hr
  rwa [target14 mpl 20 .addLo12 symTAB (by decide), resolve_TAB] at h

theorem range14_40 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) :
    BranchInRange (mpl.base 14 + BitVec.ofNat 64 40) (mpl.base 13 + BitVec.ofNat 64 0) := by
  have hmem : ({ off := 40, kind := .jump26, sym := symMB } : RelocEntry) ∈ x25519CliBlk14.relocs := by
    decide
  have h := ((placeable14 hP).relocs_ok _ hmem).2.2
  rw [relocTarget14 mpl 40 .jump26 symMB (by decide), resolve_MB] at h
  exact h

section fetch14
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m : Memory}
  (hCL : (prog mpl 14).CodeLoaded m)
include hP hCL

theorem f14_0 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 0) =
    some (.ldr .W32 .B8 false (.gpr 11#5) (.Offset (.gpr 0#5) 31#64)) :=
  fetch_plain hP (by decide) blk14_eq hCL (by decide) (by decide) (by decide) (by decide +kernel)

theorem f14_4 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 4) =
    some (.moveWide .W32 .MOVZ (.gpr 9#5) 0x0040#16 0) :=
  fetch_plain hP (by decide) blk14_eq hCL (by decide) (by decide) (by decide) (by decide +kernel)

theorem f14_8 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 8) =
    some (.ldr .W32 .B8 false (.gpr 10#5) (.Offset (.gpr 0#5) 0#64)) :=
  fetch_plain hP (by decide) blk14_eq hCL (by decide) (by decide) (by decide) (by decide +kernel)

theorem f14_12 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 12) =
    some (.logicalShift .W64 .ORR (.gpr 1#5) .xzr (.gpr 0#5) .LSL 0) :=
  fetch_plain hP (by decide) blk14_eq hCL (by decide) (by decide) (by decide) (by decide +kernel)

theorem f14_24 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 24) =
    some (.bitfield .W32 .BFM (.gpr 9#5) (.gpr 11#5) 0 5) :=
  fetch_plain hP (by decide) blk14_eq hCL (by decide) (by decide) (by decide) (by decide +kernel)

theorem f14_28 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 28) =
    some (.logicalImm .W32 .AND (.gpr 10#5) (.gpr 10#5) 0x000000f8000000f8#64) :=
  fetch_plain hP (by decide) blk14_eq hCL (by decide) (by decide) (by decide) (by decide +kernel)

theorem f14_32 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 32) =
    some (.str .B8 (.gpr 10#5) (.Offset (.gpr 1#5) 0#64)) :=
  fetch_plain hP (by decide) blk14_eq hCL (by decide) (by decide) (by decide) (by decide +kernel)

theorem f14_36 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 36) =
    some (.str .B8 (.gpr 9#5) (.Offset (.gpr 1#5) 31#64)) :=
  fetch_plain hP (by decide) blk14_eq hCL (by decide) (by decide) (by decide) (by decide +kernel)

theorem f14_16 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 16) =
    decode (if mpl.relax 14 16 then nopWord
      else adrpWord 0x90000000#32 (mpl.base 14 + BitVec.ofNat 64 16) (mpl.ρ symTAB)) := by
  rw [fetch_block hP (by decide) blk14_eq hCL (by decide) (by decide), pw14_16]

theorem f14_20 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 20) =
    decode (if mpl.relax 14 16 then
        adrWord (adrTemplate 0x91000000#32) (mpl.base 14 + BitVec.ofNat 64 20) (mpl.ρ symTAB)
      else lo12Word 0 0x91000000#32 (mpl.ρ symTAB)) := by
  rw [fetch_block hP (by decide) blk14_eq hCL (by decide) (by decide), pw14_20]

theorem f14_40 : (prog mpl 14).fetchMem m (mpl.base 14 + BitVec.ofNat 64 40) =
    some (.b (mpl.base 13 + BitVec.ofNat 64 0 - (mpl.base 14 + BitVec.ofNat 64 40))) := by
  rw [fetch_block hP (by decide) blk14_eq hCL (by decide) (by decide), pw14_40,
    decode_branchWord_b (range14_40 hP)]

end fetch14

end X25519Dalek.Edw
end

section
/-! # Abstract machine states

`mkS s0 pc r ps m` is the entry state `s0` with the general-purpose register file replaced by `r`,
and `pc`, the flags and memory replaced; every other field (`sp`, vector registers, status, ...)
is `s0`'s. After the zlib CRC-32 mission's `mkS`, with memory added. -/

namespace X25519Dalek.Edw

open Arm64 Arm64.Obj

def mkS (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) :
    State :=
  { s0 with regs := ⟨r⟩, pc := pc, pstate := ps, mem := m }

section lemmas
variable (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory)

@[simp] theorem mkS_mem : (mkS s0 pc r ps m).mem = m := rfl
@[simp] theorem mkS_pc : (mkS s0 pc r ps m).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 pc r ps m).sp = s0.sp := rfl
@[simp] theorem mkS_status : (mkS s0 pc r ps m).status = s0.status := rfl
@[simp] theorem mkS_pstate : (mkS s0 pc r ps m).pstate = ps := rfl
@[simp] theorem mkS_vregs : (mkS s0 pc r ps m).vregs = s0.vregs := rfl
@[simp] theorem mkS_spAligned : (mkS s0 pc r ps m).spAligned = s0.spAligned := rfl

@[simp] theorem rd_gpr (i : BitVec 5) :
    (mkS s0 pc r ps m).readReg64 (.gpr i) = if i = 31#5 then 0#64 else r i := by
  simp [State.readReg64, RegFile.read, mkS]

@[simp] theorem rd_xzr : (mkS s0 pc r ps m).readReg64 .xzr = 0#64 := rfl
@[simp] theorem rd_sp : (mkS s0 pc r ps m).readReg64 .sp = s0.sp := rfl

theorem wr_gpr (i : BitVec 5) (v : BitVec 64) (hi : i ≠ 31#5) :
    (mkS s0 pc r ps m).writeReg64 (.gpr i) v = mkS s0 pc (Function.update r i v) ps m := by
  simp only [mkS, State.writeReg64, RegFile.write, beq_iff_eq, hi, if_false]
  congr 2; funext k; simp [Function.update_apply]

@[simp] theorem wr_gpr_ite (i : BitVec 5) (v : BitVec 64) :
    (mkS s0 pc r ps m).writeReg64 (.gpr i) v =
      if i = 31#5 then mkS s0 pc r ps m else mkS s0 pc (Function.update r i v) ps m := by
  split
  · subst_vars; rfl
  · exact wr_gpr s0 pc r ps m i v ‹_›

@[simp] theorem wr_xzr (v : BitVec 64) : (mkS s0 pc r ps m).writeReg64 .xzr v = mkS s0 pc r ps m :=
  rfl
@[simp] theorem mkS_advancePC : (mkS s0 pc r ps m).advancePC = mkS s0 (pc + 4#64) r ps m := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 pc r ps m).setPC q = mkS s0 q r ps m := rfl
@[simp] theorem mkS_setPState (q : PState) : (mkS s0 pc r ps m).setPState q = mkS s0 pc r q m := rfl
@[simp] theorem mkS_setMem (q : Memory) : (mkS s0 pc r ps m).setMem q = mkS s0 pc r ps q := rfl

end lemmas

@[simp] theorem stackFrame_mkS (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (ps : PState)
    (m : Memory) (n : Nat) : stackFrame (mkS s0 pc r ps m) n = stackFrame s0 n := rfl

/-- `CalleeSavedPreserved` for an abstract state whose callee-saved registers are `s0`'s. -/
theorem calleeSaved_mkS {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {ps : PState}
    {m : Memory} (h : ∀ i : BitVec 5, 19 ≤ i.toNat → i.toNat ≤ 29 → r i = s0.regs.regs i) :
    CalleeSavedPreserved s0 (mkS s0 pc r ps m) := by
  simp only [CalleeSavedPreserved, calleeSavedVRegs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp [State.readReg64, RegFile.read, mkS] <;> exact h _ (by decide) (by decide)

end X25519Dalek.Edw
end

section
namespace X25519Dalek.Edw

set_option maxRecDepth 100000

open Arm64 Arm64.Obj Arm64.SepProp

@[simp] theorem pc_add4 (b : BitVec 64) (k : Nat) :
    b + BitVec.ofNat 64 k + 4#64 = b + BitVec.ofNat 64 (k + 4) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp

def Reach (P : Program) (s : State) (Q : State → Prop) : Prop := ∃ sf, Steps P s sf ∧ Q sf

theorem reach_step14 {mpl : MultiPlacement} {s : State} {k : Nat} {i : Instr} {Q : State → Prop}
    (hrun : s.status = .Running) (hpc : s.pc = mpl.base 14 + BitVec.ofNat 64 k)
    (hf : (prog mpl 14).fetchMem s.mem (mpl.base 14 + BitVec.ofNat 64 k) = some i)
    (h : Reach (prog mpl 14) ((prog mpl 14).evalInst i s) Q) : Reach (prog mpl 14) s Q := by
  rw [← hpc] at hf
  obtain ⟨sf, hs, hq⟩ := h
  exact ⟨sf, Steps.step (Step.exec hrun hf) hs, hq⟩

theorem pair14 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s0 : State}
    {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory} {Q : State → Prop}
    (hCL : (prog mpl 14).CodeLoaded m) (hrun : s0.status = .Running)
    (h : Reach (prog mpl 14) (mkS s0 (mpl.base 14 + BitVec.ofNat 64 24)
      (Function.update r 0#5 (mpl.ρ symTAB)) ps m) Q) :
    Reach (prog mpl 14) (mkS s0 (mpl.base 14 + BitVec.ofNat 64 16) r ps m) Q := by
  have hf1 := f14_16 hP hCL
  have hf2 := f14_20 hP hCL
  have hrd : (0#5 : BitVec 5) ≠ 31#5 := by decide
  cases hrel : mpl.relax 14 16
  · simp only [hrel, Bool.false_eq_true, if_false] at hf1 hf2
    rw [decode_ATab (range14_16 hP)] at hf1
    rw [decode_BTab] at hf2
    refine reach_step14 hrun rfl hf1 ?_
    have e1 : (prog mpl 14).evalInst
        (.adr true (.gpr 0#5) (pageOf (mpl.ρ symTAB) - pageOf (mpl.base 14 + BitVec.ofNat 64 16)))
        (mkS s0 (mpl.base 14 + BitVec.ofNat 64 16) r ps m) =
        mkS s0 (mpl.base 14 + BitVec.ofNat 64 20) (Function.update r 0#5 (pageOf (mpl.ρ symTAB))) ps m := by
      show State.advancePC (State.writeReg64 _ _ _) = _
      rw [wr_gpr _ _ _ _ _ _ _ hrd, mkS_advancePC, pc_add4]
      congr 2
      have e : ∀ a b : BitVec 64, a + (b - a) = b := by intro a b; bv_omega
      simp only [mkS_pc, if_true]
      rw [show (mpl.base 14 + BitVec.ofNat 64 16) &&& 0xfffffffffffff000#64 =
        pageOf (mpl.base 14 + BitVec.ofNat 64 16) from rfl, e]
    rw [e1]
    refine reach_step14 hrun rfl hf2 ?_
    have e2 : (prog mpl 14).evalInst
        (.addSubImm .W64 .ADD (.gpr 0#5) (.gpr 0#5) ((mpl.ρ symTAB).extractLsb' 0 12) false)
        (mkS s0 (mpl.base 14 + BitVec.ofNat 64 20) (Function.update r 0#5 (pageOf (mpl.ρ symTAB))) ps m) =
        mkS s0 (mpl.base 14 + BitVec.ofNat 64 24) (Function.update r 0#5 (mpl.ρ symTAB)) ps m := by
      show State.advancePC (State.writeReg _ _ _ _) = _
      simp only [State.writeReg, State.readReg, rd_gpr, hrd, if_false, Function.update_self,
        evalAddSub, Bool.false_eq_true]
      rw [wr_gpr _ _ _ _ _ _ _ hrd, mkS_advancePC, pc_add4, Function.update_idem]
      congr 2
      rw [awc_add']
      exact page_add_lo _
    rw [e2]; exact h
  · simp only [hrel, if_true] at hf1 hf2
    rw [decode_nop] at hf1
    rw [decode_CTab (range14_20 hP hrel)] at hf2
    refine reach_step14 hrun rfl hf1 ?_
    rw [show (prog mpl 14).evalInst .nop (mkS s0 (mpl.base 14 + BitVec.ofNat 64 16) r ps m) =
      mkS s0 (mpl.base 14 + BitVec.ofNat 64 20) r ps m from by
        show State.advancePC _ = _; rw [mkS_advancePC, pc_add4]]
    refine reach_step14 hrun rfl hf2 ?_
    have e2 : (prog mpl 14).evalInst
        (.adr false (.gpr 0#5) (mpl.ρ symTAB - (mpl.base 14 + BitVec.ofNat 64 20)))
        (mkS s0 (mpl.base 14 + BitVec.ofNat 64 20) r ps m) =
        mkS s0 (mpl.base 14 + BitVec.ofNat 64 24) (Function.update r 0#5 (mpl.ρ symTAB)) ps m := by
      show State.advancePC (State.writeReg64 _ _ _) = _
      rw [wr_gpr _ _ _ _ _ _ _ hrd, mkS_advancePC, pc_add4]
      congr 2
      simp only [mkS_pc, Bool.false_eq_true, if_false]
      bv_omega
    rw [e2]; exact h

theorem clamp0_eq (b : BitVec 8) :
    BitVec.truncate 8
      (BitVec.zeroExtend 64
        (BitVec.truncate 32
          (BitVec.zeroExtend 64
            (BitVec.truncate 32
              (BitVec.zeroExtend 64
                  (BitVec.truncate 32
                    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 b)))) &&&
                1065151889656#64))))) = b &&& 0xf8#8 := by
  revert b; decide

theorem clamp31_eq (b : BitVec 8) :
    BitVec.truncate 8
      (BitVec.zeroExtend 64
        (BitVec.truncate 32
          (evalBitfield RegWidth.W32 BitfieldOp.BFM
            (BitVec.zeroExtend 64
              (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 64#16)))))
            (BitVec.zeroExtend 64
              (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 b)))))
            0 5))) = (b &&& 0x7f#8) ||| 0x40#8 := by
  revert b; decide

theorem calleeSaved_trans {s1 s2 s3 : State} (h1 : CalleeSavedPreserved s1 s2)
    (h2 : CalleeSavedPreserved s2 s3) : CalleeSavedPreserved s1 s3 := by
  simp_all [CalleeSavedPreserved]

/-- Tail call into block `j`: the callee's contract finishes the execution. -/
theorem reach_tail {mpl : MultiPlacement} {i j : Nat} {α : Type} {spec' : Spec α} {x' : α}
    {R : SepProp} {s : State} {entry : BitVec 64} {Q : State → Prop}
    (hsub : subroutine_ok (prog mpl j) entry spec')
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hpre : s.mem ⊨ spec'.pre x' s ∗ R)
    (hal : s.spAligned = true) (hCL : (prog mpl j).CodeLoaded s.mem)
    (hQ : ∀ sf, SubroutineOutcome spec' x' R s sf → Q sf) : Reach (prog mpl i) s Q := by
  obtain ⟨sf, hst, hout⟩ := hsub x' R s hpc hrun hpre hal hCL
  exact ⟨sf, steps_transfer hst, hQ sf hout⟩

theorem multi_codeLoaded_of_keepsFrozen {mpl : MultiPlacement} {m m' : Memory}
    (h : x25519CliMultiLib.CodeLoaded mpl m) (hk : m.KeepsFrozen m') :
    x25519CliMultiLib.CodeLoaded mpl m' := fun i hi => (h i hi).of_keepsFrozen hk

theorem clamp_set (bs : List (BitVec 8)) (h : bs.length = 32) :
    (bs.set 0 (bs[0] &&& 0xf8#8)).set 31 ((bs[31] &&& 0x7f#8) ||| 0x40#8) = clampScalarBytes bs := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
     b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], _ => rfl

theorem false_entails {Q : SepProp} : (⌜False⌝ : SepProp) ⊢ Q :=
  SepProp.entails_iff.mpr fun _ h => ((SepProp.holds_pure_iff.mp h).2).elim

theorem sepConj_entails_left {P Q R : SepProp} (h : P ⊢ Q) {m : Memory} (hm : m ⊨ P ∗ R) :
    m ⊨ Q ∗ R := Satisfies.mono (sepConj_mono_left h) hm

/-- The outcome of a tail-called callee entered at the abstract state `mkS s0 pc r ps m`
(callee-saved registers and `lr` those of `s0`) is an outcome of the caller entered at `s0`. -/
theorem outcome_tail {α β : Type} {spec' : Spec α} {spec : Spec β} {x' : α} {x : β} {R : SepProp}
    {s0 sf : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory}
    (hlr : r 30#5 = s0.regs.regs 30#5)
    (hcs : ∀ i : BitVec 5, 19 ≤ i.toNat → i.toNat ≤ 29 → r i = s0.regs.regs i)
    (hpost : spec'.post x' (mkS s0 pc r ps m) sf ⊢ spec.post x s0 sf)
    (hpan : spec'.onPanic x' (mkS s0 pc r ps m) sf ⊢ spec.onPanic x s0 sf)
    (hexit : ∀ c, spec'.onExit x' c (mkS s0 pc r ps m) sf ⊢ spec.onExit x c s0 sf)
    (hoom : spec'.onOom x' (mkS s0 pc r ps m) sf ⊢ spec.onOom x s0 sf)
    (h : SubroutineOutcome spec' x' R (mkS s0 pc r ps m) sf) : SubroutineOutcome spec x R s0 sf := by
  rcases h with ⟨⟨hpc, hsp, hst⟩, ⟨hsp', hcs'⟩, hp⟩ | ⟨hst, hp⟩ | ⟨c, hst, hp⟩ | ⟨hst, hp⟩
  · refine Or.inl ⟨⟨?_, hsp, hst⟩, ⟨hsp', calleeSaved_trans (calleeSaved_mkS hcs) hcs'⟩,
      sepConj_entails_left hpost hp⟩
    rw [hpc]; simp [State.readReg64, RegFile.read]; exact hlr
  · exact Or.inr (Or.inl ⟨hst, sepConj_entails_left hpan hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hst, sepConj_entails_left (hexit c) hp⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hst, sepConj_entails_left hoom hp⟩))

theorem lookup_MBC : lookupBlockSym "<curve25519_dalek::edwards::EdwardsPoint>::mul_base_clamped"
    x25519CliMultiLib.blocks = some (14, 0) := by decide


theorem mbc_core (mpl : MultiPlacement) (hP : x25519CliMultiLib.Placeable mpl)
    (hMB13 : subroutine_ok (prog mpl 13) (mpl.base 13 + BitVec.ofNat 64 0)
      (x25519CliMultiLib.withCodeLoaded mpl (edwardsBasepointTableMulBaseSpec mpl))) :
    subroutine_ok (x25519CliMultiLib.blockProgram mpl 14)
      (x25519CliMultiLib.fnAddr mpl "<curve25519_dalek::edwards::EdwardsPoint>::mul_base_clamped")
      (x25519CliMultiLib.withCodeLoaded mpl
        (ToBaseSpec.toSpec (edwardsPointMulBaseClampedSpec mpl) (mpl.base 14))) := by
  intro x R s0 hpc hrun hpre hal hCL0
  obtain ⟨out, bytes, out_bs, bs⟩ := x
  simp only [MultiPlacedLib.withCodeLoaded] at hpre
  have h1 := Satisfies.of_eq hpre (Q := ⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = bytes ∧
      out_bs.length = 160 ∧ bs.length = 32⌝ ∗ ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗
      (bytes ↦ₛ bs) ∗ ((ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗
        (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (out ↦ₛ out_bs) ∗ stackFrame s0 1680 ∗ R)) (by ac_rfl)
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
  obtain ⟨⟨hx8, hx0, hol, hbl⟩, hCL, hB⟩ := h1
  set G := (ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes) ∗
        (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (out ↦ₛ out_bs) ∗ stackFrame s0 1680 ∗ R with hG
  have hCL14 : (prog mpl 14).CodeLoaded s0.mem := hCL 14 (by decide)
  have hpc0 : s0.pc = mpl.base 14 + BitVec.ofNat 64 0 := by
    rw [hpc]; simp only [MultiPlacedLib.fnAddr]; rw [lookup_MBC]
  have hx0' : s0.readReg64 (.gpr 0#5) = bytes := hx0
  have r31 := sat_bytes_read bs bytes G s0.mem hB 31 (by omega)
  have r0 := sat_bytes_read bs bytes G s0.mem hB 0 (by omega)
  show Reach (prog mpl 14) (mkS s0 s0.pc s0.regs.regs s0.pstate s0.mem) _
  have hx0r : s0.regs.regs 0#5 = bytes := hx0'
  rw [hpc0]
  refine reach_step14 hrun rfl (f14_0 hP hCL14) ?_
  simp (config := { decide := true }) only [Program.evalInst, execInstWithSvc, execLdr, execStr, execMoveWide, execLogicalShift, execLogicalImm, execBitfield, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Memory.readSized, Memory.writeSized, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setMem, mkS_setPC, rd_gpr, wr_gpr_ite, Function.update_apply, mkS_mem, mkS_pc, mkS_status, pc_add4, evalLogical, shiftVal, shift64, Nat.reduceAdd, rd_xzr, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.zero_or, if_true, ↓reduceIte, hx0r, canRead1 (perm_rw_r r31.2.1) r31.2.2, r31.1]
  refine reach_step14 hrun rfl (f14_4 hP hCL14) ?_
  simp (config := { decide := true }) only [Program.evalInst, execInstWithSvc, execLdr, execStr, execMoveWide, execLogicalShift, execLogicalImm, execBitfield, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Memory.readSized, Memory.writeSized, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setMem, mkS_setPC, rd_gpr, wr_gpr_ite, Function.update_apply, mkS_mem, mkS_pc, mkS_status, pc_add4, evalLogical, shiftVal, shift64, Nat.reduceAdd, rd_xzr, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.zero_or, if_true, ↓reduceIte]
  refine reach_step14 hrun rfl (f14_8 hP hCL14) ?_
  simp (config := { decide := true }) only [Program.evalInst, execInstWithSvc, execLdr, execStr, execMoveWide, execLogicalShift, execLogicalImm, execBitfield, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Memory.readSized, Memory.writeSized, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setMem, mkS_setPC, rd_gpr, wr_gpr_ite, Function.update_apply, mkS_mem, mkS_pc, mkS_status, pc_add4, evalLogical, shiftVal, shift64, Nat.reduceAdd, rd_xzr, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.zero_or, if_true, ↓reduceIte, hx0r, canRead1 (perm_rw_r r0.2.1) r0.2.2, r0.1]
  refine reach_step14 hrun rfl (f14_12 hP hCL14) ?_
  simp (config := { decide := true }) only [Program.evalInst, execInstWithSvc, execLdr, execStr, execMoveWide, execLogicalShift, execLogicalImm, execBitfield, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Memory.readSized, Memory.writeSized, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setMem, mkS_setPC, rd_gpr, wr_gpr_ite, Function.update_apply, mkS_mem, mkS_pc, mkS_status, pc_add4, evalLogical, shiftVal, shift64, Nat.reduceAdd, rd_xzr, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.zero_or, if_true, ↓reduceIte, hx0r]
  refine pair14 hP hCL14 hrun ?_
  refine reach_step14 hrun rfl (f14_24 hP hCL14) ?_
  simp (config := { decide := true }) only [Program.evalInst, execInstWithSvc, execLdr, execStr, execMoveWide, execLogicalShift, execLogicalImm, execBitfield, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Memory.readSized, Memory.writeSized, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setMem, mkS_setPC, rd_gpr, wr_gpr_ite, Function.update_apply, mkS_mem, mkS_pc, mkS_status, pc_add4, evalLogical, shiftVal, shift64, Nat.reduceAdd, rd_xzr, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.zero_or, if_true, ↓reduceIte]
  refine reach_step14 hrun rfl (f14_28 hP hCL14) ?_
  simp (config := { decide := true }) only [Program.evalInst, execInstWithSvc, execLdr, execStr, execMoveWide, execLogicalShift, execLogicalImm, execBitfield, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Memory.readSized, Memory.writeSized, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setMem, mkS_setPC, rd_gpr, wr_gpr_ite, Function.update_apply, mkS_mem, mkS_pc, mkS_status, pc_add4, evalLogical, shiftVal, shift64, Nat.reduceAdd, rd_xzr, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.zero_or, if_true, ↓reduceIte]
  have hw0 : s0.mem.canWrite (bytes + 0#64) 1 = true := canWrite1 r0.2.1
  refine reach_step14 hrun rfl (f14_32 hP hCL14) ?_
  simp (config := { decide := true }) only [Program.evalInst, execInstWithSvc, execLdr, execStr, execMoveWide, execLogicalShift, execLogicalImm, execBitfield, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Memory.readSized, Memory.writeSized, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setMem, mkS_setPC, rd_gpr, wr_gpr_ite, Function.update_apply, mkS_mem, mkS_pc, mkS_status, pc_add4, evalLogical, shiftVal, shift64, Nat.reduceAdd, rd_xzr, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.zero_or, if_true, ↓reduceIte, hw0]
  have hw31 : ∀ v, (s0.mem.write8 (bytes + 0#64) v).canWrite (bytes + 31#64) 1 = true := by
    intro v; apply canWrite1; rw [Memory.perm_write8_apply]; exact r31.2.1
  have hCLw : ∀ v, (prog mpl 14).CodeLoaded (s0.mem.write8 (bytes + 0#64) v) := fun v =>
    hCL14.of_keepsFrozen (Memory.keepsFrozen_write8 hw0 v)
  refine reach_step14 hrun rfl (f14_36 hP (hCLw _)) ?_
  simp (config := { decide := true }) only [Program.evalInst, execInstWithSvc, execLdr, execStr, execMoveWide, execLogicalShift, execLogicalImm, execBitfield, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Memory.readSized, Memory.writeSized, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setMem, mkS_setPC, rd_gpr, wr_gpr_ite, Function.update_apply, mkS_mem, mkS_pc, mkS_status, pc_add4, evalLogical, shiftVal, shift64, Nat.reduceAdd, rd_xzr, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.zero_or, if_true, ↓reduceIte, hw31]
  rw [clamp0_eq, clamp31_eq]
  set v0 := bs[0] &&& 0xf8#8 with hv0
  set v31 := (bs[31] &&& 0x7f#8) ||| 0x40#8 with hv31
  set m2 := (s0.mem.write8 (bytes + 0#64) v0).write8 (bytes + 31#64) v31 with hm2
  have hkf : s0.mem.KeepsFrozen m2 :=
    (Memory.keepsFrozen_write8 hw0 v0).trans (Memory.keepsFrozen_write8 (hw31 v0) v31)
  refine reach_step14 hrun rfl (f14_40 hP (hCL14.of_keepsFrozen hkf)) ?_
  simp only [Program.evalInst, execInstWithSvc, mkS_setPC, mkS_pc]
  rw [show mpl.base 14 + 40#64 + (mpl.base 13 + BitVec.ofNat 64 0 - (mpl.base 14 + BitVec.ofNat 64 40)) =
    mpl.base 13 + BitVec.ofNat 64 0 by bv_omega]
  have hB1 := sat_bytes_write bs bytes G s0.mem hB 0 (by omega) v0
  have hB2 := sat_bytes_write _ bytes G _ hB1 31 (by simp; omega) v31
  rw [clamp_set bs hbl] at hB2
  have hm2CL : x25519CliMultiLib.CodeLoaded mpl m2 := multi_codeLoaded_of_keepsFrozen hCL hkf
  have hcl31 : ((clampScalarBytes bs).getD 31 0#8).toNat ≤ 127 := by
    rw [← clamp_set bs hbl]
    have h31 : 31 < ((bs.set 0 v0).set 31 v31).length := by simp; omega
    rw [List.getD_eq_getElem _ _ h31, List.getElem_set_self]
    exact (by decide : ∀ b : BitVec 8, ((b &&& 0x7f#8) ||| 0x40#8).toNat ≤ 127) _
  have hcllen : (clampScalarBytes bs).length = 32 := by rw [← clamp_set bs hbl]; simp [hbl]
  have hx8r : s0.regs.regs 8#5 = out := hx8
  refine reach_tail (j := 13) (R := R)
    (x' := (out, mpl.ρ symTAB, bytes, out_bs, ed25519BasepointTableBytes, clampScalarBytes bs))
    hMB13 rfl hrun ?_ (by simpa using hal) ((hCL 13 (by decide)).of_keepsFrozen hkf) ?_
  · show m2 ⊨ ((⌜_⌝ ∗ _) ∗ _) ∗ R
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨?_, ?_, ?_, hol, table_bounded, hcllen, hcl31⟩, ?_⟩
    · simp (config := { decide := true }) [Function.update_apply, hx8r]
    · simp (config := { decide := true }) [Function.update_apply]
    · simp (config := { decide := true }) [Function.update_apply]
    · have h3 := (satisfies_pure_sepConj _ _ _).mpr ⟨hm2CL, hB2⟩
      simp only [mkS_mem, stackFrame_mkS]
      have htab : ed25519_basepoint_table mpl = mpl.ρ symTAB := rfl
      exact Satisfies.of_eq h3 (by rw [hG, htab]; ac_rfl)
  · intro sf hout
    refine outcome_tail ?_ ?_ ?_ ?_ ?_ ?_ hout
    rotate_left 3
    · show ⌜False⌝ ⊢ _; exact false_entails
    · intro c; show ⌜False⌝ ⊢ _; exact false_entails
    · show ⌜False⌝ ⊢ _; exact false_entails
    · simp (config := { decide := true }) [Function.update_apply]
    · intro i h1 h2
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> first | rfl | (simp at h1)
    · simp only [MultiPlacedLib.withCodeLoaded, edwardsBasepointTableMulBaseSpec,
        edwardsPointMulBaseClampedSpec, ToBaseSpec.toSpec]
      rw [show ed25519_basepoint_table mpl = mpl.ρ symTAB from rfl]
      simp only [sepExists_sepConj_right]
      exact Entails.sepExists_elim fun res =>
        Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.sepExists_intro res)

theorem fnOk_mul_base_clamped_dev :
    fnOk "<curve25519_dalek::edwards::EdwardsPoint>::mul_base_clamped"
      edwardsPointMulBaseClampedSpec := by
  obtain ⟨i, o, hlk, hMB⟩ := X25519Dalek.fnOk_basepointTable_mul_base_v2
  have h2 : some (i, o) = some (13, 0) := hlk.symm.trans lookup_MB
  cases h2
  refine ⟨14, 0, lookup_MBC, fun mpl hP => mbc_core mpl hP ?_⟩
  have h13 := hMB mpl hP
  have ha : x25519CliMultiLib.fnAddr mpl symMB = mpl.base 13 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr]; rw [lookup_MB]
  rw [ha] at h13
  exact h13

end X25519Dalek.Edw
end

open X25519Dalek in
theorem solution :
    fnOk
      "<curve25519_dalek::edwards::EdwardsPoint>::mul_base_clamped"
      edwardsPointMulBaseClampedSpec :=
  X25519Dalek.Edw.fnOk_mul_base_clamped_dev
