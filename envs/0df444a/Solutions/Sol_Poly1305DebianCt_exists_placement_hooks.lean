-- Prove2me | solution 1 for Poly1305DebianCt.exists_placement_hooks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-26T15:17:37.547844+00:00
-- url     : https://prove2.me/submissions/e8afc779-646e-48e3-9695-e8b69c325d05

import Definitions.Def_Poly1305DebianCt_Spec
import Definitions.Def_Libc_ExplicitBzero
import Definitions.Def_Musl_ExternHooks

section
/-! A concrete placement of `Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib` (built by hand on
the pattern of `rust-obj2lean`'s canonical placement of the functional library: code at `0x100000`, external
functions and the guard's GOT slot from `0x101000`, data objects from `0x102000`, no linker relaxation)
and kernel-checked proofs that it is `Placeable` and `GuardUniform`. -/

namespace Poly1305DebianCtNonvac

open Arm64 Arm64.Obj Poly1305DebianCt

/-! ## Decidability of the range conditions -/

instance (p t : BitVec 64) : Decidable (BranchInRange p t) := by
  unfold BranchInRange; infer_instance
instance (p t : BitVec 64) : Decidable (AdrpInRange p t) := by
  unfold AdrpInRange; infer_instance
instance (p t : BitVec 64) : Decidable (AdrInRange p t) := by
  unfold AdrInRange; infer_instance
instance (s : Nat) (t : BitVec 64) : Decidable (Lo12Aligned s t) := by
  unfold Lo12Aligned; infer_instance
instance (p t : BitVec 64) : Decidable (Imm19InRange p t) := by
  unfold Imm19InRange; infer_instance
instance (p t : BitVec 64) : Decidable (TstBr14InRange p t) := by
  unfold TstBr14InRange; infer_instance
instance (p t : BitVec 64) : Decidable (Prel32InRange p t) := by
  unfold Prel32InRange; infer_instance
instance (t : BitVec 64) : Decidable (Abs32InRange t) := by
  unfold Abs32InRange; infer_instance
instance (t : BitVec 64) : Decidable (TlsUInt32InRange t) := by
  unfold TlsUInt32InRange; infer_instance
instance (t : BitVec 64) : Decidable (TprelHi12InRange t) := by
  unfold TprelHi12InRange; infer_instance
instance (t : BitVec 64) : Decidable (TprelLo12InRange t) := by
  unfold TprelLo12InRange; infer_instance
instance (t : BitVec 64) : Decidable (TprelG1InRange t) := by
  unfold TprelG1InRange; infer_instance
instance (t : BitVec 64) : Decidable (TprelG0InRange t) := by
  unfold TprelG0InRange; infer_instance
instance (t : BitVec 64) : Decidable (TlsIeInRange t) := by
  unfold TlsIeInRange; infer_instance

instance (k : RelocKind) (p t : BitVec 64) : Decidable (CodeRelocInRange k p t) := by
  cases k <;> unfold CodeRelocInRange <;> infer_instance

instance (blk : CodeBlock) (pl : Placement) (k : RelocKind) (off : Nat) (p t : BitVec 64) :
    Decidable (blk.relocInRange pl k off p t) := by
  unfold CodeBlock.relocInRange
  split <;> infer_instance

/-! ## The placement -/

/-- Addresses of the non-block symbols. -/
def rhoTable : List (String × Nat) := [
  ("__stack_chk_fail", 0x101000),
  ("__stack_chk_guard", 0x101040),
  ("crypto_onetimeauth_poly1305_donna_implementation", 0x102400),
  ("implementation [libsodium_la_onetimeauth_poly1305]", 0x102200),
  ("libsodium_la_crypto_onetimeauth:.rodata.str1.8+0x0", 0x102000),
  ("memset", 0x1010c0),
  ("optblocker_u16 [libsodium_la_verify]", 0x102600),
  ("randombytes_buf", 0x101100),
  ("sodium_memzero", 0x101140)]

def pl0 : Placement where
  base := 0x100000#64
  ρ := fun s => BitVec.ofNat 64 ((lookup s rhoTable).getD 0)
  relax := fun _ => false
  b2b := fun _ => false

set_option maxRecDepth 100000

theorem text_relocs_ok : ∀ r ∈ libsodiumDebianOnetimeauthCtLib.text.relocs,
    r.off % 4 = 0 ∧ r.off + 4 ≤ libsodiumDebianOnetimeauthCtLib.text.code.length ∧
    libsodiumDebianOnetimeauthCtLib.text.relocInRange pl0 r.kind r.off
      (pl0.base + BitVec.ofNat 64 r.off)
      (libsodiumDebianOnetimeauthCtLib.text.relocTarget pl0 r.off r) := by
  decide +kernel

theorem text_placeable : libsodiumDebianOnetimeauthCtLib.text.Placeable pl0 where
  align_pos := by decide +kernel
  base_aligned := by decide +kernel
  no_wrap := by decide +kernel
  len_aligned := by decide +kernel
  relocs_nodup := by decide +kernel
  relocs_ok := text_relocs_ok
  relaxed_ok := by
    intro off r h
    simp [CodeBlock.relaxedAt, pl0] at h
  symbols_ok := by decide +kernel
  externs_ok := by decide +kernel

theorem placeable : libsodiumDebianOnetimeauthCtLib.Placeable pl0 where
  text := text_placeable
  data_nodup := by decide +kernel
  data_ok := by decide +kernel
  data_relocs_ok := by decide +kernel

theorem guardUniform : GuardUniform pl0 := by
  unfold GuardUniform guardDirect
  decide +kernel

end Poly1305DebianCtNonvac
end

section
/-! Copied from `p2m-standalone/arm64-libc/proofs/exists_hookOk_explicitBzeroSpec.lean`, namespace
renamed. Non-vacuity of `Libc.explicitBzeroSpec`: a hook that writes `x1` zero bytes at `x0` and
returns to `x30` meets the contract. Self-contained against the published bundles (the upstream
version in `exists_hookOk_explicitBzeroSpec.upstream.lean` uses DeepMind's ProofLib). -/

open Arm64

namespace Poly1305DebianCtNonvac.Bzero

/-! ## Single-byte writes -/

theorem read8_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).read8 x = if x = a then v else m.read8 x := by
  unfold Memory.read8 Memory.write8
  by_cases h : x = a <;> simp [h]

theorem perm_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).perm x = m.perm x := by
  unfold Memory.perm Memory.write8 Memory.rawPerm
  by_cases h : x = a
  · subst h
    cases hc : m.cells x with
    | none => simp
    | some c =>
      obtain ⟨p, b⟩ := c
      cases p <;> simp [Perm.rwx]
  · simp [h]

theorem isLazyFree_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isLazyFree x = if x = a then false else m.isLazyFree x := by
  unfold Memory.isLazyFree Memory.write8 Memory.rawPerm
  by_cases h : x = a
  · subst h
    cases hc : m.cells x with
    | none => simp
    | some c =>
      obtain ⟨p, b⟩ := c
      cases p <;> simp
  · simp [h]

theorem isAnon_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isAnon x = m.isAnon x := by
  unfold Memory.isAnon Memory.write8 Memory.rawPerm
  by_cases h : x = a
  · subst h
    cases hc : m.cells x with
    | none => simp
    | some c =>
      obtain ⟨p, b⟩ := c
      cases p <;> simp
  · simp [h]

/-! ## Writing `n` zero bytes -/

theorem inRegion_succ (a x : BitVec 64) (n : Nat) :
    InRegion a (n + 1) x ↔ x = a ∨ InRegion (a + 1#64) n x := by
  unfold InRegion
  bv_omega

theorem zeros_read8 (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n 0#8)).read8 x = if InRegion a n x then 0#8 else m.read8 x := by
  induction n with
  | zero => intro m a x; simp [Memory.writeBytes, InRegion]
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, read8_write8]
    by_cases h1 : InRegion (a + 1#64) n x
    · simp [h1, (inRegion_succ a x n).2 (Or.inr h1)]
    · by_cases h2 : x = a
      · simp [h2, (inRegion_succ a a n).2 (Or.inl rfl)]
      · have h3 : ¬ InRegion a (n + 1) x := fun h => by
          rcases (inRegion_succ a x n).1 h with h | h
          · exact h2 h
          · exact h1 h
        simp [h1, h2, h3]

theorem zeros_perm (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n 0#8)).perm x = m.perm x := by
  induction n with
  | zero => intro m a x; rfl
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, perm_write8]

theorem zeros_isAnon (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n 0#8)).isAnon x = m.isAnon x := by
  induction n with
  | zero => intro m a x; rfl
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, isAnon_write8]

theorem zeros_isLazyFree (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n 0#8)).isLazyFree x =
      if InRegion a n x then false else m.isLazyFree x := by
  induction n with
  | zero => intro m a x; simp [Memory.writeBytes, InRegion]
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, isLazyFree_write8]
    by_cases h1 : InRegion (a + 1#64) n x
    · simp [h1, (inRegion_succ a x n).2 (Or.inr h1)]
    · by_cases h2 : x = a
      · simp [h2, (inRegion_succ a a n).2 (Or.inl rfl)]
      · have h3 : ¬ InRegion a (n + 1) x := fun h => by
          rcases (inRegion_succ a x n).1 h with h | h
          · exact h2 h
          · exact h1 h
        simp [h1, h2, h3]

/-! ## Heaps -/

/-- The heap owning `[a, a + n)` read-write with every byte zero. -/
def zHeap (a : BitVec 64) (n : Nat) : Heap :=
  { phys := fun x => if InRegion a n x then some (.rw 0#8) else none }

theorem empty_union (h : Heap) : Heap.empty.union h = h := rfl

theorem zHeap_holds (n : Nat) : ∀ (a : BitVec 64), n ≤ 2 ^ 64 →
    (pointsToBytes a (List.replicate n 0#8)).holds (zHeap a n) := by
  induction n with
  | zero =>
    intro a _
    show zHeap a 0 = Heap.empty
    unfold zHeap Heap.empty
    congr
  | succ n ih =>
    intro a hn
    refine ⟨Heap.singleton a 0#8, zHeap (a + 1#64) n, ?_, ?_, rfl, ih (a + 1#64) (by omega)⟩
    · have ha : ¬ InRegion (a + 1#64) n a := by
        unfold InRegion
        bv_omega
      refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun _ => Or.inl rfl⟩
      · by_cases hx : x = a
        · subst hx
          exact Or.inr (Or.inl (by simp [zHeap, ha]))
        · exact Or.inl (by simp [Heap.singleton, hx])
      · intro γ k oa v h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
    · unfold zHeap Heap.singleton Heap.union
      congr
      funext x
      by_cases hx : x = a
      · subst hx
        simp [(inRegion_succ x x n).2 (Or.inl rfl)]
      · by_cases h1 : InRegion (a + 1#64) n x
        · simp [hx, h1, (inRegion_succ a x n).2 (Or.inr h1)]
        · have h3 : ¬ InRegion a (n + 1) x := fun h => by
            rcases (inRegion_succ a x n).1 h with h | h
            · exact hx h
            · exact h1 h
          simp [hx, h1, h3]

/-- `h'` is `h` with the values of some read-write cells changed. -/
def Rew (h h' : Heap) : Prop :=
  (∀ a, h'.phys a = h.phys a ∨
    ∃ b b', h.phys a = some (.rw b) ∧ h'.phys a = some (.rw b')) ∧
  h'.auth = h.auth ∧ h'.frag = h.frag ∧ h'.mapped = h.mapped

theorem Rew.disjoint {h h' g : Heap} (r : Rew h h') (d : h.Disjoint g) : h'.Disjoint g := by
  obtain ⟨r1, ra, rf, rm⟩ := r
  obtain ⟨d1, d2, d3, d4, d5⟩ := d
  refine ⟨fun a => ?_, ?_, ?_, ?_, ?_⟩
  · rcases r1 a with e | ⟨b, b', e1, e2⟩
    · rw [e]; exact d1 a
    · rcases d1 a with h0 | h0 | ⟨c, c1, _⟩
      · rw [e1] at h0; cases h0
      · exact Or.inr (Or.inl h0)
      · rw [e1] at c1; cases c1
  · rw [ra]; exact d2
  · rw [rf]; exact d3
  · rw [ra, rf]; exact d4
  · rw [rm]; exact d5

theorem Rew.union_left {h h' : Heap} (g : Heap) (r : Rew h h') : Rew (h.union g) (h'.union g) := by
  obtain ⟨r1, ra, rf, rm⟩ := r
  refine ⟨fun a => ?_, ?_, ?_, ?_⟩
  · rcases r1 a with e | ⟨b, b', e1, e2⟩
    · left; simp only [Heap.union, e]
    · right; exact ⟨b, b', by simp [Heap.union, e1], by simp [Heap.union, e2]⟩
  · simp only [Heap.union, ra]
  · simp only [Heap.union, rf]
  · simp only [Heap.union, rm]

theorem matches_zeros {H H' : Heap} {m : Memory} {p : BitVec 64} {n : Nat}
    (hM : H.Matches m) (r : Rew H H')
    (hin : ∀ a, InRegion p n a → H'.phys a = some (.rw 0#8) ∧ ∃ b, H.phys a = some (.rw b))
    (hout : ∀ a, ¬ InRegion p n a → H'.phys a = H.phys a) :
    H'.Matches (m.writeBytes p (List.replicate n 0#8)) := by
  obtain ⟨_, ra, rf, rm⟩ := r
  obtain ⟨hM1, ⟨B, hB⟩, hM3⟩ := hM
  refine ⟨fun a c hc => ?_, ⟨B, fun γ hγ k => by rw [ra, rf]; exact hB γ hγ k⟩, fun a ha => ?_⟩
  · by_cases h : InRegion p n a
    · obtain ⟨h1, b, h2⟩ := hin a h
      rw [h1] at hc
      cases hc
      have := hM1 a _ h2
      simp only at this
      simp [zeros_read8, zeros_perm, zeros_isLazyFree, h, this.2.1]
    · rw [hout a h] at hc
      have := hM1 a c hc
      cases c <;> simpa [zeros_read8, zeros_perm, zeros_isLazyFree, h] using this
  · rw [rm] at ha
    rw [zeros_perm, zeros_isAnon]
    exact hM3 a ha

/-! ## The hook -/

/-- Writes `x1` zero bytes at `x0` and returns to `x30`. -/
def hookBzero (s : State) : State :=
  (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
    (List.replicate (s.readReg64 .x1).toNat 0#8))).setPC (s.readReg64 .lr)

theorem hookBzero_ok : HookOk hookBzero Libc.explicitBzeroSpec := by
  rintro ⟨p, n⟩ R s0 hrun ⟨H, hH, hM⟩ _
  obtain ⟨H1, hR, d1, rfl, ⟨hP, H2, -, rfl, ⟨rfl, hx0, hx1⟩,
    ⟨hReg, hS, d2, rfl, ⟨mm, rfl⟩, ⟨mS, hSh⟩⟩⟩, hRh⟩ := hH
  rw [empty_union] at d1 hM
  have hS_eq : hS = regionHeap (s0.sp - BitVec.ofNat 64 VerifiedLibraries.Musl.externStack)
      VerifiedLibraries.Musl.externStack mS := hSh
  -- the region is shorter than the address space: it is disjoint from the 4096-byte stack area
  have hn : n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hle => ?_
    have hin : InRegion p n (s0.sp - BitVec.ofNat 64 VerifiedLibraries.Musl.externStack) := by
      unfold InRegion
      exact Nat.lt_of_lt_of_le (BitVec.isLt _) hle
    rcases d2.1 (s0.sp - BitVec.ofNat 64 VerifiedLibraries.Musl.externStack) with h | h | ⟨c, h, _⟩
    · simp [regionHeap, hin] at h
    · simp [hS_eq, regionHeap, InRegion, VerifiedLibraries.Musl.externStack] at h
    · simp [regionHeap, hin] at h
  have r0 : Rew (regionHeap p n mm) (zHeap p n) := by
    refine ⟨fun a => ?_, rfl, rfl, rfl⟩
    by_cases h : InRegion p n a
    · exact Or.inr ⟨mm.read8 a, 0#8, by simp [regionHeap, h], by simp [zHeap, h]⟩
    · left; simp [regionHeap, zHeap, h]
  have r1 := Rew.union_left hS r0
  have r2 := Rew.union_left hR r1
  have hmem : (hookBzero s0).mem = s0.mem.writeBytes p (List.replicate n 0#8) := by
    simp only [hookBzero, hx0, hx1]; rfl
  refine ⟨?_, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩, ?_⟩⟩
  · intro a hfr
    rw [hmem]
    have hout : ¬ InRegion p n a := by
      intro h
      have := hM.1 a (.rw (mm.read8 a)) (by simp [Heap.union, regionHeap, h])
      simp only at this
      simp [Memory.Frozen, this.2.1, Perm.rw, Perm.frozen] at hfr
    simp [zeros_read8, zeros_perm, zeros_isLazyFree, zeros_isAnon, hout]
  · rw [hmem]
    refine ⟨((zHeap p n).union hS).union hR,
      ⟨(zHeap p n).union hS, hR, r1.disjoint d1, rfl,
        ⟨zHeap p n, hS, r0.disjoint d2, rfl, zHeap_holds n p (Nat.le_of_lt hn), ⟨mS, hSh⟩⟩, hRh⟩,
      matches_zeros hM r2 (fun a h => ⟨by simp [Heap.union, zHeap, h],
        mm.read8 a, by simp [Heap.union, regionHeap, h]⟩) (fun a h => by
          simp [Heap.union, zHeap, regionHeap, h])⟩

end Poly1305DebianCtNonvac.Bzero

end

section
/-! Non-vacuity of `VerifiedLibraries.Musl.cryptoMemsetSpec`: a hook that writes `x2` copies of
the low byte of `x1` at `x0` and returns to `x30` meets the contract. Adapted from the
`explicitBzeroSpec` proof (`Bzero.lean`). Self-contained against the published bundles (the upstream
version in `exists_hookOk_explicitBzeroSpec.upstream.lean` uses DeepMind's ProofLib). -/

open Arm64

namespace Poly1305DebianCtNonvac.Fill

/-! ## Single-byte writes -/

theorem read8_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).read8 x = if x = a then v else m.read8 x := by
  unfold Memory.read8 Memory.write8
  by_cases h : x = a <;> simp [h]

theorem perm_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).perm x = m.perm x := by
  unfold Memory.perm Memory.write8 Memory.rawPerm
  by_cases h : x = a
  · subst h
    cases hc : m.cells x with
    | none => simp
    | some c =>
      obtain ⟨p, b⟩ := c
      cases p <;> simp [Perm.rwx]
  · simp [h]

theorem isLazyFree_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isLazyFree x = if x = a then false else m.isLazyFree x := by
  unfold Memory.isLazyFree Memory.write8 Memory.rawPerm
  by_cases h : x = a
  · subst h
    cases hc : m.cells x with
    | none => simp
    | some c =>
      obtain ⟨p, b⟩ := c
      cases p <;> simp
  · simp [h]

theorem isAnon_write8 (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isAnon x = m.isAnon x := by
  unfold Memory.isAnon Memory.write8 Memory.rawPerm
  by_cases h : x = a
  · subst h
    cases hc : m.cells x with
    | none => simp
    | some c =>
      obtain ⟨p, b⟩ := c
      cases p <;> simp
  · simp [h]

/-! ## Writing `n` copies of a byte -/

theorem inRegion_succ (a x : BitVec 64) (n : Nat) :
    InRegion a (n + 1) x ↔ x = a ∨ InRegion (a + 1#64) n x := by
  unfold InRegion
  bv_omega

theorem zeros_read8 (c : BitVec 8) (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n c)).read8 x = if InRegion a n x then c else m.read8 x := by
  induction n with
  | zero => intro m a x; simp [Memory.writeBytes, InRegion]
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, read8_write8]
    by_cases h1 : InRegion (a + 1#64) n x
    · simp [h1, (inRegion_succ a x n).2 (Or.inr h1)]
    · by_cases h2 : x = a
      · simp [h2, (inRegion_succ a a n).2 (Or.inl rfl)]
      · have h3 : ¬ InRegion a (n + 1) x := fun h => by
          rcases (inRegion_succ a x n).1 h with h | h
          · exact h2 h
          · exact h1 h
        simp [h1, h2, h3]

theorem zeros_perm (c : BitVec 8) (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n c)).perm x = m.perm x := by
  induction n with
  | zero => intro m a x; rfl
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, perm_write8]

theorem zeros_isAnon (c : BitVec 8) (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n c)).isAnon x = m.isAnon x := by
  induction n with
  | zero => intro m a x; rfl
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, isAnon_write8]

theorem zeros_isLazyFree (c : BitVec 8) (n : Nat) : ∀ (m : Memory) (a x : BitVec 64),
    (m.writeBytes a (List.replicate n c)).isLazyFree x =
      if InRegion a n x then false else m.isLazyFree x := by
  induction n with
  | zero => intro m a x; simp [Memory.writeBytes, InRegion]
  | succ n ih =>
    intro m a x
    rw [List.replicate_succ, Memory.writeBytes, ih, isLazyFree_write8]
    by_cases h1 : InRegion (a + 1#64) n x
    · simp [h1, (inRegion_succ a x n).2 (Or.inr h1)]
    · by_cases h2 : x = a
      · simp [h2, (inRegion_succ a a n).2 (Or.inl rfl)]
      · have h3 : ¬ InRegion a (n + 1) x := fun h => by
          rcases (inRegion_succ a x n).1 h with h | h
          · exact h2 h
          · exact h1 h
        simp [h1, h2, h3]

/-! ## Heaps -/

/-- The heap owning `[a, a + n)` read-write with every byte zero. -/
def zHeap (c : BitVec 8) (a : BitVec 64) (n : Nat) : Heap :=
  { phys := fun x => if InRegion a n x then some (.rw c) else none }

theorem empty_union (h : Heap) : Heap.empty.union h = h := rfl

theorem zHeap_holds (c : BitVec 8) (n : Nat) : ∀ (a : BitVec 64), n ≤ 2 ^ 64 →
    (pointsToBytes a (List.replicate n c)).holds (zHeap c a n) := by
  induction n with
  | zero =>
    intro a _
    show zHeap c a 0 = Heap.empty
    unfold zHeap Heap.empty
    congr
  | succ n ih =>
    intro a hn
    refine ⟨Heap.singleton a c, zHeap c (a + 1#64) n, ?_, ?_, rfl, ih (a + 1#64) (by omega)⟩
    · have ha : ¬ InRegion (a + 1#64) n a := by
        unfold InRegion
        bv_omega
      refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun _ => Or.inl rfl⟩
      · by_cases hx : x = a
        · subst hx
          exact Or.inr (Or.inl (by simp [zHeap, ha]))
        · exact Or.inl (by simp [Heap.singleton, hx])
      · intro γ k oa v h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
    · unfold zHeap Heap.singleton Heap.union
      congr
      funext x
      by_cases hx : x = a
      · subst hx
        simp [(inRegion_succ x x n).2 (Or.inl rfl)]
      · by_cases h1 : InRegion (a + 1#64) n x
        · simp [hx, h1, (inRegion_succ a x n).2 (Or.inr h1)]
        · have h3 : ¬ InRegion a (n + 1) x := fun h => by
            rcases (inRegion_succ a x n).1 h with h | h
            · exact hx h
            · exact h1 h
          simp [hx, h1, h3]

/-- `h'` is `h` with the values of some read-write cells changed. -/
def Rew (h h' : Heap) : Prop :=
  (∀ a, h'.phys a = h.phys a ∨
    ∃ b b', h.phys a = some (.rw b) ∧ h'.phys a = some (.rw b')) ∧
  h'.auth = h.auth ∧ h'.frag = h.frag ∧ h'.mapped = h.mapped

theorem Rew.disjoint {h h' g : Heap} (r : Rew h h') (d : h.Disjoint g) : h'.Disjoint g := by
  obtain ⟨r1, ra, rf, rm⟩ := r
  obtain ⟨d1, d2, d3, d4, d5⟩ := d
  refine ⟨fun a => ?_, ?_, ?_, ?_, ?_⟩
  · rcases r1 a with e | ⟨b, b', e1, e2⟩
    · rw [e]; exact d1 a
    · rcases d1 a with h0 | h0 | ⟨c, c1, _⟩
      · rw [e1] at h0; cases h0
      · exact Or.inr (Or.inl h0)
      · rw [e1] at c1; cases c1
  · rw [ra]; exact d2
  · rw [rf]; exact d3
  · rw [ra, rf]; exact d4
  · rw [rm]; exact d5

theorem Rew.union_left {h h' : Heap} (g : Heap) (r : Rew h h') : Rew (h.union g) (h'.union g) := by
  obtain ⟨r1, ra, rf, rm⟩ := r
  refine ⟨fun a => ?_, ?_, ?_, ?_⟩
  · rcases r1 a with e | ⟨b, b', e1, e2⟩
    · left; simp only [Heap.union, e]
    · right; exact ⟨b, b', by simp [Heap.union, e1], by simp [Heap.union, e2]⟩
  · simp only [Heap.union, ra]
  · simp only [Heap.union, rf]
  · simp only [Heap.union, rm]

theorem matches_zeros {H H' : Heap} {m : Memory} {p : BitVec 64} {n : Nat} {c : BitVec 8}
    (hM : H.Matches m) (r : Rew H H')
    (hin : ∀ a, InRegion p n a → H'.phys a = some (.rw c) ∧ ∃ b, H.phys a = some (.rw b))
    (hout : ∀ a, ¬ InRegion p n a → H'.phys a = H.phys a) :
    H'.Matches (m.writeBytes p (List.replicate n c)) := by
  obtain ⟨_, ra, rf, rm⟩ := r
  obtain ⟨hM1, ⟨B, hB⟩, hM3⟩ := hM
  refine ⟨fun a c hc => ?_, ⟨B, fun γ hγ k => by rw [ra, rf]; exact hB γ hγ k⟩, fun a ha => ?_⟩
  · by_cases h : InRegion p n a
    · obtain ⟨h1, b, h2⟩ := hin a h
      rw [h1] at hc
      cases hc
      have := hM1 a _ h2
      simp only at this
      simp [zeros_read8, zeros_perm, zeros_isLazyFree, h, this.2.1]
    · rw [hout a h] at hc
      have := hM1 a c hc
      cases c <;> simpa [zeros_read8, zeros_perm, zeros_isLazyFree, h] using this
  · rw [rm] at ha
    rw [zeros_perm, zeros_isAnon]
    exact hM3 a ha

/-! ## The hook -/

/-- Writes `x2` copies of the low byte of `x1` at `x0` and returns to `x30`, leaving `x0`. -/
def hookMemset (s : State) : State :=
  (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
    (List.replicate (s.readReg64 .x2).toNat ((s.readReg32 .x1).truncate 8)))).setPC (s.readReg64 .lr)

theorem hookMemset_ok : HookOk hookMemset VerifiedLibraries.Musl.cryptoMemsetSpec := by
  rintro ⟨p, c, n⟩ R s0 hrun ⟨H, hH, hM⟩ _
  obtain ⟨H1, hR, d1, rfl, ⟨hP, H2, -, rfl, ⟨rfl, hx0, hx1, hx2⟩,
    ⟨hReg, hS, d2, rfl, ⟨mm, rfl⟩, ⟨mS, hSh⟩⟩⟩, hRh⟩ := hH
  rw [empty_union] at d1 hM
  have hS_eq : hS = regionHeap (s0.sp - BitVec.ofNat 64 VerifiedLibraries.Musl.externStack)
      VerifiedLibraries.Musl.externStack mS := hSh
  have hn : n < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hle => ?_
    have hin : InRegion p n (s0.sp - BitVec.ofNat 64 VerifiedLibraries.Musl.externStack) := by
      unfold InRegion
      exact Nat.lt_of_lt_of_le (BitVec.isLt _) hle
    rcases d2.1 (s0.sp - BitVec.ofNat 64 VerifiedLibraries.Musl.externStack) with h | h | ⟨c, h, _⟩
    · simp [regionHeap, hin] at h
    · simp [hS_eq, regionHeap, InRegion, VerifiedLibraries.Musl.externStack] at h
    · simp [regionHeap, hin] at h
  have r0 : Rew (regionHeap p n mm) (zHeap c p n) := by
    refine ⟨fun a => ?_, rfl, rfl, rfl⟩
    by_cases h : InRegion p n a
    · exact Or.inr ⟨mm.read8 a, c, by simp [regionHeap, h], by simp [zHeap, h]⟩
    · left; simp [regionHeap, zHeap, h]
  have r1 := Rew.union_left hS r0
  have r2 := Rew.union_left hR r1
  have hmem : (hookMemset s0).mem = s0.mem.writeBytes p (List.replicate n c) := by
    simp only [hookMemset, hx0, hx1, hx2]; rfl
  have hd0 : Heap.empty.Disjoint (zHeap c p n) := by
    refine ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_,
      fun _ => Or.inl rfl⟩
    intro γ k oa v h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
  refine ⟨?_, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩, ?_⟩⟩
  · intro a hfr
    rw [hmem]
    have hout : ¬ InRegion p n a := by
      intro h
      have := hM.1 a (.rw (mm.read8 a)) (by simp [Heap.union, regionHeap, h])
      simp only at this
      simp [Memory.Frozen, this.2.1, Perm.rw, Perm.frozen] at hfr
    simp [zeros_read8, zeros_perm, zeros_isLazyFree, zeros_isAnon, hout]
  · rw [hmem]
    refine ⟨((zHeap c p n).union hS).union hR,
      ⟨(zHeap c p n).union hS, hR, r1.disjoint d1, rfl,
        ⟨zHeap c p n, hS, r0.disjoint d2, rfl,
          ⟨Heap.empty, zHeap c p n, hd0, (empty_union _).symm, ⟨rfl, hx0⟩,
            zHeap_holds c n p (Nat.le_of_lt hn)⟩, ⟨mS, hSh⟩⟩, hRh⟩,
      matches_zeros hM r2 (fun a h => ⟨by simp [Heap.union, zHeap, h],
        mm.read8 a, by simp [Heap.union, regionHeap, h]⟩) (fun a h => by
          simp [Heap.union, zHeap, regionHeap, h])⟩

end Poly1305DebianCtNonvac.Fill

end

section
/-! # Non-vacuity of the constant-time Debian libsodium Poly1305 judgments

`Poly1305DebianCt.exists_placement_hooks`: the placement `pl0` (`Placement.lean`) and the hook
table `hooks0` (`sodium_memzero` ↦ `Bzero.hookBzero`, `memset` ↦ `Fill.hookMemset`, everything else
none) satisfy every hypothesis of the contracts. -/

namespace Poly1305DebianCtNonvac

open Arm64 Arm64.Obj Poly1305DebianCt

/-- The hook table. -/
def hooks0 (name : String) : Option (State → State) :=
  if name = "sodium_memzero" then some Bzero.hookBzero
  else if name = "memset" then some Fill.hookMemset
  else none

theorem memzeroOk : Poly1305Libsodium.MemzeroOk hooks0 :=
  ⟨Bzero.hookBzero, by simp [hooks0], Bzero.hookBzero_ok⟩

theorem memsetOk : MemsetOk hooks0 :=
  ⟨Fill.hookMemset, by simp [hooks0], Fill.hookMemset_ok⟩

instance (a b : BitVec 64) (n : Nat) : Decidable (Link.InRange a b n) := by
  unfold Link.InRange; infer_instance

instance (b1 n1 b2 n2 : Nat) : Decidable (RangesDisjoint b1 n1 b2 n2) := by
  unfold RangesDisjoint; infer_instance

theorem externFns_inj : ∀ e₁ ∈ Link.PlacedLib.externFns libsodiumDebianOnetimeauthCtLib,
    ∀ e₂ ∈ Link.PlacedLib.externFns libsodiumDebianOnetimeauthCtLib, pl0.ρ e₁ = pl0.ρ e₂ → e₁ = e₂ := by
  decide +kernel

theorem linkOk : Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthCtLib pl0 hooks0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e₁ h₁ e₂ h₂ h
    rw [externFns_inj e₁ h₁ e₂ h₂ h]
  · decide +kernel
  · decide +kernel
  · unfold Link.DataDisjoint; decide +kernel
  · decide +kernel

end Poly1305DebianCtNonvac
end

namespace Poly1305DebianCt

open Arm64 Arm64.Obj

theorem exists_placement_hooks :
    ∃ (pl : Placement) (externs : String → Option (State → State)),
      lib.Placeable pl ∧ GuardUniform pl ∧
        Poly1305Libsodium.MemzeroOk externs ∧ MemsetOk externs ∧
        Link.PlacedLib.LinkOk lib pl externs := by
  exact ⟨Poly1305DebianCtNonvac.pl0, Poly1305DebianCtNonvac.hooks0, Poly1305DebianCtNonvac.placeable,
    Poly1305DebianCtNonvac.guardUniform, Poly1305DebianCtNonvac.memzeroOk,
    Poly1305DebianCtNonvac.memsetOk, Poly1305DebianCtNonvac.linkOk⟩

end Poly1305DebianCt

theorem solution : type_of% @Poly1305DebianCt.exists_placement_hooks := @Poly1305DebianCt.exists_placement_hooks
