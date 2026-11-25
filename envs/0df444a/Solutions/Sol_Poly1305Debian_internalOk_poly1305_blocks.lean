-- Prove2me | solution 1 for Poly1305Debian.internalOk_poly1305_blocks
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-11-25T20:13:52.830059+00:00
-- url     : https://prove2.me/submissions/88a8159d-6d0b-46ad-aee3-5c9adbe47af5

import Definitions.Def_Poly1305Debian_Spec
import Definitions.Def_Libc_ExplicitBzero
import Definitions.Def_Musl_ExternHooks

section
/-! A concrete placement of `Poly1305Debian.libsodiumDebianOnetimeauthLib` (the canonical one of
`rust-obj2lean`) and kernel-checked proofs that it is `Placeable` and `GuardUniform`. -/

namespace Poly1305DebianNonvac

open Arm64 Arm64.Obj Poly1305Debian

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
  ("crypto_verify_16", 0x101080),
  ("implementation [libsodium_la_onetimeauth_poly1305]", 0x102200),
  ("libsodium_la_crypto_onetimeauth:.rodata.str1.8+0x0", 0x102000),
  ("memset", 0x1010c0),
  ("randombytes_buf", 0x101100),
  ("sodium_memzero", 0x101140)]

def pl0 : Placement where
  base := 0x100000#64
  ρ := fun s => BitVec.ofNat 64 ((lookup s rhoTable).getD 0)

set_option maxRecDepth 100000

theorem text_relocs_ok : ∀ r ∈ libsodiumDebianOnetimeauthLib.text.relocs,
    r.off % 4 = 0 ∧ r.off + 4 ≤ libsodiumDebianOnetimeauthLib.text.code.length ∧
    libsodiumDebianOnetimeauthLib.text.relocInRange pl0 r.kind r.off
      (pl0.base + BitVec.ofNat 64 r.off)
      (libsodiumDebianOnetimeauthLib.text.relocTarget pl0 r.off r) := by
  decide +kernel

theorem text_placeable : libsodiumDebianOnetimeauthLib.text.Placeable pl0 where
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

theorem placeable : libsodiumDebianOnetimeauthLib.Placeable pl0 where
  text := text_placeable
  data_nodup := by decide +kernel
  data_ok := by decide +kernel
  data_relocs_ok := by decide +kernel

theorem guardUniform : GuardUniform pl0 := by
  unfold GuardUniform guardDirect
  decide +kernel

end Poly1305DebianNonvac
end

section
/-! Copied from `p2m-standalone/arm64-libc/proofs/exists_hookOk_explicitBzeroSpec.lean`, namespace
renamed. Non-vacuity of `Libc.explicitBzeroSpec`: a hook that writes `x1` zero bytes at `x0` and
returns to `x30` meets the contract. Self-contained against the published bundles (the upstream
version in `exists_hookOk_explicitBzeroSpec.upstream.lean` uses DeepMind's ProofLib). -/

open Arm64

namespace Poly1305DebianNonvac.Bzero

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

end Poly1305DebianNonvac.Bzero
end

section
/-! Non-vacuity of `VerifiedLibraries.Musl.cryptoMemsetSpec`: a hook that writes `x2` copies of
the low byte of `x1` at `x0` and returns to `x30` meets the contract. Adapted from the
`explicitBzeroSpec` proof (`Bzero.lean`). Self-contained against the published bundles (the upstream
version in `exists_hookOk_explicitBzeroSpec.upstream.lean` uses DeepMind's ProofLib). -/

open Arm64

namespace Poly1305DebianNonvac.Fill

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

end Poly1305DebianNonvac.Fill
end

section
/-! # Non-vacuity of the Debian libsodium Poly1305 contracts

`Poly1305Debian.exists_placement_hooks`: the placement `pl0` (`Placement.lean`) and the hook
table `hooks0` (`sodium_memzero` ↦ `Bzero.hookBzero`, `memset` ↦ `Fill.hookMemset`, everything else
none) satisfy every hypothesis of the contracts. -/

namespace Poly1305DebianNonvac

open Arm64 Arm64.Obj Poly1305Debian

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

theorem externFns_inj : ∀ e₁ ∈ Link.PlacedLib.externFns libsodiumDebianOnetimeauthLib,
    ∀ e₂ ∈ Link.PlacedLib.externFns libsodiumDebianOnetimeauthLib, pl0.ρ e₁ = pl0.ρ e₂ → e₁ = e₂ := by
  decide +kernel

theorem linkOk : Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthLib pl0 hooks0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e₁ h₁ e₂ h₂ h
    rw [externFns_inj e₁ h₁ e₂ h₂ h]
  · decide +kernel
  · decide +kernel
  · unfold Link.DataDisjoint; decide +kernel
  · decide +kernel

end Poly1305DebianNonvac

end

section
/-!
# Disproof of `Poly1305Debian.internalOk_poly1305_blocks`

The contract `blocksSpec` admits any message length `bytes ≥ 16`. Debian's GCC code computes the end
pointer `x2 = m + bytes` and loops `do { …; m += 16 } while (m != end)` (`cmp x1, x2; b.ne`), so for
`bytes = 17` the second iteration loads 16 bytes at `m + 16`, 15 of them outside the message. With
nothing mapped there the load faults. The placement and hooks are those of the non-vacuity proof
`Poly1305Debian.exists_placement_hooks` (inlined: a disproof cannot import theorems); the method
(concrete state, `exec1`, kernel-evaluated run, heaps for the precondition) follows the disproof of
`Poly1305Libsodium.internalOk_init_update_final_oneshot`.
-/

namespace Poly1305DebianBlocksCex

open Arm64 Arm64.Obj Poly1305Debian Poly1305DebianNonvac
open Poly1305Libsodium (StateOk bytesIn)

/-- Byte `i` of the little-endian number `N`. -/
def byteOf (N i : Nat) : BitVec 8 := BitVec.ofNat 8 (N >>> (8 * i))

/-- The first `n` little-endian bytes of `N`. -/
def bytesOfNat (n N : Nat) : List (BitVec 8) := (List.range n).map (byteOf N)

abbrev P : Program := libsodiumDebianOnetimeauthLib.program pl0 hooks0

/-- The relocated code under `pl0`. -/
def codeN : Nat := 392608241686280855239802867577973438379180087993945370474000957301715568270455099383544063471156358922207090629893922489763303594596934774044383738779191984797616414982108273800967447167692181398525856277451761833054854138591727646212299659547382737132560985926775121105325055957708719645498554905538056387250511254959792414298208467945669938140651441115066748320096605673442071504223091027690233223657603634725329192279029705260242810761192362285331071792148484699512376521386278628850905191684370161794317831617351819825448575440142161767256265224058225819200155250477737766893797369422529000098946184360527203199737420937482874560228572332776262716075285515512495729033756438421616859917718549898510301047043775007101637433377614223437034998564041784292285933088663491430069708625838542856299073050328460177153703387506304872455606795500997490703030950981680558868410012911775017408329777548258071803919251986767922460508791340116739675525306227963143843023440311537169641366463200102192049885498186037532420479089186974912195674359167449938502184026151943456461588203667085437690638539993856176648846680830654538176439196439644079264081380278495078130022892414654405978951820781210739435906583466195341022542076278760469576721442843410772383651713898604705003257652575583177790122633190660852934498091392018149099179451548097512971373437407038686593558571623659955287163836147079322141960761346298476547675701161847683329250847351424472080782579612407203763826297556192576455823967530646713329327896683182189189763468776825629740224938527166381601135183146923241684239935517915948308146306213892337090371570344814816077122272002033088079830898302808482860073615367067638851492383725202905007898911013784389163821538496888068984509921993106567880714433484603536960455483792259245479462905578093428798046733950397472033896376319202969646040456167607963250997562949305264779355366909280472647670246336374083942500342676109975649311618726933259732180678642328067494293475047829606526162804079885563376212278706456216730663726988203574202695272871087382395777222051319928745293144904053042542118466418160107542945656183223088102516557243600365156596447278533969878117598467129085348741813333407222414722455322259796213922884568195230066620386541709935849831987385701620010564388419093605171233834253419002393086166743794102785010843700358721972481837245408255634608242619696044217909563319813745582304224063519328050675059678658316752249755683628381710083930303242311669786745277176876456888975646392066478534979992815893014236261144458815051424543139738598064877117422605113121949999184139975725007204535946040287133858678753714006067259187862517193053146698537546521289129563022542208277303167097593781280511628001643569192653821832662577712221494152671489153097819860903012911392233508645275809382043350391956962143857275995008656143842319332352956188365388390696297146332710842166158825116481308397038552510564788194986339821964812706836274602882260392905835341091847691269247750280443461783805023212881321236341497686609446418207057607493404810454849293173886469043857550933046569225078553072482572253501809390011309427211300389175450255239544173867023490260330910380993693271021135317517147242317643180213230059648695889145841398774743709414972806539727645862029311077732379512796269181468427670800297663453937829608412291664408803729192973993234225449520520423516105597942262936345224115828052375942153853631627415182578497807690289696994448831885373962097177379916811817075307111704771071257065568006878550699278368462012690660546567886616300997433351997218733436505272643805679172081899146394540497770917844230855905214984077822089374150282944615524428771089198919773732916075515480578488840788389742791965991406866190539195685788421624186597251391834123425726427846583198767109476706193374458038262502333829473620639260483745266804822928919586352018906124699242938442328627332550545299277036369342719471472536186259146624301787219478697438331464880127879938925124796511283397696873720386266717065346003852536234297239887688244419189532743507028975547504428025595046074515106317037788785737224587130510820278802065611279293206056313997746577135214673397989049466699450496256483305864444678467891117100477687567796694111561615936254583614981835491731985991978172504427344089377326574561726779942850365490521775693727505221624927

/-- The bundle's code bytes (before relocation). -/
def rawN : Nat := 392608150769187078811687400217603750167961742839567685166263362599817464094354238532982869431950062937321789950533269322852575566061675757526370512918643482182408148420358925064446486049024878187859191251119221247161310875640878638845147464907763241012445151818515914885767891267783040551980275527940273384523836767815918756596385257310002692477740069034524609081399377305290566468702830416068955947225548402458599416067280571592203998321756198594476784210240551751793619196301938282365156528738206138541192743754215911521781120796240466778407345388328592653869158753404821112990373399322887437534166353903349683874437373219668625540530166886944542709378952487119041474018288482474535381006647316831235676913773064915367398702914195072280081101430947515679107634025668498103775927736582579441476909376573144476775227640885627231562407270990639931324393071905369128077551303170000030625684132233285274374301026234719930095774094931666967775635941119786775918757090429369972730551483582388120857838374421980301096500643887006788375565263821251601605001788515815084637908618643695791069155657586410796804265342595996115425373290045533686657900677926035056443939390653514413845569195947877724128450158662320783286686358253859691872461536730577498361194678751685215140581710541720322797053803013293902055329758408450240941729196761386614801608819437543589970248521524653975319254577689928171572064388325888737105187437673493999189929643540327039414190556849122040882249700007115944721009683493320827607201044363840679237225344858931182408501342247287986295078502030685375191624496319028070247636760847645981621832786856082540879464150227851019824538668267579119111960731337181346319560067161603077694576080328345919808630651585162504463221266350115335689039971544423683510944736802486367057952738889499414979721125047993415645628513655274875774975150918478803738960748961542039310263053889226259270605842702109284480360475541722992244770891052297973213032478194543923740017416767825518965799256483512800863355708650938081483623053898401918516008194695637804851289455292326755440174978226292403693720642917590597953395760415435835202125210779109542461222556333866028199910926274647292595887177196192499034417972215027192109156322377622519029835777995473079311089804528833647525772049206734426346687354387504652428628702502163367156057094707757718572396503980609115115740264995925721677053566488906398879218874062735355095866101366927158167748883890450659132991958770053217021363969572967869434380084692921011400753250633168490652010010005733471931156617398987645337770517870623254672711711796502829062703135889742538224222346823352739772930840623383949024810459487278709055525056875187554516118985201192063980922244037820878904660594469732047876496891236996029629209408836123265249357013932801970950411292432521290916445341441005369932657795956631810828337911873347010668270374628409510205039795954408516016760795944855566191742533288940276599590181566759290983034046095993828482242165943955372518038038879587617516606980959711046785469012547025020179736372515487476024146981987769090041378952335944404653709770066303504358498088233743105541150682415208980309269823327296250251666441913490756552643242162828949557290924477416592670449969467030741197638447264154305139070458323286306907663117725171849714876399945515667984081676763563514132406432849629754140703912611219768343678556500701387207684027717102686848656603587883055895976778846824256115719436700241404893298099616288175229642992223789092266914674376657955920289532584404586384449101679468923242348751134259280022844100912646024404860658054718241686309912521924139023673431906000783727295420340059237754934978757901760513223205724817952253058572164123921771288402939807225302085126722413651757281930884606151535484695974589534006760820737273769222613998407304291962279141584575200407969765728908039303916101967725788776156008691501690404873229051425635281198650367209562645623136368430989674062883437175709650634560814862957180494804041005632841241234236408230183644868778921775508141971535658103082140608802950086852088554435329512585975559812716472907178873943884254364395581316685026568645454634342350061571840237746240091024965893443581343325302416042828606643158051605897040127603503710231520200121390829348391880642399261905809097845106589415084100110031287427974839757120607

def stA : BitVec 64 := 0x200000#64
def msgA : BitVec 64 := 0x300000#64
def spA : BitVec 64 := 0x400000#64
def lrA : BitVec 64 := 0x500000#64

def inR (b : BitVec 64) (n : Nat) (a : BitVec 64) : Bool := decide ((a - b).toNat < n)

/-- Code (1800 bytes, `rx`), 96 zero state bytes and 17 zero message bytes (`rw`); nothing else. -/
def mem0 : Memory := Memory.ofFn
  (fun a => if inR pl0.base 1800 a then byteOf codeN (a - pl0.base).toNat else 0)
  (fun a => if inR pl0.base 1800 a then some Perm.rx
    else if inR stA 96 a then some Perm.rw
    else if inR msgA 17 a then some Perm.rw else none)

/-- `x0 = st`, `x1 = m`, `x2 = 17`, `x30 = lrA`. -/
def regs0 : RegFile :=
  ⟨fun i => if i = 0#5 then stA else if i = 1#5 then msgA else if i = 2#5 then 17#64
    else if i = 30#5 then lrA else 0#64⟩

def s0 : State :=
  { regs := regs0, sp := spA,
    pc := libsodiumDebianOnetimeauthLib.fnAddr pl0 "poly1305_blocks [libsodium_la_poly1305_donna]",
    mem := mem0 }

/-- One step of the semantics of `P` away from hook entry points: fetch and execute. -/
def exec1 (s : State) : State :=
  match P.fetchMem s.mem s.pc with
  | some i => P.evalInst i s
  | none => { s with status := .Halted }

/-- A status that is none of the four subroutine outcomes and allows no further step. -/
def isStop : ExecStatus → Bool
  | .Exception _ => true
  | .Halted => true
  | _ => false

/-- Within `n` steps the run, never at `lrA` nor at a hook while running, reaches a stopped
state (`isStop`). -/
def toFault : Nat → State → Bool
  | 0, _ => false
  | n + 1, s => if s.status = .Running then
      (decide (s.pc ≠ lrA) && (P.externAt? s.pc).isNone && toFault n (exec1 s))
    else isStop s.status

/-! ## Kernel facts -/

theorem f_raw : libsodiumDebianOnetimeauthText.code = bytesOfNat 1800 rawN := by
  show libsodiumDebianOnetimeauthPlacedCode = _; decide +kernel

theorem getD_bytesOfNat (n N k : Nat) :
    (bytesOfNat n N).getD k 0#8 = if k < n then byteOf N k else 0#8 := by
  unfold bytesOfNat
  split
  · simp [List.getD_eq_getElem?_getD, *]
  · simp [List.getD_eq_getElem?_getD, *]

/-- The relocated code. `getD` is rewritten to `byteOf` first, so the kernel never walks a list. -/
theorem f_code : P.code = bytesOfNat 1800 codeN := by
  simp only [P, PlacedLib.program, libsodiumDebianOnetimeauthLib, CodeBlock.patched,
    CodeBlock.patchedWord, CodeBlock.wordAt, wordOfBytesLE, f_raw, getD_bytesOfNat]
  decide +kernel

theorem f_traj : toFault 200 s0 = true := by decide +kernel


/-! ## Code loaded -/

theorem toNat_sub_conc (a b : BitVec 64) :
    (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_sub]

theorem code_byte (i : Nat) (hi : i < 1800) :
    mem0.read8 (pl0.base + BitVec.ofNat 64 i) =
        (bytesOfNat 1800 codeN)[i]'(by simp [bytesOfNat]; exact hi) ∧
      mem0.perm (pl0.base + BitVec.ofNat 64 i) = some Perm.rx ∧
      mem0.isLazyFree (pl0.base + BitVec.ofNat 64 i) = false := by
  have e : (pl0.base + BitVec.ofNat 64 i - pl0.base).toNat = i := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  have hin : inR pl0.base 1800 (pl0.base + BitVec.ofNat 64 i) = true := by
    simp only [inR, e]; simpa using hi
  simp only [mem0, Memory.ofFn, Memory.read8, Memory.perm, Memory.isLazyFree, hin, if_true,
    e, bytesOfNat, List.getElem_map, List.getElem_range]
  refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial

theorem codeLoaded : P.CodeLoaded mem0 := by
  have key : ∀ (c : List (BitVec 8)), c = bytesOfNat 1800 codeN →
      ∀ (i : Nat) (hi : i < c.length),
        mem0.read8 (P.base + BitVec.ofNat 64 i) = c[i] ∧
        mem0.perm (P.base + BitVec.ofNat 64 i) = some Perm.rx ∧
        mem0.isLazyFree (P.base + BitVec.ofNat 64 i) = false := by
    intro c hc i hi
    have hb : P.base = pl0.base := rfl
    have hi' : i < 1800 := by rw [hc] at hi; simpa [bytesOfNat] using hi
    have hci : c[i] = (bytesOfNat 1800 codeN)[i]'(by simp [bytesOfNat]; exact hi') := by
      simp only [List.getElem_of_eq hc]
    rw [hb, hci]
    exact code_byte i hi'
  have hl : P.code.length = 1800 := by rw [f_code]; simp [bytesOfNat]
  unfold Program.CodeLoaded
  refine ⟨by decide, by rw [hl]; decide, ?_⟩
  exact key P.code f_code

/-! ## Heaps for the precondition (from the clang one-shot disproof) -/

/-- A heap with no ghost state and no mapping tokens. -/
def Plain (h : Heap) : Prop :=
  (∀ γ k, h.auth γ k = none) ∧ (∀ γ k, h.frag γ k = none) ∧ ∀ a, h.mapped a = false

theorem plain_empty : Plain Heap.empty := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem plain_region (b : BitVec 64) (n : Nat) (m : Memory) : Plain (regionHeap b n m) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem plain_union {h1 h2 : Heap} (p1 : Plain h1) (p2 : Plain h2) : Plain (h1.union h2) := by
  refine ⟨fun γ k => ?_, fun γ k => ?_, fun a => ?_⟩
  · simp [Heap.union, p1.1 γ k, p2.1 γ k]
  · simp [Heap.union, p1.2.1 γ k, p2.2.1 γ k]
  · simp [Heap.union, p1.2.2 a, p2.2.2 a]

theorem disj_of_phys {h1 h2 : Heap} (p1 : Plain h1) (p2 : Plain h2)
    (h : ∀ a, h1.phys a = none ∨ h2.phys a = none) : h1.Disjoint h2 := by
  refine ⟨fun a => ?_, fun γ k => Or.inl (p1.1 γ k), fun γ k => Or.inl (p1.2.1 γ k), ?_,
    fun a => Or.inl (p1.2.2 a)⟩
  · rcases h a with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · intro γ k oa v hc
    rcases hc with ⟨e, _⟩ | ⟨_, e⟩
    · rw [p1.1 γ k] at e; cases e
    · rw [p1.2.1 γ k] at e; cases e

theorem union_phys_none {h1 h2 : Heap} {a : BitVec 64} (e1 : h1.phys a = none)
    (e2 : h2.phys a = none) : (h1.union h2).phys a = none := by
  simp [Heap.union, e1, e2]

theorem matches_union {h1 h2 : Heap} {m : Memory} (p1 : Plain h1) (p2 : Plain h2)
    (m1 : h1.Matches m) (m2 : h2.Matches m) : (h1.union h2).Matches m := by
  refine ⟨fun a c hc => ?_, ⟨0, fun γ _ k => ?_⟩, fun a ha => ?_⟩
  · simp only [Heap.union] at hc
    split at hc
    · rename_i b e; cases hc; exact m1.1 a _ e
    · exact m2.1 a c hc
  · exact ⟨(plain_union p1 p2).1 γ k, (plain_union p1 p2).2.1 γ k⟩
  · rw [(plain_union p1 p2).2.2 a] at ha; cases ha

theorem matches_empty (m : Memory) : Heap.empty.Matches m := by
  refine ⟨fun _ _ hc => ?_, ⟨0, fun _ _ _ => ⟨rfl, rfl⟩⟩, fun _ ha => ?_⟩
  · simp [Heap.empty] at hc
  · simp [Heap.empty] at ha

theorem matches_region {b : BitVec 64} {n : Nat} {m : Memory}
    (h : ∀ a, InRegion b n a → m.perm a = some Perm.rw ∧ m.isLazyFree a = false) :
    (regionHeap b n m).Matches m := by
  refine ⟨fun a c hc => ?_, ⟨0, fun _ _ _ => ⟨rfl, rfl⟩⟩, fun _ ha => by cases ha⟩
  simp only [regionHeap] at hc
  split at hc
  · rename_i hr; cases hc; exact ⟨rfl, h a hr⟩
  · cases hc

theorem region_phys_none {b a : BitVec 64} {n : Nat} {m : Memory} (h : ¬ InRegion b n a) :
    (regionHeap b n m).phys a = none := by simp [regionHeap, h]

theorem inRegion_succ {a x : BitVec 64} {n : Nat} (hn : n + 1 < 2 ^ 64) (hx : x ≠ a) :
    InRegion a (n + 1) x ↔ InRegion (a + 1#64) n x := by
  simp only [InRegion]
  have hx' : x.toNat ≠ a.toNat := fun e => hx (BitVec.eq_of_toNat_eq e)
  have := x.isLt; have := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

theorem not_inRegion_self_succ {a : BitVec 64} {n : Nat} (hn : n + 1 < 2 ^ 64) :
    ¬ InRegion (a + 1#64) n a := by
  simp only [InRegion]
  have := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

theorem points_region : ∀ (n : Nat) (a : BitVec 64) (m : Memory), n < 2 ^ 64 →
    (pointsToBytes a (m.readBytes a n)).holds (regionHeap a n m)
  | 0, a, m, _ => by
    show regionHeap a 0 m = Heap.empty
    apply Heap.ext
    · funext x; simp [regionHeap, InRegion, Heap.empty]
    all_goals rfl
  | n + 1, a, m, hn => by
    refine ⟨Heap.singleton a (m.read8 a), regionHeap (a + 1#64) n m, ?_, ?_, rfl,
      points_region n (a + 1#64) m (by omega)⟩
    · refine disj_of_phys ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩ (plain_region _ _ _)
        fun x => ?_
      by_cases e : x = a
      · subst e; exact Or.inr (region_phys_none (not_inRegion_self_succ hn))
      · exact Or.inl (by simp [Heap.singleton, e])
    · apply Heap.ext
      · funext x
        by_cases e : x = a
        · subst e
          have : InRegion x (n + 1) x := by simp [InRegion]
          simp [regionHeap, Heap.union, Heap.singleton, this]
        · have := inRegion_succ hn e
          simp only [regionHeap, Heap.union, Heap.singleton, e, if_false]
          by_cases r : InRegion (a + 1#64) n x
          · simp [r, this.2 r]
          · have r' : ¬ InRegion a (n + 1) x := fun h => r (this.1 h)
            simp [r, r']
      all_goals rfl

theorem sep_intro {P Q : SepProp} {h1 h2 : Heap} (hd : h1.Disjoint h2) (p : P.holds h1)
    (q : Q.holds h2) : (P ∗ Q).holds (h1.union h2) := ⟨h1, h2, hd, rfl, p, q⟩

theorem pure_intro {φ : Prop} (hφ : φ) : (⌜φ⌝ : SepProp).holds Heap.empty := ⟨rfl, hφ⟩

theorem emp_intro : (emp : SepProp).holds Heap.empty := rfl

theorem disj_empty_left {h : Heap} (p : Plain h) : Heap.empty.Disjoint h :=
  disj_of_phys plain_empty p fun _ => Or.inl rfl

theorem disj_empty_right {h : Heap} (p : Plain h) : h.Disjoint Heap.empty :=
  disj_of_phys p plain_empty fun _ => Or.inr rfl

theorem region_num {b a : BitVec 64} {n : Nat} (h : InRegion b n a) :
    (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < n := by
  simp only [InRegion] at h; rwa [toNat_sub_conc] at h

theorem not_inR_of {b a : BitVec 64} {n : Nat}
    (h : ¬ (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < n) : inR b n a = false := by
  simp only [inR, toNat_sub_conc]; simpa using h

theorem inR_of {b a : BitVec 64} {n : Nat}
    (h : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < n) : inR b n a = true := by
  simp only [inR, toNat_sub_conc]; simpa using h

/-- `h` has cells only where `S` holds. -/
def Supp (h : Heap) (S : BitVec 64 → Prop) : Prop := ∀ a, ¬ S a → h.phys a = none

theorem supp_region (b : BitVec 64) (n : Nat) (m : Memory) : Supp (regionHeap b n m) (InRegion b n) :=
  fun _ h => region_phys_none h

theorem supp_union {h1 h2 : Heap} {S T : BitVec 64 → Prop} (a : Supp h1 S) (b : Supp h2 T) :
    Supp (h1.union h2) (fun x => S x ∨ T x) := fun x hx =>
  union_phys_none (a x fun h => hx (Or.inl h)) (b x fun h => hx (Or.inr h))

theorem disj_supp {h1 h2 : Heap} {S T : BitVec 64 → Prop} (p1 : Plain h1) (p2 : Plain h2)
    (a : Supp h1 S) (b : Supp h2 T) (hd : ∀ x, S x → ¬ T x) : h1.Disjoint h2 :=
  disj_of_phys p1 p2 fun x => by
    by_cases hs : S x
    · exact Or.inr (b x (hd x hs))
    · exact Or.inl (a x hs)

/-! ## Memory regions of `mem0` -/

theorem mem0_st {x : BitVec 64} (h : InRegion stA 96 x) :
    mem0.perm x = some Perm.rw ∧ mem0.isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  simp only [stA, BitVec.toNat_ofNat] at hx
  have h1 : inR pl0.base 1800 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR stA 96 x = true := inR_of (by simp only [stA, BitVec.toNat_ofNat]; omega)
  simp only [mem0, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2]; exact ⟨rfl, rfl⟩

theorem mem0_msg {x : BitVec 64} (h : InRegion msgA 17 x) :
    mem0.perm x = some Perm.rw ∧ mem0.isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  simp only [msgA, BitVec.toNat_ofNat] at hx
  have h1 : inR pl0.base 1800 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR stA 96 x = false := not_inR_of (by simp only [stA, BitVec.toNat_ofNat]; omega)
  have h3 : inR msgA 17 x = true := inR_of (by simp only [msgA, BitVec.toNat_ofNat]; omega)
  simp only [mem0, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2, h3]; exact ⟨rfl, rfl⟩

theorem sub_region {b c x : BitVec 64} {n k : Nat}
    (hk : (2 ^ 64 - b.toNat + c.toNat) % 2 ^ 64 + k ≤ n) (h : InRegion c k x) : InRegion b n x := by
  have := region_num h
  simp only [InRegion, toNat_sub_conc]
  have := x.isLt; have := b.isLt; have := c.isLt
  omega

/-! ## The precondition -/

def rh0 : List (BitVec 8) := mem0.readBytes stA 48
def fin0 : List (BitVec 8) := mem0.readBytes (stA + 88#64) 1
def msg0 : List (BitVec 8) := mem0.readBytes msgA 17

theorem fin0_eq : fin0 = [0#8] := by decide +kernel

theorem s0_x0 : s0.readReg64 Reg.x0 = stA := by decide
theorem s0_x1 : s0.readReg64 Reg.x1 = msgA := by decide

theorem f_pure : StateOk rh0 ∧ (s0.readReg64 Reg.x2).toNat = msg0.length ∧ 16 ≤ msg0.length := by
  unfold StateOk; decide +kernel

theorem hpre : s0.mem ⊨ blocksSpec.pre (false, rh0, 0#8, msg0) s0 ∗ emp := by
  let m := mem0
  have e88 : (stA + 88#64).toNat = 2097240 := by decide
  have D3 : (regionHeap (stA + 88#64) 1 m).Disjoint (regionHeap msgA 17 m) :=
    disj_supp (plain_region _ _ _) (plain_region _ _ _) (supp_region _ _ _)
      (supp_region _ _ _) (fun x h1 h2 => by
        have a1 := region_num h1; have a2 := region_num h2; have := x.isLt
        rw [e88] at a1; simp only [msgA, BitVec.toNat_ofNat] at a2; omega)
  have P34 := plain_union (plain_region (stA + 88#64) 1 m) (plain_region msgA 17 m)
  have D2 : (regionHeap stA 48 m).Disjoint
      ((regionHeap (stA + 88#64) 1 m).union (regionHeap msgA 17 m)) :=
    disj_supp (plain_region _ _ _) P34 (supp_region _ _ _)
      (supp_union (supp_region _ _ _) (supp_region _ _ _)) (fun x h1 h2 => by
        have a1 := region_num h1; have := x.isLt
        simp only [stA, BitVec.toNat_ofNat] at a1
        rcases h2 with h2 | h2
        · have a2 := region_num h2; rw [e88] at a2; omega
        · have a2 := region_num h2; simp only [msgA, BitVec.toNat_ofNat] at a2; omega)
  have P234 := plain_union (plain_region stA 48 m) P34
  refine ⟨_, sep_intro (disj_empty_right (plain_union plain_empty P234))
    (sep_intro (disj_empty_left P234) (pure_intro f_pure)
      (sep_intro D2 ?_ (sep_intro D3 ?_ ?_))) emp_intro, ?_⟩
  · rw [s0_x0]; exact points_region 48 stA mem0 (by omega)
  · rw [s0_x0, ← fin0_eq]; exact points_region 1 (stA + 88#64) mem0 (by omega)
  · show (bytesIn false (s0.readReg64 Reg.x1) msg0).holds _
    rw [s0_x1]; exact points_region 17 msgA mem0 (by omega)
  · exact matches_union (plain_union plain_empty P234) plain_empty
      (matches_union plain_empty P234 (matches_empty _)
        (matches_union (plain_region _ _ _) P34
          (matches_region fun _ h => mem0_st (sub_region (by decide) h))
          (matches_union (plain_region _ _ _) (plain_region _ _ _)
            (matches_region fun _ h => mem0_st (sub_region (by decide) h))
            (matches_region fun _ h => mem0_msg h))))
      (matches_empty _)

/-! ## Determinism away from hooks, and the run to the fault -/

theorem step_exec1 {s s' : State} (hx : P.externAt? s.pc = none) (h : Step P s s') :
    s.status = .Running ∧ s' = exec1 s := by
  cases h with
  | exec hr hf => exact ⟨hr, by simp [exec1, hf]⟩
  | halt_unmapped hr hf _ => exact ⟨hr, by simp [exec1, hf]⟩
  | externHook _ he _ _ => rw [hx] at he; cases he
  | extern_fault _ he _ => rw [hx] at he; cases he

theorem no_step {s s' : State} (h : Step P s s') : s.status = .Running := by
  cases h <;> assumption

theorem toFault_safe : ∀ (n : Nat) (s sf : State), toFault n s = true → Steps P s sf →
    (sf.status = .Running ∧ sf.pc ≠ lrA) ∨ isStop sf.status = true
  | 0, _, _, ht, _ => by simp [toFault] at ht
  | n + 1, s, sf, ht, hs => by
    simp only [toFault] at ht
    by_cases hr : s.status = .Running
    · rw [if_pos hr] at ht
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at ht
      obtain ⟨⟨hl, hx⟩, ht⟩ := ht
      cases hs with
      | refl => exact Or.inl ⟨hr, hl⟩
      | step h1 h2 =>
        obtain ⟨_, rfl⟩ := step_exec1 hx h1
        exact toFault_safe n _ sf ht h2
    · rw [if_neg hr] at ht
      cases hs with
      | refl => exact Or.inr ht
      | step h1 _ => exact absurd (no_step h1) hr

/-! ## The disproof -/

theorem not_internalOk_poly1305_blocks :
    ¬ internalOk "poly1305_blocks [libsodium_la_poly1305_donna]" (fun _ => blocksSpec) := by
  rintro ⟨-, h⟩
  have hok := h pl0 placeable guardUniform hooks0 memzeroOk memsetOk linkOk
  obtain ⟨sf, hs, hout⟩ :=
    hok (false, rh0, 0#8, msg0) emp s0 rfl rfl hpre (by decide) codeLoaded
  have hsafe := toFault_safe 200 s0 sf f_traj hs
  rcases hout with ⟨⟨hpcf, _, hrun⟩, _, _⟩ | ⟨h1, _⟩ | ⟨c, h1, _⟩ | ⟨h1, _⟩
  · rcases hsafe with ⟨_, hne⟩ | hst
    · exact hne (hpcf.trans (by decide))
    · rw [hrun] at hst; cases hst
  · rcases hsafe with ⟨h2, _⟩ | hst
    · rw [h2] at h1; cases h1
    · rw [h1] at hst; cases hst
  · rcases hsafe with ⟨h2, _⟩ | hst
    · rw [h2] at h1; cases h1
    · rw [h1] at hst; cases hst
  · rcases hsafe with ⟨h2, _⟩ | hst
    · rw [h2] at h1; cases h1
    · rw [h1] at hst; cases hst

end Poly1305DebianBlocksCex
end
theorem solution :
    ¬ Poly1305Debian.internalOk "poly1305_blocks [libsodium_la_poly1305_donna]"
      (fun _ => Poly1305Debian.blocksSpec) :=
  Poly1305DebianBlocksCex.not_internalOk_poly1305_blocks

