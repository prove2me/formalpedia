-- Prove2me | solution 1 for Poly1305Libsodium.internalOk_init_update_final_oneshot
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-11-24T23:14:30.806254+00:00
-- url     : https://prove2.me/submissions/13e72391-b82e-40ec-998f-de69ca03333d

import Definitions.Def_Poly1305Libsodium_Spec

/-!
# Disproof of `Poly1305Libsodium.internalOk_init_update_final_oneshot`

Adapted from the accepted disproof of the sibling statement
`Poly1305Libsodium.internalOk_poly1305_finish` (poly1305-libsodium-aarch64,
`proofs/internalOk_poly1305_finish/disproof/solution.lean`), whose counterexample, hooks, heap
lemmas and kernel-evaluated run this file reuses; credit to that disproof (and, through it, to the
BoringSSL Poly1305 disproof, q453).

The same placement (both externs at `0x20000`, so the hook found there is `crypto_verify_16`'s,
`id`) breaks `oneshotOk`: the one-shot `crypto_onetimeauth_poly1305_donna`, entered with an empty
message, runs its prologue and inlined init, skips the block call and the tail copy, calls
`poly1305_finish`, whose tail call `b sodium_memzero` lands on `0x20000` and never returns.
So the conjunction is false via its second component.
-/

section
/-! Non-vacuity of `Libc.explicitBzeroSpec`: a hook that writes `x1` zero bytes at `x0` and
returns to `x30` meets the contract. Self-contained against the published bundles (the upstream
version in `exists_hookOk_explicitBzeroSpec.upstream.lean` uses DeepMind's ProofLib). -/

open Arm64

namespace Libc.BzeroHook

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

theorem hookBzero_ok : HookOk hookBzero explicitBzeroSpec := by
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

end Libc.BzeroHook
end

section
/-! Concrete data (adapted from the disproof of `Poly1305Libsodium.internalOk_poly1305_finish`).

Both externs of the library are placed at `0x20000`. The program's hook table lists
`crypto_verify_16` first, so the hook found at `0x20000` is `crypto_verify_16`'s, here `id`, and
the tail call `b sodium_memzero` of `poly1305_finish` (called by the one-shot) lands on a step
that maps the state to itself for ever. `sodium_memzero`'s hook is the zeroing hook `Libc.BzeroHook.hookBzero`, which meets
`Libc.explicitBzeroSpec`. Byte strings are little-endian natural numbers (`byteOf`). -/

namespace Poly1305Libsodium.FinCex

open Arm64 Arm64.Obj

/-- Byte `i` of the little-endian number `N`. -/
def byteOf (N i : Nat) : BitVec 8 := BitVec.ofNat 8 (N >>> (8 * i))
/-- The first `n` little-endian bytes of `N`. -/
def bytesOfNat (n N : Nat) : List (BitVec 8) := (List.range n).map (byteOf N)

def hookA : BitVec 64 := 0x20000#64
def pl0 : Placement := { base := 0x10000#64, ρ := fun _ => hookA }

/-- `crypto_verify_16` does nothing; `sodium_memzero` zeroes. -/
def exts : String → Option (State → State) := fun n =>
  if n = "crypto_verify_16" then some id
  else if n = "sodium_memzero" then some Libc.BzeroHook.hookBzero else none

abbrev P : Program := libsodiumPoly1305Lib.program pl0 exts

/-- The relocated code under `pl0`. -/
def codeN : Nat := 66975806172950862150681441686323622314505214705902697587562565109415162731792384638437996115083670842930751576992167044214476873117551644079306726779953225809486259944194127360195852639483542133519873824282199307990511976254429724602214360378211623902837645035901845114114802090552857627741853895802348690897541799017803796338523806968748516591611088883773259469034846128668904363346551719337114355946041831740080800891948581276022231203802479084345815610180094687491958648218903211391141740296546772828031011305601627113345890393056027097251940760756853481194511516899293076596773160350361283904866059494700042983121911336392336179180933893204577526617728020006983330788628034800004491717495830548173428744740904598766862768114461682868939206940674321774456799338054920613986917738419843657544663813909045985670974961445608166246586689838120006323929597767578903152763724006157899998739623475352847377019671677707281640150678523593995058963799864802581409432887125040254549956635911023707207839281311957888903511628396934714212966272212039686918147999846670471678854298724044874439746947286916722692189903991259999615882842156793797645810983164880860197179355866639406791403725410984275983036829763324779538482316680034467967449855045958525985676421227648746354606585040570223218049150216020171509211112010836501361937530826316240130735630354351372948560919297614316545986046728456394542827908236399774700429921076796959457646233940124034479040739994632368338148571190121404093305349087081020130430221494484648923071543707862904437462068083499483468894552785323995606598031873324672595543180945002954796380922672907222303587993015945802900737804688380834257694387765921909192980157177176281259021644191010295402676808463390376334712000160087820180401918713094162552193404791834396612596194249413402041464874398423568410365451205868874988629450600596163468791313927609745805422822233362125553388627703455497954643057590891432000232971107537027095347150156947898976600175938156477132534338420918496056052607197716158663175516092003909504124809640358315797552057079485744581586767949328066069059260693399880894260385976473776157203304745533910949186535609567569940933461371733358424950366557859233797390245588453964304945520461146857706088352367518504320383556163123116577234854813227215702637004397425432668346257395430627511089887817277587861854967535848984976723324446741944192764056958604318722375684010062246633802946609809440555179745989760167273065688858118754165602218766762098215725631474452099493652576844617801093281727948534525120343054133934276210330124302893661534400921950612317672191446821308867169171837797972988630969956426238112049184458790379496965682635351905986025042772386066230323795097091908102737272950369423889719884023964240289513995124604182012648950172938700237084942216504855871758918295277556502934996312880253297673659082812803275798564047363058948333064732913076283172501530194551414682373052059683463181197610426243980828430858308218686148571429023020534156992694669113694037828878893688650855404820772102257239760419701518711343833905045751734858471815216888359758147532062084764840233425473706772299915966879543964182765127362359591937372726379068278890431034000148840817195068392693312873960830551058017151271591429374304167239844269295982533692470859175731106252983326156480495500751496268106829176367098036047428431963323389
/-- The bundle's code bytes (before relocation). -/
def rawN : Nat := 66975806172950862150681441686323622314505214705902697587562565109415162731792384638437996115083670842930751576992167044214476873117551644079306726779953225809486259944194127360195852639483542133519873824282199307990511976254429724602214360378211623902837645035901845114114802090552857627741853895802348690897541799017803796338523806968748516591611088883773259469034846128668904363346551719337114355946041831740080800891948581276022231203802479084345815610180094687491958648218903211391141740296546772828031011305601627113345890393056027097251940760756853481194511516899293076596773160350361283904866059494700042983121911336392336179180933893204577526617728020006983330788628034800004491717495830548173428744740904598766862768114461682868939206940674321774444024191350067724990999049071586247122830192637769755757351866695490932593268394237183626754452379091103610812794658407596567559966607536480533112976719734331779361455088576434652297790167528374704730430647418190147206075815980622638386326945514454499221240549409219835074380086011893933578163665167730488969621884830429253110595237748566591433278449990797212447332770446936528357227815227884224085559050474252047484445893661429154148671934352613474095599702602111093086044511098004191030371162570425046384438914453881539713668310157217103592609832507462031254143903334563301947763149562618518424460721693797361333146452568927531024280978618077539683924827740756272080421103408118872074290245760369926177250865100792928288005695932648543440633288192611649789357904389224399868658861137737142472225583471857681331532276995285187370260353843844662340011765229821832802854549526386494913701398035041051239381288234710987153267419178531636378777295928742325904065999246266989366063804599776009650897827974989563001684921936628594347702347843999164933209210314595689271311138354836663077858607550815024772014493419261909479932032486458416012264569161909450943186217869679216614792707947393005659621117701056990422659716107438015177511224609202029031011866139865542837017052398699478105781975984587771367396211366144997955152600859531880915226832802227978066174137768790559283932641715110520854677437530616800604626523168204622218771739399931499559301327976534884705685219096602579457951502107971975775988273930048274477766465676541098005207075067102006182435182245517278689473797038914407647545701134850541457653948847573736053040835220737277522447854210153907575764046531545659085166894591042314718887911805128666944553175474794612548631037270095376646641262274816875623879856580952814226382247310275689369796822610470429526851283176163595012117559473225443487732660799944915079766894871772380665519277811951712967616602797024566045778134971475735225031868856790900562225284961226320557165529994302956190717728373792567525679893462400001280333316138181820555802131633291832708228084558422917182814248711280473624591529921298117175747870226505366010502025254756279615332762462651092231490874660161195703046990402548620222048704136450455965345393909034023021912536377876392917777132731478755066181134657160507744468706149752310782436292649053335271181198691141310018055565612540621565277005176915001998584934174243709390375921142941755636796199720952625335614275879717002460729057244992810283032500992973172339894954112472955578766501823874053837704024224568384535800504729215656391163420920958007248571586149373

def outA : BitVec 64 := 0x31000#64
def keyA : BitVec 64 := 0x32000#64
def msgA : BitVec 64 := 0x33000#64
def spA : BitVec 64 := 0x40000#64
def lrA : BitVec 64 := 0x50000#64
def inR (b : BitVec 64) (n : Nat) (a : BitVec 64) : Bool := decide ((a - b).toNat < n)

/-- Code, a zero output buffer (16 bytes), a zero key (32 bytes), 4336 bytes of stack. -/
def mem0 : Memory := Memory.ofFn
  (fun a => if inR pl0.base 1396 a then byteOf codeN (a - pl0.base).toNat else 0)
  (fun a => if inR pl0.base 1396 a then some Perm.rx
    else if inR outA 16 a then some Perm.rw
    else if inR keyA 32 a then some Perm.rw
    else if inR (spA - 4336#64) 4336 a then some Perm.rw else none)

/-- `x0 = out`, `x1 = m` (empty message), `x2 = 0`, `x3 = key`, `x30 = lrA`. -/
def regs0 : RegFile :=
  ⟨fun i => if i = 0#5 then outA else if i = 1#5 then msgA else if i = 3#5 then keyA
    else if i = 30#5 then lrA else 0#64⟩

def s0 : State :=
  { regs := regs0, sp := spA,
    pc := libsodiumPoly1305Lib.fnAddr pl0 "crypto_onetimeauth_poly1305_donna [libsodium_poly1305_donna]",
    mem := mem0 }

/-- One step of the semantics of `P`: at `hookA` the hook `id`, elsewhere fetch and execute. -/
def exec1 (s : State) : State :=
  if s.pc = hookA then s else
  match P.fetchMem s.mem s.pc with
  | some i => P.evalInst i s
  | none => { s with status := .Halted }

/-- Within `n` steps the run stays `Running`, never reaches `lrA`, and arrives at `hookA`. -/
def toHook : Nat → State → Bool
  | 0, s => s.pc = hookA ∧ s.status = .Running
  | n + 1, s => if s.pc = hookA then s.status = .Running
    else if s.pc = lrA then false
    else if s.status = .Running then toHook n (exec1 s) else false

end Poly1305Libsodium.FinCex
end

section
/-! Facts about the concrete run, checked by kernel evaluation (`decide +kernel`). -/

namespace Poly1305Libsodium.FinCex

open Arm64 Arm64.Obj

theorem f_raw : libsodiumPoly1305Text.code = bytesOfNat 1396 rawN := by
  show libsodiumPoly1305PlacedCode = _; decide +kernel

theorem getD_bytesOfNat (n N k : Nat) :
    (bytesOfNat n N).getD k 0#8 = if k < n then byteOf N k else 0#8 := by
  unfold bytesOfNat
  split
  · simp [List.getD_eq_getElem?_getD, *]
  · simp [List.getD_eq_getElem?_getD, *]

/-- The relocated code. `getD` is rewritten to `byteOf` first, so the kernel never walks a list. -/
theorem f_code : P.code = bytesOfNat 1396 codeN := by
  simp only [P, PlacedLib.program, libsodiumPoly1305Lib, CodeBlock.patched, CodeBlock.patchedWord,
    CodeBlock.wordAt, wordOfBytesLE, f_raw, getD_bytesOfNat]
  decide +kernel

theorem f_traj : toHook 200 s0 = true := by decide +kernel

theorem f_pure : (mem0.readBytes outA 16).length = 16 ∧
    (s0.readReg64 Reg.x2).toNat = (mem0.readBytes msgA 0).length ∧
    (mem0.readBytes keyA 32).length = 32 := by
  decide +kernel

end Poly1305Libsodium.FinCex
end

section
/-! Generic lemmas for the disproof (adapted from the BoringSSL Poly1305 disproof, q453,
`Solutions/Poly1305BoringsslGoal/Gen.lean`): heaps for the precondition. -/

namespace Poly1305Libsodium.FinCex

open Arm64 Arm64.Obj

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

end Poly1305Libsodium.FinCex
end

section
/-! # `oneshotOk` is false (adapted from the `internalOk_poly1305_finish` disproof)

With both externs at `0x20000`, `crypto_verify_16`'s hook `id` and `sodium_memzero`'s hook the
zeroing hook (which meets `Libc.explicitBzeroSpec`, so `MemzeroOk exts` holds), the one-shot
entered with an empty message runs its prologue and inlined init on the stack, skips the blocks
and the tail copy, and calls `poly1305_finish` (`leftover = 0`), whose tail call
`b sodium_memzero` lands on `0x20000`. There `externAt?` returns `crypto_verify_16`'s hook, the first stub at
that offset, and every later step maps the state to itself. The run never returns, so no
`SubroutineOutcome` is reached. -/

namespace Poly1305Libsodium.FinCex

open Arm64 Arm64.Obj

/-! ## Placement and code -/

theorem code_len : libsodiumPoly1305Lib.text.code.length = 1396 := by
  show libsodiumPoly1305Text.code.length = 1396
  rw [f_raw]; simp [bytesOfNat]

theorem placeable : libsodiumPoly1305Lib.Placeable pl0 := by
  refine ⟨⟨by decide, by decide +kernel, by rw [code_len]; decide, by rw [code_len],
    by decide +kernel, ?_, ?_, ?_, ?_⟩,
    by simp [libsodiumPoly1305Lib, libsodiumPoly1305Data],
    by simp [libsodiumPoly1305Lib, libsodiumPoly1305Data],
    by simp [libsodiumPoly1305Lib, libsodiumPoly1305Data]⟩
  · intro r hr
    rw [code_len]
    simp only [libsodiumPoly1305Lib, libsodiumPoly1305Text, List.mem_cons, List.mem_nil_iff,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by decide, by decide, ?_⟩ <;>
      simp only [CodeBlock.relocInRange, CodeRelocInRange, BranchInRange] <;> decide +kernel
  · intro off r h
    simp [CodeBlock.relaxedAt, pl0] at h
  · intro s hs
    rw [code_len]
    simp only [libsodiumPoly1305Lib, libsodiumPoly1305Text, List.mem_cons, List.mem_nil_iff,
      or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he
    rw [code_len]
    simp only [libsodiumPoly1305Lib, libsodiumPoly1305Text, List.mem_cons, List.mem_nil_iff,
      or_false] at he
    rcases he with rfl | rfl <;> decide +kernel

theorem toNat_sub_conc (a b : BitVec 64) :
    (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_sub]

theorem code_byte (i : Nat) (hi : i < 1396) :
    mem0.read8 (pl0.base + BitVec.ofNat 64 i) =
        (bytesOfNat 1396 codeN)[i]'(by simp [bytesOfNat]; exact hi) ∧
      mem0.perm (pl0.base + BitVec.ofNat 64 i) = some Perm.rx ∧
      mem0.isLazyFree (pl0.base + BitVec.ofNat 64 i) = false := by
  have e : (pl0.base + BitVec.ofNat 64 i - pl0.base).toNat = i := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  have hin : inR pl0.base 1396 (pl0.base + BitVec.ofNat 64 i) = true := by
    simp only [inR, e]; simpa using hi
  simp only [mem0, Memory.ofFn, Memory.read8, Memory.perm, Memory.isLazyFree, hin, if_true,
    e, bytesOfNat, List.getElem_map, List.getElem_range]
  refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial

theorem codeLoaded : P.CodeLoaded mem0 := by
  have key : ∀ (c : List (BitVec 8)), c = bytesOfNat 1396 codeN →
      ∀ (i : Nat) (hi : i < c.length),
        mem0.read8 (P.base + BitVec.ofNat 64 i) = c[i] ∧
        mem0.perm (P.base + BitVec.ofNat 64 i) = some Perm.rx ∧
        mem0.isLazyFree (P.base + BitVec.ofNat 64 i) = false := by
    intro c hc i hi
    have hb : P.base = pl0.base := rfl
    have hi' : i < 1396 := by rw [hc] at hi; simpa [bytesOfNat] using hi
    have hci : c[i] = (bytesOfNat 1396 codeN)[i]'(by simp [bytesOfNat]; exact hi') := by
      simp only [List.getElem_of_eq hc]
    rw [hb, hci]
    exact code_byte i hi'
  have hl : P.code.length = 1396 := by rw [f_code]; simp [bytesOfNat]
  unfold Program.CodeLoaded
  refine ⟨by decide, by rw [hl]; decide, ?_⟩
  exact key P.code f_code

/-! ## Memory regions of `mem0` -/

theorem region_num {b a : BitVec 64} {n : Nat} (h : InRegion b n a) :
    (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < n := by
  simp only [InRegion] at h; rwa [toNat_sub_conc] at h

theorem not_inR_of {b a : BitVec 64} {n : Nat}
    (h : ¬ (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < n) : inR b n a = false := by
  simp only [inR, toNat_sub_conc]; simpa using h

theorem inR_of {b a : BitVec 64} {n : Nat}
    (h : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < n) : inR b n a = true := by
  simp only [inR, toNat_sub_conc]; simpa using h

theorem mem0_out {x : BitVec 64} (h : InRegion outA 16 x) :
    mem0.perm x = some Perm.rw ∧ mem0.isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  simp only [outA, BitVec.toNat_ofNat] at hx
  have h1 : inR pl0.base 1396 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR outA 16 x = true := inR_of (by simp only [outA, BitVec.toNat_ofNat]; omega)
  simp only [mem0, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2]; exact ⟨rfl, rfl⟩

theorem mem0_key {x : BitVec 64} (h : InRegion keyA 32 x) :
    mem0.perm x = some Perm.rw ∧ mem0.isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  simp only [keyA, BitVec.toNat_ofNat] at hx
  have h1 : inR pl0.base 1396 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR outA 16 x = false := not_inR_of (by simp only [outA, BitVec.toNat_ofNat]; omega)
  have h3 : inR keyA 32 x = true := inR_of (by simp only [keyA, BitVec.toNat_ofNat]; omega)
  simp only [mem0, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2, h3]; exact ⟨rfl, rfl⟩

theorem mem0_stk {x : BitVec 64} (h : InRegion (spA - 4336#64) 4336 x) :
    mem0.perm x = some Perm.rw ∧ mem0.isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  have e : (spA - 4336#64).toNat = 0x40000 - 4336 := by decide
  rw [e] at hx
  have h1 : inR pl0.base 1396 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR outA 16 x = false := not_inR_of (by simp only [outA, BitVec.toNat_ofNat]; omega)
  have h3 : inR keyA 32 x = false := not_inR_of (by simp only [keyA, BitVec.toNat_ofNat]; omega)
  have h4 : inR (spA - 4336#64) 4336 x = true := inR_of (by rw [e]; omega)
  simp only [mem0, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2, h3, h4]
  exact ⟨rfl, rfl⟩

theorem mem0_msg {x : BitVec 64} (h : InRegion msgA 0 x) :
    mem0.perm x = some Perm.rw ∧ mem0.isLazyFree x = false := by
  have hx := region_num h; omega

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

theorem sep_reg {b1 b2 : BitVec 64} {n1 n2 : Nat}
    (h : (b1.toNat + n1 ≤ b2.toNat ∨ b2.toNat + n2 ≤ b1.toNat) ∧ b1.toNat + n1 ≤ 2 ^ 64 ∧
      b2.toNat + n2 ≤ 2 ^ 64) :
    ∀ x, InRegion b1 n1 x → ¬ InRegion b2 n2 x := by
  intro x h1 h2
  have := region_num h1; have := region_num h2; have := x.isLt
  omega

/-! ## The precondition -/

def out0 : List (BitVec 8) := mem0.readBytes outA 16
def msg0 : List (BitVec 8) := mem0.readBytes msgA 0
def key0 : List (BitVec 8) := mem0.readBytes keyA 32

theorem s0_x0 : s0.readReg64 Reg.x0 = outA := by decide
theorem s0_x1 : s0.readReg64 Reg.x1 = msgA := by decide
theorem s0_x3 : s0.readReg64 Reg.x3 = keyA := by decide

theorem hpre : s0.mem ⊨ oneshotSpec.pre (false, false, out0, msg0, key0) s0 ∗ emp := by
  let m := mem0
  have hsp : s0.sp - BitVec.ofNat 64 4336 = spA - 4336#64 := rfl
  -- key ∗ stack
  have D4 : (regionHeap keyA 32 m).Disjoint (regionHeap (spA - 4336#64) 4336 m) :=
    disj_supp (plain_region _ _ _) (plain_region _ _ _) (supp_region _ _ _)
      (supp_region _ _ _) (sep_reg (by decide))
  have P45 := plain_union (plain_region keyA 32 m) (plain_region (spA - 4336#64) 4336 m)
  -- msg ∗ (key ∗ stack)
  have D3 : (regionHeap msgA 0 m).Disjoint
      ((regionHeap keyA 32 m).union (regionHeap (spA - 4336#64) 4336 m)) :=
    disj_supp (plain_region _ _ _) P45 (supp_region _ _ _)
      (supp_union (supp_region _ _ _) (supp_region _ _ _)) (fun x hx _ => by
        have := region_num hx; omega)
  have P345 := plain_union (plain_region msgA 0 m) P45
  -- out ∗ (msg ∗ (key ∗ stack))
  have D2 : (regionHeap outA 16 m).Disjoint
      ((regionHeap msgA 0 m).union
        ((regionHeap keyA 32 m).union (regionHeap (spA - 4336#64) 4336 m))) :=
    disj_supp (plain_region _ _ _) P345 (supp_region _ _ _)
      (supp_union (supp_region _ _ _) (supp_union (supp_region _ _ _) (supp_region _ _ _)))
      (fun x hx hy => by
        rcases hy with hy | hy | hy
        · have := region_num hy; omega
        · exact sep_reg (by decide) x hx hy
        · exact sep_reg (by decide) x hx hy)
  have P2345 := plain_union (plain_region outA 16 m) P345
  refine ⟨_, sep_intro (disj_empty_right (plain_union plain_empty P2345))
    (sep_intro (disj_empty_left P2345) (pure_intro f_pure)
      (sep_intro D2 ?_ (sep_intro D3 ?_ (sep_intro D4 ?_ ?_)))) emp_intro, ?_⟩
  · rw [s0_x0]; exact points_region 16 outA mem0 (by omega)
  · show (bytesIn false (s0.readReg64 Reg.x1) msg0).holds _
    rw [s0_x1]; exact points_region 0 msgA mem0 (by omega)
  · show (bytesIn false (s0.readReg64 Reg.x3) key0).holds _
    rw [s0_x3]; exact points_region 32 keyA mem0 (by omega)
  · show (memRegion (s0.sp - BitVec.ofNat 64 4336) 4336).holds _
    rw [hsp]; exact ⟨mem0, rfl⟩
  · exact matches_union (plain_union plain_empty P2345) plain_empty
      (matches_union plain_empty P2345 (matches_empty _)
        (matches_union (plain_region _ _ _) P345
          (matches_region fun _ h => mem0_out h)
          (matches_union (plain_region _ _ _) P45
            (matches_region fun _ h => mem0_msg h)
            (matches_union (plain_region _ _ _) (plain_region _ _ _)
              (matches_region fun _ h => mem0_key h)
              (matches_region fun _ h => mem0_stk h)))))
      (matches_empty _)

/-! ## Hooks -/

theorem memzeroOk : MemzeroOk exts :=
  ⟨Libc.BzeroHook.hookBzero, by simp [exts], Libc.BzeroHook.hookBzero_ok⟩

theorem externAt_eq (pc : BitVec 64) : P.externAt? pc = if pc = hookA then some id else none := by
  simp only [Program.externAt?, Program.hookAtOff?, P, PlacedLib.program, libsodiumPoly1305Lib,
    libsodiumPoly1305Text, pl0, List.map_cons, List.map_nil, List.findSome?_cons,
    List.findSome?_nil]
  by_cases h : pc = hookA
  · subst h; simp [exts]
  · have hne : ¬ ((18446744073709486080 + hookA.toNat) % 18446744073709551616 =
        (18446744073709486080 + pc.toNat) % 18446744073709551616) := by
      intro e; apply h; apply BitVec.eq_of_toNat_eq
      have h1 : hookA.toNat = 0x20000 := rfl
      have := pc.isLt
      omega
    simp [hne, h]

/-! ## Determinism: the run never leaves the hook -/

theorem keepsFrozen_refl (m : Memory) : m.KeepsFrozen m := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

theorem step_exec1 {s s' : State} (h : Step P s s') : s.status = .Running ∧ s' = exec1 s := by
  cases h with
  | exec hr hf =>
    refine ⟨hr, ?_⟩
    have hp : s.pc ≠ hookA := by
      intro e; simp [Program.fetchMem, externAt_eq, e] at hf
    simp [exec1, hp, hf]
  | halt_unmapped hr hf he =>
    refine ⟨hr, ?_⟩
    have hp : s.pc ≠ hookA := by
      intro e; rw [externAt_eq, if_pos e] at he; cases he
    simp [exec1, hp, hf]
  | externHook hr he _ _ =>
    refine ⟨hr, ?_⟩
    rw [externAt_eq] at he
    split at he
    · rename_i hp; cases he; simp [exec1, hp]
    · cases he
  | extern_fault hr he hn =>
    rw [externAt_eq] at he
    split at he
    · cases he; exact absurd ⟨keepsFrozen_refl _, rfl⟩ hn
    · cases he

theorem hook_stay {s sf : State} (hp : s.pc = hookA) (h : Steps P s sf) : sf = s := by
  induction h with
  | refl => rfl
  | @step a b c h1 h2 ih =>
    obtain ⟨_, e2⟩ := step_exec1 h1
    have e : exec1 a = a := by simp [exec1, hp]
    have hb : b = a := e2.trans e
    subst hb
    exact ih hp

theorem hookA_ne : hookA ≠ lrA := by decide

theorem toHook_safe : ∀ (n : Nat) (s sf : State), toHook n s = true → Steps P s sf →
    sf.pc ≠ lrA ∧ sf.status = .Running
  | 0, s, sf, ht, hs => by
    simp only [toHook, decide_eq_true_eq] at ht
    rw [hook_stay ht.1 hs, ht.1]; exact ⟨hookA_ne, ht.2⟩
  | n + 1, s, sf, ht, hs => by
    simp only [toHook] at ht
    by_cases hp : s.pc = hookA
    · rw [if_pos hp] at ht
      rw [hook_stay hp hs, hp]; exact ⟨hookA_ne, by simpa using ht⟩
    · rw [if_neg hp] at ht
      by_cases hl : s.pc = lrA
      · rw [if_pos hl] at ht; cases ht
      · rw [if_neg hl] at ht
        by_cases hr : s.status = .Running
        · rw [if_pos hr] at ht
          cases hs with
          | refl => exact ⟨hl, hr⟩
          | step h1 h2 =>
            obtain ⟨_, rfl⟩ := step_exec1 h1
            exact toHook_safe n _ sf ht h2
        · rw [if_neg hr] at ht; cases ht

/-! ## The disproof -/

theorem not_oneshotOk : ¬ oneshotOk := by
  rintro ⟨-, h⟩
  have hok := h pl0 placeable exts memzeroOk
  obtain ⟨sf, hs, hout⟩ :=
    hok (false, false, out0, msg0, key0) emp s0 rfl rfl hpre (by decide) codeLoaded
  obtain ⟨hne, hrun⟩ := toHook_safe 200 s0 sf f_traj hs
  rcases hout with ⟨⟨hpcf, _, _⟩, _, _⟩ | ⟨h1, _⟩ | ⟨c, h1, _⟩ | ⟨h1, _⟩
  · exact hne (hpcf.trans (by decide))
  · rw [hrun] at h1; cases h1
  · rw [hrun] at h1; cases h1
  · rw [hrun] at h1; cases h1

end Poly1305Libsodium.FinCex
end

theorem solution : ¬ ((∃ Rep : Poly1305Libsodium.StateRep, Poly1305Libsodium.initOk Rep ∧
    Poly1305Libsodium.updateOk Rep ∧ Poly1305Libsodium.finalOk Rep) ∧
    Poly1305Libsodium.oneshotOk) :=
  fun h => Poly1305Libsodium.FinCex.not_oneshotOk h.2

