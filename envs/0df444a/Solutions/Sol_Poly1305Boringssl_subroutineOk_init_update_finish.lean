-- Prove2me | solution 1 for Poly1305Boringssl.subroutineOk_init_update_finish
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-11-24T11:29:16.094911+00:00
-- url     : https://prove2.me/submissions/5cf59151-bfad-482d-bf9b-dfbaea0b333a

import Definitions.Def_Poly1305Boringssl_Spec

section
/-! Concrete data for the disproof of `Poly1305Boringssl.subroutineOk_init_update_finish`.
Byte strings are little-endian natural numbers (`byteOf`), so the kernel looks a byte up with one
shift instead of walking a list. -/

namespace Poly1305Boringssl.Cex

open Arm64 Arm64.Obj

/-- Byte `i` of the little-endian number `N`. -/
def byteOf (N i : Nat) : BitVec 8 := BitVec.ofNat 8 (N >>> (8 * i))
/-- The first `n` little-endian bytes of `N`. -/
def bytesOfNat (n N : Nat) : List (BitVec 8) := (List.range n).map (byteOf N)

def pl0 : Placement := { base := 0x10000#64, ρ := fun _ => 0#64 }
abbrev P : Program := boringsslPoly1305Lib.program pl0
def codeN : Nat := 482532943369658890285432370492509158426265737993229517700142830385798843807383768039113953458951026017547284170395053797266676968918188342454281071509017701335699824157428867323500632845192639078383281073612922793022387573386119667694097648839723382196811320415273812327145730355543498101700352128304098860391166239526904465404760178595442067092410362336279764595154524134505956893706332889277973027623596696089916542898004849136342644521433149088321409690480279170353566694735950047785117735878718388859731826208910977517543782151131765388797268192812881214708810022283529530479672370441931534411879588730994495353010376320084684720704288195759950531015184930821911980560622691082904140011008043470513803760268466164029723059799304592038682475431161734593929449791111029377077168466648418610136507586777699072688357461170464383658034653409715869846072269426581943710360452269096733676147066799619085138409963756541626969212657362818596688066053404516211738713091524009089730236471264546883511594174906763396774548726285159152865219788766170431284693703730660871786734793177839474681236838021710777732411854651822840525395745201058997861340580967499996701752375843036171982068054268578973862462612028234343303366312221420434229943903373570763495904712915786290019285177197551122621357392675483357670490955732553840685589095474085601072782006239294360143582211918061192295318035585708995459043880570097169861782961626204642501603109476679105612077978546240898557765382424441381106671440647079429625312372664412348267143601502935124891333717163735110201817062477492579340028755521042507770532023277433168414491590931522463290035327243773524993344402808658533341513033936930527976411032152481853463686875466399659129201191448867310153679868650107551116640346870912651028098433665764098667590069804207728702961498245965106009034414157221085603302116234819192730464667545902166677881036378581527551221759986294648901798272061872355849879503787872973940190600130427110078066637870841093137789802222598909718321854100683454483569139321954672946031517898465651409442593322337159708430212327193574958247720858324492948112286378949786488660952574922615633810328233536819052123383555395248948841831803056052165691308342635592287926371166068041102445442732841759463880264940119664489892320428623574716588441636452806938328570916562590820073376440622115247110184448006050352238265685188693931413199691762240339046562071909342464431217628226407887513779979557509594822700124878089107623098419101921351906403131035720150405042803902680296882212003013047459604562264939631528175991253206940561199125885257006664926206892845733523943847206355755381312638230498760069916539959121233750294856088591046457527930350913432249299735256729441115458509152986152
def keyN : Nat := 67108862
def msgN : Nat := 315076259657932589691391822981745383343
def st1N : Nat := 67108862
def st2N : Nat := 11356854900532753490904187703760946947933394904325446811579539722866857151632351327928496773398177410973318189049054191862278491471870
def macBadN : Nat := 67108868
def macRfcN : Nat := 134217732
def key : List (BitVec 8) := bytesOfNat 32 keyN
def msg : List (BitVec 8) := bytesOfNat 16 msgN
def stA : BitVec 64 := 0x20000#64
def keyA : BitVec 64 := 0x30000#64
def macA : BitVec 64 := 0x31000#64
def msgA : BitVec 64 := 0x32000#64
def spA : BitVec 64 := 0x40000#64
def lrA : BitVec 64 := 0x50000#64
def inR (b : BitVec 64) (n : Nat) (a : BitVec 64) : Bool := decide ((a - b).toNat < n)
/-- The memory of every run: code, state bytes `stN`, key, tag bytes `mcN`, message, stack. -/
def memOf (stN mcN : Nat) : Memory := Memory.ofFn
  (fun a => if inR pl0.base 1136 a then byteOf codeN (a - pl0.base).toNat
    else if inR stA 512 a then byteOf stN (a - stA).toNat
    else if inR keyA 32 a then byteOf keyN (a - keyA).toNat
    else if inR macA 16 a then byteOf mcN (a - macA).toNat
    else if inR msgA 16 a then byteOf msgN (a - msgA).toNat else 0)
  (fun a => if inR pl0.base 1136 a then some Perm.rx
    else if inR stA 512 a then some Perm.rw
    else if inR keyA 32 a then some Perm.ro
    else if inR macA 16 a then some Perm.rw
    else if inR msgA 16 a then some Perm.ro
    else if inR (spA - 64#64) 64 a then some Perm.rw else none)
def regsOf (x1 x2 : BitVec 64) : RegFile :=
  ⟨fun i => if i = 0#5 then stA else if i = 1#5 then x1 else
      if i = 2#5 then x2 else if i = 30#5 then lrA else 0#64⟩
def entry (fn : String) (m : Memory) (x1 x2 : BitVec 64) : State :=
  { regs := regsOf x1 x2, sp := spA, pc := boringsslPoly1305Lib.fnAddr pl0 fn, mem := m }
/-- One step of the deterministic semantics (no hooks in this library). -/
def exec1 (s : State) : State :=
  match P.fetchMem s.mem s.pc with
  | some i => P.evalInst i s
  | none => { s with status := .Halted }
/-- `some` the final state if, within `n` steps, the run stays `Running`, first reaches `lrA` at
its end, and the step after that leaves `Running`. -/
def trajEnd : Nat → State → Option State
  | 0, s => if s.pc = lrA ∧ s.status = .Running ∧ (exec1 s).status ≠ .Running then some s else none
  | n + 1, s => if s.pc = lrA then
      (if s.status = .Running ∧ (exec1 s).status ≠ .Running then some s else none)
    else if s.status = .Running then trajEnd n (exec1 s) else none
end Poly1305Boringssl.Cex
end

section
/-! Facts about the concrete runs, checked by kernel evaluation (`decide +kernel`). -/

namespace Poly1305Boringssl.Cex

open Arm64 Arm64.Obj

theorem f_init : (trajEnd 200 (entry "CRYPTO_poly1305_init" (memOf 0 0) keyA 0)).map
    (fun t => t.mem.readBytes stA 512) = some (bytesOfNat 512 st1N) := by decide +kernel
theorem f_upd : (trajEnd 300 (entry "CRYPTO_poly1305_update" (memOf st1N 0) msgA 16)).map
    (fun t => t.mem.readBytes stA 512) = some (bytesOfNat 512 st2N) := by decide +kernel
theorem f_fin : (trajEnd 200 (entry "CRYPTO_poly1305_finish" (memOf st2N 0) macA 0)).map
    (fun t => t.mem.readBytes macA 16) = some (bytesOfNat 16 macBadN) := by decide +kernel
theorem f_rfc : poly1305Mac msg key = bytesOfNat 16 macRfcN := by decide +kernel
theorem f_ne : bytesOfNat 16 macRfcN ≠ bytesOfNat 16 macBadN := by decide +kernel
/-- The bundle's code bytes (before relocation) as a little-endian number. -/
def rawN : Nat := 482532943369658890285432370492509158426265737993229517700142830385798843807383768039113953458951026017547284170395053797266676968918188342454281071509017701335699824157428867323500632845192639078383281073612922793022387573386119667694097648839723382196811320415273812327145730355543498101700352128304098860391166239526904465404760178595442067092410362336279764595154524134505956893706332889277973027623596696089916542898004849136342644521433149088321409690480279170353566694735950047785117735878718388859731826208910977517543782151131765388797268192812881214708810022283529530479672370441931534411879588730994495353010097715234898375178597785673494759259179485103804847555427117641915840206862656776745640485786113673862747169183291438101984999257507815791411707131899978019960726712195665871945372022986249537096450813791075103997805650826461024075970606576964964084660627732459334397033674534101035332195182481737087569873335783594790820634340037116424647237793115440666182164993314378692865802359259086113507791196476298924923834619538680233299233621261162784712455307196823648029313727288185968123044897043756994989742220709986866614046065650915713160749909136091768725227816347838821424323203318296035381417587051685019730397409304012906276767681351405866870575460881160118724381810570548978751479341996495536484207346690176519971792325279454651528117223132138432267348554412085084971263747497093342875634370393642164389035525812794023322105788830580222468013675986085049094465485340817468770781837170360158120305830888187336925020376118953677841453630396107085172578042477941008046991257999198447284530266145496890692443860863647081599194686798402545061034186406515262654747679727916538622231608559547164617276725746714677570289724954089391108732947808529144724892380364319670055960628663367714493816109987627100109175180315420940568346346980532462608750524965850545271858752600324672185198201465667009023413600555994383388311564132745436017298867311961161791163792180019448647735668703095676608002105925205381268514610881307383364388792913613707245696541654677262559206344780759515053134146374622473245424992974207054234908244793637569773645619187949070007219789607497299569173311927834967971505526856609426026680735097929570151036969396313333674539162593620864568685824155229795511751137621036078993722383216965297749043847353742929553388362169338987270762137911696432206295144999568875203605323112168077210288246966384487433971073029056633348988327715373458029034872939368370622879994939782070443159153693187421410549312915661709188893426416876781492140349026537561507891228335769727940630767924803522000747000999455357245532397599068047169203947657870135328685053572258949542162657334348949790745809983450424995673740914205736

theorem f_raw : boringsslPoly1305Text.code = bytesOfNat 1136 rawN := by
  show boringsslPoly1305PlacedCode = _; decide +kernel

theorem getD_bytesOfNat (n N k : Nat) :
    (bytesOfNat n N).getD k 0#8 = if k < n then byteOf N k else 0#8 := by
  unfold bytesOfNat
  split
  · simp [List.getD_eq_getElem?_getD, *]
  · simp [List.getD_eq_getElem?_getD, *]

/-- The relocated code. `getD` is rewritten to `byteOf` first, so the kernel never walks a list. -/
theorem f_code : P.code = bytesOfNat 1136 codeN := by
  simp only [P, PlacedLib.program, boringsslPoly1305Lib, CodeBlock.patched, CodeBlock.patchedWord,
    CodeBlock.wordAt, wordOfBytesLE, f_raw, getD_bytesOfNat]
  decide +kernel
theorem f_key : (memOf 0 0).readBytes keyA 32 = key := by decide +kernel
theorem f_msg : (memOf st1N 0).readBytes msgA 16 = msg := by decide +kernel
theorem f_st1 : (memOf st1N 0).readBytes stA 512 = bytesOfNat 512 st1N := by decide +kernel
theorem f_st2 : (memOf st2N 0).readBytes stA 512 = bytesOfNat 512 st2N := by decide +kernel

end Poly1305Boringssl.Cex
end

section
/-! Generic lemmas for the disproof: the semantics is deterministic on this library, so a
`Steps` run that returns ends at the state `trajEnd` computes; heaps for the preconditions;
reading owned bytes back from a postcondition. -/

namespace Poly1305Boringssl.Cex

open Arm64 Arm64.Obj

/-! ## Determinism -/

theorem externAt_none (pc : BitVec 64) : P.externAt? pc = none := by
  simp [Program.externAt?, Program.hookAtOff?, P, PlacedLib.program, boringsslPoly1305Lib,
    boringsslPoly1305Text]

theorem step_exec1 {s s' : State} (h : Step P s s') : s.status = .Running ∧ s' = exec1 s := by
  cases h with
  | exec hr hf => exact ⟨hr, by simp [exec1, hf]⟩
  | halt_unmapped hr hf _ => exact ⟨hr, by simp [exec1, hf]⟩
  | externHook _ he _ _ => rw [externAt_none] at he; cases he
  | extern_fault _ he _ => rw [externAt_none] at he; cases he

theorem steps_stuck {s sf : State} (hs : s.status ≠ .Running) (h : Steps P s sf) : sf = s := by
  cases h with
  | refl => rfl
  | step h1 _ => exact absurd (step_exec1 h1).1 hs

theorem trajEnd_sound : ∀ (n : Nat) (s t sf : State), trajEnd n s = some t → Steps P s sf →
    sf.pc = lrA → sf.status = .Running → sf = t
  | 0, s, t, sf, ht, hs, hpc, hst => by
    simp only [trajEnd] at ht
    split at ht
    · rename_i hc
      simp only [Option.some.injEq] at ht; subst ht
      cases hs with
      | refl => rfl
      | step h1 h2 =>
        obtain ⟨_, rfl⟩ := step_exec1 h1
        have := steps_stuck hc.2.2 h2; subst this; exact absurd hst hc.2.2
    · cases ht
  | n + 1, s, t, sf, ht, hs, hpc, hst => by
    simp only [trajEnd] at ht
    by_cases hp : s.pc = lrA
    · rw [if_pos hp] at ht
      split at ht
      · rename_i hc
        simp only [Option.some.injEq] at ht; subst ht
        cases hs with
        | refl => rfl
        | step h1 h2 =>
          obtain ⟨_, rfl⟩ := step_exec1 h1
          have := steps_stuck hc.2 h2; subst this; exact absurd hst hc.2
      · cases ht
    · rw [if_neg hp] at ht
      split at ht
      · cases hs with
        | refl => exact absurd hpc hp
        | step h1 h2 =>
          obtain ⟨_, rfl⟩ := step_exec1 h1
          exact trajEnd_sound n _ t sf ht h2 hpc hst
      · cases ht

/-! ## Separation logic -/

theorem sat_false_sep (m : Memory) (R : SepProp) : ¬ (m ⊨ ⌜False⌝ ∗ R) := by
  rintro ⟨h, ⟨h1, h2, _, _, ⟨_, hf⟩, _⟩, _⟩
  exact hf

/-- A heap with no ghost state and no mapping tokens. -/
def Plain (h : Heap) : Prop :=
  (∀ γ k, h.auth γ k = none) ∧ (∀ γ k, h.frag γ k = none) ∧ ∀ a, h.mapped a = false

theorem plain_empty : Plain Heap.empty := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem plain_region (b : BitVec 64) (n : Nat) (m : Memory) : Plain (regionHeap b n m) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem plain_regionRO (b : BitVec 64) (n : Nat) (m : Memory) : Plain (regionHeapRO b n m) :=
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

theorem matches_regionRO {b : BitVec 64} {n : Nat} {m : Memory}
    (h : ∀ a, InRegion b n a → (m.perm a).r = true ∧ m.isLazyFree a = false) :
    (regionHeapRO b n m).Matches m := by
  refine ⟨fun a c hc => ?_, ⟨0, fun _ _ _ => ⟨rfl, rfl⟩⟩, fun _ ha => by cases ha⟩
  simp only [regionHeapRO] at hc
  split at hc
  · rename_i hr; cases hc; exact ⟨rfl, h a hr⟩
  · cases hc

theorem region_phys_none {b a : BitVec 64} {n : Nat} {m : Memory} (h : ¬ InRegion b n a) :
    (regionHeap b n m).phys a = none := by simp [regionHeap, h]

theorem regionRO_phys_none {b a : BitVec 64} {n : Nat} {m : Memory} (h : ¬ InRegion b n a) :
    (regionHeapRO b n m).phys a = none := by simp [regionHeapRO, h]

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

theorem points_regionRO : ∀ (n : Nat) (a : BitVec 64) (m : Memory), n < 2 ^ 64 →
    (pointsToBytesRO a (m.readBytes a n)).holds (regionHeapRO a n m)
  | 0, a, m, _ => by
    show regionHeapRO a 0 m = Heap.empty
    apply Heap.ext
    · funext x; simp [regionHeapRO, InRegion, Heap.empty]
    all_goals rfl
  | n + 1, a, m, hn => by
    refine ⟨Heap.singletonRO a (m.read8 a), regionHeapRO (a + 1#64) n m, ?_, ?_, rfl,
      points_regionRO n (a + 1#64) m (by omega)⟩
    · refine disj_of_phys ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩ (plain_regionRO _ _ _)
        fun x => ?_
      by_cases e : x = a
      · subst e; exact Or.inr (regionRO_phys_none (not_inRegion_self_succ hn))
      · exact Or.inl (by simp [Heap.singletonRO, e])
    · apply Heap.ext
      · funext x
        by_cases e : x = a
        · subst e
          have : InRegion x (n + 1) x := by simp [InRegion]
          simp [regionHeapRO, Heap.union, Heap.singletonRO, this]
        · have := inRegion_succ hn e
          simp only [regionHeapRO, Heap.union, Heap.singletonRO, e, if_false]
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

/-! ## Reading owned bytes back -/

/-- `h'`'s read-write cells are cells of `h`. -/
def SubRW (h' h : Heap) : Prop := ∀ a b, h'.phys a = some (.rw b) → h.phys a = some (.rw b)

theorem subRW_left (h1 h2 : Heap) : SubRW h1 (h1.union h2) := fun _ _ e => by
  simp [Heap.union, e]

theorem subRW_right {h1 h2 : Heap} (hd : h1.Disjoint h2) : SubRW h2 (h1.union h2) := by
  intro a b h
  rcases hd.1 a with h0 | h0 | ⟨b', e1, e2⟩
  · simp [Heap.union, h0, h]
  · rw [h] at h0; cases h0
  · rw [h] at e2; cases e2

theorem subRW_trans {h1 h2 h3 : Heap} (a : SubRW h1 h2) (b : SubRW h2 h3) : SubRW h1 h3 :=
  fun x y e => b x y (a x y e)

theorem bytes_rw : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap),
    (pointsToBytes a bs).holds h → ∀ i (hi : i < bs.length),
      h.phys (a + BitVec.ofNat 64 i) = some (.rw bs[i])
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, a, h, hs, i, hi => by
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hs
    cases i with
    | zero =>
      simp only [pointsTo8] at p1; subst p1
      exact subRW_left _ _ _ _ (by simp [Heap.singleton])
    | succ i =>
      have := bytes_rw bs (a + 1#64) h2 p2 i (by simp at hi; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm] at this
      exact subRW_right hd _ _ (by simpa using this)

theorem length_readBytes (m : Memory) : ∀ (n : Nat) (a : BitVec 64), (m.readBytes a n).length = n
  | 0, _ => rfl
  | n + 1, a => by simp [Memory.readBytes, length_readBytes m n]

theorem getElem_readBytes (m : Memory) : ∀ (n : Nat) (a : BitVec 64) (i : Nat)
    (hi : i < (m.readBytes a n).length), (m.readBytes a n)[i] = m.read8 (a + BitVec.ofNat 64 i)
  | 0, _, i, hi => by simp [Memory.readBytes] at hi
  | n + 1, a, 0, _ => by simp [Memory.readBytes]
  | n + 1, a, i + 1, hi => by
    simp only [Memory.readBytes, List.getElem_cons_succ]
    rw [getElem_readBytes m n (a + 1#64) i]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

/-- Owned bytes `bs` at `a` in a sub-heap of a heap matching `m` are what `m` holds there. -/
theorem owned_eq_readBytes {bs : List (BitVec 8)} {a : BitVec 64} {h' h : Heap} {m : Memory}
    (hp : (pointsToBytes a bs).holds h') (hs : SubRW h' h) (hm : h.Matches m) :
    bs = m.readBytes a bs.length := by
  apply List.ext_getElem (by rw [length_readBytes])
  intro i h1 h2
  rw [getElem_readBytes]
  have := hm.1 _ _ (hs _ _ (bytes_rw bs a h' hp i h1))
  exact this.1.symm

end Poly1305Boringssl.Cex
end

section
/-! # The goal is false

For every `Rep`, run `CRYPTO_poly1305_init` on a zeroed state with the key
`feffff03 00…00` (r = 0x3fffffe, s = 0), `CRYPTO_poly1305_update` with the 16-byte message
`af97d05e2fa1bd5e427bbd84f67a09ed`, and `CRYPTO_poly1305_finish`. The contracts carry `Rep`
from each run to the next, and `finishSpec` then forces RFC 8439's tag `04000008 00…00` at
`mac`; the deterministic run writes `04000004 00…00`. -/

namespace Poly1305Boringssl.Cex

open Arm64 Arm64.Obj

/-! ## Placement and code -/

theorem code_len : boringsslPoly1305Lib.text.code.length = 1136 := by
  show boringsslPoly1305Text.code.length = 1136
  rw [f_raw]; simp [bytesOfNat]

theorem placeable : boringsslPoly1305Lib.Placeable pl0 := by
  refine ⟨⟨by decide, by decide +kernel, by rw [code_len]; decide, by rw [code_len],
    by decide +kernel, ?_, ?_, ?_, by simp [boringsslPoly1305Lib, boringsslPoly1305Text]⟩,
    by simp [boringsslPoly1305Lib, boringsslPoly1305Data],
    by simp [boringsslPoly1305Lib, boringsslPoly1305Data],
    by simp [boringsslPoly1305Lib, boringsslPoly1305Data]⟩
  · intro r hr
    rw [code_len]
    simp only [boringsslPoly1305Lib, boringsslPoly1305Text, List.mem_cons, List.mem_nil_iff,
      or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      refine ⟨by decide, by decide, ?_⟩ <;>
      simp only [CodeBlock.relocInRange, CodeRelocInRange, BranchInRange] <;> decide +kernel
  · intro off r h
    simp [CodeBlock.relaxedAt, pl0] at h
  · intro s hs
    rw [code_len]
    simp only [boringsslPoly1305Lib, boringsslPoly1305Text, List.mem_cons, List.mem_nil_iff,
      or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> decide

theorem toNat_sub_conc (a b : BitVec 64) :
    (a - b).toNat = (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_sub]

theorem code_byte (sN mN : Nat) (i : Nat) (hi : i < 1136) :
    (memOf sN mN).read8 (pl0.base + BitVec.ofNat 64 i) =
        (bytesOfNat 1136 codeN)[i]'(by simp [bytesOfNat]; exact hi) ∧
      (memOf sN mN).perm (pl0.base + BitVec.ofNat 64 i) = some Perm.rx ∧
      (memOf sN mN).isLazyFree (pl0.base + BitVec.ofNat 64 i) = false := by
  have e : (pl0.base + BitVec.ofNat 64 i - pl0.base).toNat = i := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  have hin : inR pl0.base 1136 (pl0.base + BitVec.ofNat 64 i) = true := by
    simp only [inR, e]; simpa using hi
  simp only [memOf, Memory.ofFn, Memory.read8, Memory.perm, Memory.isLazyFree, hin, if_true,
    e, bytesOfNat, List.getElem_map, List.getElem_range]
  refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial

theorem codeLoaded (sN mN : Nat) : P.CodeLoaded (memOf sN mN) := by
  have key : ∀ (c : List (BitVec 8)), c = bytesOfNat 1136 codeN →
      ∀ (i : Nat) (hi : i < c.length),
        (memOf sN mN).read8 (P.base + BitVec.ofNat 64 i) = c[i] ∧
        (memOf sN mN).perm (P.base + BitVec.ofNat 64 i) = some Perm.rx ∧
        (memOf sN mN).isLazyFree (P.base + BitVec.ofNat 64 i) = false := by
    intro c hc i hi
    have hb : P.base = pl0.base := rfl
    have hi' : i < 1136 := by rw [hc] at hi; simpa [bytesOfNat] using hi
    have hci : c[i] = (bytesOfNat 1136 codeN)[i]'(by simp [bytesOfNat]; exact hi') := by
      simp only [List.getElem_of_eq hc]
    rw [hb, hci]
    exact code_byte sN mN i hi'
  have hl : P.code.length = 1136 := by rw [f_code]; simp [bytesOfNat]
  unfold Program.CodeLoaded
  refine ⟨by decide, by rw [hl]; decide, ?_⟩
  exact key P.code f_code

/-! ## Memory regions of `memOf` -/

/-- Where `a` lies, numerically. -/
theorem region_num {b a : BitVec 64} {n : Nat} (h : InRegion b n a) :
    (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < n := by
  simp only [InRegion] at h; rwa [toNat_sub_conc] at h

theorem not_inR_of {b a : BitVec 64} {n : Nat}
    (h : ¬ (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < n) : inR b n a = false := by
  simp only [inR, toNat_sub_conc]; simpa using h

theorem inR_of {b a : BitVec 64} {n : Nat}
    (h : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < n) : inR b n a = true := by
  simp only [inR, toNat_sub_conc]; simpa using h

theorem memOf_st (sN mN : Nat) {x : BitVec 64} (h : InRegion stA 512 x) :
    (memOf sN mN).perm x = some Perm.rw ∧ (memOf sN mN).isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  simp only [stA, BitVec.toNat_ofNat] at hx
  have h1 : inR pl0.base 1136 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR stA 512 x = true := inR_of (by simp only [stA, BitVec.toNat_ofNat]; omega)
  simp only [memOf, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2]; exact ⟨rfl, rfl⟩

theorem memOf_key (sN mN : Nat) {x : BitVec 64} (h : InRegion keyA 32 x) :
    ((memOf sN mN).perm x).r = true ∧ (memOf sN mN).isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  simp only [keyA, BitVec.toNat_ofNat] at hx
  have h1 : inR pl0.base 1136 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR stA 512 x = false := not_inR_of (by simp only [stA, BitVec.toNat_ofNat]; omega)
  have h3 : inR keyA 32 x = true := inR_of (by simp only [keyA, BitVec.toNat_ofNat]; omega)
  simp only [memOf, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2, h3]; exact ⟨rfl, rfl⟩

theorem memOf_mac (sN mN : Nat) {x : BitVec 64} (h : InRegion macA 16 x) :
    (memOf sN mN).perm x = some Perm.rw ∧ (memOf sN mN).isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  simp only [macA, BitVec.toNat_ofNat] at hx
  have h1 : inR pl0.base 1136 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR stA 512 x = false := not_inR_of (by simp only [stA, BitVec.toNat_ofNat]; omega)
  have h3 : inR keyA 32 x = false := not_inR_of (by simp only [keyA, BitVec.toNat_ofNat]; omega)
  have h4 : inR macA 16 x = true := inR_of (by simp only [macA, BitVec.toNat_ofNat]; omega)
  simp only [memOf, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2, h3, h4]; exact ⟨rfl, rfl⟩

theorem memOf_msg (sN mN : Nat) {x : BitVec 64} (h : InRegion msgA 16 x) :
    ((memOf sN mN).perm x).r = true ∧ (memOf sN mN).isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  simp only [msgA, BitVec.toNat_ofNat] at hx
  have h1 : inR pl0.base 1136 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR stA 512 x = false := not_inR_of (by simp only [stA, BitVec.toNat_ofNat]; omega)
  have h3 : inR keyA 32 x = false := not_inR_of (by simp only [keyA, BitVec.toNat_ofNat]; omega)
  have h4 : inR macA 16 x = false := not_inR_of (by simp only [macA, BitVec.toNat_ofNat]; omega)
  have h5 : inR msgA 16 x = true := inR_of (by simp only [msgA, BitVec.toNat_ofNat]; omega)
  simp only [memOf, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2, h3, h4, h5]
  exact ⟨rfl, rfl⟩

/-- The stack: `[spA - 64, spA)`; `n ≤ 64` bytes below `spA`. -/
theorem memOf_stk (sN mN : Nat) {n : Nat} (hn : n ≤ 64) {x : BitVec 64}
    (h : InRegion (spA - BitVec.ofNat 64 n) n x) :
    (memOf sN mN).perm x = some Perm.rw ∧ (memOf sN mN).isLazyFree x = false := by
  have hx := region_num h; have := x.isLt
  have e : (spA - BitVec.ofNat 64 n).toNat = 0x40000 - n := by
    rw [toNat_sub_conc]; simp only [spA, BitVec.toNat_ofNat]; omega
  rw [e] at hx
  have h1 : inR pl0.base 1136 x = false := not_inR_of (by simp only [pl0, BitVec.toNat_ofNat]; omega)
  have h2 : inR stA 512 x = false := not_inR_of (by simp only [stA, BitVec.toNat_ofNat]; omega)
  have h3 : inR keyA 32 x = false := not_inR_of (by simp only [keyA, BitVec.toNat_ofNat]; omega)
  have h4 : inR macA 16 x = false := not_inR_of (by simp only [macA, BitVec.toNat_ofNat]; omega)
  have h5 : inR msgA 16 x = false := not_inR_of (by simp only [msgA, BitVec.toNat_ofNat]; omega)
  have h6 : inR (spA - 64#64) 64 x = true := inR_of (by
    have : (spA - 64#64).toNat = 0x40000 - 64 := by decide
    rw [this]; omega)
  simp only [memOf, Memory.ofFn, Memory.perm, Memory.isLazyFree, h1, h2, h3, h4, h5, h6]
  exact ⟨rfl, rfl⟩

/-! ## Supports -/

/-- `h` has cells only where `S` holds. -/
def Supp (h : Heap) (S : BitVec 64 → Prop) : Prop := ∀ a, ¬ S a → h.phys a = none

theorem supp_region (b : BitVec 64) (n : Nat) (m : Memory) : Supp (regionHeap b n m) (InRegion b n) :=
  fun _ h => region_phys_none h

theorem supp_regionRO (b : BitVec 64) (n : Nat) (m : Memory) :
    Supp (regionHeapRO b n m) (InRegion b n) := fun _ h => regionRO_phys_none h

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

/-! ## One run -/

theorem run_post {α : Type} {spec : Spec α} {x : α} {s0 t : State} {n : Nat}
    (hok : subroutine_ok P s0.pc spec) (hst : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ emp) (hal : s0.spAligned = true)
    (hcode : P.CodeLoaded s0.mem) (hlr : s0.readReg64 Reg.lr = lrA)
    (hpan : spec.onPanic x s0 = fun _ => ⌜False⌝)
    (hexit : ∀ c, spec.onExit x c s0 = fun _ => ⌜False⌝)
    (hoom : spec.onOom x s0 = fun _ => ⌜False⌝)
    (ht : trajEnd n s0 = some t) : t.mem ⊨ spec.post x s0 t ∗ emp := by
  obtain ⟨sf, hs, hout⟩ := hok x emp s0 rfl hst hpre hal hcode
  rcases hout with ⟨⟨hpc, _, hsr⟩, _, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
  · rw [hlr] at hpc
    have := trajEnd_sound n s0 t sf ht hs hpc hsr
    subst this; exact hpost
  · rw [hpan] at hp; exact (sat_false_sep _ _ hp).elim
  · rw [hexit] at hp; exact (sat_false_sep _ _ hp).elim
  · rw [hoom] at hp; exact (sat_false_sep _ _ hp).elim

theorem traj_of {n : Nat} {s : State} {f : State → List (BitVec 8)} {v : List (BitVec 8)}
    (h : (trajEnd n s).map f = some v) : ∃ t, trajEnd n s = some t ∧ f t = v := by
  cases e : trajEnd n s with
  | none => rw [e] at h; cases h
  | some t => rw [e] at h; exact ⟨t, rfl, by simpa using h⟩

end Poly1305Boringssl.Cex
end

section
namespace Poly1305Boringssl.Cex

open Arm64 Arm64.Obj

def sI : State := entry "CRYPTO_poly1305_init" (memOf 0 0) keyA 0
def sU : State := entry "CRYPTO_poly1305_update" (memOf st1N 0) msgA 16
def sF : State := entry "CRYPTO_poly1305_finish" (memOf st2N 0) macA 0

theorem sI_x0 : sI.readReg64 Reg.x0 = stA := by decide
theorem sI_x1 : sI.readReg64 Reg.x1 = keyA := by decide
theorem sU_x0 : sU.readReg64 Reg.x0 = stA := by decide
theorem sU_x1 : sU.readReg64 Reg.x1 = msgA := by decide
theorem sU_x2 : (sU.readReg64 Reg.x2).toNat = 16 := by decide
theorem sF_x0 : sF.readReg64 Reg.x0 = stA := by decide
theorem sF_x1 : sF.readReg64 Reg.x1 = macA := by decide

/-- `init` leaves a state satisfying `Rep` for the empty message. -/
theorem after_init (Rep : StateRep) (hi : initOk Rep) :
    Rep stA (bytesOfNat 512 st1N) ((memOf 0 0).readBytes keyA 32) [] := by
  obtain ⟨t, ht, hv⟩ := traj_of f_init
  have hok : subroutine_ok P sI.pc (initSpec Rep) := hi.2 pl0 placeable
  let m := memOf 0 0
  have D2 : (regionHeap stA 512 m).Disjoint (regionHeapRO keyA 32 m) :=
    disj_supp (plain_region _ _ _) (plain_regionRO _ _ _) (supp_region _ _ _)
      (supp_regionRO _ _ _) (sep_reg (by decide))
  have P12 := plain_union (plain_region stA 512 m) (plain_regionRO keyA 32 m)
  have hpre : sI.mem ⊨ (initSpec Rep).pre (m.readBytes stA 512, m.readBytes keyA 32) sI ∗ emp := by
    refine ⟨_, sep_intro (disj_empty_right (plain_union plain_empty P12))
      (sep_intro (disj_empty_left P12) (pure_intro ⟨length_readBytes _ _ _, length_readBytes _ _ _⟩)
        (sep_intro D2 ?_ ?_)) emp_intro, ?_⟩
    · rw [sI_x0]; exact points_region 512 stA m (by decide)
    · rw [sI_x1]; exact points_regionRO 32 keyA m (by decide)
    · exact matches_union (plain_union plain_empty P12) plain_empty
        (matches_union plain_empty P12 (matches_empty _)
          (matches_union (plain_region _ _ _) (plain_regionRO _ _ _)
            (matches_region fun _ h => memOf_st 0 0 h) (matches_regionRO fun _ h => memOf_key 0 0 h)))
        (matches_empty _)
  have hpost := run_post hok rfl hpre (by decide) (codeLoaded 0 0) (by decide)
    rfl (fun _ => rfl) rfl ht
  obtain ⟨h, ⟨h1, h2, hd, rfl, hp1, _⟩, hm⟩ := hpost
  obtain ⟨h11, h12, hd1, rfl, ⟨st', ha, hb, hd11, rfl, ⟨_, hφ⟩, hpts⟩, _⟩ := hp1
  have e := owned_eq_readBytes hpts
    (subRW_trans (subRW_right hd11) (subRW_trans (subRW_left _ _) (subRW_left _ _))) hm
  rw [hφ.1, sI_x0, hv] at e
  have := hφ.2; rw [sI_x0, e] at this; exact this

/-- `update` with the message leaves a state satisfying `Rep` for the message. -/
theorem after_update (Rep : StateRep) (hu : updateOk Rep) (key0 : List (BitVec 8))
    (h0 : Rep stA (bytesOfNat 512 st1N) key0 []) :
    Rep stA (bytesOfNat 512 st2N) key0 ([] ++ (memOf st1N 0).readBytes msgA 16) := by
  obtain ⟨t, ht, hv⟩ := traj_of f_upd
  have hok : subroutine_ok P sU.pc (updateSpec Rep) := hu.2 pl0 placeable
  let m := memOf st1N 0
  have D3 : (regionHeapRO msgA 16 m).Disjoint (regionHeap (sU.sp - BitVec.ofNat 64 64) 64 m) :=
    disj_supp (plain_regionRO _ _ _) (plain_region _ _ _) (supp_regionRO _ _ _)
      (supp_region _ _ _) (sep_reg (by decide))
  have P23 := plain_union (plain_regionRO msgA 16 m) (plain_region (sU.sp - BitVec.ofNat 64 64) 64 m)
  have D2 : (regionHeap stA 512 m).Disjoint
      ((regionHeapRO msgA 16 m).union (regionHeap (sU.sp - BitVec.ofNat 64 64) 64 m)) :=
    disj_supp (plain_region _ _ _) P23 (supp_region _ _ _)
      (supp_union (supp_regionRO _ _ _) (supp_region _ _ _)) (fun x hx hy => by
        rcases hy with hy | hy
        · exact sep_reg (by decide) x hx hy
        · exact sep_reg (by decide) x hx hy)
  have P123 := plain_union (plain_region stA 512 m) P23
  have hpre : sU.mem ⊨ (updateSpec Rep).pre
      (m.readBytes stA 512, key0, [], m.readBytes msgA 16) sU ∗ emp := by
    refine ⟨_, sep_intro (disj_empty_right (plain_union plain_empty P123))
      (sep_intro (disj_empty_left P123) (pure_intro ⟨length_readBytes _ _ _, ?_, ?_⟩)
        (sep_intro D2 ?_ (sep_intro D3 ?_ ⟨m, rfl⟩))) emp_intro, ?_⟩
    · rw [sU_x0]; show Rep stA (m.readBytes stA 512) key0 []; rw [f_st1]; exact h0
    · rw [sU_x2, length_readBytes]
    · rw [sU_x0]; exact points_region 512 stA m (by decide)
    · rw [sU_x1]; exact points_regionRO 16 msgA m (by decide)
    · exact matches_union (plain_union plain_empty P123) plain_empty
        (matches_union plain_empty P123 (matches_empty _)
          (matches_union (plain_region _ _ _) P23
            (matches_region fun _ h => memOf_st st1N 0 h)
            (matches_union (plain_regionRO _ _ _) (plain_region _ _ _)
              (matches_regionRO fun _ h => memOf_msg st1N 0 h)
              (matches_region fun _ h => memOf_stk st1N 0 (by decide) h))))
        (matches_empty _)
  have hpost := run_post hok rfl hpre (by decide) (codeLoaded st1N 0) (by decide)
    rfl (fun _ => rfl) rfl ht
  obtain ⟨h, ⟨h1, h2, hd, rfl, hp1, _⟩, hm⟩ := hpost
  obtain ⟨h11, h12, hd1, rfl, ⟨st', ha, hb, hd11, rfl, ⟨_, hφ⟩, hpts⟩, _⟩ := hp1
  have e := owned_eq_readBytes hpts
    (subRW_trans (subRW_right hd11) (subRW_trans (subRW_left _ _) (subRW_left _ _))) hm
  rw [hφ.1, sU_x0, hv] at e
  have := hφ.2; rw [sU_x0, e] at this; exact this

/-- `finish` would have to write RFC 8439's tag; it writes another. -/
theorem after_finish (Rep : StateRep) (hf : finishOk Rep) (key0 msg0 : List (BitVec 8))
    (h0 : Rep stA (bytesOfNat 512 st2N) key0 msg0) :
    poly1305Mac msg0 key0 = bytesOfNat 16 macBadN := by
  obtain ⟨t, ht, hv⟩ := traj_of f_fin
  have hok : subroutine_ok P sF.pc (finishSpec Rep) := hf.2 pl0 placeable
  let m := memOf st2N 0
  have D3 : (regionHeap macA 16 m).Disjoint (regionHeap (sF.sp - BitVec.ofNat 64 48) 48 m) :=
    disj_supp (plain_region _ _ _) (plain_region _ _ _) (supp_region _ _ _)
      (supp_region _ _ _) (sep_reg (by decide))
  have P23 := plain_union (plain_region macA 16 m) (plain_region (sF.sp - BitVec.ofNat 64 48) 48 m)
  have D2 : (regionHeap stA 512 m).Disjoint
      ((regionHeap macA 16 m).union (regionHeap (sF.sp - BitVec.ofNat 64 48) 48 m)) :=
    disj_supp (plain_region _ _ _) P23 (supp_region _ _ _)
      (supp_union (supp_region _ _ _) (supp_region _ _ _)) (fun x hx hy => by
        rcases hy with hy | hy
        · exact sep_reg (by decide) x hx hy
        · exact sep_reg (by decide) x hx hy)
  have P123 := plain_union (plain_region stA 512 m) P23
  have hpre : sF.mem ⊨ (finishSpec Rep).pre
      (m.readBytes stA 512, key0, msg0, m.readBytes macA 16) sF ∗ emp := by
    refine ⟨_, sep_intro (disj_empty_right (plain_union plain_empty P123))
      (sep_intro (disj_empty_left P123)
        (pure_intro ⟨length_readBytes _ _ _, ?_, length_readBytes _ _ _⟩)
        (sep_intro D2 ?_ (sep_intro D3 ?_ ⟨m, rfl⟩))) emp_intro, ?_⟩
    · rw [sF_x0]; show Rep stA (m.readBytes stA 512) key0 msg0; rw [f_st2]; exact h0
    · rw [sF_x0]; exact points_region 512 stA m (by decide)
    · rw [sF_x1]; exact points_region 16 macA m (by decide)
    · exact matches_union (plain_union plain_empty P123) plain_empty
        (matches_union plain_empty P123 (matches_empty _)
          (matches_union (plain_region _ _ _) P23
            (matches_region fun _ h => memOf_st st2N 0 h)
            (matches_union (plain_region _ _ _) (plain_region _ _ _)
              (matches_region fun _ h => memOf_mac st2N 0 h)
              (matches_region fun _ h => memOf_stk st2N 0 (by decide) h))))
        (matches_empty _)
  have hpost := run_post hok rfl hpre (by decide) (codeLoaded st2N 0) (by decide)
    rfl (fun _ => rfl) rfl ht
  obtain ⟨h, ⟨h1, h2, hd, rfl, hp1, _⟩, hm⟩ := hpost
  obtain ⟨hA, hBC, hdA, rfl, _, ⟨hB, hC, hdB, rfl, hmac, _⟩⟩ := hp1
  have e := owned_eq_readBytes hmac
    (subRW_trans (subRW_left hB hC) (subRW_trans (subRW_right hdA) (subRW_left _ _))) hm
  have hl : (poly1305Mac msg0 key0).length = 16 := by simp [poly1305Mac, numTo16LeBytes]
  rw [sF_x1, hl, hv] at e
  exact e

theorem not_goal : ¬ ∃ Rep : StateRep, initOk Rep ∧ updateOk Rep ∧ finishOk Rep := by
  rintro ⟨Rep, hi, hu, hf⟩
  have h1 := after_init Rep hi
  have h2 := after_update Rep hu _ h1
  have h3 := after_finish Rep hf _ _ h2
  rw [f_key, f_msg, List.nil_append, f_rfc] at h3
  exact f_ne h3

end Poly1305Boringssl.Cex
end

open Poly1305Boringssl in
theorem solution : ¬ (∃ Rep : StateRep, initOk Rep ∧ updateOk Rep ∧ finishOk Rep) :=
  Poly1305Boringssl.Cex.not_goal
