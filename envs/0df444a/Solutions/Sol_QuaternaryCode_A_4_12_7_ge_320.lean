-- Prove2me | solution 1 for QuaternaryCode.A_4_12_7_ge_320
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-20T02:33:43.863677+00:00
-- url     : https://prove2.me/submissions/9bd5ea2b-0432-404b-8206-41210e2f3d70

import Mathlib

set_option autoImplicit false

namespace QaryCodeCert

/-! ## Bit-sliced checker for `q`-ary codes

A code of `M` words of length `n` over the alphabet `{0, ..., q-1}` is given twice: as the list `words`
(word `j` is the natural number whose base-`q` digit `c`, least significant first, is its symbol at
coordinate `c`) and as the table `cols` of its `n * q` symbol columns (`cols[c][a]` is the `M`-bit natural
number whose bit `j` says that word `j` has symbol `a` at coordinate `c`); `cols` is checked to be computed
from `words`.

For a word `x`, `run q x 0 cols Ts` walks the coordinates and, at coordinate `c`, adds the column of the
symbol of `x` at `c` to unary saturating counters, one bit-slice per word: bit `j` of the `k`-th counter
(0-based) says that word `j` agrees with `x` in at least `k + 1` coordinates. Everything below is proved;
the final checks are `decide +kernel`. -/

/-- the symbol of the word `x` at coordinate `c`: digit `c` of `x` in base `q`. -/
def sym (q x c : ℕ) : ℕ := x / q ^ c % q

theorem sym_lt {q : ℕ} (hq : 0 < q) (x c : ℕ) : sym q x c < q := Nat.mod_lt _ hq

/-- advance all counters by one column `B`; `p` is the previous (lower) counter. -/
def upd (B : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | p, t :: ts => (t ||| (p &&& B)) :: upd B t ts

/-- process the coordinates `c, c + 1, ...`; `R :: rs` are their symbol columns. -/
def run (q x : ℕ) : ℕ → List (List ℕ) → List ℕ → List ℕ
  | _, [], Ts => Ts
  | c, R :: rs, Ts => run q x (c + 1) rs (upd (R.getD (sym q x c) 0) (R.getD (sym q x c) 0) Ts)

/-- symbol column `(c, a)` of a list of words: bit `j` says that word `j` has symbol `a` at coordinate `c`. -/
def colOf (q c a : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.bit (decide (sym q x c = a)) (colOf q c a xs)

/-- row check: for every word `x = words[i]`, the counter "agreement ≥ s + 1" is exactly `{i}`. -/
def rowsOk (q : ℕ) (cols : List (List ℕ)) (s : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, x :: xs => ((run q x 0 cols (List.replicate (s + 1) 0)).getD s 0 == 2 ^ i) && rowsOk q cols s (i + 1) xs

/-- `Rep j m k Ts`: bit `j` of the `idx`-th entry of `Ts` is `decide (k + idx + 1 ≤ m)`. -/
def Rep (j m : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | k, t :: ts => t.testBit j = decide (k + 1 ≤ m) ∧ Rep j m (k + 1) ts

theorem upd_length (B : ℕ) : ∀ (Ts : List ℕ) (p : ℕ), (upd B p Ts).length = Ts.length := by
  intro Ts
  induction Ts with
  | nil => intro p; simp [upd]
  | cons t ts ih => intro p; simp [upd, ih]

theorem run_length (q x : ℕ) : ∀ (cs : List (List ℕ)) (c : ℕ) (Ts : List ℕ),
    (run q x c cs Ts).length = Ts.length := by
  intro cs
  induction cs with
  | nil => intro c Ts; simp [run]
  | cons R cs ih =>
    intro c Ts
    simp only [run, ih, upd_length]

theorem rep_replicate (j : ℕ) (K : ℕ) : ∀ k, Rep j 0 k (List.replicate K 0) := by
  induction K with
  | zero => intro k; simp [Rep]
  | succ K ih => intro k; simp only [List.replicate_succ, Rep]; exact ⟨by simp, ih (k + 1)⟩

theorem upd_rep (B j : ℕ) : ∀ (Ts : List ℕ) (k m p : ℕ), Rep j m k Ts →
    (p.testBit j && B.testBit j) = (decide (k ≤ m) && B.testBit j) →
    Rep j (m + if B.testBit j then 1 else 0) k (upd B p Ts) := by
  intro Ts
  induction Ts with
  | nil => intro k m p _ _; simp [upd, Rep]
  | cons t ts ih =>
    intro k m p h hp
    simp only [Rep] at h
    obtain ⟨ht, hts⟩ := h
    simp only [upd, Rep]
    refine ⟨?_, ih (k + 1) m t hts (by rw [ht])⟩
    rw [Nat.testBit_or, Nat.testBit_and, hp, ht]
    cases hB : B.testBit j
    · simp
    · by_cases h2 : k ≤ m
      · have h3 : k + 1 ≤ m + 1 := by omega
        simp [h2, h3]
      · have h1 : ¬ k + 1 ≤ m := by omega
        have h3 : ¬ k + 1 ≤ m + 1 := by omega
        simp [h1, h2, h3]

theorem run_rep (q x j : ℕ) : ∀ (cs : List (List ℕ)) (c m : ℕ) (Ts : List ℕ), Rep j m 0 Ts →
    Rep j (m + ∑ i ∈ Finset.range cs.length,
      if ((cs.getD i []).getD (sym q x (c + i)) 0).testBit j then 1 else 0) 0 (run q x c cs Ts) := by
  intro cs
  induction cs with
  | nil => intro c m Ts h; simpa [run] using h
  | cons R cs ih =>
    intro c m Ts h
    have h1 : Rep j (m + if (R.getD (sym q x c) 0).testBit j then 1 else 0) 0
        (upd (R.getD (sym q x c) 0) (R.getD (sym q x c) 0) Ts) :=
      upd_rep _ j Ts 0 m _ h (by rw [Bool.and_self, decide_eq_true (Nat.zero_le m), Bool.true_and])
    have h2 := ih (c + 1) _ _ h1
    simp only [run]
    have e : (m + ∑ i ∈ Finset.range (R :: cs).length,
          if (((R :: cs).getD i []).getD (sym q x (c + i)) 0).testBit j then 1 else 0) =
        (m + if (R.getD (sym q x c) 0).testBit j then 1 else 0) + ∑ i ∈ Finset.range cs.length,
          if ((cs.getD i []).getD (sym q x (c + 1 + i)) 0).testBit j then 1 else 0 := by
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
      have hs : (∑ i ∈ Finset.range cs.length,
            if ((cs.getD i []).getD (sym q x (c + (i + 1))) 0).testBit j then 1 else 0) =
          ∑ i ∈ Finset.range cs.length,
            if ((cs.getD i []).getD (sym q x (c + 1 + i)) 0).testBit j then 1 else 0 :=
        Finset.sum_congr rfl (fun i _ => by rw [show c + (i + 1) = c + 1 + i by omega])
      rw [hs]
      ring
    rw [e]
    exact h2

theorem rep_getD (j m : ℕ) : ∀ (Ts : List ℕ) (k idx : ℕ), Rep j m k Ts → idx < Ts.length →
    (Ts.getD idx 0).testBit j = decide (k + idx + 1 ≤ m) := by
  intro Ts
  induction Ts with
  | nil => intro k idx _ h; simp at h
  | cons t ts ih =>
    intro k idx h hidx
    simp only [Rep] at h
    cases idx with
    | zero => simpa using h.1
    | succ idx =>
      simp only [List.getD_cons_succ]
      rw [ih (k + 1) idx h.2 (by simpa using hidx)]
      have e : k + 1 + idx + 1 = k + (idx + 1) + 1 := by omega
      rw [e]

theorem colOf_testBit (q c a : ℕ) : ∀ (ws : List ℕ) (j : ℕ), j < ws.length →
    (colOf q c a ws).testBit j = decide (sym q (ws.getD j 0) c = a) := by
  intro ws
  induction ws with
  | nil => intro j h; simp at h
  | cons x xs ih =>
    intro j hj
    cases j with
    | zero => simp [colOf]
    | succ j =>
      simp only [colOf, Nat.testBit_bit_succ, List.getD_cons_succ]
      exact ih j (by simpa using hj)

theorem rowsOk_sound (q : ℕ) (cols : List (List ℕ)) (s : ℕ) : ∀ (xs : List ℕ) (i0 : ℕ),
    rowsOk q cols s i0 xs = true →
    ∀ idx < xs.length, (run q (xs.getD idx 0) 0 cols (List.replicate (s + 1) 0)).getD s 0 = 2 ^ (i0 + idx) := by
  intro xs
  induction xs with
  | nil => intro i0 _ idx h; simp at h
  | cons x xs ih =>
    intro i0 h idx hidx
    simp only [rowsOk, Bool.and_eq_true, beq_iff_eq] at h
    cases idx with
    | zero => simpa using h.1
    | succ idx =>
      simp only [List.getD_cons_succ]
      rw [ih (i0 + 1) h.2 idx (by simpa using hidx)]
      congr 1
      omega

/-- `d(x,y) + #{c | x c = y c} = n` for words of length `n`. -/
theorem ham_agree {n q : ℕ} (x y : Fin n → Fin q) :
    hammingDist x y + (Finset.univ.filter (fun c => x c = y c)).card = n := by
  simp only [hammingDist, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  have h : ∀ c ∈ (Finset.univ : Finset (Fin n)),
      ((if x c ≠ y c then 1 else 0) + (if x c = y c then 1 else 0) : ℕ) = 1 := by
    intro c _
    by_cases hc : x c = y c <;> simp [hc]
  rw [Finset.sum_congr rfl h]
  simp

/-- word `j` of the list, as a function from coordinates to symbols. -/
def word (q : ℕ) (hq : 0 < q) (words : List ℕ) (n j : ℕ) : Fin n → Fin q :=
  fun c => ⟨sym q (words.getD j 0) c, sym_lt hq _ _⟩

theorem sound (q n M s : ℕ) (hq : 0 < q) (hs : s < n) (words : List ℕ) (cols : List (List ℕ))
    (hlen : words.length = M)
    (hcols : cols = (List.range n).map (fun c => (List.range q).map (fun a => colOf q c a words)))
    (hR : rowsOk q cols s 0 words = true) :
    ∃ C : Finset (Fin n → Fin q), C.card = M ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → n - s ≤ hammingDist x y) := by
  have hcl : cols.length = n := by rw [hcols]; simp
  have hcol : ∀ c < n, ∀ a < q, ∀ j < M,
      ((cols.getD c []).getD a 0).testBit j = decide (sym q (words.getD j 0) c = a) := by
    intro c hc a ha j hj
    have e1 : cols.getD c [] = (List.range q).map (fun a => colOf q c a words) := by
      rw [hcols, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
      rfl
    have e2 : ((List.range q).map (fun a => colOf q c a words)).getD a 0 = colOf q c a words := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha]
      rfl
    rw [e1, e2]
    exact colOf_testBit q c a words j (by omega)
  -- the counter value for word `x` against word `j`
  have hcount : ∀ x j : ℕ, j < M → (∑ i ∈ Finset.range cols.length,
      if ((cols.getD i []).getD (sym q x (0 + i)) 0).testBit j then 1 else 0) =
      (Finset.univ.filter (fun c : Fin n => sym q (words.getD j 0) c = sym q x c)).card := by
    intro x j hj
    rw [hcl, Finset.card_filter, Finset.sum_range]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Nat.zero_add, hcol c c.isLt _ (sym_lt hq _ _) j hj]
    simp
  -- agreements
  have hov : ∀ i < M, ∀ j < M, i ≠ j →
      (Finset.univ.filter (fun c => word q hq words n i c = word q hq words n j c)).card ≤ s := by
    intro i hi j hj hij
    have hr := rowsOk_sound q cols s words 0 hR i (by omega)
    have hrep := run_rep q (words.getD i 0) j cols 0 0 _ (rep_replicate j (s + 1) 0)
    rw [hcount _ j hj] at hrep
    have hlenT := run_length q (words.getD i 0) cols 0 (List.replicate (s + 1) 0)
    rw [List.length_replicate] at hlenT
    have e := rep_getD j _ _ 0 s hrep (by omega)
    rw [hr, Nat.testBit_two_pow] at e
    have hne : decide (0 + i = j) = false := by simp; omega
    rw [hne] at e
    have e' : ¬ (0 + s + 1 ≤ 0 + (Finset.univ.filter
        (fun c : Fin n => sym q (words.getD j 0) c = sym q (words.getD i 0) c)).card) := by
      intro hh; rw [decide_eq_true hh] at e; exact Bool.false_ne_true e
    have hfil : (Finset.univ.filter (fun c => word q hq words n i c = word q hq words n j c)) =
        Finset.univ.filter (fun c : Fin n => sym q (words.getD j 0) c = sym q (words.getD i 0) c) := by
      apply Finset.filter_congr
      intro c _
      simp only [word, Fin.mk.injEq]
      exact eq_comm
    rw [hfil]
    omega
  have hdist : ∀ i < M, ∀ j < M, i ≠ j →
      n - s ≤ hammingDist (word q hq words n i) (word q hq words n j) := by
    intro i hi j hj hij
    have h1 := ham_agree (word q hq words n i) (word q hq words n j)
    have h2 := hov i hi j hj hij
    omega
  let f : Fin M → (Fin n → Fin q) := fun j => word q hq words n j
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hne' : (a : ℕ) ≠ b := fun e => hne (Fin.ext e)
    have := hdist a a.isLt b b.isLt hne'
    have h0 : hammingDist (word q hq words n a) (word q hq words n b) = 0 := by
      have : f a = f b := hab
      simp only [f] at this
      rw [this, hammingDist_self]
    omega
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro x hx y hy hxy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
    have hab : (a : ℕ) ≠ b := fun e => hxy (by simp only [f]; rw [e])
    exact hdist a a.isLt b b.isLt hab

end QaryCodeCert

namespace QaryCodeCert

/-- the 320 codewords: base-4 digit `c` (least significant first) of a word is its symbol at coordinate `c`
(`c < 12`). -/
def words : List ℕ := [463000, 8320774, 14716641, 10054015, 1852000, 6661630, 16505881, 8534919,
  2490820, 6284890, 12689341, 12089379, 6298690, 1702876, 8880699, 16672165,
  7408000, 585246, 9869305, 15691879, 12854785, 12435871, 2340984, 5922790,
  8417545, 16357015, 6811504, 1968366, 115750, 7873464, 15096415, 10468801,
  4349980, 3901314, 10878565, 14424571, 9963280, 14803086, 8362345, 425719,
  1087495, 6913945, 16189054, 9363936, 622705, 7366639, 15605256, 9959830,
  1597830, 6391320, 16777215, 8788065, 2800850, 5462860, 13443755, 11846965,
  9088820, 15943850, 7156045, 1365715, 2272205, 5983315, 12924340, 12374570,
  11482250, 14078740, 4762355, 3231085, 11259170, 13773500, 5002075, 3519685,
  11203400, 13833430, 5074225, 3443375, 5627066, 2898724, 11682499, 13346141,
  14465621, 10837451, 3875884, 4375474, 12211676, 12825154, 6146981, 2370619,
  5731049, 3052919, 11594896, 13175566, 15292274, 9482476, 968971, 7810709,
  9795374, 15503536, 7530839, 724681, 1905922, 6615708, 16419707, 8613093,
  7623688, 897942, 9685617, 15347183, 2216272, 5781198, 12996393, 12560567,
  554068, 7443402, 15723053, 9833907, 13717537, 11057087, 3591768, 5188038,
  5507188, 3010538, 11769357, 13267347, 8865088, 16687838, 6347577, 1653927,
  138517, 8125067, 15041388, 10249458, 4538503, 3974937, 10673918, 14367072,
  1376797, 7136643, 15899748, 9141242, 4228933, 3760347, 10950972, 14614178,
  5251537, 2737743, 12042152, 13522998, 2236962, 6014396, 12958811, 12344261,
  8947848, 15822614, 7280369, 1503599, 7605738, 911988, 9671571, 15365133,
  11128887, 13645737, 5131854, 3647952, 10290042, 15000804, 8035587, 227997,
  14591808, 10961118, 3750201, 4251303, 6205752, 2578086, 12136257, 12634335,
  15405957, 9630747, 822780, 7694946, 8776467, 16518285, 6452586, 1807092,
  11292183, 14002569, 4968558, 3291120, 5117868, 3665970, 11110869, 13659723,
  1551438, 7228368, 15741495, 9033129, 12902778, 12388068, 2326275, 5937309,
  8045793, 205695, 10312344, 14990598, 14777028, 10001754, 451773, 8323875,
  11614302, 13164480, 5678631, 3097017, 3694257, 4307247, 14663880, 10889046,
  1279467, 6972021, 15997842, 9305100, 11717420, 13315250, 5592405, 2929355,
  4602394, 4185476, 10593379, 14173181, 3807814, 4455896, 14517311, 10773409,
  1721914, 6529444, 16635971, 8667101, 6887656, 1113974, 9340561, 16212239,
  9539206, 15231256, 7737599, 1046369, 1632361, 6361079, 16741904, 8819086,
  23010, 7978620, 15189915, 10362885, 92040, 7897110, 15137265, 10428015,
  368160, 8157630, 14811225, 10217415, 1472640, 7315230, 15853305, 8913255,
  5890560, 2098590, 12483705, 13081575, 6785025, 1994655, 8394360, 16380390,
  4502690, 4019004, 10693339, 14339397, 2378570, 6139092, 12834099, 12202669,
  4934180, 3321274, 11326557, 13972419, 9514280, 15256246, 7779153, 1004751,
  13797650, 11234956, 3479403, 5042421, 11838020, 13452762, 5454909, 2808739,
  8983250, 15791436, 7244971, 1534773, 10634420, 14394154, 4577997, 3947859,
  2959505, 5558031, 13285096, 11751798, 1233545, 7025943, 16076016, 9218926,
  2658605, 5338803, 13569876, 11987146, 4858955, 3392469, 11385394, 13917612]

/-- the 12 x 4 symbol columns of the code (`cols[c][a]` has bit `j` iff word `j` has symbol `a` at coordinate `c`). -/
def cols : List (List ℕ) := [[1103586911189548124406974665106075429044613835115965407622047772468535418893502830008058909892881,
   275905355237043450498537615845957284617523565374331195131510296941350617116991101713807075214404,
   605183162001811399002446593153520777723213354072278966456697472369112210188356001855717962289698,
   151311607492507108487062832063998623217353767794077200736786066043221479581790616445378139539592],
  [552819163011370111742568175515868182601595025255277812259019714633148796242616928314198275987476,
   301679947505369889637133954299845816031506094493986833756133863532754240193030184851322371080578,
   200905237399717453777050357320105922604624663559038729514919755936953819558482337890222467203649,
   1080582688004452627238269219033732193364978739048349394416968273719362869786511098967218972664872],
  [200843862968375888617256174855620542142912016339812887946490200076009581150000355923753027309954,
   301465172068484271830958523619122402553186879177948360476304104915424639221523071250420327391809,
   1080644086313161830083856035530148666276001169064489831382146738813520823530401376155756504057876,
   553033914570888091862950972164660503630604457774401690142100564017264681878715746693032228176936],
  [543453730859897462148524089293742726614828921739231990069930084236559476725186925734334752245826,
   171323138461883028738099267944778656652298126353185559593092045048657416436033259751622683660824,
   1085237601478171958091583169987911924091623833290200999543123972023487534509165421972963404645505,
   335972565120957633416815178943118807243953640974034220740895506513515298110254942564041246384420],
  [202369884391899936491649920025704171843740454763140440588974517021430895685201478558317814487105,
   1077657487708867970853822285852609494902817373076071900042417839187388048541485336925497068716328,
   551344293686370476847727085319763644529061008994299762235256547232646814590938197314828319736340,
   304615370133771698201822414971474803327085685523140667080392704380753966963015537224318883996802],
  [276128514127413632686215952622656996612981526855352721096999240728449128012652734659253955477777,
   151362231011595055519813783605234883696293011565871901665737600978299051447606469187903465751074,
   604960026988761899996463324477819577346499330168815941700170627011299174852007806511572901243016,
   1103536263793139494192528645463840656946930653766612205484134139104172371468373539664231764464708],
  [302526849688315164797406658139869633863506363228654241779132315956225884877516679213602178154772,
   1077127780496689880062638389828096667613367733771829200022539319793933644973284647730420052661313,
   204458328449741005530487467529044802645857409103734573407572802773704242315742358544048503030312,
   551874077286164032004489190672541010479973016252434754737797169298355953614096864534891353090178],
  [167965999644992695330468258307499877214098736775262134395670886888688298647823594005231817527681,
   1087030654837020969085040958981443391314403241051974637099415735360364466163469919598170310477848,
   546647270235221066094505785976525307587874780189978834758117032439634579310926442331612261925924,
   334343111203675351885006702904083538486327764339437163693837953133532381658420594087947697005122],
  [1080590815073429275767955489427273426194030848520737080533575089175616074273123661662431275522068,
   552810968522923761327537378295478335211735156766767040716480322346307869711928262754123663877160,
   200903246708929529966653292261426006098707421109579066293953899512170312202710318689464260788610,
   301682005615627515332875546185374347098231095959569582403032296788125469592878306916942886748737],
  [284470324050128081697504959999981893286161007218407210113365560669544777045932506564006208672900,
   1136903399572352810985005899833939474799218717392072479744956287369334051601376743399279562080545,
   143020487930357478268085089154390438182692066154577202803337975898368204245872448742021088290888,
   571592824368071711444425757181240308334632731591595877285381783884972692887458851317655227892242],
  [171184502766022542137935360307110124579422855416582830411988773061953498254218934709057710343297,
   1085272708002651262540367283661805013950389066421187664398804157172212636495940217399026716516888,
   543418624351877724538143309203331888572447963889207067222732894950523999338647102371290816188708,
   336111200800358553178575752997305087500444636629675207913515782637529591691834295543586843887682],
  [275913533339893404474139920778317733785548760914088960809330129607623325732385308155781912338705,
   151303429371011801705941500092126495007541274053392241378800171988491697779408202328043539206690,
   605181117479660011175171235310215527535300796235936927377483506508216074660585836382044436056200,
   1103588955730344865039769049988892358274313691153234640381427799717888627608261203157092199334980]]

theorem words_length : words.length = 320 := by decide +kernel

theorem cols_eq : cols = (List.range 12).map (fun c => (List.range 4).map (fun a => colOf 4 c a words)) := by
  decide +kernel

theorem rows_ok : rowsOk 4 cols 5 0 words = true := by decide +kernel

theorem main : ∃ C : Finset (Fin 12 → Fin 4), C.card = 320 ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 7 ≤ hammingDist x y) := by
  obtain ⟨C, h1, h2⟩ := sound 4 12 320 5 (by norm_num) (by norm_num) words cols words_length cols_eq rows_ok
  exact ⟨C, h1, fun x hx y hy hxy => by simpa using h2 x hx y hy hxy⟩

end QaryCodeCert

theorem solution : ∃ C : Finset (Fin 12 → Fin 4), C.card = 320 ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 7 ≤ hammingDist x y) := by
  exact QaryCodeCert.main
