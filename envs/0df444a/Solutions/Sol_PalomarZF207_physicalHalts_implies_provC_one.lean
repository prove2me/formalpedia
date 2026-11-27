-- Prove2me | solution 1 for PalomarZF207.physicalHalts_implies_provC_one
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T23:49:11.281314+00:00
-- url     : https://prove2.me/submissions/06c6c77f-2c0d-4797-9bbb-a5b92669722f

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_physical
import Definitions.Def_palomar_zf207_calc
import Definitions.Def_palomar_zf207_tm_check
import Theorems.Thm_PalomarZF207_tm_bops_part1
import Theorems.Thm_PalomarZF207_tm_bops_part2
import Theorems.Thm_PalomarZF207_tm_bops_part3
import Theorems.Thm_PalomarZF207_tm_bops_part4
import Theorems.Thm_PalomarZF207_tm_bops_part5

open PalomarZF207
open PalomarZF207History
open PalomarZF207Calc
open PalomarZF207TMCheck

namespace DevTMSound

/-! ### 1. Equivalence of `fastRow` to `stepPhysical` -/

private def checkRowsPrefix : Nat → Nat → List Trans → Bool
  | _, 0, _ => true
  | _, _ + 1, [] => false
  | i, n + 1, r :: rs => (fastRow i == r) && checkRowsPrefix (i + 1) n rs

private theorem checkRowsPrefix_sound : ∀ n i l, checkRowsPrefix i n l = true →
    ∀ j, j < n → fastRow (i + j) = l.getD j (none, none)
  | 0, _, _, _, _, hlt => by omega
  | _ + 1, _, [], h, _, _ => by simp [checkRowsPrefix] at h
  | n + 1, i, r :: rs, h, 0, _ => by
    simp [checkRowsPrefix] at h
    simpa [List.getD] using h.1
  | n + 1, i, r :: rs, h, j + 1, hlt => by
    simp [checkRowsPrefix] at h
    have ih := checkRowsPrefix_sound n (i + 1) rs h.2 j (Nat.lt_of_succ_lt_succ hlt)
    have heq : i + (j + 1) = i + 1 + j := by omega
    rw [heq, ih]; rfl

private theorem literalRows_len : literalRows.length = 207 := by
  have h1 : (literalRows.drop 100).length = 107 := rfl
  rw [List.length_drop] at h1
  omega

private theorem fastRow_eq (q : Nat) : fastRow q = literalRows.getD q (none, none) := by
  by_cases h : q < 207
  · by_cases h1 : q < 70
    · have hchk : checkRowsPrefix 0 70 literalRows = true := rfl
      simpa using checkRowsPrefix_sound 70 0 literalRows hchk q h1
    · by_cases h2 : q < 140
      · have hchk : checkRowsPrefix 70 70 (literalRows.drop 70) = true := rfl
        have := checkRowsPrefix_sound 70 70 (literalRows.drop 70) hchk (q - 70) (by omega)
        have hq : 70 + (q - 70) = q := by omega
        rw [hq] at this
        rw [this]
        simp [List.getD, List.getElem?_drop, hq]
      · have hchk : checkRowsPrefix 140 67 (literalRows.drop 140) = true := rfl
        have := checkRowsPrefix_sound 67 140 (literalRows.drop 140) hchk (q - 140) (by omega)
        have hq : 140 + (q - 140) = q := by omega
        rw [hq] at this
        rw [this]
        simp [List.getD, List.getElem?_drop, hq]
  · have hge : ¬ q < literalRows.length := by rw [literalRows_len]; exact h
    have hble : Nat.ble 207 q = true := Nat.ble_eq.mpr (Nat.le_of_not_lt h)
    have h1 : fastRow q = (none, none) := by unfold fastRow; rw [hble]
    rw [h1]
    simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hge)]

private def fastStep (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (q, left, right) := c
  let r := right / 2
  let tr := match Nat.beq (right % 2) 1 with
    | true => (fastRow q).2
    | false => (fastRow q).1
  match tr with
  | none => c
  | some (write, direction, next) =>
    let w : Nat := match write with | true => 1 | false => 0
    match direction with
    | true => (next, w + 2 * left, r)
    | false =>
      let bit : Nat := left % 2
      let l : Nat := left / 2
      let middle : Nat := w + 2 * r
      (next, l, bit + 2 * middle)

private theorem fastStep_eq (c : Nat × Nat × Nat) : fastStep c = stepPhysical c := by
  rcases c with ⟨q, left, right⟩
  unfold fastStep stepPhysical
  simp only [fastRow_eq]
  cases h : Nat.beq (right % 2) 1
  · have hne : right % 2 ≠ 1 := by intro heq; rw [heq] at h; contradiction
    have h2 : (right % 2 == 1) = false := beq_false_of_ne hne
    simp only [h2]
    cases (literalRows.getD q (none, none)).1 with
    | none => rfl
    | some x => rcases x with ⟨w, d, n⟩; cases w <;> cases d <;> rfl
  · have heq : right % 2 = 1 := Nat.eq_of_beq_eq_true h
    have h2 : (right % 2 == 1) = true := beq_iff_eq.mpr heq
    simp only [h2]
    cases (literalRows.getD q (none, none)).2 with
    | none => rfl
    | some x => rcases x with ⟨w, d, n⟩; cases w <;> cases d <;> rfl

private theorem iterPhysical_add : ∀ m n c,
    iterPhysical (m + n) c = iterPhysical n (iterPhysical m c)
  | 0, n, c => by simp [iterPhysical]
  | m + 1, n, c => by
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h, iterPhysical, iterPhysical, iterPhysical_add m n (stepPhysical c)]

private def runCheckPow : Nat → Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | 0, (q, l, r) =>
    match Nat.ble 207 q with
    | true => none
    | false =>
      let (q', l', r') := fastStep (q, l, r)
      match Nat.beq (q' % 1) 0, Nat.beq (l' % 1) 0, Nat.beq (r' % 1) 0 with
      | true, true, true => some (q', l', r')
      | _, _, _ => none
  | k + 1, c =>
    match runCheckPow k c with
    | none => none
    | some c1 => runCheckPow k c1

private theorem nat_beq_mod_one (n : Nat) : Nat.beq (n % 1) 0 = true := by
  rw [Nat.mod_one]; rfl

private theorem runCheckPow_sound : ∀ k c c',
    runCheckPow k c = some c' →
    iterPhysical (2 ^ k) c = c' ∧ ∀ j < 2 ^ k, (iterPhysical j c).1 < 207
  | 0, (q, l, r), c', h => by
    unfold runCheckPow at h
    cases hb : Nat.ble 207 q with
    | true => rw [hb] at h; contradiction
    | false =>
      rw [hb] at h
      dsimp only at h
      rw [nat_beq_mod_one, nat_beq_mod_one, nat_beq_mod_one] at h
      injection h with hcc; subst hcc
      have hlt : q < 207 := by
        apply Nat.lt_of_not_ge
        intro hge
        have := Nat.ble_eq.mpr hge
        rw [hb] at this; contradiction
      refine ⟨by simp [iterPhysical, fastStep_eq], fun j hj => ?_⟩
      have hj0 : j = 0 := by omega
      subst hj0; exact hlt
  | k + 1, c, c', h => by
    unfold runCheckPow at h
    cases h1 : runCheckPow k c with
    | none => rw [h1] at h; contradiction
    | some c1 =>
      rw [h1] at h
      obtain ⟨hi1, hn1⟩ := runCheckPow_sound k c c1 h1
      obtain ⟨hi2, hn2⟩ := runCheckPow_sound k c1 c' h
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
      refine ⟨?_, fun j hj => ?_⟩
      · rw [hpow, iterPhysical_add, hi1, hi2]
      · by_cases hlt : j < 2 ^ k
        · exact hn1 j hlt
        · have hj' : j = 2 ^ k + (j - 2 ^ k) := by omega
          rw [hj', iterPhysical_add, hi1]
          exact hn2 (j - 2 ^ k) (by omega)

/-! ### 2. Startup Verification (58,616 Steps = 14 × 4096 + 1272) -/

private def runCheckSteps (bits : List Nat) (c : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  match bits with
  | [] => some c
  | k :: ks =>
    match runCheckPow k c with
    | none => none
    | some c1 => runCheckSteps ks c1

private def bitsSum : List Nat → Nat
  | [] => 0
  | k :: ks => 2 ^ k + bitsSum ks

private theorem runCheckSteps_sound : ∀ bits c c',
    runCheckSteps bits c = some c' →
    iterPhysical (bitsSum bits) c = c' ∧ ∀ j < bitsSum bits, (iterPhysical j c).1 < 207
  | [], c, c', h => by
    injection h with hcc; subst hcc
    exact ⟨rfl, fun j hj => by simp [bitsSum] at hj⟩
  | k :: ks, c, c', h => by
    unfold runCheckSteps at h
    cases h1 : runCheckPow k c with
    | none => rw [h1] at h; contradiction
    | some c1 =>
      rw [h1] at h
      obtain ⟨hi1, hn1⟩ := runCheckPow_sound k c c1 h1
      obtain ⟨hi2, hn2⟩ := runCheckSteps_sound ks c1 c' h
      refine ⟨?_, fun j hj => ?_⟩
      · simp only [bitsSum]; rw [iterPhysical_add, hi1, hi2]
      · simp only [bitsSum] at hj
        by_cases hlt : j < 2 ^ k
        · exact hn1 j hlt
        · have hj' : j = 2 ^ k + (j - 2 ^ k) := by omega
          rw [hj', iterPhysical_add, hi1]
          exact hn2 (j - 2 ^ k) (by omega)

/-! ### 2. Safe Reachability & Startup Verification (58,616 Steps) -/

private def SafeReach (c1 c2 : Nat × Nat × Nat) : Prop :=
  ∃ n, iterPhysical n c1 = c2 ∧ ∀ j < n, (iterPhysical j c1).1 < 207

private def SafeReachPos (c1 c2 : Nat × Nat × Nat) : Prop :=
  ∃ n, 0 < n ∧ iterPhysical n c1 = c2 ∧ ∀ j < n, (iterPhysical j c1).1 < 207

private theorem SafeReach.refl (c : Nat × Nat × Nat) : SafeReach c c :=
  ⟨0, rfl, fun _ h => by omega⟩

private theorem SafeReach.trans {c1 c2 c3 : Nat × Nat × Nat}
    (h1 : SafeReach c1 c2) (h2 : SafeReach c2 c3) : SafeReach c1 c3 := by
  obtain ⟨n1, he1, hs1⟩ := h1
  obtain ⟨n2, he2, hs2⟩ := h2
  refine ⟨n1 + n2, by rw [iterPhysical_add, he1, he2], fun j hj => ?_⟩
  by_cases hlt : j < n1
  · exact hs1 j hlt
  · have hj' : j = n1 + (j - n1) := by omega
    rw [hj', iterPhysical_add, he1]
    exact hs2 (j - n1) (by omega)

private theorem SafeReachPos.of_pos {c1 c2 : Nat × Nat × Nat} (h : SafeReachPos c1 c2) :
    SafeReach c1 c2 :=
  let ⟨n, _, he, hs⟩ := h; ⟨n, he, hs⟩

private theorem SafeReach.trans_pos {c1 c2 c3 : Nat × Nat × Nat}
    (h1 : SafeReach c1 c2) (h2 : SafeReachPos c2 c3) : SafeReachPos c1 c3 := by
  obtain ⟨n1, he1, hs1⟩ := h1
  obtain ⟨n2, hp2, he2, hs2⟩ := h2
  refine ⟨n1 + n2, by omega, by rw [iterPhysical_add, he1, he2], fun j hj => ?_⟩
  by_cases hlt : j < n1
  · exact hs1 j hlt
  · have hj' : j = n1 + (j - n1) := by omega
    rw [hj', iterPhysical_add, he1]
    exact hs2 (j - n1) (by omega)

private theorem SafeReachPos.trans {c1 c2 c3 : Nat × Nat × Nat}
    (h1 : SafeReachPos c1 c2) (h2 : SafeReach c2 c3) : SafeReachPos c1 c3 := by
  obtain ⟨n1, hp1, he1, hs1⟩ := h1
  obtain ⟨n2, he2, hs2⟩ := h2
  refine ⟨n1 + n2, by omega, by rw [iterPhysical_add, he1, he2], fun j hj => ?_⟩
  by_cases hlt : j < n1
  · exact hs1 j hlt
  · have hj' : j = n1 + (j - n1) := by omega
    rw [hj', iterPhysical_add, he1]
    exact hs2 (j - n1) (by omega)

private theorem SafeReachPos.step {c : Nat × Nat × Nat} (hq : c.1 < 207) :
    SafeReachPos c (stepPhysical c) :=
  ⟨1, Nat.zero_lt_one, rfl, fun j hj => by
    have hj0 : j = 0 := by omega
    rw [hj0]; exact hq⟩

private theorem SafeReachPos.step_fast {c c' : Nat × Nat × Nat}
    (hq : c.1 < 207) (h : fastStep c = c') : SafeReachPos c c' := by
  rw [← h, fastStep_eq]; exact SafeReachPos.step hq

private def verifyChain8 : List (Nat × Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | c1 :: c2 :: rest =>
    (match runCheckPow 8 c1 with
     | some c => Nat.beq c.1 c2.1 && Nat.beq c.2.1 c2.2.1 && Nat.beq c.2.2 c2.2.2
     | none => false) && verifyChain8 (c2 :: rest)

private theorem verifyChain8_sound : ∀ l c1 c2,
    l.head? = some c1 → l.getLast? = some c2 → verifyChain8 l = true → SafeReach c1 c2
  | [], _, _, h1, _, _ => by simp at h1
  | [x], c1, c2, h1, h2, _ => by
    simp at h1 h2; subst h1; subst h2; exact SafeReach.refl _
  | x :: y :: rest, c1, c2, h1, h2, hv => by
    simp only [List.head?, Option.some.injEq] at h1; subst h1
    unfold verifyChain8 at hv
    have hb := Bool.and_eq_true_iff.mp hv
    have hstep : SafeReach x y := by
      cases hr : runCheckPow 8 x with
      | none => rw [hr] at hb; simp at hb
      | some c =>
        rw [hr] at hb
        have h12 := Bool.and_eq_true_iff.mp hb.1
        have h11 := Bool.and_eq_true_iff.mp h12.1
        have he1 : c.1 = y.1 := Nat.eq_of_beq_eq_true h11.1
        have he2 : c.2.1 = y.2.1 := Nat.eq_of_beq_eq_true h11.2
        have he3 : c.2.2 = y.2.2 := Nat.eq_of_beq_eq_true h12.2
        have hcy : c = y := by
          rcases c with ⟨a1, a2, a3⟩; rcases y with ⟨b1, b2, b3⟩
          dsimp only at he1 he2 he3; subst he1; subst he2; subst he3; rfl
        subst hcy
        obtain ⟨hi, hn⟩ := runCheckPow_sound 8 x c hr
        exact ⟨2 ^ 8, hi, hn⟩
    have hlast : (y :: rest).getLast? = some c2 := by simpa [List.getLast?] using h2
    exact hstep.trans (verifyChain8_sound (y :: rest) y c2 rfl hlast hb.2)

private def startupPts0 : List (Nat × Nat × Nat) := [
  (0, 0, 0),
  (108, 17, 1052664),
  (74, 1, 286130056),
  (3, 273, 17947647),
  (3, 280, 152427519),
  (68, 0, 2566091962528),
  (46, 21626859, 2389),
  (94, 332, 190175230),
  (66, 20, 23265443847),
  (3, 0, 1488988405802),
  (2, 88064, 5592912),
  (7, 348, 28633391103),
  (1, 5407, 1781198335),
  (3, 22, 320695304190),
  (32, 390070235, 21845),
  (34, 91, 1843974799360),
  (10, 384, 460993708031),
  (7, 97, 1843974242300),
  (3, 0, 472056869157926),
  (3, 412159, 449926591),
  (125, 6, 481231049326130),
  (27, 1613, 1879808778240),
  (3, 0, 7699513582033702),
  (38, 443532677829997, 109),
  (4, 26431487, 1840679597),
  (3, 6431, 7539457187839),
  (34, 103935, 471216073984),
  (2, 1632, 30157828734976),
  (38, 109790100906, 449237),
  (74, 1, 30871285869313849),
  (6, 1, 494088319106285529),
  (2, 106496, 7539189438976),
  (50, 6687, 120627019874303),
  (1, 108607, 7539186644991),
  (9, 1704, 482508077400048),
  (3, 1745215, 471198772095),
  (79, 1704, 482508079497209),
  (79, 1704, 482508079431683),
  (68, 0, 31621649493635306848)
]
private def startupPts1 : List (Nat × Nat × Nat) := [
  (68, 0, 31621649493635306848),
  (4, 1, 494088273136757845),
  (50, 29288757679786, 449387),
  (3, 6982943, 1884867091007),
  (24, 27932191, 471216772783),
  (115, 426, 30881662399150700),
  (33, 0, 32381920338735098779008),
  (0, 457642147498, 460173741),
  (4, 6, 505967836795892603669),
  (34, 446917631, 7539508294997),
  (10, 27932352, 120632122976959),
  (60, 27932355, 120632122845887),
  (85, 6819, 7905747379426164406),
  (74, 1, 32381941266129034374229),
  (1, 446914815, 120632131643947),
  (3, 6983079, 7720456156785407),
  (4, 6, 8095485316532392672021),
  (74, 1, 32381941264662839553109),
  (50, 31449266696745320672694, 27),
  (74, 1, 518111064884815914265685),
  (79, 1704, 505967836795852816507),
  (38, 125797066797974944144237, 109),
  (68, 0, 530545731036524173187552608),
  (6, 0, 132636432759131008938394968),
  (84, 111731199, 123527304045046719),
  (3, 6819, 2023871348374533832691),
  (3, 1746047, 7905747458882990079),
  (68, 0, 132636432759130905859138904),
  (1, 468705486026070, 29451204310),
  (6, 0, 2122182924446707432407901528),
  (10, 1788035072, 123527304062544567),
  (68, 0, 530545731111536120613226838),
  (77, 1705, 129527766384663840423788),
  (50, 1874900327295658, 1884877076187),
  (83, 106, 33159108195142439507327689),
  (6, 0, 33954926791825857918066435416),
  (115, 426, 8289777048785609742614466),
  (32, 6984319, 505967837450293567487),
  (50, 27937023, 2023871349801266534399)
]
private def startupPts2 : List (Nat × Nat × Nat) := [
  (50, 27937023, 2023871349801266534399),
  (4, 28608364543, 1976436865039250773),
  (4, 26, 2122182924488559013228709669),
  (68, 0, 8692461258705137691796504204672),
  (74, 1, 33954926791816944246019058261),
  (6, 106, 530545731122138287112716393),
  (60, 28611706879, 1976436865039684935),
  (4, 1, 543278828669219726517849819733),
  (1, 27939327, 32381941596819112517631),
  (39, 27288, 33159108195142805577793535),
  (115, 426, 2122182924489139556710350870),
  (1, 1788493823, 505967837450232048511),
  (83, 106, 8488731697956558227915145145),
  (2, 436736, 2072444262196425348349952),
  (1, 27955199, 32381941596819145547775),
  (43, 6832, 132636432780571222311174143),
  (2, 111951872, 8095485399204697040896),
  (3, 0, 2173115314676566657688372388694),
  (2, 7168065536, 126491959362573391264),
  (3, 6836, 132636432780565358305083390),
  (34, 112041983, 8095485399204697040896),
  (84, 120297567194895701, 7539508304748),
  (68, 0, 34769845034829678200236294537312),
  (1, 25836912639, 31622989840643347567),
  (21, 6287, 132636432780569756351594495),
  (10, 425201762304, 1976436865040209238),
  (3, 24, 33954926791825576151031480307),
  (10, 106837311488, 126491959362579027291),
  (3, 408063, 33159108195143366774620159),
  (44, 100, 135819707167309482106510376960),
  (98, 430033600511, 31622989840644756823),
  (32, 108716359679, 126491959362579027291),
  (6, 1, 8692461258707806854816664125465),
  (1, 6543, 2122182924489175473575690239),
  (3, 108543, 132636432780575666121736191),
  (10, 27648, 530545731122302664486944767),
  (3, 108, 135819707167309481833779953662),
  (3, 1853882367, 8095485399205057746687),
  (84, 7567732375547, 1976436865040297300)
]
private def startupPts3 : List (Nat × Nat × Nat) := [
  (84, 7567732375547, 1976436865040297300),
  (56, 119453777919, 126491959362579027291),
  (2, 7516192768, 2023871349801264436640),
  (3, 1855, 8488731697956701894302760959),
  (10, 122880, 2122182924489223164787687423),
  (48, 4538783999449770, 30881826016254827),
  (14, 0, 8901080328916846676952860420211744),
  (1, 272383, 530545731122305241441107967),
  (3, 4521983, 33159108195144089759252479),
  (98, 75041668595674, 1976436865040307627),
  (56, 73662463, 2072444262196505609953279),
  (10, 304942678016, 505967837450318752429),
  (6, 0, 2225270082229210180057467421982248),
  (2, 21495808, 8289777048786022439747584),
  (3, 0, 556317520557302536004968577498698),
  (10, 21757952, 132636432780576445740810239),
  (3, 91328184582101, 31622989840644934506),
  (4, 5, 556317520557302908676325913919532),
  (63, 5, 556317520557302908113513399451436),
  (3, 349962239, 8289777048786027853209599),
  (60, 375557987676105389, 7720456504063704),
  (77, 5, 8901080328916847352472188682764524),
  (4, 5, 8901080328916847351346563653828396),
  (68, 0, 569669141050678230558220075696914472),
  (1, 21102591, 2122182924489223325841752063),
  (68, 0, 2278676564202712922232950671531834016),
  (10, 90112, 543278828669241171415555637247),
  (4, 98956046499818, 505967837450319121237),
  (2, 92, 556317520557302953712356547362816),
  (68, 0, 9114706256810851519836836327107579520),
  (10, 96256, 8692461258707858743015237484543),
  (56, 1546188226559, 518111065549126788557483),
  (10, 1610612736, 530545731122305831482863615),
  (3, 395263, 2173115314676964685753675153407),
  (34, 1575, 556317520557302959552973051527168),
  (1, 411566079, 2122182924489223325797236735),
  (3, 6319, 139079380139325739882380095651839),
  (1, 1999084996559822458371290328128365, 438),
  (34, 6479871, 2173115314676964687952837869568)
]
private def startupPts4 : List (Nat × Nat × Nat) := [
  (34, 6479871, 2173115314676964687952837869568),
  (60, 404607, 34769845034831434989653236645887),
  (10, 424664891392, 530545731122305832099425119),
  (21, 105495134207, 2122182924489223328397700479),
  (10, 6803228196864, 33159108195144114506214069),
  (3, 1665138687, 135819707167310293017318612991),
  (38, 446419313063079253, 8095485399205106080621),
  (68, 0, 9333459206974312140709648816482579119558),
  (50, 104398847, 34769845034831435012402058100735),
  (33, 0, 597341389246355977004064775783011974099328),
  (1, 125655865747620261116212628123062, 28760941),
  (74, 1, 37333836827897248562828410419353483214961),
  (68, 0, 2389365556985423908018657084160138056539232),
  (76, 100, 583341200435894508794193912802398175232),
  (1, 1679818751, 34769845034831435012471312924671),
  (6, 0, 597341389246355977005254565443018336236696),
  (81, 8158599263068786059756296750347995, 7190235),
  (68, 0, 2389365556985423908021601062818595920151334),
  (68, 0, 9557462227941695632085223659935141245947032),
  (34, 6608895, 142417285262669557811117235590135808),
  (1, 433019944959, 2173115314676964688279986853247),
  (4, 25, 37333836827897248562837513605973329051500),
  (81, 1904958367003826523584219, 494109216260077275),
  (2, 413120, 36458825027243406799647280414798643200),
  (3, 443446783377405, 33954926791827573254375979178),
  (3, 100, 149335347311588994251355260579015242547207),
  (3, 1642495, 9114706256810851699911820103196344319),
  (102, 101, 149335347311588994251355260579015242547200),
  (1, 25887, 583341200435894508794356477842832752639),
  (3, 7078106103807, 2173115314676964688280062700207),
  (1, 112425063940095, 135819707167310293017502870186),
  (3, 434110463, 35604321315667389452780391229816831),
  (1, 1947976174183722926959469, 7905747460161236406),
  (2, 444529115136, 556317520557302960199695732659456),
  (46, 461618961805474475, 530545731122305832099624378),
  (10, 27262976, 9114706256810851699911814883896721407),
  (15, 118219490218475178, 2122182924489223328398497515),
  (2, 1736704, 145835300108973627198589038096445079552),
  (3, 1697, 149335347311588994251355174870159712059391)
]
private def startupPts5 : List (Nat × Nat × Nat) := [
  (3, 1697, 149335347311588994251355174870159712059391),
  (115, 426, 597341389246355977005420700043039045844992),
  (1, 7318758490111, 34769845034831435012480983279807),
  (3, 0, 611677582588268520453550796844634932898668886),
  (84, 6980735, 36458825027243406799647259524144824319),
  (56, 111710207, 2278676564202712924977953720259051519),
  (126, 6818, 37333836827897248562838793752724300103676),
  (24, 457619537919, 556317520557302960199695732485119),
  (3, 1704, 149335347311588994251355175010759761461259),
  (14, 0, 9786841321412296327256812749478130129352463712),
  (34, 29289059713023, 8692461258707858753120245820072),
  (84, 117156037525503, 2173115314676964688280061455019),
  (79, 1704, 149335347311588994251355175010897200414555),
  (84, 114410717183, 2225270082229211840798782929940479),
  (32, 436444, 583341200435894508794356152386317189119),
  (10, 457648898048, 556317520557302960199695732485119),
  (3, 29289797910527, 8692461258707858753120245818031),
  (68, 0, 39147365285649185309027250998020606908501349760),
  (4, 6, 38229848911766782528346851015813388467949333),
  (74, 1, 152919395647067130113387699211017995736318549),
  (44, 6820, 37333836827897248562838793752586861150204),
  (3, 1788215295, 142417285262669557811122107516190719),
  (98, 29999625008054250, 8488731697956893313593990059),
  (68, 0, 9786841321412296327256812749514158926378145120),
  (10, 1831400898560, 139079380139325740049923933121279),
  (24, 1920398212980536661, 132636432780576458024906094),
  (10, 1831535116288, 139079380139325740049923933121279),
  (3, 30008970856890325, 8488731697956893313593990026),
  (2, 1746944, 145835300108973627198589038096445079552),
  (4, 6, 38229848911766782528346924800537883492482645),
  (34, 109327, 2333364801743578035177424609543121272832),
  (43, 6832, 37333836827897248562838784745525045362686),
  (34, 1791295487, 142417285262669557811122088904491008),
  (20, 27332, 9333459206974312140709679204063393087486),
  (7, 1792016384, 142417285262669557811122088904491008),
  (51, 458789748735, 556317520557302960199695659784191),
  (10, 109408, 2333364801743578035177424304615475642367),
  (56, 1835628756991, 139079380139325740049923914946047),
  (10, 28012544, 9114706256810851699911813689904201727)
]

private theorem startup_ok0 : verifyChain8 startupPts0 = true := rfl
private theorem startup_ok1 : verifyChain8 startupPts1 = true := rfl
private theorem startup_ok2 : verifyChain8 startupPts2 = true := rfl
private theorem startup_ok3 : verifyChain8 startupPts3 = true := rfl
private theorem startup_ok4 : verifyChain8 startupPts4 = true := rfl
private theorem startup_ok5 : verifyChain8 startupPts5 = true := rfl

private def verifyPowChain : List (Nat × (Nat × Nat × Nat) × (Nat × Nat × Nat)) → Bool
  | [] => true
  | (k, c1, c2) :: rest =>
    (match runCheckPow k c1 with
     | some c => Nat.beq c.1 c2.1 && Nat.beq c.2.1 c2.2.1 && Nat.beq c.2.2 c2.2.2
     | none => false) && verifyPowChain rest

private theorem verifyPowChain_step (k : Nat) (c1 c2 : Nat × Nat × Nat)
    (h : (match runCheckPow k c1 with
          | some c => Nat.beq c.1 c2.1 && Nat.beq c.2.1 c2.2.1 && Nat.beq c.2.2 c2.2.2
          | none => false) = true) : SafeReach c1 c2 := by
  cases hr : runCheckPow k c1 with
  | none => rw [hr] at h; contradiction
  | some c =>
    rw [hr] at h
    have h12 := Bool.and_eq_true_iff.mp h
    have h11 := Bool.and_eq_true_iff.mp h12.1
    have hcy : c = c2 := by
      rcases c with ⟨a1, a2, a3⟩; rcases c2 with ⟨b1, b2, b3⟩
      have e1 := Nat.eq_of_beq_eq_true h11.1
      have e2 := Nat.eq_of_beq_eq_true h11.2
      have e3 := Nat.eq_of_beq_eq_true h12.2
      dsimp only at e1 e2 e3; subst e1; subst e2; subst e3; rfl
    subst hcy
    obtain ⟨hi, hn⟩ := runCheckPow_sound k c1 c hr
    exact ⟨2 ^ k, hi, hn⟩

private def startupTailChain : List (Nat × (Nat × Nat × Nat) × (Nat × Nat × Nat)) := [
  (6, (10, 28012544, 9114706256810851699911813689904201727), (3, 1709, 149335347311588994251355155495115563204611)),
  (6, (3, 1709, 149335347311588994251355155495115563204611), (7, 28049408, 9114706256810851699911813689887424512)),
  (6, (7, 28049408, 9114706256810851699911813689887424512), (2, 1712, 149335347311588994251355155495115563204608)),
  (5, (2, 1712, 149335347311588994251355155495115563204608), (11, 26, 9557462227941695632086729951687396045094915)),
  (4, (11, 26, 9557462227941695632086729951687396045094915), (68, 0, 39147365285649185309027245882111574200708759936)),
  (3, (68, 0, 39147365285649185309027245882111574200708759936), (74, 1, 152919395647067130113387679226998336721518593))
]

private theorem startup_tail_ok : verifyPowChain startupTailChain = true := rfl

private theorem verifyPowChain_cons {k : Nat} {c1 c2 : Nat × Nat × Nat} {rest}
    (h : verifyPowChain ((k, c1, c2) :: rest) = true) :
    SafeReach c1 c2 ∧ verifyPowChain rest = true := by
  unfold verifyPowChain at h
  have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨verifyPowChain_step k c1 c2 h1, h2⟩

private theorem startup_safe_reach :
    SafeReach (0, 0, 0) (74, 1, 152919395647067130113387679226998336721518593) := by
  have h0 := verifyChain8_sound startupPts0 _ _ rfl rfl startup_ok0
  have h1 := verifyChain8_sound startupPts1 _ _ rfl rfl startup_ok1
  have h2 := verifyChain8_sound startupPts2 _ _ rfl rfl startup_ok2
  have h3 := verifyChain8_sound startupPts3 _ _ rfl rfl startup_ok3
  have h4 := verifyChain8_sound startupPts4 _ _ rfl rfl startup_ok4
  have h5 := verifyChain8_sound startupPts5 _ _ rfl rfl startup_ok5
  have ⟨s1, ht⟩ := verifyPowChain_cons startup_tail_ok
  have ⟨s2, ht⟩ := verifyPowChain_cons ht
  have ⟨s3, ht⟩ := verifyPowChain_cons ht
  have ⟨s4, ht⟩ := verifyPowChain_cons ht
  have ⟨s5, ht⟩ := verifyPowChain_cons ht
  have ⟨s6, _⟩ := verifyPowChain_cons ht
  exact (((((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans s1).trans s2).trans s3).trans s4).trans s5).trans s6)

/-! ### 3. Bit-Encoded Tape Frames, Window Simulator & 7 Gadget Lemmas -/

private def ones (n : Nat) : Nat := 2 ^ n - 1

private theorem pow2_pos (n : Nat) : 1 ≤ 2 ^ n := Nat.one_le_two_pow

private theorem pow2_succ (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

private theorem pow2_succ_mul (n x : Nat) : 2 ^ (n + 1) * x = 2 * (2 ^ n * x) := by
  rw [pow2_succ, Nat.mul_assoc]

private theorem ones_zero : ones 0 = 0 := rfl

private theorem ones_succ (n : Nat) : ones (n + 1) = 1 + 2 * ones n := by
  unfold ones; rw [pow2_succ]; have := pow2_pos n; omega

private theorem ones_lt (n : Nat) : ones n < 2 ^ n := by
  unfold ones; have := pow2_pos n; omega

private theorem ones_succ_mul (n x : Nat) :
    ones (n + 1) + 2 ^ (n + 1) * x = 1 + 2 * (ones n + 2 ^ n * x) := by
  rw [ones_succ, pow2_succ_mul]; omega

private theorem ones_shift_left (n x : Nat) :
    ones n + 2 ^ n * (1 + 2 * x) = ones (n + 1) + 2 ^ (n + 1) * x := by
  unfold ones; rw [Nat.mul_add, Nat.mul_one, pow2_succ, Nat.mul_left_comm, Nat.mul_assoc]
  have := pow2_pos n; omega

private theorem ones_add (a b : Nat) (suf : Nat) :
    ones (a + b) + 2 ^ (a + b) * suf = ones a + 2 ^ a * (ones b + 2 ^ b * suf) := by
  unfold ones
  have ha := pow2_pos a
  have hb := pow2_pos b
  rw [Nat.pow_add, Nat.mul_add, Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.mul_assoc]
  have hab : 2 ^ a ≤ 2 ^ a * 2 ^ b := Nat.le_mul_of_pos_right _ (by omega)
  omega

private theorem mod2_ones_succ (n suf : Nat) :
    (ones (n + 1) + 2 ^ (n + 1) * suf) % 2 = 1 := by
  rw [ones_succ_mul]; omega

private theorem div2_ones_succ (n suf : Nat) :
    (ones (n + 1) + 2 ^ (n + 1) * suf) / 2 = ones n + 2 ^ n * suf := by
  rw [ones_succ_mul]; omega

private theorem mod2_pow_succ (n suf : Nat) :
    (2 ^ (n + 1) * suf) % 2 = 0 := by
  rw [pow2_succ_mul]; omega

private theorem div2_pow_succ (n suf : Nat) :
    (2 ^ (n + 1) * suf) / 2 = 2 ^ n * suf := by
  rw [pow2_succ_mul]; omega

private theorem mod2_pref (rem pref suf : Nat) (hrem : 1 ≤ rem) :
    (pref + 2 ^ rem * suf) % 2 = pref % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, rem = k + 1 := ⟨rem - 1, by omega⟩
  rw [pow2_succ_mul]; omega

private theorem div2_pref (rem pref suf : Nat) (hrem : 1 ≤ rem) :
    (pref + 2 ^ rem * suf) / 2 = pref / 2 + 2 ^ (rem - 1) * suf := by
  obtain ⟨k, rfl⟩ : ∃ k, rem = k + 1 := ⟨rem - 1, by omega⟩
  rw [pow2_succ_mul]; simp only [Nat.add_sub_cancel]; omega

/-! #### 3.1 Suffix-Invariant Bit-List Window Simulator Soundness -/

private theorem natToBits_length : ∀ k n, (natToBits k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [natToBits, natToBits_length k (n / 2)]

private theorem bitsToNat_append : ∀ as bs,
    bitsToNat (as ++ bs) = bitsToNat as + 2 ^ as.length * bitsToNat bs
  | [], _ => by simp [bitsToNat]
  | a :: as, bs => by
    cases a <;> simp only [List.cons_append, bitsToNat, List.length_cons, pow2_succ, bitsToNat_append as bs, Nat.mul_assoc] <;> omega

private theorem bitsToNat_replicate_true : ∀ k, bitsToNat (List.replicate k true) = ones k
  | 0 => rfl
  | k + 1 => by
    have := pow2_pos k
    simp only [List.replicate, bitsToNat, ones, pow2_succ, bitsToNat_replicate_true k]
    omega

private theorem bitsToNat_replicate_false : ∀ k, bitsToNat (List.replicate k false) = 0
  | 0 => rfl
  | k + 1 => by simp [List.replicate, bitsToNat, bitsToNat_replicate_false k]

private theorem allFalse_sound : ∀ bs, allFalse bs = true → bitsToNat bs = 0
  | [], _ => rfl
  | false :: bs, h => by simp [bitsToNat, allFalse_sound bs h]
  | true :: _, h => by simp [allFalse] at h

private theorem allTrue_sound : ∀ bs, allTrue bs = true → bitsToNat bs = ones bs.length
  | [], _ => rfl
  | true :: bs, h => by
    have := pow2_pos bs.length
    simp only [bitsToNat, List.length_cons, ones, pow2_succ, allTrue_sound bs h]
    omega
  | false :: _, h => by simp [allTrue] at h

private theorem isOneBits_sound : ∀ bs, isOneBits bs = true → bitsToNat bs = 1
  | true :: bs, h => by simp [bitsToNat, allFalse_sound bs h]
  | false :: _, h => by simp [isOneBits] at h
  | [], h => by simp [isOneBits] at h

private theorem beqBits_sound : ∀ as bs, beqBits as bs = true → as = bs
  | [], [], _ => rfl
  | true :: as, true :: bs, h => congrArg (true :: ·) (beqBits_sound as bs h)
  | false :: as, false :: bs, h => congrArg (false :: ·) (beqBits_sound as bs h)
  | true :: _, false :: _, h => by simp [beqBits] at h
  | false :: _, true :: _, h => by simp [beqBits] at h
  | [], _ :: _, h => by simp [beqBits] at h
  | _ :: _, [], h => by simp [beqBits] at h

private theorem popLeft_sound (l : List Bool) :
    (match (generalizing := false) (popLeft l).1 with | true => 1 | false => 0) = bitsToNat l % 2 ∧
    bitsToNat (popLeft l).2 = bitsToNat l / 2 := by
  cases l with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs => cases b <;> simp [popLeft, bitsToNat] <;> omega

private theorem stepBits_sound (q : Nat) (l r : List Bool) (q' : Nat) (l' r' : List Bool) (suf : Nat)
    (h : stepBits q l r = some (q', l', r')) :
    fastStep (q, bitsToNat l, bitsToNat r + 2 ^ r.length * suf) =
      (q', bitsToNat l', bitsToNat r' + 2 ^ r'.length * suf) := by
  cases r with
  | nil => simp [stepBits] at h
  | cons b rs =>
    unfold stepBits at h; dsimp only at h
    have hstep_branch : ∀ (tr : Option (Bool × Bool × Nat)) (R : Nat),
        (match tr with
         | none => some (q, l, b :: rs)
         | some (w, dir, nq) =>
           match dir with
           | true => some (nq, w :: l, rs)
           | false =>
             match (generalizing := false) l with
             | [] => some (nq, [], false :: w :: rs)
             | lb :: ls => some (nq, ls, lb :: w :: rs)) = some (q', l', r') →
        R = bitsToNat rs + 2 ^ rs.length * suf →
        (match tr with
         | none => (q, bitsToNat l, bitsToNat (b :: rs) + 2 ^ (b :: rs).length * suf)
         | some (write, direction, next) =>
           match direction with
           | true => (next, (match write with | true => 1 | false => 0) + 2 * bitsToNat l, R)
           | false => (next, bitsToNat l / 2, bitsToNat l % 2 + 2 * ((match write with | true => 1 | false => 0) + 2 * R))) =
        (q', bitsToNat l', bitsToNat r' + 2 ^ r'.length * suf) := by
      intro tr R htr hR; subst hR
      cases tr with
      | none =>
        injection htr with h1
        have : q = q' ∧ l = l' ∧ b :: rs = r' := by cases h1; exact ⟨rfl, rfl, rfl⟩
        rcases this with ⟨rfl, rfl, rfl⟩; rfl
      | some x =>
        rcases x with ⟨w, dir, nq⟩
        cases dir with
        | true =>
          injection htr with h1
          have : nq = q' ∧ w :: l = l' ∧ rs = r' := by cases h1; exact ⟨rfl, rfl, rfl⟩
          rcases this with ⟨rfl, rfl, rfl⟩
          cases w <;> simp [bitsToNat]
        | false =>
          cases l with
          | nil =>
            injection htr with h1
            have : nq = q' ∧ [] = l' ∧ false :: w :: rs = r' := by cases h1; exact ⟨rfl, rfl, rfl⟩
            rcases this with ⟨rfl, rfl, rfl⟩
            cases w <;> simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_assoc] <;> congr 1 <;> congr 1 <;> omega
          | cons lb ls =>
            injection htr with h1
            have : nq = q' ∧ ls = l' ∧ lb :: w :: rs = r' := by cases h1; exact ⟨rfl, rfl, rfl⟩
            rcases this with ⟨rfl, rfl, rfl⟩
            cases lb <;> cases w <;> simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_assoc] <;>
              (have h1 : (1 + 2 * bitsToNat ls) % 2 = 1 := by omega;
               have h2 : (1 + 2 * bitsToNat ls) / 2 = bitsToNat ls := by omega;
               have h3 : (2 * bitsToNat ls) % 2 = 0 := by omega;
               have h4 : (2 * bitsToNat ls) / 2 = bitsToNat ls := by omega;
               try rw [h1, h2]; try rw [h3, h4]) <;>
              congr 1 <;> congr 1 <;> omega
    cases b with
    | false =>
      dsimp only at h
      have hm : (bitsToNat (false :: rs) + 2 ^ (false :: rs).length * suf) % 2 = 0 := by
        simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_assoc]; omega
      have hd : (bitsToNat (false :: rs) + 2 ^ (false :: rs).length * suf) / 2 = bitsToNat rs + 2 ^ rs.length * suf := by
        simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_assoc]; omega
      unfold fastStep; dsimp only; rw [hm, hd]
      exact hstep_branch (fastRow q).1 _ h rfl
    | true =>
      dsimp only at h
      have hm : (bitsToNat (true :: rs) + 2 ^ (true :: rs).length * suf) % 2 = 1 := by
        simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_assoc]; omega
      have hd : (bitsToNat (true :: rs) + 2 ^ (true :: rs).length * suf) / 2 = bitsToNat rs + 2 ^ rs.length * suf := by
        simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_assoc]; omega
      unfold fastStep; dsimp only; rw [hm, hd]
      exact hstep_branch (fastRow q).2 _ h rfl

private theorem runBits_sound (stop : Nat → Bool) :
    ∀ fuel q l r q' l' r',
      runBits stop fuel q l r = some (q', l', r') →
      stop q' = true ∧
      ∀ suf, SafeReach (q, bitsToNat l, bitsToNat r + 2 ^ r.length * suf)
                       (q', bitsToNat l', bitsToNat r' + 2 ^ r'.length * suf)
  | fuel, q, l, r, q', l', r', h => by
    unfold runBits at h
    cases hs : stop q with
    | true =>
      rw [hs] at h; injection h with h1
      have : q = q' ∧ l = l' ∧ r = r' := by cases h1; exact ⟨rfl, rfl, rfl⟩
      rcases this with ⟨rfl, rfl, rfl⟩
      exact ⟨hs, fun _ => SafeReach.refl _⟩
    | false =>
      rw [hs] at h
      cases fuel with
      | zero => contradiction
      | succ fuel' =>
        cases hq : Nat.ble 207 q with
        | true => rw [hq] at h; contradiction
        | false =>
          rw [hq] at h
          cases hst : stepBits q l r with
          | none => rw [hst] at h; contradiction
          | some res =>
            rcases res with ⟨q1, l1, r1⟩
            rw [hst] at h
            have hq_lt : q < 207 := by
              apply Nat.lt_of_not_ge; intro hge
              have := Nat.ble_eq.mpr hge; rw [hq] at this; contradiction
            obtain ⟨hstop', hreach⟩ := runBits_sound stop fuel' q1 l1 r1 q' l' r' h
            refine ⟨hstop', fun suf => ?_⟩
            exact (SafeReachPos.step_fast hq_lt (stepBits_sound q l r q1 l1 r1 suf hst)).of_pos.trans (hreach suf)

private theorem runBits_sound_pos (stop : Nat → Bool)
    (fuel q : Nat) (l r : List Bool) (q' : Nat) (l' r' : List Bool)
    (hstop : stop q = false)
    (h : runBits stop fuel q l r = some (q', l', r')) :
    stop q' = true ∧
    ∀ suf, SafeReachPos (q, bitsToNat l, bitsToNat r + 2 ^ r.length * suf)
                        (q', bitsToNat l', bitsToNat r' + 2 ^ r'.length * suf) := by
  unfold runBits at h; rw [hstop] at h
  cases fuel with
  | zero => contradiction
  | succ fuel' =>
    cases hq : Nat.ble 207 q with
    | true => rw [hq] at h; contradiction
    | false =>
      rw [hq] at h
      cases hst : stepBits q l r with
      | none => rw [hst] at h; contradiction
      | some res =>
        rcases res with ⟨q1, l1, r1⟩
        rw [hst] at h
        have hq_lt : q < 207 := by
          apply Nat.lt_of_not_ge; intro hge
          have := Nat.ble_eq.mpr hge; rw [hq] at this; contradiction
        obtain ⟨hstop', hreach⟩ := runBits_sound stop fuel' q1 l1 r1 q' l' r' h
        refine ⟨hstop', fun suf => ?_⟩
        exact (SafeReachPos.step_fast hq_lt (stepBits_sound q l r q1 l1 r1 suf hst)).trans (hreach suf)

/-! #### 3.2 Register Tape Encoding & Basic Scan Loops -/

private def tailBits : Nat → Nat
  | 0 => 0
  | t + 1 => 6 + 8 * tailBits t

private def regBlock (v suf : Nat) : Nat :=
  2 * (ones (v + 1) + 2 ^ (v + 1) * suf)

private def markedRegBlock (v suf : Nat) : Nat :=
  4 * (ones v + 2 ^ v * suf)

private def regsSuffix : List Nat → Nat → Nat
  | [], t => tailBits t
  | v :: vs, t => regBlock v (regsSuffix vs t)

private def regsSuffixPre : List Nat → Nat → Nat
  | [], suf => suf
  | v :: vs, suf => regBlock v (regsSuffixPre vs suf)

private theorem regsSuffix_append : ∀ pre post t,
    regsSuffix (pre ++ post) t = regsSuffixPre pre (regsSuffix post t)
  | [], _, _ => rfl
  | _ :: pre, post, t => by simp [regsSuffix, regsSuffixPre, regsSuffix_append pre post t]

private def regsBits (rs : List Nat) (t : Nat) : Nat :=
  1 + 2 * regsSuffix rs t

private def markedRegsBits (pre : List Nat) (v : Nat) (post : List Nat) (t : Nat) : Nat :=
  1 + 2 * regsSuffixPre pre (markedRegBlock v (regsSuffix post t))

private def shiftLeftRegs : List Nat → Nat → Nat
  | [], left => left
  | v :: vs, left => shiftLeftRegs vs (ones (v + 1) + 2 ^ (v + 1) * (2 * left))

private def frameState (pref m : Nat) (rs : List Nat) (t : Nat) : Nat × Nat × Nat :=
  (74, 1, pref + 2 ^ (42 + m) * regsBits rs t)

private theorem startup_is_frame :
    (74, 1, 152919395647067130113387679226998336721518593) =
    frameState 1 6 [0, 0, 0, 0, 0, 0, 2, 0, 0] 26 := rfl

-- Four clean single-step lemmas returning SafeReach directly (no `match d` unfolding!)
private theorem step0R {q next : Nat} {w : Bool} (hq : q < 207)
    (hrow : (fastRow q).1 = some (w, true, next)) (left suf : Nat) :
    SafeReach (q, left, 2 * suf)
      (next, (match (generalizing := false) w with | true => 1 | false => 0) + 2 * left, suf) := by
  apply SafeReachPos.of_pos; apply SafeReachPos.step_fast hq
  unfold fastStep; dsimp only
  have hm : (2 * suf) % 2 = 0 := by omega
  have hd : (2 * suf) / 2 = suf := by omega
  rw [hm, hd]; simp only [hrow]

private theorem step0L {q next : Nat} {w : Bool} (hq : q < 207)
    (hrow : (fastRow q).1 = some (w, false, next)) (left suf : Nat) :
    SafeReach (q, left, 2 * suf)
      (next, left / 2, left % 2 + 2 * ((match (generalizing := false) w with | true => 1 | false => 0) + 2 * suf)) := by
  apply SafeReachPos.of_pos; apply SafeReachPos.step_fast hq
  unfold fastStep; dsimp only
  have hm : (2 * suf) % 2 = 0 := by omega
  have hd : (2 * suf) / 2 = suf := by omega
  rw [hm, hd]; simp only [hrow]

private theorem step1R {q next : Nat} {w : Bool} (hq : q < 207)
    (hrow : (fastRow q).2 = some (w, true, next)) (left suf : Nat) :
    SafeReach (q, left, 1 + 2 * suf)
      (next, (match (generalizing := false) w with | true => 1 | false => 0) + 2 * left, suf) := by
  apply SafeReachPos.of_pos; apply SafeReachPos.step_fast hq
  unfold fastStep; dsimp only
  have hm : (1 + 2 * suf) % 2 = 1 := by omega
  have hd : (1 + 2 * suf) / 2 = suf := by omega
  rw [hm, hd]; simp only [hrow]

private theorem step1L {q next : Nat} {w : Bool} (hq : q < 207)
    (hrow : (fastRow q).2 = some (w, false, next)) (left suf : Nat) :
    SafeReach (q, left, 1 + 2 * suf)
      (next, left / 2, left % 2 + 2 * ((match (generalizing := false) w with | true => 1 | false => 0) + 2 * suf)) := by
  apply SafeReachPos.of_pos; apply SafeReachPos.step_fast hq
  unfold fastStep; dsimp only
  have hm : (1 + 2 * suf) % 2 = 1 := by omega
  have hd : (1 + 2 * suf) / 2 = suf := by omega
  rw [hm, hd]; simp only [hrow]

-- Scan RIGHT over 1^n keeping 1s
private theorem scan_right_ones_keep (q : Nat) (hq : q < 207)
    (hrow : (fastRow q).2 = some (true, true, q)) :
    ∀ n left suf, SafeReach (q, left, ones n + 2 ^ n * suf) (q, ones n + 2 ^ n * left, suf)
  | 0, left, suf => by simp [ones]; exact SafeReach.refl _
  | n + 1, left, suf => by
    rw [ones_succ_mul]
    have hs := step1R hq hrow left (ones n + 2 ^ n * suf)
    have ih := scan_right_ones_keep q hq hrow n (1 + 2 * left) suf
    rw [ones_shift_left] at ih
    exact hs.trans ih

-- Scan RIGHT over 1^n erasing to 0s
private theorem scan_right_ones_erase (q : Nat) (hq : q < 207)
    (hrow : (fastRow q).2 = some (false, true, q)) :
    ∀ n left suf, SafeReach (q, left, ones n + 2 ^ n * suf) (q, 2 ^ n * left, suf)
  | 0, left, suf => by simp [ones]; exact SafeReach.refl _
  | n + 1, left, suf => by
    rw [ones_succ_mul]
    have hs := step1R hq hrow left (ones n + 2 ^ n * suf)
    rw [Nat.zero_add] at hs
    have ih := scan_right_ones_erase q hq hrow n (2 * left) suf
    have heq : 2 ^ n * (2 * left) = 2 ^ (n + 1) * left := by
      rw [pow2_succ_mul, Nat.mul_left_comm]
    rw [heq] at ih
    exact hs.trans ih

-- Scan RIGHT over 0^n filling with 1s
private theorem scan_right_zeros_fill (q : Nat) (hq : q < 207)
    (hrow : (fastRow q).1 = some (true, true, q)) :
    ∀ n left suf, SafeReach (q, left, 2 ^ n * suf) (q, ones n + 2 ^ n * left, suf)
  | 0, left, suf => by simp [ones]; exact SafeReach.refl _
  | n + 1, left, suf => by
    rw [pow2_succ_mul]
    have hs := step0R hq hrow left (2 ^ n * suf)
    have ih := scan_right_zeros_fill q hq hrow n (1 + 2 * left) suf
    rw [ones_shift_left] at ih
    exact hs.trans ih

-- Scan RIGHT over 0^n keeping 0s
private theorem scan_right_zeros_keep (q : Nat) (hq : q < 207)
    (hrow : (fastRow q).1 = some (false, true, q)) :
    ∀ n left suf, SafeReach (q, left, 2 ^ n * suf) (q, 2 ^ n * left, suf)
  | 0, left, suf => by simp; exact SafeReach.refl _
  | n + 1, left, suf => by
    rw [pow2_succ_mul]
    have hs := step0R hq hrow left (2 ^ n * suf)
    rw [Nat.zero_add] at hs
    have ih := scan_right_zeros_keep q hq hrow n (2 * left) suf
    have heq : 2 ^ n * (2 * left) = 2 ^ (n + 1) * left := by
      rw [pow2_succ_mul, Nat.mul_left_comm]
    rw [heq] at ih
    exact hs.trans ih

-- Scan LEFT over 1^n in left keeping 1s
private theorem scan_left_ones (q : Nat) (hq : q < 207)
    (hrow : (fastRow q).2 = some (true, false, q)) :
    ∀ n left suf,
      SafeReach (q, ones n + 2 ^ n * left, 1 + 2 * suf)
                (q, left, ones (n + 1) + 2 ^ (n + 1) * suf)
  | 0, left, suf => by simp [ones]; exact SafeReach.refl _
  | n + 1, left, suf => by
    have hs := step1L hq hrow (ones (n + 1) + 2 ^ (n + 1) * left) suf
    rw [mod2_ones_succ, div2_ones_succ] at hs
    have ih := scan_left_ones q hq hrow n left (1 + 2 * suf)
    rw [ones_shift_left] at ih
    exact hs.trans ih

-- Scan LEFT over 0^n in left keeping 0s
private theorem scan_left_zeros (q : Nat) (hq : q < 207)
    (hrow : (fastRow q).1 = some (false, false, q)) :
    ∀ n left suf,
      SafeReach (q, 2 ^ n * left, 2 * suf)
                (q, left, 2 ^ (n + 1) * suf)
  | 0, left, suf => by simp; exact SafeReach.refl _
  | n + 1, left, suf => by
    have hs := step0L hq hrow (2 ^ (n + 1) * left) suf
    rw [mod2_pow_succ, div2_pow_succ, Nat.zero_add, Nat.zero_add] at hs
    have ih := scan_left_zeros q hq hrow n left (2 * suf)
    have heq : 2 ^ (n + 1) * (2 * suf) = 2 ^ (n + 2) * suf := by
      rw [pow2_succ_mul (n + 1), pow2_succ_mul n, pow2_succ_mul n, Nat.mul_left_comm (2 ^ n) 2 suf]
    rw [heq] at ih
    exact hs.trans ih

/-! #### 3.3 The 7 Gadget Lemmas -/

-- Gadget 0: q=7 on 0^n ++ (1 + 2*(2*suf)) -> q=2 at left/2
private theorem gadget_7_zero_reset (n left suf : Nat) :
    SafeReach (7, left, 2 ^ n * (1 + 2 * (2 * suf)))
              (2, left / 2, left % 2 + 2 * (2 ^ n * (1 + 2 * (2 * suf)))) := by
  have h1 := scan_right_zeros_keep 7 (by omega) rfl n left (1 + 2 * (2 * suf))
  have h2 := step1R (q := 7) (by omega) rfl (2 ^ n * left) (2 * suf)
  rw [Nat.zero_add] at h2
  have h3 := step0L (q := 10) (by omega) rfl (2 * (2 ^ n * left)) suf
  have hm1 : (2 * (2 ^ n * left)) % 2 = 0 := by omega
  have hd1 : (2 * (2 ^ n * left)) / 2 = 2 ^ n * left := by omega
  rw [hm1, hd1, Nat.zero_add, Nat.zero_add] at h3
  have h4 := step0L (q := 15) (by omega) rfl (2 ^ n * left) (2 * suf)
  cases n with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul] at h1 h2 h3 h4 ⊢
    exact ((h1.trans h2).trans h3).trans h4
  | succ k =>
    rw [mod2_pow_succ, div2_pow_succ, Nat.zero_add] at h4
    have h5 := scan_left_zeros 2 (by omega) rfl k left (1 + 2 * (2 * suf))
    have h6 := step0L (q := 2) (by omega) rfl left (2 ^ k * (1 + 2 * (2 * suf)))
    rw [Nat.zero_add, ← pow2_succ_mul] at h6
    exact ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6

-- Gadget 1: q=34 on 0^n ++ (1 + 2*suf) (n >= 1) fills 0^n -> 1^n and returns to q=3 at left/2
private theorem gadget_fill_and_back (n left suf : Nat) (hn : 1 ≤ n) :
    SafeReach (34, left, 2 ^ n * (1 + 2 * suf))
              (3, left / 2, left % 2 + 2 * (ones n + 2 ^ n * (1 + 2 * suf))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 := scan_right_zeros_fill 34 (by omega) rfl (k + 1) left (1 + 2 * suf)
  have h2 := step1L (q := 34) (by omega) rfl (ones (k + 1) + 2 ^ (k + 1) * left) suf
  rw [mod2_ones_succ, div2_ones_succ] at h2
  have h3 := step1L (q := 2) (by omega) rfl (ones k + 2 ^ k * left) (1 + 2 * suf)
  cases k with
  | zero =>
    simp only [ones_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at h1 h2 h3 ⊢
    have heq : ones 1 + 2 ^ 1 * (1 + 2 * suf) = 1 + 2 * (1 + 2 * suf) := by simp [ones]
    rw [heq]; exact (h1.trans h2).trans h3
  | succ k' =>
    rw [mod2_ones_succ, div2_ones_succ] at h3
    have h4 := scan_left_ones 3 (by omega) rfl k' left (1 + 2 * (1 + 2 * suf))
    rw [ones_shift_left] at h4
    have h5 := step1L (q := 3) (by omega) rfl left (ones (k' + 1) + 2 ^ (k' + 1) * (1 + 2 * suf))
    rw [← ones_succ_mul] at h5
    exact (((h1.trans h2).trans h3).trans h4).trans h5

-- Helper: tailBits t = regsSuffixPre (List.replicate t 1) 0
private theorem tailBits_eq_pre : ∀ t, tailBits t = regsSuffixPre (List.replicate t 1) 0
  | 0 => rfl
  | t + 1 => by
    simp only [tailBits, List.replicate_succ, regsSuffixPre, regBlock, ones]
    rw [tailBits_eq_pre t]; omega

private theorem regsSuffixPre_append : ∀ a b suf,
    regsSuffixPre (a ++ b) suf = regsSuffixPre a (regsSuffixPre b suf)
  | [], _, _ => rfl
  | _ :: a, b, suf => by simp [regsSuffixPre, regsSuffixPre_append a b suf]

private theorem regsSuffix_eq_pre (rs : List Nat) (t : Nat) :
    regsSuffix rs t = regsSuffixPre (rs ++ List.replicate t 1) 0 := by
  rw [regsSuffixPre_append, ← tailBits_eq_pre]
  induction rs with
  | nil => rfl
  | cons v vs ih => simp [regsSuffix, regsSuffixPre, ih]

private theorem shiftLeftRegs_append : ∀ a b left,
    shiftLeftRegs (a ++ b) left = shiftLeftRegs b (shiftLeftRegs a left)
  | [], _, _ => rfl
  | _ :: a, b, left => by simp [shiftLeftRegs, shiftLeftRegs_append a b]

private theorem regsSuffixPre_even : ∀ l x, ∃ y, regsSuffixPre l (2 * x) = 2 * y
  | [], x => ⟨x, rfl⟩
  | v :: vs, x => ⟨ones (v + 1) + 2 ^ (v + 1) * regsSuffixPre vs (2 * x), rfl⟩

-- Helper: scan LEFT in state 3 across a single block `0 1^(v+1)` starting on `2 * suf` -> `regBlock v (2 * suf)`!
private theorem scan_left_3_block (v left suf : Nat) :
    SafeReach (3, ones (v + 1) + 2 ^ (v + 1) * (2 * left), 2 * suf)
              (3, left, regBlock v (2 * suf)) := by
  have h1 := step0L (q := 3) (by omega) rfl (ones (v + 1) + 2 ^ (v + 1) * (2 * left)) suf
  rw [mod2_ones_succ, div2_ones_succ, Nat.zero_add] at h1
  have h2 := step1L (q := 4) (by omega) rfl (ones v + 2 ^ v * (2 * left)) (2 * suf)
  cases v with
  | zero =>
    simp only [ones_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at h1 h2
    have hm : (2 * left) % 2 = 0 := by omega
    have hd : (2 * left) / 2 = left := by omega
    rw [hm, hd, Nat.zero_add] at h2
    have heq : 2 * (1 + 2 * (2 * suf)) = regBlock 0 (2 * suf) := by simp [regBlock, ones]
    rw [heq] at h2
    exact h1.trans h2
  | succ v' =>
    rw [mod2_ones_succ, div2_ones_succ] at h2
    have h3 := scan_left_ones 3 (by omega) rfl v' (2 * left) (1 + 2 * (2 * suf))
    rw [ones_shift_left] at h3
    have h4 := step1L (q := 3) (by omega) rfl (2 * left) (ones (v' + 1) + 2 ^ (v' + 1) * (2 * suf))
    have hm : (2 * left) % 2 = 0 := by omega
    have hd : (2 * left) / 2 = left := by omega
    rw [hm, hd, Nat.zero_add, ← ones_succ_mul] at h4
    exact ((h1.trans h2).trans h3).trans h4

private theorem scan_left_3_pre : ∀ pre left suf,
    SafeReach (3, shiftLeftRegs pre left, 2 * suf)
              (3, left, regsSuffixPre pre (2 * suf))
  | [], _, _ => SafeReach.refl _
  | v :: vs, left, suf => by
    simp only [shiftLeftRegs, regsSuffixPre]
    have h1 := scan_left_3_pre vs (ones (v + 1) + 2 ^ (v + 1) * (2 * left)) suf
    obtain ⟨y, hy⟩ := regsSuffixPre_even vs suf
    have h2 := scan_left_3_block v left y
    rw [← hy] at h2
    exact h1.trans h2

-- Helper: scan LEFT in state 3 across `1^(n+1)` (sentinel 1 + 1^n) starting on `2 * suf`
private theorem scan_left_3_sent_ones (n left suf : Nat) :
    SafeReach (3, ones (n + 1) + 2 ^ (n + 1) * left, 2 * suf)
              (3, left / 2, left % 2 + 2 * (ones n + 2 ^ n * (1 + 2 * (2 * suf)))) := by
  have h1 := step0L (q := 3) (by omega) rfl (ones (n + 1) + 2 ^ (n + 1) * left) suf
  rw [mod2_ones_succ, div2_ones_succ, Nat.zero_add] at h1
  have h2 := step1L (q := 4) (by omega) rfl (ones n + 2 ^ n * left) (2 * suf)
  cases n with
  | zero =>
    simp only [ones_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at h1 h2 ⊢
    exact h1.trans h2
  | succ k =>
    rw [mod2_ones_succ, div2_ones_succ] at h2
    have h3 := scan_left_ones 3 (by omega) rfl k left (1 + 2 * (2 * suf))
    have h4 := step1L (q := 3) (by omega) rfl left (ones (k + 1) + 2 ^ (k + 1) * (2 * suf))
    rw [← ones_succ_mul, ← ones_shift_left] at h4
    exact ((h1.trans h2).trans h3).trans h4

-- Gadget 2: register skip chain -> mark first 1 of reg k -> reset to q=3
private def regSkipState : Nat → Nat
  | 0 => 48
  | 1 => 35
  | 2 => 24
  | 3 => 46
  | 4 => 31
  | 5 => 32
  | 6 => 21
  | 7 => 51
  | _ => 56

private theorem regSkip_step : ∀ k, k < 9 →
    regSkipState k < 207 ∧
    (fastRow (regSkipState k)).2 = some (true, true, regSkipState k) ∧
    (fastRow (regSkipState k)).1 =
      some (false, true, match k with | 0 => 15 | k' + 1 => regSkipState k')
  | 0, _ => ⟨by decide, rfl, rfl⟩
  | 1, _ => ⟨by decide, rfl, rfl⟩
  | 2, _ => ⟨by decide, rfl, rfl⟩
  | 3, _ => ⟨by decide, rfl, rfl⟩
  | 4, _ => ⟨by decide, rfl, rfl⟩
  | 5, _ => ⟨by decide, rfl, rfl⟩
  | 6, _ => ⟨by decide, rfl, rfl⟩
  | 7, _ => ⟨by decide, rfl, rfl⟩
  | 8, _ => ⟨by decide, rfl, rfl⟩
  | _ + 9, h => by omega

private theorem skip_regs_right : ∀ (k : Nat) (pre : List Nat),
    k < 9 → pre.length = k → ∀ left suf,
      SafeReach (regSkipState k, left, regsSuffixPre pre (2 * suf))
                (15, 2 * shiftLeftRegs pre left, suf)
  | 0, [], _, _, left, suf => by
    simp only [regsSuffixPre, shiftLeftRegs]
    have hs := step0R (q := 48) (by omega) rfl left suf
    rw [Nat.zero_add] at hs; exact hs
  | 0, _ :: _, _, hlen, _, _ => by simp at hlen
  | k + 1, [], _, hlen, _, _ => by simp at hlen
  | k + 1, v :: vs, hk, hlen, left, suf => by
    have ⟨hlt, _, h0row⟩ := regSkip_step (k + 1) hk
    simp only [regsSuffixPre, regBlock, shiftLeftRegs]
    have h0 := step0R hlt h0row left (ones (v + 1) + 2 ^ (v + 1) * regsSuffixPre vs (2 * suf))
    rw [Nat.zero_add] at h0
    have ⟨hlt', h1row', _⟩ := regSkip_step k (by omega)
    have h1 := scan_right_ones_keep (regSkipState k) hlt' h1row' (v + 1) (2 * left)
      (regsSuffixPre vs (2 * suf))
    have ih := skip_regs_right k vs (by omega) (by simp at hlen; omega)
      (ones (v + 1) + 2 ^ (v + 1) * (2 * left)) suf
    exact (h0.trans h1).trans ih

private theorem gadget_mark_reg (k n left : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (t : Nat)
    (hk : k < 9) (hlen : pre.length = k) :
    SafeReach (regSkipState k, left, ones n + 2 ^ n * regsBits (pre ++ v :: post) t)
              (3, left / 2, left % 2 + 2 * (ones n + 2 ^ n * markedRegsBits pre v post t)) := by
  have ⟨hlt, h1row, _⟩ := regSkip_step k hk
  have hrw : ones n + 2 ^ n * regsBits (pre ++ v :: post) t =
      ones (n + 1) + 2 ^ (n + 1) * regsSuffixPre pre (regBlock v (regsSuffix post t)) := by
    unfold regsBits; rw [regsSuffix_append, ones_shift_left]; rfl
  rw [hrw]
  have h1 := scan_right_ones_keep (regSkipState k) hlt h1row (n + 1) left
    (regsSuffixPre pre (regBlock v (regsSuffix post t)))
  have h2 := skip_regs_right k pre hk hlen (ones (n + 1) + 2 ^ (n + 1) * left)
    (ones (v + 1) + 2 ^ (v + 1) * regsSuffix post t)
  have h3 : SafeReach (15, 2 * shiftLeftRegs pre (ones (n + 1) + 2 ^ (n + 1) * left),
      ones (v + 1) + 2 ^ (v + 1) * regsSuffix post t)
      (2, shiftLeftRegs pre (ones (n + 1) + 2 ^ (n + 1) * left),
      2 * (2 * (ones v + 2 ^ v * regsSuffix post t))) := by
    rw [ones_succ_mul v]
    have hs := step1L (q := 15) (by omega) rfl
      (2 * shiftLeftRegs pre (ones (n + 1) + 2 ^ (n + 1) * left))
      (ones v + 2 ^ v * regsSuffix post t)
    have hm : (2 * shiftLeftRegs pre (ones (n + 1) + 2 ^ (n + 1) * left)) % 2 = 0 := by omega
    have hd : (2 * shiftLeftRegs pre (ones (n + 1) + 2 ^ (n + 1) * left)) / 2 =
        shiftLeftRegs pre (ones (n + 1) + 2 ^ (n + 1) * left) := by omega
    rw [hm, hd, Nat.zero_add, Nat.zero_add] at hs
    exact hs
  have hback : SafeReach (2, shiftLeftRegs pre (ones (n + 1) + 2 ^ (n + 1) * left),
      2 * (2 * (ones v + 2 ^ v * regsSuffix post t)))
      (3, left / 2, left % 2 + 2 * (ones n + 2 ^ n * markedRegsBits pre v post t)) := by
    cases hrev : pre.reverse with
    | nil =>
      have hpre : pre = [] := List.reverse_eq_nil_iff.mp hrev
      subst hpre
      simp only [shiftLeftRegs, markedRegsBits, regsSuffixPre, markedRegBlock]
      have ha := step0L (q := 2) (by omega) rfl (ones (n + 1) + 2 ^ (n + 1) * left)
        (2 * (ones v + 2 ^ v * regsSuffix post t))
      rw [mod2_ones_succ, div2_ones_succ, Nat.zero_add] at ha
      have h4eq : 2 * (2 * (ones v + 2 ^ v * regsSuffix post t)) =
          4 * (ones v + 2 ^ v * regsSuffix post t) := by omega
      rw [h4eq] at ha ⊢
      have hb := step1L (q := 2) (by omega) rfl (ones n + 2 ^ n * left)
        (4 * (ones v + 2 ^ v * regsSuffix post t))
      cases n with
      | zero =>
        simp only [ones_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at ha hb ⊢
        exact ha.trans hb
      | succ k =>
        rw [mod2_ones_succ, div2_ones_succ] at hb
        have hc := scan_left_ones 3 (by omega) rfl k left (1 + 2 * (4 * (ones v + 2 ^ v * regsSuffix post t)))
        have hd := step1L (q := 3) (by omega) rfl left
          (ones (k + 1) + 2 ^ (k + 1) * (4 * (ones v + 2 ^ v * regsSuffix post t)))
        rw [← ones_succ_mul, ← ones_shift_left] at hd
        exact ((ha.trans hb).trans hc).trans hd
    | cons u us =>
      have hpre : pre = us.reverse ++ [u] := by
        have := congrArg List.reverse hrev; simpa using this
      rw [hpre, shiftLeftRegs_append]
      simp only [shiftLeftRegs, markedRegsBits, regsSuffixPre_append, regsSuffixPre]
      let L0 := shiftLeftRegs us.reverse (ones (n + 1) + 2 ^ (n + 1) * left)
      let mblk := markedRegBlock v (regsSuffix post t)
      have hmblk : 2 * (2 * (ones v + 2 ^ v * regsSuffix post t)) = mblk := by
        simp [mblk, markedRegBlock]; omega
      have h2u : SafeReach (2, ones (u + 1) + 2 ^ (u + 1) * (2 * L0), 2 * (2 * (ones v + 2 ^ v * regsSuffix post t)))
          (3, L0, regBlock u mblk) := by
        have ha := step0L (q := 2) (by omega) rfl (ones (u + 1) + 2 ^ (u + 1) * (2 * L0))
          (2 * (ones v + 2 ^ v * regsSuffix post t))
        rw [mod2_ones_succ, div2_ones_succ, Nat.zero_add, hmblk] at ha
        rw [hmblk]
        have hb := step1L (q := 2) (by omega) rfl (ones u + 2 ^ u * (2 * L0)) mblk
        cases u with
        | zero =>
          simp only [ones_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at ha hb
          have hm : (2 * L0) % 2 = 0 := by omega
          have hd : (2 * L0) / 2 = L0 := by omega
          rw [hm, hd, Nat.zero_add] at hb
          have heq : 2 * (1 + 2 * mblk) = regBlock 0 mblk := by simp [regBlock, ones]
          rw [heq] at hb; exact ha.trans hb
        | succ u' =>
          rw [mod2_ones_succ, div2_ones_succ] at hb
          have hc := scan_left_ones 3 (by omega) rfl u' (2 * L0) (1 + 2 * mblk)
          rw [ones_shift_left] at hc
          have hd := step1L (q := 3) (by omega) rfl (2 * L0) (ones (u' + 1) + 2 ^ (u' + 1) * mblk)
          have hm : (2 * L0) % 2 = 0 := by omega
          have hd2 : (2 * L0) / 2 = L0 := by omega
          rw [hm, hd2, Nat.zero_add, ← ones_succ_mul] at hd
          exact ((ha.trans hb).trans hc).trans hd
      have h3pre := scan_left_3_pre us.reverse (ones (n + 1) + 2 ^ (n + 1) * left)
        (ones (u + 1) + 2 ^ (u + 1) * mblk)
      obtain ⟨y, hy⟩ := regsSuffixPre_even us.reverse (ones (u + 1) + 2 ^ (u + 1) * mblk)
      have h3sent := scan_left_3_sent_ones n left y
      rw [← hy] at h3sent
      exact (h2u.trans h3pre).trans h3sent
  exact ((h1.trans h2).trans h3).trans hback

-- Helper: scan RIGHT in state 60/0 across `regsSuffixPre`
private theorem scan_right_60_pre : ∀ pre left suf,
    SafeReach (60, left, regsSuffixPre pre suf)
              (60, shiftLeftRegs pre left, suf)
  | [], _, _ => SafeReach.refl _
  | v :: vs, left, suf => by
    simp only [regsSuffixPre, regBlock, shiftLeftRegs]
    have h0 := step0R (q := 60) (by omega) rfl left (ones (v + 1) + 2 ^ (v + 1) * regsSuffixPre vs suf)
    rw [Nat.zero_add] at h0
    have h1 := step1R (q := 0) (by omega) rfl (2 * left) (ones v + 2 ^ v * regsSuffixPre vs suf)
    rw [← ones_succ_mul v] at h1
    have h2 := scan_right_ones_keep 60 (by omega) rfl v (1 + 2 * (2 * left)) (regsSuffixPre vs suf)
    rw [ones_shift_left] at h2
    exact ((h0.trans h1).trans h2).trans (scan_right_60_pre vs _ suf)

-- Helper: scan LEFT in state 50/38 across a single block `0 1^(v+1)` starting on `2 * suf` -> `regBlock v (2 * suf)`
private theorem scan_left_50_block (v left suf : Nat) :
    SafeReach (50, ones (v + 1) + 2 ^ (v + 1) * (2 * left), 2 * suf)
              (50, left, regBlock v (2 * suf)) := by
  have h1 := step0L (q := 50) (by omega) rfl (ones (v + 1) + 2 ^ (v + 1) * (2 * left)) suf
  rw [mod2_ones_succ, div2_ones_succ, Nat.zero_add] at h1
  have h2 := step1L (q := 38) (by omega) rfl (ones v + 2 ^ v * (2 * left)) (2 * suf)
  cases v with
  | zero =>
    simp only [ones_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at h1 h2
    have hm : (2 * left) % 2 = 0 := by omega
    have hd : (2 * left) / 2 = left := by omega
    rw [hm, hd, Nat.zero_add] at h2
    have heq : 2 * (1 + 2 * (2 * suf)) = regBlock 0 (2 * suf) := by simp [regBlock, ones]
    rw [heq] at h2; exact h1.trans h2
  | succ v' =>
    rw [mod2_ones_succ, div2_ones_succ] at h2
    have h3 := scan_left_ones 50 (by omega) rfl v' (2 * left) (1 + 2 * (2 * suf))
    rw [ones_shift_left] at h3
    have h4 := step1L (q := 50) (by omega) rfl (2 * left) (ones (v' + 1) + 2 ^ (v' + 1) * (2 * suf))
    have hm : (2 * left) % 2 = 0 := by omega
    have hd : (2 * left) / 2 = left := by omega
    rw [hm, hd, Nat.zero_add, ← ones_succ_mul] at h4
    exact ((h1.trans h2).trans h3).trans h4

private theorem scan_left_50_pre : ∀ pre left suf,
    SafeReach (50, shiftLeftRegs pre left, 2 * suf)
              (50, left, regsSuffixPre pre (2 * suf))
  | [], _, _ => SafeReach.refl _
  | v :: vs, left, suf => by
    simp only [shiftLeftRegs, regsSuffixPre]
    have h1 := scan_left_50_pre vs (ones (v + 1) + 2 ^ (v + 1) * (2 * left)) suf
    obtain ⟨y, hy⟩ := regsSuffixPre_even vs suf
    have h2 := scan_left_50_block v left y
    rw [← hy] at h2
    exact h1.trans h2

-- Helper: scan LEFT in state 50 across `1^(n+1)` + `00` to `(38, l, 4 * (ones n + 2^n * (1 + 2*(2*suf))))`
private theorem scan_left_50_sent_ones (n l suf : Nat) :
    SafeReach (50, ones (n + 1) + 2 ^ (n + 1) * (4 * l), 2 * suf)
              (38, l, 4 * (ones n + 2 ^ n * (1 + 2 * (2 * suf)))) := by
  have h1 := step0L (q := 50) (by omega) rfl (ones (n + 1) + 2 ^ (n + 1) * (4 * l)) suf
  rw [mod2_ones_succ, div2_ones_succ, Nat.zero_add] at h1
  have h2 := step1L (q := 38) (by omega) rfl (ones n + 2 ^ n * (4 * l)) (2 * suf)
  cases n with
  | zero =>
    simp only [ones_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at h1 h2 ⊢
    have hm1 : (4 * l) % 2 = 0 := by omega
    have hd1 : (4 * l) / 2 = 2 * l := by omega
    rw [hm1, hd1, Nat.zero_add] at h2
    have h5 := step0L (q := 50) (by omega) rfl (2 * l) (1 + 2 * (2 * suf))
    have hm2 : (2 * l) % 2 = 0 := by omega
    have hd2 : (2 * l) / 2 = l := by omega
    rw [hm2, hd2, Nat.zero_add, Nat.zero_add] at h5
    have h4eq : 2 * (2 * (1 + 2 * (2 * suf))) = 4 * (1 + 2 * (2 * suf)) := by omega
    rw [h4eq] at h5
    exact (h1.trans h2).trans h5
  | succ k =>
    rw [mod2_ones_succ, div2_ones_succ] at h2
    have h3 := scan_left_ones 50 (by omega) rfl k (4 * l) (1 + 2 * (2 * suf))
    rw [ones_shift_left, ones_succ_mul] at h3
    have h4 := step1L (q := 50) (by omega) rfl (4 * l) (ones (k + 1) + 2 ^ (k + 1) * (2 * suf))
    have hm1 : (4 * l) % 2 = 0 := by omega
    have hd1 : (4 * l) / 2 = 2 * l := by omega
    rw [hm1, hd1, Nat.zero_add] at h4
    have h5 := step0L (q := 50) (by omega) rfl (2 * l) (1 + 2 * (ones (k + 1) + 2 ^ (k + 1) * (2 * suf)))
    have hm2 : (2 * l) % 2 = 0 := by omega
    have hd2 : (2 * l) / 2 = l := by omega
    rw [hm2, hd2, Nat.zero_add, Nat.zero_add] at h5
    have heq2 : 2 * (2 * (1 + 2 * (ones (k + 1) + 2 ^ (k + 1) * (2 * suf)))) =
        4 * (ones (k + 1) + 2 ^ (k + 1) * (1 + 2 * (2 * suf))) := by
      rw [← ones_succ_mul, ← ones_shift_left]; omega
    rw [heq2] at h5
    exact (((h1.trans h2).trans h3).trans h4).trans h5

-- Helper: 1/81 right-shift across a list of blocks (ending with `1` at `suf`)
private theorem shift_right_1_81 : ∀ blocks a L suf,
    SafeReach (1, ones a + 2 ^ a * L, regsSuffixPre blocks suf)
              (1, (match blocks.reverse with
                   | [] => ones a + 2 ^ a * L
                   | u :: us => ones u + 2 ^ u * (2 * shiftLeftRegs us.reverse (ones (a + 1) + 2 ^ (a + 1) * L))),
               suf)
  | [], a, L, suf => SafeReach.refl _
  | u :: us, a, L, suf => by
    simp only [regsSuffixPre, regBlock]
    have h0 := step0R (q := 1) (by omega) rfl (ones a + 2 ^ a * L)
      (ones (u + 1) + 2 ^ (u + 1) * regsSuffixPre us suf)
    rw [← ones_succ_mul a] at h0
    have h1 := step1R (q := 81) (by omega) rfl (ones (a + 1) + 2 ^ (a + 1) * L)
      (ones u + 2 ^ u * regsSuffixPre us suf)
    rw [Nat.zero_add, ← ones_succ_mul u] at h1
    have h2 := scan_right_ones_keep 1 (by omega) rfl u
      (2 * (ones (a + 1) + 2 ^ (a + 1) * L)) (regsSuffixPre us suf)
    have ih := shift_right_1_81 us u (2 * (ones (a + 1) + 2 ^ (a + 1) * L)) suf
    have hstep := ((h0.trans h1).trans h2).trans ih
    cases hrev : us.reverse with
    | nil =>
      have hus : us = [] := List.reverse_eq_nil_iff.mp hrev
      subst hus; simpa [shiftLeftRegs] using hstep
    | cons w ws =>
      rw [hrev] at hstep
      have hrev2 : (u :: us).reverse = w :: (ws ++ [u]) := by simp [hrev]
      rw [hrev2]; dsimp only
      have hrev3 : (ws ++ [u]).reverse = u :: ws.reverse := by simp
      rw [hrev3]; simpa [shiftLeftRegs] using hstep

-- Helper: finish 1/81 at 0 -> 61 -> 123 -> 38 -> 50 on `tailBits 1`!
private theorem shift_right_finish_zero (a L : Nat) :
    SafeReach (1, ones a + 2 ^ a * L, 0)
              (50, ones (a + 1) + 2 ^ (a + 1) * L, tailBits 1) := by
  have h0 := step0R (q := 1) (by omega) rfl (ones a + 2 ^ a * L) 0
  rw [← ones_succ_mul] at h0
  have h1 := step0R (q := 81) (by omega) rfl (ones (a + 1) + 2 ^ (a + 1) * L) 0
  rw [Nat.zero_add] at h1
  have h2 := step0R (q := 61) (by omega) rfl (2 * (ones (a + 1) + 2 ^ (a + 1) * L)) 0
  have h3 := step0L (q := 123) (by omega) rfl (1 + 2 * (2 * (ones (a + 1) + 2 ^ (a + 1) * L))) 0
  have hm1 : (1 + 2 * (2 * (ones (a + 1) + 2 ^ (a + 1) * L))) % 2 = 1 := by omega
  have hd1 : (1 + 2 * (2 * (ones (a + 1) + 2 ^ (a + 1) * L))) / 2 =
      2 * (ones (a + 1) + 2 ^ (a + 1) * L) := by omega
  rw [hm1, hd1] at h3
  have h4 := step1L (q := 38) (by omega) rfl (2 * (ones (a + 1) + 2 ^ (a + 1) * L)) 1
  have hm2 : (2 * (ones (a + 1) + 2 ^ (a + 1) * L)) % 2 = 0 := by omega
  have hd2 : (2 * (ones (a + 1) + 2 ^ (a + 1) * L)) / 2 = ones (a + 1) + 2 ^ (a + 1) * L := by omega
  rw [hm2, hd2] at h4
  exact ((((h0.trans h1).trans h2).trans h3).trans h4)

-- Gadget 3: INC register `v` (in `pre ++ v :: post`)
private theorem gadget_inc_reg (n l : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (t : Nat) :
    SafeReach (60, 4 * l, ones n + 2 ^ n * markedRegsBits pre v post t)
              (38, l, 4 * (ones n + 2 ^ n * regsBits (pre ++ (v + 1) :: post) (t + 1))) := by
  have hrw : ones n + 2 ^ n * markedRegsBits pre v post t =
      ones (n + 1) + 2 ^ (n + 1) * regsSuffixPre pre (markedRegBlock v (regsSuffix post t)) := by
    unfold markedRegsBits; rw [ones_shift_left]
  rw [hrw]
  have h1 := scan_right_ones_keep 60 (by omega) rfl (n + 1) (4 * l)
    (regsSuffixPre pre (markedRegBlock v (regsSuffix post t)))
  have h2 := scan_right_60_pre pre (ones (n + 1) + 2 ^ (n + 1) * (4 * l))
    (markedRegBlock v (regsSuffix post t))
  let Lpre := shiftLeftRegs pre (ones (n + 1) + 2 ^ (n + 1) * (4 * l))
  have hmrb : markedRegBlock v (regsSuffix post t) =
      2 * (2 * (ones v + 2 ^ v * regsSuffixPre (post ++ List.replicate t 1) 0)) := by
    unfold markedRegBlock; rw [regsSuffix_eq_pre]; omega
  rw [hmrb] at h2
  have h3 := step0R (q := 60) (by omega) rfl Lpre
    (2 * (ones v + 2 ^ v * regsSuffixPre (post ++ List.replicate t 1) 0))
  rw [Nat.zero_add] at h3
  have h4 := step0R (q := 0) (by omega) rfl (2 * Lpre)
    (ones v + 2 ^ v * regsSuffixPre (post ++ List.replicate t 1) 0)
  have h5 := scan_right_ones_keep 1 (by omega) rfl v (1 + 2 * (2 * Lpre))
    (regsSuffixPre (post ++ List.replicate t 1) 0)
  rw [ones_shift_left] at h5
  let tailList := post ++ List.replicate t 1
  have h6 := shift_right_1_81 tailList (v + 1) (2 * Lpre) 0
  have h7 : SafeReach (1, ones (v + 1) + 2 ^ (v + 1) * (2 * Lpre), regsSuffixPre tailList 0)
      (50, Lpre, regBlock (v + 1) (regsSuffix post (t + 1))) := by
    cases hrev : tailList.reverse with
    | nil =>
      rw [hrev] at h6
      have htl : tailList = [] := List.reverse_eq_nil_iff.mp hrev
      have hpost : post = [] := by cases post <;> simp [tailList] at htl ⊢
      have ht0 : t = 0 := by cases t <;> simp [tailList, hpost] at htl ⊢
      subst hpost; subst ht0
      have hf := shift_right_finish_zero (v + 1) (2 * Lpre)
      have hb := scan_left_50_block (v + 1) Lpre 3
      simpa [tailBits, regsSuffix] using (h6.trans hf).trans hb
    | cons u us =>
      rw [hrev] at h6
      have htl : tailList = us.reverse ++ [u] := by
        have := congrArg List.reverse hrev; simpa using this
      have hf := shift_right_finish_zero u (2 * shiftLeftRegs us.reverse (ones (v + 2) + 2 ^ (v + 2) * (2 * Lpre)))
      have hb1 := scan_left_50_block u (shiftLeftRegs us.reverse (ones (v + 2) + 2 ^ (v + 2) * (2 * Lpre))) 3
      have hb2 := scan_left_50_pre us.reverse (ones (v + 2) + 2 ^ (v + 2) * (2 * Lpre))
        (ones (u + 1) + 2 ^ (u + 1) * tailBits 1)
      obtain ⟨y, hy⟩ := regsSuffixPre_even us.reverse (ones (u + 1) + 2 ^ (u + 1) * tailBits 1)
      have hb3 := scan_left_50_block (v + 1) Lpre y
      rw [← hy] at hb3
      have htail_eq : regsSuffixPre us.reverse (2 * (ones (u + 1) + 2 ^ (u + 1) * tailBits 1)) =
          regsSuffix post (t + 1) := by
        have h1eq : regsSuffixPre us.reverse (2 * (ones (u + 1) + 2 ^ (u + 1) * tailBits 1)) =
            regsSuffixPre (us.reverse ++ [u]) (tailBits 1) := by
          rw [regsSuffixPre_append]; rfl
        rw [h1eq, ← htl, regsSuffix_eq_pre, tailBits_eq_pre]
        simp only [tailList, List.replicate_succ, List.replicate_zero]
        rw [← regsSuffixPre_append]
        congr 1
        have hrep : ∀ k, List.replicate k 1 ++ [1] = 1 :: List.replicate k 1 := by
          intro k; induction k with
          | zero => rfl
          | succ j ih => simp [List.replicate_succ, ih]
        rw [List.append_assoc, hrep t]
      rw [htail_eq] at hb2 hb3
      exact (((h6.trans hf).trans hb1).trans hb2).trans hb3
  have h8 := scan_left_50_pre pre (ones (n + 1) + 2 ^ (n + 1) * (4 * l))
    (ones (v + 2) + 2 ^ (v + 2) * regsSuffix post (t + 1))
  obtain ⟨y2, hy2⟩ := regsSuffixPre_even pre (ones (v + 2) + 2 ^ (v + 2) * regsSuffix post (t + 1))
  have h9 := scan_left_50_sent_ones n l y2
  rw [← hy2] at h9
  have hres : 1 + 2 * regsSuffixPre pre (2 * (ones (v + 2) + 2 ^ (v + 2) * regsSuffix post (t + 1))) =
      regsBits (pre ++ (v + 1) :: post) (t + 1) := by
    unfold regsBits; rw [regsSuffix_append]; rfl
  rw [hres] at h9
  rw [hmrb] at h1 ⊢
  exact ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h7).trans h8).trans h9

-- Helper: common right-shift prefix of DEC (from q=1 on 1^n ++ markedRegsBits pre v post t to q=61)
private theorem dec_shift_to_61 (n l : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (t : Nat) :
    SafeReach (1, 4 * l, ones n + 2 ^ n * markedRegsBits pre v post t)
              (61, 2 * shiftLeftRegs pre (ones (n + 2) + 2 ^ (n + 2) * (4 * l)),
               ones v + 2 ^ v * regsSuffix post t) := by
  have hrw : ones n + 2 ^ n * markedRegsBits pre v post t =
      ones (n + 1) + 2 ^ (n + 1) * regsSuffixPre pre (markedRegBlock v (regsSuffix post t)) := by
    unfold markedRegsBits; rw [ones_shift_left]
  rw [hrw]
  have h1 := scan_right_ones_keep 1 (by omega) rfl (n + 1) (4 * l)
    (regsSuffixPre pre (markedRegBlock v (regsSuffix post t)))
  have h2 := shift_right_1_81 pre (n + 1) (4 * l) (markedRegBlock v (regsSuffix post t))
  have hmrb : markedRegBlock v (regsSuffix post t) =
      2 * (2 * (ones v + 2 ^ v * regsSuffix post t)) := by unfold markedRegBlock; omega
  rw [hmrb] at h1 h2 ⊢
  cases hrev : pre.reverse with
  | nil =>
    rw [hrev] at h2
    have hpre : pre = [] := List.reverse_eq_nil_iff.mp hrev
    subst hpre; simp only [shiftLeftRegs]
    have h3 := step0R (q := 1) (by omega) rfl (ones (n + 1) + 2 ^ (n + 1) * (4 * l))
      (2 * (ones v + 2 ^ v * regsSuffix post t))
    rw [← ones_succ_mul] at h3
    have h4 := step0R (q := 81) (by omega) rfl (ones (n + 2) + 2 ^ (n + 2) * (4 * l))
      (ones v + 2 ^ v * regsSuffix post t)
    rw [Nat.zero_add] at h4
    exact ((h1.trans h2).trans h3).trans h4
  | cons u us =>
    rw [hrev] at h2
    have hpre : pre = us.reverse ++ [u] := by
      have := congrArg List.reverse hrev; simpa using this
    let Lu := shiftLeftRegs us.reverse (ones (n + 2) + 2 ^ (n + 2) * (4 * l))
    have h3 := step0R (q := 1) (by omega) rfl (ones u + 2 ^ u * (2 * Lu))
      (2 * (ones v + 2 ^ v * regsSuffix post t))
    rw [← ones_succ_mul] at h3
    have h4 := step0R (q := 81) (by omega) rfl (ones (u + 1) + 2 ^ (u + 1) * (2 * Lu))
      (ones v + 2 ^ v * regsSuffix post t)
    rw [Nat.zero_add] at h4
    have hsh : shiftLeftRegs pre (ones (n + 2) + 2 ^ (n + 2) * (4 * l)) =
        ones (u + 1) + 2 ^ (u + 1) * (2 * Lu) := by
      rw [hpre, shiftLeftRegs_append]; rfl
    rw [hsh]
    exact ((h1.trans h2).trans h3).trans h4

-- Gadget 4: DEC NZ (v = v' + 1)
private theorem gadget_dec_reg_nz (n l : Nat) (pre : List Nat) (v' : Nat) (post : List Nat) (t : Nat) :
    SafeReach (1, 4 * l, ones n + 2 ^ n * markedRegsBits pre (v' + 1) post t)
              (38, l, 4 * (ones (n + 1) + 2 ^ (n + 1) * regsBits (pre ++ v' :: post) t)) := by
  have h1 := dec_shift_to_61 n l pre (v' + 1) post t
  let Lpre := shiftLeftRegs pre (ones (n + 2) + 2 ^ (n + 2) * (4 * l))
  have h2 := step1L (q := 61) (by omega) rfl (2 * Lpre) (ones v' + 2 ^ v' * regsSuffix post t)
  have hm : (2 * Lpre) % 2 = 0 := by omega
  have hd : (2 * Lpre) / 2 = Lpre := by omega
  rw [hm, hd, Nat.zero_add, ← ones_succ_mul] at h2
  have h3 := scan_left_50_pre pre (ones (n + 2) + 2 ^ (n + 2) * (4 * l))
    (ones (v' + 1) + 2 ^ (v' + 1) * regsSuffix post t)
  obtain ⟨y, hy⟩ := regsSuffixPre_even pre (ones (v' + 1) + 2 ^ (v' + 1) * regsSuffix post t)
  have h4 := scan_left_50_sent_ones (n + 1) l y
  rw [← hy] at h4
  have hres : 1 + 2 * regsSuffixPre pre (2 * (ones (v' + 1) + 2 ^ (v' + 1) * regsSuffix post t)) =
      regsBits (pre ++ v' :: post) t := by
    unfold regsBits; rw [regsSuffix_append]; rfl
  rw [hres] at h4
  exact ((h1.trans h2).trans h3).trans h4

-- Helper: 98/84 left-shift across a single block `u`
private theorem shift_left_98_block (u left suf : Nat) :
    SafeReach (98, ones u + 2 ^ u * (2 * left), 1 + 2 * (1 + 2 * suf))
              (98, left / 2, left % 2 + 2 * (1 + 2 * (ones u + 2 ^ u * (2 * (1 + 2 * suf))))) := by
  have h1 := step1L (q := 98) (by omega) rfl (ones u + 2 ^ u * (2 * left)) (1 + 2 * suf)
  rw [Nat.zero_add] at h1
  cases u with
  | zero =>
    simp only [ones_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at h1 ⊢
    have hm : (2 * left) % 2 = 0 := by omega
    have hd : (2 * left) / 2 = left := by omega
    rw [hm, hd, Nat.zero_add] at h1
    have h2 := step0L (q := 84) (by omega) rfl left (2 * (1 + 2 * suf))
    exact h1.trans h2
  | succ u' =>
    rw [mod2_ones_succ, div2_ones_succ] at h1
    have h2 := scan_left_ones 84 (by omega) rfl u' (2 * left) (2 * (1 + 2 * suf))
    have h3 := step1L (q := 84) (by omega) rfl (2 * left) (ones u' + 2 ^ u' * (2 * (1 + 2 * suf)))
    have hm : (2 * left) % 2 = 0 := by omega
    have hd : (2 * left) / 2 = left := by omega
    rw [hm, hd, Nat.zero_add, ← ones_succ_mul] at h3
    have h4 := step0L (q := 84) (by omega) rfl left (ones (u' + 1) + 2 ^ (u' + 1) * (2 * (1 + 2 * suf)))
    exact ((h1.trans h2).trans h3).trans h4

-- Cleanest statement of shift_left_98_pre using `shiftLeftOut`:
private def shiftLeftOut : List Nat → Nat → Nat
  | [], suf => 1 + 2 * suf
  | u :: us, suf => ones (u + 1) + 2 ^ (u + 1) * (2 * shiftLeftOut us suf)

private theorem two_mul_shiftLeftOut : ∀ pre suf,
    2 * shiftLeftOut pre suf = regsSuffixPre pre (2 * (1 + 2 * suf))
  | [], _ => rfl
  | u :: us, suf => by
    simp only [shiftLeftOut, regsSuffixPre, regBlock, ← two_mul_shiftLeftOut us suf]

private theorem shiftLeftOut_odd : ∀ pre suf, shiftLeftOut pre suf % 2 = 1
  | [], _ => by simp [shiftLeftOut]
  | u :: _, _ => by simp only [shiftLeftOut]; exact mod2_ones_succ u _

private theorem shift_left_98_clean : ∀ pre L suf, L % 2 = 1 →
    SafeReach (98, (shiftLeftRegs pre L) / 2, 1 + 2 * (1 + 2 * suf))
              (98, L / 2, 1 + 2 * shiftLeftOut pre suf)
  | [], _, _, _ => SafeReach.refl _
  | u :: us, L, suf, hL => by
    simp only [shiftLeftRegs, shiftLeftOut]
    have h1 := shift_left_98_clean us (ones (u + 1) + 2 ^ (u + 1) * (2 * L)) suf (mod2_ones_succ u (2 * L))
    rw [div2_ones_succ] at h1
    have hodd := shiftLeftOut_odd us suf
    have hsplit : shiftLeftOut us suf = 1 + 2 * (shiftLeftOut us suf / 2) := by omega
    have h2 := shift_left_98_block u L (shiftLeftOut us suf / 2)
    rw [hL, ← hsplit] at h2
    rw [← ones_succ_mul] at h2
    exact h1.trans h2

-- Gadget 5: DEC Z (v = 0, t >= 1)
private theorem gadget_dec_reg_z (n l : Nat) (pre : List Nat) (post : List Nat) (t : Nat) (ht : 1 ≤ t) :
    SafeReach (1, 4 * l, ones n + 2 ^ n * markedRegsBits pre 0 post t)
              (126, l / 2, l % 2 + 4 * (ones (n + 1) + 2 ^ (n + 1) * regsBits (pre ++ 0 :: post) t)) := by
  have h1 := dec_shift_to_61 n l pre 0 post t
  simp only [ones_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul] at h1
  have hsuf_form : ∃ s', regsSuffix post t = 2 * (1 + 2 * s') := by
    cases post with
    | nil =>
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      exact ⟨1 + 2 * tailBits t', by simp [regsSuffix, tailBits]; omega⟩
    | cons w ws =>
      exact ⟨ones w + 2 ^ w * regsSuffix ws t, by
        simp only [regsSuffix, regBlock]; rw [ones_succ_mul]⟩
  obtain ⟨s', hs'⟩ := hsuf_form
  rw [hs'] at h1
  let Lpre := shiftLeftRegs pre (ones (n + 2) + 2 ^ (n + 2) * (4 * l))
  have h2 := step0R (q := 61) (by omega) rfl (2 * Lpre) (1 + 2 * s')
  have h3 := step1L (q := 123) (by omega) rfl (1 + 2 * (2 * Lpre)) s'
  have hm1 : (1 + 2 * (2 * Lpre)) % 2 = 1 := by omega
  have hd1 : (1 + 2 * (2 * Lpre)) / 2 = 2 * Lpre := by omega
  rw [hm1, hd1] at h3
  have h4 := step1L (q := 98) (by omega) rfl (2 * Lpre) (1 + 2 * s')
  have hm2 : (2 * Lpre) % 2 = 0 := by omega
  have hd2 : (2 * Lpre) / 2 = Lpre := by omega
  rw [hm2, hd2, Nat.zero_add, Nat.zero_add] at h4
  have hodd_L : ∀ a x, x % 2 = 1 → (shiftLeftRegs a x) % 2 = 1 := by
    intro a; induction a with
    | nil => intro x hx; exact hx
    | cons _ _ ih => intro x _; apply ih; exact mod2_ones_succ _ _
  have hLodd : Lpre % 2 = 1 := hodd_L pre _ (mod2_ones_succ (n + 1) (4 * l))
  have h5' := step0L (q := 84) (by omega) rfl Lpre (2 * (1 + 2 * s'))
  rw [hLodd] at h5'
  have h6 := shift_left_98_clean pre (ones (n + 2) + 2 ^ (n + 2) * (4 * l)) (2 * (1 + 2 * s'))
    (mod2_ones_succ (n + 1) (4 * l))
  rw [div2_ones_succ] at h6
  let suf_all := shiftLeftOut pre (2 * (1 + 2 * s'))
  have hsuf_even : 2 * suf_all = regsSuffix (pre ++ 0 :: post) t := by
    rw [two_mul_shiftLeftOut, regsSuffix_append]; simp only [regsSuffix, hs', regBlock, ones]
  have h7 := step1L (q := 98) (by omega) rfl (ones (n + 1) + 2 ^ (n + 1) * (4 * l)) suf_all
  rw [mod2_ones_succ, div2_ones_succ, Nat.zero_add] at h7
  have h8 := scan_left_ones 84 (by omega) rfl n (4 * l) (2 * suf_all)
  rw [ones_succ_mul] at h8
  have h9 := step1L (q := 84) (by omega) rfl (4 * l) (ones n + 2 ^ n * (2 * suf_all))
  have hm3 : (4 * l) % 2 = 0 := by omega
  have hd3 : (4 * l) / 2 = 2 * l := by omega
  rw [hm3, hd3, Nat.zero_add] at h9
  have h10 := step0L (q := 84) (by omega) rfl (2 * l) (1 + 2 * (ones n + 2 ^ n * (2 * suf_all)))
  have hm4 : (2 * l) % 2 = 0 := by omega
  have hd4 : (2 * l) / 2 = l := by omega
  rw [hm4, hd4, Nat.zero_add] at h10
  have h11 := step0L (q := 98) (by omega) rfl l (1 + 2 * (1 + 2 * (ones n + 2 ^ n * (2 * suf_all))))
  rw [Nat.zero_add] at h11
  have heq2 : l % 2 + 2 * (2 * (1 + 2 * (1 + 2 * (ones n + 2 ^ n * (2 * suf_all))))) =
      l % 2 + 4 * (ones (n + 1) + 2 ^ (n + 1) * regsBits (pre ++ 0 :: post) t) := by
    rw [← ones_succ_mul n, ← ones_succ_mul (n + 1), ← ones_shift_left (n + 1), hsuf_even]
    unfold regsBits; omega
  rw [heq2] at h11
  exact (((((((((h1.trans h2).trans h3).trans h4).trans h5').trans h6).trans h7).trans h8).trans h9).trans h10).trans h11

-- Gadget 6: erase 1^n + sentinel 1 in state 10, restore sentinel 1 via 15, skip 0^n back to q=2
private theorem gadget_erase_and_reset (n left suf : Nat) :
    SafeReach (10, left, ones n + 2 ^ n * (1 + 2 * (2 * suf)))
              (2, left / 2, left % 2 + 2 * (2 ^ n * (1 + 2 * (2 * suf)))) := by
  rw [ones_shift_left]
  have h1 := scan_right_ones_erase 10 (by omega) rfl (n + 1) left (2 * suf)
  have h2 := step0L (q := 10) (by omega) rfl (2 ^ (n + 1) * left) suf
  rw [mod2_pow_succ, div2_pow_succ, Nat.zero_add, Nat.zero_add] at h2
  have h3 := step0L (q := 15) (by omega) rfl (2 ^ n * left) (2 * suf)
  cases n with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul] at h1 h2 h3 ⊢
    exact (h1.trans h2).trans h3
  | succ k =>
    rw [mod2_pow_succ, div2_pow_succ, Nat.zero_add] at h3
    have h4 := scan_left_zeros 2 (by omega) rfl k left (1 + 2 * (2 * suf))
    have h5 := step0L (q := 2) (by omega) rfl left (2 ^ k * (1 + 2 * (2 * suf)))
    rw [Nat.zero_add, ← pow2_succ_mul] at h5
    exact (((h1.trans h2).trans h3).trans h4).trans h5

/-! #### 3.4 Soundness of `decodeLBits` and `resolveStep` -/

private theorem regOfSkipState_sound {q k : Nat} (h : regOfSkipState q = some k) :
    k < 9 ∧ q = regSkipState k := by
  unfold regOfSkipState at h
  cases h1 : Nat.ble 57 q with
  | true => rw [h1] at h; contradiction
  | false =>
    rw [h1] at h; dsimp only at h
    cases h2 : Nat.ble 35 q with
    | false =>
      rw [h2] at h; dsimp only at h
      split at h; · injection h with h; subst h; exact ⟨by omega, Nat.eq_of_beq_eq_true ‹_›⟩
      split at h; · injection h with h; subst h; exact ⟨by omega, Nat.eq_of_beq_eq_true ‹_›⟩
      split at h; · injection h with h; subst h; exact ⟨by omega, Nat.eq_of_beq_eq_true ‹_›⟩
      split at h; · injection h with h; subst h; exact ⟨by omega, Nat.eq_of_beq_eq_true ‹_›⟩
      contradiction
    | true =>
      rw [h2] at h; dsimp only at h
      split at h; · injection h with h; subst h; exact ⟨by omega, Nat.eq_of_beq_eq_true ‹_›⟩
      split at h; · injection h with h; subst h; exact ⟨by omega, Nat.eq_of_beq_eq_true ‹_›⟩
      split at h; · injection h with h; subst h; exact ⟨by omega, Nat.eq_of_beq_eq_true ‹_›⟩
      split at h; · injection h with h; subst h; exact ⟨by omega, Nat.eq_of_beq_eq_true ‹_›⟩
      split at h; · injection h with h; subst h; exact ⟨by omega, Nat.eq_of_beq_eq_true ‹_›⟩
      contradiction

/-! #### 3.4 Fast Return-to-74 Shortcut, `decodeLBits`, and `resolveStep` -/

private theorem splitLastTrue_none : ∀ bs, splitLastTrue bs = none → bitsToNat bs = 0
  | [], _ => rfl
  | b :: bs, h => by
    unfold splitLastTrue at h
    cases hs : splitLastTrue bs with
    | some _ => rw [hs] at h; contradiction
    | none =>
      rw [hs] at h
      cases b with
      | true => simp at h
      | false => simp [bitsToNat, splitLastTrue_none bs hs]

private theorem splitLastTrue_sound : ∀ l xs, splitLastTrue l = some xs →
    bitsToNat l = bitsToNat (xs ++ [true])
  | [], _, h => by simp [splitLastTrue] at h
  | b :: bs, xs, h => by
    unfold splitLastTrue at h
    cases hs : splitLastTrue bs with
    | some ys =>
      rw [hs] at h; injection h with h1; subst h1
      cases b <;> simp [bitsToNat, splitLastTrue_sound bs ys hs]
    | none =>
      rw [hs] at h
      cases b with
      | false => simp at h
      | true =>
        simp at h; subst h
        simp [bitsToNat, splitLastTrue_none bs hs]

private theorem zState_step0 (k : Nat) (hk : k < 6) (left suf : Nat) :
    SafeReach (zState k, left, 2 * suf)
      (zState (k + 1), left / 2, left % 2 + 2 * (2 * suf)) := by
  match k with
  | 0 => simpa only [zState, Nat.zero_add] using step0L (by omega) (show (fastRow 3).1 = some (false, false, 4) from rfl) left suf
  | 1 => simpa only [zState, Nat.zero_add] using step0L (by omega) (show (fastRow 4).1 = some (false, false, 6) from rfl) left suf
  | 2 => simpa only [zState, Nat.zero_add] using step0L (by omega) (show (fastRow 6).1 = some (false, false, 9) from rfl) left suf
  | 3 => simpa only [zState, Nat.zero_add] using step0L (by omega) (show (fastRow 9).1 = some (false, false, 14) from rfl) left suf
  | 4 => simpa only [zState, Nat.zero_add] using step0L (by omega) (show (fastRow 14).1 = some (false, false, 22) from rfl) left suf
  | 5 => simpa only [zState, Nat.zero_add] using step0L (by omega) (show (fastRow 22).1 = some (false, false, 33) from rfl) left suf
  | _ + 6 => omega

private theorem zState_step1 (k : Nat) (hk : k ≤ 6) (left suf : Nat) :
    SafeReach (zState k, left, 1 + 2 * suf)
      (3, left / 2, left % 2 + 2 * (1 + 2 * suf)) := by
  match k with
  | 0 => exact step1L (by omega) (show (fastRow 3).2 = some (true, false, 3) from rfl) left suf
  | 1 => exact step1L (by omega) (show (fastRow 4).2 = some (true, false, 3) from rfl) left suf
  | 2 => exact step1L (by omega) (show (fastRow 6).2 = some (true, false, 3) from rfl) left suf
  | 3 => exact step1L (by omega) (show (fastRow 9).2 = some (true, false, 3) from rfl) left suf
  | 4 => exact step1L (by omega) (show (fastRow 14).2 = some (true, false, 3) from rfl) left suf
  | 5 => exact step1L (by omega) (show (fastRow 22).2 = some (true, false, 3) from rfl) left suf
  | 6 => exact step1L (by omega) (show (fastRow 33).2 = some (true, false, 3) from rfl) left suf
  | _ + 7 => omega

private theorem scan_68_zeros : ∀ n suf, SafeReach (68, 0, 2 ^ n * suf) (68, 0, suf)
  | 0, suf => by simp only [Nat.pow_zero, Nat.one_mul]; exact SafeReach.refl _
  | n + 1, suf => by
    rw [pow2_succ, Nat.mul_assoc]
    have s := step0R (by omega) (show (fastRow 68).1 = some (false, true, 68) from rfl) 0 (2 ^ n * suf)
    exact s.trans (scan_68_zeros n suf)

private theorem zState_finish_to_74 (Y : Nat) :
    SafeReach (3, 0, 2 * (1 + 2 * Y)) (74, 1, Y) := by
  let X := 1 + 2 * Y
  have hz0 : (0 : Nat) / 2 = 0 := rfl
  have hz1 : (0 : Nat) % 2 = 0 := rfl
  have s1 : SafeReach (3, 0, 2 * X) (4, 0, 2 * (2 * X)) := by
    have := zState_step0 0 (by omega) 0 X; simpa only [zState, hz0, hz1, Nat.zero_add] using this
  have s2 : SafeReach (4, 0, 2 * (2 * X)) (6, 0, 2 * (4 * X)) := by
    have := zState_step0 1 (by omega) 0 (2 * X); dsimp only [zState] at this
    rw [hz0, show 0 % 2 + 2 * (2 * (2 * X)) = 2 * (4 * X) by omega] at this; exact this
  have s3 : SafeReach (6, 0, 2 * (4 * X)) (9, 0, 2 * (8 * X)) := by
    have := zState_step0 2 (by omega) 0 (4 * X); dsimp only [zState] at this
    rw [hz0, show 0 % 2 + 2 * (2 * (4 * X)) = 2 * (8 * X) by omega] at this; exact this
  have s4 : SafeReach (9, 0, 2 * (8 * X)) (14, 0, 2 * (16 * X)) := by
    have := zState_step0 3 (by omega) 0 (8 * X); dsimp only [zState] at this
    rw [hz0, show 0 % 2 + 2 * (2 * (8 * X)) = 2 * (16 * X) by omega] at this; exact this
  have s5 : SafeReach (14, 0, 2 * (16 * X)) (22, 0, 2 * (32 * X)) := by
    have := zState_step0 4 (by omega) 0 (16 * X); dsimp only [zState] at this
    rw [hz0, show 0 % 2 + 2 * (2 * (16 * X)) = 2 * (32 * X) by omega] at this; exact this
  have s6 : SafeReach (22, 0, 2 * (32 * X)) (33, 0, 2 * (64 * X)) := by
    have := zState_step0 5 (by omega) 0 (32 * X); dsimp only [zState] at this
    rw [hz0, show 0 % 2 + 2 * (2 * (32 * X)) = 2 * (64 * X) by omega] at this; exact this
  have s7 : SafeReach (33, 0, 2 * (64 * X)) (68, 0, 2 ^ 8 * X) := by
    have := step0L (by omega) (show (fastRow 33).1 = some (false, false, 68) from rfl) 0 (64 * X)
    have hmul : 0 % 2 + 2 * (0 + 2 * (64 * X)) = 2 ^ 8 * X := by omega
    rw [hmul] at this; exact this
  have s8 : SafeReach (68, 0, 2 ^ 8 * X) (68, 0, 1 + 2 * Y) := scan_68_zeros 8 X
  have s9 : SafeReach (68, 0, 1 + 2 * Y) (74, 1, Y) :=
    step1R (by omega) (show (fastRow 68).2 = some (true, true, 74) from rfl) 0 Y
  exact (((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9

private theorem scan_zState_to_74 : ∀ xs k (b : Bool) (R : Nat), k ≤ 6 → no7zeros k (b :: xs) = true →
    SafeReach (zState k, bitsToNat (xs ++ [true]),
               (match (generalizing := false) b with | true => 1 | false => 0) + 2 * R)
              (74, 1, bitsToNat (xs.reverse ++ [b]) + 2 ^ (xs.length + 1) * R)
  | [], k, b, R, hk, hno => by
    cases b with
    | true =>
      have s1 := zState_step1 k hk 1 R
      have s2 := zState_step1 0 (by omega) 0 (1 + 2 * R)
      have s3 := zState_finish_to_74 (1 + 2 * R)
      have hz0 : (0 : Nat) / 2 = 0 := rfl
      have hz1 : (0 : Nat) % 2 = 0 := rfl
      simp only [zState, hz0, hz1, Nat.zero_add] at s2
      simpa only [List.nil_append, List.reverse_nil, List.length_nil, bitsToNat, Nat.zero_add,
        Nat.pow_one, Nat.mul_zero] using (s1.trans s2).trans s3
    | false =>
      have hlt6 : k < 6 := by
        unfold no7zeros at hno
        cases h6 : Nat.ble 6 k with
        | true => rw [h6] at hno; simp at hno
        | false =>
          apply Nat.lt_of_not_ge; intro hge
          have := Nat.ble_eq.mpr hge; rw [h6] at this; contradiction
      have s1 := zState_step0 k hlt6 1 R
      have s2 := zState_step1 (k + 1) (by omega) 0 (2 * R)
      have s3 := zState_finish_to_74 (2 * R)
      have hz0 : (0 : Nat) / 2 = 0 := rfl
      have hz1 : (0 : Nat) % 2 = 0 := rfl
      simp only [hz0, hz1, Nat.zero_add] at s2
      simpa only [List.nil_append, List.reverse_nil, List.length_nil, bitsToNat, Nat.zero_add,
        Nat.pow_one, Nat.mul_zero] using (s1.trans s2).trans s3
  | x :: xs, k, b, R, hk, hno => by
    have hbx : bitsToNat (x :: (xs ++ [true])) % 2 = (match (generalizing := false) x with | true => 1 | false => 0) ∧
        bitsToNat (x :: (xs ++ [true])) / 2 = bitsToNat (xs ++ [true]) := by
      cases x <;> simp only [bitsToNat] <;> constructor <;> omega
    have hrev : bitsToNat ((x :: xs).reverse ++ [b]) + 2 ^ ((x :: xs).length + 1) * R =
        bitsToNat (xs.reverse ++ [x]) + 2 ^ (xs.length + 1) *
          ((match (generalizing := false) b with | true => 1 | false => 0) + 2 * R) := by
      have hrl : (xs.reverse ++ [x]).length = xs.length + 1 := by simp
      have ha : (x :: xs).reverse ++ [b] = (xs.reverse ++ [x]) ++ [b] := by simp [List.reverse_cons]
      have h2m : 2 ^ xs.length * (2 * R) = 2 * (2 ^ xs.length * R) := by rw [Nat.mul_left_comm]
      rw [ha, bitsToNat_append, hrl]
      cases b <;> simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_add, Nat.mul_assoc, h2m] <;> omega
    rw [hrev]
    cases b with
    | true =>
      have hno' : no7zeros 0 (x :: xs) = true := hno
      have s1 := zState_step1 k hk (bitsToNat (x :: (xs ++ [true]))) R
      rw [hbx.1, hbx.2] at s1
      exact s1.trans (scan_zState_to_74 xs 0 x (1 + 2 * R) (by omega) hno')
    | false =>
      have hlt6 : k < 6 := by
        unfold no7zeros at hno
        cases h6 : Nat.ble 6 k with
        | true => rw [h6] at hno; simp at hno
        | false =>
          apply Nat.lt_of_not_ge; intro hge
          have := Nat.ble_eq.mpr hge; rw [h6] at this; contradiction
      have hno' : no7zeros (k + 1) (x :: xs) = true := by
        unfold no7zeros at hno
        have h6 : Nat.ble 6 k = false := by
          cases hb : Nat.ble 6 k with
          | false => rfl
          | true => have := Nat.ble_eq.mp hb; omega
        rw [h6] at hno; exact hno
      have s1 := zState_step0 k hlt6 (bitsToNat (x :: (xs ++ [true]))) R
      rw [hbx.1, hbx.2] at s1
      simpa only [List.cons_append, Nat.zero_add] using s1.trans (scan_zState_to_74 xs (k + 1) x (2 * R) (by omega) hno')

private theorem scan_2_to_74 : ∀ xs (b : Bool) (R : Nat), okFrom2 (b :: xs) = true →
    SafeReach (2, bitsToNat (xs ++ [true]),
               (match (generalizing := false) b with | true => 1 | false => 0) + 2 * R)
              (74, 1, bitsToNat (xs.reverse ++ [b]) + 2 ^ (xs.length + 1) * R)
  | [], b, R, _ => by
    have hz0 : (0 : Nat) / 2 = 0 := rfl
    have hz1 : (0 : Nat) % 2 = 0 := rfl
    have ho1 : (1 : Nat) % 2 = 1 := rfl
    cases b with
    | true =>
      have s1 := step1L (by omega) (show (fastRow 2).2 = some (true, false, 3) from rfl) 1 R
      have s2 := zState_step1 0 (by omega) 0 (1 + 2 * R)
      have s3 := zState_finish_to_74 (1 + 2 * R)
      simp only [zState, hz0, hz1, ho1, Nat.zero_add] at s1 s2
      simpa only [List.nil_append, List.reverse_nil, List.length_nil, bitsToNat, Nat.zero_add,
        Nat.pow_one, Nat.mul_zero] using (s1.trans s2).trans s3
    | false =>
      have s1 := step0L (by omega) (show (fastRow 2).1 = some (false, false, 2) from rfl) 1 R
      have s2 := step1L (by omega) (show (fastRow 2).2 = some (true, false, 3) from rfl) 0 (2 * R)
      have s3 := zState_finish_to_74 (2 * R)
      simp only [hz0, hz1, ho1, Nat.zero_add] at s1 s2
      simpa only [List.nil_append, List.reverse_nil, List.length_nil, bitsToNat, Nat.zero_add,
        Nat.pow_one, Nat.mul_zero] using (s1.trans s2).trans s3
  | x :: xs, b, R, hok => by
    have hbx : bitsToNat (x :: (xs ++ [true])) % 2 = (match (generalizing := false) x with | true => 1 | false => 0) ∧
        bitsToNat (x :: (xs ++ [true])) / 2 = bitsToNat (xs ++ [true]) := by
      cases x <;> simp only [bitsToNat] <;> constructor <;> omega
    have hrev : bitsToNat ((x :: xs).reverse ++ [b]) + 2 ^ ((x :: xs).length + 1) * R =
        bitsToNat (xs.reverse ++ [x]) + 2 ^ (xs.length + 1) *
          ((match (generalizing := false) b with | true => 1 | false => 0) + 2 * R) := by
      have hrl : (xs.reverse ++ [x]).length = xs.length + 1 := by simp
      have ha : (x :: xs).reverse ++ [b] = (xs.reverse ++ [x]) ++ [b] := by simp [List.reverse_cons]
      have h2m : 2 ^ xs.length * (2 * R) = 2 * (2 ^ xs.length * R) := by rw [Nat.mul_left_comm]
      rw [ha, bitsToNat_append, hrl]
      cases b <;> simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_add, Nat.mul_assoc, h2m] <;> omega
    rw [hrev]
    cases b with
    | true =>
      have s1 := step1L (by omega) (show (fastRow 2).2 = some (true, false, 3) from rfl)
        (bitsToNat (x :: (xs ++ [true]))) R
      rw [hbx.1, hbx.2] at s1
      exact s1.trans (scan_zState_to_74 xs 0 x (1 + 2 * R) (by omega) hok)
    | false =>
      have s1 := step0L (by omega) (show (fastRow 2).1 = some (false, false, 2) from rfl)
        (bitsToNat (x :: (xs ++ [true]))) R
      rw [hbx.1, hbx.2] at s1
      simp only [Nat.zero_add] at s1
      simpa only [List.cons_append, Nat.zero_add] using s1.trans (scan_2_to_74 xs x (2 * R) hok)

private theorem returnTo74From3_sound (l r l' r' : List Bool)
    (h : returnTo74From3 l r = some (l', r')) :
    ∀ suf, SafeReach (3, bitsToNat l, bitsToNat r + 2 ^ r.length * suf)
                     (74, bitsToNat l', bitsToNat r' + 2 ^ r'.length * suf) := by
  cases r with
  | nil => simp [returnTo74From3] at h
  | cons b rs =>
    unfold returnTo74From3 at h; dsimp only at h
    cases hs : splitLastTrue l with
    | none =>
      rw [hs] at h; dsimp only at h
      cases hr : runBits (fun x => Nat.beq x 74) 160 3 l (b :: rs) with
      | none => rw [hr] at h; contradiction
      | some res =>
        rcases res with ⟨q', l1, r1⟩; rw [hr] at h; dsimp only at h
        injection h with h1
        have : l1 = l' ∧ r1 = r' := by cases h1; exact ⟨rfl, rfl⟩
        rcases this with ⟨rfl, rfl⟩
        obtain ⟨hq', hreach⟩ := runBits_sound _ 160 3 l (b :: rs) q' l1 r1 hr
        have hq74 : q' = 74 := Nat.eq_of_beq_eq_true hq'; subst hq74
        exact hreach
    | some xs =>
      rw [hs] at h; dsimp only at h
      cases hno : no7zeros 0 (b :: xs) with
      | true =>
        rw [hno] at h; dsimp only at h
        injection h with h1
        have : [true] = l' ∧ xs.reverse ++ b :: rs = r' := by cases h1; exact ⟨rfl, rfl⟩
        rcases this with ⟨rfl, rfl⟩
        intro suf
        have hl := splitLastTrue_sound l xs hs
        have hsc := scan_zState_to_74 xs 0 b (bitsToNat rs + 2 ^ rs.length * suf) (by omega) hno
        have heqL : bitsToNat (b :: rs) + 2 ^ (b :: rs).length * suf =
            (match (generalizing := false) b with | true => 1 | false => 0) +
              2 * (bitsToNat rs + 2 ^ rs.length * suf) := by
          cases b <;> simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_assoc] <;> omega
        have heqR : bitsToNat (xs.reverse ++ [b]) + 2 ^ (xs.length + 1) * (bitsToNat rs + 2 ^ rs.length * suf) =
            bitsToNat (xs.reverse ++ b :: rs) + 2 ^ (xs.reverse ++ b :: rs).length * suf := by
          have ha : xs.reverse ++ b :: rs = (xs.reverse ++ [b]) ++ rs := by simp
          have hrl : (xs.reverse ++ [b]).length = xs.length + 1 := by simp
          rw [ha]
          conv => rhs; rw [bitsToNat_append (xs.reverse ++ [b]) rs, @List.length_append _ (xs.reverse ++ [b]) rs, hrl, Nat.pow_add 2 (xs.length + 1) rs.length, Nat.mul_assoc]
          rw [Nat.mul_add, Nat.add_assoc]
        rw [hl, heqL]; rw [heqR] at hsc; exact hsc
      | false =>
        rw [hno] at h; dsimp only at h
        cases hr : runBits (fun x => Nat.beq x 74) 160 3 l (b :: rs) with
        | none => rw [hr] at h; contradiction
        | some res =>
          rcases res with ⟨q', l1, r1⟩; rw [hr] at h; dsimp only at h
          injection h with h1
          have : l1 = l' ∧ r1 = r' := by cases h1; exact ⟨rfl, rfl⟩
          rcases this with ⟨rfl, rfl⟩
          obtain ⟨hq', hreach⟩ := runBits_sound _ 160 3 l (b :: rs) q' l1 r1 hr
          have hq74 : q' = 74 := Nat.eq_of_beq_eq_true hq'; subst hq74
          exact hreach

private theorem returnTo74From2_sound (l r l' r' : List Bool)
    (h : returnTo74From2 l r = some (l', r')) :
    ∀ suf, SafeReach (2, bitsToNat l, bitsToNat r + 2 ^ r.length * suf)
                     (74, bitsToNat l', bitsToNat r' + 2 ^ r'.length * suf) := by
  cases r with
  | nil => simp [returnTo74From2] at h
  | cons b rs =>
    unfold returnTo74From2 at h; dsimp only at h
    cases hs : splitLastTrue l with
    | none =>
      rw [hs] at h; dsimp only at h
      cases hr : runBits (fun x => Nat.beq x 74) 160 2 l (b :: rs) with
      | none => rw [hr] at h; contradiction
      | some res =>
        rcases res with ⟨q', l1, r1⟩; rw [hr] at h; dsimp only at h
        injection h with h1
        have : l1 = l' ∧ r1 = r' := by cases h1; exact ⟨rfl, rfl⟩
        rcases this with ⟨rfl, rfl⟩
        obtain ⟨hq', hreach⟩ := runBits_sound _ 160 2 l (b :: rs) q' l1 r1 hr
        have hq74 : q' = 74 := Nat.eq_of_beq_eq_true hq'; subst hq74
        exact hreach
    | some xs =>
      rw [hs] at h; dsimp only at h
      cases hok : okFrom2 (b :: xs) with
      | true =>
        rw [hok] at h; dsimp only at h
        injection h with h1
        have : [true] = l' ∧ xs.reverse ++ b :: rs = r' := by cases h1; exact ⟨rfl, rfl⟩
        rcases this with ⟨rfl, rfl⟩
        intro suf
        have hl := splitLastTrue_sound l xs hs
        have hsc := scan_2_to_74 xs b (bitsToNat rs + 2 ^ rs.length * suf) hok
        have heqL : bitsToNat (b :: rs) + 2 ^ (b :: rs).length * suf =
            (match (generalizing := false) b with | true => 1 | false => 0) +
              2 * (bitsToNat rs + 2 ^ rs.length * suf) := by
          cases b <;> simp only [bitsToNat, List.length_cons, pow2_succ, Nat.mul_assoc] <;> omega
        have heqR : bitsToNat (xs.reverse ++ [b]) + 2 ^ (xs.length + 1) * (bitsToNat rs + 2 ^ rs.length * suf) =
            bitsToNat (xs.reverse ++ b :: rs) + 2 ^ (xs.reverse ++ b :: rs).length * suf := by
          have ha : xs.reverse ++ b :: rs = (xs.reverse ++ [b]) ++ rs := by simp
          have hrl : (xs.reverse ++ [b]).length = xs.length + 1 := by simp
          rw [ha]
          conv => rhs; rw [bitsToNat_append (xs.reverse ++ [b]) rs, @List.length_append _ (xs.reverse ++ [b]) rs, hrl, Nat.pow_add 2 (xs.length + 1) rs.length, Nat.mul_assoc]
          rw [Nat.mul_add, Nat.add_assoc]
        rw [hl, heqL]; rw [heqR] at hsc; exact hsc
      | false =>
        rw [hok] at h; dsimp only at h
        cases hr : runBits (fun x => Nat.beq x 74) 160 2 l (b :: rs) with
        | none => rw [hr] at h; contradiction
        | some res =>
          rcases res with ⟨q', l1, r1⟩; rw [hr] at h; dsimp only at h
          injection h with h1
          have : l1 = l' ∧ r1 = r' := by cases h1; exact ⟨rfl, rfl⟩
          rcases this with ⟨rfl, rfl⟩
          obtain ⟨hq', hreach⟩ := runBits_sound _ 160 2 l (b :: rs) q' l1 r1 hr
          have hq74 : q' = 74 := Nat.eq_of_beq_eq_true hq'; subst hq74
          exact hreach

private def frameBits (p : List Bool) (m : Nat) (rs : List Nat) (t : Nat) : Nat × Nat × Nat :=
  frameState (bitsToNat p) m rs t

private theorem regsBits_form (rs : List Nat) (t : Nat) :
    ∃ s, regsBits rs t = 1 + 2 * (2 * s) := by
  refine ⟨regsSuffix rs t / 2, ?_⟩
  unfold regsBits
  cases rs with
  | nil =>
    cases t with
    | zero => simp [regsSuffix, tailBits]
    | succ _ => simp [regsSuffix, tailBits]; omega
  | cons _ _ => simp [regsSuffix, regBlock]

private theorem finishEraseBits_sound (q : Nat) (l r p5 : List Bool)
    (h : finishEraseBits q l r = some p5) :
    p5.length = 42 ∧
    ∀ m rs t,
      SafeReach (q, bitsToNat l, bitsToNat r + 2 ^ r.length * (ones m + 2 ^ m * regsBits rs t))
                (frameBits p5 m rs t) := by
  unfold finishEraseBits at h
  cases h1 : runBits (fun x => Nat.beq x 10) 100 q l r with
  | none => rw [h1] at h; contradiction
  | some res4 =>
    rcases res4 with ⟨q4, l4, r4⟩
    rw [h1] at h; dsimp only at h
    cases ht4 : allTrue r4 with
    | false => rw [ht4] at h; contradiction
    | true =>
      rw [ht4] at h; dsimp only at h
      cases h2 : returnTo74From2 (popLeft l4).2 ((popLeft l4).1 :: List.replicate r4.length false) with
      | none => rw [h2] at h; contradiction
      | some res5 =>
        rcases res5 with ⟨l5, r5⟩
        rw [h2] at h; dsimp only at h
        cases hc : isOneBits l5 && Nat.beq r5.length 42 with
        | false => rw [hc] at h; contradiction
        | true =>
          rw [hc] at h; injection h with hp5; subst hp5
          have ⟨hl5, hr5⟩ := Bool.and_eq_true_iff.mp hc
          have hl5e : bitsToNat l5 = 1 := isOneBits_sound l5 hl5
          have hr5e : r5.length = 42 := Nat.eq_of_beq_eq_true hr5
          obtain ⟨hq4, hrw1⟩ := runBits_sound _ 100 q l r q4 l4 r4 h1
          have hq4e : q4 = 10 := Nat.eq_of_beq_eq_true hq4; subst hq4e
          have hr4e : bitsToNat r4 = ones r4.length := allTrue_sound r4 ht4
          have hret := returnTo74From2_sound _ _ l5 r5 h2
          obtain ⟨hpl1, hpl2⟩ := popLeft_sound l4
          have hb2 : bitsToNat ((popLeft l4).1 :: List.replicate r4.length false) = bitsToNat l4 % 2 := by
            cases hlb : (popLeft l4).1 <;> rw [hlb] at hpl1 <;>
              simp [bitsToNat, bitsToNat_replicate_false, ← hpl1]
          have hlen2 : ((popLeft l4).1 :: List.replicate r4.length false).length = r4.length + 1 := by simp
          refine ⟨hr5e, fun m rs t => ?_⟩
          have hs1 := hrw1 (ones m + 2 ^ m * regsBits rs t)
          have hs2 := hret (2 ^ m * regsBits rs t)
          rw [hl5e, hr5e, hpl2, hb2, hlen2] at hs2
          rw [hr4e] at hs1
          obtain ⟨s, hs⟩ := regsBits_form rs t
          have hge := gadget_erase_and_reset (r4.length + m) (bitsToNat l4) s
          rw [← hs] at hge
          have heqA : ones r4.length + 2 ^ r4.length * (ones m + 2 ^ m * regsBits rs t) =
              ones (r4.length + m) + 2 ^ (r4.length + m) * regsBits rs t := (ones_add r4.length m _).symm
          have heqB : bitsToNat l4 % 2 + 2 * (2 ^ (r4.length + m) * regsBits rs t) =
              bitsToNat l4 % 2 + 2 ^ (r4.length + 1) * (2 ^ m * regsBits rs t) := by
            rw [Nat.pow_add, pow2_succ, Nat.mul_assoc, Nat.mul_assoc]
          have heqC : bitsToNat r5 + 2 ^ 42 * (2 ^ m * regsBits rs t) =
              bitsToNat r5 + 2 ^ (42 + m) * regsBits rs t := by
            rw [Nat.pow_add, Nat.mul_assoc]
          rw [heqA] at hs1; rw [heqB] at hge; rw [heqC] at hs2
          exact (hs1.trans hge).trans hs2

-- List register access & update helpers
private def listSplitAt : Nat → List Nat → Option (List Nat × Nat × List Nat)
  | _, [] => none
  | 0, v :: vs => some ([], v, vs)
  | k + 1, v :: vs =>
    match listSplitAt k vs with
    | none => none
    | some (pre, x, post) => some (v :: pre, x, post)

private theorem listSplitAt_sound : ∀ k rs pre v post,
    listSplitAt k rs = some (pre, v, post) →
    pre.length = k ∧ rs = pre ++ v :: post
  | _, [], _, _, _, h => by simp [listSplitAt] at h
  | 0, v :: vs, pre, v', post, h => by
    simp [listSplitAt] at h; rcases h with ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  | k + 1, u :: us, pre, v', post, h => by
    unfold listSplitAt at h
    cases hs : listSplitAt k us with
    | none => rw [hs] at h; contradiction
    | some x =>
      rcases x with ⟨pre', x', post'⟩
      rw [hs] at h; injection h with h1
      have : pre = u :: pre' ∧ v' = x' ∧ post = post' := by cases h1; exact ⟨rfl, rfl, rfl⟩
      rcases this with ⟨rfl, rfl, rfl⟩
      obtain ⟨hl, he⟩ := listSplitAt_sound k us pre' v' post hs
      exact ⟨by simp [hl], by simp [he]⟩

private theorem listSplitAt_of_lt : ∀ k rs, k < rs.length →
    ∃ pre v post, listSplitAt k rs = some (pre, v, post) ∧ pre.length = k ∧ rs = pre ++ v :: post
  | _, [], h => by simp at h
  | 0, v :: vs, _ => ⟨[], v, vs, rfl, rfl, rfl⟩
  | k + 1, u :: us, h => by
    obtain ⟨pre, v, post, hs, hl, he⟩ := listSplitAt_of_lt k us (by simp at h; omega)
    exact ⟨u :: pre, v, post, by simp [listSplitAt, hs], by simp [hl], by simp [he]⟩

private def regGet (k : Nat) (rs : List Nat) : Nat := rs.getD k 0

private def regSet (k val : Nat) : List Nat → List Nat
  | [] => []
  | v :: vs => match k with | 0 => val :: vs | k' + 1 => v :: regSet k' val vs

private theorem regGet_append (pre : List Nat) (v : Nat) (post : List Nat) :
    regGet pre.length (pre ++ v :: post) = v := by
  induction pre with
  | nil => rfl
  | cons _ _ _ => simp [regGet, List.getD]

private theorem regSet_append (pre : List Nat) (v w : Nat) (post : List Nat) :
    regSet pre.length w (pre ++ v :: post) = pre ++ w :: post := by
  induction pre with
  | nil => rfl
  | cons _ _ ih => simp [regSet, ih]

private theorem regSet_length (k w : Nat) : ∀ rs, (regSet k w rs).length = rs.length
  | [] => by simp [regSet]
  | _ :: vs => by cases k with | zero => rfl | succ k' => simp [regSet, regSet_length k' w vs]

private theorem decodeLBits_sound_goto (pref pn : List Bool) (h : decodeLBits pref = .goto pn)
    (hlen : pref.length = 42) :
    pn.length = 42 ∧
    ∀ m rs t, SafeReachPos (frameBits pref m rs t) (frameBits pn m rs t) := by
  unfold decodeLBits at h
  cases h0 : runBits isGadgetOrHalt 100 74 [true] pref with
  | none => rw [h0] at h; contradiction
  | some res1 =>
    rcases res1 with ⟨q1, l1, r1⟩; rw [h0] at h; dsimp only at h
    split at h; · contradiction
    split at h
    · cases hf1 : allFalse r1 <;> rw [hf1] at h; · contradiction
      dsimp only at h
      cases hret2 : returnTo74From3 _ _ <;> rw [hret2] at h; · contradiction
      rename_i res20; rcases res20 with ⟨l2_0, r2_0⟩; dsimp only at h
      cases h2 : runBits _ 100 74 l2_0 r2_0 <;> rw [h2] at h; · contradiction
      rename_i res2; rcases res2 with ⟨q2, l2, r2⟩; dsimp only at h
      cases hreg : regOfSkipState q2 <;> cases ht2 : allTrue r2 <;>
        rw [hreg, ht2] at h <;> try contradiction
      dsimp only at h
      cases hret3 : returnTo74From3 _ _ <;> rw [hret3] at h; · contradiction
      rename_i res30; rcases res30 with ⟨l3_0, r3_0⟩; dsimp only at h
      cases h3 : runBits _ 100 74 l3_0 r3_0 <;> rw [h3] at h; · contradiction
      rename_i res3; rcases res3 with ⟨q3, l3, r3⟩; dsimp only at h
      cases ht3 : allTrue r3 <;> rw [ht3] at h; · contradiction
      dsimp only at h
      cases l3 with
      | nil => contradiction
      | cons a l3a =>
        cases a <;> try contradiction
        cases l3a with
        | nil => contradiction
        | cons b l3' =>
          cases b <;> try contradiction
          dsimp only at h
          split at h
          · cases hf : finishEraseBits 38 _ _ <;> rw [hf] at h <;> contradiction
          · split at h
            · cases hf1 : finishEraseBits 38 _ _ <;> cases hf2 : finishEraseBits 126 _ _ <;>
                rw [hf1, hf2] at h <;> contradiction
            · contradiction
    · obtain ⟨_, hrw0⟩ := runBits_sound_pos isGadgetOrHalt 100 74 [true] pref q1 l1 r1 rfl h0
      cases hg : runBits (fun q => Nat.beq q 74 || Nat.beq q 7) 150 q1 l1 r1 with
      | none => rw [hg] at h; contradiction
      | some resg =>
        rcases resg with ⟨qg, lg, rg⟩; rw [hg] at h; dsimp only at h
        obtain ⟨_, hrwg⟩ := runBits_sound _ 150 q1 l1 r1 qg lg rg hg
        split at h
        · rename_i hqg74
          have hqge : qg = 74 := Nat.eq_of_beq_eq_true hqg74; subst hqge
          cases hc : isOneBits lg && Nat.beq rg.length 42 with
          | false => rw [hc] at h; contradiction
          | true =>
            rw [hc] at h; injection h with hp; subst hp
            have ⟨hlg, hrg⟩ := Bool.and_eq_true_iff.mp hc
            have hlge : bitsToNat lg = 1 := isOneBits_sound lg hlg
            have hrge : rg.length = 42 := Nat.eq_of_beq_eq_true hrg
            refine ⟨hrge, fun m rs t => ?_⟩
            have hs0 := hrw0 (2 ^ m * regsBits rs t)
            have hsg := hrwg (2 ^ m * regsBits rs t)
            rw [hlen] at hs0; rw [hlge, hrge] at hsg
            have heq : ∀ p, p + 2 ^ 42 * (2 ^ m * regsBits rs t) = p + 2 ^ (42 + m) * regsBits rs t :=
              fun p => by rw [Nat.pow_add, Nat.mul_assoc]
            rw [heq] at hs0 hsg
            exact hs0.trans hsg
        · split at h
          · rename_i _ hqg7
            have hqge : qg = 7 := Nat.eq_of_beq_eq_true hqg7; subst hqge
            cases hfg : allFalse rg with
            | true =>
              rw [hfg] at h; dsimp only at h
              cases h5 : returnTo74From2 (popLeft lg).2 ((popLeft lg).1 :: List.replicate rg.length false) with
              | none => rw [h5] at h; contradiction
              | some res5 =>
                rcases res5 with ⟨l5, r5⟩; rw [h5] at h; dsimp only at h
                cases hc : isOneBits l5 && Nat.beq r5.length 42 with
                | false => rw [hc] at h; contradiction
                | true =>
                  rw [hc] at h; injection h with hp; subst hp
                  have ⟨hl5, hr5⟩ := Bool.and_eq_true_iff.mp hc
                  have hl5e : bitsToNat l5 = 1 := isOneBits_sound l5 hl5
                  have hr5e : r5.length = 42 := Nat.eq_of_beq_eq_true hr5
                  have hrg0 : bitsToNat rg = 0 := allFalse_sound rg hfg
                  have hret := returnTo74From2_sound _ _ l5 r5 h5
                  obtain ⟨hpl1, hpl2⟩ := popLeft_sound lg
                  have hb2 : bitsToNat ((popLeft lg).1 :: List.replicate rg.length false) = bitsToNat lg % 2 := by
                    cases hlb : (popLeft lg).1 <;> rw [hlb] at hpl1 <;>
                      simp [bitsToNat, bitsToNat_replicate_false, ← hpl1]
                  have hlen2 : ((popLeft lg).1 :: List.replicate rg.length false).length = rg.length + 1 := by simp
                  refine ⟨hr5e, fun m rs t => ?_⟩
                  have hs0 := hrw0 (2 ^ m * regsBits rs t)
                  have hsg := hrwg (2 ^ m * regsBits rs t)
                  have hs5 := hret (2 ^ m * regsBits rs t)
                  rw [hlen] at hs0; rw [hrg0] at hsg; rw [hl5e, hr5e, hpl2, hb2, hlen2] at hs5
                  obtain ⟨s, hs⟩ := regsBits_form rs t
                  have hgz := gadget_7_zero_reset (rg.length + m) (bitsToNat lg) s
                  rw [← hs] at hgz
                  have heq0 : ∀ p, p + 2 ^ 42 * (2 ^ m * regsBits rs t) = p + 2 ^ (42 + m) * regsBits rs t :=
                    fun p => by rw [Nat.pow_add, Nat.mul_assoc]
                  have heqA : 0 + 2 ^ rg.length * (2 ^ m * regsBits rs t) = 2 ^ (rg.length + m) * regsBits rs t := by
                    rw [Nat.zero_add, Nat.pow_add, Nat.mul_assoc]
                  have heqB : bitsToNat lg % 2 + 2 * (2 ^ (rg.length + m) * regsBits rs t) =
                      bitsToNat lg % 2 + 2 ^ (rg.length + 1) * (2 ^ m * regsBits rs t) := by
                    rw [Nat.pow_add, pow2_succ, Nat.mul_assoc, Nat.mul_assoc]
                  rw [heq0] at hs0 hs5; rw [heqA] at hsg; rw [heqB] at hgz
                  exact ((hs0.trans hsg).trans hgz).trans hs5
            | false =>
              rw [hfg] at h; dsimp only at h
              cases h5 : runBits (fun q => Nat.beq q 74) 150 7 lg rg with
              | none => rw [h5] at h; contradiction
              | some res5 =>
                rcases res5 with ⟨q5, l5, r5⟩; rw [h5] at h; dsimp only at h
                cases hc : isOneBits l5 && Nat.beq r5.length 42 with
                | false => rw [hc] at h; contradiction
                | true =>
                  rw [hc] at h; injection h with hp; subst hp
                  have ⟨hl5, hr5⟩ := Bool.and_eq_true_iff.mp hc
                  have hl5e : bitsToNat l5 = 1 := isOneBits_sound l5 hl5
                  have hr5e : r5.length = 42 := Nat.eq_of_beq_eq_true hr5
                  obtain ⟨hq5, hrw5⟩ := runBits_sound _ 150 7 lg rg q5 l5 r5 h5
                  have hq5e : q5 = 74 := Nat.eq_of_beq_eq_true hq5; subst hq5e
                  refine ⟨hr5e, fun m rs t => ?_⟩
                  have hs0 := hrw0 (2 ^ m * regsBits rs t)
                  have hsg := hrwg (2 ^ m * regsBits rs t)
                  have hs5 := hrw5 (2 ^ m * regsBits rs t)
                  rw [hlen] at hs0; rw [hl5e, hr5e] at hs5
                  have heq0 : ∀ p, p + 2 ^ 42 * (2 ^ m * regsBits rs t) = p + 2 ^ (42 + m) * regsBits rs t :=
                    fun p => by rw [Nat.pow_add, Nat.mul_assoc]
                  rw [heq0] at hs0 hs5
                  exact (hs0.trans hsg).trans hs5
          · contradiction

private theorem decodeLBits_sound_inc (pref : List Bool) (k : Nat) (pn : List Bool)
    (h : decodeLBits pref = .inc k pn) (hlen : pref.length = 42) :
    k < 9 ∧ pn.length = 42 ∧
    ∀ m rs t, 1 ≤ m → rs.length = 9 →
      SafeReachPos (frameBits pref m rs t) (frameBits pn m (regSet k (regGet k rs + 1) rs) (t + 1)) := by
  unfold decodeLBits at h
  cases h0 : runBits isGadgetOrHalt 100 74 [true] pref with
  | none => rw [h0] at h; contradiction
  | some res1 =>
    rcases res1 with ⟨q1, l1, r1⟩; rw [h0] at h; dsimp only at h
    split at h; · contradiction
    split at h
    · rename_i _ hq34
      have hq34e := Nat.eq_of_beq_eq_true hq34; subst hq34e
      cases hf1 : allFalse r1 with
      | false => rw [hf1] at h; contradiction
      | true =>
        rw [hf1] at h; dsimp only at h
        cases hret2 : returnTo74From3 (popLeft l1).2 ((popLeft l1).1 :: List.replicate r1.length true) with
        | none => rw [hret2] at h; contradiction
        | some res20 =>
          rcases res20 with ⟨l2_0, r2_0⟩; rw [hret2] at h; dsimp only at h
          cases h2 : runBits (fun q => (regOfSkipState q).isSome) 100 74 l2_0 r2_0 with
          | none => rw [h2] at h; contradiction
          | some res2 =>
            rcases res2 with ⟨q2, l2, r2⟩; rw [h2] at h; dsimp only at h
            cases hreg : regOfSkipState q2 with
            | none => rw [hreg] at h; contradiction
            | some k' =>
              cases ht2 : allTrue r2 with
              | false => rw [hreg, ht2] at h; contradiction
              | true =>
                rw [hreg, ht2] at h; dsimp only at h
                obtain ⟨hk', hq2e⟩ := regOfSkipState_sound hreg; subst hq2e
                cases hret3 : returnTo74From3 (popLeft l2).2 ((popLeft l2).1 :: List.replicate r2.length true) with
                | none => rw [hret3] at h; contradiction
                | some res30 =>
                  rcases res30 with ⟨l3_0, r3_0⟩; rw [hret3] at h; dsimp only at h
                  cases h3 : runBits (fun q => Nat.beq q 60 || Nat.beq q 1) 100 74 l3_0 r3_0 with
                  | none => rw [h3] at h; contradiction
                  | some res3 =>
                    rcases res3 with ⟨q3, l3, r3⟩; rw [h3] at h; dsimp only at h
                    cases ht3 : allTrue r3 with
                    | false => rw [ht3] at h; contradiction
                    | true =>
                      rw [ht3] at h; dsimp only at h
                      cases l3 with
                      | nil => contradiction
                      | cons a l3a =>
                        cases a with
                        | true => contradiction
                        | false =>
                          cases l3a with
                          | nil => contradiction
                          | cons b l3' =>
                            cases b with
                            | true => contradiction
                            | false =>
                              dsimp only at h
                              split at h
                              · rename_i hq60
                                have hq60e := Nat.eq_of_beq_eq_true hq60; subst hq60e
                                cases hf : finishEraseBits 38 l3' (false :: false :: List.replicate r3.length true) with
                                | none => rw [hf] at h; contradiction
                                | some pn' =>
                                  rw [hf] at h; dsimp only at h; injection h with hk_eq hpn_eq; subst hk_eq; subst hpn_eq
                                  obtain ⟨_, hrw0⟩ := runBits_sound_pos _ 100 74 [true] pref 34 l1 r1 rfl h0
                                  have hret2s := returnTo74From3_sound _ _ l2_0 r2_0 hret2
                                  obtain ⟨_, hrw2⟩ := runBits_sound _ 100 74 l2_0 r2_0 (regSkipState k') l2 r2 h2
                                  have hret3s := returnTo74From3_sound _ _ l3_0 r3_0 hret3
                                  obtain ⟨_, hrw3⟩ := runBits_sound _ 100 74 l3_0 r3_0 60 (false :: false :: l3') r3 h3
                                  obtain ⟨hltn, hfin⟩ := finishEraseBits_sound 38 l3' (false :: false :: List.replicate r3.length true) pn' hf
                                  have hr1_0 := allFalse_sound r1 hf1
                                  have hr2_1 := allTrue_sound r2 ht2
                                  have hr3_1 := allTrue_sound r3 ht3
                                  obtain ⟨hpl1a, hpl1b⟩ := popLeft_sound l1
                                  obtain ⟨hpl2a, hpl2b⟩ := popLeft_sound l2
                                  have hb1 : bitsToNat ((popLeft l1).1 :: List.replicate r1.length true) =
                                      bitsToNat l1 % 2 + 2 * ones r1.length := by
                                    cases hlb : (popLeft l1).1 <;> rw [hlb] at hpl1a <;>
                                      simp [bitsToNat, bitsToNat_replicate_true, ← hpl1a]
                                  have hb2 : bitsToNat ((popLeft l2).1 :: List.replicate r2.length true) =
                                      bitsToNat l2 % 2 + 2 * ones r2.length := by
                                    cases hlb : (popLeft l2).1 <;> rw [hlb] at hpl2a <;>
                                      simp [bitsToNat, bitsToNat_replicate_true, ← hpl2a]
                                  have hlen1' : ((popLeft l1).1 :: List.replicate r1.length true).length = r1.length + 1 := by simp
                                  have hlen2' : ((popLeft l2).1 :: List.replicate r2.length true).length = r2.length + 1 := by simp
                                  have hb3 : bitsToNat (false :: false :: List.replicate r3.length true) = 4 * ones r3.length := by
                                    simp [bitsToNat, bitsToNat_replicate_true]; omega
                                  have hlen3' : (false :: false :: List.replicate r3.length true).length = r3.length + 2 := by simp
                                  have hl3_eq : bitsToNat (false :: false :: l3') = 4 * bitsToNat l3' := by
                                    simp [bitsToNat]; omega
                                  refine ⟨hk', hltn, fun m rs t hm hlenrs => ?_⟩
                                  obtain ⟨pre, v, post, _, hprelen, rfl⟩ := listSplitAt_of_lt k' rs (by omega)
                                  have hs0 := hrw0 (2 ^ m * regsBits (pre ++ v :: post) t)
                                  have hg1 := gadget_fill_and_back (r1.length + m) (bitsToNat l1) (regsSuffix (pre ++ v :: post) t) (by omega)
                                  have hs2a := hret2s (ones m + 2 ^ m * regsBits (pre ++ v :: post) t)
                                  have hs2b := hrw2 (ones m + 2 ^ m * regsBits (pre ++ v :: post) t)
                                  have hg2 := gadget_mark_reg k' (r2.length + m) (bitsToNat l2) pre v post t hk' hprelen
                                  have hs3a := hret3s (ones m + 2 ^ m * markedRegsBits pre v post t)
                                  have hs3b := hrw3 (ones m + 2 ^ m * markedRegsBits pre v post t)
                                  have hg3 := gadget_inc_reg (r3.length + m) (bitsToNat l3') pre v post t
                                  have hsf := hfin m (pre ++ (v + 1) :: post) (t + 1)
                                  rw [← hprelen, regGet_append, regSet_append]
                                  rw [hlen, hr1_0] at hs0
                                  rw [hpl1b, hb1, hlen1'] at hs2a
                                  rw [hr2_1] at hs2b
                                  rw [hpl2b, hb2, hlen2'] at hs3a
                                  rw [hr3_1, hl3_eq] at hs3b
                                  rw [hb3, hlen3'] at hsf
                                  have heq0 : bitsToNat pref + 2 ^ 42 * (2 ^ m * regsBits (pre ++ v :: post) t) =
                                      bitsToNat pref + 2 ^ (42 + m) * regsBits (pre ++ v :: post) t := by rw [Nat.pow_add, Nat.mul_assoc]
                                  have heq1 : 0 + 2 ^ r1.length * (2 ^ m * regsBits (pre ++ v :: post) t) =
                                      2 ^ (r1.length + m) * (1 + 2 * regsSuffix (pre ++ v :: post) t) := by
                                    rw [Nat.zero_add, Nat.pow_add, Nat.mul_assoc]; rfl
                                  have heq2 : bitsToNat l1 % 2 + 2 * (ones (r1.length + m) + 2 ^ (r1.length + m) * (1 + 2 * regsSuffix (pre ++ v :: post) t)) =
                                      (bitsToNat l1 % 2 + 2 * ones r1.length) + 2 ^ (r1.length + 1) * (ones m + 2 ^ m * regsBits (pre ++ v :: post) t) := by
                                    unfold regsBits; rw [ones_add r1.length m, pow2_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
                                  have heq3 : ones r2.length + 2 ^ r2.length * (ones m + 2 ^ m * regsBits (pre ++ v :: post) t) =
                                      ones (r2.length + m) + 2 ^ (r2.length + m) * regsBits (pre ++ v :: post) t := (ones_add r2.length m _).symm
                                  have heq4 : bitsToNat l2 % 2 + 2 * (ones (r2.length + m) + 2 ^ (r2.length + m) * markedRegsBits pre v post t) =
                                      (bitsToNat l2 % 2 + 2 * ones r2.length) + 2 ^ (r2.length + 1) * (ones m + 2 ^ m * markedRegsBits pre v post t) := by
                                    rw [ones_add r2.length m, pow2_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
                                  have heq5 : ones r3.length + 2 ^ r3.length * (ones m + 2 ^ m * markedRegsBits pre v post t) =
                                      ones (r3.length + m) + 2 ^ (r3.length + m) * markedRegsBits pre v post t := (ones_add r3.length m _).symm
                                  have heq6 : 4 * (ones (r3.length + m) + 2 ^ (r3.length + m) * regsBits (pre ++ (v + 1) :: post) (t + 1)) =
                                      4 * ones r3.length + 2 ^ (r3.length + 2) * (ones m + 2 ^ m * regsBits (pre ++ (v + 1) :: post) (t + 1)) := by
                                    rw [ones_add r3.length m, pow2_succ, pow2_succ, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc]
                                  rw [heq0, heq1] at hs0; rw [heq2] at hg1; rw [heq3] at hs2b
                                  rw [heq4] at hg2; rw [heq5] at hs3b; rw [heq6] at hg3
                                  exact (((((((hs0.trans hg1).trans hs2a).trans hs2b).trans hg2).trans hs3a).trans hs3b).trans hg3).trans hsf
                              · split at h
                                · cases hf1 : finishEraseBits 38 _ _ <;> cases hf2 : finishEraseBits 126 _ _ <;>
                                    rw [hf1, hf2] at h <;> contradiction
                                · contradiction
    · cases hg : runBits _ 150 q1 l1 r1 <;> rw [hg] at h; · contradiction
      rename_i resg; rcases resg with ⟨qg, lg, rg⟩; dsimp only at h
      split at h
      · cases hc : isOneBits lg && Nat.beq rg.length 42 <;> rw [hc] at h <;> contradiction
      · split at h
        · cases hfg : allFalse rg <;> rw [hfg] at h <;> dsimp only at h
          · cases h5 : runBits _ 150 7 lg rg <;> rw [h5] at h; · contradiction
            rename_i res5; rcases res5 with ⟨q5, l5, r5⟩; dsimp only at h
            cases hc : isOneBits l5 && Nat.beq r5.length 42 <;> rw [hc] at h <;> contradiction
          · cases h5 : returnTo74From2 _ _ <;> rw [h5] at h; · contradiction
            rename_i res5; rcases res5 with ⟨l5, r5⟩; dsimp only at h
            cases hc : isOneBits l5 && Nat.beq r5.length 42 <;> rw [hc] at h <;> contradiction
        · contradiction

private theorem decodeLBits_sound_dec (pref : List Bool) (k : Nat) (pnz pz : List Bool)
    (h : decodeLBits pref = .dec k pnz pz) (hlen : pref.length = 42) :
    k < 9 ∧ pnz.length = 42 ∧ pz.length = 42 ∧
    (∀ m rs t, 1 ≤ m → rs.length = 9 → 0 < regGet k rs →
      SafeReachPos (frameBits pref m rs t) (frameBits pnz (m + 1) (regSet k (regGet k rs - 1) rs) t)) ∧
    (∀ m rs t, 1 ≤ m → 1 ≤ t → rs.length = 9 → regGet k rs = 0 →
      SafeReachPos (frameBits pref m rs t) (frameBits pz m rs t)) := by
  unfold decodeLBits at h
  cases h0 : runBits isGadgetOrHalt 100 74 [true] pref with
  | none => rw [h0] at h; contradiction
  | some res1 =>
    rcases res1 with ⟨q1, l1, r1⟩; rw [h0] at h; dsimp only at h
    split at h; · contradiction
    split at h
    · rename_i _ hq34
      have hq34e := Nat.eq_of_beq_eq_true hq34; subst hq34e
      cases hf1 : allFalse r1 with
      | false => rw [hf1] at h; contradiction
      | true =>
        rw [hf1] at h; dsimp only at h
        cases hret2 : returnTo74From3 (popLeft l1).2 ((popLeft l1).1 :: List.replicate r1.length true) with
        | none => rw [hret2] at h; contradiction
        | some res20 =>
          rcases res20 with ⟨l2_0, r2_0⟩; rw [hret2] at h; dsimp only at h
          cases h2 : runBits (fun q => (regOfSkipState q).isSome) 100 74 l2_0 r2_0 with
          | none => rw [h2] at h; contradiction
          | some res2 =>
            rcases res2 with ⟨q2, l2, r2⟩; rw [h2] at h; dsimp only at h
            cases hreg : regOfSkipState q2 with
            | none => rw [hreg] at h; contradiction
            | some k' =>
              cases ht2 : allTrue r2 with
              | false => rw [hreg, ht2] at h; contradiction
              | true =>
                rw [hreg, ht2] at h; dsimp only at h
                obtain ⟨hk', hq2e⟩ := regOfSkipState_sound hreg; subst hq2e
                cases hret3 : returnTo74From3 (popLeft l2).2 ((popLeft l2).1 :: List.replicate r2.length true) with
                | none => rw [hret3] at h; contradiction
                | some res30 =>
                  rcases res30 with ⟨l3_0, r3_0⟩; rw [hret3] at h; dsimp only at h
                  cases h3 : runBits (fun q => Nat.beq q 60 || Nat.beq q 1) 100 74 l3_0 r3_0 with
                  | none => rw [h3] at h; contradiction
                  | some res3 =>
                    rcases res3 with ⟨q3, l3, r3⟩; rw [h3] at h; dsimp only at h
                    cases ht3 : allTrue r3 with
                    | false => rw [ht3] at h; contradiction
                    | true =>
                      rw [ht3] at h; dsimp only at h
                      cases l3 with
                      | nil => contradiction
                      | cons a l3a =>
                        cases a with
                        | true => contradiction
                        | false =>
                          cases l3a with
                          | nil => contradiction
                          | cons b l3' =>
                            cases b with
                            | true => contradiction
                            | false =>
                              dsimp only at h
                              split at h
                              · cases hf : finishEraseBits 38 _ _ <;> rw [hf] at h <;> contradiction
                              · split at h
                                · rename_i _ hq1
                                  have hq1e := Nat.eq_of_beq_eq_true hq1; subst hq1e
                                  cases hf1e : finishEraseBits 38 l3' (false :: false :: List.replicate r3.length true) with
                                  | none => rw [hf1e] at h; contradiction
                                  | some pnz' =>
                                    cases hf2e : finishEraseBits 126 (popLeft l3').2
                                      ((popLeft l3').1 :: false :: true :: List.replicate r3.length true) with
                                    | none => rw [hf1e, hf2e] at h; contradiction
                                    | some pz' =>
                                      rw [hf1e, hf2e] at h; dsimp only at h
                                      injection h with h1e h2e h3e; subst h1e; subst h2e; subst h3e
                                      obtain ⟨_, hrw0⟩ := runBits_sound_pos _ 100 74 [true] pref 34 l1 r1 rfl h0
                                      have hret2s := returnTo74From3_sound _ _ l2_0 r2_0 hret2
                                      obtain ⟨_, hrw2⟩ := runBits_sound _ 100 74 l2_0 r2_0 (regSkipState k') l2 r2 h2
                                      have hret3s := returnTo74From3_sound _ _ l3_0 r3_0 hret3
                                      obtain ⟨_, hrw3⟩ := runBits_sound _ 100 74 l3_0 r3_0 1 (false :: false :: l3') r3 h3
                                      obtain ⟨hltnz, hfinnz⟩ := finishEraseBits_sound 38 l3'
                                        (false :: false :: List.replicate r3.length true) pnz' hf1e
                                      obtain ⟨hltz, hfinz⟩ := finishEraseBits_sound 126 (popLeft l3').2
                                        ((popLeft l3').1 :: false :: true :: List.replicate r3.length true) pz' hf2e
                                      have hr1_0 := allFalse_sound r1 hf1
                                      have hr2_1 := allTrue_sound r2 ht2
                                      have hr3_1 := allTrue_sound r3 ht3
                                      obtain ⟨hpl1a, hpl1b⟩ := popLeft_sound l1
                                      obtain ⟨hpl2a, hpl2b⟩ := popLeft_sound l2
                                      obtain ⟨hpl3a, hpl3b⟩ := popLeft_sound l3'
                                      have hb1 : bitsToNat ((popLeft l1).1 :: List.replicate r1.length true) =
                                          bitsToNat l1 % 2 + 2 * ones r1.length := by
                                        cases hlb : (popLeft l1).1 <;> rw [hlb] at hpl1a <;>
                                          simp [bitsToNat, bitsToNat_replicate_true, ← hpl1a]
                                      have hb2 : bitsToNat ((popLeft l2).1 :: List.replicate r2.length true) =
                                          bitsToNat l2 % 2 + 2 * ones r2.length := by
                                        cases hlb : (popLeft l2).1 <;> rw [hlb] at hpl2a <;>
                                          simp [bitsToNat, bitsToNat_replicate_true, ← hpl2a]
                                      have hlen1' : ((popLeft l1).1 :: List.replicate r1.length true).length = r1.length + 1 := by simp
                                      have hlen2' : ((popLeft l2).1 :: List.replicate r2.length true).length = r2.length + 1 := by simp
                                      have hb3a : bitsToNat (false :: false :: List.replicate r3.length true) = 4 * ones r3.length := by
                                        simp [bitsToNat, bitsToNat_replicate_true]; omega
                                      have hlen3a : (false :: false :: List.replicate r3.length true).length = r3.length + 2 := by simp
                                      have hb3b : bitsToNat ((popLeft l3').1 :: false :: true :: List.replicate r3.length true) =
                                          bitsToNat l3' % 2 + 4 * ones (r3.length + 1) := by
                                        have := pow2_pos r3.length
                                        cases hlb : (popLeft l3').1 <;> rw [hlb] at hpl3a <;>
                                          simp [bitsToNat, bitsToNat_replicate_true, ones, pow2_succ, ← hpl3a] <;> omega
                                      have hlen3b : ((popLeft l3').1 :: false :: true :: List.replicate r3.length true).length = r3.length + 3 := by simp
                                      have hl3_eq : bitsToNat (false :: false :: l3') = 4 * bitsToNat l3' := by
                                        simp [bitsToNat]; omega
                                      refine ⟨hk', hltnz, hltz, ?_, ?_⟩
                                      · intro m rs t hm hlenrs hpos
                                        obtain ⟨pre, v, post, _, hprelen, rfl⟩ := listSplitAt_of_lt k' rs (by omega)
                                        rw [← hprelen, regGet_append] at hpos ⊢
                                        obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
                                        simp only [Nat.add_sub_cancel, regSet_append]
                                        have hs0 := hrw0 (2 ^ m * regsBits (pre ++ (v' + 1) :: post) t)
                                        have hg1 := gadget_fill_and_back (r1.length + m) (bitsToNat l1) (regsSuffix (pre ++ (v' + 1) :: post) t) (by omega)
                                        have hs2a := hret2s (ones m + 2 ^ m * regsBits (pre ++ (v' + 1) :: post) t)
                                        have hs2b := hrw2 (ones m + 2 ^ m * regsBits (pre ++ (v' + 1) :: post) t)
                                        have hg2 := gadget_mark_reg k' (r2.length + m) (bitsToNat l2) pre (v' + 1) post t hk' hprelen
                                        have hs3a := hret3s (ones m + 2 ^ m * markedRegsBits pre (v' + 1) post t)
                                        have hs3b := hrw3 (ones m + 2 ^ m * markedRegsBits pre (v' + 1) post t)
                                        have hg4 := gadget_dec_reg_nz (r3.length + m) (bitsToNat l3') pre v' post t
                                        have hsf := hfinnz (m + 1) (pre ++ v' :: post) t
                                        rw [hlen, hr1_0] at hs0; rw [hpl1b, hb1, hlen1'] at hs2a
                                        rw [hr2_1] at hs2b; rw [hpl2b, hb2, hlen2'] at hs3a
                                        rw [hr3_1, hl3_eq] at hs3b; rw [hb3a, hlen3a] at hsf
                                        have heq0 : bitsToNat pref + 2 ^ 42 * (2 ^ m * regsBits (pre ++ (v' + 1) :: post) t) =
                                            bitsToNat pref + 2 ^ (42 + m) * regsBits (pre ++ (v' + 1) :: post) t := by rw [Nat.pow_add, Nat.mul_assoc]
                                        have heq1 : 0 + 2 ^ r1.length * (2 ^ m * regsBits (pre ++ (v' + 1) :: post) t) =
                                            2 ^ (r1.length + m) * (1 + 2 * regsSuffix (pre ++ (v' + 1) :: post) t) := by
                                          rw [Nat.zero_add, Nat.pow_add, Nat.mul_assoc]; rfl
                                        have heq2 : bitsToNat l1 % 2 + 2 * (ones (r1.length + m) + 2 ^ (r1.length + m) * (1 + 2 * regsSuffix (pre ++ (v' + 1) :: post) t)) =
                                            (bitsToNat l1 % 2 + 2 * ones r1.length) + 2 ^ (r1.length + 1) * (ones m + 2 ^ m * regsBits (pre ++ (v' + 1) :: post) t) := by
                                          unfold regsBits; rw [ones_add r1.length m, pow2_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
                                        have heq3 : ones r2.length + 2 ^ r2.length * (ones m + 2 ^ m * regsBits (pre ++ (v' + 1) :: post) t) =
                                            ones (r2.length + m) + 2 ^ (r2.length + m) * regsBits (pre ++ (v' + 1) :: post) t := (ones_add r2.length m _).symm
                                        have heq4 : bitsToNat l2 % 2 + 2 * (ones (r2.length + m) + 2 ^ (r2.length + m) * markedRegsBits pre (v' + 1) post t) =
                                            (bitsToNat l2 % 2 + 2 * ones r2.length) + 2 ^ (r2.length + 1) * (ones m + 2 ^ m * markedRegsBits pre (v' + 1) post t) := by
                                          rw [ones_add r2.length m, pow2_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
                                        have heq5 : ones r3.length + 2 ^ r3.length * (ones m + 2 ^ m * markedRegsBits pre (v' + 1) post t) =
                                            ones (r3.length + m) + 2 ^ (r3.length + m) * markedRegsBits pre (v' + 1) post t := (ones_add r3.length m _).symm
                                        have heq6 : 4 * (ones (r3.length + m + 1) + 2 ^ (r3.length + m + 1) * regsBits (pre ++ v' :: post) t) =
                                            4 * ones r3.length + 2 ^ (r3.length + 2) * (ones (m + 1) + 2 ^ (m + 1) * regsBits (pre ++ v' :: post) t) := by
                                          have hadd : r3.length + m + 1 = r3.length + (m + 1) := by omega
                                          have hp : 4 * 2 ^ r3.length = 2 ^ (r3.length + 2) := by rw [pow2_succ (r3.length + 1), pow2_succ r3.length]; omega
                                          rw [hadd, ones_add r3.length (m + 1), Nat.mul_add, ← Nat.mul_assoc, hp]
                                        rw [heq0, heq1] at hs0; rw [heq2] at hg1; rw [heq3] at hs2b
                                        rw [heq4] at hg2; rw [heq5] at hs3b; rw [heq6] at hg4
                                        exact (((((((hs0.trans hg1).trans hs2a).trans hs2b).trans hg2).trans hs3a).trans hs3b).trans hg4).trans hsf
                                      · intro m rs t hm ht hlenrs hz
                                        obtain ⟨pre, v, post, _, hprelen, rfl⟩ := listSplitAt_of_lt k' rs (by omega)
                                        rw [← hprelen, regGet_append] at hz; subst hz
                                        have hs0 := hrw0 (2 ^ m * regsBits (pre ++ 0 :: post) t)
                                        have hg1 := gadget_fill_and_back (r1.length + m) (bitsToNat l1) (regsSuffix (pre ++ 0 :: post) t) (by omega)
                                        have hs2a := hret2s (ones m + 2 ^ m * regsBits (pre ++ 0 :: post) t)
                                        have hs2b := hrw2 (ones m + 2 ^ m * regsBits (pre ++ 0 :: post) t)
                                        have hg2 := gadget_mark_reg k' (r2.length + m) (bitsToNat l2) pre 0 post t hk' hprelen
                                        have hs3a := hret3s (ones m + 2 ^ m * markedRegsBits pre 0 post t)
                                        have hs3b := hrw3 (ones m + 2 ^ m * markedRegsBits pre 0 post t)
                                        have hg5 := gadget_dec_reg_z (r3.length + m) (bitsToNat l3') pre post t ht
                                        have hsf := hfinz m (pre ++ 0 :: post) t
                                        rw [hlen, hr1_0] at hs0; rw [hpl1b, hb1, hlen1'] at hs2a
                                        rw [hr2_1] at hs2b; rw [hpl2b, hb2, hlen2'] at hs3a
                                        rw [hr3_1, hl3_eq] at hs3b; rw [hpl3b, hb3b, hlen3b] at hsf
                                        have heq0 : bitsToNat pref + 2 ^ 42 * (2 ^ m * regsBits (pre ++ 0 :: post) t) =
                                            bitsToNat pref + 2 ^ (42 + m) * regsBits (pre ++ 0 :: post) t := by rw [Nat.pow_add, Nat.mul_assoc]
                                        have heq1 : 0 + 2 ^ r1.length * (2 ^ m * regsBits (pre ++ 0 :: post) t) =
                                            2 ^ (r1.length + m) * (1 + 2 * regsSuffix (pre ++ 0 :: post) t) := by
                                          rw [Nat.zero_add, Nat.pow_add, Nat.mul_assoc]; rfl
                                        have heq2 : bitsToNat l1 % 2 + 2 * (ones (r1.length + m) + 2 ^ (r1.length + m) * (1 + 2 * regsSuffix (pre ++ 0 :: post) t)) =
                                            (bitsToNat l1 % 2 + 2 * ones r1.length) + 2 ^ (r1.length + 1) * (ones m + 2 ^ m * regsBits (pre ++ 0 :: post) t) := by
                                          unfold regsBits; rw [ones_add r1.length m, pow2_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
                                        have heq3 : ones r2.length + 2 ^ r2.length * (ones m + 2 ^ m * regsBits (pre ++ 0 :: post) t) =
                                            ones (r2.length + m) + 2 ^ (r2.length + m) * regsBits (pre ++ 0 :: post) t := (ones_add r2.length m _).symm
                                        have heq4 : bitsToNat l2 % 2 + 2 * (ones (r2.length + m) + 2 ^ (r2.length + m) * markedRegsBits pre 0 post t) =
                                            (bitsToNat l2 % 2 + 2 * ones r2.length) + 2 ^ (r2.length + 1) * (ones m + 2 ^ m * markedRegsBits pre 0 post t) := by
                                          rw [ones_add r2.length m, pow2_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
                                        have heq5 : ones r3.length + 2 ^ r3.length * (ones m + 2 ^ m * markedRegsBits pre 0 post t) =
                                            ones (r3.length + m) + 2 ^ (r3.length + m) * markedRegsBits pre 0 post t := (ones_add r3.length m _).symm
                                        have heq6 : bitsToNat l3' % 2 + 4 * (ones (r3.length + m + 1) + 2 ^ (r3.length + m + 1) * regsBits (pre ++ 0 :: post) t) =
                                            (bitsToNat l3' % 2 + 4 * ones (r3.length + 1)) + 2 ^ (r3.length + 3) * (ones m + 2 ^ m * regsBits (pre ++ 0 :: post) t) := by
                                          have hadd : r3.length + m + 1 = (r3.length + 1) + m := by omega
                                          have hp : 4 * 2 ^ (r3.length + 1) = 2 ^ (r3.length + 3) := by
                                            rw [pow2_succ (r3.length + 2), pow2_succ (r3.length + 1)]; omega
                                          rw [hadd, ones_add (r3.length + 1) m, Nat.mul_add, ← Nat.mul_assoc, hp, Nat.add_assoc]
                                        rw [heq0, heq1] at hs0; rw [heq2] at hg1; rw [heq3] at hs2b
                                        rw [heq4] at hg2; rw [heq5] at hs3b; rw [heq6] at hg5
                                        exact (((((((hs0.trans hg1).trans hs2a).trans hs2b).trans hg2).trans hs3a).trans hs3b).trans hg5).trans hsf
                                · contradiction
    · cases hg : runBits _ 150 q1 l1 r1 <;> rw [hg] at h; · contradiction
      rename_i resg; rcases resg with ⟨qg, lg, rg⟩; dsimp only at h
      split at h
      · cases hc : isOneBits lg && Nat.beq rg.length 42 <;> rw [hc] at h <;> contradiction
      · split at h
        · cases hfg : allFalse rg <;> rw [hfg] at h <;> dsimp only at h
          · cases h5 : runBits _ 150 7 lg rg <;> rw [h5] at h; · contradiction
            rename_i res5; rcases res5 with ⟨q5, l5, r5⟩; dsimp only at h
            cases hc : isOneBits l5 && Nat.beq r5.length 42 <;> rw [hc] at h <;> contradiction
          · cases h5 : returnTo74From2 _ _ <;> rw [h5] at h; · contradiction
            rename_i res5; rcases res5 with ⟨l5, r5⟩; dsimp only at h
            cases hc : isOneBits l5 && Nat.beq r5.length 42 <;> rw [hc] at h <;> contradiction
        · contradiction

private theorem resolveGoto_sound : ∀ fuel p, p.length = 42 →
    (resolveGoto fuel p).length = 42 ∧
    ∀ m rs t, SafeReach (frameBits p m rs t) (frameBits (resolveGoto fuel p) m rs t)
  | 0, _, hlen => ⟨hlen, fun _ _ _ => SafeReach.refl _⟩
  | fuel + 1, p, hlen => by
    unfold resolveGoto
    cases h : decodeLBits p with
    | goto p' =>
      obtain ⟨hlen', hs⟩ := decodeLBits_sound_goto p p' h hlen
      obtain ⟨hlen'', hr⟩ := resolveGoto_sound fuel p' hlen'
      exact ⟨hlen'', fun m rs t => (hs m rs t).of_pos.trans (hr m rs t)⟩
    | inc _ _ => exact ⟨hlen, fun _ _ _ => SafeReach.refl _⟩
    | dec _ _ _ => exact ⟨hlen, fun _ _ _ => SafeReach.refl _⟩
    | halt => exact ⟨hlen, fun _ _ _ => SafeReach.refl _⟩
    | fail => exact ⟨hlen, fun _ _ _ => SafeReach.refl _⟩

private theorem reachesGoto_sound : ∀ fuel a b, reachesGoto fuel a b = true → a.length = 42 →
    b.length = 42 ∧
    ∀ m rs t, SafeReach (frameBits a m rs t) (frameBits b m rs t)
  | 0, a, b, h, hlen => by
    have hab := beqBits_sound a b h; subst hab
    exact ⟨hlen, fun _ _ _ => SafeReach.refl _⟩
  | fuel + 1, a, b, h, hlen => by
    unfold reachesGoto at h
    cases hb : beqBits a b with
    | true =>
      have hab := beqBits_sound a b hb; subst hab
      exact ⟨hlen, fun _ _ _ => SafeReach.refl _⟩
    | false =>
      rw [hb] at h; dsimp only at h
      cases hd : decodeLBits a with
      | goto a' =>
        rw [hd] at h
        obtain ⟨hlen', hs⟩ := decodeLBits_sound_goto a a' hd hlen
        obtain ⟨hlenb, hr⟩ := reachesGoto_sound fuel a' b h hlen'
        exact ⟨hlenb, fun m rs t => (hs m rs t).of_pos.trans (hr m rs t)⟩
      | inc _ _ => rw [hd] at h; contradiction
      | dec _ _ _ => rw [hd] at h; contradiction
      | halt => rw [hd] at h; contradiction
      | fail => rw [hd] at h; contradiction

private theorem resolveStep_sound_inc : ∀ fuel p p0 k pn,
    resolveStep fuel p = some (p0, .inc k pn) → p.length = 42 →
    k < 9 ∧ p0.length = 42 ∧ pn.length = 42 ∧
    (∀ m rs t, SafeReach (frameBits p m rs t) (frameBits p0 m rs t)) ∧
    (∀ m rs t, 1 ≤ m → rs.length = 9 →
      SafeReachPos (frameBits p0 m rs t) (frameBits pn m (regSet k (regGet k rs + 1) rs) (t + 1)))
  | 0, _, _, _, _, h, _ => by simp [resolveStep] at h
  | fuel + 1, p, p0, k, pn, h, hlen => by
    unfold resolveStep at h
    cases hd : decodeLBits p with
    | goto p' =>
      rw [hd] at h
      obtain ⟨hlen', hg⟩ := decodeLBits_sound_goto p p' hd hlen
      obtain ⟨hk, hl0, hln, hreach0, hinc⟩ := resolveStep_sound_inc fuel p' p0 k pn h hlen'
      exact ⟨hk, hl0, hln, fun m rs t => (hg m rs t).of_pos.trans (hreach0 m rs t), hinc⟩
    | inc k' pn' =>
      rw [hd] at h; injection h with h1
      have : p0 = p ∧ k = k' ∧ pn = pn' := by cases h1; exact ⟨rfl, rfl, rfl⟩
      rcases this with ⟨rfl, rfl, rfl⟩
      obtain ⟨hk, hln, hinc⟩ := decodeLBits_sound_inc p0 k pn hd hlen
      exact ⟨hk, hlen, hln, fun _ _ _ => SafeReach.refl _, hinc⟩
    | dec _ _ _ => rw [hd] at h; simp at h
    | halt => rw [hd] at h; simp at h
    | fail => rw [hd] at h; simp at h

private theorem resolveStep_sound_dec : ∀ fuel p p0 k pnz pz,
    resolveStep fuel p = some (p0, .dec k pnz pz) → p.length = 42 →
    k < 9 ∧ p0.length = 42 ∧ pnz.length = 42 ∧ pz.length = 42 ∧
    (∀ m rs t, SafeReach (frameBits p m rs t) (frameBits p0 m rs t)) ∧
    (∀ m rs t, 1 ≤ m → rs.length = 9 → 0 < regGet k rs →
      SafeReachPos (frameBits p0 m rs t) (frameBits pnz (m + 1) (regSet k (regGet k rs - 1) rs) t)) ∧
    (∀ m rs t, 1 ≤ m → 1 ≤ t → rs.length = 9 → regGet k rs = 0 →
      SafeReachPos (frameBits p0 m rs t) (frameBits pz m rs t))
  | 0, _, _, _, _, _, h, _ => by simp [resolveStep] at h
  | fuel + 1, p, p0, k, pnz, pz, h, hlen => by
    unfold resolveStep at h
    cases hd : decodeLBits p with
    | goto p' =>
      rw [hd] at h
      obtain ⟨hlen', hg⟩ := decodeLBits_sound_goto p p' hd hlen
      obtain ⟨hk, hl0, hlnz, hlz, hreach0, hnz, hz⟩ := resolveStep_sound_dec fuel p' p0 k pnz pz h hlen'
      exact ⟨hk, hl0, hlnz, hlz, fun m rs t => (hg m rs t).of_pos.trans (hreach0 m rs t), hnz, hz⟩
    | dec k' pnz' pz' =>
      rw [hd] at h; injection h with h1
      have : p0 = p ∧ k = k' ∧ pnz = pnz' ∧ pz = pz' := by cases h1; exact ⟨rfl, rfl, rfl, rfl⟩
      rcases this with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨hk, hlnz, hlz, hnz, hz⟩ := decodeLBits_sound_dec p0 k pnz pz hd hlen
      exact ⟨hk, hlen, hlnz, hlz, fun _ _ _ => SafeReach.refl _, hnz, hz⟩
    | inc _ _ => rw [hd] at h; simp at h
    | halt => rw [hd] at h; simp at h
    | fail => rw [hd] at h; simp at h

/-! ### 4. Abstract Register Machine, Macro Verification & Soundness Invariant -/

private def unpairAux : Nat → Nat → Nat → Nat × Nat
  | 0, s, n => (s - n, n)
  | fuel + 1, s, n =>
    if n ≤ s then (s - n, n) else unpairAux fuel (s + 1) (n - (s + 1))

private def unpair (n : Nat) : Nat × Nat := unpairAux n 0 n

private theorem tri_step (s : Nat) : (s + 1) * (s + 1 + 1) / 2 = s * (s + 1) / 2 + (s + 1) := by
  have hmul : (s + 1) * (s + 1 + 1) = s * (s + 1) + 2 * (s + 1) := by
    have h1 : (s + 1) * (s + 1 + 1) = (s + 1) * s + (s + 1) * 2 := Nat.mul_add (s + 1) s 2
    have h2 : (s + 1) * s = s * (s + 1) := Nat.mul_comm (s + 1) s
    omega
  omega

private theorem unpairAux_spec : ∀ fuel s n,
    (∀ a b, n + s * (s + 1) / 2 = cantor a b → a + b ≥ s → a + b ≤ s + fuel →
      unpairAux fuel s n = (a, b))
  | 0, s, n, a, b, heq, hge, hle => by
    have hab : a + b = s := by omega
    have hns : n = b := by unfold cantor at heq; rw [hab] at heq; omega
    simp [unpairAux, hns, show s - b = a by omega]
  | fuel + 1, s, n, a, b, heq, hge, hle => by
    unfold unpairAux
    by_cases h : n ≤ s
    · have hab : a + b = s := by
        apply Classical.byContradiction
        intro hne
        have hgt : a + b ≥ s + 1 := by omega
        unfold cantor at heq
        have htri : (a + b) * (a + b + 1) / 2 ≥ (s + 1) * (s + 1 + 1) / 2 := by
          apply Nat.div_le_div_right
          exact Nat.mul_le_mul hgt (Nat.succ_le_succ hgt)
        have hstep := tri_step s
        omega
      have hnb : n = b := by unfold cantor at heq; rw [hab] at heq; omega
      rw [if_pos h, hnb, show s - b = a by omega]
    · rw [if_neg h]
      have hgt : a + b ≥ s + 1 := by
        apply Classical.byContradiction
        intro hlt
        have hab : a + b = s := by omega
        unfold cantor at heq; rw [hab] at heq; omega
      apply unpairAux_spec fuel (s + 1) (n - (s + 1)) a b _ hgt (by omega)
      have hstep := tri_step s
      omega

private theorem cantor_ge_sum (a b : Nat) : a + b ≤ cantor a b := by
  unfold cantor
  cases h : a + b with
  | zero => omega
  | succ k =>
    have hmul : (k + 1) * (k + 1 + 1) ≥ 2 * (k + 1) := by
      have hle : 2 ≤ k + 1 + 1 := by omega
      have := Nat.mul_le_mul_left (k + 1) hle
      omega
    omega

private theorem unpair_cantor (a b : Nat) : unpair (cantor a b) = (a, b) := by
  apply unpairAux_spec (cantor a b) 0 (cantor a b) a b
  · simp
  · omega
  · simpa using cantor_ge_sum a b

/-! #### 4.1 Register Reachability & Register Update Algebra -/

private def RegReach (p1 : List Bool) (rs1 : List Nat) (p2 : List Bool) (rs2 : List Nat) : Prop :=
  ∀ m t, 1 ≤ m → 1 ≤ t → ∃ m' t', 1 ≤ m' ∧ 1 ≤ t' ∧ SafeReach (frameBits p1 m rs1 t) (frameBits p2 m' rs2 t')

private def RegReachPos (p1 : List Bool) (rs1 : List Nat) (p2 : List Bool) (rs2 : List Nat) : Prop :=
  ∀ m t, 1 ≤ m → 1 ≤ t → ∃ m' t', 1 ≤ m' ∧ 1 ≤ t' ∧ SafeReachPos (frameBits p1 m rs1 t) (frameBits p2 m' rs2 t')

private theorem RegReach.refl (p : List Bool) (rs : List Nat) : RegReach p rs p rs :=
  fun m t hm ht => ⟨m, t, hm, ht, SafeReach.refl _⟩

private theorem RegReachPos.of_pos {p1 p2 : List Bool} {rs1 rs2 : List Nat}
    (h : RegReachPos p1 rs1 p2 rs2) : RegReach p1 rs1 p2 rs2 :=
  fun m t hm ht => let ⟨m', t', hm', ht', hr⟩ := h m t hm ht; ⟨m', t', hm', ht', hr.of_pos⟩

private theorem RegReach.trans {p1 p2 p3 : List Bool} {rs1 rs2 rs3 : List Nat}
    (h1 : RegReach p1 rs1 p2 rs2) (h2 : RegReach p2 rs2 p3 rs3) : RegReach p1 rs1 p3 rs3 :=
  fun m t hm ht =>
    let ⟨m1, t1, hm1, ht1, r1⟩ := h1 m t hm ht
    let ⟨m2, t2, hm2, ht2, r2⟩ := h2 m1 t1 hm1 ht1
    ⟨m2, t2, hm2, ht2, r1.trans r2⟩

private theorem RegReachPos.trans {p1 p2 p3 : List Bool} {rs1 rs2 rs3 : List Nat}
    (h1 : RegReachPos p1 rs1 p2 rs2) (h2 : RegReach p2 rs2 p3 rs3) : RegReachPos p1 rs1 p3 rs3 :=
  fun m t hm ht =>
    let ⟨m1, t1, hm1, ht1, r1⟩ := h1 m t hm ht
    let ⟨m2, t2, hm2, ht2, r2⟩ := h2 m1 t1 hm1 ht1
    ⟨m2, t2, hm2, ht2, r1.trans r2⟩

private theorem RegReach.trans_pos {p1 p2 p3 : List Bool} {rs1 rs2 rs3 : List Nat}
    (h1 : RegReach p1 rs1 p2 rs2) (h2 : RegReachPos p2 rs2 p3 rs3) : RegReachPos p1 rs1 p3 rs3 :=
  fun m t hm ht =>
    let ⟨m1, t1, hm1, ht1, r1⟩ := h1 m t hm ht
    let ⟨m2, t2, hm2, ht2, r2⟩ := h2 m1 t1 hm1 ht1
    ⟨m2, t2, hm2, ht2, r1.trans_pos r2⟩

private theorem regGet_regSet_same : ∀ k v rs, k < rs.length → regGet k (regSet k v rs) = v
  | _, _, [], h => by simp at h
  | 0, _, _ :: _, _ => rfl
  | k + 1, v, _ :: vs, h => by
    simp only [regSet, regGet, List.getD]
    exact regGet_regSet_same k v vs (by simp at h; omega)

private theorem regGet_zero (x : Nat) (xs : List Nat) : regGet 0 (x :: xs) = x := rfl
private theorem regGet_succ (k x : Nat) (xs : List Nat) : regGet (k + 1) (x :: xs) = regGet k xs := rfl

private theorem regGet_regSet_ne : ∀ k j v rs, k ≠ j → regGet k (regSet j v rs) = regGet k rs
  | _, _, _, [], _ => by simp [regSet]
  | 0, 0, _, _ :: _, h => absurd rfl h
  | 0, _ + 1, _, _ :: _, _ => rfl
  | _ + 1, 0, _, _ :: _, _ => rfl
  | k + 1, j + 1, v, _ :: vs, h => by
    simp only [regSet, regGet, List.getD]
    exact regGet_regSet_ne k j v vs (by omega)

private theorem regSet_regSet_same : ∀ k v1 v2 rs, regSet k v2 (regSet k v1 rs) = regSet k v2 rs
  | _, _, _, [] => by simp [regSet]
  | 0, _, _, _ :: _ => rfl
  | k + 1, v1, v2, _ :: vs => by simp [regSet, regSet_regSet_same k v1 v2 vs]

private theorem regSet_regSet_comm : ∀ k j v1 v2 rs, k ≠ j →
    regSet k v1 (regSet j v2 rs) = regSet j v2 (regSet k v1 rs)
  | _, _, _, _, [], _ => by simp [regSet]
  | 0, 0, _, _, _ :: _, h => absurd rfl h
  | 0, _ + 1, _, _, _ :: _, _ => rfl
  | _ + 1, 0, _, _, _ :: _, _ => rfl
  | k + 1, j + 1, v1, v2, _ :: vs, h => by
    simp [regSet, regSet_regSet_comm k j v1 v2 vs (by omega)]

private theorem regSet_get_self : ∀ k rs, k < rs.length → regSet k (regGet k rs) rs = rs
  | _, [], h => by simp at h
  | 0, _ :: _, _ => rfl
  | k + 1, _ :: vs, h => by
    simp only [regSet, regGet, List.getD]
    exact congrArg (_ :: ·) (regSet_get_self k vs (by simp at h; omega))

private theorem regReach_goto {a b : List Bool} (h : reachesGoto 25 a b = true) (hl : a.length = 42)
    (rs : List Nat) : RegReach a rs b rs := by
  obtain ⟨_, hr⟩ := reachesGoto_sound 25 a b h hl
  intro m t hm ht
  exact ⟨m, t, hm, ht, hr m rs t⟩

private theorem regReach_resolveGoto (p : List Bool) (hl : p.length = 42) (rs : List Nat) :
    RegReach p rs (resolveGoto 25 p) rs := by
  obtain ⟨_, hr⟩ := resolveGoto_sound 25 p hl
  intro m t hm ht
  exact ⟨m, t, hm, ht, hr m rs t⟩

private theorem regReach_inc {p p0 : List Bool} {k : Nat} {pn : List Bool}
    (h : resolveStep 25 p = some (p0, .inc k pn)) (hl : p.length = 42)
    (rs : List Nat) (hlen : rs.length = 9) :
    RegReachPos p rs pn (regSet k (regGet k rs + 1) rs) := by
  obtain ⟨_, _, _, hr0, hstep⟩ := resolveStep_sound_inc 25 p p0 k pn h hl
  intro m t hm ht
  exact ⟨m, t + 1, hm, by omega, (hr0 m rs t).trans_pos (hstep m rs t hm hlen)⟩

private theorem regReach_dec_p0 {p p0 : List Bool} {k : Nat} {pnz pz : List Bool}
    (h : resolveStep 25 p = some (p0, .dec k pnz pz)) (hl : p.length = 42) (rs : List Nat) :
    RegReach p rs p0 rs := by
  obtain ⟨_, _, _, _, hr0, _, _⟩ := resolveStep_sound_dec 25 p p0 k pnz pz h hl
  intro m t hm ht
  exact ⟨m, t, hm, ht, hr0 m rs t⟩

private theorem regReach_dec_nz0 {p p0 : List Bool} {k : Nat} {pnz pz : List Bool}
    (h : resolveStep 25 p = some (p0, .dec k pnz pz)) (hl : p.length = 42)
    (rs : List Nat) (hlen : rs.length = 9) (hpos : 0 < regGet k rs) :
    RegReachPos p0 rs pnz (regSet k (regGet k rs - 1) rs) := by
  obtain ⟨_, _, _, _, _, hnz, _⟩ := resolveStep_sound_dec 25 p p0 k pnz pz h hl
  intro m t hm ht
  exact ⟨m + 1, t, by omega, ht, hnz m rs t hm hlen hpos⟩

private theorem regReach_dec_z0 {p p0 : List Bool} {k : Nat} {pnz pz : List Bool}
    (h : resolveStep 25 p = some (p0, .dec k pnz pz)) (hl : p.length = 42)
    (rs : List Nat) (hlen : rs.length = 9) (hz : regGet k rs = 0) :
    RegReachPos p0 rs pz rs := by
  obtain ⟨_, _, _, _, _, _, hzero⟩ := resolveStep_sound_dec 25 p p0 k pnz pz h hl
  intro m t hm ht
  exact ⟨m, t, hm, ht, hzero m rs t hm ht hlen hz⟩

private theorem regReach_dec_nz {p p0 : List Bool} {k : Nat} {pnz pz : List Bool}
    (h : resolveStep 25 p = some (p0, .dec k pnz pz)) (hl : p.length = 42)
    (rs : List Nat) (hlen : rs.length = 9) (hpos : 0 < regGet k rs) :
    RegReachPos p rs pnz (regSet k (regGet k rs - 1) rs) :=
  (regReach_dec_p0 h hl rs).trans_pos (regReach_dec_nz0 h hl rs hlen hpos)

private theorem regReach_dec_z {p p0 : List Bool} {k : Nat} {pnz pz : List Bool}
    (h : resolveStep 25 p = some (p0, .dec k pnz pz)) (hl : p.length = 42)
    (rs : List Nat) (hlen : rs.length = 9) (hz : regGet k rs = 0) :
    RegReachPos p rs pz rs :=
  (regReach_dec_p0 h hl rs).trans_pos (regReach_dec_z0 h hl rs hlen hz)

/-! #### 4.2 Macro Soundness Theorems -/

private theorem chkInc_sound {p pn : List Bool} {r : Nat} (h : chkInc p r = some pn) (hl : p.length = 42) :
    r < 9 ∧ pn.length = 42 ∧
    ∀ rs, rs.length = 9 → RegReachPos p rs pn (regSet r (regGet r rs + 1) rs) := by
  unfold chkInc at h
  cases hs : resolveStep 25 p with
  | none => rw [hs] at h; simp at h
  | some res =>
    rcases res with ⟨p0, ins⟩
    cases ins with
    | dec _ _ _ => rw [hs] at h; simp at h
    | inc k pn' =>
      rw [hs] at h; dsimp only at h
      split at h
      · rename_i hkr; injection h with hpn; subst hpn
        have hk : k = r := Nat.eq_of_beq_eq_true hkr; subst hk
        obtain ⟨hr, _, hln, _, _⟩ := resolveStep_sound_inc 25 p p0 k pn' hs hl
        exact ⟨hr, hln, fun rs hlen => regReach_inc hs hl rs hlen⟩
      · contradiction

private theorem chkIncN_sound : ∀ k (p : List Bool) r (pn : List Bool), chkIncN k p r = some pn → p.length = 42 →
    pn.length = 42 ∧
    ∀ rs, rs.length = 9 → RegReach p rs pn (regSet r (regGet r rs + k) rs)
  | 0, p, r, pn, h, hl => by
    unfold chkIncN at h; injection h with he; subst he
    refine ⟨hl, fun rs hlen => ?_⟩
    by_cases hr : r < 9
    · rw [Nat.add_zero, regSet_get_self r rs (by omega)]; exact RegReach.refl _ _
    · have hge : rs.length ≤ r := by omega
      have hnoop : ∀ k v l, l.length ≤ k → regSet k v l = l := by
        intro k v l; induction l generalizing k with
        | nil => intro _; simp [regSet]
        | cons _ _ ih => cases k with | zero => intro h; simp at h | succ k' => intro h; simp [regSet, ih k' (by simp at h; omega)]
      rw [hnoop r _ rs hge]; exact RegReach.refl _ _
  | k + 1, p, r, pn, h, hl => by
    unfold chkIncN at h
    cases h1 : chkInc p r with
    | none => rw [h1] at h; simp at h
    | some p1 =>
      rw [h1] at h; dsimp only at h
      obtain ⟨hr, hl1, hs1⟩ := chkInc_sound h1 hl
      obtain ⟨hln, hsn⟩ := chkIncN_sound k p1 r pn h hl1
      refine ⟨hln, fun rs hlen => ?_⟩
      have r1 := (hs1 rs hlen).of_pos
      have r2 := hsn (regSet r (regGet r rs + 1) rs) (by rw [regSet_length]; exact hlen)
      rw [regGet_regSet_same r _ rs (by omega), regSet_regSet_same,
          show regGet r rs + 1 + k = regGet r rs + (k + 1) by omega] at r2
      exact r1.trans r2

private theorem chkZero_sound {p pz : List Bool} {r : Nat} (h : chkZero p r = some pz) (hl : p.length = 42) :
    r < 9 ∧ pz.length = 42 ∧
    ∀ rs, rs.length = 9 → RegReachPos p rs pz (regSet r 0 rs) := by
  unfold chkZero at h
  cases hs : resolveStep 25 p with
  | none => rw [hs] at h; simp at h
  | some res =>
    rcases res with ⟨p0, ins⟩
    cases ins with
    | inc _ _ => rw [hs] at h; simp at h
    | dec k pnz pz' =>
      rw [hs] at h; dsimp only at h
      split at h
      · rename_i hcond; injection h with hpz; subst hpz
        have ⟨hkr, hpnz⟩ := Bool.and_eq_true_iff.mp hcond
        have hk : k = r := Nat.eq_of_beq_eq_true hkr; subst hk
        obtain ⟨hr, _, hlnz, hlz, _, _, _⟩ := resolveStep_sound_dec 25 p p0 k pnz pz' hs hl
        refine ⟨hr, hlz, fun rs hlen => ?_⟩
        suffices ∀ v rs, rs.length = 9 → regGet k rs = v → RegReachPos p0 rs pz' (regSet k 0 rs) from
          (regReach_dec_p0 hs hl rs).trans_pos (this (regGet k rs) rs hlen rfl)
        intro v; induction v with
        | zero =>
          intro rs hlen hv
          have hz := regReach_dec_z0 hs hl rs hlen hv
          have heq : regSet k 0 rs = rs := by rw [← hv, regSet_get_self k rs (by omega)]
          rw [heq]; exact hz
        | succ v' ih =>
          intro rs hlen hv
          have hnz := regReach_dec_nz0 hs hl rs hlen (by omega)
          have hsub : regGet k rs - 1 = v' := by omega
          rw [hsub] at hnz
          have hg := regReach_goto hpnz hlnz (regSet k v' rs)
          have hr2 := ih (regSet k v' rs) (by rw [regSet_length]; exact hlen) (regGet_regSet_same k v' rs (by omega))
          rw [regSet_regSet_same] at hr2
          exact (hnz.trans hg).trans hr2.of_pos
      · contradiction

private theorem chkMove_sound {p pz : List Bool} {dst src : Nat} (hne : dst ≠ src)
    (h : chkMove p dst src = some pz) (hl : p.length = 42) :
    dst < 9 ∧ src < 9 ∧ pz.length = 42 ∧
    ∀ rs, rs.length = 9 →
      RegReachPos p rs pz (regSet src 0 (regSet dst (regGet dst rs + regGet src rs) rs)) := by
  unfold chkMove at h
  cases hs : resolveStep 25 p with
  | none => rw [hs] at h; simp at h
  | some res =>
    rcases res with ⟨p0, ins⟩
    cases ins with
    | inc _ _ => rw [hs] at h; simp at h
    | dec k pnz pz' =>
      rw [hs] at h; dsimp only at h
      split at h
      · rename_i hks
        have hk : k = src := Nat.eq_of_beq_eq_true hks; subst hk
        cases hi : chkInc pnz dst with
        | none => rw [hi] at h; simp at h
        | some p2 =>
          rw [hi] at h; dsimp only at h
          split at h
          · rename_i hp2; injection h with hpz; subst hpz
            obtain ⟨hsrc, _, hlnz, hlz, _, _, _⟩ := resolveStep_sound_dec 25 p p0 k pnz pz' hs hl
            obtain ⟨hdst, hl2, hinc⟩ := chkInc_sound hi hlnz
            refine ⟨hdst, hsrc, hlz, fun rs hlen => ?_⟩
            suffices ∀ v rs, rs.length = 9 → regGet k rs = v →
                RegReachPos p0 rs pz' (regSet k 0 (regSet dst (regGet dst rs + v) rs)) from
              (regReach_dec_p0 hs hl rs).trans_pos (this (regGet k rs) rs hlen rfl)
            intro v; induction v with
            | zero =>
              intro rs hlen hv
              have hz := regReach_dec_z0 hs hl rs hlen hv
              rw [Nat.add_zero, regSet_get_self dst rs (by omega), ← hv, regSet_get_self k rs (by omega)]
              exact hz
            | succ v' ih =>
              intro rs hlen hv
              have hnz := regReach_dec_nz0 hs hl rs hlen (by omega)
              rw [show regGet k rs - 1 = v' by omega] at hnz
              let rs1 := regSet k v' rs
              have hlen1 : rs1.length = 9 := by rw [regSet_length]; exact hlen
              have r2 := hinc rs1 hlen1
              let rs2 := regSet dst (regGet dst rs1 + 1) rs1
              have hlen2 : rs2.length = 9 := by rw [regSet_length]; exact hlen1
              have rg := regReach_goto hp2 hl2 rs2
              have hget_k : regGet k rs2 = v' := by
                rw [regGet_regSet_ne k dst _ rs1 (Ne.symm hne), regGet_regSet_same k v' rs (by omega)]
              have hget_d : regGet dst rs2 = regGet dst rs + 1 := by
                rw [regGet_regSet_same dst _ rs1 (by omega), regGet_regSet_ne dst k v' rs hne]
              have r3 := ih rs2 hlen2 hget_k
              have hnorm : regSet k 0 (regSet dst (regGet dst rs2 + v') rs2) =
                  regSet k 0 (regSet dst (regGet dst rs + (v' + 1)) rs) := by
                rw [hget_d, show regGet dst rs + 1 + v' = regGet dst rs + (v' + 1) by omega]
                dsimp only [rs2, rs1]
                rw [regSet_regSet_same, regSet_regSet_comm dst k _ v' rs hne,
                    regSet_regSet_comm k dst 0 _ _ (Ne.symm hne), regSet_regSet_same,
                    regSet_regSet_comm dst k _ 0 rs hne]
              rw [hnorm] at r3
              exact ((hnz.trans r2.of_pos).trans rg).trans r3.of_pos
          · contradiction
      · contradiction

private theorem chkLin2_sound {p pz : List Bool} {src d1 d2 : Nat}
    (h1 : d1 ≠ src) (h2 : d2 ≠ src) (h12 : d1 ≠ d2)
    (h : chkLin2 p src d1 d2 = some pz) (hl : p.length = 42) :
    src < 9 ∧ d1 < 9 ∧ d2 < 9 ∧ pz.length = 42 ∧
    ∀ rs, rs.length = 9 →
      RegReachPos p rs pz
        (regSet src 0 (regSet d2 (regGet d2 rs + regGet src rs) (regSet d1 (regGet d1 rs + regGet src rs) rs))) := by
  unfold chkLin2 at h
  cases hs : resolveStep 25 p with
  | none => rw [hs] at h; simp at h
  | some res =>
    rcases res with ⟨p0, ins⟩
    cases ins with
    | inc _ _ => rw [hs] at h; simp at h
    | dec k pnz pz' =>
      rw [hs] at h; dsimp only at h
      split at h
      · rename_i hks
        have hk : k = src := Nat.eq_of_beq_eq_true hks; subst hk
        obtain ⟨hsrc, _, hlnz, hlz, _, _, _⟩ := resolveStep_sound_dec 25 p p0 k pnz pz' hs hl
        cases hs1 : resolveStep 25 pnz with
        | none => rw [hs1] at h; simp at h
        | some res1 =>
          rcases res1 with ⟨p1_0, ins1⟩
          cases ins1 with
          | dec _ _ _ => rw [hs1] at h; simp at h
          | inc k1 p1 =>
            rw [hs1] at h; dsimp only at h
            obtain ⟨hk1, _, hl1, _, _⟩ := resolveStep_sound_inc 25 pnz p1_0 k1 p1 hs1 hlnz
            have hbody : d1 < 9 ∧ d2 < 9 ∧ pz = pz' ∧
                ∀ rs1, rs1.length = 9 →
                  RegReachPos pnz rs1 p0 (regSet d2 (regGet d2 rs1 + 1) (regSet d1 (regGet d1 rs1 + 1) rs1)) := by
              split at h
              · rename_i hk1d1
                have he1 : k1 = d1 := Nat.eq_of_beq_eq_true hk1d1; subst he1
                cases hb : chkInc p1 d2 with
                | none => rw [hb] at h; simp at h
                | some p2 =>
                  rw [hb] at h; dsimp only at h
                  split at h
                  · rename_i hp2; injection h with hpz
                    obtain ⟨hd2, hl2, hib⟩ := chkInc_sound hb hl1
                    refine ⟨hk1, hd2, hpz.symm, fun rs1 hlen1 => ?_⟩
                    have r1 := regReach_inc hs1 hlnz rs1 hlen1
                    have r2 := hib (regSet k1 (regGet k1 rs1 + 1) rs1) (by rw [regSet_length]; exact hlen1)
                    rw [regGet_regSet_ne d2 k1 _ rs1 (Ne.symm h12)] at r2
                    have rg := regReach_goto hp2 hl2 (regSet d2 (regGet d2 rs1 + 1) (regSet k1 (regGet k1 rs1 + 1) rs1))
                    exact (r1.trans r2.of_pos).trans rg
                  · contradiction
              · split at h
                · rename_i _ hk1d2
                  have he2 : k1 = d2 := Nat.eq_of_beq_eq_true hk1d2; subst he2
                  cases hb : chkInc p1 d1 with
                  | none => rw [hb] at h; simp at h
                  | some p2 =>
                    rw [hb] at h; dsimp only at h
                    split at h
                    · rename_i hp2; injection h with hpz
                      obtain ⟨hd1, hl2, hib⟩ := chkInc_sound hb hl1
                      refine ⟨hd1, hk1, hpz.symm, fun rs1 hlen1 => ?_⟩
                      have r1 := regReach_inc hs1 hlnz rs1 hlen1
                      have r2 := hib (regSet k1 (regGet k1 rs1 + 1) rs1) (by rw [regSet_length]; exact hlen1)
                      rw [regGet_regSet_ne d1 k1 _ rs1 h12] at r2
                      have rg := regReach_goto hp2 hl2 (regSet d1 (regGet d1 rs1 + 1) (regSet k1 (regGet k1 rs1 + 1) rs1))
                      have r12 := (r1.trans r2.of_pos).trans rg
                      rw [regSet_regSet_comm d1 k1 _ _ rs1 h12] at r12
                      exact r12
                    · contradiction
                · contradiction
            obtain ⟨hd1, hd2, rfl, hstepBody⟩ := hbody
            refine ⟨hsrc, hd1, hd2, hlz, fun rs hlen => ?_⟩
            suffices ∀ v rs, rs.length = 9 → regGet k rs = v →
                RegReachPos p0 rs pz (regSet k 0 (regSet d2 (regGet d2 rs + v) (regSet d1 (regGet d1 rs + v) rs))) from
              (regReach_dec_p0 hs hl rs).trans_pos (this (regGet k rs) rs hlen rfl)
            intro v; induction v with
            | zero =>
              intro rs hlen hv
              have hz := regReach_dec_z0 hs hl rs hlen hv
              rw [Nat.add_zero, Nat.add_zero, regSet_get_self d1 rs (by omega),
                  regSet_get_self d2 rs (by omega), ← hv, regSet_get_self k rs (by omega)]
              exact hz
            | succ v' ih =>
              intro rs hlen hv
              have hnz := regReach_dec_nz0 hs hl rs hlen (by omega)
              rw [show regGet k rs - 1 = v' by omega] at hnz
              let rs1 := regSet k v' rs
              have hlen1 : rs1.length = 9 := by rw [regSet_length]; exact hlen
              have r2 := hstepBody rs1 hlen1
              let rs2 := regSet d2 (regGet d2 rs1 + 1) (regSet d1 (regGet d1 rs1 + 1) rs1)
              have hlen2 : rs2.length = 9 := by rw [regSet_length, regSet_length]; exact hlen1
              have hgk : regGet k rs2 = v' := by
                rw [regGet_regSet_ne k d2 _ _ (Ne.symm h2), regGet_regSet_ne k d1 _ _ (Ne.symm h1),
                    regGet_regSet_same k v' rs (by omega)]
              have hgd1 : regGet d1 rs2 = regGet d1 rs + 1 := by
                rw [regGet_regSet_ne d1 d2 _ _ h12, regGet_regSet_same d1 _ rs1 (by omega),
                    regGet_regSet_ne d1 k v' rs h1]
              have hgd2 : regGet d2 rs2 = regGet d2 rs + 1 := by
                rw [regGet_regSet_same d2 _ _ (by rw [regSet_length]; omega),
                    regGet_regSet_ne d2 k v' rs h2]
              have r3 := ih rs2 hlen2 hgk
              have hnorm : regSet k 0 (regSet d2 (regGet d2 rs2 + v') (regSet d1 (regGet d1 rs2 + v') rs2)) =
                  regSet k 0 (regSet d2 (regGet d2 rs + (v' + 1)) (regSet d1 (regGet d1 rs + (v' + 1)) rs)) := by
                rw [hgd1, hgd2, show regGet d1 rs + 1 + v' = regGet d1 rs + (v' + 1) by omega,
                    show regGet d2 rs + 1 + v' = regGet d2 rs + (v' + 1) by omega]
                dsimp only [rs2, rs1]
                rw [regSet_regSet_comm d1 d2 _ _ _ h12, regSet_regSet_same d1,
                    regSet_regSet_same d2,
                    regSet_regSet_comm d1 k _ v' rs h1, regSet_regSet_comm d2 k _ v' _ h2,
                    regSet_regSet_same k]
              rw [hnorm] at r3
              exact (hnz.trans r2.of_pos).trans r3.of_pos
      · contradiction

private theorem chkLin4_sound {p pz : List Bool} {dst src : Nat} (hne : dst ≠ src) (hdst : dst < 9)
    (h : chkLin4 p dst src = some pz) (hl : p.length = 42) :
    src < 9 ∧ pz.length = 42 ∧
    ∀ rs, rs.length = 9 →
      RegReachPos p rs pz (regSet src 0 (regSet dst (regGet dst rs + 4 * regGet src rs) rs)) := by
  unfold chkLin4 at h
  cases hs : resolveStep 25 p with
  | none => rw [hs] at h; simp at h
  | some res =>
    rcases res with ⟨p0, ins⟩
    cases ins with
    | inc _ _ => rw [hs] at h; simp at h
    | dec k pnz pz' =>
      rw [hs] at h; dsimp only at h
      split at h
      · rename_i hks
        have hk : k = src := Nat.eq_of_beq_eq_true hks; subst hk
        cases hi : chkIncN 4 pnz dst with
        | none => rw [hi] at h; simp at h
        | some p2 =>
          rw [hi] at h; dsimp only at h
          split at h
          · rename_i hp2; injection h with hpz; subst hpz
            obtain ⟨hsrc, _, hlnz, hlz, _, _, _⟩ := resolveStep_sound_dec 25 p p0 k pnz pz' hs hl
            obtain ⟨hl2, hinc4⟩ := chkIncN_sound 4 pnz dst p2 hi hlnz
            refine ⟨hsrc, hlz, fun rs hlen => ?_⟩
            suffices ∀ v rs, rs.length = 9 → regGet k rs = v →
                RegReachPos p0 rs pz' (regSet k 0 (regSet dst (regGet dst rs + 4 * v) rs)) from
              (regReach_dec_p0 hs hl rs).trans_pos (this (regGet k rs) rs hlen rfl)
            intro v; induction v with
            | zero =>
              intro rs hlen hv
              have hz := regReach_dec_z0 hs hl rs hlen hv
              rw [Nat.mul_zero, Nat.add_zero, regSet_get_self dst rs (by omega), ← hv, regSet_get_self k rs (by omega)]
              exact hz
            | succ v' ih =>
              intro rs hlen hv
              have hnz := regReach_dec_nz0 hs hl rs hlen (by omega)
              rw [show regGet k rs - 1 = v' by omega] at hnz
              let rs1 := regSet k v' rs
              have hlen1 : rs1.length = 9 := by rw [regSet_length]; exact hlen
              have r2 := hinc4 rs1 hlen1
              let rs2 := regSet dst (regGet dst rs1 + 4) rs1
              have hlen2 : rs2.length = 9 := by rw [regSet_length]; exact hlen1
              have rg := regReach_goto hp2 hl2 rs2
              have hgk : regGet k rs2 = v' := by
                rw [regGet_regSet_ne k dst _ rs1 (Ne.symm hne), regGet_regSet_same k v' rs (by omega)]
              have hgd : regGet dst rs2 = regGet dst rs + 4 := by
                rw [regGet_regSet_same dst _ rs1 (by omega), regGet_regSet_ne dst k v' rs hne]
              have r3 := ih rs2 hlen2 hgk
              have hnorm : regSet k 0 (regSet dst (regGet dst rs2 + 4 * v') rs2) =
                  regSet k 0 (regSet dst (regGet dst rs + 4 * (v' + 1)) rs) := by
                rw [hgd, show regGet dst rs + 4 + 4 * v' = regGet dst rs + 4 * (v' + 1) by omega]
                dsimp only [rs2, rs1]
                rw [regSet_regSet_same, regSet_regSet_comm dst k _ v' rs hne,
                    regSet_regSet_comm k dst 0 _ _ (Ne.symm hne), regSet_regSet_same,
                    regSet_regSet_comm dst k _ 0 rs hne]
              rw [hnorm] at r3
              exact ((hnz.trans r2).trans rg).trans r3.of_pos
          · contradiction
      · contradiction

private theorem chkCopy3_sound_gen {p pn : List Bool} {src : Nat} (h2 : src ≠ 2) (h8 : src ≠ 8)
    (h : chkCopy3 p src = some pn) (hl : p.length = 42) :
    src < 9 ∧ pn.length = 42 ∧
    ∀ rs, rs.length = 9 →
      RegReachPos p rs pn
        (regSet 8 0 (regSet src (regGet 8 rs + regGet src rs) (regSet 2 (regGet 2 rs + regGet src rs) rs))) := by
  unfold chkCopy3 at h
  cases h1 : chkLin2 p src 2 8 with
  | none => rw [h1] at h; simp at h
  | some p1 =>
    rw [h1] at h; dsimp only at h
    obtain ⟨hsrc, _, _, hl1, hr1⟩ := chkLin2_sound (Ne.symm h2) (Ne.symm h8) (by decide) h1 hl
    obtain ⟨_, _, hln, hr2⟩ := chkMove_sound h8 h hl1
    refine ⟨hsrc, hln, fun rs hlen => ?_⟩
    have r1 := hr1 rs hlen
    let rs1 := regSet src 0 (regSet 8 (regGet 8 rs + regGet src rs) (regSet 2 (regGet 2 rs + regGet src rs) rs))
    have hlen1 : rs1.length = 9 := by rw [regSet_length, regSet_length, regSet_length]; exact hlen
    have r2 := hr2 rs1 hlen1
    have hnorm : regSet 8 0 (regSet src (regGet src rs1 + regGet 8 rs1) rs1) =
        regSet 8 0 (regSet src (regGet 8 rs + regGet src rs) (regSet 2 (regGet 2 rs + regGet src rs) rs)) := by
      have hgsrc : regGet src rs1 = 0 := regGet_regSet_same src 0 _ (by rw [regSet_length, regSet_length]; omega)
      have hg8 : regGet 8 rs1 = regGet 8 rs + regGet src rs := by
        rw [regGet_regSet_ne 8 src 0 _ (Ne.symm h8),
            regGet_regSet_same 8 _ _ (by rw [regSet_length]; omega)]
      rw [hgsrc, hg8, Nat.zero_add]
      dsimp only [rs1]
      rw [regSet_regSet_same src, regSet_regSet_comm src 8 _ _ _ h8, regSet_regSet_same 8,
          regSet_regSet_comm 8 src 0 _ _ (Ne.symm h8),
          regSet_regSet_comm src 8 _ 0 _ h8]
    rw [hnorm] at r2
    exact r1.trans r2.of_pos

private theorem chkCopy3_sound {p pn : List Bool} {src : Nat} (h2 : src ≠ 2) (h8 : src ≠ 8)
    (h : chkCopy3 p src = some pn) (hl : p.length = 42) :
    src < 9 ∧ pn.length = 42 ∧
    ∀ rs, rs.length = 9 → regGet 8 rs = 0 →
      RegReachPos p rs pn (regSet 2 (regGet 2 rs + regGet src rs) rs) := by
  obtain ⟨hsrc, hln, hgen⟩ := chkCopy3_sound_gen h2 h8 h hl
  refine ⟨hsrc, hln, fun rs hlen hr9 => ?_⟩
  have r := hgen rs hlen
  have hnorm : regSet 8 0 (regSet src (regGet 8 rs + regGet src rs) (regSet 2 (regGet 2 rs + regGet src rs) rs)) =
      regSet 2 (regGet 2 rs + regGet src rs) rs := by
    rw [hr9, Nat.zero_add, regSet_regSet_comm src 2 _ _ rs h2, regSet_get_self src rs (by omega),
        regSet_regSet_comm 8 2 0 _ rs (by decide), ← hr9, regSet_get_self 8 rs (by omega)]
  rwa [hnorm] at r

-- Cantor step helper for unpair loop: (r9, r6) steps through Cantor enumeration!
private def uStep (a b : Nat) : Nat × Nat :=
  match a with
  | a' + 1 => (a', b + 1)
  | 0 => (b + 1, 0)

private def uIter : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n + 1, (a, b) => uIter n (uStep a b)

private theorem cantor_uStep (a b : Nat) : cantor (uStep a b).1 (uStep a b).2 = cantor a b + 1 := by
  cases a with
  | zero =>
    unfold uStep cantor
    simp only [Nat.add_zero, Nat.zero_add]
    have hmul : (b + 1) * (b + 1 + 1) = b * (b + 1) + 2 * (b + 1) := by
      have h1 : (b + 1) * (b + 1 + 1) = (b + 1) * b + (b + 1) * 2 := Nat.mul_add (b + 1) b 2
      have h2 : (b + 1) * b = b * (b + 1) := Nat.mul_comm (b + 1) b
      omega
    omega
  | succ a' =>
    unfold uStep cantor; dsimp only
    have hsum : a' + (b + 1) = a' + 1 + b := by omega
    rw [hsum]; omega

private theorem cantor_uIter : ∀ n a b,
    cantor (uIter n (a, b)).1 (uIter n (a, b)).2 = cantor a b + n
  | 0, a, b => by simp [uIter]
  | n + 1, a, b => by
    unfold uIter
    rw [cantor_uIter n (uStep a b).1 (uStep a b).2, cantor_uStep a b]
    omega

private theorem uIter_zero_eq_unpair (n : Nat) : uIter n (0, 0) = unpair n := by
  have hc := cantor_uIter n 0 0
  have h0 : cantor 0 0 = 0 := rfl
  rw [h0, Nat.zero_add] at hc
  have hu := congrArg unpair hc
  rw [unpair_cantor] at hu
  exact hu

private theorem chkUnpairLoop_sound {p pz : List Bool} {src : Nat} (h5 : src ≠ 5) (h8 : src ≠ 8)
    (h : chkUnpairLoop p src = some pz) (hl : p.length = 42) :
    src < 9 ∧ pz.length = 42 ∧
    ∀ rs, rs.length = 9 → regGet 5 rs = 0 → regGet 8 rs = 0 →
      RegReachPos p rs pz
        (regSet src 0 (regSet 5 (unpair (regGet src rs)).2 (regSet 8 (unpair (regGet src rs)).1 rs))) := by
  unfold chkUnpairLoop at h
  cases hs : resolveStep 25 p with
  | none => rw [hs] at h; simp at h
  | some res =>
    rcases res with ⟨p0, ins⟩
    cases ins with
    | inc _ _ => rw [hs] at h; simp at h
    | dec k pnz pz' =>
      rw [hs] at h; dsimp only at h
      split at h
      · rename_i hks
        have hk : k = src := Nat.eq_of_beq_eq_true hks; subst hk
        cases hi : chkInc pnz 5 with
        | none => rw [hi] at h; simp at h
        | some p1 =>
          rw [hi] at h; dsimp only at h
          cases hs2 : resolveStep 25 p1 with
          | none => rw [hs2] at h; simp at h
          | some res2 =>
            rcases res2 with ⟨p1_0, ins2⟩
            cases ins2 with
            | inc _ _ => rw [hs2] at h; simp at h
            | dec k2 pnz2 pz2 =>
              rw [hs2] at h; dsimp only at h
              split at h
              · rename_i hc2
                have ⟨hk2, hpnz2⟩ := Bool.and_eq_true_iff.mp hc2
                have hk2e : k2 = 8 := Nat.eq_of_beq_eq_true hk2; subst hk2e
                cases hm : chkMove pz2 8 5 with
                | none => rw [hm] at h; simp at h
                | some p3 =>
                  rw [hm] at h; dsimp only at h
                  split at h
                  · rename_i hp3; injection h with hpz; subst hpz
                    obtain ⟨hsrc, _, hlnz, hlz, _, _, _⟩ := resolveStep_sound_dec 25 p p0 k pnz pz' hs hl
                    obtain ⟨_, hl1, hinc5⟩ := chkInc_sound hi hlnz
                    obtain ⟨_, _, hlnz2, hlz2, _, _, _⟩ := resolveStep_sound_dec 25 p1 p1_0 8 pnz2 pz2 hs2 hl1
                    obtain ⟨_, _, hl3, hmov⟩ := chkMove_sound (by decide) hm hlz2
                    refine ⟨hsrc, hlz, fun rs hlen hr6 hr9 => ?_⟩
                    suffices ∀ n a b rs, rs.length = 9 → regGet k rs = n → regGet 8 rs = a → regGet 5 rs = b →
                        RegReachPos p0 rs pz'
                          (regSet k 0 (regSet 5 (uIter n (a, b)).2 (regSet 8 (uIter n (a, b)).1 rs))) by
                      have := this (regGet k rs) 0 0 rs hlen rfl hr9 hr6
                      rw [uIter_zero_eq_unpair] at this
                      exact (regReach_dec_p0 hs hl rs).trans_pos this
                    intro n; induction n with
                    | zero =>
                      intro a b rs hlen hn ha hb
                      have hz := regReach_dec_z0 hs hl rs hlen hn
                      simp only [uIter]
                      rw [← ha, regSet_get_self 8 rs (by omega), ← hb, regSet_get_self 5 rs (by omega),
                          ← hn, regSet_get_self k rs (by omega)]
                      exact hz
                    | succ n' ih =>
                      intro a b rs hlen hn ha hb
                      have r1 := regReach_dec_nz0 hs hl rs hlen (by omega)
                      rw [show regGet k rs - 1 = n' by omega] at r1
                      let rs1 := regSet k n' rs
                      have hlen1 : rs1.length = 9 := by rw [regSet_length]; exact hlen
                      have r2 := hinc5 rs1 hlen1
                      let rs2 := regSet 5 (regGet 5 rs1 + 1) rs1
                      have hlen2 : rs2.length = 9 := by rw [regSet_length]; exact hlen1
                      have hgk2 : regGet k rs2 = n' := by
                        rw [regGet_regSet_ne k 5 _ rs1 h5, regGet_regSet_same k n' rs (by omega)]
                      have hg5_2 : regGet 5 rs2 = b + 1 := by
                        rw [regGet_regSet_same 5 _ rs1 (by omega), regGet_regSet_ne 5 k n' rs (Ne.symm h5), hb]
                      have hg8_2 : regGet 8 rs2 = a := by
                        rw [regGet_regSet_ne 8 5 _ rs1 (by decide), regGet_regSet_ne 8 k n' rs (Ne.symm h8), ha]
                      cases a with
                      | zero =>
                        have r3 := regReach_dec_z hs2 hl1 rs2 hlen2 hg8_2
                        have r4 := hmov rs2 hlen2
                        let rs3 := regSet 5 0 (regSet 8 (regGet 8 rs2 + regGet 5 rs2) rs2)
                        have rg3 := regReach_goto hp3 hl3 rs3
                        have hlen3 : rs3.length = 9 := by rw [regSet_length, regSet_length]; exact hlen2
                        have hgk3 : regGet k rs3 = n' := by
                          rw [regGet_regSet_ne k 5 _ _ h5, regGet_regSet_ne k 8 _ _ h8, hgk2]
                        have hg8_3 : regGet 8 rs3 = b + 1 := by
                          rw [regGet_regSet_ne 8 5 _ _ (by decide),
                              regGet_regSet_same 8 _ rs2 (by omega), hg8_2, hg5_2, Nat.zero_add]
                        have hg5_3 : regGet 5 rs3 = 0 :=
                          regGet_regSet_same 5 0 _ (by rw [regSet_length]; omega)
                        have r5 := ih (b + 1) 0 rs3 hlen3 hgk3 hg8_3 hg5_3
                        have hnorm : regSet k 0 (regSet 5 (uIter n' (b + 1, 0)).2 (regSet 8 (uIter n' (b + 1, 0)).1 rs3)) =
                            regSet k 0 (regSet 5 (uIter n' (b + 1, 0)).2 (regSet 8 (uIter n' (b + 1, 0)).1 rs)) := by
                          dsimp only [rs3, rs2, rs1]
                          rw [regSet_regSet_comm 8 5 _ 0 _ (by decide), regSet_regSet_same 8,
                              regSet_regSet_comm 8 5 _ _ _ (by decide), regSet_regSet_same 5,
                              regSet_regSet_same 5,
                              regSet_regSet_comm 8 k _ n' rs (Ne.symm h8),
                              regSet_regSet_comm 5 k _ n' _ (Ne.symm h5),
                              regSet_regSet_same k]
                        simp only [uIter, uStep]
                        rw [hnorm] at r5
                        exact ((((r1.trans r2.of_pos).trans r3.of_pos).trans r4.of_pos).trans rg3).trans r5.of_pos
                      | succ a' =>
                        have r3 := regReach_dec_nz hs2 hl1 rs2 hlen2 (by omega)
                        rw [show regGet 8 rs2 - 1 = a' by omega] at r3
                        let rs3 := regSet 8 a' rs2
                        have rg3 := regReach_goto hpnz2 hlnz2 rs3
                        have hlen3 : rs3.length = 9 := by rw [regSet_length]; exact hlen2
                        have hgk3 : regGet k rs3 = n' := by
                          rw [regGet_regSet_ne k 8 _ rs2 h8, hgk2]
                        have hg8_3 : regGet 8 rs3 = a' := regGet_regSet_same 8 a' rs2 (by omega)
                        have hg5_3 : regGet 5 rs3 = b + 1 := by
                          rw [regGet_regSet_ne 5 8 _ rs2 (by decide), hg5_2]
                        have r4 := ih a' (b + 1) rs3 hlen3 hgk3 hg8_3 hg5_3
                        have hnorm : regSet k 0 (regSet 5 (uIter n' (a', b + 1)).2 (regSet 8 (uIter n' (a', b + 1)).1 rs3)) =
                            regSet k 0 (regSet 5 (uIter n' (a', b + 1)).2 (regSet 8 (uIter n' (a', b + 1)).1 rs)) := by
                          dsimp only [rs3, rs2, rs1]
                          rw [regSet_regSet_same 8,
                              regSet_regSet_comm 8 5 _ _ _ (by decide), regSet_regSet_same 5,
                              regSet_regSet_comm 8 k _ n' rs (Ne.symm h8),
                              regSet_regSet_comm 5 k _ n' _ (Ne.symm h5),
                              regSet_regSet_same k]
                        simp only [uIter, uStep]
                        rw [hnorm] at r4
                        exact (((r1.trans r2.of_pos).trans r3.of_pos).trans rg3).trans r4.of_pos
                  · contradiction
              · contradiction
      · contradiction

private theorem chkUnpair_sound {p pn : List Bool} {src dst : Nat}
    (hs5 : src ≠ 5) (hs8 : src ≠ 8) (hd8 : dst ≠ 8) (_hd5 : dst ≠ 5) (hsd : src ≠ dst)
    (h : chkUnpair p src dst = some pn) (hl : p.length = 42) :
    src < 9 ∧ dst < 9 ∧ pn.length = 42 ∧
    ∀ rs, rs.length = 9 → regGet 5 rs = 0 → regGet 8 rs = 0 →
      RegReachPos p rs pn
        (regSet dst (regGet dst rs + (unpair (regGet src rs)).1)
          (regSet src (unpair (regGet src rs)).2 rs)) := by
  unfold chkUnpair at h
  cases h1 : chkUnpairLoop p src with
  | none => rw [h1] at h; simp at h
  | some p1 =>
    rw [h1] at h; dsimp only at h
    cases h2 : chkMove p1 src 5 with
    | none => rw [h2] at h; simp at h
    | some p2 =>
      rw [h2] at h; dsimp only at h
      obtain ⟨hsrc, hl1, hr1⟩ := chkUnpairLoop_sound hs5 hs8 h1 hl
      obtain ⟨_, _, hl2, hr2⟩ := chkMove_sound hs5 h2 hl1
      obtain ⟨hdst, _, hln, hr3⟩ := chkMove_sound hd8 h hl2
      refine ⟨hsrc, hdst, hln, fun rs hlen hr6 hr9 => ?_⟩
      have r1 := hr1 rs hlen hr6 hr9
      let rs1 := regSet src 0 (regSet 5 (unpair (regGet src rs)).2 (regSet 8 (unpair (regGet src rs)).1 rs))
      have hlen1 : rs1.length = 9 := by rw [regSet_length, regSet_length, regSet_length]; exact hlen
      have r2 := hr2 rs1 hlen1
      let rs2 := regSet 5 0 (regSet src (regGet src rs1 + regGet 5 rs1) rs1)
      have hlen2 : rs2.length = 9 := by rw [regSet_length, regSet_length]; exact hlen1
      have r3 := hr3 rs2 hlen2
      have hnorm : regSet 8 0 (regSet dst (regGet dst rs2 + regGet 8 rs2) rs2) =
          regSet dst (regGet dst rs + (unpair (regGet src rs)).1)
            (regSet src (unpair (regGet src rs)).2 rs) := by
        have hgs1 : regGet src rs1 = 0 := regGet_regSet_same src 0 _ (by rw [regSet_length, regSet_length]; omega)
        have hg5_1 : regGet 5 rs1 = (unpair (regGet src rs)).2 := by
          rw [regGet_regSet_ne 5 src 0 _ (Ne.symm hs5), regGet_regSet_same 5 _ _ (by rw [regSet_length]; omega)]
        have hrs2 : rs2 = regSet src (unpair (regGet src rs)).2 (regSet 8 (unpair (regGet src rs)).1 rs) := by
          dsimp only [rs2]; rw [hgs1, hg5_1, Nat.zero_add]; dsimp only [rs1]
          rw [regSet_regSet_same src, regSet_regSet_comm 5 src 0 _ _ (Ne.symm hs5),
              regSet_regSet_same 5, regSet_regSet_comm 5 8 0 _ rs (by decide),
              ← hr6, regSet_get_self 5 rs (by omega)]
        rw [hrs2]
        have hgd2 : regGet dst (regSet src (unpair (regGet src rs)).2 (regSet 8 (unpair (regGet src rs)).1 rs)) = regGet dst rs := by
          rw [regGet_regSet_ne dst src _ _ (Ne.symm hsd), regGet_regSet_ne dst 8 _ rs hd8]
        have hg8_2 : regGet 8 (regSet src (unpair (regGet src rs)).2 (regSet 8 (unpair (regGet src rs)).1 rs)) =
            (unpair (regGet src rs)).1 := by
          rw [regGet_regSet_ne 8 src _ _ (Ne.symm hs8), regGet_regSet_same 8 _ rs (by omega)]
        rw [hgd2, hg8_2, regSet_regSet_comm 8 dst 0 _ _ (Ne.symm hd8),
            regSet_regSet_comm 8 src 0 _ _ (Ne.symm hs8), regSet_regSet_same 8,
            ← hr9, regSet_get_self 8 rs (by omega)]
      rw [hnorm] at r3
      exact (r1.trans r2.of_pos).trans r3.of_pos

private theorem chkPairLoop_sound {p pz : List Bool} (h : chkPairLoop p = some pz) (hl : p.length = 42) :
    pz.length = 42 ∧
    ∀ rs, rs.length = 9 → regGet 2 rs = 0 →
      RegReachPos p rs pz
        (regSet 8 0 (regSet 5 (regGet 5 rs + regGet 8 rs * (regGet 8 rs + 1) / 2) rs)) := by
  unfold chkPairLoop at h
  cases hs : resolveStep 25 p with
  | none => rw [hs] at h; simp at h
  | some res =>
    rcases res with ⟨p0, ins⟩
    cases ins with
    | inc _ _ => rw [hs] at h; simp at h
    | dec k pnz pz' =>
      rw [hs] at h; dsimp only at h
      split at h
      · rename_i hk8
        have hk : k = 8 := Nat.eq_of_beq_eq_true hk8; subst hk
        cases hi : chkInc pnz 5 with
        | none => rw [hi] at h; simp at h
        | some p1 =>
          rw [hi] at h; dsimp only at h
          cases hm : chkMove p1 2 8 with
          | none => rw [hm] at h; simp at h
          | some p2 =>
            rw [hm] at h; dsimp only at h
            cases hl2c : chkLin2 p2 2 5 8 with
            | none => rw [hl2c] at h; simp at h
            | some p3 =>
              rw [hl2c] at h; dsimp only at h
              split at h
              · rename_i hp3; injection h with hpz; subst hpz
                obtain ⟨_, _, hlnz, hlz, _, _, _⟩ := resolveStep_sound_dec 25 p p0 8 pnz pz' hs hl
                obtain ⟨_, hl1, hinc5⟩ := chkInc_sound hi hlnz
                obtain ⟨_, _, hl2, hmov⟩ := chkMove_sound (by decide) hm hl1
                obtain ⟨_, _, _, hl3, hlin⟩ := chkLin2_sound (by decide) (by decide) (by decide) hl2c hl2
                refine ⟨hlz, fun rs hlen hr3 => ?_⟩
                suffices ∀ v rs, rs.length = 9 → regGet 2 rs = 0 → regGet 8 rs = v →
                    RegReachPos p0 rs pz' (regSet 8 0 (regSet 5 (regGet 5 rs + v * (v + 1) / 2) rs)) from
                  (regReach_dec_p0 hs hl rs).trans_pos (this (regGet 8 rs) rs hlen hr3 rfl)
                intro v; induction v with
                | zero =>
                  intro rs hlen _ hv
                  have hz := regReach_dec_z0 hs hl rs hlen hv
                  simp only [Nat.zero_mul, Nat.zero_div, Nat.add_zero]
                  rw [regSet_get_self 5 rs (by omega), ← hv, regSet_get_self 8 rs (by omega)]
                  exact hz
                | succ v' ih =>
                  intro rs hlen hr3 hv
                  have r1 := regReach_dec_nz0 hs hl rs hlen (by omega)
                  rw [show regGet 8 rs - 1 = v' by omega] at r1
                  let rs1 := regSet 8 v' rs
                  have hlen1 : rs1.length = 9 := by rw [regSet_length]; exact hlen
                  have r2 := hinc5 rs1 hlen1
                  let rs2 := regSet 5 (regGet 5 rs1 + 1) rs1
                  have hlen2 : rs2.length = 9 := by rw [regSet_length]; exact hlen1
                  have r3 := hmov rs2 hlen2
                  let rs3 := regSet 8 0 (regSet 2 (regGet 2 rs2 + regGet 8 rs2) rs2)
                  have hlen3 : rs3.length = 9 := by rw [regSet_length, regSet_length]; exact hlen2
                  have r4 := hlin rs3 hlen3
                  let rs4 := regSet 2 0 (regSet 8 (regGet 8 rs3 + regGet 2 rs3) (regSet 5 (regGet 5 rs3 + regGet 2 rs3) rs3))
                  have hrs4 : rs4 = regSet 8 v' (regSet 5 (regGet 5 rs + (v' + 1)) rs) := by
                    have hg2_2 : regGet 2 rs2 = 0 := by
                      rw [regGet_regSet_ne 2 5 _ rs1 (by decide), regGet_regSet_ne 2 8 _ rs (by decide), hr3]
                    have hg8_2 : regGet 8 rs2 = v' := by
                      rw [regGet_regSet_ne 8 5 _ rs1 (by decide), regGet_regSet_same 8 v' rs (by omega)]
                    have hg5_2 : regGet 5 rs2 = regGet 5 rs + 1 := by
                      rw [regGet_regSet_same 5 _ rs1 (by omega), regGet_regSet_ne 5 8 _ rs (by decide)]
                    have hg8_3 : regGet 8 rs3 = 0 := regGet_regSet_same 8 0 _ (by rw [regSet_length]; omega)
                    have hg2_3 : regGet 2 rs3 = v' := by
                      rw [regGet_regSet_ne 2 8 _ _ (by decide), regGet_regSet_same 2 _ rs2 (by omega), hg2_2, hg8_2, Nat.zero_add]
                    have hg5_3 : regGet 5 rs3 = regGet 5 rs + 1 := by
                      rw [regGet_regSet_ne 5 8 _ _ (by decide), regGet_regSet_ne 5 2 _ rs2 (by decide), hg5_2]
                    dsimp only [rs4]; rw [hg8_3, hg2_3, hg5_3, Nat.zero_add,
                      show regGet 5 rs + 1 + v' = regGet 5 rs + (v' + 1) by omega]
                    dsimp only [rs3]; rw [hg2_2, hg8_2, Nat.zero_add]
                    dsimp only [rs2, rs1]
                    rw [regSet_regSet_comm 5 8 _ 0 _ (by decide),
                        regSet_regSet_same 8,
                        regSet_regSet_comm 5 2 _ v' _ (by decide),
                        regSet_regSet_same 5,
                        regSet_regSet_comm 8 2 v' v' _ (by decide),
                        regSet_regSet_same 2,
                        regSet_regSet_comm 2 8 0 v' _ (by decide),
                        regSet_regSet_comm 2 5 0 _ _ (by decide),
                        regSet_regSet_comm 2 8 0 v' rs (by decide),
                        ← hr3, regSet_get_self 2 rs (by omega),
                        regSet_regSet_comm 8 5 v' _ _ (by decide),
                        regSet_regSet_same 8,
                        regSet_regSet_comm 5 8 _ v' rs (by decide)]
                  change RegReachPos p2 rs3 p3 rs4 at r4
                  rw [hrs4] at r4
                  have rg4 := regReach_goto hp3 hl3 (regSet 8 v' (regSet 5 (regGet 5 rs + (v' + 1)) rs))
                  have hgk4 : regGet 2 (regSet 8 v' (regSet 5 (regGet 5 rs + (v' + 1)) rs)) = 0 := by
                    rw [regGet_regSet_ne 2 8 _ _ (by decide), regGet_regSet_ne 2 5 _ rs (by decide), hr3]
                  have hg8_4 : regGet 8 (regSet 8 v' (regSet 5 (regGet 5 rs + (v' + 1)) rs)) = v' :=
                    regGet_regSet_same 8 v' _ (by rw [regSet_length]; omega)
                  have r5 := ih (regSet 8 v' (regSet 5 (regGet 5 rs + (v' + 1)) rs))
                    (by rw [regSet_length, regSet_length]; exact hlen) hgk4 hg8_4
                  have htri : (v' + 1) * (v' + 1 + 1) / 2 = v' * (v' + 1) / 2 + (v' + 1) := by
                    have h1 : (v' + 1) * (v' + 1 + 1) = (v' + 1) * v' + (v' + 1) * 2 := Nat.mul_add (v' + 1) v' 2
                    have h2 : (v' + 1) * v' = v' * (v' + 1) := Nat.mul_comm (v' + 1) v'
                    omega
                  have hnorm : regSet 8 0 (regSet 5 (regGet 5 (regSet 8 v' (regSet 5 (regGet 5 rs + (v' + 1)) rs)) + v' * (v' + 1) / 2)
                      (regSet 8 v' (regSet 5 (regGet 5 rs + (v' + 1)) rs))) =
                      regSet 8 0 (regSet 5 (regGet 5 rs + (v' + 1) * (v' + 1 + 1) / 2) rs) := by
                    rw [regGet_regSet_ne 5 8 _ _ (by decide), regGet_regSet_same 5 _ rs (by omega),
                        htri, show regGet 5 rs + (v' + 1) + v' * (v' + 1) / 2 = regGet 5 rs + (v' * (v' + 1) / 2 + (v' + 1)) by omega,
                        regSet_regSet_comm 5 8 _ v' _ (by decide), regSet_regSet_same 5,
                        regSet_regSet_comm 8 5 0 _ _ (by decide), regSet_regSet_same 8,
                        regSet_regSet_comm 5 8 _ 0 rs (by decide)]
                  rw [hnorm] at r5
                  exact ((((r1.trans r2.of_pos).trans r3.of_pos).trans r4.of_pos).trans rg4).trans r5.of_pos
              · contradiction
      · contradiction

private theorem chkPushR3_sound {p pn : List Bool} (h : chkPushR3 p = some pn) (hl : p.length = 42) :
    pn.length = 42 ∧
    ∀ r1 r2 r3 r4 r5 r7 r8,
      RegReachPos p [r1, r2, r3, r4, r5, 0, r7, r8, 0] pn [cantor r3 r1, r2, 0, r4, r5, 0, r7, r8, 0] := by
  unfold chkPushR3 at h
  cases h1 : chkMove p 8 2 with
  | none => rw [h1] at h; simp at h
  | some p1 =>
    rw [h1] at h; dsimp only at h
    cases h2 : chkMove p1 2 0 with
    | none => rw [h2] at h; simp at h
    | some p2 =>
      rw [h2] at h; dsimp only at h
      cases h3 : chkLin2 p2 2 5 8 with
      | none => rw [h3] at h; simp at h
      | some p3 =>
        rw [h3] at h; dsimp only at h
        cases h4 : chkPairLoop p3 with
        | none => rw [h4] at h; simp at h
        | some p4 =>
          rw [h4] at h; dsimp only at h
          obtain ⟨_, _, hl1, hr1⟩ := chkMove_sound (by decide) h1 hl
          obtain ⟨_, _, hl2, hr2⟩ := chkMove_sound (by decide) h2 hl1
          obtain ⟨_, _, _, hl3, hr3⟩ := chkLin2_sound (by decide) (by decide) (by decide) h3 hl2
          obtain ⟨hl4, hr4⟩ := chkPairLoop_sound h4 hl3
          obtain ⟨_, _, hln, hr5⟩ := chkMove_sound (by decide) h hl4
          refine ⟨hln, fun r1 r2 r3 r4 r5 r7 r8 => ?_⟩
          have s1 := hr1 [r1, r2, r3, r4, r5, 0, r7, r8, 0] rfl
          have s2 := hr2 [r1, r2, 0, r4, r5, 0, r7, r8, r3] rfl
          have s3 := hr3 [0, r2, r1, r4, r5, 0, r7, r8, r3] rfl
          have s4 := hr4 [0, r2, 0, r4, r5, r1, r7, r8, r3 + r1] rfl rfl
          have s5 := hr5 [0, r2, 0, r4, r5, r1 + (r3 + r1) * (r3 + r1 + 1) / 2, r7, r8, 0] rfl
          simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s1 s2 s3 s4 s5
          have hcan : r1 + (r3 + r1) * (r3 + r1 + 1) / 2 = cantor r3 r1 := by unfold cantor; omega
          rw [hcan] at s4 s5
          exact (((s1.trans s2.of_pos).trans s3.of_pos).trans s4.of_pos).trans s5.of_pos

private theorem chkPopPair4_sound {p pn : List Bool} (h : chkPopPair4 p = some pn) (hl : p.length = 42) :
    pn.length = 42 ∧
    ∀ a s r2 r3 r4 r5 r7 r8,
      RegReachPos p [cantor a s, r2, r3, r4, r5, 0, r7, r8, 0] pn [s, r2, Ic a r3, r4, r5, 0, r7, r8, 0] := by
  unfold chkPopPair4 at h
  cases h1 : chkUnpairLoop p 0 with
  | none => rw [h1] at h; simp at h
  | some p1 =>
    rw [h1] at h; dsimp only at h
    cases h2 : chkMove p1 0 5 with
    | none => rw [h2] at h; simp at h
    | some p2 =>
      rw [h2] at h; dsimp only at h
      cases h3 : chkLin2 p2 2 5 8 with
      | none => rw [h3] at h; simp at h
      | some p3 =>
        rw [h3] at h; dsimp only at h
        cases h4 : chkPairLoop p3 with
        | none => rw [h4] at h; simp at h
        | some p4 =>
          rw [h4] at h; dsimp only at h
          obtain ⟨_, hl1, hr1⟩ := chkUnpairLoop_sound (by decide) (by decide) h1 hl
          obtain ⟨_, _, hl2, hr2⟩ := chkMove_sound (by decide) h2 hl1
          obtain ⟨_, _, _, hl3, hr3⟩ := chkLin2_sound (by decide) (by decide) (by decide) h3 hl2
          obtain ⟨hl4, hr4⟩ := chkPairLoop_sound h4 hl3
          obtain ⟨_, hln, hr5⟩ := chkLin4_sound (by decide) (by decide) h hl4
          refine ⟨hln, fun a s r2 r3 r4 r5 r7 r8 => ?_⟩
          have s1 := hr1 [cantor a s, r2, r3, r4, r5, 0, r7, r8, 0] rfl rfl rfl
          simp only [regGet_zero, regSet, unpair_cantor] at s1
          have s2 := hr2 [0, r2, r3, r4, r5, s, r7, r8, a] rfl
          have s3 := hr3 [s, r2, r3, r4, r5, 0, r7, r8, a] rfl
          have s4 := hr4 [s, r2, 0, r4, r5, r3, r7, r8, a + r3] rfl rfl
          have s5 := hr5 [s, r2, 0, r4, r5, r3 + (a + r3) * (a + r3 + 1) / 2, r7, r8, 0] rfl
          simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s2 s3 s4 s5
          have hic : 4 * (r3 + (a + r3) * (a + r3 + 1) / 2) = Ic a r3 := by unfold Ic cantor; omega
          rw [hic] at s5
          exact (((s1.trans s2.of_pos).trans s3.of_pos).trans s4.of_pos).trans s5.of_pos

private def chkNeqClean (q : List Bool) : Option (List Bool) :=
  match chkZero q 7 with
  | some q1 =>
    match resolveStep 25 q1 with
    | some (q1_0, .dec k pnz pz) =>
      if Nat.beq k 8 then
        match chkZero pnz 7 with
        | some q2 => if reachesGoto 25 q2 q1_0 then some pz else none
        | none => none
      else none
    | _ => none
  | none => none

private theorem chkNeqClean_sound {q pn : List Bool} (h : chkNeqClean q = some pn) (hl : q.length = 42) :
    pn.length = 42 ∧
    ∀ rs, rs.length = 9 → RegReachPos q rs pn (regSet 8 0 (regSet 7 0 rs)) := by
  unfold chkNeqClean at h
  cases hz1 : chkZero q 7 with
  | none => rw [hz1] at h; simp at h
  | some q1 =>
    rw [hz1] at h; dsimp only at h
    cases hs : resolveStep 25 q1 with
    | none => rw [hs] at h; simp at h
    | some res =>
      rcases res with ⟨q1_0, ins⟩
      cases ins with
      | inc _ _ => rw [hs] at h; simp at h
      | dec k pnz pz =>
        rw [hs] at h; dsimp only at h
        split at h
        · rename_i hk8
          have hk : k = 8 := Nat.eq_of_beq_eq_true hk8; subst hk
          cases hz2 : chkZero pnz 7 with
          | none => rw [hz2] at h; simp at h
          | some q2 =>
            rw [hz2] at h; dsimp only at h
            split at h
            · rename_i hq2; injection h with hpn; subst hpn
              obtain ⟨_, hl1, hzero1⟩ := chkZero_sound hz1 hl
              obtain ⟨_, _, hlnz, hlz, _, _, _⟩ := resolveStep_sound_dec 25 q1 q1_0 8 pnz pz hs hl1
              obtain ⟨_, hl2, hzero2⟩ := chkZero_sound hz2 hlnz
              refine ⟨hlz, fun rs hlen => ?_⟩
              have r1 := hzero1 rs hlen
              suffices ∀ v rs', rs'.length = 9 → regGet 7 rs' = 0 → regGet 8 rs' = v →
                  RegReachPos q1_0 rs' pz (regSet 8 0 rs') by
                have r0 := regReach_dec_p0 hs hl1 (regSet 7 0 rs)
                have r2 := this (regGet 8 (regSet 7 0 rs)) (regSet 7 0 rs)
                  (by rw [regSet_length]; exact hlen) (regGet_regSet_same 7 0 rs (by omega)) rfl
                exact (r1.trans r0).trans r2.of_pos
              intro v; induction v with
              | zero =>
                intro rs' hlen' _ hv
                have hz := regReach_dec_z0 hs hl1 rs' hlen' hv
                rw [← hv, regSet_get_self 8 rs' (by omega)]; exact hz
              | succ v' ih =>
                intro rs' hlen' h7 hv
                have r2 := regReach_dec_nz0 hs hl1 rs' hlen' (by omega)
                rw [show regGet 8 rs' - 1 = v' by omega] at r2
                let rs1 := regSet 8 v' rs'
                have hlen1 : rs1.length = 9 := by rw [regSet_length]; exact hlen'
                have r3 := hzero2 rs1 hlen1
                have hrs1 : regSet 7 0 rs1 = rs1 := by
                  have h7' : regGet 7 rs1 = 0 := by rw [regGet_regSet_ne 7 8 v' rs' (by decide), h7]
                  rw [← h7', regSet_get_self 7 rs1 (by omega)]
                rw [hrs1] at r3
                have rg := regReach_goto hq2 hl2 rs1
                have r4 := ih rs1 hlen1 (by rw [regGet_regSet_ne 7 8 v' rs' (by decide), h7])
                  (regGet_regSet_same 8 v' rs' (by omega))
                dsimp only [rs1] at r4
                rw [regSet_regSet_same 8] at r4
                exact ((r2.trans r3.of_pos).trans rg).trans r4.of_pos
            · contradiction
        · contradiction

private def chkEq89 (p : List Bool) : Option (List Bool × List Bool) :=
  match resolveStep 25 p with
  | some (p0, .dec k pnz pz) =>
    if Nat.beq k 7 then
      match resolveStep 25 pnz with
      | some (_, .dec k1 pnz1 pz1) =>
        if Nat.beq k1 8 && reachesGoto 25 pnz1 p0 then
          match chkNeqClean pz1 with
          | some neq1 =>
            let neq1' := resolveGoto 25 neq1
            match resolveStep 25 pz with
            | some (_, .dec k2 pnz2 pz2) =>
              if Nat.beq k2 8 then
                match chkNeqClean pnz2 with
                | some neq2 => if reachesGoto 25 neq2 neq1' then some (pz2, neq1') else none
                | none => none
              else none
            | _ => none
          | none => none
        else none
      | _ => none
    else none
  | _ => none

private theorem chkEq89_sound {p peq pneq : List Bool} (h : chkEq89 p = some (peq, pneq)) (hl : p.length = 42) :
    peq.length = 42 ∧ pneq.length = 42 ∧
    (∀ rs, rs.length = 9 → regGet 7 rs = regGet 8 rs →
      RegReachPos p rs peq (regSet 8 0 (regSet 7 0 rs))) ∧
    (∀ rs, rs.length = 9 → regGet 7 rs ≠ regGet 8 rs →
      RegReachPos p rs pneq (regSet 8 0 (regSet 7 0 rs))) := by
  unfold chkEq89 at h
  cases hs : resolveStep 25 p with
  | none => rw [hs] at h; simp at h
  | some res =>
    rcases res with ⟨p0, ins⟩
    cases ins with
    | inc _ _ => rw [hs] at h; simp at h
    | dec k pnz pz =>
      rw [hs] at h; dsimp only at h
      split at h
      · rename_i hk7; have hk : k = 7 := Nat.eq_of_beq_eq_true hk7; subst hk
        cases hs1 : resolveStep 25 pnz with
        | none => rw [hs1] at h; simp at h
        | some res1 =>
          rcases res1 with ⟨p1_0, ins1⟩
          cases ins1 with
          | inc _ _ => rw [hs1] at h; simp at h
          | dec k1 pnz1 pz1 =>
            rw [hs1] at h; dsimp only at h
            split at h
            · rename_i hc1
              have ⟨hk1, hpnz1⟩ := Bool.and_eq_true_iff.mp hc1
              have hk1e : k1 = 8 := Nat.eq_of_beq_eq_true hk1; subst hk1e
              cases hnc1 : chkNeqClean pz1 with
              | none => rw [hnc1] at h; simp at h
              | some neq1 =>
                rw [hnc1] at h; dsimp only at h
                cases hs2 : resolveStep 25 pz with
                | none => rw [hs2] at h; simp at h
                | some res2 =>
                  rcases res2 with ⟨p2_0, ins2⟩
                  cases ins2 with
                  | inc _ _ => rw [hs2] at h; simp at h
                  | dec k2 pnz2 pz2 =>
                    rw [hs2] at h; dsimp only at h
                    split at h
                    · rename_i hk2; have hk2e : k2 = 8 := Nat.eq_of_beq_eq_true hk2; subst hk2e
                      cases hnc2 : chkNeqClean pnz2 with
                      | none => rw [hnc2] at h; simp at h
                      | some neq2 =>
                        rw [hnc2] at h; dsimp only at h
                        split at h
                        · rename_i hneq; injection h with hpair
                          have hpeq : peq = pz2 ∧ pneq = resolveGoto 25 neq1 := by cases hpair; exact ⟨rfl, rfl⟩
                          rcases hpeq with ⟨rfl, rfl⟩
                          obtain ⟨_, _, hlnz, hlz, _, _, _⟩ := resolveStep_sound_dec 25 p p0 7 pnz pz hs hl
                          obtain ⟨_, _, hlnz1, hlz1, _, _, _⟩ := resolveStep_sound_dec 25 pnz p1_0 8 pnz1 pz1 hs1 hlnz
                          obtain ⟨hlneq1, hcl1⟩ := chkNeqClean_sound hnc1 hlz1
                          obtain ⟨hlneq, _⟩ := resolveGoto_sound 25 neq1 hlneq1
                          obtain ⟨_, _, hlnz2, hleq, _, _, _⟩ := resolveStep_sound_dec 25 pz p2_0 8 pnz2 peq hs2 hlz
                          obtain ⟨hlneq2, hcl2⟩ := chkNeqClean_sound hnc2 hlnz2
                          have hmain : ∀ v rs, rs.length = 9 → regGet 7 rs = v →
                              (regGet 7 rs = regGet 8 rs → RegReachPos p0 rs peq (regSet 8 0 (regSet 7 0 rs))) ∧
                              (regGet 7 rs ≠ regGet 8 rs → RegReachPos p0 rs (resolveGoto 25 neq1) (regSet 8 0 (regSet 7 0 rs))) := by
                            intro v; induction v with
                            | zero =>
                              intro rs hlen hv
                              constructor
                              · intro heq
                                have h8 : regGet 8 rs = 0 := by omega
                                have r1 := regReach_dec_z0 hs hl rs hlen hv
                                have r2 := regReach_dec_z hs2 hlz rs hlen h8
                                rw [← hv, regSet_get_self 7 rs (by omega), heq, regSet_get_self 8 rs (by omega)]
                                exact r1.trans r2.of_pos
                              · intro hne
                                have h8pos : 0 < regGet 8 rs := by omega
                                have r1 := regReach_dec_z0 hs hl rs hlen hv
                                have r2 := regReach_dec_nz hs2 hlz rs hlen h8pos
                                have r3 := hcl2 (regSet 8 (regGet 8 rs - 1) rs) (by rw [regSet_length]; exact hlen)
                                rw [regSet_regSet_comm 8 7 0 0 _ (by decide), regSet_regSet_same 8,
                                    regSet_regSet_comm 7 8 0 0 rs (by decide)] at r3
                                have rg := regReach_goto hneq hlneq2 (regSet 8 0 (regSet 7 0 rs))
                                exact ((r1.trans r2.of_pos).trans r3.of_pos).trans rg
                            | succ v' ih =>
                              intro rs hlen hv
                              have r1 := regReach_dec_nz0 hs hl rs hlen (by omega)
                              rw [show regGet 7 rs - 1 = v' by omega] at r1
                              let rs1 := regSet 7 v' rs
                              have hlen1 : rs1.length = 9 := by rw [regSet_length]; exact hlen
                              have hg8_1 : regGet 8 rs1 = regGet 8 rs := regGet_regSet_ne 8 7 v' rs (by decide)
                              cases h8c : regGet 8 rs with
                              | zero =>
                                constructor
                                · intro heq; omega
                                · intro _
                                  have r2 := regReach_dec_z hs1 hlnz rs1 hlen1 (by rw [hg8_1, h8c])
                                  have r3 := hcl1 rs1 hlen1
                                  dsimp only [rs1] at r3; rw [regSet_regSet_same 7] at r3
                                  have rg := regReach_resolveGoto neq1 hlneq1 (regSet 8 0 (regSet 7 0 rs))
                                  exact ((r1.trans r2.of_pos).trans r3.of_pos).trans rg
                              | succ w' =>
                                have r2 := regReach_dec_nz hs1 hlnz rs1 hlen1 (by omega)
                                rw [show regGet 8 rs1 - 1 = w' by omega] at r2
                                let rs2 := regSet 8 w' rs1
                                have rg := regReach_goto hpnz1 hlnz1 rs2
                                have hlen2 : rs2.length = 9 := by rw [regSet_length]; exact hlen1
                                have hg7_2 : regGet 7 rs2 = v' := by
                                  rw [regGet_regSet_ne 7 8 w' rs1 (by decide), regGet_regSet_same 7 v' rs (by omega)]
                                have hg8_2 : regGet 8 rs2 = w' := regGet_regSet_same 8 w' rs1 (by omega)
                                have hnorm : regSet 8 0 (regSet 7 0 rs2) = regSet 8 0 (regSet 7 0 rs) := by
                                  dsimp only [rs2, rs1]
                                  rw [regSet_regSet_comm 7 8 0 w' _ (by decide), regSet_regSet_same 7,
                                      regSet_regSet_same 8]
                                obtain ⟨iheq, ihne⟩ := ih rs2 hlen2 hg7_2
                                constructor
                                · intro heq
                                  have r3 := iheq (by omega)
                                  rw [hnorm] at r3
                                  exact ((r1.trans r2.of_pos).trans rg).trans r3.of_pos
                                · intro hne
                                  have r3 := ihne (by omega)
                                  rw [hnorm] at r3
                                  exact ((r1.trans r2.of_pos).trans rg).trans r3.of_pos
                          exact ⟨hleq, hlneq,
                            fun rs hlen heq => (regReach_dec_p0 hs hl rs).trans_pos ((hmain (regGet 7 rs) rs hlen rfl).1 heq),
                            fun rs hlen hne => (regReach_dec_p0 hs hl rs).trans_pos ((hmain (regGet 7 rs) rs hlen rfl).2 hne)⟩
                        · contradiction
                    · contradiction
            · contradiction
      · contradiction

/-! #### 4.3 Branch B: 275 Straight-Line BOps & Symbolic Evaluation -/

private theorem pB_length (n : Nat) : (pB n).length = 42 := natToBits_length 42 n

private inductive Sym where
  | vF0 | vG0 | vU0 | vX | vY | vZ
  | zero | one
  | ic (a b : Sym) | mc (a b : Sym) | uc (a b : Sym) | ec (a b : Sym)
  deriving BEq

private def Sym.eval (f0 g0 u0 x y z : Nat) : Sym → Nat
  | .vF0 => f0 | .vG0 => g0 | .vU0 => u0 | .vX => x | .vY => y | .vZ => z
  | .zero => 0 | .one => 1
  | .ic a b => Ic (a.eval f0 g0 u0 x y z) (b.eval f0 g0 u0 x y z)
  | .mc a b => Mc (a.eval f0 g0 u0 x y z) (b.eval f0 g0 u0 x y z)
  | .uc a b => Uc (a.eval f0 g0 u0 x y z) (b.eval f0 g0 u0 x y z)
  | .ec a b => Ec (a.eval f0 g0 u0 x y z) (b.eval f0 g0 u0 x y z)

private inductive SymR2 where
  | w0 | w1 | w2
  deriving BEq

private def SymR2.eval (w0 : Nat) : SymR2 → Nat
  | .w0 => w0
  | .w1 => (unpair w0).2
  | .w2 => (unpair (unpair w0).2).2

private structure SymState where
  stk : List Sym
  r2 : SymR2
  r3 : Sym
  r4 : Sym
  r5 : Sym
  r8 : Sym
  deriving BEq

private def evalStack (s0 f0 g0 u0 x y z : Nat) : List Sym → Nat
  | [] => s0
  | a :: rest => cantor (a.eval f0 g0 u0 x y z) (evalStack s0 f0 g0 u0 x y z rest)

private def SymState.toRegs (s0 w0 f0 g0 u0 z ctr : Nat) (st : SymState) : List Nat :=
  let x := g0 + (unpair w0).1
  let y := u0 + (unpair (unpair w0).2).1
  [evalStack s0 f0 g0 u0 x y z st.stk, st.r2.eval w0, st.r3.eval f0 g0 u0 x y z,
   st.r4.eval f0 g0 u0 x y z, st.r5.eval f0 g0 u0 x y z, 0, ctr, st.r8.eval f0 g0 u0 x y z, 0]

private def symStep (op : BOp) (st : SymState) : Option SymState :=
  match op with
  | .pushR3 => some { st with stk := st.r3 :: st.stk, r3 := .zero }
  | .popPair4 =>
    match st.stk with
    | a :: rest => some { st with stk := rest, r3 := .ic a st.r3 }
    | [] => none
  | .copy3_4 =>
    match st.r3 with
    | .zero => some { st with r3 := st.r4 }
    | _ => none
  | .copy3_5 =>
    match st.r3 with
    | .zero => some { st with r3 := st.r5 }
    | _ => none
  | .copy3_8 =>
    match st.r3 with
    | .zero => some { st with r3 := st.r8 }
    | _ => none
  | .unpair2_8 =>
    match st.r2, st.r8 with
    | .w0, .vG0 => some { st with r2 := .w1, r8 := .vX }
    | _, _ => none
  | .unpair2_4 =>
    match st.r2, st.r4 with
    | .w1, .vU0 => some { st with r2 := .w2, r4 := .vY }
    | _, _ => none
  | .inc3 k =>
    match st.r3, k with
    | .zero, 1 => some { st with r3 := .one }
    | .ic a b, 1 => some { st with r3 := .mc a b }
    | .ic a b, 2 => some { st with r3 := .uc b a }
    | .ic a b, 3 => some { st with r3 := .ec a b }
    | _, _ => none

private def symRun : List BOp → SymState → Option SymState
  | [], st => some st
  | op :: ops, st =>
    match symStep op st with
    | some st' => symRun ops st'
    | none => none

private theorem symStep_sound (op : BOp) (p1 p2 : List Bool) (st1 st2 : SymState)
    (hc : chkBOp p1 op = some p2) (hs : symStep op st1 = some st2) (hl : p1.length = 42) :
    p2.length = 42 ∧
    ∀ s0 w0 f0 g0 u0 z ctr,
      RegReach p1 (st1.toRegs s0 w0 f0 g0 u0 z ctr) p2 (st2.toRegs s0 w0 f0 g0 u0 z ctr) := by
  cases op with
  | pushR3 =>
    simp only [chkBOp] at hc; simp only [symStep] at hs; injection hs with hst; subst hst
    obtain ⟨hl2, hr⟩ := chkPushR3_sound hc hl
    exact ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => (hr _ _ _ _ _ _ _).of_pos⟩
  | popPair4 =>
    simp only [chkBOp] at hc; simp only [symStep] at hs
    rcases st1 with ⟨stk, r2, r3, r4, r5, r8⟩
    cases stk with
    | nil => simp at hs
    | cons a rest =>
      injection hs with hst; subst hst
      obtain ⟨hl2, hr⟩ := chkPopPair4_sound hc hl
      exact ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => (hr _ _ _ _ _ _ _ _).of_pos⟩
  | copy3_4 =>
    simp only [chkBOp] at hc; simp only [symStep] at hs
    rcases st1 with ⟨stk, r2, r3, r4, r5, r8⟩
    cases r3 <;> try (simp at hs)
    subst hs
    obtain ⟨_, hl2, hr⟩ := chkCopy3_sound (by decide) (by decide) hc hl
    refine ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => ?_⟩
    have r := hr (SymState.toRegs s0 w0 f0 g0 u0 z ctr ⟨stk, r2, .zero, r4, r5, r8⟩) rfl rfl
    simpa [SymState.toRegs, Sym.eval, regGet_zero, regGet_succ, regSet] using r.of_pos
  | copy3_5 =>
    simp only [chkBOp] at hc; simp only [symStep] at hs
    rcases st1 with ⟨stk, r2, r3, r4, r5, r8⟩
    cases r3 <;> try (simp at hs)
    subst hs
    obtain ⟨_, hl2, hr⟩ := chkCopy3_sound (by decide) (by decide) hc hl
    refine ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => ?_⟩
    have r := hr (SymState.toRegs s0 w0 f0 g0 u0 z ctr ⟨stk, r2, .zero, r4, r5, r8⟩) rfl rfl
    simpa [SymState.toRegs, Sym.eval, regGet_zero, regGet_succ, regSet] using r.of_pos
  | copy3_8 =>
    simp only [chkBOp] at hc; simp only [symStep] at hs
    rcases st1 with ⟨stk, r2, r3, r4, r5, r8⟩
    cases r3 <;> try (simp at hs)
    subst hs
    obtain ⟨_, hl2, hr⟩ := chkCopy3_sound (by decide) (by decide) hc hl
    refine ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => ?_⟩
    have r := hr (SymState.toRegs s0 w0 f0 g0 u0 z ctr ⟨stk, r2, .zero, r4, r5, r8⟩) rfl rfl
    simpa [SymState.toRegs, Sym.eval, regGet_zero, regGet_succ, regSet] using r.of_pos
  | unpair2_8 =>
    simp only [chkBOp] at hc; simp only [symStep] at hs
    rcases st1 with ⟨stk, r2, r3, r4, r5, r8⟩
    cases r2 <;> try (simp at hs)
    cases r8 <;> try (simp at hs)
    subst hs
    obtain ⟨_, _, hl2, hr⟩ := chkUnpair_sound (by decide) (by decide) (by decide) (by decide) (by decide) hc hl
    refine ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => ?_⟩
    have r := hr (SymState.toRegs s0 w0 f0 g0 u0 z ctr ⟨stk, .w0, r3, r4, r5, .vG0⟩) rfl rfl rfl
    simpa [SymState.toRegs, SymR2.eval, Sym.eval, regGet_zero, regGet_succ, regSet] using r.of_pos
  | unpair2_4 =>
    simp only [chkBOp] at hc; simp only [symStep] at hs
    rcases st1 with ⟨stk, r2, r3, r4, r5, r8⟩
    cases r2 <;> try (simp at hs)
    cases r4 <;> try (simp at hs)
    subst hs
    obtain ⟨_, _, hl2, hr⟩ := chkUnpair_sound (by decide) (by decide) (by decide) (by decide) (by decide) hc hl
    refine ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => ?_⟩
    have r := hr (SymState.toRegs s0 w0 f0 g0 u0 z ctr ⟨stk, .w1, r3, .vU0, r5, r8⟩) rfl rfl rfl
    simpa [SymState.toRegs, SymR2.eval, Sym.eval, regGet_zero, regGet_succ, regSet] using r.of_pos
  | inc3 k =>
    simp only [chkBOp] at hc; simp only [symStep] at hs
    obtain ⟨hl2, hr⟩ := chkIncN_sound k p1 2 p2 hc hl
    rcases st1 with ⟨stk, r2, r3, r4, r5, r8⟩
    cases r3 with
    | zero =>
      cases k with
      | zero => simp at hs
      | succ k' =>
        cases k' with
        | zero =>
          injection hs with hst; subst hst
          refine ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => ?_⟩
          have r := hr (SymState.toRegs s0 w0 f0 g0 u0 z ctr ⟨stk, r2, .zero, r4, r5, r8⟩) rfl
          simpa [SymState.toRegs, Sym.eval, regGet_zero, regGet_succ, regSet] using r
        | succ _ => simp at hs
    | ic a b =>
      cases k with
      | zero => simp at hs
      | succ k1 =>
        cases k1 with
        | zero =>
          injection hs with hst; subst hst
          refine ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => ?_⟩
          have r := hr (SymState.toRegs s0 w0 f0 g0 u0 z ctr ⟨stk, r2, .ic a b, r4, r5, r8⟩) rfl
          simpa [SymState.toRegs, Sym.eval, regGet_zero, regGet_succ, regSet, Ic, Mc] using r
        | succ k2 =>
          cases k2 with
          | zero =>
            injection hs with hst; subst hst
            refine ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => ?_⟩
            have r := hr (SymState.toRegs s0 w0 f0 g0 u0 z ctr ⟨stk, r2, .ic a b, r4, r5, r8⟩) rfl
            simpa [SymState.toRegs, Sym.eval, regGet_zero, regGet_succ, regSet, Ic, Uc] using r
          | succ k3 =>
            cases k3 with
            | zero =>
              injection hs with hst; subst hst
              refine ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => ?_⟩
              have r := hr (SymState.toRegs s0 w0 f0 g0 u0 z ctr ⟨stk, r2, .ic a b, r4, r5, r8⟩) rfl
              simpa [SymState.toRegs, Sym.eval, regGet_zero, regGet_succ, regSet, Ic, Ec] using r
            | succ _ => simp at hs
    | vF0 => simp at hs
    | vG0 => simp at hs
    | vU0 => simp at hs
    | vX => simp at hs
    | vY => simp at hs
    | vZ => simp at hs
    | one => simp at hs
    | mc _ _ => simp at hs
    | uc _ _ => simp at hs
    | ec _ _ => simp at hs

private theorem symRun_sound : ∀ ops (p1 p2 : List Bool) st1 st2,
    chkBOps p1 ops = some p2 → symRun ops st1 = some st2 → p1.length = 42 →
    p2.length = 42 ∧
    ∀ s0 w0 f0 g0 u0 z ctr,
      RegReach p1 (st1.toRegs s0 w0 f0 g0 u0 z ctr) p2 (st2.toRegs s0 w0 f0 g0 u0 z ctr)
  | [], p1, p2, st1, st2, hc, hs, hl => by
    unfold chkBOps at hc; unfold symRun at hs
    injection hc with hp; subst hp; injection hs with hst; subst hst
    exact ⟨hl, fun _ _ _ _ _ _ _ => RegReach.refl _ _⟩
  | op :: ops, p1, p2, st1, st2, hc, hs, hl => by
    unfold chkBOps at hc; unfold symRun at hs
    cases h1 : chkBOp p1 op with
    | none => rw [h1] at hc; simp at hc
    | some pm =>
      rw [h1] at hc; dsimp only at hc
      cases h2 : symStep op st1 with
      | none => rw [h2] at hs; simp at hs
      | some stm =>
        rw [h2] at hs; dsimp only at hs
        obtain ⟨hlm, rm⟩ := symStep_sound op p1 pm st1 stm h1 h2 hl
        obtain ⟨hl2, r2⟩ := symRun_sound ops pm p2 stm st2 hc hs hlm
        exact ⟨hl2, fun s0 w0 f0 g0 u0 z ctr => (rm s0 w0 f0 g0 u0 z ctr).trans (r2 s0 w0 f0 g0 u0 z ctr)⟩

private theorem symRun_to_sound (ops : List BOp) (p1 p2 : List Bool) (st1 st2 : SymState)
    (hc : chkBOpsTo p1 ops p2 = true) (hs : symRun ops st1 = some st2) (hl1 : p1.length = 42) :
    ∀ s0 w0 f0 g0 u0 z ctr,
      RegReach p1 (st1.toRegs s0 w0 f0 g0 u0 z ctr) p2 (st2.toRegs s0 w0 f0 g0 u0 z ctr) := by
  unfold chkBOpsTo at hc
  cases h : chkBOps p1 ops with
  | none => rw [h] at hc; contradiction
  | some pm =>
    rw [h] at hc; dsimp only at hc
    obtain ⟨hlm, hr⟩ := symRun_sound ops p1 pm st1 st2 h hs hl1
    intro s0 w0 f0 g0 u0 z ctr
    exact (hr s0 w0 f0 g0 u0 z ctr).trans (regReach_goto hc hlm _)

private theorem symRun_append : ∀ ops1 ops2 st1 st3,
    symRun (ops1 ++ ops2) st1 = some st3 →
    ∃ st2, symRun ops1 st1 = some st2 ∧ symRun ops2 st2 = some st3
  | [], _, st1, _, h => ⟨st1, rfl, h⟩
  | op :: ops1, ops2, st1, st3, h => by
    simp only [List.cons_append, symRun] at h
    rw [symRun]
    cases hs : symStep op st1 with
    | none => simp [hs] at h
    | some stm =>
      rw [hs] at h; dsimp only at h ⊢
      exact symRun_append ops1 ops2 stm st3 h

private theorem symRun_split {ops1 ops2 : List BOp} {p1 p2 p3 : List Bool} {st1 st3 : SymState}
    (hc1 : chkBOpsTo p1 ops1 p2 = true) (hl1 : p1.length = 42)
    (hrest : ∀ st2, symRun ops2 st2 = some st3 →
      ∀ s0 w0 f0 g0 u0 z ctr, RegReach p2 (st2.toRegs s0 w0 f0 g0 u0 z ctr) p3 (st3.toRegs s0 w0 f0 g0 u0 z ctr))
    (hs : symRun (ops1 ++ ops2) st1 = some st3) :
    ∀ s0 w0 f0 g0 u0 z ctr, RegReach p1 (st1.toRegs s0 w0 f0 g0 u0 z ctr) p3 (st3.toRegs s0 w0 f0 g0 u0 z ctr) := by
  obtain ⟨st2, hs1, hs2⟩ := symRun_append ops1 ops2 st1 st3 hs
  intro s0 w0 f0 g0 u0 z ctr
  exact (symRun_to_sound ops1 p1 p2 st1 st2 hc1 hs1 hl1 s0 w0 f0 g0 u0 z ctr).trans
    (hrest st2 hs2 s0 w0 f0 g0 u0 z ctr)

-- The 19 chunks of Branch B (275 BOps from pref 149 to pref 12181), verified in tm_bops_part1..5
private def allBOps : List BOp :=
  bopsChunk0 ++ (bopsChunk1 ++ (bopsChunk2 ++ (bopsChunk3 ++ (bopsChunk4 ++
  (bopsChunk5 ++ (bopsChunk6 ++ (bopsChunk7 ++ (bopsChunk8 ++ (bopsChunk9 ++
  (bopsChunk10 ++ (bopsChunk11 ++ (bopsChunk12 ++ (bopsChunk13 ++ (bopsChunk14 ++
  (bopsChunk15 ++ (bopsChunk16 ++ (bopsChunk17 ++ bopsChunk18)))))))))))))))))

private theorem bops_ok0 : chkBOpsTo (pB 149) bopsChunk0 (pB 1356437) = true := PalomarZF207.tm_bops_part1.1
private theorem bops_ok1 : chkBOpsTo (pB 1356437) bopsChunk1 (pB 56406677) = true := PalomarZF207.tm_bops_part1.2.1
private theorem bops_ok2 : chkBOpsTo (pB 56406677) bopsChunk2 (pB 98349717) = true := PalomarZF207.tm_bops_part1.2.2.1
private theorem bops_ok3 : chkBOpsTo (pB 98349717) bopsChunk3 (pB 192721557) = true := PalomarZF207.tm_bops_part1.2.2.2
private theorem bops_ok4 : chkBOpsTo (pB 192721557) bopsChunk4 (pB 701077) = true := PalomarZF207.tm_bops_part2.1
private theorem bops_ok5 : chkBOpsTo (pB 701077) bopsChunk5 (pB 6926997) = true := PalomarZF207.tm_bops_part2.2.1
private theorem bops_ok6 : chkBOpsTo (pB 6926997) bopsChunk6 (pB 3912341) = true := PalomarZF207.tm_bops_part2.2.2.1
private theorem bops_ok7 : chkBOpsTo (pB 3912341) bopsChunk7 (pB 881301) = true := PalomarZF207.tm_bops_part2.2.2.2
private theorem bops_ok8 : chkBOpsTo (pB 881301) bopsChunk8 (pB 6805) = true := PalomarZF207.tm_bops_part3.1
private theorem bops_ok9 : chkBOpsTo (pB 6805) bopsChunk9 (pB 375445) = true := PalomarZF207.tm_bops_part3.2.1
private theorem bops_ok10 : chkBOpsTo (pB 375445) bopsChunk10 (pB 90517) = true := PalomarZF207.tm_bops_part3.2.2.1
private theorem bops_ok11 : chkBOpsTo (pB 90517) bopsChunk11 (pB 45461) = true := PalomarZF207.tm_bops_part3.2.2.2
private theorem bops_ok12 : chkBOpsTo (pB 45461) bopsChunk12 (pB 2453) = true := PalomarZF207.tm_bops_part4.1
private theorem bops_ok13 : chkBOpsTo (pB 2453) bopsChunk13 (pB 88469) = true := PalomarZF207.tm_bops_part4.2.1
private theorem bops_ok14 : chkBOpsTo (pB 88469) bopsChunk14 (pB 80277) = true := PalomarZF207.tm_bops_part4.2.2.1
private theorem bops_ok15 : chkBOpsTo (pB 80277) bopsChunk15 (pB 30101) = true := PalomarZF207.tm_bops_part4.2.2.2
private theorem bops_ok16 : chkBOpsTo (pB 30101) bopsChunk16 (pB 2965) = true := PalomarZF207.tm_bops_part5.1
private theorem bops_ok17 : chkBOpsTo (pB 2965) bopsChunk17 (pB 14229) = true := PalomarZF207.tm_bops_part5.2.1
private theorem bops_ok18 : chkBOpsTo (pB 14229) bopsChunk18 (pB 12181) = true := PalomarZF207.tm_bops_part5.2.2

private def sNc (B : Sym) : Sym := .ic B .one
private def sRho8 (a b c u : Sym) : Sym := .ic (.ic (.ic c u) a) (.ic (.ic a c) (.ic b c))
private def sHead1 (x y : Sym) : Sym := .ic (sNc (.uc y (sNc (.uc y x)))) x
private def sHead2 (x y z : Sym) : Sym := .ic (.uc y (.uc z x)) (.uc z (.uc y x))
private def sHead3 (x y z : Sym) : Sym := .ic (.mc x y) (.ic (.ec x z) (.mc z y))
private def sHead4 (x y z : Sym) : Sym := .ic (.ec x y) (.ic (.mc z x) (.mc z y))
private def sHead5 (x y : Sym) : Sym := sNc (.uc y (sNc (.ec x y)))
private def sHead6 (x y z : Sym) : Sym := .ic (.uc y z) (.ic (.uc y (.ic z x)) (.uc y x))
private def sGateG (a b c : Sym) : Sym :=
  let subBA := .uc c (.ic (.mc c b) (.mc c a))
  let stepEx := sNc (.uc a (.ic c (sNc (.mc a c))))
  let stepAll := .uc a (.ic c stepEx)
  let hullBody := sNc (.uc b (.ic c (sNc (.uc b (.ic subBA stepAll)))))
  let lhs := .uc a (.ic (.mc a c) hullBody)
  let rhs := sNc (.ic c (.mc a c))
  .ic lhs rhs
private def sGateF (a b c : Sym) : Sym :=
  let delta := .ic (.ec a b) (.uc c (.ec a b))
  let vax := .ic (.mc a b) (.uc c (.mc a b))
  let q := .uc c (sGateG a b c)
  sNc (.ic delta (.ic vax q))

private def initSym : SymState :=
  { stk := [], r2 := .w0, r3 := .vF0, r4 := .vU0, r5 := .vZ, r8 := .vG0 }

private def finalSym : SymState :=
  { stk := [sHead6 .vX .vY .vZ, sHead5 .vX .vY, sHead4 .vX .vY .vZ, sHead3 .vX .vY .vZ,
            sHead2 .vX .vY .vZ, sHead1 .vX .vY, sRho8 .vY .vZ .vX .vU0, .uc .vU0 .vG0, .vF0],
    r2 := .w2, r3 := sGateF .vX .vY .vZ, r4 := .vY, r5 := .vZ, r8 := .vX }

set_option maxRecDepth 8192 in
private theorem branchB_sym_ok : symRun allBOps initSym = some finalSym := rfl

private theorem branchB_body_sound :
    ∀ s0 w0 f0 g0 u0 z ctr,
      RegReach (pB 149) (initSym.toRegs s0 w0 f0 g0 u0 z ctr) (pB 12181) (finalSym.toRegs s0 w0 f0 g0 u0 z ctr) :=
  symRun_split bops_ok0 (pB_length 149)
  (fun _ => symRun_split bops_ok1 (pB_length 1356437)
  (fun _ => symRun_split bops_ok2 (pB_length 56406677)
  (fun _ => symRun_split bops_ok3 (pB_length 98349717)
  (fun _ => symRun_split bops_ok4 (pB_length 192721557)
  (fun _ => symRun_split bops_ok5 (pB_length 701077)
  (fun _ => symRun_split bops_ok6 (pB_length 6926997)
  (fun _ => symRun_split bops_ok7 (pB_length 3912341)
  (fun _ => symRun_split bops_ok8 (pB_length 881301)
  (fun _ => symRun_split bops_ok9 (pB_length 6805)
  (fun _ => symRun_split bops_ok10 (pB_length 375445)
  (fun _ => symRun_split bops_ok11 (pB_length 90517)
  (fun _ => symRun_split bops_ok12 (pB_length 45461)
  (fun _ => symRun_split bops_ok13 (pB_length 2453)
  (fun _ => symRun_split bops_ok14 (pB_length 88469)
  (fun _ => symRun_split bops_ok15 (pB_length 80277)
  (fun _ => symRun_split bops_ok16 (pB_length 30101)
  (fun _ => symRun_split bops_ok17 (pB_length 2965)
  (fun _ hs18 => symRun_to_sound bopsChunk18 (pB 14229) (pB 12181) _ finalSym bops_ok18 hs18 (pB_length 14229)))))))))))))))))))
  branchB_sym_ok

/-! #### 4.4 ProvStack & Complete Program Soundness Invariant -/

private inductive ProvStack : Nat → Prop where
  | nil : ProvStack 0
  | cons {a s : Nat} : ProvC a → ProvStack s → ProvStack (cantor a s)

private theorem ProvStack.unpair_parts {n : Nat} (h : ProvStack n) :
    ProvC (unpair n).1 ∧ ProvStack (unpair n).2 := by
  cases h with
  | nil => exact ⟨.truth, .nil⟩
  | cons ha hs => rw [unpair_cantor]; exact ⟨ha, hs⟩

private def LoopInv (rs : List Nat) : Prop :=
  ∃ r1 r2 r3 r4 r7 r8, rs = [r1, r2, r3, r4, 0, 0, r7, r8, 0] ∧
    ProvStack r1 ∧ ProvC r3 ∧ ProvC r8

-- Branch B tail check (12181 -> 1)
private def chkBranchBTail (p : List Bool) : Bool :=
  match chkLin2 p 4 5 8 with
  | some pt1 =>
    match chkEq89 pt1 with
    | some (eqB1, neqB1) =>
      match chkZero eqB1 2 with
      | some z1 =>
        if reachesGoto 25 z1 neqB1 then
          match chkMove neqB1 8 5 with
          | some pt2 =>
            match chkMove pt2 7 3 with
            | some pt3 =>
              match chkEq89 pt3 with
              | some (eqB2, neqB2) =>
                if reachesGoto 25 neqB2 (pB 1) then
                  match chkZero eqB2 2 with
                  | some z2 => reachesGoto 25 z2 (pB 1)
                  | none => false
                else false
              | none => false
            | none => false
          | none => false
        else false
      | none => false
    | none => false
  | none => false

set_option maxRecDepth 8192 in
private theorem branchBTail_ok : chkBranchBTail (pB 12181) = true := rfl

private theorem branchB_sound (s0 w0 f0 u0 z ctr g0 : Nat)
    (hs0 : ProvStack s0) (hf0 : ProvC f0) (hg0 : ProvC g0) :
    ∃ rs', LoopInv rs' ∧ RegReachPos (pB 149) [s0, w0, f0, u0, z, 0, ctr, g0, 0] (pB 1) rs' := by
  have hrb := branchB_body_sound s0 w0 f0 g0 u0 z ctr
  let x := g0 + (unpair w0).1
  let y := u0 + (unpair (unpair w0).2).1
  let w2 := (unpair (unpair w0).2).2
  let s1 := evalStack s0 f0 g0 u0 x y z finalSym.stk
  have hs1 : ProvStack s1 := by
    dsimp only [s1, finalSym, evalStack, Sym.eval, sHead1, sHead2, sHead3, sHead4, sHead5, sHead6, sRho8, sNc]
    exact .cons (.ax_h6 x y z) (.cons (.ax_h5 x y) (.cons (.ax_h4 x y z) (.cons (.ax_h3 x y z)
      (.cons (.ax_h2 x y z) (.cons (.ax_h1 x y) (.cons (.ax_rho8 y z x u0)
      (.cons (.gen u0 hg0) (.cons hf0 hs0))))))))
  have hfg : finalSym.r3.eval f0 g0 u0 x y z = gateF x y z := rfl
  have hrb' : RegReach (pB 149) [s0, w0, f0, u0, z, 0, ctr, g0, 0] (pB 12181) [s1, w2, gateF x y z, y, z, 0, ctr, x, 0] := hrb
  have ht := branchBTail_ok
  unfold chkBranchBTail at ht
  cases hlin : chkLin2 (pB 12181) 4 5 8 with
  | none => rw [hlin] at ht; simp at ht
  | some pt1 =>
    rw [hlin] at ht; dsimp only at ht
    cases heq1 : chkEq89 pt1 with
    | none => rw [heq1] at ht; simp at ht
    | some p1p =>
      rcases p1p with ⟨eqB1, neqB1⟩; rw [heq1] at ht; dsimp only at ht
      cases hz1 : chkZero eqB1 2 with
      | none => rw [hz1] at ht; simp at ht
      | some z1 =>
        rw [hz1] at ht; dsimp only at ht
        have hz1e : reachesGoto 25 z1 neqB1 = true := by split at ht <;> first | assumption | contradiction
        rw [if_pos hz1e] at ht
        cases hm1 : chkMove neqB1 8 5 with
        | none => rw [hm1] at ht; simp at ht
        | some pt2 =>
          rw [hm1] at ht; dsimp only at ht
          cases hm2 : chkMove pt2 7 3 with
          | none => rw [hm2] at ht; simp at ht
          | some pt3 =>
            rw [hm2] at ht; dsimp only at ht
            cases heq2 : chkEq89 pt3 with
            | none => rw [heq2] at ht; simp at ht
            | some p2p =>
              rcases p2p with ⟨eqB2, neqB2⟩; rw [heq2] at ht; dsimp only at ht
              have hneq2e : reachesGoto 25 neqB2 (pB 1) = true := by split at ht <;> first | assumption | contradiction
              rw [if_pos hneq2e] at ht
              cases hz2 : chkZero eqB2 2 with
              | none => rw [hz2] at ht; simp at ht
              | some z2 =>
                rw [hz2] at ht; dsimp only at ht
                obtain ⟨_, _, _, hl1, rlin⟩ := chkLin2_sound (by decide) (by decide) (by decide) hlin (pB_length 12181)
                obtain ⟨hleq1, hlneq1, req1, rneq1⟩ := chkEq89_sound heq1 hl1
                obtain ⟨_, hlz1, rzero1⟩ := chkZero_sound hz1 hleq1
                obtain ⟨_, _, hl2, rmov1⟩ := chkMove_sound (by decide) hm1 hlneq1
                obtain ⟨_, _, hl3, rmov2⟩ := chkMove_sound (by decide) hm2 hl2
                obtain ⟨hleq2, hlneq2, req2, rneq2⟩ := chkEq89_sound heq2 hl3
                obtain ⟨_, hlz2, rzero2⟩ := chkZero_sound hz2 hleq2
                have s_lin := rlin [s1, w2, gateF x y z, y, z, 0, ctr, x, 0] rfl
                simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s_lin
                have hstep1 : ∃ f1, (f1 = 0 ∨ (z ≠ x ∧ f1 = gateF x y z)) ∧
                    RegReachPos (pB 12181) [s1, w2, gateF x y z, y, z, 0, ctr, x, 0] neqB1 [s1, w2, f1, y, 0, z, ctr, 0, 0] := by
                  by_cases hxz : x = z
                  · refine ⟨0, Or.inl rfl, ?_⟩
                    have s_e := req1 [s1, w2, gateF x y z, y, 0, z, ctr, x, z] rfl (by simp [regGet_zero, regGet_succ, hxz])
                    have s_z := rzero1 [s1, w2, gateF x y z, y, 0, z, ctr, 0, 0] rfl
                    simp only [regGet_zero, regGet_succ, regSet] at s_e s_z
                    have rg1 := regReach_goto hz1e hlz1 [s1, w2, 0, y, 0, z, ctr, 0, 0]
                    exact ((s_lin.trans s_e.of_pos).trans s_z.of_pos).trans rg1
                  · refine ⟨gateF x y z, Or.inr ⟨Ne.symm hxz, rfl⟩, ?_⟩
                    have s_n := rneq1 [s1, w2, gateF x y z, y, 0, z, ctr, x, z] rfl (by simp [regGet_zero, regGet_succ, hxz])
                    simp only [regGet_zero, regGet_succ, regSet] at s_n
                    exact s_lin.trans s_n.of_pos
                obtain ⟨f1, hf1_spec, r_neq1⟩ := hstep1
                have s_m1 := rmov1 [s1, w2, f1, y, 0, z, ctr, 0, 0] rfl
                have s_m2 := rmov2 [s1, w2, f1, y, 0, 0, ctr, 0, z] rfl
                simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s_m1 s_m2
                by_cases hyz : y = z
                · refine ⟨[s1, w2, 0, 0, 0, 0, ctr, 0, 0], ⟨s1, w2, 0, 0, ctr, 0, rfl, hs1, .truth, .truth⟩, ?_⟩
                  have s_e2 := req2 [s1, w2, f1, 0, 0, 0, ctr, y, z] rfl (by simp [regGet_zero, regGet_succ, hyz])
                  have s_z2 := rzero2 [s1, w2, f1, 0, 0, 0, ctr, 0, 0] rfl
                  simp only [regGet_zero, regGet_succ, regSet] at s_e2 s_z2
                  have rg2 := regReach_goto ht hlz2 [s1, w2, 0, 0, 0, 0, ctr, 0, 0]
                  exact hrb'.trans_pos (((((r_neq1.trans s_m1.of_pos).trans s_m2.of_pos).trans s_e2.of_pos).trans s_z2.of_pos).trans rg2)
                · have hf1_prov : ProvC f1 := by
                    rcases hf1_spec with rfl | ⟨hzx, rfl⟩
                    · exact .truth
                    · exact .ax_gate x y z hzx (Ne.symm hyz)
                  refine ⟨[s1, w2, f1, 0, 0, 0, ctr, 0, 0], ⟨s1, w2, f1, 0, ctr, 0, rfl, hs1, hf1_prov, .truth⟩, ?_⟩
                  have s_n2 := rneq2 [s1, w2, f1, 0, 0, 0, ctr, y, z] rfl (by simp [regGet_zero, regGet_succ, hyz])
                  simp only [regGet_zero, regGet_succ, regSet] at s_n2
                  have rg2 := regReach_goto hneq2e hlneq2 [s1, w2, f1, 0, 0, 0, ctr, 0, 0]
                  exact hrb'.trans_pos ((((r_neq1.trans s_m1.of_pos).trans s_m2.of_pos).trans s_n2.of_pos).trans rg2)

-- Branch A check (85 -> 1)
private def chkBranchA (p : List Bool) : Bool :=
  match chkUnpair p 1 3 with
  | some pa1 =>
    match chkPushR3 pa1 with
    | some pa2 =>
      match chkCopy3 pa2 3 with
      | some pa3 =>
        match chkPopPair4 pa3 with
        | some pa4 =>
          match chkMove pa4 8 2 with
          | some pa5 =>
            match chkEq89 pa5 with
            | some (eqA, neqA) =>
              if reachesGoto 25 neqA (pB 1) then
                match chkPushR3 eqA with
                | some pa6 =>
                  match chkCopy3 pa6 3 with
                  | some pa7 => reachesGoto 25 pa7 (pB 1)
                  | none => false
                | none => false
              else false
            | none => false
          | none => false
        | none => false
      | none => false
    | none => false
  | none => false

set_option maxRecDepth 8192 in
private theorem branchA_ok : chkBranchA (pB 85) = true := rfl

private theorem branchA_sound (r1 w r3 r4 ctr r8 : Nat)
    (hr1 : ProvStack r1) (hr3 : ProvC r3) (hr8 : ProvC r8) :
    ∃ rs', LoopInv rs' ∧ RegReachPos (pB 85) [r1, w, r3, r4, 0, 0, ctr, r8, 0] (pB 1) rs' := by
  have ht := branchA_ok
  unfold chkBranchA at ht
  cases hu : chkUnpair (pB 85) 1 3 with
  | none => rw [hu] at ht; simp at ht
  | some pa1 =>
    rw [hu] at ht; dsimp only at ht
    cases hp : chkPushR3 pa1 with
    | none => rw [hp] at ht; simp at ht
    | some pa2 =>
      rw [hp] at ht; dsimp only at ht
      cases hc : chkCopy3 pa2 3 with
      | none => rw [hc] at ht; simp at ht
      | some pa3 =>
        rw [hc] at ht; dsimp only at ht
        cases hpop : chkPopPair4 pa3 with
        | none => rw [hpop] at ht; simp at ht
        | some pa4 =>
          rw [hpop] at ht; dsimp only at ht
          cases hm : chkMove pa4 8 2 with
          | none => rw [hm] at ht; simp at ht
          | some pa5 =>
            rw [hm] at ht; dsimp only at ht
            cases heq : chkEq89 pa5 with
            | none => rw [heq] at ht; simp at ht
            | some eqp =>
              rcases eqp with ⟨eqA, neqA⟩; rw [heq] at ht; dsimp only at ht
              have hneqe : reachesGoto 25 neqA (pB 1) = true := by split at ht <;> first | assumption | contradiction
              rw [if_pos hneqe] at ht
              cases hp2 : chkPushR3 eqA with
              | none => rw [hp2] at ht; simp at ht
              | some pa6 =>
                rw [hp2] at ht; dsimp only at ht
                cases hc2 : chkCopy3 pa6 3 with
                | none => rw [hc2] at ht; simp at ht
                | some pa7 =>
                  rw [hc2] at ht; dsimp only at ht
                  obtain ⟨_, _, hl1, ru⟩ := chkUnpair_sound (by decide) (by decide) (by decide) (by decide) (by decide) hu (pB_length 85)
                  obtain ⟨hl2, rp⟩ := chkPushR3_sound hp hl1
                  obtain ⟨_, hl3, rc⟩ := chkCopy3_sound (by decide) (by decide) hc hl2
                  obtain ⟨hl4, rpop⟩ := chkPopPair4_sound hpop hl3
                  obtain ⟨_, _, hl5, rm⟩ := chkMove_sound (by decide) hm hl4
                  obtain ⟨hleq, hlneq, req, rneq⟩ := chkEq89_sound heq hl5
                  obtain ⟨hl6, rp2⟩ := chkPushR3_sound hp2 hleq
                  obtain ⟨_, hl7, rc2⟩ := chkCopy3_sound (by decide) (by decide) hc2 hl6
                  let B := r4 + (unpair w).1
                  let w' := (unpair w).2
                  have s1 := ru [r1, w, r3, r4, 0, 0, ctr, r8, 0] rfl rfl rfl
                  have s2 := rp r1 w' r3 B 0 ctr r8
                  have s3 := rc [cantor r3 r1, w', 0, B, 0, 0, ctr, r8, 0] rfl rfl
                  have s4 := rpop r3 r1 w' B B 0 ctr r8
                  have s5 := rm [r1, w', Ic r3 B, B, 0, 0, ctr, r8, 0] rfl
                  simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s1 s3 s5
                  have hpre : RegReachPos (pB 85) [r1, w, r3, r4, 0, 0, ctr, r8, 0] pa5 [r1, w', 0, B, 0, 0, ctr, r8, Ic r3 B] :=
                    (((s1.trans s2.of_pos).trans s3.of_pos).trans s4.of_pos).trans s5.of_pos
                  by_cases hmp : r8 = Ic r3 B
                  · have hB : ProvC B := by rw [hmp] at hr8; exact .mp hr8 hr3
                    have s6 := req [r1, w', 0, B, 0, 0, ctr, r8, Ic r3 B] rfl (by simp [regGet_zero, regGet_succ, hmp])
                    have s7 := rp2 r1 w' 0 B 0 ctr 0
                    have s8 := rc2 [cantor 0 r1, w', 0, B, 0, 0, ctr, 0, 0] rfl rfl
                    simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s6 s8
                    have rg := regReach_goto ht hl7 [cantor 0 r1, w', B, B, 0, 0, ctr, 0, 0]
                    refine ⟨[cantor 0 r1, w', B, B, 0, 0, ctr, 0, 0],
                      ⟨cantor 0 r1, w', B, B, ctr, 0, rfl, .cons .truth hr1, hB, .truth⟩,
                      (((hpre.trans s6.of_pos).trans s7.of_pos).trans s8.of_pos).trans rg⟩
                  · have s6 := rneq [r1, w', 0, B, 0, 0, ctr, r8, Ic r3 B] rfl (by simp [regGet_zero, regGet_succ, hmp])
                    simp only [regGet_zero, regGet_succ, regSet] at s6
                    have rg := regReach_goto hneqe hlneq [r1, w', 0, B, 0, 0, ctr, 0, 0]
                    refine ⟨[r1, w', 0, B, 0, 0, ctr, 0, 0],
                      ⟨r1, w', 0, B, ctr, 0, rfl, hr1, .truth, .truth⟩,
                      (hpre.trans s6.of_pos).trans rg⟩

-- Top-level check (pref 0 and pref 1)
private def chkTop0 : Bool :=
  match chkEq89 (pB 0) with
  | some (_, neq1) =>
    match chkUnpair neq1 0 7 with
    | some p => reachesGoto 25 p (pB 1)
    | none => false
  | none => false

private def chkTop1 : Bool :=
  match resolveStep 25 (pB 1) with
  | some (_, .dec k1 p_unp p_z0) =>
    if Nat.beq k1 1 then
      let p_unp0 := resolveGoto 25 p_unp
      match chkLin2 p_z0 6 1 8 with
      | some pz1 =>
        match chkInc pz1 6 with
        | some pz2 =>
          match chkMove pz2 6 8 with
          | some pz3 =>
            if reachesGoto 25 pz3 p_unp0 then
              match chkUnpair p_unp0 1 4 with
              | some p_br =>
                match resolveStep 25 p_br with
                | some (_, .dec k2 p_br2 p_c0) =>
                  if Nat.beq k2 4 then
                    match chkMove p_c0 8 2 with
                    | some pc1 =>
                      match chkCopy3 pc1 7 with
                      | some pc2 =>
                        match chkInc pc2 8 with
                        | some pc3 =>
                          if reachesGoto 25 pc3 (pB 0) then
                            match resolveStep 25 p_br2 with
                            | some (_, .dec k3 pB_ pA_) =>
                              Nat.beq k3 4 && reachesGoto 25 pA_ (pB 85) && reachesGoto 25 pB_ (pB 149)
                            | _ => false
                          else false
                        | none => false
                      | none => false
                    | none => false
                  else false
                | _ => false
              | none => false
            else false
          | none => false
        | none => false
      | none => false
    else false
  | _ => false

set_option maxRecDepth 8192 in
private theorem top0_ok : chkTop0 = true := rfl
set_option maxRecDepth 8192 in
private theorem top1_ok : chkTop1 = true := rfl

private theorem loop1_step (rs : List Nat) (hinv : LoopInv rs) :
    ProvC 1 ∨ ∃ rs', LoopInv rs' ∧ RegReachPos (pB 1) rs (pB 1) rs' := by
  obtain ⟨r1, r2, r3, r4, r7, r8, rfl, hr1, hr3, hr8⟩ := hinv
  have ht1 := top1_ok; unfold chkTop1 at ht1
  cases hs1 : resolveStep 25 (pB 1) with
  | none => rw [hs1] at ht1; simp at ht1
  | some res1 =>
    rcases res1 with ⟨p1_0, ins1⟩
    cases ins1 with
    | inc _ _ => rw [hs1] at ht1; simp at ht1
    | dec k1 p_unp p_z0 =>
      rw [hs1] at ht1; dsimp only at ht1
      have hk1 : Nat.beq k1 1 = true := by split at ht1 <;> first | assumption | contradiction
      rw [if_pos hk1] at ht1
      have hk1e : k1 = 1 := Nat.eq_of_beq_eq_true hk1; subst hk1e
      cases hlin : chkLin2 p_z0 6 1 8 with
      | none => rw [hlin] at ht1; simp at ht1
      | some pz1 =>
        rw [hlin] at ht1; dsimp only at ht1
        cases hinc : chkInc pz1 6 with
        | none => rw [hinc] at ht1; simp at ht1
        | some pz2 =>
          rw [hinc] at ht1; dsimp only at ht1
          cases hmov : chkMove pz2 6 8 with
          | none => rw [hmov] at ht1; simp at ht1
          | some pz3 =>
            rw [hmov] at ht1; dsimp only at ht1
            have hpz3 : reachesGoto 25 pz3 (resolveGoto 25 p_unp) = true := by split at ht1 <;> first | assumption | contradiction
            rw [if_pos hpz3] at ht1
            cases hunp : chkUnpair (resolveGoto 25 p_unp) 1 4 with
            | none => rw [hunp] at ht1; simp at ht1
            | some p_br =>
              rw [hunp] at ht1; dsimp only at ht1
              cases hs2 : resolveStep 25 p_br with
              | none => rw [hs2] at ht1; simp at ht1
              | some res2 =>
                rcases res2 with ⟨pbr_0, ins2⟩
                cases ins2 with
                | inc _ _ => rw [hs2] at ht1; simp at ht1
                | dec k2 p_br2 p_c0 =>
                  rw [hs2] at ht1; dsimp only at ht1
                  have hk2 : Nat.beq k2 4 = true := by split at ht1 <;> first | assumption | contradiction
                  rw [if_pos hk2] at ht1
                  have hk2e : k2 = 4 := Nat.eq_of_beq_eq_true hk2; subst hk2e
                  cases hmc : chkMove p_c0 8 2 with
                  | none => rw [hmc] at ht1; simp at ht1
                  | some pc1 =>
                    rw [hmc] at ht1; dsimp only at ht1
                    cases hcc : chkCopy3 pc1 7 with
                    | none => rw [hcc] at ht1; simp at ht1
                    | some pc2 =>
                      rw [hcc] at ht1; dsimp only at ht1
                      cases hic : chkInc pc2 8 with
                      | none => rw [hic] at ht1; simp at ht1
                      | some pc3 =>
                        rw [hic] at ht1; dsimp only at ht1
                        have hpc3 : reachesGoto 25 pc3 (pB 0) = true := by split at ht1 <;> first | assumption | contradiction
                        rw [if_pos hpc3] at ht1
                        cases hs3 : resolveStep 25 p_br2 with
                        | none => rw [hs3] at ht1; simp at ht1
                        | some res3 =>
                          rcases res3 with ⟨pbr2_0, ins3⟩
                          cases ins3 with
                          | inc _ _ => rw [hs3] at ht1; simp at ht1
                          | dec k3 pB_ pA_ =>
                            rw [hs3] at ht1; dsimp only at ht1
                            have h12 := Bool.and_eq_true_iff.mp ht1
                            have h11 := Bool.and_eq_true_iff.mp h12.1
                            have hk3e : k3 = 4 := Nat.eq_of_beq_eq_true h11.1; subst hk3e
                            have hpAg := h11.2
                            have hpBg := h12.2
                            obtain ⟨_, _, hl_unp, hl_z0, _, _, _⟩ := resolveStep_sound_dec 25 (pB 1) p1_0 1 p_unp p_z0 hs1 (pB_length 1)
                            obtain ⟨hl_unp0, _⟩ := resolveGoto_sound 25 p_unp hl_unp
                            obtain ⟨_, _, _, hl_z1, rlin⟩ := chkLin2_sound (by decide) (by decide) (by decide) hlin hl_z0
                            obtain ⟨_, hl_z2, rinc⟩ := chkInc_sound hinc hl_z1
                            obtain ⟨_, _, hl_z3, rmov⟩ := chkMove_sound (by decide) hmov hl_z2
                            obtain ⟨_, _, hl_br, runp⟩ := chkUnpair_sound (by decide) (by decide) (by decide) (by decide) (by decide) hunp hl_unp0
                            obtain ⟨_, _, hl_br2, hl_c0, _, _, _⟩ := resolveStep_sound_dec 25 p_br pbr_0 4 p_br2 p_c0 hs2 hl_br
                            obtain ⟨_, _, hl_c1, rmc⟩ := chkMove_sound (by decide) hmc hl_c0
                            obtain ⟨_, hl_c2, rcc⟩ := chkCopy3_sound_gen (by decide) (by decide) hcc hl_c1
                            obtain ⟨_, hl_c3, ric⟩ := chkInc_sound hic hl_c2
                            obtain ⟨_, _, hl_pB, hl_pA, _, _, _⟩ := resolveStep_sound_dec 25 p_br2 pbr2_0 4 pB_ pA_ hs3 hl_br2
                            have hto_unp : ∃ w ctr,
                                RegReachPos (pB 1) [r1, r2, r3, r4, 0, 0, r7, r8, 0] (resolveGoto 25 p_unp) [r1, w, r3, r4, 0, 0, ctr, r8, 0] := by
                              cases r2 with
                              | zero =>
                                refine ⟨r7, r7 + 1, ?_⟩
                                have s0 := regReach_dec_z hs1 (pB_length 1) [r1, 0, r3, r4, 0, 0, r7, r8, 0] rfl rfl
                                have s1 := rlin [r1, 0, r3, r4, 0, 0, r7, r8, 0] rfl
                                have s2 := rinc [r1, r7, r3, r4, 0, 0, 0, r8, r7] rfl
                                have s3 := rmov [r1, r7, r3, r4, 0, 0, 1, r8, r7] rfl
                                simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s1 s2 s3
                                rw [show 1 + r7 = r7 + 1 by omega] at s3
                                have rg := regReach_goto hpz3 hl_z3 [r1, r7, r3, r4, 0, 0, r7 + 1, r8, 0]
                                exact (((s0.trans s1.of_pos).trans s2.of_pos).trans s3.of_pos).trans rg
                              | succ w' =>
                                refine ⟨w', r7, ?_⟩
                                have s0 := regReach_dec_nz hs1 (pB_length 1) [r1, w' + 1, r3, r4, 0, 0, r7, r8, 0] rfl (by simp [regGet_zero, regGet_succ])
                                simp only [regGet_zero, regGet_succ, regSet, Nat.add_sub_cancel] at s0
                                have rg := regReach_resolveGoto p_unp hl_unp [r1, w', r3, r4, 0, 0, r7, r8, 0]
                                exact s0.trans rg
                            obtain ⟨w, ctr, r_unp⟩ := hto_unp
                            have s_unp := runp [r1, w, r3, r4, 0, 0, ctr, r8, 0] rfl rfl rfl
                            simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s_unp
                            let op := (unpair w).1
                            let w' := (unpair w).2
                            have r_br : RegReachPos (pB 1) [r1, r2, r3, r4, 0, 0, r7, r8, 0] p_br [r1, w', r3, r4, op, 0, ctr, r8, 0] :=
                              r_unp.trans s_unp.of_pos
                            cases hop : op with
                            | zero =>
                              rw [hop] at r_br
                              by_cases hsum1 : r3 + r8 = 1
                              · left
                                have hcases : r3 = 1 ∨ r8 = 1 := by omega
                                rcases hcases with h | h
                                · rw [h] at hr3; exact hr3
                                · rw [h] at hr8; exact hr8
                              · right
                                have s_z := regReach_dec_z hs2 hl_br [r1, w', r3, r4, 0, 0, ctr, r8, 0] rfl rfl
                                have s_mc := rmc [r1, w', r3, r4, 0, 0, ctr, r8, 0] rfl
                                have s_cc := rcc [r1, w', 0, r4, 0, 0, ctr, r8, r3] rfl
                                have s_ic := ric [r1, w', r8, r4, 0, 0, ctr, r3 + r8, 0] rfl
                                simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s_mc s_cc s_ic
                                have rg0 := regReach_goto hpc3 hl_c3 [r1, w', r8, r4, 0, 0, ctr, r3 + r8, 1]
                                have ht0 := top0_ok; unfold chkTop0 at ht0
                                cases heq0 : chkEq89 (pB 0) with
                                | none => rw [heq0] at ht0; simp at ht0
                                | some eq0p =>
                                  rcases eq0p with ⟨_, neq1⟩; rw [heq0] at ht0; dsimp only at ht0
                                  cases hu0 : chkUnpair neq1 0 7 with
                                  | none => rw [hu0] at ht0; simp at ht0
                                  | some p1' =>
                                    rw [hu0] at ht0; dsimp only at ht0
                                    obtain ⟨_, hl_neq1, _, rneq0⟩ := chkEq89_sound heq0 (pB_length 0)
                                    obtain ⟨_, _, hl_p1', ru0⟩ := chkUnpair_sound (by decide) (by decide) (by decide) (by decide) (by decide) hu0 hl_neq1
                                    have s_neq := rneq0 [r1, w', r8, r4, 0, 0, ctr, r3 + r8, 1] rfl (by simp [regGet_zero, regGet_succ, hsum1])
                                    have s_u0 := ru0 [r1, w', r8, r4, 0, 0, ctr, 0, 0] rfl rfl rfl
                                    simp only [regGet_zero, regGet_succ, regSet, Nat.zero_add] at s_neq s_u0
                                    have rg1 := regReach_goto ht0 hl_p1' [(unpair r1).2, w', r8, r4, 0, 0, ctr, (unpair r1).1, 0]
                                    obtain ⟨hp_hd, hp_tl⟩ := hr1.unpair_parts
                                    exact ⟨[(unpair r1).2, w', r8, r4, 0, 0, ctr, (unpair r1).1, 0],
                                      ⟨(unpair r1).2, w', r8, r4, ctr, (unpair r1).1, rfl, hp_tl, hr8, hp_hd⟩,
                                      ((((((r_br.trans s_z.of_pos).trans s_mc.of_pos).trans s_cc.of_pos).trans s_ic.of_pos).trans rg0).trans s_neq.of_pos).trans (s_u0.of_pos.trans rg1)⟩
                            | succ op1 =>
                              rw [hop] at r_br
                              right
                              have s_nz1 := regReach_dec_nz hs2 hl_br [r1, w', r3, r4, op1 + 1, 0, ctr, r8, 0] rfl (by simp [regGet_zero, regGet_succ])
                              simp only [regGet_zero, regGet_succ, regSet, Nat.add_sub_cancel] at s_nz1
                              cases op1 with
                              | zero =>
                                have s_z2 := regReach_dec_z hs3 hl_br2 [r1, w', r3, r4, 0, 0, ctr, r8, 0] rfl rfl
                                have rgA := regReach_goto hpAg hl_pA [r1, w', r3, r4, 0, 0, ctr, r8, 0]
                                obtain ⟨rs', hinv', rA⟩ := branchA_sound r1 w' r3 r4 ctr r8 hr1 hr3 hr8
                                exact ⟨rs', hinv', (((r_br.trans s_nz1.of_pos).trans s_z2.of_pos).trans rgA).trans rA.of_pos⟩
                              | succ z =>
                                have s_nz2 := regReach_dec_nz hs3 hl_br2 [r1, w', r3, r4, z + 1, 0, ctr, r8, 0] rfl (by simp [regGet_zero, regGet_succ])
                                simp only [regGet_zero, regGet_succ, regSet, Nat.add_sub_cancel] at s_nz2
                                have rgB := regReach_goto hpBg hl_pB [r1, w', r3, r4, z, 0, ctr, r8, 0]
                                obtain ⟨rs', hinv', rB⟩ := branchB_sound r1 w' r3 r4 z ctr r8 hr1 hr3 hr8
                                exact ⟨rs', hinv', (((r_br.trans s_nz1.of_pos).trans s_nz2.of_pos).trans rgB).trans rB.of_pos⟩

private theorem halts_step_down {c1 c2 : Nat × Nat × Nat} {n : Nat}
    (hr : SafeReachPos c1 c2) (hh : (iterPhysical n c1).1 ≥ 207) :
    ∃ n', n' < n ∧ (iterPhysical n' c2).1 ≥ 207 := by
  obtain ⟨k, hkpos, hkeq, hksafe⟩ := hr
  have hle : k ≤ n := by
    apply Nat.le_of_not_lt; intro hlt
    have := hksafe n hlt; omega
  refine ⟨n - k, by omega, ?_⟩
  have hadd : k + (n - k) = n := by omega
  rw [← hkeq, ← iterPhysical_add, hadd]; exact hh

private theorem halts_from_loop1 : ∀ n, ∀ m t rs, 1 ≤ m → 1 ≤ t → LoopInv rs →
    (iterPhysical n (frameBits (pB 1) m rs t)).1 ≥ 207 → ProvC 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m t rs hm ht hinv hh
    rcases loop1_step rs hinv with h1 | ⟨rs', hinv', hr⟩
    · exact h1
    · obtain ⟨m', t', hm', ht', hsafe⟩ := hr m t hm ht
      obtain ⟨n', hlt, hh'⟩ := halts_step_down hsafe hh
      exact ih n' hlt m' t' rs' hm' ht' hinv' hh'

theorem physicalHalts_implies_provC_one (h : PhysicalHalts207) : ProvC 1 := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨k, hkeq, hksafe⟩ := startup_safe_reach
  rw [startup_is_frame] at hkeq
  have hle : k ≤ n := by
    apply Nat.le_of_not_lt; intro hlt
    have := hksafe n hlt; omega
  have hh : (iterPhysical (n - k) (frameBits (pB 1) 6 [0, 0, 0, 0, 0, 0, 2, 0, 0] 26)).1 ≥ 207 := by
    have hadd : k + (n - k) = n := by omega
    change (iterPhysical (n - k) (frameState 1 6 [0, 0, 0, 0, 0, 0, 2, 0, 0] 26)).1 ≥ 207
    rw [← hkeq, ← iterPhysical_add, hadd]; exact hn
  have hinit : LoopInv [0, 0, 0, 0, 0, 0, 2, 0, 0] :=
    ⟨0, 0, 0, 0, 2, 0, rfl, .nil, .truth, .truth⟩
  exact halts_from_loop1 (n - k) 6 26 [0, 0, 0, 0, 0, 0, 2, 0, 0] (by omega) (by omega) hinit hh

end DevTMSound

theorem solution : PhysicalHalts207 → PalomarZF207Calc.ProvC 1 :=
  DevTMSound.physicalHalts_implies_provC_one
