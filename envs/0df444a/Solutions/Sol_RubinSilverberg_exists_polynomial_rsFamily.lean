-- Prove2me | solution 1 for RubinSilverberg.exists_polynomial_rsFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2a6c85e9-1d00-5457-bf17-dfc4915166f4

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_exists_polynomial_rsFamily

set_option autoImplicit false

def hornerN (l : List Nat) (x : Nat) : Nat := l.foldr (fun a acc => a + x * acc) 0

def naS  : List Nat := [1050565743469874507983410599, 14997184216447495056504351, 94852424902970201581820, 348716791109098206246, 820885301671395486, 1282425059839248, 1328703503972, 879654210, 337307, 57]
def ngS  : List Nat := [13286871262660103049895857, 198289139929260102942493, 1308180436672455431010, 5006339152104133228, 12243368615082048, 19833325794114, 21268035846, 14545780, 5751, 1]
def dtpS : List Nat := [366599, 1211, 1]
def a4zS : List Nat := [80529976801, 618353028, 1750094, 2172, 1]
def a6zS : List Nat := [85950068397886801, 796171667993478, 3049909189995, 6175188000, 6955995, 4122, 1]

def tabA : List (Nat × Nat × Nat × List (Nat × Nat × Nat) × List (Nat × Nat × Nat)) := [
  (1, 0, 16, [(1, 0, 0)], []),
  (0, 0, 16, [(1, 0, 0)], []),
  (190, 1, 15, [], [(1, 0, 0)]),
  (2280, 2, 14, [], [(1, 0, 0)]),
  (855, 2, 13, [], [(17, 0, 1), (16, 1, 0)]),
  (3648, 3, 12, [], [(17, 0, 1), (9, 1, 0)]),
  (11400, 3, 12, [], [(17, 0, 1), (8, 1, 0)]),
  (27360, 4, 11, [(26, 1, 0)], [(17, 0, 1)]),
  (7410, 4, 10, [(448, 1, 1), (432, 2, 0)], [(119, 0, 2)]),
  (79040, 5, 9, [(145, 1, 1), (108, 2, 0)], [(17, 0, 2)]),
  (8892, 5, 8, [(2640, 1, 2), (5104, 2, 1), (1152, 3, 0)], [(187, 0, 3)]),
  (98800, 6, 8, [(388, 1, 1), (864, 2, 0)], [(17, 0, 2)]),
  (7410, 6, 7, [(6160, 1, 2), (24464, 2, 1), (24192, 3, 0)], [(187, 0, 3)]),
  (54720, 7, 6, [(795, 1, 2), (3944, 2, 1), (9072, 3, 0)], [(17, 0, 3)]),
  (2280, 7, 5, [(13832, 1, 3), (103792, 2, 2), (554112, 3, 1), (373248, 4, 0)], [(221, 0, 4)]),
  (1824, 8, 4, [(9842, 1, 3), (92608, 2, 2), (911520, 3, 1), (373248, 4, 0)], [(119, 0, 4)]),
  (4275, 8, 4, [(1792, 1, 3), (23264, 2, 2), (378368, 3, 1), (338688, 4, 0)], [(17, 0, 4)]),
  (18240, 9, 3, [(133, 1, 3), (2132, 2, 2), (54000, 3, 1), (15552, 4, 0)], [(1, 0, 4)]),
  (190, 9, 2, [(2784, 1, 4), (58080, 2, 3), (2116864, 3, 2), (946944, 4, 1), (2985984, 5, 0)], [(17, 0, 5)]),
  (360, 10, 1, [(200, 1, 4), (5056, 2, 3), (259456, 3, 2), (1990656, 5, 0)], [(1, 0, 5), (154368, 4, 1)]),
  (1, 10, 0, [(4560, 1, 5), (144096, 2, 4), (9859328, 3, 3), (226934784, 5, 1), (429981696, 6, 0)], [(19, 0, 6), (8798976, 4, 2)])]

def phomN (l : List (Nat × Nat × Nat)) (Np D : Nat) : Nat :=
  l.foldr (fun e acc => acc + e.1 * Np ^ e.2.1 * D ^ e.2.2) 0

def rhsCoeffsA (s : Nat) : List Nat × List Nat :=
  let w := s + 600
  let d := hornerN dtpS s
  let h := hornerN a4zS s
  let lead := hornerN a4zS s
  let Np := h ^ 3
  let D := 1728 * w * d ^ 5
  let E := Np + D
  (tabA.map fun r => lead * (r.1 * E ^ r.2.1 * D ^ r.2.2.1 * phomN r.2.2.2.1 Np D),
   tabA.map fun r => lead * (r.1 * E ^ r.2.1 * D ^ r.2.2.1 * phomN r.2.2.2.2 Np D))

def lhsPairA (t s : Nat) : Nat × Nat :=
  let w := s + 600
  let d := hornerN dtpS s
  let P5 := (hornerN naS s * t + 144 * w * d ^ 4) ^ 5
  let R := (hornerN ngS s * t + 144 * d ^ 4) ^ 5 * w ^ 4
  (429981696 * (1 * P5 ^ 0 * R ^ 4 + 228 * P5 ^ 1 * R ^ 3 + 494 * P5 ^ 2 * R ^ 2 + 1 * P5 ^ 4 * R ^ 0),
   429981696 * (228 * P5 ^ 3 * R ^ 1))

def checkRangeA (lo len : Nat) : Bool :=
  ((List.range len).map (· + lo)).all fun s =>
    let cs := rhsCoeffsA s
    (List.range 21).all fun t =>
      let L := lhsPairA t s
      L.1 + hornerN cs.2 t == hornerN cs.1 t + L.2

theorem checkA_0 : checkRangeA 0 197 = true := by decide +kernel

def tabB : List (Nat × Nat × Nat × List (Nat × Nat × Nat) × List (Nat × Nat × Nat)) := [
  (1, 0, 24, [(1, 0, 0)], []),
  (30, 0, 24, [(1, 0, 0)], []),
  (435, 1, 23, [(1, 0, 0)], []),
  (580, 1, 22, [(7, 0, 1), (9, 1, 0)], []),
  (3915, 2, 21, [(7, 0, 1), (8, 1, 0)], []),
  (1566, 2, 20, [(91, 0, 2), (78, 1, 1), (48, 2, 0)], []),
  (84825, 3, 20, [(7, 0, 1)], [(16, 1, 0)]),
  (156600, 3, 19, [(13, 0, 2)], [(91, 1, 1), (92, 2, 0)]),
  (450225, 4, 18, [(13, 0, 2)], [(208, 1, 1), (144, 2, 0)]),
  (100050, 4, 17, [(143, 0, 3)], [(4004, 1, 2), (5632, 2, 1), (1728, 3, 0)]),
  (30015, 5, 16, [(1001, 0, 3)], [(45760, 1, 2), (44880, 2, 1), (6912, 3, 0)]),
  (600300, 5, 16, [(91, 0, 3)], [(6175, 1, 2), (9272, 2, 1), (2736, 3, 0)]),
  (950475, 6, 16, [(91, 0, 2)], [(8840, 1, 1), (7824, 2, 0)]),
  (17108550, 6, 15, [(7, 0, 3)], [(926, 1, 2), (1072, 2, 1), (544, 3, 0)]),
  (145422675, 7, 14, [(1, 0, 3)], [(176, 1, 2), (48, 2, 1), (384, 3, 0)]),
  (155117520, 8, 13, [(1, 0, 3), (176, 2, 1)], [(228, 1, 2), (1728, 3, 0)]),
  (145422675, 8, 12, [(1, 0, 4), (288, 2, 2)], [(288, 1, 3), (5120, 3, 1), (6912, 4, 0)]),
  (17108550, 8, 11, [(7, 0, 5), (3584, 2, 3)], [(2504, 1, 4), (93184, 3, 2), (283392, 4, 1), (165888, 5, 0)]),
  (950475, 9, 10, [(91, 0, 5), (122976, 2, 3)], [(39936, 1, 4), (2960384, 3, 2), (11577600, 4, 1), (5971968, 5, 0)]),
  (600300, 9, 9, [(91, 0, 6), (191568, 2, 4)], [(48243, 1, 5), (6310304, 3, 3), (40515072, 4, 2), (46455552, 5, 1), (11943936, 6, 0)]),
  (30015, 10, 8, [(1001, 0, 6), (3880800, 2, 4)], [(634920, 1, 5), (142879744, 3, 3), (1168475904, 4, 2), (1188919296, 5, 1), (143327232, 6, 0)]),
  (100050, 10, 8, [(143, 0, 6), (808368, 2, 4)], [(107250, 1, 5), (38518336, 3, 3), (451953408, 4, 2), (757651968, 5, 1), (367276032, 6, 0)]),
  (450225, 11, 7, [(13, 0, 6), (117216, 2, 4)], [(11440, 1, 5), (6444800, 3, 3), (94192384, 4, 2), (142000128, 5, 1), (95551488, 6, 0)]),
  (156600, 11, 6, [(13, 0, 7), (163284, 2, 5)], [(13299, 1, 6), (11171552, 3, 4), (217203840, 4, 3), (474406656, 5, 2), (747740160, 6, 1), (429981696, 7, 0)]),
  (6525, 12, 5, [(91, 0, 7), (1680624, 2, 5)], [(107536, 1, 6), (132912128, 3, 4), (3147511552, 4, 3), (6260502528, 5, 2), (21054173184, 6, 1), (10319560704, 7, 0)]),
  (1566, 12, 4, [(91, 0, 8), (2261248, 2, 6)], [(123292, 1, 7), (216211904, 3, 5), (6487793920, 4, 4), (17369596928, 5, 3), (97854234624, 6, 2), (96136740864, 7, 1), (20639121408, 8, 0)]),
  (3915, 13, 4, [(7, 0, 7), (242352, 2, 5)], [(10816, 1, 6), (26620160, 3, 4), (953885440, 4, 3), (2350596096, 5, 2), (26796552192, 6, 1), (13329432576, 7, 0)]),
  (580, 13, 3, [(7, 0, 8), (317176, 2, 6), (36118462464, 8, 0)], [(12259, 1, 7), (41205008, 3, 5), (1808220160, 4, 4), (5714806016, 5, 3), (93590857728, 6, 2), (70131806208, 7, 1)]),
  (435, 14, 2, [(1, 0, 8), (60720, 2, 6), (5016453120, 7, 1), (61917364224, 8, 0)], [(1976, 1, 7), (8987648, 3, 5), (463120640, 4, 4), (1359157248, 5, 3), (40644882432, 6, 2)]),
  (30, 14, 1, [(1, 0, 9), (77680, 2, 7), (24514928640, 7, 2), (509958291456, 8, 1), (743008370688, 9, 0)], [(2218, 1, 8), (13365152, 3, 6), (822366976, 4, 5), (2990693888, 5, 4), (118286217216, 6, 3)]),
  (1, 15, 0, [(1, 0, 9), (101040, 2, 7), (471904911360, 7, 2), (2600529297408, 8, 1), (8916100448256, 9, 0)], [(2480, 1, 8), (19642496, 3, 6), (1399023872, 4, 5), (4759216128, 5, 4), (315623485440, 6, 3)])]

def rhsCoeffsB (s : Nat) : List Nat × List Nat :=
  let w := s + 600
  let d := hornerN dtpS s
  let h := hornerN a4zS s
  let lead := hornerN a6zS s
  let Np := h ^ 3
  let D := 1728 * w * d ^ 5
  let E := Np + D
  (tabB.map fun r => lead * (r.1 * E ^ r.2.1 * D ^ r.2.2.1 * phomN r.2.2.2.1 Np D),
   tabB.map fun r => lead * (r.1 * E ^ r.2.1 * D ^ r.2.2.1 * phomN r.2.2.2.2 Np D))

def lhsPairB (t s : Nat) : Nat × Nat :=
  let w := s + 600
  let d := hornerN dtpS s
  let P5 := (hornerN naS s * t + 144 * w * d ^ 4) ^ 5
  let R := (hornerN ngS s * t + 144 * d ^ 4) ^ 5 * w ^ 4
  (8916100448256 * (1 * P5 ^ 0 * R ^ 6 + 522 * P5 ^ 5 * R ^ 1 + 1 * P5 ^ 6 * R ^ 0),
   8916100448256 * (522 * P5 ^ 1 * R ^ 5 + 10005 * P5 ^ 2 * R ^ 4 + 10005 * P5 ^ 4 * R ^ 2))

def checkRangeB (lo len : Nat) : Bool :=
  ((List.range len).map (· + lo)).all fun s =>
    let cs := rhsCoeffsB s
    (List.range 31).all fun t =>
      let L := lhsPairB t s
      L.1 + hornerN cs.2 t == hornerN cs.1 t + L.2

theorem checkB_0 : checkRangeB 0 99 = true := by decide +kernel

theorem checkB_1 : checkRangeB 99 99 = true := by decide +kernel

theorem checkB_2 : checkRangeB 198 97 = true := by decide +kernel

open Polynomial

namespace M4cP2
namespace D52

section Generic
variable {S : Type*} [CommSemiring S]

def hornerC (l : List ℕ) (x : S) : S := l.foldr (fun (a : ℕ) (acc : S) => (a : S) + x * acc) 0

def hornerG (l : List S) (x : S) : S := l.foldr (fun (a : S) (acc : S) => a + x * acc) 0

def phomG (l : List (ℕ × ℕ × ℕ)) (Np D : S) : S :=
  l.foldr (fun (e : ℕ × ℕ × ℕ) (acc : S) => acc + (e.1 : S) * Np ^ e.2.1 * D ^ e.2.2) 0

abbrev Row := ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)

def rhsCoeffsG (tab : List Row) (d h lead w : S) : List S × List S :=
  let Np := h ^ 3
  let D := 1728 * w * d ^ 5
  let E := Np + D
  (tab.map fun r => lead * ((r.1 : S) * E ^ r.2.1 * D ^ r.2.2.1 * phomG r.2.2.2.1 Np D),
   tab.map fun r => lead * ((r.1 : S) * E ^ r.2.1 * D ^ r.2.2.1 * phomG r.2.2.2.2 Np D))

def lhsPairAG (na ng d w t : S) : S × S :=
  let P5 := (na * t + 144 * w * d ^ 4) ^ 5
  let R := (ng * t + 144 * d ^ 4) ^ 5 * w ^ 4
  (429981696 * (1 * P5 ^ 0 * R ^ 4 + 228 * P5 ^ 1 * R ^ 3 + 494 * P5 ^ 2 * R ^ 2 + 1 * P5 ^ 4 * R ^ 0),
   429981696 * (228 * P5 ^ 3 * R ^ 1))

def lhsPairBG (na ng d w t : S) : S × S :=
  let P5 := (na * t + 144 * w * d ^ 4) ^ 5
  let R := (ng * t + 144 * d ^ 4) ^ 5 * w ^ 4
  (8916100448256 * (1 * P5 ^ 0 * R ^ 6 + 522 * P5 ^ 5 * R ^ 1 + 1 * P5 ^ 6 * R ^ 0),
   8916100448256 * (522 * P5 ^ 1 * R ^ 5 + 10005 * P5 ^ 2 * R ^ 4 + 10005 * P5 ^ 4 * R ^ 2))

def sidePlusA (na ng d h w t : S) : S :=
  (lhsPairAG na ng d w t).1 + hornerG (rhsCoeffsG tabA d h h w).2 t
def sideMinusA (na ng d h w t : S) : S :=
  hornerG (rhsCoeffsG tabA d h h w).1 t + (lhsPairAG na ng d w t).2
def sidePlusB (na ng d h lead w t : S) : S :=
  (lhsPairBG na ng d w t).1 + hornerG (rhsCoeffsG tabB d h lead w).2 t
def sideMinusB (na ng d h lead w t : S) : S :=
  hornerG (rhsCoeffsG tabB d h lead w).1 t + (lhsPairBG na ng d w t).2

end Generic

theorem hornerN_eq (l : List ℕ) (x : ℕ) : hornerN l x = hornerC l x := by
  unfold hornerN hornerC; simp only [Nat.cast_id]

theorem hornerN_eq' (l : List ℕ) (x : ℕ) : hornerN l x = hornerG l x := rfl

theorem phomN_eq (l : List (ℕ × ℕ × ℕ)) (Np D : ℕ) : phomN l Np D = phomG l Np D := by
  unfold phomN phomG; simp only [Nat.cast_id]

theorem lhsPairA_eq (t s : ℕ) :
    lhsPairA t s = lhsPairAG (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (s + 600) t := by
  simp only [lhsPairA, lhsPairAG, hornerN_eq]

theorem lhsPairB_eq (t s : ℕ) :
    lhsPairB t s = lhsPairBG (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (s + 600) t := by
  simp only [lhsPairB, lhsPairBG, hornerN_eq]

theorem rhsCoeffsA_eq (s : ℕ) :
    rhsCoeffsA s = rhsCoeffsG tabA (hornerC dtpS s) (hornerC a4zS s) (hornerC a4zS s) (s + 600) := by
  simp only [rhsCoeffsA, rhsCoeffsG, hornerN_eq, phomN_eq, Nat.cast_id]

theorem rhsCoeffsB_eq (s : ℕ) :
    rhsCoeffsB s = rhsCoeffsG tabB (hornerC dtpS s) (hornerC a4zS s) (hornerC a6zS s) (s + 600) := by
  simp only [rhsCoeffsB, rhsCoeffsG, hornerN_eq, phomN_eq, Nat.cast_id]

theorem certA_iff (t s : ℕ) :
    ((lhsPairA t s).1 + hornerN (rhsCoeffsA s).2 t = hornerN (rhsCoeffsA s).1 t + (lhsPairA t s).2) ↔
    (sidePlusA (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (hornerC a4zS s) (s + 600) t =
      sideMinusA (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (hornerC a4zS s) (s + 600) t) := by
  rw [lhsPairA_eq, rhsCoeffsA_eq, hornerN_eq', hornerN_eq']; rfl

theorem certB_iff (t s : ℕ) :
    ((lhsPairB t s).1 + hornerN (rhsCoeffsB s).2 t = hornerN (rhsCoeffsB s).1 t + (lhsPairB t s).2) ↔
    (sidePlusB (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (hornerC a4zS s) (hornerC a6zS s) (s + 600) t =
      sideMinusB (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (hornerC a4zS s) (hornerC a6zS s) (s + 600) t) := by
  rw [lhsPairB_eq, rhsCoeffsB_eq, hornerN_eq', hornerN_eq']; rfl

noncomputable def PhiPlusA (j : ℕ) : ℤ[X] :=
  sidePlusA (hornerC naS X) (hornerC ngS X) (hornerC dtpS X) (hornerC a4zS X) (X + 600) (j : ℤ[X])
noncomputable def PhiMinusA (j : ℕ) : ℤ[X] :=
  sideMinusA (hornerC naS X) (hornerC ngS X) (hornerC dtpS X) (hornerC a4zS X) (X + 600) (j : ℤ[X])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem natDegree_PhiA_le (j : ℕ) : (PhiPlusA j - PhiMinusA j).natDegree ≤ 196 := by
  unfold PhiPlusA PhiMinusA sidePlusA sideMinusA lhsPairAG rhsCoeffsG
  simp only [hornerC, hornerG, phomG, tabA, naS, ngS, dtpS, a4zS, List.foldr_cons, List.foldr_nil,
    List.map_cons, List.map_nil, mul_zero, add_zero]
  compute_degree!

noncomputable def PhiPlusB (j : ℕ) : ℤ[X] :=
  sidePlusB (hornerC naS X) (hornerC ngS X) (hornerC dtpS X) (hornerC a4zS X) (hornerC a6zS X) (X + 600)
    (j : ℤ[X])
noncomputable def PhiMinusB (j : ℕ) : ℤ[X] :=
  sideMinusB (hornerC naS X) (hornerC ngS X) (hornerC dtpS X) (hornerC a4zS X) (hornerC a6zS X) (X + 600)
    (j : ℤ[X])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem natDegree_PhiB_le (j : ℕ) : (PhiPlusB j - PhiMinusB j).natDegree ≤ 294 := by
  unfold PhiPlusB PhiMinusB sidePlusB sideMinusB lhsPairBG rhsCoeffsG
  simp only [hornerC, hornerG, phomG, tabB, naS, ngS, dtpS, a4zS, a6zS, List.foldr_cons, List.foldr_nil,
    List.map_cons, List.map_nil, mul_zero, add_zero]
  compute_degree!

section Map
variable {S T : Type*} [CommSemiring S] [CommSemiring T] (f : S →+* T)

theorem map_hornerC (l : List ℕ) (x : S) : f (hornerC l x) = hornerC l (f x) := by
  induction l with
  | nil => simp [hornerC]
  | cons a l ih =>
    simp only [hornerC, List.foldr_cons, map_add, map_natCast, map_mul] at ih ⊢
    rw [ih]

theorem map_hornerG (L : List S) (x : S) : f (hornerG L x) = hornerG (L.map f) (f x) := by
  induction L with
  | nil => simp [hornerG]
  | cons a L ih =>
    simp only [hornerG, List.foldr_cons, List.map_cons, map_add, map_mul] at ih ⊢
    rw [ih]

theorem map_phomG (l : List (ℕ × ℕ × ℕ)) (a b : S) : f (phomG l a b) = phomG l (f a) (f b) := by
  induction l with
  | nil => simp [phomG]
  | cons e l ih =>
    simp only [phomG, List.foldr_cons, map_add, map_mul, map_pow, map_natCast] at ih ⊢
    rw [ih]

theorem map_rhsCoeffsG_fst (tab : List Row) (d h lead w : S) :
    (rhsCoeffsG tab d h lead w).1.map f = (rhsCoeffsG tab (f d) (f h) (f lead) (f w)).1 := by
  simp only [rhsCoeffsG, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [map_phomG, map_natCast, map_ofNat]

theorem map_rhsCoeffsG_snd (tab : List Row) (d h lead w : S) :
    (rhsCoeffsG tab d h lead w).2.map f = (rhsCoeffsG tab (f d) (f h) (f lead) (f w)).2 := by
  simp only [rhsCoeffsG, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [map_phomG, map_natCast, map_ofNat]

theorem map_lhsPairAG (na ng d w t : S) :
    f (lhsPairAG na ng d w t).1 = (lhsPairAG (f na) (f ng) (f d) (f w) (f t)).1 ∧
    f (lhsPairAG na ng d w t).2 = (lhsPairAG (f na) (f ng) (f d) (f w) (f t)).2 := by
  constructor <;> simp [lhsPairAG, map_ofNat]

theorem map_lhsPairBG (na ng d w t : S) :
    f (lhsPairBG na ng d w t).1 = (lhsPairBG (f na) (f ng) (f d) (f w) (f t)).1 ∧
    f (lhsPairBG na ng d w t).2 = (lhsPairBG (f na) (f ng) (f d) (f w) (f t)).2 := by
  constructor <;> simp [lhsPairBG, map_ofNat]

theorem map_sidePlusA (na ng d h w t : S) :
    f (sidePlusA na ng d h w t) = sidePlusA (f na) (f ng) (f d) (f h) (f w) (f t) := by
  simp only [sidePlusA, map_add, (map_lhsPairAG f na ng d w t).1, map_hornerG, map_rhsCoeffsG_snd]

theorem map_sideMinusA (na ng d h w t : S) :
    f (sideMinusA na ng d h w t) = sideMinusA (f na) (f ng) (f d) (f h) (f w) (f t) := by
  simp only [sideMinusA, map_add, (map_lhsPairAG f na ng d w t).2, map_hornerG, map_rhsCoeffsG_fst]

theorem map_sidePlusB (na ng d h lead w t : S) :
    f (sidePlusB na ng d h lead w t) = sidePlusB (f na) (f ng) (f d) (f h) (f lead) (f w) (f t) := by
  simp only [sidePlusB, map_add, (map_lhsPairBG f na ng d w t).1, map_hornerG, map_rhsCoeffsG_snd]

theorem map_sideMinusB (na ng d h lead w t : S) :
    f (sideMinusB na ng d h lead w t) = sideMinusB (f na) (f ng) (f d) (f h) (f lead) (f w) (f t) := by
  simp only [sideMinusB, map_add, (map_lhsPairBG f na ng d w t).2, map_hornerG, map_rhsCoeffsG_fst]

theorem transportA (x : S) (j : ℕ)
    (h : sidePlusA (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (x + 600) (j : S) =
      sideMinusA (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (x + 600) (j : S)) :
    sidePlusA (hornerC naS (f x)) (hornerC ngS (f x)) (hornerC dtpS (f x)) (hornerC a4zS (f x)) (f x + 600)
        (j : T) =
      sideMinusA (hornerC naS (f x)) (hornerC ngS (f x)) (hornerC dtpS (f x)) (hornerC a4zS (f x)) (f x + 600)
        (j : T) := by
  have h' := congrArg f h
  rw [map_sidePlusA, map_sideMinusA, map_hornerC f naS, map_hornerC f ngS, map_hornerC f dtpS,
    map_hornerC f a4zS, map_add, map_ofNat, map_natCast] at h'
  exact h'

theorem transportB (x : S) (j : ℕ)
    (h : sidePlusB (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (hornerC a6zS x) (x + 600)
        (j : S) =
      sideMinusB (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (hornerC a6zS x) (x + 600)
        (j : S)) :
    sidePlusB (hornerC naS (f x)) (hornerC ngS (f x)) (hornerC dtpS (f x)) (hornerC a4zS (f x))
        (hornerC a6zS (f x)) (f x + 600) (j : T) =
      sideMinusB (hornerC naS (f x)) (hornerC ngS (f x)) (hornerC dtpS (f x)) (hornerC a4zS (f x))
        (hornerC a6zS (f x)) (f x + 600) (j : T) := by
  have h' := congrArg f h
  rw [map_sidePlusB, map_sideMinusB, map_hornerC f naS, map_hornerC f ngS, map_hornerC f dtpS,
    map_hornerC f a4zS, map_hornerC f a6zS, map_add, map_ofNat, map_natCast] at h'
  exact h'

end Map

theorem gridA (s : ℕ) (hs : s < 197) (t : ℕ) (ht : t < 21) :
    sidePlusA (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (hornerC a4zS s) (s + 600) t =
      sideMinusA (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (hornerC a4zS s) (s + 600) t := by
  have h := checkA_0
  unfold checkRangeA at h
  simp only [List.all_eq_true, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Nat.add_zero, beq_iff_eq] at h
  exact (certA_iff t s).mp (h s hs t ht)

theorem gridB (s : ℕ) (hs : s < 295) (t : ℕ) (ht : t < 31) :
    sidePlusB (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (hornerC a4zS s) (hornerC a6zS s) (s + 600) t =
      sideMinusB (hornerC naS s) (hornerC ngS s) (hornerC dtpS s) (hornerC a4zS s) (hornerC a6zS s)
        (s + 600) t := by
  have h0 := checkB_0
  have h1 := checkB_1
  have h2 := checkB_2
  unfold checkRangeB at h0 h1 h2
  simp only [List.all_eq_true, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Nat.add_zero, beq_iff_eq] at h0 h1 h2
  rw [← certB_iff]
  rcases lt_or_ge s 99 with h | h
  · exact h0 s h t ht
  rcases lt_or_ge s 198 with h' | h'
  · have := h1 (s - 99) (by omega) t ht
    rwa [Nat.sub_add_cancel h] at this
  · have := h2 (s - 198) (by omega) t ht
    rwa [Nat.sub_add_cancel h'] at this

section EvalZ

theorem eval_PhiPlusA (j : ℕ) (x : ℤ) : (PhiPlusA j).eval x =
    sidePlusA (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (x + 600) (j : ℤ) := by
  unfold PhiPlusA
  rw [← coe_evalRingHom, map_sidePlusA]
  simp [map_hornerC, map_natCast]

theorem eval_PhiMinusA (j : ℕ) (x : ℤ) : (PhiMinusA j).eval x =
    sideMinusA (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (x + 600) (j : ℤ) := by
  unfold PhiMinusA
  rw [← coe_evalRingHom, map_sideMinusA]
  simp [map_hornerC, map_natCast]

theorem eval_PhiPlusB (j : ℕ) (x : ℤ) : (PhiPlusB j).eval x =
    sidePlusB (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (hornerC a6zS x) (x + 600)
      (j : ℤ) := by
  unfold PhiPlusB
  rw [← coe_evalRingHom, map_sidePlusB]
  simp [map_hornerC, map_natCast]

theorem eval_PhiMinusB (j : ℕ) (x : ℤ) : (PhiMinusB j).eval x =
    sideMinusB (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (hornerC a6zS x) (x + 600)
      (j : ℤ) := by
  unfold PhiMinusB
  rw [← coe_evalRingHom, map_sideMinusB]
  simp [map_hornerC, map_natCast]

theorem eval_PhiA (j s : ℕ) (hj : j < 21) (hs : s < 197) : (PhiPlusA j - PhiMinusA j).eval (s : ℤ) = 0 := by
  rw [eval_sub, eval_PhiPlusA, eval_PhiMinusA, sub_eq_zero]
  exact transportA (Nat.castRingHom ℤ) s j (gridA s hs j hj)

theorem eval_PhiB (j s : ℕ) (hj : j < 31) (hs : s < 295) : (PhiPlusB j - PhiMinusB j).eval (s : ℤ) = 0 := by
  rw [eval_sub, eval_PhiPlusB, eval_PhiMinusB, sub_eq_zero]
  exact transportB (Nat.castRingHom ℤ) s j (gridB s hs j hj)

theorem PhiA_eq (j : ℕ) (hj : j < 21) : PhiPlusA j = PhiMinusA j := by
  rw [← sub_eq_zero]
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun i : Fin 197 => ((i : ℕ) : ℤ))
    (fun a b h => Fin.ext (by simpa using h)) (fun i => eval_PhiA j i hj i.isLt) ?_
  simpa using Nat.lt_succ_of_le (natDegree_PhiA_le j)

theorem PhiB_eq (j : ℕ) (hj : j < 31) : PhiPlusB j = PhiMinusB j := by
  rw [← sub_eq_zero]
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun i : Fin 295 => ((i : ℕ) : ℤ))
    (fun a b h => Fin.ext (by simpa using h)) (fun i => eval_PhiB j i hj i.isLt) ?_
  simpa using Nat.lt_succ_of_le (natDegree_PhiB_le j)

end EvalZ

section AnyRing
variable {K : Type*} [CommRing K]

theorem identityA (x : K) (j : ℕ) (hj : j < 21) :
    sidePlusA (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (x + 600) (j : K) =
      sideMinusA (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (x + 600) (j : K) := by
  have h := transportA (eval₂RingHom (Int.castRingHom K) x) X j (by
    have := PhiA_eq j hj; unfold PhiPlusA PhiMinusA at this; exact this)
  rwa [coe_eval₂RingHom, eval₂_X] at h

theorem identityB (x : K) (j : ℕ) (hj : j < 31) :
    sidePlusB (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (hornerC a6zS x) (x + 600)
        (j : K) =
      sideMinusB (hornerC naS x) (hornerC ngS x) (hornerC dtpS x) (hornerC a4zS x) (hornerC a6zS x) (x + 600)
        (j : K) := by
  have h := transportB (eval₂RingHom (Int.castRingHom K) x) X j (by
    have := PhiB_eq j hj; unfold PhiPlusB PhiMinusB at this; exact this)
  rwa [coe_eval₂RingHom, eval₂_X] at h

end AnyRing

end M4cP2.D52

open Polynomial Finset RubinSilverberg

namespace M4cP2
namespace D52

section HornerAlgebra
variable {S : Type*} [CommRing S]

theorem hornerG_map_sub {ι : Type*} (L : List ι) (f g : ι → S) (t : S) :
    hornerG (L.map f) t - hornerG (L.map g) t = hornerG (L.map fun r => f r - g r) t := by
  induction L with
  | nil => simp [hornerG]
  | cons a L ih =>
    simp only [hornerG, List.map_cons, List.foldr_cons] at ih ⊢
    rw [← ih]; ring

theorem hornerG_map_const_mul {ι : Type*} (L : List ι) (c : S) (g : ι → S) (t : S) :
    hornerG (L.map fun r => c * g r) t = c * hornerG (L.map g) t := by
  induction L with
  | nil => simp [hornerG]
  | cons a L ih =>
    simp only [hornerG, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih]; ring

theorem hornerG_map_eq_sum {ι : Type*} (L : List ι) (g : ι → S) (t : S) (d₀ : ι) :
    hornerG (L.map g) t = ∑ k ∈ range L.length, g (L.getD k d₀) * t ^ k := by
  induction L with
  | nil => simp [hornerG]
  | cons a L ih =>
    simp only [hornerG, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, List.length_cons, sum_range_succ', List.getD_cons_zero, pow_zero, mul_one, mul_sum]
    simp only [List.getD_cons_succ, pow_succ]
    rw [add_comm]
    exact congrArg₂ (· + ·) (sum_congr rfl fun k _ => by ring) rfl

end HornerAlgebra

section RowAlgebra
variable {F : Type*} [Field F]

def alphaRow (r : Row) (J : F) : F :=
  (r.1 : F) * (1 - J) ^ r.2.1 * (phomG r.2.2.2.1 (-J) 1 - phomG r.2.2.2.2 (-J) 1)

theorem map_alphaRow {F' : Type*} [Field F'] (f : F →+* F') (r : Row) (J : F) :
    f (alphaRow r J) = alphaRow r (f J) := by
  simp [alphaRow, map_phomG]

def rowDeg (r : Row) : ℕ :=
  match r.2.2.2.1 ++ r.2.2.2.2 with
  | [] => 0
  | e :: _ => e.2.1 + e.2.2

def rowOK (N : ℕ) (r : Row) : Bool :=
  (r.2.2.2.1 ++ r.2.2.2.2).all (fun e => e.2.1 + e.2.2 == rowDeg r) && (r.2.1 + r.2.2.1 + rowDeg r == N)

theorem tabA_ok : tabA.all (rowOK 16) = true := by decide
theorem tabB_ok : tabB.all (rowOK 24) = true := by decide
theorem tabA_length : tabA.length = 21 := rfl
theorem tabB_length : tabB.length = 31 := rfl

theorem phomG_div (row : List (ℕ × ℕ × ℕ)) (g : ℕ) (hg : ∀ e ∈ row, e.2.1 + e.2.2 = g)
    (Np D : F) (hD : D ≠ 0) : phomG row (Np / D) 1 * D ^ g = phomG row Np D := by
  induction row with
  | nil => simp [phomG]
  | cons e row ih =>
    have he := hg e (by simp)
    have ih' := ih fun e' h' => hg e' (by simp [h'])
    simp only [phomG, List.foldr_cons] at ih' ⊢
    rw [add_mul, ih', one_pow, mul_one, ← he, pow_add, div_pow]
    have : D ^ e.2.1 ≠ 0 := pow_ne_zero _ hD
    field_simp

theorem row_identity (N : ℕ) (r : Row) (hr : rowOK N r = true) (Np D : F) (hD : D ≠ 0) :
    (r.1 : F) * (Np + D) ^ r.2.1 * D ^ r.2.2.1 * (phomG r.2.2.2.1 Np D - phomG r.2.2.2.2 Np D)
      = D ^ N * alphaRow r (-(Np / D)) := by
  simp only [rowOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_append] at hr
  obtain ⟨hg, hN⟩ := hr
  unfold alphaRow
  rw [neg_neg, ← phomG_div _ _ (fun e he => hg e (Or.inl he)) Np D hD,
    ← phomG_div _ _ (fun e he => hg e (Or.inr he)) Np D hD, ← hN, pow_add, pow_add]
  have hDm : D ^ r.2.1 ≠ 0 := pow_ne_zero _ hD
  have e1 : (1 + Np / D) ^ r.2.1 * D ^ r.2.1 = (Np + D) ^ r.2.1 := by
    rw [← mul_pow]; congr 1; field_simp; ring
  rw [show (1 : F) - -(Np / D) = 1 + Np / D by ring, ← e1]
  ring

theorem rhs_sub (tab : List Row) (N : ℕ) (htab : tab.all (rowOK N) = true) (d h lead w t : F)
    (hD : (1728 * w * d ^ 5 : F) ≠ 0) (r₀ : Row) :
    hornerG (rhsCoeffsG tab d h lead w).1 t - hornerG (rhsCoeffsG tab d h lead w).2 t =
      lead * (1728 * w * d ^ 5) ^ N *
        ∑ k ∈ range tab.length, alphaRow (tab.getD k r₀) (-(h ^ 3 / (1728 * w * d ^ 5))) * t ^ k := by
  simp only [rhsCoeffsG]
  rw [hornerG_map_sub]
  have key : ∀ r ∈ tab,
      lead * ((r.1 : F) * (h ^ 3 + 1728 * w * d ^ 5) ^ r.2.1 * (1728 * w * d ^ 5) ^ r.2.2.1 *
          phomG r.2.2.2.1 (h ^ 3) (1728 * w * d ^ 5)) -
        lead * ((r.1 : F) * (h ^ 3 + 1728 * w * d ^ 5) ^ r.2.1 * (1728 * w * d ^ 5) ^ r.2.2.1 *
          phomG r.2.2.2.2 (h ^ 3) (1728 * w * d ^ 5)) =
      lead * (1728 * w * d ^ 5) ^ N * alphaRow r (-(h ^ 3 / (1728 * w * d ^ 5))) := by
    intro r hr
    rw [List.all_eq_true] at htab
    linear_combination lead * row_identity N r (htab r hr) (h ^ 3) (1728 * w * d ^ 5) hD
  rw [List.map_congr_left key, hornerG_map_const_mul, hornerG_map_eq_sum _ _ _ r₀]

end RowAlgebra

section LhsAlgebra
variable {F : Type*} [Field F]

theorem lhsA_sub (na ng d u t : F) :
    (lhsPairAG na ng d (u ^ 5) t).1 - (lhsPairAG na ng d (u ^ 5) t).2 =
      429981696 * kleinHHom (na * t + 144 * u ^ 5 * d ^ 4) ((ng * t + 144 * d ^ 4) * u ^ 4) := by
  dsimp only [lhsPairAG]
  unfold kleinHHom
  generalize na * t + 144 * u ^ 5 * d ^ 4 = P
  generalize ng * t + 144 * d ^ 4 = Q
  ring

theorem lhsB_sub (na ng d u t : F) :
    (lhsPairBG na ng d (u ^ 5) t).1 - (lhsPairBG na ng d (u ^ 5) t).2 =
      8916100448256 * kleinTHom (na * t + 144 * u ^ 5 * d ^ 4) ((ng * t + 144 * d ^ 4) * u ^ 4) := by
  dsimp only [lhsPairBG]
  unfold kleinTHom
  generalize na * t + 144 * u ^ 5 * d ^ 4 = P
  generalize ng * t + 144 * d ^ 4 = Q
  ring

theorem kleinHHom_smul (c n m : F) : kleinHHom (c * n) (c * m) = c ^ 20 * kleinHHom n m := by
  unfold kleinHHom; ring

theorem kleinTHom_smul (c n m : F) : kleinTHom (c * n) (c * m) = c ^ 30 * kleinTHom n m := by
  unfold kleinTHom; ring

theorem map_kleinHHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n m : R) :
    f (kleinHHom n m) = kleinHHom (f n) (f m) := by
  unfold kleinHHom; simp [map_sub, map_add, map_mul, map_pow, map_ofNat]

theorem map_kleinTHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n m : R) :
    f (kleinTHom n m) = kleinTHom (f n) (f m) := by
  unfold kleinTHom; simp [map_sub, map_add, map_mul, map_pow, map_ofNat]

end LhsAlgebra

section Bridges
variable {F : Type*} [Field F] (u : F)

theorem bridge_dtp : hornerC dtpS (u ^ 5 - 600) = u ^ 10 + 11 * u ^ 5 - 1 := by
  simp only [hornerC, dtpS, List.foldr_cons, List.foldr_nil]; push_cast; ring

theorem bridge_a4z : hornerC a4zS (u ^ 5 - 600) = kleinH u := by
  simp only [hornerC, a4zS, List.foldr_cons, List.foldr_nil]; unfold kleinH; push_cast; ring

theorem bridge_a6z : hornerC a6zS (u ^ 5 - 600) = kleinT u := by
  simp only [hornerC, a6zS, List.foldr_cons, List.foldr_nil]; unfold kleinT; push_cast; ring

theorem bridge_na : hornerC naS (u ^ 5 - 600) =
    kleinT u * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1) := by
  simp only [hornerC, naS, List.foldr_cons, List.foldr_nil]; unfold kleinT; push_cast; ring

theorem bridge_ng : hornerC ngS (u ^ 5 - 600) =
    kleinT u * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57) := by
  simp only [hornerC, ngS, List.foldr_cons, List.foldr_nil]; unfold kleinT; push_cast; ring

theorem kleinV_eq : kleinV u = u * (u ^ 10 + 11 * u ^ 5 - 1) := rfl

theorem klein_syzygy : kleinT u ^ 2 - kleinH u ^ 3 = 1728 * kleinV u ^ 5 := by
  unfold kleinT kleinH kleinV; ring

theorem rsBeta_eq : rsBeta u = kleinT u * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1) /
    (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4) := rfl

theorem rsGamma_eq : rsGamma u = kleinT u * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57) /
    (144 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4) := rfl

end Bridges

section Datum
variable {K : Type*} [Field K] [CharZero K]

structure DatumFacts (A B u₀ : K) : Prop where
  hu : u₀ ≠ 0
  hd : u₀ ^ 10 + 11 * u₀ ^ 5 - 1 ≠ 0
  hH : kleinH u₀ ≠ 0
  hT : kleinT u₀ ≠ 0
  hdisc : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0
  hJ : 4 * A ^ 3 / (4 * A ^ 3 + 27 * B ^ 2) =
    -(kleinH u₀ ^ 3 / (1728 * u₀ ^ 5 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 5))

theorem datumFacts {A B u₀ : K} (hA : A ≠ 0) (hB : B ≠ 0) (h : IsKleinDatum A B u₀) :
    DatumFacts A B u₀ := by
  obtain ⟨heq, hV⟩ := h
  rw [kleinV_eq] at hV heq
  have hu : u₀ ≠ 0 := left_ne_zero_of_mul hV
  have hd : u₀ ^ 10 + 11 * u₀ ^ 5 - 1 ≠ 0 := right_ne_zero_of_mul hV
  have hV5 : (u₀ * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1)) ^ 5 ≠ 0 := pow_ne_zero _ hV
  have hA3 : (6912 : K) * A ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hA)
  have hH : kleinH u₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow three_ne_zero, zero_mul, zero_add] at heq
    exact (mul_ne_zero hA3 hV5) heq
  have hdisc : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_add] at heq
    exact (mul_ne_zero hA3 hV5) heq
  have hT : kleinT u₀ ≠ 0 := by
    intro h0
    have syz := klein_syzygy u₀
    rw [kleinV_eq, h0] at syz
    have : (46656 : K) * B ^ 2 * (u₀ * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1)) ^ 5 = 0 := by
      linear_combination (-1 : K) * heq + (-(4 * A ^ 3 + 27 * B ^ 2)) * syz
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact hB (pow_eq_zero_iff two_ne_zero |>.mp h2)
    · exact hV5 h1
  refine ⟨hu, hd, hH, hT, hdisc, ?_⟩
  have h5 : (1728 : K) * u₀ ^ 5 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 5 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hu)) (pow_ne_zero _ hd)
  rw [eq_neg_iff_add_eq_zero, div_add_div _ _ hdisc h5, div_eq_zero_iff]
  exact Or.inl (by linear_combination heq)

variable {A B u₀ : K}

theorem famA_nat (hf : DatumFacts A B u₀) (j : ℕ) (hj : j < 21) :
    rsFamilyA A u₀ 0 (j : K) =
      A * ∑ k ∈ range 21, alphaRow (tabA.getD k default) (4 * A ^ 3 / (4 * A ^ 3 + 27 * B ^ 2)) * (j : K) ^ k := by
  obtain ⟨hu, hd, hH, hT, hdisc, hJ⟩ := hf
  have hD : (1728 * u₀ ^ 5 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 5 : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hu)) (pow_ne_zero _ hd)
  have hC : (144 * u₀ ^ 4 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4 : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hu)) (pow_ne_zero _ hd)
  have hnum : rsNum u₀ 0 (j : K) = (144 * u₀ ^ 4 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4)⁻¹ *
      (kleinT u₀ * (57 * u₀ ^ 15 - 247 * u₀ ^ 10 - 171 * u₀ ^ 5 - 1) * j +
        144 * u₀ ^ 5 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4) := by
    unfold rsNum; rw [rsBeta_eq]; set dd := u₀ ^ 10 + 11 * u₀ ^ 5 - 1; field_simp; ring
  have hden : rsDen u₀ 0 (j : K) = (144 * u₀ ^ 4 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4)⁻¹ *
      ((kleinT u₀ * (u₀ ^ 15 - 171 * u₀ ^ 10 + 247 * u₀ ^ 5 + 57) * j +
        144 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4) * u₀ ^ 4) := by
    unfold rsDen; rw [rsGamma_eq]; set dd := u₀ ^ 10 + 11 * u₀ ^ 5 - 1; field_simp; ring

  have id := identityA (u₀ ^ 5 - 600) j hj
  rw [sub_add_cancel, bridge_dtp, bridge_a4z, bridge_na, bridge_ng] at id
  unfold sidePlusA sideMinusA at id
  rw [← sub_eq_sub_iff_add_eq_add, lhsA_sub, rhs_sub tabA 16 tabA_ok _ _ _ _ _ hD default, tabA_length,
    ← hJ] at id

  have hk := (eq_div_iff (by norm_num : (429981696 : K) ≠ 0)).mpr
    ((mul_comm _ _).trans id)
  unfold rsFamilyA
  rw [hnum, hden, kleinHHom_smul, hk]
  set dd := u₀ ^ 10 + 11 * u₀ ^ 5 - 1
  field_simp
  ring

theorem famB_nat (hf : DatumFacts A B u₀) (j : ℕ) (hj : j < 31) :
    rsFamilyB B u₀ 0 (j : K) =
      B * ∑ k ∈ range 31, alphaRow (tabB.getD k default) (4 * A ^ 3 / (4 * A ^ 3 + 27 * B ^ 2)) * (j : K) ^ k := by
  obtain ⟨hu, hd, hH, hT, hdisc, hJ⟩ := hf
  have hD : (1728 * u₀ ^ 5 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 5 : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hu)) (pow_ne_zero _ hd)
  have hC : (144 * u₀ ^ 4 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4 : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hu)) (pow_ne_zero _ hd)
  have hnum : rsNum u₀ 0 (j : K) = (144 * u₀ ^ 4 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4)⁻¹ *
      (kleinT u₀ * (57 * u₀ ^ 15 - 247 * u₀ ^ 10 - 171 * u₀ ^ 5 - 1) * j +
        144 * u₀ ^ 5 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4) := by
    unfold rsNum; rw [rsBeta_eq]; set dd := u₀ ^ 10 + 11 * u₀ ^ 5 - 1; field_simp; ring
  have hden : rsDen u₀ 0 (j : K) = (144 * u₀ ^ 4 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4)⁻¹ *
      ((kleinT u₀ * (u₀ ^ 15 - 171 * u₀ ^ 10 + 247 * u₀ ^ 5 + 57) * j +
        144 * (u₀ ^ 10 + 11 * u₀ ^ 5 - 1) ^ 4) * u₀ ^ 4) := by
    unfold rsDen; rw [rsGamma_eq]; set dd := u₀ ^ 10 + 11 * u₀ ^ 5 - 1; field_simp; ring
  have id := identityB (u₀ ^ 5 - 600) j hj
  rw [sub_add_cancel, bridge_dtp, bridge_a4z, bridge_a6z, bridge_na, bridge_ng] at id
  unfold sidePlusB sideMinusB at id
  rw [← sub_eq_sub_iff_add_eq_add, lhsB_sub, rhs_sub tabB 24 tabB_ok _ _ _ _ _ hD default, tabB_length,
    ← hJ] at id
  have hk := (eq_div_iff (by norm_num : (8916100448256 : K) ≠ 0)).mpr
    ((mul_comm _ _).trans id)
  unfold rsFamilyB
  rw [hnum, hden, kleinTHom_smul, hk]
  set dd := u₀ ^ 10 + 11 * u₀ ^ 5 - 1
  field_simp
  ring

end Datum

section StageT
variable {K : Type*} [Field K]

noncomputable def paPoly (n : ℕ) (A : K) (cA : ℕ → K) (l : K) : K[X] :=
  ∑ k ∈ range (n + 1), C (A * cA k) * X ^ k * (1 + C l * X) ^ (n - k)

theorem eval_paPoly (n : ℕ) (A : K) (cA : ℕ → K) (l t : K) :
    (paPoly n A cA l).eval t = ∑ k ∈ range (n + 1), A * cA k * t ^ k * (1 + l * t) ^ (n - k) := by
  simp [paPoly, eval_finsetSum]

theorem eval_paPoly_zero (n : ℕ) (A : K) (cA : ℕ → K) (t : K) :
    (paPoly n A cA 0).eval t = A * ∑ k ∈ range (n + 1), cA k * t ^ k := by
  rw [eval_paPoly, mul_sum]
  exact sum_congr rfl fun k _ => by ring

theorem natDegree_paPoly_le (n : ℕ) (A : K) (cA : ℕ → K) (l : K) : (paPoly n A cA l).natDegree ≤ n := by
  unfold paPoly
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have h1 : (1 + C l * X : K[X]).natDegree ≤ 1 := by compute_degree!
  calc ((C (A * cA k) * X ^ k * (1 + C l * X) ^ (n - k)).natDegree)
      ≤ (C (A * cA k) * X ^ k).natDegree + ((1 + C l * X) ^ (n - k)).natDegree := natDegree_mul_le
    _ ≤ k + (n - k) * 1 :=
        add_le_add (natDegree_C_mul_X_pow_le _ _) (natDegree_pow_le.trans (Nat.mul_le_mul_left _ h1))
    _ = n := by omega

theorem map_paPoly {K' : Type*} [Field K'] (f : K →+* K') (n : ℕ) (A : K) (cA : ℕ → K) (l : K) :
    (paPoly n A cA l).map f = paPoly n (f A) (fun k => f (cA k)) (f l) := by
  simp [paPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow]

theorem paPoly_shift (n : ℕ) (A : K) (cA : ℕ → K) (l t : K) (hc : 1 + l * t ≠ 0) :
    (1 + l * t) ^ n * (paPoly n A cA 0).eval (t / (1 + l * t)) = (paPoly n A cA l).eval t := by
  rw [eval_paPoly, eval_paPoly, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [zero_mul, add_zero, one_pow, mul_one, div_pow,
    show (1 + l * t) ^ n = (1 + l * t) ^ k * (1 + l * t) ^ (n - k) by
      rw [← pow_add, Nat.add_sub_cancel' hk']]
  have : (1 + l * t) ^ k ≠ 0 := pow_ne_zero _ hc
  field_simp

theorem eq_paPoly_of_homog [CharZero K] (n : ℕ) (A : K) (cA : ℕ → K) (f : K → K → K) (P : K → K[X])
    (hP : ∀ l t, (P l).eval t = f l t)
    (hhom : ∀ l t, 1 + l * t ≠ 0 → f l t = (1 + l * t) ^ n * f 0 (t / (1 + l * t)))
    (h0 : ∀ s, f 0 s = (paPoly n A cA 0).eval s) (l t : K) :
    f l t = (paPoly n A cA l).eval t := by
  have hagree : ∀ x : K, 1 + l * x ≠ 0 → f l x = (paPoly n A cA l).eval x := fun x hx => by
    rw [hhom l x hx, h0, paPoly_shift n A cA l x hx]
  have hinf : {x : K | 1 + l * x ≠ 0}.Infinite := by
    refine Set.Infinite.mono (s := ({-l⁻¹}ᶜ : Set K)) (fun x hx h0 => hx ?_)
      (Set.finite_singleton _).infinite_compl
    simp only [Set.mem_singleton_iff]
    by_cases hl : l = 0
    · simp [hl] at h0
    · field_simp; linear_combination h0
  have hpoly : P l = paPoly n A cA l := by
    rw [← sub_eq_zero]
    refine eq_zero_of_infinite_isRoot _ (hinf.mono fun x hx => ?_)
    simp only [Set.mem_setOf_eq, IsRoot.def, eval_sub, hP, hagree x hx, sub_self]
  rw [← hP, hpoly]

theorem eq_paPoly_zero_of_nat [CharZero K] (n : ℕ) (A : K) (cA : ℕ → K) (P : K[X]) (hdeg : P.natDegree ≤ n)
    (hnat : ∀ j : ℕ, j < n + 1 → P.eval (j : K) = A * ∑ k ∈ range (n + 1), cA k * (j : K) ^ k) :
    P = paPoly n A cA 0 := by
  refine eq_of_natDegree_lt_card_of_eval_eq _ _ (f := fun i : Fin (n + 1) => ((i : ℕ) : K))
    (fun a b h => Fin.ext (by simpa using h)) (fun i => ?_) ?_
  · rw [hnat i i.isLt, eval_paPoly_zero]
  · simpa using ⟨hdeg, natDegree_paPoly_le n A cA 0⟩

variable {A B u₀ : K}

def coefA (A B : K) (k : ℕ) : K := alphaRow (tabA.getD k default) (4 * A ^ 3 / (4 * A ^ 3 + 27 * B ^ 2))
def coefB (A B : K) (k : ℕ) : K := alphaRow (tabB.getD k default) (4 * A ^ 3 / (4 * A ^ 3 + 27 * B ^ 2))

theorem map_coefA {K' : Type*} [Field K'] (f : K →+* K') (A B : K) (k : ℕ) :
    f (coefA A B k) = coefA (f A) (f B) k := by
  unfold coefA; rw [map_alphaRow]; simp [map_div₀, map_ofNat]

theorem map_coefB {K' : Type*} [Field K'] (f : K →+* K') (A B : K) (k : ℕ) :
    f (coefB A B k) = coefB (f A) (f B) k := by
  unfold coefB; rw [map_alphaRow]; simp [map_div₀, map_ofNat]

noncomputable def LApoly (A u₀ l : K) : K[X] :=
  C A * kleinHHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1) * C (kleinH u₀)⁻¹

noncomputable def LBpoly (B u₀ l : K) : K[X] :=
  C B * kleinTHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1) * C (kleinT u₀)⁻¹

theorem eval_LApoly (A u₀ l t : K) : (LApoly A u₀ l).eval t = rsFamilyA A u₀ l t := by
  unfold LApoly rsFamilyA rsNum rsDen
  rw [eval_mul, eval_mul, eval_C, eval_C, ← coe_evalRingHom, map_kleinHHom]
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, eval_one]
  rw [div_eq_mul_inv]

theorem eval_LBpoly (B u₀ l t : K) : (LBpoly B u₀ l).eval t = rsFamilyB B u₀ l t := by
  unfold LBpoly rsFamilyB rsNum rsDen
  rw [eval_mul, eval_mul, eval_C, eval_C, ← coe_evalRingHom, map_kleinTHom]
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, eval_one]
  rw [div_eq_mul_inv]

theorem natDegree_LApoly_le (A u₀ l : K) : (LApoly A u₀ l).natDegree ≤ 20 := by
  unfold LApoly kleinHHom; compute_degree!

theorem natDegree_LBpoly_le (B u₀ l : K) : (LBpoly B u₀ l).natDegree ≤ 30 := by
  unfold LBpoly kleinTHom; compute_degree!

theorem rsFamilyA_homog (A u₀ l t : K) (hc : 1 + l * t ≠ 0) :
    rsFamilyA A u₀ l t = (1 + l * t) ^ 20 * rsFamilyA A u₀ 0 (t / (1 + l * t)) := by
  unfold rsFamilyA rsNum rsDen
  rw [show (rsBeta u₀ + l * u₀) * t + u₀ = (1 + l * t) * ((rsBeta u₀ + 0 * u₀) * (t / (1 + l * t)) + u₀) by
        field_simp; ring,
    show (rsGamma u₀ + l) * t + 1 = (1 + l * t) * ((rsGamma u₀ + 0) * (t / (1 + l * t)) + 1) by
        field_simp; ring,
    kleinHHom_smul]
  ring

theorem rsFamilyB_homog (B u₀ l t : K) (hc : 1 + l * t ≠ 0) :
    rsFamilyB B u₀ l t = (1 + l * t) ^ 30 * rsFamilyB B u₀ 0 (t / (1 + l * t)) := by
  unfold rsFamilyB rsNum rsDen
  rw [show (rsBeta u₀ + l * u₀) * t + u₀ = (1 + l * t) * ((rsBeta u₀ + 0 * u₀) * (t / (1 + l * t)) + u₀) by
        field_simp; ring,
    show (rsGamma u₀ + l) * t + 1 = (1 + l * t) * ((rsGamma u₀ + 0) * (t / (1 + l * t)) + 1) by
        field_simp; ring,
    kleinTHom_smul]
  ring

theorem rsFamilyA_eq_paPoly [CharZero K] (hf : DatumFacts A B u₀) (l t : K) :
    rsFamilyA A u₀ l t = (paPoly 20 A (coefA A B) l).eval t := by
  refine eq_paPoly_of_homog 20 A (coefA A B) (fun l t => rsFamilyA A u₀ l t) (LApoly A u₀)
    (eval_LApoly A u₀) (fun l t hc => rsFamilyA_homog A u₀ l t hc) (fun s => ?_) l t
  have := eq_paPoly_zero_of_nat 20 A (coefA A B) (LApoly A u₀ 0) (natDegree_LApoly_le A u₀ 0)
    (fun j hj => by rw [eval_LApoly]; exact famA_nat hf j hj)
  change rsFamilyA A u₀ 0 s = _
  rw [← eval_LApoly, this]

theorem rsFamilyB_eq_paPoly [CharZero K] (hf : DatumFacts A B u₀) (l t : K) :
    rsFamilyB B u₀ l t = (paPoly 30 B (coefB A B) l).eval t := by
  refine eq_paPoly_of_homog 30 B (coefB A B) (fun l t => rsFamilyB B u₀ l t) (LBpoly B u₀)
    (eval_LBpoly B u₀) (fun l t hc => rsFamilyB_homog B u₀ l t hc) (fun s => ?_) l t
  have := eq_paPoly_zero_of_nat 30 B (coefB A B) (LBpoly B u₀ 0) (natDegree_LBpoly_le B u₀ 0)
    (fun j hj => by rw [eval_LBpoly]; exact famB_nat hf j hj)
  change rsFamilyB B u₀ 0 s = _
  rw [← eval_LBpoly, this]

end StageT

theorem exists_polynomial_rsFamily (a b l : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (u₀ : AlgebraicClosure ℚ)
    (h : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) a) (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀) :
    ∃ pa pb : Polynomial ℚ, pa.natDegree ≤ 20 ∧ pb.natDegree ≤ 30 ∧ ∀ t : AlgebraicClosure ℚ,
      rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) a) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) l) t =
          (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t ∧
        rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) l) t =
          (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t := by
  set φ := algebraMap ℚ (AlgebraicClosure ℚ) with hφ
  have hf : DatumFacts (φ a) (φ b) u₀ :=
    datumFacts ((map_ne_zero_iff φ φ.injective).mpr ha) ((map_ne_zero_iff φ φ.injective).mpr hb) h
  refine ⟨paPoly 20 a (coefA a b) l, paPoly 30 b (coefB a b) l, natDegree_paPoly_le _ _ _ _,
    natDegree_paPoly_le _ _ _ _, fun t => ⟨?_, ?_⟩⟩
  · rw [map_paPoly, rsFamilyA_eq_paPoly hf]
    simp only [map_coefA]
  · rw [map_paPoly, rsFamilyB_eq_paPoly hf]
    simp only [map_coefB]

end M4cP2.D52

open RubinSilverberg in
theorem solution (a b l : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (u₀ : AlgebraicClosure ℚ) (h : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) a) (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀) : ∃ pa pb : Polynomial ℚ, pa.natDegree ≤ 20 ∧ pb.natDegree ≤ 30 ∧ ∀ t : AlgebraicClosure ℚ, rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) a) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) l) t = (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t ∧ rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) l) t = (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t :=
  M4cP2.D52.exists_polynomial_rsFamily a b l ha hb u₀ h

end S_RubinSilverberg_exists_polynomial_rsFamily
end P2MW
export P2MW.S_RubinSilverberg_exists_polynomial_rsFamily (solution)
