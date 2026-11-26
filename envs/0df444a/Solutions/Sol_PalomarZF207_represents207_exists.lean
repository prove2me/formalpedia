-- Prove2me | solution 1 for PalomarZF207.represents207_exists
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:58:02.255148+00:00
-- url     : https://prove2.me/submissions/d58f2866-aee0-4930-a92d-d4492e169d23

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement

open PalomarZF207
open PalomarZF207History

namespace SolRepresents207

private def fNot (p : Formula) : Formula := .imp p .bot
private def fIff (p q : Formula) : Formula := .and (.imp p q) (.imp q p)
private def fTrue : Formula := .imp .bot .bot

private theorem bound_fNot {p : Formula} {n : Nat} (hp : Bound p n) : Bound (fNot p) n :=
  ⟨hp, trivial⟩

private theorem bound_fIff {p q : Formula} {n : Nat} (hp : Bound p n) (hq : Bound q n) :
    Bound (fIff p q) n :=
  ⟨⟨hp, hq⟩, ⟨hq, hp⟩⟩

private theorem bound_fTrue (n : Nat) : Bound fTrue n := ⟨trivial, trivial⟩

private theorem eval_fNot {V : Type} (E : V → V → Prop) (p : Formula) (s : Nat → V) :
    eval E (fNot p) s ↔ ¬ eval E p s := Iff.rfl

private theorem eval_fIff {V : Type} (E : V → V → Prop) (p q : Formula) (s : Nat → V) :
    eval E (fIff p q) s ↔ (eval E p s ↔ eval E q s) :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

private theorem eval_fTrue {V : Type} (E : V → V → Prop) (s : Nat → V) :
    eval E fTrue s ↔ True :=
  ⟨fun _ => trivial, fun _ h => h⟩

private def fEmpty (a : Nat) : Formula := .all (fNot (.mem 0 (a + 1)))

private theorem bound_fEmpty {a n : Nat} (ha : a < n) : Bound (fEmpty a) n :=
  ⟨⟨Nat.zero_lt_succ n, Nat.succ_lt_succ ha⟩, trivial⟩

private theorem eval_fEmpty {V : Type} (E : V → V → Prop) (a : Nat) (s : Nat → V) :
    eval E (fEmpty a) s ↔ Empty E (s a) := Iff.rfl

private def fSucc (a b : Nat) : Formula :=
  .all (fIff (.mem 0 (b + 1)) (.or (.mem 0 (a + 1)) (.eq 0 (a + 1))))

private theorem bound_fSucc {a b n : Nat} (ha : a < n) (hb : b < n) : Bound (fSucc a b) n :=
  bound_fIff ⟨Nat.zero_lt_succ n, Nat.succ_lt_succ hb⟩
    ⟨⟨Nat.zero_lt_succ n, Nat.succ_lt_succ ha⟩, ⟨Nat.zero_lt_succ n, Nat.succ_lt_succ ha⟩⟩

private theorem eval_fSucc {V : Type} (E : V → V → Prop) (a b : Nat) (s : Nat → V) :
    eval E (fSucc a b) s ↔ Succ E (s a) (s b) := by
  constructor
  · intro h x; exact (eval_fIff E _ _ (pushValue s x)).mp (h x)
  · intro h x; exact (eval_fIff E _ _ (pushValue s x)).mpr (h x)

private def fPair (a b p : Nat) : Formula :=
  .all (fIff (.mem 0 (p + 1)) (.or (.eq 0 (a + 1)) (.eq 0 (b + 1))))

private theorem bound_fPair {a b p n : Nat} (ha : a < n) (hb : b < n) (hp : p < n) :
    Bound (fPair a b p) n :=
  bound_fIff ⟨Nat.zero_lt_succ n, Nat.succ_lt_succ hp⟩
    ⟨⟨Nat.zero_lt_succ n, Nat.succ_lt_succ ha⟩, ⟨Nat.zero_lt_succ n, Nat.succ_lt_succ hb⟩⟩

private theorem eval_fPair {V : Type} (E : V → V → Prop) (a b p : Nat) (s : Nat → V) :
    eval E (fPair a b p) s ↔ Pair E (s a) (s b) (s p) := by
  constructor
  · intro h x; exact (eval_fIff E _ _ (pushValue s x)).mp (h x)
  · intro h x; exact (eval_fIff E _ _ (pushValue s x)).mpr (h x)

private def fOrderedPair (a b p : Nat) : Formula :=
  .ex (.ex (.and (fPair (a + 2) (a + 2) 1)
    (.and (fPair (a + 2) (b + 2) 0) (fPair 1 0 (p + 2)))))

private theorem bound_fOrderedPair {a b p n : Nat} (ha : a < n) (hb : b < n) (hp : p < n) :
    Bound (fOrderedPair a b p) n := by
  refine ⟨bound_fPair (by omega) (by omega) (by omega),
    ⟨bound_fPair (by omega) (by omega) (by omega), bound_fPair (by omega) (by omega) (by omega)⟩⟩

private theorem eval_fOrderedPair {V : Type} (E : V → V → Prop) (a b p : Nat) (s : Nat → V) :
    eval E (fOrderedPair a b p) s ↔ OrderedPair E (s a) (s b) (s p) := by
  constructor
  · rintro ⟨aa, ab, h1, h2, h3⟩
    exact ⟨aa, ab, (eval_fPair E _ _ _ _).mp h1, (eval_fPair E _ _ _ _).mp h2,
      (eval_fPair E _ _ _ _).mp h3⟩
  · rintro ⟨aa, ab, h1, h2, h3⟩
    exact ⟨aa, ab, (eval_fPair E _ _ _ _).mpr h1, (eval_fPair E _ _ _ _).mpr h2,
      (eval_fPair E _ _ _ _).mpr h3⟩

private def fAt (f x y : Nat) : Formula :=
  .ex (.and (.mem 0 (f + 1)) (fOrderedPair (x + 1) (y + 1) 0))

private theorem bound_fAt {f x y n : Nat} (hf : f < n) (hx : x < n) (hy : y < n) :
    Bound (fAt f x y) n :=
  ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega)⟩

private theorem eval_fAt {V : Type} (E : V → V → Prop) (f x y : Nat) (s : Nat → V) :
    eval E (fAt f x y) s ↔ At E (s f) (s x) (s y) := by
  constructor
  · rintro ⟨p, h1, h2⟩; exact ⟨p, h1, (eval_fOrderedPair E _ _ _ _).mp h2⟩
  · rintro ⟨p, h1, h2⟩; exact ⟨p, h1, (eval_fOrderedPair E _ _ _ _).mpr h2⟩

private def fFunctionOn (f dom : Nat) : Formula :=
  .and
    (.all (.imp (.mem 0 (dom + 1))
      (.ex (.and (fAt (f + 2) 1 0)
        (.all (.imp (fAt (f + 3) 2 0) (.eq 0 1)))))))
    (.all (.imp (.mem 0 (f + 1))
      (.ex (.ex (.and (.mem 1 (dom + 3)) (fOrderedPair 1 0 2))))))

private theorem bound_fFunctionOn {f dom n : Nat} (hf : f < n) (hd : dom < n) :
    Bound (fFunctionOn f dom) n := by
  refine ⟨⟨⟨by omega, by omega⟩,
    ⟨bound_fAt (by omega) (by omega) (by omega),
     ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩,
    ⟨⟨by omega, by omega⟩,
     ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega)⟩⟩⟩

private theorem eval_fFunctionOn {V : Type} (E : V → V → Prop) (f dom : Nat) (s : Nat → V) :
    eval E (fFunctionOn f dom) s ↔ FunctionOn E (s f) (s dom) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, huniq⟩ := h1 x hx
      exact ⟨y, (eval_fAt E _ _ _ _).mp hy, fun z hz => huniq z ((eval_fAt E _ _ _ _).mpr hz)⟩
    · intro p hp
      obtain ⟨x, y, hx, hpair⟩ := h2 p hp
      exact ⟨x, y, hx, (eval_fOrderedPair E _ _ _ _).mp hpair⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, huniq⟩ := h1 x hx
      exact ⟨y, (eval_fAt E _ _ _ _).mpr hy, fun z hz => huniq z ((eval_fAt E _ _ _ _).mp hz)⟩
    · intro p hp
      obtain ⟨x, y, hx, hpair⟩ := h2 p hp
      exact ⟨x, y, hx, (eval_fOrderedPair E _ _ _ _).mpr hpair⟩

private def fInductive (a : Nat) : Formula :=
  .and
    (.ex (.and (fEmpty 0) (.mem 0 (a + 1))))
    (.all (.imp (.mem 0 (a + 1)) (.ex (.and (fSucc 1 0) (.mem 0 (a + 2))))))

private theorem bound_fInductive {a n : Nat} (ha : a < n) : Bound (fInductive a) n :=
  ⟨⟨bound_fEmpty (by omega), ⟨by omega, by omega⟩⟩,
   ⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩

private theorem eval_fInductive {V : Type} (E : V → V → Prop) (a : Nat) (s : Nat → V) :
    eval E (fInductive a) s ↔ Inductive E (s a) := by
  constructor
  · rintro ⟨⟨z, hz, hza⟩, hstep⟩
    exact ⟨⟨z, (eval_fEmpty E _ _).mp hz, hza⟩, fun x hx =>
      let ⟨y, hy, hya⟩ := hstep x hx
      ⟨y, (eval_fSucc E _ _ _).mp hy, hya⟩⟩
  · rintro ⟨⟨z, hz, hza⟩, hstep⟩
    exact ⟨⟨z, (eval_fEmpty E _ _).mpr hz, hza⟩, fun x hx =>
      let ⟨y, hy, hya⟩ := hstep x hx
      ⟨y, (eval_fSucc E _ _ _).mpr hy, hya⟩⟩

private def fOmega (w : Nat) : Formula :=
  .and (fInductive w)
    (.all (.imp (fInductive 0) (.all (.imp (.mem 0 (w + 2)) (.mem 0 1)))))

private theorem bound_fOmega {w n : Nat} (hw : w < n) : Bound (fOmega w) n :=
  ⟨bound_fInductive hw, ⟨bound_fInductive (by omega), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩⟩

private theorem eval_fOmega {V : Type} (E : V → V → Prop) (w : Nat) (s : Nat → V) :
    eval E (fOmega w) s ↔ Omega E (s w) := by
  constructor
  · rintro ⟨hw, hmin⟩
    exact ⟨(eval_fInductive E _ _).mp hw, fun a ha x hx =>
      hmin a ((eval_fInductive E _ _).mpr ha) x hx⟩
  · rintro ⟨hw, hmin⟩
    exact ⟨(eval_fInductive E _ _).mpr hw, fun a ha x hx =>
      hmin a ((eval_fInductive E _ _).mp ha) x hx⟩

private def fNatObject (x : Nat) : Formula :=
  .ex (.and (fOmega 0) (.mem (x + 1) 0))

private theorem bound_fNatObject {x n : Nat} (hx : x < n) : Bound (fNatObject x) n :=
  ⟨bound_fOmega (by omega), ⟨by omega, by omega⟩⟩

private theorem eval_fNatObject {V : Type} (E : V → V → Prop) (x : Nat) (s : Nat → V) :
    eval E (fNatObject x) s ↔ NatObject E (s x) := by
  constructor
  · rintro ⟨w, hw, hxw⟩; exact ⟨w, (eval_fOmega E _ _).mp hw, hxw⟩
  · rintro ⟨w, hw, hxw⟩; exact ⟨w, (eval_fOmega E _ _).mpr hw, hxw⟩

private def fNumeral : Nat → Nat → Formula
  | 0, x => fEmpty x
  | k + 1, x => .ex (.and (fNumeral k 0) (fSucc 0 (x + 1)))

private theorem bound_fNumeral : ∀ (k x n : Nat), x < n → Bound (fNumeral k x) n
  | 0, _, _, hx => bound_fEmpty hx
  | k + 1, _, _, hx =>
    ⟨bound_fNumeral k 0 _ (by omega), bound_fSucc (by omega) (by omega)⟩

private theorem eval_fNumeral {V : Type} (E : V → V → Prop) :
    ∀ (k x : Nat) (s : Nat → V), eval E (fNumeral k x) s ↔ Numeral E k (s x)
  | 0, x, s => eval_fEmpty E x s
  | k + 1, x, s => by
    constructor
    · rintro ⟨y, hy, hsucc⟩
      exact ⟨y, (eval_fNumeral E k 0 (pushValue s y)).mp hy,
        (eval_fSucc E 0 (x + 1) (pushValue s y)).mp hsucc⟩
    · rintro ⟨y, hy, hsucc⟩
      exact ⟨y, (eval_fNumeral E k 0 (pushValue s y)).mpr hy,
        (eval_fSucc E 0 (x + 1) (pushValue s y)).mpr hsucc⟩

private def fAdd (a b c : Nat) : Formula :=
  .and (fNatObject a) (.and (fNatObject b) (.and (fNatObject c)
    (.ex (.ex (.ex
      (.and (fEmpty 2)
      (.and (fSucc (b + 3) 1)
      (.and (fFunctionOn 0 1)
      (.and (fAt 0 2 (a + 3))
      (.and (fAt 0 (b + 3) (c + 3))
      (.and (.all (.all (.imp (.mem 1 3) (.imp (fAt 2 1 0) (fNatObject 0)))))
        (.all (.imp (.mem 0 (b + 4))
          (.ex (.ex (.ex
            (.and (fSucc 3 2)
            (.and (fAt 4 3 1)
            (.and (fAt 4 2 0) (fSucc 1 0))))))))))))))))))))

private theorem bound_fAdd {a b c n : Nat} (ha : a < n) (hb : b < n) (hc : c < n) :
    Bound (fAdd a b c) n := by
  refine ⟨bound_fNatObject ha, bound_fNatObject hb, bound_fNatObject hc,
    bound_fEmpty (by omega), bound_fSucc (by omega) (by omega),
    bound_fFunctionOn (by omega) (by omega),
    bound_fAt (by omega) (by omega) (by omega),
    bound_fAt (by omega) (by omega) (by omega),
    ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
    ⟨⟨by omega, by omega⟩,
     bound_fSucc (by omega) (by omega),
     bound_fAt (by omega) (by omega) (by omega),
     bound_fAt (by omega) (by omega) (by omega),
     bound_fSucc (by omega) (by omega)⟩⟩

private theorem eval_fAdd {V : Type} (E : V → V → Prop) (a b c : Nat) (s : Nat → V) :
    eval E (fAdd a b c) s ↔ Add E (s a) (s b) (s c) := by
  constructor
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject E _ _).mp ha, (eval_fNatObject E _ _).mp hb,
      (eval_fNatObject E _ _).mp hc, z, dom, f,
      (eval_fEmpty E _ _).mp hz, (eval_fSucc E _ _ _).mp hdom,
      (eval_fFunctionOn E _ _ _).mp hfun, (eval_fAt E _ _ _ _).mp hf0,
      (eval_fAt E _ _ _ _).mp hfb, ?_, ?_⟩
    · intro i x hi hfx
      exact (eval_fNatObject E _ _).mp (hnat i x hi ((eval_fAt E _ _ _ _).mpr hfx))
    · intro i hi
      obtain ⟨j, x, y, hij, hfix, hfjy, hxy⟩ := hstep i hi
      exact ⟨j, x, y, (eval_fSucc E _ _ _).mp hij, (eval_fAt E _ _ _ _).mp hfix,
        (eval_fAt E _ _ _ _).mp hfjy, (eval_fSucc E _ _ _).mp hxy⟩
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject E _ _).mpr ha, (eval_fNatObject E _ _).mpr hb,
      (eval_fNatObject E _ _).mpr hc, z, dom, f,
      (eval_fEmpty E _ _).mpr hz, (eval_fSucc E _ _ _).mpr hdom,
      (eval_fFunctionOn E _ _ _).mpr hfun, (eval_fAt E _ _ _ _).mpr hf0,
      (eval_fAt E _ _ _ _).mpr hfb, ?_, ?_⟩
    · intro i x hi hfx
      exact (eval_fNatObject E _ _).mpr (hnat i x hi ((eval_fAt E _ _ _ _).mp hfx))
    · intro i hi
      obtain ⟨j, x, y, hij, hfix, hfjy, hxy⟩ := hstep i hi
      exact ⟨j, x, y, (eval_fSucc E _ _ _).mpr hij, (eval_fAt E _ _ _ _).mpr hfix,
        (eval_fAt E _ _ _ _).mpr hfjy, (eval_fSucc E _ _ _).mpr hxy⟩

private def fMul (a b c : Nat) : Formula :=
  .and (fNatObject a) (.and (fNatObject b) (.and (fNatObject c)
    (.ex (.ex (.ex
      (.and (fEmpty 2)
      (.and (fSucc (b + 3) 1)
      (.and (fFunctionOn 0 1)
      (.and (fAt 0 2 2)
      (.and (fAt 0 (b + 3) (c + 3))
      (.and (.all (.all (.imp (.mem 1 3) (.imp (fAt 2 1 0) (fNatObject 0)))))
        (.all (.imp (.mem 0 (b + 4))
          (.ex (.ex (.ex
            (.and (fSucc 3 2)
            (.and (fAt 4 3 1)
            (.and (fAt 4 2 0) (fAdd 1 (a + 7) 0))))))))))))))))))))

private theorem bound_fMul {a b c n : Nat} (ha : a < n) (hb : b < n) (hc : c < n) :
    Bound (fMul a b c) n := by
  refine ⟨bound_fNatObject ha, bound_fNatObject hb, bound_fNatObject hc,
    bound_fEmpty (by omega), bound_fSucc (by omega) (by omega),
    bound_fFunctionOn (by omega) (by omega),
    bound_fAt (by omega) (by omega) (by omega),
    bound_fAt (by omega) (by omega) (by omega),
    ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
    ⟨⟨by omega, by omega⟩,
     bound_fSucc (by omega) (by omega),
     bound_fAt (by omega) (by omega) (by omega),
     bound_fAt (by omega) (by omega) (by omega),
     bound_fAdd (by omega) (by omega) (by omega)⟩⟩

private theorem eval_fMul {V : Type} (E : V → V → Prop) (a b c : Nat) (s : Nat → V) :
    eval E (fMul a b c) s ↔ Mul E (s a) (s b) (s c) := by
  constructor
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject E _ _).mp ha, (eval_fNatObject E _ _).mp hb,
      (eval_fNatObject E _ _).mp hc, z, dom, f,
      (eval_fEmpty E _ _).mp hz, (eval_fSucc E _ _ _).mp hdom,
      (eval_fFunctionOn E _ _ _).mp hfun, (eval_fAt E _ _ _ _).mp hf0,
      (eval_fAt E _ _ _ _).mp hfb, ?_, ?_⟩
    · intro i x hi hfx
      exact (eval_fNatObject E _ _).mp (hnat i x hi ((eval_fAt E _ _ _ _).mpr hfx))
    · intro i hi
      obtain ⟨j, x, y, hij, hfix, hfjy, hxy⟩ := hstep i hi
      exact ⟨j, x, y, (eval_fSucc E _ _ _).mp hij, (eval_fAt E _ _ _ _).mp hfix,
        (eval_fAt E _ _ _ _).mp hfjy, (eval_fAdd E _ _ _ _).mp hxy⟩
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject E _ _).mpr ha, (eval_fNatObject E _ _).mpr hb,
      (eval_fNatObject E _ _).mpr hc, z, dom, f,
      (eval_fEmpty E _ _).mpr hz, (eval_fSucc E _ _ _).mpr hdom,
      (eval_fFunctionOn E _ _ _).mpr hfun, (eval_fAt E _ _ _ _).mpr hf0,
      (eval_fAt E _ _ _ _).mpr hfb, ?_, ?_⟩
    · intro i x hi hfx
      exact (eval_fNatObject E _ _).mpr (hnat i x hi ((eval_fAt E _ _ _ _).mp hfx))
    · intro i hi
      obtain ⟨j, x, y, hij, hfix, hfjy, hxy⟩ := hstep i hi
      exact ⟨j, x, y, (eval_fSucc E _ _ _).mpr hij, (eval_fAt E _ _ _ _).mpr hfix,
        (eval_fAt E _ _ _ _).mpr hfjy, (eval_fAdd E _ _ _ _).mpr hxy⟩

private def fBitCons (bit : Bool) (x y : Nat) : Formula :=
  .ex (.ex (.ex
    (.and (fNumeral (if bit then 1 else 0) 2)
    (.and (fNumeral 2 1)
    (.and (fMul 1 (x + 3) 0) (fAdd 2 0 (y + 3)))))))

private theorem bound_fBitCons (bit : Bool) {x y n : Nat} (hx : x < n) (hy : y < n) :
    Bound (fBitCons bit x y) n :=
  ⟨bound_fNumeral _ 2 _ (by omega),
   bound_fNumeral 2 1 _ (by omega),
   bound_fMul (by omega) (by omega) (by omega),
   bound_fAdd (by omega) (by omega) (by omega)⟩

private theorem eval_fBitCons {V : Type} (E : V → V → Prop) (bit : Bool) (x y : Nat) (s : Nat → V) :
    eval E (fBitCons bit x y) s ↔ BitCons E bit (s x) (s y) := by
  constructor
  · rintro ⟨b, two, twice, hb, htwo, hmul, hadd⟩
    exact ⟨b, two, twice, (eval_fNumeral E _ _ _).mp hb, (eval_fNumeral E _ _ _).mp htwo,
      (eval_fMul E _ _ _ _).mp hmul, (eval_fAdd E _ _ _ _).mp hadd⟩
  · rintro ⟨b, two, twice, hb, htwo, hmul, hadd⟩
    exact ⟨b, two, twice, (eval_fNumeral E _ _ _).mpr hb, (eval_fNumeral E _ _ _).mpr htwo,
      (eval_fMul E _ _ _ _).mpr hmul, (eval_fAdd E _ _ _ _).mpr hadd⟩

private def fValid (sq sl sr : Nat) : Formula :=
  .and (fNatObject sq) (.and (fNatObject sl) (fNatObject sr))

private theorem bound_fValid {sq sl sr n : Nat} (hq : sq < n) (hl : sl < n) (hr : sr < n) :
    Bound (fValid sq sl sr) n :=
  ⟨bound_fNatObject hq, bound_fNatObject hl, bound_fNatObject hr⟩

private theorem eval_fValid {V : Type} (E : V → V → Prop) (sq sl sr : Nat) (s : Nat → V) :
    eval E (fValid sq sl sr) s ↔ Valid E ⟨s sq, s sl, s sr⟩ := by
  constructor
  · rintro ⟨hq, hl, hr⟩
    exact ⟨(eval_fNatObject E _ _).mp hq, (eval_fNatObject E _ _).mp hl,
      (eval_fNatObject E _ _).mp hr⟩
  · rintro ⟨hq, hl, hr⟩
    exact ⟨(eval_fNatObject E _ _).mpr hq, (eval_fNatObject E _ _).mpr hl,
      (eval_fNatObject E _ _).mpr hr⟩

private def fMoveLeftBit (write bit : Bool) (sl tl tr : Nat) : Formula :=
  .and (fBitCons bit 1 (sl + 3))
  (.and (.eq (tl + 3) 1)
  (.and (fBitCons write 2 0) (fBitCons bit 0 (tr + 3))))

private theorem bound_fMoveLeftBit (write bit : Bool) {sl tl tr n : Nat}
    (hsl : sl < n) (htl : tl < n) (htr : tr < n) :
    Bound (fMoveLeftBit write bit sl tl tr) (n + 3) :=
  ⟨bound_fBitCons bit (by omega) (by omega),
   ⟨by omega, by omega⟩,
   bound_fBitCons write (by omega) (by omega),
   bound_fBitCons bit (by omega) (by omega)⟩

private def fMove (read write direction : Bool) (next : Nat) (_sq sl sr tq tl tr : Nat) : Formula :=
  .ex
    (.and (fBitCons read 0 (sr + 1))
    (.and (fNumeral next (tq + 1))
      (if direction then
        .and (fBitCons write (sl + 1) (tl + 1)) (.eq (tr + 1) 0)
      else
        .ex (.ex (.or (fMoveLeftBit write false sl tl tr) (fMoveLeftBit write true sl tl tr))))))

private theorem bound_fMove (read write direction : Bool) (next : Nat)
    {sq sl sr tq tl tr n : Nat}
    (_hq : sq < n) (hl : sl < n) (hr : sr < n) (htq : tq < n) (htl : tl < n) (htr : tr < n) :
    Bound (fMove read write direction next sq sl sr tq tl tr) n := by
  refine ⟨bound_fBitCons read (by omega) (by omega), bound_fNumeral next _ _ (by omega), ?_⟩
  cases direction
  · exact ⟨bound_fMoveLeftBit write false hl htl htr, bound_fMoveLeftBit write true hl htl htr⟩
  · exact ⟨bound_fBitCons write (by omega) (by omega), ⟨by omega, by omega⟩⟩

private theorem eval_fMove {V : Type} (E : V → V → Prop) (read write direction : Bool) (next : Nat)
    (sq sl sr tq tl tr : Nat) (s : Nat → V) :
    eval E (fMove read write direction next sq sl sr tq tl tr) s ↔
      Move E read write direction next ⟨s sq, s sl, s sr⟩ ⟨s tq, s tl, s tr⟩ := by
  cases direction
  · constructor
    · rintro ⟨r, hr, hq, l, middle, hbranch⟩
      refine ⟨r, (eval_fBitCons E read 0 (sr + 1) (pushValue s r)).mp hr,
        (eval_fNumeral E next (tq + 1) (pushValue s r)).mp hq, ?_⟩
      cases hbranch with
      | inl hf =>
        rcases hf with ⟨h1, h2, h3, h4⟩
        exact ⟨l, false, middle, (eval_fBitCons E _ _ _ _).mp h1, h2,
          (eval_fBitCons E _ _ _ _).mp h3, (eval_fBitCons E _ _ _ _).mp h4⟩
      | inr ht =>
        rcases ht with ⟨h1, h2, h3, h4⟩
        exact ⟨l, true, middle, (eval_fBitCons E _ _ _ _).mp h1, h2,
          (eval_fBitCons E _ _ _ _).mp h3, (eval_fBitCons E _ _ _ _).mp h4⟩
    · rintro ⟨r, hr, hq, l, bit, middle, h1, h2, h3, h4⟩
      refine ⟨r, (eval_fBitCons E _ _ _ _).mpr hr, (eval_fNumeral E _ _ _).mpr hq, l, middle, ?_⟩
      cases bit
      · exact Or.inl ⟨(eval_fBitCons E _ _ _ _).mpr h1, h2,
          (eval_fBitCons E _ _ _ _).mpr h3, (eval_fBitCons E _ _ _ _).mpr h4⟩
      · exact Or.inr ⟨(eval_fBitCons E _ _ _ _).mpr h1, h2,
          (eval_fBitCons E _ _ _ _).mpr h3, (eval_fBitCons E _ _ _ _).mpr h4⟩
  · constructor
    · rintro ⟨r, hr, hq, hl, htr⟩
      exact ⟨r, (eval_fBitCons E read 0 (sr + 1) (pushValue s r)).mp hr,
        (eval_fNumeral E next (tq + 1) (pushValue s r)).mp hq,
        (eval_fBitCons E write (sl + 1) (tl + 1) (pushValue s r)).mp hl, htr⟩
    · rintro ⟨r, hr, hq, hl, htr⟩
      exact ⟨r, (eval_fBitCons E read 0 (sr + 1) (pushValue s r)).mpr hr,
        (eval_fNumeral E next (tq + 1) (pushValue s r)).mpr hq,
        (eval_fBitCons E write (sl + 1) (tl + 1) (pushValue s r)).mpr hl, htr⟩

private def fAnyFin : Nat → (Nat → Formula) → Formula
  | 0, _ => .bot
  | k + 1, F => .or (fAnyFin k F) (F k)

private theorem bound_fAnyFin : ∀ (k n : Nat) (F : Nat → Formula),
    (∀ i < k, Bound (F i) n) → Bound (fAnyFin k F) n
  | 0, _, _, _ => trivial
  | k + 1, n, F, hF =>
    ⟨bound_fAnyFin k n F (fun i hi => hF i (Nat.lt_succ_of_lt hi)), hF k (Nat.lt_succ_self k)⟩

private theorem eval_fAnyFin {V : Type} (E : V → V → Prop) :
    ∀ (k : Nat) (F : Nat → Formula) (s : Nat → V),
      eval E (fAnyFin k F) s ↔ ∃ q : Fin k, eval E (F q.val) s
  | 0, _, _ => ⟨fun h => False.elim h, fun ⟨q, _⟩ => Fin.elim0 q⟩
  | k + 1, F, s => by
    constructor
    · intro h
      cases h with
      | inl h1 =>
        obtain ⟨q, hq⟩ := (eval_fAnyFin E k F s).mp h1
        exact ⟨⟨q.val, Nat.lt_succ_of_lt q.isLt⟩, hq⟩
      | inr h2 =>
        exact ⟨⟨k, Nat.lt_succ_self k⟩, h2⟩
    · rintro ⟨⟨q, hq⟩, hFq⟩
      by_cases hlt : q < k
      · exact Or.inl ((eval_fAnyFin E k F s).mpr ⟨⟨q, hlt⟩, hFq⟩)
      · have heq : q = k := by omega
        subst heq
        exact Or.inr hFq

private def fAllFin : Nat → (Nat → Formula) → Formula
  | 0, _ => fTrue
  | k + 1, F => .and (fAllFin k F) (F k)

private theorem bound_fAllFin : ∀ (k n : Nat) (F : Nat → Formula),
    (∀ i < k, Bound (F i) n) → Bound (fAllFin k F) n
  | 0, n, _, _ => bound_fTrue n
  | k + 1, n, F, hF =>
    ⟨bound_fAllFin k n F (fun i hi => hF i (Nat.lt_succ_of_lt hi)), hF k (Nat.lt_succ_self k)⟩

private theorem eval_fAllFin {V : Type} (E : V → V → Prop) :
    ∀ (k : Nat) (F : Nat → Formula) (s : Nat → V),
      eval E (fAllFin k F) s ↔ ∀ q : Fin k, eval E (F q.val) s
  | 0, _, _ => ⟨fun _ q => Fin.elim0 q, fun _ h => h⟩
  | k + 1, F, s => by
    constructor
    · rintro ⟨h1, h2⟩ ⟨q, hq⟩
      by_cases hlt : q < k
      · exact (eval_fAllFin E k F s).mp h1 ⟨q, hlt⟩
      · have heq : q = k := by omega
        subst heq
        exact h2
    · intro h
      exact ⟨(eval_fAllFin E k F s).mpr (fun q => h ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩),
        h ⟨k, Nat.lt_succ_self k⟩⟩

private def fRowBranch (q : Nat) (read : Bool) (sq sl sr tq tl tr : Nat) : Formula :=
  match (if read then (literalRows.getD q (none, none)).2
         else (literalRows.getD q (none, none)).1) with
  | none => .bot
  | some (write, direction, next) => fMove read write direction next sq sl sr tq tl tr

private theorem bound_fRowBranch (q : Nat) (read : Bool) {sq sl sr tq tl tr n : Nat}
    (hq : sq < n) (hl : sl < n) (hr : sr < n) (htq : tq < n) (htl : tl < n) (htr : tr < n) :
    Bound (fRowBranch q read sq sl sr tq tl tr) n := by
  unfold fRowBranch
  cases (if read then (literalRows.getD q (none, none)).2
         else (literalRows.getD q (none, none)).1) with
  | none => exact trivial
  | some entry =>
    rcases entry with ⟨write, direction, next⟩
    exact bound_fMove read write direction next hq hl hr htq htl htr

private theorem eval_fRowBranch {V : Type} (E : V → V → Prop) (q : Nat) (read : Bool)
    (sq sl sr tq tl tr : Nat) (s : Nat → V) :
    eval E (fRowBranch q read sq sl sr tq tl tr) s ↔
      ∃ write direction next,
        (if read then (literalRows.getD q (none, none)).2
         else (literalRows.getD q (none, none)).1) = some (write, direction, next) ∧
        Move E read write direction next ⟨s sq, s sl, s sr⟩ ⟨s tq, s tl, s tr⟩ := by
  unfold fRowBranch
  cases hrow : (if read then (literalRows.getD q (none, none)).2
                else (literalRows.getD q (none, none)).1) with
  | none =>
    constructor
    · intro h; exact False.elim h
    · rintro ⟨_, _, _, heq, _⟩; cases heq
  | some entry =>
    rcases entry with ⟨write, direction, next⟩
    constructor
    · intro hm
      exact ⟨write, direction, next, rfl, (eval_fMove E read write direction next _ _ _ _ _ _ s).mp hm⟩
    · rintro ⟨w', d', n', heq, hm⟩
      injection heq with htuple
      cases htuple
      exact (eval_fMove E read write direction next _ _ _ _ _ _ s).mpr hm

private def fStep (sq sl sr tq tl tr : Nat) : Formula :=
  .and (fValid sq sl sr) (.and (fValid tq tl tr)
    (fAnyFin 207 (fun q =>
      .and (fNumeral q sq)
        (.or (fRowBranch q false sq sl sr tq tl tr) (fRowBranch q true sq sl sr tq tl tr)))))

private theorem bound_fStep {sq sl sr tq tl tr n : Nat}
    (hq : sq < n) (hl : sl < n) (hr : sr < n) (htq : tq < n) (htl : tl < n) (htr : tr < n) :
    Bound (fStep sq sl sr tq tl tr) n := by
  refine ⟨bound_fValid hq hl hr, bound_fValid htq htl htr, bound_fAnyFin 207 n _ ?_⟩
  intro i _
  exact ⟨bound_fNumeral i sq n hq,
    bound_fRowBranch i false hq hl hr htq htl htr,
    bound_fRowBranch i true hq hl hr htq htl htr⟩

private theorem eval_fStep {V : Type} (E : V → V → Prop) (sq sl sr tq tl tr : Nat) (s : Nat → V) :
    eval E (fStep sq sl sr tq tl tr) s ↔ Step E ⟨s sq, s sl, s sr⟩ ⟨s tq, s tl, s tr⟩ := by
  constructor
  · rintro ⟨hvs, hvt, hqany⟩
    obtain ⟨q, hnum, hread⟩ := (eval_fAnyFin E 207 _ s).mp hqany
    refine ⟨(eval_fValid E _ _ _ s).mp hvs, (eval_fValid E _ _ _ s).mp hvt, q,
      (eval_fNumeral E _ _ s).mp hnum, ?_⟩
    cases hread with
    | inl hf =>
      obtain ⟨w, d, nxt, hrow, hm⟩ := (eval_fRowBranch E q.val false _ _ _ _ _ _ s).mp hf
      exact ⟨false, w, d, nxt, hrow, hm⟩
    | inr ht =>
      obtain ⟨w, d, nxt, hrow, hm⟩ := (eval_fRowBranch E q.val true _ _ _ _ _ _ s).mp ht
      exact ⟨true, w, d, nxt, hrow, hm⟩
  · rintro ⟨hvs, hvt, q, hnum, read, w, d, nxt, hrow, hm⟩
    refine ⟨(eval_fValid E _ _ _ s).mpr hvs, (eval_fValid E _ _ _ s).mpr hvt,
      (eval_fAnyFin E 207 _ s).mpr ⟨q, (eval_fNumeral E _ _ s).mpr hnum, ?_⟩⟩
    cases read
    · exact Or.inl ((eval_fRowBranch E q.val false _ _ _ _ _ _ s).mpr ⟨w, d, nxt, hrow, hm⟩)
    · exact Or.inr ((eval_fRowBranch E q.val true _ _ _ _ _ _ s).mpr ⟨w, d, nxt, hrow, hm⟩)

private def fTerminal (sq : Nat) : Formula :=
  fAllFin 207 (fun q => fNot (fNumeral q sq))

private theorem bound_fTerminal {sq n : Nat} (hq : sq < n) : Bound (fTerminal sq) n :=
  bound_fAllFin 207 n _ (fun i _ => bound_fNot (bound_fNumeral i sq n hq))

private theorem eval_fTerminal {V : Type} (E : V → V → Prop) (sq sl sr : Nat) (s : Nat → V) :
    eval E (fTerminal sq) s ↔ Terminal E ⟨s sq, s sl, s sr⟩ := by
  constructor
  · intro h q hnum
    exact (eval_fAllFin E 207 _ s).mp h q ((eval_fNumeral E q.val sq s).mpr hnum)
  · intro h
    exact (eval_fAllFin E 207 _ s).mpr (fun q hnum => h q ((eval_fNumeral E q.val sq s).mp hnum))

private def fCantor (a b z : Nat) : Formula :=
  .and (fNatObject a) (.and (fNatObject b) (.and (fNatObject z)
    (.ex (.ex (.ex (.ex (.ex (.ex (.ex
      (.and (fNumeral 2 6)
      (.and (fAdd (a + 7) (b + 7) 5)
      (.and (fSucc 5 4)
      (.and (fMul 5 4 3)
      (.and (fMul 6 (b + 7) 2)
      (.and (fMul 6 (z + 7) 1)
      (.and (fAdd 3 2 0) (.eq 1 0)))))))))))))))))

private theorem bound_fCantor {a b z n : Nat} (ha : a < n) (hb : b < n) (hz : z < n) :
    Bound (fCantor a b z) n :=
  ⟨bound_fNatObject ha, bound_fNatObject hb, bound_fNatObject hz,
   bound_fNumeral 2 6 _ (by omega),
   bound_fAdd (by omega) (by omega) (by omega),
   bound_fSucc (by omega) (by omega),
   bound_fMul (by omega) (by omega) (by omega),
   bound_fMul (by omega) (by omega) (by omega),
   bound_fMul (by omega) (by omega) (by omega),
   bound_fAdd (by omega) (by omega) (by omega),
   ⟨by omega, by omega⟩⟩

private theorem eval_fCantor {V : Type} (E : V → V → Prop) (a b z : Nat) (s : Nat → V) :
    eval E (fCantor a b z) s ↔ Cantor E (s a) (s b) (s z) := by
  constructor
  · rintro ⟨ha, hb, hz, two, sum, nxt, prod, tb, tz, tot, h2, hsum, hnxt, hprod, htb, htz, htot, heq⟩
    exact ⟨(eval_fNatObject E _ _).mp ha, (eval_fNatObject E _ _).mp hb, (eval_fNatObject E _ _).mp hz,
      two, sum, nxt, prod, tb, tz, tot,
      (eval_fNumeral E _ _ _).mp h2, (eval_fAdd E _ _ _ _).mp hsum,
      (eval_fSucc E _ _ _).mp hnxt, (eval_fMul E _ _ _ _).mp hprod,
      (eval_fMul E _ _ _ _).mp htb, (eval_fMul E _ _ _ _).mp htz,
      (eval_fAdd E _ _ _ _).mp htot, heq⟩
  · rintro ⟨ha, hb, hz, two, sum, nxt, prod, tb, tz, tot, h2, hsum, hnxt, hprod, htb, htz, htot, heq⟩
    exact ⟨(eval_fNatObject E _ _).mpr ha, (eval_fNatObject E _ _).mpr hb, (eval_fNatObject E _ _).mpr hz,
      two, sum, nxt, prod, tb, tz, tot,
      (eval_fNumeral E _ _ _).mpr h2, (eval_fAdd E _ _ _ _).mpr hsum,
      (eval_fSucc E _ _ _).mpr hnxt, (eval_fMul E _ _ _ _).mpr hprod,
      (eval_fMul E _ _ _ _).mpr htb, (eval_fMul E _ _ _ _).mpr htz,
      (eval_fAdd E _ _ _ _).mpr htot, heq⟩

private def fListCons (a b c : Nat) : Formula :=
  .ex (.and (fCantor (a + 1) (b + 1) 0) (fSucc 0 (c + 1)))

private theorem bound_fListCons {a b c n : Nat} (ha : a < n) (hb : b < n) (hc : c < n) :
    Bound (fListCons a b c) n :=
  ⟨bound_fCantor (by omega) (by omega) (by omega), bound_fSucc (by omega) (by omega)⟩

private theorem eval_fListCons {V : Type} (E : V → V → Prop) (a b c : Nat) (s : Nat → V) :
    eval E (fListCons a b c) s ↔ ListCons E (s a) (s b) (s c) := by
  constructor
  · rintro ⟨p, hp, hsucc⟩; exact ⟨p, (eval_fCantor E _ _ _ _).mp hp, (eval_fSucc E _ _ _).mp hsucc⟩
  · rintro ⟨p, hp, hsucc⟩; exact ⟨p, (eval_fCantor E _ _ _ _).mpr hp, (eval_fSucc E _ _ _).mpr hsucc⟩

private def fListHead (x a : Nat) : Formula :=
  .or (.and (fEmpty x) (fEmpty a)) (.ex (fListCons (a + 1) 0 (x + 1)))

private theorem bound_fListHead {x a n : Nat} (hx : x < n) (ha : a < n) :
    Bound (fListHead x a) n :=
  ⟨⟨bound_fEmpty hx, bound_fEmpty ha⟩, bound_fListCons (by omega) (by omega) (by omega)⟩

private theorem eval_fListHead {V : Type} (E : V → V → Prop) (x a : Nat) (s : Nat → V) :
    eval E (fListHead x a) s ↔ ListHead E (s x) (s a) := by
  constructor
  · intro h
    cases h with
    | inl h0 => exact Or.inl ⟨(eval_fEmpty E _ _).mp h0.1, (eval_fEmpty E _ _).mp h0.2⟩
    | inr h1 =>
      obtain ⟨b, hb⟩ := h1
      exact Or.inr ⟨b, (eval_fListCons E _ _ _ _).mp hb⟩
  · intro h
    cases h with
    | inl h0 => exact Or.inl ⟨(eval_fEmpty E _ _).mpr h0.1, (eval_fEmpty E _ _).mpr h0.2⟩
    | inr h1 =>
      obtain ⟨b, hb⟩ := h1
      exact Or.inr ⟨b, (eval_fListCons E _ _ _ _).mpr hb⟩

private def fListTail (x b : Nat) : Formula :=
  .or (.and (fEmpty x) (fEmpty b)) (.ex (fListCons 0 (b + 1) (x + 1)))

private theorem bound_fListTail {x b n : Nat} (hx : x < n) (hb : b < n) :
    Bound (fListTail x b) n :=
  ⟨⟨bound_fEmpty hx, bound_fEmpty hb⟩, bound_fListCons (by omega) (by omega) (by omega)⟩

private theorem eval_fListTail {V : Type} (E : V → V → Prop) (x b : Nat) (s : Nat → V) :
    eval E (fListTail x b) s ↔ ListTail E (s x) (s b) := by
  constructor
  · intro h
    cases h with
    | inl h0 => exact Or.inl ⟨(eval_fEmpty E _ _).mp h0.1, (eval_fEmpty E _ _).mp h0.2⟩
    | inr h1 =>
      obtain ⟨a, ha⟩ := h1
      exact Or.inr ⟨a, (eval_fListCons E _ _ _ _).mp ha⟩
  · intro h
    cases h with
    | inl h0 => exact Or.inl ⟨(eval_fEmpty E _ _).mpr h0.1, (eval_fEmpty E _ _).mpr h0.2⟩
    | inr h1 =>
      obtain ⟨a, ha⟩ := h1
      exact Or.inr ⟨a, (eval_fListCons E _ _ _ _).mpr ha⟩

private def fNumericConfCode (sq sl sr code : Nat) : Formula :=
  .ex (.and (fCantor (sl + 1) (sr + 1) 0) (fCantor (sq + 1) 0 (code + 1)))

private theorem bound_fNumericConfCode {sq sl sr code n : Nat}
    (hq : sq < n) (hl : sl < n) (hr : sr < n) (hc : code < n) :
    Bound (fNumericConfCode sq sl sr code) n :=
  ⟨bound_fCantor (by omega) (by omega) (by omega), bound_fCantor (by omega) (by omega) (by omega)⟩

private theorem eval_fNumericConfCode {V : Type} (E : V → V → Prop)
    (sq sl sr code : Nat) (s : Nat → V) :
    eval E (fNumericConfCode sq sl sr code) s ↔
      NumericConfCode E ⟨s sq, s sl, s sr⟩ (s code) := by
  constructor
  · rintro ⟨lr, h1, h2⟩
    exact ⟨lr, (eval_fCantor E _ _ _ _).mp h1, (eval_fCantor E _ _ _ _).mp h2⟩
  · rintro ⟨lr, h1, h2⟩
    exact ⟨lr, (eval_fCantor E _ _ _ _).mpr h1, (eval_fCantor E _ _ _ _).mpr h2⟩

private def fNumericStep (before after : Nat) : Formula :=
  .ex (.ex (.ex (.ex (.ex (.ex
    (.and (fNumericConfCode 5 4 3 (before + 6))
    (.and (fNumericConfCode 2 1 0 (after + 6)) (fStep 5 4 3 2 1 0))))))))

private theorem bound_fNumericStep {before after n : Nat} (hb : before < n) (ha : after < n) :
    Bound (fNumericStep before after) n :=
  ⟨bound_fNumericConfCode (by omega) (by omega) (by omega) (by omega),
   bound_fNumericConfCode (by omega) (by omega) (by omega) (by omega),
   bound_fStep (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

private theorem eval_fNumericStep {V : Type} (E : V → V → Prop)
    (before after : Nat) (s : Nat → V) :
    eval E (fNumericStep before after) s ↔ NumericStep E (s before) (s after) := by
  constructor
  · rintro ⟨sq, sl, sr, tq, tl, tr, h1, h2, h3⟩
    exact ⟨⟨sq, sl, sr⟩, ⟨tq, tl, tr⟩,
      (eval_fNumericConfCode E _ _ _ _ _).mp h1,
      (eval_fNumericConfCode E _ _ _ _ _).mp h2,
      (eval_fStep E _ _ _ _ _ _ _).mp h3⟩
  · rintro ⟨⟨sq, sl, sr⟩, ⟨tq, tl, tr⟩, h1, h2, h3⟩
    exact ⟨sq, sl, sr, tq, tl, tr,
      (eval_fNumericConfCode E _ _ _ _ _).mpr h1,
      (eval_fNumericConfCode E _ _ _ _ _).mpr h2,
      (eval_fStep E _ _ _ _ _ _ _).mpr h3⟩

private def fRunEdge (initial next tail : Nat) : Formula :=
  .or
    (.and (fEmpty tail) (.eq next initial))
    (.and (fNot (fEmpty tail))
      (.ex (.and (fListHead (tail + 1) 0) (fNumericStep 0 (next + 1)))))

private theorem bound_fRunEdge {initial next tail n : Nat}
    (hi : initial < n) (hn : next < n) (ht : tail < n) :
    Bound (fRunEdge initial next tail) n :=
  ⟨⟨bound_fEmpty ht, ⟨hn, hi⟩⟩,
   ⟨bound_fNot (bound_fEmpty ht),
    ⟨bound_fListHead (by omega) (by omega), bound_fNumericStep (by omega) (by omega)⟩⟩⟩

private theorem eval_fRunEdge {V : Type} (E : V → V → Prop)
    (initial next tail : Nat) (s : Nat → V) :
    eval E (fRunEdge initial next tail) s ↔ RunEdge E (s initial) (s next) (s tail) := by
  constructor
  · intro h
    cases h with
    | inl h0 => exact Or.inl ⟨(eval_fEmpty E _ _).mp h0.1, h0.2⟩
    | inr h1 =>
      rcases h1 with ⟨hne, prev, hhd, hstep⟩
      exact Or.inr ⟨hne, prev, (eval_fListHead E _ _ _).mp hhd, (eval_fNumericStep E _ _ _).mp hstep⟩
  · intro h
    cases h with
    | inl h0 => exact Or.inl ⟨(eval_fEmpty E _ _).mpr h0.1, h0.2⟩
    | inr h1 =>
      rcases h1 with ⟨hne, prev, hhd, hstep⟩
      exact Or.inr ⟨hne, prev, (eval_fListHead E _ _ _).mpr hhd, (eval_fNumericStep E _ _ _).mpr hstep⟩

private def fLinkedRun (initial code : Nat) : Formula :=
  .and (fNatObject initial) (.and (fNatObject code) (.and (fNot (fEmpty code))
    (.ex (.ex (.ex
      (.and (fEmpty 2)
      (.and (fSucc (code + 3) 1)
      (.and (fFunctionOn 0 1)
      (.and (fAt 0 2 (code + 3))
      (.and (fAt 0 (code + 3) 2)
      (.and (.all (.all (.imp (.mem 1 3) (.imp (fAt 2 1 0) (fNatObject 0)))))
        (.all (.imp (.mem 0 (code + 4))
          (.ex (.ex (.ex
            (.and (fSucc 3 2)
            (.and (fAt 4 3 1)
            (.and (fAt 4 2 0)
            (.and (fListTail 1 0)
              (.or (fEmpty 1)
                (.ex (.ex
                  (.and (fListHead 3 1)
                  (.and (fListTail 3 0)
                    (fRunEdge (initial + 9) 1 0))))))))))))))))))))))))))

private theorem bound_fLinkedRun {initial code n : Nat} (hi : initial < n) (hc : code < n) :
    Bound (fLinkedRun initial code) n := by
  refine ⟨bound_fNatObject hi, bound_fNatObject hc, bound_fNot (bound_fEmpty hc),
    bound_fEmpty (by omega), bound_fSucc (by omega) (by omega),
    bound_fFunctionOn (by omega) (by omega),
    bound_fAt (by omega) (by omega) (by omega),
    bound_fAt (by omega) (by omega) (by omega),
    ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
    ⟨⟨by omega, by omega⟩,
     bound_fSucc (by omega) (by omega),
     bound_fAt (by omega) (by omega) (by omega),
     bound_fAt (by omega) (by omega) (by omega),
     bound_fListTail (by omega) (by omega),
     ⟨bound_fEmpty (by omega),
      bound_fListHead (by omega) (by omega),
      bound_fListTail (by omega) (by omega),
      bound_fRunEdge (by omega) (by omega) (by omega)⟩⟩⟩

private theorem eval_fLinkedRun {V : Type} (E : V → V → Prop)
    (initial code : Nat) (s : Nat → V) :
    eval E (fLinkedRun initial code) s ↔ LinkedRun E (s initial) (s code) := by
  constructor
  · rintro ⟨hi, hc, hne, z, dom, f, hz, hdom, hfun, hf0, hfc, hnat, hstep⟩
    refine ⟨(eval_fNatObject E _ _).mp hi, (eval_fNatObject E _ _).mp hc, hne,
      z, dom, f, (eval_fEmpty E _ _).mp hz, (eval_fSucc E _ _ _).mp hdom,
      (eval_fFunctionOn E _ _ _).mp hfun, (eval_fAt E _ _ _ _).mp hf0,
      (eval_fAt E _ _ _ _).mp hfc, ?_, ?_⟩
    · intro i x hdomi hfix
      exact (eval_fNatObject E _ _).mp (hnat i x hdomi ((eval_fAt E _ _ _ _).mpr hfix))
    · intro i hic
      obtain ⟨j, x, y, hij, hfix, hfjy, htail, hedge⟩ := hstep i hic
      refine ⟨j, x, y, (eval_fSucc E _ _ _).mp hij, (eval_fAt E _ _ _ _).mp hfix,
        (eval_fAt E _ _ _ _).mp hfjy, (eval_fListTail E _ _ _).mp htail, ?_⟩
      cases hedge with
      | inl hx0 => exact Or.inl ((eval_fEmpty E _ _).mp hx0)
      | inr hx1 =>
        rcases hx1 with ⟨a, b, hhd, htl, hre⟩
        exact Or.inr ⟨a, b, (eval_fListHead E _ _ _).mp hhd, (eval_fListTail E _ _ _).mp htl,
          (eval_fRunEdge E _ _ _ _).mp hre⟩
  · rintro ⟨hi, hc, hne, z, dom, f, hz, hdom, hfun, hf0, hfc, hnat, hstep⟩
    refine ⟨(eval_fNatObject E _ _).mpr hi, (eval_fNatObject E _ _).mpr hc, hne,
      z, dom, f, (eval_fEmpty E _ _).mpr hz, (eval_fSucc E _ _ _).mpr hdom,
      (eval_fFunctionOn E _ _ _).mpr hfun, (eval_fAt E _ _ _ _).mpr hf0,
      (eval_fAt E _ _ _ _).mpr hfc, ?_, ?_⟩
    · intro i x hdomi hfix
      exact (eval_fNatObject E _ _).mpr (hnat i x hdomi ((eval_fAt E _ _ _ _).mp hfix))
    · intro i hic
      obtain ⟨j, x, y, hij, hfix, hfjy, htail, hedge⟩ := hstep i hic
      refine ⟨j, x, y, (eval_fSucc E _ _ _).mpr hij, (eval_fAt E _ _ _ _).mpr hfix,
        (eval_fAt E _ _ _ _).mpr hfjy, (eval_fListTail E _ _ _).mpr htail, ?_⟩
      cases hedge with
      | inl hx0 => exact Or.inl ((eval_fEmpty E _ _).mpr hx0)
      | inr hx1 =>
        rcases hx1 with ⟨a, b, hhd, htl, hre⟩
        exact Or.inr ⟨a, b, (eval_fListHead E _ _ _).mpr hhd, (eval_fListTail E _ _ _).mpr htl,
          (eval_fRunEdge E _ _ _ _).mpr hre⟩

def haltFormula : Formula :=
  .ex (.ex (.ex (.ex (.ex (.ex
    (.and (fEmpty 5)
    (.and (fLinkedRun 5 4)
    (.and (fListHead 4 3)
    (.and (fNumericConfCode 2 1 0 3)
    (.and (fValid 2 1 0) (fTerminal 2)))))))))))

theorem haltFormula_closed : Closed haltFormula :=
  ⟨bound_fEmpty (by omega),
   bound_fLinkedRun (by omega) (by omega),
   bound_fListHead (by omega) (by omega),
   bound_fNumericConfCode (by omega) (by omega) (by omega) (by omega),
   bound_fValid (by omega) (by omega) (by omega),
   bound_fTerminal (by omega)⟩

theorem eval_haltFormula {V : Type} (E : V → V → Prop) (s : Nat → V) :
    eval E haltFormula s ↔ InternalLinkedHalts E := by
  constructor
  · rintro ⟨zero, hist, last, tq, tl, tr, hz, hrun, hhd, hcode, hval, hterm⟩
    exact ⟨zero, hist, last, ⟨tq, tl, tr⟩,
      (eval_fEmpty E _ _).mp hz,
      (eval_fLinkedRun E _ _ _).mp hrun,
      (eval_fListHead E _ _ _).mp hhd,
      (eval_fNumericConfCode E _ _ _ _ _).mp hcode,
      (eval_fValid E _ _ _ _).mp hval,
      (eval_fTerminal E 2 1 0 _).mp hterm⟩
  · rintro ⟨zero, hist, last, ⟨tq, tl, tr⟩, hz, hrun, hhd, hcode, hval, hterm⟩
    exact ⟨zero, hist, last, tq, tl, tr,
      (eval_fEmpty E _ _).mpr hz,
      (eval_fLinkedRun E _ _ _).mpr hrun,
      (eval_fListHead E _ _ _).mpr hhd,
      (eval_fNumericConfCode E _ _ _ _ _).mpr hcode,
      (eval_fValid E _ _ _ _).mpr hval,
      (eval_fTerminal E 2 1 0 _).mpr hterm⟩

end SolRepresents207

theorem solution : ∃ H : Formula, Represents207 H :=
  ⟨SolRepresents207.haltFormula, SolRepresents207.haltFormula_closed,
   fun _ E _ _ s => SolRepresents207.eval_haltFormula E s⟩
