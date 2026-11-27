-- Prove2me | solution 1 for PalomarZF207.internal_provC1_implies_reg_halts
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-27T04:14:45.482078+00:00
-- url     : https://prove2.me/submissions/d57eccd6-7787-4a1a-ad60-46c32442ac85

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_internal_prov
import Definitions.Def_palomar_zf207_internal_tm
import Theorems.Thm_PalomarZF207_internal_startup_and_linkedHalts

open PalomarZF207
open PalomarZF207History
open PalomarZF207Internal
open PalomarZF207InternalTM

namespace SolInternalRegHalts

/-! ### Part 1: Core ZF Model Infrastructure & Internal Arithmetic -/

private theorem pushValue_comp_lift {V : Type} (σ : Nat → Nat) (s : Nat → V) (x : V) :
    (fun i => pushValue s x (lift σ i)) = pushValue (fun i => s (σ i)) x := by
  funext i; cases i <;> rfl

private theorem eval_rename {V : Type} (E : V → V → Prop) :
    ∀ (f : Formula) (σ : Nat → Nat) (s : Nat → V),
      eval E (rename σ f) s ↔ eval E f (fun i => s (σ i))
  | .bot, _, _ => Iff.rfl
  | .mem _ _, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl
  | .and p q, σ, s => by simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .or p q, σ, s => by simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .imp p q, σ, s => by simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .all p, σ, s => by
    constructor
    · intro h x; have hx := (eval_rename E p (lift σ) (pushValue s x)).mp (h x); rwa [pushValue_comp_lift] at hx
    · intro h x; apply (eval_rename E p (lift σ) (pushValue s x)).mpr; rw [pushValue_comp_lift]; exact h x
  | .ex p, σ, s => by
    constructor
    · rintro ⟨x, hx⟩; have hx' := (eval_rename E p (lift σ) (pushValue s x)).mp hx; rw [pushValue_comp_lift] at hx'; exact ⟨x, hx'⟩
    · rintro ⟨x, hx⟩; refine ⟨x, (eval_rename E p (lift σ) (pushValue s x)).mpr ?_⟩; rw [pushValue_comp_lift]; exact hx

private theorem eval_congr_bound {V : Type} (E : V → V → Prop) :
    ∀ (f : Formula) (n : Nat) (s₁ s₂ : Nat → V),
      Bound f n → (∀ i < n, s₁ i = s₂ i) → (eval E f s₁ ↔ eval E f s₂)
  | .bot, _, _, _, _, _ => Iff.rfl
  | .mem i j, _, _, _, ⟨hi, hj⟩, h => by simp only [eval, h i hi, h j hj]
  | .eq i j, _, _, _, ⟨hi, hj⟩, h => by simp only [eval, h i hi, h j hj]
  | .and p q, n, s₁, s₂, ⟨hp, hq⟩, h => by simp only [eval, eval_congr_bound E p n s₁ s₂ hp h, eval_congr_bound E q n s₁ s₂ hq h]
  | .or p q, n, s₁, s₂, ⟨hp, hq⟩, h => by simp only [eval, eval_congr_bound E p n s₁ s₂ hp h, eval_congr_bound E q n s₁ s₂ hq h]
  | .imp p q, n, s₁, s₂, ⟨hp, hq⟩, h => by simp only [eval, eval_congr_bound E p n s₁ s₂ hp h, eval_congr_bound E q n s₁ s₂ hq h]
  | .all p, n, s₁, s₂, hp, h => by
    constructor
    · intro h1 x; exact (eval_congr_bound E p (n + 1) (pushValue s₁ x) (pushValue s₂ x) hp (fun i hi => by
        cases i with | zero => rfl | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mp (h1 x)
    · intro h2 x; exact (eval_congr_bound E p (n + 1) (pushValue s₁ x) (pushValue s₂ x) hp (fun i hi => by
        cases i with | zero => rfl | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mpr (h2 x)
  | .ex p, n, s₁, s₂, hp, h => by
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, (eval_congr_bound E p (n + 1) (pushValue s₁ x) (pushValue s₂ x) hp (fun i hi => by
        cases i with | zero => rfl | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mp hx⟩
    · rintro ⟨x, hx⟩; exact ⟨x, (eval_congr_bound E p (n + 1) (pushValue s₁ x) (pushValue s₂ x) hp (fun i hi => by
        cases i with | zero => rfl | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mpr hx⟩

private def pushParams {V : Type} (s : Nat → V) : List V → Nat → V
  | [] => s
  | x :: xs => pushParams (pushValue s x) xs

private def mkParams {V : Type} (env : Nat → V) : Nat → List V
  | 0 => []
  | n + 1 => env n :: mkParams env n

private theorem mkParams_length {V : Type} (env : Nat → V) : ∀ n, (mkParams env n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (mkParams_length env n)

private theorem pushParams_mkParams_ge {V : Type} (env s : Nat → V) :
    ∀ n k, pushParams s (mkParams env n) (n + k) = s k
  | 0, k => by simp [mkParams, pushParams]
  | n + 1, k => by
    rw [show n + 1 + k = n + (k + 1) by omega]
    show pushParams (pushValue s (env n)) (mkParams env n) (n + (k + 1)) = s k
    rw [pushParams_mkParams_ge env (pushValue s (env n)) n (k + 1)]; rfl

private theorem pushParams_mkParams_lt {V : Type} (env s : Nat → V) :
    ∀ n i, i < n → pushParams s (mkParams env n) i = env i
  | 0, _, hi => False.elim (Nat.not_lt_zero _ hi)
  | n + 1, i, hi => by
    show pushParams (pushValue s (env n)) (mkParams env n) i = env i
    by_cases hlt : i < n
    · exact pushParams_mkParams_lt env (pushValue s (env n)) n i hlt
    · have heq : i = n := by omega
      rw [heq]; simpa [pushValue] using pushParams_mkParams_ge env (pushValue s (env n)) n 0

private theorem eval_allPrefix {V : Type} (E : V → V → Prop) :
    ∀ (n : Nat) (f : Formula) (s : Nat → V) (xs : List V),
      xs.length = n → eval E (allPrefix n f) s → eval E f (pushParams s xs)
  | 0, _, _, [], _, h => h
  | n + 1, f, s, x :: xs, hlen, h =>
    eval_allPrefix E n f (pushValue s x) xs (Nat.succ.inj hlen) (h x)

section ZFModel

variable {V : Type} {E : V → V → Prop}

private theorem ax_ext (hM : Model E) (hNE : Nonempty V) {a b : V}
    (h1 : ∀ z, E z a → E z b) (h2 : ∀ z, E z b → E z a) : a = b := by
  have hAx : Axiom fixedExt := Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  exact hM fixedExt hAx (fun _ => Classical.choice hNE) a b h1 h2

private theorem ax_empty (hM : Model E) (hNE : Nonempty V) : ∃ z, Empty E z := by
  have hAx : Axiom fixedEmpty := Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  exact hM fixedEmpty hAx (fun _ => Classical.choice hNE)

private theorem ax_pair (hM : Model E) (hNE : Nonempty V) (a b : V) : ∃ p, Pair E a b p := by
  have hAx : Axiom fixedPair := Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  obtain ⟨p, hp⟩ := hM fixedPair hAx (fun _ => Classical.choice hNE) a b
  exact ⟨p, fun x => ⟨(hp x).1, (hp x).2⟩⟩

private theorem ax_union (hM : Model E) (hNE : Nonempty V) (u : V) :
    ∃ v, ∀ x, E x v ↔ ∃ y, E y u ∧ E x y := by
  have hAx : Axiom fixedUnion := Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  obtain ⟨v, hv⟩ := hM fixedUnion hAx (fun _ => Classical.choice hNE) u
  exact ⟨v, fun x => ⟨(hv x).1, (hv x).2⟩⟩

private theorem ax_omega (hM : Model E) (hNE : Nonempty V) : ∃ w, Omega E w := by
  have hAx : Axiom fixedOmega :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  obtain ⟨w, ⟨⟨z, hz, hzw⟩, hstep⟩, hmin⟩ := hM fixedOmega hAx (fun _ => Classical.choice hNE)
  refine ⟨w, ⟨⟨z, hz, hzw⟩, ?_⟩, ?_⟩
  · intro x hxw; obtain ⟨y, hy, hyw⟩ := hstep x hxw; exact ⟨y, fun t => ⟨(hy t).1, (hy t).2⟩, hyw⟩
  · intro a ⟨⟨za, hza, hzaa⟩, hstepa⟩ x hxw
    apply hmin a ⟨⟨za, hza, hzaa⟩, ?_⟩ x hxw
    intro u hua; obtain ⟨y, hy, hya⟩ := hstepa u hua; exact ⟨y, fun t => ⟨(hy t).mp, (hy t).mpr⟩, hya⟩

private theorem ax_foundation (hM : Model E) (hNE : Nonempty V) {a : V} (hne : ∃ x, E x a) :
    ∃ x, E x a ∧ ∀ y, E y x → ¬ E y a := by
  have hAx : Axiom fixedFoundation :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))))
  exact hM fixedFoundation hAx (fun _ => Classical.choice hNE) a hne

private theorem ax_sep (hM : Model E) (hNE : Nonempty V) (n : Nat) (body : Formula)
    (hB : Bound body (n + 1)) (env : Nat → V) (dom : V) :
    ∃ sub, ∀ x, E x sub ↔ E x dom ∧ eval E body (pushValue env x) := by
  have hAx : Axiom (separationSchema n body) := Or.inr (Or.inl ⟨n, body, hB, rfl⟩)
  let s₀ : Nat → V := fun _ => Classical.choice hNE
  have hSep := eval_allPrefix E n (separationFormula (rename sepIndex body)) s₀
    (mkParams env n) (mkParams_length env n) (hM (separationSchema n body) hAx s₀)
  obtain ⟨sub, hsub⟩ := hSep dom
  refine ⟨sub, fun x => ?_⟩
  have hEq : eval E (rename sepIndex body)
      (pushValue (pushValue (pushValue (pushParams s₀ (mkParams env n)) dom) sub) x) ↔
      eval E body (pushValue env x) := by
    rw [eval_rename]
    apply eval_congr_bound E body (n + 1) _ _ hB
    intro i hi
    cases i with
    | zero => rfl
    | succ k => exact pushParams_mkParams_lt env s₀ n k (Nat.lt_of_succ_lt_succ hi)
  exact ⟨fun h => let ⟨h1, h2⟩ := (hsub x).1 h; ⟨h1, hEq.mp h2⟩,
         fun ⟨h1, h2⟩ => (hsub x).2 ⟨h1, hEq.mpr h2⟩⟩

private theorem empty_unique (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : Empty E a) (hb : Empty E b) : a = b :=
  ax_ext hM hNE (fun z hz => False.elim (ha z hz)) (fun z hz => False.elim (hb z hz))

private theorem succ_unique (hM : Model E) (hNE : Nonempty V) {a b₁ b₂ : V}
    (h1 : Succ E a b₁) (h2 : Succ E a b₂) : b₁ = b₂ :=
  ax_ext hM hNE (fun z hz => (h2 z).mpr ((h1 z).mp hz)) (fun z hz => (h1 z).mpr ((h2 z).mp hz))

private theorem exists_binUnion (hM : Model E) (hNE : Nonempty V) (a b : V) :
    ∃ u, ∀ x, E x u ↔ E x a ∨ E x b := by
  obtain ⟨p, hp⟩ := ax_pair hM hNE a b
  obtain ⟨u, hu⟩ := ax_union hM hNE p
  refine ⟨u, fun x => ?_⟩
  rw [hu]
  constructor
  · rintro ⟨y, hyp, hxy⟩; rcases (hp y).mp hyp with rfl | rfl; exact Or.inl hxy; exact Or.inr hxy
  · rintro (hxa | hxb)
    · exact ⟨a, (hp a).mpr (Or.inl rfl), hxa⟩
    · exact ⟨b, (hp b).mpr (Or.inr rfl), hxb⟩

private theorem exists_insert (hM : Model E) (hNE : Nonempty V) (s x : V) :
    ∃ t, ∀ y, E y t ↔ E y s ∨ y = x := by
  obtain ⟨sx, hsx⟩ := ax_pair hM hNE x x
  obtain ⟨u, hu⟩ := exists_binUnion hM hNE s sx
  refine ⟨u, fun y => ?_⟩
  rw [hu]
  exact ⟨fun h => h.elim Or.inl (fun h2 => (hsx y).mp h2 |>.elim Or.inr Or.inr),
         fun h => h.elim Or.inl (fun h2 => Or.inr ((hsx y).mpr (Or.inl h2)))⟩

private theorem exists_succ (hM : Model E) (hNE : Nonempty V) (a : V) : ∃ b, Succ E a b :=
  exists_insert hM hNE a a

private theorem exists_orderedPair (hM : Model E) (hNE : Nonempty V) (a b : V) :
    ∃ p, OrderedPair E a b p := by
  obtain ⟨aa, haa⟩ := ax_pair hM hNE a a
  obtain ⟨ab, hab⟩ := ax_pair hM hNE a b
  obtain ⟨p, hp⟩ := ax_pair hM hNE aa ab
  exact ⟨p, aa, ab, haa, hab, hp⟩

private theorem orderedPair_inj {a b a' b' p : V}
    (h1 : OrderedPair E a b p) (h2 : OrderedPair E a' b' p) : a = a' ∧ b = b' := by
  rcases h1 with ⟨aa, ab, haa, hab, hp1⟩
  rcases h2 with ⟨aa', ab', haa', hab', hp2⟩
  have hmem_aa : aa = aa' ∨ aa = ab' := (hp2 aa).mp ((hp1 aa).mpr (Or.inl rfl))
  have ha_eq : a = a' := by
    rcases hmem_aa with h | h
    · rw [h] at haa; rcases (haa' a).mp ((haa a).mpr (Or.inl rfl)) with rfl | rfl <;> rfl
    · rw [h] at haa; rcases (haa a').mp ((hab' a').mpr (Or.inl rfl)) with rfl | rfl <;> rfl
  refine ⟨ha_eq, ?_⟩
  subst ha_eq
  have hmem_ab : ab = aa' ∨ ab = ab' := (hp2 ab).mp ((hp1 ab).mpr (Or.inr rfl))
  rcases hmem_ab with h | h
  · rw [h] at hab
    have hb_eq : b = a := by rcases (haa' b).mp ((hab b).mpr (Or.inr rfl)) with rfl | rfl <;> rfl
    rcases (hp1 ab').mp ((hp2 ab').mpr (Or.inr rfl)) with h' | h'
    · rw [h'] at hab'; have hb' : b' = a := by rcases (haa b').mp ((hab' b').mpr (Or.inr rfl)) with rfl | rfl <;> rfl
      exact hb_eq.trans hb'.symm
    · rw [h', h] at hab'; have hb' : b' = a := by rcases (haa' b').mp ((hab' b').mpr (Or.inr rfl)) with rfl | rfl <;> rfl
      exact hb_eq.trans hb'.symm
  · rw [h] at hab
    rcases (hab' b).mp ((hab b).mpr (Or.inr rfl)) with hba | hbb'
    · by_cases hb'a : b' = a
      · exact hba.trans hb'a.symm
      · rcases (hab b').mp ((hab' b').mpr (Or.inr rfl)) with h1 | h2
        · exact False.elim (hb'a h1)
        · exact h2.symm
    · exact hbb'

private theorem mem_irrefl (hM : Model E) (hNE : Nonempty V) (x : V) : ¬ E x x := by
  intro hxx
  obtain ⟨s, hs⟩ := ax_pair hM hNE x x
  obtain ⟨y, hys, hmin⟩ := ax_foundation hM hNE ⟨x, (hs x).mpr (Or.inl rfl)⟩
  rcases (hs y).mp hys with rfl | rfl <;> exact hmin y hxx ((hs y).mpr (Or.inl rfl))

private theorem mem_asymm (hM : Model E) (hNE : Nonempty V) {x y : V} (hxy : E x y) : ¬ E y x := by
  intro hyx
  obtain ⟨s, hs⟩ := ax_pair hM hNE x y
  obtain ⟨z, hzs, hmin⟩ := ax_foundation hM hNE ⟨x, (hs x).mpr (Or.inl rfl)⟩
  rcases (hs z).mp hzs with rfl | rfl
  · exact hmin y hyx ((hs y).mpr (Or.inr rfl))
  · exact hmin x hxy ((hs x).mpr (Or.inl rfl))

private theorem omega_induction (hM : Model E) (hNE : Nonempty V) (n : Nat) (body : Formula)
    (hB : Bound body (n + 1)) (env : Nat → V)
    (hbase : ∀ z, Empty E z → eval E body (pushValue env z))
    (hstep : ∀ x y, NatObject E x → Succ E x y →
      eval E body (pushValue env x) → eval E body (pushValue env y)) :
    ∀ x, NatObject E x → eval E body (pushValue env x) := by
  intro x ⟨w, hw, hxw⟩
  obtain ⟨sub, hsub⟩ := ax_sep hM hNE n body hB env w
  have hind : Inductive E sub := by
    constructor
    · obtain ⟨z, hz, hzw⟩ := hw.1.1; exact ⟨z, hz, (hsub z).mpr ⟨hzw, hbase z hz⟩⟩
    · intro u husub
      have ⟨huw, hubody⟩ := (hsub u).mp husub
      obtain ⟨y, huy, hyw⟩ := hw.1.2 u huw
      exact ⟨y, huy, (hsub y).mpr ⟨hyw, hstep u y ⟨w, hw, huw⟩ huy hubody⟩⟩
  exact ((hsub x).mp (hw.2 sub hind x hxw)).2

/-! ### Base Syntactic Formula Builders -/

private def fNot (p : Formula) : Formula := .imp p .bot
private def fIff (p q : Formula) : Formula := .and (.imp p q) (.imp q p)
private def fEmpty (a : Nat) : Formula := .all (fNot (.mem 0 (a + 1)))
private def fSucc (a b : Nat) : Formula :=
  .all (fIff (.mem 0 (b + 1)) (.or (.mem 0 (a + 1)) (.eq 0 (a + 1))))
private def fPair (a b p : Nat) : Formula :=
  .all (fIff (.mem 0 (p + 1)) (.or (.eq 0 (a + 1)) (.eq 0 (b + 1))))
private def fOrderedPair (a b p : Nat) : Formula :=
  .ex (.ex (.and (fPair (a + 2) (a + 2) 1) (.and (fPair (a + 2) (b + 2) 0) (fPair 1 0 (p + 2)))))
private def fAt (f x y : Nat) : Formula :=
  .ex (.and (.mem 0 (f + 1)) (fOrderedPair (x + 1) (y + 1) 0))
private def fFunctionOn (f d : Nat) : Formula :=
  .and
    (.all (.imp (.mem 0 (d + 1)) (.ex (.and (fAt (f + 2) 1 0) (.all (.imp (fAt (f + 3) 2 0) (.eq 0 1)))))))
    (.all (.imp (.mem 0 (f + 1)) (.ex (.ex (.and (.mem 1 (d + 3)) (fOrderedPair 1 0 2))))))
private def fInductive (a : Nat) : Formula :=
  .and (.ex (.and (fEmpty 0) (.mem 0 (a + 1))))
    (.all (.imp (.mem 0 (a + 1)) (.ex (.and (fSucc 1 0) (.mem 0 (a + 2))))))
private def fOmega (w : Nat) : Formula :=
  .and (fInductive w) (.all (.imp (fInductive 0) (.all (.imp (.mem 0 (w + 2)) (.mem 0 1)))))
private def fNatObject (x : Nat) : Formula := .ex (.and (fOmega 0) (.mem (x + 1) 0))
private def fNumeral : Nat → Nat → Formula
  | 0, x => fEmpty x
  | k + 1, x => .ex (.and (fNumeral k 0) (fSucc 0 (x + 1)))
private def fAdd (a b c : Nat) : Formula :=
  .and (fNatObject a) (.and (fNatObject b) (.and (fNatObject c)
    (.ex (.ex (.ex (.and (fEmpty 2) (.and (fSucc (b + 3) 1) (.and (fFunctionOn 0 1)
      (.and (fAt 0 2 (a + 3)) (.and (fAt 0 (b + 3) (c + 3))
        (.and (.all (.all (.imp (.mem 1 3) (.imp (fAt 2 1 0) (fNatObject 0)))))
          (.all (.imp (.mem 0 (b + 4))
            (.ex (.ex (.ex (.and (fSucc 3 2) (.and (fAt 4 3 1) (.and (fAt 4 2 0) (fSucc 1 0))))))))))))))))))))
private def fMul (a b c : Nat) : Formula :=
  .and (fNatObject a) (.and (fNatObject b) (.and (fNatObject c)
    (.ex (.ex (.ex (.and (fEmpty 2) (.and (fSucc (b + 3) 1) (.and (fFunctionOn 0 1)
      (.and (fAt 0 2 2) (.and (fAt 0 (b + 3) (c + 3))
        (.and (.all (.all (.imp (.mem 1 3) (.imp (fAt 2 1 0) (fNatObject 0)))))
          (.all (.imp (.mem 0 (b + 4))
            (.ex (.ex (.ex (.and (fSucc 3 2) (.and (fAt 4 3 1) (.and (fAt 4 2 0) (fAdd 1 (a + 7) 0))))))))))))))))))))
private def fCantor (a b z : Nat) : Formula :=
  .and (fNatObject a) (.and (fNatObject b) (.and (fNatObject z)
    (.ex (.ex (.ex (.ex (.ex (.ex (.ex
      (.and (fNumeral 2 6) (.and (fAdd (a + 7) (b + 7) 5) (.and (fSucc 5 4)
        (.and (fMul 5 4 3) (.and (fMul 6 (b + 7) 2) (.and (fMul 6 (z + 7) 1)
          (.and (fAdd 3 2 0) (.eq 1 0)))))))))))))))))

private theorem bound_fNot {p : Formula} {n : Nat} (hp : Bound p n) : Bound (fNot p) n := ⟨hp, trivial⟩
private theorem bound_fIff {p q : Formula} {n : Nat} (hp : Bound p n) (hq : Bound q n) : Bound (fIff p q) n := ⟨⟨hp, hq⟩, ⟨hq, hp⟩⟩
private theorem bound_fEmpty {a n : Nat} (ha : a < n) : Bound (fEmpty a) n := ⟨⟨by omega, by omega⟩, trivial⟩
private theorem bound_fSucc {a b n : Nat} (ha : a < n) (hb : b < n) : Bound (fSucc a b) n :=
  bound_fIff ⟨by omega, by omega⟩ ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
private theorem bound_fPair {a b p n : Nat} (ha : a < n) (hb : b < n) (hp : p < n) : Bound (fPair a b p) n :=
  bound_fIff ⟨by omega, by omega⟩ ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
private theorem bound_fOrderedPair {a b p n : Nat} (ha : a < n) (hb : b < n) (hp : p < n) : Bound (fOrderedPair a b p) n :=
  ⟨bound_fPair (by omega) (by omega) (by omega), ⟨bound_fPair (by omega) (by omega) (by omega), bound_fPair (by omega) (by omega) (by omega)⟩⟩
private theorem bound_fAt {f x y n : Nat} (hf : f < n) (hx : x < n) (hy : y < n) : Bound (fAt f x y) n :=
  ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega)⟩
private theorem bound_fFunctionOn {f d n : Nat} (hf : f < n) (hd : d < n) : Bound (fFunctionOn f d) n :=
  ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩,
   ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega)⟩⟩⟩
private theorem bound_fInductive {a n : Nat} (ha : a < n) : Bound (fInductive a) n :=
  ⟨⟨bound_fEmpty (by omega), ⟨by omega, by omega⟩⟩, ⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩
private theorem bound_fOmega {w n : Nat} (hw : w < n) : Bound (fOmega w) n :=
  ⟨bound_fInductive hw, ⟨bound_fInductive (by omega), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩⟩
private theorem bound_fNatObject {x n : Nat} (hx : x < n) : Bound (fNatObject x) n :=
  ⟨bound_fOmega (by omega), ⟨by omega, by omega⟩⟩
private theorem bound_fNumeral : ∀ {k x n : Nat}, x < n → Bound (fNumeral k x) n
  | 0, _, _, hx => bound_fEmpty hx
  | k + 1, _, _, hx => ⟨bound_fNumeral (k := k) (by omega), bound_fSucc (by omega) (by omega)⟩
private theorem bound_fAdd {a b c n : Nat} (ha : a < n) (hb : b < n) (hc : c < n) : Bound (fAdd a b c) n :=
  ⟨bound_fNatObject ha, ⟨bound_fNatObject hb, ⟨bound_fNatObject hc,
    ⟨bound_fEmpty (by omega), ⟨bound_fSucc (by omega) (by omega), ⟨bound_fFunctionOn (by omega) (by omega),
      ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
        ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
         ⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
          ⟨bound_fAt (by omega) (by omega) (by omega), bound_fSucc (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem bound_fMul {a b c n : Nat} (ha : a < n) (hb : b < n) (hc : c < n) : Bound (fMul a b c) n :=
  ⟨bound_fNatObject ha, ⟨bound_fNatObject hb, ⟨bound_fNatObject hc,
    ⟨bound_fEmpty (by omega), ⟨bound_fSucc (by omega) (by omega), ⟨bound_fFunctionOn (by omega) (by omega),
      ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
        ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
         ⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
          ⟨bound_fAt (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem bound_fCantor {a b z n : Nat} (ha : a < n) (hb : b < n) (hz : z < n) : Bound (fCantor a b z) n :=
  ⟨bound_fNatObject ha, ⟨bound_fNatObject hb, ⟨bound_fNatObject hz,
    ⟨bound_fNumeral (by omega), ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨bound_fSucc (by omega) (by omega),
      ⟨bound_fMul (by omega) (by omega) (by omega), ⟨bound_fMul (by omega) (by omega) (by omega),
        ⟨bound_fMul (by omega) (by omega) (by omega), ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem eval_fIff (p q : Formula) (s : Nat → V) : eval E (fIff p q) s ↔ (eval E p s ↔ eval E q s) :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.mp, h.mpr⟩⟩
private theorem eval_fEmpty (a : Nat) (s : Nat → V) : eval E (fEmpty a) s ↔ Empty E (s a) := Iff.rfl
private theorem eval_fSucc (a b : Nat) (s : Nat → V) : eval E (fSucc a b) s ↔ Succ E (s a) (s b) :=
  ⟨fun h x => (eval_fIff _ _ _).mp (h x), fun h x => (eval_fIff _ _ _).mpr (h x)⟩
private theorem eval_fPair (a b p : Nat) (s : Nat → V) : eval E (fPair a b p) s ↔ Pair E (s a) (s b) (s p) :=
  ⟨fun h x => (eval_fIff _ _ _).mp (h x), fun h x => (eval_fIff _ _ _).mpr (h x)⟩
private theorem eval_fOrderedPair (a b p : Nat) (s : Nat → V) : eval E (fOrderedPair a b p) s ↔ OrderedPair E (s a) (s b) (s p) := by
  constructor
  · rintro ⟨aa, ab, h1, h2, h3⟩; exact ⟨aa, ab, (eval_fPair _ _ _ _).mp h1, (eval_fPair _ _ _ _).mp h2, (eval_fPair _ _ _ _).mp h3⟩
  · rintro ⟨aa, ab, h1, h2, h3⟩; exact ⟨aa, ab, (eval_fPair _ _ _ _).mpr h1, (eval_fPair _ _ _ _).mpr h2, (eval_fPair _ _ _ _).mpr h3⟩
private theorem eval_fAt (f x y : Nat) (s : Nat → V) : eval E (fAt f x y) s ↔ At E (s f) (s x) (s y) :=
  ⟨fun ⟨p, h1, h2⟩ => ⟨p, h1, (eval_fOrderedPair _ _ _ _).mp h2⟩, fun ⟨p, h1, h2⟩ => ⟨p, h1, (eval_fOrderedPair _ _ _ _).mpr h2⟩⟩
private theorem eval_fFunctionOn (f d : Nat) (s : Nat → V) : eval E (fFunctionOn f d) s ↔ FunctionOn E (s f) (s d) := by
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨fun x hx => ?_, fun p hp => ?_⟩
    · obtain ⟨y, hy, hu⟩ := h1 x hx; exact ⟨y, (eval_fAt _ _ _ _).mp hy, fun z hz => hu z ((eval_fAt _ _ _ _).mpr hz)⟩
    · obtain ⟨x, y, hx, hp'⟩ := h2 p hp; exact ⟨x, y, hx, (eval_fOrderedPair _ _ _ _).mp hp'⟩
  · rintro ⟨h1, h2⟩; refine ⟨fun x hx => ?_, fun p hp => ?_⟩
    · obtain ⟨y, hy, hu⟩ := h1 x hx; exact ⟨y, (eval_fAt _ _ _ _).mpr hy, fun z hz => hu z ((eval_fAt _ _ _ _).mp hz)⟩
    · obtain ⟨x, y, hx, hp'⟩ := h2 p hp; exact ⟨x, y, hx, (eval_fOrderedPair _ _ _ _).mpr hp'⟩
private theorem eval_fInductive (a : Nat) (s : Nat → V) : eval E (fInductive a) s ↔ Inductive E (s a) := by
  constructor
  · rintro ⟨⟨z, hz, hza⟩, hs⟩; exact ⟨⟨z, hz, hza⟩, fun x hx => let ⟨y, h1, h2⟩ := hs x hx; ⟨y, (eval_fSucc _ _ _).mp h1, h2⟩⟩
  · rintro ⟨⟨z, hz, hza⟩, hs⟩; exact ⟨⟨z, hz, hza⟩, fun x hx => let ⟨y, h1, h2⟩ := hs x hx; ⟨y, (eval_fSucc _ _ _).mpr h1, h2⟩⟩
private theorem eval_fOmega (w : Nat) (s : Nat → V) : eval E (fOmega w) s ↔ Omega E (s w) :=
  ⟨fun ⟨h1, h2⟩ => ⟨(eval_fInductive _ _).mp h1, fun a ha x hx => h2 a ((eval_fInductive _ _).mpr ha) x hx⟩,
   fun ⟨h1, h2⟩ => ⟨(eval_fInductive _ _).mpr h1, fun a ha x hx => h2 a ((eval_fInductive _ _).mp ha) x hx⟩⟩
private theorem eval_fNatObject (x : Nat) (s : Nat → V) : eval E (fNatObject x) s ↔ NatObject E (s x) :=
  ⟨fun ⟨w, h1, h2⟩ => ⟨w, (eval_fOmega _ _).mp h1, h2⟩, fun ⟨w, h1, h2⟩ => ⟨w, (eval_fOmega _ _).mpr h1, h2⟩⟩
private theorem eval_fNumeral : ∀ (k x : Nat) (s : Nat → V), eval E (fNumeral k x) s ↔ Numeral E k (s x)
  | 0, _, _ => Iff.rfl
  | k + 1, _, _ =>
    ⟨fun ⟨y, h1, h2⟩ => ⟨y, (eval_fNumeral k 0 _).mp h1, (eval_fSucc _ _ _).mp h2⟩,
     fun ⟨y, h1, h2⟩ => ⟨y, (eval_fNumeral k 0 _).mpr h1, (eval_fSucc _ _ _).mpr h2⟩⟩
private theorem eval_fAdd (a b c : Nat) (s : Nat → V) : eval E (fAdd a b c) s ↔ Add E (s a) (s b) (s c) := by
  constructor
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mp ha, (eval_fNatObject _ _).mp hb, (eval_fNatObject _ _).mp hc,
      z, dom, f, hz, (eval_fSucc _ _ _).mp hdom, (eval_fFunctionOn _ _ _).mp hfun,
      (eval_fAt _ _ _ _).mp hf0, (eval_fAt _ _ _ _).mp hfb,
      fun i x hi hix => (eval_fNatObject _ _).mp (hnat i x hi ((eval_fAt _ _ _ _).mpr hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
    exact ⟨j, x, y, (eval_fSucc _ _ _).mp h1, (eval_fAt _ _ _ _).mp h2, (eval_fAt _ _ _ _).mp h3, (eval_fSucc _ _ _).mp h4⟩
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mpr ha, (eval_fNatObject _ _).mpr hb, (eval_fNatObject _ _).mpr hc,
      z, dom, f, hz, (eval_fSucc _ _ _).mpr hdom, (eval_fFunctionOn _ _ _).mpr hfun,
      (eval_fAt _ _ _ _).mpr hf0, (eval_fAt _ _ _ _).mpr hfb,
      fun i x hi hix => (eval_fNatObject _ _).mpr (hnat i x hi ((eval_fAt _ _ _ _).mp hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
    exact ⟨j, x, y, (eval_fSucc _ _ _).mpr h1, (eval_fAt _ _ _ _).mpr h2, (eval_fAt _ _ _ _).mpr h3, (eval_fSucc _ _ _).mpr h4⟩
private theorem eval_fMul (a b c : Nat) (s : Nat → V) : eval E (fMul a b c) s ↔ Mul E (s a) (s b) (s c) := by
  constructor
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mp ha, (eval_fNatObject _ _).mp hb, (eval_fNatObject _ _).mp hc,
      z, dom, f, hz, (eval_fSucc _ _ _).mp hdom, (eval_fFunctionOn _ _ _).mp hfun,
      (eval_fAt _ _ _ _).mp hf0, (eval_fAt _ _ _ _).mp hfb,
      fun i x hi hix => (eval_fNatObject _ _).mp (hnat i x hi ((eval_fAt _ _ _ _).mpr hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
    exact ⟨j, x, y, (eval_fSucc _ _ _).mp h1, (eval_fAt _ _ _ _).mp h2, (eval_fAt _ _ _ _).mp h3, (eval_fAdd _ _ _ _).mp h4⟩
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mpr ha, (eval_fNatObject _ _).mpr hb, (eval_fNatObject _ _).mpr hc,
      z, dom, f, hz, (eval_fSucc _ _ _).mpr hdom, (eval_fFunctionOn _ _ _).mpr hfun,
      (eval_fAt _ _ _ _).mpr hf0, (eval_fAt _ _ _ _).mpr hfb,
      fun i x hi hix => (eval_fNatObject _ _).mpr (hnat i x hi ((eval_fAt _ _ _ _).mp hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
    exact ⟨j, x, y, (eval_fSucc _ _ _).mpr h1, (eval_fAt _ _ _ _).mpr h2, (eval_fAt _ _ _ _).mpr h3, (eval_fAdd _ _ _ _).mpr h4⟩
private theorem eval_fCantor (a b z : Nat) (s : Nat → V) : eval E (fCantor a b z) s ↔ Cantor E (s a) (s b) (s z) := by
  constructor
  · rintro ⟨ha, hb, hz, two, sum, next, prod, tb, tz, tot, h2, hadd, hs, hm1, hm2, hm3, ha2, heq⟩
    exact ⟨(eval_fNatObject _ _).mp ha, (eval_fNatObject _ _).mp hb, (eval_fNatObject _ _).mp hz,
      two, sum, next, prod, tb, tz, tot, (eval_fNumeral 2 _ _).mp h2, (eval_fAdd _ _ _ _).mp hadd,
      (eval_fSucc _ _ _).mp hs, (eval_fMul _ _ _ _).mp hm1, (eval_fMul _ _ _ _).mp hm2,
      (eval_fMul _ _ _ _).mp hm3, (eval_fAdd _ _ _ _).mp ha2, heq⟩
  · rintro ⟨ha, hb, hz, two, sum, next, prod, tb, tz, tot, h2, hadd, hs, hm1, hm2, hm3, ha2, heq⟩
    exact ⟨(eval_fNatObject _ _).mpr ha, (eval_fNatObject _ _).mpr hb, (eval_fNatObject _ _).mpr hz,
      two, sum, next, prod, tb, tz, tot, (eval_fNumeral 2 _ _).mpr h2, (eval_fAdd _ _ _ _).mpr hadd,
      (eval_fSucc _ _ _).mpr hs, (eval_fMul _ _ _ _).mpr hm1, (eval_fMul _ _ _ _).mpr hm2,
      (eval_fMul _ _ _ _).mpr hm3, (eval_fAdd _ _ _ _).mpr ha2, heq⟩

/-! ### Order, Arithmetic, Cantor Pairing & Unpairing on ω -/

private theorem nat_zero (hM : Model E) (hNE : Nonempty V) {z : V} (hz : Empty E z) : NatObject E z := by
  obtain ⟨w, hw⟩ := ax_omega hM hNE; obtain ⟨z', hz', hz'w⟩ := hw.1.1
  rw [empty_unique hM hNE hz hz']; exact ⟨w, hw, hz'w⟩

private theorem nat_succ (hM : Model E) (hNE : Nonempty V) {x y : V}
    (hx : NatObject E x) (hxy : Succ E x y) : NatObject E y := by
  rcases hx with ⟨w, hw, hxw⟩; obtain ⟨y', huy', hy'w⟩ := hw.1.2 x hxw
  rw [succ_unique hM hNE hxy huy']; exact ⟨w, hw, hy'w⟩

private theorem nat_mem_is_nat (hM : Model E) (hNE : Nonempty V) :
    ∀ x, NatObject E x → ∀ y, E y x → NatObject E y := by
  let body : Formula := .all (.imp (.mem 0 1) (fNatObject 0))
  have h := omega_induction hM hNE 0 body ⟨⟨by omega, by omega⟩, bound_fNatObject (by omega)⟩
    (fun _ => Classical.choice hNE)
    (fun z hz y hy => False.elim (hz y hy))
    (fun x _ hx hxy ih u hu => by
      rcases (hxy u).mp hu with hux | rfl
      · exact (eval_fNatObject _ _).mpr ((eval_fNatObject _ _).mp (ih u hux))
      · exact (eval_fNatObject _ _).mpr hx)
  intro x hx y hy; exact (eval_fNatObject _ _).mp (h x hx y hy)

private theorem nat_lt_trans (hM : Model E) (hNE : Nonempty V) :
    ∀ z, NatObject E z → ∀ x y, E x y → E y z → E x z := by
  let body : Formula := .all (.all (.imp (.mem 1 0) (.imp (.mem 0 2) (.mem 1 2))))
  exact omega_induction hM hNE 0 body
    ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩
    (fun _ => Classical.choice hNE)
    (fun z hz _ y _ hyz => False.elim (hz y hyz))
    (fun _ _ _ hzz' ih x y hxy hyz' => by
      rcases (hzz' y).mp hyz' with hyz | rfl
      · exact (hzz' x).mpr (Or.inl (ih x y hxy hyz))
      · exact (hzz' x).mpr (Or.inl hxy))

private theorem nat_zero_le (hM : Model E) (hNE : Nonempty V) {z : V} (hz : Empty E z) :
    ∀ x, NatObject E x → z = x ∨ E z x := by
  let body : Formula := .or (.eq 1 0) (.mem 1 0)
  exact omega_induction hM hNE 1 body ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ (fun _ => z)
    (fun z' hz' => Or.inl (empty_unique hM hNE hz hz'))
    (fun _ _ _ hxy ih => by
      dsimp only [body, eval, pushValue] at ih ⊢
      rcases ih with hzx | hzx
      · exact Or.inr ((hxy z).mpr (Or.inr hzx))
      · exact Or.inr ((hxy z).mpr (Or.inl hzx)))

private theorem nat_succ_le_iff (hM : Model E) (hNE : Nonempty V) {x x' : V}
    (_hx : NatObject E x) (hxx' : Succ E x x') :
    ∀ y, NatObject E y → (E x y ↔ x' = y ∨ E x' y) := by
  let body : Formula := fIff (.mem 1 0) (.or (.eq 2 0) (.mem 2 0))
  let env : Nat → V := fun i => if i = 0 then x else x'
  have h := omega_induction hM hNE 2 body
    (bound_fIff ⟨by omega, by omega⟩ ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩) env
    (fun z hz => (eval_fIff _ _ _).mpr ⟨fun hxz => False.elim (hz x hxz), fun h => by
      dsimp only [eval, pushValue, env] at h
      rcases h with heq | hx'z
      · exact False.elim (hz x (heq ▸ (hxx' x).mpr (Or.inr rfl)))
      · exact False.elim (hz x' hx'z)⟩)
    (fun _ _ _ hyy' ih => by
      have ih' := (eval_fIff _ _ _).mp ih
      apply (eval_fIff _ _ _).mpr
      dsimp only [eval, pushValue, env] at ih' ⊢
      constructor
      · intro hxy'
        rcases (hyy' x).mp hxy' with hxy | hxy
        · rcases ih'.mp hxy with heq | hx'y
          · exact Or.inr ((hyy' x').mpr (Or.inr heq))
          · exact Or.inr ((hyy' x').mpr (Or.inl hx'y))
        · exact Or.inl (succ_unique hM hNE hxx' (hxy ▸ hyy'))
      · rintro (heq | hx'y')
        · exact heq ▸ (hxx' x).mpr (Or.inr rfl)
        · rcases (hyy' x').mp hx'y' with hx'y | heq
          · exact (hyy' x).mpr (Or.inl (ih'.mpr (Or.inr hx'y)))
          · exact (hyy' x).mpr (Or.inl (ih'.mpr (Or.inl heq))))
  intro y hy; exact (eval_fIff _ _ _).mp (h y hy)

private theorem nat_trichotomy (hM : Model E) (hNE : Nonempty V) :
    ∀ x, NatObject E x → ∀ y, NatObject E y → E x y ∨ x = y ∨ E y x := by
  intro x hx
  let body : Formula := .or (.mem 1 0) (.or (.eq 1 0) (.mem 0 1))
  exact omega_induction hM hNE 1 body ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩ (fun _ => x)
    (fun z hz => by
      dsimp only [body, eval, pushValue]
      rcases nat_zero_le hM hNE hz x hx with hzx | hzx
      · exact Or.inr (Or.inl hzx.symm)
      · exact Or.inr (Or.inr hzx))
    (fun y _ hy hyy' ih => by
      dsimp only [body, eval, pushValue] at ih ⊢
      rcases ih with hxy | hxy | hyx
      · exact Or.inl ((hyy' x).mpr (Or.inl hxy))
      · exact Or.inl ((hyy' x).mpr (Or.inr hxy))
      · rcases (nat_succ_le_iff hM hNE hy hyy' x hx).mp hyx with hy'x | hy'x
        · exact Or.inr (Or.inl hy'x.symm)
        · exact Or.inr (Or.inr hy'x))

private theorem nat_cases (hM : Model E) (hNE : Nonempty V) :
    ∀ x, NatObject E x → Empty E x ∨ ∃ p, NatObject E p ∧ Succ E p x := by
  let body : Formula := .or (fEmpty 0) (.ex (.and (fNatObject 0) (fSucc 0 1)))
  have h := omega_induction hM hNE 0 body
    ⟨bound_fEmpty (by omega), ⟨bound_fNatObject (by omega), bound_fSucc (by omega) (by omega)⟩⟩
    (fun _ => Classical.choice hNE)
    (fun _ hz => Or.inl hz)
    (fun x _ hx hxy _ => Or.inr ⟨x, (eval_fNatObject _ _).mpr hx, (eval_fSucc _ _ _).mpr hxy⟩)
  intro x hx
  rcases h x hx with hz | ⟨p, hp, hpx⟩
  · exact Or.inl hz
  · exact Or.inr ⟨p, (eval_fNatObject _ _).mp hp, (eval_fSucc _ _ _).mp hpx⟩

private theorem functionOn_singleton (hM : Model E) (hNE : Nonempty V) {z dom a : V}
    (hz : Empty E z) (hdom : Succ E z dom) :
    ∃ f, FunctionOn E f dom ∧ At E f z a ∧ ∀ x y, At E f x y → x = z ∧ y = a := by
  obtain ⟨p, hp⟩ := exists_orderedPair hM hNE z a
  obtain ⟨f, hf⟩ := ax_pair hM hNE p p
  have hAt : ∀ x y, At E f x y ↔ x = z ∧ y = a := fun x y =>
    ⟨fun ⟨q, hqf, hq⟩ => by rcases (hf q).mp hqf with rfl | rfl <;> exact orderedPair_inj hq hp,
     fun ⟨rfl, rfl⟩ => ⟨p, (hf p).mpr (Or.inl rfl), hp⟩⟩
  refine ⟨f, ⟨fun x hx => ?_, fun q hq => ?_⟩, (hAt z a).mpr ⟨rfl, rfl⟩, fun x y h => (hAt x y).mp h⟩
  · rcases (hdom x).mp hx with hxz | rfl
    · exact False.elim (hz x hxz)
    · exact ⟨a, (hAt x a).mpr ⟨rfl, rfl⟩, fun w hw => ((hAt x w).mp hw).2⟩
  · rcases (hf q).mp hq with rfl | rfl <;> exact ⟨z, a, (hdom z).mpr (Or.inr rfl), hp⟩

private theorem functionOn_extend (hM : Model E) (hNE : Nonempty V) {f dom dom' y : V}
    (hfun : FunctionOn E f dom) (hdom' : Succ E dom dom') :
    ∃ f', FunctionOn E f' dom' ∧ (∀ x w, At E f' x w ↔ At E f x w ∨ (x = dom ∧ w = y)) := by
  obtain ⟨p, hp⟩ := exists_orderedPair hM hNE dom y
  obtain ⟨f', hf'⟩ := exists_insert hM hNE f p
  have hAt : ∀ x w, At E f' x w ↔ At E f x w ∨ (x = dom ∧ w = y) := fun x w =>
    ⟨fun ⟨q, hqf', hq⟩ => by
      rcases (hf' q).mp hqf' with hqf | rfl
      · exact Or.inl ⟨q, hqf, hq⟩
      · exact Or.inr (orderedPair_inj hq hp),
     fun h => h.elim (fun ⟨q, hqf, hq⟩ => ⟨q, (hf' q).mpr (Or.inl hqf), hq⟩)
       (fun ⟨rfl, rfl⟩ => ⟨p, (hf' p).mpr (Or.inr rfl), hp⟩)⟩
  refine ⟨f', ⟨fun x hx => ?_, fun q hq => ?_⟩, hAt⟩
  · rcases (hdom' x).mp hx with hxdom | rfl
    · obtain ⟨w, hfw, huniq⟩ := hfun.1 x hxdom
      refine ⟨w, (hAt x w).mpr (Or.inl hfw), fun z hz => ?_⟩
      rcases (hAt x z).mp hz with hfz | ⟨hxd, _⟩
      · exact huniq z hfz
      · exact False.elim (mem_irrefl hM hNE x (hxd ▸ hxdom))
    · refine ⟨y, (hAt x y).mpr (Or.inr ⟨rfl, rfl⟩), fun z hz => ?_⟩
      rcases (hAt x z).mp hz with ⟨q, hqf, hq⟩ | ⟨_, hzy⟩
      · obtain ⟨u, _, hudom, huv⟩ := hfun.2 q hqf
        exact False.elim (mem_irrefl hM hNE x ((orderedPair_inj hq huv).1 ▸ hudom))
      · exact hzy
  · rcases (hf' q).mp hq with hqf | rfl
    · obtain ⟨u, v, hudom, huv⟩ := hfun.2 q hqf; exact ⟨u, v, (hdom' u).mpr (Or.inl hudom), huv⟩
    · exact ⟨dom, y, (hdom' dom).mpr (Or.inr rfl), hp⟩

private theorem functionOn_at_unique {f dom x y₁ y₂ : V} (hfun : FunctionOn E f dom)
    (hx : E x dom) (h1 : At E f x y₁) (h2 : At E f x y₂) : y₁ = y₂ := by
  obtain ⟨y, _, hu⟩ := hfun.1 x hx
  exact (hu y₁ h1).trans (hu y₂ h2).symm

private theorem add_zero (hM : Model E) (hNE : Nonempty V) {a z : V}
    (ha : NatObject E a) (hz : Empty E z) : Add E a z a := by
  have hzNat := nat_zero hM hNE hz
  obtain ⟨dom, hdom⟩ := exists_succ hM hNE z
  obtain ⟨f, hfun, hfza, hfat⟩ := functionOn_singleton hM hNE hz hdom
  exact ⟨ha, hzNat, ha, z, dom, f, hz, hdom, hfun, hfza, hfza,
    fun i x _ h => (hfat i x h).2 ▸ ha, fun i hi => False.elim (hz i hi)⟩

private theorem add_succ (hM : Model E) (hNE : Nonempty V) {a b b' c c' : V}
    (habc : Add E a b c) (hbb' : Succ E b b') (hcc' : Succ E c c') : Add E a b' c' := by
  rcases habc with ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
  have hb' := nat_succ hM hNE hb hbb'; have hc' := nat_succ hM hNE hc hcc'
  have := succ_unique hM hNE hdom hbb'; subst this
  obtain ⟨dom', hdom'⟩ := exists_succ hM hNE dom
  obtain ⟨f', hfun', hf'at⟩ := functionOn_extend hM hNE hfun hdom'
  refine ⟨ha, hb', hc', z, dom', f', hz, hdom', hfun',
    (hf'at z a).mpr (Or.inl hf0), (hf'at dom c').mpr (Or.inr ⟨rfl, rfl⟩), fun i x _ hfix => ?_, fun i hi => ?_⟩
  · rcases (hf'at i x).mp hfix with ⟨q, hqf, hq⟩ | ⟨_, rfl⟩
    · obtain ⟨u, v, hud, huv⟩ := hfun.2 q hqf; rw [(orderedPair_inj hq huv).2]; exact hnat u v hud ⟨q, hqf, huv⟩
    · exact hc'
  · rcases (hbb' i).mp hi with hib | rfl
    · obtain ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hib
      exact ⟨j, x, y, h1, (hf'at i x).mpr (Or.inl h2), (hf'at j y).mpr (Or.inl h3), h4⟩
    · exact ⟨dom, c, c', hbb', (hf'at i c).mpr (Or.inl hfb), (hf'at dom c').mpr (Or.inr ⟨rfl, rfl⟩), hcc'⟩

private theorem add_exists (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → ∃ c, Add E a b c := by
  let body : Formula := .ex (fAdd 2 1 0)
  have h := omega_induction hM hNE 1 body (bound_fAdd (by omega) (by omega) (by omega)) (fun _ => a)
    (fun z hz => ⟨a, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE ha hz)⟩)
    (fun b _ _ hbb' ⟨c, hc⟩ => by
      have habc : Add E a b c := (eval_fAdd _ _ _ _).mp hc
      obtain ⟨c', hcc'⟩ := exists_succ hM hNE c
      exact ⟨c', (eval_fAdd _ _ _ _).mpr (add_succ hM hNE habc hbb' hcc')⟩)
  intro b hb; obtain ⟨c, hc⟩ := h b hb; exact ⟨c, (eval_fAdd _ _ _ _).mp hc⟩

private theorem add_unique (hM : Model E) (hNE : Nonempty V) {a b c₁ c₂ : V}
    (h1 : Add E a b c₁) (h2 : Add E a b c₂) : c₁ = c₂ := by
  rcases h1 with ⟨_, hb, _, z1, dom1, f1, hz1, hdom1, hfun1, hf10, hf1b, _, hstep1⟩
  rcases h2 with ⟨_, _, _, z2, dom2, f2, hz2, hdom2, hfun2, hf20, hf2b, _, hstep2⟩
  have := empty_unique hM hNE hz1 hz2; subst this
  have := succ_unique hM hNE hdom1 hdom2; subst this
  let body : Formula := .imp (.mem 0 1) (.all (.all (.imp (fAt 4 2 1) (.imp (fAt 5 2 0) (.eq 1 0)))))
  let env : Nat → V := fun k => if k = 0 then dom1 else if k = 1 then f1 else f2
  have hAgree := omega_induction hM hNE 3 body
    ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩ env
    (fun z hz _ x y hx hy => by
      have := empty_unique hM hNE hz hz1; subst this
      have hzd : E z dom1 := (hdom1 z).mpr (by rcases nat_zero_le hM hNE hz b hb with rfl | h; exact Or.inr rfl; exact Or.inl h)
      exact (functionOn_at_unique hfun1 hzd ((eval_fAt _ _ _ _).mp hx) hf10).trans
        (functionOn_at_unique hfun2 hzd ((eval_fAt _ _ _ _).mp hy) hf20).symm)
    (fun i j _ hij ih hjd x y hx hy => by
      have hib : E i b := by
        rcases (hdom1 j).mp hjd with hjb | rfl
        · exact nat_lt_trans hM hNE b hb i j ((hij i).mpr (Or.inr rfl)) hjb
        · exact (hij i).mpr (Or.inr rfl)
      obtain ⟨j1, x1, y1, hij1, hf1i, hf1j, hxy1⟩ := hstep1 i hib
      obtain ⟨j2, x2, y2, hij2, hf2i, hf2j, hxy2⟩ := hstep2 i hib
      have := succ_unique hM hNE hij1 hij; subst this
      have := succ_unique hM hNE hij2 hij; subst this
      have hid : E i dom1 := (hdom1 i).mpr (Or.inl hib)
      have hx12 : x1 = x2 := ih hid x1 x2 ((eval_fAt _ _ _ _).mpr hf1i) ((eval_fAt _ _ _ _).mpr hf2i)
      subst hx12
      have hy12 : y1 = y2 := succ_unique hM hNE hxy1 hxy2
      exact (functionOn_at_unique hfun1 hjd ((eval_fAt _ _ _ _).mp hx) hf1j).trans
        (hy12.trans (functionOn_at_unique hfun2 hjd ((eval_fAt _ _ _ _).mp hy) hf2j).symm))
  exact hAgree b hb ((hdom1 b).mpr (Or.inr rfl)) c₁ c₂ ((eval_fAt _ _ _ _).mpr hf1b) ((eval_fAt _ _ _ _).mpr hf2b)

private theorem mul_zero (hM : Model E) (hNE : Nonempty V) {a z : V}
    (ha : NatObject E a) (hz : Empty E z) : Mul E a z z := by
  have hzNat := nat_zero hM hNE hz
  obtain ⟨dom, hdom⟩ := exists_succ hM hNE z
  obtain ⟨f, hfun, hfzz, hfat⟩ := functionOn_singleton hM hNE hz hdom
  exact ⟨ha, hzNat, hzNat, z, dom, f, hz, hdom, hfun, hfzz, hfzz,
    fun i x _ h => (hfat i x h).2 ▸ hzNat, fun i hi => False.elim (hz i hi)⟩

private theorem mul_succ (hM : Model E) (hNE : Nonempty V) {a b b' c c' : V}
    (habc : Mul E a b c) (hbb' : Succ E b b') (hadd : Add E c a c') : Mul E a b' c' := by
  rcases habc with ⟨ha, hb, _, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
  have hb' := nat_succ hM hNE hb hbb'; have hc' := hadd.2.2.1
  have := succ_unique hM hNE hdom hbb'; subst this
  obtain ⟨dom', hdom'⟩ := exists_succ hM hNE dom
  obtain ⟨f', hfun', hf'at⟩ := functionOn_extend hM hNE hfun hdom'
  refine ⟨ha, hb', hc', z, dom', f', hz, hdom', hfun',
    (hf'at z z).mpr (Or.inl hf0), (hf'at dom c').mpr (Or.inr ⟨rfl, rfl⟩), fun i x _ hfix => ?_, fun i hi => ?_⟩
  · rcases (hf'at i x).mp hfix with ⟨q, hqf, hq⟩ | ⟨_, rfl⟩
    · obtain ⟨u, v, hud, huv⟩ := hfun.2 q hqf; rw [(orderedPair_inj hq huv).2]; exact hnat u v hud ⟨q, hqf, huv⟩
    · exact hc'
  · rcases (hbb' i).mp hi with hib | rfl
    · obtain ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hib
      exact ⟨j, x, y, h1, (hf'at i x).mpr (Or.inl h2), (hf'at j y).mpr (Or.inl h3), h4⟩
    · exact ⟨dom, c, c', hbb', (hf'at i c).mpr (Or.inl hfb), (hf'at dom c').mpr (Or.inr ⟨rfl, rfl⟩), hadd⟩

private theorem mul_exists (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → ∃ c, Mul E a b c := by
  let body : Formula := .ex (fMul 2 1 0)
  have h := omega_induction hM hNE 1 body (bound_fMul (by omega) (by omega) (by omega)) (fun _ => a)
    (fun z hz => ⟨z, (eval_fMul _ _ _ _).mpr (mul_zero hM hNE ha hz)⟩)
    (fun b _ _ hbb' ⟨c, hc⟩ => by
      have hm : Mul E a b c := (eval_fMul _ _ _ _).mp hc
      obtain ⟨c', hadd⟩ := add_exists hM hNE hm.2.2.1 a ha
      exact ⟨c', (eval_fMul _ _ _ _).mpr (mul_succ hM hNE hm hbb' hadd)⟩)
  intro b hb; obtain ⟨c, hc⟩ := h b hb; exact ⟨c, (eval_fMul _ _ _ _).mp hc⟩

private theorem mul_unique (hM : Model E) (hNE : Nonempty V) {a b c₁ c₂ : V}
    (h1 : Mul E a b c₁) (h2 : Mul E a b c₂) : c₁ = c₂ := by
  rcases h1 with ⟨_, hb, _, z1, dom1, f1, hz1, hdom1, hfun1, hf10, hf1b, _, hstep1⟩
  rcases h2 with ⟨_, _, _, z2, dom2, f2, hz2, hdom2, hfun2, hf20, hf2b, _, hstep2⟩
  have := empty_unique hM hNE hz1 hz2; subst this
  have := succ_unique hM hNE hdom1 hdom2; subst this
  let body : Formula := .imp (.mem 0 1) (.all (.all (.imp (fAt 4 2 1) (.imp (fAt 5 2 0) (.eq 1 0)))))
  let env : Nat → V := fun k => if k = 0 then dom1 else if k = 1 then f1 else f2
  have hAgree := omega_induction hM hNE 3 body
    ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩ env
    (fun z hz _ x y hx hy => by
      have := empty_unique hM hNE hz hz1; subst this
      have hzd : E z dom1 := (hdom1 z).mpr (by rcases nat_zero_le hM hNE hz b hb with rfl | h; exact Or.inr rfl; exact Or.inl h)
      exact (functionOn_at_unique hfun1 hzd ((eval_fAt _ _ _ _).mp hx) hf10).trans
        (functionOn_at_unique hfun2 hzd ((eval_fAt _ _ _ _).mp hy) hf20).symm)
    (fun i j _ hij ih hjd x y hx hy => by
      have hib : E i b := by
        rcases (hdom1 j).mp hjd with hjb | rfl
        · exact nat_lt_trans hM hNE b hb i j ((hij i).mpr (Or.inr rfl)) hjb
        · exact (hij i).mpr (Or.inr rfl)
      obtain ⟨j1, x1, y1, hij1, hf1i, hf1j, hxy1⟩ := hstep1 i hib
      obtain ⟨j2, x2, y2, hij2, hf2i, hf2j, hxy2⟩ := hstep2 i hib
      have := succ_unique hM hNE hij1 hij; subst this
      have := succ_unique hM hNE hij2 hij; subst this
      have hid : E i dom1 := (hdom1 i).mpr (Or.inl hib)
      have hx12 : x1 = x2 := ih hid x1 x2 ((eval_fAt _ _ _ _).mpr hf1i) ((eval_fAt _ _ _ _).mpr hf2i)
      subst hx12
      have hy12 : y1 = y2 := add_unique hM hNE hxy1 hxy2
      exact (functionOn_at_unique hfun1 hjd ((eval_fAt _ _ _ _).mp hx) hf1j).trans
        (hy12.trans (functionOn_at_unique hfun2 hjd ((eval_fAt _ _ _ _).mp hy) hf2j).symm))
  exact hAgree b hb ((hdom1 b).mpr (Or.inr rfl)) c₁ c₂ ((eval_fAt _ _ _ _).mpr hf1b) ((eval_fAt _ _ _ _).mpr hf2b)

private noncomputable def zeroV (hM : Model E) (hNE : Nonempty V) : V := Classical.choose (ax_empty hM hNE)
private theorem zeroV_empty (hM : Model E) (hNE : Nonempty V) : Empty E (zeroV hM hNE) := Classical.choose_spec (ax_empty hM hNE)
private theorem zeroV_nat (hM : Model E) (hNE : Nonempty V) : NatObject E (zeroV hM hNE) := nat_zero hM hNE (zeroV_empty hM hNE)

private noncomputable def succV (hM : Model E) (hNE : Nonempty V) (a : V) : V := Classical.choose (exists_succ hM hNE a)
private theorem succV_spec (hM : Model E) (hNE : Nonempty V) (a : V) : Succ E a (succV hM hNE a) := Classical.choose_spec (exists_succ hM hNE a)
private theorem succV_nat (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) : NatObject E (succV hM hNE a) :=
  nat_succ hM hNE ha (succV_spec hM hNE a)

private noncomputable def numV (hM : Model E) (hNE : Nonempty V) : Nat → V
  | 0 => zeroV hM hNE
  | k + 1 => succV hM hNE (numV hM hNE k)

private theorem numV_numeral (hM : Model E) (hNE : Nonempty V) : ∀ k, Numeral E k (numV hM hNE k)
  | 0 => zeroV_empty hM hNE
  | k + 1 => ⟨numV hM hNE k, numV_numeral hM hNE k, succV_spec hM hNE _⟩

private theorem numV_nat (hM : Model E) (hNE : Nonempty V) : ∀ k, NatObject E (numV hM hNE k)
  | 0 => zeroV_nat hM hNE
  | k + 1 => succV_nat hM hNE (numV_nat hM hNE k)

private theorem numeral_unique (hM : Model E) (hNE : Nonempty V) : ∀ {k x y}, Numeral E k x → Numeral E k y → x = y
  | 0, _, _, hx, hy => empty_unique hM hNE hx hy
  | k + 1, _, _, ⟨x', hx', hsx⟩, ⟨y', hy', hsy⟩ => by
    rw [numeral_unique hM hNE hx' hy'] at hsx; exact succ_unique hM hNE hsx hsy

private theorem mem_numV_iff (hM : Model E) (hNE : Nonempty V) :
    ∀ k x, E x (numV hM hNE k) ↔ ∃ i, i < k ∧ x = numV hM hNE i
  | 0, x => ⟨fun h => False.elim (zeroV_empty hM hNE x h), fun ⟨_, hi, _⟩ => by omega⟩
  | k + 1, x => by
    constructor
    · intro h
      rcases (succV_spec hM hNE (numV hM hNE k) x).mp h with hlt | rfl
      · obtain ⟨i, hi, rfl⟩ := (mem_numV_iff hM hNE k x).mp hlt; exact ⟨i, by omega, rfl⟩
      · exact ⟨k, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases hik : i = k
      · rw [hik]; exact (succV_spec hM hNE (numV hM hNE k) _).mpr (Or.inr rfl)
      · exact (succV_spec hM hNE (numV hM hNE k) _).mpr (Or.inl ((mem_numV_iff hM hNE k _).mpr ⟨i, by omega, rfl⟩))

private theorem numV_lt_of_lt (hM : Model E) (hNE : Nonempty V) {a b : Nat} (h : a < b) :
    E (numV hM hNE a) (numV hM hNE b) :=
  (mem_numV_iff hM hNE b (numV hM hNE a)).mpr ⟨a, h, rfl⟩

open Classical in
private noncomputable def addV (hM : Model E) (hNE : Nonempty V) (a b : V) : V :=
  if h : NatObject E a ∧ NatObject E b then Classical.choose (add_exists hM hNE h.1 b h.2) else zeroV hM hNE

private theorem addV_spec (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    Add E a b (addV hM hNE a b) := by
  classical
  unfold addV; rw [dif_pos ⟨ha, hb⟩]; exact Classical.choose_spec (add_exists hM hNE ha b hb)

private theorem addV_nat (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    NatObject E (addV hM hNE a b) := (addV_spec hM hNE ha hb).2.2.1

private theorem add_iff_eq (hM : Model E) (hNE : Nonempty V) {a b c : V} (ha : NatObject E a) (hb : NatObject E b) :
    Add E a b c ↔ c = addV hM hNE a b :=
  ⟨fun h => add_unique hM hNE h (addV_spec hM hNE ha hb), fun h => h ▸ addV_spec hM hNE ha hb⟩

private theorem addV_zero (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    addV hM hNE a (zeroV hM hNE) = a :=
  add_unique hM hNE (addV_spec hM hNE ha (zeroV_nat hM hNE)) (add_zero hM hNE ha (zeroV_empty hM hNE))

private theorem addV_succ (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    addV hM hNE a (succV hM hNE b) = succV hM hNE (addV hM hNE a b) :=
  add_unique hM hNE (addV_spec hM hNE ha (succV_nat hM hNE hb))
    (add_succ hM hNE (addV_spec hM hNE ha hb) (succV_spec hM hNE b) (succV_spec hM hNE _))

open Classical in
private noncomputable def mulV (hM : Model E) (hNE : Nonempty V) (a b : V) : V :=
  if h : NatObject E a ∧ NatObject E b then Classical.choose (mul_exists hM hNE h.1 b h.2) else zeroV hM hNE

private theorem mulV_spec (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    Mul E a b (mulV hM hNE a b) := by
  classical
  unfold mulV; rw [dif_pos ⟨ha, hb⟩]; exact Classical.choose_spec (mul_exists hM hNE ha b hb)

private theorem mulV_nat (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    NatObject E (mulV hM hNE a b) := (mulV_spec hM hNE ha hb).2.2.1

private theorem mul_iff_eq (hM : Model E) (hNE : Nonempty V) {a b c : V} (ha : NatObject E a) (hb : NatObject E b) :
    Mul E a b c ↔ c = mulV hM hNE a b :=
  ⟨fun h => mul_unique hM hNE h (mulV_spec hM hNE ha hb), fun h => h ▸ mulV_spec hM hNE ha hb⟩

private theorem mulV_zero (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    mulV hM hNE a (zeroV hM hNE) = zeroV hM hNE :=
  mul_unique hM hNE (mulV_spec hM hNE ha (zeroV_nat hM hNE)) (mul_zero hM hNE ha (zeroV_empty hM hNE))

private theorem mulV_succ (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    mulV hM hNE a (succV hM hNE b) = addV hM hNE (mulV hM hNE a b) a :=
  mul_unique hM hNE (mulV_spec hM hNE ha (succV_nat hM hNE hb))
    (mul_succ hM hNE (mulV_spec hM hNE ha hb) (succV_spec hM hNE b) (addV_spec hM hNE (mulV_nat hM hNE ha hb) ha))

private theorem addV_numV (hM : Model E) (hNE : Nonempty V) (a : Nat) :
    ∀ b, addV hM hNE (numV hM hNE a) (numV hM hNE b) = numV hM hNE (a + b)
  | 0 => addV_zero hM hNE (numV_nat hM hNE a)
  | b + 1 => by
    rw [show numV hM hNE (b + 1) = succV hM hNE (numV hM hNE b) from rfl,
      addV_succ hM hNE (numV_nat hM hNE a) (numV_nat hM hNE b), addV_numV hM hNE a b]; rfl

private theorem addV_le_left (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → (a = addV hM hNE a b ∨ E a (addV hM hNE a b)) := by
  let body : Formula := .ex (.and (fAdd 2 1 0) (.or (.eq 2 0) (.mem 2 0)))
  have h := omega_induction hM hNE 1 body
    ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩ (fun _ => a)
    (fun z hz => ⟨a, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE ha hz), Or.inl rfl⟩)
    (fun b _ _ hbb' ⟨c, hc, hle⟩ => by
      have habc : Add E a b c := (eval_fAdd _ _ _ _).mp hc
      obtain ⟨c', hcc'⟩ := exists_succ hM hNE c
      refine ⟨c', (eval_fAdd _ _ _ _).mpr (add_succ hM hNE habc hbb' hcc'), Or.inr ?_⟩
      dsimp only [eval, pushValue] at hle ⊢
      rcases hle with rfl | hac
      · exact (hcc' a).mpr (Or.inr rfl)
      · exact (hcc' a).mpr (Or.inl hac))
  intro b hb
  obtain ⟨c, hc, hle⟩ := h b hb
  have heq : c = addV hM hNE a b := (add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp hc)
  dsimp only [eval, pushValue] at hle; rwa [← heq]

private theorem zero_addV (hM : Model E) (hNE : Nonempty V) :
    ∀ a, NatObject E a → addV hM hNE (zeroV hM hNE) a = a := by
  let body : Formula := fAdd 1 0 0
  have h := omega_induction hM hNE 1 body (bound_fAdd (by omega) (by omega) (by omega)) (fun _ => zeroV hM hNE)
    (fun z hz => by
      rw [empty_unique hM hNE hz (zeroV_empty hM hNE)]
      exact (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (zeroV_nat hM hNE) (zeroV_empty hM hNE)))
    (fun x _ _ hxy ih => by
      have h1 : Add E (zeroV hM hNE) x x := (eval_fAdd _ _ _ _).mp ih
      exact (eval_fAdd _ _ _ _).mpr (add_succ hM hNE h1 hxy hxy))
  intro a ha; exact ((add_iff_eq hM hNE (zeroV_nat hM hNE) ha).mp ((eval_fAdd _ _ _ _).mp (h a ha))).symm

private theorem succ_addV (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → addV hM hNE (succV hM hNE a) b = succV hM hNE (addV hM hNE a b) := by
  let body : Formula := .ex (.ex (.and (fAdd 3 2 1) (.and (fSucc 1 0) (fAdd 4 2 0))))
  let env : Nat → V := fun i => if i = 0 then a else succV hM hNE a
  have h := omega_induction hM hNE 2 body
    ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨bound_fSucc (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩ env
    (fun z hz => ⟨a, succV hM hNE a, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE ha hz),
      (eval_fSucc _ _ _).mpr (succV_spec hM hNE a),
      (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (succV_nat hM hNE ha) hz)⟩)
    (fun b _ _ hbb' ⟨c, c', h1, h2, h3⟩ => by
      have h1' : Add E a b c := (eval_fAdd _ _ _ _).mp h1
      have h2' : Succ E c c' := (eval_fSucc _ _ _).mp h2
      have h3' : Add E (succV hM hNE a) b c' := (eval_fAdd _ _ _ _).mp h3
      obtain ⟨c'', hc''⟩ := exists_succ hM hNE c'
      exact ⟨c', c'', (eval_fAdd _ _ _ _).mpr (add_succ hM hNE h1' hbb' h2'),
        (eval_fSucc _ _ _).mpr hc'', (eval_fAdd _ _ _ _).mpr (add_succ hM hNE h3' hbb' hc'')⟩)
  intro b hb
  obtain ⟨c, c', h1, h2, h3⟩ := h b hb
  have hc : c = addV hM hNE a b := (add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp h1)
  have hc' : c' = succV hM hNE c := succ_unique hM hNE ((eval_fSucc _ _ _).mp h2) (succV_spec hM hNE c)
  have h3' : c' = addV hM hNE (succV hM hNE a) b := (add_iff_eq hM hNE (succV_nat hM hNE ha) hb).mp ((eval_fAdd _ _ _ _).mp h3)
  rw [← h3', hc', hc]

private theorem addV_comm (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → addV hM hNE a b = addV hM hNE b a := by
  let body : Formula := .ex (.and (fAdd 2 1 0) (fAdd 1 2 0))
  have h := omega_induction hM hNE 1 body ⟨bound_fAdd (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩ (fun _ => a)
    (fun z hz => by
      have hzeq : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      refine ⟨a, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE ha hz), (eval_fAdd _ _ _ _).mpr ?_⟩
      dsimp only [pushValue]; rw [hzeq]
      have hspec := addV_spec hM hNE (zeroV_nat hM hNE) ha
      rwa [zero_addV hM hNE a ha] at hspec)
    (fun b b' hb hbb' ⟨c, h1, h2⟩ => by
      have hb' := succ_unique hM hNE hbb' (succV_spec hM hNE b); subst hb'
      have h1' : Add E a b c := (eval_fAdd _ _ _ _).mp h1
      have h2' : Add E b a c := (eval_fAdd _ _ _ _).mp h2
      have hc2 : c = addV hM hNE b a := (add_iff_eq hM hNE hb ha).mp h2'
      refine ⟨succV hM hNE c, (eval_fAdd _ _ _ _).mpr (add_succ hM hNE h1' hbb' (succV_spec hM hNE c)),
        (eval_fAdd _ _ _ _).mpr ?_⟩
      dsimp only [pushValue]
      have hss := succ_addV hM hNE hb a ha
      rw [← hc2] at hss; rw [← hss]; exact addV_spec hM hNE (succV_nat hM hNE hb) ha)
  intro b hb
  obtain ⟨c, h1, h2⟩ := h b hb
  exact ((add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp h1)).symm.trans
    ((add_iff_eq hM hNE hb ha).mp ((eval_fAdd _ _ _ _).mp h2))

private theorem addV_assoc (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    ∀ c, NatObject E c → addV hM hNE (addV hM hNE a b) c = addV hM hNE a (addV hM hNE b c) := by
  let body : Formula := .ex (.ex (.and (fAdd 4 2 1) (.and (fAdd 3 1 0) (fAdd 5 2 0))))
  let env : Nat → V := fun i => if i = 0 then a else if i = 1 then b else addV hM hNE a b
  have h := omega_induction hM hNE 3 body
    ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨bound_fAdd (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩ env
    (fun z hz => ⟨b, addV hM hNE a b, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE hb hz),
      (eval_fAdd _ _ _ _).mpr (addV_spec hM hNE ha hb),
      (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (addV_nat hM hNE ha hb) hz)⟩)
    (fun c _ _ hcc' ⟨bc, abc, h1, h2, h3⟩ => by
      have h1' : Add E b c bc := (eval_fAdd _ _ _ _).mp h1
      have h2' : Add E a bc abc := (eval_fAdd _ _ _ _).mp h2
      have h3' : Add E (addV hM hNE a b) c abc := (eval_fAdd _ _ _ _).mp h3
      obtain ⟨bc', hbc'⟩ := exists_succ hM hNE bc
      obtain ⟨abc', habc'⟩ := exists_succ hM hNE abc
      exact ⟨bc', abc', (eval_fAdd _ _ _ _).mpr (add_succ hM hNE h1' hcc' hbc'),
        (eval_fAdd _ _ _ _).mpr (add_succ hM hNE h2' hbc' habc'),
        (eval_fAdd _ _ _ _).mpr (add_succ hM hNE h3' hcc' habc')⟩)
  intro c hc
  obtain ⟨bc, abc, h1, h2, h3⟩ := h c hc
  have hbc : bc = addV hM hNE b c := (add_iff_eq hM hNE hb hc).mp ((eval_fAdd _ _ _ _).mp h1)
  have h2' : abc = addV hM hNE a bc := (add_iff_eq hM hNE ha (hbc ▸ addV_nat hM hNE hb hc)).mp ((eval_fAdd _ _ _ _).mp h2)
  have h3' : abc = addV hM hNE (addV hM hNE a b) c := (add_iff_eq hM hNE (addV_nat hM hNE ha hb) hc).mp ((eval_fAdd _ _ _ _).mp h3)
  rw [← h3', h2', hbc]

private theorem addV_lt_addV_left (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ c, NatObject E c → ∀ b, NatObject E b → E b c → E (addV hM hNE a b) (addV hM hNE a c) := by
  let body : Formula := .all (.imp (fNatObject 0) (.imp (.mem 0 1)
    (.ex (.ex (.and (fAdd 4 2 1) (.and (fAdd 4 3 0) (.mem 1 0)))))))
  have h := omega_induction hM hNE 1 body
    ⟨bound_fNatObject (by omega), ⟨⟨by omega, by omega⟩,
      ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩⟩ (fun _ => a)
    (fun z hz _ _ hbz => False.elim (hz _ hbz))
    (fun c c' hc hcc' ih b hb0 hbc' => by
      have hb : NatObject E b := (eval_fNatObject _ _).mp hb0
      have hc'eq := succ_unique hM hNE hcc' (succV_spec hM hNE c); subst hc'eq
      dsimp only [eval, pushValue] at hbc'
      rcases (hcc' b).mp hbc' with hbc | rfl
      · obtain ⟨ab, ac, h1, h2, hlt⟩ := ih b ((eval_fNatObject _ _).mpr hb) hbc
        have h1' : Add E a b ab := (eval_fAdd _ _ _ _).mp h1
        have h2' : Add E a c ac := (eval_fAdd _ _ _ _).mp h2
        have hac : ac = addV hM hNE a c := (add_iff_eq hM hNE ha hc).mp h2'
        refine ⟨ab, succV hM hNE ac, (eval_fAdd _ _ _ _).mpr h1', (eval_fAdd _ _ _ _).mpr ?_, (succV_spec hM hNE ac ab).mpr (Or.inl hlt)⟩
        dsimp only [pushValue]
        rw [hac, ← addV_succ hM hNE ha hc]; exact addV_spec hM hNE ha (succV_nat hM hNE hc)
      · refine ⟨addV hM hNE a b, succV hM hNE (addV hM hNE a b), (eval_fAdd _ _ _ _).mpr (addV_spec hM hNE ha hb),
          (eval_fAdd _ _ _ _).mpr ?_, (succV_spec hM hNE _ _).mpr (Or.inr rfl)⟩
        dsimp only [pushValue]
        rw [← addV_succ hM hNE ha hb]; exact addV_spec hM hNE ha (succV_nat hM hNE hb))
  intro c hc b hb hbc
  obtain ⟨ab, ac, h1, h2, hlt⟩ := h c hc b ((eval_fNatObject _ _).mpr hb) hbc
  have hab : ab = addV hM hNE a b := (add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp h1)
  have hac : ac = addV hM hNE a c := (add_iff_eq hM hNE ha hc).mp ((eval_fAdd _ _ _ _).mp h2)
  dsimp only [eval, pushValue] at hlt; rwa [← hab, ← hac]

private theorem sub_exists (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → (a = b ∨ E a b) → ∃ d, NatObject E d ∧ Add E a d b := by
  let body : Formula := .imp (.or (.eq 1 0) (.mem 1 0)) (.ex (.and (fNatObject 0) (fAdd 2 0 1)))
  have h := omega_induction hM hNE 1 body
    ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨bound_fNatObject (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩ (fun _ => a)
    (fun z hz hle => by
      dsimp only [eval, pushValue] at hle
      rcases hle with heq | haz
      · exact ⟨z, (eval_fNatObject _ _).mpr (nat_zero hM hNE hz),
          (eval_fAdd _ _ _ _).mpr (by dsimp only [pushValue]; rw [heq]; exact add_zero hM hNE (nat_zero hM hNE hz) hz)⟩
      · exact False.elim (hz a haz))
    (fun b _ _ hbb' ih hle => by
      dsimp only [eval, pushValue] at hle
      rcases hle with heq | hab'
      · exact ⟨zeroV hM hNE, (eval_fNatObject _ _).mpr (zeroV_nat hM hNE),
          (eval_fAdd _ _ _ _).mpr (heq ▸ add_zero hM hNE ha (zeroV_empty hM hNE))⟩
      · rcases (hbb' a).mp hab' with hab | hab
        · obtain ⟨d, hd, hadd⟩ := ih (Or.inr hab)
          have hd' : NatObject E d := (eval_fNatObject _ _).mp hd
          have hadd' : Add E a d b := (eval_fAdd _ _ _ _).mp hadd
          obtain ⟨d', hdd'⟩ := exists_succ hM hNE d
          exact ⟨d', (eval_fNatObject _ _).mpr (nat_succ hM hNE hd' hdd'),
            (eval_fAdd _ _ _ _).mpr (add_succ hM hNE hadd' hdd' hbb')⟩
        · obtain ⟨d, hd, hadd⟩ := ih (Or.inl hab)
          have hd' : NatObject E d := (eval_fNatObject _ _).mp hd
          have hadd' : Add E a d b := (eval_fAdd _ _ _ _).mp hadd
          obtain ⟨d', hdd'⟩ := exists_succ hM hNE d
          exact ⟨d', (eval_fNatObject _ _).mpr (nat_succ hM hNE hd' hdd'),
            (eval_fAdd _ _ _ _).mpr (add_succ hM hNE hadd' hdd' hbb')⟩)
  intro b hb hle
  obtain ⟨d, hd, hadd⟩ := h b hb hle
  exact ⟨d, (eval_fNatObject _ _).mp hd, (eval_fAdd _ _ _ _).mp hadd⟩

private theorem addV_left_distrib (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    ∀ c, NatObject E c → mulV hM hNE a (addV hM hNE b c) = addV hM hNE (mulV hM hNE a b) (mulV hM hNE a c) := by
  let body : Formula := .ex (.ex (.ex (.and (fAdd 5 3 2) (.and (fMul 4 3 1) (.and (fMul 4 2 0) (fAdd 6 1 0))))))
  let env : Nat → V := fun i => if i = 0 then a else if i = 1 then b else mulV hM hNE a b
  have h := omega_induction hM hNE 3 body
    ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨bound_fMul (by omega) (by omega) (by omega),
      ⟨bound_fMul (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩⟩ env
    (fun z hz =>
      ⟨b, z, mulV hM hNE a b, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE hb hz),
        (eval_fMul _ _ _ _).mpr (mul_zero hM hNE ha hz),
        (eval_fMul _ _ _ _).mpr (mulV_spec hM hNE ha hb),
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (mulV_nat hM hNE ha hb) hz)⟩)
    (fun c c' hc hcc' ⟨bc, ac, abc, h1, h2, h3, h4⟩ => by
      have hc'eq := succ_unique hM hNE hcc' (succV_spec hM hNE c); subst hc'eq
      have h1' : Add E b c bc := (eval_fAdd _ _ _ _).mp h1
      have h2' : Mul E a c ac := (eval_fMul _ _ _ _).mp h2
      have h3' : Mul E a bc abc := (eval_fMul _ _ _ _).mp h3
      have h4'' : Add E (mulV hM hNE a b) ac abc := (eval_fAdd _ _ _ _).mp h4
      have hbc : bc = addV hM hNE b c := (add_iff_eq hM hNE hb hc).mp h1'
      have hac : ac = mulV hM hNE a c := (mul_iff_eq hM hNE ha hc).mp h2'
      have habc : abc = mulV hM hNE a bc := (mul_iff_eq hM hNE ha (hbc ▸ addV_nat hM hNE hb hc)).mp h3'
      have h4' : abc = addV hM hNE (mulV hM hNE a b) ac := (add_iff_eq hM hNE (mulV_nat hM hNE ha hb) (hac ▸ mulV_nat hM hNE ha hc)).mp h4''
      refine ⟨succV hM hNE bc, addV hM hNE ac a, addV hM hNE abc a,
        (eval_fAdd _ _ _ _).mpr (add_succ hM hNE h1' hcc' (succV_spec hM hNE bc)),
        (eval_fMul _ _ _ _).mpr (mul_succ hM hNE h2' hcc' (addV_spec hM hNE (hac ▸ mulV_nat hM hNE ha hc) ha)),
        (eval_fMul _ _ _ _).mpr (mul_succ hM hNE h3' (succV_spec hM hNE bc)
          (addV_spec hM hNE (habc ▸ mulV_nat hM hNE ha (hbc ▸ addV_nat hM hNE hb hc)) ha)),
        (eval_fAdd _ _ _ _).mpr ?_⟩
      dsimp only [pushValue, env]
      rw [h4', addV_assoc hM hNE (mulV_nat hM hNE ha hb) (hac ▸ mulV_nat hM hNE ha hc) a ha]
      exact addV_spec hM hNE (mulV_nat hM hNE ha hb) (addV_nat hM hNE (hac ▸ mulV_nat hM hNE ha hc) ha))
  intro c hc
  obtain ⟨bc, ac, abc, h1, h2, h3, h4⟩ := h c hc
  have hbc : bc = addV hM hNE b c := (add_iff_eq hM hNE hb hc).mp ((eval_fAdd _ _ _ _).mp h1)
  have hac : ac = mulV hM hNE a c := (mul_iff_eq hM hNE ha hc).mp ((eval_fMul _ _ _ _).mp h2)
  have h3' : abc = mulV hM hNE a bc := (mul_iff_eq hM hNE ha (hbc ▸ addV_nat hM hNE hb hc)).mp ((eval_fMul _ _ _ _).mp h3)
  have h4' : abc = addV hM hNE (mulV hM hNE a b) ac := (add_iff_eq hM hNE (mulV_nat hM hNE ha hb) (hac ▸ mulV_nat hM hNE ha hc)).mp ((eval_fAdd _ _ _ _).mp h4)
  rw [← hbc, ← h3', h4', hac]

private theorem two_mulV_eq_addV (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    mulV hM hNE (numV hM hNE 2) a = addV hM hNE a a := by
  let body : Formula := .ex (.and (fMul 2 1 0) (fAdd 1 1 0))
  have h := omega_induction hM hNE 1 body ⟨bound_fMul (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩
    (fun _ => numV hM hNE 2)
    (fun z hz => ⟨z, (eval_fMul _ _ _ _).mpr (mul_zero hM hNE (numV_nat hM hNE 2) hz),
      (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (nat_zero hM hNE hz) hz)⟩)
    (fun x x' hx hxx' ⟨m, hm, ha2⟩ => by
      have hx' := succ_unique hM hNE hxx' (succV_spec hM hNE x); subst hx'
      have hm0 : Mul E (numV hM hNE 2) x m := (eval_fMul _ _ _ _).mp hm
      have ha0 : Add E x x m := (eval_fAdd _ _ _ _).mp ha2
      have hm' : m = mulV hM hNE (numV hM hNE 2) x := (mul_iff_eq hM hNE (numV_nat hM hNE 2) hx).mp hm0
      have ha' : m = addV hM hNE x x := (add_iff_eq hM hNE hx hx).mp ha0
      refine ⟨succV hM hNE (succV hM hNE m), (eval_fMul _ _ _ _).mpr ?_, (eval_fAdd _ _ _ _).mpr ?_⟩
      · dsimp only [pushValue]
        have h2m : Add E m (numV hM hNE 2) (succV hM hNE (succV hM hNE m)) := by
          have h0 := add_zero hM hNE (hm' ▸ mulV_nat hM hNE (numV_nat hM hNE 2) hx) (zeroV_empty hM hNE)
          have h1 := add_succ hM hNE h0 (succV_spec hM hNE _) (succV_spec hM hNE _)
          exact add_succ hM hNE h1 (succV_spec hM hNE _) (succV_spec hM hNE _)
        exact mul_succ hM hNE hm0 hxx' h2m
      · dsimp only [pushValue]
        have hs1 := succ_addV hM hNE hx x hx
        have hs2 := addV_succ hM hNE (succV_nat hM hNE hx) hx
        rw [hs1, ← ha'] at hs2
        rw [← hs2]; exact addV_spec hM hNE (succV_nat hM hNE hx) (succV_nat hM hNE hx))
  obtain ⟨m, hm, ha2⟩ := h a ha
  exact ((mul_iff_eq hM hNE (numV_nat hM hNE 2) ha).mp ((eval_fMul _ _ _ _).mp hm)).symm.trans
    ((add_iff_eq hM hNE ha ha).mp ((eval_fAdd _ _ _ _).mp ha2))

private theorem succ_mulV (hM : Model E) (hNE : Nonempty V) {s : V} (hs : NatObject E s) :
    ∀ x, NatObject E x → mulV hM hNE (succV hM hNE s) x = addV hM hNE (mulV hM hNE s x) x := by
  have hs1Nat := succV_nat hM hNE hs
  let b2 : Formula := .ex (.ex (.and (fMul 3 2 1) (.and (fAdd 1 2 0) (fMul 4 2 0))))
  let e2 : Nat → V := fun i => if i = 0 then s else succV hM hNE s
  have hm2 := omega_induction hM hNE 2 b2
    ⟨bound_fMul (by omega) (by omega) (by omega), ⟨bound_fAdd (by omega) (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega)⟩⟩ e2
    (fun z hz =>
      ⟨z, z, (eval_fMul _ _ _ _).mpr (mul_zero hM hNE hs hz),
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (nat_zero hM hNE hz) hz),
        (eval_fMul _ _ _ _).mpr (mul_zero hM hNE hs1Nat hz)⟩)
    (fun x x' hx hxx' ⟨sx, s1x, hm1, ha1, hm2⟩ => by
      have hx' := succ_unique hM hNE hxx' (succV_spec hM hNE x); subst hx'
      have hm10 : Mul E s x sx := (eval_fMul _ _ _ _).mp hm1
      have ha10 : Add E sx x s1x := (eval_fAdd _ _ _ _).mp ha1
      have hm20 : Mul E (succV hM hNE s) x s1x := (eval_fMul _ _ _ _).mp hm2
      have hsx : sx = mulV hM hNE s x := (mul_iff_eq hM hNE hs hx).mp hm10
      have hs1x : s1x = addV hM hNE sx x := (add_iff_eq hM hNE (hsx ▸ mulV_nat hM hNE hs hx) hx).mp ha10
      have hm2' : s1x = mulV hM hNE (succV hM hNE s) x := (mul_iff_eq hM hNE hs1Nat hx).mp hm20
      refine ⟨addV hM hNE sx s, addV hM hNE s1x (succV hM hNE s),
        (eval_fMul _ _ _ _).mpr (mul_succ hM hNE hm10 hxx' (addV_spec hM hNE (hsx ▸ mulV_nat hM hNE hs hx) hs)),
        (eval_fAdd _ _ _ _).mpr ?_,
        (eval_fMul _ _ _ _).mpr (mul_succ hM hNE hm20 hxx' (addV_spec hM hNE (hm2' ▸ mulV_nat hM hNE hs1Nat hx) hs1Nat))⟩
      dsimp only [pushValue, e2]
      have hsxNat : NatObject E sx := hsx ▸ mulV_nat hM hNE hs hx
      have hgoal : addV hM hNE s1x (succV hM hNE s) = addV hM hNE (addV hM hNE sx s) (succV hM hNE x) := by
        rw [hs1x, addV_succ hM hNE (addV_nat hM hNE hsxNat hx) hs,
          addV_succ hM hNE (addV_nat hM hNE hsxNat hs) hx,
          addV_assoc hM hNE hsxNat hx s hs, addV_assoc hM hNE hsxNat hs x hx,
          addV_comm hM hNE hx s hs]
      rw [hgoal]; exact addV_spec hM hNE (addV_nat hM hNE hsxNat hs) (succV_nat hM hNE hx))
  intro x hx
  obtain ⟨sx, s1x, hm1, ha1, hm2⟩ := hm2 x hx
  have hsx : sx = mulV hM hNE s x := (mul_iff_eq hM hNE hs hx).mp ((eval_fMul _ _ _ _).mp hm1)
  have hs1x : s1x = addV hM hNE sx x := (add_iff_eq hM hNE (hsx ▸ mulV_nat hM hNE hs hx) hx).mp ((eval_fAdd _ _ _ _).mp ha1)
  have hm2' : s1x = mulV hM hNE (succV hM hNE s) x := (mul_iff_eq hM hNE hs1Nat hx).mp ((eval_fMul _ _ _ _).mp hm2)
  rw [← hm2', hs1x, hsx]

private theorem triangular_half_exists (hM : Model E) (hNE : Nonempty V) :
    ∀ s, NatObject E s → ∃ q, NatObject E q ∧
      mulV hM hNE (numV hM hNE 2) q = mulV hM hNE s (succV hM hNE s) := by
  let body : Formula := .ex (.ex (.ex (.and (fNatObject 2) (.and (fSucc 3 1) (.and (fMul 4 2 0) (fMul 3 1 0))))))
  have h := omega_induction hM hNE 1 body
    ⟨bound_fNatObject (by omega), ⟨bound_fSucc (by omega) (by omega),
      ⟨bound_fMul (by omega) (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega)⟩⟩⟩
    (fun _ => numV hM hNE 2)
    (fun z hz => by
      have hzeq : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      have hz0 : mulV hM hNE (zeroV hM hNE) (succV hM hNE (zeroV hM hNE)) = zeroV hM hNE := by
        rw [mulV_succ hM hNE (zeroV_nat hM hNE) (zeroV_nat hM hNE),
          mulV_zero hM hNE (zeroV_nat hM hNE), addV_zero hM hNE (zeroV_nat hM hNE)]
      refine ⟨zeroV hM hNE, succV hM hNE (zeroV hM hNE), zeroV hM hNE,
        (eval_fNatObject _ _).mpr (zeroV_nat hM hNE),
        (eval_fSucc _ _ _).mpr (by dsimp only [pushValue]; rw [hzeq]; exact succV_spec hM hNE _),
        (eval_fMul _ _ _ _).mpr (mul_zero hM hNE (numV_nat hM hNE 2) (zeroV_empty hM hNE)),
        (eval_fMul _ _ _ _).mpr ?_⟩
      dsimp only [pushValue]; rw [hzeq]
      have hspec := mulV_spec hM hNE (zeroV_nat hM hNE) (succV_nat hM hNE (zeroV_nat hM hNE))
      rwa [hz0] at hspec)
    (fun s s' hs hss' ⟨q, s1, p, hq, hs1, h2q, hsp⟩ => by
      have hs'eq := succ_unique hM hNE hss' (succV_spec hM hNE s); subst hs'eq
      have hs1' : Succ E s s1 := (eval_fSucc _ _ _).mp hs1
      have hs1eq := succ_unique hM hNE hs1' (succV_spec hM hNE s); subst hs1eq
      have hqNat : NatObject E q := (eval_fNatObject _ _).mp hq
      have h2q0 : Mul E (numV hM hNE 2) q p := (eval_fMul _ _ _ _).mp h2q
      have hsp0 : Mul E s (succV hM hNE s) p := (eval_fMul _ _ _ _).mp hsp
      have h2q' : p = mulV hM hNE (numV hM hNE 2) q := (mul_iff_eq hM hNE (numV_nat hM hNE 2) hqNat).mp h2q0
      have hsp' : p = mulV hM hNE s (succV hM hNE s) := (mul_iff_eq hM hNE hs (succV_nat hM hNE hs)).mp hsp0
      have hs1Nat := succV_nat hM hNE hs
      have hq'Nat := addV_nat hM hNE hqNat hs1Nat
      have hcalc : mulV hM hNE (numV hM hNE 2) (addV hM hNE q (succV hM hNE s)) =
          mulV hM hNE (succV hM hNE s) (succV hM hNE (succV hM hNE s)) := by
        rw [addV_left_distrib hM hNE (numV_nat hM hNE 2) hqNat (succV hM hNE s) hs1Nat,
          ← h2q', hsp', two_mulV_eq_addV hM hNE hs1Nat,
          mulV_succ hM hNE hs1Nat hs1Nat, succ_mulV hM hNE hs (succV hM hNE s) hs1Nat,
          addV_assoc hM hNE (mulV_nat hM hNE hs hs1Nat) hs1Nat (succV hM hNE s) hs1Nat]
      refine ⟨addV hM hNE q (succV hM hNE s), succV hM hNE (succV hM hNE s),
        mulV hM hNE (numV hM hNE 2) (addV hM hNE q (succV hM hNE s)),
        (eval_fNatObject _ _).mpr hq'Nat, (eval_fSucc _ _ _).mpr (succV_spec hM hNE _),
        (eval_fMul _ _ _ _).mpr (mulV_spec hM hNE (numV_nat hM hNE 2) hq'Nat),
        (eval_fMul _ _ _ _).mpr ?_⟩
      dsimp only [pushValue]
      rw [hcalc]; exact mulV_spec hM hNE hs1Nat (succV_nat hM hNE hs1Nat))
  intro s hs
  obtain ⟨q, s1, p, hq, hs1, h2q, hsp⟩ := h s hs
  have hs1' : Succ E s s1 := (eval_fSucc _ _ _).mp hs1
  have hs1eq := succ_unique hM hNE hs1' (succV_spec hM hNE s); subst hs1eq
  have hqNat : NatObject E q := (eval_fNatObject _ _).mp hq
  exact ⟨q, hqNat, ((mul_iff_eq hM hNE (numV_nat hM hNE 2) hqNat).mp ((eval_fMul _ _ _ _).mp h2q)).symm.trans
    ((mul_iff_eq hM hNE hs (succV_nat hM hNE hs)).mp ((eval_fMul _ _ _ _).mp hsp))⟩

private theorem cantor_exists (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) : ∃ p, Cantor E a b p ∧ (b = p ∨ E b p) := by
  let s := addV hM hNE a b
  have hs := addV_nat hM hNE ha hb
  obtain ⟨q, hq, h2q⟩ := triangular_half_exists hM hNE s hs
  let p := addV hM hNE q b
  have hp := addV_nat hM hNE hq hb
  have h2p : mulV hM hNE (numV hM hNE 2) p =
      addV hM hNE (mulV hM hNE s (succV hM hNE s)) (mulV hM hNE (numV hM hNE 2) b) := by
    rw [addV_left_distrib hM hNE (numV_nat hM hNE 2) hq b hb, h2q]
  have hbp : b = p ∨ E b p := by
    have hle := addV_le_left hM hNE hb q hq
    rwa [addV_comm hM hNE hb q hq] at hle
  refine ⟨p, ⟨ha, hb, hp, numV hM hNE 2, s, succV hM hNE s,
    mulV hM hNE s (succV hM hNE s), mulV hM hNE (numV hM hNE 2) b,
    mulV hM hNE (numV hM hNE 2) p,
    addV hM hNE (mulV hM hNE s (succV hM hNE s)) (mulV hM hNE (numV hM hNE 2) b),
    numV_numeral hM hNE 2, addV_spec hM hNE ha hb, succV_spec hM hNE s,
    mulV_spec hM hNE hs (succV_nat hM hNE hs), mulV_spec hM hNE (numV_nat hM hNE 2) hb,
    mulV_spec hM hNE (numV_nat hM hNE 2) hp,
    addV_spec hM hNE (mulV_nat hM hNE hs (succV_nat hM hNE hs)) (mulV_nat hM hNE (numV_nat hM hNE 2) hb),
    h2p⟩, hbp⟩

private theorem cantor_unique (hM : Model E) (hNE : Nonempty V) {a b p₁ p₂ : V}
    (h1 : Cantor E a b p₁) (h2 : Cantor E a b p₂) : p₁ = p₂ := by
  rcases h1 with ⟨_, _, hp1, two1, sum1, next1, prod1, tb1, tz1, tot1, h2_1, hadd1, hs1, hm1_1, hm2_1, hm3_1, ha2_1, heq1⟩
  rcases h2 with ⟨_, _, hp2, two2, sum2, next2, prod2, tb2, tz2, tot2, h2_2, hadd2, hs2, hm1_2, hm2_2, hm3_2, ha2_2, heq2⟩
  have := numeral_unique hM hNE h2_1 (numV_numeral hM hNE 2); subst this
  have := numeral_unique hM hNE h2_2 (numV_numeral hM hNE 2); subst this
  have := add_unique hM hNE hadd1 hadd2; subst this
  have := succ_unique hM hNE hs1 hs2; subst this
  have := mul_unique hM hNE hm1_1 hm1_2; subst this
  have := mul_unique hM hNE hm2_1 hm2_2; subst this
  have := add_unique hM hNE ha2_1 ha2_2; subst this
  have htz : tz1 = tz2 := heq1.trans heq2.symm; subst htz
  have hm3eq1 := (mul_iff_eq hM hNE (numV_nat hM hNE 2) hp1).mp hm3_1
  have hm3eq2 := (mul_iff_eq hM hNE (numV_nat hM hNE 2) hp2).mp hm3_2
  rcases nat_trichotomy hM hNE p₁ hp1 p₂ hp2 with hlt | rfl | hgt
  · have h2lt : E (mulV hM hNE (numV hM hNE 2) p₁) (mulV hM hNE (numV hM hNE 2) p₂) := by
      rw [two_mulV_eq_addV hM hNE hp1, two_mulV_eq_addV hM hNE hp2]
      have h1 := addV_lt_addV_left hM hNE hp1 p₂ hp2 p₁ hp1 hlt
      have h2 := addV_lt_addV_left hM hNE hp2 p₂ hp2 p₁ hp1 hlt
      rw [addV_comm hM hNE hp2 p₁ hp1] at h2
      exact nat_lt_trans hM hNE _ (addV_nat hM hNE hp2 hp2) _ _ h1 h2
    exact False.elim (mem_irrefl hM hNE _ (hm3eq1 ▸ hm3eq2 ▸ h2lt))
  · rfl
  · have h2lt : E (mulV hM hNE (numV hM hNE 2) p₂) (mulV hM hNE (numV hM hNE 2) p₁) := by
      rw [two_mulV_eq_addV hM hNE hp1, two_mulV_eq_addV hM hNE hp2]
      have h1 := addV_lt_addV_left hM hNE hp2 p₁ hp1 p₂ hp2 hgt
      have h2 := addV_lt_addV_left hM hNE hp1 p₁ hp1 p₂ hp2 hgt
      rw [addV_comm hM hNE hp1 p₂ hp2] at h2
      exact nat_lt_trans hM hNE _ (addV_nat hM hNE hp1 hp1) _ _ h1 h2
    exact False.elim (mem_irrefl hM hNE _ (hm3eq1 ▸ hm3eq2 ▸ h2lt))

private theorem cantor_le_right (hM : Model E) (hNE : Nonempty V) {a b p : V}
    (hc : Cantor E a b p) : b = p ∨ E b p := by
  obtain ⟨p', hc', hbp'⟩ := cantor_exists hM hNE hc.1 hc.2.1
  rwa [cantor_unique hM hNE hc hc']

private theorem cantor_unpair (hM : Model E) (hNE : Nonempty V) :
    ∀ p, NatObject E p → ∃ a b, Cantor E a b p := by
  let body : Formula := .ex (.ex (fCantor 1 0 2))
  have h := omega_induction hM hNE 0 body (bound_fCantor (by omega) (by omega) (by omega))
    (fun _ => Classical.choice hNE)
    (fun z hz => by
      have hzeq : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      obtain ⟨p, hcp, _⟩ := cantor_exists hM hNE (zeroV_nat hM hNE) (zeroV_nat hM hNE)
      have hp0 : p = zeroV hM hNE := by
        rcases hcp with ⟨_, _, hp, two, s, ns, prod, tb, tz, tot, h2, hadd, hs, hm1, hm2, hm3, ha2, heq⟩
        have := numeral_unique hM hNE h2 (numV_numeral hM hNE 2); subst this
        have hs0 : s = zeroV hM hNE := (add_iff_eq hM hNE (zeroV_nat hM hNE) (zeroV_nat hM hNE)).mp hadd |>.trans (addV_zero hM hNE (zeroV_nat hM hNE))
        subst hs0
        have hns : ns = numV hM hNE 1 := succ_unique hM hNE hs (succV_spec hM hNE _)
        subst hns
        have hpr : prod = zeroV hM hNE := by
          rw [(mul_iff_eq hM hNE (zeroV_nat hM hNE) (numV_nat hM hNE 1)).mp hm1,
            show numV hM hNE 1 = succV hM hNE (zeroV hM hNE) from rfl,
            mulV_succ hM hNE (zeroV_nat hM hNE) (zeroV_nat hM hNE),
            mulV_zero hM hNE (zeroV_nat hM hNE), addV_zero hM hNE (zeroV_nat hM hNE)]
        subst hpr
        have htb : tb = zeroV hM hNE := (mul_iff_eq hM hNE (numV_nat hM hNE 2) (zeroV_nat hM hNE)).mp hm2 |>.trans (mulV_zero hM hNE (numV_nat hM hNE 2))
        subst htb
        have htot : tot = zeroV hM hNE := (add_iff_eq hM hNE (zeroV_nat hM hNE) (zeroV_nat hM hNE)).mp ha2 |>.trans (addV_zero hM hNE (zeroV_nat hM hNE))
        rw [htot] at heq
        have h2p : mulV hM hNE (numV hM hNE 2) p = zeroV hM hNE := ((mul_iff_eq hM hNE (numV_nat hM hNE 2) hp).mp hm3).symm.trans heq
        rw [two_mulV_eq_addV hM hNE hp] at h2p
        rcases addV_le_left hM hNE hp p hp with hpeq | hplt
        · rw [h2p] at hpeq; exact hpeq
        · rw [h2p] at hplt; exact False.elim (zeroV_empty hM hNE p hplt)
      rw [hp0] at hcp
      exact ⟨zeroV hM hNE, zeroV hM hNE, (eval_fCantor _ _ _ _).mpr (by dsimp only [pushValue]; rwa [hzeq])⟩)
    (fun p p' hp hpp' ⟨a, b, hcab⟩ => by
      have hp'eq := succ_unique hM hNE hpp' (succV_spec hM hNE p); subst hp'eq
      have hcab' : Cantor E a b p := (eval_fCantor _ _ _ _).mp hcab
      have ha := hcab'.1; have hb := hcab'.2.1
      have h2p : mulV hM hNE (numV hM hNE 2) p =
          addV hM hNE (mulV hM hNE (addV hM hNE a b) (succV hM hNE (addV hM hNE a b)))
            (mulV hM hNE (numV hM hNE 2) b) := by
        rcases hcab' with ⟨_, _, _, two, sum, next, prod, tb, tz, tot, h2, hadd, hs, hm1, hm2, hm3, ha2, heq⟩
        have := numeral_unique hM hNE h2 (numV_numeral hM hNE 2); subst this
        have := (add_iff_eq hM hNE ha hb).mp hadd; subst this
        have := succ_unique hM hNE hs (succV_spec hM hNE _); subst this
        have := (mul_iff_eq hM hNE (addV_nat hM hNE ha hb) (succV_nat hM hNE (addV_nat hM hNE ha hb))).mp hm1; subst this
        have := (mul_iff_eq hM hNE (numV_nat hM hNE 2) hb).mp hm2; subst this
        have := (add_iff_eq hM hNE (mulV_nat hM hNE (addV_nat hM hNE ha hb) (succV_nat hM hNE (addV_nat hM hNE ha hb)))
          (mulV_nat hM hNE (numV_nat hM hNE 2) hb)).mp ha2; subst this
        exact ((mul_iff_eq hM hNE (numV_nat hM hNE 2) hp).mp hm3).symm.trans heq
      have h2p' : mulV hM hNE (numV hM hNE 2) (succV hM hNE p) =
          addV hM hNE (mulV hM hNE (numV hM hNE 2) p) (numV hM hNE 2) :=
        mulV_succ hM hNE (numV_nat hM hNE 2) hp
      rcases nat_cases hM hNE a ha with ha0 | ⟨a', ha'Nat, ha'a⟩
      · have haeq : a = zeroV hM hNE := empty_unique hM hNE ha0 (zeroV_empty hM hNE)
        subst haeq
        rw [zero_addV hM hNE b hb] at h2p
        have hb1 := succV_nat hM hNE hb
        have hcalc : mulV hM hNE (numV hM hNE 2) (succV hM hNE p) =
            addV hM hNE (mulV hM hNE (addV hM hNE (succV hM hNE b) (zeroV hM hNE))
              (succV hM hNE (addV hM hNE (succV hM hNE b) (zeroV hM hNE))))
              (mulV hM hNE (numV hM hNE 2) (zeroV hM hNE)) := by
          rw [addV_zero hM hNE hb1, mulV_zero hM hNE (numV_nat hM hNE 2),
            addV_zero hM hNE (mulV_nat hM hNE hb1 (succV_nat hM hNE hb1)),
            h2p', h2p,
            addV_assoc hM hNE (mulV_nat hM hNE hb hb1) (mulV_nat hM hNE (numV_nat hM hNE 2) hb) (numV hM hNE 2) (numV_nat hM hNE 2),
            ← mulV_succ hM hNE (numV_nat hM hNE 2) hb,
            two_mulV_eq_addV hM hNE hb1,
            mulV_succ hM hNE hb1 hb1, succ_mulV hM hNE hb (succV hM hNE b) hb1,
            addV_assoc hM hNE (mulV_nat hM hNE hb hb1) hb1 (succV hM hNE b) hb1]
        have hsp := succV_nat hM hNE hp
        refine ⟨succV hM hNE b, zeroV hM hNE, (eval_fCantor _ _ _ _).mpr ?_⟩
        exact ⟨hb1, zeroV_nat hM hNE, hsp, numV hM hNE 2,
          addV hM hNE (succV hM hNE b) (zeroV hM hNE), succV hM hNE (addV hM hNE (succV hM hNE b) (zeroV hM hNE)),
          mulV hM hNE (addV hM hNE (succV hM hNE b) (zeroV hM hNE)) (succV hM hNE (addV hM hNE (succV hM hNE b) (zeroV hM hNE))),
          mulV hM hNE (numV hM hNE 2) (zeroV hM hNE),
          mulV hM hNE (numV hM hNE 2) (succV hM hNE p),
          addV hM hNE (mulV hM hNE (addV hM hNE (succV hM hNE b) (zeroV hM hNE))
            (succV hM hNE (addV hM hNE (succV hM hNE b) (zeroV hM hNE))))
            (mulV hM hNE (numV hM hNE 2) (zeroV hM hNE)),
          numV_numeral hM hNE 2, addV_spec hM hNE hb1 (zeroV_nat hM hNE), succV_spec hM hNE _,
          mulV_spec hM hNE (addV_nat hM hNE hb1 (zeroV_nat hM hNE)) (succV_nat hM hNE (addV_nat hM hNE hb1 (zeroV_nat hM hNE))),
          mulV_spec hM hNE (numV_nat hM hNE 2) (zeroV_nat hM hNE),
          mulV_spec hM hNE (numV_nat hM hNE 2) hsp,
          addV_spec hM hNE (mulV_nat hM hNE (addV_nat hM hNE hb1 (zeroV_nat hM hNE)) (succV_nat hM hNE (addV_nat hM hNE hb1 (zeroV_nat hM hNE))))
            (mulV_nat hM hNE (numV_nat hM hNE 2) (zeroV_nat hM hNE)), hcalc⟩
      · have haeq : a = succV hM hNE a' := succ_unique hM hNE ha'a (succV_spec hM hNE a')
        subst haeq
        have hb1 := succV_nat hM hNE hb
        have hsum_eq : addV hM hNE a' (succV hM hNE b) = addV hM hNE (succV hM hNE a') b := by
          rw [addV_succ hM hNE ha'Nat hb, succ_addV hM hNE ha'Nat b hb]
        have hcalc : mulV hM hNE (numV hM hNE 2) (succV hM hNE p) =
            addV hM hNE (mulV hM hNE (addV hM hNE a' (succV hM hNE b)) (succV hM hNE (addV hM hNE a' (succV hM hNE b))))
              (mulV hM hNE (numV hM hNE 2) (succV hM hNE b)) := by
          rw [hsum_eq, h2p', h2p,
            addV_assoc hM hNE (mulV_nat hM hNE (addV_nat hM hNE ha hb) (succV_nat hM hNE (addV_nat hM hNE ha hb)))
              (mulV_nat hM hNE (numV_nat hM hNE 2) hb) (numV hM hNE 2) (numV_nat hM hNE 2),
            ← mulV_succ hM hNE (numV_nat hM hNE 2) hb]
        have hsp := succV_nat hM hNE hp
        refine ⟨a', succV hM hNE b, (eval_fCantor _ _ _ _).mpr ?_⟩
        exact ⟨ha'Nat, hb1, hsp, numV hM hNE 2,
          addV hM hNE a' (succV hM hNE b), succV hM hNE (addV hM hNE a' (succV hM hNE b)),
          mulV hM hNE (addV hM hNE a' (succV hM hNE b)) (succV hM hNE (addV hM hNE a' (succV hM hNE b))),
          mulV hM hNE (numV hM hNE 2) (succV hM hNE b),
          mulV hM hNE (numV hM hNE 2) (succV hM hNE p),
          addV hM hNE (mulV hM hNE (addV hM hNE a' (succV hM hNE b)) (succV hM hNE (addV hM hNE a' (succV hM hNE b))))
            (mulV hM hNE (numV hM hNE 2) (succV hM hNE b)),
          numV_numeral hM hNE 2, addV_spec hM hNE ha'Nat hb1, succV_spec hM hNE _,
          mulV_spec hM hNE (addV_nat hM hNE ha'Nat hb1) (succV_nat hM hNE (addV_nat hM hNE ha'Nat hb1)),
          mulV_spec hM hNE (numV_nat hM hNE 2) hb1,
          mulV_spec hM hNE (numV_nat hM hNE 2) hsp,
          addV_spec hM hNE (mulV_nat hM hNE (addV_nat hM hNE ha'Nat hb1) (succV_nat hM hNE (addV_nat hM hNE ha'Nat hb1)))
            (mulV_nat hM hNE (numV_nat hM hNE 2) hb1), hcalc⟩)
  intro p hp
  obtain ⟨a, b, hc⟩ := h p hp
  exact ⟨a, b, (eval_fCantor _ _ _ _).mp hc⟩

private theorem cantor_zero_ne (hM : Model E) (hNE : Nonempty V) {a b p : V}
    (hc : Cantor E a b p) (hbne : ¬ Empty E b) : ¬ Empty E p := by
  intro hp0
  rcases cantor_le_right hM hNE hc with rfl | hbp
  · exact hbne hp0
  · exact hp0 b hbp

private theorem mulV_four_add_two_ne (hM : Model E) (hNE : Nonempty V) {p1 p2 : V}
    (hp1 : NatObject E p1) (hp2 : NatObject E p2) :
    addV hM hNE (mulV hM hNE (numV hM hNE 4) p1) (numV hM hNE 2) ≠ mulV hM hNE (numV hM hNE 4) p2 := by
  have h4 := numV_nat hM hNE 4
  have h2 := numV_nat hM hNE 2
  have h4_le_mono : ∀ x, NatObject E x → ∀ y, NatObject E y → (x = y ∨ E x y) →
      mulV hM hNE (numV hM hNE 4) x = mulV hM hNE (numV hM hNE 4) y ∨
      E (mulV hM hNE (numV hM hNE 4) x) (mulV hM hNE (numV hM hNE 4) y) := by
    intro x hx y hy hle
    rcases hle with rfl | hxy
    · exact Or.inl rfl
    · obtain ⟨d, hd, hadd⟩ := sub_exists hM hNE hx y hy (Or.inr hxy)
      have hy_eq : y = addV hM hNE x d := (add_iff_eq hM hNE hx hd).mp hadd
      rw [hy_eq, addV_left_distrib hM hNE h4 hx d hd]
      exact addV_le_left hM hNE (mulV_nat hM hNE h4 hx) (mulV hM hNE (numV hM hNE 4) d) (mulV_nat hM hNE h4 hd)
  intro heq
  rcases nat_trichotomy hM hNE p1 hp1 p2 hp2 with hlt | rfl | hgt
  · have hle : succV hM hNE p1 = p2 ∨ E (succV hM hNE p1) p2 := (nat_succ_le_iff hM hNE hp1 (succV_spec hM hNE p1) p2 hp2).mp hlt
    have h4le := h4_le_mono (succV hM hNE p1) (succV_nat hM hNE hp1) p2 hp2 hle
    have h4succ : mulV hM hNE (numV hM hNE 4) (succV hM hNE p1) =
        addV hM hNE (mulV hM hNE (numV hM hNE 4) p1) (numV hM hNE 4) := mulV_succ hM hNE h4 hp1
    have h2lt4 : E (addV hM hNE (mulV hM hNE (numV hM hNE 4) p1) (numV hM hNE 2))
        (addV hM hNE (mulV hM hNE (numV hM hNE 4) p1) (numV hM hNE 4)) :=
      addV_lt_addV_left hM hNE (mulV_nat hM hNE h4 hp1) (numV hM hNE 4) h4 (numV hM hNE 2) h2 (numV_lt_of_lt hM hNE (by omega))
    rw [← h4succ, heq] at h2lt4
    rcases h4le with h4eq | h4lt
    · exact mem_irrefl hM hNE _ (h4eq ▸ h2lt4)
    · exact mem_asymm hM hNE h2lt4 h4lt
  · have hlt2 : E (addV hM hNE (mulV hM hNE (numV hM hNE 4) p1) (zeroV hM hNE))
        (addV hM hNE (mulV hM hNE (numV hM hNE 4) p1) (numV hM hNE 2)) :=
      addV_lt_addV_left hM hNE (mulV_nat hM hNE h4 hp1) (numV hM hNE 2) h2 (zeroV hM hNE) (zeroV_nat hM hNE) (numV_lt_of_lt hM hNE (a := 0) (b := 2) (by omega))
    rw [addV_zero hM hNE (mulV_nat hM hNE h4 hp1), heq] at hlt2
    exact mem_irrefl hM hNE _ hlt2
  · have hle : succV hM hNE p2 = p1 ∨ E (succV hM hNE p2) p1 := (nat_succ_le_iff hM hNE hp2 (succV_spec hM hNE p2) p1 hp1).mp hgt
    have h4le := h4_le_mono (succV hM hNE p2) (succV_nat hM hNE hp2) p1 hp1 hle
    have h4lt : E (mulV hM hNE (numV hM hNE 4) p2) (mulV hM hNE (numV hM hNE 4) (succV hM hNE p2)) := by
      rw [mulV_succ hM hNE h4 hp2]
      have h0lt4 : E (addV hM hNE (mulV hM hNE (numV hM hNE 4) p2) (zeroV hM hNE))
          (addV hM hNE (mulV hM hNE (numV hM hNE 4) p2) (numV hM hNE 4)) :=
        addV_lt_addV_left hM hNE (mulV_nat hM hNE h4 hp2) (numV hM hNE 4) h4 (zeroV hM hNE) (zeroV_nat hM hNE) (numV_lt_of_lt hM hNE (a := 0) (b := 4) (by omega))
      rwa [addV_zero hM hNE (mulV_nat hM hNE h4 hp2)] at h0lt4
    have h4ltp1 : E (mulV hM hNE (numV hM hNE 4) p2) (mulV hM hNE (numV hM hNE 4) p1) := by
      rcases h4le with h4eq | h4lt2
      · exact h4eq ▸ h4lt
      · exact nat_lt_trans hM hNE _ (mulV_nat hM hNE h4 hp1) _ _ h4lt h4lt2
    have hp1le : mulV hM hNE (numV hM hNE 4) p1 = mulV hM hNE (numV hM hNE 4) p2 ∨
        E (mulV hM hNE (numV hM hNE 4) p1) (mulV hM hNE (numV hM hNE 4) p2) := by
      rw [← heq]; exact addV_le_left hM hNE (mulV_nat hM hNE h4 hp1) (numV hM hNE 2) h2
    rcases hp1le with h4eq | h4lt2
    · exact mem_irrefl hM hNE _ (h4eq ▸ h4ltp1)
    · exact mem_asymm hM hNE h4ltp1 h4lt2

private theorem calcUc_ne_calcIc (hM : Model E) (hNE : Nonempty V) {a b c d u ic : V}
    (hu : CalcUc E a b u) (hic : CalcIc E c d ic) : u ≠ ic := by
  rcases hu with ⟨p1, f1, q1, t1, hcp1, hf1, hmq1, ht1, ha1⟩
  rcases hic with ⟨p2, f2, hcp2, hf2, hmq2⟩
  have := numeral_unique hM hNE hf1 (numV_numeral hM hNE 4); subst this
  have := numeral_unique hM hNE hf2 (numV_numeral hM hNE 4); subst this
  have := numeral_unique hM hNE ht1 (numV_numeral hM hNE 2); subst this
  have hq1 := (mul_iff_eq hM hNE (numV_nat hM hNE 4) hcp1.2.2.1).mp hmq1; subst hq1
  have hu_eq := (add_iff_eq hM hNE (mulV_nat hM hNE (numV_nat hM hNE 4) hcp1.2.2.1) (numV_nat hM hNE 2)).mp ha1; subst hu_eq
  have hic_eq := (mul_iff_eq hM hNE (numV_nat hM hNE 4) hcp2.2.2.1).mp hmq2; subst hic_eq
  exact mulV_four_add_two_ne hM hNE hcp1.2.2.1 hcp2.2.2.1

private theorem calcIc_ne_zero_of_ne_zero (hM : Model E) (hNE : Nonempty V) {a b ic : V}
    (hic : CalcIc E a b ic) (hb : ¬ Empty E b) : ¬ Empty E ic := by
  rcases hic with ⟨p, f, hcp, hf, hm⟩
  have := numeral_unique hM hNE hf (numV_numeral hM hNE 4); subst this
  have hpne : ¬ Empty E p := cantor_zero_ne hM hNE hcp hb
  rcases nat_cases hM hNE p hcp.2.2.1 with hp0 | ⟨p', hp'Nat, hp'p⟩
  · exact False.elim (hpne hp0)
  · have hpeq := succ_unique hM hNE hp'p (succV_spec hM hNE p'); subst hpeq
    have hic_eq := (mul_iff_eq hM hNE (numV_nat hM hNE 4) (succV_nat hM hNE hp'Nat)).mp hm; subst hic_eq
    rw [mulV_succ hM hNE (numV_nat hM hNE 4) hp'Nat]
    have hlt : E (zeroV hM hNE) (addV hM hNE (mulV hM hNE (numV hM hNE 4) p') (numV hM hNE 4)) := by
      have h1 := addV_lt_addV_left hM hNE (mulV_nat hM hNE (numV_nat hM hNE 4) hp'Nat)
        (numV hM hNE 4) (numV_nat hM hNE 4) (zeroV hM hNE) (zeroV_nat hM hNE) (numV_lt_of_lt hM hNE (a := 0) (b := 4) (by omega))
      rw [addV_zero hM hNE (mulV_nat hM hNE (numV_nat hM hNE 4) hp'Nat)] at h1
      rcases nat_zero_le hM hNE (zeroV_empty hM hNE) (mulV hM hNE (numV hM hNE 4) p')
          (mulV_nat hM hNE (numV_nat hM hNE 4) hp'Nat) with h0 | h0lt
      · rw [h0]; exact h1
      · exact nat_lt_trans hM hNE _ (addV_nat hM hNE (mulV_nat hM hNE (numV_nat hM hNE 4) hp'Nat) (numV_nat hM hNE 4)) _ _ h0lt h1
    intro he; exact he (zeroV hM hNE) hlt

/-! ### Existence & Uniqueness of Internal Calculus C Operations -/

private theorem calcIc_exists (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) : ∃ res, CalcIc E a b res ∧ NatObject E res := by
  obtain ⟨p, hcp, _⟩ := cantor_exists hM hNE ha hb
  exact ⟨mulV hM hNE (numV hM hNE 4) p, ⟨p, numV hM hNE 4, hcp, numV_numeral hM hNE 4,
    mulV_spec hM hNE (numV_nat hM hNE 4) hcp.2.2.1⟩, mulV_nat hM hNE (numV_nat hM hNE 4) hcp.2.2.1⟩

private theorem calcIc_unique (hM : Model E) (hNE : Nonempty V) {a b r1 r2 : V}
    (h1 : CalcIc E a b r1) (h2 : CalcIc E a b r2) : r1 = r2 := by
  rcases h1 with ⟨p1, f1, hc1, hf1, hm1⟩
  rcases h2 with ⟨p2, f2, hc2, hf2, hm2⟩
  have := cantor_unique hM hNE hc1 hc2; subst this
  have := numeral_unique hM hNE hf1 hf2; subst this
  exact mul_unique hM hNE hm1 hm2

private theorem calcMc_exists (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) : ∃ res, CalcMc E a b res ∧ NatObject E res := by
  obtain ⟨ic, hic, hicN⟩ := calcIc_exists hM hNE ha hb
  exact ⟨succV hM hNE ic, ⟨ic, hic, succV_spec hM hNE ic⟩, succV_nat hM hNE hicN⟩

private theorem calcMc_unique (hM : Model E) (hNE : Nonempty V) {a b r1 r2 : V}
    (h1 : CalcMc E a b r1) (h2 : CalcMc E a b r2) : r1 = r2 := by
  rcases h1 with ⟨ic1, hic1, hs1⟩
  rcases h2 with ⟨ic2, hic2, hs2⟩
  have := calcIc_unique hM hNE hic1 hic2; subst this
  exact succ_unique hM hNE hs1 hs2

private theorem calcUc_exists (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) : ∃ res, CalcUc E a b res ∧ NatObject E res := by
  obtain ⟨p, hcp, _⟩ := cantor_exists hM hNE hb ha
  let q := mulV hM hNE (numV hM hNE 4) p
  have hq := mulV_nat hM hNE (numV_nat hM hNE 4) hcp.2.2.1
  exact ⟨addV hM hNE q (numV hM hNE 2),
    ⟨p, numV hM hNE 4, q, numV hM hNE 2, hcp, numV_numeral hM hNE 4,
      mulV_spec hM hNE (numV_nat hM hNE 4) hcp.2.2.1, numV_numeral hM hNE 2,
      addV_spec hM hNE hq (numV_nat hM hNE 2)⟩,
    addV_nat hM hNE hq (numV_nat hM hNE 2)⟩

private theorem calcUc_unique (hM : Model E) (hNE : Nonempty V) {a b r1 r2 : V}
    (h1 : CalcUc E a b r1) (h2 : CalcUc E a b r2) : r1 = r2 := by
  rcases h1 with ⟨p1, f1, q1, t1, hc1, hf1, hm1, ht1, ha1⟩
  rcases h2 with ⟨p2, f2, q2, t2, hc2, hf2, hm2, ht2, ha2⟩
  have := cantor_unique hM hNE hc1 hc2; subst this
  have := numeral_unique hM hNE hf1 hf2; subst this
  have := mul_unique hM hNE hm1 hm2; subst this
  have := numeral_unique hM hNE ht1 ht2; subst this
  exact add_unique hM hNE ha1 ha2

private theorem calcEc_exists (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) : ∃ res, CalcEc E a b res ∧ NatObject E res := by
  obtain ⟨p, hcp, _⟩ := cantor_exists hM hNE ha hb
  let q := mulV hM hNE (numV hM hNE 4) p
  have hq := mulV_nat hM hNE (numV_nat hM hNE 4) hcp.2.2.1
  exact ⟨addV hM hNE q (numV hM hNE 3),
    ⟨p, numV hM hNE 4, q, numV hM hNE 3, hcp, numV_numeral hM hNE 4,
      mulV_spec hM hNE (numV_nat hM hNE 4) hcp.2.2.1, numV_numeral hM hNE 3,
      addV_spec hM hNE hq (numV_nat hM hNE 3)⟩,
    addV_nat hM hNE hq (numV_nat hM hNE 3)⟩

private theorem calcEc_unique (hM : Model E) (hNE : Nonempty V) {a b r1 r2 : V}
    (h1 : CalcEc E a b r1) (h2 : CalcEc E a b r2) : r1 = r2 := by
  rcases h1 with ⟨p1, f1, q1, t1, hc1, hf1, hm1, ht1, ha1⟩
  rcases h2 with ⟨p2, f2, q2, t2, hc2, hf2, hm2, ht2, ha2⟩
  have := cantor_unique hM hNE hc1 hc2; subst this
  have := numeral_unique hM hNE hf1 hf2; subst this
  have := mul_unique hM hNE hm1 hm2; subst this
  have := numeral_unique hM hNE ht1 ht2; subst this
  exact add_unique hM hNE ha1 ha2

private theorem calcNc_exists (hM : Model E) (hNE : Nonempty V) {b : V} (hb : NatObject E b) :
    ∃ res, CalcNc E b res ∧ NatObject E res := by
  obtain ⟨ic, hic, hicN⟩ := calcIc_exists hM hNE hb (numV_nat hM hNE 1)
  exact ⟨ic, ⟨numV hM hNE 1, numV_numeral hM hNE 1, hic⟩, hicN⟩

private theorem calcNc_unique (hM : Model E) (hNE : Nonempty V) {b r1 r2 : V}
    (h1 : CalcNc E b r1) (h2 : CalcNc E b r2) : r1 = r2 := by
  rcases h1 with ⟨o1, ho1, hi1⟩; rcases h2 with ⟨o2, ho2, hi2⟩
  have := numeral_unique hM hNE ho1 ho2; subst this
  exact calcIc_unique hM hNE hi1 hi2

private theorem calcRho8_exists (hM : Model E) (hNE : Nonempty V) {a b c u : V}
    (ha : NatObject E a) (hb : NatObject E b) (hc : NatObject E c) (hu : NatObject E u)
    (hle : E u a ∨ u = a) : ∃ res, CalcRho8 E a b c u res ∧ NatObject E res := by
  obtain ⟨i1, hi1, hi1N⟩ := calcIc_exists hM hNE hc hu
  obtain ⟨i2, hi2, hi2N⟩ := calcIc_exists hM hNE hi1N ha
  obtain ⟨i3, hi3, hi3N⟩ := calcIc_exists hM hNE ha hc
  obtain ⟨i4, hi4, hi4N⟩ := calcIc_exists hM hNE hb hc
  obtain ⟨i5, hi5, hi5N⟩ := calcIc_exists hM hNE hi3N hi4N
  obtain ⟨res, hres, hresN⟩ := calcIc_exists hM hNE hi2N hi5N
  exact ⟨res, ⟨ha, hb, hc, hu, hle, i1, i2, i3, i4, i5, hi1, hi2, hi3, hi4, hi5, hres⟩, hresN⟩

private theorem calcRho8_unique (hM : Model E) (hNE : Nonempty V) {a b c u r1 r2 : V}
    (h1 : CalcRho8 E a b c u r1) (h2 : CalcRho8 E a b c u r2) : r1 = r2 := by
  rcases h1 with ⟨_, _, _, _, _, i1, i2, i3, i4, i5, hi1, hi2, hi3, hi4, hi5, hr1⟩
  rcases h2 with ⟨_, _, _, _, _, j1, j2, j3, j4, j5, hj1, hj2, hj3, hj4, hj5, hr2⟩
  have := calcIc_unique hM hNE hi1 hj1; subst this
  have := calcIc_unique hM hNE hi2 hj2; subst this
  have := calcIc_unique hM hNE hi3 hj3; subst this
  have := calcIc_unique hM hNE hi4 hj4; subst this
  have := calcIc_unique hM hNE hi5 hj5; subst this
  exact calcIc_unique hM hNE hr1 hr2

private theorem calcHead1_exists (hM : Model E) (hNE : Nonempty V) {x y : V}
    (hx : NatObject E x) (hy : NatObject E y) : ∃ res, CalcHead1 E x y res ∧ NatObject E res := by
  obtain ⟨u1, hu1, hu1N⟩ := calcUc_exists hM hNE hy hx
  obtain ⟨n1, hn1, hn1N⟩ := calcNc_exists hM hNE hu1N
  obtain ⟨u2, hu2, hu2N⟩ := calcUc_exists hM hNE hy hn1N
  obtain ⟨n2, hn2, hn2N⟩ := calcNc_exists hM hNE hu2N
  obtain ⟨res, hres, hresN⟩ := calcIc_exists hM hNE hn2N hx
  exact ⟨res, ⟨hx, hy, u1, n1, u2, n2, hu1, hn1, hu2, hn2, hres⟩, hresN⟩

private theorem calcHead1_unique (hM : Model E) (hNE : Nonempty V) {x y r1 r2 : V}
    (h1 : CalcHead1 E x y r1) (h2 : CalcHead1 E x y r2) : r1 = r2 := by
  rcases h1 with ⟨_, _, u1, n1, u2, n2, hu1, hn1, hu2, hn2, hr1⟩
  rcases h2 with ⟨_, _, v1, m1, v2, m2, hv1, hm1, hv2, hm2, hr2⟩
  have := calcUc_unique hM hNE hu1 hv1; subst this
  have := calcNc_unique hM hNE hn1 hm1; subst this
  have := calcUc_unique hM hNE hu2 hv2; subst this
  have := calcNc_unique hM hNE hn2 hm2; subst this
  exact calcIc_unique hM hNE hr1 hr2

private theorem calcHead2_exists (hM : Model E) (hNE : Nonempty V) {x y z : V}
    (hx : NatObject E x) (hy : NatObject E y) (hz : NatObject E z) : ∃ res, CalcHead2 E x y z res ∧ NatObject E res := by
  obtain ⟨u1, hu1, hu1N⟩ := calcUc_exists hM hNE hz hx
  obtain ⟨u2, hu2, hu2N⟩ := calcUc_exists hM hNE hy hu1N
  obtain ⟨u3, hu3, hu3N⟩ := calcUc_exists hM hNE hy hx
  obtain ⟨u4, hu4, hu4N⟩ := calcUc_exists hM hNE hz hu3N
  obtain ⟨res, hres, hresN⟩ := calcIc_exists hM hNE hu2N hu4N
  exact ⟨res, ⟨hx, hy, hz, u1, u2, u3, u4, hu1, hu2, hu3, hu4, hres⟩, hresN⟩

private theorem calcHead2_unique (hM : Model E) (hNE : Nonempty V) {x y z r1 r2 : V}
    (h1 : CalcHead2 E x y z r1) (h2 : CalcHead2 E x y z r2) : r1 = r2 := by
  rcases h1 with ⟨_, _, _, u1, u2, u3, u4, hu1, hu2, hu3, hu4, hr1⟩
  rcases h2 with ⟨_, _, _, v1, v2, v3, v4, hv1, hv2, hv3, hv4, hr2⟩
  have := calcUc_unique hM hNE hu1 hv1; subst this
  have := calcUc_unique hM hNE hu2 hv2; subst this
  have := calcUc_unique hM hNE hu3 hv3; subst this
  have := calcUc_unique hM hNE hu4 hv4; subst this
  exact calcIc_unique hM hNE hr1 hr2

private theorem calcHead3_exists (hM : Model E) (hNE : Nonempty V) {x y z : V}
    (hx : NatObject E x) (hy : NatObject E y) (hz : NatObject E z) : ∃ res, CalcHead3 E x y z res ∧ NatObject E res := by
  obtain ⟨m1, hm1, hm1N⟩ := calcMc_exists hM hNE hx hy
  obtain ⟨e1, he1, he1N⟩ := calcEc_exists hM hNE hx hz
  obtain ⟨m2, hm2, hm2N⟩ := calcMc_exists hM hNE hz hy
  obtain ⟨i1, hi1, hi1N⟩ := calcIc_exists hM hNE he1N hm2N
  obtain ⟨res, hres, hresN⟩ := calcIc_exists hM hNE hm1N hi1N
  exact ⟨res, ⟨hx, hy, hz, m1, e1, m2, i1, hm1, he1, hm2, hi1, hres⟩, hresN⟩

private theorem calcHead3_unique (hM : Model E) (hNE : Nonempty V) {x y z r1 r2 : V}
    (h1 : CalcHead3 E x y z r1) (h2 : CalcHead3 E x y z r2) : r1 = r2 := by
  rcases h1 with ⟨_, _, _, m1, e1, m2, i1, hm1, he1, hm2, hi1, hr1⟩
  rcases h2 with ⟨_, _, _, n1, f1, n2, j1, hn1, hf1, hn2, hj1, hr2⟩
  have := calcMc_unique hM hNE hm1 hn1; subst this
  have := calcEc_unique hM hNE he1 hf1; subst this
  have := calcMc_unique hM hNE hm2 hn2; subst this
  have := calcIc_unique hM hNE hi1 hj1; subst this
  exact calcIc_unique hM hNE hr1 hr2

private theorem calcHead4_exists (hM : Model E) (hNE : Nonempty V) {x y z : V}
    (hx : NatObject E x) (hy : NatObject E y) (hz : NatObject E z) : ∃ res, CalcHead4 E x y z res ∧ NatObject E res := by
  obtain ⟨e1, he1, he1N⟩ := calcEc_exists hM hNE hx hy
  obtain ⟨m1, hm1, hm1N⟩ := calcMc_exists hM hNE hz hx
  obtain ⟨m2, hm2, hm2N⟩ := calcMc_exists hM hNE hz hy
  obtain ⟨i1, hi1, hi1N⟩ := calcIc_exists hM hNE hm1N hm2N
  obtain ⟨res, hres, hresN⟩ := calcIc_exists hM hNE he1N hi1N
  exact ⟨res, ⟨hx, hy, hz, e1, m1, m2, i1, he1, hm1, hm2, hi1, hres⟩, hresN⟩

private theorem calcHead4_unique (hM : Model E) (hNE : Nonempty V) {x y z r1 r2 : V}
    (h1 : CalcHead4 E x y z r1) (h2 : CalcHead4 E x y z r2) : r1 = r2 := by
  rcases h1 with ⟨_, _, _, e1, m1, m2, i1, he1, hm1, hm2, hi1, hr1⟩
  rcases h2 with ⟨_, _, _, f1, n1, n2, j1, hf1, hn1, hn2, hj1, hr2⟩
  have := calcEc_unique hM hNE he1 hf1; subst this
  have := calcMc_unique hM hNE hm1 hn1; subst this
  have := calcMc_unique hM hNE hm2 hn2; subst this
  have := calcIc_unique hM hNE hi1 hj1; subst this
  exact calcIc_unique hM hNE hr1 hr2

private theorem calcHead5_exists (hM : Model E) (hNE : Nonempty V) {x y : V}
    (hx : NatObject E x) (hy : NatObject E y) : ∃ res, CalcHead5 E x y res ∧ NatObject E res := by
  obtain ⟨e1, he1, he1N⟩ := calcEc_exists hM hNE hx hy
  obtain ⟨n1, hn1, hn1N⟩ := calcNc_exists hM hNE he1N
  obtain ⟨u1, hu1, hu1N⟩ := calcUc_exists hM hNE hy hn1N
  obtain ⟨res, hres, hresN⟩ := calcNc_exists hM hNE hu1N
  exact ⟨res, ⟨hx, hy, e1, n1, u1, he1, hn1, hu1, hres⟩, hresN⟩

private theorem calcHead5_unique (hM : Model E) (hNE : Nonempty V) {x y r1 r2 : V}
    (h1 : CalcHead5 E x y r1) (h2 : CalcHead5 E x y r2) : r1 = r2 := by
  rcases h1 with ⟨_, _, e1, n1, u1, he1, hn1, hu1, hr1⟩
  rcases h2 with ⟨_, _, f1, m1, v1, hf1, hm1, hv1, hr2⟩
  have := calcEc_unique hM hNE he1 hf1; subst this
  have := calcNc_unique hM hNE hn1 hm1; subst this
  have := calcUc_unique hM hNE hu1 hv1; subst this
  exact calcNc_unique hM hNE hr1 hr2

private theorem calcHead6_exists (hM : Model E) (hNE : Nonempty V) {x y z : V}
    (hx : NatObject E x) (hy : NatObject E y) (hz : NatObject E z) : ∃ res, CalcHead6 E x y z res ∧ NatObject E res := by
  obtain ⟨u1, hu1, hu1N⟩ := calcUc_exists hM hNE hy hz
  obtain ⟨i1, hi1, hi1N⟩ := calcIc_exists hM hNE hz hx
  obtain ⟨u2, hu2, hu2N⟩ := calcUc_exists hM hNE hy hi1N
  obtain ⟨u3, hu3, hu3N⟩ := calcUc_exists hM hNE hy hx
  obtain ⟨i2, hi2, hi2N⟩ := calcIc_exists hM hNE hu2N hu3N
  obtain ⟨res, hres, hresN⟩ := calcIc_exists hM hNE hu1N hi2N
  exact ⟨res, ⟨hx, hy, hz, u1, i1, u2, u3, i2, hu1, hi1, hu2, hu3, hi2, hres⟩, hresN⟩

private theorem calcHead6_unique (hM : Model E) (hNE : Nonempty V) {x y z r1 r2 : V}
    (h1 : CalcHead6 E x y z r1) (h2 : CalcHead6 E x y z r2) : r1 = r2 := by
  rcases h1 with ⟨_, _, _, u1, i1, u2, u3, i2, hu1, hi1, hu2, hu3, hi2, hr1⟩
  rcases h2 with ⟨_, _, _, v1, j1, v2, v3, j2, hv1, hj1, hv2, hv3, hj2, hr2⟩
  have := calcUc_unique hM hNE hu1 hv1; subst this
  have := calcIc_unique hM hNE hi1 hj1; subst this
  have := calcUc_unique hM hNE hu2 hv2; subst this
  have := calcUc_unique hM hNE hu3 hv3; subst this
  have := calcIc_unique hM hNE hi2 hj2; subst this
  exact calcIc_unique hM hNE hr1 hr2

private theorem calcGateG_exists (hM : Model E) (hNE : Nonempty V) {a b c : V}
    (ha : NatObject E a) (hb : NatObject E b) (hc : NatObject E c) : ∃ res, CalcGateG E a b c res ∧ NatObject E res := by
  obtain ⟨m1, hm1, hm1N⟩ := calcMc_exists hM hNE hc hb
  obtain ⟨m2, hm2, hm2N⟩ := calcMc_exists hM hNE hc ha
  obtain ⟨i1, hi1, hi1N⟩ := calcIc_exists hM hNE hm1N hm2N
  obtain ⟨subBA, hsubBA, hsubBAN⟩ := calcUc_exists hM hNE hc hi1N
  obtain ⟨m3, hm3, hm3N⟩ := calcMc_exists hM hNE ha hc
  obtain ⟨n1, hn1, hn1N⟩ := calcNc_exists hM hNE hm3N
  obtain ⟨i2, hi2, hi2N⟩ := calcIc_exists hM hNE hc hn1N
  obtain ⟨u1, hu1, hu1N⟩ := calcUc_exists hM hNE ha hi2N
  obtain ⟨stepEx, hstepEx, hstepExN⟩ := calcNc_exists hM hNE hu1N
  obtain ⟨i3, hi3, hi3N⟩ := calcIc_exists hM hNE hc hstepExN
  obtain ⟨stepAll, hstepAll, hstepAllN⟩ := calcUc_exists hM hNE ha hi3N
  obtain ⟨i4, hi4, hi4N⟩ := calcIc_exists hM hNE hsubBAN hstepAllN
  obtain ⟨u2, hu2, hu2N⟩ := calcUc_exists hM hNE hb hi4N
  obtain ⟨n2, hn2, hn2N⟩ := calcNc_exists hM hNE hu2N
  obtain ⟨i5, hi5, hi5N⟩ := calcIc_exists hM hNE hc hn2N
  obtain ⟨u3, hu3, hu3N⟩ := calcUc_exists hM hNE hb hi5N
  obtain ⟨hullBody, hhullBody, hhullBodyN⟩ := calcNc_exists hM hNE hu3N
  obtain ⟨i6, hi6, hi6N⟩ := calcIc_exists hM hNE hm3N hhullBodyN
  obtain ⟨lhs, hlhs, hlhsN⟩ := calcUc_exists hM hNE ha hi6N
  obtain ⟨i7, hi7, hi7N⟩ := calcIc_exists hM hNE hc hm3N
  obtain ⟨rhs, hrhs, hrhsN⟩ := calcNc_exists hM hNE hi7N
  obtain ⟨res, hres, hresN⟩ := calcIc_exists hM hNE hlhsN hrhsN
  exact ⟨res, ⟨ha, hb, hc, m1, m2, i1, subBA, m3, n1, i2, u1, stepEx, i3, stepAll, i4, u2, n2, i5, u3, hullBody, i6, lhs, i7, rhs,
    hm1, hm2, hi1, hsubBA, hm3, hn1, hi2, hu1, hstepEx, hi3, hstepAll, hi4, hu2, hn2, hi5, hu3, hhullBody, hi6, hlhs, hi7, hrhs, hres⟩, hresN⟩

private theorem calcGateF_exists (hM : Model E) (hNE : Nonempty V) {a b c : V}
    (ha : NatObject E a) (hb : NatObject E b) (hc : NatObject E c) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ res, CalcGateF E a b c res ∧ NatObject E res := by
  obtain ⟨e1, he1, he1N⟩ := calcEc_exists hM hNE ha hb
  obtain ⟨ue1, hue1, hue1N⟩ := calcUc_exists hM hNE hc he1N
  obtain ⟨delta, hdelta, hdeltaN⟩ := calcIc_exists hM hNE he1N hue1N
  obtain ⟨m1, hm1, hm1N⟩ := calcMc_exists hM hNE ha hb
  obtain ⟨um1, hum1, hum1N⟩ := calcUc_exists hM hNE hc hm1N
  obtain ⟨vax, hvax, hvaxN⟩ := calcIc_exists hM hNE hm1N hum1N
  obtain ⟨g, hg, hgN⟩ := calcGateG_exists hM hNE ha hb hc
  obtain ⟨q, hq, hqN⟩ := calcUc_exists hM hNE hc hgN
  obtain ⟨iq, hiq, hiqN⟩ := calcIc_exists hM hNE hvaxN hqN
  obtain ⟨idq, hidq, hidqN⟩ := calcIc_exists hM hNE hdeltaN hiqN
  obtain ⟨res, hres, hresN⟩ := calcNc_exists hM hNE hidqN
  exact ⟨res, ⟨ha, hb, hc, hca, hcb, e1, ue1, delta, m1, um1, vax, g, q, iq, idq,
    he1, hue1, hdelta, hm1, hum1, hvax, hg, hq, hiq, hidq, hres⟩, hresN⟩

/-! ### Part 2: Syntactic Formulas for Internal TM Reachability, Halting & Frames -/

private def fNumeralBin (k x : Nat) : Formula :=
  if k = 0 then fEmpty x
  else if k = 1 then .ex (.and (fEmpty 0) (fSucc 0 (x + 1)))
  else if k % 2 = 0 then .ex (.and (fNumeralBin (k / 2) 0) (fAdd 0 0 (x + 1)))
  else .ex (.ex (.and (fNumeralBin (k / 2) 1) (.and (fAdd 1 1 0) (fSucc 0 (x + 2)))))
termination_by k

private theorem bound_fNumeralBin (k x n : Nat) (hx : x < n) : Bound (fNumeralBin k x) n := by
  unfold fNumeralBin
  split
  · exact bound_fEmpty hx
  · split
    · exact ⟨bound_fEmpty (by omega), bound_fSucc (by omega) (by omega)⟩
    · split
      · exact ⟨bound_fNumeralBin (k / 2) 0 (n + 1) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩
      · exact ⟨bound_fNumeralBin (k / 2) 1 (n + 2) (by omega), ⟨bound_fAdd (by omega) (by omega) (by omega), bound_fSucc (by omega) (by omega)⟩⟩
termination_by k

private theorem eval_fNumeralBin (hM : Model E) (hNE : Nonempty V) (k x : Nat) (s : Nat → V) :
    eval E (fNumeralBin k x) s ↔ Numeral E k (s x) := by
  unfold fNumeralBin
  split
  · next h0 => subst h0; exact Iff.rfl
  · next h0 =>
    split
    · next h1 =>
      subst h1
      exact ⟨fun ⟨y, hy, hs⟩ => ⟨y, hy, (eval_fSucc _ _ _).mp hs⟩,
             fun ⟨y, hy, hs⟩ => ⟨y, hy, (eval_fSucc _ _ _).mpr hs⟩⟩
    · next h1 =>
      split
      · next hev =>
        have hk : k / 2 + k / 2 = k := by omega
        constructor
        · rintro ⟨y, hy, hadd⟩
          have hy' : Numeral E (k / 2) y := (eval_fNumeralBin hM hNE (k / 2) 0 _).mp hy
          have hyeq : y = numV hM hNE (k / 2) := numeral_unique hM hNE hy' (numV_numeral hM hNE (k / 2))
          have hadd' : Add E y y (s x) := (eval_fAdd _ _ _ _).mp hadd
          rw [hyeq] at hadd'
          have hsx : s x = numV hM hNE k := ((add_iff_eq hM hNE (numV_nat hM hNE _) (numV_nat hM hNE _)).mp hadd').trans
            (by rw [addV_numV, hk])
          rw [hsx]; exact numV_numeral hM hNE k
        · intro hnk
          have hsx : s x = numV hM hNE k := numeral_unique hM hNE hnk (numV_numeral hM hNE k)
          refine ⟨numV hM hNE (k / 2), (eval_fNumeralBin hM hNE (k / 2) 0 _).mpr (numV_numeral hM hNE (k / 2)),
            (eval_fAdd _ _ _ _).mpr ?_⟩
          dsimp only [pushValue]
          have hspec := addV_spec hM hNE (numV_nat hM hNE (k / 2)) (numV_nat hM hNE (k / 2))
          rw [addV_numV, hk, ← hsx] at hspec; exact hspec
      · next hodd =>
        have hk : k / 2 + k / 2 + 1 = k := by omega
        constructor
        · rintro ⟨y, z, hy, hadd, hsucc⟩
          have hy' : Numeral E (k / 2) y := (eval_fNumeralBin hM hNE (k / 2) 1 _).mp hy
          have hyeq : y = numV hM hNE (k / 2) := numeral_unique hM hNE hy' (numV_numeral hM hNE (k / 2))
          have hadd' : Add E y y z := (eval_fAdd _ _ _ _).mp hadd
          rw [hyeq] at hadd'
          have hzeq : z = numV hM hNE (k / 2 + k / 2) := ((add_iff_eq hM hNE (numV_nat hM hNE _) (numV_nat hM hNE _)).mp hadd').trans (addV_numV hM hNE _ _)
          have hsucc' : Succ E z (s x) := (eval_fSucc _ _ _).mp hsucc
          rw [hzeq] at hsucc'
          have hnum : succV hM hNE (numV hM hNE (k / 2 + k / 2)) = numV hM hNE k := by
            have : numV hM hNE (k / 2 + k / 2 + 1) = succV hM hNE (numV hM hNE (k / 2 + k / 2)) := rfl
            rw [← this, hk]
          have hsx : s x = numV hM hNE k := (succ_unique hM hNE hsucc' (succV_spec hM hNE _)).trans hnum
          rw [hsx]; exact numV_numeral hM hNE k
        · intro hnk
          have hsx : s x = numV hM hNE k := numeral_unique hM hNE hnk (numV_numeral hM hNE k)
          refine ⟨numV hM hNE (k / 2), numV hM hNE (k / 2 + k / 2),
            (eval_fNumeralBin hM hNE (k / 2) 1 _).mpr (numV_numeral hM hNE (k / 2)),
            (eval_fAdd _ _ _ _).mpr (by
              dsimp only [pushValue]
              have hspec := addV_spec hM hNE (numV_nat hM hNE (k / 2)) (numV_nat hM hNE (k / 2))
              rwa [addV_numV] at hspec),
            (eval_fSucc _ _ _).mpr (by
              dsimp only [pushValue]
              have hspec := succV_spec hM hNE (numV hM hNE (k / 2 + k / 2))
              have hnum : succV hM hNE (numV hM hNE (k / 2 + k / 2)) = numV hM hNE k := by
                have : numV hM hNE (k / 2 + k / 2 + 1) = succV hM hNE (numV hM hNE (k / 2 + k / 2)) := rfl
                rw [← this, hk]
              rw [hnum, ← hsx] at hspec; exact hspec)⟩
termination_by k

private def fBitCons (bit : Bool) (x y : Nat) : Formula :=
  .ex (.ex (.ex (.and (fNumeral (if bit then 1 else 0) 2)
    (.and (fNumeral 2 1) (.and (fMul 1 (x + 3) 0) (fAdd 2 0 (y + 3)))))))

private theorem bound_fBitCons (bit : Bool) {x y n : Nat} (hx : x < n) (hy : y < n) : Bound (fBitCons bit x y) n :=
  ⟨bound_fNumeral (by omega), ⟨bound_fNumeral (by omega), ⟨bound_fMul (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩⟩

private theorem eval_fBitCons (bit : Bool) (x y : Nat) (s : Nat → V) :
    eval E (fBitCons bit x y) s ↔ BitCons E bit (s x) (s y) := by
  constructor
  · rintro ⟨b, two, tw, h1, h2, h3, h4⟩
    exact ⟨b, two, tw, (eval_fNumeral _ _ _).mp h1, (eval_fNumeral _ _ _).mp h2, (eval_fMul _ _ _ _).mp h3, (eval_fAdd _ _ _ _).mp h4⟩
  · rintro ⟨b, two, tw, h1, h2, h3, h4⟩
    exact ⟨b, two, tw, (eval_fNumeral _ _ _).mpr h1, (eval_fNumeral _ _ _).mpr h2, (eval_fMul _ _ _ _).mpr h3, (eval_fAdd _ _ _ _).mpr h4⟩

private def fConfCode (q l r c : Nat) : Formula :=
  .ex (.and (fCantor (l + 1) (r + 1) 0) (fCantor (q + 1) 0 (c + 1)))

private theorem bound_fConfCode {q l r c n : Nat} (hq : q < n) (hl : l < n) (hr : r < n) (hc : c < n) :
    Bound (fConfCode q l r c) n :=
  ⟨bound_fCantor (by omega) (by omega) (by omega), bound_fCantor (by omega) (by omega) (by omega)⟩

private theorem eval_fConfCode (q l r c : Nat) (s : Nat → V) :
    eval E (fConfCode q l r c) s ↔ NumericConfCode E ⟨s q, s l, s r⟩ (s c) :=
  ⟨fun ⟨lr, h1, h2⟩ => ⟨lr, (eval_fCantor _ _ _ _).mp h1, (eval_fCantor _ _ _ _).mp h2⟩,
   fun ⟨lr, h1, h2⟩ => ⟨lr, (eval_fCantor _ _ _ _).mpr h1, (eval_fCantor _ _ _ _).mpr h2⟩⟩

private def fTerminal (q : Nat) : Formula :=
  .ex (.and (fNumeralBin 207 0) (.or (.eq (q + 1) 0) (.mem 0 (q + 1))))

private theorem bound_fTerminal {q n : Nat} (hq : q < n) : Bound (fTerminal q) n :=
  ⟨bound_fNumeralBin 207 0 (n + 1) (by omega), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩

private theorem eval_fTerminal (hM : Model E) (hNE : Nonempty V) (q : Nat) (s : Nat → V)
    (hqN : NatObject E (s q)) : eval E (fTerminal q) s ↔ ∀ i : Fin 207, ¬ Numeral E i.val (s q) := by
  constructor
  · rintro ⟨n207, h207, hge⟩ i hni
    have h207' : Numeral E 207 n207 := (eval_fNumeralBin hM hNE 207 0 _).mp h207
    have hn207 : n207 = numV hM hNE 207 := numeral_unique hM hNE h207' (numV_numeral hM hNE 207)
    have hsq : s q = numV hM hNE i.val := numeral_unique hM hNE hni (numV_numeral hM hNE i.val)
    have hlt : E (numV hM hNE i.val) (numV hM hNE 207) := numV_lt_of_lt hM hNE i.isLt
    dsimp only [eval, pushValue] at hge
    rw [hn207, hsq] at hge
    rcases hge with heq | hgt
    · exact mem_irrefl hM hNE _ (heq ▸ hlt)
    · exact mem_asymm hM hNE hlt hgt
  · intro hterm
    refine ⟨numV hM hNE 207, (eval_fNumeralBin hM hNE 207 0 _).mpr (numV_numeral hM hNE 207), ?_⟩
    dsimp only [eval, pushValue]
    rcases nat_trichotomy hM hNE (s q) hqN (numV hM hNE 207) (numV_nat hM hNE 207) with hlt | heq | hgt
    · obtain ⟨i, hi, heqi⟩ := (mem_numV_iff hM hNE 207 (s q)).mp hlt
      exact False.elim (hterm ⟨i, hi⟩ (heqi ▸ numV_numeral hM hNE i))
    · exact Or.inl heq
    · exact Or.inr hgt

private def fRowBranch (read : Bool) (row : PalomarZF207History.Row) (sl sr tq tl tr : Nat) : Formula :=
  match row with
  | none => .bot
  | some (w, true, next) =>
    .ex (.and (fBitCons read 0 (sr + 1)) (.and (fNumeralBin next (tq + 1))
      (.and (fBitCons w (sl + 1) (tl + 1)) (.eq (tr + 1) 0))))
  | some (w, false, next) =>
    .ex (.ex (.ex (.and (fBitCons read 2 (sr + 3)) (.and (fNumeralBin next (tq + 3))
      (.and (fBitCons w 2 0) (.and (.eq (tl + 3) 1)
        (.or (.and (fBitCons false 1 (sl + 3)) (fBitCons false 0 (tr + 3)))
             (.and (fBitCons true 1 (sl + 3)) (fBitCons true 0 (tr + 3))))))))))

private theorem bound_fRowBranch (read : Bool) (row : PalomarZF207History.Row) {sl sr tq tl tr n : Nat}
    (hsl : sl < n) (hsr : sr < n) (htq : tq < n) (htl : tl < n) (htr : tr < n) :
    Bound (fRowBranch read row sl sr tq tl tr) n := by
  cases row with
  | none => trivial
  | some x =>
    rcases x with ⟨w, d, next⟩
    cases d with
    | true => exact ⟨bound_fBitCons _ (by omega) (by omega), ⟨bound_fNumeralBin _ _ _ (by omega), ⟨bound_fBitCons _ (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩
    | false => exact ⟨bound_fBitCons _ (by omega) (by omega), ⟨bound_fNumeralBin _ _ _ (by omega), ⟨bound_fBitCons _ (by omega) (by omega),
      ⟨⟨by omega, by omega⟩, ⟨⟨bound_fBitCons _ (by omega) (by omega), bound_fBitCons _ (by omega) (by omega)⟩,
        ⟨bound_fBitCons _ (by omega) (by omega), bound_fBitCons _ (by omega) (by omega)⟩⟩⟩⟩⟩⟩

private theorem eval_fRowBranch (hM : Model E) (hNE : Nonempty V) (read : Bool) (row : PalomarZF207History.Row)
    (sq sl sr tq tl tr : Nat) (s : Nat → V) :
    eval E (fRowBranch read row sl sr tq tl tr) s ↔
      ∃ w d next, row = some (w, d, next) ∧
        Move E read w d next ⟨s sq, s sl, s sr⟩ ⟨s tq, s tl, s tr⟩ := by
  cases row with
  | none => exact ⟨False.elim, fun ⟨_, _, _, h, _⟩ => by contradiction⟩
  | some x =>
    rcases x with ⟨w, d, next⟩
    cases d with
    | true =>
      constructor
      · rintro ⟨r, h1, h2, h3, h4⟩
        have h1' : BitCons E read r (s sr) := (eval_fBitCons _ _ _ _).mp h1
        have h2' : Numeral E next (s tq) := (eval_fNumeralBin hM hNE next (tq + 1) _).mp h2
        have h3' : BitCons E w (s sl) (s tl) := (eval_fBitCons w (sl + 1) (tl + 1) _).mp h3
        exact ⟨w, true, next, rfl, r, h1', h2', h3', h4⟩
      · rintro ⟨w', d', next', heq, hmv⟩
        injection heq with h1'; cases h1'
        rcases hmv with ⟨r, h1, h2, h3, h4⟩
        exact ⟨r, (eval_fBitCons _ _ _ _).mpr h1, (eval_fNumeralBin hM hNE _ _ _).mpr h2,
          (eval_fBitCons _ _ _ _).mpr h3, h4⟩
    | false =>
      constructor
      · rintro ⟨r, l, mid, h1, h2, h3, h4, (⟨h5, h6⟩ | ⟨h5, h6⟩)⟩
        · have h1' : BitCons E read r (s sr) := (eval_fBitCons _ _ _ _).mp h1
          have h2' : Numeral E next (s tq) := (eval_fNumeralBin hM hNE next (tq + 3) _).mp h2
          have h3' : BitCons E w r mid := (eval_fBitCons _ _ _ _).mp h3
          have h5' : BitCons E false l (s sl) := (eval_fBitCons _ _ _ _).mp h5
          have h6' : BitCons E false mid (s tr) := (eval_fBitCons _ _ _ _).mp h6
          exact ⟨w, false, next, rfl, r, h1', h2', l, false, mid, h5', h4, h3', h6'⟩
        · have h1' : BitCons E read r (s sr) := (eval_fBitCons _ _ _ _).mp h1
          have h2' : Numeral E next (s tq) := (eval_fNumeralBin hM hNE next (tq + 3) _).mp h2
          have h3' : BitCons E w r mid := (eval_fBitCons _ _ _ _).mp h3
          have h5' : BitCons E true l (s sl) := (eval_fBitCons _ _ _ _).mp h5
          have h6' : BitCons E true mid (s tr) := (eval_fBitCons _ _ _ _).mp h6
          exact ⟨w, false, next, rfl, r, h1', h2', l, true, mid, h5', h4, h3', h6'⟩
      · rintro ⟨w', d', next', heq, hmv⟩
        injection heq with h1'; cases h1'
        rcases hmv with ⟨r, h1, h2, l, bit, mid, h5, h4, h3, h6⟩
        refine ⟨r, l, mid, (eval_fBitCons _ _ _ _).mpr h1, (eval_fNumeralBin hM hNE _ _ _).mpr h2,
          (eval_fBitCons _ _ _ _).mpr h3, h4, ?_⟩
        cases bit with
        | false => exact Or.inl ⟨(eval_fBitCons _ _ _ _).mpr h5, (eval_fBitCons _ _ _ _).mpr h6⟩
        | true => exact Or.inr ⟨(eval_fBitCons _ _ _ _).mpr h5, (eval_fBitCons _ _ _ _).mpr h6⟩

private def fRows (sq sl sr tq tl tr : Nat) : Nat → List (PalomarZF207History.Row × PalomarZF207History.Row) → Formula
  | _, [] => .bot
  | q, (r0, r1) :: rest =>
    .or (.and (fNumeralBin q sq) (.or (fRowBranch false r0 sl sr tq tl tr) (fRowBranch true r1 sl sr tq tl tr)))
        (fRows sq sl sr tq tl tr (q + 1) rest)

private theorem bound_fRows (sq sl sr tq tl tr : Nat) : ∀ (q : Nat) (rows : List (PalomarZF207History.Row × PalomarZF207History.Row)) {n : Nat},
    sq < n → sl < n → sr < n → tq < n → tl < n → tr < n → Bound (fRows sq sl sr tq tl tr q rows) n
  | _, [], _, _, _, _, _, _, _ => trivial
  | q, (r0, r1) :: rest, n, h1, h2, h3, h4, h5, h6 =>
    ⟨⟨bound_fNumeralBin q sq n h1, ⟨bound_fRowBranch false r0 h2 h3 h4 h5 h6, bound_fRowBranch true r1 h2 h3 h4 h5 h6⟩⟩,
     bound_fRows sq sl sr tq tl tr (q + 1) rest h1 h2 h3 h4 h5 h6⟩

private theorem eval_fRows (hM : Model E) (hNE : Nonempty V) (sq sl sr tq tl tr : Nat) (s : Nat → V) :
    ∀ (q0 : Nat) (rows : List (PalomarZF207History.Row × PalomarZF207History.Row)),
      eval E (fRows sq sl sr tq tl tr q0 rows) s ↔
        ∃ i, i < rows.length ∧ Numeral E (q0 + i) (s sq) ∧
          ∃ read w d next,
            (if read then (rows.getD i (none, none)).2 else (rows.getD i (none, none)).1) = some (w, d, next) ∧
            Move E read w d next ⟨s sq, s sl, s sr⟩ ⟨s tq, s tl, s tr⟩
  | _, [] => ⟨False.elim, fun ⟨_, hi, _⟩ => by simp at hi⟩
  | q0, (r0, r1) :: rest => by
    constructor
    · rintro (⟨hq0, hbr⟩ | hrest)
      · refine ⟨0, by simp, (eval_fNumeralBin hM hNE q0 sq s).mp hq0, ?_⟩
        rcases hbr with h0 | h1
        · obtain ⟨w, d, next, hr, hm⟩ := (eval_fRowBranch hM hNE false r0 sq sl sr tq tl tr s).mp h0
          exact ⟨false, w, d, next, by simpa [List.getD] using hr, hm⟩
        · obtain ⟨w, d, next, hr, hm⟩ := (eval_fRowBranch hM hNE true r1 sq sl sr tq tl tr s).mp h1
          exact ⟨true, w, d, next, by simpa [List.getD] using hr, hm⟩
      · obtain ⟨i, hi, hqi, read, w, d, next, hr, hm⟩ := (eval_fRows hM hNE sq sl sr tq tl tr s (q0 + 1) rest).mp hrest
        refine ⟨i + 1, by simp; omega, by rwa [show q0 + (i + 1) = q0 + 1 + i by omega], read, w, d, next, ?_, hm⟩
        simpa [List.getD] using hr
    · rintro ⟨i, hi, hqi, read, w, d, next, hr, hm⟩
      cases i with
      | zero =>
        left
        refine ⟨(eval_fNumeralBin hM hNE q0 sq s).mpr (by simpa using hqi), ?_⟩
        cases read with
        | false => exact Or.inl ((eval_fRowBranch hM hNE false r0 sq sl sr tq tl tr s).mpr ⟨w, d, next, by simpa [List.getD] using hr, hm⟩)
        | true => exact Or.inr ((eval_fRowBranch hM hNE true r1 sq sl sr tq tl tr s).mpr ⟨w, d, next, by simpa [List.getD] using hr, hm⟩)
      | succ j =>
        right
        apply (eval_fRows hM hNE sq sl sr tq tl tr s (q0 + 1) rest).mpr
        refine ⟨j, by simp at hi; omega, by rwa [show q0 + 1 + j = q0 + (j + 1) by omega], read, w, d, next, ?_, hm⟩
        simpa [List.getD] using hr

private theorem literalRows_len : literalRows.length = 207 := by
  have h1 : (literalRows.drop 100).length = 107 := rfl
  rw [List.length_drop] at h1; omega

private def fNumericStep (b a : Nat) : Formula :=
  .ex (.ex (.ex (.ex (.ex (.ex
    (.and (fConfCode 5 4 3 (b + 6))
      (.and (fConfCode 2 1 0 (a + 6))
        (.and (fNatObject 5) (.and (fNatObject 4) (.and (fNatObject 3)
          (.and (fNatObject 2) (.and (fNatObject 1) (.and (fNatObject 0)
            (fRows 5 4 3 2 1 0 0 literalRows))))))))))))))

private theorem bound_fNumericStep {b a n : Nat} (hb : b < n) (ha : a < n) : Bound (fNumericStep b a) n :=
  ⟨bound_fConfCode (by omega) (by omega) (by omega) (by omega),
    ⟨bound_fConfCode (by omega) (by omega) (by omega) (by omega),
      ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega),
        ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega),
          bound_fRows 5 4 3 2 1 0 0 literalRows (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩

private theorem eval_fNumericStep (hM : Model E) (hNE : Nonempty V) (b a : Nat) (s : Nat → V) :
    eval E (fNumericStep b a) s ↔ NumericStep E (s b) (s a) := by
  constructor
  · rintro ⟨sq, sl, sr, tq, tl, tr, hc1, hc2, h1, h2, h3, h4, h5, h6, hrows⟩
    obtain ⟨i, hi, hqi, read, w, d, next, hr, hm⟩ := (eval_fRows hM hNE 5 4 3 2 1 0 _ 0 literalRows).mp hrows
    rw [literalRows_len] at hi
    exact ⟨⟨sq, sl, sr⟩, ⟨tq, tl, tr⟩, (eval_fConfCode _ _ _ _ _).mp hc1, (eval_fConfCode _ _ _ _ _).mp hc2,
      ⟨(eval_fNatObject _ _).mp h1, (eval_fNatObject _ _).mp h2, (eval_fNatObject _ _).mp h3⟩,
      ⟨(eval_fNatObject _ _).mp h4, (eval_fNatObject _ _).mp h5, (eval_fNatObject _ _).mp h6⟩,
      ⟨i, hi⟩, by dsimp only [pushValue] at hqi; simpa using hqi, read, w, d, next, hr, hm⟩
  · rintro ⟨⟨sq, sl, sr⟩, ⟨tq, tl, tr⟩, hc1, hc2, ⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, q, hqi, read, w, d, next, hr, hm⟩
    refine ⟨sq, sl, sr, tq, tl, tr, (eval_fConfCode _ _ _ _ _).mpr hc1, (eval_fConfCode _ _ _ _ _).mpr hc2,
      (eval_fNatObject _ _).mpr h1, (eval_fNatObject _ _).mpr h2, (eval_fNatObject _ _).mpr h3,
      (eval_fNatObject _ _).mpr h4, (eval_fNatObject _ _).mpr h5, (eval_fNatObject _ _).mpr h6, ?_⟩
    apply (eval_fRows hM hNE 5 4 3 2 1 0 _ 0 literalRows).mpr
    exact ⟨q.val, by rw [literalRows_len]; exact q.isLt, by dsimp only [pushValue]; simpa using hqi, read, w, d, next, hr, hm⟩

attribute [irreducible] fNumericStep

private def fInternalReach (c1 c2 : Nat) : Formula :=
  .ex (.ex (.ex (.ex
    (.and (fNatObject 3) (.and (fNatObject (c1 + 4)) (.and (fNatObject (c2 + 4))
      (.and (fEmpty 2) (.and (fSucc 3 1) (.and (fFunctionOn 0 1)
        (.and (fAt 0 2 (c1 + 4)) (.and (fAt 0 3 (c2 + 4))
          (.and (.all (.all (.imp (.mem 1 3) (.imp (fAt 2 1 0) (fNatObject 0)))))
            (.all (.imp (.mem 0 4)
              (.ex (.ex (.ex (.and (fSucc 3 2) (.and (fAt 4 3 1) (.and (fAt 4 2 0) (fNumericStep 1 0)))))))))))))))))))))

private theorem bound_fInternalReach {c1 c2 n : Nat} (h1 : c1 < n) (h2 : c2 < n) : Bound (fInternalReach c1 c2) n :=
  ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega),
    ⟨bound_fEmpty (by omega), ⟨bound_fSucc (by omega) (by omega), ⟨bound_fFunctionOn (by omega) (by omega),
      ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
        ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
         ⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
          ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNumericStep (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem eval_fInternalReach (hM : Model E) (hNE : Nonempty V) (c1 c2 : Nat) (s : Nat → V) :
    eval E (fInternalReach c1 c2) s ↔ InternalReach E (s c1) (s c2) := by
  constructor
  · rintro ⟨n, z, dom, f, hn, hc1, hc2, hz, hdom, hfun, hf0, hfn, hnat, hstep⟩
    refine ⟨n, (eval_fNatObject _ _).mp hn, (eval_fNatObject _ _).mp hc1, (eval_fNatObject _ _).mp hc2,
      z, dom, f, hz, (eval_fSucc _ _ _).mp hdom, (eval_fFunctionOn _ _ _).mp hfun,
      (eval_fAt _ _ _ _).mp hf0, (eval_fAt _ _ _ _).mp hfn,
      fun i x hi hix => (eval_fNatObject _ _).mp (hnat i x hi ((eval_fAt _ _ _ _).mpr hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
    exact ⟨j, x, y, (eval_fSucc _ _ _).mp h1, (eval_fAt _ _ _ _).mp h2, (eval_fAt _ _ _ _).mp h3, (eval_fNumericStep hM hNE _ _ _).mp h4⟩
  · rintro ⟨n, hn, hc1, hc2, z, dom, f, hz, hdom, hfun, hf0, hfn, hnat, hstep⟩
    refine ⟨n, z, dom, f, (eval_fNatObject _ _).mpr hn, (eval_fNatObject _ _).mpr hc1, (eval_fNatObject _ _).mpr hc2,
      hz, (eval_fSucc _ _ _).mpr hdom, (eval_fFunctionOn _ _ _).mpr hfun,
      (eval_fAt _ _ _ _).mpr hf0, (eval_fAt _ _ _ _).mpr hfn,
      fun i x hi hix => (eval_fNatObject _ _).mpr (hnat i x hi ((eval_fAt _ _ _ _).mp hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
    exact ⟨j, x, y, (eval_fSucc _ _ _).mpr h1, (eval_fAt _ _ _ _).mpr h2, (eval_fAt _ _ _ _).mpr h3, (eval_fNumericStep hM hNE _ _ _).mpr h4⟩

private def fInternalHaltsFrom (c : Nat) : Formula :=
  .ex (.ex (.ex (.ex
    (.and (fInternalReach (c + 4) 3)
      (.and (fConfCode 2 1 0 3)
        (.and (fNatObject 2) (.and (fNatObject 1) (.and (fNatObject 0) (fTerminal 2)))))))))

private theorem bound_fInternalHaltsFrom {c n : Nat} (hc : c < n) : Bound (fInternalHaltsFrom c) n :=
  ⟨bound_fInternalReach (by omega) (by omega), ⟨bound_fConfCode (by omega) (by omega) (by omega) (by omega),
    ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega), bound_fTerminal (by omega)⟩⟩⟩⟩⟩

private theorem eval_fInternalHaltsFrom (hM : Model E) (hNE : Nonempty V) (c : Nat) (s : Nat → V) :
    eval E (fInternalHaltsFrom c) s ↔ InternalHaltsFrom E (s c) := by
  constructor
  · rintro ⟨c', tq, tl, tr, hr, hc, hq, hl, hrN, ht⟩
    have hqN : NatObject E tq := (eval_fNatObject _ _).mp hq
    exact ⟨c', ⟨tq, tl, tr⟩, (eval_fInternalReach hM hNE _ _ _).mp hr, (eval_fConfCode _ _ _ _ _).mp hc,
      ⟨hqN, (eval_fNatObject _ _).mp hl, (eval_fNatObject _ _).mp hrN⟩,
      (eval_fTerminal hM hNE 2 _ hqN).mp ht⟩
  · rintro ⟨c', ⟨tq, tl, tr⟩, hr, hc, ⟨hqN, hlN, hrN⟩, ht⟩
    exact ⟨c', tq, tl, tr, (eval_fInternalReach hM hNE _ _ _).mpr hr, (eval_fConfCode _ _ _ _ _).mpr hc,
      (eval_fNatObject _ _).mpr hqN, (eval_fNatObject _ _).mpr hlN, (eval_fNatObject _ _).mpr hrN,
      (eval_fTerminal hM hNE 2 _ hqN).mpr ht⟩

attribute [irreducible] fInternalReach fInternalHaltsFrom

private def fPow2 (n res : Nat) : Formula :=
  .and (fNatObject n) (.and (fNatObject res)
    (.ex (.ex (.ex (.ex (.ex
      (.and (fEmpty 4) (.and (fNumeral 1 3) (.and (fNumeral 2 2)
        (.and (fSucc (n + 5) 1) (.and (fFunctionOn 0 1)
          (.and (fAt 0 4 3) (.and (fAt 0 (n + 5) (res + 5))
            (.and (.all (.all (.imp (.mem 1 3) (.imp (fAt 2 1 0) (fNatObject 0)))))
              (.all (.imp (.mem 0 (n + 6))
                (.ex (.ex (.ex (.and (fSucc 3 2) (.and (fAt 4 3 1) (.and (fAt 4 2 0) (fMul 6 1 0)))))))))))))))))))))))

private theorem bound_fPow2 {a b n : Nat} (ha : a < n) (hb : b < n) : Bound (fPow2 a b) n :=
  ⟨bound_fNatObject ha, ⟨bound_fNatObject hb,
    ⟨bound_fEmpty (by omega), ⟨bound_fNumeral (by omega), ⟨bound_fNumeral (by omega),
      ⟨bound_fSucc (by omega) (by omega), ⟨bound_fFunctionOn (by omega) (by omega),
        ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
          ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
           ⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
            ⟨bound_fAt (by omega) (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem eval_fPow2 (a b : Nat) (s : Nat → V) : eval E (fPow2 a b) s ↔ Pow2 E (s a) (s b) := by
  constructor
  · rintro ⟨ha, hb, z, one, two, dom, f, hz, h1, h2, hdom, hfun, hf0, hfn, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mp ha, (eval_fNatObject _ _).mp hb,
      z, one, two, dom, f, hz, (eval_fNumeral _ _ _).mp h1, (eval_fNumeral _ _ _).mp h2,
      (eval_fSucc _ _ _).mp hdom, (eval_fFunctionOn _ _ _).mp hfun,
      (eval_fAt _ _ _ _).mp hf0, (eval_fAt _ _ _ _).mp hfn,
      fun i x hi hix => (eval_fNatObject _ _).mp (hnat i x hi ((eval_fAt _ _ _ _).mpr hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, s1, s2, s3, s4⟩ := hstep i hi
    exact ⟨j, x, y, (eval_fSucc _ _ _).mp s1, (eval_fAt _ _ _ _).mp s2, (eval_fAt _ _ _ _).mp s3, (eval_fMul _ _ _ _).mp s4⟩
  · rintro ⟨ha, hb, z, one, two, dom, f, hz, h1, h2, hdom, hfun, hf0, hfn, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mpr ha, (eval_fNatObject _ _).mpr hb,
      z, one, two, dom, f, hz, (eval_fNumeral _ _ _).mpr h1, (eval_fNumeral _ _ _).mpr h2,
      (eval_fSucc _ _ _).mpr hdom, (eval_fFunctionOn _ _ _).mpr hfun,
      (eval_fAt _ _ _ _).mpr hf0, (eval_fAt _ _ _ _).mpr hfn,
      fun i x hi hix => (eval_fNatObject _ _).mpr (hnat i x hi ((eval_fAt _ _ _ _).mp hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, s1, s2, s3, s4⟩ := hstep i hi
    exact ⟨j, x, y, (eval_fSucc _ _ _).mpr s1, (eval_fAt _ _ _ _).mpr s2, (eval_fAt _ _ _ _).mpr s3, (eval_fMul _ _ _ _).mpr s4⟩

private def fOnes (a b : Nat) : Formula :=
  .and (fNatObject a) (.and (fNatObject b)
    (.ex (.ex (.and (fPow2 (a + 2) 1) (.and (fNumeral 1 0) (fAdd (b + 2) 0 1))))))

private theorem bound_fOnes {a b n : Nat} (ha : a < n) (hb : b < n) : Bound (fOnes a b) n :=
  ⟨bound_fNatObject ha, ⟨bound_fNatObject hb,
    ⟨bound_fPow2 (by omega) (by omega), ⟨bound_fNumeral (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩⟩⟩

private theorem eval_fOnes (a b : Nat) (s : Nat → V) : eval E (fOnes a b) s ↔ Ones E (s a) (s b) :=
  ⟨fun ⟨ha, hb, p, one, h1, h2, h3⟩ => ⟨(eval_fNatObject _ _).mp ha, (eval_fNatObject _ _).mp hb,
    p, one, (eval_fPow2 _ _ _).mp h1, (eval_fNumeral _ _ _).mp h2, (eval_fAdd _ _ _ _).mp h3⟩,
   fun ⟨ha, hb, p, one, h1, h2, h3⟩ => ⟨(eval_fNatObject _ _).mpr ha, (eval_fNatObject _ _).mpr hb,
    p, one, (eval_fPow2 _ _ _).mpr h1, (eval_fNumeral _ _ _).mpr h2, (eval_fAdd _ _ _ _).mpr h3⟩⟩

private def fTailBitsV (t res : Nat) : Formula :=
  .and (fNatObject t) (.and (fNatObject res)
    (.ex (.ex (.ex (.ex (.ex
      (.and (fEmpty 4) (.and (fNumeralBin 6 3) (.and (fNumeralBin 8 2)
        (.and (fSucc (t + 5) 1) (.and (fFunctionOn 0 1)
          (.and (fAt 0 4 4) (.and (fAt 0 (t + 5) (res + 5))
            (.and (.all (.all (.imp (.mem 1 3) (.imp (fAt 2 1 0) (fNatObject 0)))))
              (.all (.imp (.mem 0 (t + 6))
                (.ex (.ex (.ex (.ex (.and (fSucc 4 3) (.and (fAt 5 4 2) (.and (fAt 5 3 1)
                  (.and (fMul 7 2 0) (fAdd 8 0 1)))))))))))))))))))))))))

private theorem bound_fTailBitsV {t res n : Nat} (ht : t < n) (hr : res < n) : Bound (fTailBitsV t res) n :=
  ⟨bound_fNatObject ht, ⟨bound_fNatObject hr,
    ⟨bound_fEmpty (by omega), ⟨bound_fNumeralBin 6 3 _ (by omega), ⟨bound_fNumeralBin 8 2 _ (by omega),
      ⟨bound_fSucc (by omega) (by omega), ⟨bound_fFunctionOn (by omega) (by omega),
        ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
          ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
           ⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
            ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fMul (by omega) (by omega) (by omega),
              bound_fAdd (by omega) (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem eval_fTailBitsV (hM : Model E) (hNE : Nonempty V) (t res : Nat) (s : Nat → V) :
    eval E (fTailBitsV t res) s ↔ TailBitsV E (s t) (s res) := by
  constructor
  · rintro ⟨ht, hr, z, six, eight, dom, f, hz, h6, h8, hdom, hfun, hf0, hft, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mp ht, (eval_fNatObject _ _).mp hr,
      z, six, eight, dom, f, hz, (eval_fNumeralBin hM hNE 6 _ _).mp h6, (eval_fNumeralBin hM hNE 8 _ _).mp h8,
      (eval_fSucc _ _ _).mp hdom, (eval_fFunctionOn _ _ _).mp hfun,
      (eval_fAt _ _ _ _).mp hf0, (eval_fAt _ _ _ _).mp hft,
      fun i x hi hix => (eval_fNatObject _ _).mp (hnat i x hi ((eval_fAt _ _ _ _).mpr hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, p, s1, s2, s3, s4, s5⟩ := hstep i hi
    exact ⟨j, x, y, p, (eval_fSucc _ _ _).mp s1, (eval_fAt _ _ _ _).mp s2, (eval_fAt _ _ _ _).mp s3,
      (eval_fMul _ _ _ _).mp s4, (eval_fAdd _ _ _ _).mp s5⟩
  · rintro ⟨ht, hr, z, six, eight, dom, f, hz, h6, h8, hdom, hfun, hf0, hft, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mpr ht, (eval_fNatObject _ _).mpr hr,
      z, six, eight, dom, f, hz, (eval_fNumeralBin hM hNE 6 _ _).mpr h6, (eval_fNumeralBin hM hNE 8 _ _).mpr h8,
      (eval_fSucc _ _ _).mpr hdom, (eval_fFunctionOn _ _ _).mpr hfun,
      (eval_fAt _ _ _ _).mpr hf0, (eval_fAt _ _ _ _).mpr hft,
      fun i x hi hix => (eval_fNatObject _ _).mpr (hnat i x hi ((eval_fAt _ _ _ _).mp hix)),
      fun i hi => ?_⟩
    obtain ⟨j, x, y, p, s1, s2, s3, s4, s5⟩ := hstep i hi
    exact ⟨j, x, y, p, (eval_fSucc _ _ _).mpr s1, (eval_fAt _ _ _ _).mpr s2, (eval_fAt _ _ _ _).mpr s3,
      (eval_fMul _ _ _ _).mpr s4, (eval_fAdd _ _ _ _).mpr s5⟩

private def fRegBlockV (v suf res : Nat) : Formula :=
  .and (fNatObject v) (.and (fNatObject suf) (.and (fNatObject res)
    (.ex (.ex (.ex (.ex (.ex (.ex
      (.and (fSucc (v + 6) 5) (.and (fOnes 5 4) (.and (fPow2 5 3) (.and (fNumeral 2 2)
        (.and (fMul 3 (suf + 6) 1) (.and (fAdd 4 1 0) (fMul 2 0 (res + 6))))))))))))))))

private theorem bound_fRegBlockV {v suf res n : Nat} (hv : v < n) (hs : suf < n) (hr : res < n) :
    Bound (fRegBlockV v suf res) n :=
  ⟨bound_fNatObject hv, ⟨bound_fNatObject hs, ⟨bound_fNatObject hr,
    ⟨bound_fSucc (by omega) (by omega), ⟨bound_fOnes (by omega) (by omega), ⟨bound_fPow2 (by omega) (by omega),
      ⟨bound_fNumeral (by omega), ⟨bound_fMul (by omega) (by omega) (by omega),
        ⟨bound_fAdd (by omega) (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem eval_fRegBlockV (v suf res : Nat) (s : Nat → V) :
    eval E (fRegBlockV v suf res) s ↔ RegBlockV E (s v) (s suf) (s res) :=
  ⟨fun ⟨hv, hs, hr, vs, o, p, two, prod, sum, h1, h2, h3, h4, h5, h6, h7⟩ =>
    ⟨(eval_fNatObject _ _).mp hv, (eval_fNatObject _ _).mp hs, (eval_fNatObject _ _).mp hr,
      vs, o, p, two, prod, sum, (eval_fSucc _ _ _).mp h1, (eval_fOnes _ _ _).mp h2, (eval_fPow2 _ _ _).mp h3,
      (eval_fNumeral _ _ _).mp h4, (eval_fMul _ _ _ _).mp h5, (eval_fAdd _ _ _ _).mp h6, (eval_fMul _ _ _ _).mp h7⟩,
   fun ⟨hv, hs, hr, vs, o, p, two, prod, sum, h1, h2, h3, h4, h5, h6, h7⟩ =>
    ⟨(eval_fNatObject _ _).mpr hv, (eval_fNatObject _ _).mpr hs, (eval_fNatObject _ _).mpr hr,
      vs, o, p, two, prod, sum, (eval_fSucc _ _ _).mpr h1, (eval_fOnes _ _ _).mpr h2, (eval_fPow2 _ _ _).mpr h3,
      (eval_fNumeral _ _ _).mpr h4, (eval_fMul _ _ _ _).mpr h5, (eval_fAdd _ _ _ _).mpr h6, (eval_fMul _ _ _ _).mpr h7⟩⟩

private def fRegsBitsV (r0 r1 r2 r3 r4 r5 r6 r7 r8 t res : Nat) : Formula :=
  .ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex
    (.and (fTailBitsV (t + 13) 12)
      (.and (fRegBlockV (r8 + 13) 12 11) (.and (fRegBlockV (r7 + 13) 11 10)
        (.and (fRegBlockV (r6 + 13) 10 9) (.and (fRegBlockV (r5 + 13) 9 8)
          (.and (fRegBlockV (r4 + 13) 8 7) (.and (fRegBlockV (r3 + 13) 7 6)
            (.and (fRegBlockV (r2 + 13) 6 5) (.and (fRegBlockV (r1 + 13) 5 4)
              (.and (fRegBlockV (r0 + 13) 4 3)
                (.and (fNumeral 1 2) (.and (fNumeral 2 1) (.and (fMul 1 3 0) (fAdd 2 0 (res + 13)))))))))))))))))))))))))))

private theorem bound_fRegsBitsV {r0 r1 r2 r3 r4 r5 r6 r7 r8 t res n : Nat}
    (h0 : r0 < n) (h1 : r1 < n) (h2 : r2 < n) (h3 : r3 < n) (h4 : r4 < n)
    (h5 : r5 < n) (h6 : r6 < n) (h7 : r7 < n) (h8 : r8 < n) (ht : t < n) (hr : res < n) :
    Bound (fRegsBitsV r0 r1 r2 r3 r4 r5 r6 r7 r8 t res) n :=
  ⟨bound_fTailBitsV (by omega) (by omega),
    ⟨bound_fRegBlockV (by omega) (by omega) (by omega), ⟨bound_fRegBlockV (by omega) (by omega) (by omega),
      ⟨bound_fRegBlockV (by omega) (by omega) (by omega), ⟨bound_fRegBlockV (by omega) (by omega) (by omega),
        ⟨bound_fRegBlockV (by omega) (by omega) (by omega), ⟨bound_fRegBlockV (by omega) (by omega) (by omega),
          ⟨bound_fRegBlockV (by omega) (by omega) (by omega), ⟨bound_fRegBlockV (by omega) (by omega) (by omega),
            ⟨bound_fRegBlockV (by omega) (by omega) (by omega),
              ⟨bound_fNumeral (by omega), ⟨bound_fNumeral (by omega),
                ⟨bound_fMul (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem eval_fRegsBitsV (hM : Model E) (hNE : Nonempty V)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 t res : Nat) (s : Nat → V) :
    eval E (fRegsBitsV r0 r1 r2 r3 r4 r5 r6 r7 r8 t res) s ↔
      RegsBitsV E ⟨s r0, s r1, s r2, s r3, s r4, s r5, s r6, s r7, s r8⟩ (s t) (s res) :=
  ⟨fun ⟨s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, one, two, prod, ht, b8, b7, b6, b5, b4, b3, b2, b1, b0, h1, h2, hm, ha⟩ =>
    ⟨s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, one, two, prod,
      (eval_fTailBitsV hM hNE _ _ _).mp ht,
      (eval_fRegBlockV _ _ _ _).mp b8, (eval_fRegBlockV _ _ _ _).mp b7, (eval_fRegBlockV _ _ _ _).mp b6,
      (eval_fRegBlockV _ _ _ _).mp b5, (eval_fRegBlockV _ _ _ _).mp b4, (eval_fRegBlockV _ _ _ _).mp b3,
      (eval_fRegBlockV _ _ _ _).mp b2, (eval_fRegBlockV _ _ _ _).mp b1, (eval_fRegBlockV _ _ _ _).mp b0,
      (eval_fNumeral _ _ _).mp h1, (eval_fNumeral _ _ _).mp h2, (eval_fMul _ _ _ _).mp hm, (eval_fAdd _ _ _ _).mp ha⟩,
   fun ⟨s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, one, two, prod, ht, b8, b7, b6, b5, b4, b3, b2, b1, b0, h1, h2, hm, ha⟩ =>
    ⟨s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, one, two, prod,
      (eval_fTailBitsV hM hNE _ _ _).mpr ht,
      (eval_fRegBlockV _ _ _ _).mpr b8, (eval_fRegBlockV _ _ _ _).mpr b7, (eval_fRegBlockV _ _ _ _).mpr b6,
      (eval_fRegBlockV _ _ _ _).mpr b5, (eval_fRegBlockV _ _ _ _).mpr b4, (eval_fRegBlockV _ _ _ _).mpr b3,
      (eval_fRegBlockV _ _ _ _).mpr b2, (eval_fRegBlockV _ _ _ _).mpr b1, (eval_fRegBlockV _ _ _ _).mpr b0,
      (eval_fNumeral _ _ _).mpr h1, (eval_fNumeral _ _ _).mpr h2, (eval_fMul _ _ _ _).mpr hm, (eval_fAdd _ _ _ _).mpr ha⟩⟩

private def fFrameCodeV1 (m r0 r1 r2 r3 r4 r5 r6 r7 r8 t code : Nat) : Formula :=
  .and (fNatObject m) (.and (fNatObject t)
    (.and (fNatObject r0) (.and (fNatObject r1) (.and (fNatObject r2) (.and (fNatObject r3)
      (.and (fNatObject r4) (.and (fNatObject r5) (.and (fNatObject r6) (.and (fNatObject r7) (.and (fNatObject r8)
        (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex
          (.and (fNumeralBin 74 7) (.and (fNumeral 1 6) (.and (fNumeralBin 42 5)
            (.and (fAdd 5 (m + 8) 4) (.and (fPow2 4 3)
              (.and (fRegsBitsV (r0 + 8) (r1 + 8) (r2 + 8) (r3 + 8) (r4 + 8) (r5 + 8) (r6 + 8) (r7 + 8) (r8 + 8) (t + 8) 2)
                (.and (fMul 3 2 1) (.and (fAdd 6 1 0) (fConfCode 7 6 0 (code + 8))))))))))))))))))))))))))))

private theorem bound_fFrameCodeV1 {m r0 r1 r2 r3 r4 r5 r6 r7 r8 t code n : Nat}
    (hm : m < n) (h0 : r0 < n) (h1 : r1 < n) (h2 : r2 < n) (h3 : r3 < n) (h4 : r4 < n)
    (h5 : r5 < n) (h6 : r6 < n) (h7 : r7 < n) (h8 : r8 < n) (ht : t < n) (hc : code < n) :
    Bound (fFrameCodeV1 m r0 r1 r2 r3 r4 r5 r6 r7 r8 t code) n :=
  ⟨bound_fNatObject hm, ⟨bound_fNatObject ht,
    ⟨bound_fNatObject h0, ⟨bound_fNatObject h1, ⟨bound_fNatObject h2, ⟨bound_fNatObject h3,
      ⟨bound_fNatObject h4, ⟨bound_fNatObject h5, ⟨bound_fNatObject h6, ⟨bound_fNatObject h7, ⟨bound_fNatObject h8,
        ⟨bound_fNumeralBin 74 7 _ (by omega), ⟨bound_fNumeral (by omega), ⟨bound_fNumeralBin 42 5 _ (by omega),
          ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨bound_fPow2 (by omega) (by omega),
            ⟨bound_fRegsBitsV (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
              ⟨bound_fMul (by omega) (by omega) (by omega), ⟨bound_fAdd (by omega) (by omega) (by omega),
                bound_fConfCode (by omega) (by omega) (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem eval_fFrameCodeV1 (hM : Model E) (hNE : Nonempty V)
    (m r0 r1 r2 r3 r4 r5 r6 r7 r8 t code : Nat) (s : Nat → V) :
    eval E (fFrameCodeV1 m r0 r1 r2 r3 r4 r5 r6 r7 r8 t code) s ↔
      FrameCodeV E 1 (s m) ⟨s r0, s r1, s r2, s r3, s r4, s r5, s r6, s r7, s r8⟩ (s t) (s code) := by
  constructor
  · rintro ⟨hm, ht, h0, h1, h2, h3, h4, h5, h6, h7, h8, q74, one, p42, exp, pexp, rb, prod, rightV,
      hq74, hone, hp42, hexp, hpexp, hrb, hprod, hright, hcc⟩
    exact ⟨(eval_fNatObject _ _).mp hm, (eval_fNatObject _ _).mp ht,
      ⟨(eval_fNatObject _ _).mp h0, (eval_fNatObject _ _).mp h1, (eval_fNatObject _ _).mp h2,
       (eval_fNatObject _ _).mp h3, (eval_fNatObject _ _).mp h4, (eval_fNatObject _ _).mp h5,
       (eval_fNatObject _ _).mp h6, (eval_fNatObject _ _).mp h7, (eval_fNatObject _ _).mp h8⟩,
      q74, one, p42, one, exp, pexp, rb, prod, rightV,
      (eval_fNumeralBin hM hNE 74 _ _).mp hq74, (eval_fNumeral _ _ _).mp hone,
      (eval_fNumeralBin hM hNE 42 _ _).mp hp42, (eval_fNumeral _ _ _).mp hone,
      (eval_fAdd _ _ _ _).mp hexp, (eval_fPow2 _ _ _).mp hpexp,
      (eval_fRegsBitsV hM hNE _ _ _ _ _ _ _ _ _ _ _ _).mp hrb,
      (eval_fMul _ _ _ _).mp hprod, (eval_fAdd _ _ _ _).mp hright,
      (eval_fConfCode _ _ _ _ _).mp hcc⟩
  · rintro ⟨hm, ht, ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, q74, one, p42, prefV, exp, pexp, rb, prod, rightV,
      hq74, hone, hp42, hpref, hexp, hpexp, hrb, hprod, hright, hcc⟩
    have hpeq : prefV = one := numeral_unique hM hNE hpref hone
    rw [hpeq] at hright
    exact ⟨(eval_fNatObject _ _).mpr hm, (eval_fNatObject _ _).mpr ht,
      (eval_fNatObject _ _).mpr h0, (eval_fNatObject _ _).mpr h1, (eval_fNatObject _ _).mpr h2,
      (eval_fNatObject _ _).mpr h3, (eval_fNatObject _ _).mpr h4, (eval_fNatObject _ _).mpr h5,
      (eval_fNatObject _ _).mpr h6, (eval_fNatObject _ _).mpr h7, (eval_fNatObject _ _).mpr h8,
      q74, one, p42, exp, pexp, rb, prod, rightV,
      (eval_fNumeralBin hM hNE 74 _ _).mpr hq74, (eval_fNumeral _ _ _).mpr hone,
      (eval_fNumeralBin hM hNE 42 _ _).mpr hp42,
      (eval_fAdd _ _ _ _).mpr hexp, (eval_fPow2 _ _ _).mpr hpexp,
      (eval_fRegsBitsV hM hNE _ _ _ _ _ _ _ _ _ _ _ _).mpr hrb,
      (eval_fMul _ _ _ _).mpr hprod, (eval_fAdd _ _ _ _).mpr hright,
      (eval_fConfCode _ _ _ _ _).mpr hcc⟩

attribute [irreducible] fFrameCodeV1

private theorem frameCodeV_nat {pref : Nat} {m : V} {rs : Regs9 V} {t code : V}
    (h : FrameCodeV E pref m rs t code) : NatObject E code := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, lr, _, hc2⟩
  exact hc2.2.2.1

/-! ### Part 3: Continuation-Passing Stack Compiler (`CanPush`) -/

private theorem internalReach_trans (hM : Model E) (hNE : Nonempty V) {c1 c2 c3 : V}
    (h12 : InternalReach E c1 c2) (h23 : InternalReach E c2 c3) : InternalReach E c1 c3 :=
  (internal_startup_and_linkedHalts V E hNE hM).2.1 c1 c2 c3 h12 h23

private theorem internalHaltsFrom_of_reach (hM : Model E) (hNE : Nonempty V) {c1 c2 : V}
    (hr : InternalReach E c1 c2) (hh : InternalHaltsFrom E c2) : InternalHaltsFrom E c1 := by
  rcases hh with ⟨c', t, hr', hc', hv', ht'⟩
  exact ⟨c', t, internalReach_trans hM hNE hr hr', hc', hv', ht'⟩

private theorem internalReach_refl (hM : Model E) (hNE : Nonempty V) {c : V} (hc : NatObject E c) :
    InternalReach E c c := by
  obtain ⟨dom, hdom⟩ := exists_succ hM hNE (zeroV hM hNE)
  obtain ⟨f, hfun, hf0, hfat⟩ := functionOn_singleton hM hNE (zeroV_empty hM hNE) hdom (a := c)
  exact ⟨zeroV hM hNE, zeroV_nat hM hNE, hc, hc, zeroV hM hNE, dom, f, zeroV_empty hM hNE,
    hdom, hfun, hf0, hf0, fun i x _ h => (hfat i x h).2 ▸ hc, fun i hi => False.elim (zeroV_empty hM hNE i hi)⟩

/-- Helper: compose a single-step transition into `InternalHaltsFrom E code ∨ ∃ ..., InternalReach E code code'`. -/
private def CleanFrame (r0 r1 r2 r3 r6 r7 m t code : V) : Prop :=
  ∃ z, Empty E z ∧ ¬ Empty E m ∧ ¬ Empty E t ∧
    FrameCodeV E 1 m ⟨r0, r1, r2, r3, z, z, r6, r7, z⟩ t code

open Classical in
private noncomputable def cantorV (hM : Model E) (hNE : Nonempty V) (a b : V) : V :=
  if h : NatObject E a ∧ NatObject E b then Classical.choose (cantor_exists hM hNE h.1 h.2) else zeroV hM hNE

private theorem cantorV_spec (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    Cantor E a b (cantorV hM hNE a b) := by
  classical
  unfold cantorV; rw [dif_pos ⟨ha, hb⟩]; exact (Classical.choose_spec (cantor_exists hM hNE ha hb)).1

private theorem cantorV_nat (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    NatObject E (cantorV hM hNE a b) := (cantorV_spec hM hNE ha hb).2.2.1

private noncomputable def cmdShift (hM : Model E) (hNE : Nonempty V) (r_next : V) : V :=
  succV hM hNE (cantorV hM hNE (zeroV hM hNE) r_next)

private theorem cmdShift_nat (hM : Model E) (hNE : Nonempty V) {r_next : V} (hr : NatObject E r_next) :
    NatObject E (cmdShift hM hNE r_next) :=
  succV_nat hM hNE (cantorV_nat hM hNE (zeroV_nat hM hNE) hr)

private noncomputable def cmdMP (hM : Model E) (hNE : Nonempty V) (b r_next : V) : V :=
  succV hM hNE (cantorV hM hNE (numV hM hNE 1) (cantorV hM hNE b r_next))

private theorem cmdMP_nat (hM : Model E) (hNE : Nonempty V) {b r_next : V} (hb : NatObject E b) (hr : NatObject E r_next) :
    NatObject E (cmdMP hM hNE b r_next) :=
  succV_nat hM hNE (cantorV_nat hM hNE (numV_nat hM hNE 1) (cantorV_nat hM hNE hb hr))

private noncomputable def cmdGenAx (hM : Model E) (hNE : Nonempty V) (x y opZ r_next : V) : V :=
  succV hM hNE (cantorV hM hNE (succV hM hNE (succV hM hNE opZ))
    (cantorV hM hNE x (cantorV hM hNE y r_next)))

private theorem cmdGenAx_nat (hM : Model E) (hNE : Nonempty V) {x y opZ r_next : V}
    (hx : NatObject E x) (hy : NatObject E y) (hz : NatObject E opZ) (hr : NatObject E r_next) :
    NatObject E (cmdGenAx hM hNE x y opZ r_next) :=
  succV_nat hM hNE (cantorV_nat hM hNE (succV_nat hM hNE (succV_nat hM hNE hz))
    (cantorV_nat hM hNE hx (cantorV_nat hM hNE hy hr)))

private theorem exec_shift (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {hd tl r0 r2 r3 r6 r7 r_next m t code : V}
    (hrn : NatObject E r_next) (hcat : Cantor E hd tl r0)
    (hF : CleanFrame (E := E) r0 (cmdShift hM hNE r_next) r2 r3 r6 r7 m t code) :
    InternalHaltsFrom E code ∨
    ∃ m' t' code', CleanFrame (E := E) tl r_next r7 r3 r6 hd m' t' code' ∧ InternalReach E code code' := by
  rcases hF with ⟨z, hz, hmne, htne, hfc⟩
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  rcases hfc.2.2.1 with ⟨hr0N, _, hr2N, hr3N, _, _, hr6N, hr7N, _⟩
  have hstep := (hLoop r0 (cmdShift hM hNE r_next) r2 r3 r6 r7 m t (zeroV hM hNE) code
    hr0N (cmdShift_nat hM hNE hrn) hr2N hr3N hr6N hr7N hfc.1 hfc.2.1 hz hmne htne hfc
    (cantorV hM hNE (zeroV hM hNE) r_next) r6 (zeroV hM hNE) r_next (Or.inr ⟨succV_spec hM hNE _, rfl⟩)
    (cantorV_spec hM hNE (zeroV_nat hM hNE) hrn)).1 hz
    (addV hM hNE r2 r7) (numV hM hNE 1) (addV_spec hM hNE hr2N hr7N) (numV_numeral hM hNE 1)
  by_cases h1 : addV hM hNE r2 r7 = numV hM hNE 1
  · exact Or.inl (hstep.1 h1)
  · obtain ⟨m', t', code', hm', ht', hfc', hr'⟩ := hstep.2 h1 hd tl hcat
    exact Or.inr ⟨m', t', code', ⟨zeroV hM hNE, hz, hm', ht', hfc'⟩, hr'⟩

private theorem exec_shift_halt (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {r0 r3 r6 r_next m t code : V}
    (hrn : NatObject E r_next)
    (hF : CleanFrame (E := E) r0 (cmdShift hM hNE r_next) (zeroV hM hNE) r3 r6 (numV hM hNE 1) m t code) :
    InternalHaltsFrom E code := by
  rcases hF with ⟨z, hz, hmne, htne, hfc⟩
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  rcases hfc.2.2.1 with ⟨hr0N, _, hr2N, hr3N, _, _, hr6N, hr7N, _⟩
  have hstep := (hLoop r0 (cmdShift hM hNE r_next) (zeroV hM hNE) r3 r6 (numV hM hNE 1) m t (zeroV hM hNE) code
    hr0N (cmdShift_nat hM hNE hrn) hr2N hr3N hr6N hr7N hfc.1 hfc.2.1 hz hmne htne hfc
    (cantorV hM hNE (zeroV hM hNE) r_next) r6 (zeroV hM hNE) r_next (Or.inr ⟨succV_spec hM hNE _, rfl⟩)
    (cantorV_spec hM hNE (zeroV_nat hM hNE) hrn)).1 hz
    (numV hM hNE 1) (numV hM hNE 1)
    ((add_iff_eq hM hNE hr2N hr7N).mpr (zero_addV hM hNE _ hr7N).symm) (numV_numeral hM hNE 1)
  exact hstep.1 rfl

private theorem exec_mp_neq (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {r0 b r2 r3 r6 r7 B ic r_next m t code : V}
    (hb : NatObject E b) (hrn : NatObject E r_next)
    (hB : Add E r3 b B) (hic : CalcIc E r2 B ic) (hne : r7 ≠ ic)
    (hF : CleanFrame (E := E) r0 (cmdMP hM hNE b r_next) r2 r3 r6 r7 m t code) :
    ∃ m' t' code', CleanFrame (E := E) r0 r_next (zeroV hM hNE) B r6 (zeroV hM hNE) m' t' code' ∧ InternalReach E code code' := by
  rcases hF with ⟨z, hz, hmne, htne, hfc⟩
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  rcases hfc.2.2.1 with ⟨hr0N, _, hr2N, hr3N, _, _, hr6N, hr7N, _⟩
  have hstep := (hLoop r0 (cmdMP hM hNE b r_next) r2 r3 r6 r7 m t (zeroV hM hNE) code
    hr0N (cmdMP_nat hM hNE hb hrn) hr2N hr3N hr6N hr7N hfc.1 hfc.2.1 hz hmne htne hfc
    (cantorV hM hNE (numV hM hNE 1) (cantorV hM hNE b r_next)) r6 (numV hM hNE 1) (cantorV hM hNE b r_next)
    (Or.inr ⟨succV_spec hM hNE _, rfl⟩)
    (cantorV_spec hM hNE (numV_nat hM hNE 1) (cantorV_nat hM hNE hb hrn))).2.1 (numV_numeral hM hNE 1)
    b r_next B ic (cantorV_spec hM hNE hb hrn) hB hic
  obtain ⟨m', t', code', hm', ht', hfc', hr'⟩ := hstep.2 hne
  exact ⟨m', t', code', ⟨zeroV hM hNE, hz, hm', ht', hfc'⟩, hr'⟩

private theorem exec_mp_eq (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {r0 b r2 r3 r6 r7 B r_next m t code : V}
    (hb : NatObject E b) (hrn : NatObject E r_next)
    (hB : Add E r3 b B) (hic : CalcIc E r2 B r7)
    (hF : CleanFrame (E := E) r0 (cmdMP hM hNE b r_next) r2 r3 r6 r7 m t code) :
    ∃ s0 m' t' code', Cantor E (zeroV hM hNE) r0 s0 ∧
      CleanFrame (E := E) s0 r_next B B r6 (zeroV hM hNE) m' t' code' ∧ InternalReach E code code' := by
  rcases hF with ⟨z, hz, hmne, htne, hfc⟩
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  rcases hfc.2.2.1 with ⟨hr0N, _, hr2N, hr3N, _, _, hr6N, hr7N, _⟩
  have hstep := (hLoop r0 (cmdMP hM hNE b r_next) r2 r3 r6 r7 m t (zeroV hM hNE) code
    hr0N (cmdMP_nat hM hNE hb hrn) hr2N hr3N hr6N hr7N hfc.1 hfc.2.1 hz hmne htne hfc
    (cantorV hM hNE (numV hM hNE 1) (cantorV hM hNE b r_next)) r6 (numV hM hNE 1) (cantorV hM hNE b r_next)
    (Or.inr ⟨succV_spec hM hNE _, rfl⟩)
    (cantorV_spec hM hNE (numV_nat hM hNE 1) (cantorV_nat hM hNE hb hrn))).2.1 (numV_numeral hM hNE 1)
    b r_next B r7 (cantorV_spec hM hNE hb hrn) hB hic
  let s0 := cantorV hM hNE (zeroV hM hNE) r0
  obtain ⟨m', t', code', hm', ht', hfc', hr'⟩ := hstep.1 rfl s0 (cantorV_spec hM hNE (zeroV_nat hM hNE) hr0N)
  exact ⟨s0, m', t', code', cantorV_spec hM hNE (zeroV_nat hM hNE) hr0N, ⟨zeroV hM hNE, hz, hm', ht', hfc'⟩, hr'⟩

private theorem exec_genAx (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {r0 x y opZ r2 r3 r6 r7 X Y r_next m t code : V}
    (hx : NatObject E x) (hy : NatObject E y) (hopZ : NatObject E opZ) (hrn : NatObject E r_next)
    (hX : Add E r7 x X) (hY : Add E r3 y Y)
    (hF : CleanFrame (E := E) r0 (cmdGenAx hM hNE x y opZ r_next) r2 r3 r6 r7 m t code) :
    ∃ uc r8 h1 h2 h3 h4 h5 h6 s1 s2 s3 s4 s5 s6 s7 s8 s9 top m' t' code',
      CalcUc E r3 r7 uc ∧ CalcRho8 E Y opZ X r3 r8 ∧
      CalcHead1 E X Y h1 ∧ CalcHead2 E X Y opZ h2 ∧ CalcHead3 E X Y opZ h3 ∧
      CalcHead4 E X Y opZ h4 ∧ CalcHead5 E X Y h5 ∧ CalcHead6 E X Y opZ h6 ∧
      Cantor E r2 r0 s1 ∧ Cantor E uc s1 s2 ∧ Cantor E r8 s2 s3 ∧
      Cantor E h1 s3 s4 ∧ Cantor E h2 s4 s5 ∧ Cantor E h3 s5 s6 ∧
      Cantor E h4 s6 s7 ∧ Cantor E h5 s7 s8 ∧ Cantor E h6 s8 s9 ∧
      ((opZ ≠ X ∧ opZ ≠ Y ∧ CalcGateF E X Y opZ top) ∨ ((opZ = X ∨ opZ = Y) ∧ Empty E top)) ∧
      CleanFrame (E := E) s9 r_next top (zeroV hM hNE) r6 (zeroV hM hNE) m' t' code' ∧
      InternalReach E code code' := by
  rcases hF with ⟨z, hz, hmne, htne, hfc⟩
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  rcases hfc.2.2.1 with ⟨hr0N, _, hr2N, hr3N, _, _, hr6N, hr7N, _⟩
  have hXN := hX.2.2.1; have hYN := hY.2.2.1
  have hr3leY : E r3 Y ∨ r3 = Y := by
    have hle := addV_le_left hM hNE hr3N y hy
    rw [← (add_iff_eq hM hNE hr3N hy).mp hY] at hle
    exact hle.elim Or.inr Or.inl
  obtain ⟨uc, huc, hucN⟩ := calcUc_exists hM hNE hr3N hr7N
  obtain ⟨r8, hr8, hr8N⟩ := calcRho8_exists hM hNE hYN hopZ hXN hr3N hr3leY
  obtain ⟨h1, hh1, hh1N⟩ := calcHead1_exists hM hNE hXN hYN
  obtain ⟨h2, hh2, hh2N⟩ := calcHead2_exists hM hNE hXN hYN hopZ
  obtain ⟨h3, hh3, hh3N⟩ := calcHead3_exists hM hNE hXN hYN hopZ
  obtain ⟨h4, hh4, hh4N⟩ := calcHead4_exists hM hNE hXN hYN hopZ
  obtain ⟨h5, hh5, hh5N⟩ := calcHead5_exists hM hNE hXN hYN
  obtain ⟨h6, hh6, hh6N⟩ := calcHead6_exists hM hNE hXN hYN hopZ
  let s1 := cantorV hM hNE r2 r0; have hs1 := cantorV_spec hM hNE hr2N hr0N
  let s2 := cantorV hM hNE uc s1; have hs2 := cantorV_spec hM hNE hucN hs1.2.2.1
  let s3 := cantorV hM hNE r8 s2; have hs3 := cantorV_spec hM hNE hr8N hs2.2.2.1
  let s4 := cantorV hM hNE h1 s3; have hs4 := cantorV_spec hM hNE hh1N hs3.2.2.1
  let s5 := cantorV hM hNE h2 s4; have hs5 := cantorV_spec hM hNE hh2N hs4.2.2.1
  let s6 := cantorV hM hNE h3 s5; have hs6 := cantorV_spec hM hNE hh3N hs5.2.2.1
  let s7 := cantorV hM hNE h4 s6; have hs7 := cantorV_spec hM hNE hh4N hs6.2.2.1
  let s8 := cantorV hM hNE h5 s7; have hs8 := cantorV_spec hM hNE hh5N hs7.2.2.1
  let s9 := cantorV hM hNE h6 s8; have hs9 := cantorV_spec hM hNE hh6N hs8.2.2.1
  have htop_ex : ∃ top, (opZ ≠ X ∧ opZ ≠ Y ∧ CalcGateF E X Y opZ top) ∨ ((opZ = X ∨ opZ = Y) ∧ Empty E top) := by
    by_cases h1 : opZ = X
    · exact ⟨zeroV hM hNE, Or.inr ⟨Or.inl h1, hz⟩⟩
    · by_cases h2 : opZ = Y
      · exact ⟨zeroV hM hNE, Or.inr ⟨Or.inr h2, hz⟩⟩
      · obtain ⟨top, htop, _⟩ := calcGateF_exists hM hNE hXN hYN hopZ h1 h2
        exact ⟨top, Or.inl ⟨h1, h2, htop⟩⟩
  obtain ⟨top, htop⟩ := htop_ex
  let op1 := succV hM hNE opZ
  let op2 := succV hM hNE op1
  let w1 := cantorV hM hNE y r_next
  let w' := cantorV hM hNE x w1
  let w := cantorV hM hNE op2 w'
  have hstep := (hLoop r0 (cmdGenAx hM hNE x y opZ r_next) r2 r3 r6 r7 m t (zeroV hM hNE) code
    hr0N (cmdGenAx_nat hM hNE hx hy hopZ hrn) hr2N hr3N hr6N hr7N hfc.1 hfc.2.1 hz hmne htne hfc
    w r6 op2 w' (Or.inr ⟨succV_spec hM hNE _, rfl⟩)
    (cantorV_spec hM hNE (succV_nat hM hNE (succV_nat hM hNE hopZ)) (cantorV_nat hM hNE hx (cantorV_nat hM hNE hy hrn)))).2.2
    opZ op1 (succV_spec hM hNE opZ) (succV_spec hM hNE op1)
    x w1 y r_next X Y (cantorV_spec hM hNE hx (cantorV_nat hM hNE hy hrn)) (cantorV_spec hM hNE hy hrn) hX hY
    uc r8 h1 h2 h3 h4 h5 h6 s1 s2 s3 s4 s5 s6 s7 s8 s9 top
    huc hr8 hh1 hh2 hh3 hh4 hh5 hh6 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 htop
  obtain ⟨m', t', code', hm', ht', hfc', hr'⟩ := hstep
  exact ⟨uc, r8, h1, h2, h3, h4, h5, h6, s1, s2, s3, s4, s5, s6, s7, s8, s9, top, m', t', code',
    huc, hr8, hh1, hh2, hh3, hh4, hh5, hh6, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, htop,
    ⟨zeroV hM hNE, hz, hm', ht', hfc'⟩, hr'⟩

private noncomputable def cmdShiftN (hM : Model E) (hNE : Nonempty V) : Nat → V → V
  | 0, r => r
  | n + 1, r => cmdShift hM hNE (cmdShiftN hM hNE n r)

private theorem cmdShiftN_nat (hM : Model E) (hNE : Nonempty V) :
    ∀ n {r}, NatObject E r → NatObject E (cmdShiftN hM hNE n r)
  | 0, _, hr => hr
  | n + 1, _, hr => cmdShift_nat hM hNE (cmdShiftN_nat hM hNE n hr)

/-- `SAVE_T`: from arbitrary `(r0, T, B, A)`, either halts or reaches `(cantor(T, r0), 0, 0, 0)`. -/
private noncomputable def cmdSaveT (hM : Model E) (hNE : Nonempty V) (r_next : V) : V :=
  cmdGenAx hM hNE (zeroV hM hNE) (zeroV hM hNE) (zeroV hM hNE)
    (cmdShiftN hM hNE 8 (cmdMP hM hNE (zeroV hM hNE) r_next))

private theorem cmdSaveT_nat (hM : Model E) (hNE : Nonempty V) {r_next : V} (hr : NatObject E r_next) :
    NatObject E (cmdSaveT hM hNE r_next) :=
  cmdGenAx_nat hM hNE (zeroV_nat hM hNE) (zeroV_nat hM hNE) (zeroV_nat hM hNE)
    (cmdShiftN_nat hM hNE 8 (cmdMP_nat hM hNE (zeroV_nat hM hNE) hr))

private theorem exec_saveT (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {r0 T B r6 A r_next m t code : V} (hrn : NatObject E r_next)
    (hF : CleanFrame (E := E) r0 (cmdSaveT hM hNE r_next) T B r6 A m t code) :
    InternalHaltsFrom E code ∨
    ∃ s1 m' t' code', Cantor E T r0 s1 ∧
      CleanFrame (E := E) s1 r_next (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m' t' code' ∧
      InternalReach E code code' := by
  have hmpN := cmdMP_nat hM hNE (zeroV_nat hM hNE) hrn
  have hB_N : NatObject E B := by rcases hF with ⟨_, _, _, _, hfc⟩; exact hfc.2.2.1.2.2.2.1
  have hA_N : NatObject E A := by rcases hF with ⟨_, _, _, _, hfc⟩; exact hfc.2.2.1.2.2.2.2.2.2.2.1
  obtain ⟨uc, r8, h1, h2, h3, h4, h5, h6, s1, s2, s3, s4, s5, s6, s7, s8, s9, top, m1, t1, c1,
    huc, hr8, _, _, _, _, _, _, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, _, hF1, hr01⟩ :=
    exec_genAx hM hNE hLoop (zeroV_nat hM hNE) (zeroV_nat hM hNE) (zeroV_nat hM hNE)
      (cmdShiftN_nat hM hNE 8 hmpN) (add_zero hM hNE hA_N (zeroV_empty hM hNE))
      (add_zero hM hNE hB_N (zeroV_empty hM hNE)) hF
  -- 8 Shifts pop h6, h5, h4, h3, h2, h1, r8, uc
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 7 hmpN) hs9 hF1 with hh | ⟨m2, t2, c2, hF2, hr12⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE hr01 hh)
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 6 hmpN) hs8 hF2 with hh | ⟨m3, t3, c3, hF3, hr23⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE (internalReach_trans hM hNE hr01 hr12) hh)
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 5 hmpN) hs7 hF3 with hh | ⟨m4, t4, c4, hF4, hr34⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE hr01 hr12) hr23) hh)
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 4 hmpN) hs6 hF4 with hh | ⟨m5, t5, c5, hF5, hr45⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE hr01 hr12) hr23) hr34) hh)
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 3 hmpN) hs5 hF5 with hh | ⟨m6, t6, c6, hF6, hr56⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE hr01 hr12) hr23) hr34) hr45) hh)
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 2 hmpN) hs4 hF6 with hh | ⟨m7, t7, c7, hF7, hr67⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE hr01 hr12) hr23) hr34) hr45) hr56) hh)
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 1 hmpN) hs3 hF7 with hh | ⟨m8, t8, c8, hF8, hr78⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE hr01 hr12) hr23) hr34) hr45) hr56) hr67) hh)
  rcases exec_shift hM hNE hLoop hmpN hs2 hF8 with hh | ⟨m9, t9, c9, hF9, hr89⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE hr01 hr12) hr23) hr34) hr45) hr56) hr67) hr78) hh)
  -- Now at (s1, cmdMP 0 r_next, r8, 0, r6, uc)
  obtain ⟨ic, hic, _⟩ := calcIc_exists hM hNE hs3.1 (zeroV_nat hM hNE)
  obtain ⟨m10, t10, c10, hF10, hr910⟩ :=
    exec_mp_neq hM hNE hLoop (zeroV_nat hM hNE) hrn (add_zero hM hNE (zeroV_nat hM hNE) (zeroV_empty hM hNE))
      hic (calcUc_ne_calcIc hM hNE huc hic) hF9
  right
  refine ⟨s1, m10, t10, c10, hs1, hF10, ?_⟩
  exact internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE
    (internalReach_trans hM hNE (internalReach_trans hM hNE (internalReach_trans hM hNE
      (internalReach_trans hM hNE (internalReach_trans hM hNE hr01 hr12) hr23) hr34) hr45) hr56) hr67) hr78)
    (internalReach_trans hM hNE hr89 hr910)

/-- `DELETE_SECOND`: from `(cantor(x, cantor(w, S)), 0, 0, 0)`, either halts or reaches `(cantor(x, S), 0, 0, 0)`. -/
private noncomputable def cmdDelSecond (hM : Model E) (hNE : Nonempty V) (r_next : V) : V :=
  cmdShift hM hNE (cmdShift hM hNE (cmdSaveT hM hNE r_next))

private theorem cmdDelSecond_nat (hM : Model E) (hNE : Nonempty V) {r_next : V} (hr : NatObject E r_next) :
    NatObject E (cmdDelSecond hM hNE r_next) :=
  cmdShift_nat hM hNE (cmdShift_nat hM hNE (cmdSaveT_nat hM hNE hr))

private theorem exec_delSecond (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {x w S sw sxw r6 r_next m t code : V} (hrn : NatObject E r_next)
    (hsw : Cantor E w S sw) (hsxw : Cantor E x sw sxw)
    (hF : CleanFrame (E := E) sxw (cmdDelSecond hM hNE r_next) (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m t code) :
    InternalHaltsFrom E code ∨
    ∃ sx m' t' code', Cantor E x S sx ∧
      CleanFrame (E := E) sx r_next (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m' t' code' ∧
      InternalReach E code code' := by
  rcases exec_shift hM hNE hLoop (cmdShift_nat hM hNE (cmdSaveT_nat hM hNE hrn)) hsxw hF with hh | ⟨m1, t1, c1, hF1, hr01⟩
  · exact Or.inl hh
  rcases exec_shift hM hNE hLoop (cmdSaveT_nat hM hNE hrn) hsw hF1 with hh | ⟨m2, t2, c2, hF2, hr12⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE hr01 hh)
  rcases exec_saveT hM hNE hLoop hrn hF2 with hh | ⟨sx, m3, t3, c3, hsx, hF3, hr23⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE (internalReach_trans hM hNE hr01 hr12) hh)
  exact Or.inr ⟨sx, m3, t3, c3, hsx, hF3, internalReach_trans hM hNE (internalReach_trans hM hNE hr01 hr12) hr23⟩

/-- `CanPush φ`: continuation-passing stack-pushing capability for formula code `φ`. -/
private def CanPush (φ : V) : Prop :=
  ∀ r_next, NatObject E r_next → ∃ r_start, NatObject E r_start ∧
    ∀ r0 r6 m t code z,
      NatObject E r0 → NatObject E r6 → NatObject E m → NatObject E t →
      Empty E z → ¬ Empty E m → ¬ Empty E t →
      FrameCodeV E 1 m ⟨r0, r_start, z, z, z, z, r6, z, z⟩ t code →
      InternalHaltsFrom E code ∨
      ∃ r0' m' t' code',
        Cantor E φ r0 r0' ∧ ¬ Empty E m' ∧ ¬ Empty E t' ∧
        FrameCodeV E 1 m' ⟨r0', r_next, z, z, z, z, r6, z, z⟩ t' code' ∧
        InternalReach E code code'

private def fCanPush (phi : Nat) : Formula :=
  .all (.imp (fNatObject 0)
    (.ex (.and (fNatObject 0)
      (.all (.all (.all (.all (.all (.all
        (.imp (fNatObject 5) (.imp (fNatObject 4) (.imp (fNatObject 3) (.imp (fNatObject 2)
          (.imp (fEmpty 0) (.imp (fNot (fEmpty 3)) (.imp (fNot (fEmpty 2))
            (.imp (fFrameCodeV1 3 5 6 0 0 0 0 4 0 0 2 1)
              (.or (fInternalHaltsFrom 1)
                (.ex (.ex (.ex (.ex
                  (.and (fCantor (phi + 12) 9 3)
                    (.and (fNot (fEmpty 2)) (.and (fNot (fEmpty 1))
                      (.and (fFrameCodeV1 2 3 11 4 4 4 4 8 4 4 1 0)
                        (fInternalReach 5 0)))))))))))))))))))))))))))

private theorem bound_fCanPush {phi n : Nat} (hp : phi < n) : Bound (fCanPush phi) n :=
  ⟨bound_fNatObject (by omega),
    ⟨bound_fNatObject (by omega),
      ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega), ⟨bound_fNatObject (by omega),
        ⟨bound_fNatObject (by omega), ⟨bound_fEmpty (by omega), ⟨bound_fNot (bound_fEmpty (by omega)),
          ⟨bound_fNot (bound_fEmpty (by omega)),
            ⟨bound_fFrameCodeV1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
              ⟨bound_fInternalHaltsFrom (by omega),
                ⟨bound_fCantor (by omega) (by omega) (by omega),
                  ⟨bound_fNot (bound_fEmpty (by omega)), ⟨bound_fNot (bound_fEmpty (by omega)),
                    ⟨bound_fFrameCodeV1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
                      bound_fInternalReach (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem eval_fCanPush (hM : Model E) (hNE : Nonempty V) (phi : Nat) (s : Nat → V) :
    eval E (fCanPush phi) s ↔ CanPush (E := E) (s phi) := by
  constructor
  · intro h r_next hrn
    obtain ⟨r_start, hrs, hbody⟩ := h r_next ((eval_fNatObject _ _).mpr hrn)
    refine ⟨r_start, (eval_fNatObject _ _).mp hrs, fun r0 r6 m t code z hr0 hr6 hm ht hz hmne htne hfc => ?_⟩
    rcases hbody r0 r6 m t code z
      ((eval_fNatObject _ _).mpr hr0) ((eval_fNatObject _ _).mpr hr6)
      ((eval_fNatObject _ _).mpr hm) ((eval_fNatObject _ _).mpr ht)
      hz hmne htne ((eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc) with hh | ⟨r0', m', t', code', hc, hm', ht', hfc', hr⟩
    · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mp hh)
    · exact Or.inr ⟨r0', m', t', code', (eval_fCantor _ _ _ _).mp hc, hm', ht',
        (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfc', (eval_fInternalReach hM hNE _ _ _).mp hr⟩
  · intro h r_next hrn
    obtain ⟨r_start, hrs, hbody⟩ := h r_next ((eval_fNatObject _ _).mp hrn)
    refine ⟨r_start, (eval_fNatObject _ _).mpr hrs, fun r0 r6 m t code z hr0 hr6 hm ht hz hmne htne hfc => ?_⟩
    rcases hbody r0 r6 m t code z
      ((eval_fNatObject _ _).mp hr0) ((eval_fNatObject _ _).mp hr6)
      ((eval_fNatObject _ _).mp hm) ((eval_fNatObject _ _).mp ht)
      hz hmne htne ((eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfc) with hh | ⟨r0', m', t', code', hc, hm', ht', hfc', hr⟩
    · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mpr hh)
    · exact Or.inr ⟨r0', m', t', code', (eval_fCantor _ _ _ _).mpr hc, hm', ht',
        (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc', (eval_fInternalReach hM hNE _ _ _).mpr hr⟩

attribute [irreducible] fCanPush

private theorem canPush_of_clean (hM : Model E) (hNE : Nonempty V) {φ : V}
    (h : ∀ r_next, NatObject E r_next → ∃ r_start, NatObject E r_start ∧
      ∀ r0 r6 m t code, CleanFrame (E := E) r0 r_start (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m t code →
        InternalHaltsFrom E code ∨
        ∃ r0' m' t' code', Cantor E φ r0 r0' ∧
          CleanFrame (E := E) r0' r_next (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m' t' code' ∧
          InternalReach E code code') : CanPush (E := E) φ := by
  intro r_next hrn
  obtain ⟨r_start, hrs, hbody⟩ := h r_next hrn
  refine ⟨r_start, hrs, fun r0 r6 m t code z _ _ _ _ hz hmne htne hfc => ?_⟩
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  rcases hbody r0 r6 m t code ⟨zeroV hM hNE, hz, hmne, htne, hfc⟩ with hh | ⟨r0', m', t', code', hc, ⟨z', hz', hm', ht', hfc'⟩, hr⟩
  · exact Or.inl hh
  · have := empty_unique hM hNE hz' hz; subst this
    exact Or.inr ⟨r0', m', t', code', hc, hm', ht', hfc', hr⟩

private theorem canPush_apply (hM : Model E) (hNE : Nonempty V) {φ r_next : V}
    (hcp : CanPush (E := E) φ) (hrn : NatObject E r_next) :
    ∃ r_start, NatObject E r_start ∧
      ∀ r0 r6 m t code, CleanFrame (E := E) r0 r_start (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m t code →
        InternalHaltsFrom E code ∨
        ∃ r0' m' t' code', Cantor E φ r0 r0' ∧
          CleanFrame (E := E) r0' r_next (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m' t' code' ∧
          InternalReach E code code' := by
  obtain ⟨r_start, hrs, hbody⟩ := hcp r_next hrn
  refine ⟨r_start, hrs, fun r0 r6 m t code ⟨z, hz, hmne, htne, hfc⟩ => ?_⟩
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  rcases hfc.2.2.1 with ⟨hr0N, _, _, _, _, _, hr6N, _, _⟩
  rcases hbody r0 r6 m t code (zeroV hM hNE) hr0N hr6N hfc.1 hfc.2.1 hz hmne htne hfc with hh | ⟨r0', m', t', code', hc, hm', ht', hfc', hr⟩
  · exact Or.inl hh
  · exact Or.inr ⟨r0', m', t', code', hc, ⟨zeroV hM hNE, hz, hm', ht', hfc'⟩, hr⟩

/-- Helper: delete `k` items right below the top of the stack `x`. -/
private noncomputable def cmdDelSecondN (hM : Model E) (hNE : Nonempty V) : Nat → V → V
  | 0, r => r
  | k + 1, r => cmdDelSecond hM hNE (cmdDelSecondN hM hNE k r)

private theorem cmdDelSecondN_nat (hM : Model E) (hNE : Nonempty V) :
    ∀ k {r}, NatObject E r → NatObject E (cmdDelSecondN hM hNE k r)
  | 0, _, hr => hr
  | k + 1, _, hr => cmdDelSecond_nat hM hNE (cmdDelSecondN_nat hM hNE k hr)

/-- Helper: pop `k` items from stack via `k` Shifts. -/
private theorem exec_del_1 (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {x w1 S s1 sx r6 r_next m t code : V} (hrn : NatObject E r_next)
    (h1 : Cantor E w1 S s1) (hx : Cantor E x s1 sx)
    (hF : CleanFrame (E := E) sx (cmdDelSecondN hM hNE 1 r_next) (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m t code) :
    InternalHaltsFrom E code ∨
    ∃ r0' m' t' code', Cantor E x S r0' ∧
      CleanFrame (E := E) r0' r_next (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m' t' code' ∧
      InternalReach E code code' :=
  exec_delSecond hM hNE hLoop hrn h1 hx hF

private theorem exec_del_succ (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E) {k : Nat}
    {x w S sw sxw r6 r_next m t code : V} (hrn : NatObject E r_next)
    (hsw : Cantor E w S sw) (hsxw : Cantor E x sw sxw)
    (hF : CleanFrame (E := E) sxw (cmdDelSecondN hM hNE (k + 1) r_next) (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m t code) :
    InternalHaltsFrom E code ∨
    ∃ sx m' t' code', Cantor E x S sx ∧
      CleanFrame (E := E) sx (cmdDelSecondN hM hNE k r_next) (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m' t' code' ∧
      InternalReach E code code' :=
  exec_delSecond hM hNE hLoop (cmdDelSecondN_nat hM hNE k hrn) hsw hsxw hF

/-- Closure of `CanPush` under all 11 rules of `InternalCalcDeriv`. -/
private theorem canPush_zero (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E) {x : V} (hx : Empty E x) :
    CanPush (E := E) x := by
  have := empty_unique hM hNE hx (zeroV_empty hM hNE); subst this
  apply canPush_of_clean hM hNE
  intro r_next hrn
  exact ⟨cmdSaveT hM hNE r_next, cmdSaveT_nat hM hNE hrn, fun r0 r6 m t code hF => exec_saveT hM hNE hLoop hrn hF⟩

private theorem canPush_gateF (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {a b c x : V} (hgf : CalcGateF E a b c x) : CanPush (E := E) x := by
  have ha := hgf.1; have hb := hgf.2.1; have hc := hgf.2.2.1
  have hca := hgf.2.2.2.1; have hcb := hgf.2.2.2.2.1
  apply canPush_of_clean hM hNE
  intro r_next hrn
  let r_del := cmdDelSecondN hM hNE 9 r_next
  let r_save := cmdSaveT hM hNE r_del
  refine ⟨cmdGenAx hM hNE a b c r_save, cmdGenAx_nat hM hNE ha hb hc (cmdSaveT_nat hM hNE (cmdDelSecondN_nat hM hNE 9 hrn)),
    fun r0 r6 m t code hF => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, s1, s2, s3, s4, s5, s6, s7, s8, s9, top, m0, t0, c0,
    _, _, _, _, _, _, _, _, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, htop, hF0, hr0⟩ :=
    exec_genAx hM hNE hLoop ha hb hc (cmdSaveT_nat hM hNE (cmdDelSecondN_nat hM hNE 9 hrn))
      ((add_iff_eq hM hNE (zeroV_nat hM hNE) ha).mpr (zero_addV hM hNE a ha).symm)
      ((add_iff_eq hM hNE (zeroV_nat hM hNE) hb).mpr (zero_addV hM hNE b hb).symm) hF
  have htop_eq : top = x := by
    rcases htop with ⟨_, _, hgf'⟩ | ⟨heq, _⟩
    · -- GateF unique
      rcases hgf' with ⟨_, _, _, _, _, e1', ue1', d', m1', um1', v', g', q', iq', idq',
        he1', hue1', hd', hm1', hum1', hv', hg', hq', hiq', hidq', hres'⟩
      rcases hgf with ⟨_, _, _, _, _, e1, ue1, d, m1, um1, v, g, q, iq, idq,
        he1, hue1, hd, hm1, hum1, hv, hg, hq, hiq, hidq, hres⟩
      have := calcEc_unique hM hNE he1' he1; subst this
      have := calcUc_unique hM hNE hue1' hue1; subst this
      have := calcIc_unique hM hNE hd' hd; subst this
      have := calcMc_unique hM hNE hm1' hm1; subst this
      have := calcUc_unique hM hNE hum1' hum1; subst this
      have := calcIc_unique hM hNE hv' hv; subst this
      have hgeq : g' = g := by
        rcases hg' with ⟨_, _, _, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21,
          p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22⟩
        rcases hg with ⟨_, _, _, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21,
          q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22⟩
        have := calcMc_unique hM hNE p1 q1; subst this; have := calcMc_unique hM hNE p2 q2; subst this
        have := calcIc_unique hM hNE p3 q3; subst this; have := calcUc_unique hM hNE p4 q4; subst this
        have := calcMc_unique hM hNE p5 q5; subst this; have := calcNc_unique hM hNE p6 q6; subst this
        have := calcIc_unique hM hNE p7 q7; subst this; have := calcUc_unique hM hNE p8 q8; subst this
        have := calcNc_unique hM hNE p9 q9; subst this; have := calcIc_unique hM hNE p10 q10; subst this
        have := calcUc_unique hM hNE p11 q11; subst this; have := calcIc_unique hM hNE p12 q12; subst this
        have := calcUc_unique hM hNE p13 q13; subst this; have := calcNc_unique hM hNE p14 q14; subst this
        have := calcIc_unique hM hNE p15 q15; subst this; have := calcUc_unique hM hNE p16 q16; subst this
        have := calcNc_unique hM hNE p17 q17; subst this; have := calcIc_unique hM hNE p18 q18; subst this
        have := calcUc_unique hM hNE p19 q19; subst this; have := calcIc_unique hM hNE p20 q20; subst this
        have := calcNc_unique hM hNE p21 q21; subst this; exact calcIc_unique hM hNE p22 q22
      subst hgeq
      have := calcUc_unique hM hNE hq' hq; subst this
      have := calcIc_unique hM hNE hiq' hiq; subst this
      have := calcIc_unique hM hNE hidq' hidq; subst this
      exact calcNc_unique hM hNE hres' hres
    · exact False.elim (heq.elim hca hcb)
  subst htop_eq
  rcases exec_saveT hM hNE hLoop (cmdDelSecondN_nat hM hNE 9 hrn) hF0 with hh | ⟨p9, m1, t1, c1, hp9, hF1, hr1⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE hr0 hh)
  have r01 := internalReach_trans hM hNE hr0 hr1
  rcases exec_del_succ hM hNE hLoop hrn hs9 hp9 hF1 with hh | ⟨p8, m2, t2, c2, hp8, hF2, hr2⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r01 hh)
  have r02 := internalReach_trans hM hNE r01 hr2
  rcases exec_del_succ hM hNE hLoop hrn hs8 hp8 hF2 with hh | ⟨p7, m3, t3, c3, hp7, hF3, hr3⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r02 hh)
  have r03 := internalReach_trans hM hNE r02 hr3
  rcases exec_del_succ hM hNE hLoop hrn hs7 hp7 hF3 with hh | ⟨p6, m4, t4, c4, hp6, hF4, hr4⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
  have r04 := internalReach_trans hM hNE r03 hr4
  rcases exec_del_succ hM hNE hLoop hrn hs6 hp6 hF4 with hh | ⟨p5, m5, t5, c5, hp5, hF5, hr5⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r04 hh)
  have r05 := internalReach_trans hM hNE r04 hr5
  rcases exec_del_succ hM hNE hLoop hrn hs5 hp5 hF5 with hh | ⟨p4, m6, t6, c6, hp4, hF6, hr6⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r05 hh)
  have r06 := internalReach_trans hM hNE r05 hr6
  rcases exec_del_succ hM hNE hLoop hrn hs4 hp4 hF6 with hh | ⟨p3, m7, t7, c7, hp3, hF7, hr7⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r06 hh)
  have r07 := internalReach_trans hM hNE r06 hr7
  rcases exec_del_succ hM hNE hLoop hrn hs3 hp3 hF7 with hh | ⟨p2, m8, t8, c8, hp2, hF8, hr8⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r07 hh)
  have r08 := internalReach_trans hM hNE r07 hr8
  rcases exec_del_succ hM hNE hLoop hrn hs2 hp2 hF8 with hh | ⟨p1, m9, t9, c9, hp1, hF9, hr9⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r08 hh)
  have r09 := internalReach_trans hM hNE r08 hr9
  rcases exec_del_1 hM hNE hLoop hrn hs1 hp1 hF9 with hh | ⟨p0, m10, t10, c10, hp0, hF10, hr10⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r09 hh)
  exact Or.inr ⟨p0, m10, t10, c10, hp0, hF10, internalReach_trans hM hNE r09 hr10⟩

/-- Generic extractor for the 8 items pushed by `GenAx(a, b, c)` starting from `(r0, 0, u, 0)` (with `b = Y - u`):
    depth `k ∈ {0..6}` selects: 0→h6, 1→h5, 2→h4, 3→h3, 4→h2, 5→h1, 6→rho8. -/
private theorem canPush_genAx_item (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    (k : Nat) (hk : k ≤ 6) {x y opZ u target : V}
    (hx : NatObject E x) (hy : NatObject E y) (hopZ : NatObject E opZ) (hu : NatObject E u)
    (htarget : ∀ Y r8 h1 h2 h3 h4 h5 h6,
      Add E u y Y → CalcRho8 E Y opZ x u r8 →
      CalcHead1 E x Y h1 → CalcHead2 E x Y opZ h2 → CalcHead3 E x Y opZ h3 →
      CalcHead4 E x Y opZ h4 → CalcHead5 E x Y h5 → CalcHead6 E x Y opZ h6 →
      (k = 0 ∧ target = h6) ∨ (k = 1 ∧ target = h5) ∨ (k = 2 ∧ target = h4) ∨
      (k = 3 ∧ target = h3) ∨ (k = 4 ∧ target = h2) ∨ (k = 5 ∧ target = h1) ∨ (k = 6 ∧ target = r8)) :
    CanPush (E := E) target := by
  apply canPush_of_clean hM hNE
  intro r_next hrn
  let r_del := cmdDelSecondN hM hNE (7 - k) r_next
  let r_save := cmdSaveT hM hNE r_del
  let r_sh := cmdShiftN hM hNE (k + 2) r_save
  let r_gen := cmdGenAx hM hNE x y opZ r_sh
  have hr_delN := cmdDelSecondN_nat hM hNE (7 - k) hrn
  have hr_saveN := cmdSaveT_nat hM hNE hr_delN
  have hr_shN := cmdShiftN_nat hM hNE (k + 2) hr_saveN
  have hr_genN := cmdGenAx_nat hM hNE hx hy hopZ hr_shN
  -- Prepend MP(u) if u ≠ 0 to set B = u
  have hsetup : ∃ r_start, NatObject E r_start ∧
      ∀ r0 r6 m t code, CleanFrame (E := E) r0 r_start (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m t code →
        ∃ m1 t1 c1, CleanFrame (E := E) r0 r_gen (zeroV hM hNE) u r6 (zeroV hM hNE) m1 t1 c1 ∧ InternalReach E code c1 := by
    by_cases hu0 : Empty E u
    · have := empty_unique hM hNE hu0 (zeroV_empty hM hNE); subst this
      exact ⟨r_gen, hr_genN, fun r0 r6 m t code hF => by
        have hcN : NatObject E code := by rcases hF with ⟨_, _, _, _, hfc⟩; exact frameCodeV_nat hfc
        exact ⟨m, t, code, hF, internalReach_refl hM hNE hcN⟩⟩
    · refine ⟨cmdMP hM hNE u r_gen, cmdMP_nat hM hNE hu hr_genN, fun r0 r6 m t code hF => ?_⟩
      obtain ⟨ic, hic, _⟩ := calcIc_exists hM hNE (zeroV_nat hM hNE) hu
      have hne : zeroV hM hNE ≠ ic := fun heq => calcIc_ne_zero_of_ne_zero hM hNE hic hu0 (heq ▸ zeroV_empty hM hNE)
      exact exec_mp_neq hM hNE hLoop hu hr_genN
        ((add_iff_eq hM hNE (zeroV_nat hM hNE) hu).mpr (zero_addV hM hNE u hu).symm) hic hne hF
  obtain ⟨r_start, hr_startN, hrun_setup⟩ := hsetup
  refine ⟨r_start, hr_startN, fun r0 r6 m t code hF => ?_⟩
  obtain ⟨m0, t0, c0, hF0, hr0⟩ := hrun_setup r0 r6 m t code hF
  obtain ⟨uc, r8, h1, h2, h3, h4, h5, h6, s1, s2, s3, s4, s5, s6, s7, s8, s9, top, m1, t1, c1,
    _, hr8, hh1, hh2, hh3, hh4, hh5, hh6, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, _, hF1, hr1⟩ :=
    exec_genAx hM hNE hLoop hx hy hopZ hr_shN
      ((add_iff_eq hM hNE (zeroV_nat hM hNE) hx).mpr (zero_addV hM hNE x hx).symm)
      (addV_spec hM hNE hu hy) hF0
  have r01 := internalReach_trans hM hNE hr0 hr1
  have hspec := htarget (addV hM hNE u y) r8 h1 h2 h3 h4 h5 h6 (addV_spec hM hNE hu hy) hr8 hh1 hh2 hh3 hh4 hh5 hh6
  -- Do 2 Shifts first (puts h6 in T, h5 in A, s7 on stack)
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE (k + 1) hr_saveN) hs9 hF1 with hh | ⟨m2, t2, c2, hF2, hr2⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r01 hh)
  have r02 := internalReach_trans hM hNE r01 hr2
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE k hr_saveN) hs8 hF2 with hh | ⟨m3, t3, c3, hF3, hr3⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r02 hh)
  have r03 := internalReach_trans hM hNE r02 hr3
  -- Case split on k ∈ {0..6}
  rcases hspec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- k = 0: target = h6, stack = s7 (7 items above r0)
    rcases exec_saveT hM hNE hLoop hr_delN hF3 with hh | ⟨p7, ms, ts, cs, hp7, hFs, hrs⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
    have r0s := internalReach_trans hM hNE r03 hrs
    rcases exec_del_succ hM hNE hLoop hrn hs7 hp7 hFs with hh | ⟨p6, md6, td6, cd6, hp6, hFd6, hrd6⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0s hh)
    have r0d6 := internalReach_trans hM hNE r0s hrd6
    rcases exec_del_succ hM hNE hLoop hrn hs6 hp6 hFd6 with hh | ⟨p5, md5, td5, cd5, hp5, hFd5, hrd5⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d6 hh)
    have r0d5 := internalReach_trans hM hNE r0d6 hrd5
    rcases exec_del_succ hM hNE hLoop hrn hs5 hp5 hFd5 with hh | ⟨p4, md4, td4, cd4, hp4, hFd4, hrd4⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d5 hh)
    have r0d4 := internalReach_trans hM hNE r0d5 hrd4
    rcases exec_del_succ hM hNE hLoop hrn hs4 hp4 hFd4 with hh | ⟨p3, md3, td3, cd3, hp3, hFd3, hrd3⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d4 hh)
    have r0d3 := internalReach_trans hM hNE r0d4 hrd3
    rcases exec_del_succ hM hNE hLoop hrn hs3 hp3 hFd3 with hh | ⟨p2, md2, td2, cd2, hp2, hFd2, hrd2⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d3 hh)
    have r0d2 := internalReach_trans hM hNE r0d3 hrd2
    rcases exec_del_succ hM hNE hLoop hrn hs2 hp2 hFd2 with hh | ⟨p1, md1, td1, cd1, hp1, hFd1, hrd1⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d2 hh)
    have r0d1 := internalReach_trans hM hNE r0d2 hrd1
    rcases exec_del_1 hM hNE hLoop hrn hs1 hp1 hFd1 with hh | ⟨p0, md0, td0, cd0, hp0, hFd0, hrd0⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d1 hh)
    exact Or.inr ⟨p0, md0, td0, cd0, hp0, hFd0, internalReach_trans hM hNE r0d1 hrd0⟩
  · -- k = 1: target = h5, 1 more Shift → s6 (6 items above r0)
    rcases exec_shift hM hNE hLoop hr_saveN hs7 hF3 with hh | ⟨m4, t4, c4, hF4, hr4⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
    have r04 := internalReach_trans hM hNE r03 hr4
    rcases exec_saveT hM hNE hLoop hr_delN hF4 with hh | ⟨p6, ms, ts, cs, hp6, hFs, hrs⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r04 hh)
    have r0s := internalReach_trans hM hNE r04 hrs
    rcases exec_del_succ hM hNE hLoop hrn hs6 hp6 hFs with hh | ⟨p5, md5, td5, cd5, hp5, hFd5, hrd5⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0s hh)
    have r0d5 := internalReach_trans hM hNE r0s hrd5
    rcases exec_del_succ hM hNE hLoop hrn hs5 hp5 hFd5 with hh | ⟨p4, md4, td4, cd4, hp4, hFd4, hrd4⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d5 hh)
    have r0d4 := internalReach_trans hM hNE r0d5 hrd4
    rcases exec_del_succ hM hNE hLoop hrn hs4 hp4 hFd4 with hh | ⟨p3, md3, td3, cd3, hp3, hFd3, hrd3⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d4 hh)
    have r0d3 := internalReach_trans hM hNE r0d4 hrd3
    rcases exec_del_succ hM hNE hLoop hrn hs3 hp3 hFd3 with hh | ⟨p2, md2, td2, cd2, hp2, hFd2, hrd2⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d3 hh)
    have r0d2 := internalReach_trans hM hNE r0d3 hrd2
    rcases exec_del_succ hM hNE hLoop hrn hs2 hp2 hFd2 with hh | ⟨p1, md1, td1, cd1, hp1, hFd1, hrd1⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d2 hh)
    have r0d1 := internalReach_trans hM hNE r0d2 hrd1
    rcases exec_del_1 hM hNE hLoop hrn hs1 hp1 hFd1 with hh | ⟨p0, md0, td0, cd0, hp0, hFd0, hrd0⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d1 hh)
    exact Or.inr ⟨p0, md0, td0, cd0, hp0, hFd0, internalReach_trans hM hNE r0d1 hrd0⟩
  · -- k = 2: target = h4, 2 more Shifts → s5 (5 items above r0)
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 1 hr_saveN) hs7 hF3 with hh | ⟨m4, t4, c4, hF4, hr4⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
    have r04 := internalReach_trans hM hNE r03 hr4
    rcases exec_shift hM hNE hLoop hr_saveN hs6 hF4 with hh | ⟨m5, t5, c5, hF5, hr5⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r04 hh)
    have r05 := internalReach_trans hM hNE r04 hr5
    rcases exec_saveT hM hNE hLoop hr_delN hF5 with hh | ⟨p5, ms, ts, cs, hp5, hFs, hrs⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r05 hh)
    have r0s := internalReach_trans hM hNE r05 hrs
    rcases exec_del_succ hM hNE hLoop hrn hs5 hp5 hFs with hh | ⟨p4, md4, td4, cd4, hp4, hFd4, hrd4⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0s hh)
    have r0d4 := internalReach_trans hM hNE r0s hrd4
    rcases exec_del_succ hM hNE hLoop hrn hs4 hp4 hFd4 with hh | ⟨p3, md3, td3, cd3, hp3, hFd3, hrd3⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d4 hh)
    have r0d3 := internalReach_trans hM hNE r0d4 hrd3
    rcases exec_del_succ hM hNE hLoop hrn hs3 hp3 hFd3 with hh | ⟨p2, md2, td2, cd2, hp2, hFd2, hrd2⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d3 hh)
    have r0d2 := internalReach_trans hM hNE r0d3 hrd2
    rcases exec_del_succ hM hNE hLoop hrn hs2 hp2 hFd2 with hh | ⟨p1, md1, td1, cd1, hp1, hFd1, hrd1⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d2 hh)
    have r0d1 := internalReach_trans hM hNE r0d2 hrd1
    rcases exec_del_1 hM hNE hLoop hrn hs1 hp1 hFd1 with hh | ⟨p0, md0, td0, cd0, hp0, hFd0, hrd0⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d1 hh)
    exact Or.inr ⟨p0, md0, td0, cd0, hp0, hFd0, internalReach_trans hM hNE r0d1 hrd0⟩
  · -- k = 3: target = h3, 3 more Shifts → s4 (4 items above r0)
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 2 hr_saveN) hs7 hF3 with hh | ⟨m4, t4, c4, hF4, hr4⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
    have r04 := internalReach_trans hM hNE r03 hr4
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 1 hr_saveN) hs6 hF4 with hh | ⟨m5, t5, c5, hF5, hr5⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r04 hh)
    have r05 := internalReach_trans hM hNE r04 hr5
    rcases exec_shift hM hNE hLoop hr_saveN hs5 hF5 with hh | ⟨m6, t6, c6, hF6, hr6⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r05 hh)
    have r06 := internalReach_trans hM hNE r05 hr6
    rcases exec_saveT hM hNE hLoop hr_delN hF6 with hh | ⟨p4, ms, ts, cs, hp4, hFs, hrs⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r06 hh)
    have r0s := internalReach_trans hM hNE r06 hrs
    rcases exec_del_succ hM hNE hLoop hrn hs4 hp4 hFs with hh | ⟨p3, md3, td3, cd3, hp3, hFd3, hrd3⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0s hh)
    have r0d3 := internalReach_trans hM hNE r0s hrd3
    rcases exec_del_succ hM hNE hLoop hrn hs3 hp3 hFd3 with hh | ⟨p2, md2, td2, cd2, hp2, hFd2, hrd2⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d3 hh)
    have r0d2 := internalReach_trans hM hNE r0d3 hrd2
    rcases exec_del_succ hM hNE hLoop hrn hs2 hp2 hFd2 with hh | ⟨p1, md1, td1, cd1, hp1, hFd1, hrd1⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d2 hh)
    have r0d1 := internalReach_trans hM hNE r0d2 hrd1
    rcases exec_del_1 hM hNE hLoop hrn hs1 hp1 hFd1 with hh | ⟨p0, md0, td0, cd0, hp0, hFd0, hrd0⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d1 hh)
    exact Or.inr ⟨p0, md0, td0, cd0, hp0, hFd0, internalReach_trans hM hNE r0d1 hrd0⟩
  · -- k = 4: target = h2, 4 more Shifts → s3 (3 items above r0)
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 3 hr_saveN) hs7 hF3 with hh | ⟨m4, t4, c4, hF4, hr4⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
    have r04 := internalReach_trans hM hNE r03 hr4
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 2 hr_saveN) hs6 hF4 with hh | ⟨m5, t5, c5, hF5, hr5⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r04 hh)
    have r05 := internalReach_trans hM hNE r04 hr5
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 1 hr_saveN) hs5 hF5 with hh | ⟨m6, t6, c6, hF6, hr6⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r05 hh)
    have r06 := internalReach_trans hM hNE r05 hr6
    rcases exec_shift hM hNE hLoop hr_saveN hs4 hF6 with hh | ⟨m7, t7, c7, hF7, hr7⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r06 hh)
    have r07 := internalReach_trans hM hNE r06 hr7
    rcases exec_saveT hM hNE hLoop hr_delN hF7 with hh | ⟨p3, ms, ts, cs, hp3, hFs, hrs⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r07 hh)
    have r0s := internalReach_trans hM hNE r07 hrs
    rcases exec_del_succ hM hNE hLoop hrn hs3 hp3 hFs with hh | ⟨p2, md2, td2, cd2, hp2, hFd2, hrd2⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0s hh)
    have r0d2 := internalReach_trans hM hNE r0s hrd2
    rcases exec_del_succ hM hNE hLoop hrn hs2 hp2 hFd2 with hh | ⟨p1, md1, td1, cd1, hp1, hFd1, hrd1⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d2 hh)
    have r0d1 := internalReach_trans hM hNE r0d2 hrd1
    rcases exec_del_1 hM hNE hLoop hrn hs1 hp1 hFd1 with hh | ⟨p0, md0, td0, cd0, hp0, hFd0, hrd0⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d1 hh)
    exact Or.inr ⟨p0, md0, td0, cd0, hp0, hFd0, internalReach_trans hM hNE r0d1 hrd0⟩
  · -- k = 5: target = h1, 5 more Shifts → s2 (2 items above r0)
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 4 hr_saveN) hs7 hF3 with hh | ⟨m4, t4, c4, hF4, hr4⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
    have r04 := internalReach_trans hM hNE r03 hr4
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 3 hr_saveN) hs6 hF4 with hh | ⟨m5, t5, c5, hF5, hr5⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r04 hh)
    have r05 := internalReach_trans hM hNE r04 hr5
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 2 hr_saveN) hs5 hF5 with hh | ⟨m6, t6, c6, hF6, hr6⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r05 hh)
    have r06 := internalReach_trans hM hNE r05 hr6
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 1 hr_saveN) hs4 hF6 with hh | ⟨m7, t7, c7, hF7, hr7⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r06 hh)
    have r07 := internalReach_trans hM hNE r06 hr7
    rcases exec_shift hM hNE hLoop hr_saveN hs3 hF7 with hh | ⟨m8, t8, c8, hF8, hr8⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r07 hh)
    have r08 := internalReach_trans hM hNE r07 hr8
    rcases exec_saveT hM hNE hLoop hr_delN hF8 with hh | ⟨p2, ms, ts, cs, hp2, hFs, hrs⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r08 hh)
    have r0s := internalReach_trans hM hNE r08 hrs
    rcases exec_del_succ hM hNE hLoop hrn hs2 hp2 hFs with hh | ⟨p1, md1, td1, cd1, hp1, hFd1, hrd1⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0s hh)
    have r0d1 := internalReach_trans hM hNE r0s hrd1
    rcases exec_del_1 hM hNE hLoop hrn hs1 hp1 hFd1 with hh | ⟨p0, md0, td0, cd0, hp0, hFd0, hrd0⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0d1 hh)
    exact Or.inr ⟨p0, md0, td0, cd0, hp0, hFd0, internalReach_trans hM hNE r0d1 hrd0⟩
  · -- k = 6: target = rho8, 6 more Shifts → s1 (1 item above r0)
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 5 hr_saveN) hs7 hF3 with hh | ⟨m4, t4, c4, hF4, hr4⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
    have r04 := internalReach_trans hM hNE r03 hr4
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 4 hr_saveN) hs6 hF4 with hh | ⟨m5, t5, c5, hF5, hr5⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r04 hh)
    have r05 := internalReach_trans hM hNE r04 hr5
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 3 hr_saveN) hs5 hF5 with hh | ⟨m6, t6, c6, hF6, hr6⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r05 hh)
    have r06 := internalReach_trans hM hNE r05 hr6
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 2 hr_saveN) hs4 hF6 with hh | ⟨m7, t7, c7, hF7, hr7⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r06 hh)
    have r07 := internalReach_trans hM hNE r06 hr7
    rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 1 hr_saveN) hs3 hF7 with hh | ⟨m8, t8, c8, hF8, hr8⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r07 hh)
    have r08 := internalReach_trans hM hNE r07 hr8
    rcases exec_shift hM hNE hLoop hr_saveN hs2 hF8 with hh | ⟨m9, t9, c9, hF9, hr9⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r08 hh)
    have r09 := internalReach_trans hM hNE r08 hr9
    rcases exec_saveT hM hNE hLoop hr_delN hF9 with hh | ⟨p1, ms, ts, cs, hp1, hFs, hrs⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r09 hh)
    have r0s := internalReach_trans hM hNE r09 hrs
    rcases exec_del_1 hM hNE hLoop hrn hs1 hp1 hFs with hh | ⟨p0, md0, td0, cd0, hp0, hFd0, hrd0⟩
    · exact Or.inl (internalHaltsFrom_of_reach hM hNE r0s hh)
    exact Or.inr ⟨p0, md0, td0, cd0, hp0, hFd0, internalReach_trans hM hNE r0s hrd0⟩

private theorem canPush_axiom (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {x : V} (hax : CalcAxiom E x) : CanPush (E := E) x := by
  rcases hax with h0 | ⟨a, b, c, u, hr8⟩ | ⟨a, b, hh1⟩ | ⟨a, b, c, hh2⟩ | ⟨a, b, c, hh3⟩ |
    ⟨a, b, c, hh4⟩ | ⟨a, b, hh5⟩ | ⟨a, b, c, hh6⟩ | ⟨a, b, c, hgf⟩
  · exact canPush_zero hM hNE hLoop h0
  · obtain ⟨d, hd, hadd⟩ := sub_exists hM hNE hr8.2.2.2.1 a hr8.1 (hr8.2.2.2.2.1.elim Or.inr Or.inl)
    exact canPush_genAx_item hM hNE hLoop 6 (by omega) hr8.2.2.1 hd hr8.2.1 hr8.2.2.2.1
      (fun Y r8' _ _ _ _ _ _ hY hr8' _ _ _ _ _ _ => by
        have := add_unique hM hNE hY hadd; subst this
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, calcRho8_unique hM hNE hr8 hr8'⟩))))))
  · exact canPush_genAx_item hM hNE hLoop 5 (by omega) hh1.1 hh1.2.1 (zeroV_nat hM hNE) (zeroV_nat hM hNE)
      (fun Y _ h1' _ _ _ _ _ hY _ hh1' _ _ _ _ _ => by
        have := (add_iff_eq hM hNE (zeroV_nat hM hNE) hh1.2.1).mp hY |>.trans (zero_addV hM hNE b hh1.2.1); subst this
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, calcHead1_unique hM hNE hh1 hh1'⟩))))))
  · exact canPush_genAx_item hM hNE hLoop 4 (by omega) hh2.1 hh2.2.1 hh2.2.2.1 (zeroV_nat hM hNE)
      (fun Y _ _ h2' _ _ _ _ hY _ _ hh2' _ _ _ _ => by
        have := (add_iff_eq hM hNE (zeroV_nat hM hNE) hh2.2.1).mp hY |>.trans (zero_addV hM hNE b hh2.2.1); subst this
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, calcHead2_unique hM hNE hh2 hh2'⟩)))))
  · exact canPush_genAx_item hM hNE hLoop 3 (by omega) hh3.1 hh3.2.1 hh3.2.2.1 (zeroV_nat hM hNE)
      (fun Y _ _ _ h3' _ _ _ hY _ _ _ hh3' _ _ _ => by
        have := (add_iff_eq hM hNE (zeroV_nat hM hNE) hh3.2.1).mp hY |>.trans (zero_addV hM hNE b hh3.2.1); subst this
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, calcHead3_unique hM hNE hh3 hh3'⟩))))
  · exact canPush_genAx_item hM hNE hLoop 2 (by omega) hh4.1 hh4.2.1 hh4.2.2.1 (zeroV_nat hM hNE)
      (fun Y _ _ _ _ h4' _ _ hY _ _ _ _ hh4' _ _ => by
        have := (add_iff_eq hM hNE (zeroV_nat hM hNE) hh4.2.1).mp hY |>.trans (zero_addV hM hNE b hh4.2.1); subst this
        exact Or.inr (Or.inr (Or.inl ⟨rfl, calcHead4_unique hM hNE hh4 hh4'⟩)))
  · exact canPush_genAx_item hM hNE hLoop 1 (by omega) hh5.1 hh5.2.1 (zeroV_nat hM hNE) (zeroV_nat hM hNE)
      (fun Y _ _ _ _ _ h5' _ hY _ _ _ _ _ hh5' _ => by
        have := (add_iff_eq hM hNE (zeroV_nat hM hNE) hh5.2.1).mp hY |>.trans (zero_addV hM hNE b hh5.2.1); subst this
        exact Or.inr (Or.inl ⟨rfl, calcHead5_unique hM hNE hh5 hh5'⟩))
  · exact canPush_genAx_item hM hNE hLoop 0 (by omega) hh6.1 hh6.2.1 hh6.2.2.1 (zeroV_nat hM hNE)
      (fun Y _ _ _ _ _ _ h6' hY _ _ _ _ _ _ hh6' => by
        have := (add_iff_eq hM hNE (zeroV_nat hM hNE) hh6.2.1).mp hY |>.trans (zero_addV hM hNE b hh6.2.1); subst this
        exact Or.inl ⟨rfl, calcHead6_unique hM hNE hh6 hh6'⟩)
  · exact canPush_gateF hM hNE hLoop hgf

private theorem canPush_mp (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {a imp x : V} (hxN : NatObject E x) (hic : CalcIc E a x imp)
    (ha : CanPush (E := E) a) (himp : CanPush (E := E) imp) : CanPush (E := E) x := by
  apply canPush_of_clean hM hNE
  intro r_next hrn
  let r_del := cmdDelSecond hM hNE r_next
  let r_save := cmdSaveT hM hNE r_del
  let r_mp := cmdMP hM hNE x r_save
  let r_sh2 := cmdShift hM hNE (cmdShift hM hNE r_mp)
  have hr_delN := cmdDelSecond_nat hM hNE hrn
  have hr_saveN := cmdSaveT_nat hM hNE hr_delN
  have hr_mpN := cmdMP_nat hM hNE hxN hr_saveN
  have hr_sh2N := cmdShift_nat hM hNE (cmdShift_nat hM hNE hr_mpN)
  obtain ⟨r_a, hr_aN, hrun_a⟩ := canPush_apply hM hNE ha hr_sh2N
  obtain ⟨r_imp, hr_impN, hrun_imp⟩ := canPush_apply hM hNE himp hr_aN
  refine ⟨r_imp, hr_impN, fun r0 r6 m t code hF => ?_⟩
  rcases hrun_imp r0 r6 m t code hF with hh | ⟨s_imp, m1, t1, c1, hs_imp, hF1, hr01⟩
  · exact Or.inl hh
  rcases hrun_a s_imp r6 m1 t1 c1 hF1 with hh | ⟨s_a, m2, t2, c2, hs_a, hF2, hr12⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE hr01 hh)
  have r02 := internalReach_trans hM hNE hr01 hr12
  rcases exec_shift hM hNE hLoop (cmdShift_nat hM hNE hr_mpN) hs_a hF2 with hh | ⟨m3, t3, c3, hF3, hr23⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r02 hh)
  have r03 := internalReach_trans hM hNE r02 hr23
  rcases exec_shift hM hNE hLoop hr_mpN hs_imp hF3 with hh | ⟨m4, t4, c4, hF4, hr34⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
  have r04 := internalReach_trans hM hNE r03 hr34
  obtain ⟨s0, m5, t5, c5, hs0, hF5, hr45⟩ :=
    exec_mp_eq hM hNE hLoop hxN hr_saveN ((add_iff_eq hM hNE (zeroV_nat hM hNE) hxN).mpr (zero_addV hM hNE x hxN).symm) hic hF4
  have r05 := internalReach_trans hM hNE r04 hr45
  rcases exec_saveT hM hNE hLoop hr_delN hF5 with hh | ⟨sx, m6, t6, c6, hsx, hF6, hr56⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r05 hh)
  have r06 := internalReach_trans hM hNE r05 hr56
  rcases exec_delSecond hM hNE hLoop hrn hs0 hsx hF6 with hh | ⟨r0', m7, t7, c7, hr0', hF7, hr67⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r06 hh)
  exact Or.inr ⟨r0', m7, t7, c7, hr0', hF7, internalReach_trans hM hNE r06 hr67⟩

private theorem canPush_uc (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {a b x : V} (ha : NatObject E a) (huc : CalcUc E a b x)
    (hb : CanPush (E := E) b) : CanPush (E := E) x := by
  apply canPush_of_clean hM hNE
  intro r_next hrn
  let r_save := cmdSaveT hM hNE r_next
  let r_sh9 := cmdShiftN hM hNE 9 r_save
  let r_gen := cmdGenAx hM hNE (zeroV hM hNE) (zeroV hM hNE) (zeroV hM hNE) r_sh9
  let r_pop := cmdShift hM hNE r_gen
  have hr_saveN := cmdSaveT_nat hM hNE hrn
  have hr_sh9N := cmdShiftN_nat hM hNE 9 hr_saveN
  have hr_genN := cmdGenAx_nat hM hNE (zeroV_nat hM hNE) (zeroV_nat hM hNE) (zeroV_nat hM hNE) hr_sh9N
  have hr_popN := cmdShift_nat hM hNE hr_genN
  have hsetup : ∃ r_after_b, NatObject E r_after_b ∧
      ∀ sb r6 m t code, CleanFrame (E := E) sb r_after_b (zeroV hM hNE) (zeroV hM hNE) r6 (zeroV hM hNE) m t code →
        ∃ m1 t1 c1, CleanFrame (E := E) sb r_pop (zeroV hM hNE) a r6 (zeroV hM hNE) m1 t1 c1 ∧ InternalReach E code c1 := by
    by_cases ha0 : Empty E a
    · have := empty_unique hM hNE ha0 (zeroV_empty hM hNE); subst this
      exact ⟨r_pop, hr_popN, fun sb r6 m t code hF => by
        have hcN : NatObject E code := by rcases hF with ⟨_, _, _, _, hfc⟩; exact frameCodeV_nat hfc
        exact ⟨m, t, code, hF, internalReach_refl hM hNE hcN⟩⟩
    · refine ⟨cmdMP hM hNE a r_pop, cmdMP_nat hM hNE ha hr_popN, fun sb r6 m t code hF => ?_⟩
      obtain ⟨ic, hic, _⟩ := calcIc_exists hM hNE (zeroV_nat hM hNE) ha
      have hne : zeroV hM hNE ≠ ic := fun heq => calcIc_ne_zero_of_ne_zero hM hNE hic ha0 (heq ▸ zeroV_empty hM hNE)
      exact exec_mp_neq hM hNE hLoop ha hr_popN
        ((add_iff_eq hM hNE (zeroV_nat hM hNE) ha).mpr (zero_addV hM hNE a ha).symm) hic hne hF
  obtain ⟨r_after_b, hr_abN, hrun_setup⟩ := hsetup
  obtain ⟨r_b, hr_bN, hrun_b⟩ := canPush_apply hM hNE hb hr_abN
  refine ⟨r_b, hr_bN, fun r0 r6 m t code hF => ?_⟩
  rcases hrun_b r0 r6 m t code hF with hh | ⟨sb, m0, t0, c0, hsb, hF0, hr0⟩
  · exact Or.inl hh
  obtain ⟨m1, t1, c1, hF1, hr1⟩ := hrun_setup sb r6 m0 t0 c0 hF0
  have r01 := internalReach_trans hM hNE hr0 hr1
  rcases exec_shift hM hNE hLoop hr_genN hsb hF1 with hh | ⟨m2, t2, c2, hF2, hr2⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r01 hh)
  have r02 := internalReach_trans hM hNE r01 hr2
  have hbN : NatObject E b := hsb.1
  obtain ⟨uc', _, _, _, _, _, _, _, s1, s2, s3, s4, s5, s6, s7, s8, s9, _, m3, t3, c3,
    huc', _, _, _, _, _, _, _, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, _, hF3, hr3⟩ :=
    exec_genAx hM hNE hLoop (zeroV_nat hM hNE) (zeroV_nat hM hNE) (zeroV_nat hM hNE) hr_sh9N
      (add_zero hM hNE hbN (zeroV_empty hM hNE)) (add_zero hM hNE ha (zeroV_empty hM hNE)) hF2
  have huceq : uc' = x := calcUc_unique hM hNE huc' huc; subst huceq
  have r03 := internalReach_trans hM hNE r02 hr3
  -- 9 Shifts pop h6, h5, h4, h3, h2, h1, rho8, uc', 0 → puts uc' in T and restores stack to r0!
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 8 hr_saveN) hs9 hF3 with hh | ⟨m4, t4, c4, hF4, hr4⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r03 hh)
  have r04 := internalReach_trans hM hNE r03 hr4
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 7 hr_saveN) hs8 hF4 with hh | ⟨m5, t5, c5, hF5, hr5⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r04 hh)
  have r05 := internalReach_trans hM hNE r04 hr5
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 6 hr_saveN) hs7 hF5 with hh | ⟨m6, t6, c6, hF6, hr6⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r05 hh)
  have r06 := internalReach_trans hM hNE r05 hr6
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 5 hr_saveN) hs6 hF6 with hh | ⟨m7, t7, c7, hF7, hr7⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r06 hh)
  have r07 := internalReach_trans hM hNE r06 hr7
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 4 hr_saveN) hs5 hF7 with hh | ⟨m8, t8, c8, hF8, hr8⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r07 hh)
  have r08 := internalReach_trans hM hNE r07 hr8
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 3 hr_saveN) hs4 hF8 with hh | ⟨m9, t9, c9, hF9, hr9⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r08 hh)
  have r09 := internalReach_trans hM hNE r08 hr9
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 2 hr_saveN) hs3 hF9 with hh | ⟨m10, t10, c10, hF10, hr10⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r09 hh)
  have r010 := internalReach_trans hM hNE r09 hr10
  rcases exec_shift hM hNE hLoop (cmdShiftN_nat hM hNE 1 hr_saveN) hs2 hF10 with hh | ⟨m11, t11, c11, hF11, hr11⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r010 hh)
  have r011 := internalReach_trans hM hNE r010 hr11
  rcases exec_shift hM hNE hLoop hr_saveN hs1 hF11 with hh | ⟨m12, t12, c12, hF12, hr12⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r011 hh)
  have r012 := internalReach_trans hM hNE r011 hr12
  rcases exec_saveT hM hNE hLoop hrn hF12 with hh | ⟨r0', m13, t13, c13, hr0', hF13, hr13⟩
  · exact Or.inl (internalHaltsFrom_of_reach hM hNE r012 hh)
  exact Or.inr ⟨r0', m13, t13, c13, hr0', hF13, internalReach_trans hM hNE r012 hr13⟩

private theorem internalProvC1_implies_canPush1 (hM : Model E) (hNE : Nonempty V)
    (hLoop : InternalLoopStep E) (hProv : InternalProvC1 E) :
    CanPush (E := E) (numV hM hNE 1) := by
  rcases hProv with ⟨len, f, last, one, ⟨hlenN, _, hfun, hnat, hderiv⟩, hlast, hone, hflast⟩
  have hone_eq : one = numV hM hNE 1 := numeral_unique hM hNE hone (numV_numeral hM hNE 1)
  rw [hone_eq] at hflast
  let body : Formula := .all (.imp (.mem 0 1) (.imp (.mem 0 2) (.all (.imp (fAt 4 1 0) (fCanPush 0)))))
  let env : Nat → V := fun i => if i = 0 then len else f
  have hB : Bound body 3 :=
    ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fCanPush (by omega)⟩⟩⟩
  have hind := omega_induction hM hNE 2 body hB env
    (fun z hz i hiz _ _ _ => False.elim (hz i hiz))
    (fun k k' _ hkk' ih i hik' hilen x hfix => by
      have hfix' : At E f i x := (eval_fAt _ _ _ _).mp hfix
      have hxN : NatObject E x := hnat i x hilen hfix'
      rcases (hkk' i).mp hik' with hik | rfl
      · have hcp : CanPush (E := E) x := (eval_fCanPush hM hNE 0 _).mp (ih i hik hilen x hfix)
        exact (eval_fCanPush hM hNE 0 _).mpr hcp
      · apply (eval_fCanPush hM hNE 0 _).mpr
        rcases hderiv i x hilen hfix' with hax | ⟨j, k0, a, imp, hji, hki, hfja, hic, hfkimp⟩ | ⟨j, a, b, hji, haN, hfjb, huc⟩
        · exact canPush_axiom hM hNE hLoop hax
        · have hjlen : E j len := nat_lt_trans hM hNE len hlenN j i hji hilen
          have hklen : E k0 len := nat_lt_trans hM hNE len hlenN k0 i hki hilen
          have hcpa : CanPush (E := E) a := (eval_fCanPush hM hNE 0 _).mp (ih j hji hjlen a ((eval_fAt _ _ _ _).mpr hfja))
          have hcpimp : CanPush (E := E) imp := (eval_fCanPush hM hNE 0 _).mp (ih k0 hki hklen imp ((eval_fAt _ _ _ _).mpr hfkimp))
          exact canPush_mp hM hNE hLoop hxN hic hcpa hcpimp
        · have hjlen : E j len := nat_lt_trans hM hNE len hlenN j i hji hilen
          have hcpb : CanPush (E := E) b := (eval_fCanPush hM hNE 0 _).mp (ih j hji hjlen b ((eval_fAt _ _ _ _).mpr hfjb))
          exact canPush_uc hM hNE hLoop haN huc hcpb)
  have hlast_lt : E last len := (hlast last).mpr (Or.inr rfl)
  exact (eval_fCanPush hM hNE 0 _).mp (hind len hlenN last hlast_lt hlast_lt (numV hM hNE 1) ((eval_fAt _ _ _ _).mpr hflast))

/-! ### Part 4: Inner Drain, Outer Scheduler & Final Halting Proof -/

/-- One arbitrary non-zero step on `r1 = w + 1` either halts or strictly decreases `r1` preserving `r6`. -/
private theorem exec_any_step (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {r0 r1 r2 r3 r6 r7 m t code w ctr : V}
    (hwN : NatObject E w) (_hctrN : NatObject E ctr)
    (hw_rel : (Empty E r1 ∧ w = r6 ∧ Succ E r6 ctr) ∨ (Succ E w r1 ∧ ctr = r6))
    (hF : CleanFrame (E := E) r0 r1 r2 r3 r6 r7 m t code) :
    InternalHaltsFrom E code ∨
    ∃ r0' r1' r2' r3' r7' m' t' code',
      (r1' = w ∨ E r1' w) ∧
      CleanFrame (E := E) r0' r1' r2' r3' ctr r7' m' t' code' ∧
      InternalReach E code code' := by
  rcases hF with ⟨z, hz, hmne, htne, hfc⟩
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  rcases hfc.2.2.1 with ⟨hr0N, hr1N, hr2N, hr3N, _, _, hr6N, hr7N, _⟩
  obtain ⟨op, w', hcw⟩ := cantor_unpair hM hNE w hwN
  have hw'_le : w' = w ∨ E w' w := cantor_le_right hM hNE hcw
  have hL := hLoop r0 r1 r2 r3 r6 r7 m t (zeroV hM hNE) code hr0N hr1N hr2N hr3N hr6N hr7N hfc.1 hfc.2.1 hz hmne htne hfc w ctr op w' hw_rel hcw
  rcases nat_cases hM hNE op hcw.1 with hop0 | ⟨op1, hop1N, hop1s⟩
  · -- op = 0: Shift / Halt
    have hs := hL.1 hop0 (addV hM hNE r2 r7) (numV hM hNE 1) (addV_spec hM hNE hr2N hr7N) (numV_numeral hM hNE 1)
    by_cases h1 : addV hM hNE r2 r7 = numV hM hNE 1
    · exact Or.inl (hs.1 h1)
    · obtain ⟨hd, tl, hcr0⟩ := cantor_unpair hM hNE r0 hr0N
      obtain ⟨m', t', code', hm', ht', hfc', hr'⟩ := hs.2 h1 hd tl hcr0
      exact Or.inr ⟨tl, w', r7, r3, hd, m', t', code', hw'_le, ⟨zeroV hM hNE, hz, hm', ht', hfc'⟩, hr'⟩
  · rcases nat_cases hM hNE op1 hop1N with hop1_0 | ⟨opZ, hopZN, hopZs⟩
    · -- op = 1: Branch A (MP)
      have hop_one : Numeral E 1 op := ⟨op1, hop1_0, hop1s⟩
      obtain ⟨b, w2, hcw'⟩ := cantor_unpair hM hNE w' hcw.2.1
      have hw2_le : w2 = w ∨ E w2 w := by
        rcases cantor_le_right hM hNE hcw' with rfl | hlt
        · exact hw'_le
        · rcases hw'_le with rfl | hlt2
          · exact Or.inr hlt
          · exact Or.inr (nat_lt_trans hM hNE w hwN w2 w' hlt hlt2)
      let B := addV hM hNE r3 b
      have hBN := addV_nat hM hNE hr3N hcw'.1
      obtain ⟨ic, hic, _⟩ := calcIc_exists hM hNE hr2N hBN
      have hA := hL.2.1 hop_one b w2 B ic hcw' (addV_spec hM hNE hr3N hcw'.1) hic
      by_cases heq : r7 = ic
      · obtain ⟨m', t', code', hm', ht', hfc', hr'⟩ := hA.1 heq (cantorV hM hNE (zeroV hM hNE) r0) (cantorV_spec hM hNE (zeroV_nat hM hNE) hr0N)
        exact Or.inr ⟨cantorV hM hNE (zeroV hM hNE) r0, w2, B, B, zeroV hM hNE, m', t', code', hw2_le, ⟨zeroV hM hNE, hz, hm', ht', hfc'⟩, hr'⟩
      · obtain ⟨m', t', code', hm', ht', hfc', hr'⟩ := hA.2 heq
        exact Or.inr ⟨r0, w2, zeroV hM hNE, B, zeroV hM hNE, m', t', code', hw2_le, ⟨zeroV hM hNE, hz, hm', ht', hfc'⟩, hr'⟩
    · -- op = opZ + 2: Branch B (GenAx)
      obtain ⟨x, w1, hcw'⟩ := cantor_unpair hM hNE w' hcw.2.1
      obtain ⟨y, w2, hcw1⟩ := cantor_unpair hM hNE w1 hcw'.2.1
      have hw2_le : w2 = w ∨ E w2 w := by
        have h1 : w1 = w ∨ E w1 w := by
          rcases cantor_le_right hM hNE hcw' with rfl | hlt
          · exact hw'_le
          · rcases hw'_le with rfl | hlt2; exact Or.inr hlt; exact Or.inr (nat_lt_trans hM hNE w hwN w1 w' hlt hlt2)
        rcases cantor_le_right hM hNE hcw1 with rfl | hlt
        · exact h1
        · rcases h1 with rfl | hlt2; exact Or.inr hlt; exact Or.inr (nat_lt_trans hM hNE w hwN w2 w1 hlt hlt2)
      let X := addV hM hNE r7 x; have hXN := addV_nat hM hNE hr7N hcw'.1
      let Y := addV hM hNE r3 y; have hYN := addV_nat hM hNE hr3N hcw1.1
      have hr3leY : E r3 Y ∨ r3 = Y := by
        have hle := addV_le_left hM hNE hr3N y hcw1.1
        exact hle.elim Or.inr Or.inl
      obtain ⟨uc, huc, hucN⟩ := calcUc_exists hM hNE hr3N hr7N
      obtain ⟨r8, hr8, hr8N⟩ := calcRho8_exists hM hNE hYN hopZN hXN hr3N hr3leY
      obtain ⟨h1, hh1, hh1N⟩ := calcHead1_exists hM hNE hXN hYN
      obtain ⟨h2, hh2, hh2N⟩ := calcHead2_exists hM hNE hXN hYN hopZN
      obtain ⟨h3, hh3, hh3N⟩ := calcHead3_exists hM hNE hXN hYN hopZN
      obtain ⟨h4, hh4, hh4N⟩ := calcHead4_exists hM hNE hXN hYN hopZN
      obtain ⟨h5, hh5, hh5N⟩ := calcHead5_exists hM hNE hXN hYN
      obtain ⟨h6, hh6, hh6N⟩ := calcHead6_exists hM hNE hXN hYN hopZN
      let s1 := cantorV hM hNE r2 r0; have hs1 := cantorV_spec hM hNE hr2N hr0N
      let s2 := cantorV hM hNE uc s1; have hs2 := cantorV_spec hM hNE hucN hs1.2.2.1
      let s3 := cantorV hM hNE r8 s2; have hs3 := cantorV_spec hM hNE hr8N hs2.2.2.1
      let s4 := cantorV hM hNE h1 s3; have hs4 := cantorV_spec hM hNE hh1N hs3.2.2.1
      let s5 := cantorV hM hNE h2 s4; have hs5 := cantorV_spec hM hNE hh2N hs4.2.2.1
      let s6 := cantorV hM hNE h3 s5; have hs6 := cantorV_spec hM hNE hh3N hs5.2.2.1
      let s7 := cantorV hM hNE h4 s6; have hs7 := cantorV_spec hM hNE hh4N hs6.2.2.1
      let s8 := cantorV hM hNE h5 s7; have hs8 := cantorV_spec hM hNE hh5N hs7.2.2.1
      let s9 := cantorV hM hNE h6 s8; have hs9 := cantorV_spec hM hNE hh6N hs8.2.2.1
      have htop_ex : ∃ top, (opZ ≠ X ∧ opZ ≠ Y ∧ CalcGateF E X Y opZ top) ∨ ((opZ = X ∨ opZ = Y) ∧ Empty E top) := by
        by_cases c1 : opZ = X
        · exact ⟨zeroV hM hNE, Or.inr ⟨Or.inl c1, hz⟩⟩
        · by_cases c2 : opZ = Y
          · exact ⟨zeroV hM hNE, Or.inr ⟨Or.inr c2, hz⟩⟩
          · obtain ⟨top, htop, _⟩ := calcGateF_exists hM hNE hXN hYN hopZN c1 c2
            exact ⟨top, Or.inl ⟨c1, c2, htop⟩⟩
      obtain ⟨top, htop⟩ := htop_ex
      obtain ⟨m', t', code', hm', ht', hfc', hr'⟩ := hL.2.2 opZ op1 hopZs hop1s x w1 y w2 X Y
        hcw' hcw1 (addV_spec hM hNE hr7N hcw'.1) (addV_spec hM hNE hr3N hcw1.1)
        uc r8 h1 h2 h3 h4 h5 h6 s1 s2 s3 s4 s5 s6 s7 s8 s9 top
        huc hr8 hh1 hh2 hh3 hh4 hh5 hh6 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 htop
      exact Or.inr ⟨s9, w2, top, zeroV hM hNE, zeroV hM hNE, m', t', code', hw2_le, ⟨zeroV hM hNE, hz, hm', ht', hfc'⟩, hr'⟩

/-- Inner Drain: from any clean frame with `r1`, either halts or drains `r1` to `0` keeping `r6`. -/
private theorem inner_drain (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E) :
    ∀ n, NatObject E n → ∀ r1, (r1 = n ∨ E r1 n) →
      ∀ r0 r2 r3 r6 r7 m t code,
        CleanFrame (E := E) r0 r1 r2 r3 r6 r7 m t code →
        InternalHaltsFrom E code ∨
        ∃ r0' r2' r3' r7' m' t' code',
          CleanFrame (E := E) r0' (zeroV hM hNE) r2' r3' r6 r7' m' t' code' ∧
          InternalReach E code code' := by
  -- 0=z, 1=code, 2=t, 3=m, 4=r7, 5=r6, 6=r3, 7=r2, 8=r0, 9=r1, 10=n
  let body : Formula :=
    .all (.imp (.or (.eq 0 1) (.mem 0 1))
      (.all (.all (.all (.all (.all (.all (.all (.all (.all
        (.imp (fEmpty 0) (.imp (fNot (fEmpty 3)) (.imp (fNot (fEmpty 2))
          (.imp (fFrameCodeV1 3 8 9 7 6 0 0 5 4 0 2 1)
            (.or (fInternalHaltsFrom 1)
              (.ex (.ex (.ex (.ex (.ex (.ex (.ex
                (.and (fNot (fEmpty 2)) (.and (fNot (fEmpty 1))
                  (.and (fFrameCodeV1 2 6 7 5 4 7 7 12 3 7 1 0)
                    (fInternalReach 8 0))))))))))))))))))))))))))
  have hB : Bound body 1 :=
    ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
      ⟨bound_fEmpty (by omega), ⟨bound_fNot (bound_fEmpty (by omega)), ⟨bound_fNot (bound_fEmpty (by omega)),
        ⟨bound_fFrameCodeV1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          ⟨bound_fInternalHaltsFrom (by omega),
            ⟨bound_fNot (bound_fEmpty (by omega)), ⟨bound_fNot (bound_fEmpty (by omega)),
              ⟨bound_fFrameCodeV1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
                bound_fInternalReach (by omega) (by omega)⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hind := omega_induction hM hNE 0 body hB (fun _ => Classical.choice hNE)
    (fun z0 hz0 r1 hle r0 r2 r3 r6 r7 m t code z hz hmne htne hfc => by
      dsimp only [eval, pushValue] at hle
      have hr1_0 : r1 = z0 := hle.elim id (fun h => False.elim (hz0 r1 h))
      have hzeq := empty_unique hM hNE hz0 hz
      have hfc' : FrameCodeV E 1 m ⟨r0, r1, r2, r3, z, z, r6, r7, z⟩ t code :=
        (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfc
      rw [hr1_0, hzeq] at hfc'
      exact Or.inr ⟨r0, r2, r3, r7, m, t, code, hmne, htne,
        (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc',
        (eval_fInternalReach hM hNE _ _ _).mpr (internalReach_refl hM hNE (frameCodeV_nat hfc'))⟩)
    (fun n n' hn hnn' ih r1 hle r0 r2 r3 r6 r7 m t code z hz hmne htne hfc => by
      dsimp only [eval, pushValue] at hle
      have hfc' : FrameCodeV E 1 m ⟨r0, r1, r2, r3, z, z, r6, r7, z⟩ t code :=
        (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfc
      rcases hle with hr1eq | hr1n'
      · -- r1 = n' = succ n
        have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
        rw [hr1eq] at hfc'
        have hF : CleanFrame (E := E) r0 n' r2 r3 r6 r7 m t code := ⟨zeroV hM hNE, hz, hmne, htne, hfc'⟩
        rcases exec_any_step hM hNE hLoop hn hfc'.2.2.1.2.2.2.2.2.2.1 (Or.inr ⟨hnn', rfl⟩) hF with hh | ⟨r0', r1', r2', r3', r7', m', t', c', hr1'le, ⟨z', hz', hm', ht', hfc1⟩, hr01⟩
        · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mpr hh)
        · have := empty_unique hM hNE hz' hz; subst this
          rcases ih r1' hr1'le r0' r2' r3' r6 r7' m' t' c' (zeroV hM hNE) hz hm' ht'
            ((eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc1) with hh | ⟨r0'', r2'', r3'', r7'', m'', t'', c'', hm'', ht'', hfc2, hr12⟩
          · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mpr (internalHaltsFrom_of_reach hM hNE hr01 ((eval_fInternalHaltsFrom hM hNE _ _).mp hh)))
          · have hfc2' : FrameCodeV E 1 m'' ⟨r0'', zeroV hM hNE, r2'', r3'', zeroV hM hNE, zeroV hM hNE, r6, r7'', zeroV hM hNE⟩ t'' c'' :=
              (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfc2
            exact Or.inr ⟨r0'', r2'', r3'', r7'', m'', t'', c'', hm'', ht'',
              (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc2',
              (eval_fInternalReach hM hNE _ _ _).mpr (internalReach_trans hM hNE hr01 ((eval_fInternalReach hM hNE _ _ _).mp hr12))⟩
      · have hres : InternalHaltsFrom E code ∨
            ∃ r0' r2' r3' r7' m' t' c', ¬ Empty E m' ∧ ¬ Empty E t' ∧
              FrameCodeV E 1 m' ⟨r0', z, r2', r3', z, z, r6, r7', z⟩ t' c' ∧ InternalReach E code c' := by
          have hih := match (hnn' r1).mp hr1n' with
            | Or.inl hr1n => ih r1 (Or.inr hr1n) r0 r2 r3 r6 r7 m t code z hz hmne htne ((eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc')
            | Or.inr hr1eq => ih r1 (Or.inl hr1eq) r0 r2 r3 r6 r7 m t code z hz hmne htne ((eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc')
          rcases hih with hh | ⟨r0', r2', r3', r7', m', t', c', hm', ht', hfc2, hr2⟩
          · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mp hh)
          · exact Or.inr ⟨r0', r2', r3', r7', m', t', c', hm', ht', (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfc2, (eval_fInternalReach hM hNE _ _ _).mp hr2⟩
        rcases hres with hh | ⟨r0', r2', r3', r7', m', t', c', hm', ht', hfc2, hr2⟩
        · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mpr hh)
        · exact Or.inr ⟨r0', r2', r3', r7', m', t', c', hm', ht', (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc2, (eval_fInternalReach hM hNE _ _ _).mpr hr2⟩)
  intro n hn r1 hle r0 r2 r3 r6 r7 m t code ⟨z, hz, hmne, htne, hfc⟩
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  rcases hind n hn r1 hle r0 r2 r3 r6 r7 m t code (zeroV hM hNE) hz hmne htne
    ((eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc) with hh | ⟨r0', r2', r3', r7', m', t', c', hm', ht', hfc', hr⟩
  · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mp hh)
  · exact Or.inr ⟨r0', r2', r3', r7', m', t', c', ⟨zeroV hM hNE, hz, hm', ht', (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfc'⟩,
      (eval_fInternalReach hM hNE _ _ _).mp hr⟩

/-- Outer Scheduler: from `⟨0,0,0,0,0,0,2,0,0⟩` at `c1`, for every `k ≥ 2`, either halts or reaches `r1 = 0, r6 = k`. -/
private theorem outer_scheduler (hM : Model E) (hNE : Nonempty V) (hLoop : InternalLoopStep E)
    {m0 t0 c1 : V} (hInit : CleanFrame (E := E) (zeroV hM hNE) (zeroV hM hNE) (zeroV hM hNE) (zeroV hM hNE) (numV hM hNE 2) (zeroV hM hNE) m0 t0 c1) :
    ∀ k, NatObject E k → (k = numV hM hNE 2 ∨ E (numV hM hNE 2) k) →
      InternalHaltsFrom E c1 ∨
      ∃ r0 r2 r3 r7 m t code,
        CleanFrame (E := E) r0 (zeroV hM hNE) r2 r3 k r7 m t code ∧
        InternalReach E c1 code := by
  -- env: 0=c1, 1=numV 2, 2=zeroV
  -- under pushValue env k: 0=k, 1=c1, 2=numV 2, 3=zeroV
  -- under 7 .ex (r0, r2, r3, r7, m, t, code): 0=code, 1=t, 2=m, 3=r7, 4=r3, 5=r2, 6=r0, 7=k, 8=c1, 9=numV 2, 10=zeroV
  let body : Formula :=
    .imp (.or (.eq 0 2) (.mem 2 0))
      (.or (fInternalHaltsFrom 1)
        (.ex (.ex (.ex (.ex (.ex (.ex (.ex
          (.and (fNot (fEmpty 2)) (.and (fNot (fEmpty 1))
            (.and (fFrameCodeV1 2 6 10 5 4 10 10 7 3 10 1 0)
              (fInternalReach 8 0))))))))))))
  let env : Nat → V := fun i => if i = 0 then c1 else if i = 1 then numV hM hNE 2 else zeroV hM hNE
  have hB : Bound body 4 :=
    ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
      ⟨bound_fInternalHaltsFrom (by omega),
        ⟨bound_fNot (bound_fEmpty (by omega)), ⟨bound_fNot (bound_fEmpty (by omega)),
          ⟨bound_fFrameCodeV1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            bound_fInternalReach (by omega) (by omega)⟩⟩⟩⟩⟩
  have hind := omega_induction hM hNE 3 body hB env
    (fun z hz hge => by
      dsimp only [eval, pushValue, env] at hge
      rcases hge with heq | h2z
      · exact False.elim (hz (numV hM hNE 1) (heq ▸ numV_lt_of_lt hM hNE (by omega)))
      · exact False.elim (hz _ h2z))
    (fun k k' hk hkk' ih hge => by
      dsimp only [eval, pushValue, env] at hge
      rcases hge with hk'2 | h2k'
      · -- k' = 2: base case from hInit!
        rcases hInit with ⟨z, hz, hmne, htne, hfc⟩
        have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
        right
        refine ⟨zeroV hM hNE, zeroV hM hNE, zeroV hM hNE, zeroV hM hNE, m0, t0, c1, hmne, htne, ?_,
          (eval_fInternalReach hM hNE _ _ _).mpr (internalReach_refl hM hNE (frameCodeV_nat hfc))⟩
        apply (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
        dsimp only [pushValue, env]; simp only [ite_true] at hk'2 ⊢; rwa [hk'2]
      · -- 2 < k' = succ k, so 2 ≤ k!
        have h2lek : k = numV hM hNE 2 ∨ E (numV hM hNE 2) k :=
          ((hkk' (numV hM hNE 2)).mp h2k').elim Or.inr (fun h => Or.inl h.symm)
        rcases ih h2lek with hh | ⟨r0, r2, r3, r7, m, t, code, hmne, htne, hfc, hr01⟩
        · have hh' : InternalHaltsFrom E c1 := (eval_fInternalHaltsFrom hM hNE 1 _).mp hh
          exact Or.inl ((eval_fInternalHaltsFrom hM hNE 1 _).mpr hh')
        · have hfc' := (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfc
          have hr01' := (eval_fInternalReach hM hNE _ _ _).mp hr01
          have hF : CleanFrame (E := E) r0 (zeroV hM hNE) r2 r3 k r7 m t code := ⟨zeroV hM hNE, zeroV_empty hM hNE, hmne, htne, hfc'⟩
          rcases exec_any_step hM hNE hLoop hk (nat_succ hM hNE hk hkk') (Or.inl ⟨zeroV_empty hM hNE, rfl, hkk'⟩) hF with hh | ⟨r0', r1', r2', r3', r7', m', t', c', _, hF1, hr12⟩
          · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mpr (internalHaltsFrom_of_reach hM hNE hr01' hh))
          · have r02 := internalReach_trans hM hNE hr01' hr12
            have hr1'N : NatObject E r1' := by rcases hF1 with ⟨_, _, _, _, hfc1⟩; exact hfc1.2.2.1.2.1
            rcases inner_drain hM hNE hLoop r1' hr1'N r1' (Or.inl rfl) r0' r2' r3' k' r7' m' t' c' hF1 with hh | ⟨r0'', r2'', r3'', r7'', m'', t'', c'', ⟨z'', hz'', hm'', ht'', hfc2⟩, hr23⟩
            · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mpr (internalHaltsFrom_of_reach hM hNE r02 hh))
            · have := empty_unique hM hNE hz'' (zeroV_empty hM hNE); subst this
              exact Or.inr ⟨r0'', r2'', r3'', r7'', m'', t'', c'', hm'', ht'',
                (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hfc2,
                (eval_fInternalReach hM hNE _ _ _).mpr (internalReach_trans hM hNE r02 hr23)⟩)
  intro k hk hge
  rcases hind k hk hge with hh | ⟨r0, r2, r3, r7, m, t, code, hmne, htne, hfc, hr⟩
  · exact Or.inl ((eval_fInternalHaltsFrom hM hNE _ _).mp hh)
  · exact Or.inr ⟨r0, r2, r3, r7, m, t, code,
      ⟨zeroV hM hNE, zeroV_empty hM hNE, hmne, htne, (eval_fFrameCodeV1 hM hNE _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfc⟩,
      (eval_fInternalReach hM hNE _ _ _).mp hr⟩

private theorem main_reg_halts (V : Type) (E : V → V → Prop) (hNE : Nonempty V) (hM : Model E)
    (hLoop : InternalLoopStep E) (hProv : InternalProvC1 E)
    (m t z two c1 : V) (hz : Empty E z) (h2 : Numeral E 2 two)
    (hmne : ¬ Empty E m) (htne : ¬ Empty E t)
    (hfc : FrameCodeV E 1 m ⟨z, z, z, z, z, z, two, z, z⟩ t c1) :
    InternalHaltsFrom E c1 := by
  have hzeq := empty_unique hM hNE hz (zeroV_empty hM hNE); subst hzeq
  have h2eq := numeral_unique hM hNE h2 (numV_numeral hM hNE 2); subst h2eq
  have hInit : CleanFrame (E := E) (zeroV hM hNE) (zeroV hM hNE) (zeroV hM hNE) (zeroV hM hNE) (numV hM hNE 2) (zeroV hM hNE) m t c1 :=
    ⟨zeroV hM hNE, hz, hmne, htne, hfc⟩
  have hcp1 := internalProvC1_implies_canPush1 hM hNE hLoop hProv
  let r_sh2 := cmdShift hM hNE (cmdShift hM hNE (zeroV hM hNE))
  have hr_sh2N := cmdShift_nat hM hNE (cmdShift_nat hM hNE (zeroV_nat hM hNE))
  obtain ⟨r_p1, hr_p1N, hrun_p1⟩ := canPush_apply hM hNE hcp1 hr_sh2N
  let r_gen2 := cmdGenAx hM hNE (zeroV hM hNE) (zeroV hM hNE) (zeroV hM hNE) r_p1
  have hr_gen2N := cmdGenAx_nat hM hNE (zeroV_nat hM hNE) (zeroV_nat hM hNE) (zeroV_nat hM hNE) hr_p1N
  let w1 := cantorV hM hNE (zeroV hM hNE) r_gen2
  let w' := cantorV hM hNE (zeroV hM hNE) w1
  let W0 := cantorV hM hNE (numV hM hNE 2) w'
  have hW0N : NatObject E W0 := cantorV_nat hM hNE (numV_nat hM hNE 2) (cantorV_nat hM hNE (zeroV_nat hM hNE) (cantorV_nat hM hNE (zeroV_nat hM hNE) hr_gen2N))
  -- Show 2 < W0: 2 * W0 = (2 + w') * (3 + w') + 2 * w' ≥ 6 > 4 = 2 * 2
  have h2ltW0 : E (numV hM hNE 2) W0 := by
    have hw'N : NatObject E w' := cantorV_nat hM hNE (zeroV_nat hM hNE) (cantorV_nat hM hNE (zeroV_nat hM hNE) hr_gen2N)
    have hcw0 := cantorV_spec hM hNE (numV_nat hM hNE 2) hw'N
    rcases hcw0 with ⟨_, _, _, two', s, ns, prod, tb, tz, tot, h2', hadd, hs, hm1, hm2, hm3, ha2, hEq⟩
    have := numeral_unique hM hNE h2' (numV_numeral hM hNE 2); subst this
    have hseq : s = addV hM hNE (numV hM hNE 2) w' := (add_iff_eq hM hNE (numV_nat hM hNE 2) hw'N).mp hadd; subst hseq
    have hnseq : ns = succV hM hNE (addV hM hNE (numV hM hNE 2) w') := succ_unique hM hNE hs (succV_spec hM hNE _); subst hnseq
    have hns_eq : succV hM hNE (addV hM hNE (numV hM hNE 2) w') = addV hM hNE (numV hM hNE 3) w' := by
      have h3 : numV hM hNE 3 = succV hM hNE (numV hM hNE 2) := rfl
      rw [h3, succ_addV hM hNE (numV_nat hM hNE 2) w' hw'N]
    have h4_lt_prod : E (numV hM hNE 4) prod := by
      have hpeq : prod = mulV hM hNE (addV hM hNE (numV hM hNE 2) w') (addV hM hNE (numV hM hNE 3) w') := by
        rw [← hns_eq]; exact (mul_iff_eq hM hNE (addV_nat hM hNE (numV_nat hM hNE 2) hw'N) (succV_nat hM hNE (addV_nat hM hNE (numV_nat hM hNE 2) hw'N))).mp hm1
      rw [hpeq, addV_left_distrib hM hNE (addV_nat hM hNE (numV_nat hM hNE 2) hw'N) (numV_nat hM hNE 3) w' hw'N]
      have h6eq : mulV hM hNE (addV hM hNE (numV hM hNE 2) w') (numV hM hNE 3) =
          addV hM hNE (numV hM hNE 6) (addV hM hNE (addV hM hNE w' w') w') := by
        have hmul3 : ∀ X, NatObject E X → mulV hM hNE X (numV hM hNE 3) = addV hM hNE (addV hM hNE X X) X := by
          intro X hXN
          have h3s : numV hM hNE 3 = succV hM hNE (numV hM hNE 2) := rfl
          have h2s : numV hM hNE 2 = succV hM hNE (numV hM hNE 1) := rfl
          have h1s : numV hM hNE 1 = succV hM hNE (zeroV hM hNE) := rfl
          rw [h3s, mulV_succ hM hNE hXN (numV_nat hM hNE 2),
            h2s, mulV_succ hM hNE hXN (numV_nat hM hNE 1),
            h1s, mulV_succ hM hNE hXN (zeroV_nat hM hNE),
            mulV_zero hM hNE hXN, zero_addV hM hNE X hXN]
        rw [hmul3 _ (addV_nat hM hNE (numV_nat hM hNE 2) hw'N)]
        have hA : addV hM hNE (addV hM hNE (numV hM hNE 2) w') (addV hM hNE (numV hM hNE 2) w') =
            addV hM hNE (numV hM hNE 4) (addV hM hNE w' w') := by
          rw [addV_assoc hM hNE (numV_nat hM hNE 2) hw'N _ (addV_nat hM hNE (numV_nat hM hNE 2) hw'N),
            addV_comm hM hNE hw'N _ (addV_nat hM hNE (numV_nat hM hNE 2) hw'N),
            addV_assoc hM hNE (numV_nat hM hNE 2) hw'N w' hw'N,
            ← addV_assoc hM hNE (numV_nat hM hNE 2) (numV_nat hM hNE 2) _ (addV_nat hM hNE hw'N hw'N),
            addV_numV]
        rw [hA, addV_assoc hM hNE (numV_nat hM hNE 4) (addV_nat hM hNE hw'N hw'N) _ (addV_nat hM hNE (numV_nat hM hNE 2) hw'N),
          addV_comm hM hNE (addV_nat hM hNE hw'N hw'N) _ (addV_nat hM hNE (numV_nat hM hNE 2) hw'N),
          addV_assoc hM hNE (numV_nat hM hNE 2) hw'N _ (addV_nat hM hNE hw'N hw'N),
          ← addV_assoc hM hNE (numV_nat hM hNE 4) (numV_nat hM hNE 2) _ (addV_nat hM hNE hw'N (addV_nat hM hNE hw'N hw'N)),
          addV_numV, addV_comm hM hNE hw'N (addV hM hNE w' w') (addV_nat hM hNE hw'N hw'N)]
      rw [h6eq, addV_assoc hM hNE (numV_nat hM hNE 6) (addV_nat hM hNE (addV_nat hM hNE hw'N hw'N) hw'N) _
        (mulV_nat hM hNE (addV_nat hM hNE (numV_nat hM hNE 2) hw'N) hw'N)]
      rcases addV_le_left hM hNE (numV_nat hM hNE 6) _ (addV_nat hM hNE (addV_nat hM hNE (addV_nat hM hNE hw'N hw'N) hw'N)
        (mulV_nat hM hNE (addV_nat hM hNE (numV_nat hM hNE 2) hw'N) hw'N)) with h6 | h6
      · rw [← h6]; exact numV_lt_of_lt hM hNE (by omega)
      · exact nat_lt_trans hM hNE _ (addV_nat hM hNE (numV_nat hM hNE 6)
          (addV_nat hM hNE (addV_nat hM hNE (addV_nat hM hNE hw'N hw'N) hw'N)
            (mulV_nat hM hNE (addV_nat hM hNE (numV_nat hM hNE 2) hw'N) hw'N))) _ _
          (numV_lt_of_lt hM hNE (by omega)) h6
    have h4_lt_tz : E (numV hM hNE 4) tz := by
      have hle : prod = tot ∨ E prod tot := by
        rw [(add_iff_eq hM hNE hm1.2.2.1 hm2.2.2.1).mp ha2]
        exact addV_le_left hM hNE hm1.2.2.1 tb hm2.2.2.1
      rw [← hEq] at hle
      rcases hle with rfl | hlt
      · exact h4_lt_prod
      · exact nat_lt_trans hM hNE tz hm3.2.2.1 _ _ h4_lt_prod hlt
    rcases nat_trichotomy hM hNE (numV hM hNE 2) (numV_nat hM hNE 2) W0 hW0N with hlt | heq | hgt
    · exact hlt
    · exfalso
      have htz4 : tz = numV hM hNE 4 := by
        rw [(mul_iff_eq hM hNE (numV_nat hM hNE 2) hW0N).mp hm3, ← heq, two_mulV_eq_addV hM hNE (numV_nat hM hNE 2), addV_numV]
      exact mem_irrefl hM hNE _ (htz4 ▸ h4_lt_tz)
    · exfalso
      obtain ⟨i, hi, hi_eq⟩ := (mem_numV_iff hM hNE 2 W0).mp hgt
      have htz_lt4 : E tz (numV hM hNE 4) := by
        rw [(mul_iff_eq hM hNE (numV_nat hM hNE 2) hW0N).mp hm3, hi_eq, two_mulV_eq_addV hM hNE (numV_nat hM hNE i), addV_numV]
        exact numV_lt_of_lt hM hNE (by omega)
      exact mem_asymm hM hNE h4_lt_tz htz_lt4
  -- Run Outer Scheduler to r6 = W0, r1 = 0
  rcases outer_scheduler hM hNE hLoop hInit W0 hW0N (Or.inr h2ltW0) with hh | ⟨r0, r2, r3, r7, m1, t1, code1, ⟨z1, hz1, hm1ne, ht1ne, hfc1⟩, hr01⟩
  · exact hh
  have := empty_unique hM hNE hz1 hz; subst this
  rcases hfc1.2.2.1 with ⟨hr0N, _, hr2N, hr3N, _, _, _, hr7N, _⟩
  -- Step 1: pop W0 from r6 (r1 = 0), executing GenAx(0, 0, 0) → r1 = r_gen2, r3 = 0, r7 = 0!
  have hr3le : E r3 r3 ∨ r3 = r3 := Or.inr rfl
  obtain ⟨uc, huc, hucN⟩ := calcUc_exists hM hNE hr3N hr7N
  obtain ⟨r8, hr8, hr8N⟩ := calcRho8_exists hM hNE hr3N (zeroV_nat hM hNE) hr7N hr3N hr3le
  obtain ⟨h1, hh1, hh1N⟩ := calcHead1_exists hM hNE hr7N hr3N
  obtain ⟨h2, hh2, hh2N⟩ := calcHead2_exists hM hNE hr7N hr3N (zeroV_nat hM hNE)
  obtain ⟨h3, hh3, hh3N⟩ := calcHead3_exists hM hNE hr7N hr3N (zeroV_nat hM hNE)
  obtain ⟨h4, hh4, hh4N⟩ := calcHead4_exists hM hNE hr7N hr3N (zeroV_nat hM hNE)
  obtain ⟨h5, hh5, hh5N⟩ := calcHead5_exists hM hNE hr7N hr3N
  obtain ⟨h6, hh6, hh6N⟩ := calcHead6_exists hM hNE hr7N hr3N (zeroV_nat hM hNE)
  let s1 := cantorV hM hNE r2 r0; have hs1 := cantorV_spec hM hNE hr2N hr0N
  let s2 := cantorV hM hNE uc s1; have hs2 := cantorV_spec hM hNE hucN hs1.2.2.1
  let s3 := cantorV hM hNE r8 s2; have hs3 := cantorV_spec hM hNE hr8N hs2.2.2.1
  let s4 := cantorV hM hNE h1 s3; have hs4 := cantorV_spec hM hNE hh1N hs3.2.2.1
  let s5 := cantorV hM hNE h2 s4; have hs5 := cantorV_spec hM hNE hh2N hs4.2.2.1
  let s6 := cantorV hM hNE h3 s5; have hs6 := cantorV_spec hM hNE hh3N hs5.2.2.1
  let s7 := cantorV hM hNE h4 s6; have hs7 := cantorV_spec hM hNE hh4N hs6.2.2.1
  let s8 := cantorV hM hNE h5 s7; have hs8 := cantorV_spec hM hNE hh5N hs7.2.2.1
  let s9 := cantorV hM hNE h6 s8; have hs9 := cantorV_spec hM hNE hh6N hs8.2.2.1
  have htop_ex : ∃ top, (zeroV hM hNE ≠ r7 ∧ zeroV hM hNE ≠ r3 ∧ CalcGateF E r7 r3 (zeroV hM hNE) top) ∨ ((zeroV hM hNE = r7 ∨ zeroV hM hNE = r3) ∧ Empty E top) := by
    by_cases c1 : zeroV hM hNE = r7
    · exact ⟨zeroV hM hNE, Or.inr ⟨Or.inl c1, hz⟩⟩
    · by_cases c2 : zeroV hM hNE = r3
      · exact ⟨zeroV hM hNE, Or.inr ⟨Or.inr c2, hz⟩⟩
      · obtain ⟨top, htop, _⟩ := calcGateF_exists hM hNE hr7N hr3N (zeroV_nat hM hNE) c1 c2
        exact ⟨top, Or.inl ⟨c1, c2, htop⟩⟩
  obtain ⟨top, htop⟩ := htop_ex
  have hstepW0 := (hLoop r0 (zeroV hM hNE) r2 r3 W0 r7 m1 t1 (zeroV hM hNE) code1 hr0N (zeroV_nat hM hNE) hr2N hr3N hW0N hr7N
    hfc1.1 hfc1.2.1 hz hm1ne ht1ne hfc1 W0 (succV hM hNE W0) (numV hM hNE 2) w'
    (Or.inl ⟨hz, rfl, succV_spec hM hNE W0⟩)
    (cantorV_spec hM hNE (numV_nat hM hNE 2) (cantorV_nat hM hNE (zeroV_nat hM hNE) (cantorV_nat hM hNE (zeroV_nat hM hNE) hr_gen2N)))).2.2
    (zeroV hM hNE) (numV hM hNE 1) (succV_spec hM hNE (zeroV hM hNE)) (succV_spec hM hNE (numV hM hNE 1))
    (zeroV hM hNE) w1 (zeroV hM hNE) r_gen2 r7 r3
    (cantorV_spec hM hNE (zeroV_nat hM hNE) (cantorV_nat hM hNE (zeroV_nat hM hNE) hr_gen2N))
    (cantorV_spec hM hNE (zeroV_nat hM hNE) hr_gen2N)
    (add_zero hM hNE hr7N hz) (add_zero hM hNE hr3N hz)
    uc r8 h1 h2 h3 h4 h5 h6 s1 s2 s3 s4 s5 s6 s7 s8 s9 top
    huc hr8 hh1 hh2 hh3 hh4 hh5 hh6 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 htop
  obtain ⟨m2, t2, code2, hm2, ht2, hfc2, hr12⟩ := hstepW0
  have r02 := internalReach_trans hM hNE hr01 hr12
  -- Step 2: execute r_gen2 = GenAx(0, 0, 0) → resets (T, B, A) = (0, 0, 0)!
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s9', top', m3, t3, code3,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htop', hF3, hr23⟩ :=
    exec_genAx hM hNE hLoop (zeroV_nat hM hNE) (zeroV_nat hM hNE) (zeroV_nat hM hNE) hr_p1N
      (add_zero hM hNE (zeroV_nat hM hNE) hz) (add_zero hM hNE (zeroV_nat hM hNE) hz)
      ⟨zeroV hM hNE, hz, hm2, ht2, hfc2⟩
  have htop'_0 : top' = zeroV hM hNE := by
    rcases htop' with ⟨hneq, _, _⟩ | ⟨_, ht0⟩
    · exact False.elim (hneq rfl)
    · exact empty_unique hM hNE ht0 hz
  subst htop'_0
  have r03 := internalReach_trans hM hNE r02 hr23
  -- Step 3: execute r_p1 (CanPush 1) → either halts or pushes 1 onto stack!
  rcases hrun_p1 s9' (succV hM hNE W0) m3 t3 code3 hF3 with hh | ⟨s_one, m4, t4, code4, hs_one, hF4, hr34⟩
  · exact internalHaltsFrom_of_reach hM hNE r03 hh
  have r04 := internalReach_trans hM hNE r03 hr34
  -- Step 4: Shift pops 1 into A (r7 = 1, r2 = 0)
  rcases exec_shift hM hNE hLoop (cmdShift_nat hM hNE (zeroV_nat hM hNE)) hs_one hF4 with hh | ⟨m5, t5, code5, hF5, hr45⟩
  · exact internalHaltsFrom_of_reach hM hNE r04 hh
  have r05 := internalReach_trans hM hNE r04 hr45
  -- Step 5: Shift sees r2 + r7 = 0 + 1 = 1 → HALTS!
  exact internalHaltsFrom_of_reach hM hNE r05 (exec_shift_halt hM hNE hLoop (zeroV_nat hM hNE) hF5)

end ZFModel

end SolInternalRegHalts

theorem solution :
    ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E →
      PalomarZF207InternalTM.InternalLoopStep E →
      PalomarZF207Internal.InternalProvC1 E →
      ∀ (m t z two c1 : V),
        PalomarZF207History.Empty E z →
        PalomarZF207History.Numeral E 2 two →
        ¬ PalomarZF207History.Empty E m →
        ¬ PalomarZF207History.Empty E t →
        PalomarZF207InternalTM.FrameCodeV E 1 m ⟨z, z, z, z, z, z, two, z, z⟩ t c1 →
        PalomarZF207InternalTM.InternalHaltsFrom E c1 :=
  SolInternalRegHalts.main_reg_halts
