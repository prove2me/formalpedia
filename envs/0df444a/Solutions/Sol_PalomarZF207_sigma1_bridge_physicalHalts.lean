-- Prove2me | solution 1 for PalomarZF207.sigma1_bridge_physicalHalts
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T18:35:13.249185+00:00
-- url     : https://prove2.me/submissions/787a24cd-6307-4be3-847c-eec6ed8e3e02

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement
import Definitions.Def_palomar_zf207_physical

open PalomarZF207
open PalomarZF207History

namespace SigmaBridgeDev

/-! ### Part 0: General Formula evaluation lemmas and Separation / Omega Induction -/

theorem pushValue_comp_lift {V : Type} (σ : Nat → Nat) (s : Nat → V) (x : V) :
    (fun i => pushValue s x (lift σ i)) = pushValue (fun i => s (σ i)) x := by
  funext i
  cases i <;> rfl

theorem eval_rename {V : Type} (E : V → V → Prop) :
    ∀ (f : Formula) (σ : Nat → Nat) (s : Nat → V),
      eval E (rename σ f) s ↔ eval E f (fun i => s (σ i))
  | .bot, _, _ => Iff.rfl
  | .mem _ _, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl
  | .and p q, σ, s => by
    simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .or p q, σ, s => by
    simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .imp p q, σ, s => by
    simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .all p, σ, s => by
    constructor
    · intro h x
      have hx := (eval_rename E p (lift σ) (pushValue s x)).mp (h x)
      rwa [pushValue_comp_lift] at hx
    · intro h x
      apply (eval_rename E p (lift σ) (pushValue s x)).mpr
      rw [pushValue_comp_lift]
      exact h x
  | .ex p, σ, s => by
    constructor
    · rintro ⟨x, hx⟩
      have hx' := (eval_rename E p (lift σ) (pushValue s x)).mp hx
      rw [pushValue_comp_lift] at hx'
      exact ⟨x, hx'⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (eval_rename E p (lift σ) (pushValue s x)).mpr ?_⟩
      rw [pushValue_comp_lift]
      exact hx

theorem eval_congr_bound {V : Type} (E : V → V → Prop) :
    ∀ (f : Formula) (n : Nat) (s₁ s₂ : Nat → V),
      Bound f n → (∀ i < n, s₁ i = s₂ i) → (eval E f s₁ ↔ eval E f s₂)
  | .bot, _, _, _, _, _ => Iff.rfl
  | .mem i j, n, s₁, s₂, ⟨hi, hj⟩, h => by
    simp only [eval, h i hi, h j hj]
  | .eq i j, n, s₁, s₂, ⟨hi, hj⟩, h => by
    simp only [eval, h i hi, h j hj]
  | .and p q, n, s₁, s₂, ⟨hp, hq⟩, h => by
    simp only [eval, eval_congr_bound E p n s₁ s₂ hp h, eval_congr_bound E q n s₁ s₂ hq h]
  | .or p q, n, s₁, s₂, ⟨hp, hq⟩, h => by
    simp only [eval, eval_congr_bound E p n s₁ s₂ hp h, eval_congr_bound E q n s₁ s₂ hq h]
  | .imp p q, n, s₁, s₂, ⟨hp, hq⟩, h => by
    simp only [eval, eval_congr_bound E p n s₁ s₂ hp h, eval_congr_bound E q n s₁ s₂ hq h]
  | .all p, n, s₁, s₂, hp, h => by
    constructor
    · intro h1 x
      exact (eval_congr_bound E p (n + 1) (pushValue s₁ x) (pushValue s₂ x) hp (fun i hi => by
        cases i with
        | zero => rfl
        | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mp (h1 x)
    · intro h2 x
      exact (eval_congr_bound E p (n + 1) (pushValue s₁ x) (pushValue s₂ x) hp (fun i hi => by
        cases i with
        | zero => rfl
        | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mpr (h2 x)
  | .ex p, n, s₁, s₂, hp, h => by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (eval_congr_bound E p (n + 1) (pushValue s₁ x) (pushValue s₂ x) hp (fun i hi => by
        cases i with
        | zero => rfl
        | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mp hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (eval_congr_bound E p (n + 1) (pushValue s₁ x) (pushValue s₂ x) hp (fun i hi => by
        cases i with
        | zero => rfl
        | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mpr hx⟩

def pushParams {V : Type} (s : Nat → V) : List V → Nat → V
  | [] => s
  | x :: xs => pushParams (pushValue s x) xs

def mkParams {V : Type} (env : Nat → V) : Nat → List V
  | 0 => []
  | n + 1 => env n :: mkParams env n

theorem mkParams_length {V : Type} (env : Nat → V) : ∀ n, (mkParams env n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (mkParams_length env n)

theorem pushParams_mkParams_ge {V : Type} (env s : Nat → V) :
    ∀ n k, pushParams s (mkParams env n) (n + k) = s k
  | 0, k => by simp [mkParams, pushParams]
  | n + 1, k => by
    rw [show n + 1 + k = n + (k + 1) by omega]
    show pushParams (pushValue s (env n)) (mkParams env n) (n + (k + 1)) = s k
    rw [pushParams_mkParams_ge env (pushValue s (env n)) n (k + 1)]
    rfl

theorem pushParams_mkParams_lt {V : Type} (env s : Nat → V) :
    ∀ n i, i < n → pushParams s (mkParams env n) i = env i
  | 0, _, hi => False.elim (Nat.not_lt_zero _ hi)
  | n + 1, i, hi => by
    show pushParams (pushValue s (env n)) (mkParams env n) i = env i
    by_cases hlt : i < n
    · exact pushParams_mkParams_lt env (pushValue s (env n)) n i hlt
    · have heq : i = n := by omega
      rw [heq]
      have h := pushParams_mkParams_ge env (pushValue s (env n)) n 0
      simpa [pushValue] using h

theorem eval_allPrefix {V : Type} (E : V → V → Prop) :
    ∀ (n : Nat) (f : Formula) (s : Nat → V) (xs : List V),
      xs.length = n → eval E (allPrefix n f) s → eval E f (pushParams s xs)
  | 0, _, _, [], _, h => h
  | n + 1, f, s, x :: xs, hlen, h =>
    eval_allPrefix E n f (pushValue s x) xs (Nat.succ.inj hlen) (h x)

/-! ### Part 1: Extracting ZF Axioms and Model Arithmetic -/

section ZFModel

variable {V : Type} {E : V → V → Prop}

theorem ax_ext (hM : Model E) (hNE : Nonempty V) {a b : V}
    (h1 : ∀ z, E z a → E z b) (h2 : ∀ z, E z b → E z a) : a = b := by
  have hAx : Axiom fixedExt := Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  exact hM fixedExt hAx (fun _ => Classical.choice hNE) a b h1 h2

theorem ax_empty (hM : Model E) (hNE : Nonempty V) : ∃ z, Empty E z := by
  have hAx : Axiom fixedEmpty :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  exact hM fixedEmpty hAx (fun _ => Classical.choice hNE)

theorem ax_pair (hM : Model E) (hNE : Nonempty V) (a b : V) : ∃ p, Pair E a b p := by
  have hAx : Axiom fixedPair :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  obtain ⟨p, hp⟩ := hM fixedPair hAx (fun _ => Classical.choice hNE) a b
  exact ⟨p, fun x => ⟨(hp x).1, (hp x).2⟩⟩

theorem ax_union (hM : Model E) (hNE : Nonempty V) (u : V) :
    ∃ v, ∀ x, E x v ↔ ∃ y, E y u ∧ E x y := by
  have hAx : Axiom fixedUnion :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  obtain ⟨v, hv⟩ := hM fixedUnion hAx (fun _ => Classical.choice hNE) u
  exact ⟨v, fun x => ⟨(hv x).1, (hv x).2⟩⟩

theorem ax_omega (hM : Model E) (hNE : Nonempty V) : ∃ w, Omega E w := by
  have hAx : Axiom fixedOmega :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  obtain ⟨w, ⟨⟨z, hz, hzw⟩, hstep⟩, hmin⟩ := hM fixedOmega hAx (fun _ => Classical.choice hNE)
  refine ⟨w, ⟨⟨z, hz, hzw⟩, ?_⟩, ?_⟩
  · intro x hxw
    obtain ⟨y, hy, hyw⟩ := hstep x hxw
    exact ⟨y, fun t => ⟨(hy t).1, (hy t).2⟩, hyw⟩
  · intro a ⟨⟨za, hza, hzaa⟩, hstepa⟩ x hxw
    apply hmin a ⟨⟨za, hza, hzaa⟩, ?_⟩ x hxw
    intro u hua
    obtain ⟨y, hy, hya⟩ := hstepa u hua
    exact ⟨y, fun t => ⟨(hy t).mp, (hy t).mpr⟩, hya⟩

theorem ax_foundation (hM : Model E) (hNE : Nonempty V) {a : V} (hne : ∃ x, E x a) :
    ∃ x, E x a ∧ ∀ y, E y x → ¬ E y a := by
  have hAx : Axiom fixedFoundation :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))))
  exact hM fixedFoundation hAx (fun _ => Classical.choice hNE) a hne

theorem ax_sep (hM : Model E) (hNE : Nonempty V) (n : Nat) (body : Formula)
    (hB : Bound body (n + 1)) (env : Nat → V) (dom : V) :
    ∃ sub, ∀ x, E x sub ↔ E x dom ∧ eval E body (pushValue env x) := by
  have hAx : Axiom (separationSchema n body) := Or.inr (Or.inl ⟨n, body, hB, rfl⟩)
  let s₀ : Nat → V := fun _ => Classical.choice hNE
  have hAll := hM (separationSchema n body) hAx s₀
  have hSep := eval_allPrefix E n (separationFormula (rename sepIndex body)) s₀
    (mkParams env n) (mkParams_length env n) hAll
  obtain ⟨sub, hsub⟩ := hSep dom
  refine ⟨sub, fun x => ?_⟩
  have hx := hsub x
  have hEq : eval E (rename sepIndex body)
      (pushValue (pushValue (pushValue (pushParams s₀ (mkParams env n)) dom) sub) x) ↔
      eval E body (pushValue env x) := by
    rw [eval_rename]
    apply eval_congr_bound E body (n + 1) _ _ hB
    intro i hi
    cases i with
    | zero => rfl
    | succ k =>
      have hk : k < n := Nat.lt_of_succ_lt_succ hi
      show pushValue (pushValue (pushValue (pushParams s₀ (mkParams env n)) dom) sub) x (k + 3) = env k
      exact pushParams_mkParams_lt env s₀ n k hk
  exact ⟨fun h => let ⟨h1, h2⟩ := hx.1 h; ⟨h1, hEq.mp h2⟩,
         fun ⟨h1, h2⟩ => hx.2 ⟨h1, hEq.mpr h2⟩⟩

/-! Basic uniqueness & set constructors -/

theorem empty_unique (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : Empty E a) (hb : Empty E b) : a = b :=
  ax_ext hM hNE (fun z hz => False.elim (ha z hz)) (fun z hz => False.elim (hb z hz))

theorem succ_unique (hM : Model E) (hNE : Nonempty V) {a b₁ b₂ : V}
    (h1 : Succ E a b₁) (h2 : Succ E a b₂) : b₁ = b₂ :=
  ax_ext hM hNE (fun z hz => (h2 z).mpr ((h1 z).mp hz)) (fun z hz => (h1 z).mpr ((h2 z).mp hz))

theorem pair_unique (hM : Model E) (hNE : Nonempty V) {a b p₁ p₂ : V}
    (h1 : Pair E a b p₁) (h2 : Pair E a b p₂) : p₁ = p₂ :=
  ax_ext hM hNE (fun z hz => (h2 z).mpr ((h1 z).mp hz)) (fun z hz => (h1 z).mpr ((h2 z).mp hz))

theorem omega_unique (hM : Model E) (hNE : Nonempty V) {w₁ w₂ : V}
    (h1 : Omega E w₁) (h2 : Omega E w₂) : w₁ = w₂ :=
  ax_ext hM hNE (fun x hx => h1.2 w₂ h2.1 x hx) (fun x hx => h2.2 w₁ h1.1 x hx)

theorem exists_insert (hM : Model E) (hNE : Nonempty V) (s x : V) :
    ∃ t, ∀ y, E y t ↔ E y s ∨ y = x := by
  obtain ⟨sx, hsx⟩ := ax_pair hM hNE x x
  obtain ⟨p, hp⟩ := ax_pair hM hNE s sx
  obtain ⟨u, hu⟩ := ax_union hM hNE p
  refine ⟨u, fun y => ?_⟩
  rw [hu]
  constructor
  · rintro ⟨w, hwp, hyw⟩
    rcases (hp w).mp hwp with rfl | rfl
    · exact Or.inl hyw
    · rcases (hsx y).mp hyw with rfl | rfl <;> exact Or.inr rfl
  · intro h
    rcases h with hys | rfl
    · exact ⟨s, (hp s).mpr (Or.inl rfl), hys⟩
    · exact ⟨sx, (hp sx).mpr (Or.inr rfl), (hsx y).mpr (Or.inl rfl)⟩

theorem exists_succ (hM : Model E) (hNE : Nonempty V) (a : V) : ∃ b, Succ E a b :=
  exists_insert hM hNE a a

theorem exists_orderedPair (hM : Model E) (hNE : Nonempty V) (a b : V) :
    ∃ p, OrderedPair E a b p := by
  obtain ⟨aa, haa⟩ := ax_pair hM hNE a a
  obtain ⟨ab, hab⟩ := ax_pair hM hNE a b
  obtain ⟨p, hp⟩ := ax_pair hM hNE aa ab
  exact ⟨p, aa, ab, haa, hab, hp⟩

theorem orderedPair_unique (hM : Model E) (hNE : Nonempty V) {a b p₁ p₂ : V}
    (h1 : OrderedPair E a b p₁) (h2 : OrderedPair E a b p₂) : p₁ = p₂ := by
  rcases h1 with ⟨aa1, ab1, haa1, hab1, hp1⟩
  rcases h2 with ⟨aa2, ab2, haa2, hab2, hp2⟩
  have haa : aa1 = aa2 := pair_unique hM hNE haa1 haa2
  have hab : ab1 = ab2 := pair_unique hM hNE hab1 hab2
  subst haa; subst hab
  exact pair_unique hM hNE hp1 hp2

theorem orderedPair_inj {a b a' b' p : V}
    (h1 : OrderedPair E a b p) (h2 : OrderedPair E a' b' p) : a = a' ∧ b = b' := by
  rcases h1 with ⟨aa, ab, haa, hab, hp1⟩
  rcases h2 with ⟨aa', ab', haa', hab', hp2⟩
  have hmem_aa : aa = aa' ∨ aa = ab' := (hp2 aa).mp ((hp1 aa).mpr (Or.inl rfl))
  have ha_eq : a = a' := by
    rcases hmem_aa with h | h
    · rw [h] at haa
      rcases (haa' a).mp ((haa a).mpr (Or.inl rfl)) with rfl | rfl <;> rfl
    · rw [h] at haa
      rcases (haa a').mp ((hab' a').mpr (Or.inl rfl)) with rfl | rfl <;> rfl
  refine ⟨ha_eq, ?_⟩
  subst ha_eq
  have hmem_ab : ab = aa' ∨ ab = ab' := (hp2 ab).mp ((hp1 ab).mpr (Or.inr rfl))
  rcases hmem_ab with h | h
  · rw [h] at hab
    have hb_eq : b = a := by
      rcases (haa' b).mp ((hab b).mpr (Or.inr rfl)) with rfl | rfl <;> rfl
    have hmem_ab' : ab' = aa ∨ ab' = ab := (hp1 ab').mp ((hp2 ab').mpr (Or.inr rfl))
    rcases hmem_ab' with h' | h'
    · rw [h'] at hab'
      have hb' : b' = a := by
        rcases (haa b').mp ((hab' b').mpr (Or.inr rfl)) with rfl | rfl <;> rfl
      exact hb_eq.trans hb'.symm
    · rw [h', h] at hab'
      have hb' : b' = a := by
        rcases (haa' b').mp ((hab' b').mpr (Or.inr rfl)) with rfl | rfl <;> rfl
      exact hb_eq.trans hb'.symm
  · rw [h] at hab
    rcases (hab' b).mp ((hab b).mpr (Or.inr rfl)) with hba | hbb'
    · by_cases hb'a : b' = a
      · exact hba.trans hb'a.symm
      · rcases (hab b').mp ((hab' b').mpr (Or.inr rfl)) with h1 | h2
        · exact False.elim (hb'a h1)
        · exact h2.symm
    · exact hbb'

theorem mem_irrefl (hM : Model E) (hNE : Nonempty V) (x : V) : ¬ E x x := by
  intro hxx
  obtain ⟨s, hs⟩ := ax_pair hM hNE x x
  obtain ⟨y, hys, hmin⟩ := ax_foundation hM hNE ⟨x, (hs x).mpr (Or.inl rfl)⟩
  rcases (hs y).mp hys with rfl | rfl
  · exact hmin y hxx ((hs y).mpr (Or.inl rfl))
  · exact hmin y hxx ((hs y).mpr (Or.inl rfl))

theorem mem_asymm (hM : Model E) (hNE : Nonempty V) {x y : V} (hxy : E x y) : ¬ E y x := by
  intro hyx
  obtain ⟨s, hs⟩ := ax_pair hM hNE x y
  obtain ⟨z, hzs, hmin⟩ := ax_foundation hM hNE ⟨x, (hs x).mpr (Or.inl rfl)⟩
  rcases (hs z).mp hzs with rfl | rfl
  · exact hmin y hyx ((hs y).mpr (Or.inr rfl))
  · exact hmin x hxy ((hs x).mpr (Or.inl rfl))

/-! Omega induction for any first-order definable predicate -/

theorem omega_induction (hM : Model E) (hNE : Nonempty V) (n : Nat) (body : Formula)
    (hB : Bound body (n + 1)) (env : Nat → V)
    (hbase : ∀ z, Empty E z → eval E body (pushValue env z))
    (hstep : ∀ x y, NatObject E x → Succ E x y →
      eval E body (pushValue env x) → eval E body (pushValue env y)) :
    ∀ x, NatObject E x → eval E body (pushValue env x) := by
  intro x ⟨w, hw, hxw⟩
  obtain ⟨sub, hsub⟩ := ax_sep hM hNE n body hB env w
  have hind : Inductive E sub := by
    constructor
    · obtain ⟨z, hz, hzw⟩ := hw.1.1
      exact ⟨z, hz, (hsub z).mpr ⟨hzw, hbase z hz⟩⟩
    · intro u husub
      have ⟨huw, hubody⟩ := (hsub u).mp husub
      obtain ⟨y, huy, hyw⟩ := hw.1.2 u huw
      exact ⟨y, huy, (hsub y).mpr ⟨hyw, hstep u y ⟨w, hw, huw⟩ huy hubody⟩⟩
  exact ((hsub x).mp (hw.2 sub hind x hxw)).2

/-! Basic syntactic formula builders for induction predicates -/

def fNot (p : Formula) : Formula := .imp p .bot
def fIff (p q : Formula) : Formula := .and (.imp p q) (.imp q p)
def fEmpty (a : Nat) : Formula := .all (fNot (.mem 0 (a + 1)))
def fSucc (a b : Nat) : Formula :=
  .all (fIff (.mem 0 (b + 1)) (.or (.mem 0 (a + 1)) (.eq 0 (a + 1))))
def fPair (a b p : Nat) : Formula :=
  .all (fIff (.mem 0 (p + 1)) (.or (.eq 0 (a + 1)) (.eq 0 (b + 1))))
def fOrderedPair (a b p : Nat) : Formula :=
  .ex (.ex (.and (fPair (a + 2) (a + 2) 1)
    (.and (fPair (a + 2) (b + 2) 0) (fPair 1 0 (p + 2)))))
def fAt (f x y : Nat) : Formula :=
  .ex (.and (.mem 0 (f + 1)) (fOrderedPair (x + 1) (y + 1) 0))
def fFunctionOn (f dom : Nat) : Formula :=
  .and
    (.all (.imp (.mem 0 (dom + 1))
      (.ex (.and (fAt (f + 2) 1 0) (.all (.imp (fAt (f + 3) 2 0) (.eq 0 1)))))))
    (.all (.imp (.mem 0 (f + 1))
      (.ex (.ex (.and (.mem 1 (dom + 3)) (fOrderedPair 1 0 2))))))
def fInductive (a : Nat) : Formula :=
  .and (.ex (.and (fEmpty 0) (.mem 0 (a + 1))))
    (.all (.imp (.mem 0 (a + 1)) (.ex (.and (fSucc 1 0) (.mem 0 (a + 2))))))
def fOmega (w : Nat) : Formula :=
  .and (fInductive w) (.all (.imp (fInductive 0) (.all (.imp (.mem 0 (w + 2)) (.mem 0 1)))))
def fNatObject (x : Nat) : Formula := .ex (.and (fOmega 0) (.mem (x + 1) 0))
def fAdd (a b c : Nat) : Formula :=
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
def fMul (a b c : Nat) : Formula :=
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

theorem bound_fNot {p : Formula} {n : Nat} (hp : Bound p n) : Bound (fNot p) n := ⟨hp, trivial⟩
theorem bound_fIff {p q : Formula} {n : Nat} (hp : Bound p n) (hq : Bound q n) :
    Bound (fIff p q) n := ⟨⟨hp, hq⟩, ⟨hq, hp⟩⟩
theorem bound_fEmpty {a n : Nat} (ha : a < n) : Bound (fEmpty a) n := ⟨⟨by omega, by omega⟩, trivial⟩
theorem bound_fSucc {a b n : Nat} (ha : a < n) (hb : b < n) : Bound (fSucc a b) n :=
  bound_fIff ⟨by omega, by omega⟩ ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
theorem bound_fPair {a b p n : Nat} (ha : a < n) (hb : b < n) (hp : p < n) : Bound (fPair a b p) n :=
  bound_fIff ⟨by omega, by omega⟩ ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
theorem bound_fOrderedPair {a b p n : Nat} (ha : a < n) (hb : b < n) (hp : p < n) :
    Bound (fOrderedPair a b p) n :=
  ⟨bound_fPair (by omega) (by omega) (by omega),
   ⟨bound_fPair (by omega) (by omega) (by omega), bound_fPair (by omega) (by omega) (by omega)⟩⟩
theorem bound_fAt {f x y n : Nat} (hf : f < n) (hx : x < n) (hy : y < n) : Bound (fAt f x y) n :=
  ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega)⟩
theorem bound_fFunctionOn {f d n : Nat} (hf : f < n) (hd : d < n) : Bound (fFunctionOn f d) n :=
  ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega),
    ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩,
   ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega)⟩⟩⟩
theorem bound_fInductive {a n : Nat} (ha : a < n) : Bound (fInductive a) n :=
  ⟨⟨bound_fEmpty (by omega), ⟨by omega, by omega⟩⟩,
   ⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩
theorem bound_fOmega {w n : Nat} (hw : w < n) : Bound (fOmega w) n :=
  ⟨bound_fInductive hw, ⟨bound_fInductive (by omega), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩⟩
theorem bound_fNatObject {x n : Nat} (hx : x < n) : Bound (fNatObject x) n :=
  ⟨bound_fOmega (by omega), ⟨by omega, by omega⟩⟩
theorem bound_fAdd {a b c n : Nat} (ha : a < n) (hb : b < n) (hc : c < n) : Bound (fAdd a b c) n :=
  ⟨bound_fNatObject ha, bound_fNatObject hb, bound_fNatObject hc,
   bound_fEmpty (by omega), bound_fSucc (by omega) (by omega),
   bound_fFunctionOn (by omega) (by omega), bound_fAt (by omega) (by omega) (by omega),
   bound_fAt (by omega) (by omega) (by omega),
   ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
   ⟨⟨by omega, by omega⟩, bound_fSucc (by omega) (by omega), bound_fAt (by omega) (by omega) (by omega),
    bound_fAt (by omega) (by omega) (by omega), bound_fSucc (by omega) (by omega)⟩⟩
theorem bound_fMul {a b c n : Nat} (ha : a < n) (hb : b < n) (hc : c < n) : Bound (fMul a b c) n :=
  ⟨bound_fNatObject ha, bound_fNatObject hb, bound_fNatObject hc,
   bound_fEmpty (by omega), bound_fSucc (by omega) (by omega),
   bound_fFunctionOn (by omega) (by omega), bound_fAt (by omega) (by omega) (by omega),
   bound_fAt (by omega) (by omega) (by omega),
   ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
   ⟨⟨by omega, by omega⟩, bound_fSucc (by omega) (by omega), bound_fAt (by omega) (by omega) (by omega),
    bound_fAt (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩

theorem eval_fNot (p : Formula) (s : Nat → V) : eval E (fNot p) s ↔ ¬ eval E p s := Iff.rfl
theorem eval_fIff (p q : Formula) (s : Nat → V) : eval E (fIff p q) s ↔ (eval E p s ↔ eval E q s) :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.mp, h.mpr⟩⟩
theorem eval_fEmpty (a : Nat) (s : Nat → V) : eval E (fEmpty a) s ↔ Empty E (s a) := Iff.rfl
theorem eval_fSucc (a b : Nat) (s : Nat → V) : eval E (fSucc a b) s ↔ Succ E (s a) (s b) :=
  ⟨fun h x => (eval_fIff _ _ _).mp (h x), fun h x => (eval_fIff _ _ _).mpr (h x)⟩
theorem eval_fPair (a b p : Nat) (s : Nat → V) : eval E (fPair a b p) s ↔ Pair E (s a) (s b) (s p) :=
  ⟨fun h x => (eval_fIff _ _ _).mp (h x), fun h x => (eval_fIff _ _ _).mpr (h x)⟩
theorem eval_fOrderedPair (a b p : Nat) (s : Nat → V) :
    eval E (fOrderedPair a b p) s ↔ OrderedPair E (s a) (s b) (s p) :=
  ⟨fun ⟨aa, ab, h1, h2, h3⟩ =>
     ⟨aa, ab, (eval_fPair _ _ _ _).mp h1, (eval_fPair _ _ _ _).mp h2, (eval_fPair _ _ _ _).mp h3⟩,
   fun ⟨aa, ab, h1, h2, h3⟩ =>
     ⟨aa, ab, (eval_fPair _ _ _ _).mpr h1, (eval_fPair _ _ _ _).mpr h2, (eval_fPair _ _ _ _).mpr h3⟩⟩
theorem eval_fAt (f x y : Nat) (s : Nat → V) : eval E (fAt f x y) s ↔ At E (s f) (s x) (s y) :=
  ⟨fun ⟨p, h1, h2⟩ => ⟨p, h1, (eval_fOrderedPair _ _ _ _).mp h2⟩,
   fun ⟨p, h1, h2⟩ => ⟨p, h1, (eval_fOrderedPair _ _ _ _).mpr h2⟩⟩
theorem eval_fFunctionOn (f d : Nat) (s : Nat → V) :
    eval E (fFunctionOn f d) s ↔ FunctionOn E (s f) (s d) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun p hp => ?_⟩
    · obtain ⟨y, hy, hu⟩ := h1 x hx
      exact ⟨y, (eval_fAt _ _ _ _).mp hy, fun z hz => hu z ((eval_fAt _ _ _ _).mpr hz)⟩
    · obtain ⟨x, y, hx, hp'⟩ := h2 p hp
      exact ⟨x, y, hx, (eval_fOrderedPair _ _ _ _).mp hp'⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun p hp => ?_⟩
    · obtain ⟨y, hy, hu⟩ := h1 x hx
      exact ⟨y, (eval_fAt _ _ _ _).mpr hy, fun z hz => hu z ((eval_fAt _ _ _ _).mp hz)⟩
    · obtain ⟨x, y, hx, hp'⟩ := h2 p hp
      exact ⟨x, y, hx, (eval_fOrderedPair _ _ _ _).mpr hp'⟩
theorem eval_fInductive (a : Nat) (s : Nat → V) : eval E (fInductive a) s ↔ Inductive E (s a) :=
  ⟨fun ⟨⟨z, hz, hza⟩, hs⟩ =>
     ⟨⟨z, hz, hza⟩, fun x hx => let ⟨y, hy, hya⟩ := hs x hx; ⟨y, (eval_fSucc _ _ _).mp hy, hya⟩⟩,
   fun ⟨⟨z, hz, hza⟩, hs⟩ =>
     ⟨⟨z, hz, hza⟩, fun x hx => let ⟨y, hy, hya⟩ := hs x hx; ⟨y, (eval_fSucc _ _ _).mpr hy, hya⟩⟩⟩
theorem eval_fOmega (w : Nat) (s : Nat → V) : eval E (fOmega w) s ↔ Omega E (s w) :=
  ⟨fun ⟨hw, hm⟩ => ⟨(eval_fInductive _ _).mp hw, fun a ha x hx => hm a ((eval_fInductive _ _).mpr ha) x hx⟩,
   fun ⟨hw, hm⟩ => ⟨(eval_fInductive _ _).mpr hw, fun a ha x hx => hm a ((eval_fInductive _ _).mp ha) x hx⟩⟩
theorem eval_fNatObject (x : Nat) (s : Nat → V) : eval E (fNatObject x) s ↔ NatObject E (s x) :=
  ⟨fun ⟨w, hw, hxw⟩ => ⟨w, (eval_fOmega _ _).mp hw, hxw⟩,
   fun ⟨w, hw, hxw⟩ => ⟨w, (eval_fOmega _ _).mpr hw, hxw⟩⟩
theorem eval_fAdd (a b c : Nat) (s : Nat → V) : eval E (fAdd a b c) s ↔ Add E (s a) (s b) (s c) := by
  constructor
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mp ha, (eval_fNatObject _ _).mp hb, (eval_fNatObject _ _).mp hc,
      z, dom, f, hz, (eval_fSucc _ _ _).mp hdom, (eval_fFunctionOn _ _ _).mp hfun,
      (eval_fAt _ _ _ _).mp hf0, (eval_fAt _ _ _ _).mp hfb,
      fun i x hi hfx => (eval_fNatObject _ _).mp (hnat i x hi ((eval_fAt _ _ _ _).mpr hfx)),
      fun i hi => let ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
        ⟨j, x, y, (eval_fSucc _ _ _).mp h1, (eval_fAt _ _ _ _).mp h2,
         (eval_fAt _ _ _ _).mp h3, (eval_fSucc _ _ _).mp h4⟩⟩
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mpr ha, (eval_fNatObject _ _).mpr hb, (eval_fNatObject _ _).mpr hc,
      z, dom, f, hz, (eval_fSucc _ _ _).mpr hdom, (eval_fFunctionOn _ _ _).mpr hfun,
      (eval_fAt _ _ _ _).mpr hf0, (eval_fAt _ _ _ _).mpr hfb,
      fun i x hi hfx => (eval_fNatObject _ _).mpr (hnat i x hi ((eval_fAt _ _ _ _).mp hfx)),
      fun i hi => let ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
        ⟨j, x, y, (eval_fSucc _ _ _).mpr h1, (eval_fAt _ _ _ _).mpr h2,
         (eval_fAt _ _ _ _).mpr h3, (eval_fSucc _ _ _).mpr h4⟩⟩
theorem eval_fMul (a b c : Nat) (s : Nat → V) : eval E (fMul a b c) s ↔ Mul E (s a) (s b) (s c) := by
  constructor
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mp ha, (eval_fNatObject _ _).mp hb, (eval_fNatObject _ _).mp hc,
      z, dom, f, hz, (eval_fSucc _ _ _).mp hdom, (eval_fFunctionOn _ _ _).mp hfun,
      (eval_fAt _ _ _ _).mp hf0, (eval_fAt _ _ _ _).mp hfb,
      fun i x hi hfx => (eval_fNatObject _ _).mp (hnat i x hi ((eval_fAt _ _ _ _).mpr hfx)),
      fun i hi => let ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
        ⟨j, x, y, (eval_fSucc _ _ _).mp h1, (eval_fAt _ _ _ _).mp h2,
         (eval_fAt _ _ _ _).mp h3, (eval_fAdd _ _ _ _).mp h4⟩⟩
  · rintro ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
    refine ⟨(eval_fNatObject _ _).mpr ha, (eval_fNatObject _ _).mpr hb, (eval_fNatObject _ _).mpr hc,
      z, dom, f, hz, (eval_fSucc _ _ _).mpr hdom, (eval_fFunctionOn _ _ _).mpr hfun,
      (eval_fAt _ _ _ _).mpr hf0, (eval_fAt _ _ _ _).mpr hfb,
      fun i x hi hfx => (eval_fNatObject _ _).mpr (hnat i x hi ((eval_fAt _ _ _ _).mp hfx)),
      fun i hi => let ⟨j, x, y, h1, h2, h3, h4⟩ := hstep i hi
        ⟨j, x, y, (eval_fSucc _ _ _).mpr h1, (eval_fAt _ _ _ _).mpr h2,
         (eval_fAt _ _ _ _).mpr h3, (eval_fAdd _ _ _ _).mpr h4⟩⟩

/-! ### Part 2: Order, Succ, Add, Mul inside any ZF Model -/

theorem nat_zero (hM : Model E) (hNE : Nonempty V) {z : V} (hz : Empty E z) : NatObject E z := by
  obtain ⟨w, hw⟩ := ax_omega hM hNE
  obtain ⟨z', hz', hz'w⟩ := hw.1.1
  have : z = z' := empty_unique hM hNE hz hz'
  subst this
  exact ⟨w, hw, hz'w⟩

theorem nat_succ (hM : Model E) (hNE : Nonempty V) {x y : V}
    (hx : NatObject E x) (hxy : Succ E x y) : NatObject E y := by
  rcases hx with ⟨w, hw, hxw⟩
  obtain ⟨y', huy', hy'w⟩ := hw.1.2 x hxw
  have : y = y' := succ_unique hM hNE hxy huy'
  subst this
  exact ⟨w, hw, hy'w⟩

theorem nat_mem_is_nat (hM : Model E) (hNE : Nonempty V) :
    ∀ x, NatObject E x → ∀ y, E y x → NatObject E y := by
  let body : Formula := .all (.imp (.mem 0 1) (fNatObject 0))
  have hB : Bound body 1 := ⟨⟨by omega, by omega⟩, bound_fNatObject (by omega)⟩
  have h := omega_induction hM hNE 0 body hB (fun _ => Classical.choice hNE)
    (fun z hz y hy => False.elim (hz y hy))
    (fun x y hx hxy ih u hu => by
      rcases (hxy u).mp hu with hux | rfl
      · exact (eval_fNatObject _ _).mpr (ih u hux |> (eval_fNatObject _ _).mp)
      · exact (eval_fNatObject _ _).mpr hx)
  intro x hx y hy
  exact (eval_fNatObject _ _).mp (h x hx y hy)

theorem nat_lt_trans (hM : Model E) (hNE : Nonempty V) :
    ∀ z, NatObject E z → ∀ x y, E x y → E y z → E x z := by
  let body : Formula := .all (.all (.imp (.mem 1 0) (.imp (.mem 0 2) (.mem 1 2))))
  have hB : Bound body 1 := ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩
  have h := omega_induction hM hNE 0 body hB (fun _ => Classical.choice hNE)
    (fun z hz x y _ hyz => False.elim (hz y hyz))
    (fun z z' _ hzz' ih x y hxy hyz' => by
      rcases (hzz' y).mp hyz' with hyz | rfl
      · exact (hzz' x).mpr (Or.inl (ih x y hxy hyz))
      · exact (hzz' x).mpr (Or.inl hxy))
  exact h

theorem nat_zero_le (hM : Model E) (hNE : Nonempty V) {z : V} (hz : Empty E z) :
    ∀ x, NatObject E x → z = x ∨ E z x := by
  let body : Formula := .or (.eq 1 0) (.mem 1 0)
  have hB : Bound body 2 := ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  exact omega_induction hM hNE 1 body hB (fun _ => z)
    (fun z' hz' => Or.inl (empty_unique hM hNE hz hz'))
    (fun x y _ hxy ih => by
      dsimp only [body, eval, pushValue] at ih ⊢
      rcases ih with hzx | hzx
      · exact Or.inr ((hxy z).mpr (Or.inr hzx))
      · exact Or.inr ((hxy z).mpr (Or.inl hzx)))

theorem nat_succ_le_iff (hM : Model E) (hNE : Nonempty V) {x x' : V}
    (_hx : NatObject E x) (hxx' : Succ E x x') :
    ∀ y, NatObject E y → (E x y ↔ x' = y ∨ E x' y) := by
  let body : Formula := fIff (.mem 1 0) (.or (.eq 2 0) (.mem 2 0))
  have hB : Bound body 3 :=
    bound_fIff ⟨by omega, by omega⟩ ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  let env : Nat → V := fun i => if i = 0 then x else x'
  have h := omega_induction hM hNE 2 body hB env
    (fun z hz => by
      apply (eval_fIff _ _ _).mpr
      dsimp only [eval, pushValue, env]
      constructor
      · intro hxz; exact False.elim (hz x hxz)
      · rintro (heq | hx'z)
        · exact False.elim (hz x (heq ▸ (hxx' x).mpr (Or.inr rfl)))
        · exact False.elim (hz x' hx'z))
    (fun y y' hy hyy' ih => by
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
  intro y hy
  exact (eval_fIff _ _ _).mp (h y hy)

theorem nat_trichotomy (hM : Model E) (hNE : Nonempty V) :
    ∀ x, NatObject E x → ∀ y, NatObject E y → E x y ∨ x = y ∨ E y x := by
  intro x hx
  let body : Formula := .or (.mem 1 0) (.or (.eq 1 0) (.mem 0 1))
  have hB : Bound body 2 := ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩
  exact omega_induction hM hNE 1 body hB (fun _ => x)
    (fun z hz => by
      dsimp only [body, eval, pushValue]
      rcases nat_zero_le hM hNE hz x hx with hzx | hzx
      · exact Or.inr (Or.inl hzx.symm)
      · exact Or.inr (Or.inr hzx))
    (fun y y' hy hyy' ih => by
      dsimp only [body, eval, pushValue] at ih ⊢
      rcases ih with hxy | hxy | hyx
      · exact Or.inl ((hyy' x).mpr (Or.inl hxy))
      · exact Or.inl ((hyy' x).mpr (Or.inr hxy))
      · rcases (nat_succ_le_iff hM hNE hy hyy' x hx).mp hyx with hy'x | hy'x
        · exact Or.inr (Or.inl hy'x.symm)
        · exact Or.inr (Or.inr hy'x))

theorem succ_inj (hM : Model E) (hNE : Nonempty V) {x y z : V}
    (hx : NatObject E x) (hy : NatObject E y) (hxz : Succ E x z) (hyz : Succ E y z) : x = y := by
  rcases nat_trichotomy hM hNE x hx y hy with hxy | hxy | hyx
  · have hyz' : E y z := (hyz y).mpr (Or.inr rfl)
    rcases (hxz y).mp hyz' with hyx | hyx
    · exact False.elim (mem_asymm hM hNE hxy hyx)
    · exact False.elim (mem_irrefl hM hNE x (hyx ▸ hxy))
  · exact hxy
  · have hxz' : E x z := (hxz x).mpr (Or.inr rfl)
    rcases (hyz x).mp hxz' with hxy | hxy
    · exact False.elim (mem_asymm hM hNE hyx hxy)
    · exact False.elim (mem_irrefl hM hNE y (hxy ▸ hyx))

theorem bound_rename {f : Formula} {k m : Nat} {σ : Nat → Nat}
    (hf : Bound f k) (hσ : ∀ i < k, σ i < m) : Bound (rename σ f) m := by
  induction f generalizing k m σ with
  | bot => trivial
  | mem i j => exact ⟨hσ i hf.1, hσ j hf.2⟩
  | eq i j => exact ⟨hσ i hf.1, hσ j hf.2⟩
  | and p q ihp ihq => exact ⟨ihp hf.1 hσ, ihq hf.2 hσ⟩
  | or p q ihp ihq => exact ⟨ihp hf.1 hσ, ihq hf.2 hσ⟩
  | imp p q ihp ihq => exact ⟨ihp hf.1 hσ, ihq hf.2 hσ⟩
  | all p ihp =>
    exact ihp hf (fun i hi => by
      cases i with
      | zero => exact Nat.zero_lt_succ m
      | succ j => exact Nat.succ_lt_succ (hσ j (Nat.lt_of_succ_lt_succ hi)))
  | ex p ihp =>
    exact ihp hf (fun i hi => by
      cases i with
      | zero => exact Nat.zero_lt_succ m
      | succ j => exact Nat.succ_lt_succ (hσ j (Nat.lt_of_succ_lt_succ hi)))

theorem omega_strong_induction (hM : Model E) (hNE : Nonempty V) (n : Nat) (body : Formula)
    (hB : Bound body (n + 1)) (env : Nat → V)
    (hstep : ∀ x, NatObject E x →
      (∀ y, E y x → eval E body (pushValue env y)) → eval E body (pushValue env x)) :
    ∀ x, NatObject E x → eval E body (pushValue env x) := by
  let qBody : Formula := .all (.imp (.mem 0 1) (rename (fun i => if i = 0 then 0 else i + 1) body))
  have hB' : Bound (rename (fun i => if i = 0 then 0 else i + 1) body) (n + 2) :=
    bound_rename hB (fun i hi => by split <;> omega)
  have hqB : Bound qBody (n + 1) := ⟨⟨by omega, by omega⟩, hB'⟩
  have hRen : ∀ x y, eval E (rename (fun i => if i = 0 then 0 else i + 1) body)
      (pushValue (pushValue env x) y) ↔ eval E body (pushValue env y) := by
    intro x y
    rw [eval_rename]
    apply eval_congr_bound E body (n + 1) _ _ hB
    intro i _
    cases i <;> rfl
  have hQ : ∀ x, NatObject E x → eval E qBody (pushValue env x) :=
    omega_induction hM hNE n qBody hqB env
      (fun z hz y hy => False.elim (hz y hy))
      (fun x x' hx hxx' ih y hy => by
        apply (hRen x' y).mpr
        rcases (hxx' y).mp hy with hyx | hyx
        · exact (hRen x y).mp (ih y hyx)
        · rw [hyx]
          exact hstep x hx (fun u hu => (hRen x u).mp (ih u hu)))
  intro x hx
  obtain ⟨x', hxx'⟩ := exists_succ hM hNE x
  exact (hRen x' x).mp (hQ x' (nat_succ hM hNE hx hxx') x ((hxx' x).mpr (Or.inr rfl)))

/-! ### Part 3A: Add, Mul totality/functionality and Arithmetic Laws -/

theorem functionOn_singleton (hM : Model E) (hNE : Nonempty V) {z dom a : V}
    (hz : Empty E z) (hdom : Succ E z dom) :
    ∃ f, FunctionOn E f dom ∧ At E f z a ∧ ∀ x y, At E f x y → x = z ∧ y = a := by
  obtain ⟨p, hp⟩ := exists_orderedPair hM hNE z a
  obtain ⟨f, hf⟩ := ax_pair hM hNE p p
  have hAt : ∀ x y, At E f x y ↔ x = z ∧ y = a := by
    intro x y
    constructor
    · rintro ⟨q, hqf, hq⟩
      rcases (hf q).mp hqf with rfl | rfl
      · exact orderedPair_inj hq hp
      · exact orderedPair_inj hq hp
    · rintro ⟨rfl, rfl⟩
      exact ⟨p, (hf p).mpr (Or.inl rfl), hp⟩
  refine ⟨f, ⟨?_, ?_⟩, (hAt z a).mpr ⟨rfl, rfl⟩, fun x y h => (hAt x y).mp h⟩
  · intro x hx
    rcases (hdom x).mp hx with hxz | rfl
    · exact False.elim (hz x hxz)
    · exact ⟨a, (hAt x a).mpr ⟨rfl, rfl⟩, fun w hw => ((hAt x w).mp hw).2⟩
  · intro q hq
    rcases (hf q).mp hq with rfl | rfl
    · exact ⟨z, a, (hdom z).mpr (Or.inr rfl), hp⟩
    · exact ⟨z, a, (hdom z).mpr (Or.inr rfl), hp⟩

theorem functionOn_extend (hM : Model E) (hNE : Nonempty V) {f dom dom' y : V}
    (hfun : FunctionOn E f dom) (hdom' : Succ E dom dom') :
    ∃ f', FunctionOn E f' dom' ∧
      (∀ x w, At E f' x w ↔ At E f x w ∨ (x = dom ∧ w = y)) := by
  obtain ⟨p, hp⟩ := exists_orderedPair hM hNE dom y
  obtain ⟨f', hf'⟩ := exists_insert hM hNE f p
  have hAt : ∀ x w, At E f' x w ↔ At E f x w ∨ (x = dom ∧ w = y) := by
    intro x w
    constructor
    · rintro ⟨q, hqf', hq⟩
      rcases (hf' q).mp hqf' with hqf | rfl
      · exact Or.inl ⟨q, hqf, hq⟩
      · exact Or.inr (orderedPair_inj hq hp)
    · rintro (⟨q, hqf, hq⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, (hf' q).mpr (Or.inl hqf), hq⟩
      · exact ⟨p, (hf' p).mpr (Or.inr rfl), hp⟩
  refine ⟨f', ⟨?_, ?_⟩, hAt⟩
  · intro x hx
    rcases (hdom' x).mp hx with hxdom | hxeq
    · obtain ⟨w, hfw, huniq⟩ := hfun.1 x hxdom
      refine ⟨w, (hAt x w).mpr (Or.inl hfw), fun z hz => ?_⟩
      rcases (hAt x z).mp hz with hfz | ⟨hxd, _⟩
      · exact huniq z hfz
      · exact False.elim (mem_irrefl hM hNE x (hxd ▸ hxdom))
    · rw [hxeq]
      refine ⟨y, (hAt dom y).mpr (Or.inr ⟨rfl, rfl⟩), fun z hz => ?_⟩
      rcases (hAt dom z).mp hz with ⟨q, hqf, hq⟩ | ⟨_, hzy⟩
      · obtain ⟨u, v, hudom, huv⟩ := hfun.2 q hqf
        have hdu := (orderedPair_inj hq huv).1
        exact False.elim (mem_irrefl hM hNE dom (hdu ▸ hudom))
      · exact hzy
  · intro q hq
    rcases (hf' q).mp hq with hqf | rfl
    · obtain ⟨u, v, hudom, huv⟩ := hfun.2 q hqf
      exact ⟨u, v, (hdom' u).mpr (Or.inl hudom), huv⟩
    · exact ⟨dom, y, (hdom' dom).mpr (Or.inr rfl), hp⟩

theorem add_zero (hM : Model E) (hNE : Nonempty V) {a z : V}
    (ha : NatObject E a) (hz : Empty E z) : Add E a z a := by
  have hzNat : NatObject E z := nat_zero hM hNE hz
  obtain ⟨dom, hdom⟩ := exists_succ hM hNE z
  obtain ⟨f, hfun, hfza, hfat⟩ := functionOn_singleton hM hNE hz hdom
  refine ⟨ha, hzNat, ha, z, dom, f, hz, hdom, hfun, hfza, hfza, ?_, ?_⟩
  · intro i x _ hfix
    have ⟨_, hxa⟩ := hfat i x hfix
    rw [hxa]; exact ha
  · intro i hi
    exact False.elim (hz i hi)

theorem add_succ (hM : Model E) (hNE : Nonempty V) {a b b' c c' : V}
    (habc : Add E a b c) (hbb' : Succ E b b') (hcc' : Succ E c c') : Add E a b' c' := by
  rcases habc with ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
  have hb' : NatObject E b' := nat_succ hM hNE hb hbb'
  have hc' : NatObject E c' := nat_succ hM hNE hc hcc'
  have hdom_eq : dom = b' := succ_unique hM hNE hdom hbb'
  subst hdom_eq
  obtain ⟨dom', hdom'⟩ := exists_succ hM hNE dom
  obtain ⟨f', hfun', hf'at⟩ := functionOn_extend hM hNE hfun hdom'
  refine ⟨ha, hb', hc', z, dom', f', hz, hdom', hfun',
    (hf'at z a).mpr (Or.inl hf0), (hf'at dom c').mpr (Or.inr ⟨rfl, rfl⟩), ?_, ?_⟩
  · intro i x _ hfix
    rcases (hf'at i x).mp hfix with hfx | ⟨_, rfl⟩
    · obtain ⟨q, hqf, hq⟩ := hfx
      obtain ⟨u, v, hudom, huv⟩ := hfun.2 q hqf
      have ⟨_, h2⟩ := orderedPair_inj hq huv
      rw [h2]
      exact hnat u v hudom ⟨q, hqf, huv⟩
    · exact hc'
  · intro i hi
    rcases (hbb' i).mp hi with hib | rfl
    · obtain ⟨j, x, y, hij, hfix, hfjy, hxy⟩ := hstep i hib
      exact ⟨j, x, y, hij, (hf'at i x).mpr (Or.inl hfix), (hf'at j y).mpr (Or.inl hfjy), hxy⟩
    · exact ⟨dom, c, c', hbb', (hf'at i c).mpr (Or.inl hfb),
        (hf'at dom c').mpr (Or.inr ⟨rfl, rfl⟩), hcc'⟩

theorem add_exists (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → ∃ c, Add E a b c := by
  let body : Formula := .ex (fAdd 2 1 0)
  have hB : Bound body 2 := bound_fAdd (by omega) (by omega) (by omega)
  have h := omega_induction hM hNE 1 body hB (fun _ => a)
    (fun z hz => ⟨a, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE ha hz)⟩)
    (fun b b' _ hbb' ih => by
      obtain ⟨c, hc⟩ := ih
      have habc : Add E a b c := (eval_fAdd _ _ _ _).mp hc
      obtain ⟨c', hcc'⟩ := exists_succ hM hNE c
      exact ⟨c', (eval_fAdd _ _ _ _).mpr (add_succ hM hNE habc hbb' hcc')⟩)
  intro b hb
  obtain ⟨c, hc⟩ := h b hb
  exact ⟨c, (eval_fAdd _ _ _ _).mp hc⟩

theorem add_unique (hM : Model E) (hNE : Nonempty V) {a b c₁ c₂ : V}
    (h1 : Add E a b c₁) (h2 : Add E a b c₂) : c₁ = c₂ := by
  rcases h1 with ⟨_, hb, _, z1, dom1, f1, hz1, hdom1, hfun1, hf10, hf1b, _, hstep1⟩
  rcases h2 with ⟨_, _, _, z2, dom2, f2, hz2, hdom2, hfun2, hf20, hf2b, _, hstep2⟩
  have hz : z1 = z2 := empty_unique hM hNE hz1 hz2
  have hdom : dom1 = dom2 := succ_unique hM hNE hdom1 hdom2
  subst hz; subst hdom
  -- Induct on i ∈ ω: i ∈ dom1 → ∀ x y, At f1 i x → At f2 i y → x = y
  let body : Formula :=
    .imp (.mem 0 1) (.all (.all (.imp (fAt 4 2 1) (.imp (fAt 5 2 0) (.eq 1 0)))))
  have hB : Bound body 4 :=
    ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega),
      ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩
  let env : Nat → V := fun k => if k = 0 then dom1 else if k = 1 then f1 else f2
  have hAgree := omega_induction hM hNE 3 body hB env
    (fun z hz _ x y hx hy => by
      have hzeq : z = z1 := empty_unique hM hNE hz hz1
      subst hzeq
      have hxa : x = a := by
        obtain ⟨w, hfw, huniq⟩ := hfun1.1 z ((hdom1 z).mpr (by
          rcases nat_zero_le hM hNE hz b hb with rfl | hzb
          · exact Or.inr rfl
          · exact Or.inl hzb))
        exact (huniq x ((eval_fAt _ _ _ _).mp hx)).trans (huniq a hf10).symm
      have hya : y = a := by
        obtain ⟨w, hfw, huniq⟩ := hfun2.1 z ((hdom1 z).mpr (by
          rcases nat_zero_le hM hNE hz b hb with rfl | hzb
          · exact Or.inr rfl
          · exact Or.inl hzb))
        exact (huniq y ((eval_fAt _ _ _ _).mp hy)).trans (huniq a hf20).symm
      exact hxa.trans hya.symm)
    (fun i j hi hij ih hjdom x y hx hy => by
      have hib : E i b := by
        rcases (hdom1 j).mp hjdom with hjb | hjb
        · exact nat_lt_trans hM hNE b hb i j ((hij i).mpr (Or.inr rfl)) hjb
        · rw [← hjb]; exact (hij i).mpr (Or.inr rfl)
      have hidom : E i dom1 := (hdom1 i).mpr (Or.inl hib)
      obtain ⟨j1, x1, y1, hij1, hf1x1, hf1y1, hx1y1⟩ := hstep1 i hib
      obtain ⟨j2, x2, y2, hij2, hf2x2, hf2y2, hx2y2⟩ := hstep2 i hib
      have hj1 : j1 = j := succ_unique hM hNE hij1 hij
      have hj2 : j2 = j := succ_unique hM hNE hij2 hij
      rw [hj1] at hf1y1
      rw [hj2] at hf2y2
      have hx12 : x1 = x2 := ih hidom x1 x2 ((eval_fAt _ _ _ _).mpr hf1x1) ((eval_fAt _ _ _ _).mpr hf2x2)
      rw [hx12] at hx1y1
      have hy12 : y1 = y2 := succ_unique hM hNE hx1y1 hx2y2
      have hxy1 : x = y1 := by
        obtain ⟨w, _, huniq⟩ := hfun1.1 j hjdom
        exact (huniq x ((eval_fAt _ _ _ _).mp hx)).trans (huniq y1 hf1y1).symm
      have hyy2 : y = y2 := by
        obtain ⟨w, _, huniq⟩ := hfun2.1 j hjdom
        exact (huniq y ((eval_fAt _ _ _ _).mp hy)).trans (huniq y2 hf2y2).symm
      exact hxy1.trans (hy12.trans hyy2.symm))
  exact hAgree b hb ((hdom1 b).mpr (Or.inr rfl)) c₁ c₂
    ((eval_fAt _ _ _ _).mpr hf1b) ((eval_fAt _ _ _ _).mpr hf2b)

theorem mul_zero (hM : Model E) (hNE : Nonempty V) {a z : V}
    (ha : NatObject E a) (hz : Empty E z) : Mul E a z z := by
  have hzNat : NatObject E z := nat_zero hM hNE hz
  obtain ⟨dom, hdom⟩ := exists_succ hM hNE z
  obtain ⟨f, hfun, hfzz, hfat⟩ := functionOn_singleton hM hNE hz hdom
  refine ⟨ha, hzNat, hzNat, z, dom, f, hz, hdom, hfun, hfzz, hfzz, ?_, ?_⟩
  · intro i x _ hfix
    have ⟨_, hxz⟩ := hfat i x hfix
    rw [hxz]; exact hzNat
  · intro i hi
    exact False.elim (hz i hi)

theorem mul_succ (hM : Model E) (hNE : Nonempty V) {a b b' c c' : V}
    (habc : Mul E a b c) (hbb' : Succ E b b') (hadd : Add E c a c') : Mul E a b' c' := by
  rcases habc with ⟨ha, hb, hc, z, dom, f, hz, hdom, hfun, hf0, hfb, hnat, hstep⟩
  have hb' : NatObject E b' := nat_succ hM hNE hb hbb'
  have hc' : NatObject E c' := hadd.2.2.1
  have hdom_eq : dom = b' := succ_unique hM hNE hdom hbb'
  subst hdom_eq
  obtain ⟨dom', hdom'⟩ := exists_succ hM hNE dom
  obtain ⟨f', hfun', hf'at⟩ := functionOn_extend hM hNE hfun hdom'
  refine ⟨ha, hb', hc', z, dom', f', hz, hdom', hfun',
    (hf'at z z).mpr (Or.inl hf0), (hf'at dom c').mpr (Or.inr ⟨rfl, rfl⟩), ?_, ?_⟩
  · intro i x _ hfix
    rcases (hf'at i x).mp hfix with hfx | ⟨_, rfl⟩
    · obtain ⟨q, hqf, hq⟩ := hfx
      obtain ⟨u, v, hudom, huv⟩ := hfun.2 q hqf
      have ⟨_, h2⟩ := orderedPair_inj hq huv
      rw [h2]
      exact hnat u v hudom ⟨q, hqf, huv⟩
    · exact hc'
  · intro i hi
    rcases (hbb' i).mp hi with hib | rfl
    · obtain ⟨j, x, y, hij, hfix, hfjy, hxy⟩ := hstep i hib
      exact ⟨j, x, y, hij, (hf'at i x).mpr (Or.inl hfix), (hf'at j y).mpr (Or.inl hfjy), hxy⟩
    · exact ⟨dom, c, c', hbb', (hf'at i c).mpr (Or.inl hfb),
        (hf'at dom c').mpr (Or.inr ⟨rfl, rfl⟩), hadd⟩

theorem mul_exists (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → ∃ c, Mul E a b c := by
  let body : Formula := .ex (fMul 2 1 0)
  have hB : Bound body 2 := bound_fMul (by omega) (by omega) (by omega)
  have h := omega_induction hM hNE 1 body hB (fun _ => a)
    (fun z hz => ⟨z, (eval_fMul _ _ _ _).mpr (mul_zero hM hNE ha hz)⟩)
    (fun b b' _ hbb' ih => by
      obtain ⟨c, hc⟩ := ih
      have habc : Mul E a b c := (eval_fMul _ _ _ _).mp hc
      obtain ⟨c', hc'⟩ := add_exists hM hNE habc.2.2.1 a ha
      exact ⟨c', (eval_fMul _ _ _ _).mpr (mul_succ hM hNE habc hbb' hc')⟩)
  intro b hb
  obtain ⟨c, hc⟩ := h b hb
  exact ⟨c, (eval_fMul _ _ _ _).mp hc⟩

theorem mul_unique (hM : Model E) (hNE : Nonempty V) {a b c₁ c₂ : V}
    (h1 : Mul E a b c₁) (h2 : Mul E a b c₂) : c₁ = c₂ := by
  rcases h1 with ⟨_, hb, _, z1, dom1, f1, hz1, hdom1, hfun1, hf10, hf1b, _, hstep1⟩
  rcases h2 with ⟨_, _, _, z2, dom2, f2, hz2, hdom2, hfun2, hf20, hf2b, _, hstep2⟩
  have hz : z1 = z2 := empty_unique hM hNE hz1 hz2
  have hdom : dom1 = dom2 := succ_unique hM hNE hdom1 hdom2
  subst hz; subst hdom
  let body : Formula :=
    .imp (.mem 0 1) (.all (.all (.imp (fAt 4 2 1) (.imp (fAt 5 2 0) (.eq 1 0)))))
  have hB : Bound body 4 :=
    ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega),
      ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩
  let env : Nat → V := fun k => if k = 0 then dom1 else if k = 1 then f1 else f2
  have hAgree := omega_induction hM hNE 3 body hB env
    (fun z hz _ x y hx hy => by
      have hzeq : z = z1 := empty_unique hM hNE hz hz1
      subst hzeq
      have hzdom : E z dom1 := (hdom1 z).mpr (by
        rcases nat_zero_le hM hNE hz b hb with rfl | hzb
        · exact Or.inr rfl
        · exact Or.inl hzb)
      have hxz : x = z := by
        obtain ⟨w, _, huniq⟩ := hfun1.1 z hzdom
        exact (huniq x ((eval_fAt _ _ _ _).mp hx)).trans (huniq z hf10).symm
      have hyz : y = z := by
        obtain ⟨w, _, huniq⟩ := hfun2.1 z hzdom
        exact (huniq y ((eval_fAt _ _ _ _).mp hy)).trans (huniq z hf20).symm
      exact hxz.trans hyz.symm)
    (fun i j _ hij ih hjdom x y hx hy => by
      have hib : E i b := by
        rcases (hdom1 j).mp hjdom with hjb | hjb
        · exact nat_lt_trans hM hNE b hb i j ((hij i).mpr (Or.inr rfl)) hjb
        · rw [← hjb]; exact (hij i).mpr (Or.inr rfl)
      have hidom : E i dom1 := (hdom1 i).mpr (Or.inl hib)
      obtain ⟨j1, x1, y1, hij1, hf1x1, hf1y1, hx1y1⟩ := hstep1 i hib
      obtain ⟨j2, x2, y2, hij2, hf2x2, hf2y2, hx2y2⟩ := hstep2 i hib
      have hj1 : j1 = j := succ_unique hM hNE hij1 hij
      have hj2 : j2 = j := succ_unique hM hNE hij2 hij
      rw [hj1] at hf1y1
      rw [hj2] at hf2y2
      have hx12 : x1 = x2 := ih hidom x1 x2 ((eval_fAt _ _ _ _).mpr hf1x1) ((eval_fAt _ _ _ _).mpr hf2x2)
      rw [hx12] at hx1y1
      have hy12 : y1 = y2 := add_unique hM hNE hx1y1 hx2y2
      have hxy1 : x = y1 := by
        obtain ⟨w, _, huniq⟩ := hfun1.1 j hjdom
        exact (huniq x ((eval_fAt _ _ _ _).mp hx)).trans (huniq y1 hf1y1).symm
      have hyy2 : y = y2 := by
        obtain ⟨w, _, huniq⟩ := hfun2.1 j hjdom
        exact (huniq y ((eval_fAt _ _ _ _).mp hy)).trans (huniq y2 hf2y2).symm
      exact hxy1.trans (hy12.trans hyy2.symm))
  exact hAgree b hb ((hdom1 b).mpr (Or.inr rfl)) c₁ c₂
    ((eval_fAt _ _ _ _).mpr hf1b) ((eval_fAt _ _ _ _).mpr hf2b)

/-! Functional wrappers for arithmetic in a fixed ZF model -/

noncomputable def zeroV (hM : Model E) (hNE : Nonempty V) : V :=
  Classical.choose (ax_empty hM hNE)

theorem zeroV_empty (hM : Model E) (hNE : Nonempty V) : Empty E (zeroV hM hNE) :=
  Classical.choose_spec (ax_empty hM hNE)

theorem zeroV_nat (hM : Model E) (hNE : Nonempty V) : NatObject E (zeroV hM hNE) :=
  nat_zero hM hNE (zeroV_empty hM hNE)

noncomputable def succV (hM : Model E) (hNE : Nonempty V) (a : V) : V :=
  Classical.choose (exists_succ hM hNE a)

theorem succV_spec (hM : Model E) (hNE : Nonempty V) (a : V) : Succ E a (succV hM hNE a) :=
  Classical.choose_spec (exists_succ hM hNE a)

theorem succV_nat (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    NatObject E (succV hM hNE a) :=
  nat_succ hM hNE ha (succV_spec hM hNE a)

open Classical in
noncomputable def addV (hM : Model E) (hNE : Nonempty V) (a b : V) : V :=
  if h : NatObject E a ∧ NatObject E b then
    Classical.choose (add_exists hM hNE h.1 b h.2)
  else
    zeroV hM hNE

theorem addV_spec (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) : Add E a b (addV hM hNE a b) := by
  classical
  unfold addV
  rw [dif_pos ⟨ha, hb⟩]
  exact Classical.choose_spec (add_exists hM hNE ha b hb)

theorem addV_nat (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) : NatObject E (addV hM hNE a b) :=
  (addV_spec hM hNE ha hb).2.2.1

theorem add_iff_eq (hM : Model E) (hNE : Nonempty V) {a b c : V}
    (ha : NatObject E a) (hb : NatObject E b) : Add E a b c ↔ c = addV hM hNE a b :=
  ⟨fun h => add_unique hM hNE h (addV_spec hM hNE ha hb), fun h => h ▸ addV_spec hM hNE ha hb⟩

theorem addV_zero (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    addV hM hNE a (zeroV hM hNE) = a :=
  add_unique hM hNE (addV_spec hM hNE ha (zeroV_nat hM hNE))
    (add_zero hM hNE ha (zeroV_empty hM hNE))

theorem addV_succ (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) :
    addV hM hNE a (succV hM hNE b) = succV hM hNE (addV hM hNE a b) :=
  add_unique hM hNE (addV_spec hM hNE ha (succV_nat hM hNE hb))
    (add_succ hM hNE (addV_spec hM hNE ha hb) (succV_spec hM hNE b) (succV_spec hM hNE _))

open Classical in
noncomputable def mulV (hM : Model E) (hNE : Nonempty V) (a b : V) : V :=
  if h : NatObject E a ∧ NatObject E b then
    Classical.choose (mul_exists hM hNE h.1 b h.2)
  else
    zeroV hM hNE

theorem mulV_spec (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) : Mul E a b (mulV hM hNE a b) := by
  classical
  unfold mulV
  rw [dif_pos ⟨ha, hb⟩]
  exact Classical.choose_spec (mul_exists hM hNE ha b hb)

theorem mulV_nat (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) : NatObject E (mulV hM hNE a b) :=
  (mulV_spec hM hNE ha hb).2.2.1

theorem mul_iff_eq (hM : Model E) (hNE : Nonempty V) {a b c : V}
    (ha : NatObject E a) (hb : NatObject E b) : Mul E a b c ↔ c = mulV hM hNE a b :=
  ⟨fun h => mul_unique hM hNE h (mulV_spec hM hNE ha hb), fun h => h ▸ mulV_spec hM hNE ha hb⟩

theorem mulV_zero (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    mulV hM hNE a (zeroV hM hNE) = zeroV hM hNE :=
  mul_unique hM hNE (mulV_spec hM hNE ha (zeroV_nat hM hNE))
    (mul_zero hM hNE ha (zeroV_empty hM hNE))

theorem mulV_succ (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) :
    mulV hM hNE a (succV hM hNE b) = addV hM hNE (mulV hM hNE a b) a :=
  mul_unique hM hNE (mulV_spec hM hNE ha (succV_nat hM hNE hb))
    (mul_succ hM hNE (mulV_spec hM hNE ha hb) (succV_spec hM hNE b)
      (addV_spec hM hNE (mulV_nat hM hNE ha hb) ha))

/-! Algebraic laws on ω via omega_induction -/

theorem zero_addV (hM : Model E) (hNE : Nonempty V) :
    ∀ a, NatObject E a → addV hM hNE (zeroV hM hNE) a = a := by
  let body : Formula := fAdd 1 0 0
  have hB : Bound body 2 := bound_fAdd (by omega) (by omega) (by omega)
  have h := omega_induction hM hNE 1 body hB (fun _ => zeroV hM hNE)
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      exact (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (zeroV_nat hM hNE) (zeroV_empty hM hNE)))
    (fun x y hx hxy ih => by
      have h1 : Add E (zeroV hM hNE) x x := (eval_fAdd _ _ _ _).mp ih
      exact (eval_fAdd _ _ _ _).mpr (add_succ hM hNE h1 hxy hxy))
  intro a ha
  exact (add_iff_eq hM hNE (zeroV_nat hM hNE) ha).mp ((eval_fAdd _ _ _ _).mp (h a ha)) |>.symm

theorem succ_addV (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → addV hM hNE (succV hM hNE a) b = succV hM hNE (addV hM hNE a b) := by
  let body : Formula := .ex (.and (fAdd 2 1 0) (.ex (.and (fSucc 1 0) (fAdd 4 2 0))))
  have hB : Bound body 3 :=
    ⟨bound_fAdd (by omega) (by omega) (by omega),
     bound_fSucc (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩
  let env : Nat → V := fun i => if i = 0 then a else succV hM hNE a
  have h := omega_induction hM hNE 2 body hB env
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      refine ⟨a, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE ha (zeroV_empty hM hNE)),
        succV hM hNE a, (eval_fSucc _ _ _).mpr (succV_spec hM hNE a),
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (succV_nat hM hNE ha) (zeroV_empty hM hNE))⟩)
    (fun x y hx hxy ih => by
      rcases ih with ⟨s, hs, s', hss', hadd'⟩
      have hs' : Add E a x s := (eval_fAdd _ _ _ _).mp hs
      have hss'' : Succ E s s' := (eval_fSucc _ _ _).mp hss'
      have hadd'' : Add E (succV hM hNE a) x s' := (eval_fAdd _ _ _ _).mp hadd'
      obtain ⟨s'', hs's''⟩ := exists_succ hM hNE s'
      exact ⟨s', (eval_fAdd _ _ _ _).mpr (add_succ hM hNE hs' hxy hss''),
        s'', (eval_fSucc _ _ _).mpr hs's'',
        (eval_fAdd _ _ _ _).mpr (add_succ hM hNE hadd'' hxy hs's'')⟩)
  intro b hb
  rcases h b hb with ⟨s, hs, s', hss', hadd'⟩
  have h1 : s = addV hM hNE a b := (add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp hs)
  subst h1
  have h2 : s' = succV hM hNE (addV hM hNE a b) :=
    succ_unique hM hNE ((eval_fSucc _ _ _).mp hss') (succV_spec hM hNE _)
  subst h2
  exact ((add_iff_eq hM hNE (succV_nat hM hNE ha) hb).mp ((eval_fAdd _ _ _ _).mp hadd')).symm

theorem addV_comm (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → addV hM hNE a b = addV hM hNE b a := by
  let body : Formula := .ex (.and (fAdd 2 1 0) (fAdd 1 2 0))
  have hB : Bound body 2 := ⟨bound_fAdd (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩
  have h := omega_induction hM hNE 1 body hB (fun _ => a)
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      refine ⟨a, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE ha (zeroV_empty hM hNE)),
        (eval_fAdd _ _ _ _).mpr ?_⟩
      show Add E (zeroV hM hNE) a a
      have := addV_spec hM hNE (zeroV_nat hM hNE) ha
      rwa [zero_addV hM hNE a ha] at this)
    (fun x y hx hxy ih => by
      have hy : y = succV hM hNE x := succ_unique hM hNE hxy (succV_spec hM hNE x)
      subst hy
      rcases ih with ⟨s, h1, h2⟩
      have hs1 : s = addV hM hNE a x := (add_iff_eq hM hNE ha hx).mp ((eval_fAdd _ _ _ _).mp h1)
      have hs2 : s = addV hM hNE x a := (add_iff_eq hM hNE hx ha).mp ((eval_fAdd _ _ _ _).mp h2)
      refine ⟨succV hM hNE s, ?_, ?_⟩
      · apply (eval_fAdd _ _ _ _).mpr
        rw [hs1, ← addV_succ hM hNE ha hx]
        exact addV_spec hM hNE ha (succV_nat hM hNE hx)
      · apply (eval_fAdd _ _ _ _).mpr
        rw [hs2, ← succ_addV hM hNE hx a ha]
        exact addV_spec hM hNE (succV_nat hM hNE hx) ha)
  intro b hb
  rcases h b hb with ⟨s, h1, h2⟩
  exact ((add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp h1)).symm.trans
    ((add_iff_eq hM hNE hb ha).mp ((eval_fAdd _ _ _ _).mp h2))

theorem addV_assoc (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) :
    ∀ c, NatObject E c → addV hM hNE (addV hM hNE a b) c = addV hM hNE a (addV hM hNE b c) := by
  let body : Formula :=
    .ex (.ex (.ex (.and (fAdd 4 5 2) (.and (fAdd 5 3 1) (.and (fAdd 2 3 0) (fAdd 4 1 0))))))
  have hB : Bound body 3 :=
    ⟨bound_fAdd (by omega) (by omega) (by omega),
     bound_fAdd (by omega) (by omega) (by omega),
     bound_fAdd (by omega) (by omega) (by omega),
     bound_fAdd (by omega) (by omega) (by omega)⟩
  let env : Nat → V := fun i => if i = 0 then a else b
  have h := omega_induction hM hNE 2 body hB env
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      refine ⟨addV hM hNE a b, b, addV hM hNE a b,
        (eval_fAdd _ _ _ _).mpr (addV_spec hM hNE ha hb),
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE hb (zeroV_empty hM hNE)),
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (addV_nat hM hNE ha hb) (zeroV_empty hM hNE)),
        (eval_fAdd _ _ _ _).mpr (addV_spec hM hNE ha hb)⟩)
    (fun c c' hc hcc' ih => by
      have hc' : c' = succV hM hNE c := succ_unique hM hNE hcc' (succV_spec hM hNE c)
      subst hc'
      rcases ih with ⟨ab, bc, tot, hab, hbc, h1, h2⟩
      have hab' : ab = addV hM hNE a b := (add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp hab)
      have hbc' : bc = addV hM hNE b c := (add_iff_eq hM hNE hb hc).mp ((eval_fAdd _ _ _ _).mp hbc)
      have h1' : tot = addV hM hNE ab c := (add_iff_eq hM hNE (hab' ▸ addV_nat hM hNE ha hb) hc).mp ((eval_fAdd _ _ _ _).mp h1)
      have h2' : tot = addV hM hNE a bc := (add_iff_eq hM hNE ha (hbc' ▸ addV_nat hM hNE hb hc)).mp ((eval_fAdd _ _ _ _).mp h2)
      subst hab'; subst hbc'
      refine ⟨addV hM hNE a b, succV hM hNE (addV hM hNE b c), succV hM hNE tot,
        (eval_fAdd _ _ _ _).mpr (addV_spec hM hNE ha hb),
        (eval_fAdd _ _ _ _).mpr (by
          show Add E b (succV hM hNE c) (succV hM hNE (addV hM hNE b c))
          rw [← addV_succ hM hNE hb hc]; exact addV_spec hM hNE hb (succV_nat hM hNE hc)),
        (eval_fAdd _ _ _ _).mpr (by
          show Add E (addV hM hNE a b) (succV hM hNE c) (succV hM hNE tot)
          rw [h1', ← addV_succ hM hNE (addV_nat hM hNE ha hb) hc]
          exact addV_spec hM hNE (addV_nat hM hNE ha hb) (succV_nat hM hNE hc)),
        (eval_fAdd _ _ _ _).mpr (by
          show Add E a (succV hM hNE (addV hM hNE b c)) (succV hM hNE tot)
          rw [h2', ← addV_succ hM hNE ha (addV_nat hM hNE hb hc)]
          exact addV_spec hM hNE ha (succV_nat hM hNE (addV_nat hM hNE hb hc)))⟩)
  intro c hc
  rcases h c hc with ⟨ab, bc, tot, hab, hbc, h1, h2⟩
  have hab' : ab = addV hM hNE a b := (add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp hab)
  have hbc' : bc = addV hM hNE b c := (add_iff_eq hM hNE hb hc).mp ((eval_fAdd _ _ _ _).mp hbc)
  subst hab'; subst hbc'
  exact ((add_iff_eq hM hNE (addV_nat hM hNE ha hb) hc).mp ((eval_fAdd _ _ _ _).mp h1)).symm.trans
    ((add_iff_eq hM hNE ha (addV_nat hM hNE hb hc)).mp ((eval_fAdd _ _ _ _).mp h2))

theorem addV_cancel_right (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) :
    ∀ c, NatObject E c → addV hM hNE a c = addV hM hNE b c → a = b := by
  let body : Formula := .imp (.ex (.and (fAdd 2 1 0) (fAdd 3 1 0))) (.eq 1 2)
  have hB : Bound body 3 :=
    ⟨⟨bound_fAdd (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩,
     ⟨by omega, by omega⟩⟩
  let env : Nat → V := fun i => if i = 0 then a else b
  have h := omega_induction hM hNE 2 body hB env
    (fun z hz ⟨s, h1, h2⟩ => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      have ha1 := (add_iff_eq hM hNE ha (zeroV_nat hM hNE)).mp ((eval_fAdd _ _ _ _).mp h1)
      have hb1 := (add_iff_eq hM hNE hb (zeroV_nat hM hNE)).mp ((eval_fAdd _ _ _ _).mp h2)
      rw [addV_zero hM hNE ha] at ha1
      rw [addV_zero hM hNE hb] at hb1
      exact ha1.symm.trans hb1)
    (fun c c' hc hcc' ih ⟨s, h1, h2⟩ => by
      have hc' : c' = succV hM hNE c := succ_unique hM hNE hcc' (succV_spec hM hNE c)
      subst hc'
      have h1' := (add_iff_eq hM hNE ha (succV_nat hM hNE hc)).mp ((eval_fAdd _ _ _ _).mp h1)
      have h2' := (add_iff_eq hM hNE hb (succV_nat hM hNE hc)).mp ((eval_fAdd _ _ _ _).mp h2)
      rw [addV_succ hM hNE ha hc] at h1'
      rw [addV_succ hM hNE hb hc] at h2'
      have heq : addV hM hNE a c = addV hM hNE b c :=
        succ_inj hM hNE (addV_nat hM hNE ha hc) (addV_nat hM hNE hb hc)
          (succV_spec hM hNE _) (h1'.symm.trans h2' ▸ succV_spec hM hNE _)
      exact ih ⟨addV hM hNE a c, (eval_fAdd _ _ _ _).mpr (addV_spec hM hNE ha hc),
        (eval_fAdd _ _ _ _).mpr (heq ▸ addV_spec hM hNE hb hc)⟩)
  intro c hc heq
  exact h c hc ⟨addV hM hNE a c, (eval_fAdd _ _ _ _).mpr (addV_spec hM hNE ha hc),
    (eval_fAdd _ _ _ _).mpr (heq ▸ addV_spec hM hNE hb hc)⟩

theorem addV_left_distrib (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) :
    ∀ c, NatObject E c → mulV hM hNE a (addV hM hNE b c) = addV hM hNE (mulV hM hNE a b) (mulV hM hNE a c) := by
  let body : Formula :=
    .ex (.ex (.ex (.ex (.and (fAdd 6 4 3) (.and (fMul 5 6 2) (.and (fMul 5 4 1)
      (.and (fMul 5 3 0) (fAdd 2 1 0))))))))
  have hB : Bound body 3 :=
    ⟨bound_fAdd (by omega) (by omega) (by omega),
     bound_fMul (by omega) (by omega) (by omega),
     bound_fMul (by omega) (by omega) (by omega),
     bound_fMul (by omega) (by omega) (by omega),
     bound_fAdd (by omega) (by omega) (by omega)⟩
  let env : Nat → V := fun i => if i = 0 then a else b
  have h := omega_induction hM hNE 2 body hB env
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      refine ⟨b, mulV hM hNE a b, zeroV hM hNE, mulV hM hNE a b,
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE hb (zeroV_empty hM hNE)),
        (eval_fMul _ _ _ _).mpr (mulV_spec hM hNE ha hb),
        (eval_fMul _ _ _ _).mpr (mul_zero hM hNE ha (zeroV_empty hM hNE)),
        (eval_fMul _ _ _ _).mpr (mulV_spec hM hNE ha hb),
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (mulV_nat hM hNE ha hb) (zeroV_empty hM hNE))⟩)
    (fun c c' hc hcc' ih => by
      have hc' : c' = succV hM hNE c := succ_unique hM hNE hcc' (succV_spec hM hNE c)
      subst hc'
      rcases ih with ⟨bc, ab, ac, tot, hbc, hab, hac, h1, h2⟩
      have hbc' : bc = addV hM hNE b c := (add_iff_eq hM hNE hb hc).mp ((eval_fAdd _ _ _ _).mp hbc)
      have hab' : ab = mulV hM hNE a b := (mul_iff_eq hM hNE ha hb).mp ((eval_fMul _ _ _ _).mp hab)
      have hac' : ac = mulV hM hNE a c := (mul_iff_eq hM hNE ha hc).mp ((eval_fMul _ _ _ _).mp hac)
      have h1' : tot = mulV hM hNE a bc := (mul_iff_eq hM hNE ha (hbc' ▸ addV_nat hM hNE hb hc)).mp ((eval_fMul _ _ _ _).mp h1)
      have h2' : tot = addV hM hNE ab ac := (add_iff_eq hM hNE (hab' ▸ mulV_nat hM hNE ha hb) (hac' ▸ mulV_nat hM hNE ha hc)).mp ((eval_fAdd _ _ _ _).mp h2)
      subst hbc'; subst hab'; subst hac'
      have hEq : addV hM hNE (mulV hM hNE a (addV hM hNE b c)) a =
          addV hM hNE (mulV hM hNE a b) (addV hM hNE (mulV hM hNE a c) a) := by
        rw [← h1', h2', addV_assoc hM hNE (mulV_nat hM hNE ha hb) (mulV_nat hM hNE ha hc) a ha]
      refine ⟨succV hM hNE (addV hM hNE b c), mulV hM hNE a b, addV hM hNE (mulV hM hNE a c) a,
        addV hM hNE (mulV hM hNE a (addV hM hNE b c)) a,
        (eval_fAdd _ _ _ _).mpr (addV_succ hM hNE hb hc ▸ addV_spec hM hNE hb (succV_nat hM hNE hc)),
        (eval_fMul _ _ _ _).mpr (mulV_spec hM hNE ha hb),
        (eval_fMul _ _ _ _).mpr (mulV_succ hM hNE ha hc ▸ mulV_spec hM hNE ha (succV_nat hM hNE hc)),
        (eval_fMul _ _ _ _).mpr (mulV_succ hM hNE ha (addV_nat hM hNE hb hc) ▸ mulV_spec hM hNE ha (succV_nat hM hNE (addV_nat hM hNE hb hc))),
        (eval_fAdd _ _ _ _).mpr (hEq ▸ addV_spec hM hNE (mulV_nat hM hNE ha hb) (addV_nat hM hNE (mulV_nat hM hNE ha hc) ha))⟩)
  intro c hc
  rcases h c hc with ⟨bc, ab, ac, tot, hbc, hab, hac, h1, h2⟩
  have hbc' : bc = addV hM hNE b c := (add_iff_eq hM hNE hb hc).mp ((eval_fAdd _ _ _ _).mp hbc)
  have hab' : ab = mulV hM hNE a b := (mul_iff_eq hM hNE ha hb).mp ((eval_fMul _ _ _ _).mp hab)
  have hac' : ac = mulV hM hNE a c := (mul_iff_eq hM hNE ha hc).mp ((eval_fMul _ _ _ _).mp hac)
  subst hbc'; subst hab'; subst hac'
  exact ((mul_iff_eq hM hNE ha (addV_nat hM hNE hb hc)).mp ((eval_fMul _ _ _ _).mp h1)).symm.trans
    ((add_iff_eq hM hNE (mulV_nat hM hNE ha hb) (mulV_nat hM hNE ha hc)).mp ((eval_fAdd _ _ _ _).mp h2))

theorem zero_mulV (hM : Model E) (hNE : Nonempty V) :
    ∀ b, NatObject E b → mulV hM hNE (zeroV hM hNE) b = zeroV hM hNE := by
  let body : Formula := fMul 1 0 1
  have hB : Bound body 2 := bound_fMul (by omega) (by omega) (by omega)
  have h := omega_induction hM hNE 1 body hB (fun _ => zeroV hM hNE)
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      exact (eval_fMul _ _ _ _).mpr (mul_zero hM hNE (zeroV_nat hM hNE) (zeroV_empty hM hNE)))
    (fun b b' hb hbb' ih => by
      have h1 := (eval_fMul _ _ _ _).mp ih
      exact (eval_fMul _ _ _ _).mpr (mul_succ hM hNE h1 hbb' (add_zero hM hNE (zeroV_nat hM hNE) (zeroV_empty hM hNE))))
  intro b hb
  exact ((mul_iff_eq hM hNE (zeroV_nat hM hNE) hb).mp ((eval_fMul _ _ _ _).mp (h b hb))).symm

theorem succ_mulV (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → mulV hM hNE (succV hM hNE a) b = addV hM hNE (mulV hM hNE a b) b := by
  let body : Formula := .ex (.ex (.and (fMul 3 2 1) (.and (fAdd 1 2 0) (fMul 4 2 0))))
  have hB : Bound body 3 :=
    ⟨bound_fMul (by omega) (by omega) (by omega),
     bound_fAdd (by omega) (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega)⟩
  let env : Nat → V := fun i => if i = 0 then a else succV hM hNE a
  have h := omega_induction hM hNE 2 body hB env
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      refine ⟨zeroV hM hNE, zeroV hM hNE,
        (eval_fMul _ _ _ _).mpr (mul_zero hM hNE ha (zeroV_empty hM hNE)),
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (zeroV_nat hM hNE) (zeroV_empty hM hNE)),
        (eval_fMul _ _ _ _).mpr (mul_zero hM hNE (succV_nat hM hNE ha) (zeroV_empty hM hNE))⟩)
    (fun b b' hb hbb' ih => by
      have hb' : b' = succV hM hNE b := succ_unique hM hNE hbb' (succV_spec hM hNE b)
      subst hb'
      rcases ih with ⟨ab, tot, hab, htot, hsb⟩
      have hab' : ab = mulV hM hNE a b := (mul_iff_eq hM hNE ha hb).mp ((eval_fMul _ _ _ _).mp hab)
      have htot' : tot = addV hM hNE ab b := (add_iff_eq hM hNE (hab' ▸ mulV_nat hM hNE ha hb) hb).mp ((eval_fAdd _ _ _ _).mp htot)
      have hsb' : tot = mulV hM hNE (succV hM hNE a) b := (mul_iff_eq hM hNE (succV_nat hM hNE ha) hb).mp ((eval_fMul _ _ _ _).mp hsb)
      subst hab'
      have hNatAB : NatObject E (mulV hM hNE a b) := mulV_nat hM hNE ha hb
      have hEq : addV hM hNE (addV hM hNE (mulV hM hNE a b) a) (succV hM hNE b) =
          addV hM hNE tot (succV hM hNE a) := by
        rw [htot', addV_succ hM hNE (addV_nat hM hNE hNatAB ha) hb,
            addV_succ hM hNE (addV_nat hM hNE hNatAB hb) ha,
            addV_assoc hM hNE hNatAB ha b hb, addV_comm hM hNE ha b hb,
            ← addV_assoc hM hNE hNatAB hb a ha]
      refine ⟨addV hM hNE (mulV hM hNE a b) a, addV hM hNE tot (succV hM hNE a),
        (eval_fMul _ _ _ _).mpr (mulV_succ hM hNE ha hb ▸ mulV_spec hM hNE ha (succV_nat hM hNE hb)),
        (eval_fAdd _ _ _ _).mpr (hEq ▸ addV_spec hM hNE (addV_nat hM hNE hNatAB ha) (succV_nat hM hNE hb)),
        (eval_fMul _ _ _ _).mpr (hsb' ▸ mulV_succ hM hNE (succV_nat hM hNE ha) hb ▸ mulV_spec hM hNE (succV_nat hM hNE ha) (succV_nat hM hNE hb))⟩)
  intro b hb
  rcases h b hb with ⟨ab, tot, hab, htot, hsb⟩
  have hab' : ab = mulV hM hNE a b := (mul_iff_eq hM hNE ha hb).mp ((eval_fMul _ _ _ _).mp hab)
  subst hab'
  exact ((mul_iff_eq hM hNE (succV_nat hM hNE ha) hb).mp ((eval_fMul _ _ _ _).mp hsb)).symm.trans
    ((add_iff_eq hM hNE (mulV_nat hM hNE ha hb) hb).mp ((eval_fAdd _ _ _ _).mp htot))

theorem mulV_comm (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → mulV hM hNE a b = mulV hM hNE b a := by
  let body : Formula := .ex (.and (fMul 2 1 0) (fMul 1 2 0))
  have hB : Bound body 2 := ⟨bound_fMul (by omega) (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega)⟩
  have h := omega_induction hM hNE 1 body hB (fun _ => a)
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      refine ⟨zeroV hM hNE, (eval_fMul _ _ _ _).mpr (mul_zero hM hNE ha (zeroV_empty hM hNE)),
        (eval_fMul _ _ _ _).mpr (by
          show Mul E (zeroV hM hNE) a (zeroV hM hNE)
          have := mulV_spec hM hNE (zeroV_nat hM hNE) ha
          rwa [zero_mulV hM hNE a ha] at this)⟩)
    (fun b b' hb hbb' ih => by
      have hb' : b' = succV hM hNE b := succ_unique hM hNE hbb' (succV_spec hM hNE b)
      subst hb'
      rcases ih with ⟨p, h1, h2⟩
      have h1' : p = mulV hM hNE a b := (mul_iff_eq hM hNE ha hb).mp ((eval_fMul _ _ _ _).mp h1)
      have h2' : p = mulV hM hNE b a := (mul_iff_eq hM hNE hb ha).mp ((eval_fMul _ _ _ _).mp h2)
      refine ⟨addV hM hNE p a,
        (eval_fMul _ _ _ _).mpr (h1' ▸ mulV_succ hM hNE ha hb ▸ mulV_spec hM hNE ha (succV_nat hM hNE hb)),
        (eval_fMul _ _ _ _).mpr (h2' ▸ succ_mulV hM hNE hb a ha ▸ mulV_spec hM hNE (succV_nat hM hNE hb) ha)⟩)
  intro b hb
  rcases h b hb with ⟨p, h1, h2⟩
  exact ((mul_iff_eq hM hNE ha hb).mp ((eval_fMul _ _ _ _).mp h1)).symm.trans
    ((mul_iff_eq hM hNE hb ha).mp ((eval_fMul _ _ _ _).mp h2))

theorem mulV_right_distrib (hM : Model E) (hNE : Nonempty V) {a b c : V}
    (ha : NatObject E a) (hb : NatObject E b) (hc : NatObject E c) :
    mulV hM hNE (addV hM hNE a b) c = addV hM hNE (mulV hM hNE a c) (mulV hM hNE b c) := by
  rw [mulV_comm hM hNE (addV_nat hM hNE ha hb) c hc,
      addV_left_distrib hM hNE hc ha b hb,
      mulV_comm hM hNE hc a ha, mulV_comm hM hNE hc b hb]

theorem mulV_assoc (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) :
    ∀ c, NatObject E c → mulV hM hNE (mulV hM hNE a b) c = mulV hM hNE a (mulV hM hNE b c) := by
  let body : Formula :=
    .ex (.ex (.ex (.and (fMul 4 5 2) (.and (fMul 5 3 1) (.and (fMul 2 3 0) (fMul 4 1 0))))))
  have hB : Bound body 3 :=
    ⟨bound_fMul (by omega) (by omega) (by omega),
     bound_fMul (by omega) (by omega) (by omega),
     bound_fMul (by omega) (by omega) (by omega),
     bound_fMul (by omega) (by omega) (by omega)⟩
  let env : Nat → V := fun i => if i = 0 then a else b
  have h := omega_induction hM hNE 2 body hB env
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      refine ⟨mulV hM hNE a b, zeroV hM hNE, zeroV hM hNE,
        (eval_fMul _ _ _ _).mpr (mulV_spec hM hNE ha hb),
        (eval_fMul _ _ _ _).mpr (mul_zero hM hNE hb (zeroV_empty hM hNE)),
        (eval_fMul _ _ _ _).mpr (mul_zero hM hNE (mulV_nat hM hNE ha hb) (zeroV_empty hM hNE)),
        (eval_fMul _ _ _ _).mpr (mul_zero hM hNE ha (zeroV_empty hM hNE))⟩)
    (fun c c' hc hcc' ih => by
      have hc' : c' = succV hM hNE c := succ_unique hM hNE hcc' (succV_spec hM hNE c)
      subst hc'
      rcases ih with ⟨ab, bc, tot, hab, hbc, h1, h2⟩
      have hab' : ab = mulV hM hNE a b := (mul_iff_eq hM hNE ha hb).mp ((eval_fMul _ _ _ _).mp hab)
      have hbc' : bc = mulV hM hNE b c := (mul_iff_eq hM hNE hb hc).mp ((eval_fMul _ _ _ _).mp hbc)
      have h1' : tot = mulV hM hNE ab c := (mul_iff_eq hM hNE (hab' ▸ mulV_nat hM hNE ha hb) hc).mp ((eval_fMul _ _ _ _).mp h1)
      have h2' : tot = mulV hM hNE a bc := (mul_iff_eq hM hNE ha (hbc' ▸ mulV_nat hM hNE hb hc)).mp ((eval_fMul _ _ _ _).mp h2)
      subst hab'; subst hbc'
      have hEq : addV hM hNE tot (mulV hM hNE a b) =
          mulV hM hNE a (addV hM hNE (mulV hM hNE b c) b) := by
        rw [addV_left_distrib hM hNE ha (mulV_nat hM hNE hb hc) b hb, h2']
      refine ⟨mulV hM hNE a b, addV hM hNE (mulV hM hNE b c) b, addV hM hNE tot (mulV hM hNE a b),
        (eval_fMul _ _ _ _).mpr (mulV_spec hM hNE ha hb),
        (eval_fMul _ _ _ _).mpr (by
          show Mul E b (succV hM hNE c) (addV hM hNE (mulV hM hNE b c) b)
          rw [← mulV_succ hM hNE hb hc]; exact mulV_spec hM hNE hb (succV_nat hM hNE hc)),
        (eval_fMul _ _ _ _).mpr (by
          show Mul E (mulV hM hNE a b) (succV hM hNE c) (addV hM hNE tot (mulV hM hNE a b))
          rw [h1', ← mulV_succ hM hNE (mulV_nat hM hNE ha hb) hc]
          exact mulV_spec hM hNE (mulV_nat hM hNE ha hb) (succV_nat hM hNE hc)),
        (eval_fMul _ _ _ _).mpr (by
          show Mul E a (addV hM hNE (mulV hM hNE b c) b) (addV hM hNE tot (mulV hM hNE a b))
          rw [hEq]; exact mulV_spec hM hNE ha (addV_nat hM hNE (mulV_nat hM hNE hb hc) hb))⟩)
  intro c hc
  rcases h c hc with ⟨ab, bc, tot, hab, hbc, h1, h2⟩
  have hab' : ab = mulV hM hNE a b := (mul_iff_eq hM hNE ha hb).mp ((eval_fMul _ _ _ _).mp hab)
  have hbc' : bc = mulV hM hNE b c := (mul_iff_eq hM hNE hb hc).mp ((eval_fMul _ _ _ _).mp hbc)
  subst hab'; subst hbc'
  exact ((mul_iff_eq hM hNE (mulV_nat hM hNE ha hb) hc).mp ((eval_fMul _ _ _ _).mp h1)).symm.trans
    ((mul_iff_eq hM hNE ha (mulV_nat hM hNE hb hc)).mp ((eval_fMul _ _ _ _).mp h2))

theorem mulV_one (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    mulV hM hNE a (succV hM hNE (zeroV hM hNE)) = a := by
  rw [mulV_succ hM hNE ha (zeroV_nat hM hNE), mulV_zero hM hNE ha, zero_addV hM hNE a ha]

theorem one_mulV (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    mulV hM hNE (succV hM hNE (zeroV hM hNE)) a = a := by
  rw [mulV_comm hM hNE (succV_nat hM hNE (zeroV_nat hM hNE)) a ha, mulV_one hM hNE ha]

/-! Order + Addition + Subtraction + Euclidean Division -/

theorem addV_le_left (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → (a = addV hM hNE a b ∨ E a (addV hM hNE a b)) := by
  let body : Formula := .ex (.and (fAdd 2 1 0) (.or (.eq 2 0) (.mem 2 0)))
  have hB : Bound body 2 := ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩
  have h := omega_induction hM hNE 1 body hB (fun _ => a)
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      exact ⟨a, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE ha (zeroV_empty hM hNE)), Or.inl rfl⟩)
    (fun b b' hb hbb' ih => by
      have hb' : b' = succV hM hNE b := succ_unique hM hNE hbb' (succV_spec hM hNE b)
      subst hb'
      rcases ih with ⟨s, hs, hle⟩
      have hs' : s = addV hM hNE a b := (add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp hs)
      subst hs'
      refine ⟨succV hM hNE (addV hM hNE a b),
        (eval_fAdd _ _ _ _).mpr (addV_succ hM hNE ha hb ▸ addV_spec hM hNE ha (succV_nat hM hNE hb)),
        Or.inr ?_⟩
      rcases hle with heq | hlt
      · exact (succV_spec hM hNE _ a).mpr (Or.inr heq)
      · exact (succV_spec hM hNE _ a).mpr (Or.inl hlt))
  intro b hb
  rcases h b hb with ⟨s, hs, hle⟩
  have hs' : s = addV hM hNE a b := (add_iff_eq hM hNE ha hb).mp ((eval_fAdd _ _ _ _).mp hs)
  subst hs'
  exact hle

theorem addV_lt_addV_left (hM : Model E) (hNE : Nonempty V) {a b c : V}
    (ha : NatObject E a) (hb : NatObject E b) (hc : NatObject E c) (hbc : E b c) :
    E (addV hM hNE a b) (addV hM hNE a c) := by
  suffices ∀ x, NatObject E x → E (addV hM hNE b x) (addV hM hNE c x) by
    rw [addV_comm hM hNE ha b hb, addV_comm hM hNE ha c hc]
    exact this a ha
  let body2 : Formula := .ex (.ex (.and (fAdd 3 2 1) (.and (fAdd 4 2 0) (.mem 1 0))))
  have hB2 : Bound body2 3 :=
    ⟨bound_fAdd (by omega) (by omega) (by omega),
     bound_fAdd (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩
  let env : Nat → V := fun i => if i = 0 then b else c
  have h := omega_induction hM hNE 2 body2 hB2 env
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      exact ⟨b, c, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE hb (zeroV_empty hM hNE)),
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE hc (zeroV_empty hM hNE)), hbc⟩)
    (fun x x' hx hxx' ih => by
      have hx' : x' = succV hM hNE x := succ_unique hM hNE hxx' (succV_spec hM hNE x)
      subst hx'
      rcases ih with ⟨bx, cx, hbx, hcx, hlt⟩
      have hbx' : bx = addV hM hNE b x := (add_iff_eq hM hNE hb hx).mp ((eval_fAdd _ _ _ _).mp hbx)
      have hcx' : cx = addV hM hNE c x := (add_iff_eq hM hNE hc hx).mp ((eval_fAdd _ _ _ _).mp hcx)
      subst hbx'; subst hcx'
      have hslt : E (succV hM hNE (addV hM hNE b x)) (succV hM hNE (addV hM hNE c x)) := by
        rcases (nat_succ_le_iff hM hNE (addV_nat hM hNE hb hx) (succV_spec hM hNE _) _ (addV_nat hM hNE hc hx)).mp hlt with heq | hlt'
        · exact (succV_spec hM hNE _ _).mpr (Or.inr heq)
        · exact (succV_spec hM hNE _ _).mpr (Or.inl hlt')
      exact ⟨succV hM hNE (addV hM hNE b x), succV hM hNE (addV hM hNE c x),
        (eval_fAdd _ _ _ _).mpr (addV_succ hM hNE hb hx ▸ addV_spec hM hNE hb (succV_nat hM hNE hx)),
        (eval_fAdd _ _ _ _).mpr (addV_succ hM hNE hc hx ▸ addV_spec hM hNE hc (succV_nat hM hNE hx)),
        hslt⟩)
  intro x hx
  rcases h x hx with ⟨bx, cx, hbx, hcx, hlt⟩
  have hbx' : bx = addV hM hNE b x := (add_iff_eq hM hNE hb hx).mp ((eval_fAdd _ _ _ _).mp hbx)
  have hcx' : cx = addV hM hNE c x := (add_iff_eq hM hNE hc hx).mp ((eval_fAdd _ _ _ _).mp hcx)
  subst hbx'; subst hcx'
  exact hlt

theorem sub_exists (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → (a = b ∨ E a b) → ∃ d, NatObject E d ∧ addV hM hNE a d = b := by
  let body : Formula := .imp (.or (.eq 1 0) (.mem 1 0)) (.ex (fAdd 2 0 1))
  have hB : Bound body 2 := ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, bound_fAdd (by omega) (by omega) (by omega)⟩
  have h := omega_induction hM hNE 1 body hB (fun _ => a)
    (fun z hz hle => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      dsimp only [eval, pushValue] at hle
      rcases hle with heq | hlt
      · refine ⟨zeroV hM hNE, (eval_fAdd 2 0 1 _).mpr ?_⟩
        show Add E a (zeroV hM hNE) (zeroV hM hNE)
        rw [heq]; exact add_zero hM hNE (zeroV_nat hM hNE) (zeroV_empty hM hNE)
      · exact False.elim (zeroV_empty hM hNE a hlt))
    (fun b b' hb hbb' ih hle => by
      have hb' : b' = succV hM hNE b := succ_unique hM hNE hbb' (succV_spec hM hNE b)
      subst hb'
      dsimp only [eval, pushValue] at hle
      rcases hle with heq | hlt
      · refine ⟨zeroV hM hNE, (eval_fAdd 2 0 1 _).mpr ?_⟩
        show Add E a (zeroV hM hNE) (succV hM hNE b)
        rw [← heq]; exact add_zero hM hNE ha (zeroV_empty hM hNE)
      · rcases (succV_spec hM hNE b a).mp hlt with hab | hab
        · obtain ⟨d, hd⟩ := ih (Or.inr hab)
          have hd' : Add E a d b := (eval_fAdd _ _ _ _).mp hd
          exact ⟨succV hM hNE d, (eval_fAdd _ _ _ _).mpr (add_succ hM hNE hd' (succV_spec hM hNE d) (succV_spec hM hNE b))⟩
        · obtain ⟨d, hd⟩ := ih (Or.inl hab)
          have hd' : Add E a d b := (eval_fAdd _ _ _ _).mp hd
          exact ⟨succV hM hNE d, (eval_fAdd _ _ _ _).mpr (add_succ hM hNE hd' (succV_spec hM hNE d) (succV_spec hM hNE b))⟩)
  intro b hb hle
  obtain ⟨d, hd⟩ := h b hb hle
  have hd' : Add E a d b := (eval_fAdd _ _ _ _).mp hd
  exact ⟨d, hd'.2.1, ((add_iff_eq hM hNE ha hd'.2.1).mp hd').symm⟩

theorem div_mod_exists (hM : Model E) (hNE : Nonempty V) {m : V}
    (hm : NatObject E m) (hm_pos : E (zeroV hM hNE) m) :
    ∀ a, NatObject E a → ∃ q r, NatObject E q ∧ NatObject E r ∧
      a = addV hM hNE (mulV hM hNE q m) r ∧ E r m := by
  let body : Formula :=
    .ex (.ex (.ex (.and (fMul 2 4 0) (.and (fAdd 0 1 3) (.mem 1 4)))))
  have hB : Bound body 2 :=
    ⟨bound_fMul (by omega) (by omega) (by omega),
     bound_fAdd (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩
  have h := omega_induction hM hNE 1 body hB (fun _ => m)
    (fun z hz => by
      have : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst this
      refine ⟨zeroV hM hNE, zeroV hM hNE, zeroV hM hNE,
        (eval_fMul _ _ _ _).mpr (by
          show Mul E (zeroV hM hNE) m (zeroV hM hNE)
          have := mulV_spec hM hNE (zeroV_nat hM hNE) hm
          rwa [zero_mulV hM hNE m hm] at this),
        (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (zeroV_nat hM hNE) (zeroV_empty hM hNE)),
        hm_pos⟩)
    (fun a a' ha haa' ih => by
      have ha' : a' = succV hM hNE a := succ_unique hM hNE haa' (succV_spec hM hNE a)
      subst ha'
      rcases ih with ⟨q, r, qm, hqm, hadd, hrm⟩
      have hqm' : Mul E q m qm := (eval_fMul _ _ _ _).mp hqm
      have hadd' : Add E qm r a := (eval_fAdd _ _ _ _).mp hadd
      have hq : NatObject E q := hqm'.1
      have hr : NatObject E r := hadd'.2.1
      have hqm_eq : qm = mulV hM hNE q m := (mul_iff_eq hM hNE hq hm).mp hqm'
      have ha_eq : a = addV hM hNE qm r := (add_iff_eq hM hNE hqm'.2.2.1 hr).mp hadd'
      rcases (nat_succ_le_iff hM hNE hr (succV_spec hM hNE r) m hm).mp hrm with hsr_eq | hsr_lt
      · have hEq : succV hM hNE a = mulV hM hNE (succV hM hNE q) m := by
          rw [ha_eq, ← addV_succ hM hNE hqm'.2.2.1 hr, hsr_eq, hqm_eq, ← succ_mulV hM hNE hq m hm]
        refine ⟨succV hM hNE q, zeroV hM hNE, succV hM hNE a,
          (eval_fMul 2 4 0 _).mpr (by
            show Mul E (succV hM hNE q) m (succV hM hNE a)
            rw [hEq]; exact mulV_spec hM hNE (succV_nat hM hNE hq) hm),
          (eval_fAdd 0 1 3 _).mpr (add_zero hM hNE (succV_nat hM hNE ha) (zeroV_empty hM hNE)),
          hm_pos⟩
      · refine ⟨q, succV hM hNE r, qm, (eval_fMul 2 4 0 _).mpr hqm',
          (eval_fAdd 0 1 3 _).mpr (add_succ hM hNE hadd' (succV_spec hM hNE r) (succV_spec hM hNE a)),
          hsr_lt⟩)
  intro a ha
  rcases h a ha with ⟨q, r, qm, hqm, hadd, hrm⟩
  have hqm' : Mul E q m qm := (eval_fMul _ _ _ _).mp hqm
  have hadd' : Add E qm r a := (eval_fAdd _ _ _ _).mp hadd
  have hqm_eq : qm = mulV hM hNE q m := (mul_iff_eq hM hNE hqm'.1 hm).mp hqm'
  have ha_eq : a = addV hM hNE qm r := (add_iff_eq hM hNE hqm'.2.2.1 hadd'.2.1).mp hadd'
  exact ⟨q, r, hqm'.1, hadd'.2.1, hqm_eq ▸ ha_eq, hrm⟩

theorem div_mod_unique (hM : Model E) (hNE : Nonempty V) {m q₁ r₁ q₂ r₂ : V}
    (hm : NatObject E m) (hq1 : NatObject E q₁) (hr1 : NatObject E r₁)
    (hq2 : NatObject E q₂) (hr2 : NatObject E r₂)
    (h1 : E r₁ m) (h2 : E r₂ m)
    (heq : addV hM hNE (mulV hM hNE q₁ m) r₁ = addV hM hNE (mulV hM hNE q₂ m) r₂) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  have hlt_contra : ∀ q r q' r', NatObject E q → NatObject E r → NatObject E q' → NatObject E r' →
      E r m → E q q' → addV hM hNE (mulV hM hNE q m) r ≠ addV hM hNE (mulV hM hNE q' m) r' := by
    intro q r q' r' hq hr hq' hr' hrm hqq' heq'
    have hsq_le : succV hM hNE q = q' ∨ E (succV hM hNE q) q' :=
      (nat_succ_le_iff hM hNE hq (succV_spec hM hNE q) q' hq').mp hqq'
    obtain ⟨d, hd, hd_eq⟩ := sub_exists hM hNE (succV_nat hM hNE hq) q' hq' hsq_le
    have hq'_mul : mulV hM hNE q' m = addV hM hNE (addV hM hNE (mulV hM hNE q m) m) (mulV hM hNE d m) := by
      rw [← hd_eq, mulV_right_distrib hM hNE (succV_nat hM hNE hq) hd hm, succ_mulV hM hNE hq m hm]
    have h1lt : E (addV hM hNE (mulV hM hNE q m) r) (addV hM hNE (mulV hM hNE q m) m) :=
      addV_lt_addV_left hM hNE (mulV_nat hM hNE hq hm) hr hm hrm
    have h2le : addV hM hNE (mulV hM hNE q m) m = addV hM hNE (mulV hM hNE q' m) r' ∨
        E (addV hM hNE (mulV hM hNE q m) m) (addV hM hNE (mulV hM hNE q' m) r') := by
      rw [hq'_mul, addV_assoc hM hNE (addV_nat hM hNE (mulV_nat hM hNE hq hm) hm) (mulV_nat hM hNE hd hm) r' hr']
      exact addV_le_left hM hNE (addV_nat hM hNE (mulV_nat hM hNE hq hm) hm) _ (addV_nat hM hNE (mulV_nat hM hNE hd hm) hr')
    rw [heq'] at h1lt
    rcases h2le with h | h
    · exact mem_irrefl hM hNE _ (h ▸ h1lt)
    · exact mem_asymm hM hNE h1lt h
  rcases nat_trichotomy hM hNE q₁ hq1 q₂ hq2 with hlt | rfl | hgt
  · exact False.elim (hlt_contra q₁ r₁ q₂ r₂ hq1 hr1 hq2 hr2 h1 hlt heq)
  · refine ⟨rfl, ?_⟩
    rw [addV_comm hM hNE (mulV_nat hM hNE hq1 hm) r₁ hr1,
        addV_comm hM hNE (mulV_nat hM hNE hq1 hm) r₂ hr2] at heq
    exact addV_cancel_right hM hNE hr1 hr2 (mulV hM hNE q₁ m) (mulV_nat hM hNE hq1 hm) heq
  · exact False.elim (hlt_contra q₂ r₂ q₁ r₁ hq2 hr2 hq1 hr1 h2 hgt heq.symm)

/-! ### Part 3B: Divisibility, Coprimality, Bezout, CRT, and Gödel's β-function -/

noncomputable abbrev oneV (hM : Model E) (hNE : Nonempty V) : V := succV hM hNE (zeroV hM hNE)

theorem oneV_nat (hM : Model E) (hNE : Nonempty V) : NatObject E (oneV hM hNE) :=
  succV_nat hM hNE (zeroV_nat hM hNE)

theorem zero_lt_succV (hM : Model E) (hNE : Nonempty V) {x : V} (hx : NatObject E x) :
    E (zeroV hM hNE) (succV hM hNE x) := by
  rcases nat_zero_le hM hNE (zeroV_empty hM hNE) x hx with h | h
  · exact (succV_spec hM hNE x _).mpr (Or.inr h)
  · exact (succV_spec hM hNE x _).mpr (Or.inl h)

theorem mulV_pos (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b)
    (ha_pos : E (zeroV hM hNE) a) (hb_pos : E (zeroV hM hNE) b) :
    E (zeroV hM hNE) (mulV hM hNE a b) := by
  have h1a : oneV hM hNE = a ∨ E (oneV hM hNE) a :=
    (nat_succ_le_iff hM hNE (zeroV_nat hM hNE) (succV_spec hM hNE _) a ha).mp ha_pos
  have h1b : oneV hM hNE = b ∨ E (oneV hM hNE) b :=
    (nat_succ_le_iff hM hNE (zeroV_nat hM hNE) (succV_spec hM hNE _) b hb).mp hb_pos
  obtain ⟨a', ha', ha_eq⟩ := sub_exists hM hNE (oneV_nat hM hNE) a ha h1a
  obtain ⟨b', hb', hb_eq⟩ := sub_exists hM hNE (oneV_nat hM hNE) b hb h1b
  rw [← hb_eq, addV_left_distrib hM hNE ha (oneV_nat hM hNE) b' hb', mulV_one hM hNE ha]
  rcases addV_le_left hM hNE ha (mulV hM hNE a b') (mulV_nat hM hNE ha hb') with heq | hlt
  · exact heq ▸ ha_pos
  · exact nat_lt_trans hM hNE _ (addV_nat hM hNE ha (mulV_nat hM hNE ha hb')) _ _ ha_pos hlt

theorem addV_eq_zero_iff (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : NatObject E a) (hb : NatObject E b) :
    addV hM hNE a b = zeroV hM hNE ↔ a = zeroV hM hNE ∧ b = zeroV hM hNE := by
  constructor
  · intro hab
    have hle1 := addV_le_left hM hNE ha b hb
    rw [hab] at hle1
    have ha0 : a = zeroV hM hNE := by
      rcases hle1 with h | h
      · exact h
      · exact False.elim (zeroV_empty hM hNE a h)
    rw [ha0, zero_addV hM hNE b hb] at hab
    exact ⟨ha0, hab⟩
  · rintro ⟨rfl, rfl⟩
    exact addV_zero hM hNE (zeroV_nat hM hNE)

def DividesV (hM : Model E) (hNE : Nonempty V) (d a : V) : Prop :=
  NatObject E d ∧ NatObject E a ∧ ∃ q, NatObject E q ∧ a = mulV hM hNE q d

theorem dividesV_zero (hM : Model E) (hNE : Nonempty V) {d : V} (hd : NatObject E d) :
    DividesV hM hNE d (zeroV hM hNE) :=
  ⟨hd, zeroV_nat hM hNE, zeroV hM hNE, zeroV_nat hM hNE, (zero_mulV hM hNE d hd).symm⟩

theorem dividesV_refl (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    DividesV hM hNE a a :=
  ⟨ha, ha, oneV hM hNE, oneV_nat hM hNE, (one_mulV hM hNE ha).symm⟩

theorem dividesV_trans (hM : Model E) (hNE : Nonempty V) {a b c : V}
    (h1 : DividesV hM hNE a b) (h2 : DividesV hM hNE b c) : DividesV hM hNE a c := by
  rcases h1 with ⟨ha, hb, q1, hq1, hb_eq⟩
  rcases h2 with ⟨_, hc, q2, hq2, hc_eq⟩
  refine ⟨ha, hc, mulV hM hNE q2 q1, mulV_nat hM hNE hq2 hq1, ?_⟩
  rw [hc_eq, hb_eq, mulV_assoc hM hNE hq2 hq1 a ha]

theorem dividesV_mul_left (hM : Model E) (hNE : Nonempty V) {d a b : V}
    (h : DividesV hM hNE d a) (hb : NatObject E b) : DividesV hM hNE d (mulV hM hNE b a) := by
  rcases h with ⟨hd, ha, q, hq, ha_eq⟩
  refine ⟨hd, mulV_nat hM hNE hb ha, mulV hM hNE b q, mulV_nat hM hNE hb hq, ?_⟩
  rw [ha_eq, mulV_assoc hM hNE hb hq d hd]

theorem dividesV_mul_right (hM : Model E) (hNE : Nonempty V) {d a b : V}
    (h : DividesV hM hNE d a) (hb : NatObject E b) : DividesV hM hNE d (mulV hM hNE a b) := by
  rw [mulV_comm hM hNE h.2.1 b hb]
  exact dividesV_mul_left hM hNE h hb

theorem dividesV_add (hM : Model E) (hNE : Nonempty V) {d a b : V}
    (h1 : DividesV hM hNE d a) (h2 : DividesV hM hNE d b) : DividesV hM hNE d (addV hM hNE a b) := by
  rcases h1 with ⟨hd, ha, q1, hq1, ha_eq⟩
  rcases h2 with ⟨_, hb, q2, hq2, hb_eq⟩
  refine ⟨hd, addV_nat hM hNE ha hb, addV hM hNE q1 q2, addV_nat hM hNE hq1 hq2, ?_⟩
  rw [ha_eq, hb_eq, mulV_right_distrib hM hNE hq1 hq2 hd]

theorem dividesV_of_add_right (hM : Model E) (hNE : Nonempty V) {d a b : V}
    (ha : NatObject E a) (hb : NatObject E b)
    (h1 : DividesV hM hNE d a) (h2 : DividesV hM hNE d (addV hM hNE a b)) :
    DividesV hM hNE d b := by
  rcases h1 with ⟨hd, _, q1, hq1, ha_eq⟩
  rcases h2 with ⟨_, _, q2, hq2, hab_eq⟩
  rcases nat_zero_le hM hNE (zeroV_empty hM hNE) d hd with hd0 | hd_pos
  · rw [← hd0, mulV_zero hM hNE hq2] at hab_eq
    have hb0 := (addV_eq_zero_iff hM hNE ha hb).mp hab_eq |>.2
    rw [hb0]; exact dividesV_zero hM hNE hd
  · rcases nat_trichotomy hM hNE q1 hq1 q2 hq2 with hlt | heq | hgt
    · obtain ⟨q, hq, hq_eq⟩ := sub_exists hM hNE hq1 q2 hq2 (Or.inr hlt)
      refine ⟨hd, hb, q, hq, ?_⟩
      rw [← hq_eq, mulV_right_distrib hM hNE hq1 hq hd, ← ha_eq] at hab_eq
      rw [addV_comm hM hNE ha b hb, addV_comm hM hNE ha (mulV hM hNE q d) (mulV_nat hM hNE hq hd)] at hab_eq
      exact addV_cancel_right hM hNE hb (mulV_nat hM hNE hq hd) a ha hab_eq
    · rw [← heq, ← ha_eq] at hab_eq
      have : addV hM hNE a b = addV hM hNE a (zeroV hM hNE) := by rw [addV_zero hM hNE ha]; exact hab_eq
      rw [addV_comm hM hNE ha b hb, addV_comm hM hNE ha (zeroV hM hNE) (zeroV_nat hM hNE)] at this
      have hb0 := addV_cancel_right hM hNE hb (zeroV_nat hM hNE) a ha this
      rw [hb0]; exact dividesV_zero hM hNE hd
    · obtain ⟨q, hq, hq_eq⟩ := sub_exists hM hNE hq2 q1 hq1 (Or.inr hgt)
      have hq_pos : E (zeroV hM hNE) q := by
        rcases nat_zero_le hM hNE (zeroV_empty hM hNE) q hq with hq0 | hqp
        · rw [← hq0, addV_zero hM hNE hq2] at hq_eq
          exact False.elim (mem_irrefl hM hNE q1 (hq_eq ▸ hgt))
        · exact hqp
      rw [← hq_eq, mulV_right_distrib hM hNE hq2 hq hd] at ha_eq
      rw [ha_eq, addV_assoc hM hNE (mulV_nat hM hNE hq2 hd) (mulV_nat hM hNE hq hd) b hb] at hab_eq
      have : addV hM hNE (mulV hM hNE q2 d) (addV hM hNE (mulV hM hNE q d) b) =
          addV hM hNE (mulV hM hNE q2 d) (zeroV hM hNE) := by rw [addV_zero hM hNE (mulV_nat hM hNE hq2 hd)]; exact hab_eq
      rw [addV_comm hM hNE (mulV_nat hM hNE hq2 hd) _ (addV_nat hM hNE (mulV_nat hM hNE hq hd) hb),
          addV_comm hM hNE (mulV_nat hM hNE hq2 hd) _ (zeroV_nat hM hNE)] at this
      have hsum0 := addV_cancel_right hM hNE (addV_nat hM hNE (mulV_nat hM hNE hq hd) hb) (zeroV_nat hM hNE) _ (mulV_nat hM hNE hq2 hd) this
      have hqd0 := (addV_eq_zero_iff hM hNE (mulV_nat hM hNE hq hd) hb).mp hsum0 |>.1
      have hqd_pos := mulV_pos hM hNE hq hd hq_pos hd_pos
      exact False.elim (zeroV_empty hM hNE (zeroV hM hNE) (hqd0 ▸ hqd_pos))

theorem dividesV_one_eq (hM : Model E) (hNE : Nonempty V) {d : V}
    (h : DividesV hM hNE d (oneV hM hNE)) : d = oneV hM hNE := by
  rcases h with ⟨hd, _, q, hq, h1⟩
  rcases nat_zero_le hM hNE (zeroV_empty hM hNE) d hd with hd0 | hd_pos
  · rw [← hd0, mulV_zero hM hNE hq] at h1
    have hlt := zero_lt_succV hM hNE (zeroV_nat hM hNE)
    rw [oneV] at h1
    rw [h1] at hlt
    exact False.elim (zeroV_empty hM hNE _ hlt)
  · rcases nat_zero_le hM hNE (zeroV_empty hM hNE) q hq with hq0 | hq_pos
    · rw [← hq0, zero_mulV hM hNE d hd] at h1
      have hlt := zero_lt_succV hM hNE (zeroV_nat hM hNE)
      rw [oneV] at h1
      rw [h1] at hlt
      exact False.elim (zeroV_empty hM hNE _ hlt)
    · have h1q := (nat_succ_le_iff hM hNE (zeroV_nat hM hNE) (succV_spec hM hNE _) q hq).mp hq_pos
      obtain ⟨q', hq', hq_eq⟩ := sub_exists hM hNE (oneV_nat hM hNE) q hq h1q
      rw [← hq_eq, mulV_right_distrib hM hNE (oneV_nat hM hNE) hq' hd, one_mulV hM hNE hd] at h1
      have hd_le := addV_le_left hM hNE hd (mulV hM hNE q' d) (mulV_nat hM hNE hq' hd)
      rw [← h1] at hd_le
      have h1d := (nat_succ_le_iff hM hNE (zeroV_nat hM hNE) (succV_spec hM hNE _) d hd).mp hd_pos
      rcases hd_le with hdeq | hdlt
      · exact hdeq
      · rcases h1d with h1eq | h1lt
        · exact h1eq.symm
        · exact False.elim (mem_asymm hM hNE hdlt h1lt)

def CoprimeV (hM : Model E) (hNE : Nonempty V) (a b : V) : Prop :=
  ∀ g, NatObject E g → DividesV hM hNE g a → DividesV hM hNE g b → g = oneV hM hNE

def BezoutV (hM : Model E) (hNE : Nonempty V) (a b : V) : Prop :=
  ∃ u v, NatObject E u ∧ NatObject E v ∧
    (mulV hM hNE u a = succV hM hNE (mulV hM hNE v b) ∨
     mulV hM hNE v b = succV hM hNE (mulV hM hNE u a))

def fOne (x : Nat) : Formula := .ex (.and (fEmpty 0) (fSucc 0 (x + 1)))
def fDivides (d a : Nat) : Formula := .and (fNatObject d) (.and (fNatObject a) (.ex (fMul 0 (d + 1) (a + 1))))
def fCoprime (a b : Nat) : Formula :=
  .all (.imp (fNatObject 0) (.imp (fDivides 0 (a + 1)) (.imp (fDivides 0 (b + 1)) (fOne 0))))
def fBezout (a b : Nat) : Formula :=
  .ex (.ex (.ex (.ex
    (.and (fMul 3 (a + 4) 1) (.and (fMul 2 (b + 4) 0) (.or (fSucc 0 1) (fSucc 1 0)))))))

theorem bound_fOne {x n : Nat} (hx : x < n) : Bound (fOne x) n :=
  ⟨bound_fEmpty (by omega), bound_fSucc (by omega) (by omega)⟩
theorem bound_fDivides {d a n : Nat} (hd : d < n) (ha : a < n) : Bound (fDivides d a) n :=
  ⟨bound_fNatObject hd, bound_fNatObject ha, bound_fMul (by omega) (by omega) (by omega)⟩
theorem bound_fCoprime {a b n : Nat} (ha : a < n) (hb : b < n) : Bound (fCoprime a b) n :=
  ⟨bound_fNatObject (by omega), ⟨bound_fDivides (by omega) (by omega),
    ⟨bound_fDivides (by omega) (by omega), bound_fOne (by omega)⟩⟩⟩
theorem bound_fBezout {a b n : Nat} (ha : a < n) (hb : b < n) : Bound (fBezout a b) n :=
  ⟨bound_fMul (by omega) (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega),
   ⟨bound_fSucc (by omega) (by omega), bound_fSucc (by omega) (by omega)⟩⟩

theorem eval_fOne (hM : Model E) (hNE : Nonempty V) (x : Nat) (s : Nat → V) :
    eval E (fOne x) s ↔ s x = oneV hM hNE := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hz' : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
    have hzx' : Succ E z (s x) := (eval_fSucc 0 (x + 1) _).mp hzx
    rw [hz'] at hzx'
    exact succ_unique hM hNE hzx' (succV_spec hM hNE _)
  · intro hx
    refine ⟨zeroV hM hNE, zeroV_empty hM hNE, (eval_fSucc 0 (x + 1) _).mpr ?_⟩
    show Succ E (zeroV hM hNE) (s x)
    rw [hx]; exact succV_spec hM hNE _

theorem eval_fDivides (hM : Model E) (hNE : Nonempty V) (d a : Nat) (s : Nat → V) :
    eval E (fDivides d a) s ↔ DividesV hM hNE (s d) (s a) := by
  constructor
  · rintro ⟨hd, ha, q, hq⟩
    have hd' := (eval_fNatObject _ _).mp hd
    have ha' := (eval_fNatObject _ _).mp ha
    have hq' := (eval_fMul _ _ _ _).mp hq
    exact ⟨hd', ha', q, hq'.1, (mul_iff_eq hM hNE hq'.1 hd').mp hq'⟩
  · rintro ⟨hd, ha, q, hq, heq⟩
    refine ⟨(eval_fNatObject _ _).mpr hd, (eval_fNatObject _ _).mpr ha, q, (eval_fMul 0 (d + 1) (a + 1) _).mpr ?_⟩
    show Mul E q (s d) (s a)
    rw [heq]; exact mulV_spec hM hNE hq hd

theorem eval_fCoprime (hM : Model E) (hNE : Nonempty V) (a b : Nat) (s : Nat → V) :
    eval E (fCoprime a b) s ↔ CoprimeV hM hNE (s a) (s b) := by
  constructor
  · intro h g hg hga hgb
    exact (eval_fOne hM hNE 0 _).mp (h g ((eval_fNatObject _ _).mpr hg)
      ((eval_fDivides hM hNE 0 (a + 1) _).mpr hga) ((eval_fDivides hM hNE 0 (b + 1) _).mpr hgb))
  · intro h g hg hga hgb
    exact (eval_fOne hM hNE 0 _).mpr (h g ((eval_fNatObject _ _).mp hg)
      ((eval_fDivides hM hNE 0 (a + 1) _).mp hga) ((eval_fDivides hM hNE 0 (b + 1) _).mp hgb))

theorem eval_fBezout (hM : Model E) (hNE : Nonempty V) (a b : Nat) (s : Nat → V)
    (ha : NatObject E (s a)) (hb : NatObject E (s b)) :
    eval E (fBezout a b) s ↔ BezoutV hM hNE (s a) (s b) := by
  constructor
  · rintro ⟨u, v, ua, vb, hua, hvb, hsucc⟩
    have hua' := (eval_fMul _ _ _ _).mp hua
    have hvb' := (eval_fMul _ _ _ _).mp hvb
    have hua_eq : ua = mulV hM hNE u (s a) := (mul_iff_eq hM hNE hua'.1 ha).mp hua'
    have hvb_eq : vb = mulV hM hNE v (s b) := (mul_iff_eq hM hNE hvb'.1 hb).mp hvb'
    refine ⟨u, v, hua'.1, hvb'.1, ?_⟩
    rcases hsucc with h | h
    · left; rw [← hua_eq, ← hvb_eq]; exact succ_unique hM hNE ((eval_fSucc _ _ _).mp h) (succV_spec hM hNE vb)
    · right; rw [← hua_eq, ← hvb_eq]; exact succ_unique hM hNE ((eval_fSucc _ _ _).mp h) (succV_spec hM hNE ua)
  · rintro ⟨u, v, hu, hv, h⟩
    refine ⟨u, v, mulV hM hNE u (s a), mulV hM hNE v (s b),
      (eval_fMul 3 (a + 4) 1 _).mpr (mulV_spec hM hNE hu ha),
      (eval_fMul 2 (b + 4) 0 _).mpr (mulV_spec hM hNE hv hb), ?_⟩
    rcases h with h | h
    · left; apply (eval_fSucc 0 1 _).mpr; show Succ E (mulV hM hNE v (s b)) (mulV hM hNE u (s a))
      rw [h]; exact succV_spec hM hNE _
    · right; apply (eval_fSucc 1 0 _).mpr; show Succ E (mulV hM hNE u (s a)) (mulV hM hNE v (s b))
      rw [h]; exact succV_spec hM hNE _

theorem coprime_implies_bezout (hM : Model E) (hNE : Nonempty V) :
    ∀ a b, NatObject E a → NatObject E b → CoprimeV hM hNE a b → BezoutV hM hNE a b := by
  suffices h : ∀ s, NatObject E s →
      ∀ a b, Add E a b s → CoprimeV hM hNE a b → BezoutV hM hNE a b by
    intro a b ha hb hcop
    exact h (addV hM hNE a b) (addV_nat hM hNE ha hb) a b (addV_spec hM hNE ha hb) hcop
  let body : Formula := .all (.all (.imp (fAdd 1 0 2) (.imp (fCoprime 1 0) (fBezout 1 0))))
  have hB : Bound body 1 :=
    ⟨bound_fAdd (by omega) (by omega) (by omega),
     ⟨bound_fCoprime (by omega) (by omega), bound_fBezout (by omega) (by omega)⟩⟩
  have hInd := omega_strong_induction hM hNE 0 body hB (fun _ => Classical.choice hNE) (by
    intro s hs ih a b hab hcopF
    have hab' : Add E a b s := (eval_fAdd 1 0 2 _).mp hab
    have ha : NatObject E a := hab'.1
    have hb : NatObject E b := hab'.2.1
    have hs_eq : s = addV hM hNE a b := (add_iff_eq hM hNE ha hb).mp hab'
    have hcop : CoprimeV hM hNE a b := (eval_fCoprime hM hNE 1 0 _).mp hcopF
    apply (eval_fBezout hM hNE 1 0 _ ha hb).mpr
    show BezoutV hM hNE a b
    rcases nat_zero_le hM hNE (zeroV_empty hM hNE) b hb with hb0 | hb_pos
    · have ha1 : a = oneV hM hNE :=
        hcop a ha (dividesV_refl hM hNE ha) (hb0 ▸ dividesV_zero hM hNE ha)
      refine ⟨oneV hM hNE, zeroV hM hNE, oneV_nat hM hNE, zeroV_nat hM hNE, Or.inl ?_⟩
      rw [ha1, ← hb0, mulV_one hM hNE (oneV_nat hM hNE), mulV_zero hM hNE (zeroV_nat hM hNE)]
    · rcases nat_zero_le hM hNE (zeroV_empty hM hNE) a ha with ha0 | ha_pos
      · have hb1 : b = oneV hM hNE :=
          hcop b hb (ha0 ▸ dividesV_zero hM hNE hb) (dividesV_refl hM hNE hb)
        refine ⟨zeroV hM hNE, oneV hM hNE, zeroV_nat hM hNE, oneV_nat hM hNE, Or.inr ?_⟩
        rw [hb1, ← ha0, mulV_one hM hNE (oneV_nat hM hNE), mulV_zero hM hNE (zeroV_nat hM hNE)]
      · rcases nat_trichotomy hM hNE a ha b hb with hab_lt | hab_eq | hba_lt
        · obtain ⟨b', hb', hb_eq⟩ := sub_exists hM hNE ha b hb (Or.inr hab_lt)
          have hb_lt_s : E b s := by
            rw [hs_eq, addV_comm hM hNE ha b hb]
            have := addV_lt_addV_left hM hNE hb (zeroV_nat hM hNE) ha ha_pos
            rwa [addV_zero hM hNE hb] at this
          have hcop' : CoprimeV hM hNE a b' := by
            intro g hg hga hgb'
            exact hcop g hg hga (hb_eq ▸ dividesV_add hM hNE hga hgb')
          have ih' := ih b hb_lt_s a b' ((eval_fAdd 1 0 2 _).mpr (hb_eq ▸ addV_spec hM hNE ha hb'))
            ((eval_fCoprime hM hNE 1 0 _).mpr hcop')
          obtain ⟨u, v, hu, hv, huv⟩ := (eval_fBezout hM hNE 1 0 _ ha hb').mp ih'
          dsimp only [pushValue] at huv
          refine ⟨addV hM hNE u v, v, addV_nat hM hNE hu hv, hv, ?_⟩
          rw [mulV_right_distrib hM hNE hu hv ha, ← hb_eq, addV_left_distrib hM hNE hv ha b' hb']
          rcases huv with h1 | h2
          · left
            rw [h1, addV_comm hM hNE (succV_nat hM hNE (mulV_nat hM hNE hv hb')) (mulV hM hNE v a) (mulV_nat hM hNE hv ha),
                addV_succ hM hNE (mulV_nat hM hNE hv ha) (mulV_nat hM hNE hv hb')]
          · right
            rw [h2, addV_comm hM hNE (mulV_nat hM hNE hv ha) (succV hM hNE (mulV hM hNE u a)) (succV_nat hM hNE (mulV_nat hM hNE hu ha)),
                succ_addV hM hNE (mulV_nat hM hNE hu ha) (mulV hM hNE v a) (mulV_nat hM hNE hv ha)]
        · have ha1 : a = oneV hM hNE :=
            hcop a ha (dividesV_refl hM hNE ha) (hab_eq ▸ dividesV_refl hM hNE ha)
          refine ⟨oneV hM hNE, zeroV hM hNE, oneV_nat hM hNE, zeroV_nat hM hNE, Or.inl ?_⟩
          rw [ha1, mulV_one hM hNE (oneV_nat hM hNE), zero_mulV hM hNE b hb]
        · obtain ⟨a', ha', ha_eq⟩ := sub_exists hM hNE hb a ha (Or.inr hba_lt)
          have ha_lt_s : E a s := by
            rw [hs_eq]
            have := addV_lt_addV_left hM hNE ha (zeroV_nat hM hNE) hb hb_pos
            rwa [addV_zero hM hNE ha] at this
          have hcop' : CoprimeV hM hNE a' b := by
            intro g hg hga' hgb
            exact hcop g hg (ha_eq ▸ dividesV_add hM hNE hgb hga') hgb
          have ih' := ih a ha_lt_s a' b ((eval_fAdd 1 0 2 _).mpr (by
            show Add E a' b a
            rw [← ha_eq, addV_comm hM hNE hb a' ha']
            exact addV_spec hM hNE ha' hb)) ((eval_fCoprime hM hNE 1 0 _).mpr hcop')
          obtain ⟨u, v, hu, hv, huv⟩ := (eval_fBezout hM hNE 1 0 _ ha' hb).mp ih'
          dsimp only [pushValue] at huv
          refine ⟨u, addV hM hNE u v, hu, addV_nat hM hNE hu hv, ?_⟩
          rw [← ha_eq, addV_left_distrib hM hNE hu hb a' ha', mulV_right_distrib hM hNE hu hv hb]
          rcases huv with h1 | h2
          · left
            rw [h1, addV_succ hM hNE (mulV_nat hM hNE hu hb) (mulV_nat hM hNE hv hb)]
          · right
            rw [h2, addV_succ hM hNE (mulV_nat hM hNE hu hb) (mulV_nat hM hNE hu ha')])
  intro s hs a b hab hcop
  have h1 := hInd s hs a b ((eval_fAdd 1 0 2 _).mpr hab) ((eval_fCoprime hM hNE 1 0 _).mpr hcop)
  exact (eval_fBezout hM hNE 1 0 _ hab.1 hab.2.1).mp h1

theorem coprimeV_mul_left (hM : Model E) (hNE : Nonempty V) {a b m : V}
    (ha : NatObject E a) (hb : NatObject E b) (hm : NatObject E m)
    (h1 : CoprimeV hM hNE a m) (h2 : CoprimeV hM hNE b m) :
    CoprimeV hM hNE (mulV hM hNE a b) m := by
  obtain ⟨u, v, hu, hv, huv⟩ := coprime_implies_bezout hM hNE a m ha hm h1
  intro g hg hgab hgm
  have hgb : DividesV hM hNE g b := by
    have h1' : DividesV hM hNE g (mulV hM hNE (mulV hM hNE u a) b) := by
      rw [mulV_assoc hM hNE hu ha b hb]
      exact dividesV_mul_left hM hNE hgab hu
    have h2' : DividesV hM hNE g (mulV hM hNE (mulV hM hNE v m) b) := by
      rw [mulV_assoc hM hNE hv hm b hb, mulV_comm hM hNE hm b hb, ← mulV_assoc hM hNE hv hb m hm]
      exact dividesV_mul_left hM hNE hgm (mulV_nat hM hNE hv hb)
    rcases huv with heq | heq
    · rw [heq, succ_mulV hM hNE (mulV_nat hM hNE hv hm) b hb] at h1'
      exact dividesV_of_add_right hM hNE (mulV_nat hM hNE (mulV_nat hM hNE hv hm) hb) hb h2' h1'
    · rw [heq, succ_mulV hM hNE (mulV_nat hM hNE hu ha) b hb] at h2'
      exact dividesV_of_add_right hM hNE (mulV_nat hM hNE (mulV_nat hM hNE hu ha) hb) hb h1' h2'
  exact h2 g hg hgb hgm

theorem le_of_mul_le_mul_right (hM : Model E) (hNE : Nonempty V) {a b m : V}
    (ha : NatObject E a) (hb : NatObject E b) (hm : NatObject E m)
    (hm_pos : E (zeroV hM hNE) m)
    (hle : mulV hM hNE a m = mulV hM hNE b m ∨ E (mulV hM hNE a m) (mulV hM hNE b m)) :
    a = b ∨ E a b := by
  rcases nat_trichotomy hM hNE a ha b hb with hlt | heq | hgt
  · exact Or.inr hlt
  · exact Or.inl heq
  · exfalso
    obtain ⟨d, hd, hd_eq⟩ := sub_exists hM hNE hb a ha (Or.inr hgt)
    have hd_pos : E (zeroV hM hNE) d := by
      rcases nat_zero_le hM hNE (zeroV_empty hM hNE) d hd with hd0 | hdp
      · rw [← hd0, addV_zero hM hNE hb] at hd_eq
        exact False.elim (mem_irrefl hM hNE b (hd_eq ▸ hgt))
      · exact hdp
    have hdm_pos := mulV_pos hM hNE hd hm hd_pos hm_pos
    have hgt' : E (mulV hM hNE b m) (mulV hM hNE a m) := by
      rw [← hd_eq, mulV_right_distrib hM hNE hb hd hm]
      have := addV_lt_addV_left hM hNE (mulV_nat hM hNE hb hm) (zeroV_nat hM hNE)
        (mulV_nat hM hNE hd hm) hdm_pos
      rwa [addV_zero hM hNE (mulV_nat hM hNE hb hm)] at this
    rcases hle with heq' | hlt'
    · exact mem_irrefl hM hNE _ (heq' ▸ hgt')
    · exact mem_asymm hM hNE hlt' hgt'

theorem crt2_one (hM : Model E) (hNE : Nonempty V) {m₁ m₂ r₁ r₂ u v : V}
    (hm1 : NatObject E m₁) (hm2 : NatObject E m₂) (hr1 : NatObject E r₁) (hr2 : NatObject E r₂)
    (hu : NatObject E u) (hv : NatObject E v)
    (hm1_pos : E (zeroV hM hNE) m₁) (hm2_pos : E (zeroV hM hNE) m₂)
    (hr1_lt : E r₁ m₁) (hr2_lt : E r₂ m₂)
    (hbez : mulV hM hNE u m₁ = succV hM hNE (mulV hM hNE v m₂)) :
    ∃ c, NatObject E c ∧ E c (mulV hM hNE m₁ m₂) ∧
      (∃ q₁, NatObject E q₁ ∧ c = addV hM hNE (mulV hM hNE q₁ m₁) r₁) ∧
      (∃ q₂, NatObject E q₂ ∧ c = addV hM hNE (mulV hM hNE q₂ m₂) r₂) := by
  obtain ⟨q, v0, hq, hv0, hv_eq, hv0_lt⟩ := div_mod_exists hM hNE hm1 hm1_pos v hv
  have h1m1 : DividesV hM hNE m₁ (succV hM hNE (mulV hM hNE v0 m₂)) := by
    have htot : DividesV hM hNE m₁ (addV hM hNE (mulV hM hNE (mulV hM hNE q m₂) m₁)
        (succV hM hNE (mulV hM hNE v0 m₂))) := by
      have hEq : addV hM hNE (mulV hM hNE (mulV hM hNE q m₂) m₁) (succV hM hNE (mulV hM hNE v0 m₂)) =
          mulV hM hNE u m₁ := by
        rw [hbez, addV_succ hM hNE (mulV_nat hM hNE (mulV_nat hM hNE hq hm2) hm1) (mulV_nat hM hNE hv0 hm2),
            hv_eq, mulV_right_distrib hM hNE (mulV_nat hM hNE hq hm1) hv0 hm2,
            mulV_assoc hM hNE hq hm1 m₂ hm2, mulV_comm hM hNE hm1 m₂ hm2, ← mulV_assoc hM hNE hq hm2 m₁ hm1]
      rw [hEq]
      exact ⟨hm1, mulV_nat hM hNE hu hm1, u, hu, rfl⟩
    exact dividesV_of_add_right hM hNE (mulV_nat hM hNE (mulV_nat hM hNE hq hm2) hm1)
      (succV_nat hM hNE (mulV_nat hM hNE hv0 hm2))
      ⟨hm1, mulV_nat hM hNE (mulV_nat hM hNE hq hm2) hm1, mulV hM hNE q m₂, mulV_nat hM hNE hq hm2, rfl⟩ htot
  obtain ⟨_, _, u', hu', hu'_eq⟩ := h1m1
  obtain ⟨d, hd, hm1_eq⟩ := sub_exists hM hNE hv0 m₁ hm1 (Or.inr hv0_lt)
  have hd_pos : E (zeroV hM hNE) d := by
    rcases nat_zero_le hM hNE (zeroV_empty hM hNE) d hd with hd0 | hdp
    · rw [← hd0, addV_zero hM hNE hv0] at hm1_eq
      exact False.elim (mem_irrefl hM hNE v0 (hm1_eq ▸ hv0_lt))
    · exact hdp
  have h1_le_dm2 : oneV hM hNE = mulV hM hNE d m₂ ∨ E (oneV hM hNE) (mulV hM hNE d m₂) :=
    (nat_succ_le_iff hM hNE (zeroV_nat hM hNE) (succV_spec hM hNE _) _ (mulV_nat hM hNE hd hm2)).mp
      (mulV_pos hM hNE hd hm2 hd_pos hm2_pos)
  have hu'm1_le : mulV hM hNE u' m₁ = mulV hM hNE m₂ m₁ ∨ E (mulV hM hNE u' m₁) (mulV hM hNE m₂ m₁) := by
    rw [← hu'_eq, mulV_comm hM hNE hm2 m₁ hm1, ← hm1_eq, mulV_right_distrib hM hNE hv0 hd hm2]
    have hsucc_eq : succV hM hNE (mulV hM hNE v0 m₂) = addV hM hNE (mulV hM hNE v0 m₂) (oneV hM hNE) := by
      rw [oneV, addV_succ hM hNE (mulV_nat hM hNE hv0 hm2) (zeroV_nat hM hNE),
          addV_zero hM hNE (mulV_nat hM hNE hv0 hm2)]
    rw [hsucc_eq]
    rcases h1_le_dm2 with heq | hlt
    · exact Or.inl (heq ▸ rfl)
    · exact Or.inr (addV_lt_addV_left hM hNE (mulV_nat hM hNE hv0 hm2) (oneV_nat hM hNE) (mulV_nat hM hNE hd hm2) hlt)
  have hu'_le_m2 : u' = m₂ ∨ E u' m₂ :=
    le_of_mul_le_mul_right hM hNE hu' hm2 hm1 hm1_pos hu'm1_le
  obtain ⟨w, hw, hm2_eq⟩ := sub_exists hM hNE hu' m₂ hm2 hu'_le_m2
  -- e₁ := d * m₂ = w * m₁ + 1
  have he1_eq : mulV hM hNE d m₂ = succV hM hNE (mulV hM hNE w m₁) := by
    have hsum : addV hM hNE (mulV hM hNE d m₂) (mulV hM hNE v0 m₂) =
        addV hM hNE (succV hM hNE (mulV hM hNE w m₁)) (mulV hM hNE v0 m₂) := by
      calc addV hM hNE (mulV hM hNE d m₂) (mulV hM hNE v0 m₂)
          = mulV hM hNE (addV hM hNE d v0) m₂ :=
              (mulV_right_distrib hM hNE hd hv0 hm2).symm
        _ = mulV hM hNE m₁ m₂ := by rw [addV_comm hM hNE hd v0 hv0, hm1_eq]
        _ = mulV hM hNE m₂ m₁ := mulV_comm hM hNE hm1 m₂ hm2
        _ = mulV hM hNE (addV hM hNE u' w) m₁ := by rw [hm2_eq]
        _ = addV hM hNE (mulV hM hNE u' m₁) (mulV hM hNE w m₁) :=
              mulV_right_distrib hM hNE hu' hw hm1
        _ = addV hM hNE (succV hM hNE (mulV hM hNE v0 m₂)) (mulV hM hNE w m₁) := by rw [← hu'_eq]
        _ = addV hM hNE (mulV hM hNE w m₁) (succV hM hNE (mulV hM hNE v0 m₂)) :=
              addV_comm hM hNE (succV_nat hM hNE (mulV_nat hM hNE hv0 hm2)) (mulV hM hNE w m₁) (mulV_nat hM hNE hw hm1)
        _ = succV hM hNE (addV hM hNE (mulV hM hNE w m₁) (mulV hM hNE v0 m₂)) :=
              addV_succ hM hNE (mulV_nat hM hNE hw hm1) (mulV_nat hM hNE hv0 hm2)
        _ = addV hM hNE (succV hM hNE (mulV hM hNE w m₁)) (mulV hM hNE v0 m₂) :=
              (succ_addV hM hNE (mulV_nat hM hNE hw hm1) (mulV hM hNE v0 m₂) (mulV_nat hM hNE hv0 hm2)).symm
    exact addV_cancel_right hM hNE (mulV_nat hM hNE hd hm2) (succV_nat hM hNE (mulV_nat hM hNE hw hm1))
      (mulV hM hNE v0 m₂) (mulV_nat hM hNE hv0 hm2) hsum
  let e1 := mulV hM hNE d m₂
  let e2 := mulV hM hNE u m₁
  have he1_nat : NatObject E e1 := mulV_nat hM hNE hd hm2
  have he2_nat : NatObject E e2 := mulV_nat hM hNE hu hm1
  let X := addV hM hNE (mulV hM hNE r₁ e1) (mulV hM hNE r₂ e2)
  have hX_nat : NatObject E X := addV_nat hM hNE (mulV_nat hM hNE hr1 he1_nat) (mulV_nat hM hNE hr2 he2_nat)
  obtain ⟨Q, c, hQ, hc, hX_eq, hc_lt⟩ := div_mod_exists hM hNE (mulV_nat hM hNE hm1 hm2)
    (mulV_pos hM hNE hm1 hm2 hm1_pos hm2_pos) X hX_nat
  refine ⟨c, hc, hc_lt, ?_, ?_⟩
  · -- c ≡ r₁ (mod m₁)
    obtain ⟨q1, r1', hq1, hr1', hc_eq1, hr1'_lt⟩ := div_mod_exists hM hNE hm1 hm1_pos c hc
    have hX1 : X = addV hM hNE (mulV hM hNE (addV hM hNE (mulV hM hNE Q m₂) q1) m₁) r1' := by
      rw [hX_eq, hc_eq1, ← addV_assoc hM hNE (mulV_nat hM hNE hQ (mulV_nat hM hNE hm1 hm2)) (mulV_nat hM hNE hq1 hm1) r1' hr1',
          mulV_right_distrib hM hNE (mulV_nat hM hNE hQ hm2) hq1 hm1,
          mulV_assoc hM hNE hQ hm2 m₁ hm1, mulV_comm hM hNE hm2 m₁ hm1]
    have hX2 : X = addV hM hNE (mulV hM hNE (addV hM hNE (mulV hM hNE r₁ w) (mulV hM hNE r₂ u)) m₁) r₁ := by
      show addV hM hNE (mulV hM hNE r₁ e1) (mulV hM hNE r₂ e2) = _
      have he1' : mulV hM hNE r₁ e1 = addV hM hNE (mulV hM hNE (mulV hM hNE r₁ w) m₁) r₁ := by
        show mulV hM hNE r₁ (mulV hM hNE d m₂) = _
        rw [he1_eq, mulV_succ hM hNE hr1 (mulV_nat hM hNE hw hm1), mulV_assoc hM hNE hr1 hw m₁ hm1]
      have he2' : mulV hM hNE r₂ e2 = mulV hM hNE (mulV hM hNE r₂ u) m₁ := by
        show mulV hM hNE r₂ (mulV hM hNE u m₁) = _
        rw [mulV_assoc hM hNE hr2 hu m₁ hm1]
      rw [he1', he2', mulV_right_distrib hM hNE (mulV_nat hM hNE hr1 hw) (mulV_nat hM hNE hr2 hu) hm1,
          addV_assoc hM hNE (mulV_nat hM hNE (mulV_nat hM hNE hr1 hw) hm1) hr1 (mulV hM hNE (mulV hM hNE r₂ u) m₁) (mulV_nat hM hNE (mulV_nat hM hNE hr2 hu) hm1),
          addV_comm hM hNE hr1 _ (mulV_nat hM hNE (mulV_nat hM hNE hr2 hu) hm1),
          ← addV_assoc hM hNE (mulV_nat hM hNE (mulV_nat hM hNE hr1 hw) hm1) (mulV_nat hM hNE (mulV_nat hM hNE hr2 hu) hm1) r₁ hr1]
    have ⟨_, hrr⟩ := div_mod_unique hM hNE hm1
      (addV_nat hM hNE (mulV_nat hM hNE hQ hm2) hq1) hr1'
      (addV_nat hM hNE (mulV_nat hM hNE hr1 hw) (mulV_nat hM hNE hr2 hu)) hr1
      hr1'_lt hr1_lt (hX1.symm.trans hX2)
    exact ⟨q1, hq1, hrr ▸ hc_eq1⟩
  · -- c ≡ r₂ (mod m₂)
    obtain ⟨q2, r2', hq2, hr2', hc_eq2, hr2'_lt⟩ := div_mod_exists hM hNE hm2 hm2_pos c hc
    have hX1 : X = addV hM hNE (mulV hM hNE (addV hM hNE (mulV hM hNE Q m₁) q2) m₂) r2' := by
      rw [hX_eq, hc_eq2, ← addV_assoc hM hNE (mulV_nat hM hNE hQ (mulV_nat hM hNE hm1 hm2)) (mulV_nat hM hNE hq2 hm2) r2' hr2',
          mulV_right_distrib hM hNE (mulV_nat hM hNE hQ hm1) hq2 hm2,
          mulV_assoc hM hNE hQ hm1 m₂ hm2]
    have hX2 : X = addV hM hNE (mulV hM hNE (addV hM hNE (mulV hM hNE r₁ d) (mulV hM hNE r₂ v)) m₂) r₂ := by
      show addV hM hNE (mulV hM hNE r₁ e1) (mulV hM hNE r₂ e2) = _
      have he1' : mulV hM hNE r₁ e1 = mulV hM hNE (mulV hM hNE r₁ d) m₂ := by
        show mulV hM hNE r₁ (mulV hM hNE d m₂) = _
        rw [mulV_assoc hM hNE hr1 hd m₂ hm2]
      have he2' : mulV hM hNE r₂ e2 = addV hM hNE (mulV hM hNE (mulV hM hNE r₂ v) m₂) r₂ := by
        show mulV hM hNE r₂ (mulV hM hNE u m₁) = _
        rw [hbez, mulV_succ hM hNE hr2 (mulV_nat hM hNE hv hm2), mulV_assoc hM hNE hr2 hv m₂ hm2]
      rw [he1', he2', mulV_right_distrib hM hNE (mulV_nat hM hNE hr1 hd) (mulV_nat hM hNE hr2 hv) hm2,
          ← addV_assoc hM hNE (mulV_nat hM hNE (mulV_nat hM hNE hr1 hd) hm2) (mulV_nat hM hNE (mulV_nat hM hNE hr2 hv) hm2) r₂ hr2]
    have ⟨_, hrr⟩ := div_mod_unique hM hNE hm2
      (addV_nat hM hNE (mulV_nat hM hNE hQ hm1) hq2) hr2'
      (addV_nat hM hNE (mulV_nat hM hNE hr1 hd) (mulV_nat hM hNE hr2 hv)) hr2
      hr2'_lt hr2_lt (hX1.symm.trans hX2)
    exact ⟨q2, hq2, hrr ▸ hc_eq2⟩

theorem crt2 (hM : Model E) (hNE : Nonempty V) {m₁ m₂ r₁ r₂ : V}
    (hm1 : NatObject E m₁) (hm2 : NatObject E m₂) (hr1 : NatObject E r₁) (hr2 : NatObject E r₂)
    (hm1_pos : E (zeroV hM hNE) m₁) (hm2_pos : E (zeroV hM hNE) m₂)
    (hr1_lt : E r₁ m₁) (hr2_lt : E r₂ m₂)
    (hcop : CoprimeV hM hNE m₁ m₂) :
    ∃ c, NatObject E c ∧ E c (mulV hM hNE m₁ m₂) ∧
      (∃ q₁, NatObject E q₁ ∧ c = addV hM hNE (mulV hM hNE q₁ m₁) r₁) ∧
      (∃ q₂, NatObject E q₂ ∧ c = addV hM hNE (mulV hM hNE q₂ m₂) r₂) := by
  obtain ⟨u, v, hu, hv, huv⟩ := coprime_implies_bezout hM hNE m₁ m₂ hm1 hm2 hcop
  rcases huv with h1 | h2
  · exact crt2_one hM hNE hm1 hm2 hr1 hr2 hu hv hm1_pos hm2_pos hr1_lt hr2_lt h1
  · obtain ⟨c, hc, hc_lt, hq2, hq1⟩ := crt2_one hM hNE hm2 hm1 hr2 hr1 hv hu hm2_pos hm1_pos hr2_lt hr1_lt h2
    rw [mulV_comm hM hNE hm2 m₁ hm1] at hc_lt
    exact ⟨c, hc, hc_lt, hq1, hq2⟩

theorem exists_common_multiple (hM : Model E) (hNE : Nonempty V) :
    ∀ M, NatObject E M → ∃ d, NatObject E d ∧ E (zeroV hM hNE) d ∧
      ∀ k, NatObject E k → E (zeroV hM hNE) k → (k = M ∨ E k M) → DividesV hM hNE k d := by
  let body : Formula :=
    .ex (.and (fNatObject 0) (.and (.ex (.and (fEmpty 0) (.mem 0 1)))
      (.all (.imp (fNatObject 0) (.imp (.ex (.and (fEmpty 0) (.mem 0 1)))
        (.imp (.or (.eq 0 2) (.mem 0 2)) (fDivides 0 1)))))))
  have hB : Bound body 1 :=
    ⟨bound_fNatObject (by omega), ⟨⟨bound_fEmpty (by omega), ⟨by omega, by omega⟩⟩,
     ⟨bound_fNatObject (by omega), ⟨⟨bound_fEmpty (by omega), ⟨by omega, by omega⟩⟩,
      ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, bound_fDivides (by omega) (by omega)⟩⟩⟩⟩⟩
  have hInd := omega_induction hM hNE 0 body hB (fun _ => Classical.choice hNE)
    (fun z hz => by
      have hz' : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst hz'
      refine ⟨oneV hM hNE, (eval_fNatObject _ _).mpr (oneV_nat hM hNE),
        ⟨zeroV hM hNE, zeroV_empty hM hNE, zero_lt_succV hM hNE (zeroV_nat hM hNE)⟩,
        fun k _ ⟨z', hz', hz'k⟩ hkle => ?_⟩
      have : z' = zeroV hM hNE := empty_unique hM hNE hz' (zeroV_empty hM hNE)
      subst this
      dsimp only [eval, pushValue] at hkle
      rcases hkle with rfl | hlt
      · exact False.elim (zeroV_empty hM hNE _ hz'k)
      · exact False.elim (zeroV_empty hM hNE _ hlt))
    (fun M M' hM_nat hMM' ih => by
      have hM' : M' = succV hM hNE M := succ_unique hM hNE hMM' (succV_spec hM hNE M)
      subst hM'
      rcases ih with ⟨d, hdF, ⟨z0, hz0, hz0d⟩, hdiv⟩
      have hd : NatObject E d := (eval_fNatObject _ _).mp hdF
      have : z0 = zeroV hM hNE := empty_unique hM hNE hz0 (zeroV_empty hM hNE)
      subst this
      let d' := mulV hM hNE d (succV hM hNE M)
      have hd' : NatObject E d' := mulV_nat hM hNE hd (succV_nat hM hNE hM_nat)
      refine ⟨d', (eval_fNatObject _ _).mpr hd',
        ⟨zeroV hM hNE, zeroV_empty hM hNE, mulV_pos hM hNE hd (succV_nat hM hNE hM_nat) hz0d (zero_lt_succV hM hNE hM_nat)⟩,
        fun k hkF ⟨z1, hz1, hz1k⟩ hkle => ?_⟩
      have hk : NatObject E k := (eval_fNatObject _ _).mp hkF
      have : z1 = zeroV hM hNE := empty_unique hM hNE hz1 (zeroV_empty hM hNE)
      subst this
      apply (eval_fDivides hM hNE 0 1 _).mpr
      show DividesV hM hNE k d'
      dsimp only [eval, pushValue] at hkle
      rcases hkle with hkeq | hklt
      · rw [hkeq]
        exact dividesV_mul_left hM hNE (dividesV_refl hM hNE (succV_nat hM hNE hM_nat)) hd
      · rcases (succV_spec hM hNE M k).mp hklt with hkM | hkM
        · have hkdiv : DividesV hM hNE k d :=
            (eval_fDivides hM hNE 0 1 _).mp (hdiv k hkF ⟨zeroV hM hNE, zeroV_empty hM hNE, hz1k⟩ (Or.inr hkM))
          exact dividesV_mul_right hM hNE hkdiv (succV_nat hM hNE hM_nat)
        · have hkdiv : DividesV hM hNE k d :=
            (eval_fDivides hM hNE 0 1 _).mp (hdiv k hkF ⟨zeroV hM hNE, zeroV_empty hM hNE, hz1k⟩ (Or.inl hkM))
          exact dividesV_mul_right hM hNE hkdiv (succV_nat hM hNE hM_nat))
  intro M hMn
  rcases hInd M hMn with ⟨d, hdF, ⟨z0, hz0, hz0d⟩, hdiv⟩
  have hd : NatObject E d := (eval_fNatObject _ _).mp hdF
  have : z0 = zeroV hM hNE := empty_unique hM hNE hz0 (zeroV_empty hM hNE)
  subst this
  refine ⟨d, hd, hz0d, fun k hk hk_pos hkle => ?_⟩
  exact (eval_fDivides hM hNE 0 1 _).mp
    (hdiv k ((eval_fNatObject _ _).mpr hk) ⟨zeroV hM hNE, zeroV_empty hM hNE, hk_pos⟩ hkle)

theorem beta_moduli_coprime (hM : Model E) (hNE : Nonempty V) {M d i j : V}
    (hMn : NatObject E M) (hd : NatObject E d)
    (hd_mult : ∀ k, NatObject E k → E (zeroV hM hNE) k → (k = M ∨ E k M) → DividesV hM hNE k d)
    (hi : NatObject E i) (hj : NatObject E j) (hij : E i j) (hjM : j = M ∨ E j M) :
    CoprimeV hM hNE (succV hM hNE (mulV hM hNE (succV hM hNE i) d))
      (succV hM hNE (mulV hM hNE (succV hM hNE j) d)) := by
  let mi := succV hM hNE (mulV hM hNE (succV hM hNE i) d)
  let mj := succV hM hNE (mulV hM hNE (succV hM hNE j) d)
  have hsi : NatObject E (succV hM hNE i) := succV_nat hM hNE hi
  have hsj : NatObject E (succV hM hNE j) := succV_nat hM hNE hj
  have hmi : NatObject E mi := succV_nat hM hNE (mulV_nat hM hNE hsi hd)
  have hmj : NatObject E mj := succV_nat hM hNE (mulV_nat hM hNE hsj hd)
  intro g hg hgmi hgmj
  obtain ⟨diff, hdiff, hdiff_eq⟩ := sub_exists hM hNE hi j hj (Or.inr hij)
  have hdiff_pos : E (zeroV hM hNE) diff := by
    rcases nat_zero_le hM hNE (zeroV_empty hM hNE) diff hdiff with h0 | hp
    · rw [← h0, addV_zero hM hNE hi] at hdiff_eq
      exact False.elim (mem_irrefl hM hNE i (hdiff_eq ▸ hij))
    · exact hp
  have hdiff_le_M : diff = M ∨ E diff M := by
    have hdiff_le_j : diff = j ∨ E diff j := by
      have := addV_le_left hM hNE hdiff i hi
      rwa [addV_comm hM hNE hdiff i hi, hdiff_eq] at this
    rcases hdiff_le_j with h1 | h1
    · rw [h1]; exact hjM
    · rcases hjM with h2 | h2
      · rw [← h2]; exact Or.inr h1
      · exact Or.inr (nat_lt_trans hM hNE M hMn diff j h1 h2)
  have hdiff_div_d : DividesV hM hNE diff d := hd_mult diff hdiff hdiff_pos hdiff_le_M
  -- mj = mi + diff * d
  have hmj_eq : mj = addV hM hNE mi (mulV hM hNE diff d) := by
    show succV hM hNE (mulV hM hNE (succV hM hNE j) d) =
      addV hM hNE (succV hM hNE (mulV hM hNE (succV hM hNE i) d)) (mulV hM hNE diff d)
    rw [succ_addV hM hNE (mulV_nat hM hNE hsi hd) _ (mulV_nat hM hNE hdiff hd),
        ← mulV_right_distrib hM hNE hsi hdiff hd,
        succ_addV hM hNE hi diff hdiff, hdiff_eq]
  have hg_diffd : DividesV hM hNE g (mulV hM hNE diff d) :=
    dividesV_of_add_right hM hNE hmi (mulV_nat hM hNE hdiff hd) hgmi (hmj_eq ▸ hgmj)
  have hg_dd : DividesV hM hNE g (mulV hM hNE d d) := by
    rcases hdiff_div_d with ⟨_, _, q, hq, hd_eq⟩
    have hdiffd_div_dd : DividesV hM hNE (mulV hM hNE diff d) (mulV hM hNE d d) :=
      ⟨mulV_nat hM hNE hdiff hd, mulV_nat hM hNE hd hd, q, hq, by
        rw [← mulV_assoc hM hNE hq hdiff d hd, ← hd_eq]⟩
    exact dividesV_trans hM hNE hg_diffd hdiffd_div_dd
  -- Let kd = (i + 1) * d. g ∣ 1 + kd and g ∣ d*d → g ∣ kd * (1 + kd) = kd + kd^2 → g ∣ kd → g ∣ 1
  let kd := mulV hM hNE (succV hM hNE i) d
  have hkd : NatObject E kd := mulV_nat hM hNE hsi hd
  have hg_kdsq : DividesV hM hNE g (mulV hM hNE kd kd) := by
    have hEq : mulV hM hNE kd kd = mulV hM hNE (mulV hM hNE (succV hM hNE i) (succV hM hNE i)) (mulV hM hNE d d) := by
      show mulV hM hNE (mulV hM hNE (succV hM hNE i) d) (mulV hM hNE (succV hM hNE i) d) = _
      rw [mulV_assoc hM hNE hsi hd _ hkd, ← mulV_assoc hM hNE hd hsi d hd,
          mulV_comm hM hNE hd (succV hM hNE i) hsi, mulV_assoc hM hNE hsi hd d hd,
          ← mulV_assoc hM hNE hsi hsi (mulV hM hNE d d) (mulV_nat hM hNE hd hd)]
    rw [hEq]
    exact dividesV_mul_left hM hNE hg_dd (mulV_nat hM hNE hsi hsi)
  have hg_kd_mi : DividesV hM hNE g (addV hM hNE (mulV hM hNE kd kd) kd) := by
    have hEq : addV hM hNE (mulV hM hNE kd kd) kd = mulV hM hNE kd mi := by
      show _ = mulV hM hNE kd (succV hM hNE kd)
      rw [mulV_succ hM hNE hkd hkd]
    rw [hEq]
    exact dividesV_mul_left hM hNE hgmi hkd
  have hg_kd : DividesV hM hNE g kd :=
    dividesV_of_add_right hM hNE (mulV_nat hM hNE hkd hkd) hkd hg_kdsq hg_kd_mi
  have hmi_add : mi = addV hM hNE kd (oneV hM hNE) := by
    show succV hM hNE kd = addV hM hNE kd (succV hM hNE (zeroV hM hNE))
    rw [addV_succ hM hNE hkd (zeroV_nat hM hNE), addV_zero hM hNE hkd]
  have hg_one : DividesV hM hNE g (oneV hM hNE) :=
    dividesV_of_add_right hM hNE hkd (oneV_nat hM hNE) hg_kd (hmi_add ▸ hgmi)
  exact dividesV_one_eq hM hNE hg_one

def BetaV (hM : Model E) (hNE : Nonempty V) (c d i x : V) : Prop :=
  NatObject E c ∧ NatObject E d ∧ NatObject E i ∧ NatObject E x ∧
  ∃ q, NatObject E q ∧
    c = addV hM hNE (mulV hM hNE q (succV hM hNE (mulV hM hNE (succV hM hNE i) d))) x ∧
    E x (succV hM hNE (mulV hM hNE (succV hM hNE i) d))

def fBeta (c d i x : Nat) : Formula :=
  .and (fNatObject c) (.and (fNatObject d) (.and (fNatObject i) (.and (fNatObject x)
    (.ex (.ex (.ex (.ex (.ex
      (.and (fSucc (i + 5) 4)
      (.and (fMul 4 (d + 5) 3)
      (.and (fSucc 3 2)
      (.and (fMul 1 2 0)
      (.and (fAdd 0 (x + 5) (c + 5)) (.mem (x + 5) 2))))))))))))))

theorem bound_fBeta {c d i x n : Nat} (hc : c < n) (hd : d < n) (hi : i < n) (hx : x < n) :
    Bound (fBeta c d i x) n :=
  ⟨bound_fNatObject hc, bound_fNatObject hd, bound_fNatObject hi, bound_fNatObject hx,
   bound_fSucc (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega),
   bound_fSucc (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega),
   bound_fAdd (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩

theorem eval_fBeta (hM : Model E) (hNE : Nonempty V) (c d i x : Nat) (s : Nat → V) :
    eval E (fBeta c d i x) s ↔ BetaV hM hNE (s c) (s d) (s i) (s x) := by
  constructor
  · rintro ⟨hcF, hdF, hiF, hxF, si, sid, m, q, qm, hsi, hsid, hm, hqm, hadd, hxm⟩
    have hc := (eval_fNatObject _ _).mp hcF
    have hd := (eval_fNatObject _ _).mp hdF
    have hi := (eval_fNatObject _ _).mp hiF
    have hx := (eval_fNatObject _ _).mp hxF
    have hsi' : si = succV hM hNE (s i) := succ_unique hM hNE ((eval_fSucc _ _ _).mp hsi) (succV_spec hM hNE _)
    have hsid' : sid = mulV hM hNE (succV hM hNE (s i)) (s d) :=
      (mul_iff_eq hM hNE (succV_nat hM hNE hi) hd).mp (hsi' ▸ (eval_fMul _ _ _ _).mp hsid)
    have hm' : m = succV hM hNE (mulV hM hNE (succV hM hNE (s i)) (s d)) :=
      succ_unique hM hNE (hsid' ▸ (eval_fSucc _ _ _).mp hm) (succV_spec hM hNE _)
    have hqmF := (eval_fMul _ _ _ _).mp hqm
    have hq := hqmF.1
    have hqm' : qm = mulV hM hNE q m := (mul_iff_eq hM hNE hq (hm' ▸ succV_nat hM hNE (mulV_nat hM hNE (succV_nat hM hNE hi) hd))).mp hqmF
    have haddF := (eval_fAdd _ _ _ _).mp hadd
    have hc_eq : s c = addV hM hNE qm (s x) := (add_iff_eq hM hNE hqmF.2.2.1 hx).mp haddF
    exact ⟨hc, hd, hi, hx, q, hq, hm' ▸ hqm' ▸ hc_eq, hm' ▸ hxm⟩
  · rintro ⟨hc, hd, hi, hx, q, hq, hc_eq, hxm⟩
    let si := succV hM hNE (s i)
    let sid := mulV hM hNE si (s d)
    let m := succV hM hNE sid
    let qm := mulV hM hNE q m
    have hsi : NatObject E si := succV_nat hM hNE hi
    have hsid : NatObject E sid := mulV_nat hM hNE hsi hd
    have hm : NatObject E m := succV_nat hM hNE hsid
    refine ⟨(eval_fNatObject _ _).mpr hc, (eval_fNatObject _ _).mpr hd,
      (eval_fNatObject _ _).mpr hi, (eval_fNatObject _ _).mpr hx,
      si, sid, m, q, qm,
      (eval_fSucc (i + 5) 4 _).mpr (succV_spec hM hNE (s i)),
      (eval_fMul 4 (d + 5) 3 _).mpr (mulV_spec hM hNE hsi hd),
      (eval_fSucc 3 2 _).mpr (succV_spec hM hNE sid),
      (eval_fMul 1 2 0 _).mpr (mulV_spec hM hNE hq hm),
      (eval_fAdd 0 (x + 5) (c + 5) _).mpr (by
        show Add E qm (s x) (s c)
        rw [hc_eq]; exact addV_spec hM hNE (mulV_nat hM hNE hq hm) hx),
      hxm⟩

theorem betaV_exists_val (hM : Model E) (hNE : Nonempty V) {c d i : V}
    (hc : NatObject E c) (hd : NatObject E d) (hi : NatObject E i) :
    ∃ x, BetaV hM hNE c d i x := by
  let m := succV hM hNE (mulV hM hNE (succV hM hNE i) d)
  have hm : NatObject E m := succV_nat hM hNE (mulV_nat hM hNE (succV_nat hM hNE hi) hd)
  obtain ⟨q, x, hq, hx, hc_eq, hxm⟩ :=
    div_mod_exists hM hNE hm (zero_lt_succV hM hNE (mulV_nat hM hNE (succV_nat hM hNE hi) hd)) c hc
  exact ⟨x, hc, hd, hi, hx, q, hq, hc_eq, hxm⟩

theorem betaV_unique (hM : Model E) (hNE : Nonempty V) {c d i x₁ x₂ : V}
    (h1 : BetaV hM hNE c d i x₁) (h2 : BetaV hM hNE c d i x₂) : x₁ = x₂ := by
  rcases h1 with ⟨_, hd, hi, hx1, q1, hq1, hc1, hlt1⟩
  rcases h2 with ⟨_, _, _, hx2, q2, hq2, hc2, hlt2⟩
  let m := succV hM hNE (mulV hM hNE (succV hM hNE i) d)
  have hm : NatObject E m := succV_nat hM hNE (mulV_nat hM hNE (succV_nat hM hNE hi) hd)
  exact (div_mod_unique hM hNE hm hq1 hx1 hq2 hx2 hlt1 hlt2 (hc1.symm.trans hc2)).2

theorem functionOn_exists_of_beta (hM : Model E) (hNE : Nonempty V) {c d : V}
    (hc : NatObject E c) (hd : NatObject E d) :
    ∀ dom, NatObject E dom →
      ∃ f, FunctionOn E f dom ∧ ∀ i x, E i dom → (At E f i x ↔ BetaV hM hNE c d i x) := by
  let body : Formula :=
    .ex (.and (fFunctionOn 0 1)
      (.all (.all (.imp (.mem 1 3) (fIff (fAt 2 1 0) (fBeta 4 5 1 0))))))
  have hB : Bound body 3 :=
    ⟨bound_fFunctionOn (by omega) (by omega),
     ⟨⟨by omega, by omega⟩, bound_fIff (bound_fAt (by omega) (by omega) (by omega))
       (bound_fBeta (by omega) (by omega) (by omega) (by omega))⟩⟩
  let env : Nat → V := fun k => if k = 0 then c else d
  have hInd := omega_induction hM hNE 2 body hB env
    (fun z hz => by
      refine ⟨z, (eval_fFunctionOn 0 1 _).mpr ⟨fun x hx => False.elim (hz x hx), fun p hp => False.elim (hz p hp)⟩,
        fun i x hi => False.elim (hz i hi)⟩)
    (fun k k' hk hkk' ih => by
      rcases ih with ⟨f, hfunF, hat⟩
      have hfun : FunctionOn E f k := (eval_fFunctionOn 0 1 _).mp hfunF
      obtain ⟨y, hy⟩ := betaV_exists_val hM hNE hc hd hk
      obtain ⟨f', hfun', hf'at⟩ := functionOn_extend hM hNE hfun hkk'
      refine ⟨f', (eval_fFunctionOn 0 1 _).mpr hfun', fun i x hi => ?_⟩
      apply (eval_fIff _ _ _).mpr
      show eval E (fAt 2 1 0) (pushValue (pushValue (pushValue (pushValue env k') f') i) x) ↔
           eval E (fBeta 4 5 1 0) (pushValue (pushValue (pushValue (pushValue env k') f') i) x)
      rw [eval_fAt, eval_fBeta hM hNE]
      show At E f' i x ↔ BetaV hM hNE c d i x
      rw [hf'at]
      rcases (hkk' i).mp hi with hik | hik
      · have hprev := (eval_fIff _ _ _).mp (hat i x hik)
        rw [eval_fAt, eval_fBeta hM hNE] at hprev
        constructor
        · rintro (hfx | ⟨rfl, rfl⟩)
          · exact hprev.mp hfx
          · exact False.elim (mem_irrefl hM hNE i hik)
        · intro hb; exact Or.inl (hprev.mpr hb)
      · rw [hik]
        constructor
        · rintro (⟨q, hqf, hq⟩ | ⟨_, rfl⟩)
          · obtain ⟨u, v, huk, huv⟩ := hfun.2 q hqf
            have hku := (orderedPair_inj hq huv).1
            exact False.elim (mem_irrefl hM hNE k (hku ▸ huk))
          · exact hy
        · intro hb; exact Or.inr ⟨rfl, betaV_unique hM hNE hb hy⟩)
  intro dom hdom
  rcases hInd dom hdom with ⟨f, hfunF, hat⟩
  refine ⟨f, (eval_fFunctionOn 0 1 _).mp hfunF, fun i x hi => ?_⟩
  have h1 := (eval_fIff _ _ _).mp (hat i x hi)
  rwa [eval_fAt, eval_fBeta hM hNE] at h1

theorem exists_functionOn_bound (hM : Model E) (hNE : Nonempty V) {f dom : V}
    (hdom : NatObject E dom) (hfun : FunctionOn E f dom)
    (hnat : ∀ i x, E i dom → At E f i x → NatObject E x) :
    ∀ k, NatObject E k → (k = dom ∨ E k dom) →
      ∃ M, NatObject E M ∧ (dom = M ∨ E dom M) ∧ ∀ i x, E i k → At E f i x → E x M := by
  let body : Formula :=
    .imp (.or (.eq 0 1) (.mem 0 1))
      (.ex (.and (fNatObject 0) (.and (.or (.eq 2 0) (.mem 2 0))
        (.all (.all (.imp (.mem 1 3) (.imp (fAt 5 1 0) (.mem 0 2))))))))
  have hB : Bound body 3 :=
    ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
     ⟨bound_fNatObject (by omega), ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
      ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩⟩⟩
  let env : Nat → V := fun i => if i = 0 then dom else f
  have hInd := omega_induction hM hNE 2 body hB env
    (fun z hz _ => by
      refine ⟨dom, (eval_fNatObject _ _).mpr hdom, Or.inl rfl, fun i x hi _ => False.elim (hz i hi)⟩)
    (fun k k' hk hkk' ih hkle => by
      simp only [eval, pushValue, env, ↓reduceIte] at hkle
      have hk_lt_dom : E k dom := by
        rcases hkle with hkeq | hklt
        · rw [← hkeq]; exact (hkk' k).mpr (Or.inr rfl)
        · exact nat_lt_trans hM hNE dom hdom k k' ((hkk' k).mpr (Or.inr rfl)) hklt
      rcases ih (Or.inr hk_lt_dom) with ⟨M, hMF, hdomM, hbound⟩
      have hMn : NatObject E M := (eval_fNatObject _ _).mp hMF
      obtain ⟨y, hfky, huniq⟩ := hfun.1 k hk_lt_dom
      have hy : NatObject E y := hnat k y hk_lt_dom hfky
      let M' := succV hM hNE (addV hM hNE M y)
      have hM'n : NatObject E M' := succV_nat hM hNE (addV_nat hM hNE hMn hy)
      have hM_lt_M' : E M M' := by
        rcases addV_le_left hM hNE hMn y hy with h | h
        · exact (succV_spec hM hNE _ M).mpr (Or.inr h)
        · exact (succV_spec hM hNE _ M).mpr (Or.inl h)
      have hy_lt_M' : E y M' := by
        have hyle := addV_le_left hM hNE hy M hMn
        rw [addV_comm hM hNE hy M hMn] at hyle
        rcases hyle with h | h
        · exact (succV_spec hM hNE _ y).mpr (Or.inr h)
        · exact (succV_spec hM hNE _ y).mpr (Or.inl h)
      have hdomM' : dom = M' ∨ E dom M' := by
        simp only [eval, pushValue, env, ↓reduceIte] at hdomM
        rcases hdomM with h | h
        · exact Or.inr (h ▸ hM_lt_M')
        · exact Or.inr (nat_lt_trans hM hNE M' hM'n dom M h hM_lt_M')
      refine ⟨M', (eval_fNatObject _ _).mpr hM'n, hdomM', fun i x hi hfix => ?_⟩
      rcases (hkk' i).mp hi with hik | hik
      · have hxM : E x M := hbound i x hik hfix
        exact nat_lt_trans hM hNE M' hM'n x M hxM hM_lt_M'
      · have hfix' : At E f k x := hik ▸ ((eval_fAt _ _ _ _).mp hfix)
        have hxy : x = y := huniq x hfix'
        exact hxy ▸ hy_lt_M')
  intro k hk hkle
  rcases hInd k hk hkle with ⟨M, hMF, hdomM, hbound⟩
  refine ⟨M, (eval_fNatObject _ _).mp hMF, hdomM, fun i x hi hfix => ?_⟩
  exact hbound i x hi ((eval_fAt _ _ _ _).mpr hfix)

theorem beta_exists_of_functionOn (hM : Model E) (hNE : Nonempty V) {f code dom : V}
    (hcode : NatObject E code) (hdom : Succ E code dom) (hfun : FunctionOn E f dom)
    (hnat : ∀ i x, E i dom → At E f i x → NatObject E x) :
    ∃ c d, NatObject E c ∧ NatObject E d ∧
      ∀ i x, E i dom → At E f i x → BetaV hM hNE c d i x := by
  have hdom_nat : NatObject E dom := nat_succ hM hNE hcode hdom
  obtain ⟨M, hMn, hdomM, hbound⟩ :=
    exists_functionOn_bound hM hNE hdom_nat hfun hnat dom hdom_nat (Or.inl rfl)
  obtain ⟨d, hd, hd_pos, hd_mult⟩ := exists_common_multiple hM hNE M hMn
  -- Induct on k ≤ dom: ∃ P c, 0 < P ∧ c < P ∧
  --   (∀ i ∈ k, ∀ x, At f i x → Beta c d i x) ∧
  --   (∀ i ∈ k, Divides (1 + (i+1)*d) P) ∧
  --   (∀ j ∈ dom, (k = j ∨ k < j) → Coprime P (1 + (j+1)*d))
  -- Parameters: env 0 = dom, env 1 = f, env 2 = d
  -- Wait: inside body, var 0 is k, var 1 = dom, var 2 = f, var 3 = d
  let fMod (j dIdx mIdx : Nat) : Formula :=
    .ex (.ex (.and (fSucc (j + 2) 1) (.and (fMul 1 (dIdx + 2) 0) (fSucc 0 (mIdx + 2)))))
  have bound_fMod : ∀ j dIdx mIdx n, j < n → dIdx < n → mIdx < n → Bound (fMod j dIdx mIdx) n :=
    fun _ _ _ _ hj hd' hm =>
      ⟨bound_fSucc (by omega) (by omega), bound_fMul (by omega) (by omega) (by omega),
       bound_fSucc (by omega) (by omega)⟩
  have eval_fMod : ∀ j dIdx mIdx (s : Nat → V), NatObject E (s j) → NatObject E (s dIdx) →
      (eval E (fMod j dIdx mIdx) s ↔ s mIdx = succV hM hNE (mulV hM hNE (succV hM hNE (s j)) (s dIdx))) := by
    intro j dIdx mIdx s hj' hd'
    constructor
    · rintro ⟨sj, sjd, hsj, hsjd, hm⟩
      have hsj' := succ_unique hM hNE ((eval_fSucc _ _ _).mp hsj) (succV_spec hM hNE (s j))
      have hsjd' := (mul_iff_eq hM hNE (succV_nat hM hNE hj') hd').mp (hsj' ▸ (eval_fMul _ _ _ _).mp hsjd)
      exact succ_unique hM hNE (hsjd' ▸ (eval_fSucc _ _ _).mp hm) (succV_spec hM hNE _)
    · intro heq
      refine ⟨succV hM hNE (s j), mulV hM hNE (succV hM hNE (s j)) (s dIdx),
        (eval_fSucc (j + 2) 1 _).mpr (succV_spec hM hNE (s j)),
        (eval_fMul 1 (dIdx + 2) 0 _).mpr (mulV_spec hM hNE (succV_nat hM hNE hj') hd'),
        (eval_fSucc 0 (mIdx + 2) _).mpr (by
          show Succ E (mulV hM hNE (succV hM hNE (s j)) (s dIdx)) (s mIdx)
          rw [heq]; exact succV_spec hM hNE _)⟩
  let body : Formula :=
    .imp (.or (.eq 0 1) (.mem 0 1))
      (.ex (.ex
        (.and (fNatObject 1) (.and (fNatObject 0)
        (.and (.ex (.and (fEmpty 0) (.mem 0 2)))
        (.and (.mem 0 1)
        (.and (.all (.all (.imp (.mem 1 4) (.imp (fAt 6 1 0) (fBeta 2 7 1 0)))))
        (.and (.all (.imp (.mem 0 3) (.all (.imp (fMod 1 7 0) (fDivides 0 3)))))
          (.all (.imp (.mem 0 4) (.imp (.or (.eq 3 0) (.mem 3 0))
            (.all (.imp (fMod 1 7 0) (fCoprime 3 0))))))))))))))
  have hB : Bound body 4 :=
    ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
     ⟨bound_fNatObject (by omega), bound_fNatObject (by omega),
      ⟨bound_fEmpty (by omega), ⟨by omega, by omega⟩⟩,
      ⟨by omega, by omega⟩,
      ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega),
        bound_fBeta (by omega) (by omega) (by omega) (by omega)⟩⟩,
      ⟨⟨by omega, by omega⟩, ⟨bound_fMod _ _ _ _ (by omega) (by omega) (by omega),
        bound_fDivides (by omega) (by omega)⟩⟩,
      ⟨⟨by omega, by omega⟩, ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
        ⟨bound_fMod _ _ _ _ (by omega) (by omega) (by omega),
          bound_fCoprime (by omega) (by omega)⟩⟩⟩⟩⟩
  let env : Nat → V := fun i => if i = 0 then dom else if i = 1 then f else d
  have hInd := omega_induction hM hNE 3 body hB env
    (fun z hz _ => by
      have hz' : z = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
      subst hz'
      refine ⟨oneV hM hNE, zeroV hM hNE,
        (eval_fNatObject _ _).mpr (oneV_nat hM hNE),
        (eval_fNatObject _ _).mpr (zeroV_nat hM hNE),
        ⟨zeroV hM hNE, zeroV_empty hM hNE, zero_lt_succV hM hNE (zeroV_nat hM hNE)⟩,
        zero_lt_succV hM hNE (zeroV_nat hM hNE),
        fun i _ hi _ => False.elim (zeroV_empty hM hNE i hi),
        fun i hi => False.elim (zeroV_empty hM hNE i hi),
        fun j _ _ m _ => (eval_fCoprime hM hNE 3 0 _).mpr (fun g _ hg1 _ => dividesV_one_eq hM hNE hg1)⟩)
    (fun k k' hk hkk' ih hkle => by
      simp only [eval, pushValue, env, ↓reduceIte] at hkle
      have hk_lt_dom : E k dom := by
        rcases hkle with hkeq | hklt
        · rw [← hkeq]; exact (hkk' k).mpr (Or.inr rfl)
        · exact nat_lt_trans hM hNE dom hdom_nat k k' ((hkk' k).mpr (Or.inr rfl)) hklt
      rcases ih (Or.inr hk_lt_dom) with ⟨P, c, hPF, hcF, ⟨z0, hz0, hz0P⟩, hcP, hbeta, hdivP, hcopP⟩
      have hPn : NatObject E P := (eval_fNatObject _ _).mp hPF
      have hcn : NatObject E c := (eval_fNatObject _ _).mp hcF
      have : z0 = zeroV hM hNE := empty_unique hM hNE hz0 (zeroV_empty hM hNE)
      subst this
      obtain ⟨yk, hfkyk, huniq_yk⟩ := hfun.1 k hk_lt_dom
      have hyk : NatObject E yk := hnat k yk hk_lt_dom hfkyk
      let mk := succV hM hNE (mulV hM hNE (succV hM hNE k) d)
      have hmk : NatObject E mk := succV_nat hM hNE (mulV_nat hM hNE (succV_nat hM hNE hk) hd)
      have hmk_pos : E (zeroV hM hNE) mk := zero_lt_succV hM hNE (mulV_nat hM hNE (succV_nat hM hNE hk) hd)
      -- yk < M ≤ d < 1 + (k+1)*d = mk
      have hyk_lt_mk : E yk mk := by
        have hyk_lt_M : E yk M := hbound k yk hk_lt_dom hfkyk
        have hM_le_d : M = d ∨ E M d := by
          rcases nat_zero_le hM hNE (zeroV_empty hM hNE) M hMn with hM0 | hMpos
          · exact Or.inr (hM0 ▸ hd_pos)
          · obtain ⟨_, _, q, hq, hd_eq⟩ := hd_mult M hMn hMpos (Or.inl rfl)
            rcases nat_zero_le hM hNE (zeroV_empty hM hNE) q hq with hq0 | hqpos
            · rw [← hq0, zero_mulV hM hNE M hMn] at hd_eq
              exact False.elim (zeroV_empty hM hNE _ (hd_eq ▸ hd_pos))
            · have h1q := (nat_succ_le_iff hM hNE (zeroV_nat hM hNE) (succV_spec hM hNE _) q hq).mp hqpos
              obtain ⟨q', hq', hq_eq⟩ := sub_exists hM hNE (oneV_nat hM hNE) q hq h1q
              rw [← hq_eq, mulV_right_distrib hM hNE (oneV_nat hM hNE) hq' hMn, one_mulV hM hNE hMn] at hd_eq
              rw [hd_eq]
              exact addV_le_left hM hNE hMn (mulV hM hNE q' M) (mulV_nat hM hNE hq' hMn)
        have hd_lt_mk : E d mk := by
          have hd_le_skd : d = mulV hM hNE (succV hM hNE k) d ∨ E d (mulV hM hNE (succV hM hNE k) d) := by
            rw [succ_mulV hM hNE hk d hd, addV_comm hM hNE (mulV_nat hM hNE hk hd) d hd]
            exact addV_le_left hM hNE hd (mulV hM hNE k d) (mulV_nat hM hNE hk hd)
          rcases hd_le_skd with h | h
          · exact (succV_spec hM hNE _ d).mpr (Or.inr h)
          · exact (succV_spec hM hNE _ d).mpr (Or.inl h)
        have hyk_lt_d : E yk d := by
          rcases hM_le_d with h | h
          · exact h ▸ hyk_lt_M
          · exact nat_lt_trans hM hNE d hd yk M hyk_lt_M h
        exact nat_lt_trans hM hNE mk hmk yk d hyk_lt_d hd_lt_mk
      have hcop_P_mk : CoprimeV hM hNE P mk := by
        have h1 := hcopP k hk_lt_dom (Or.inl rfl) mk ((eval_fMod 1 7 0 _ hk hd).mpr rfl)
        exact (eval_fCoprime hM hNE 3 0 _).mp h1
      obtain ⟨c', hc', hc'_lt, ⟨qP, hqP, hc'_eqP⟩, ⟨qmk, hqmk, hc'_eqmk⟩⟩ :=
        crt2 hM hNE hPn hmk hcn hyk hz0P hmk_pos hcP hyk_lt_mk hcop_P_mk
      let P' := mulV hM hNE P mk
      have hP'n : NatObject E P' := mulV_nat hM hNE hPn hmk
      refine ⟨P', c', (eval_fNatObject _ _).mpr hP'n, (eval_fNatObject _ _).mpr hc',
        ⟨zeroV hM hNE, zeroV_empty hM hNE, mulV_pos hM hNE hPn hmk hz0P hmk_pos⟩,
        hc'_lt, ?_, ?_, ?_⟩
      · -- Beta agrees on all i ∈ k'
        intro i x hi hfix
        rw [eval_fBeta hM hNE]
        show BetaV hM hNE c' d i x
        have hfix' : At E f i x := (eval_fAt _ _ _ _).mp hfix
        rcases (hkk' i).mp hi with hik | hik
        · have hbi : BetaV hM hNE c d i x :=
            (eval_fBeta hM hNE 2 7 1 0 _).mp (hbeta i x hik hfix)
          rcases hbi with ⟨_, _, hi_nat, hx_nat, qi, hqi, hc_eq_i, hx_lt_mi⟩
          let mi := succV hM hNE (mulV hM hNE (succV hM hNE i) d)
          have hmi_nat : NatObject E mi := succV_nat hM hNE (mulV_nat hM hNE (succV_nat hM hNE hi_nat) hd)
          have hmi_div_P : DividesV hM hNE mi P :=
            (eval_fDivides hM hNE 0 3 _).mp (hdivP i hik mi ((eval_fMod 1 7 0 _ hi_nat hd).mpr rfl))
          obtain ⟨_, _, qmi, hqmi, hP_eq_mi⟩ := hmi_div_P
          refine ⟨hc', hd, hi_nat, hx_nat, addV hM hNE (mulV hM hNE qP qmi) qi,
            addV_nat hM hNE (mulV_nat hM hNE hqP hqmi) hqi, ?_, hx_lt_mi⟩
          rw [hc'_eqP, hc_eq_i, hP_eq_mi, mulV_right_distrib hM hNE (mulV_nat hM hNE hqP hqmi) hqi hmi_nat,
              mulV_assoc hM hNE hqP hqmi mi hmi_nat,
              addV_assoc hM hNE (mulV_nat hM hNE hqP (mulV_nat hM hNE hqmi hmi_nat)) (mulV_nat hM hNE hqi hmi_nat) x hx_nat]
        · rw [hik] at hfix' ⊢
          have hxyk : x = yk := huniq_yk x hfix'
          rw [hxyk]
          exact ⟨hc', hd, hk, hyk, qmk, hqmk, hc'_eqmk, hyk_lt_mk⟩
      · -- Divisibility of P' by m_i for i ∈ k'
        intro i hi m hmF
        have hi_nat : NatObject E i := nat_mem_is_nat hM hNE k' (nat_succ hM hNE hk hkk') i hi
        have hm_eq : m = succV hM hNE (mulV hM hNE (succV hM hNE i) d) :=
          (eval_fMod 1 7 0 _ hi_nat hd).mp hmF
        apply (eval_fDivides hM hNE 0 3 _).mpr
        show DividesV hM hNE m P'
        rcases (hkk' i).mp hi with hik | hik
        · have hmi_div_P : DividesV hM hNE m P :=
            (eval_fDivides hM hNE 0 3 _).mp (hdivP i hik m ((eval_fMod 1 7 0 _ hi_nat hd).mpr hm_eq))
          exact dividesV_mul_right hM hNE hmi_div_P hmk
        · rw [hm_eq, hik]
          exact dividesV_mul_left hM hNE (dividesV_refl hM hNE hmk) hPn
      · -- Coprimality of P' with m_j for k' ≤ j < dom
        intro j hjdom hjge m hmF
        have hj_nat : NatObject E j := nat_mem_is_nat hM hNE dom hdom_nat j hjdom
        have hm_eq : m = succV hM hNE (mulV hM hNE (succV hM hNE j) d) :=
          (eval_fMod 1 7 0 _ hj_nat hd).mp hmF
        dsimp only [eval, pushValue, env] at hjge
        have hkj : E k j := (nat_succ_le_iff hM hNE hk hkk' j hj_nat).mpr hjge
        have hcop_P_m : CoprimeV hM hNE P m :=
          (eval_fCoprime hM hNE 3 0 _).mp (hcopP j hjdom (Or.inr hkj) m ((eval_fMod 1 7 0 _ hj_nat hd).mpr hm_eq))
        have hjM : j = M ∨ E j M := by
          rcases hdomM with h | h
          · exact Or.inr (h ▸ hjdom)
          · exact Or.inr (nat_lt_trans hM hNE M hMn j dom hjdom h)
        have hcop_mk_m : CoprimeV hM hNE mk m :=
          hm_eq ▸ beta_moduli_coprime hM hNE hMn hd hd_mult hk hj_nat hkj hjM
        apply (eval_fCoprime hM hNE 3 0 _).mpr
        show CoprimeV hM hNE P' m
        exact coprimeV_mul_left hM hNE hPn hmk (hm_eq ▸ succV_nat hM hNE (mulV_nat hM hNE (succV_nat hM hNE hj_nat) hd))
          hcop_P_m hcop_mk_m)
  rcases hInd dom hdom_nat (Or.inl rfl) with ⟨_, c, _, hcF, _, _, hbeta, _, _⟩
  refine ⟨c, d, (eval_fNatObject _ _).mp hcF, hd, fun i x hi hfix => ?_⟩
  exact (eval_fBeta hM hNE 2 7 1 0 _).mp (hbeta i x hi ((eval_fAt _ _ _ _).mpr hfix))

/-! ### Part 4: SigmaFormula for InternalLinkedHalts and PhysicalHalts207 Bridge -/

noncomputable def numV (hM : Model E) (hNE : Nonempty V) : Nat → V
  | 0 => zeroV hM hNE
  | k + 1 => succV hM hNE (numV hM hNE k)

theorem numV_nat (hM : Model E) (hNE : Nonempty V) : ∀ k, NatObject E (numV hM hNE k)
  | 0 => zeroV_nat hM hNE
  | k + 1 => succV_nat hM hNE (numV_nat hM hNE k)

theorem numeral_iff_numV (hM : Model E) (hNE : Nonempty V) :
    ∀ k x, Numeral E k x ↔ x = numV hM hNE k
  | 0, x =>
    ⟨fun h => empty_unique hM hNE h (zeroV_empty hM hNE), fun h => h ▸ zeroV_empty hM hNE⟩
  | k + 1, x => by
    constructor
    · rintro ⟨y, hy, hsucc⟩
      have hy' : y = numV hM hNE k := (numeral_iff_numV hM hNE k y).mp hy
      rw [hy'] at hsucc
      exact succ_unique hM hNE hsucc (succV_spec hM hNE (numV hM hNE k))
    · intro hx
      exact ⟨numV hM hNE k, (numeral_iff_numV hM hNE k _).mpr rfl, hx ▸ succV_spec hM hNE _⟩

theorem mem_numV_iff (hM : Model E) (hNE : Nonempty V) :
    ∀ k x, E x (numV hM hNE k) ↔ ∃ q : Fin k, x = numV hM hNE q.val
  | 0, x => ⟨fun h => False.elim (zeroV_empty hM hNE x h), fun ⟨q, _⟩ => Fin.elim0 q⟩
  | k + 1, x => by
    constructor
    · intro hx
      rcases (succV_spec hM hNE (numV hM hNE k) x).mp hx with hlt | heq
      · obtain ⟨q, hq⟩ := (mem_numV_iff hM hNE k x).mp hlt
        exact ⟨⟨q.val, Nat.lt_succ_of_lt q.isLt⟩, hq⟩
      · exact ⟨⟨k, Nat.lt_succ_self k⟩, heq⟩
    · rintro ⟨⟨q, hq⟩, rfl⟩
      by_cases hlt : q < k
      · exact (succV_spec hM hNE _ _).mpr (Or.inl ((mem_numV_iff hM hNE k _).mpr ⟨⟨q, hlt⟩, rfl⟩))
      · have heq : q = k := by omega
        subst heq
        exact (succV_spec hM hNE _ _).mpr (Or.inr rfl)

noncomputable def evalTermV (hM : Model E) (hNE : Nonempty V) : ArithTerm → (Nat → V) → V
  | .zero, _ => zeroV hM hNE
  | .one, _ => oneV hM hNE
  | .var i, s => s i
  | .add p q, s => addV hM hNE (evalTermV hM hNE p s) (evalTermV hM hNE q s)
  | .mul p q, s => mulV hM hNE (evalTermV hM hNE p s) (evalTermV hM hNE q s)

theorem evalTermV_nat (hM : Model E) (hNE : Nonempty V) :
    ∀ (t : ArithTerm) (s : Nat → V), (∀ i, NatObject E (s i)) → NatObject E (evalTermV hM hNE t s)
  | .zero, _, _ => zeroV_nat hM hNE
  | .one, _, _ => oneV_nat hM hNE
  | .var i, _, hs => hs i
  | .add p q, s, hs => addV_nat hM hNE (evalTermV_nat hM hNE p s hs) (evalTermV_nat hM hNE q s hs)
  | .mul p q, s, hs => mulV_nat hM hNE (evalTermV_nat hM hNE p s hs) (evalTermV_nat hM hNE q s hs)

theorem graph_iff_evalTermV (hM : Model E) (hNE : Nonempty V) :
    ∀ (t : ArithTerm) (s : Nat → V), (∀ i, NatObject E (s i)) →
      ∀ z, t.graph E s z ↔ z = evalTermV hM hNE t s
  | .zero, _, _, z => numeral_iff_numV hM hNE 0 z
  | .one, _, _, z => numeral_iff_numV hM hNE 1 z
  | .var i, s, hs, z => ⟨fun h => h.2, fun h => ⟨h ▸ hs i, h⟩⟩
  | .add p q, s, hs, z => by
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      have ha' := (graph_iff_evalTermV hM hNE p s hs a).mp ha
      have hb' := (graph_iff_evalTermV hM hNE q s hs b).mp hb
      rw [ha', hb'] at hab
      exact (add_iff_eq hM hNE (evalTermV_nat hM hNE p s hs) (evalTermV_nat hM hNE q s hs)).mp hab
    · intro hz
      refine ⟨evalTermV hM hNE p s, evalTermV hM hNE q s,
        (graph_iff_evalTermV hM hNE p s hs _).mpr rfl,
        (graph_iff_evalTermV hM hNE q s hs _).mpr rfl, ?_⟩
      rw [hz]
      exact addV_spec hM hNE (evalTermV_nat hM hNE p s hs) (evalTermV_nat hM hNE q s hs)
  | .mul p q, s, hs, z => by
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      have ha' := (graph_iff_evalTermV hM hNE p s hs a).mp ha
      have hb' := (graph_iff_evalTermV hM hNE q s hs b).mp hb
      rw [ha', hb'] at hab
      exact (mul_iff_eq hM hNE (evalTermV_nat hM hNE p s hs) (evalTermV_nat hM hNE q s hs)).mp hab
    · intro hz
      refine ⟨evalTermV hM hNE p s, evalTermV hM hNE q s,
        (graph_iff_evalTermV hM hNE p s hs _).mpr rfl,
        (graph_iff_evalTermV hM hNE q s hs _).mpr rfl, ?_⟩
      rw [hz]
      exact mulV_spec hM hNE (evalTermV_nat hM hNE p s hs) (evalTermV_nat hM hNE q s hs)

theorem pushValue_nat {s : Nat → V} {x : V} (hs : ∀ i, NatObject E (s i)) (hx : NatObject E x) :
    ∀ i, NatObject E (pushValue s x i)
  | 0 => hx
  | i + 1 => hs i

end ZFModel

/-! SigmaFormula builders -/

def shiftTerm (k : Nat) : ArithTerm → ArithTerm
  | .zero => .zero
  | .one => .one
  | .var i => .var (i + k)
  | .add p q => .add (shiftTerm k p) (shiftTerm k q)
  | .mul p q => .mul (shiftTerm k p) (shiftTerm k q)

theorem bound_shiftTerm {t : ArithTerm} {n : Nat} (k : Nat) (ht : t.bound n) :
    (shiftTerm k t).bound (n + k) := by
  induction t with
  | zero => trivial
  | one => trivial
  | var i => exact Nat.add_lt_add_right ht k
  | add p q ihp ihq => exact ⟨ihp ht.1, ihq ht.2⟩
  | mul p q ihp ihq => exact ⟨ihp ht.1, ihq ht.2⟩

theorem evalTermV_shiftTerm {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (k : Nat) (t : ArithTerm) (s₁ s₂ : Nat → V) (h : ∀ i, s₂ (i + k) = s₁ i) :
    evalTermV hM hNE (shiftTerm k t) s₂ = evalTermV hM hNE t s₁ := by
  induction t with
  | zero => rfl
  | one => rfl
  | var i => exact h i
  | add p q ihp ihq => simp only [shiftTerm, evalTermV, ihp, ihq]
  | mul p q ihp ihq => simp only [shiftTerm, evalTermV, ihp, ihq]

theorem evalTermV_shift1 {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (t : ArithTerm) (s : Nat → V) (x : V) :
    evalTermV hM hNE (shiftTerm 1 t) (pushValue s x) = evalTermV hM hNE t s :=
  evalTermV_shiftTerm hM hNE 1 t s _ (fun _ => rfl)

theorem evalTermV_shift2 {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (t : ArithTerm) (s : Nat → V) (x1 x2 : V) :
    evalTermV hM hNE (shiftTerm 2 t) (pushValue (pushValue s x1) x2) = evalTermV hM hNE t s :=
  evalTermV_shiftTerm hM hNE 2 t s _ (fun _ => rfl)

theorem evalTermV_shift3 {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (t : ArithTerm) (s : Nat → V) (x1 x2 x3 : V) :
    evalTermV hM hNE (shiftTerm 3 t) (pushValue (pushValue (pushValue s x1) x2) x3) =
      evalTermV hM hNE t s :=
  evalTermV_shiftTerm hM hNE 3 t s _ (fun _ => rfl)

theorem evalTermV_shift6 {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (t : ArithTerm) (s : Nat → V) (x1 x2 x3 x4 x5 x6 : V) :
    evalTermV hM hNE (shiftTerm 6 t)
      (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue s x1) x2) x3) x4) x5) x6) =
      evalTermV hM hNE t s :=
  evalTermV_shiftTerm hM hNE 6 t s _ (fun _ => rfl)

theorem evalTermV_shift7 {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (t : ArithTerm) (s : Nat → V) (x1 x2 x3 x4 x5 x6 x7 : V) :
    evalTermV hM hNE (shiftTerm 7 t)
      (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue s x1) x2) x3) x4) x5) x6) x7) =
      evalTermV hM hNE t s :=
  evalTermV_shiftTerm hM hNE 7 t s _ (fun _ => rfl)

theorem natValue_shiftTerm (k : Nat) (t : ArithTerm) (s₁ s₂ : Nat → Nat)
    (h : ∀ i, s₂ (i + k) = s₁ i) :
    (shiftTerm k t).natValue s₂ = t.natValue s₁ := by
  induction t with
  | zero => rfl
  | one => rfl
  | var i => exact h i
  | add p q ihp ihq => simp only [shiftTerm, ArithTerm.natValue, ihp, ihq]
  | mul p q ihp ihq => simp only [shiftTerm, ArithTerm.natValue, ihp, ihq]

theorem natValue_shift1 (t : ArithTerm) (s : Nat → Nat) (x : Nat) :
    (shiftTerm 1 t).natValue (pushValue s x) = t.natValue s :=
  natValue_shiftTerm 1 t s _ (fun _ => rfl)

theorem natValue_shift3 (t : ArithTerm) (s : Nat → Nat) (x1 x2 x3 : Nat) :
    (shiftTerm 3 t).natValue (pushValue (pushValue (pushValue s x1) x2) x3) = t.natValue s :=
  natValue_shiftTerm 3 t s _ (fun _ => rfl)

theorem natValue_shift6 (t : ArithTerm) (s : Nat → Nat) (x1 x2 x3 x4 x5 x6 : Nat) :
    (shiftTerm 6 t).natValue
      (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue s x1) x2) x3) x4) x5) x6) =
      t.natValue s :=
  natValue_shiftTerm 6 t s _ (fun _ => rfl)

theorem bound_var {i n : Nat} (h : i < n) : (ArithTerm.var i).bound n := h

def sNum : Nat → ArithTerm
  | 0 => .zero
  | k + 1 => .add (sNum k) .one

theorem bound_sNum : ∀ k n, (sNum k).bound n
  | 0, _ => trivial
  | k + 1, n => ⟨bound_sNum k n, trivial⟩

theorem evalTermV_sNum {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (s : Nat → V) : ∀ k, evalTermV hM hNE (sNum k) s = numV hM hNE k
  | 0 => rfl
  | k + 1 => by
    simp only [sNum, evalTermV, evalTermV_sNum hM hNE s k, oneV]
    rw [addV_succ hM hNE (numV_nat hM hNE k) (zeroV_nat hM hNE), addV_zero hM hNE (numV_nat hM hNE k)]
    rfl

theorem natValue_sNum (s : Nat → Nat) : ∀ k, (sNum k).natValue s = k
  | 0 => rfl
  | k + 1 => by simp [sNum, ArithTerm.natValue, natValue_sNum s k]

def sEq (p q : ArithTerm) : SigmaFormula := .atom p q true true
def sNe (p q : ArithTerm) : SigmaFormula := .atom p q true false
def sLt (p q : ArithTerm) : SigmaFormula := .atom p q false true
def sGe (p q : ArithTerm) : SigmaFormula := .atom p q false false
def sFalse : SigmaFormula := sNe .zero .zero

theorem eval_sEq {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (p q : ArithTerm) (s : Nat → V) (hs : ∀ i, NatObject E (s i)) :
    (sEq p q).internalEval E s ↔ evalTermV hM hNE p s = evalTermV hM hNE q s := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    rw [(graph_iff_evalTermV hM hNE p s hs a).mp ha, (graph_iff_evalTermV hM hNE q s hs b).mp hb] at hab
    exact hab
  · intro h
    exact ⟨evalTermV hM hNE p s, evalTermV hM hNE q s,
      (graph_iff_evalTermV hM hNE p s hs _).mpr rfl,
      (graph_iff_evalTermV hM hNE q s hs _).mpr rfl, h⟩

theorem eval_sNe {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (p q : ArithTerm) (s : Nat → V) (hs : ∀ i, NatObject E (s i)) :
    (sNe p q).internalEval E s ↔ evalTermV hM hNE p s ≠ evalTermV hM hNE q s := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    rw [(graph_iff_evalTermV hM hNE p s hs a).mp ha, (graph_iff_evalTermV hM hNE q s hs b).mp hb] at hab
    exact hab
  · intro h
    exact ⟨evalTermV hM hNE p s, evalTermV hM hNE q s,
      (graph_iff_evalTermV hM hNE p s hs _).mpr rfl,
      (graph_iff_evalTermV hM hNE q s hs _).mpr rfl, h⟩

theorem eval_sLt {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (p q : ArithTerm) (s : Nat → V) (hs : ∀ i, NatObject E (s i)) :
    (sLt p q).internalEval E s ↔ E (evalTermV hM hNE p s) (evalTermV hM hNE q s) := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    rw [(graph_iff_evalTermV hM hNE p s hs a).mp ha, (graph_iff_evalTermV hM hNE q s hs b).mp hb] at hab
    exact hab
  · intro h
    exact ⟨evalTermV hM hNE p s, evalTermV hM hNE q s,
      (graph_iff_evalTermV hM hNE p s hs _).mpr rfl,
      (graph_iff_evalTermV hM hNE q s hs _).mpr rfl, h⟩

theorem eval_sGe {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (p q : ArithTerm) (s : Nat → V) (hs : ∀ i, NatObject E (s i)) :
    (sGe p q).internalEval E s ↔ ¬ E (evalTermV hM hNE p s) (evalTermV hM hNE q s) := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    rw [(graph_iff_evalTermV hM hNE p s hs a).mp ha, (graph_iff_evalTermV hM hNE q s hs b).mp hb] at hab
    exact hab
  · intro h
    exact ⟨evalTermV hM hNE p s, evalTermV hM hNE q s,
      (graph_iff_evalTermV hM hNE p s hs _).mpr rfl,
      (graph_iff_evalTermV hM hNE q s hs _).mpr rfl, h⟩

def sBeta (c d i x : ArithTerm) : SigmaFormula :=
  let m := ArithTerm.add (.mul (.add (shiftTerm 1 i) .one) (shiftTerm 1 d)) .one
  .exists_ (.conj (sEq (shiftTerm 1 c) (.add (.mul (.var 0) m) (shiftTerm 1 x)))
                  (sLt (shiftTerm 1 x) m))

theorem bound_sBeta {c d i x : ArithTerm} {n : Nat}
    (hc : c.bound n) (hd : d.bound n) (hi : i.bound n) (hx : x.bound n) :
    (sBeta c d i x).bound n :=
  ⟨⟨bound_shiftTerm 1 hc, ⟨⟨Nat.zero_lt_succ n, ⟨⟨bound_shiftTerm 1 hi, trivial⟩, bound_shiftTerm 1 hd⟩, trivial⟩,
    bound_shiftTerm 1 hx⟩⟩,
   ⟨bound_shiftTerm 1 hx, ⟨⟨⟨bound_shiftTerm 1 hi, trivial⟩, bound_shiftTerm 1 hd⟩, trivial⟩⟩⟩

theorem eval_sBeta {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (c d i x : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sBeta c d i x).internalEval E s ↔
      BetaV hM hNE (evalTermV hM hNE c s) (evalTermV hM hNE d s) (evalTermV hM hNE i s) (evalTermV hM hNE x s) := by
  have hc := evalTermV_nat hM hNE c s hs
  have hd := evalTermV_nat hM hNE d s hs
  have hi := evalTermV_nat hM hNE i s hs
  have hx := evalTermV_nat hM hNE x s hs
  have hModEq : ∀ q, NatObject E q →
      evalTermV hM hNE (.add (.mul (.add (shiftTerm 1 i) .one) (shiftTerm 1 d)) .one) (pushValue s q) =
      succV hM hNE (mulV hM hNE (succV hM hNE (evalTermV hM hNE i s)) (evalTermV hM hNE d s)) := by
    intro q _
    simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s q) (fun _ => rfl), oneV]
    rw [addV_succ hM hNE hi (zeroV_nat hM hNE), addV_zero hM hNE hi,
        addV_succ hM hNE (mulV_nat hM hNE (succV_nat hM hNE hi) hd) (zeroV_nat hM hNE),
        addV_zero hM hNE (mulV_nat hM hNE (succV_nat hM hNE hi) hd)]
  constructor
  · rintro ⟨q, hq, heqF, hltF⟩
    have hs' := pushValue_nat hs hq
    have heq := (eval_sEq hM hNE _ _ _ hs').mp heqF
    have hlt := (eval_sLt hM hNE _ _ _ hs').mp hltF
    simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s q) (fun _ => rfl)] at heq hlt
    rw [show addV hM hNE (mulV hM hNE (addV hM hNE (evalTermV hM hNE i s) (oneV hM hNE)) (evalTermV hM hNE d s)) (oneV hM hNE) =
        succV hM hNE (mulV hM hNE (succV hM hNE (evalTermV hM hNE i s)) (evalTermV hM hNE d s)) by
      have := hModEq q hq
      simpa [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s q) (fun _ => rfl)] using this] at heq hlt
    exact ⟨hc, hd, hi, hx, q, hq, heq, hlt⟩
  · rintro ⟨_, _, _, _, q, hq, heq, hlt⟩
    have hs' := pushValue_nat hs hq
    refine ⟨q, hq, (eval_sEq hM hNE _ _ _ hs').mpr ?_, (eval_sLt hM hNE _ _ _ hs').mpr ?_⟩
    · simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s q) (fun _ => rfl), pushValue]
      rw [show addV hM hNE (mulV hM hNE (addV hM hNE (evalTermV hM hNE i s) (oneV hM hNE)) (evalTermV hM hNE d s)) (oneV hM hNE) =
          succV hM hNE (mulV hM hNE (succV hM hNE (evalTermV hM hNE i s)) (evalTermV hM hNE d s)) by
        have := hModEq q hq
        simpa [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s q) (fun _ => rfl)] using this]
      exact heq
    · simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s q) (fun _ => rfl)]
      rw [show addV hM hNE (mulV hM hNE (addV hM hNE (evalTermV hM hNE i s) (oneV hM hNE)) (evalTermV hM hNE d s)) (oneV hM hNE) =
          succV hM hNE (mulV hM hNE (succV hM hNE (evalTermV hM hNE i s)) (evalTermV hM hNE d s)) by
        have := hModEq q hq
        simpa [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s q) (fun _ => rfl)] using this]
      exact hlt

def sCantor (a b z : ArithTerm) : SigmaFormula :=
  sEq (.mul (sNum 2) z) (.add (.mul (.add a b) (.add (.add a b) .one)) (.mul (sNum 2) b))

theorem bound_sCantor {a b z : ArithTerm} {n : Nat}
    (ha : a.bound n) (hb : b.bound n) (hz : z.bound n) : (sCantor a b z).bound n :=
  ⟨⟨bound_sNum 2 n, hz⟩, ⟨⟨⟨ha, hb⟩, ⟨⟨ha, hb⟩, trivial⟩⟩, ⟨bound_sNum 2 n, hb⟩⟩⟩

theorem eval_sCantor {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (a b z : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sCantor a b z).internalEval E s ↔
      Cantor E (evalTermV hM hNE a s) (evalTermV hM hNE b s) (evalTermV hM hNE z s) := by
  have ha := evalTermV_nat hM hNE a s hs
  have hb := evalTermV_nat hM hNE b s hs
  have hz := evalTermV_nat hM hNE z s hs
  have h2 := numV_nat hM hNE 2
  have hsum := addV_nat hM hNE ha hb
  have hnxt := succV_nat hM hNE hsum
  have hnext_eq : addV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s)) (oneV hM hNE) =
      succV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s)) := by
    rw [oneV, addV_succ hM hNE hsum (zeroV_nat hM hNE), addV_zero hM hNE hsum]
  unfold sCantor
  rw [eval_sEq hM hNE _ _ s hs]
  simp only [evalTermV, evalTermV_sNum hM hNE s 2, hnext_eq]
  constructor
  · intro heq
    refine ⟨ha, hb, hz, numV hM hNE 2, addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s),
      succV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s)),
      mulV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s)) (succV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s))),
      mulV hM hNE (numV hM hNE 2) (evalTermV hM hNE b s),
      mulV hM hNE (numV hM hNE 2) (evalTermV hM hNE z s),
      addV hM hNE (mulV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s)) (succV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s))))
        (mulV hM hNE (numV hM hNE 2) (evalTermV hM hNE b s)),
      (numeral_iff_numV hM hNE 2 _).mpr rfl,
      addV_spec hM hNE ha hb, succV_spec hM hNE _,
      mulV_spec hM hNE hsum hnxt, mulV_spec hM hNE h2 hb, mulV_spec hM hNE h2 hz,
      addV_spec hM hNE (mulV_nat hM hNE hsum hnxt) (mulV_nat hM hNE h2 hb), heq⟩
  · rintro ⟨_, _, _, two, sum, nxt, prod, tb, tz, tot, h2', hsum', hnxt', hprod', htb', htz', htot', heq⟩
    have h2eq : two = numV hM hNE 2 := (numeral_iff_numV hM hNE 2 two).mp h2'
    have hsumeq : sum = addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s) :=
      (add_iff_eq hM hNE ha hb).mp hsum'
    rw [hsumeq] at hnxt' hprod'
    have hnxteq : nxt = succV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s)) :=
      succ_unique hM hNE hnxt' (succV_spec hM hNE _)
    rw [hnxteq] at hprod'
    have hprodeq : prod = mulV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s))
        (succV hM hNE (addV hM hNE (evalTermV hM hNE a s) (evalTermV hM hNE b s))) :=
      (mul_iff_eq hM hNE hsum hnxt).mp hprod'
    rw [h2eq] at htb' htz'
    have htbeq : tb = mulV hM hNE (numV hM hNE 2) (evalTermV hM hNE b s) := (mul_iff_eq hM hNE h2 hb).mp htb'
    have htzeq : tz = mulV hM hNE (numV hM hNE 2) (evalTermV hM hNE z s) := (mul_iff_eq hM hNE h2 hz).mp htz'
    rw [hprodeq, htbeq] at htot'
    have htoteq := (add_iff_eq hM hNE (mulV_nat hM hNE hsum hnxt) (mulV_nat hM hNE h2 hb)).mp htot'
    rw [← htzeq, heq, htoteq]

def sListCons (a b c : ArithTerm) : SigmaFormula :=
  .exists_ (.conj (sCantor (shiftTerm 1 a) (shiftTerm 1 b) (.var 0))
                  (sEq (shiftTerm 1 c) (.add (.var 0) .one)))

theorem bound_sListCons {a b c : ArithTerm} {n : Nat}
    (ha : a.bound n) (hb : b.bound n) (hc : c.bound n) : (sListCons a b c).bound n :=
  ⟨bound_sCantor (bound_shiftTerm 1 ha) (bound_shiftTerm 1 hb) (Nat.zero_lt_succ n),
   ⟨bound_shiftTerm 1 hc, ⟨Nat.zero_lt_succ n, trivial⟩⟩⟩

theorem eval_sListCons {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (a b c : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sListCons a b c).internalEval E s ↔
      ListCons E (evalTermV hM hNE a s) (evalTermV hM hNE b s) (evalTermV hM hNE c s) := by
  constructor
  · rintro ⟨p, hp, hcant, heqF⟩
    have hs' := pushValue_nat hs hp
    have hcant' := (eval_sCantor hM hNE _ _ _ _ hs').mp hcant
    have heq := (eval_sEq hM hNE _ _ _ hs').mp heqF
    simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s p) (fun _ => rfl), pushValue, oneV] at hcant' heq
    rw [addV_succ hM hNE hp (zeroV_nat hM hNE), addV_zero hM hNE hp] at heq
    exact ⟨p, hcant', heq ▸ succV_spec hM hNE p⟩
  · rintro ⟨p, hcant, hsucc⟩
    have hp := hcant.2.2.1
    have hs' := pushValue_nat hs hp
    refine ⟨p, hp, (eval_sCantor hM hNE _ _ _ _ hs').mpr ?_, (eval_sEq hM hNE _ _ _ hs').mpr ?_⟩
    · simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s p) (fun _ => rfl), pushValue]
      exact hcant
    · simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s p) (fun _ => rfl), pushValue, oneV]
      rw [addV_succ hM hNE hp (zeroV_nat hM hNE), addV_zero hM hNE hp]
      exact succ_unique hM hNE hsucc (succV_spec hM hNE p)

def sListHead (x a : ArithTerm) : SigmaFormula :=
  .disj (.conj (sEq x .zero) (sEq a .zero))
        (.exists_ (sListCons (shiftTerm 1 a) (.var 0) (shiftTerm 1 x)))

theorem bound_sListHead {x a : ArithTerm} {n : Nat} (hx : x.bound n) (ha : a.bound n) :
    (sListHead x a).bound n :=
  ⟨⟨⟨hx, trivial⟩, ⟨ha, trivial⟩⟩,
   bound_sListCons (bound_shiftTerm 1 ha) (Nat.zero_lt_succ n) (bound_shiftTerm 1 hx)⟩

theorem eval_sListHead {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (x a : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sListHead x a).internalEval E s ↔
      ListHead E (evalTermV hM hNE x s) (evalTermV hM hNE a s) := by
  constructor
  · rintro (⟨hx0, ha0⟩ | ⟨b, hb, hcons⟩)
    · left
      have hx' := (eval_sEq hM hNE _ _ s hs).mp hx0
      have ha' := (eval_sEq hM hNE _ _ s hs).mp ha0
      exact ⟨hx' ▸ zeroV_empty hM hNE, ha' ▸ zeroV_empty hM hNE⟩
    · right
      have hs' := pushValue_nat hs hb
      have hc := (eval_sListCons hM hNE _ _ _ _ hs').mp hcons
      simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s b) (fun _ => rfl), pushValue] at hc
      exact ⟨b, hc⟩
  · rintro (⟨hx0, ha0⟩ | ⟨b, hcons⟩)
    · left
      exact ⟨(eval_sEq hM hNE _ _ s hs).mpr (empty_unique hM hNE hx0 (zeroV_empty hM hNE)),
             (eval_sEq hM hNE _ _ s hs).mpr (empty_unique hM hNE ha0 (zeroV_empty hM hNE))⟩
    · right
      have hb : NatObject E b := let ⟨_, hc, _⟩ := hcons; hc.2.1
      have hs' := pushValue_nat hs hb
      refine ⟨b, hb, (eval_sListCons hM hNE _ _ _ _ hs').mpr ?_⟩
      simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s b) (fun _ => rfl), pushValue]
      exact hcons

def sListTail (x b : ArithTerm) : SigmaFormula :=
  .disj (.conj (sEq x .zero) (sEq b .zero))
        (.exists_ (sListCons (.var 0) (shiftTerm 1 b) (shiftTerm 1 x)))

theorem bound_sListTail {x b : ArithTerm} {n : Nat} (hx : x.bound n) (hb : b.bound n) :
    (sListTail x b).bound n :=
  ⟨⟨⟨hx, trivial⟩, ⟨hb, trivial⟩⟩,
   bound_sListCons (Nat.zero_lt_succ n) (bound_shiftTerm 1 hb) (bound_shiftTerm 1 hx)⟩

theorem eval_sListTail {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (x b : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sListTail x b).internalEval E s ↔
      ListTail E (evalTermV hM hNE x s) (evalTermV hM hNE b s) := by
  constructor
  · rintro (⟨hx0, hb0⟩ | ⟨a, ha, hcons⟩)
    · left
      have hx' := (eval_sEq hM hNE _ _ s hs).mp hx0
      have hb' := (eval_sEq hM hNE _ _ s hs).mp hb0
      exact ⟨hx' ▸ zeroV_empty hM hNE, hb' ▸ zeroV_empty hM hNE⟩
    · right
      have hs' := pushValue_nat hs ha
      have hc := (eval_sListCons hM hNE _ _ _ _ hs').mp hcons
      simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s a) (fun _ => rfl), pushValue] at hc
      exact ⟨a, hc⟩
  · rintro (⟨hx0, hb0⟩ | ⟨a, hcons⟩)
    · left
      exact ⟨(eval_sEq hM hNE _ _ s hs).mpr (empty_unique hM hNE hx0 (zeroV_empty hM hNE)),
             (eval_sEq hM hNE _ _ s hs).mpr (empty_unique hM hNE hb0 (zeroV_empty hM hNE))⟩
    · right
      have ha : NatObject E a := let ⟨_, hc, _⟩ := hcons; hc.1
      have hs' := pushValue_nat hs ha
      refine ⟨a, ha, (eval_sListCons hM hNE _ _ _ _ hs').mpr ?_⟩
      simp only [evalTermV, evalTermV_shiftTerm hM hNE 1 _ s (pushValue s a) (fun _ => rfl), pushValue]
      exact hcons

def sBitCons (bit : Bool) (x y : ArithTerm) : SigmaFormula :=
  sEq y (.add (if bit then .one else .zero) (.mul (sNum 2) x))

theorem bound_sBitCons (bit : Bool) {x y : ArithTerm} {n : Nat} (hx : x.bound n) (hy : y.bound n) :
    (sBitCons bit x y).bound n :=
  ⟨hy, ⟨by cases bit <;> trivial, ⟨bound_sNum 2 n, hx⟩⟩⟩

theorem eval_sBitCons {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (bit : Bool) (x y : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sBitCons bit x y).internalEval E s ↔
      BitCons E bit (evalTermV hM hNE x s) (evalTermV hM hNE y s) := by
  have hx := evalTermV_nat hM hNE x s hs
  have h2 := numV_nat hM hNE 2
  have hb_eq : evalTermV hM hNE (if bit then .one else .zero) s = numV hM hNE (if bit then 1 else 0) := by
    cases bit <;> rfl
  have hb_nat : NatObject E (numV hM hNE (if bit then 1 else 0)) := numV_nat hM hNE _
  unfold sBitCons
  rw [eval_sEq hM hNE _ _ s hs]
  simp only [evalTermV, evalTermV_sNum hM hNE s 2, hb_eq]
  constructor
  · intro heq
    exact ⟨numV hM hNE (if bit then 1 else 0), numV hM hNE 2,
      mulV hM hNE (numV hM hNE 2) (evalTermV hM hNE x s),
      (numeral_iff_numV hM hNE _ _).mpr rfl, (numeral_iff_numV hM hNE 2 _).mpr rfl,
      mulV_spec hM hNE h2 hx, heq ▸ addV_spec hM hNE hb_nat (mulV_nat hM hNE h2 hx)⟩
  · rintro ⟨b, two, twice, hb', h2', hmul', hadd'⟩
    have hbeq := (numeral_iff_numV hM hNE _ b).mp hb'
    have h2eq := (numeral_iff_numV hM hNE 2 two).mp h2'
    have htw := (mul_iff_eq hM hNE h2 hx).mp (h2eq ▸ hmul')
    exact (add_iff_eq hM hNE hb_nat (mulV_nat hM hNE h2 hx)).mp (hbeq ▸ htw ▸ hadd')

def sMoveLeftBit (write bit : Bool) (sl tl tr : ArithTerm) : SigmaFormula :=
  .conj (sBitCons bit (.var 1) (shiftTerm 3 sl))
  (.conj (sEq (shiftTerm 3 tl) (.var 1))
  (.conj (sBitCons write (.var 2) (.var 0)) (sBitCons bit (.var 0) (shiftTerm 3 tr))))

def sMove (read write direction : Bool) (next : Nat) (sl sr tq tl tr : ArithTerm) : SigmaFormula :=
  .exists_
    (.conj (sBitCons read (.var 0) (shiftTerm 1 sr))
    (.conj (sEq (shiftTerm 1 tq) (sNum next))
      (if direction then
        .conj (sBitCons write (shiftTerm 1 sl) (shiftTerm 1 tl)) (sEq (shiftTerm 1 tr) (.var 0))
      else
        .exists_ (.exists_
          (.disj (sMoveLeftBit write false sl tl tr) (sMoveLeftBit write true sl tl tr))))))

theorem bound_sMove (read write direction : Bool) (next : Nat)
    {sl sr tq tl tr : ArithTerm} {n : Nat}
    (hsl : sl.bound n) (hsr : sr.bound n) (htq : tq.bound n) (htl : tl.bound n) (htr : tr.bound n) :
    (sMove read write direction next sl sr tq tl tr).bound n := by
  refine ⟨bound_sBitCons read (bound_var (by omega)) (bound_shiftTerm 1 hsr),
    ⟨bound_shiftTerm 1 htq, bound_sNum next (n + 1)⟩, ?_⟩
  cases direction
  · constructor
    · exact ⟨bound_sBitCons false (bound_var (by omega)) (bound_shiftTerm 3 hsl),
        ⟨bound_shiftTerm 3 htl, bound_var (by omega)⟩,
        bound_sBitCons write (bound_var (by omega)) (bound_var (by omega)),
        bound_sBitCons false (bound_var (by omega)) (bound_shiftTerm 3 htr)⟩
    · exact ⟨bound_sBitCons true (bound_var (by omega)) (bound_shiftTerm 3 hsl),
        ⟨bound_shiftTerm 3 htl, bound_var (by omega)⟩,
        bound_sBitCons write (bound_var (by omega)) (bound_var (by omega)),
        bound_sBitCons true (bound_var (by omega)) (bound_shiftTerm 3 htr)⟩
  · exact ⟨bound_sBitCons write (bound_shiftTerm 1 hsl) (bound_shiftTerm 1 htl),
      ⟨bound_shiftTerm 1 htr, bound_var (by omega)⟩⟩

theorem eval_sMove {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (read write direction : Bool) (next : Nat)
    (sq sl sr tq tl tr : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sMove read write direction next sl sr tq tl tr).internalEval E s ↔
      Move E read write direction next
        ⟨evalTermV hM hNE sq s, evalTermV hM hNE sl s, evalTermV hM hNE sr s⟩
        ⟨evalTermV hM hNE tq s, evalTermV hM hNE tl s, evalTermV hM hNE tr s⟩ := by
  cases direction
  · constructor
    · rintro ⟨r, hr, hread, hnext, l, hl, mid, hmid, hbr⟩
      have hs1 := pushValue_nat hs hr
      have hs3 := pushValue_nat (pushValue_nat hs1 hl) hmid
      have hread' := (eval_sBitCons hM hNE read _ _ _ hs1).mp hread
      have hnext' := (eval_sEq hM hNE _ _ _ hs1).mp hnext
      simp only [evalTermV, evalTermV_shift1, evalTermV_sNum, pushValue] at hread' hnext'
      refine ⟨r, hread', (numeral_iff_numV hM hNE next _).mpr hnext', ?_⟩
      cases hbr with
      | inl hf =>
        rcases hf with ⟨h1, h2, h3, h4⟩
        have h1' := (eval_sBitCons hM hNE false _ _ _ hs3).mp h1
        have h2' := (eval_sEq hM hNE _ _ _ hs3).mp h2
        have h3' := (eval_sBitCons hM hNE write _ _ _ hs3).mp h3
        have h4' := (eval_sBitCons hM hNE false _ _ _ hs3).mp h4
        simp only [evalTermV, evalTermV_shift3, pushValue] at h1' h2' h3' h4'
        exact ⟨l, false, mid, h1', h2', h3', h4'⟩
      | inr ht =>
        rcases ht with ⟨h1, h2, h3, h4⟩
        have h1' := (eval_sBitCons hM hNE true _ _ _ hs3).mp h1
        have h2' := (eval_sEq hM hNE _ _ _ hs3).mp h2
        have h3' := (eval_sBitCons hM hNE write _ _ _ hs3).mp h3
        have h4' := (eval_sBitCons hM hNE true _ _ _ hs3).mp h4
        simp only [evalTermV, evalTermV_shift3, pushValue] at h1' h2' h3' h4'
        exact ⟨l, true, mid, h1', h2', h3', h4'⟩
    · rintro ⟨r, hread, hnext, l, bit, mid, h1, h2, h3, h4⟩
      have hr : NatObject E r := let ⟨_, _, _, _, _, hm, _⟩ := hread; hm.2.1
      have hl : NatObject E l := let ⟨_, _, _, _, _, hm, _⟩ := h1; hm.2.1
      have hmid : NatObject E mid := let ⟨_, _, _, _, _, hm, _⟩ := h4; hm.2.1
      have hs1 := pushValue_nat hs hr
      have hs3 := pushValue_nat (pushValue_nat hs1 hl) hmid
      refine ⟨r, hr, (eval_sBitCons hM hNE read _ _ _ hs1).mpr ?_,
        (eval_sEq hM hNE _ _ _ hs1).mpr ?_, l, hl, mid, hmid, ?_⟩
      · simpa [evalTermV, evalTermV_shift1, pushValue] using hread
      · simpa [evalTermV, evalTermV_shift1, evalTermV_sNum, pushValue] using (numeral_iff_numV hM hNE next _).mp hnext
      · cases bit
        · left
          refine ⟨(eval_sBitCons hM hNE false _ _ _ hs3).mpr ?_,
            (eval_sEq hM hNE _ _ _ hs3).mpr ?_,
            (eval_sBitCons hM hNE write _ _ _ hs3).mpr ?_,
            (eval_sBitCons hM hNE false _ _ _ hs3).mpr ?_⟩
          · simpa [evalTermV, evalTermV_shift3, pushValue] using h1
          · simpa [evalTermV, evalTermV_shift3, pushValue] using h2
          · simpa [evalTermV, evalTermV_shift3, pushValue] using h3
          · simpa [evalTermV, evalTermV_shift3, pushValue] using h4
        · right
          refine ⟨(eval_sBitCons hM hNE true _ _ _ hs3).mpr ?_,
            (eval_sEq hM hNE _ _ _ hs3).mpr ?_,
            (eval_sBitCons hM hNE write _ _ _ hs3).mpr ?_,
            (eval_sBitCons hM hNE true _ _ _ hs3).mpr ?_⟩
          · simpa [evalTermV, evalTermV_shift3, pushValue] using h1
          · simpa [evalTermV, evalTermV_shift3, pushValue] using h2
          · simpa [evalTermV, evalTermV_shift3, pushValue] using h3
          · simpa [evalTermV, evalTermV_shift3, pushValue] using h4
  · constructor
    · rintro ⟨r, hr, hread, hnext, hleft, htr⟩
      have hs1 := pushValue_nat hs hr
      have hread' := (eval_sBitCons hM hNE read _ _ _ hs1).mp hread
      have hnext' := (eval_sEq hM hNE _ _ _ hs1).mp hnext
      have hleft' := (eval_sBitCons hM hNE write _ _ _ hs1).mp hleft
      have htr' := (eval_sEq hM hNE _ _ _ hs1).mp htr
      simp only [evalTermV, evalTermV_shift1, evalTermV_sNum, pushValue] at hread' hnext' hleft' htr'
      exact ⟨r, hread', (numeral_iff_numV hM hNE next _).mpr hnext', hleft', htr'⟩
    · rintro ⟨r, hread, hnext, hleft, htr⟩
      have hr : NatObject E r := let ⟨_, _, _, _, _, hm, _⟩ := hread; hm.2.1
      have hs1 := pushValue_nat hs hr
      refine ⟨r, hr, (eval_sBitCons hM hNE read _ _ _ hs1).mpr ?_,
        (eval_sEq hM hNE _ _ _ hs1).mpr ?_,
        (eval_sBitCons hM hNE write _ _ _ hs1).mpr ?_,
        (eval_sEq hM hNE _ _ _ hs1).mpr ?_⟩
      · simpa [evalTermV, evalTermV_shift1, pushValue] using hread
      · simpa [evalTermV, evalTermV_shift1, evalTermV_sNum, pushValue] using (numeral_iff_numV hM hNE next _).mp hnext
      · simpa [evalTermV, evalTermV_shift1, pushValue] using hleft
      · simpa [evalTermV, evalTermV_shift1, pushValue] using htr

def sAnyFin : Nat → (Nat → SigmaFormula) → SigmaFormula
  | 0, _ => sFalse
  | k + 1, F => .disj (sAnyFin k F) (F k)

theorem bound_sAnyFin : ∀ (k n : Nat) (F : Nat → SigmaFormula),
    (∀ i < k, (F i).bound n) → (sAnyFin k F).bound n
  | 0, _, _, _ => ⟨trivial, trivial⟩
  | k + 1, n, F, hF =>
    ⟨bound_sAnyFin k n F (fun i hi => hF i (Nat.lt_succ_of_lt hi)), hF k (Nat.lt_succ_self k)⟩

theorem eval_sAnyFin {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V) :
    ∀ (k : Nat) (F : Nat → SigmaFormula) (s : Nat → V), (∀ i, NatObject E (s i)) →
      ((sAnyFin k F).internalEval E s ↔ ∃ q : Fin k, (F q.val).internalEval E s)
  | 0, _, s, hs =>
    ⟨fun h => False.elim (((eval_sNe hM hNE .zero .zero s hs).mp h) rfl), fun ⟨q, _⟩ => Fin.elim0 q⟩
  | k + 1, F, s, hs => by
    constructor
    · rintro (h1 | h2)
      · obtain ⟨q, hq⟩ := (eval_sAnyFin hM hNE k F s hs).mp h1
        exact ⟨⟨q.val, Nat.lt_succ_of_lt q.isLt⟩, hq⟩
      · exact ⟨⟨k, Nat.lt_succ_self k⟩, h2⟩
    · rintro ⟨⟨q, hq⟩, hFq⟩
      by_cases hlt : q < k
      · exact Or.inl ((eval_sAnyFin hM hNE k F s hs).mpr ⟨⟨q, hlt⟩, hFq⟩)
      · have heq : q = k := by omega
        subst heq
        exact Or.inr hFq

theorem natEval_sAnyFin :
    ∀ (k : Nat) (F : Nat → SigmaFormula) (s : Nat → Nat),
      ((sAnyFin k F).natEval s ↔ ∃ q : Fin k, (F q.val).natEval s)
  | 0, _, _ => ⟨fun h => False.elim (h rfl), fun ⟨q, _⟩ => Fin.elim0 q⟩
  | k + 1, F, s => by
    constructor
    · rintro (h1 | h2)
      · obtain ⟨q, hq⟩ := (natEval_sAnyFin k F s).mp h1
        exact ⟨⟨q.val, Nat.lt_succ_of_lt q.isLt⟩, hq⟩
      · exact ⟨⟨k, Nat.lt_succ_self k⟩, h2⟩
    · rintro ⟨⟨q, hq⟩, hFq⟩
      by_cases hlt : q < k
      · exact Or.inl ((natEval_sAnyFin k F s).mpr ⟨⟨q, hlt⟩, hFq⟩)
      · have heq : q = k := by omega
        subst heq
        exact Or.inr hFq

def sRowBranch (q : Nat) (read : Bool) (sl sr tq tl tr : ArithTerm) : SigmaFormula :=
  match (if read then (literalRows.getD q (none, none)).2
         else (literalRows.getD q (none, none)).1) with
  | none => sFalse
  | some (write, direction, next) => sMove read write direction next sl sr tq tl tr

theorem bound_sRowBranch (q : Nat) (read : Bool) {sl sr tq tl tr : ArithTerm} {n : Nat}
    (hsl : sl.bound n) (hsr : sr.bound n) (htq : tq.bound n) (htl : tl.bound n) (htr : tr.bound n) :
    (sRowBranch q read sl sr tq tl tr).bound n := by
  unfold sRowBranch
  cases (if read then (literalRows.getD q (none, none)).2
         else (literalRows.getD q (none, none)).1) with
  | none => exact ⟨trivial, trivial⟩
  | some entry =>
    rcases entry with ⟨w, d, nxt⟩
    exact bound_sMove read w d nxt hsl hsr htq htl htr

theorem eval_sRowBranch {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (q : Nat) (read : Bool) (sq sl sr tq tl tr : ArithTerm) (s : Nat → V)
    (hs : ∀ k, NatObject E (s k)) :
    (sRowBranch q read sl sr tq tl tr).internalEval E s ↔
      ∃ write direction next,
        (if read then (literalRows.getD q (none, none)).2
         else (literalRows.getD q (none, none)).1) = some (write, direction, next) ∧
        Move E read write direction next
          ⟨evalTermV hM hNE sq s, evalTermV hM hNE sl s, evalTermV hM hNE sr s⟩
          ⟨evalTermV hM hNE tq s, evalTermV hM hNE tl s, evalTermV hM hNE tr s⟩ := by
  unfold sRowBranch
  cases hrow : (if read then (literalRows.getD q (none, none)).2
                else (literalRows.getD q (none, none)).1) with
  | none =>
    constructor
    · intro h; exact False.elim (((eval_sNe hM hNE .zero .zero s hs).mp h) rfl)
    · rintro ⟨_, _, _, heq, _⟩; cases heq
  | some entry =>
    rcases entry with ⟨w, d, nxt⟩
    constructor
    · intro hm
      exact ⟨w, d, nxt, rfl, (eval_sMove hM hNE read w d nxt sq sl sr tq tl tr s hs).mp hm⟩
    · rintro ⟨w', d', nxt', heq, hm⟩
      injection heq with ht
      cases ht
      exact (eval_sMove hM hNE read w d nxt sq sl sr tq tl tr s hs).mpr hm

def sStep (sq sl sr tq tl tr : ArithTerm) : SigmaFormula :=
  sAnyFin 207 (fun q =>
    .conj (sEq sq (sNum q))
      (.disj (sRowBranch q false sl sr tq tl tr) (sRowBranch q true sl sr tq tl tr)))

theorem bound_sStep {sq sl sr tq tl tr : ArithTerm} {n : Nat}
    (hsq : sq.bound n) (hsl : sl.bound n) (hsr : sr.bound n)
    (htq : tq.bound n) (htl : tl.bound n) (htr : tr.bound n) :
    (sStep sq sl sr tq tl tr).bound n :=
  bound_sAnyFin 207 n _ (fun i _ =>
    ⟨⟨hsq, bound_sNum i n⟩,
     bound_sRowBranch i false hsl hsr htq htl htr,
     bound_sRowBranch i true hsl hsr htq htl htr⟩)

theorem eval_sStep {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (sq sl sr tq tl tr : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sStep sq sl sr tq tl tr).internalEval E s ↔
      Step E ⟨evalTermV hM hNE sq s, evalTermV hM hNE sl s, evalTermV hM hNE sr s⟩
             ⟨evalTermV hM hNE tq s, evalTermV hM hNE tl s, evalTermV hM hNE tr s⟩ := by
  rw [sStep, eval_sAnyFin hM hNE 207 _ s hs]
  constructor
  · rintro ⟨q, hqeq, hbr⟩
    have hqnum : Numeral E q.val (evalTermV hM hNE sq s) :=
      (numeral_iff_numV hM hNE q.val _).mpr (by
        have := (eval_sEq hM hNE _ _ s hs).mp hqeq
        rwa [evalTermV_sNum hM hNE s q.val] at this)
    refine ⟨⟨evalTermV_nat hM hNE sq s hs, evalTermV_nat hM hNE sl s hs, evalTermV_nat hM hNE sr s hs⟩,
      ⟨evalTermV_nat hM hNE tq s hs, evalTermV_nat hM hNE tl s hs, evalTermV_nat hM hNE tr s hs⟩,
      q, hqnum, ?_⟩
    cases hbr with
    | inl hf =>
      obtain ⟨w, d, nxt, hrow, hm⟩ := (eval_sRowBranch hM hNE q.val false sq sl sr tq tl tr s hs).mp hf
      exact ⟨false, w, d, nxt, hrow, hm⟩
    | inr ht =>
      obtain ⟨w, d, nxt, hrow, hm⟩ := (eval_sRowBranch hM hNE q.val true sq sl sr tq tl tr s hs).mp ht
      exact ⟨true, w, d, nxt, hrow, hm⟩
  · rintro ⟨_, _, q, hqnum, read, w, d, nxt, hrow, hm⟩
    refine ⟨q, (eval_sEq hM hNE _ _ s hs).mpr ?_, ?_⟩
    · rw [evalTermV_sNum hM hNE s q.val]
      exact (numeral_iff_numV hM hNE q.val _).mp hqnum
    · cases read
      · exact Or.inl ((eval_sRowBranch hM hNE q.val false sq sl sr tq tl tr s hs).mpr ⟨w, d, nxt, hrow, hm⟩)
      · exact Or.inr ((eval_sRowBranch hM hNE q.val true sq sl sr tq tl tr s hs).mpr ⟨w, d, nxt, hrow, hm⟩)

def sTerminal (sq : ArithTerm) : SigmaFormula := sGe sq (sNum 207)

theorem bound_sTerminal {sq : ArithTerm} {n : Nat} (hsq : sq.bound n) : (sTerminal sq).bound n :=
  ⟨hsq, bound_sNum 207 n⟩

theorem eval_sTerminal {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (sq sl sr : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sTerminal sq).internalEval E s ↔
      Terminal E ⟨evalTermV hM hNE sq s, evalTermV hM hNE sl s, evalTermV hM hNE sr s⟩ := by
  rw [sTerminal, eval_sGe hM hNE _ _ s hs, evalTermV_sNum hM hNE s 207, mem_numV_iff hM hNE 207]
  constructor
  · intro h q hnum
    exact h ⟨q, (numeral_iff_numV hM hNE q.val _).mp hnum⟩
  · rintro h ⟨q, hq⟩
    exact h q ((numeral_iff_numV hM hNE q.val _).mpr hq)

def sNumericConfCode (sq sl sr code : ArithTerm) : SigmaFormula :=
  .exists_ (.conj (sCantor (shiftTerm 1 sl) (shiftTerm 1 sr) (.var 0))
                  (sCantor (shiftTerm 1 sq) (.var 0) (shiftTerm 1 code)))

theorem bound_sNumericConfCode {sq sl sr code : ArithTerm} {n : Nat}
    (hsq : sq.bound n) (hsl : sl.bound n) (hsr : sr.bound n) (hc : code.bound n) :
    (sNumericConfCode sq sl sr code).bound n :=
  ⟨bound_sCantor (bound_shiftTerm 1 hsl) (bound_shiftTerm 1 hsr) (Nat.zero_lt_succ n),
   bound_sCantor (bound_shiftTerm 1 hsq) (Nat.zero_lt_succ n) (bound_shiftTerm 1 hc)⟩

theorem eval_sNumericConfCode {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (sq sl sr code : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sNumericConfCode sq sl sr code).internalEval E s ↔
      NumericConfCode E ⟨evalTermV hM hNE sq s, evalTermV hM hNE sl s, evalTermV hM hNE sr s⟩
        (evalTermV hM hNE code s) := by
  constructor
  · rintro ⟨lr, hlr, h1, h2⟩
    have hs' := pushValue_nat hs hlr
    have h1' := (eval_sCantor hM hNE _ _ _ _ hs').mp h1
    have h2' := (eval_sCantor hM hNE _ _ _ _ hs').mp h2
    simp only [evalTermV, evalTermV_shift1, pushValue] at h1' h2'
    exact ⟨lr, h1', h2'⟩
  · rintro ⟨lr, h1, h2⟩
    have hlr : NatObject E lr := h1.2.2.1
    have hs' := pushValue_nat hs hlr
    refine ⟨lr, hlr, (eval_sCantor hM hNE _ _ _ _ hs').mpr ?_, (eval_sCantor hM hNE _ _ _ _ hs').mpr ?_⟩
    · simpa [evalTermV, evalTermV_shift1, pushValue] using h1
    · simpa [evalTermV, evalTermV_shift1, pushValue] using h2

def sNumericStep (before after : ArithTerm) : SigmaFormula :=
  .exists_ (.exists_ (.exists_ (.exists_ (.exists_ (.exists_
    (.conj (sNumericConfCode (.var 5) (.var 4) (.var 3) (shiftTerm 6 before))
    (.conj (sNumericConfCode (.var 2) (.var 1) (.var 0) (shiftTerm 6 after))
           (sStep (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))))))))

theorem bound_sNumericStep {before after : ArithTerm} {n : Nat}
    (hb : before.bound n) (ha : after.bound n) : (sNumericStep before after).bound n :=
  ⟨bound_sNumericConfCode (bound_var (by omega)) (bound_var (by omega)) (bound_var (by omega)) (bound_shiftTerm 6 hb),
   bound_sNumericConfCode (bound_var (by omega)) (bound_var (by omega)) (bound_var (by omega)) (bound_shiftTerm 6 ha),
   bound_sStep (bound_var (by omega)) (bound_var (by omega)) (bound_var (by omega))
     (bound_var (by omega)) (bound_var (by omega)) (bound_var (by omega))⟩

theorem eval_sNumericStep {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (before after : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sNumericStep before after).internalEval E s ↔
      NumericStep E (evalTermV hM hNE before s) (evalTermV hM hNE after s) := by
  constructor
  · rintro ⟨sq, hsq, sl, hsl, sr, hsr, tq, htq, tl, htl, tr, htr, h1, h2, h3⟩
    have hs6 := pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat hs hsq) hsl) hsr) htq) htl) htr
    have h1' := (eval_sNumericConfCode hM hNE _ _ _ _ _ hs6).mp h1
    have h2' := (eval_sNumericConfCode hM hNE _ _ _ _ _ hs6).mp h2
    have h3' := (eval_sStep hM hNE _ _ _ _ _ _ _ hs6).mp h3
    simp only [evalTermV, evalTermV_shift6, pushValue] at h1' h2' h3'
    exact ⟨⟨sq, sl, sr⟩, ⟨tq, tl, tr⟩, h1', h2', h3'⟩
  · rintro ⟨⟨sq, sl, sr⟩, ⟨tq, tl, tr⟩, h1, h2, h3⟩
    have ⟨⟨hsq, hsl, hsr⟩, ⟨htq, htl, htr⟩, _⟩ := h3
    have hs6 := pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat hs hsq) hsl) hsr) htq) htl) htr
    refine ⟨sq, hsq, sl, hsl, sr, hsr, tq, htq, tl, htl, tr, htr,
      (eval_sNumericConfCode hM hNE _ _ _ _ _ hs6).mpr ?_,
      (eval_sNumericConfCode hM hNE _ _ _ _ _ hs6).mpr ?_,
      (eval_sStep hM hNE _ _ _ _ _ _ _ hs6).mpr ?_⟩
    · simpa [evalTermV, evalTermV_shift6, pushValue] using h1
    · simpa [evalTermV, evalTermV_shift6, pushValue] using h2
    · simpa [evalTermV, pushValue] using h3

def sRunEdge (initial next tail : ArithTerm) : SigmaFormula :=
  .disj (.conj (sEq tail .zero) (sEq next initial))
        (.conj (sNe tail .zero)
          (.exists_ (.conj (sListHead (shiftTerm 1 tail) (.var 0))
                           (sNumericStep (.var 0) (shiftTerm 1 next)))))

theorem bound_sRunEdge {initial next tail : ArithTerm} {n : Nat}
    (hi : initial.bound n) (hn : next.bound n) (ht : tail.bound n) :
    (sRunEdge initial next tail).bound n :=
  ⟨⟨⟨ht, trivial⟩, ⟨hn, hi⟩⟩,
   ⟨⟨ht, trivial⟩,
    ⟨bound_sListHead (bound_shiftTerm 1 ht) (bound_var (by omega)),
     bound_sNumericStep (bound_var (by omega)) (bound_shiftTerm 1 hn)⟩⟩⟩

theorem eval_sRunEdge {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (initial next tail : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sRunEdge initial next tail).internalEval E s ↔
      RunEdge E (evalTermV hM hNE initial s) (evalTermV hM hNE next s) (evalTermV hM hNE tail s) := by
  constructor
  · rintro (⟨ht0, hni⟩ | ⟨htne, prev, hprev, hhd, hstep⟩)
    · left
      exact ⟨((eval_sEq hM hNE _ _ s hs).mp ht0) ▸ zeroV_empty hM hNE,
             (eval_sEq hM hNE _ _ s hs).mp hni⟩
    · right
      have hne' : ¬ Empty E (evalTermV hM hNE tail s) := fun he =>
        ((eval_sNe hM hNE _ _ s hs).mp htne) (empty_unique hM hNE he (zeroV_empty hM hNE))
      have hs1 := pushValue_nat hs hprev
      have hhd' := (eval_sListHead hM hNE _ _ _ hs1).mp hhd
      have hstep' := (eval_sNumericStep hM hNE _ _ _ hs1).mp hstep
      simp only [evalTermV, evalTermV_shift1, pushValue] at hhd' hstep'
      exact ⟨hne', prev, hhd', hstep'⟩
  · rintro (⟨ht0, hni⟩ | ⟨htne, prev, hhd, hstep⟩)
    · left
      exact ⟨(eval_sEq hM hNE _ _ s hs).mpr (empty_unique hM hNE ht0 (zeroV_empty hM hNE)),
             (eval_sEq hM hNE _ _ s hs).mpr hni⟩
    · right
      have hne' : evalTermV hM hNE tail s ≠ zeroV hM hNE := fun heq =>
        htne (heq ▸ zeroV_empty hM hNE)
      have hprev : NatObject E prev := by
        rcases hstep with ⟨_, _, ⟨_, _, hc⟩, _, _⟩
        exact hc.2.2.1
      have hs1 := pushValue_nat hs hprev
      refine ⟨(eval_sNe hM hNE _ _ s hs).mpr hne', prev, hprev,
        (eval_sListHead hM hNE _ _ _ hs1).mpr ?_,
        (eval_sNumericStep hM hNE _ _ _ hs1).mpr ?_⟩
      · simpa [evalTermV, evalTermV_shift1, pushValue] using hhd
      · simpa [evalTermV, evalTermV_shift1, pushValue] using hstep

def sLinkedRun (initial code : ArithTerm) : SigmaFormula :=
  .conj (sNe code .zero)
    (.exists_ (.exists_
      (.conj (sBeta (.var 1) (.var 0) .zero (shiftTerm 2 code))
      (.conj (sBeta (.var 1) (.var 0) (shiftTerm 2 code) .zero)
        (.forallLt (shiftTerm 2 code)
          (.exists_ (.exists_
            (.conj (sBeta (.var 4) (.var 3) (.var 2) (.var 1))
            (.conj (sBeta (.var 4) (.var 3) (.add (.var 2) .one) (.var 0))
            (.conj (sListTail (.var 1) (.var 0))
              (.disj (sEq (.var 1) .zero)
                (.exists_ (.exists_
                  (.conj (sListHead (.var 3) (.var 1))
                  (.conj (sListTail (.var 3) (.var 0))
                    (sRunEdge (shiftTerm 7 initial) (.var 1) (.var 0)))))))))))))))))

theorem bound_sLinkedRun {initial code : ArithTerm} {n : Nat}
    (hi : initial.bound n) (hc : code.bound n) : (sLinkedRun initial code).bound n :=
  ⟨⟨hc, trivial⟩,
   ⟨bound_sBeta (bound_var (by omega)) (bound_var (by omega)) trivial (bound_shiftTerm 2 hc),
    bound_sBeta (bound_var (by omega)) (bound_var (by omega)) (bound_shiftTerm 2 hc) trivial,
    bound_shiftTerm 2 hc,
    ⟨bound_sBeta (bound_var (by omega)) (bound_var (by omega)) (bound_var (by omega)) (bound_var (by omega)),
     bound_sBeta (bound_var (by omega)) (bound_var (by omega)) ⟨bound_var (by omega), trivial⟩ (bound_var (by omega)),
     bound_sListTail (bound_var (by omega)) (bound_var (by omega)),
     ⟨⟨bound_var (by omega), trivial⟩,
      ⟨bound_sListHead (bound_var (by omega)) (bound_var (by omega)),
       bound_sListTail (bound_var (by omega)) (bound_var (by omega)),
       bound_sRunEdge (bound_shiftTerm 7 hi) (bound_var (by omega)) (bound_var (by omega))⟩⟩⟩⟩⟩

theorem eval_sLinkedRun {V : Type} {E : V → V → Prop} (hM : Model E) (hNE : Nonempty V)
    (initial code : ArithTerm) (s : Nat → V) (hs : ∀ k, NatObject E (s k)) :
    (sLinkedRun initial code).internalEval E s ↔
      LinkedRun E (evalTermV hM hNE initial s) (evalTermV hM hNE code s) := by
  have hi_nat := evalTermV_nat hM hNE initial s hs
  have hc_nat := evalTermV_nat hM hNE code s hs
  constructor
  · rintro ⟨hneF, c, hc, d, hd, hb0, hbc, bound, hboundG, hforall⟩
    have hne : ¬ Empty E (evalTermV hM hNE code s) := fun he =>
      ((eval_sNe hM hNE _ _ s hs).mp hneF) (empty_unique hM hNE he (zeroV_empty hM hNE))
    have hs2 := pushValue_nat (pushValue_nat hs hc) hd
    have hbound_eq : bound = evalTermV hM hNE code s := by
      have := (graph_iff_evalTermV hM hNE (shiftTerm 2 code) _ hs2 bound).mp hboundG
      rwa [evalTermV_shift2] at this
    subst hbound_eq
    have hb0' : BetaV hM hNE c d (zeroV hM hNE) (evalTermV hM hNE code s) := by
      have := (eval_sBeta hM hNE _ _ _ _ _ hs2).mp hb0
      simpa [evalTermV, evalTermV_shift2, pushValue] using this
    have hbc' : BetaV hM hNE c d (evalTermV hM hNE code s) (zeroV hM hNE) := by
      have := (eval_sBeta hM hNE _ _ _ _ _ hs2).mp hbc
      simpa [evalTermV, evalTermV_shift2, pushValue] using this
    let dom := succV hM hNE (evalTermV hM hNE code s)
    obtain ⟨f, hfun, hfat⟩ := functionOn_exists_of_beta hM hNE hc hd dom (succV_nat hM hNE hc_nat)
    refine ⟨hi_nat, hc_nat, hne, zeroV hM hNE, dom, f, zeroV_empty hM hNE, succV_spec hM hNE _,
      hfun,
      (hfat (zeroV hM hNE) _ (zero_lt_succV hM hNE hc_nat)).mpr hb0',
      (hfat (evalTermV hM hNE code s) _ ((succV_spec hM hNE _ _).mpr (Or.inr rfl))).mpr hbc',
      fun i x hi hfix => ((hfat i x hi).mp hfix).2.2.2.1,
      fun i hi => ?_⟩
    have hi_nat' : NatObject E i := nat_mem_is_nat hM hNE _ hc_nat i hi
    rcases hforall i hi_nat' hi with ⟨x, hx, y, hy, hbi, hbsi, htail, hedge⟩
    have hs5 := pushValue_nat (pushValue_nat (pushValue_nat hs2 hi_nat') hx) hy
    have hbi' : BetaV hM hNE c d i x := by
      simpa [evalTermV, pushValue] using (eval_sBeta hM hNE _ _ _ _ _ hs5).mp hbi
    have hbsi' : BetaV hM hNE c d (succV hM hNE i) y := by
      have h1 := (eval_sBeta hM hNE _ _ _ _ _ hs5).mp hbsi
      simp only [evalTermV, pushValue, oneV] at h1
      rwa [addV_succ hM hNE hi_nat' (zeroV_nat hM hNE), addV_zero hM hNE hi_nat'] at h1
    have htail' : ListTail E x y := by
      simpa [evalTermV, pushValue] using (eval_sListTail hM hNE _ _ _ hs5).mp htail
    have hsi_dom : E (succV hM hNE i) dom := by
      rcases (nat_succ_le_iff hM hNE hi_nat' (succV_spec hM hNE i) _ hc_nat).mp hi with h | h
      · exact (succV_spec hM hNE _ _).mpr (Or.inr h)
      · exact (succV_spec hM hNE _ _).mpr (Or.inl h)
    refine ⟨succV hM hNE i, x, y, succV_spec hM hNE i,
      (hfat i x ((succV_spec hM hNE _ _).mpr (Or.inl hi))).mpr hbi',
      (hfat (succV hM hNE i) y hsi_dom).mpr hbsi', htail', ?_⟩
    cases hedge with
    | inl hx0 =>
      have hx0' : x = zeroV hM hNE := (eval_sEq hM hNE _ _ _ hs5).mp hx0
      exact Or.inl (hx0' ▸ zeroV_empty hM hNE)
    | inr hpair =>
      rcases hpair with ⟨a, ha, b, hb, hhd, htl, hre⟩
      have hs7 := pushValue_nat (pushValue_nat hs5 ha) hb
      have hhd' := (eval_sListHead hM hNE _ _ _ hs7).mp hhd
      have htl' := (eval_sListTail hM hNE _ _ _ hs7).mp htl
      have hre' := (eval_sRunEdge hM hNE _ _ _ _ hs7).mp hre
      simp only [evalTermV, evalTermV_shift7, pushValue] at hhd' htl' hre'
      exact Or.inr ⟨a, b, hhd', htl', hre'⟩
  · rintro ⟨_, _, hne, zero, dom, f, hz, hdom, hfun, hf0, hfc, hnat, hstep⟩
    have hz_eq : zero = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
    subst hz_eq
    have hne' : evalTermV hM hNE code s ≠ zeroV hM hNE := fun heq => hne (heq ▸ zeroV_empty hM hNE)
    obtain ⟨c, d, hc, hd, hbeta⟩ := beta_exists_of_functionOn hM hNE hc_nat hdom hfun hnat
    have hs2 := pushValue_nat (pushValue_nat hs hc) hd
    refine ⟨(eval_sNe hM hNE _ _ s hs).mpr hne', c, hc, d, hd,
      (eval_sBeta hM hNE _ _ _ _ _ hs2).mpr ?_,
      (eval_sBeta hM hNE _ _ _ _ _ hs2).mpr ?_,
      evalTermV hM hNE code s,
      (graph_iff_evalTermV hM hNE (shiftTerm 2 code) _ hs2 _).mpr
        (evalTermV_shift2 hM hNE code s c d).symm,
      fun i hi_nat' hi => ?_⟩
    · simp only [evalTermV, evalTermV_shift2, pushValue]
      have h0dom : E (zeroV hM hNE) dom := by
        have : dom = succV hM hNE (evalTermV hM hNE code s) := succ_unique hM hNE hdom (succV_spec hM hNE _)
        exact this ▸ zero_lt_succV hM hNE hc_nat
      exact hbeta (zeroV hM hNE) _ h0dom hf0
    · simp only [evalTermV, evalTermV_shift2, pushValue]
      exact hbeta _ (zeroV hM hNE) ((hdom _).mpr (Or.inr rfl)) hfc
    · obtain ⟨j, x, y, hij, hfix, hfjy, htail, hedge⟩ := hstep i hi
      have hj_eq : j = succV hM hNE i := succ_unique hM hNE hij (succV_spec hM hNE i)
      subst hj_eq
      have hidom : E i dom := (hdom i).mpr (Or.inl hi)
      have hjdom : E (succV hM hNE i) dom := by
        rcases (nat_succ_le_iff hM hNE hi_nat' (succV_spec hM hNE i) _ hc_nat).mp hi with h | h
        · exact (hdom _).mpr (Or.inr h)
        · exact (hdom _).mpr (Or.inl h)
      have hx : NatObject E x := hnat i x hidom hfix
      have hy : NatObject E y := hnat (succV hM hNE i) y hjdom hfjy
      have hs5 := pushValue_nat (pushValue_nat (pushValue_nat hs2 hi_nat') hx) hy
      refine ⟨x, hx, y, hy,
        (eval_sBeta hM hNE _ _ _ _ _ hs5).mpr ?_,
        (eval_sBeta hM hNE _ _ _ _ _ hs5).mpr ?_,
        (eval_sListTail hM hNE _ _ _ hs5).mpr ?_, ?_⟩
      · simpa [evalTermV, pushValue] using hbeta i x hidom hfix
      · simp only [evalTermV, pushValue, oneV]
        rw [addV_succ hM hNE hi_nat' (zeroV_nat hM hNE), addV_zero hM hNE hi_nat']
        exact hbeta (succV hM hNE i) y hjdom hfjy
      · simpa [evalTermV, pushValue] using htail
      · cases hedge with
        | inl hx0 =>
          left
          exact (eval_sEq hM hNE _ _ _ hs5).mpr (empty_unique hM hNE hx0 (zeroV_empty hM hNE))
        | inr hpair =>
          right
          rcases hpair with ⟨a, b, hhd, htl, hre⟩
          have ha : NatObject E a := by
            rcases hhd with ⟨_, ha0⟩ | ⟨_, _, hc, _⟩
            · exact nat_zero hM hNE ha0
            · exact hc.1
          have hb : NatObject E b := by
            rcases htl with ⟨_, hb0⟩ | ⟨_, _, hc, _⟩
            · exact nat_zero hM hNE hb0
            · exact hc.2.1
          have hs7 := pushValue_nat (pushValue_nat hs5 ha) hb
          refine ⟨a, ha, b, hb,
            (eval_sListHead hM hNE _ _ _ hs7).mpr ?_,
            (eval_sListTail hM hNE _ _ _ hs7).mpr ?_,
            (eval_sRunEdge hM hNE _ _ _ _ hs7).mpr ?_⟩
          · simpa [evalTermV, pushValue] using hhd
          · simpa [evalTermV, pushValue] using htl
          · simpa [evalTermV, evalTermV_shift7, pushValue] using hre

def sHalts207 : SigmaFormula :=
  .exists_ (.exists_ (.exists_ (.exists_ (.exists_
    (.conj (sLinkedRun .zero (.var 4))
    (.conj (sListHead (.var 4) (.var 3))
    (.conj (sNumericConfCode (.var 2) (.var 1) (.var 0) (.var 3))
      (sTerminal (.var 2)))))))))

theorem sHalts207_bound : sHalts207.bound 0 :=
  ⟨bound_sLinkedRun trivial (bound_var (by omega)),
   bound_sListHead (bound_var (by omega)) (bound_var (by omega)),
   bound_sNumericConfCode (bound_var (by omega)) (bound_var (by omega)) (bound_var (by omega)) (bound_var (by omega)),
   bound_sTerminal (bound_var (by omega))⟩

theorem sHalts207_represents (H : Formula) (hH : Represents207 H) :
    RepresentsArithmetic sHalts207 H := by
  refine ⟨hH.1, fun V E hNE hM s env henv => ?_⟩
  rw [hH.2 V E hNE hM s]
  constructor
  · rintro ⟨zero, hist, last, ⟨tq, tl, tr⟩, hz, hrun, hhd, hcode, ⟨htq, htl, htr⟩, hterm⟩
    have hz_eq : zero = zeroV hM hNE := empty_unique hM hNE hz (zeroV_empty hM hNE)
    subst hz_eq
    have hhist : NatObject E hist := hrun.2.1
    have hlast : NatObject E last := let ⟨_, _, hc⟩ := hcode; hc.2.2.1
    have hs5 := pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat henv hhist) hlast) htq) htl) htr
    refine ⟨hist, hhist, last, hlast, tq, htq, tl, htl, tr, htr,
      (eval_sLinkedRun hM hNE _ _ _ hs5).mpr ?_,
      (eval_sListHead hM hNE _ _ _ hs5).mpr ?_,
      (eval_sNumericConfCode hM hNE _ _ _ _ _ hs5).mpr ?_,
      (eval_sTerminal hM hNE (.var 2) (.var 1) (.var 0) _ hs5).mpr ?_⟩
    · simpa [evalTermV, pushValue] using hrun
    · simpa [evalTermV, pushValue] using hhd
    · simpa [evalTermV, pushValue] using hcode
    · simpa [evalTermV, pushValue] using hterm
  · rintro ⟨hist, hhist, last, hlast, tq, htq, tl, htl, tr, htr, hrun, hhd, hcode, hterm⟩
    have hs5 := pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat (pushValue_nat henv hhist) hlast) htq) htl) htr
    have hrun' := (eval_sLinkedRun hM hNE _ _ _ hs5).mp hrun
    have hhd' := (eval_sListHead hM hNE _ _ _ hs5).mp hhd
    have hcode' := (eval_sNumericConfCode hM hNE _ _ _ _ _ hs5).mp hcode
    have hterm' := (eval_sTerminal hM hNE (.var 2) (.var 1) (.var 0) _ hs5).mp hterm
    simp only [evalTermV, pushValue] at hrun' hhd' hcode' hterm'
    exact ⟨zeroV hM hNE, hist, last, ⟨tq, tl, tr⟩, zeroV_empty hM hNE,
      hrun', hhd', hcode', ⟨htq, htl, htr⟩, hterm'⟩

/-! Standard Nat soundness: sHalts207.natEval → PhysicalHalts207 -/

def cantorN (a b : Nat) : Nat := ((a + b) * (a + b + 1) + 2 * b) / 2
def confCodeN (c : Nat × Nat × Nat) : Nat := cantorN c.1 (cantorN c.2.1 c.2.2)

theorem cantor_eq_of_formula {a b z : Nat} (h : 2 * z = (a + b) * (a + b + 1) + 2 * b) :
    z = cantorN a b := by
  unfold cantorN; omega

theorem cantor_inj {a b a' b' z : Nat}
    (h1 : 2 * z = (a + b) * (a + b + 1) + 2 * b)
    (h2 : 2 * z = (a' + b') * (a' + b' + 1) + 2 * b') :
    a = a' ∧ b = b' := by
  have hlt : ∀ x y x' y', x + y < x' + y' →
      (x + y) * (x + y + 1) + 2 * y < (x' + y') * (x' + y' + 1) + 2 * y' := by
    intro x y x' y' hxy
    have h1 : (x + y + 1) * (x + y + 2) ≤ (x' + y') * (x' + y' + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (x + y) * (x + y + 1) + 2 * y < (x + y + 1) * (x + y + 2) := by
      have : (x + y + 1) * (x + y + 2) = (x + y) * (x + y + 1) + 2 * (x + y) + 2 := by
        calc (x + y + 1) * (x + y + 2)
            = (x + y + 1) * (x + y) + (x + y + 1) * 2 := Nat.mul_add _ _ _
          _ = (x + y) * (x + y + 1) + 2 * (x + y) + 2 := by rw [Nat.mul_comm (x + y + 1) (x + y)]; omega
      omega
    omega
  have hs : a + b = a' + b' := by
    by_cases hlt1 : a + b < a' + b'
    · have := hlt a b a' b' hlt1; omega
    · by_cases hlt2 : a' + b' < a + b
      · have := hlt a' b' a b hlt2; omega
      · omega
  rw [hs] at h1
  have hb : b = b' := by omega
  exact ⟨by omega, hb⟩

theorem cantor_zero {a b : Nat} (h : 0 = (a + b) * (a + b + 1) + 2 * b) : a = 0 ∧ b = 0 := by
  have h0 : (a + b) * (a + b + 1) = 0 := by omega
  rcases Nat.mul_eq_zero.mp h0 with h1 | h2 <;> omega

theorem natEval_sBeta_eq {c d i x : ArithTerm} {s : Nat → Nat}
    (h : (sBeta c d i x).natEval s) :
    x.natValue s = c.natValue s % ((i.natValue s + 1) * d.natValue s + 1) := by
  rcases h with ⟨q, heq, hlt⟩
  unfold sEq at heq
  unfold sLt at hlt
  simp only [SigmaFormula.natEval, ArithTerm.natValue, natValue_shift1, pushValue, ↓reduceIte] at heq hlt
  have hmod : (q * ((i.natValue s + 1) * d.natValue s + 1) + x.natValue s) %
      ((i.natValue s + 1) * d.natValue s + 1) = x.natValue s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  rw [← heq] at hmod
  exact hmod.symm

theorem natEval_sCantor_eq {a b z : ArithTerm} {s : Nat → Nat}
    (h : (sCantor a b z).natEval s) :
    2 * z.natValue s = (a.natValue s + b.natValue s) * (a.natValue s + b.natValue s + 1) + 2 * b.natValue s := by
  unfold sCantor sEq at h
  simp only [SigmaFormula.natEval, ArithTerm.natValue, natValue_sNum, ↓reduceIte] at h
  exact h

theorem natEval_sListCons_eq {a b c : ArithTerm} {s : Nat → Nat}
    (h : (sListCons a b c).natEval s) :
    ∃ p, 2 * p = (a.natValue s + b.natValue s) * (a.natValue s + b.natValue s + 1) + 2 * b.natValue s ∧
      c.natValue s = p + 1 := by
  rcases h with ⟨p, hcant, heq⟩
  have hc := natEval_sCantor_eq hcant
  unfold sEq at heq
  simp only [SigmaFormula.natEval, ArithTerm.natValue, natValue_shift1, pushValue, ↓reduceIte] at hc heq
  exact ⟨p, hc, heq⟩

theorem natEval_sListHead_eq {x a : ArithTerm} {s : Nat → Nat}
    (h : (sListHead x a).natEval s) :
    (x.natValue s = 0 ∧ a.natValue s = 0) ∨
    ∃ b p, 2 * p = (a.natValue s + b) * (a.natValue s + b + 1) + 2 * b ∧ x.natValue s = p + 1 := by
  rcases h with ⟨hx, ha⟩ | ⟨b, hcons⟩
  · exact Or.inl ⟨hx, ha⟩
  · obtain ⟨p, hc, heq⟩ := natEval_sListCons_eq hcons
    simp only [ArithTerm.natValue, natValue_shiftTerm 1 _ s (pushValue s b) (fun _ => rfl), pushValue] at hc heq
    exact Or.inr ⟨b, p, hc, heq⟩

theorem natEval_sListTail_eq {x b : ArithTerm} {s : Nat → Nat}
    (h : (sListTail x b).natEval s) :
    (x.natValue s = 0 ∧ b.natValue s = 0) ∨
    ∃ a p, 2 * p = (a + b.natValue s) * (a + b.natValue s + 1) + 2 * b.natValue s ∧ x.natValue s = p + 1 := by
  rcases h with ⟨hx, hb⟩ | ⟨a, hcons⟩
  · exact Or.inl ⟨hx, hb⟩
  · obtain ⟨p, hc, heq⟩ := natEval_sListCons_eq hcons
    simp only [ArithTerm.natValue, natValue_shiftTerm 1 _ s (pushValue s a) (fun _ => rfl), pushValue] at hc heq
    exact Or.inr ⟨a, p, hc, heq⟩

theorem listHead_nat_unique {x a₁ a₂ : Nat}
    (h1 : (x = 0 ∧ a₁ = 0) ∨ ∃ b p, 2 * p = (a₁ + b) * (a₁ + b + 1) + 2 * b ∧ x = p + 1)
    (h2 : (x = 0 ∧ a₂ = 0) ∨ ∃ b p, 2 * p = (a₂ + b) * (a₂ + b + 1) + 2 * b ∧ x = p + 1) :
    a₁ = a₂ := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨b1, p1, hc1, hx1⟩
  · rcases h2 with ⟨_, rfl⟩ | ⟨_, _, _, hx2⟩
    · rfl
    · omega
  · rcases h2 with ⟨hx0, _⟩ | ⟨b2, p2, hc2, hx2⟩
    · omega
    · have hp : p1 = p2 := by omega
      subst hp
      exact (cantor_inj hc1 hc2).1

theorem listTail_nat_unique {x b₁ b₂ : Nat}
    (h1 : (x = 0 ∧ b₁ = 0) ∨ ∃ a p, 2 * p = (a + b₁) * (a + b₁ + 1) + 2 * b₁ ∧ x = p + 1)
    (h2 : (x = 0 ∧ b₂ = 0) ∨ ∃ a p, 2 * p = (a + b₂) * (a + b₂ + 1) + 2 * b₂ ∧ x = p + 1) :
    b₁ = b₂ := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨a1, p1, hc1, hx1⟩
  · rcases h2 with ⟨_, rfl⟩ | ⟨_, _, _, hx2⟩
    · rfl
    · omega
  · rcases h2 with ⟨hx0, _⟩ | ⟨a2, p2, hc2, hx2⟩
    · omega
    · have hp : p1 = p2 := by omega
      subst hp
      exact (cantor_inj hc1 hc2).2

theorem natEval_sNumericConfCode_eq {sq sl sr code : ArithTerm} {s : Nat → Nat}
    (h : (sNumericConfCode sq sl sr code).natEval s) :
    code.natValue s = confCodeN (sq.natValue s, sl.natValue s, sr.natValue s) := by
  rcases h with ⟨lr, h1, h2⟩
  have h1' := natEval_sCantor_eq h1
  have h2' := natEval_sCantor_eq h2
  simp only [ArithTerm.natValue, natValue_shiftTerm 1 _ s (pushValue s lr) (fun _ => rfl), pushValue] at h1' h2'
  have hlr : lr = cantorN (sl.natValue s) (sr.natValue s) := cantor_eq_of_formula h1'
  rw [hlr] at h2'
  exact cantor_eq_of_formula h2'

theorem confCodeN_inj {c₁ c₂ : Nat × Nat × Nat} (h : confCodeN c₁ = confCodeN c₂) : c₁ = c₂ := by
  rcases c₁ with ⟨q1, l1, r1⟩
  rcases c₂ with ⟨q2, l2, r2⟩
  have hEven : ∀ a b, 2 * cantorN a b = (a + b) * (a + b + 1) + 2 * b := by
    intro a b
    unfold cantorN
    have hdiv : ∃ k, (a + b) * (a + b + 1) = 2 * k := by
      rcases Nat.mod_two_eq_zero_or_one (a + b) with h2 | h2
      · refine ⟨((a + b) / 2) * (a + b + 1), ?_⟩
        rw [← Nat.mul_assoc]; congr 1; omega
      · refine ⟨(a + b) * ((a + b) / 2 + 1), ?_⟩
        rw [Nat.mul_comm 2, Nat.mul_assoc]; congr 1; omega
    rcases hdiv with ⟨k, hk⟩
    omega
  have hc1 := hEven q1 (cantorN l1 r1)
  have hc2 := hEven q2 (cantorN l2 r2)
  change cantorN q1 (cantorN l1 r1) = cantorN q2 (cantorN l2 r2) at h
  rw [← h] at hc2
  have ⟨hq, hlr⟩ := cantor_inj hc1 hc2
  have hl1 := hEven l1 r1
  have hl2 := hEven l2 r2
  rw [← hlr] at hl2
  have ⟨hl, hr⟩ := cantor_inj hl1 hl2
  rw [hq, hl, hr]

theorem natEval_sStep_eq {sq sl sr tq tl tr : ArithTerm} {s : Nat → Nat}
    (h : (sStep sq sl sr tq tl tr).natEval s) :
    (tq.natValue s, tl.natValue s, tr.natValue s) =
      stepPhysical (sq.natValue s, sl.natValue s, sr.natValue s) := by
  obtain ⟨q, hqeq, hbr⟩ := (natEval_sAnyFin 207 _ s).mp h
  have hq : sq.natValue s = q.val := by
    simpa [sEq, SigmaFormula.natEval, natValue_sNum] using hqeq
  have hBranch : ∀ (read : Bool), (sRowBranch q.val read sl sr tq tl tr).natEval s →
      (tq.natValue s, tl.natValue s, tr.natValue s) =
        stepPhysical (sq.natValue s, sl.natValue s, sr.natValue s) := by
    intro read hrb
    unfold sRowBranch at hrb
    cases hrow : (if read then (literalRows.getD q.val (none, none)).2
                  else (literalRows.getD q.val (none, none)).1) with
    | none =>
      rw [hrow] at hrb
      exact False.elim (hrb rfl)
    | some entry =>
      rcases entry with ⟨write, dir, nxt⟩
      rw [hrow] at hrb
      rcases hrb with ⟨r, hreadBit, hnext, hrest⟩
      simp only [sBitCons, sEq, SigmaFormula.natEval, ArithTerm.natValue,
                 natValue_shift1, natValue_sNum, pushValue, ↓reduceIte] at hreadBit hnext
      have hread_eq : (sr.natValue s % 2 == 1) = read := by
        cases read <;> simp [ArithTerm.natValue] at hreadBit ⊢ <;> omega
      have hr_eq : sr.natValue s / 2 = r := by
        cases read <;> simp [ArithTerm.natValue] at hreadBit <;> omega
      unfold stepPhysical
      dsimp only
      rw [hq, hread_eq, hr_eq, hrow]
      cases dir
      · rcases hrest with ⟨l, mid, hbitBranch⟩
        have hLeft : ∀ bit : Bool, (sMoveLeftBit write bit sl tl tr).natEval (pushValue (pushValue (pushValue s r) l) mid) →
            (tq.natValue s, tl.natValue s, tr.natValue s) =
              (nxt, sl.natValue s / 2, sl.natValue s % 2 + 2 * ((if write then 1 else 0) + 2 * r)) := by
          intro bit ⟨h1, h2, h3, h4⟩
          simp only [sBitCons, sEq, SigmaFormula.natEval, ArithTerm.natValue,
                     natValue_shift3, natValue_sNum, pushValue, ↓reduceIte] at h1 h2 h3 h4
          have hbit_eq : sl.natValue s % 2 = if bit then 1 else 0 := by
            cases bit <;> simp [ArithTerm.natValue] at h1 ⊢ <;> omega
          have hl_eq : sl.natValue s / 2 = l := by
            cases bit <;> simp [ArithTerm.natValue] at h1 <;> omega
          rw [hnext, h2, ← hl_eq, h4, h3, hbit_eq]
          cases bit <;> cases write <;> rfl
        cases hbitBranch with
        | inl hf => exact hLeft false hf
        | inr ht => exact hLeft true ht
      · rcases hrest with ⟨hleft, htr⟩
        simp only [sBitCons, sEq, SigmaFormula.natEval, ArithTerm.natValue,
                   natValue_shift1, natValue_sNum, pushValue, ↓reduceIte] at hleft htr
        rw [hnext, hleft, htr]
        cases write <;> rfl
  cases hbr with
  | inl hf => exact hBranch false hf
  | inr ht => exact hBranch true ht

theorem sHalts207_natEval_implies_physicalHalts (h : sHalts207.natEval (fun _ => 0)) :
    PhysicalHalts207 := by
  rcases h with ⟨hist, last, tq, tl, tr, ⟨hhist_ne, c, d, hb0, hbc, hforall⟩, hhd_hist, hcode_last, hterm⟩
  have hhist_pos : hist ≠ 0 := hhist_ne
  have hb0' : hist = c % ((0 + 1) * d + 1) := by
    simpa [ArithTerm.natValue, shiftTerm, pushValue] using natEval_sBeta_eq hb0
  have hbc' : 0 = c % ((hist + 1) * d + 1) := by
    simpa [ArithTerm.natValue, shiftTerm, pushValue] using natEval_sBeta_eq hbc
  have hcode_eq : last = confCodeN (tq, tl, tr) := natEval_sNumericConfCode_eq hcode_last
  have htq_ge : tq ≥ 207 := by
    have : ¬ (tq < 207) := by
      simpa [sTerminal, sGe, SigmaFormula.natEval, ArithTerm.natValue, natValue_sNum, pushValue] using hterm
    omega
  -- Downward induction on k ≤ hist: β(c, d, hist - k) is either 0 or has head = confCodeN (iterPhysical n (0, 0, 0))
  have hDown : ∀ k, k ≤ hist →
      let x := c % ((hist - k + 1) * d + 1)
      x = 0 ∨ ∃ n, (x = 0 ∧ confCodeN (iterPhysical n (0, 0, 0)) = 0) ∨
        ∃ b p, 2 * p = (confCodeN (iterPhysical n (0, 0, 0)) + b) * (confCodeN (iterPhysical n (0, 0, 0)) + b + 1) + 2 * b ∧ x = p + 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      left
      simpa using hbc'.symm
    | succ k ih =>
      intro hk
      let i := hist - (k + 1)
      have hi_lt : i < hist := by omega
      have hsi : i + 1 = hist - k := by omega
      rcases hforall i hi_lt with ⟨x, y, hbx, hby, htail, hedge⟩
      have hx_eq : x = c % ((i + 1) * d + 1) := natEval_sBeta_eq hbx
      have hy_eq : y = c % ((hist - k + 1) * d + 1) := by
        have := natEval_sBeta_eq hby
        simpa [ArithTerm.natValue, pushValue, hsi] using this
      have htail' := natEval_sListTail_eq htail
      dsimp only [ArithTerm.natValue, pushValue] at htail'
      show c % ((i + 1) * d + 1) = 0 ∨ _
      rw [← hx_eq]
      cases hedge with
      | inl hx0 => exact Or.inl hx0
      | inr hstepEdge =>
        rcases hstepEdge with ⟨a, b, hhd_x, htl_x, hre⟩
        have hhd_x' := natEval_sListHead_eq hhd_x
        have htl_x' := natEval_sListTail_eq htl_x
        dsimp only [ArithTerm.natValue, pushValue] at hhd_x' htl_x'
        have hby_eq : b = y := listTail_nat_unique htl_x' htail'
        subst hby_eq
        cases hre with
        | inl hinit =>
          rcases hinit with ⟨hb0'', ha0⟩
          simp only [sEq, SigmaFormula.natEval, ArithTerm.natValue, shiftTerm, pushValue, ↓reduceIte] at hb0'' ha0
          have h0code : confCodeN (iterPhysical 0 (0, 0, 0)) = 0 := rfl
          rw [ha0, ← h0code] at hhd_x'
          exact Or.inr ⟨0, hhd_x'⟩
        | inr hprevEdge =>
          rcases hprevEdge with ⟨hb_ne, prev, hhd_b, hnumstep⟩
          simp only [sNe, SigmaFormula.natEval, ArithTerm.natValue, pushValue, ↓reduceIte] at hb_ne
          have hhd_b' := natEval_sListHead_eq hhd_b
          dsimp only [ArithTerm.natValue, pushValue] at hhd_b'
          rcases ih (by omega) with hb0'' | ⟨n, hhd_n⟩
          · rw [← hy_eq] at hb0''
            exact False.elim (hb_ne hb0'')
          · rw [← hy_eq] at hhd_n
            have hprev_eq : prev = confCodeN (iterPhysical n (0, 0, 0)) :=
              listHead_nat_unique hhd_b' hhd_n
            rcases hnumstep with ⟨sq, sl, sr, tq', tl', tr', hc1, hc2, hst⟩
            have hc1' := natEval_sNumericConfCode_eq hc1
            have hc2' := natEval_sNumericConfCode_eq hc2
            have hst' := natEval_sStep_eq hst
            simp only [ArithTerm.natValue, natValue_shift6, natValue_shift1, pushValue] at hc1' hc2' hst'
            have hs_eq : (sq, sl, sr) = iterPhysical n (0, 0, 0) :=
              confCodeN_inj (hc1'.symm.trans hprev_eq)
            have ht_eq : (tq', tl', tr') = iterPhysical (n + 1) (0, 0, 0) := by
              have hiter : ∀ m c, iterPhysical (m + 1) c = stepPhysical (iterPhysical m c) := by
                intro m
                induction m with
                | zero => intro _; rfl
                | succ m ihm => intro c; exact ihm (stepPhysical c)
              rw [hiter, ← hs_eq, ← hst']
            rw [ht_eq] at hc2'
            rw [hc2'] at hhd_x'
            exact Or.inr ⟨n + 1, hhd_x'⟩
  rcases hDown hist (Nat.le_refl hist) with h0 | ⟨n, hhd_n⟩
  · have : hist = 0 := by
      have h1 : hist - hist = 0 := Nat.sub_self hist
      rw [h1] at h0
      exact hb0'.trans h0
    exact False.elim (hhist_pos this)
  · have h1 : hist - hist = 0 := Nat.sub_self hist
    rw [h1, ← hb0'] at hhd_n
    have hhd_hist' := natEval_sListHead_eq hhd_hist
    dsimp only [ArithTerm.natValue, pushValue] at hhd_hist'
    have hlast_eq : last = confCodeN (iterPhysical n (0, 0, 0)) :=
      listHead_nat_unique hhd_hist' hhd_n
    have hconf_eq : (tq, tl, tr) = iterPhysical n (0, 0, 0) :=
      confCodeN_inj (hcode_eq.symm.trans hlast_eq)
    exact ⟨n, by rw [← hconf_eq]; exact htq_ge⟩

theorem sigma1_bridge_physicalHalts (H : Formula) (hH : Represents207 H) :
    ArithmeticSigma1Sound → Provable H → PhysicalHalts207 := by
  intro hSound hProv
  have hRep := sHalts207_represents H hH
  have hNat := hSound sHalts207 sHalts207_bound H hRep hProv (fun _ => 0)
  exact sHalts207_natEval_implies_physicalHalts hNat

end SigmaBridgeDev

theorem solution (H : Formula) (hH : Represents207 H) :
    ArithmeticSigma1Sound → Provable H → PhysicalHalts207 :=
  SigmaBridgeDev.sigma1_bridge_physicalHalts H hH
