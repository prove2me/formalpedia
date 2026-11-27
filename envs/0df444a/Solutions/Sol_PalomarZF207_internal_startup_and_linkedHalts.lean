-- Prove2me | solution 1 for PalomarZF207.internal_startup_and_linkedHalts
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-27T03:50:42.925835+00:00
-- url     : https://prove2.me/submissions/45a0cce6-b9e9-4954-83b9-1213dc0a1a32

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_physical
import Definitions.Def_palomar_zf207_calc
import Definitions.Def_palomar_zf207_tm_check
import Definitions.Def_palomar_zf207_internal_prov
import Definitions.Def_palomar_zf207_internal_tm

open PalomarZF207
open PalomarZF207History
open PalomarZF207Calc
open PalomarZF207TMCheck
open PalomarZF207Internal
open PalomarZF207InternalTM

namespace SolInternalStartup

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

private theorem ax_rep (hM : Model E) (hNE : Nonempty V) (n : Nat) (phi : Formula)
    (hB : Bound phi (n + 2)) (env : Nat → V)
    (hFunc : ∀ x y₁ y₂, eval E phi (pushValue (pushValue env y₁) x) →
      eval E phi (pushValue (pushValue env y₂) x) → y₁ = y₂)
    (dom : V) :
    ∃ img, ∀ y, E y img ↔ ∃ x, E x dom ∧ eval E phi (pushValue (pushValue env y) x) := by
  have hAx : Axiom (replacementSchema n phi) := Or.inr (Or.inr ⟨n, phi, hB, rfl⟩)
  let s₀ : Nat → V := fun _ => Classical.choice hNE
  have hRep := eval_allPrefix E n
    (replacementFormula (rename repAIndex phi) (rename repBIndex phi) (rename repCIndex phi)) s₀
    (mkParams env n) (mkParams_length env n) (hM (replacementSchema n phi) hAx s₀)
  have hF : eval E (functionalityFormula (rename repAIndex phi) (rename repBIndex phi))
      (pushParams s₀ (mkParams env n)) := by
    intro x y₁ y₂ h1 h2
    have h1' : eval E phi (pushValue (pushValue env y₁) x) := by
      rw [eval_rename] at h1
      exact (eval_congr_bound E phi (n + 2) _ _ hB (fun i hi => by
        match i with
        | 0 => rfl
        | 1 => rfl
        | k + 2 =>
          show pushValue (pushValue (pushValue (pushParams s₀ (mkParams env n)) x) y₁) y₂ (k + 3) = env k
          exact pushParams_mkParams_lt env s₀ n k (by omega))).mp h1
    have h2' : eval E phi (pushValue (pushValue env y₂) x) := by
      rw [eval_rename] at h2
      exact (eval_congr_bound E phi (n + 2) _ _ hB (fun i hi => by
        match i with
        | 0 => rfl
        | 1 => rfl
        | k + 2 =>
          show pushValue (pushValue (pushValue (pushParams s₀ (mkParams env n)) x) y₁) y₂ (k + 3) = env k
          exact pushParams_mkParams_lt env s₀ n k (by omega))).mp h2
    exact hFunc x y₁ y₂ h1' h2'
  obtain ⟨img, himg⟩ := hRep hF dom
  refine ⟨img, fun y => ?_⟩
  have hEq : ∀ x, eval E (rename repCIndex phi)
      (pushValue (pushValue (pushValue (pushValue (pushParams s₀ (mkParams env n)) dom) img) y) x) ↔
      eval E phi (pushValue (pushValue env y) x) := by
    intro x
    rw [eval_rename]
    apply eval_congr_bound E phi (n + 2) _ _ hB
    intro i hi
    match i with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      show pushValue (pushValue (pushValue (pushValue (pushParams s₀ (mkParams env n)) dom) img) y) x (k + 4) = env k
      exact pushParams_mkParams_lt env s₀ n k (by omega)
  constructor
  · intro hy
    obtain ⟨x, hxd, hpx⟩ := (himg y).1 hy
    exact ⟨x, hxd, (hEq x).mp hpx⟩
  · rintro ⟨x, hxd, hpx⟩
    exact (himg y).2 ⟨x, hxd, (hEq x).mpr hpx⟩

private theorem empty_unique (hM : Model E) (hNE : Nonempty V) {a b : V}
    (ha : Empty E a) (hb : Empty E b) : a = b :=
  ax_ext hM hNE (fun z hz => False.elim (ha z hz)) (fun z hz => False.elim (hb z hz))

private theorem succ_unique (hM : Model E) (hNE : Nonempty V) {a b₁ b₂ : V}
    (h1 : Succ E a b₁) (h2 : Succ E a b₂) : b₁ = b₂ :=
  ax_ext hM hNE (fun z hz => (h2 z).mpr ((h1 z).mp hz)) (fun z hz => (h1 z).mpr ((h2 z).mp hz))

private theorem pair_unique (hM : Model E) (hNE : Nonempty V) {a b p₁ p₂ : V}
    (h1 : Pair E a b p₁) (h2 : Pair E a b p₂) : p₁ = p₂ :=
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

private theorem orderedPair_unique (hM : Model E) (hNE : Nonempty V) {a b p₁ p₂ : V}
    (h1 : OrderedPair E a b p₁) (h2 : OrderedPair E a b p₂) : p₁ = p₂ := by
  rcases h1 with ⟨aa1, ab1, haa1, hab1, hp1⟩
  rcases h2 with ⟨aa2, ab2, haa2, hab2, hp2⟩
  have := pair_unique hM hNE haa1 haa2; subst this
  have := pair_unique hM hNE hab1 hab2; subst this
  exact pair_unique hM hNE hp1 hp2

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

/-! ### Syntactic Formula Builders -/

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
private def fListCons (a b c : Nat) : Formula :=
  .ex (.and (fCantor (a + 1) (b + 1) 0) (fSucc 0 (c + 1)))

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
private theorem bound_fListCons {a b c n : Nat} (ha : a < n) (hb : b < n) (hc : c < n) : Bound (fListCons a b c) n :=
  ⟨bound_fCantor (by omega) (by omega) (by omega), bound_fSucc (by omega) (by omega)⟩

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
  | k + 1, x, s =>
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
private theorem eval_fListCons (a b c : Nat) (s : Nat → V) : eval E (fListCons a b c) s ↔ ListCons E (s a) (s b) (s c) :=
  ⟨fun ⟨p, h1, h2⟩ => ⟨p, (eval_fCantor _ _ _ _).mp h1, (eval_fSucc _ _ _).mp h2⟩,
   fun ⟨p, h1, h2⟩ => ⟨p, (eval_fCantor _ _ _ _).mpr h1, (eval_fSucc _ _ _).mpr h2⟩⟩

/-! ### Order, FunctionOn, Add, Mul, Sub, Cantor on ω -/

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
    (fun x y hx hxy ih u hu => by
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
    (fun z z' _ hzz' ih x y hxy hyz' => by
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
    (fun y y' _ hyy' ih => by
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
    (fun y y' hy hyy' ih => by
      dsimp only [body, eval, pushValue] at ih ⊢
      rcases ih with hxy | hxy | hyx
      · exact Or.inl ((hyy' x).mpr (Or.inl hxy))
      · exact Or.inl ((hyy' x).mpr (Or.inr hxy))
      · rcases (nat_succ_le_iff hM hNE hy hyy' x hx).mp hyx with hy'x | hy'x
        · exact Or.inr (Or.inl hy'x.symm)
        · exact Or.inr (Or.inr hy'x))

private theorem succ_inj (hM : Model E) (hNE : Nonempty V) {x y z : V}
    (hx : NatObject E x) (hy : NatObject E y) (hxz : Succ E x z) (hyz : Succ E y z) : x = y := by
  rcases nat_trichotomy hM hNE x hx y hy with hxy | hxy | hyx
  · rcases (hxz y).mp ((hyz y).mpr (Or.inr rfl)) with hyx | hyx
    · exact False.elim (mem_asymm hM hNE hxy hyx)
    · exact False.elim (mem_irrefl hM hNE x (hyx ▸ hxy))
  · exact hxy
  · rcases (hyz x).mp ((hxz x).mpr (Or.inr rfl)) with hxy | hxy
    · exact False.elim (mem_asymm hM hNE hyx hxy)
    · exact False.elim (mem_irrefl hM hNE y (hxy ▸ hyx))

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
    (fun b b' _ hbb' ⟨c, hc⟩ => by
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
    (fun i j hi hij ih hjd x y hx hy => by
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
    (fun b b' _ hbb' ⟨c, hc⟩ => by
      have hm := (eval_fMul _ _ _ _).mp hc
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
    (fun i j hi hij ih hjd x y hx hy => by
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

private theorem mulV_numV (hM : Model E) (hNE : Nonempty V) (a : Nat) :
    ∀ b, mulV hM hNE (numV hM hNE a) (numV hM hNE b) = numV hM hNE (a * b)
  | 0 => by simpa [numV] using mulV_zero hM hNE (numV_nat hM hNE a)
  | b + 1 => by
    rw [show numV hM hNE (b + 1) = succV hM hNE (numV hM hNE b) from rfl,
      mulV_succ hM hNE (numV_nat hM hNE a) (numV_nat hM hNE b),
      mulV_numV hM hNE a b, addV_numV hM hNE (a * b) a, Nat.mul_succ]

private theorem addV_le_left (hM : Model E) (hNE : Nonempty V) {a : V} (ha : NatObject E a) :
    ∀ b, NatObject E b → (a = addV hM hNE a b ∨ E a (addV hM hNE a b)) := by
  let body : Formula := .ex (.and (fAdd 2 1 0) (.or (.eq 2 0) (.mem 2 0)))
  have h := omega_induction hM hNE 1 body
    ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩ (fun _ => a)
    (fun z hz => ⟨a, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE ha hz), Or.inl rfl⟩)
    (fun b b' _ hbb' ⟨c, hc, hle⟩ => by
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
    (fun x y _ hxy ih => by
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
    (fun b b' _ hbb' ⟨c, c', h1, h2, h3⟩ => by
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
  have h1' : Add E a b c := (eval_fAdd _ _ _ _).mp h1
  have h2' : Add E b a c := (eval_fAdd _ _ _ _).mp h2
  exact ((add_iff_eq hM hNE ha hb).mp h1').symm.trans ((add_iff_eq hM hNE hb ha).mp h2')

private theorem addV_assoc (hM : Model E) (hNE : Nonempty V) {a b : V} (ha : NatObject E a) (hb : NatObject E b) :
    ∀ c, NatObject E c → addV hM hNE (addV hM hNE a b) c = addV hM hNE a (addV hM hNE b c) := by
  let body : Formula := .ex (.ex (.and (fAdd 4 2 1) (.and (fAdd 3 1 0) (fAdd 5 2 0))))
  let env : Nat → V := fun i => if i = 0 then a else if i = 1 then b else addV hM hNE a b
  have h := omega_induction hM hNE 3 body
    ⟨bound_fAdd (by omega) (by omega) (by omega), ⟨bound_fAdd (by omega) (by omega) (by omega), bound_fAdd (by omega) (by omega) (by omega)⟩⟩ env
    (fun z hz => ⟨b, addV hM hNE a b, (eval_fAdd _ _ _ _).mpr (add_zero hM hNE hb hz),
      (eval_fAdd _ _ _ _).mpr (addV_spec hM hNE ha hb),
      (eval_fAdd _ _ _ _).mpr (add_zero hM hNE (addV_nat hM hNE ha hb) hz)⟩)
    (fun c c' _ hcc' ⟨bc, abc, h1, h2, h3⟩ => by
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

private theorem addV_cancel_left (hM : Model E) (hNE : Nonempty V) {a b c : V}
    (ha : NatObject E a) (hb : NatObject E b) (hc : NatObject E c)
    (heq : addV hM hNE a b = addV hM hNE a c) : b = c := by
  rcases nat_trichotomy hM hNE b hb c hc with hbc | rfl | hcb
  · exact False.elim (mem_irrefl hM hNE _ (heq ▸ addV_lt_addV_left hM hNE ha c hc b hb hbc))
  · rfl
  · exact False.elim (mem_irrefl hM hNE _ (heq.symm ▸ addV_lt_addV_left hM hNE ha b hb c hc hcb))

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
    (fun b b' _ hbb' ih hle => by
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
  have hm0 : Mul E (numV hM hNE 2) a m := (eval_fMul _ _ _ _).mp hm
  have ha0 : Add E a a m := (eval_fAdd _ _ _ _).mp ha2
  exact ((mul_iff_eq hM hNE (numV_nat hM hNE 2) ha).mp hm0).symm.trans ((add_iff_eq hM hNE ha ha).mp ha0)

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
      have hstep_mul : ∀ x, NatObject E x →
          mulV hM hNE (succV hM hNE s) x = addV hM hNE (mulV hM hNE s x) x := by
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
      have hcalc : mulV hM hNE (numV hM hNE 2) (addV hM hNE q (succV hM hNE s)) =
          mulV hM hNE (succV hM hNE s) (succV hM hNE (succV hM hNE s)) := by
        rw [addV_left_distrib hM hNE (numV_nat hM hNE 2) hqNat (succV hM hNE s) hs1Nat,
          ← h2q', hsp', two_mulV_eq_addV hM hNE hs1Nat,
          mulV_succ hM hNE hs1Nat hs1Nat, hstep_mul (succV hM hNE s) hs1Nat,
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
  have h2q0 : Mul E (numV hM hNE 2) q p := (eval_fMul _ _ _ _).mp h2q
  have hsp0 : Mul E s (succV hM hNE s) p := (eval_fMul _ _ _ _).mp hsp
  exact ⟨q, hqNat, ((mul_iff_eq hM hNE (numV_nat hM hNE 2) hqNat).mp h2q0).symm.trans
    ((mul_iff_eq hM hNE hs (succV_nat hM hNE hs)).mp hsp0)⟩

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

private theorem cantor_le_right (hM : Model E) (hNE : Nonempty V) {a b p : V}
    (hc : Cantor E a b p) : b = p ∨ E b p := by
  rcases hc with ⟨ha, hb, hp, two, sum, next, prod, tb, tz, tot, h2, hadd, hs, hm1, hm2, hm3, ha2, heq⟩
  have h2eq := numeral_unique hM hNE h2 (numV_numeral hM hNE 2); subst h2eq
  obtain ⟨p', hc', hbp'⟩ := cantor_exists hM hNE ha hb
  rcases hc' with ⟨_, _, hp', two', sum', next', prod', tb', tz', tot', h2', hadd', hs', hm1', hm2', hm3', ha2', heq'⟩
  have := numeral_unique hM hNE h2' (numV_numeral hM hNE 2); subst this
  have := add_unique hM hNE hadd hadd'; subst this
  have := succ_unique hM hNE hs hs'; subst this
  have := mul_unique hM hNE hm1 hm1'; subst this
  have := mul_unique hM hNE hm2 hm2'; subst this
  have := add_unique hM hNE ha2 ha2'; subst this
  have htz : tz = tz' := heq.trans heq'.symm
  subst htz
  have hm3eq := (mul_iff_eq hM hNE (numV_nat hM hNE 2) hp).mp hm3
  have hm3'eq := (mul_iff_eq hM hNE (numV_nat hM hNE 2) hp').mp hm3'
  have hpp' : p = p' := by
    rcases nat_trichotomy hM hNE p hp p' hp' with hlt | rfl | hgt
    · have h2lt : E (mulV hM hNE (numV hM hNE 2) p) (mulV hM hNE (numV hM hNE 2) p') := by
        rw [two_mulV_eq_addV hM hNE hp, two_mulV_eq_addV hM hNE hp']
        have h1 := addV_lt_addV_left hM hNE hp p' hp' p hp hlt
        have h2 := addV_lt_addV_left hM hNE hp' p' hp' p hp hlt
        rw [addV_comm hM hNE hp' p hp] at h2
        exact nat_lt_trans hM hNE _ (addV_nat hM hNE hp' hp') _ _ h1 h2
      exact False.elim (mem_irrefl hM hNE _ (hm3eq ▸ hm3'eq ▸ h2lt))
    · rfl
    · have h2lt : E (mulV hM hNE (numV hM hNE 2) p') (mulV hM hNE (numV hM hNE 2) p) := by
        rw [two_mulV_eq_addV hM hNE hp, two_mulV_eq_addV hM hNE hp']
        have h1 := addV_lt_addV_left hM hNE hp' p hp p' hp' hgt
        have h2 := addV_lt_addV_left hM hNE hp p hp p' hp' hgt
        rw [addV_comm hM hNE hp p' hp'] at h2
        exact nat_lt_trans hM hNE _ (addV_nat hM hNE hp hp) _ _ h1 h2
      exact False.elim (mem_irrefl hM hNE _ (hm3eq ▸ hm3'eq ▸ h2lt))
  rwa [hpp']

private theorem cantor_numV (hM : Model E) (hNE : Nonempty V) (a b : Nat) :
    Cantor E (numV hM hNE a) (numV hM hNE b) (numV hM hNE (cantor a b)) := by
  have h2eq : 2 * cantor a b = (a + b) * (a + b + 1) + 2 * b := by
    unfold cantor
    have heven : 2 ∣ (a + b) * (a + b + 1) := by
      have hmod : (a + b) % 2 = 0 ∨ (a + b) % 2 = 1 := by omega
      rcases hmod with h | h
      · refine ⟨(a + b) / 2 * (a + b + 1), ?_⟩
        have h1 : a + b = 2 * ((a + b) / 2) := by omega
        calc (a + b) * (a + b + 1) = (2 * ((a + b) / 2)) * (a + b + 1) := by rw [← h1]
          _ = 2 * ((a + b) / 2 * (a + b + 1)) := Nat.mul_assoc 2 ((a + b) / 2) (a + b + 1)
      · refine ⟨(a + b) * ((a + b + 1) / 2), ?_⟩
        have h1 : a + b + 1 = 2 * ((a + b + 1) / 2) := by omega
        calc (a + b) * (a + b + 1) = (a + b) * (2 * ((a + b + 1) / 2)) := by rw [← h1]
          _ = 2 * ((a + b) * ((a + b + 1) / 2)) := (Nat.mul_left_comm 2 (a + b) ((a + b + 1) / 2)).symm
    obtain ⟨q, hq⟩ := heven
    rw [hq]; omega
  refine ⟨numV_nat hM hNE a, numV_nat hM hNE b, numV_nat hM hNE (cantor a b),
    numV hM hNE 2, numV hM hNE (a + b), numV hM hNE (a + b + 1),
    numV hM hNE ((a + b) * (a + b + 1)), numV hM hNE (2 * b),
    numV hM hNE (2 * cantor a b), numV hM hNE ((a + b) * (a + b + 1) + 2 * b),
    numV_numeral hM hNE 2,
    (add_iff_eq hM hNE (numV_nat hM hNE a) (numV_nat hM hNE b)).mpr (addV_numV hM hNE a b).symm,
    succV_spec hM hNE _,
    (mul_iff_eq hM hNE (numV_nat hM hNE (a + b)) (numV_nat hM hNE (a + b + 1))).mpr (mulV_numV hM hNE _ _).symm,
    (mul_iff_eq hM hNE (numV_nat hM hNE 2) (numV_nat hM hNE b)).mpr (mulV_numV hM hNE 2 b).symm,
    (mul_iff_eq hM hNE (numV_nat hM hNE 2) (numV_nat hM hNE (cantor a b))).mpr (mulV_numV hM hNE 2 _).symm,
    (add_iff_eq hM hNE (numV_nat hM hNE _) (numV_nat hM hNE _)).mpr (addV_numV hM hNE _ _).symm,
    congrArg (numV hM hNE) h2eq⟩

/-! ### Part 2: Transitivity of InternalReach (via Replacement + Binary Union) -/

private theorem internalReach_trans (hM : Model E) (hNE : Nonempty V) {c1 c2 c3 : V}
    (h1 : InternalReach E c1 c2) (h2 : InternalReach E c2 c3) : InternalReach E c1 c3 := by
  rcases h1 with ⟨n1, hn1, hc1, hc2, z1, dom1, f1, hz1, hdom1, hfun1, hf10, hf1n, hnat1, hstep1⟩
  rcases h2 with ⟨n2, hn2, _, hc3, z2, dom2, f2, hz2, hdom2, hfun2, hf20, hf2n, hnat2, hstep2⟩
  have := empty_unique hM hNE hz1 hz2; subst this
  let n := addV hM hNE n1 n2
  have hn := addV_nat hM hNE hn1 hn2
  obtain ⟨dom, hdom⟩ := exists_succ hM hNE n
  -- Shift f2 by n1 using Replacement: p = ⟨j, y⟩ ↦ ⟨n1 + j, y⟩
  let phi : Formula := .ex (.ex (.ex (.and (fOrderedPair 2 1 3) (.and (fAdd 5 2 0) (fOrderedPair 0 1 4)))))
  have hB : Bound phi 3 :=
    ⟨bound_fOrderedPair (by omega) (by omega) (by omega),
     ⟨bound_fAdd (by omega) (by omega) (by omega), bound_fOrderedPair (by omega) (by omega) (by omega)⟩⟩
  have hFunc : ∀ p q1 q2, eval E phi (pushValue (pushValue (fun _ => n1) q1) p) →
      eval E phi (pushValue (pushValue (fun _ => n1) q2) p) → q1 = q2 := by
    rintro p q1 q2 ⟨j1, y1, k1, hp1, ha1, hq1⟩ ⟨j2, y2, k2, hp2, ha2, hq2⟩
    have hp1' : OrderedPair E j1 y1 p := (eval_fOrderedPair _ _ _ _).mp hp1
    have hp2' : OrderedPair E j2 y2 p := (eval_fOrderedPair _ _ _ _).mp hp2
    have ⟨hj, hy⟩ := orderedPair_inj hp1' hp2'
    subst hj; subst hy
    have ha1' : Add E n1 j1 k1 := (eval_fAdd _ _ _ _).mp ha1
    have ha2' : Add E n1 j1 k2 := (eval_fAdd _ _ _ _).mp ha2
    have hk := add_unique hM hNE ha1' ha2'
    subst hk
    have hq1' : OrderedPair E k1 y1 q1 := (eval_fOrderedPair _ _ _ _).mp hq1
    have hq2' : OrderedPair E k1 y1 q2 := (eval_fOrderedPair _ _ _ _).mp hq2
    exact orderedPair_unique hM hNE hq1' hq2'
  obtain ⟨f2s, hf2s⟩ := ax_rep hM hNE 1 phi hB (fun _ => n1) hFunc f2
  obtain ⟨f, hf⟩ := exists_binUnion hM hNE f1 f2s
  have hAt_f2s : ∀ k y, At E f2s k y ↔ ∃ j, E j dom2 ∧ Add E n1 j k ∧ At E f2 j y := by
    intro k y
    constructor
    · rintro ⟨q, hqf2s, hq⟩
      obtain ⟨p, hpf2, j, y', k', hp, ha, hq'⟩ := (hf2s q).mp hqf2s
      have ⟨hk, hy⟩ := orderedPair_inj hq ((eval_fOrderedPair _ _ _ _).mp hq')
      subst hk; subst hy
      obtain ⟨u, v, hud2, huv⟩ := hfun2.2 p hpf2
      have ⟨hju, hyv⟩ := orderedPair_inj ((eval_fOrderedPair _ _ _ _).mp hp) huv
      subst hju; subst hyv
      exact ⟨j, hud2, (eval_fAdd _ _ _ _).mp ha, ⟨p, hpf2, huv⟩⟩
    · rintro ⟨j, hjd2, hadd, ⟨p, hpf2, hp⟩⟩
      obtain ⟨q, hq⟩ := exists_orderedPair hM hNE k y
      refine ⟨q, (hf2s q).mpr ⟨p, hpf2, j, y, k, (eval_fOrderedPair _ _ _ _).mpr hp,
        (eval_fAdd _ _ _ _).mpr hadd, (eval_fOrderedPair _ _ _ _).mpr hq⟩, hq⟩
  have hAt_f : ∀ k y, At E f k y ↔ At E f1 k y ∨ ∃ j, E j dom2 ∧ Add E n1 j k ∧ At E f2 j y := by
    intro k y
    constructor
    · rintro ⟨q, hqf, hq⟩
      rcases (hf q).mp hqf with h1' | h2'
      · exact Or.inl ⟨q, h1', hq⟩
      · exact Or.inr ((hAt_f2s k y).mp ⟨q, h2', hq⟩)
    · rintro (⟨q, h1', hq⟩ | h2')
      · exact ⟨q, (hf q).mpr (Or.inl h1'), hq⟩
      · obtain ⟨q, hq2, hq⟩ := (hAt_f2s k y).mpr h2'
        exact ⟨q, (hf q).mpr (Or.inr hq2), hq⟩
  have hdom_mem : ∀ k, E k dom → (E k n1 ∨ k = n1) ∨ (∃ j, E j dom2 ∧ Add E n1 j k) := by
    intro k hk
    have hkNat : NatObject E k := nat_mem_is_nat hM hNE dom (nat_succ hM hNE hn hdom) k hk
    rcases nat_trichotomy hM hNE k hkNat n1 hn1 with hlt | rfl | hgt
    · exact Or.inl (Or.inl hlt)
    · exact Or.inl (Or.inr rfl)
    · obtain ⟨j, hjNat, hadd⟩ := sub_exists hM hNE hn1 k hkNat (Or.inr hgt)
      have hjd2 : E j dom2 := by
        apply (hdom2 j).mpr
        rcases (hdom k).mp hk with hkn | rfl
        · rcases nat_trichotomy hM hNE j hjNat n2 hn2 with hlt' | rfl | hgt'
          · exact Or.inl hlt'
          · exact Or.inr rfl
          · have hk_eq := (add_iff_eq hM hNE hn1 hjNat).mp hadd
            have hlt'' := addV_lt_addV_left hM hNE hn1 j hjNat n2 hn2 hgt'
            exact False.elim (mem_asymm hM hNE hkn (hk_eq ▸ hlt''))
        · have hj_eq := addV_cancel_left hM hNE hn1 hjNat hn2 (((add_iff_eq hM hNE hn1 hjNat).mp hadd).symm)
          exact Or.inr hj_eq
      exact Or.inr ⟨j, hjd2, hadd⟩
  have hfun : FunctionOn E f dom := by
    constructor
    · intro k hk
      rcases hdom_mem k hk with (hkn1 | rfl) | ⟨j, hjd2, hadd⟩
      · have hkd1 : E k dom1 := (hdom1 k).mpr (Or.inl hkn1)
        obtain ⟨y, hy, hu⟩ := hfun1.1 k hkd1
        refine ⟨y, (hAt_f k y).mpr (Or.inl hy), fun w hw => ?_⟩
        rcases (hAt_f k w).mp hw with h1' | ⟨j, hjd2, hadd, _⟩
        · exact hu w h1'
        · have hjNat := nat_mem_is_nat hM hNE dom2 (nat_succ hM hNE hn2 hdom2) j hjd2
          have hle := addV_le_left hM hNE hn1 j hjNat
          have hkeq : k = addV hM hNE n1 j := (add_iff_eq hM hNE hn1 hjNat).mp hadd
          rcases hle with heq | hlt
          · exact False.elim (mem_irrefl hM hNE k (heq.trans hkeq.symm ▸ hkn1))
          · exact False.elim (mem_asymm hM hNE hkn1 (hkeq ▸ hlt))
      · refine ⟨c2, (hAt_f k c2).mpr (Or.inl hf1n), fun w hw => ?_⟩
        rcases (hAt_f k w).mp hw with h1' | ⟨j, hjd2, hadd, h2'⟩
        · exact functionOn_at_unique hfun1 ((hdom1 k).mpr (Or.inr rfl)) h1' hf1n
        · have hjNat := nat_mem_is_nat hM hNE dom2 (nat_succ hM hNE hn2 hdom2) j hjd2
          have hj0 : j = z1 := by
            have h0 := addV_zero hM hNE hn1
            have := addV_cancel_left hM hNE hn1 hjNat (zeroV_nat hM hNE)
              ((((add_iff_eq hM hNE hn1 hjNat).mp hadd).symm).trans h0.symm)
            exact this.trans (empty_unique hM hNE (zeroV_empty hM hNE) hz1)
          subst hj0
          exact functionOn_at_unique hfun2 hjd2 h2' hf20
      · obtain ⟨y, hy, hu⟩ := hfun2.1 j hjd2
        refine ⟨y, (hAt_f k y).mpr (Or.inr ⟨j, hjd2, hadd, hy⟩), fun w hw => ?_⟩
        rcases (hAt_f k w).mp hw with h1' | ⟨j', hjd2', hadd', h2'⟩
        · obtain ⟨q, hqf1, hq⟩ := h1'
          obtain ⟨u, _, hud1, huv⟩ := hfun1.2 q hqf1
          have hku := (orderedPair_inj hq huv).1; subst hku
          have hjNat := nat_mem_is_nat hM hNE dom2 (nat_succ hM hNE hn2 hdom2) j hjd2
          have hkeq : k = addV hM hNE n1 j := (add_iff_eq hM hNE hn1 hjNat).mp hadd
          rcases (hdom1 k).mp hud1 with hkn1 | rfl
          · rcases addV_le_left hM hNE hn1 j hjNat with heq | hlt
            · exact False.elim (mem_irrefl hM hNE k (heq.trans hkeq.symm ▸ hkn1))
            · exact False.elim (mem_asymm hM hNE hkn1 (hkeq ▸ hlt))
          · have hj0 : j = z1 := by
              have h0 := addV_zero hM hNE hn1
              exact (addV_cancel_left hM hNE hn1 hjNat (zeroV_nat hM hNE) (hkeq.symm.trans h0.symm)).trans
                (empty_unique hM hNE (zeroV_empty hM hNE) hz1)
            subst hj0
            have hyc2 : y = c2 := functionOn_at_unique hfun2 hjd2 hy hf20
            rw [hyc2]
            exact functionOn_at_unique hfun1 hud1 ⟨q, hqf1, hq⟩ hf1n
        · have hjNat := nat_mem_is_nat hM hNE dom2 (nat_succ hM hNE hn2 hdom2) j hjd2
          have hj'Nat := nat_mem_is_nat hM hNE dom2 (nat_succ hM hNE hn2 hdom2) j' hjd2'
          have hjj' := addV_cancel_left hM hNE hn1 hjNat hj'Nat
            (((add_iff_eq hM hNE hn1 hjNat).mp hadd).symm.trans ((add_iff_eq hM hNE hn1 hj'Nat).mp hadd'))
          subst hjj'
          exact hu w h2'
    · intro q hqf
      rcases (hf q).mp hqf with h1' | h2'
      · obtain ⟨k, y, hkd1, hq⟩ := hfun1.2 q h1'
        have hkd : E k dom := (hdom k).mpr (by
          rcases addV_le_left hM hNE hn1 n2 hn2 with hn1n | hn1n
          · rcases (hdom1 k).mp hkd1 with hlt | rfl
            · exact Or.inl (by dsimp only [n]; rw [← hn1n]; exact hlt)
            · exact Or.inr hn1n
          · rcases (hdom1 k).mp hkd1 with hlt | rfl
            · exact Or.inl (nat_lt_trans hM hNE n hn k n1 hlt hn1n)
            · exact Or.inl hn1n)
        exact ⟨k, y, hkd, hq⟩
      · obtain ⟨p, hpf2, j, y, k, hp, ha, hq⟩ := (hf2s q).mp h2'
        obtain ⟨u, _, hud2, huv⟩ := hfun2.2 p hpf2
        have hju := (orderedPair_inj ((eval_fOrderedPair _ _ _ _).mp hp) huv).1; subst hju
        have hjNat := nat_mem_is_nat hM hNE dom2 (nat_succ hM hNE hn2 hdom2) j hud2
        have hkeq : k = addV hM hNE n1 j := (add_iff_eq hM hNE hn1 hjNat).mp ((eval_fAdd _ _ _ _).mp ha)
        have hkd : E k dom := (hdom k).mpr (by
          rcases (hdom2 j).mp hud2 with hlt | rfl
          · exact Or.inl (by dsimp only [n]; rw [hkeq]; exact addV_lt_addV_left hM hNE hn1 n2 hn2 j hjNat hlt)
          · exact Or.inr hkeq)
        exact ⟨k, y, hkd, (eval_fOrderedPair _ _ _ _).mp hq⟩
  refine ⟨n, hn, hc1, hc3, z1, dom, f, hz1, hdom, hfun,
    (hAt_f z1 c1).mpr (Or.inl hf10),
    (hAt_f n c3).mpr (Or.inr ⟨n2, (hdom2 n2).mpr (Or.inr rfl), addV_spec hM hNE hn1 hn2, hf2n⟩),
    fun i x _ hfix => ?_, fun i hi => ?_⟩
  · rcases (hAt_f i x).mp hfix with h1' | ⟨j, hjd2, _, h2'⟩
    · obtain ⟨q, hqf1, hq⟩ := h1'; obtain ⟨u, _, hud1, huv⟩ := hfun1.2 q hqf1
      have := (orderedPair_inj hq huv).1; subst this; exact hnat1 i x hud1 ⟨q, hqf1, hq⟩
    · exact hnat2 j x hjd2 h2'
  · have hiNat := nat_mem_is_nat hM hNE n hn i hi
    rcases nat_trichotomy hM hNE i hiNat n1 hn1 with hin1 | hin1eq | hn1i
    · obtain ⟨j, x, y, hij, h1x, h1y, hns⟩ := hstep1 i hin1
      exact ⟨j, x, y, hij, (hAt_f i x).mpr (Or.inl h1x), (hAt_f j y).mpr (Or.inl h1y), hns⟩
    · subst hin1eq
      have hzn2 : E z1 n2 := by
        rcases nat_zero_le hM hNE hz1 n2 hn2 with rfl | hlt
        · have heq := addV_zero hM hNE hiNat
          have hz1eq := empty_unique hM hNE hz1 (zeroV_empty hM hNE)
          exact False.elim (mem_irrefl hM hNE i ((hz1eq ▸ heq) ▸ hi))
        · exact hlt
      obtain ⟨j2, x, y, hzj2, h2x, h2y, hns⟩ := hstep2 z1 hzn2
      obtain ⟨j, hnj⟩ := exists_succ hM hNE i
      have hadd0 : Add E i z1 i := add_zero hM hNE hiNat hz1
      have hadd1 : Add E i j2 j := add_succ hM hNE hadd0 hzj2 hnj
      have hj2d2 : E j2 dom2 := (hdom2 j2).mpr ((nat_succ_le_iff hM hNE (nat_zero hM hNE hz1) hzj2 n2 hn2).mp hzn2).symm
      exact ⟨j, x, y, hnj,
        (hAt_f i x).mpr (Or.inr ⟨z1, (hdom2 z1).mpr (Or.inl hzn2), hadd0, h2x⟩),
        (hAt_f j y).mpr (Or.inr ⟨j2, hj2d2, hadd1, h2y⟩), hns⟩
    · obtain ⟨j0, hj0Nat, hadd0⟩ := sub_exists hM hNE hn1 i hiNat (Or.inr hn1i)
      have hj0n2 : E j0 n2 := by
        rcases nat_trichotomy hM hNE j0 hj0Nat n2 hn2 with hlt | rfl | hgt
        · exact hlt
        · have hieq : i = addV hM hNE n1 j0 := (add_iff_eq hM hNE hn1 hj0Nat).mp hadd0
          exact False.elim (mem_irrefl hM hNE i (hieq ▸ hi))
        · have hieq : i = addV hM hNE n1 j0 := (add_iff_eq hM hNE hn1 hj0Nat).mp hadd0
          exact False.elim (mem_asymm hM hNE hi (hieq ▸ addV_lt_addV_left hM hNE hn1 j0 hj0Nat n2 hn2 hgt))
      obtain ⟨j1, x, y, hj01, h2x, h2y, hns⟩ := hstep2 j0 hj0n2
      obtain ⟨j, hij⟩ := exists_succ hM hNE i
      have hadd1 : Add E n1 j1 j := add_succ hM hNE hadd0 hj01 hij
      have hj1d2 : E j1 dom2 := (hdom2 j1).mpr ((nat_succ_le_iff hM hNE hj0Nat hj01 n2 hn2).mp hj0n2).symm
      exact ⟨j, x, y, hij,
        (hAt_f i x).mpr (Or.inr ⟨j0, (hdom2 j0).mpr (Or.inl hj0n2), hadd0, h2x⟩),
        (hAt_f j y).mpr (Or.inr ⟨j1, hj1d2, hadd1, h2y⟩), hns⟩

/-! ### Part 3: InternalHaltsFrom → InternalLinkedHalts -/

private theorem build_hist_fn (hM : Model E) (hNE : Nonempty V)
    {n c0 dom f : V} (hn : NatObject E n) (hc0 : Empty E c0) (hc0Nat : NatObject E c0)
    (hdom : Succ E n dom) (hfun : FunctionOn E f dom)
    (hnat : ∀ i x, E i dom → At E f i x → NatObject E x) :
    ∃ hfn lc0 hist,
      FunctionOn E hfn dom ∧ At E hfn c0 lc0 ∧ ListCons E c0 c0 lc0 ∧
      (∀ i x, E i dom → At E hfn i x → NatObject E x) ∧
      (∀ i, E i n → ∃ j fj hi hj, Succ E i j ∧ At E f j fj ∧ At E hfn i hi ∧ At E hfn j hj ∧ ListCons E fj hi hj) ∧
      At E hfn n hist ∧ E n hist := by
  let body : Formula :=
    .imp (.or (.mem 0 1) (.eq 0 1))
      (.ex (.ex (.and (fSucc 2 1) (.and (fFunctionOn 0 1)
        (.and (.ex (.and (fAt 1 5 0) (fListCons 5 5 0)))
          (.and (.all (.all (.imp (.mem 1 3) (.imp (fAt 2 1 0) (fNatObject 0)))))
            (.and (.all (.imp (.mem 0 3)
              (.ex (.ex (.ex (.ex (.and (fSucc 4 3) (.and (fAt 10 3 2) (.and (fAt 5 4 1)
                (.and (fAt 5 3 0) (fListCons 2 1 0)))))))))))
              (.ex (.and (fAt 1 3 0) (.mem 3 0))))))))))
  have hB : Bound body 4 := by
    refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
      ⟨bound_fSucc (by omega) (by omega), ⟨bound_fFunctionOn (by omega) (by omega),
        ⟨⟨bound_fAt (by omega) (by omega) (by omega), bound_fListCons (by omega) (by omega) (by omega)⟩,
          ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fNatObject (by omega)⟩⟩,
            ⟨⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
              ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega),
                bound_fListCons (by omega) (by omega) (by omega)⟩⟩⟩⟩⟩,
             ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩⟩⟩⟩⟩
  let env : Nat → V := fun i => if i = 0 then n else if i = 1 then c0 else f
  have hBuild := omega_induction hM hNE 3 body hB env
    (fun z0 hz0 _ => by
      have hzeq : z0 = c0 := empty_unique hM hNE hz0 hc0
      rw [hzeq]
      obtain ⟨dom0, hdom0⟩ := exists_succ hM hNE c0
      obtain ⟨p0, hcp0, hle0⟩ := cantor_exists hM hNE hc0Nat hc0Nat
      obtain ⟨lc0, hlc0⟩ := exists_succ hM hNE p0
      have hlc0Nat := nat_succ hM hNE hcp0.2.2.1 hlc0
      obtain ⟨h0, hfun0, hh00, hh0at⟩ := functionOn_singleton hM hNE hc0 hdom0 (a := lc0)
      have hc0lt : E c0 lc0 := (hlc0 c0).mpr (hle0.elim Or.inr Or.inl)
      refine ⟨dom0, h0, (eval_fSucc _ _ _).mpr hdom0, (eval_fFunctionOn _ _ _).mpr hfun0,
        ⟨lc0, (eval_fAt _ _ _ _).mpr hh00, (eval_fListCons _ _ _ _).mpr ⟨p0, hcp0, hlc0⟩⟩,
        fun i x _ hix => (eval_fNatObject _ _).mpr ((hh0at i x ((eval_fAt _ _ _ _).mp hix)).2 ▸ hlc0Nat),
        fun i hi => False.elim (hc0 i hi),
        ⟨lc0, (eval_fAt _ _ _ _).mpr hh00, hc0lt⟩⟩)
    (fun k k' hk hkk' ih hk'le => by
      dsimp only [eval, pushValue, env] at hk'le
      have hkn : E k n := by
        rcases hk'le with hk'n | hk'eq
        · exact nat_lt_trans hM hNE n hn k k' ((hkk' k).mpr (Or.inr rfl)) hk'n
        · simp only [ite_true] at hk'eq; rw [← hk'eq]; exact (hkk' k).mpr (Or.inr rfl)
      obtain ⟨domk, hk_fn, hdomk, hfunk, ⟨lc0, hlc0at, hlc0c⟩, hnatk, hstepk, ⟨hkval, hhkat, hklt⟩⟩ := ih (Or.inl hkn)
      have hdomk' : Succ E k domk := (eval_fSucc _ _ _).mp hdomk
      have hdomk_eq : domk = k' := succ_unique hM hNE hdomk' hkk'
      subst hdomk_eq
      have hfunk' : FunctionOn E hk_fn domk := (eval_fFunctionOn _ _ _).mp hfunk
      have hhkat' : At E hk_fn k hkval := (eval_fAt _ _ _ _).mp hhkat
      have hkvalNat : NatObject E hkval := (eval_fNatObject _ _).mp (hnatk k hkval ((hkk' k).mpr (Or.inr rfl)) hhkat)
      have hk'dom : E domk dom := (hdom domk).mpr hk'le
      obtain ⟨fk', hfk', _⟩ := hfun.1 domk hk'dom
      have hfk'Nat : NatObject E fk' := hnat domk fk' hk'dom hfk'
      obtain ⟨pk', hcpk', hlek'⟩ := cantor_exists hM hNE hfk'Nat hkvalNat
      obtain ⟨lck', hlck'⟩ := exists_succ hM hNE pk'
      have hlck'Nat := nat_succ hM hNE hcpk'.2.2.1 hlck'
      obtain ⟨domk', hdomk'⟩ := exists_succ hM hNE domk
      obtain ⟨hk'_fn, hfunk_new, hAt'⟩ := functionOn_extend hM hNE hfunk' hdomk' (y := lck')
      have hval_lt : E hkval lck' := (hlck' hkval).mpr (hlek'.elim Or.inr Or.inl)
      have hk'lt : E domk lck' := by
        dsimp only [eval, pushValue] at hklt
        rcases (nat_succ_le_iff hM hNE hk hkk' hkval hkvalNat).mp hklt with rfl | hlt
        · exact hval_lt
        · exact nat_lt_trans hM hNE lck' hlck'Nat domk hkval hlt hval_lt
      have hlc0at' : At E hk_fn c0 lc0 := (eval_fAt _ _ _ _).mp hlc0at
      have hlc0c' : ListCons E c0 c0 lc0 := (eval_fListCons _ _ _ _).mp hlc0c
      refine ⟨domk', hk'_fn, (eval_fSucc _ _ _).mpr hdomk', (eval_fFunctionOn _ _ _).mpr hfunk_new,
        ⟨lc0, (eval_fAt _ _ _ _).mpr ((hAt' c0 lc0).mpr (Or.inl hlc0at')), (eval_fListCons _ _ _ _).mpr hlc0c'⟩,
        fun i x _ hix => by
          rcases (hAt' i x).mp ((eval_fAt _ _ _ _).mp hix) with h1 | ⟨_, rfl⟩
          · obtain ⟨q, hq1, hqp⟩ := h1; obtain ⟨u, _, hud, huv⟩ := hfunk'.2 q hq1
            have := (orderedPair_inj hqp huv).1; subst this
            exact hnatk i x hud ((eval_fAt _ _ _ _).mpr ⟨q, hq1, hqp⟩)
          · exact (eval_fNatObject _ _).mpr hlck'Nat,
        fun i hi => by
          dsimp only [eval, pushValue] at hi
          rcases (hkk' i).mp hi with hik | rfl
          · obtain ⟨j, fj, hi_v, hj_v, hij, hfj, hhi, hhj, hlc⟩ := hstepk i hik
            have hij' : Succ E i j := (eval_fSucc _ _ _).mp hij
            have hfj' : At E f j fj := (eval_fAt _ _ _ _).mp hfj
            have hhi' : At E hk_fn i hi_v := (eval_fAt _ _ _ _).mp hhi
            have hhj' : At E hk_fn j hj_v := (eval_fAt _ _ _ _).mp hhj
            have hlc' : ListCons E fj hi_v hj_v := (eval_fListCons _ _ _ _).mp hlc
            exact ⟨j, fj, hi_v, hj_v, (eval_fSucc _ _ _).mpr hij', (eval_fAt _ _ _ _).mpr hfj',
              (eval_fAt _ _ _ _).mpr ((hAt' i hi_v).mpr (Or.inl hhi')),
              (eval_fAt _ _ _ _).mpr ((hAt' j hj_v).mpr (Or.inl hhj')),
              (eval_fListCons _ _ _ _).mpr hlc'⟩
          · exact ⟨domk, fk', hkval, lck', (eval_fSucc _ _ _).mpr hkk', (eval_fAt _ _ _ _).mpr hfk',
              (eval_fAt _ _ _ _).mpr ((hAt' i hkval).mpr (Or.inl hhkat')),
              (eval_fAt _ _ _ _).mpr ((hAt' domk lck').mpr (Or.inr ⟨rfl, rfl⟩)),
              (eval_fListCons _ _ _ _).mpr ⟨pk', hcpk', hlck'⟩⟩,
        ⟨lck', (eval_fAt _ _ _ _).mpr ((hAt' domk lck').mpr (Or.inr ⟨rfl, rfl⟩)), hk'lt⟩⟩)
  obtain ⟨domh, hfn, hdomh, hfunh, ⟨lc0, hlc0at, hlc0c⟩, hnath, hsteph, ⟨hist, hhistat, hnlt⟩⟩ := hBuild n hn (Or.inr rfl)
  have hdomh_eq : domh = dom := succ_unique hM hNE ((eval_fSucc _ _ _).mp hdomh) hdom
  subst hdomh_eq
  refine ⟨hfn, lc0, hist, (eval_fFunctionOn _ _ _).mp hfunh, (eval_fAt _ _ _ _).mp hlc0at,
    (eval_fListCons _ _ _ _).mp hlc0c,
    fun i x hi hix => (eval_fNatObject _ _).mp (hnath i x hi ((eval_fAt _ _ _ _).mpr hix)),
    fun i hi => ?_, (eval_fAt _ _ _ _).mp hhistat, hnlt⟩
  obtain ⟨j, fj, hi_v, hj_v, hij, hfj, hhi, hhj, hlc⟩ := hsteph i hi
  exact ⟨j, fj, hi_v, hj_v, (eval_fSucc _ _ _).mp hij, (eval_fAt _ _ _ _).mp hfj,
    (eval_fAt _ _ _ _).mp hhi, (eval_fAt _ _ _ _).mp hhj, (eval_fListCons _ _ _ _).mp hlc⟩

private theorem haltsFrom_implies_linkedHalts (hM : Model E) (hNE : Nonempty V)
    {c0 : V} (hc0 : Empty E c0) (hHalts : InternalHaltsFrom E c0) :
    InternalLinkedHalts E := by
  rcases hHalts with ⟨c', term, ⟨n, hn, hc0Nat, hc'Nat, z, dom, f, hz, hdom, hfun, hf0, hf_end, hnat, hstep⟩,
    hcode', hval', hterm'⟩
  have hz_eq : z = c0 := empty_unique hM hNE hz hc0
  rw [hz_eq] at hf0
  obtain ⟨hfn, lc0, hist, hfunh', hlc0at', hlc0c', hnath, hsteph, hhistat', hnlt⟩ :=
    build_hist_fn hM hNE hn hc0 hc0Nat hdom hfun hnat
  have hhistNat : NatObject E hist := hnath n hist ((hdom n).mpr (Or.inr rfl)) hhistat'
  have hhistNE : ¬ Empty E hist := fun he => he n hnlt
  -- Helper: ListHead E (h k) (f k) for all k ≤ n
  have hHead_h : ∀ k, E k dom → ∀ hk fk, At E hfn k hk → At E f k fk → ListHead E hk fk ∧ ¬ Empty E hk := by
    intro k hkdom hk fk hkh hkf
    have hkNat := nat_mem_is_nat hM hNE dom (nat_succ hM hNE hn hdom) k hkdom
    rcases nat_zero_le hM hNE hc0 k hkNat with hk0 | h0k
    · rw [← hk0] at hkdom hkh hkf
      have h1 := functionOn_at_unique hfunh' hkdom hkh hlc0at'
      have h2 := functionOn_at_unique hfun hkdom hkf hf0
      rw [h1, h2]
      rcases hlc0c' with ⟨p, hcp, hsp⟩
      exact ⟨Or.inr ⟨c0, p, hcp, hsp⟩, fun he => he p ((hsp p).mpr (Or.inr rfl))⟩
    · -- k > 0, so k = succ k' with k' < n
      have hpred : ∀ x, NatObject E x → E c0 x → ∃ p, NatObject E p ∧ Succ E p x := by
        let bp : Formula := .imp (.mem 1 0) (.ex (.and (fNatObject 0) (fSucc 0 1)))
        have hp := omega_induction hM hNE 1 bp
          ⟨⟨by omega, by omega⟩, ⟨bound_fNatObject (by omega), bound_fSucc (by omega) (by omega)⟩⟩ (fun _ => c0)
          (fun z0 hz0 h => False.elim (hz0 c0 h))
          (fun x x' hx hxx' _ _ => ⟨x, (eval_fNatObject _ _).mpr hx, (eval_fSucc _ _ _).mpr hxx'⟩)
        intro x hx h0x; obtain ⟨p, hp1, hp2⟩ := hp x hx h0x; exact ⟨p, (eval_fNatObject _ _).mp hp1, (eval_fSucc _ _ _).mp hp2⟩
      obtain ⟨kp, hkpNat, hkpk⟩ := hpred k hkNat h0k
      have hkpn : E kp n := by
        rcases (hdom k).mp hkdom with hkn | rfl
        · exact nat_lt_trans hM hNE n hn kp k ((hkpk kp).mpr (Or.inr rfl)) hkn
        · exact (hkpk kp).mpr (Or.inr rfl)
      obtain ⟨j, fj, hkpv, hjv, hkpj, hfj, hhkp, hhj, hlc⟩ := hsteph kp hkpn
      have hjk := succ_unique hM hNE hkpj hkpk; subst hjk
      have h1 := functionOn_at_unique hfunh' hkdom hkh hhj
      have h2 := functionOn_at_unique hfun hkdom hkf hfj
      subst h1; subst h2
      rcases hlc with ⟨p, hcp, hsp⟩
      exact ⟨Or.inr ⟨hkpv, p, hcp, hsp⟩, fun he => he p ((hsp p).mpr (Or.inr rfl))⟩
  -- Step 2: Build g on succ hist via Replacement:
  --   i ↦ ⟨i, h(n - i)⟩ if i ≤ n, else ⟨i, c0⟩
  obtain ⟨domg, hdomg⟩ := exists_succ hM hNE hist
  let phiG : Formula :=
    .or (.ex (.ex (.and (fAdd 2 1 4) (.and (fAt 6 1 0) (fOrderedPair 2 0 3)))))
        (.and (.mem 2 0) (fOrderedPair 0 3 1))
  -- Under pushValue (pushValue envG y) i:
  -- 0=i, 1=y, 2=n, 3=c0, 4=hfn
  have hBG : Bound phiG 5 :=
    ⟨⟨bound_fAdd (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega), bound_fOrderedPair (by omega) (by omega) (by omega)⟩⟩,
     ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega)⟩⟩
  let envG : Nat → V := fun k => if k = 0 then n else if k = 1 then c0 else hfn
  have hFuncG : ∀ i p1 p2, eval E phiG (pushValue (pushValue envG p1) i) →
      eval E phiG (pushValue (pushValue envG p2) i) → p1 = p2 := by
    intro i p1 p2 h1 h2
    rcases h1 with ⟨d1, v1, ha1, hat1, hp1⟩ | ⟨hni1, hp1⟩
    · have ha1' : Add E i d1 n := (eval_fAdd _ _ _ _).mp ha1
      have hiNat := ha1'.1; have hd1Nat := ha1'.2.1
      rcases h2 with ⟨d2, v2, ha2, hat2, hp2⟩ | ⟨hni2, _⟩
      · have ha2' : Add E i d2 n := (eval_fAdd _ _ _ _).mp ha2
        have hd2Nat := ha2'.2.1
        have hd12 : d1 = d2 := addV_cancel_left hM hNE hiNat hd1Nat hd2Nat
          (((add_iff_eq hM hNE hiNat hd1Nat).mp ha1').symm.trans ((add_iff_eq hM hNE hiNat hd2Nat).mp ha2'))
        subst hd12
        have hd1dom : E d1 dom := (hdom d1).mpr (by
          have hle := addV_le_left hM hNE hd1Nat i hiNat
          rw [addV_comm hM hNE hd1Nat i hiNat, ← (add_iff_eq hM hNE hiNat hd1Nat).mp ha1'] at hle
          exact hle.elim Or.inr Or.inl)
        have hv12 : v1 = v2 := functionOn_at_unique hfunh' hd1dom ((eval_fAt _ _ _ _).mp hat1) ((eval_fAt _ _ _ _).mp hat2)
        subst hv12
        exact orderedPair_unique hM hNE ((eval_fOrderedPair _ _ _ _).mp hp1) ((eval_fOrderedPair _ _ _ _).mp hp2)
      · have hle := addV_le_left hM hNE hiNat d1 hd1Nat
        rw [← (add_iff_eq hM hNE hiNat hd1Nat).mp ha1'] at hle
        rcases hle with rfl | hin
        · exact False.elim (mem_irrefl hM hNE i hni2)
        · exact False.elim (mem_asymm hM hNE hin hni2)
    · rcases h2 with ⟨d2, _, ha2, _, _⟩ | ⟨_, hp2⟩
      · have ha2' : Add E i d2 n := (eval_fAdd _ _ _ _).mp ha2
        have hle := addV_le_left hM hNE ha2'.1 d2 ha2'.2.1
        rw [← (add_iff_eq hM hNE ha2'.1 ha2'.2.1).mp ha2'] at hle
        rcases hle with rfl | hin
        · exact False.elim (mem_irrefl hM hNE i hni1)
        · exact False.elim (mem_asymm hM hNE hin hni1)
      · exact orderedPair_unique hM hNE ((eval_fOrderedPair _ _ _ _).mp hp1) ((eval_fOrderedPair _ _ _ _).mp hp2)
  obtain ⟨g, hg⟩ := ax_rep hM hNE 3 phiG hBG envG hFuncG domg
  have hAt_g : ∀ i v, At E g i v ↔ E i domg ∧
      ((∃ d, Add E i d n ∧ At E hfn d v) ∨ (E n i ∧ v = c0)) := by
    intro i v
    constructor
    · rintro ⟨p, hpg, hp⟩
      obtain ⟨i', hi'dom, hphi⟩ := (hg p).mp hpg
      rcases hphi with ⟨d, v', ha, hat, hp'⟩ | ⟨hni, hp'⟩
      · have ⟨hi, hv⟩ := orderedPair_inj hp ((eval_fOrderedPair _ _ _ _).mp hp')
        subst hi; subst hv
        exact ⟨hi'dom, Or.inl ⟨d, (eval_fAdd _ _ _ _).mp ha, (eval_fAt _ _ _ _).mp hat⟩⟩
      · have ⟨hi, hv⟩ := orderedPair_inj hp ((eval_fOrderedPair _ _ _ _).mp hp')
        subst hi; subst hv
        exact ⟨hi'dom, Or.inr ⟨hni, rfl⟩⟩
    · rintro ⟨hidom, hdisj⟩
      obtain ⟨p, hp⟩ := exists_orderedPair hM hNE i v
      refine ⟨p, (hg p).mpr ⟨i, hidom, ?_⟩, hp⟩
      rcases hdisj with ⟨d, ha, hat⟩ | ⟨hni, rfl⟩
      · exact Or.inl ⟨d, v, (eval_fAdd _ _ _ _).mpr ha, (eval_fAt _ _ _ _).mpr hat, (eval_fOrderedPair _ _ _ _).mpr hp⟩
      · exact Or.inr ⟨hni, (eval_fOrderedPair _ _ _ _).mpr hp⟩
  have hfung : FunctionOn E g domg := by
    constructor
    · intro i hidom
      have hiNat := nat_mem_is_nat hM hNE domg (nat_succ hM hNE hhistNat hdomg) i hidom
      rcases nat_trichotomy hM hNE i hiNat n hn with hin | hin_eq | hni
      · obtain ⟨d, hdNat, hadd⟩ := sub_exists hM hNE hiNat n hn (Or.inr hin)
        have hddom : E d dom := (hdom d).mpr (by
          have hle := addV_le_left hM hNE hdNat i hiNat
          rw [addV_comm hM hNE hdNat i hiNat, ← (add_iff_eq hM hNE hiNat hdNat).mp hadd] at hle
          exact hle.elim Or.inr Or.inl)
        obtain ⟨v, hv, hu⟩ := hfunh'.1 d hddom
        refine ⟨v, (hAt_g i v).mpr ⟨hidom, Or.inl ⟨d, hadd, hv⟩⟩, fun w hw => ?_⟩
        rcases ((hAt_g i w).mp hw).2 with ⟨d', hadd', hv'⟩ | ⟨hni', _⟩
        · have hd'Nat := hadd'.2.1
          have hd' := addV_cancel_left hM hNE hiNat hdNat hd'Nat
            (((add_iff_eq hM hNE hiNat hdNat).mp hadd).symm.trans ((add_iff_eq hM hNE hiNat hd'Nat).mp hadd'))
          subst hd'; exact hu w hv'
        · exact False.elim (mem_asymm hM hNE hin hni')
      · rw [hin_eq] at hidom ⊢
        refine ⟨lc0, (hAt_g n lc0).mpr ⟨hidom, Or.inl ⟨c0, add_zero hM hNE hn hc0, hlc0at'⟩⟩, fun w hw => ?_⟩
        rcases ((hAt_g n w).mp hw).2 with ⟨d', hadd', hv'⟩ | ⟨hnn, _⟩
        · have hd'Nat := hadd'.2.1
          have hd0 : d' = c0 := (addV_cancel_left hM hNE hn hd'Nat hc0Nat
            (((add_iff_eq hM hNE hn hd'Nat).mp hadd').symm.trans ((add_iff_eq hM hNE hn hc0Nat).mp (add_zero hM hNE hn hc0))))
          rw [hd0] at hv'
          exact functionOn_at_unique hfunh' ((hdom c0).mpr (by rcases nat_zero_le hM hNE hc0 n hn with h0 | h; exact Or.inr h0; exact Or.inl h)) hv' hlc0at'
        · exact False.elim (mem_irrefl hM hNE n hnn)
      · refine ⟨c0, (hAt_g i c0).mpr ⟨hidom, Or.inr ⟨hni, rfl⟩⟩, fun w hw => ?_⟩
        rcases ((hAt_g i w).mp hw).2 with ⟨d', hadd', _⟩ | ⟨_, rfl⟩
        · have hle := addV_le_left hM hNE hiNat d' hadd'.2.1
          rw [← (add_iff_eq hM hNE hiNat hadd'.2.1).mp hadd'] at hle
          rcases hle with rfl | hin
          · exact False.elim (mem_irrefl hM hNE i hni)
          · exact False.elim (mem_asymm hM hNE hin hni)
        · rfl
    · intro p hpg
      obtain ⟨i, hidom, hphi⟩ := (hg p).mp hpg
      rcases hphi with ⟨_, v, _, _, hp⟩ | ⟨_, hp⟩
      · exact ⟨i, v, hidom, (eval_fOrderedPair _ _ _ _).mp hp⟩
      · exact ⟨i, c0, hidom, (eval_fOrderedPair _ _ _ _).mp hp⟩
  have hLinked : LinkedRun E c0 hist := by
    refine ⟨hc0Nat, hhistNat, hhistNE, c0, domg, g, hc0, hdomg, hfung, ?_, ?_, ?_, ?_⟩
    · apply (hAt_g c0 hist).mpr
      refine ⟨(hdomg c0).mpr (Or.inl (by
        rcases nat_zero_le hM hNE hc0 hist hhistNat with h0 | hlt
        · exact False.elim (hhistNE (h0 ▸ hc0))
        · exact hlt)),
        Or.inl ⟨n, ?_, hhistat'⟩⟩
      have h0eq : c0 = zeroV hM hNE := empty_unique hM hNE hc0 (zeroV_empty hM hNE)
      rw [h0eq]
      have hspec := addV_spec hM hNE (zeroV_nat hM hNE) hn
      rwa [zero_addV hM hNE n hn] at hspec
    · exact (hAt_g hist c0).mpr ⟨(hdomg hist).mpr (Or.inr rfl), Or.inr ⟨hnlt, rfl⟩⟩
    · intro i x _ hgx
      rcases ((hAt_g i x).mp hgx).2 with ⟨d, hadd, hhd⟩ | ⟨_, rfl⟩
      · have hdNat := hadd.2.1
        have hddom : E d dom := (hdom d).mpr (by
          have hle := addV_le_left hM hNE hdNat i hadd.1
          rw [addV_comm hM hNE hdNat i hadd.1, ← (add_iff_eq hM hNE hadd.1 hdNat).mp hadd] at hle
          exact hle.elim Or.inr Or.inl)
        exact hnath d x hddom hhd
      · exact hc0Nat
    · intro i hih
      have hiNat := nat_mem_is_nat hM hNE hist hhistNat i hih
      obtain ⟨j, hij⟩ := exists_succ hM hNE i
      have hjNat := nat_succ hM hNE hiNat hij
      have hjdom : E j domg := (hdomg j).mpr ((nat_succ_le_iff hM hNE hiNat hij hist hhistNat).mp hih).symm
      have hidom : E i domg := (hdomg i).mpr (Or.inl hih)
      rcases nat_trichotomy hM hNE i hiNat n hn with hin | hin_eq | hni
      · have hjle : j = n ∨ E j n := (nat_succ_le_iff hM hNE hiNat hij n hn).mp hin
        obtain ⟨d, hdNat, haddj⟩ := sub_exists hM hNE hjNat n hn hjle
        obtain ⟨d', hdd'⟩ := exists_succ hM hNE d
        have hd'Nat := nat_succ hM hNE hdNat hdd'
        have haddi : Add E i d' n := by
          have h1 := (add_iff_eq hM hNE hjNat hdNat).mp haddj
          have hjeq := succ_unique hM hNE hij (succV_spec hM hNE i); subst hjeq
          have hd'eq := succ_unique hM hNE hdd' (succV_spec hM hNE d); subst hd'eq
          rw [succ_addV hM hNE hiNat d hdNat, ← addV_succ hM hNE hiNat hdNat] at h1
          exact (add_iff_eq hM hNE hiNat hd'Nat).mpr h1
        have hdn : E d n := by
          have hle := addV_le_left hM hNE hd'Nat i hiNat
          rw [addV_comm hM hNE hd'Nat i hiNat, ← (add_iff_eq hM hNE hiNat hd'Nat).mp haddi] at hle
          exact (nat_succ_le_iff hM hNE hdNat hdd' n hn).mpr hle
        obtain ⟨d1, fd1, hd_v, hd1_v, hdd1, hfd1, hhd, hhd1, hlc'⟩ := hsteph d hdn
        have hd1eq : d1 = d' := succ_unique hM hNE hdd1 hdd'
        rw [hd1eq] at hfd1 hhd1
        obtain ⟨d2, fd, fd2, hdd2, hfd, hfd2, hns⟩ := hstep d hdn
        have hd2eq : d2 = d' := succ_unique hM hNE hdd2 hdd'
        rw [hd2eq] at hfd2
        have hfeq : fd1 = fd2 := functionOn_at_unique hfun ((hdom d').mpr (by
          rcases (nat_succ_le_iff hM hNE hdNat hdd' n hn).mp hdn with h0 | h; exact Or.inr h0; exact Or.inl h))
          hfd1 hfd2
        subst hfeq
        have ⟨hhead_d, hne_d⟩ := hHead_h d ((hdom d).mpr (Or.inl hdn)) hd_v fd hhd hfd
        refine ⟨j, hd1_v, hd_v, hij,
          (hAt_g i hd1_v).mpr ⟨hidom, Or.inl ⟨d', haddi, hhd1⟩⟩,
          (hAt_g j hd_v).mpr ⟨hjdom, Or.inl ⟨d, haddj, hhd⟩⟩,
          Or.inr ⟨fd1, hlc'⟩,
          Or.inr ⟨fd1, hd_v, Or.inr ⟨hd_v, hlc'⟩, Or.inr ⟨fd1, hlc'⟩, Or.inr ⟨hne_d, fd, hhead_d, hns⟩⟩⟩
      · rw [hin_eq] at hij hidom ⊢
        have hnj : E n j := (hij n).mpr (Or.inr rfl)
        exact ⟨j, lc0, c0, hij,
          (hAt_g n lc0).mpr ⟨hidom, Or.inl ⟨c0, add_zero hM hNE hn hc0, hlc0at'⟩⟩,
          (hAt_g j c0).mpr ⟨hjdom, Or.inr ⟨hnj, rfl⟩⟩,
          Or.inr ⟨c0, hlc0c'⟩,
          Or.inr ⟨c0, c0, Or.inr ⟨c0, hlc0c'⟩, Or.inr ⟨c0, hlc0c'⟩, Or.inl ⟨hc0, rfl⟩⟩⟩
      · have hnj : E n j := nat_lt_trans hM hNE j hjNat n i hni ((hij i).mpr (Or.inr rfl))
        exact ⟨j, c0, c0, hij,
          (hAt_g i c0).mpr ⟨hidom, Or.inr ⟨hni, rfl⟩⟩,
          (hAt_g j c0).mpr ⟨hjdom, Or.inr ⟨hnj, rfl⟩⟩,
          Or.inl ⟨hc0, hc0⟩, Or.inl hc0⟩
  have hHeadHist := (hHead_h n ((hdom n).mpr (Or.inr rfl)) hist c' hhistat' hf_end).1
  exact ⟨c0, hist, c', term, hc0, hLinked, hHeadHist, hcode', hval', hterm'⟩

/-! ### Part 4: Concrete 58,616-Step Startup & Lifting to Any Model of ZF -/

private def checkRowsPrefix : Nat → Nat → List Trans → Bool
  | _, 0, _ => true
  | _, _ + 1, [] => false
  | i, n + 1, r :: rs => (fastRow i == r) && checkRowsPrefix (i + 1) n rs

private theorem checkRowsPrefix_sound : ∀ n i l, checkRowsPrefix i n l = true →
    ∀ j, j < n → fastRow (i + j) = l.getD j (none, none)
  | 0, _, _, _, _, hlt => by omega
  | _ + 1, _, [], h, _, _ => by simp [checkRowsPrefix] at h
  | n + 1, i, r :: rs, h, 0, _ => by simp [checkRowsPrefix] at h; simpa [List.getD] using h.1
  | n + 1, i, r :: rs, h, j + 1, hlt => by
    simp [checkRowsPrefix] at h
    have ih := checkRowsPrefix_sound n (i + 1) rs h.2 j (Nat.lt_of_succ_lt_succ hlt)
    rw [show i + (j + 1) = i + 1 + j by omega, ih]; rfl

private theorem literalRows_len : literalRows.length = 207 := by
  have h1 : (literalRows.drop 100).length = 107 := rfl
  rw [List.length_drop] at h1; omega

private theorem fastRow_eq (q : Nat) : fastRow q = literalRows.getD q (none, none) := by
  by_cases h : q < 207
  · by_cases h1 : q < 70
    · simpa using checkRowsPrefix_sound 70 0 literalRows rfl q h1
    · by_cases h2 : q < 140
      · have := checkRowsPrefix_sound 70 70 (literalRows.drop 70) rfl (q - 70) (by omega)
        have hq : 70 + (q - 70) = q := by omega
        rw [hq] at this; rw [this]; simp [List.getD, List.getElem?_drop, hq]
      · have := checkRowsPrefix_sound 67 140 (literalRows.drop 140) rfl (q - 140) (by omega)
        have hq : 140 + (q - 140) = q := by omega
        rw [hq] at this; rw [this]; simp [List.getD, List.getElem?_drop, hq]
  · have hge : ¬ q < literalRows.length := by rw [literalRows_len]; exact h
    have hble : Nat.ble 207 q = true := Nat.ble_eq.mpr (Nat.le_of_not_lt h)
    have h1 : fastRow q = (none, none) := by unfold fastRow; rw [hble]
    rw [h1]; simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hge)]

private def fastStep (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (q, left, right) := c
  let r := right / 2
  let tr := match Nat.beq (right % 2) 1 with | true => (fastRow q).2 | false => (fastRow q).1
  match tr with
  | none => c
  | some (write, direction, next) =>
    let w : Nat := match write with | true => 1 | false => 0
    match direction with
    | true => (next, w + 2 * left, r)
    | false => (next, left / 2, left % 2 + 2 * (w + 2 * r))

private theorem fastStep_eq (c : Nat × Nat × Nat) : fastStep c = stepPhysical c := by
  rcases c with ⟨q, left, right⟩
  unfold fastStep stepPhysical; simp only [fastRow_eq]
  cases h : Nat.beq (right % 2) 1
  · have hne : right % 2 ≠ 1 := by intro heq; rw [heq] at h; contradiction
    simp only [beq_false_of_ne hne]
    cases (literalRows.getD q (none, none)).1 with
    | none => rfl | some x => rcases x with ⟨w, d, n⟩; cases w <;> cases d <;> rfl
  · simp only [beq_iff_eq.mpr (Nat.eq_of_beq_eq_true h)]
    cases (literalRows.getD q (none, none)).2 with
    | none => rfl | some x => rcases x with ⟨w, d, n⟩; cases w <;> cases d <;> rfl

private theorem iterPhysical_add : ∀ m n c, iterPhysical (m + n) c = iterPhysical n (iterPhysical m c)
  | 0, _, _ => by simp [iterPhysical]
  | m + 1, n, c => by rw [show m + 1 + n = (m + n) + 1 by omega, iterPhysical, iterPhysical, iterPhysical_add m n]

private def runCheckPow : Nat → Nat × Nat × Nat → Option (Nat × Nat × Nat)
  | 0, (q, l, r) =>
    match Nat.ble 207 q with
    | true => none
    | false =>
      let (q', l', r') := fastStep (q, l, r)
      match Nat.beq (q' % 1) 0, Nat.beq (l' % 1) 0, Nat.beq (r' % 1) 0 with
      | true, true, true => some (q', l', r') | _, _, _ => none
  | k + 1, c => match runCheckPow k c with | none => none | some c1 => runCheckPow k c1

private theorem nat_beq_mod_one (n : Nat) : Nat.beq (n % 1) 0 = true := by rw [Nat.mod_one]; rfl

private theorem runCheckPow_sound : ∀ k c c',
    runCheckPow k c = some c' → iterPhysical (2 ^ k) c = c' ∧ ∀ j < 2 ^ k, (iterPhysical j c).1 < 207
  | 0, (q, l, r), c', h => by
    unfold runCheckPow at h
    cases hb : Nat.ble 207 q with
    | true => rw [hb] at h; contradiction
    | false =>
      rw [hb] at h; dsimp only at h
      rw [nat_beq_mod_one, nat_beq_mod_one, nat_beq_mod_one] at h
      injection h with hcc; subst hcc
      have hlt : q < 207 := Nat.lt_of_not_ge (fun hge => by have := Nat.ble_eq.mpr hge; rw [hb] at this; contradiction)
      exact ⟨by simp [iterPhysical, fastStep_eq], fun j hj => by have hj0 : j = 0 := (by omega); simp [hj0, iterPhysical, hlt]⟩
  | k + 1, c, c', h => by
    unfold runCheckPow at h
    cases h1 : runCheckPow k c with
    | none => rw [h1] at h; contradiction
    | some c1 =>
      rw [h1] at h
      obtain ⟨hi1, hn1⟩ := runCheckPow_sound k c c1 h1
      obtain ⟨hi2, hn2⟩ := runCheckPow_sound k c1 c' h
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
      refine ⟨by rw [hpow, iterPhysical_add, hi1, hi2], fun j hj => ?_⟩
      by_cases hlt : j < 2 ^ k
      · exact hn1 j hlt
      · rw [show j = 2 ^ k + (j - 2 ^ k) by omega, iterPhysical_add, hi1]; exact hn2 (j - 2 ^ k) (by omega)

private def SafeReach (c1 c2 : Nat × Nat × Nat) : Prop :=
  ∃ n, iterPhysical n c1 = c2 ∧ ∀ j < n, (iterPhysical j c1).1 < 207

private theorem SafeReach.refl (c : Nat × Nat × Nat) : SafeReach c c := ⟨0, rfl, fun _ h => by omega⟩

private theorem SafeReach.trans {c1 c2 c3 : Nat × Nat × Nat} (h1 : SafeReach c1 c2) (h2 : SafeReach c2 c3) : SafeReach c1 c3 := by
  obtain ⟨n1, he1, hs1⟩ := h1; obtain ⟨n2, he2, hs2⟩ := h2
  refine ⟨n1 + n2, by rw [iterPhysical_add, he1, he2], fun j hj => ?_⟩
  by_cases hlt : j < n1
  · exact hs1 j hlt
  · rw [show j = n1 + (j - n1) by omega, iterPhysical_add, he1]; exact hs2 (j - n1) (by omega)

private def verifyChain8 : List (Nat × Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | c1 :: c2 :: rest =>
    (match runCheckPow 8 c1 with
     | some c => Nat.beq c.1 c2.1 && Nat.beq c.2.1 c2.2.1 && Nat.beq c.2.2 c2.2.2 | none => false) &&
    verifyChain8 (c2 :: rest)

private theorem verifyChain8_sound : ∀ l c1 c2,
    l.head? = some c1 → l.getLast? = some c2 → verifyChain8 l = true → SafeReach c1 c2
  | [], _, _, h1, _, _ => by simp at h1
  | [_], _, _, h1, h2, _ => by simp at h1 h2; subst h1; subst h2; exact SafeReach.refl _
  | x :: y :: rest, _, c2, h1, h2, hv => by
    simp only [List.head?, Option.some.injEq] at h1; subst h1
    unfold verifyChain8 at hv; have hb := Bool.and_eq_true_iff.mp hv
    have hstep : SafeReach x y := by
      cases hr : runCheckPow 8 x with
      | none => rw [hr] at hb; simp at hb
      | some c =>
        rw [hr] at hb
        have h12 := Bool.and_eq_true_iff.mp hb.1; have h11 := Bool.and_eq_true_iff.mp h12.1
        have hcy : c = y := by
          rcases c with ⟨a1, a2, a3⟩; rcases y with ⟨b1, b2, b3⟩
          have e1 := Nat.eq_of_beq_eq_true h11.1; have e2 := Nat.eq_of_beq_eq_true h11.2; have e3 := Nat.eq_of_beq_eq_true h12.2
          dsimp only at e1 e2 e3; subst e1; subst e2; subst e3; rfl
        subst hcy; obtain ⟨hi, hn⟩ := runCheckPow_sound 8 x c hr; exact ⟨2 ^ 8, hi, hn⟩
    exact hstep.trans (verifyChain8_sound (y :: rest) y c2 rfl (by simpa [List.getLast?] using h2) hb.2)

private def startupPts0 : List (Nat × Nat × Nat) := [
  (0, 0, 0), (108, 17, 1052664), (74, 1, 286130056), (3, 273, 17947647), (3, 280, 152427519),
  (68, 0, 2566091962528), (46, 21626859, 2389), (94, 332, 190175230), (66, 20, 23265443847),
  (3, 0, 1488988405802), (2, 88064, 5592912), (7, 348, 28633391103), (1, 5407, 1781198335),
  (3, 22, 320695304190), (32, 390070235, 21845), (34, 91, 1843974799360), (10, 384, 460993708031),
  (7, 97, 1843974242300), (3, 0, 472056869157926), (3, 412159, 449926591), (125, 6, 481231049326130),
  (27, 1613, 1879808778240), (3, 0, 7699513582033702), (38, 443532677829997, 109), (4, 26431487, 1840679597),
  (3, 6431, 7539457187839), (34, 103935, 471216073984), (2, 1632, 30157828734976), (38, 109790100906, 449237),
  (74, 1, 30871285869313849), (6, 1, 494088319106285529), (2, 106496, 7539189438976), (50, 6687, 120627019874303),
  (1, 108607, 7539186644991), (9, 1704, 482508077400048), (3, 1745215, 471198772095), (79, 1704, 482508079497209),
  (79, 1704, 482508079431683), (68, 0, 31621649493635306848)
]
private def startupPts1 : List (Nat × Nat × Nat) := [
  (68, 0, 31621649493635306848), (4, 1, 494088273136757845), (50, 29288757679786, 449387), (3, 6982943, 1884867091007),
  (24, 27932191, 471216772783), (115, 426, 30881662399150700), (33, 0, 32381920338735098779008), (0, 457642147498, 460173741),
  (4, 6, 505967836795892603669), (34, 446917631, 7539508294997), (10, 27932352, 120632122976959), (60, 27932355, 120632122845887),
  (85, 6819, 7905747379426164406), (74, 1, 32381941266129034374229), (1, 446914815, 120632131643947), (3, 6983079, 7720456156785407),
  (4, 6, 8095485316532392672021), (74, 1, 32381941264662839553109), (50, 31449266696745320672694, 27), (74, 1, 518111064884815914265685),
  (79, 1704, 505967836795852816507), (38, 125797066797974944144237, 109), (68, 0, 530545731036524173187552608),
  (6, 0, 132636432759131008938394968), (84, 111731199, 123527304045046719), (3, 6819, 2023871348374533832691),
  (3, 1746047, 7905747458882990079), (68, 0, 132636432759130905859138904), (1, 468705486026070, 29451204310),
  (6, 0, 2122182924446707432407901528), (10, 1788035072, 123527304062544567), (68, 0, 530545731111536120613226838),
  (77, 1705, 129527766384663840423788), (50, 1874900327295658, 1884877076187), (83, 106, 33159108195142439507327689),
  (6, 0, 33954926791825857918066435416), (115, 426, 8289777048785609742614466), (32, 6984319, 505967837450293567487),
  (50, 27937023, 2023871349801266534399)
]
private def startupPts2 : List (Nat × Nat × Nat) := [
  (50, 27937023, 2023871349801266534399), (4, 28608364543, 1976436865039250773), (4, 26, 2122182924488559013228709669),
  (68, 0, 8692461258705137691796504204672), (74, 1, 33954926791816944246019058261), (6, 106, 530545731122138287112716393),
  (60, 28611706879, 1976436865039684935), (4, 1, 543278828669219726517849819733), (1, 27939327, 32381941596819112517631),
  (39, 27288, 33159108195142805577793535), (115, 426, 2122182924489139556710350870), (1, 1788493823, 505967837450232048511),
  (83, 106, 8488731697956558227915145145), (2, 436736, 2072444262196425348349952), (1, 27955199, 32381941596819145547775),
  (43, 6832, 132636432780571222311174143), (2, 111951872, 8095485399204697040896), (3, 0, 2173115314676566657688372388694),
  (2, 7168065536, 126491959362573391264), (3, 6836, 132636432780565358305083390), (34, 112041983, 8095485399204697040896),
  (84, 120297567194895701, 7539508304748), (68, 0, 34769845034829678200236294537312), (1, 25836912639, 31622989840643347567),
  (21, 6287, 132636432780569756351594495), (10, 425201762304, 1976436865040209238), (3, 24, 33954926791825576151031480307),
  (10, 106837311488, 126491959362579027291), (3, 408063, 33159108195143366774620159), (44, 100, 135819707167309482106510376960),
  (98, 430033600511, 31622989840644756823), (32, 108716359679, 126491959362579027291), (6, 1, 8692461258707806854816664125465),
  (1, 6543, 2122182924489175473575690239), (3, 108543, 132636432780575666121736191), (10, 27648, 530545731122302664486944767),
  (3, 108, 135819707167309481833779953662), (3, 1853882367, 8095485399205057746687), (84, 7567732375547, 1976436865040297300)
]
private def startupPts3 : List (Nat × Nat × Nat) := [
  (84, 7567732375547, 1976436865040297300), (56, 119453777919, 126491959362579027291), (2, 7516192768, 2023871349801264436640),
  (3, 1855, 8488731697956701894302760959), (10, 122880, 2122182924489223164787687423), (48, 4538783999449770, 30881826016254827),
  (14, 0, 8901080328916846676952860420211744), (1, 272383, 530545731122305241441107967), (3, 4521983, 33159108195144089759252479),
  (98, 75041668595674, 1976436865040307627), (56, 73662463, 2072444262196505609953279), (10, 304942678016, 505967837450318752429),
  (6, 0, 2225270082229210180057467421982248), (2, 21495808, 8289777048786022439747584), (3, 0, 556317520557302536004968577498698),
  (10, 21757952, 132636432780576445740810239), (3, 91328184582101, 31622989840644934506), (4, 5, 556317520557302908676325913919532),
  (63, 5, 556317520557302908113513399451436), (3, 349962239, 8289777048786027853209599), (60, 375557987676105389, 7720456504063704),
  (77, 5, 8901080328916847352472188682764524), (4, 5, 8901080328916847351346563653828396), (68, 0, 569669141050678230558220075696914472),
  (1, 21102591, 2122182924489223325841752063), (68, 0, 2278676564202712922232950671531834016), (10, 90112, 543278828669241171415555637247),
  (4, 98956046499818, 505967837450319121237), (2, 92, 556317520557302953712356547362816), (68, 0, 9114706256810851519836836327107579520),
  (10, 96256, 8692461258707858743015237484543), (56, 1546188226559, 518111065549126788557483), (10, 1610612736, 530545731122305831482863615),
  (3, 395263, 2173115314676964685753675153407), (34, 1575, 556317520557302959552973051527168), (1, 411566079, 2122182924489223325797236735),
  (3, 6319, 139079380139325739882380095651839), (1, 1999084996559822458371290328128365, 438), (34, 6479871, 2173115314676964687952837869568)
]
private def startupPts4 : List (Nat × Nat × Nat) := [
  (34, 6479871, 2173115314676964687952837869568), (60, 404607, 34769845034831434989653236645887),
  (10, 424664891392, 530545731122305832099425119), (21, 105495134207, 2122182924489223328397700479),
  (10, 6803228196864, 33159108195144114506214069), (3, 1665138687, 135819707167310293017318612991),
  (38, 446419313063079253, 8095485399205106080621), (68, 0, 9333459206974312140709648816482579119558),
  (50, 104398847, 34769845034831435012402058100735), (33, 0, 597341389246355977004064775783011974099328),
  (1, 125655865747620261116212628123062, 28760941), (74, 1, 37333836827897248562828410419353483214961),
  (68, 0, 2389365556985423908018657084160138056539232), (76, 100, 583341200435894508794193912802398175232),
  (1, 1679818751, 34769845034831435012471312924671), (6, 0, 597341389246355977005254565443018336236696),
  (81, 8158599263068786059756296750347995, 7190235), (68, 0, 2389365556985423908021601062818595920151334),
  (68, 0, 9557462227941695632085223659935141245947032), (34, 6608895, 142417285262669557811117235590135808),
  (1, 433019944959, 2173115314676964688279986853247), (4, 25, 37333836827897248562837513605973329051500),
  (81, 1904958367003826523584219, 494109216260077275), (2, 413120, 36458825027243406799647280414798643200),
  (3, 443446783377405, 33954926791827573254375979178), (3, 100, 149335347311588994251355260579015242547207),
  (3, 1642495, 9114706256810851699911820103196344319), (102, 101, 149335347311588994251355260579015242547200),
  (1, 25887, 583341200435894508794356477842832752639), (3, 7078106103807, 2173115314676964688280062700207),
  (1, 112425063940095, 135819707167310293017502870186), (3, 434110463, 35604321315667389452780391229816831),
  (1, 1947976174183722926959469, 7905747460161236406), (2, 444529115136, 556317520557302960199695732659456),
  (46, 461618961805474475, 530545731122305832099624378), (10, 27262976, 9114706256810851699911814883896721407),
  (15, 118219490218475178, 2122182924489223328398497515), (2, 1736704, 145835300108973627198589038096445079552),
  (3, 1697, 149335347311588994251355174870159712059391)
]
private def startupPts5 : List (Nat × Nat × Nat) := [
  (3, 1697, 149335347311588994251355174870159712059391), (115, 426, 597341389246355977005420700043039045844992),
  (1, 7318758490111, 34769845034831435012480983279807), (3, 0, 611677582588268520453550796844634932898668886),
  (84, 6980735, 36458825027243406799647259524144824319), (56, 111710207, 2278676564202712924977953720259051519),
  (126, 6818, 37333836827897248562838793752724300103676), (24, 457619537919, 556317520557302960199695732485119),
  (3, 1704, 149335347311588994251355175010759761461259), (14, 0, 9786841321412296327256812749478130129352463712),
  (34, 29289059713023, 8692461258707858753120245820072), (84, 117156037525503, 2173115314676964688280061455019),
  (79, 1704, 149335347311588994251355175010897200414555), (84, 114410717183, 2225270082229211840798782929940479),
  (32, 436444, 583341200435894508794356152386317189119), (10, 457648898048, 556317520557302960199695732485119),
  (3, 29289797910527, 8692461258707858753120245818031), (68, 0, 39147365285649185309027250998020606908501349760),
  (4, 6, 38229848911766782528346851015813388467949333), (74, 1, 152919395647067130113387699211017995736318549),
  (44, 6820, 37333836827897248562838793752586861150204), (3, 1788215295, 142417285262669557811122107516190719),
  (98, 29999625008054250, 8488731697956893313593990059), (68, 0, 9786841321412296327256812749514158926378145120),
  (10, 1831400898560, 139079380139325740049923933121279), (24, 1920398212980536661, 132636432780576458024906094),
  (10, 1831535116288, 139079380139325740049923933121279), (3, 30008970856890325, 8488731697956893313593990026),
  (2, 1746944, 145835300108973627198589038096445079552), (4, 6, 38229848911766782528346924800537883492482645),
  (34, 109327, 2333364801743578035177424609543121272832), (43, 6832, 37333836827897248562838784745525045362686),
  (34, 1791295487, 142417285262669557811122088904491008), (20, 27332, 9333459206974312140709679204063393087486),
  (7, 1792016384, 142417285262669557811122088904491008), (51, 458789748735, 556317520557302960199695659784191),
  (10, 109408, 2333364801743578035177424304615475642367), (56, 1835628756991, 139079380139325740049923914946047),
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
     | some c => Nat.beq c.1 c2.1 && Nat.beq c.2.1 c2.2.1 && Nat.beq c.2.2 c2.2.2 | none => false) &&
    verifyPowChain rest

private theorem verifyPowChain_cons {k : Nat} {c1 c2 : Nat × Nat × Nat} {rest}
    (h : verifyPowChain ((k, c1, c2) :: rest) = true) : SafeReach c1 c2 ∧ verifyPowChain rest = true := by
  unfold verifyPowChain at h; have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨?_, h2⟩
  cases hr : runCheckPow k c1 with
  | none => rw [hr] at h1; contradiction
  | some c =>
    rw [hr] at h1; have h12 := Bool.and_eq_true_iff.mp h1; have h11 := Bool.and_eq_true_iff.mp h12.1
    have hcy : c = c2 := by
      rcases c with ⟨a1, a2, a3⟩; rcases c2 with ⟨b1, b2, b3⟩
      have e1 := Nat.eq_of_beq_eq_true h11.1; have e2 := Nat.eq_of_beq_eq_true h11.2; have e3 := Nat.eq_of_beq_eq_true h12.2
      dsimp only at e1 e2 e3; subst e1; subst e2; subst e3; rfl
    subst hcy; obtain ⟨hi, hn⟩ := runCheckPow_sound k c1 c hr; exact ⟨2 ^ k, hi, hn⟩

private def startupTailChain : List (Nat × (Nat × Nat × Nat) × (Nat × Nat × Nat)) := [
  (6, (10, 28012544, 9114706256810851699911813689904201727), (3, 1709, 149335347311588994251355155495115563204611)),
  (6, (3, 1709, 149335347311588994251355155495115563204611), (7, 28049408, 9114706256810851699911813689887424512)),
  (6, (7, 28049408, 9114706256810851699911813689887424512), (2, 1712, 149335347311588994251355155495115563204608)),
  (5, (2, 1712, 149335347311588994251355155495115563204608), (11, 26, 9557462227941695632086729951687396045094915)),
  (4, (11, 26, 9557462227941695632086729951687396045094915), (68, 0, 39147365285649185309027245882111574200708759936)),
  (3, (68, 0, 39147365285649185309027245882111574200708759936), (74, 1, 152919395647067130113387679226998336721518593))
]

private theorem startup_tail_ok : verifyPowChain startupTailChain = true := rfl

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

private def tailBitsN : Nat → Nat
  | 0 => 0
  | t + 1 => 6 + 8 * tailBitsN t

private def regBlockN (v suf : Nat) : Nat := 2 * ((2 ^ (v + 1) - 1) + 2 ^ (v + 1) * suf)

private def regsSuffixN : List Nat → Nat → Nat
  | [], t => tailBitsN t
  | v :: vs, t => regBlockN v (regsSuffixN vs t)

private def regsBitsN (rs : List Nat) (t : Nat) : Nat := 1 + 2 * regsSuffixN rs t

private theorem startup_right_eq :
    152919395647067130113387679226998336721518593 = 1 + 2 ^ (42 + 6) * regsBitsN [0, 0, 0, 0, 0, 0, 2, 0, 0] 26 := rfl

private def confCodeN (c : Nat × Nat × Nat) : Nat := cantor c.1 (cantor c.2.1 c.2.2)

set_option maxRecDepth 2048 in
private theorem rows_all_defined : ∀ q, q < 207 →
    (literalRows.getD q (none, none)).1.isSome = true ∧ (literalRows.getD q (none, none)).2.isSome = true := by
  have hall : literalRows.all (fun p => p.1.isSome && p.2.isSome) = true := rfl
  intro q hq
  have hlen : q < literalRows.length := by rw [literalRows_len]; exact hq
  have hmem : literalRows[q] ∈ literalRows := List.getElem_mem hlen
  have hok := List.all_eq_true.mp hall _ hmem
  have hget : literalRows.getD q (none, none) = literalRows[q] := by
    simp [List.getD, List.getElem?_eq_getElem hlen]
  rw [hget]; exact Bool.and_eq_true_iff.mp hok

private theorem bitCons_numV (hM : Model E) (hNE : Nonempty V) (bit : Bool) (x : Nat) :
    BitCons E bit (numV hM hNE x) (numV hM hNE ((if bit then 1 else 0) + 2 * x)) := by
  refine ⟨numV hM hNE (if bit then 1 else 0), numV hM hNE 2, numV hM hNE (2 * x),
    numV_numeral hM hNE _, numV_numeral hM hNE 2,
    (mul_iff_eq hM hNE (numV_nat hM hNE 2) (numV_nat hM hNE x)).mpr (mulV_numV hM hNE 2 x).symm,
    (add_iff_eq hM hNE (numV_nat hM hNE _) (numV_nat hM hNE _)).mpr (addV_numV hM hNE _ _).symm⟩

private theorem numericStep_physical (hM : Model E) (hNE : Nonempty V) (c : Nat × Nat × Nat) (hq : c.1 < 207) :
    NumericStep E (numV hM hNE (confCodeN c)) (numV hM hNE (confCodeN (stepPhysical c))) := by
  rcases c with ⟨q, l, r⟩
  dsimp only at hq
  let read := r % 2 == 1
  have hr_eq : (if read then 1 else 0) + 2 * (r / 2) = r := by
    dsimp only [read]; have hmod : r % 2 = 0 ∨ r % 2 = 1 := by omega
    rcases hmod with h | h <;> simp [h] <;> omega
  have hrow_some : (if read then (literalRows.getD q (none, none)).2 else (literalRows.getD q (none, none)).1).isSome = true := by
    have ⟨h1, h2⟩ := rows_all_defined q hq; cases read <;> assumption
  cases htr : (if read then (literalRows.getD q (none, none)).2 else (literalRows.getD q (none, none)).1) with
  | none => rw [htr] at hrow_some; contradiction
  | some tr =>
    rcases tr with ⟨w, d, nq⟩
    have hsp : stepPhysical (q, l, r) =
        if d then (nq, (if w then 1 else 0) + 2 * l, r / 2)
        else (nq, l / 2, (l % 2) + 2 * ((if w then 1 else 0) + 2 * (r / 2))) := by
      unfold stepPhysical; dsimp only
      have hread : (r % 2 == 1) = read := rfl
      rw [hread, htr]
    rw [hsp]
    let tN : Nat × Nat × Nat :=
      if d then (nq, (if w then 1 else 0) + 2 * l, r / 2)
      else (nq, l / 2, (l % 2) + 2 * ((if w then 1 else 0) + 2 * (r / 2)))
    refine ⟨⟨numV hM hNE q, numV hM hNE l, numV hM hNE r⟩,
      ⟨numV hM hNE tN.1, numV hM hNE tN.2.1, numV hM hNE tN.2.2⟩,
      ⟨numV hM hNE (cantor l r), cantor_numV hM hNE l r, cantor_numV hM hNE q (cantor l r)⟩,
      ⟨numV hM hNE (cantor tN.2.1 tN.2.2), cantor_numV hM hNE _ _, cantor_numV hM hNE _ _⟩,
      ⟨numV_nat hM hNE q, numV_nat hM hNE l, numV_nat hM hNE r⟩,
      ⟨numV_nat hM hNE tN.1, numV_nat hM hNE tN.2.1, numV_nat hM hNE tN.2.2⟩,
      ⟨q, hq⟩, numV_numeral hM hNE q, read, w, d, nq, htr, ?_⟩
    have hbcR := bitCons_numV hM hNE read (r / 2)
    rw [hr_eq] at hbcR
    refine ⟨numV hM hNE (r / 2), hbcR, ?_, ?_⟩
    · cases d <;> exact numV_numeral hM hNE nq
    · cases d with
      | true => exact ⟨bitCons_numV hM hNE w l, rfl⟩
      | false =>
        let lb := l % 2 == 1
        have hl_eq : (if lb then 1 else 0) + 2 * (l / 2) = l := by
          dsimp only [lb]; have hmod : l % 2 = 0 ∨ l % 2 = 1 := by omega
          rcases hmod with h | h <;> simp [h] <;> omega
        have hlb_eq : (if lb then 1 else 0) = l % 2 := by
          dsimp only [lb]; have hmod : l % 2 = 0 ∨ l % 2 = 1 := by omega
          rcases hmod with h | h <;> simp [h]
        have hbcL := bitCons_numV hM hNE lb (l / 2)
        rw [hl_eq] at hbcL
        refine ⟨numV hM hNE (l / 2), lb, numV hM hNE ((if w then 1 else 0) + 2 * (r / 2)),
          hbcL, rfl,
          bitCons_numV hM hNE w (r / 2), ?_⟩
        dsimp only [tN]; rw [← hlb_eq]; exact bitCons_numV hM hNE lb _

private theorem internalReach_refl (hM : Model E) (hNE : Nonempty V) {c : V} (hc : NatObject E c) :
    InternalReach E c c := by
  obtain ⟨dom, hdom⟩ := exists_succ hM hNE (zeroV hM hNE)
  obtain ⟨f, hfun, hf0, hfat⟩ := functionOn_singleton hM hNE (zeroV_empty hM hNE) hdom (a := c)
  exact ⟨zeroV hM hNE, zeroV_nat hM hNE, hc, hc, zeroV hM hNE, dom, f, zeroV_empty hM hNE,
    hdom, hfun, hf0, hf0, fun i x _ h => (hfat i x h).2 ▸ hc, fun i hi => False.elim (zeroV_empty hM hNE i hi)⟩

private theorem internalReach_step (hM : Model E) (hNE : Nonempty V) {c1 c2 : V}
    (hc1 : NatObject E c1) (hc2 : NatObject E c2) (hns : NumericStep E c1 c2) : InternalReach E c1 c2 := by
  obtain ⟨f0, hfun0, hf00, hfat0⟩ := functionOn_singleton hM hNE (zeroV_empty hM hNE) (succV_spec hM hNE (zeroV hM hNE)) (a := c1)
  obtain ⟨f1, hfun1, hAt1⟩ := functionOn_extend hM hNE hfun0 (succV_spec hM hNE (numV hM hNE 1)) (y := c2)
  refine ⟨numV hM hNE 1, numV_nat hM hNE 1, hc1, hc2, zeroV hM hNE, numV hM hNE 2, f1,
    zeroV_empty hM hNE, succV_spec hM hNE _, hfun1,
    (hAt1 _ _).mpr (Or.inl hf00), (hAt1 _ _).mpr (Or.inr ⟨rfl, rfl⟩), fun i x _ h => ?_, fun i hi => ?_⟩
  · rcases (hAt1 i x).mp h with h0 | ⟨_, rfl⟩
    · exact (hfat0 i x h0).2 ▸ hc1
    · exact hc2
  · rcases (succV_spec hM hNE (zeroV hM hNE) i).mp hi with h0 | rfl
    · exact False.elim (zeroV_empty hM hNE i h0)
    · exact ⟨numV hM hNE 1, c1, c2, succV_spec hM hNE _,
        (hAt1 _ _).mpr (Or.inl hf00), (hAt1 _ _).mpr (Or.inr ⟨rfl, rfl⟩), hns⟩

private theorem lift_safeReach (hM : Model E) (hNE : Nonempty V) :
    ∀ n c, (∀ j < n, (iterPhysical j c).1 < 207) →
      InternalReach E (numV hM hNE (confCodeN c)) (numV hM hNE (confCodeN (iterPhysical n c)))
  | 0, c, _ => internalReach_refl hM hNE (numV_nat hM hNE _)
  | n + 1, c, hsafe => by
    have h0 : c.1 < 207 := hsafe 0 (Nat.zero_lt_succ n)
    have hstep := internalReach_step hM hNE (numV_nat hM hNE _) (numV_nat hM hNE _) (numericStep_physical hM hNE c h0)
    have hrest := lift_safeReach hM hNE n (stepPhysical c) (fun j hj => hsafe (j + 1) (Nat.succ_lt_succ hj))
    exact internalReach_trans hM hNE hstep hrest

private theorem pow2_numV (hM : Model E) (hNE : Nonempty V) :
    ∀ n, Pow2 E (numV hM hNE n) (numV hM hNE (2 ^ n))
  | 0 => by
    obtain ⟨f, hfun, hf0, hfat⟩ := functionOn_singleton hM hNE (zeroV_empty hM hNE) (succV_spec hM hNE (zeroV hM hNE)) (a := numV hM hNE 1)
    exact ⟨numV_nat hM hNE 0, numV_nat hM hNE 1, zeroV hM hNE, numV hM hNE 1, numV hM hNE 2, numV hM hNE 1, f,
      zeroV_empty hM hNE, numV_numeral hM hNE 1, numV_numeral hM hNE 2, succV_spec hM hNE _, hfun, hf0, hf0,
      fun i x _ h => (hfat i x h).2 ▸ numV_nat hM hNE 1, fun i hi => False.elim (zeroV_empty hM hNE i hi)⟩
  | n + 1 => by
    rcases pow2_numV hM hNE n with ⟨hn, _, z, one, two, dom, f, hz, h1, h2, hdom, hfun, hf0, hfn, hnat, hstep⟩
    have hdom_eq := succ_unique hM hNE hdom (succV_spec hM hNE (numV hM hNE n)); subst hdom_eq
    obtain ⟨f', hfun', hAt'⟩ := functionOn_extend hM hNE hfun (succV_spec hM hNE (numV hM hNE (n + 1))) (y := numV hM hNE (2 ^ (n + 1)))
    have hmul : Mul E two (numV hM hNE (2 ^ n)) (numV hM hNE (2 ^ (n + 1))) := by
      have h2eq := numeral_unique hM hNE h2 (numV_numeral hM hNE 2); subst h2eq
      have heq : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      exact heq ▸ (mul_iff_eq hM hNE (numV_nat hM hNE 2) (numV_nat hM hNE (2 ^ n))).mpr (mulV_numV hM hNE 2 (2 ^ n)).symm
    refine ⟨numV_nat hM hNE (n + 1), numV_nat hM hNE _, z, one, two, numV hM hNE (n + 2), f',
      hz, h1, h2, succV_spec hM hNE _, hfun', (hAt' _ _).mpr (Or.inl hf0), (hAt' _ _).mpr (Or.inr ⟨rfl, rfl⟩),
      fun i x _ h => ?_, fun i hi => ?_⟩
    · rcases (hAt' i x).mp h with h0 | ⟨_, rfl⟩
      · obtain ⟨q, hqf, hq⟩ := h0; obtain ⟨u, _, hud, huv⟩ := hfun.2 q hqf
        have := (orderedPair_inj hq huv).1; subst this; exact hnat i x hud ⟨q, hqf, hq⟩
      · exact numV_nat hM hNE _
    · rcases (succV_spec hM hNE (numV hM hNE n) i).mp hi with hin | rfl
      · obtain ⟨j, x, y, hij, hix, hjy, hm⟩ := hstep i hin
        exact ⟨j, x, y, hij, (hAt' i x).mpr (Or.inl hix), (hAt' j y).mpr (Or.inl hjy), hm⟩
      · exact ⟨numV hM hNE (n + 1), numV hM hNE (2 ^ n), numV hM hNE (2 ^ (n + 1)),
          succV_spec hM hNE _, (hAt' _ _).mpr (Or.inl hfn), (hAt' _ _).mpr (Or.inr ⟨rfl, rfl⟩), hmul⟩

private theorem ones_numV (hM : Model E) (hNE : Nonempty V) (n : Nat) :
    Ones E (numV hM hNE n) (numV hM hNE (2 ^ n - 1)) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hadd : (2 ^ n - 1) + 1 = 2 ^ n := by omega
  exact ⟨numV_nat hM hNE n, numV_nat hM hNE _, numV hM hNE (2 ^ n), numV hM hNE 1,
    pow2_numV hM hNE n, numV_numeral hM hNE 1,
    hadd ▸ (add_iff_eq hM hNE (numV_nat hM hNE _) (numV_nat hM hNE 1)).mpr (addV_numV hM hNE _ 1).symm⟩

private theorem tailBitsV_numV (hM : Model E) (hNE : Nonempty V) :
    ∀ t, TailBitsV E (numV hM hNE t) (numV hM hNE (tailBitsN t))
  | 0 => by
    obtain ⟨f, hfun, hf0, hfat⟩ := functionOn_singleton hM hNE (zeroV_empty hM hNE) (succV_spec hM hNE (zeroV hM hNE)) (a := zeroV hM hNE)
    exact ⟨numV_nat hM hNE 0, numV_nat hM hNE 0, zeroV hM hNE, numV hM hNE 6, numV hM hNE 8, numV hM hNE 1, f,
      zeroV_empty hM hNE, numV_numeral hM hNE 6, numV_numeral hM hNE 8, succV_spec hM hNE _, hfun, hf0, hf0,
      fun i x _ h => (hfat i x h).2 ▸ zeroV_nat hM hNE, fun i hi => False.elim (zeroV_empty hM hNE i hi)⟩
  | t + 1 => by
    rcases tailBitsV_numV hM hNE t with ⟨_, _, z, six, eight, dom, f, hz, h6, h8, hdom, hfun, hf0, hft, hnat, hstep⟩
    have hdom_eq := succ_unique hM hNE hdom (succV_spec hM hNE (numV hM hNE t)); subst hdom_eq
    have h6eq := numeral_unique hM hNE h6 (numV_numeral hM hNE 6); subst h6eq
    have h8eq := numeral_unique hM hNE h8 (numV_numeral hM hNE 8); subst h8eq
    obtain ⟨f', hfun', hAt'⟩ := functionOn_extend hM hNE hfun (succV_spec hM hNE (numV hM hNE (t + 1))) (y := numV hM hNE (tailBitsN (t + 1)))
    refine ⟨numV_nat hM hNE (t + 1), numV_nat hM hNE _, z, numV hM hNE 6, numV hM hNE 8, numV hM hNE (t + 2), f',
      hz, h6, h8, succV_spec hM hNE _, hfun', (hAt' _ _).mpr (Or.inl hf0), (hAt' _ _).mpr (Or.inr ⟨rfl, rfl⟩),
      fun i x _ h => ?_, fun i hi => ?_⟩
    · rcases (hAt' i x).mp h with h0 | ⟨_, rfl⟩
      · obtain ⟨q, hqf, hq⟩ := h0; obtain ⟨u, _, hud, huv⟩ := hfun.2 q hqf
        have := (orderedPair_inj hq huv).1; subst this; exact hnat i x hud ⟨q, hqf, hq⟩
      · exact numV_nat hM hNE _
    · rcases (succV_spec hM hNE (numV hM hNE t) i).mp hi with hit | rfl
      · obtain ⟨j, x, y, p, hij, hix, hjy, hm, ha⟩ := hstep i hit
        exact ⟨j, x, y, p, hij, (hAt' i x).mpr (Or.inl hix), (hAt' j y).mpr (Or.inl hjy), hm, ha⟩
      · exact ⟨numV hM hNE (t + 1), numV hM hNE (tailBitsN t), numV hM hNE (tailBitsN (t + 1)), numV hM hNE (8 * tailBitsN t),
          succV_spec hM hNE _, (hAt' _ _).mpr (Or.inl hft), (hAt' _ _).mpr (Or.inr ⟨rfl, rfl⟩),
          (mul_iff_eq hM hNE (numV_nat hM hNE 8) (numV_nat hM hNE _)).mpr (mulV_numV hM hNE 8 _).symm,
          (add_iff_eq hM hNE (numV_nat hM hNE 6) (numV_nat hM hNE _)).mpr (addV_numV hM hNE 6 _).symm⟩

private theorem regBlockV_numV (hM : Model E) (hNE : Nonempty V) (v suf : Nat) :
    RegBlockV E (numV hM hNE v) (numV hM hNE suf) (numV hM hNE (regBlockN v suf)) := by
  exact ⟨numV_nat hM hNE v, numV_nat hM hNE suf, numV_nat hM hNE _,
    numV hM hNE (v + 1), numV hM hNE (2 ^ (v + 1) - 1), numV hM hNE (2 ^ (v + 1)),
    numV hM hNE 2, numV hM hNE (2 ^ (v + 1) * suf), numV hM hNE ((2 ^ (v + 1) - 1) + 2 ^ (v + 1) * suf),
    succV_spec hM hNE _, ones_numV hM hNE (v + 1), pow2_numV hM hNE (v + 1), numV_numeral hM hNE 2,
    (mul_iff_eq hM hNE (numV_nat hM hNE _) (numV_nat hM hNE _)).mpr (mulV_numV hM hNE _ _).symm,
    (add_iff_eq hM hNE (numV_nat hM hNE _) (numV_nat hM hNE _)).mpr (addV_numV hM hNE _ _).symm,
    (mul_iff_eq hM hNE (numV_nat hM hNE 2) (numV_nat hM hNE _)).mpr (mulV_numV hM hNE 2 _).symm⟩

private theorem startup_in_model (hM : Model E) (hNE : Nonempty V) :
    ∃ c0 m t z two c1,
      Empty E c0 ∧ Empty E z ∧ Numeral E 2 two ∧ ¬ Empty E m ∧ ¬ Empty E t ∧
      FrameCodeV E 1 m ⟨z, z, z, z, z, z, two, z, z⟩ t c1 ∧ InternalReach E c0 c1 := by
  obtain ⟨k, hkeq, hksafe⟩ := startup_safe_reach
  have hreach := lift_safeReach hM hNE k (0, 0, 0) hksafe
  rw [hkeq] at hreach
  have hc0 : confCodeN (0, 0, 0) = 0 := rfl
  rw [hc0] at hreach
  let z := zeroV hM hNE
  let two := numV hM hNE 2
  let m := numV hM hNE 6
  let t := numV hM hNE 26
  have hmNE : ¬ Empty E m := fun he => he (numV hM hNE 5) ((succV_spec hM hNE (numV hM hNE 5) _).mpr (Or.inr rfl))
  have htNE : ¬ Empty E t := fun he => he (numV hM hNE 25) ((succV_spec hM hNE (numV hM hNE 25) _).mpr (Or.inr rfl))
  have hrb : RegsBitsV E ⟨z, z, z, z, z, z, two, z, z⟩ t (numV hM hNE (regsBitsN [0, 0, 0, 0, 0, 0, 2, 0, 0] 26)) :=
    ⟨numV hM hNE (tailBitsN 26),
     numV hM hNE (regsSuffixN [0] 26), numV hM hNE (regsSuffixN [0, 0] 26),
     numV hM hNE (regsSuffixN [2, 0, 0] 26), numV hM hNE (regsSuffixN [0, 2, 0, 0] 26),
     numV hM hNE (regsSuffixN [0, 0, 2, 0, 0] 26), numV hM hNE (regsSuffixN [0, 0, 0, 2, 0, 0] 26),
     numV hM hNE (regsSuffixN [0, 0, 0, 0, 2, 0, 0] 26), numV hM hNE (regsSuffixN [0, 0, 0, 0, 0, 2, 0, 0] 26),
     numV hM hNE (regsSuffixN [0, 0, 0, 0, 0, 0, 2, 0, 0] 26),
     numV hM hNE 1, numV hM hNE 2, numV hM hNE (2 * regsSuffixN [0, 0, 0, 0, 0, 0, 2, 0, 0] 26),
     tailBitsV_numV hM hNE 26,
     regBlockV_numV hM hNE 0 _, regBlockV_numV hM hNE 0 _, regBlockV_numV hM hNE 2 _,
     regBlockV_numV hM hNE 0 _, regBlockV_numV hM hNE 0 _, regBlockV_numV hM hNE 0 _,
     regBlockV_numV hM hNE 0 _, regBlockV_numV hM hNE 0 _, regBlockV_numV hM hNE 0 _,
     numV_numeral hM hNE 1, numV_numeral hM hNE 2,
     (mul_iff_eq hM hNE (numV_nat hM hNE 2) (numV_nat hM hNE _)).mpr (mulV_numV hM hNE 2 _).symm,
     (add_iff_eq hM hNE (numV_nat hM hNE 1) (numV_nat hM hNE _)).mpr (addV_numV hM hNE 1 _).symm⟩
  have hfr : FrameCodeV E 1 m ⟨z, z, z, z, z, z, two, z, z⟩ t
      (numV hM hNE (confCodeN (74, 1, 152919395647067130113387679226998336721518593))) := by
    refine ⟨numV_nat hM hNE 6, numV_nat hM hNE 26,
      ⟨zeroV_nat hM hNE, zeroV_nat hM hNE, zeroV_nat hM hNE, zeroV_nat hM hNE,
       zeroV_nat hM hNE, zeroV_nat hM hNE, numV_nat hM hNE 2, zeroV_nat hM hNE, zeroV_nat hM hNE⟩,
      numV hM hNE 74, numV hM hNE 1, numV hM hNE 42, numV hM hNE 1,
      numV hM hNE (42 + 6), numV hM hNE (2 ^ (42 + 6)),
      numV hM hNE (regsBitsN [0, 0, 0, 0, 0, 0, 2, 0, 0] 26),
      numV hM hNE (2 ^ (42 + 6) * regsBitsN [0, 0, 0, 0, 0, 0, 2, 0, 0] 26),
      numV hM hNE 152919395647067130113387679226998336721518593,
      numV_numeral hM hNE 74, numV_numeral hM hNE 1, numV_numeral hM hNE 42, numV_numeral hM hNE 1,
      (add_iff_eq hM hNE (numV_nat hM hNE 42) (numV_nat hM hNE 6)).mpr (addV_numV hM hNE 42 6).symm,
      pow2_numV hM hNE (42 + 6), hrb,
      (mul_iff_eq hM hNE (numV_nat hM hNE _) (numV_nat hM hNE _)).mpr (mulV_numV hM hNE _ _).symm,
      startup_right_eq ▸ (add_iff_eq hM hNE (numV_nat hM hNE 1) (numV_nat hM hNE _)).mpr (addV_numV hM hNE 1 _).symm,
      ⟨numV hM hNE (cantor 1 152919395647067130113387679226998336721518593),
       cantor_numV hM hNE 1 152919395647067130113387679226998336721518593,
       cantor_numV hM hNE 74 (cantor 1 152919395647067130113387679226998336721518593)⟩⟩
  exact ⟨z, m, t, z, two, _, zeroV_empty hM hNE, zeroV_empty hM hNE, numV_numeral hM hNE 2, hmNE, htNE, hfr, hreach⟩

end ZFModel

end SolInternalStartup

theorem solution :
    ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E →
      (∀ c, PalomarZF207History.Empty E c →
        PalomarZF207InternalTM.InternalHaltsFrom E c →
        PalomarZF207History.InternalLinkedHalts E) ∧
      (∀ c1 c2 c3,
        PalomarZF207InternalTM.InternalReach E c1 c2 →
        PalomarZF207InternalTM.InternalReach E c2 c3 →
        PalomarZF207InternalTM.InternalReach E c1 c3) ∧
      (∃ c0 m t z two c1,
        PalomarZF207History.Empty E c0 ∧
        PalomarZF207History.Empty E z ∧
        PalomarZF207History.Numeral E 2 two ∧
        ¬ PalomarZF207History.Empty E m ∧
        ¬ PalomarZF207History.Empty E t ∧
        PalomarZF207InternalTM.FrameCodeV E 1 m ⟨z, z, z, z, z, z, two, z, z⟩ t c1 ∧
        PalomarZF207InternalTM.InternalReach E c0 c1) := by
  intro V E hNE hM
  exact ⟨fun _ hc0 hh => SolInternalStartup.haltsFrom_implies_linkedHalts hM hNE hc0 hh,
         fun _ _ _ h1 h2 => SolInternalStartup.internalReach_trans hM hNE h1 h2,
         SolInternalStartup.startup_in_model hM hNE⟩
