-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T17:52:41.346953+00:00
-- url     : https://prove2.me/submissions/35ae3013-5f91-4be5-9e21-c0f08e204b68

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

private theorem headConv_step {G : HORS} {t u : Tm} (step : G.HeadStep t u) (a : ℕ) (us : List Tm) :
    G.HeadConv t a us ↔ G.HeadConv u a us := by
  constructor
  · rintro ⟨s, hs, spine⟩
    rcases hs.cases_head with rfl | ⟨s', h', htail⟩
    · simp [HORS.HeadStep, HORS.headStep, spine] at step
    · have eq : u = s' := Option.some.inj (step.symm.trans h')
      exact ⟨s, eq ▸ htail, spine⟩
  · rintro ⟨s, hs, spine⟩
    exact ⟨s, hs.head step, spine⟩

theorem obs_step {G : HORS} {t u : Tm} (hs : G.HeadStep t u) (w : List ℕ) (c : ℕ) :
    G.Obs t w c ↔ G.Obs u w c := by
  cases w <;> simp only [HORS.Obs, headConv_step hs]

private theorem real_step {G : HORS} {t u : Tm} {X : Val .o}
    (hs : G.HeadStep t u) (h : Real G .o u X) : Real G .o t X := by
  intro w a
  exact (obs_step hs w a).trans (h w a)

theorem terminal_conv {G : HORS} {t : Tm} {c : ℕ} {args : List Tm}
    (head : t.spine = (.tm c, args)) (a : ℕ) (us : List Tm) :
    G.HeadConv t a us ↔ c = a ∧ args = us := by
  constructor
  · rintro ⟨t', hs, h⟩
    rcases hs.cases_head with rfl | ⟨v, step, _⟩
    · simpa [head] using h
    · simp [HORS.HeadStep, HORS.headStep, head] at step
  · rintro ⟨rfl, rfl⟩
    exact ⟨t, .refl, head⟩

private theorem num_zero (side : Side) (M : Machine) : Num (compile side M) (.nt iZero) 0 := by
  refine ⟨rfl, fun f F hf hF x X hx hX => real_step (u := x) ?_ hX⟩
  rfl

private theorem num_one (side : Side) (M : Machine) : Num (compile side M) (.nt iOne) 1 := by
  refine ⟨rfl, fun f F hf hF x X hx hX => real_step (u := f.app x) ?_ (hF x X hx hX)⟩
  rfl

private theorem typed_app {G : HORS} {u v : Tm} {σ τ : Ty}
    (hu : G.typeOf [] u = some (.arr σ τ)) (hv : G.typeOf [] v = some σ) :
    G.typeOf [] (.app u v) = some τ := by simp [HORS.typeOf, hu, hv]

section
variable {side : Side} {M : Machine}
local notation "𝒢" => compile side M

private theorem num_succ {t : Tm} {m : ℕ} (ht : Num 𝒢 t m) :
    Num 𝒢 (.app (.nt iSucc) t) (m + 1) := by
  refine ⟨typed_app (σ := tyN) rfl ht.1, fun f F hf hF x X hx hX => ?_⟩
  change Real 𝒢 .o _ (F^[m + 1] X)
  rw [Function.iterate_succ_apply' (f := (F : Val .o → Val .o)) m X]
  exact real_step (u := f.app ((t.app f).app x)) rfl
    (hF _ _ (typed_app (typed_app ht.1 hf) hx) (ht.2 f F hf hF x X hx hX))

private theorem num_add {t u : Tm} {m n : ℕ} (ht : Num 𝒢 t m) (hu : Num 𝒢 u n) :
    Num 𝒢 (Tm.apps (.nt iAdd) [t, u]) (m + n) := by
  refine ⟨typed_app (typed_app (σ := tyN) (τ := .arr tyN tyN) rfl ht.1) hu.1,
    fun f F hf hF x X hx hX => ?_⟩
  change Real 𝒢 .o _ (F^[m + n] X)
  rw [Function.iterate_add_apply (F : Val .o → Val .o) m n X]
  exact real_step (u := (t.app f).app ((u.app f).app x)) rfl
    (ht.2 f F hf hF _ _ (typed_app (typed_app hu.1 hf) hx) (hu.2 f F hf hF x X hx hX))

private theorem num_mul {t u : Tm} {m n : ℕ} (ht : Num 𝒢 t m) (hu : Num 𝒢 u n) :
    Num 𝒢 (Tm.apps (.nt iMul) [t, u]) (m * n) := by
  refine ⟨typed_app (typed_app (σ := tyN) (τ := .arr tyN tyN) rfl ht.1) hu.1,
    fun f F hf hF x X hx hX => ?_⟩
  change Real 𝒢 .o _ (F^[m * n] X)
  rw [Nat.mul_comm, Function.iterate_mul (F : Val .o → Val .o) n m]
  exact real_step (u := (t.app (u.app f)).app x) rfl
    (ht.2 (u.app f) _ (typed_app hu.1 hf) (hu.2 f F hf hF) x X hx hX)

private theorem num_rule {t u : Tm} {n : ℕ} (ht : (𝒢).typeOf [] t = some tyN)
    (hs : ∀ f x, (𝒢).HeadStep ((t.app f).app x) ((u.app f).app x)) (hu : Num 𝒢 u n) :
    Num 𝒢 t n :=
  ⟨ht, fun f F hf hF x X hx hX => real_step (hs f x) (hu.2 f F hf hF x X hx hX)⟩

private theorem num_pair {t₁ t₂ t₃ t₄ : Tm} {a b c d : ℕ}
    (h₁ : Num 𝒢 t₁ a) (h₂ : Num 𝒢 t₂ b) (h₃ : Num 𝒢 t₃ c) (h₄ : Num 𝒢 t₄ d) :
    Num 𝒢 (Tm.apps (.nt iPos) [t₁, t₂, t₃, t₄]) (a * c + b * d) ∧
    Num 𝒢 (Tm.apps (.nt iNeg) [t₁, t₂, t₃, t₄]) (a * d + b * c) := by
  constructor
  · refine num_rule ?_ (fun _ _ => by rfl) (num_add (num_mul h₁ h₃) (num_mul h₂ h₄))
    exact typed_app (typed_app (typed_app (typed_app rfl h₁.1) h₂.1) h₃.1) h₄.1
  · refine num_rule ?_ (fun _ _ => by rfl) (num_add (num_mul h₁ h₄) (num_mul h₂ h₃))
    exact typed_app (typed_app (typed_app (typed_app rfl h₁.1) h₂.1) h₃.1) h₄.1

end

private theorem proved_here (side : Side) (M : Machine) :
    let G := compile side M
    Pol G 0 (.nt iSeedP) (.nt iSeedM) ∧
    ∀ (m : ℕ) (p q : Tm), Pol G m p q →
      Pol G (m + 1) (Tm.apps (.nt iNextP) [p, q]) (Tm.apps (.nt iNextM) [p, q]) := by
  constructor
  · refine ⟨rfl, rfl, fun u v t s ht hs => ?_⟩
    constructor
    · exact num_rule (typed_app (typed_app rfl ht.1) hs.1) (fun _ _ => by rfl) (num_one side M)
    · exact num_rule (typed_app (typed_app rfl ht.1) hs.1) (fun _ _ => by rfl) (num_zero side M)
  · rintro m p q ⟨hp, hq, hpol⟩
    refine ⟨typed_app (typed_app rfl hp) hq, typed_app (typed_app rfl hp) hq,
      fun u v t s ht hs => ?_⟩
    obtain ⟨hplus, hminus⟩ := hpol u (v + 1) t _ ht (num_succ hs)
    obtain ⟨hl, hr⟩ := num_pair ht (num_succ hs) hplus hminus
    constructor
    · exact num_rule (typed_app (typed_app (typed_app (typed_app rfl hp) hq) ht.1) hs.1)
        (fun _ _ => by rfl) hl
    · exact num_rule (typed_app (typed_app (typed_app (typed_app rfl hp) hq) ht.1) hs.1)
        (fun _ _ => by rfl) hr

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (side : Side) (M : Machine) :
    let G := compile side M
    Pol G 0 (.nt iSeedP) (.nt iSeedM) ∧
    ∀ (m : ℕ) (p q : Tm), Pol G m p q →
      Pol G (m + 1) (Tm.apps (.nt iNextP) [p, q]) (Tm.apps (.nt iNextM) [p, q]) := proved_here side M
