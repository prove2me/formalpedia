-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_lemma_4_6_corrected_mult_agree_qtame
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T21:28:09.472082+00:00
-- url     : https://prove2.me/submissions/2a650d33-4de3-4aa3-a31a-7df6864ad66e

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

/-!
# Child 2 of corrected Lemma 4.6 — diagram agreement on `QNE α`

`PersistClust.Count.theorem_4_5_lemma_4_6_corrected_mult_agree_qtame` (Step 2 of the corrected
Lemma 4.6 route, Appendix A of RR-6968): for a q-TAME module (`FiltrationLaw` with all
structure ranks finite — the paper's standing q-tameness assumption), the diagram
`mult (rankFn stage J)` agrees with its `α`-truncation
`mult (truncRank (rankFn stage J) α)` on the closed north-east quadrant `QNE α`.

FALSITY NOTE (this child supersedes the finite-support variant, whose statement is FALSE):
without q-tameness the agreement fails. Counterexample: a hub point (immortal class), one
class born `b` dying `d`, and countably many classes at a single bar `(β, δ)` with
`δ < α < d < b < β`. The countable bar makes `A = B = ⊤` at every probe scale `ε ≥ ε*`, so
the ORIGINAL bracket `(A − B) − (C − D)` collapses to `⊤ − ⊤ − (C − D) = 0` for `ε ≥ ε*`
while it stays `1` for `ε < ε*`; with `ε* > d − α` the zero is hidden from the α-isolated
zone and `mult_orig (b,d) = 0`. The TRUNCATED bracket loses the `(·, d − ε)` pair below `α`
(it becomes `0`) while the pair `A − B` stays `1`-or-`⊤` throughout, so `mult_trunc (b,d) = 1`.
The support `{p | mult ≠ 0}` is finite here (the hub bar and the countable bar only), so a
finite-support hypothesis does not exclude this module. Q-tameness does: all corner ranks are
finite, every bracket is ℕ-valued, the bracket is monotone in `ε` (window nesting) and the
infimum is attained, so the small-ε attainment inside the E18 zone goes through.

Decomposition of the proof (mandated work order):
  (E18)   ranks agree above `α`: `truncRank r α s t = r s t` whenever `α ≤ s ∧ α ≤ t`.
          Near-trivial: it is exactly the `if_pos` branch of the `truncRank` definition.
  (CONST) interval-constancy of the window counts between the finite support values: from
          `FiltrationLaw` antitone + the finite-support hypothesis, the bracket integrands are
          locally constant (as functions of `ε`) off a finite set of critical `ε`-values.
  (GRID)  the η-grid reduction (Eqs. 19–22): the `⨅`-brackets are attained at a grid-constant `ε`
          that places every probed window strictly above `α`, where (E18) identifies original and
          truncated ranks.
  (AGREE) assembly: for `p ∈ QNE α`, evaluate both `⨅`-brackets at the same grid-constant `ε`.
-/

open PersistClust.Count

/-- **(E18)** Eq. 18: above the truncation level the truncated rank equals the original rank.
`truncRank r a s t = if a ≤ s ∧ a ≤ t then r s t else 0`, so once both windows are `≥ a` the
`if_pos` branch fires. -/
private lemma trunc_rank_eq_above_α (r : ℝ → ℝ → ℕ∞) (a : ℝ) :
    ∀ s t : ℝ, a ≤ s → a ≤ t → truncRank r a s t = r s t := by
  intro s t hs ht
  show (if a ≤ s ∧ a ≤ t then r s t else 0) = r s t
  exact if_pos ⟨hs, ht⟩

/-- Below the truncation level the truncated rank is `0`. -/
private lemma trunc_rank_zero_below (r : ℝ → ℝ → ℕ∞) (a s t : ℝ)
    (h : ¬ (a ≤ s ∧ a ≤ t)) : truncRank r a s t = 0 := by
  show (if a ≤ s ∧ a ≤ t then r s t else 0) = 0
  exact if_neg h

/-- **(R-MON-2)** the rank is nondecreasing in its second argument (the component level):
`J` merges classes as the threshold decreases (`FiltrationLaw.compat`), so a higher level `t2`
refines the classes of a lower level `t1 ≤ t2`, and a finer partition meets `stage s` in at
least as many classes. Hence `t1 ≤ t2 ≤ s` implies `rankFn s t1 ≤ rankFn s t2`. Proof: the
coarsening map sends each `J t2`-class `K = {y | J t2 x y}` (for `x ∈ stage s`) to the
`J t1`-class `g1 x`; it is well defined because `g2 x = g2 x'` (same `t2`-class, `x, x' ∈
stage s ⊆ stage t2`) forces `J t2 x' x` (refl + the class equality), hence `J t1 x' x`
(`compat`), hence `g1 x = g1 x'` (equivalence). So `g1 '' stage s` is a surjective image of
`g2 '' stage s` (up to a choice-function), giving the encard bound. -/
private lemma rankFn_monotone_second
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) {s t1 t2 : ℝ}
    (ht : t1 ≤ t2) (hst : t2 ≤ s) :
    rankFn stage J s t1 ≤ rankFn stage J s t2 := by
  unfold rankFn
  classical
  set g1 : ι → Set ι := fun x => {y | J t1 x y} with hg1def
  set g2 : ι → Set ι := fun x => {y | J t2 x y} with hg2def
  have hss2 : ∀ x, x ∈ stage s → x ∈ stage t2 := fun x hx => hLaw.antitone hst hx
  -- well-definedness of the coarsening: same `t2`-class ⟹ same `t1`-class
  have key : ∀ {x x' : ι}, x ∈ stage s → x' ∈ stage s → g2 x = g2 x' → g1 x = g1 x' := by
    intro x x' hx hx' heq
    have hx2 : x ∈ stage t2 := hss2 x hx
    have hx'2 : x' ∈ stage t2 := hss2 x' hx'
    have hJ2 : J t2 x' x := by
      have hmem : x ∈ g2 x := hLaw.refl hx2
      rw [heq] at hmem
      exact hmem
    have hJ1 : J t1 x' x := hLaw.compat ht hJ2
    ext y
    constructor
    · intro h
      exact hLaw.trans hJ1 h
    · intro h
      exact hLaw.trans (hLaw.symm hJ1) h
  -- the coarsening function on class-sets
  set F : Set ι → Set ι :=
    fun K => if h : ∃ x : ι, x ∈ stage s ∧ g2 x = K then g1 (Classical.choose h) else ∅ with hFdef
  have hsub : g1 '' stage s ⊆ F '' (g2 '' stage s) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨g2 x, ⟨x, hx, rfl⟩, ?_⟩
    have h : ∃ x' : ι, x' ∈ stage s ∧ g2 x' = g2 x := ⟨x, hx, rfl⟩
    have hF2 : F (g2 x) = g1 (Classical.choose h) := by
      simp only [hFdef]
      exact dif_pos h
    rw [hF2]
    exact key (Classical.choose_spec h).1 hx (Classical.choose_spec h).2
  calc (g1 '' stage s).encard
      ≤ (F '' (g2 '' stage s)).encard := Set.encard_le_encard hsub
    _ ≤ (g2 '' stage s).encard := Set.encard_image_le F (g2 '' stage s)

/-- **(R-ANT)** the rank is antitone in its first argument: a higher level holds a smaller
stage, hence a smaller image and a smaller count. -/
private lemma rankFn_antitone_first
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) {s1 s2 t : ℝ} (h : s1 ≤ s2) :
    rankFn stage J s2 t ≤ rankFn stage J s1 t := by
  unfold rankFn
  refine Set.encard_le_encard (fun y hy => ?_)
  exact hy.imp fun x hx => ⟨hLaw.antitone h hx.1, hx.2⟩

/-- `encard` is submodular under images: for `B ⊆ A`, `A.encard + (f '' B).encard ≥
(f '' A).encard + B.encard`. Finiteness-free in `ℕ∞` (infinite cases collapse to `⊤` on both
sides); the finite case is the usual excess argument via `encard_sdiff`. -/
private lemma encard_submod_image {α β : Type*} (A B : Set α) (hBA : B ⊆ A) (f : α → β) :
    A.encard + (f '' B).encard ≥ (f '' A).encard + B.encard := by
  by_cases hA : A.Finite
  · have hB : B.Finite := hA.subset hBA
    have hAB : (A \ B).encard = A.encard - B.encard := Set.encard_sdiff hBA hB
    have hImg : f '' A = f '' B ∪ f '' (A \ B) := by
      ext x
      refine ⟨?_, ?_⟩
      · rintro ⟨a, ha, hfa⟩
        by_cases hab : a ∈ B
        · exact Or.inl ⟨a, hab, hfa⟩
        · exact Or.inr ⟨a, ⟨ha, hab⟩, hfa⟩
      · rintro (⟨a, ha, hfa⟩ | ⟨a, ha, hfa⟩)
        · exact ⟨a, hBA ha, hfa⟩
        · exact ⟨a, ha.1, hfa⟩
    have hLe : (f '' A).encard ≤ (f '' B).encard + (A \ B).encard := by
      rw [hImg]
      calc (f '' B ∪ f '' (A \ B)).encard
          ≤ (f '' B).encard + (f '' (A \ B)).encard := Set.encard_union_le _ _
        _ ≤ (f '' B).encard + (A \ B).encard :=
            add_le_add le_rfl (Set.encard_image_le f (A \ B))
    have hBlA : B.encard ≤ A.encard := Set.encard_le_encard hBA
    calc (f '' A).encard + B.encard
        ≤ ((f '' B).encard + (A \ B).encard) + B.encard := add_le_add hLe le_rfl
      _ = (f '' B).encard + ((A \ B).encard + B.encard) := by ac_rfl
      _ = (f '' B).encard + ((A.encard - B.encard) + B.encard) := by rw [hAB]
      _ = (f '' B).encard + A.encard := by rw [tsub_add_cancel_of_le hBlA]
      _ = A.encard + (f '' B).encard := by ac_rfl
  · have hAtop : A.encard = ⊤ := Set.encard_eq_top (fun h => hA h)
    rw [hAtop, top_add]
    exact le_top

/-- **(M3 / SUBMODULARITY)** the rank is submodular: for `s1 ≤ s2`, `u1 ≤ u2` with `u2 ≤ s1`,
`rankFn stage J s1 u2 + rankFn stage J s2 u1 ≥ rankFn stage J s1 u1 + rankFn stage J s2 u2`.
Equivalently the window-count `rankFn stage J s1 u - rankFn stage J s2 u` is nondecreasing in `u`.
Finiteness-free via `encard_submod_image` and the refinement parent-map
`h K = {z | ∃ y ∈ K, J u1 y z}` (well-defined because `u2 ≤ s` puts every `x ∈ stage s` inside
`stage u2`, so `J u2 x x`). -/
private lemma rankFn_submodular
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) {s1 s2 u1 u2 : ℝ}
    (hs : s1 ≤ s2) (hu : u1 ≤ u2) (hsu : u2 ≤ s1) :
    rankFn stage J s1 u2 + rankFn stage J s2 u1 ≥
      rankFn stage J s1 u1 + rankFn stage J s2 u2 := by
  let h : Set ι → Set ι := fun K => {z | ∃ y ∈ K, J u1 y z}
  have key : ∀ x, x ∈ stage u2 → h {y | J u2 x y} = {y | J u1 x y} := by
    intro x hxu2
    show {z | ∃ y ∈ {y | J u2 x y}, J u1 y z} = {y | J u1 x y}
    ext z
    simp only [Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, hyz⟩
      exact hLaw.trans (hLaw.compat hu hy) hyz
    · intro hz
      exact ⟨x, hLaw.refl hxu2, hz⟩
  have hC : ∀ s, u2 ≤ s →
      h '' ((fun x => {y | J u2 x y}) '' stage s) = (fun x => {y | J u1 x y}) '' stage s := by
    intro s hsu2
    ext L
    refine ⟨?_, ?_⟩
    · rintro ⟨K, ⟨x, hx, hKx⟩, hKL⟩
      subst hKx
      have hxu2 : x ∈ stage u2 := hLaw.antitone hsu2 hx
      exact ⟨x, hx, (key x hxu2).symm.trans hKL⟩
    · rintro ⟨x, hx, hLx⟩
      have hxu2 : x ∈ stage u2 := hLaw.antitone hsu2 hx
      refine ⟨{y | J u2 x y}, ⟨x, hx, rfl⟩, ?_⟩
      rw [key x hxu2]
      exact hLx
  -- C(s2, u2) ⊆ C(s1, u2) via antitone stage (s1 ≤ s2)
  have hsub : ((fun x => {y | J u2 x y}) '' stage s2) ⊆
      ((fun x => {y | J u2 x y}) '' stage s1) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hLaw.antitone hs hx, rfl⟩
  show ((fun x => {y | J u2 x y}) '' stage s1).encard +
        ((fun x => {y | J u1 x y}) '' stage s2).encard ≥
        ((fun x => {y | J u1 x y}) '' stage s1).encard +
        ((fun x => {y | J u2 x y}) '' stage s2).encard
  rw [← hC s1 hsu, ← hC s2 (hsu.trans hs)]
  exact encard_submod_image _ _ hsub h

/-- **(EASY)** For `p ∈ QNE α`, `mult (rankFn stage J) p ≤ mult (truncRank (rankFn stage J) α) p`.
All `mult` guards depend only on `p`, so they take the same branch on both sides; in the
finite-death bracket, truncation acts only on the two `(·, d - ε)` corners (and only when
`d - ε < α`), where it replaces the (nonneg-subtracted-by-construction) second pair by `0`,
which can only increase the bracket via `tsub_le_self`. -/
private lemma mult_le_mult_trunc
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) (α : ℝ)
    (p : EReal × EReal) (hp : p ∈ QNE α) :
    mult (rankFn stage J) p ≤ mult (truncRank (rankFn stage J) α) p := by
  obtain ⟨hQ1, hQ2⟩ := hp
  have h1bot : p.1 ≠ ⊥ := fun h => not_lt_bot (h ▸ hQ1)
  have h2bot : p.2 ≠ ⊥ := fun h => not_lt_bot (h ▸ hQ2)
  by_cases h1top : p.1 = ⊤
  · -- outer guard `p.1 ≠ ⊤` fails on both sides ⇒ both `0`
    have hO : ¬ (p.1 ≠ ⊥ ∧ p.1 ≠ ⊤) := fun h => h.2 h1top
    simp only [mult, if_neg hO, le_refl]
  · -- else branch: `h1top : ¬(p.1 = ⊤)`, i.e. `p.1 ≠ ⊤`; p.1 is real
    have hO : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤ := ⟨h1bot, h1top⟩
    by_cases hpdb : p.2 < p.1
    · -- finite-death bracket: the real work
      have h2netop : p.2 ≠ ⊤ := ne_of_lt (hpdb.trans_le le_top)
      have h1real : p.1 = ↑p.1.toReal := (EReal.coe_toReal h1top h1bot).symm
      have h2real : p.2 = ↑p.2.toReal := (EReal.coe_toReal h2netop h2bot).symm
      have hb : α < p.1.toReal := EReal.coe_strictMono.lt_iff_lt.mp (h1real ▸ hQ1)
      have hd : α < p.2.toReal := EReal.coe_strictMono.lt_iff_lt.mp (h2real ▸ hQ2)
      have hdb : p.2.toReal < p.1.toReal :=
        EReal.coe_strictMono.lt_iff_lt.mp (h1real ▸ (h2real ▸ hpdb))
      -- unfold both `mult`s into the finite-death `⨅`-bracket
      simp only [mult, if_pos hO, if_neg h2bot, if_pos hpdb]
      -- pointwise bracket_orig ε ≤ bracket_trunc ε
      have pointwise :
        ∀ ε, ε ∈ Set.Ioo 0 ((p.1.toReal - p.2.toReal) / 2) →
          (rankFn stage J (p.1.toReal - ε) (p.2.toReal + ε) -
              rankFn stage J (p.1.toReal + ε) (p.2.toReal + ε) -
            (rankFn stage J (p.1.toReal - ε) (p.2.toReal - ε) -
              rankFn stage J (p.1.toReal + ε) (p.2.toReal - ε)))
          ≤
          (truncRank (rankFn stage J) α (p.1.toReal - ε) (p.2.toReal + ε) -
              truncRank (rankFn stage J) α (p.1.toReal + ε) (p.2.toReal + ε) -
            (truncRank (rankFn stage J) α (p.1.toReal - ε) (p.2.toReal - ε) -
              truncRank (rankFn stage J) α (p.1.toReal + ε) (p.2.toReal - ε))) := by
        intro ε hε
        obtain ⟨hε1, hε2⟩ := hε
        have hbe : α < p.1.toReal - ε := by linarith
        have hbpe : α < p.1.toReal + ε := by linarith
        have hdpe : α < p.2.toReal + ε := by linarith
        have e1 : truncRank (rankFn stage J) α (p.1.toReal - ε) (p.2.toReal + ε) =
            rankFn stage J (p.1.toReal - ε) (p.2.toReal + ε) :=
          trunc_rank_eq_above_α _ _ _ _ (le_of_lt hbe) (le_of_lt hdpe)
        have e2 : truncRank (rankFn stage J) α (p.1.toReal + ε) (p.2.toReal + ε) =
            rankFn stage J (p.1.toReal + ε) (p.2.toReal + ε) :=
          trunc_rank_eq_above_α _ _ _ _ (le_of_lt hbpe) (le_of_lt hdpe)
        by_cases q : α ≤ p.2.toReal - ε
        · have e3 : truncRank (rankFn stage J) α (p.1.toReal - ε) (p.2.toReal - ε) =
              rankFn stage J (p.1.toReal - ε) (p.2.toReal - ε) :=
            trunc_rank_eq_above_α _ _ _ _ (le_of_lt hbe) q
          have e4 : truncRank (rankFn stage J) α (p.1.toReal + ε) (p.2.toReal - ε) =
              rankFn stage J (p.1.toReal + ε) (p.2.toReal - ε) :=
            trunc_rank_eq_above_α _ _ _ _ (le_of_lt hbpe) q
          simp only [e1, e2, e3, e4]
          exact le_rfl
        · have nq3 : ¬ (α ≤ p.1.toReal - ε ∧ α ≤ p.2.toReal - ε) := fun h => q h.2
          have e3 : truncRank (rankFn stage J) α (p.1.toReal - ε) (p.2.toReal - ε) = 0 :=
            trunc_rank_zero_below _ _ _ _ nq3
          have nq4 : ¬ (α ≤ p.1.toReal + ε ∧ α ≤ p.2.toReal - ε) := fun h => q h.2
          have e4 : truncRank (rankFn stage J) α (p.1.toReal + ε) (p.2.toReal - ε) = 0 :=
            trunc_rank_zero_below _ _ _ _ nq4
          simp only [e1, e2, e3, e4, tsub_zero, tsub_self]
          exact tsub_le_self
      refine le_iInf fun ε => le_iInf fun hε => ?_
      exact (iInf_le_of_le ε (iInf_le_of_le hε le_rfl)).trans (pointwise ε hε)
    · -- inner `p.2 < p.1` guard fails on both sides ⇒ both `0`
      simp only [mult, if_pos hO, if_neg h2bot, if_neg hpdb, le_refl]

/-! ### EASY-DIRECTION MECHANISM (orchestrator, verified by hand — for the successor)

For `p ∈ QNE α` (both coords strictly `> α`), `mult (rankFn stage J) p ≤
mult (truncRank (rankFn stage J) α) p` as follows. All guards of the `mult` unfolding
(`p.1 ≠ ⊥ ∧ p.1 ≠ ⊤`, then `p.2 = ⊥` vs `p.2 < p.1`) depend only on `p`, so they take the
SAME branch on both sides; `p ∈ QNE α` excludes `p.2 = ⊥` (else `α < ⊥`), excludes `p.1 = ⊥`,
and in the `p.2 < p.1` branch both coordinates are real (`p.1 = ⊤` makes `p.2 < p.1`
impossible unless `p.2 = ⊥`... handle `p.1 = ⊤` separately: outer guard false on BOTH sides,
so both mults are `0`).

In the finite-death bracket case, write `b = p.1.toReal`, `d = p.2.toReal` (real, `d < b`,
`α < d`). For `ε ∈ Ioo 0 ((b-d)/2)`:
* `d + ε > d > α` and `b - ε > (b+d)/2 > d > α`, `b + ε > b - ε > α`: the four
  `(·, d + ε)` and `(b ± ε, ·)` corners NEVER get truncated;
* only the two `(·, d - ε)` corners truncate, and they truncate TOGETHER (when
  `d - ε < α`).
Hence `bracket_trunc ε = firstPair - secondPair_trunc` where `secondPair_trunc = 0 - 0 = 0`
when truncated and `secondPair_trunc = secondPair` otherwise, while `firstPair` is unchanged:
pointwise `bracket_orig ε ≤ bracket_trunc ε` via `tsub` monotonicity (a subtrahend that is
`0` or the original nonnegative pair; use `tsub_le_self` / `tsub_zero` or the `ENat`
equivalents, and `rankFn_antitone_first` for `0 ≤ secondPair`).
Conclude with `le_iInf` + `iInf_le_of_le` (the `⨅` over the same range on both sides).
The iInf dance: `refine le_iInf fun ε => ?_`; for `ε` in the range
`(iInf_le_of_le hmem le_rfl).trans (pointwise ε)`; for `ε` out of the range the inner
membership-`⨅` is `⊤` (empty index), so `le_top`-reasoning closes it.
-/


/-- **(ATTAIN)** STEP 1: the `⨅`-bracket in `mult` (finite-death case) is ATTAINED at some
`ε*` in the interval. For any `ℕ∞`-valued integrand `f` on a nonempty open interval
`Set.Ioo 0 c`, the infimum `⨅ ε ∈ Set.Ioo 0 c, f ε` is realized: `ℕ∞` is well-founded under
`<`, so the nonempty image `f '' (Set.Ioo 0 c)` has a least member, which is a lower bound of
the whole image and hence equals the `⨅`. -/
private lemma bracket_attain (f : ℝ → ℕ∞) {c : ℝ} (hc : 0 < c) :
    ∃ ε : ℝ, ε ∈ Set.Ioo 0 c ∧
      f ε = ⨅ (ε : ℝ) (_ : ε ∈ Set.Ioo 0 c), f ε := by
  set S := Set.Ioo (0:ℝ) c with hSdef
  have hne : S.Nonempty := ⟨c / 2, ⟨by linarith, by linarith⟩⟩
  have hwf : WellFounded (· < · : ℕ∞ → ℕ∞ → Prop) := (inferInstance : WellFoundedLT ℕ∞).wf
  obtain ⟨n, ⟨a, ha, hn⟩, hnle⟩ :
      ∃ n ∈ f '' S, ∀ m ∈ f '' S, n ≤ m :=
    ⟨hwf.min (f '' S) (hne.image f),
     hwf.min_mem (f '' S) (hne.image f),
     fun m hm => le_of_not_gt (hwf.not_lt_min (f '' S) hm)⟩
  refine ⟨a, ha, ?_⟩
  refine le_antisymm ?_ ?_
  · -- `f a = n ≤ ⨅`: `n` is a lower bound of the image
    rw [hn]
    refine le_iInf fun b => le_iInf fun (hb : b ∈ S) => ?_
    exact hnle (f b) ⟨b, hb, rfl⟩
  · -- `⨅ ≤ f a = n`: evaluate the `⨅` at `a` (and at the membership witness `ha`)
    exact (iInf_le (fun ε => ⨅ (_ : ε ∈ S), f ε) a).trans
      (iInf_le (fun (_ : a ∈ S) => f a) ha)

/-- **(TSUB-ALG)** `ℕ∞` subtraction algebra in the finite regime: from `c + d ≤ a + b` with all
four values finite, conclude `c - b ≤ a - d`. Proved by extracting the underlying `ℕ`s
(`ENat.natCast_toNat`) and dispatching to `omega`. -/
private lemma enat_tsub_le_of_add_le
    (a b c d : ℕ∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (h : c + d ≤ a + b) : c - b ≤ a - d := by
  obtain ⟨a', ha'⟩ : ∃ n : ℕ, a = n := ⟨_, (ENat.natCast_toNat ha).symm⟩
  obtain ⟨b', hb'⟩ : ∃ n : ℕ, b = n := ⟨_, (ENat.natCast_toNat hb).symm⟩
  obtain ⟨c', hc'⟩ : ∃ n : ℕ, c = n := ⟨_, (ENat.natCast_toNat hc).symm⟩
  obtain ⟨d', hd'⟩ : ∃ n : ℕ, d = n := ⟨_, (ENat.natCast_toNat hd).symm⟩
  subst ha' hb' hc' hd'
  have h1 : c' + d' ≤ a' + b' := Nat.cast_le.mp (by simpa using h)
  have hs : ((c' - b' : ℕ) : ℕ∞) ≤ ((a' - d' : ℕ) : ℕ∞) := Nat.cast_le.mpr (by omega)
  rw [show (c' : ℕ∞) - (b' : ℕ∞) = ((c' - b' : ℕ) : ℕ∞) from by norm_cast,
      show (a' : ℕ∞) - (d' : ℕ∞) = ((a' - d' : ℕ) : ℕ∞) from by norm_cast]
  exact hs

/-- **(RUNG A)** Finiteness at ε*: if the 4-corner bracket `(A−B)−(C−D)` equals `MO` with
`0 < MO < ⊤`, then the two birth-high/birth-low-vs-death-high corners `A` and `B` are FINITE
(`< ⊤`). The ⊤−⊤ trap is ruled out by `ℕ∞`-tsub arithmetic: the three trapping corner-patterns
(`A=B=⊤`, `A=⊤∧B<⊤`, `A<⊤∧B=⊤`) each force the bracket into `{0, ⊤}`, contradicting
`0 < MO < ⊤`. Pure `ℕ∞` arithmetic (no `rankFn`); the death corners `C, D` need not be finite
here (their finiteness follows later from `C ≤ A`, `D ≤ B` via second-argument monotonicity). -/
private lemma bracket_finite_corners_at
    (A B C D MO : ℕ∞)
    (hbr : (A - B) - (C - D) = MO) (hMOpos : 0 < MO) (hMOtop : MO ≠ ⊤) :
    A ≠ ⊤ ∧ B ≠ ⊤ := by
  by_cases hA : A = ⊤
  · -- A = ⊤
    by_cases hB : B = ⊤
    · -- A = ⊤, B = ⊤ : pair1 = ⊤ − ⊤ = 0, bracket = 0 − (C−D) = 0
      rw [hA, hB, ENat.sub_top, zero_tsub] at hbr
      exact absurd hbr.symm hMOpos.ne'
    · -- A = ⊤, B < ⊤ : pair1 = ⊤ − B = ⊤; bracket = ⊤ − (C−D) ∈ {⊤, 0}
      have hAB : (⊤ : ℕ∞) - B = ⊤ := ENat.sub_eq_top_iff.mpr ⟨rfl, hB⟩
      rw [hA, hAB] at hbr
      by_cases hCD : C - D = ⊤
      · -- ⊤ − ⊤ = 0
        rw [hCD, ENat.sub_top] at hbr
        exact absurd hbr.symm hMOpos.ne'
      · -- ⊤ − (C−D) = ⊤ (since C−D ≠ ⊤)
        rw [ENat.sub_eq_top_iff.mpr ⟨rfl, hCD⟩] at hbr
        exact absurd hbr.symm hMOtop
  · by_cases hB : B = ⊤
    · -- A < ⊤, B = ⊤ : pair1 = A − ⊤ = 0, bracket = 0 − (C−D) = 0
      have hAB : A - (⊤ : ℕ∞) = 0 := ENat.sub_top A
      rw [hB, hAB, zero_tsub] at hbr
      exact absurd hbr.symm hMOpos.ne'
    · exact ⟨hA, hB⟩

/-- **(RUNG B)** Finiteness propagation: if `MO > 0` is attained at `ε*` in the bracket
interval `(0, (b−d)/2)` (with all `mult`-bracket corners unrapped there), then at EVERY
`ε ∈ (0, ε*]` ALL FOUR corner ranks
`A ε = r(b−ε, d+ε)`, `B ε = r(b+ε, d+ε)`, `C ε = r(b−ε, d−ε)`, `D ε = r(b+ε, d−ε)`
are finite (`≠ ⊤`). Key steps:
* **sandwich** `A ε ≤ A ε* < ⊤`: `b−ε* ≤ b−ε` (antitone-first) and `d+ε ≤ d+ε*`
  (monotone-second);
* `bracket ε ≥ MO > 0` (`⊤`-safe ⨅-bound) forces `pair1 = A ε − B ε ≠ 0`, hence `B ε < A ε`
  (else `tsub_eq_zero_iff_le` gives `pair1 = 0`), so `B ε < A ε < ⊤`;
* **the ⊤−⊤ trap is IMPOSSIBLE for the death corners**: `C ε ≤ A ε` and `D ε ≤ B ε` by
  second-argument monotonicity (`r(s,·)` nondecreasing in the level, same first argument),
  so once `A, B` are finite all four are.
Also exported: the pointwise lower bound `MO ≤ bracket ε`. -/
private lemma bracket_finite_corners_below
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) {b d : ℝ} (hdb : d < b) (εs : ℝ)
    (hεs : εs ∈ Set.Ioo 0 ((b - d) / 2)) (MO : ℕ∞)
    (hMOpos : 0 < MO) (hMOtop : MO ≠ ⊤)
    (hεsbr : ((rankFn stage J (b - εs) (d + εs) - rankFn stage J (b + εs) (d + εs)) -
               (rankFn stage J (b - εs) (d - εs) - rankFn stage J (b + εs) (d - εs))) = MO)
    (hMOle : ∀ ε ∈ Set.Ioo 0 ((b - d) / 2),
      MO ≤ ((rankFn stage J (b - ε) (d + ε) - rankFn stage J (b + ε) (d + ε)) -
              (rankFn stage J (b - ε) (d - ε) - rankFn stage J (b + ε) (d - ε)))) :
    ∀ ε ∈ Set.Ioo 0 εs,
      rankFn stage J (b - ε) (d + ε) ≠ ⊤ ∧ rankFn stage J (b + ε) (d + ε) ≠ ⊤ ∧
        rankFn stage J (b - ε) (d - ε) ≠ ⊤ ∧ rankFn stage J (b + ε) (d - ε) ≠ ⊤ := by
  intro ε hε
  obtain ⟨hε1, hε2⟩ := hε
  obtain ⟨hεs1, hεs2⟩ := hεs
  -- the ε-window constraints: `d + ε ≤ b − ε` and `d + εs ≤ b − εs`
  have hεlt : ε < (b - d) / 2 := hε2.trans hεs2
  have hεslt : εs < (b - d) / 2 := hεs2
  have hbdε : d + ε ≤ b - ε := by linarith
  have hbdεs : d + εs ≤ b - εs := by linarith
  -- sandwich: `A ε ≤ A ε*`
  have hAsand : rankFn stage J (b - ε) (d + ε) ≤ rankFn stage J (b - εs) (d + εs) := by
    calc rankFn stage J (b - ε) (d + ε)
        ≤ rankFn stage J (b - εs) (d + ε) :=
          rankFn_antitone_first stage J hLaw (by linarith)
      _ ≤ rankFn stage J (b - εs) (d + εs) :=
          rankFn_monotone_second stage J hLaw (by linarith) hbdεs
  -- RUNG A at ε*
  obtain ⟨hAstop, hBstop⟩ := bracket_finite_corners_at
    (rankFn stage J (b - εs) (d + εs)) (rankFn stage J (b + εs) (d + εs))
    (rankFn stage J (b - εs) (d - εs)) (rankFn stage J (b + εs) (d - εs)) MO
    hεsbr hMOpos hMOtop
  have hAε : rankFn stage J (b - ε) (d + ε) ≠ ⊤ := by
    intro h
    rw [h] at hAsand
    exact hAstop (top_le_iff.mp hAsand)
  -- `pair1 ≠ 0` from `bracket ε ≥ MO > 0` (⊤-safe ⨅-bound)
  have hMOε : MO ≤ ((rankFn stage J (b - ε) (d + ε) - rankFn stage J (b + ε) (d + ε)) -
      (rankFn stage J (b - ε) (d - ε) - rankFn stage J (b + ε) (d - ε))) :=
    hMOle ε ⟨hε1, hεlt⟩
  have hpair1 : (rankFn stage J (b - ε) (d + ε) - rankFn stage J (b + ε) (d + ε)) ≠ 0 := by
    intro h
    rw [h, zero_tsub] at hMOε
    exact hMOpos.ne' (le_zero_iff.mp hMOε)
  -- `B ε < A ε < ⊤`
  have hBlt : rankFn stage J (b + ε) (d + ε) < rankFn stage J (b - ε) (d + ε) := by
    by_contra hcon
    exact hpair1 (tsub_eq_zero_iff_le.mpr (not_lt.mp hcon))
  have hBε : rankFn stage J (b + ε) (d + ε) ≠ ⊤ := by
    intro h
    rw [h] at hBlt
    exact lt_irrefl ⊤ (hBlt.trans_le le_top)
  -- the ⊤−⊤ trap is impossible: death corners bounded by birth corners (2nd-arg monotone)
  have hCle : rankFn stage J (b - ε) (d - ε) ≤ rankFn stage J (b - ε) (d + ε) :=
    rankFn_monotone_second stage J hLaw (by linarith) hbdε
  have hCε : rankFn stage J (b - ε) (d - ε) ≠ ⊤ := by
    intro h
    rw [h] at hCle
    exact hAε (top_le_iff.mp hCle)
  have hDle : rankFn stage J (b + ε) (d - ε) ≤ rankFn stage J (b + ε) (d + ε) :=
    rankFn_monotone_second stage J hLaw (by linarith) (by linarith)
  have hDε : rankFn stage J (b + ε) (d - ε) ≠ ⊤ := by
    intro h
    rw [h] at hDle
    exact hBε (top_le_iff.mp hDle)
  exact ⟨hAε, hBε, hCε, hDε⟩

/-- **(M3-FINITE)** window-count monotonicity in the level, finite regime (att9's sub-form M3 is
FALSE at `⊤`, but with all four probed ranks finite it holds): for `s1 ≤ s2`, `u1 ≤ u2 ≤ s1`,
`rankFn s1 · - rankFn s2 ·` is nondecreasing in the level, i.e.
`rankFn s1 u1 - rankFn s2 u1 ≤ rankFn s1 u2 - rankFn s2 u2`. Additive submodularity
(`rankFn_submodular`, `⊤`-safe) rearranged via `enat_tsub_le_of_add_le`. -/
private lemma rank_window_mono_finite
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) {s1 s2 u1 u2 : ℝ}
    (hs : s1 ≤ s2) (hu : u1 ≤ u2) (hsu : u2 ≤ s1)
    (hf1 : rankFn stage J s1 u1 ≠ ⊤) (hf2 : rankFn stage J s2 u1 ≠ ⊤)
    (hf3 : rankFn stage J s1 u2 ≠ ⊤) (hf4 : rankFn stage J s2 u2 ≠ ⊤) :
    rankFn stage J s1 u1 - rankFn stage J s2 u1 ≤
      rankFn stage J s1 u2 - rankFn stage J s2 u2 := by
  have hsub : rankFn stage J s1 u1 + rankFn stage J s2 u2 ≤
      rankFn stage J s1 u2 + rankFn stage J s2 u1 := by
    have := rankFn_submodular stage J hLaw hs hu hsu
    exact this
  exact enat_tsub_le_of_add_le
    (rankFn stage J s1 u2) (rankFn stage J s2 u1) (rankFn stage J s1 u1) (rankFn stage J s2 u2)
    hf3 hf2 hf1 hf4 hsub

/-- **(BIRTHDIFF-GROWTH)** the birth-window count `rankFn (b-δ) t - rankFn (b+δ) t` is nondecreasing
in the birth-window half-width `δ` (a bigger birth window catches more components). Stated in the
`⊤`-SAFE ADDITIVE form `r(b-δ,t) + r(b+δ',t) ≤ r(b-δ',t) + r(b+δ,t)` for `δ ≤ δ'`, which is just
`rankFn_antitone_first` twice plus `add_le_add` (no subtraction, valid at `⊤`). The single-`tsub`
form `r(b-δ,t) - r(b+δ,t) ≤ r(b-δ',t) - r(b+δ',t)` follows in the finite regime. -/
private lemma rank_birthdiff_grow_add
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) {b δ δ' t : ℝ}
    (hδ : δ ≤ δ') (hbδ : b + δ' ≤ b - δ) :
    rankFn stage J (b - δ) t + rankFn stage J (b + δ') t ≤
      rankFn stage J (b - δ') t + rankFn stage J (b + δ) t := by
  -- `b - δ' ≤ b - δ` and `b + δ ≤ b + δ'`; antitone in the first argument gives both summands
  have h1 : b - δ' ≤ b - δ := by gcongr
  have h2 : b + δ ≤ b + δ' := by gcongr
  have e1 : rankFn stage J (b - δ) t ≤ rankFn stage J (b - δ') t :=
    rankFn_antitone_first stage J hLaw h1
  have e2 : rankFn stage J (b + δ') t ≤ rankFn stage J (b + δ) t :=
    rankFn_antitone_first stage J hLaw h2
  exact add_le_add e1 e2

/-- **(P-SET-INCL)** For `s₁ ≤ s₂`, the P-set `P(s₂,t) := (fun x => {y | J t x y}) '' stage s₂`
is contained in `P(s₁,t)`. Pure image-monotonicity: `stage s₂ ⊆ stage s₁` (antitone), and the
image of a subset under the same map is a subset. This is the set-level form of
`rankFn_antitone_first`. -/
private lemma Pset_subset {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) {s1 s2 t : ℝ} (h : s1 ≤ s2) :
    ((fun x => {y | J t x y}) '' stage s2) ⊆ ((fun x => {y | J t x y}) '' stage s1) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hLaw.antitone h hx, rfl⟩

/-- **(RUNG 0 / MONO-SMALL)** Bracket monotonicity in the small regime: for `ε₁ ≤ ε₂` both in
`(0, (b−d)/2)`, with all four corner ranks finite at each, `bracket(ε₁) ≤ bracket(ε₂)`, where
`bracket(ε) := (r(b−ε,d+ε) − r(b+ε,d+ε)) − (r(b−ε,d−ε) − r(b+ε,d−ε))`. The bracket counts the
net growth of the birth-window gap as the death window widens; supermodularity (M3) of the rank
plus single-argument monotonicity telescopes to this inequality in the finite regime. -/
private lemma bracket_mono_small
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) {b d : ℝ} (hdb : d < b) (ε₁ ε₂ : ℝ)
    (h₁ : ε₁ ∈ Set.Ioo 0 ((b - d) / 2)) (h₂ : ε₂ ∈ Set.Ioo 0 ((b - d) / 2)) (hle : ε₁ ≤ ε₂)
    (hA1 : rankFn stage J (b - ε₁) (d + ε₁) ≠ ⊤)
    (hB1 : rankFn stage J (b + ε₁) (d + ε₁) ≠ ⊤)
    (hC1 : rankFn stage J (b - ε₁) (d - ε₁) ≠ ⊤)
    (hD1 : rankFn stage J (b + ε₁) (d - ε₁) ≠ ⊤)
    (hA2 : rankFn stage J (b - ε₂) (d + ε₂) ≠ ⊤)
    (hB2 : rankFn stage J (b + ε₂) (d + ε₂) ≠ ⊤)
    (hC2 : rankFn stage J (b - ε₂) (d - ε₂) ≠ ⊤)
    (hD2 : rankFn stage J (b + ε₂) (d - ε₂) ≠ ⊤) :
    ((rankFn stage J (b - ε₁) (d + ε₁) - rankFn stage J (b + ε₁) (d + ε₁)) -
      (rankFn stage J (b - ε₁) (d - ε₁) - rankFn stage J (b + ε₁) (d - ε₁))) ≤
      ((rankFn stage J (b - ε₂) (d + ε₂) - rankFn stage J (b + ε₂) (d + ε₂)) -
        (rankFn stage J (b - ε₂) (d - ε₂) - rankFn stage J (b + ε₂) (d - ε₂))) := by
  obtain ⟨hε₁pos, hε₁lt⟩ := h₁
  obtain ⟨hε₂pos, hε₂lt⟩ := h₂
  -- mixed corners, each bounded by a finite corner (so also finite)
  have hM₁le : rankFn stage J (b - ε₁) (d - ε₂) ≤ rankFn stage J (b - ε₁) (d - ε₁) :=
    rankFn_monotone_second stage J hLaw (by linarith) (by linarith)
  have hM₂le : rankFn stage J (b - ε₁) (d + ε₂) ≤ rankFn stage J (b - ε₂) (d + ε₂) :=
    rankFn_antitone_first stage J hLaw (by linarith)
  have hM₃le : rankFn stage J (b + ε₂) (d + ε₁) ≤ rankFn stage J (b + ε₂) (d + ε₂) :=
    rankFn_monotone_second stage J hLaw (by linarith) (by linarith)
  have hM₁top : rankFn stage J (b - ε₁) (d - ε₂) ≠ ⊤ := by
    intro h
    have hle' : (⊤ : ℕ∞) ≤ rankFn stage J (b - ε₁) (d - ε₁) := by rw [← h]; exact hM₁le
    exact hC1 (top_le_iff.mp hle')
  have hM₂top : rankFn stage J (b - ε₁) (d + ε₂) ≠ ⊤ := by
    intro h
    have hle' : (⊤ : ℕ∞) ≤ rankFn stage J (b - ε₂) (d + ε₂) := by rw [← h]; exact hM₂le
    exact hA2 (top_le_iff.mp hle')
  have hM₃top : rankFn stage J (b + ε₂) (d + ε₁) ≠ ⊤ := by
    intro h
    have hle' : (⊤ : ℕ∞) ≤ rankFn stage J (b + ε₂) (d + ε₂) := by rw [← h]; exact hM₃le
    exact hB2 (top_le_iff.mp hle')
  have hM₄le : rankFn stage J (b + ε₂) (d - ε₁) ≤ rankFn stage J (b + ε₁) (d - ε₁) :=
    rankFn_antitone_first stage J hLaw (by linarith)
  have hM₄top : rankFn stage J (b + ε₂) (d - ε₁) ≠ ⊤ := by
    intro h
    have hle' : (⊤ : ℕ∞) ≤ rankFn stage J (b + ε₁) (d - ε₁) := by rw [← h]; exact hM₄le
    exact hD1 (top_le_iff.mp hle')
  -- three submodularity instances (crossed ≥ aligned)
  have hΔ₁ : rankFn stage J (b - ε₂) (d + ε₂) + rankFn stage J (b - ε₁) (d - ε₂) ≥
      rankFn stage J (b - ε₂) (d - ε₂) + rankFn stage J (b - ε₁) (d + ε₂) :=
    rankFn_submodular stage J hLaw (by linarith) (by linarith) (by linarith)
  have hΔ₂ : rankFn stage J (b + ε₁) (d + ε₁) + rankFn stage J (b + ε₂) (d - ε₁) ≥
      rankFn stage J (b + ε₁) (d - ε₁) + rankFn stage J (b + ε₂) (d + ε₁) :=
    rankFn_submodular stage J hLaw (by linarith) (by linarith) (by linarith)
  have hΔ₃ : rankFn stage J (b - ε₁) (d + ε₂) + rankFn stage J (b + ε₂) (d + ε₁) ≥
      rankFn stage J (b - ε₁) (d + ε₁) + rankFn stage J (b + ε₂) (d + ε₂) :=
    rankFn_submodular stage J hLaw (by linarith) (by linarith) (by linarith)
  -- window nonnegativity at each probe level (collapses the ℕ-truncated subtraction)
  have hA₁B₁ : rankFn stage J (b + ε₁) (d + ε₁) ≤ rankFn stage J (b - ε₁) (d + ε₁) :=
    rankFn_antitone_first stage J hLaw (by linarith)
  have hA₂B₂ : rankFn stage J (b + ε₂) (d + ε₂) ≤ rankFn stage J (b - ε₂) (d + ε₂) :=
    rankFn_antitone_first stage J hLaw (by linarith)
  have hC₁D₁ : rankFn stage J (b + ε₁) (d - ε₁) ≤ rankFn stage J (b - ε₁) (d - ε₁) :=
    rankFn_antitone_first stage J hLaw (by linarith)
  have hC₂D₂ : rankFn stage J (b + ε₂) (d - ε₂) ≤ rankFn stage J (b - ε₂) (d - ε₂) :=
    rankFn_antitone_first stage J hLaw (by linarith)
  -- fourth submodularity instance (the low-window telescoping piece)
  have hI₉ : rankFn stage J (b - ε₁) (d - ε₁) + rankFn stage J (b + ε₂) (d - ε₂) ≥
      rankFn stage J (b - ε₁) (d - ε₂) + rankFn stage J (b + ε₂) (d - ε₁) :=
    rankFn_submodular stage J hLaw (by linarith) (by linarith) (by linarith)
  -- extract all twelve values as naturals
  obtain ⟨a1, ha1⟩ : ∃ n : ℕ, rankFn stage J (b - ε₁) (d + ε₁) = n :=
    ⟨_, (ENat.natCast_toNat hA1).symm⟩
  obtain ⟨b1, hb1⟩ : ∃ n : ℕ, rankFn stage J (b + ε₁) (d + ε₁) = n :=
    ⟨_, (ENat.natCast_toNat hB1).symm⟩
  obtain ⟨c1, hc1⟩ : ∃ n : ℕ, rankFn stage J (b - ε₁) (d - ε₁) = n :=
    ⟨_, (ENat.natCast_toNat hC1).symm⟩
  obtain ⟨d1, hd1⟩ : ∃ n : ℕ, rankFn stage J (b + ε₁) (d - ε₁) = n :=
    ⟨_, (ENat.natCast_toNat hD1).symm⟩
  obtain ⟨a2, ha2⟩ : ∃ n : ℕ, rankFn stage J (b - ε₂) (d + ε₂) = n :=
    ⟨_, (ENat.natCast_toNat hA2).symm⟩
  obtain ⟨b2, hb2⟩ : ∃ n : ℕ, rankFn stage J (b + ε₂) (d + ε₂) = n :=
    ⟨_, (ENat.natCast_toNat hB2).symm⟩
  obtain ⟨c2, hc2⟩ : ∃ n : ℕ, rankFn stage J (b - ε₂) (d - ε₂) = n :=
    ⟨_, (ENat.natCast_toNat hC2).symm⟩
  obtain ⟨d2, hd2⟩ : ∃ n : ℕ, rankFn stage J (b + ε₂) (d - ε₂) = n :=
    ⟨_, (ENat.natCast_toNat hD2).symm⟩
  obtain ⟨m1, hm1⟩ : ∃ n : ℕ, rankFn stage J (b - ε₁) (d - ε₂) = n :=
    ⟨_, (ENat.natCast_toNat hM₁top).symm⟩
  obtain ⟨m2, hm2⟩ : ∃ n : ℕ, rankFn stage J (b - ε₁) (d + ε₂) = n :=
    ⟨_, (ENat.natCast_toNat hM₂top).symm⟩
  obtain ⟨m3, hm3⟩ : ∃ n : ℕ, rankFn stage J (b + ε₂) (d + ε₁) = n :=
    ⟨_, (ENat.natCast_toNat hM₃top).symm⟩
  obtain ⟨m4, hm4⟩ : ∃ n : ℕ, rankFn stage J (b + ε₂) (d - ε₁) = n :=
    ⟨_, (ENat.natCast_toNat hM₄top).symm⟩
  rw [ha1, hb1, hc1, hd1, ha2, hb2, hc2, hd2] at ⊢
  rw [ha2, hm1, hc2, hm2] at hΔ₁
  rw [hb1, hm4, hd1, hm3] at hΔ₂
  rw [hm2, hm3, ha1, hb2] at hΔ₃
  rw [hc1, hd2, hm1, hm4] at hI₉
  rw [ha1, hb1] at hA₁B₁
  rw [ha2, hb2] at hA₂B₂
  rw [hc1, hd1] at hC₁D₁
  rw [hc2, hd2] at hC₂D₂
  norm_cast at hΔ₁ hΔ₂ hΔ₃ hI₉ hA₁B₁ hA₂B₂ hC₁D₁ hC₂D₂
  rw [show ((a1 : ℕ∞) - (b1 : ℕ∞)) = ((a1 - b1 : ℕ) : ℕ∞) from by norm_cast,
      show ((c1 : ℕ∞) - (d1 : ℕ∞)) = ((c1 - d1 : ℕ) : ℕ∞) from by norm_cast,
      show ((a1 - b1 : ℕ) : ℕ∞) - ((c1 - d1 : ℕ) : ℕ∞) =
          (((a1 - b1) - (c1 - d1) : ℕ) : ℕ∞) from by norm_cast,
      show ((a2 : ℕ∞) - (b2 : ℕ∞)) = ((a2 - b2 : ℕ) : ℕ∞) from by norm_cast,
      show ((c2 : ℕ∞) - (d2 : ℕ∞)) = ((c2 - d2 : ℕ) : ℕ∞) from by norm_cast,
      show ((a2 - b2 : ℕ) : ℕ∞) - ((c2 - d2 : ℕ) : ℕ∞) =
          (((a2 - b2) - (c2 - d2) : ℕ) : ℕ∞) from by norm_cast]
  exact Nat.cast_le.mpr (by omega)

/-- **(AGREE)** assembly: for `p ∈ QNE α`, the original and truncated `mult` agree.

The EASY direction `mult_orig ≤ mult_trunc` is `mult_le_mult_trunc`: truncation only acts on
the two `(·, d - ε)` corners of the finite-death bracket (only when `d - ε < α`), replacing the
second pair by `0`, which can only increase the bracket (`tsub_le_self`).

The HARD direction `mult_trunc ≤ mult_orig` needs the original `⨅`-bracket's infimum to be
ATTAINED at a small `ε` with all probes `> α` (there (E18) identifies the two brackets, so
`mult_trunc ≤ bracket_trunc ε₀ = bracket_orig ε₀ = mult_orig` via `iInf_le`). Attainment
follows from BRACKET MONOTONICITY in `ε` (M3 window monotonicity: with
`rankFn stage J s t = ((fun x => {y | J t x y}) '' stage s).encard`, rank-differences rewrite
as set-difference encards — diff-encard idiom: nested images from `FiltrationLaw.antitone` +
`Set.encard_sdiff` + `Set.toFinite` — making the bracket the count of component-classes born
in the birth-window dying in the death-window, a growing 2-d window, hence monotone in `ε`)
plus `ℕ∞`-well-foundedness (a nondecreasing `ℕ∞`-valued function on `(0, c)` stabilises near
`0`, so its `⨅` is attained). Resolution (orchestrator): the window-set FINITENESS follows
from q-TAMENESS (`hQ : ∀ s t, rankFn stage J s t ≠ ⊤`, the paper's standing assumption),
which replaces the finite-support hypothesis of the superseded variant: with `hQ` all
corner ranks are finite, `bracket_mono_small` transports the attained value from the
attainment scale `εs` to any smaller α-isolated `ε₀`, and both MO-branches close. Without
`hQ` the statement is FALSE (see the falsity note in the file header). `hFin` is no longer
needed anywhere in the proof. -/
private lemma mult_agree_QNE
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) (α : ℝ)
    (hQ : ∀ s t : ℝ, rankFn stage J s t ≠ ⊤)
    (p : EReal × EReal) (hp : p ∈ QNE α) :
    mult (rankFn stage J) p = mult (truncRank (rankFn stage J) α) p := by
  refine le_antisymm ?_ ?_
  · -- easy direction: truncation only removes a (nonneg) subtrahend
    exact mult_le_mult_trunc stage J hLaw α p hp
  · -- hard direction: mult_trunc ≤ mult_orig
    obtain ⟨hQ1, hQ2⟩ := hp
    have h1bot : p.1 ≠ ⊥ := fun h => not_lt_bot (h ▸ hQ1)
    have h2bot : p.2 ≠ ⊥ := fun h => not_lt_bot (h ▸ hQ2)
    by_cases h1top : p.1 = ⊤
    · -- outer guard `p.1 ≠ ⊤` fails on both sides ⇒ both mults are `0`
      have hO : ¬ (p.1 ≠ ⊥ ∧ p.1 ≠ ⊤) := fun h => h.2 h1top
      simp only [mult, if_neg hO, le_refl]
    · have hO : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤ := ⟨h1bot, h1top⟩
      by_cases hpdb : p.2 < p.1
      · -- finite-death bracket: the real work
        have h2netop : p.2 ≠ ⊤ := ne_of_lt (hpdb.trans_le le_top)
        have h1real : p.1 = ↑p.1.toReal := (EReal.coe_toReal h1top h1bot).symm
        have h2real : p.2 = ↑p.2.toReal := (EReal.coe_toReal h2netop h2bot).symm
        have hb : α < p.1.toReal := EReal.coe_strictMono.lt_iff_lt.mp (h1real ▸ hQ1)
        have hd : α < p.2.toReal := EReal.coe_strictMono.lt_iff_lt.mp (h2real ▸ hQ2)
        have hdb : p.2.toReal < p.1.toReal :=
          EReal.coe_strictMono.lt_iff_lt.mp (h1real ▸ (h2real ▸ hpdb))
        have hc : 0 < (p.1.toReal - p.2.toReal) / 2 := by linarith
        -- unfold both `mult`s into the finite-death `⨅`-bracket
        simp only [mult, if_pos hO, if_neg h2bot, if_pos hpdb]
        -- name the original-bracket infimum (the RHS) for the ⊤-case-split
        set MO := ⨅ (ε : ℝ) (_ : ε ∈ Set.Ioo 0 ((p.1.toReal - p.2.toReal) / 2)),
            ((rankFn stage J (p.1.toReal - ε) (p.2.toReal + ε) -
                rankFn stage J (p.1.toReal + ε) (p.2.toReal + ε)) -
              (rankFn stage J (p.1.toReal - ε) (p.2.toReal - ε) -
                rankFn stage J (p.1.toReal + ε) (p.2.toReal - ε)))
        -- STEP 2: if `mult_orig = ⊤` the hard direction is `le_top`
        by_cases htop : MO = ⊤
        · rw [htop]; exact le_top
        · -- mult_orig < ⊤: attainment + isolation chain (STEP 3–5).
          -- SUCCESSOR NOTE (att11, crux analysis — DO NOT re-derive, it cost 11 attempts):
          -- Goal here: `(⨅ ε ∈ Ioo 0 c, bracket_trunc ε) ≤ MO`, with `MO = mult_orig < ⊤`.
          -- SUFFICES: ∃ ε₀ ∈ (0, min (d−α) c), bracket_orig ε₀ = MO  (attainment in the
          --   E18-subinterval). Then: `mult_trunc ≤ bracket_trunc ε₀` [iInf_le] `= bracket_orig
          --   ε₀` [E18, ε₀ < d−α ⟹ all four probes > α] `= MO`. Chain is ONE line once ε₀ exists.
          -- The crux is attainment-in-the-subinterval = bracket MONOTONICITY in ε (so the infimum
          -- is reached near 0). Decomposition of `bracket(δ,ρ) := (r(b−δ,d+ρ)−r(b+δ,d+ρ)) −
          --   (r(b−δ,d−ρ)−r(b+δ,d−ρ))` monotone in (δ,ρ):
          --  * DEATH-growth (fix δ, grow ρ): ⊤-SAFE. = two single-tsub steps from M3
          --    (`rank_window_mono_finite` is the finite form; the additive M3 = `rankFn_submodular`
          --    is ⊤-safe). `bd_δ(t) := r(b−δ,t)−r(b+δ,t)` is nondecreasing in t.
          --  * BIRTH-growth (fix ρ, grow δ): needs JOINT supermodularity of `bd` in (δ,t),
          --    i.e. `bd_δ(t₁)+bd_{δ'}(t₂) ≥ bd_δ(t₂)+bd_{δ'}(t₁)` — 4th-order, NOT ⊤-safe.
          -- THE ⊤−⊤ TRAP: `bracket(ε*) = MO < ⊤` does NOT force the four ranks finite
          --    (e.g. `A = B = ⊤ ⟹ A − B = 0`, value `0` via truncation). So finite-regime
          --    monotonicity cannot be unlocked from attainment alone.
          -- TWO KNOWN ESCAPES (both need new machinery, not yet banked):
          --  (I) MO > 0 ⟹ ranks A,B at ε* ARE finite (A=B=⊤ gives value 0 ≠ MO>0; A=⊤,B<⊤ gives
          --      A−B=⊤ forcing bracket∈{0,⊤}). Propagate finiteness to small ε via antitone +
          --      `bracket(ε₀) ≥ MO > 0` (⊤-safe inf bound) excluding the trap at ε₀. Then
          --      birth-growth via `enat_tsub_le_of_add_le` (extract 8 nats, `omega`). Handle
          --      MO = 0 separately (ENat-valued ⟹ inf 0 IS attained; need it at small ε —
          --      possibly via the death-growth ⊤-safe half + a limit argument).
          --  (II) ADDENDUM isolation: hFin ⟹ window at ε_s contains only the (b,d)-support point
          --      ⟹ `bracket = m₀` there (reading `bracket = encard W(ε)`, `encard_sdiff`, finite
          --      at isolated window). Needs the COMPONENT↔SUPPORT-POINT correspondence: a class
          --      `c ∈ W(ε)` (born β, dies δ) satisfies `mult(β,δ) ≥ 1` (the exact-(β,δ) classes
          --      sit inside every (β,δ)-window ⟹ bracket ≥ 1, ⊤-safe `encard_mono`), so
          --      `(β,δ) ∈ support`; isolation excludes `(β,δ) ≠ (b,d)`. This correspondence is the
          --      persistence-theorem content (define birth/death of a `J_t`-class from
          --      `FiltrationLaw`); it is the large missing piece.
          -- Banked reusable pieces (this lane + the surgery sibling's `surgery_massX/Y`):
          --   `bracket_attain`, `enat_tsub_le_of_add_le`, `rank_window_mono_finite`,
          --   `rank_birthdiff_grow_add`, the ⊤-case-split shell, `mult_le_mult_trunc`.
          -- RUNG 2: reduction to attainment at a small ε (the crux lemma, still sorried).
          -- The hard direction reduces to: ∃ ε₀ in the range, with d−ε₀ > α (for E18),
          -- such that bracket_orig(ε₀) = MO (attainment near 0). Then:
          --   mult_trunc ≤ bracket_trunc(ε₀) [iInf_le_of_le]
          --             = bracket_orig(ε₀)   [E18: all probes > α]
          --             = MO                  [attainment]
          have attain_small : ∃ ε₀ : ℝ,
              ε₀ ∈ Set.Ioo 0 ((p.1.toReal - p.2.toReal) / 2) ∧
              α < p.2.toReal - ε₀ ∧
              ((rankFn stage J (p.1.toReal - ε₀) (p.2.toReal + ε₀) -
                  rankFn stage J (p.1.toReal + ε₀) (p.2.toReal + ε₀)) -
                (rankFn stage J (p.1.toReal - ε₀) (p.2.toReal - ε₀) -
                  rankFn stage J (p.1.toReal + ε₀) (p.2.toReal - ε₀))) = MO := by
            by_cases hMO0 : MO = 0
            · -- MO = 0 branch: q-tameness (`hQ`) makes every corner rank finite, so the
              -- zero attained at `εs` (inf-of-ℕ∞ attainment) transports to any smaller
              -- α-isolated `ε₀` by bracket monotonicity (`bracket_mono_small`).
              obtain ⟨εs, hεs, hεsbr⟩ := bracket_attain
                (fun ε => ((rankFn stage J (p.1.toReal - ε) (p.2.toReal + ε) -
                    rankFn stage J (p.1.toReal + ε) (p.2.toReal + ε)) -
                  (rankFn stage J (p.1.toReal - ε) (p.2.toReal - ε) -
                    rankFn stage J (p.1.toReal + ε) (p.2.toReal - ε)))) hc
              have hbrs : ((rankFn stage J (p.1.toReal - εs) (p.2.toReal + εs) -
                  rankFn stage J (p.1.toReal + εs) (p.2.toReal + εs)) -
                (rankFn stage J (p.1.toReal - εs) (p.2.toReal - εs) -
                  rankFn stage J (p.1.toReal + εs) (p.2.toReal - εs))) = MO := hεsbr
              have hεs1 : 0 < εs := hεs.1
              have hεs2 : εs < (p.1.toReal - p.2.toReal) / 2 := hεs.2
              -- the ⨅ is a pointwise lower bound of the bracket (⊤-safe)
              have hMOle : ∀ ε ∈ Set.Ioo 0 ((p.1.toReal - p.2.toReal) / 2),
                  MO ≤ ((rankFn stage J (p.1.toReal - ε) (p.2.toReal + ε) -
                      rankFn stage J (p.1.toReal + ε) (p.2.toReal + ε)) -
                    (rankFn stage J (p.1.toReal - ε) (p.2.toReal - ε) -
                      rankFn stage J (p.1.toReal + ε) (p.2.toReal - ε))) :=
                fun ε hε => iInf_le_of_le ε (iInf_le_of_le hε le_rfl)
              -- the witness: positive, in range, α-isolated, strictly below εs
              obtain ⟨ε₀, hε₀pos, hε₀ltc, hα₀, hε₀εs, hε₀lts⟩ :
                  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < (p.1.toReal - p.2.toReal) / 2 ∧
                    α < p.2.toReal - ε₀ ∧ ε₀ ≤ εs ∧ ε₀ < εs := by
                refine ⟨min (min (εs / 2) ((p.2.toReal - α) / 2))
                    ((p.1.toReal - p.2.toReal) / 4), ?_, ?_, ?_, ?_, ?_⟩
                · exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
                · have h1 : min (min (εs / 2) ((p.2.toReal - α) / 2))
                      ((p.1.toReal - p.2.toReal) / 4) ≤ (p.1.toReal - p.2.toReal) / 4 :=
                    min_le_right _ _
                  linarith
                · have h1 : min (min (εs / 2) ((p.2.toReal - α) / 2))
                      ((p.1.toReal - p.2.toReal) / 4) ≤ (p.2.toReal - α) / 2 :=
                    (min_le_left _ _).trans (min_le_right _ _)
                  linarith
                · have h1 : min (min (εs / 2) ((p.2.toReal - α) / 2))
                      ((p.1.toReal - p.2.toReal) / 4) ≤ εs / 2 :=
                    (min_le_left _ _).trans (min_le_left _ _)
                  linarith
                · have h1 : min (min (εs / 2) ((p.2.toReal - α) / 2))
                      ((p.1.toReal - p.2.toReal) / 4) ≤ εs / 2 :=
                    (min_le_left _ _).trans (min_le_left _ _)
                  linarith
              -- q-tameness: all eight corner ranks are finite; monotone transport
              have hmono := bracket_mono_small stage J hLaw hdb ε₀ εs
                ⟨hε₀pos, hε₀ltc⟩ hεs hε₀εs
                (hQ _ _) (hQ _ _) (hQ _ _) (hQ _ _)
                (hQ _ _) (hQ _ _) (hQ _ _) (hQ _ _)
              exact ⟨ε₀, ⟨hε₀pos, hε₀ltc⟩, hα₀,
                le_antisymm (hmono.trans_eq hbrs) (hMOle ε₀ ⟨hε₀pos, hε₀ltc⟩)⟩
            · -- MO > 0 branch: attainment + isolation + monotonicity sandwich
              have hMOpos : 0 < MO := lt_iff_le_and_ne.mpr ⟨by simp, fun h => hMO0 h.symm⟩
              -- the ⨅ is a pointwise lower bound of the bracket (⊤-safe)
              have hMOle : ∀ ε ∈ Set.Ioo 0 ((p.1.toReal - p.2.toReal) / 2),
                  MO ≤ ((rankFn stage J (p.1.toReal - ε) (p.2.toReal + ε) -
                      rankFn stage J (p.1.toReal + ε) (p.2.toReal + ε)) -
                    (rankFn stage J (p.1.toReal - ε) (p.2.toReal - ε) -
                      rankFn stage J (p.1.toReal + ε) (p.2.toReal - ε))) :=
                fun ε hε => iInf_le_of_le ε (iInf_le_of_le hε le_rfl)
              -- STEP 1: the ⨅ is attained at some εs in the range
              obtain ⟨εs, hεs, hεsbr⟩ := bracket_attain
                (fun ε => ((rankFn stage J (p.1.toReal - ε) (p.2.toReal + ε) -
                    rankFn stage J (p.1.toReal + ε) (p.2.toReal + ε)) -
                  (rankFn stage J (p.1.toReal - ε) (p.2.toReal - ε) -
                    rankFn stage J (p.1.toReal + ε) (p.2.toReal - ε)))) hc
              have hbrs : ((rankFn stage J (p.1.toReal - εs) (p.2.toReal + εs) -
                  rankFn stage J (p.1.toReal + εs) (p.2.toReal + εs)) -
                (rankFn stage J (p.1.toReal - εs) (p.2.toReal - εs) -
                  rankFn stage J (p.1.toReal + εs) (p.2.toReal - εs))) = MO := hεsbr
              -- RUNG A at εs: the two birth corners are finite
              obtain ⟨hAstop, hBstop⟩ := bracket_finite_corners_at
                (rankFn stage J (p.1.toReal - εs) (p.2.toReal + εs))
                (rankFn stage J (p.1.toReal + εs) (p.2.toReal + εs))
                (rankFn stage J (p.1.toReal - εs) (p.2.toReal - εs))
                (rankFn stage J (p.1.toReal + εs) (p.2.toReal - εs)) MO
                hbrs hMOpos htop
              have hεs1 : 0 < εs := hεs.1
              have hεs2 : εs < (p.1.toReal - p.2.toReal) / 2 := hεs.2
              -- the death corners at εs are finite too (second-argument monotonicity)
              have hCstop : rankFn stage J (p.1.toReal - εs) (p.2.toReal - εs) ≠ ⊤ := by
                intro h
                have hle := rankFn_monotone_second stage J hLaw
                  (show p.2.toReal - εs ≤ p.2.toReal + εs by linarith)
                  (show p.2.toReal + εs ≤ p.1.toReal - εs by linarith)
                rw [h] at hle
                exact hAstop (top_le_iff.mp hle)
              have hDstop : rankFn stage J (p.1.toReal + εs) (p.2.toReal - εs) ≠ ⊤ := by
                intro h
                have hle := rankFn_monotone_second stage J hLaw
                  (show p.2.toReal - εs ≤ p.2.toReal + εs by linarith)
                  (show p.2.toReal + εs ≤ p.1.toReal + εs by linarith)
                rw [h] at hle
                exact hBstop (top_le_iff.mp hle)
              -- the witness: positive, in range, α-isolated, strictly below εs
              obtain ⟨ε₀, hε₀pos, hε₀ltc, hα₀, hε₀εs, hε₀lts⟩ :
                  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < (p.1.toReal - p.2.toReal) / 2 ∧
                    α < p.2.toReal - ε₀ ∧ ε₀ ≤ εs ∧ ε₀ < εs := by
                refine ⟨min (min (εs / 2) ((p.2.toReal - α) / 2))
                    ((p.1.toReal - p.2.toReal) / 4), ?_, ?_, ?_, ?_, ?_⟩
                · exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
                · have h1 : min (min (εs / 2) ((p.2.toReal - α) / 2))
                      ((p.1.toReal - p.2.toReal) / 4) ≤ (p.1.toReal - p.2.toReal) / 4 :=
                    min_le_right _ _
                  linarith
                · have h1 : min (min (εs / 2) ((p.2.toReal - α) / 2))
                      ((p.1.toReal - p.2.toReal) / 4) ≤ (p.2.toReal - α) / 2 :=
                    (min_le_left _ _).trans (min_le_right _ _)
                  linarith
                · have h1 : min (min (εs / 2) ((p.2.toReal - α) / 2))
                      ((p.1.toReal - p.2.toReal) / 4) ≤ εs / 2 :=
                    (min_le_left _ _).trans (min_le_left _ _)
                  linarith
                · have h1 : min (min (εs / 2) ((p.2.toReal - α) / 2))
                      ((p.1.toReal - p.2.toReal) / 4) ≤ εs / 2 :=
                    (min_le_left _ _).trans (min_le_left _ _)
                  linarith
              -- RUNG B at ε₀: all four corners below εs are finite
              obtain ⟨hA₀, hB₀, hC₀, hD₀⟩ := bracket_finite_corners_below
                stage J hLaw hdb εs hεs MO hMOpos htop hbrs hMOle ε₀ ⟨hε₀pos, hε₀lts⟩
              -- the sandwich: bracket ε₀ ≤ bracket εs = MO ≤ bracket ε₀
              have hmono := bracket_mono_small stage J hLaw hdb ε₀ εs
                ⟨hε₀pos, hε₀ltc⟩ hεs hε₀εs hA₀ hB₀ hC₀ hD₀ hAstop hBstop hCstop hDstop
              exact ⟨ε₀, ⟨hε₀pos, hε₀ltc⟩, hα₀,
                le_antisymm (hmono.trans_eq hbrs) (hMOle ε₀ ⟨hε₀pos, hε₀ltc⟩)⟩
          obtain ⟨ε₀, hε₀, hα₀, hbr⟩ := attain_small
          have hε₀1 : 0 < ε₀ := hε₀.1
          have hε₀2 : ε₀ < (p.1.toReal - p.2.toReal) / 2 := hε₀.2
          refine (iInf_le_of_le ε₀ (iInf_le_of_le hε₀ le_rfl)).trans ?_
          have hbe : α ≤ p.1.toReal - ε₀ := by linarith
          have hbpe : α ≤ p.1.toReal + ε₀ := by linarith
          have hdpe : α ≤ p.2.toReal + ε₀ := by linarith
          have hdme : α ≤ p.2.toReal - ε₀ := le_of_lt hα₀
          rw [← hbr]
          simp only [trunc_rank_eq_above_α _ _ _ _ hbe hdpe,
                     trunc_rank_eq_above_α _ _ _ _ hbpe hdpe,
                     trunc_rank_eq_above_α _ _ _ _ hbe hdme,
                     trunc_rank_eq_above_α _ _ _ _ hbpe hdme]
          exact le_rfl
      · -- inner guard `p.2 < p.1` fails on both sides ⇒ both mults are `0`
        simp only [mult, if_pos hO, if_neg h2bot, if_neg hpdb, le_refl]

theorem solution
    {ι : Type*} (stage : ℝ → Set ι) (J : ℝ → ι → ι → Prop)
    (hLaw : FiltrationLaw stage J) (α : ℝ)
    (hQ : ∀ s t : ℝ, rankFn stage J s t ≠ ⊤) :
    ∀ p ∈ QNE α, mult (rankFn stage J) p = mult (truncRank (rankFn stage J) α) p := by
  intro p hp
  exact mult_agree_QNE stage J hLaw α hQ p hp
